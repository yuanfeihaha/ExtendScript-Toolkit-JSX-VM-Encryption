(function (root, factory) {
  if (typeof module === "object" && module.exports) {
    module.exports = factory(require("./opcodes").OP, require("./cipher"));
  } else {
    root.EstkVmBytecode = factory(root.EstkVmOpcodes.OP, root.EstkVmCipher);
  }
})(typeof globalThis !== "undefined" ? globalThis : this, function (OP, cipher) {
  "use strict";

  /*
   * Payload format v2.
   *
   *   "EJVM" u8 version u8 flags u32 opcodeFingerprint
   *   [FLAG_POOL]    uvar poolCount uvar regionLength masked(region)
   *   uvar functionCount functions...
   *
   * The plaintext body is framed with two checksums before RC4:
   *
   *   body u32 crc32(body) u32 crc32(key ++ body)
   *
   * Layout rules that the runtime depends on:
   *   - the entry function is always emitted first, so meta.id === 0 still
   *     identifies the program scope;
   *   - with FLAG_POOL every string, number and boolean operand becomes a
   *     pool reference, so instruction bodies carry no readable literals;
   *   - the constant region is masked with a keystream derived from the
   *     opcode fingerprint, which binds the shipped OP table to the payload.
   */

  var MAGIC = "EJVM";
  var FORMAT_VERSION = 2;

  var FLAG_PERMUTATION = 1;
  var FLAG_POOL = 2;
  var FLAG_SHUFFLE = 4;

  var DEFAULT_KEY = "ESTK-JSX-VM-v1";
  var DEFAULT_PROTECTION = "hardened";

  var PROTECTION_FLAGS = {
    standard: 0,
    hardened: FLAG_PERMUTATION | FLAG_POOL,
    maximum: FLAG_PERMUTATION | FLAG_POOL | FLAG_SHUFFLE
  };
  var PROTECTION_NAMES = ["standard", "hardened", "maximum"];

  /*
   * Canonical opcode order. src/core/runtime.jsx hardcodes the same list as
   * OPCANON: the fingerprint is computed over "NAME=value;" pairs, so the
   * shipped file can verify its own table without ever storing the original
   * numbering.
   */
  var CANONICAL_OPCODES = (
    "PUSH_CONST,PUSH_UNDEFINED,PUSH_NULL,PUSH_TRUE,PUSH_FALSE,PUSH_THIS," +
    "LOAD_NAME,STORE_NAME,TYPEOF_NAME,DEL_NAME,LOAD_ARGUMENTS,LOAD_ARG," +
    "GET_PROP,SET_PROP,DEL_PROP,MAKE_ARRAY,MAKE_OBJECT,MAKE_FUNCTION," +
    "PUSH_REGEX,UNARY,BINARY,DUP,DUP2,POP,SWAP,JMP,JMP_IF_FALSE,JMP_IF_TRUE," +
    "CALL,NEW,RETURN,THROW,ENUM_INIT,ITER_NEXT,TRY_BEGIN,TRY_NORMAL," +
    "END_FINALLY,COMPLETE,SET_TEMP,LOAD_TEMP,BIND_NAME,POP_SCOPE," +
    "BINARY_ADD,BINARY_SUB,BINARY_MUL,BINARY_DIV,BINARY_MOD,BINARY_LT," +
    "BINARY_LE,BINARY_GT,BINARY_GE,BINARY_EQ,BINARY_NE,BINARY_SEQ,BINARY_SNE," +
    "BINARY_LSHIFT,BINARY_RSHIFT,BINARY_URSHIFT,BINARY_BIT_OR,BINARY_BIT_XOR," +
    "BINARY_BIT_AND,BINARY_IN,BINARY_INSTANCEOF,UNARY_PLUS,UNARY_MINUS," +
    "UNARY_NOT,UNARY_BITNOT"
  ).split(",");

  var CANONICAL_VALUES = [];
  for (var canonicalIndex = 0; canonicalIndex < CANONICAL_OPCODES.length; canonicalIndex += 1) {
    var canonicalValue = OP[CANONICAL_OPCODES[canonicalIndex]];
    if (typeof canonicalValue !== "number") {
      throw new Error(
        "Opcode table is missing " + CANONICAL_OPCODES[canonicalIndex]
      );
    }
    CANONICAL_VALUES.push(canonicalValue);
  }

  var OPCODE_STREAM = "opcode-table";
  var LAYOUT_STREAM = "function-layout";
  var POOL_STREAM = "constant-layout";
  var POOL_MASK_MIXER = 0x5f356495;
  var STRING_CHUNK_SIZE = 8192;

  var hasOwn = Object.prototype.hasOwnProperty;
  var CHARS = new Array(256);
  for (var charIndex = 0; charIndex < 256; charIndex += 1) {
    CHARS[charIndex] = String.fromCharCode(charIndex);
  }

  function formatNumber(value) {
    if (value !== value) {
      return "NaN";
    }
    if (value === Infinity) {
      return "Infinity";
    }
    if (value === -Infinity) {
      return "-Infinity";
    }
    if (value === 0 && 1 / value === -Infinity) {
      return "-0";
    }
    return String(value);
  }

  function ByteWriter() {
    this.parts = [];
  }

  ByteWriter.prototype.u8 = function (value) {
    this.parts.push(CHARS[value & 0xff]);
  };

  ByteWriter.prototype.u32 = function (value) {
    this.parts.push(cipher.u32be(value >>> 0));
  };

  ByteWriter.prototype.uvar = function (value) {
    var current = value;
    var output = "";
    if (!(current >= 0) || Math.floor(current) !== current) {
      throw new Error("Invalid unsigned bytecode integer: " + value);
    }
    do {
      var part = current % 128;
      current = Math.floor(current / 128);
      if (current > 0) {
        part |= 0x80;
      }
      output += CHARS[part];
    } while (current > 0);
    this.parts.push(output);
  };

  ByteWriter.prototype.utf8 = function (value) {
    var bytes = cipher.encodeUtf8(String(value));
    this.uvar(bytes.length);
    this.parts.push(bytes);
  };

  ByteWriter.prototype.raw = function (bytes) {
    this.parts.push(String(bytes));
  };

  ByteWriter.prototype.finish = function () {
    return this.parts.join("");
  };

  /* ------------------------------------------------------------------ *
   * opcode table diversification
   * ------------------------------------------------------------------ */

  function identityWire() {
    var wire = [];
    for (var i = 0; i < CANONICAL_VALUES.length; i += 1) {
      wire[CANONICAL_VALUES[i]] = CANONICAL_VALUES[i];
    }
    return wire;
  }

  function streamSeed(keyBytes, tag) {
    return cipher.crc32(keyBytes + tag);
  }

  /*
   * wire[canonicalValue] = emittedValue. The permutation is reproducible from
   * the build key alone, so the same key and seed always produce the same
   * table while different builds do not share one.
   */
  function createWirePermutation(keyBytes, flags) {
    var emitted = CANONICAL_VALUES.slice();
    if ((flags & FLAG_PERMUTATION) !== 0) {
      cipher.shuffle(emitted, cipher.createPrng(streamSeed(keyBytes, OPCODE_STREAM)));
    }
    var wire = [];
    for (var i = 0; i < CANONICAL_VALUES.length; i += 1) {
      wire[CANONICAL_VALUES[i]] = emitted[i];
    }
    return wire;
  }

  function wireValues(wire) {
    var values = [];
    for (var i = 0; i < CANONICAL_VALUES.length; i += 1) {
      values.push(wire[CANONICAL_VALUES[i]]);
    }
    return values;
  }

  function fingerprintFor(wire) {
    var text = "";
    for (var i = 0; i < CANONICAL_OPCODES.length; i += 1) {
      text += CANONICAL_OPCODES[i] + "=" + wire[CANONICAL_VALUES[i]] + ";";
    }
    return cipher.crc32(text);
  }

  /* Keystream seed for the constant region; the runtime derives it the same way. */
  function poolMaskSeed(fingerprint) {
    return (fingerprint ^ POOL_MASK_MIXER) >>> 0;
  }

  function maskRegion(region, seed) {
    var prng = cipher.createPrng(seed);
    var chunks = [];
    var chunk = "";
    for (var i = 0; i < region.length; i += 1) {
      chunk += CHARS[region.charCodeAt(i) ^ (prng() & 0xff)];
      if (chunk.length >= STRING_CHUNK_SIZE) {
        chunks.push(chunk);
        chunk = "";
      }
    }
    if (chunk) {
      chunks.push(chunk);
    }
    return chunks.join("");
  }

  function renderOpcodeSource(wire) {
    var values = wireValues(wire);
    var lines = ["  var OP = {"];
    var last = CANONICAL_OPCODES.length - 1;
    for (var i = 0; i <= last; i += 1) {
      lines.push(
        "    " + CANONICAL_OPCODES[i] + ": " + values[i] + (i === last ? "" : ",")
      );
    }
    lines.push("  };");
    return lines.join("\n");
  }

  var OP_BLOCK_PATTERN = / {2}var OP = \{[\s\S]*?\n {2}\};/;

  function renderRuntime(template, options) {
    var source = String(template);
    if (!OP_BLOCK_PATTERN.test(source)) {
      throw new Error("Runtime template does not contain the opcode table");
    }
    if (source.indexOf('"__ESTK_VM_PAYLOAD__"') === -1) {
      throw new Error("Runtime template does not contain the payload slot");
    }
    if (source.indexOf('"__ESTK_VM_KEY__"') === -1) {
      throw new Error("Runtime template does not contain the key slot");
    }

    /* Base64 needs no escaping, so quoting stays identical in every host. */
    return source
      .replace(OP_BLOCK_PATTERN, function () {
        return renderOpcodeSource(options.wire);
      })
      .replace('"__ESTK_VM_PAYLOAD__"', function () {
        return '"' + options.payloadBase64 + '"';
      })
      .replace('"__ESTK_VM_KEY__"', function () {
        return '"' + options.keyBase64 + '"';
      });
  }

  /* ------------------------------------------------------------------ *
   * constant pool
   * ------------------------------------------------------------------ */

  function ConstantPool(maskSeedValue) {
    this.entries = [];
    this.index = {};
    this.remap = null;
    this.maskSeedValue = maskSeedValue;
  }

  ConstantPool.prototype.keyFor = function (value) {
    var type = typeof value;
    if (type === "string") {
      return "s" + value;
    }
    if (type === "number") {
      return "n" + formatNumber(value);
    }
    if (type === "boolean") {
      return "b" + (value ? "1" : "0");
    }
    return null;
  };

  ConstantPool.prototype.add = function (value) {
    var key = this.keyFor(value);
    if (key !== null && hasOwn.call(this.index, key)) {
      return this.index[key];
    }

    var writer = new ByteWriter();
    if (typeof value === "string") {
      writer.u8(0);
      writer.utf8(value);
    } else if (typeof value === "number") {
      writer.u8(1);
      writer.utf8(formatNumber(value));
    } else if (typeof value === "boolean") {
      writer.u8(2);
      writer.u8(value ? 1 : 0);
    } else {
      throw new Error("Unsupported constant pool value: " + String(value));
    }

    var id = this.entries.length;
    this.entries.push(writer.finish());
    if (key !== null) {
      this.index[key] = id;
    }
    return id;
  };

  ConstantPool.prototype.lookup = function (value) {
    var key = this.keyFor(value);
    var id = key !== null && hasOwn.call(this.index, key) ? this.index[key] : this.add(value);
    return this.remap ? this.remap[id] : id;
  };

  ConstantPool.prototype.finish = function (prng) {
    var count = this.entries.length;
    var order = new Array(count);
    var i;
    for (i = 0; i < count; i += 1) {
      order[i] = i;
    }
    if (prng) {
      cipher.shuffle(order, prng);
    }

    this.remap = new Array(count);
    for (i = 0; i < count; i += 1) {
      this.remap[order[i]] = i;
    }

    var region = new ByteWriter();
    for (i = 0; i < count; i += 1) {
      region.raw(this.entries[order[i]]);
    }
    var regionBytes = maskRegion(region.finish(), this.maskSeedValue);

    var writer = new ByteWriter();
    writer.uvar(count);
    writer.uvar(regionBytes.length);
    writer.raw(regionBytes);
    return {
      bytes: writer.finish(),
      count: count
    };
  };

  /* ------------------------------------------------------------------ *
   * serialization
   * ------------------------------------------------------------------ */

  function writeOperand(writer, value, pool) {
    var type = typeof value;
    if (type === "bigint") {
      value = Number(value);
      type = "number";
    }
    if (value === null) {
      writer.u8(3);
      return;
    }
    if (type === "undefined") {
      writer.u8(4);
      return;
    }
    if (pool) {
      writer.u8(5);
      writer.uvar(pool.lookup(value));
      return;
    }
    if (type === "string") {
      writer.u8(0);
      writer.utf8(value);
      return;
    }
    if (type === "number") {
      writer.u8(1);
      writer.utf8(formatNumber(value));
      return;
    }
    if (type === "boolean") {
      writer.u8(2);
      writer.u8(value ? 1 : 0);
      return;
    }
    throw new Error("Unsupported bytecode operand: " + String(value));
  }

  function writeMeta(writer, value, pool) {
    var text = value === undefined || value === null ? "" : String(value);
    if (pool) {
      writer.uvar(pool.lookup(text));
      return;
    }
    writer.utf8(text);
  }

  function isPoolable(value) {
    var type = typeof value;
    return type === "string" || type === "number" || type === "boolean" || type === "bigint";
  }

  /* The entry function stays at emitted index 0; the rest may be reordered. */
  function createLayoutOrder(count, prng) {
    var order = new Array(count);
    var i;
    for (i = 0; i < count; i += 1) {
      order[i] = i;
    }
    if (prng && count > 2) {
      var tail = order.slice(1);
      cipher.shuffle(tail, prng);
      for (i = 1; i < count; i += 1) {
        order[i] = tail[i - 1];
      }
    }
    return order;
  }

  function collectConstants(functions, order, pool, emittedId) {
    for (var emitted = 0; emitted < order.length; emitted += 1) {
      var fn = functions[order[emitted]];
      pool.add(fn.name || "");
      var i;
      for (i = 0; i < fn.params.length; i += 1) {
        pool.add(fn.params[i]);
      }
      for (i = 0; i < fn.vars.length; i += 1) {
        pool.add(fn.vars[i]);
      }
      for (i = 0; i < fn.decls.length; i += 1) {
        pool.add(fn.decls[i].name);
      }
      if (fn.selfName) {
        pool.add(fn.selfName);
      }
      for (i = 0; i < fn.code.length; i += 1) {
        var instruction = fn.code[i];
        for (var operand = 1; operand < instruction.length; operand += 1) {
          var value = instruction[operand];
          /*
           * MAKE_FUNCTION stores a function id. A shuffled layout rewrites
           * that id at serialization time, so collect the rewritten value too;
           * otherwise pool.lookup() would add it after the pool was finished
           * and return an undefined remap entry.
           */
          if (operand === 1 && instruction[0] === OP.MAKE_FUNCTION) {
            value = emittedId[value];
          }
          if (isPoolable(value)) {
            pool.add(typeof value === "bigint" ? Number(value) : value);
          }
        }
      }
    }
  }

  function serialize(program, options) {
    options = options || {};
    var flags = options.flags === undefined
      ? PROTECTION_FLAGS[DEFAULT_PROTECTION]
      : options.flags;
    var wire = options.wire || identityWire();
    var fingerprint = options.fingerprint === undefined ? 0 : options.fingerprint;
    var pooled = (flags & FLAG_POOL) !== 0;
    var functions = program.functions;
    var count = functions.length;
    var order = createLayoutOrder(count, (flags & FLAG_SHUFFLE) ? options.layoutPrng : null);
    var emittedId = new Array(count);
    var pool = pooled ? new ConstantPool(options.maskSeed || 0) : null;
    var poolBytes = "";
    var poolCount = 0;
    var instructions = 0;
    var i;

    for (i = 0; i < count; i += 1) {
      emittedId[order[i]] = i;
    }

    if (pool) {
      collectConstants(functions, order, pool, emittedId);
      var finishedPool = pool.finish((flags & FLAG_SHUFFLE) ? options.poolPrng : null);
      poolBytes = finishedPool.bytes;
      poolCount = finishedPool.count;
    }

    var writer = new ByteWriter();
    writer.raw(MAGIC);
    writer.u8(FORMAT_VERSION);
    writer.u8(flags);
    writer.u32(fingerprint);
    if (pool) {
      writer.raw(poolBytes);
    }
    writer.uvar(count);

    for (var emitted = 0; emitted < count; emitted += 1) {
      var fn = functions[order[emitted]];
      instructions += fn.code.length;

      writeMeta(writer, fn.name || "", pool);

      writer.uvar(fn.params.length);
      for (i = 0; i < fn.params.length; i += 1) {
        writeMeta(writer, fn.params[i], pool);
      }

      writer.uvar(fn.vars.length);
      for (i = 0; i < fn.vars.length; i += 1) {
        writeMeta(writer, fn.vars[i], pool);
      }

      writer.uvar(fn.decls.length);
      for (i = 0; i < fn.decls.length; i += 1) {
        writeMeta(writer, fn.decls[i].name, pool);
        writer.uvar(emittedId[fn.decls[i].functionId]);
      }

      writer.u8(fn.selfName ? 1 : 0);
      if (fn.selfName) {
        writeMeta(writer, fn.selfName, pool);
      }

      writer.uvar(fn.maxTemps || 0);
      writer.uvar(fn.code.length);
      for (i = 0; i < fn.code.length; i += 1) {
        var instruction = fn.code[i];
        var opcode = instruction[0];
        var emittedOpcode = wire[opcode];
        if (emittedOpcode === undefined) {
          throw new Error("Opcode is not part of the canonical table: " + opcode);
        }
        writer.u8(emittedOpcode);
        writer.u8(instruction.length - 1);
        for (var operand = 1; operand < instruction.length; operand += 1) {
          var operandValue = instruction[operand];
          /*
           * MAKE_FUNCTION carries a function id, so a shuffled layout has to
           * rewrite it exactly like the declaration table above.
           */
          if (operand === 1 && opcode === OP.MAKE_FUNCTION) {
            operandValue = emittedId[operandValue];
          }
          writeOperand(writer, operandValue, pool);
        }
      }
    }

    return {
      bytes: writer.finish(),
      flags: flags,
      fingerprint: fingerprint,
      functions: count,
      instructions: instructions,
      poolCount: poolCount
    };
  }

  function serializeProgram(program, options) {
    return serialize(program, options).bytes;
  }

  /* ------------------------------------------------------------------ *
   * protection levels
   * ------------------------------------------------------------------ */

  function resolveProtection(protection) {
    if (protection === undefined || protection === null || protection === "") {
      return PROTECTION_FLAGS[DEFAULT_PROTECTION];
    }
    if (typeof protection === "number") {
      if (Math.floor(protection) !== protection || protection < 0 || (protection & ~7) !== 0) {
        throw new Error("Invalid protection flags: " + protection);
      }
      return protection;
    }
    var name = String(protection).toLowerCase();
    if (!hasOwn.call(PROTECTION_FLAGS, name)) {
      throw new Error(
        "Unknown protection level: " + protection +
        " (expected " + PROTECTION_NAMES.join(", ") + ")"
      );
    }
    return PROTECTION_FLAGS[name];
  }

  function protectionName(flags) {
    for (var i = 0; i < PROTECTION_NAMES.length; i += 1) {
      if (PROTECTION_FLAGS[PROTECTION_NAMES[i]] === flags) {
        return PROTECTION_NAMES[i];
      }
    }
    return "custom";
  }

  function resolveSalt(options) {
    if (options.salt) {
      return String(options.salt);
    }
    if (options.seed !== undefined && options.seed !== null && options.seed !== "") {
      return cipher.saltFromSeed(options.seed);
    }
    return cipher.randomSalt();
  }

  /*
   * Full build step shared by the Node API, the browser builder and the
   * standalone ESTK builder so every target emits identical bytes.
   */
  function encryptProgram(program, options) {
    options = options || {};
    var password = options.key === undefined ? DEFAULT_KEY : String(options.key);
    var flags = resolveProtection(options.protection);
    var salt = resolveSalt(options);
    var keyBytes = cipher.deriveKey(password, salt);
    var wire = createWirePermutation(keyBytes, flags);
    var fingerprint = fingerprintFor(wire);
    var shuffled = (flags & FLAG_SHUFFLE) !== 0;

    var built = serialize(program, {
      flags: flags,
      wire: wire,
      fingerprint: fingerprint,
      maskSeed: poolMaskSeed(fingerprint),
      layoutPrng: shuffled ? cipher.createPrng(streamSeed(keyBytes, LAYOUT_STREAM)) : null,
      poolPrng: shuffled ? cipher.createPrng(streamSeed(keyBytes, POOL_STREAM)) : null
    });

    var body = built.bytes;
    var frame =
      body +
      cipher.u32be(cipher.crc32(body)) +
      cipher.u32be(cipher.crc32(keyBytes + body));
    var encrypted = cipher.rc4(frame, keyBytes);

    return {
      payloadBase64: cipher.base64Encode(encrypted),
      keyBase64: cipher.base64Encode(keyBytes),
      bytecode: body,
      encrypted: encrypted,
      salt: salt,
      keyBytes: keyBytes,
      wire: wire,
      flags: flags,
      protection: protectionName(flags),
      fingerprint: fingerprint,
      functions: built.functions,
      instructions: built.instructions,
      poolCount: built.poolCount
    };
  }

  return {
    CANONICAL_OPCODES: CANONICAL_OPCODES,
    CANONICAL_VALUES: CANONICAL_VALUES,
    DEFAULT_KEY: DEFAULT_KEY,
    DEFAULT_PROTECTION: DEFAULT_PROTECTION,
    FLAG_PERMUTATION: FLAG_PERMUTATION,
    FLAG_POOL: FLAG_POOL,
    FLAG_SHUFFLE: FLAG_SHUFFLE,
    FORMAT_VERSION: FORMAT_VERSION,
    MAGIC: MAGIC,
    PROTECTION_FLAGS: PROTECTION_FLAGS,
    PROTECTION_NAMES: PROTECTION_NAMES,
    createWirePermutation: createWirePermutation,
    encryptProgram: encryptProgram,
    fingerprintFor: fingerprintFor,
    identityWire: identityWire,
    poolMaskSeed: poolMaskSeed,
    protectionName: protectionName,
    renderOpcodeSource: renderOpcodeSource,
    renderRuntime: renderRuntime,
    resolveProtection: resolveProtection,
    serializeProgram: serializeProgram
  };
});
