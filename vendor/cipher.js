(function (root, factory) {
  var api = factory();
  if (typeof module === "object" && module.exports) {
    module.exports = api;
  } else {
    root.EstkVmCipher = api;
  }
})(typeof globalThis !== "undefined" ? globalThis : this, function () {
  "use strict";

  /*
   * Byte strings (JS strings whose char codes are bytes) are the shared byte
   * representation: Node, browsers and ExtendScript all handle them without
   * Buffer/Uint8Array, which keeps every build target bit-identical.
   */

  var STRING_CHUNK_SIZE = 8192;
  var BASE64_CHARS =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  var SHA256_CONSTANTS = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ];

  function encodeUtf8(text) {
    var output = "";
    for (var i = 0; i < text.length; i += 1) {
      var code = text.charCodeAt(i);
      if (code < 0x80) {
        output += String.fromCharCode(code);
      } else if (code < 0x800) {
        output += String.fromCharCode(0xc0 | (code >> 6), 0x80 | (code & 0x3f));
      } else if (code >= 0xd800 && code <= 0xdbff && i + 1 < text.length) {
        var next = text.charCodeAt(i + 1);
        if (next >= 0xdc00 && next <= 0xdfff) {
          code = 0x10000 + ((code - 0xd800) << 10) + (next - 0xdc00);
          i += 1;
          output += String.fromCharCode(
            0xf0 | (code >> 18),
            0x80 | ((code >> 12) & 0x3f),
            0x80 | ((code >> 6) & 0x3f),
            0x80 | (code & 0x3f)
          );
        } else {
          output += String.fromCharCode(0xef, 0xbf, 0xbd);
        }
      } else {
        output += String.fromCharCode(
          0xe0 | (code >> 12),
          0x80 | ((code >> 6) & 0x3f),
          0x80 | (code & 0x3f)
        );
      }
    }
    return output;
  }

  function rightRotate(value, amount) {
    return (value >>> amount) | (value << (32 - amount));
  }

  function sha256(data) {
    var bytes = data + String.fromCharCode(0x80);
    while (bytes.length % 64 !== 56) {
      bytes += String.fromCharCode(0);
    }
    var bitLength = data.length * 8;
    bytes += String.fromCharCode(0, 0, 0, 0);
    bytes += String.fromCharCode(
      (bitLength >>> 24) & 0xff,
      (bitLength >>> 16) & 0xff,
      (bitLength >>> 8) & 0xff,
      bitLength & 0xff
    );

    var hash = [
      0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
    ];
    var words = new Array(64);
    var i;

    for (var offset = 0; offset < bytes.length; offset += 64) {
      for (i = 0; i < 16; i += 1) {
        var position = offset + i * 4;
        words[i] =
          ((bytes.charCodeAt(position) << 24) |
            (bytes.charCodeAt(position + 1) << 16) |
            (bytes.charCodeAt(position + 2) << 8) |
            bytes.charCodeAt(position + 3)) >>>
          0;
      }
      for (i = 16; i < 64; i += 1) {
        var s0 =
          rightRotate(words[i - 15], 7) ^
          rightRotate(words[i - 15], 18) ^
          (words[i - 15] >>> 3);
        var s1 =
          rightRotate(words[i - 2], 17) ^
          rightRotate(words[i - 2], 19) ^
          (words[i - 2] >>> 10);
        words[i] = (words[i - 16] + s0 + words[i - 7] + s1) >>> 0;
      }

      var a = hash[0];
      var b = hash[1];
      var c = hash[2];
      var d = hash[3];
      var e = hash[4];
      var f = hash[5];
      var g = hash[6];
      var h = hash[7];

      for (i = 0; i < 64; i += 1) {
        var sigma1 = rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25);
        var choice = (e & f) ^ (~e & g);
        var temp1 = (h + sigma1 + choice + SHA256_CONSTANTS[i] + words[i]) >>> 0;
        var sigma0 = rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22);
        var majority = (a & b) ^ (a & c) ^ (b & c);
        var temp2 = (sigma0 + majority) >>> 0;
        h = g;
        g = f;
        f = e;
        e = (d + temp1) >>> 0;
        d = c;
        c = b;
        b = a;
        a = (temp1 + temp2) >>> 0;
      }

      hash[0] = (hash[0] + a) >>> 0;
      hash[1] = (hash[1] + b) >>> 0;
      hash[2] = (hash[2] + c) >>> 0;
      hash[3] = (hash[3] + d) >>> 0;
      hash[4] = (hash[4] + e) >>> 0;
      hash[5] = (hash[5] + f) >>> 0;
      hash[6] = (hash[6] + g) >>> 0;
      hash[7] = (hash[7] + h) >>> 0;
    }

    var output = "";
    for (i = 0; i < 8; i += 1) {
      output += String.fromCharCode(
        (hash[i] >>> 24) & 0xff,
        (hash[i] >>> 16) & 0xff,
        (hash[i] >>> 8) & 0xff,
        hash[i] & 0xff
      );
    }
    return output;
  }

  function crc32(bytes) {
    var crc = 0xffffffff;
    for (var i = 0; i < bytes.length; i += 1) {
      crc ^= bytes.charCodeAt(i);
      for (var bit = 0; bit < 8; bit += 1) {
        crc = (crc >>> 1) ^ (crc & 1 ? 0xedb88320 : 0);
      }
    }
    return (crc ^ 0xffffffff) >>> 0;
  }

  function rc4(data, key) {
    var state = new Array(256);
    var i;
    var j = 0;
    for (i = 0; i < 256; i += 1) {
      state[i] = i;
    }
    for (i = 0; i < 256; i += 1) {
      j = (j + state[i] + key.charCodeAt(i % key.length)) & 0xff;
      var swap = state[i];
      state[i] = state[j];
      state[j] = swap;
    }

    var chunks = [];
    var chunk = "";
    i = 0;
    j = 0;
    for (var n = 0; n < data.length; n += 1) {
      i = (i + 1) & 0xff;
      j = (j + state[i]) & 0xff;
      var nextSwap = state[i];
      state[i] = state[j];
      state[j] = nextSwap;
      chunk += String.fromCharCode(
        data.charCodeAt(n) ^ state[(state[i] + state[j]) & 0xff]
      );
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

  function base64Encode(bytes) {
    var output = [];
    var chunk = "";
    for (var i = 0; i < bytes.length; i += 3) {
      var first = bytes.charCodeAt(i);
      var second = i + 1 < bytes.length ? bytes.charCodeAt(i + 1) : 0;
      var third = i + 2 < bytes.length ? bytes.charCodeAt(i + 2) : 0;
      chunk += BASE64_CHARS.charAt(first >> 2);
      chunk += BASE64_CHARS.charAt(((first & 3) << 4) | (second >> 4));
      chunk +=
        i + 1 < bytes.length ? BASE64_CHARS.charAt(((second & 15) << 2) | (third >> 6)) : "=";
      chunk += i + 2 < bytes.length ? BASE64_CHARS.charAt(third & 63) : "=";
      if (chunk.length >= STRING_CHUNK_SIZE) {
        output.push(chunk);
        chunk = "";
      }
    }
    if (chunk) {
      output.push(chunk);
    }
    return output.join("");
  }

  /* xorshift32: layout diversity only, never a secret. */
  function createPrng(seed) {
    var state = seed >>> 0;
    if (state === 0) {
      state = 0x9e3779b9;
    }
    return function () {
      state ^= (state << 13) >>> 0;
      state >>>= 0;
      state ^= state >>> 17;
      state ^= (state << 5) >>> 0;
      state >>>= 0;
      return state;
    };
  }

  function shuffle(array, prng) {
    for (var i = array.length - 1; i > 0; i -= 1) {
      var j = prng() % (i + 1);
      var temp = array[i];
      array[i] = array[j];
      array[j] = temp;
    }
    return array;
  }

  function u32be(value) {
    return String.fromCharCode(
      (value >>> 24) & 0xff,
      (value >>> 16) & 0xff,
      (value >>> 8) & 0xff,
      value & 0xff
    );
  }

  function deriveKey(password, salt) {
    return sha256(encodeUtf8(String(password)) + salt);
  }

  function saltFromSeed(seed) {
    return sha256(encodeUtf8(String(seed))).slice(0, 16);
  }

  /*
   * Build-time diversity salt. Uses the host CSPRNG when one exists and
   * falls back to Math.random inside ExtendScript, where neither crypto nor
   * Uint8Array is available.
   */
  function randomBytes(length) {
    var output = "";
    var source =
      typeof crypto !== "undefined" && crypto && crypto.getRandomValues
        ? crypto
        : null;
    var i;

    if (source) {
      var buffer = new Uint8Array(length);
      source.getRandomValues(buffer);
      for (i = 0; i < length; i += 1) {
        output += String.fromCharCode(buffer[i]);
      }
      return output;
    }

    for (i = 0; i < length; i += 1) {
      output += String.fromCharCode(Math.floor(Math.random() * 256));
    }
    return output;
  }

  function randomSalt() {
    return randomBytes(16);
  }

  return {
    base64Encode: base64Encode,
    crc32: crc32,
    createPrng: createPrng,
    deriveKey: deriveKey,
    encodeUtf8: encodeUtf8,
    rc4: rc4,
    randomBytes: randomBytes,
    randomSalt: randomSalt,
    saltFromSeed: saltFromSeed,
    sha256: sha256,
    shuffle: shuffle,
    u32be: u32be
  };
});
