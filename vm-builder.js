(function (root) {
  "use strict";

  /*
   * Browser front end for the shared build pipeline. Everything that touches
   * bytes lives in vendor/cipher.js and vendor/bytecode.js, so the page emits
   * exactly what the Node CLI emits and still works from file:// without
   * WebCrypto (which requires a secure context).
   */

  function preprocess(source) {
    var directives = [];
    var code = [];
    var lines = source.replace(/^\uFEFF/, "").split(/\r?\n/);

    for (var i = 0; i < lines.length; i += 1) {
      var line = lines[i];
      if (/^\s*#include\b/.test(line)) {
        throw new Error(
          "#include is available in the Node CLI and ESTK dialog, not in the browser."
        );
      }
      var match = line.match(/^\s*(#(?:target|targetengine|strict)\b[^\r\n]*)/);
      if (match) {
        if (directives.indexOf(match[1].trim()) === -1) {
          directives.push(match[1].trim());
        }
        // Keep the line as a blank one so compiler diagnostics keep the
        // same line numbers the editor shows.
        code.push("");
        continue;
      }
      code.push(line);
    }

    return {
      code: code.join("\n"),
      directives: directives
    };
  }

  function normalizeError(error) {
    var location = error && error.loc ? error.loc : {};
    return {
      message: error && error.message ? error.message : String(error),
      line: error && error.lineNumber ? error.lineNumber : (location.line || null),
      column: error && error.column !== undefined ? error.column : (location.column || 0),
      index: error && error.pos !== undefined ? error.pos : null
    };
  }

  function check(source, options) {
    options = options || {};
    try {
      var preprocessed = preprocess(source);
      var diagnostics = new root.EstkVmCompiler.Compiler(preprocessed.code, {
        filename: options.filename || "<browser>"
      }).diagnose();
      return {
        ok: diagnostics.errors.length === 0,
        error: diagnostics.errors.length ? diagnostics.errors[0] : null,
        errors: diagnostics.errors,
        warnings: diagnostics.warnings || [],
        directives: preprocessed.directives
      };
    } catch (error) {
      return {
        ok: false,
        error: normalizeError(error),
        directives: []
      };
    }
  }

  function build(source, options) {
    options = options || {};
    var preprocessed = preprocess(source);
    var compiler = new root.EstkVmCompiler.Compiler(preprocessed.code, {
      filename: options.filename || "<browser>"
    });
    var compiled = compiler.compile();
    var warnings = compiled.warnings || [];
    var encrypted = root.EstkVmBytecode.encryptProgram(compiled, {
      key: options.key,
      seed: options.seed,
      protection: options.protection
    });
    var code =
      (preprocessed.directives.length
        ? preprocessed.directives.join("\n") + "\n"
        : "") +
      root.EstkVmBytecode.renderRuntime(String(root.ESTK_VM_RUNTIME_TEMPLATE), {
        wire: encrypted.wire,
        payloadBase64: encrypted.payloadBase64,
        keyBase64: encrypted.keyBase64
      });

    return {
      code: code,
      warnings: warnings,
      stats: {
        functions: encrypted.functions,
        instructions: encrypted.instructions,
        sourceBytes: root.EstkVmCipher.encodeUtf8(source).length,
        bytecodeBytes: encrypted.bytecode.length,
        encryptedBytes: encrypted.encrypted.length,
        poolEntries: encrypted.poolCount,
        protection: encrypted.protection,
        fingerprint: encrypted.fingerprint,
        warningCount: warnings.length
      }
    };
  }

  root.EstkVmBrowser = {
    build: build,
    check: check
  };
})(window);
