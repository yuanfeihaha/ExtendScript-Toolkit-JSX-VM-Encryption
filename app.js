(function () {
  "use strict";

  /* ------------------------------------------------------------------ *
   * element references
   * ------------------------------------------------------------------ */

  function byId(id) {
    return document.getElementById(id);
  }

  var workspace = byId("workspace");
  var splitter = byId("splitter");
  var sourceEditor = byId("sourceEditor");
  var highlightLayer = byId("highlightLayer");
  var gutter = byId("gutter");
  var dropZone = byId("dropZone");
  var sourceMeta = byId("sourceMeta");
  var diagnostics = byId("diagnostics");
  var diagList = byId("diagList");
  var keyInput = byId("keyInput");
  var keyIconUse = byId("keyIconUse");
  var toggleKeyButton = byId("toggleKeyButton");
  var seedInput = byId("seedInput");
  var randomSeedButton = byId("randomSeedButton");
  var outputName = byId("outputName");
  var protectionSelect = byId("protectionSelect");
  var loadButton = byId("loadButton");
  var clearButton = byId("clearButton");
  var buildButton = byId("buildButton");
  var copyButton = byId("copyButton");
  var downloadButton = byId("downloadButton");
  var fileInput = byId("fileInput");
  var buildStatus = byId("buildStatus");
  var statsOutput = byId("statsOutput");
  var resultOutput = byId("resultOutput");
  var engineStatus = byId("engineStatus");
  var engineText = byId("engineText");

  var STORAGE_PREFIX = "estk-vm-builder.";
  var SPLIT_MIN = 22;
  var SPLIT_MAX = 78;
  var SPLIT_GAP = 7;
  var NARROW_QUERY = "(max-width: 940px)";
  var HIGHLIGHT_LIMIT = 400000;
  var VALIDATE_DELAY = 300;
  var SAVE_DELAY = 500;

  var PROTECTION_LABELS = {
    standard: "标准",
    hardened: "强化",
    maximum: "极限"
  };

  var DEFAULT_PROTECTION = "hardened";

  var state = {
    filename: "",
    errorLine: 0,
    errorIndex: -1,
    hasError: false,
    warnings: [],
    code: "",
    building: false,
    split: 50,
    dirty: false
  };

  var validateTimer = null;
  var saveTimer = null;
  var renderQueued = false;
  var engineReady = false;

  /* ------------------------------------------------------------------ *
   * small helpers
   * ------------------------------------------------------------------ */

  function makeSet(words) {
    var set = {};
    var list = words.split(" ");
    for (var i = 0; i < list.length; i += 1) {
      if (list[i]) {
        set[list[i]] = true;
      }
    }
    return set;
  }

  function escapeHtml(text) {
    return text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  }

  function formatBytes(value) {
    if (value < 1024) {
      return value + " B";
    }
    if (value < 1024 * 1024) {
      return (value / 1024).toFixed(1) + " KB";
    }
    return (value / 1024 / 1024).toFixed(2) + " MB";
  }

  function hasOwn(map, key) {
    return Object.prototype.hasOwnProperty.call(map, key);
  }

  function protectionLabel(value) {
    return hasOwn(PROTECTION_LABELS, value) ? PROTECTION_LABELS[value] : String(value);
  }

  function fingerprintHex(value) {
    var text = (value >>> 0).toString(16);
    while (text.length < 8) {
      text = "0" + text;
    }
    return text;
  }

  function currentProtection() {
    var value = protectionSelect.value;
    return hasOwn(PROTECTION_LABELS, value) ? value : DEFAULT_PROTECTION;
  }

  function storageGet(name) {
    try {
      return window.localStorage.getItem(STORAGE_PREFIX + name);
    } catch (error) {
      return null;
    }
  }

  function storageSet(name, value) {
    try {
      window.localStorage.setItem(STORAGE_PREFIX + name, value);
    } catch (error) {
      /* private mode or quota: persistence is optional */
    }
  }

  function lineHeight() {
    var value = parseFloat(window.getComputedStyle(sourceEditor).lineHeight);
    return value > 0 ? value : 20;
  }

  function sanitizeFilename(name) {
    var cleaned = String(name || "").replace(/[\\/:*?"<>|\r\n]+/g, "").trim();
    if (!cleaned) {
      return "script.protected.jsx";
    }
    if (!/\.(jsx|js|tsx|ts)$/i.test(cleaned)) {
      cleaned += ".jsx";
    }
    return cleaned;
  }

  /* ------------------------------------------------------------------ *
   * tokenizer: hand written scanner, no regex backtracking
   * ------------------------------------------------------------------ */

  var KEYWORDS = makeSet(
    "break case catch const continue default delete do else finally for function if in " +
      "instanceof new return switch this throw try typeof var void while with"
  );
  var LITERALS = makeSet("true false null");
  var BUILTINS = makeSet(
    "$ app alert confirm prompt eval parseInt parseFloat isNaN isFinite undefined NaN Infinity " +
      "Arguments Array Boolean Date Error EvalError Function Math Number Object RangeError " +
      "ReferenceError RegExp String SyntaxError TypeError URIError JSON console " +
      "decodeURI decodeURIComponent encodeURI encodeURIComponent escape unescape " +
      "File Folder FileInputStream FileOutputStream Socket ExternalObject ScriptUI Window " +
      "UnitValue XML XMLList Color Path Selection Document BridgeTalk Bridge LocalObject PluScript"
  );
  var OPERATORS = [
    ">>>=", "===", "!==", "<<=", ">>=", ">>>",
    "==", "!=", "<=", ">=", "&&", "||", "++", "--",
    "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "=>"
  ];
  var OP_CHARS = "+-*/%=<>!&|^~";
  var PUNCT_CHARS = "()[]{},;:.?";

  function isDigit(ch) {
    return ch >= "0" && ch <= "9";
  }

  function isIdentStart(ch) {
    return (ch >= "a" && ch <= "z") || (ch >= "A" && ch <= "Z") || ch === "_" || ch === "$" || ch > "~";
  }

  function isIdentPart(ch) {
    return isIdentStart(ch) || isDigit(ch);
  }

  function isHexDigit(ch) {
    return isDigit(ch) || (ch >= "a" && ch <= "f") || (ch >= "A" && ch <= "F");
  }

  function regexAllowed(prevType, prevValue) {
    if (prevType === "" || prevType === "op" || prevType === "dot" || prevType === "comment") {
      return true;
    }
    if (prevType === "keyword") {
      return prevValue !== "this";
    }
    if (prevType === "punct") {
      return prevValue !== ")" && prevValue !== "]";
    }
    return false;
  }

  function tokenize(source) {
    var tokens = [];
    var n = source.length;
    var i = 0;
    var prevType = "";
    var prevValue = "";
    var atLineStart = true;

    while (i < n) {
      var ch = source.charAt(i);

      if (ch === "\n") {
        i += 1;
        atLineStart = true;
        continue;
      }
      if (ch === " " || ch === "\t" || ch === "\r" || ch === "\f") {
        i += 1;
        continue;
      }

      if (ch === "#" && atLineStart) {
        var directiveEnd = source.indexOf("\n", i);
        if (directiveEnd < 0) {
          directiveEnd = n;
        }
        tokens.push({ s: i, e: directiveEnd, c: "directive" });
        prevType = "directive";
        prevValue = "";
        i = directiveEnd;
        continue;
      }
      atLineStart = false;

      if (ch === "/" && source.charAt(i + 1) === "/") {
        var lineEnd = source.indexOf("\n", i);
        if (lineEnd < 0) {
          lineEnd = n;
        }
        tokens.push({ s: i, e: lineEnd, c: "comment" });
        prevType = "comment";
        prevValue = "";
        i = lineEnd;
        continue;
      }

      if (ch === "/" && source.charAt(i + 1) === "*") {
        var blockEnd = source.indexOf("*/", i + 2);
        blockEnd = blockEnd < 0 ? n : blockEnd + 2;
        tokens.push({ s: i, e: blockEnd, c: "comment" });
        prevType = "comment";
        prevValue = "";
        atLineStart = false;
        i = blockEnd;
        continue;
      }

      if (ch === "/" && regexAllowed(prevType, prevValue)) {
        var r = i + 1;
        var inClass = false;
        var closed = false;
        while (r < n) {
          var rc = source.charAt(r);
          if (rc === "\\") {
            r += 2;
            continue;
          }
          if (rc === "\n") {
            break;
          }
          if (rc === "[") {
            inClass = true;
          } else if (rc === "]") {
            inClass = false;
          } else if (rc === "/" && !inClass) {
            r += 1;
            closed = true;
            break;
          }
          r += 1;
        }
        if (closed) {
          while (r < n && (source.charAt(r) === "g" || source.charAt(r) === "i" || source.charAt(r) === "m")) {
            r += 1;
          }
          if (r > n) {
            r = n;
          }
          tokens.push({ s: i, e: r, c: "regex" });
          prevType = "regex";
          prevValue = "";
          i = r;
          continue;
        }
      }

      if (ch === '"' || ch === "'") {
        var q = i + 1;
        while (q < n) {
          var sc = source.charAt(q);
          if (sc === "\\") {
            q += 2;
            continue;
          }
          if (sc === ch) {
            q += 1;
            break;
          }
          if (sc === "\n") {
            break;
          }
          q += 1;
        }
        if (q > n) {
          q = n;
        }
        tokens.push({ s: i, e: q, c: "string" });
        prevType = "string";
        prevValue = "";
        i = q;
        continue;
      }

      if (isDigit(ch)) {
        var d = i;
        if (ch === "0" && (source.charAt(d + 1) === "x" || source.charAt(d + 1) === "X")) {
          d += 2;
          while (d < n && isHexDigit(source.charAt(d))) {
            d += 1;
          }
        } else {
          while (d < n && isDigit(source.charAt(d))) {
            d += 1;
          }
          if (source.charAt(d) === ".") {
            d += 1;
            while (d < n && isDigit(source.charAt(d))) {
              d += 1;
            }
          }
          if (source.charAt(d) === "e" || source.charAt(d) === "E") {
            var exponent = d + 1;
            if (source.charAt(exponent) === "+" || source.charAt(exponent) === "-") {
              exponent += 1;
            }
            if (isDigit(source.charAt(exponent))) {
              d = exponent;
              while (d < n && isDigit(source.charAt(d))) {
                d += 1;
              }
            }
          }
        }
        tokens.push({ s: i, e: d, c: "number" });
        prevType = "number";
        prevValue = "";
        i = d;
        continue;
      }

      if (isIdentStart(ch)) {
        var w = i + 1;
        while (w < n && isIdentPart(source.charAt(w))) {
          w += 1;
        }
        var word = source.slice(i, w);
        var wordClass = "";
        if (KEYWORDS[word]) {
          wordClass = "keyword";
        } else if (LITERALS[word]) {
          wordClass = "literal";
        } else if (prevType === "dot") {
          wordClass = "property";
        } else if (BUILTINS[word]) {
          wordClass = "builtin";
        } else {
          var peek = w;
          while (peek < n && (source.charAt(peek) === " " || source.charAt(peek) === "\t")) {
            peek += 1;
          }
          if (source.charAt(peek) === "(") {
            wordClass = "fn";
          }
        }
        if (wordClass) {
          tokens.push({ s: i, e: w, c: wordClass });
        }
        prevType = wordClass === "keyword" ? "keyword" : wordClass === "literal" ? "literal" : "ident";
        prevValue = word;
        i = w;
        continue;
      }

      var operator = "";
      for (var oi = 0; oi < OPERATORS.length; oi += 1) {
        if (source.substr(i, OPERATORS[oi].length) === OPERATORS[oi]) {
          operator = OPERATORS[oi];
          break;
        }
      }
      if (operator) {
        tokens.push({ s: i, e: i + operator.length, c: "op" });
        prevType = "op";
        prevValue = operator;
        i += operator.length;
        continue;
      }

      if (OP_CHARS.indexOf(ch) >= 0) {
        tokens.push({ s: i, e: i + 1, c: "op" });
        prevType = "op";
        prevValue = ch;
        i += 1;
        continue;
      }

      if (PUNCT_CHARS.indexOf(ch) >= 0) {
        tokens.push({ s: i, e: i + 1, c: "punct" });
        prevType = ch === "." ? "dot" : "punct";
        prevValue = ch;
        i += 1;
        continue;
      }

      i += 1;
    }

    return tokens;
  }

  /* ------------------------------------------------------------------ *
   * editor rendering
   * ------------------------------------------------------------------ */

  function appendPlain(source, from, to, errorIndex) {
    if (errorIndex < from || errorIndex >= to) {
      return escapeHtml(source.slice(from, to));
    }
    var end = errorIndex;
    while (end < to) {
      var ch = source.charAt(end);
      if (ch === " " || ch === "\t" || "(){}[];,".indexOf(ch) >= 0) {
        break;
      }
      end += 1;
    }
    if (end === errorIndex) {
      end = Math.min(to, errorIndex + 1);
    }
    return (
      escapeHtml(source.slice(from, errorIndex)) +
      '<span class="hl-err">' + escapeHtml(source.slice(errorIndex, end)) + "</span>" +
      escapeHtml(source.slice(end, to))
    );
  }

  function renderEditor() {
    var source = sourceEditor.value;
    var lines = source.split("\n");
    var errorLine = state.errorLine;
    var errorIndex = state.errorIndex;
    var tooBig = source.length > HIGHLIGHT_LIMIT;
    var tokens = tooBig ? [] : tokenize(source);
    var body = [];
    var numbers = [];
    var tokenIndex = 0;
    var position = 0;

    for (var li = 0; li < lines.length; li += 1) {
      var lineText = lines[li];
      var lineEnd = position + lineText.length;
      var lineClass = "hl-line";
      if (errorLine === li + 1) {
        lineClass += " err";
      }
      numbers.push(
        '<div class="gl' + (errorLine === li + 1 ? " err" : "") + '">' + (li + 1) + "</div>"
      );

      var html = "";
      var cursor = position;
      if (!tooBig) {
        while (tokenIndex < tokens.length && tokens[tokenIndex].e <= position) {
          tokenIndex += 1;
        }
        var k = tokenIndex;
        while (k < tokens.length && tokens[k].s < lineEnd) {
          var token = tokens[k];
          var from = token.s > position ? token.s : position;
          var to = token.e < lineEnd ? token.e : lineEnd;
          if (from > cursor) {
            html += appendPlain(source, cursor, from, errorIndex);
          }
          if (to > from) {
            var marked = errorIndex >= token.s && errorIndex < token.e;
            html +=
              '<span class="tok-' + token.c + (marked ? " hl-err" : "") + '">' +
              escapeHtml(source.slice(from, to)) +
              "</span>";
          }
          cursor = to;
          if (token.e <= lineEnd) {
            k += 1;
          } else {
            break;
          }
        }
      }
      if (cursor < lineEnd) {
        html += appendPlain(source, cursor, lineEnd, errorIndex);
      }
      body.push('<div class="' + lineClass + '">' + html + "</div>");
      position = lineEnd + 1;
    }

    highlightLayer.innerHTML = body.join("");
    gutter.innerHTML = numbers.join("");
    syncScroll();
  }

  function queueRender() {
    if (renderQueued) {
      return;
    }
    renderQueued = true;
    window.requestAnimationFrame(function () {
      renderQueued = false;
      renderEditor();
    });
  }

  function syncScroll() {
    var top = sourceEditor.scrollTop;
    var left = sourceEditor.scrollLeft;
    gutter.style.transform = "translateY(" + -top + "px)";
    highlightLayer.style.transform = "translate(" + -left + "px," + -top + "px)";
  }

  function updateSourceMeta() {
    var value = sourceEditor.value;
    var lines = value.length === 0 ? 1 : value.split("\n").length;
    var parts = [];
    if (state.filename) {
      parts.push(state.filename);
    }
    parts.push(value.length.toLocaleString("en-US") + " 字符");
    parts.push(lines.toLocaleString("en-US") + " 行");
    sourceMeta.textContent = parts.join(" · ");
  }

  /* ------------------------------------------------------------------ *
   * diagnostics
   * ------------------------------------------------------------------ */

  function makeIcon(iconName) {
    var namespace = "http://www.w3.org/2000/svg";
    var svg = document.createElementNS(namespace, "svg");
    var use = document.createElementNS(namespace, "use");
    svg.setAttribute("class", "icon");
    svg.setAttribute("aria-hidden", "true");
    use.setAttribute("href", "#" + iconName);
    svg.appendChild(use);
    return svg;
  }

  function setDiagnosticItems(items) {
    var overall = "ok";
    diagList.textContent = "";

    items.forEach(function (item) {
      var kind = item.kind || "";
      var row = document.createElement("div");
      var iconWrap = document.createElement("span");
      var text = document.createElement("span");
      var hasLocation = item.line || (item.index !== undefined && item.index !== null);

      row.className = "diag-item" + (kind ? " " + kind : "");
      iconWrap.className = "diag-icon";
      iconWrap.appendChild(makeIcon(item.icon || "i-info"));
      text.className = "diag-text";
      text.textContent = item.message || "";
      text.title = item.message || "";
      row.appendChild(iconWrap);
      row.appendChild(text);

      if (hasLocation) {
        var jump = document.createElement("button");
        jump.type = "button";
        jump.className = "diag-jump";
        jump.title = "定位到第 " + (item.line || "?") + " 行";
        jump.appendChild(makeIcon("i-target"));
        jump.appendChild(document.createTextNode("定位"));
        jump.addEventListener("click", function () {
          jumpToDiagnostic(item.line, item.column, item.index);
        });
        row.appendChild(jump);
      }

      if (kind === "error") {
        overall = "error";
      } else if (kind === "warn" && overall !== "error") {
        overall = "warn";
      }
      diagList.appendChild(row);
    });

    diagnostics.classList.remove("ok", "error", "warn");
    diagnostics.classList.add(overall);
  }

  function setDiagnostics(message, kind, iconName, line, column, index) {
    setDiagnosticItems([{
      message: message,
      kind: kind,
      icon: iconName,
      line: line,
      column: column,
      index: index
    }]);
  }

  function indexFromPosition(source, line, column) {
    if (!line) {
      return -1;
    }
    var lines = source.split("\n");
    var index = 0;
    for (var i = 0; i < line - 1 && i < lines.length; i += 1) {
      index += lines[i].length + 1;
    }
    return index + Math.max(0, column || 0);
  }

  function describeError(error) {
    var message = error && error.message ? error.message : String(error);
    if (error && error.line) {
      message = "第 " + error.line + " 行 第 " + ((error.column || 0) + 1) + " 列 · " + message;
    }
    return message;
  }

  function describeWarning(warning) {
    var message = warning && warning.message ? warning.message : "ESTK 兼容调整";
    if (warning && warning.line) {
      message = "第 " + warning.line + " 行 第 " + ((warning.column || 0) + 1) + " 列 · " + message;
    }
    return message;
  }

  function validate() {
    var source = sourceEditor.value;
    if (!engineReady) {
      return false;
    }
    if (!source.trim()) {
      state.hasError = false;
      state.errorLine = 0;
      state.errorIndex = -1;
      state.warnings = [];
      setDiagnostics("等待输入，将自动进行语法检测。", "", "i-info");
      queueRender();
      return false;
    }

    var result;
    try {
      result = window.EstkVmBrowser.check(source, {
        filename: state.filename || "<browser>"
      });
    } catch (error) {
      result = { ok: false, error: { message: error && error.message ? error.message : String(error) } };
    }

    if (!result.ok) {
      var failures = result.errors && result.errors.length ? result.errors : [result.error || {}];
      var failure = failures[0] || {};
      var errorItems = failures.map(function (error) {
        return {
          message: describeError(error),
          kind: "error",
          icon: "i-alert",
          line: error.line || 0,
          column: error.column || 0,
          index: error.index !== undefined ? error.index : indexFromPosition(source, error.line, error.column)
        };
      });
      var warningItems = (result.warnings || []).map(function (warning) {
        return {
          message: describeWarning(warning),
          kind: "warn",
          icon: "i-info",
          line: warning.line || 0,
          column: warning.column || 0,
          index: warning.index
        };
      });
      state.hasError = true;
      state.errorLine = failure.line || 0;
      state.errorIndex = failure.index !== undefined ? failure.index : indexFromPosition(source, failure.line, failure.column);
      state.warnings = result.warnings || [];
      setDiagnosticItems(errorItems.concat(warningItems));
      queueRender();
      return false;
    }

    state.hasError = false;
    state.errorLine = 0;
    state.errorIndex = -1;
    state.warnings = result.warnings || [];
    if (state.warnings.length) {
      setDiagnosticItems(state.warnings.map(function (warning) {
        return {
          message: describeWarning(warning),
          kind: "warn",
          icon: "i-info",
          line: warning.line || 0,
          column: warning.column || 0,
          index: warning.index
        };
      }));
      queueRender();
      return true;
    }

    var note = "语法检测通过";
    if (result.directives && result.directives.length) {
      note += " · 已提取 " + result.directives.length + " 条 #target 指令";
    }
    setDiagnostics(note + "，可以生成加密 JSX。", "ok", "i-check");
    queueRender();
    return true;
  }

  function scheduleValidation() {
    if (validateTimer) {
      window.clearTimeout(validateTimer);
    }
    validateTimer = window.setTimeout(validate, VALIDATE_DELAY);
  }

  function jumpToDiagnostic(line, column, index) {
    var value = sourceEditor.value;
    var start = index !== undefined && index !== null && index >= 0
      ? index
      : indexFromPosition(value, line, column);

    if (start < 0) {
      return;
    }

    var end = start;
    while (end < value.length && !/[\s;,()[\]{}]/.test(value.charAt(end))) {
      end += 1;
    }
    if (end === start) {
      end = Math.min(value.length, start + 1);
    }

    sourceEditor.focus();
    sourceEditor.scrollTop = Math.max(0, (line - 1) * lineHeight() - 60);
    sourceEditor.setSelectionRange(start, end);
    syncScroll();
  }

  /* ------------------------------------------------------------------ *
   * editing
   * ------------------------------------------------------------------ */

  function handleInput() {
    state.dirty = true;
    state.errorLine = 0;
    state.errorIndex = -1;
    updateSourceMeta();
    setDiagnostics("正在检测语法…", "", "i-info");
    queueRender();
    scheduleValidation();
    scheduleSave();
  }

  function scheduleSave() {
    if (saveTimer) {
      window.clearTimeout(saveTimer);
    }
    saveTimer = window.setTimeout(function () {
      storageSet("source", sourceEditor.value);
      storageSet("filename", state.filename);
      state.dirty = false;
    }, SAVE_DELAY);
  }

  function loadText(text, filename) {
    sourceEditor.value = String(text || "").replace(/\r\n?/g, "\n");
    state.filename = filename || "";
    sourceEditor.scrollTop = 0;
    sourceEditor.scrollLeft = 0;
    updateSourceMeta();
    handleInput();
  }

  function readFile(file) {
    var reader = new FileReader();
    reader.onload = function () {
      var name = file.name || "";
      outputName.value = sanitizeFilename(name.replace(/\.[^.]+$/, "") + ".protected.jsx");
      loadText(reader.result, name);
      setBuildStatus("已载入 " + name, "");
    };
    reader.onerror = function () {
      setDiagnostics("无法读取文件：" + (file.name || "未知文件"), "error", "i-alert");
    };
    reader.readAsText(file, "utf-8");
  }

  function applyIndent(outdent) {
    var value = sourceEditor.value;
    var start = sourceEditor.selectionStart;
    var end = sourceEditor.selectionEnd;
    var lineStart = value.lastIndexOf("\n", start - 1) + 1;
    var lineEnd = value.indexOf("\n", end);
    if (lineEnd < 0) {
      lineEnd = value.length;
    }
    var lines = value.slice(lineStart, lineEnd).split("\n");
    var changed = [];
    var firstDelta = 0;
    var totalDelta = 0;
    for (var i = 0; i < lines.length; i += 1) {
      var delta = 0;
      if (outdent) {
        var removed = 0;
        while (removed < 2 && lines[i].charAt(removed) === " ") {
          removed += 1;
        }
        changed.push(lines[i].slice(removed));
        delta = -removed;
      } else {
        changed.push("  " + lines[i]);
        delta = 2;
      }
      if (i === 0) {
        firstDelta = delta;
      }
      totalDelta += delta;
    }
    sourceEditor.setRangeText(changed.join("\n"), lineStart, lineEnd, "select");
    sourceEditor.setSelectionRange(
      Math.max(lineStart, start + firstDelta),
      Math.max(lineStart, end + totalDelta)
    );
    handleInput();
  }

  /* ------------------------------------------------------------------ *
   * layout: splitter
   * ------------------------------------------------------------------ */

  function applySplit(percent, persist) {
    var clamped = Math.min(SPLIT_MAX, Math.max(SPLIT_MIN, percent));
    state.split = clamped;
    if (window.matchMedia(NARROW_QUERY).matches) {
      workspace.style.gridTemplateColumns = "";
    } else {
      workspace.style.gridTemplateColumns =
        "minmax(0," + clamped + "%) " + SPLIT_GAP + "px minmax(0,1fr)";
    }
    if (persist) {
      storageSet("split", String(Math.round(clamped)));
    }
  }

  function bindSplitter() {
    var dragging = false;

    function percentAt(clientX) {
      var rect = workspace.getBoundingClientRect();
      var styles = window.getComputedStyle(workspace);
      var padLeft = parseFloat(styles.paddingLeft) || 0;
      var padRight = parseFloat(styles.paddingRight) || 0;
      var width = rect.width - padLeft - padRight;
      if (width <= 0) {
        return state.split;
      }
      return ((clientX - rect.left - padLeft) / width) * 100;
    }

    splitter.addEventListener("pointerdown", function (event) {
      if (window.matchMedia(NARROW_QUERY).matches) {
        return;
      }
      dragging = true;
      splitter.classList.add("active");
      document.body.classList.add("resizing");
      if (splitter.setPointerCapture) {
        splitter.setPointerCapture(event.pointerId);
      }
      applySplit(percentAt(event.clientX), false);
      event.preventDefault();
    });

    splitter.addEventListener("pointermove", function (event) {
      if (!dragging) {
        return;
      }
      applySplit(percentAt(event.clientX), false);
    });

    function finish() {
      if (!dragging) {
        return;
      }
      dragging = false;
      splitter.classList.remove("active");
      document.body.classList.remove("resizing");
      applySplit(state.split, true);
    }

    splitter.addEventListener("pointerup", finish);
    splitter.addEventListener("pointercancel", finish);
    splitter.addEventListener("keydown", function (event) {
      var step = event.shiftKey ? 10 : 2;
      if (event.key === "ArrowLeft") {
        applySplit(state.split - step, true);
        event.preventDefault();
      } else if (event.key === "ArrowRight") {
        applySplit(state.split + step, true);
        event.preventDefault();
      }
    });

    window.addEventListener("resize", function () {
      applySplit(state.split, false);
    });
  }

  /* ------------------------------------------------------------------ *
   * result pane
   * ------------------------------------------------------------------ */

  function setBuildStatus(message, kind) {
    buildStatus.classList.remove("ok", "bad");
    if (kind) {
      buildStatus.classList.add(kind);
    }
    buildStatus.textContent = message;
  }

  function setStatsEmpty(message) {
    statsOutput.textContent = "";
    var span = document.createElement("span");
    span.className = "stat empty";
    span.textContent = message;
    statsOutput.appendChild(span);
  }

  function setStats(items) {
    statsOutput.textContent = "";
    for (var i = 0; i < items.length; i += 1) {
      var item = items[i];
      var span = document.createElement("span");
      span.className = "stat";
      if (item.icon) {
        var svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
        svg.setAttribute("class", "icon");
        var use = document.createElementNS("http://www.w3.org/2000/svg", "use");
        use.setAttribute("href", "#" + item.icon);
        svg.appendChild(use);
        span.appendChild(svg);
      }
      span.appendChild(document.createTextNode(item.label + " "));
      var value = document.createElement("b");
      value.textContent = item.value;
      span.appendChild(value);
      statsOutput.appendChild(span);
    }
  }

  function setResult(code) {
    state.code = code;
    resultOutput.textContent = code;
    resultOutput.classList.remove("placeholder");
    copyButton.disabled = false;
    downloadButton.disabled = false;
  }

  function clearResult(message) {
    state.code = "";
    resultOutput.textContent = message;
    resultOutput.classList.add("placeholder");
    copyButton.disabled = true;
    downloadButton.disabled = true;
    setStatsEmpty("尚未构建");
    setBuildStatus("等待生成", "");
  }

  async function build() {
    if (state.building || !engineReady) {
      return;
    }
    var source = sourceEditor.value;
    if (!source.trim()) {
      setDiagnostics("请先载入或粘贴 JSX 源码。", "error", "i-alert");
      setBuildStatus("等待输入", "bad");
      return;
    }
    if (!validate()) {
      setBuildStatus("源码存在语法问题", "bad");
      return;
    }

    state.building = true;
    buildButton.disabled = true;
    var label = buildButton.querySelector("span");
    if (label) {
      label.textContent = "正在生成…";
    }
    setBuildStatus("正在编译并加密…", "");
    var started = window.performance && performance.now ? performance.now() : Date.now();

    try {
      var result = await window.EstkVmBrowser.build(source, {
        key: keyInput.value,
        seed: seedInput.value,
        protection: currentProtection(),
        filename: state.filename || "<browser>"
      });
      var elapsed = (window.performance && performance.now ? performance.now() : Date.now()) - started;
      setResult(result.code);
      var stats = result.stats;
      setStats([
        { icon: "i-layers", label: "函数", value: String(stats.functions) },
        { icon: "i-zap", label: "指令", value: stats.instructions.toLocaleString("en-US") },
        { icon: "i-file-code", label: "字节码", value: formatBytes(stats.bytecodeBytes) },
        { icon: "i-lock", label: "加密后", value: formatBytes(stats.encryptedBytes) },
        { icon: "i-target", label: "源码", value: formatBytes(stats.sourceBytes) },
        { icon: "i-shield", label: "保护", value: protectionLabel(stats.protection) },
        { icon: "i-key", label: "指纹", value: fingerprintHex(stats.fingerprint) },
        { icon: "i-shield", label: "耗时", value: elapsed.toFixed(1) + " ms" }
      ]);
      setBuildStatus("生成成功 · " + outputName.value, "ok");
      storageSet("key", keyInput.value);
      storageSet("seed", seedInput.value);
      storageSet("outputName", outputName.value);
      storageSet("protection", currentProtection());
    } catch (error) {
      clearResult("生成失败：" + describeError(error));
      setDiagnostics(describeError(error), "error", "i-alert");
      setBuildStatus("生成失败", "bad");
    } finally {
      state.building = false;
      buildButton.disabled = false;
      if (label) {
        label.textContent = "生成加密 JSX";
      }
    }
  }

  function downloadResult() {
    if (!state.code) {
      return;
    }
    var url = URL.createObjectURL(
      new Blob([state.code], { type: "text/javascript;charset=utf-8" })
    );
    var anchor = document.createElement("a");
    anchor.href = url;
    anchor.download = sanitizeFilename(outputName.value);
    document.body.appendChild(anchor);
    anchor.click();
    document.body.removeChild(anchor);
    window.setTimeout(function () {
      URL.revokeObjectURL(url);
    }, 1500);
    setBuildStatus("已下载 " + anchor.download, "ok");
  }

  async function copyResult() {
    if (!state.code) {
      return;
    }
    var copied = false;
    try {
      await navigator.clipboard.writeText(state.code);
      copied = true;
    } catch (error) {
      var helper = document.createElement("textarea");
      helper.value = state.code;
      helper.setAttribute("readonly", "readonly");
      helper.style.position = "fixed";
      helper.style.opacity = "0";
      document.body.appendChild(helper);
      helper.select();
      try {
        copied = document.execCommand("copy");
      } catch (inner) {
        copied = false;
      }
      document.body.removeChild(helper);
    }
    copyButton.setAttribute("data-tip", copied ? "已复制" : "复制失败");
    setBuildStatus(copied ? "已复制到剪贴板" : "浏览器未允许剪贴板访问", copied ? "ok" : "bad");
    window.setTimeout(function () {
      copyButton.setAttribute("data-tip", "复制加密代码");
    }, 1600);
  }

  function randomSeed() {
    var bytes = new Uint8Array(4);
    if (window.crypto && window.crypto.getRandomValues) {
      window.crypto.getRandomValues(bytes);
    } else {
      for (var i = 0; i < bytes.length; i += 1) {
        bytes[i] = Math.floor(Math.random() * 256);
      }
    }
    var hex = "";
    for (var j = 0; j < bytes.length; j += 1) {
      hex += ("0" + bytes[j].toString(16)).slice(-2);
    }
    seedInput.value = hex;
    storageSet("seed", hex);
    setBuildStatus("已生成随机种子 " + hex, "");
  }

  function toggleKeyVisibility() {
    var visible = keyInput.type === "text";
    keyInput.type = visible ? "password" : "text";
    keyIconUse.setAttribute("href", visible ? "#i-eye" : "#i-eye-off");
    toggleKeyButton.title = visible ? "显示密钥" : "隐藏密钥";
    toggleKeyButton.setAttribute("aria-label", toggleKeyButton.title);
    storageSet("keyVisible", visible ? "0" : "1");
  }

  /* ------------------------------------------------------------------ *
   * wiring
   * ------------------------------------------------------------------ */

  function bindEvents() {
    sourceEditor.addEventListener("input", handleInput);
    sourceEditor.addEventListener("scroll", syncScroll);
    sourceEditor.addEventListener("keydown", function (event) {
      if (event.key === "Tab") {
        event.preventDefault();
        var multiLine =
          sourceEditor.selectionStart !== sourceEditor.selectionEnd &&
          sourceEditor.value
            .slice(sourceEditor.selectionStart, sourceEditor.selectionEnd)
            .indexOf("\n") >= 0;
        if (multiLine || event.shiftKey) {
          applyIndent(event.shiftKey);
        } else {
          sourceEditor.setRangeText(
            "  ",
            sourceEditor.selectionStart,
            sourceEditor.selectionEnd,
            "end"
          );
          handleInput();
        }
      }
    });

    document.addEventListener("keydown", function (event) {
      var mod = event.ctrlKey || event.metaKey;
      if (!mod) {
        return;
      }
      if (event.key === "Enter") {
        event.preventDefault();
        build();
      } else if (event.key === "s" || event.key === "S") {
        event.preventDefault();
        if (state.code) {
          downloadResult();
        } else {
          build();
        }
      }
    });

    loadButton.addEventListener("click", function () {
      fileInput.click();
    });

    fileInput.addEventListener("change", function () {
      if (fileInput.files && fileInput.files[0]) {
        readFile(fileInput.files[0]);
      }
      fileInput.value = "";
    });

    clearButton.addEventListener("click", function () {
      state.filename = "";
      sourceEditor.value = "";
      clearResult("生成后将在这里显示完整的加密 JSX。");
      setDiagnostics("编辑器已清空。", "", "i-info");
      handleInput();
      sourceEditor.focus();
    });

    buildButton.addEventListener("click", build);
    copyButton.addEventListener("click", copyResult);
    downloadButton.addEventListener("click", downloadResult);
    randomSeedButton.addEventListener("click", randomSeed);
    toggleKeyButton.addEventListener("click", toggleKeyVisibility);

    keyInput.addEventListener("change", function () {
      storageSet("key", keyInput.value);
    });
    seedInput.addEventListener("change", function () {
      storageSet("seed", seedInput.value);
    });
    outputName.addEventListener("change", function () {
      outputName.value = sanitizeFilename(outputName.value);
      storageSet("outputName", outputName.value);
    });
    protectionSelect.addEventListener("change", function () {
      var level = currentProtection();
      protectionSelect.value = level;
      storageSet("protection", level);
      if (state.code && validate()) {
        build();
      }
    });

    ["dragenter", "dragover"].forEach(function (type) {
      dropZone.addEventListener(type, function (event) {
        event.preventDefault();
        if (event.dataTransfer) {
          event.dataTransfer.dropEffect = "copy";
        }
        dropZone.classList.add("dragging");
      });
    });

    ["dragleave", "dragend", "drop"].forEach(function (type) {
      dropZone.addEventListener(type, function (event) {
        event.preventDefault();
        if (type === "dragleave" && dropZone.contains(event.relatedTarget)) {
          return;
        }
        dropZone.classList.remove("dragging");
      });
    });

    dropZone.addEventListener("drop", function (event) {
      var files = event.dataTransfer && event.dataTransfer.files;
      if (files && files[0]) {
        readFile(files[0]);
      }
    });

    window.addEventListener("dragover", function (event) {
      event.preventDefault();
    });
    window.addEventListener("drop", function (event) {
      event.preventDefault();
    });
  }

  function restoreState() {
    var savedKey = storageGet("key");
    if (savedKey !== null) {
      keyInput.value = savedKey;
    }
    var savedSeed = storageGet("seed");
    if (savedSeed !== null) {
      seedInput.value = savedSeed;
    }
    var savedName = storageGet("outputName");
    if (savedName) {
      outputName.value = sanitizeFilename(savedName);
    }
    var savedProtection = storageGet("protection");
    if (savedProtection && hasOwn(PROTECTION_LABELS, savedProtection)) {
      protectionSelect.value = savedProtection;
    }
    if (storageGet("keyVisible") === "1") {
      toggleKeyVisibility();
    }
    var savedSplit = parseFloat(storageGet("split"));
    applySplit(savedSplit > 0 ? savedSplit : 50, false);

    var savedSource = storageGet("source");
    if (savedSource) {
      state.filename = storageGet("filename") || "";
      sourceEditor.value = savedSource.replace(/\r\n?/g, "\n");
      updateSourceMeta();
    }
  }

  function checkEngine() {
    var missing = [];
    if (!window.acorn) {
      missing.push("acorn");
    }
    if (!window.EstkVmCompiler) {
      missing.push("compiler");
    }
    if (!window.EstkVmCipher) {
      missing.push("cipher");
    }
    if (!window.EstkVmBytecode) {
      missing.push("bytecode");
    }
    if (!window.EstkVmBrowser) {
      missing.push("vm-builder");
    }
    if (!window.ESTK_VM_RUNTIME_TEMPLATE) {
      missing.push("runtime-template");
    }
    if (missing.length) {
      engineReady = false;
      engineStatus.classList.add("bad");
      engineText.textContent = "引擎缺失：" + missing.join(", ");
      setBuildStatus("构建引擎加载失败", "bad");
      setDiagnostics("构建脚本未能全部载入，请通过本地服务器打开本页面。", "error", "i-alert");
      buildButton.disabled = true;
      return false;
    }
    engineReady = true;
    engineStatus.classList.remove("bad");
    engineText.textContent = "引擎就绪";
    return true;
  }

  function init() {
    bindSplitter();
    bindEvents();
    restoreState();
    checkEngine();
    renderEditor();
    updateSourceMeta();
    if (sourceEditor.value.trim()) {
      scheduleValidation();
    } else {
      setDiagnostics("等待输入，将自动进行语法检测。", "", "i-info");
      clearResult("生成后将在这里显示完整的加密 JSX。");
    }
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
