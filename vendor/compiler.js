(function (root, factory) {
  if (typeof module === "object" && module.exports) {
    module.exports = factory(require("acorn"), require("./opcodes").OP);
  } else {
    root.EstkVmCompiler = factory(root.acorn, root.EstkVmOpcodes.OP);
  }
})(typeof globalThis !== "undefined" ? globalThis : this, function (acorn, OP) {
  "use strict";

const BINARY_OPERATORS = new Set([
  "==",
  "!=",
  "===",
  "!==",
  "<",
  "<=",
  ">",
  ">=",
  "<<",
  ">>",
  ">>>",
  "+",
  "-",
  "*",
  "/",
  "%",
  "|",
  "^",
  "&",
  "in",
  "instanceof"
]);

const UNARY_OPERATORS = new Set(["-", "+", "!", "~", "typeof", "void"]);

const BINARY_OPCODES = {
  "+": OP.BINARY_ADD,
  "-": OP.BINARY_SUB,
  "*": OP.BINARY_MUL,
  "/": OP.BINARY_DIV,
  "%": OP.BINARY_MOD,
  "<": OP.BINARY_LT,
  "<=": OP.BINARY_LE,
  ">": OP.BINARY_GT,
  ">=": OP.BINARY_GE,
  "==": OP.BINARY_EQ,
  "!=": OP.BINARY_NE,
  "===": OP.BINARY_SEQ,
  "!==": OP.BINARY_SNE,
  "<<": OP.BINARY_LSHIFT,
  ">>": OP.BINARY_RSHIFT,
  ">>>": OP.BINARY_URSHIFT,
  "|": OP.BINARY_BIT_OR,
  "^": OP.BINARY_BIT_XOR,
  "&": OP.BINARY_BIT_AND,
  "in": OP.BINARY_IN,
  "instanceof": OP.BINARY_INSTANCEOF
};

const UNARY_OPCODES = {
  "+": OP.UNARY_PLUS,
  "-": OP.UNARY_MINUS,
  "!": OP.UNARY_NOT,
  "~": OP.UNARY_BITNOT
};

/*
 * ExtendScript accepts a few constructs that the strict ES5 parser does not,
 * most notably const declarations and trailing commas in an argument list.
 * Tokenize first so comments and string literals are never rewritten, then
 * apply the smallest possible compatibility edits before parsing.
 */
function tokenList(parser, source) {
  var tokens = [];
  var token;
  var i;

  if (!parser) {
    return null;
  }

  try {
    if (typeof parser.tokenizer === "function") {
      var stream = parser.tokenizer(source, {
        ecmaVersion: 5,
        allowReserved: true,
        locations: true
      });
      for (;;) {
        token = stream.getToken();
        if (!token || (token.type && token.type.label === "eof")) {
          break;
        }
        tokens.push({
          value: token.value === undefined && token.type ? token.type.label : token.value,
          start: token.start,
          end: token.end
        });
      }
      return tokens;
    }

    if (typeof parser.tokenize === "function") {
      var raw = parser.tokenize(source, {
        comment: false,
        loc: true,
        range: true
      });
      for (i = 0; i < raw.length; i += 1) {
        tokens.push({
          value: raw[i].value,
          start: raw[i].range[0],
          end: raw[i].range[1]
        });
      }
      return tokens;
    }
  } catch (ignoreTokenize) {
    /* The main parser reports malformed source with its normal diagnostics. */
  }

  return null;
}

function positionAt(source, index) {
  var line = 1;
  var lineStart = 0;
  var i;
  for (i = 0; i < index && i < source.length; i += 1) {
    if (source.charCodeAt(i) === 10) {
      line += 1;
      lineStart = i + 1;
    }
  }
  return {
    line: line,
    column: index - lineStart
  };
}

function isIdentifierName(value) {
  return typeof value === "string" && /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(value);
}

var CONTROL_PAREN_KEYWORDS = {
  if: true,
  for: true,
  while: true,
  switch: true,
  catch: true,
  with: true,
  return: true,
  throw: true,
  typeof: true,
  void: true,
  delete: true,
  new: true,
  in: true,
  instanceof: true,
  do: true,
  else: true,
  case: true
};

function isCallParen(tokens, openIndex) {
  var before;
  if (openIndex <= 0 || openIndex >= tokens.length) {
    return false;
  }
  before = tokens[openIndex - 1].value;
  if (CONTROL_PAREN_KEYWORDS[before]) {
    return false;
  }
  return (
    isIdentifierName(before) ||
    before === "function" ||
    before === ")" ||
    before === "]" ||
    before === "}"
  );
}

function normalizeExtendScript(source, parser) {
  var tokens = tokenList(parser, source);
  var edits = [];
  var warnings = [];
  var i;
  var token;
  var previous;
  var next;
  var position;
  var openParents = [];
  var openStack = [];

  if (tokens === null) {
    return {
      code: source,
      warnings: warnings
    };
  }

  for (i = 0; i < tokens.length; i += 1) {
    if (tokens[i].value === "(") {
      openStack.push(i);
    } else if (tokens[i].value === ")") {
      openParents[i] = openStack.length ? openStack.pop() : -1;
    }
  }

  for (i = 0; i < tokens.length; i += 1) {
    token = tokens[i];
    previous = i > 0 ? tokens[i - 1] : null;
    next = i + 1 < tokens.length ? tokens[i + 1] : null;

    /*
     * ESTK treats const as a function-scoped binding. The VM has no block
     * scope for local declarations, so compiling it as var preserves the
     * behavior scripts already rely on.
     */
    if (
      token.value === "const" &&
      (!previous || (previous.value !== "." && previous.value !== "?.")) &&
      next &&
      (isIdentifierName(next.value) || next.value === "[" || next.value === "{")
    ) {
      edits.push({
        start: token.start,
        end: token.end,
        text: "var  "
      });
      continue;
    }

    /*
     * Acorn rejects call(a, b,), while ExtendScript accepts it and simply
     * ignores the final comma. Removing it is a safe, local repair.
     */
    if (
      token.value === "," &&
      next &&
      next.value === ")" &&
      previous &&
      previous.value !== "(" &&
      previous.value !== "[" &&
      previous.value !== "{" &&
      previous.value !== "," &&
      openParents[i + 1] !== undefined &&
      openParents[i + 1] >= 0 &&
      isCallParen(tokens, openParents[i + 1])
    ) {
      edits.push({
        start: token.start,
        end: token.end,
        text: ""
      });
      position = positionAt(source, token.start);
      warnings.push({
        code: "ESTK_TRAILING_COMMA",
        message: "参数列表末尾多余的逗号已按 ESTK 规则忽略。",
        line: position.line,
        column: position.column,
        index: token.start
      });
    }
  }

  if (edits.length === 0) {
    return {
      code: source,
      warnings: warnings
    };
  }

  edits.sort(function (left, right) {
    return left.start - right.start;
  });

  var output = "";
  var cursor = 0;
  for (i = 0; i < edits.length; i += 1) {
    var edit = edits[i];
    if (edit.start < cursor) {
      continue;
    }
    output += source.slice(cursor, edit.start) + edit.text;
    cursor = edit.end;
  }
  output += source.slice(cursor);

  return {
    code: output,
    warnings: warnings
  };
}

function parseSource(parser, source) {
  return parser.parse(source, {
    ecmaVersion: 5,
    sourceType: "script",
    allowReserved: true,
    locations: true
  });
}

function cleanSyntaxMessage(message) {
  var text = String(message || "");
  text = text.replace(/\s*\(\d+:\d+\)\s*$/, "");
  text = text.replace(/^Line \d+:\s*/, "");
  return text;
}

function normalizeDiagnostic(error) {
  var loc = error && error.loc ? error.loc : {};
  return {
    message: cleanSyntaxMessage(error && error.message ? error.message : String(error)),
    line: error && error.lineNumber !== undefined ? error.lineNumber : (loc.line || null),
    column: error && error.column !== undefined ? error.column : (loc.column || 0),
    index: error && error.pos !== undefined ? error.pos :
      (error && error.index !== undefined ? error.index : null)
  };
}

function maskSourceLine(source, line) {
  var lines = source.split("\n");
  if (line < 1 || line > lines.length) {
    return source;
  }
  lines[line - 1] = lines[line - 1].replace(/[^\r\n]/g, " ");
  return lines.join("\n");
}

/*
 * Acorn stops at the first syntax error. Mask one failing line at a time and
 * retry so the editor can show independent errors from later statements. This
 * is best-effort recovery, not a replacement for the strict compile pass.
 */
function collectSyntaxErrors(parser, source, limit) {
  var errors = [];
  var masked = source;
  var maskedLines = {};
  var attempts = 0;
  var maximum = limit || 12;
  var diagnostic;
  var next;

  while (attempts < maximum) {
    attempts += 1;
    try {
      parseSource(parser, masked);
      break;
    } catch (error) {
      diagnostic = normalizeDiagnostic(error);
      errors.push(diagnostic);
      if (!diagnostic.line || maskedLines[diagnostic.line]) {
        break;
      }
      maskedLines[diagnostic.line] = true;
      next = maskSourceLine(masked, diagnostic.line);
      if (next === masked) {
        break;
      }
      masked = next;
    }
  }

  return errors;
}

class Compiler {
  constructor(source, options = {}) {
    this.source = source;
    this.options = options;
    this.parser = options.parser || acorn;
    this.functions = [];
    this.functionIds = new WeakMap();
    this.functionNodes = [];
    this.current = null;
    this.controls = [];
    this.tempDepth = 0;
    this.maxTemps = 0;
    this.tryDepth = 0;
    this.finallyDepth = 0;
    this.warnings = [];
  }

  compile() {
    const compatibility = normalizeExtendScript(this.source, this.parser);
    this.source = compatibility.code;
    this.warnings = compatibility.warnings;

    const ast = parseSource(this.parser, this.source);

    this.prepareFunctions(ast);
    for (const node of this.functionNodes) {
      this.compileFunction(node);
    }

    return {
      functions: this.functions,
      ast,
      warnings: this.warnings.slice(),
      source: this.source
    };
  }

  diagnose() {
    const compatibility = normalizeExtendScript(this.source, this.parser);
    this.source = compatibility.code;
    this.warnings = compatibility.warnings.slice();

    const errors = collectSyntaxErrors(this.parser, this.source, 12);
    if (errors.length === 0) {
      try {
        this.compile();
      } catch (error) {
        errors.push(normalizeDiagnostic(error));
      }
    }

    this.warnings = compatibility.warnings.slice();
    return {
      errors,
      warnings: this.warnings.slice()
    };
  }

  prepareFunctions(ast) {
    const programMeta = this.createMeta({
      id: 0,
      name: "@main",
      params: [],
      selfName: "",
      node: ast,
      isProgram: true
    });
    this.functionIds.set(ast, 0);
    this.functionNodes.push(ast);
    this.functions.push(programMeta);

    this.discoverFunctions(ast, programMeta);

    for (const statement of ast.body) {
      this.collectDeclarations(statement, programMeta, ast);
    }
    for (let i = 1; i < this.functionNodes.length; i += 1) {
      const node = this.functionNodes[i];
      const meta = this.functions[i];
      for (const statement of node.body.body) {
        this.collectDeclarations(statement, meta, node);
      }
    }
  }

  createMeta({ id, name, params, selfName, node, isProgram }) {
    return {
      id,
      name: name || "",
      params: params.slice(),
      selfName: selfName || "",
      vars: [],
      decls: [],
      code: [],
      maxTemps: 0,
      isProgram: Boolean(isProgram),
      node
    };
  }

  discoverFunctions(node, parentMeta) {
    if (!node || typeof node.type !== "string") {
      return;
    }

    if (node.type === "FunctionDeclaration" || node.type === "FunctionExpression") {
      const id = this.functions.length;
      const params = node.params.map((param) => this.identifierName(param));
      const selfName =
        node.type === "FunctionExpression" && node.id
          ? node.id.name
          : node.type === "FunctionDeclaration" && node.id
            ? node.id.name
            : "";
      const meta = this.createMeta({
        id,
        name: node.id ? node.id.name : "",
        params,
        selfName: node.type === "FunctionExpression" ? selfName : "",
        node,
        isProgram: false
      });
      this.functionIds.set(node, id);
      this.functionNodes.push(node);
      this.functions.push(meta);
    }

    for (const key of Object.keys(node)) {
      if (key === "type" || key === "start" || key === "end" || key === "loc") {
        continue;
      }
      const child = node[key];
      if (Array.isArray(child)) {
        for (const entry of child) {
          if (entry && typeof entry.type === "string") {
            this.discoverFunctions(entry, parentMeta);
          }
        }
      } else if (child && typeof child.type === "string") {
        this.discoverFunctions(child, parentMeta);
      }
    }
  }

  collectDeclarations(node, meta, rootNode) {
    if (!node || typeof node.type !== "string") {
      return;
    }

    if (node.type === "FunctionDeclaration") {
      if (node !== rootNode && node.id) {
        this.addDecl(meta, node.id.name, this.functionIds.get(node));
      }
      return;
    }

    if (node.type === "FunctionExpression") {
      return;
    }

    if (node.type === "VariableDeclaration") {
      for (const declaration of node.declarations) {
        if (declaration.id && declaration.id.type === "Identifier") {
          this.addVar(meta, declaration.id.name);
        }
      }
      return;
    }

    if (node.type === "CatchClause") {
      this.collectDeclarations(node.body, meta, rootNode);
      return;
    }

    for (const key of Object.keys(node)) {
      if (key === "type" || key === "start" || key === "end" || key === "loc") {
        continue;
      }
      const child = node[key];
      if (Array.isArray(child)) {
        for (const entry of child) {
          if (entry && typeof entry.type === "string") {
            this.collectDeclarations(entry, meta, rootNode);
          }
        }
      } else if (child && typeof child.type === "string") {
        this.collectDeclarations(child, meta, rootNode);
      }
    }
  }

  addVar(meta, name) {
    if (meta.vars.indexOf(name) === -1) {
      meta.vars.push(name);
    }
  }

  addDecl(meta, name, functionId) {
    const existing = meta.decls.find((decl) => decl.name === name);
    if (existing) {
      existing.functionId = functionId;
      return;
    }
    meta.decls.push({ name, functionId });
  }

  compileFunction(node) {
    const meta = this.functions[this.functionIds.get(node)];
    this.current = meta;
    this.controls = [];
    this.tempDepth = 0;
    this.maxTemps = 0;
    this.tryDepth = 0;
    this.finallyDepth = 0;
    meta.code = [];

    if (meta.isProgram) {
      this.compileStatements(node.body);
    } else {
      this.addVar(meta, "arguments");
      this.compileStatements(node.body.body);
    }

    this.emit(OP.PUSH_UNDEFINED);
    this.emit(OP.RETURN);
    meta.maxTemps = this.maxTemps;
  }

  emit(opcode, ...operands) {
    const instruction = [opcode, ...operands];
    this.current.code.push(instruction);
    return this.current.code.length - 1;
  }

  patch(instructionIndex, operandIndex, value) {
    this.current.code[instructionIndex][operandIndex + 1] = value;
  }

  allocateTemp() {
    const slot = this.tempDepth;
    this.tempDepth += 1;
    this.maxTemps = Math.max(this.maxTemps, this.tempDepth);
    return slot;
  }

  releaseTemp() {
    this.tempDepth -= 1;
  }

  withTemp(callback) {
    const slot = this.allocateTemp();
    try {
      return callback(slot);
    } finally {
      this.releaseTemp();
    }
  }

  compileStatements(statements) {
    for (const statement of statements) {
      this.compileStatement(statement, []);
    }
  }

  compileBlock(block) {
    if (block && block.body) {
      this.compileStatements(block.body);
    }
  }

  compileStatement(node, labels) {
    if (!node) {
      return;
    }

    switch (node.type) {
      case "EmptyStatement":
      case "DebuggerStatement":
        return;

      case "BlockStatement":
        this.compileBlock(node);
        return;

      case "ExpressionStatement":
        this.compileExpression(node.expression);
        this.emit(OP.POP);
        return;

      case "VariableDeclaration":
        this.compileVariableDeclaration(node);
        return;

      case "FunctionDeclaration":
        return;

      case "IfStatement":
        this.compileIf(node);
        return;

      case "WhileStatement":
        this.compileWhile(node, labels);
        return;

      case "DoWhileStatement":
        this.compileDoWhile(node, labels);
        return;

      case "ForStatement":
        this.compileFor(node, labels);
        return;

      case "ForInStatement":
        this.compileForIn(node, labels);
        return;

      case "SwitchStatement":
        this.compileSwitch(node, labels);
        return;

      case "ReturnStatement":
        if (node.argument) {
          this.compileExpression(node.argument);
        } else {
          this.emit(OP.PUSH_UNDEFINED);
        }
        this.emit(OP.COMPLETE, "return", 0, "", this.tryDepth, this.finallyDepth);
        return;

      case "ThrowStatement":
        this.compileExpression(node.argument);
        this.emit(OP.THROW);
        return;

      case "TryStatement":
        this.compileTry(node);
        return;

      case "BreakStatement":
        this.compileBreak(node);
        return;

      case "ContinueStatement":
        this.compileContinue(node);
        return;

      case "LabeledStatement":
        this.compileLabeled(node, labels || []);
        return;

      case "WithStatement":
        throw this.error(node, "with statements are not supported by the VM");

      default:
        throw this.error(node, `Unsupported statement: ${node.type}`);
    }
  }

  compileVariableDeclaration(node) {
    for (const declaration of node.declarations) {
      if (!declaration.init) {
        continue;
      }
      this.compileExpression(declaration.init);
      if (declaration.id.type !== "Identifier") {
        throw this.error(declaration.id, "Destructuring declarations are not supported");
      }
      this.emit(OP.STORE_NAME, declaration.id.name);
      this.emit(OP.POP);
    }
  }

  compileIf(node) {
    this.compileExpression(node.test);
    const alternateJump = this.emit(OP.JMP_IF_FALSE, 0);
    this.compileStatement(node.consequent, []);

    if (node.alternate) {
      const endJump = this.emit(OP.JMP, 0);
      this.patch(alternateJump, 0, this.current.code.length);
      this.compileStatement(node.alternate, []);
      this.patch(endJump, 0, this.current.code.length);
    } else {
      this.patch(alternateJump, 0, this.current.code.length);
    }
  }

  compileWhile(node, labels) {
    const start = this.current.code.length;
    const context = this.pushControl({
      type: "loop",
      labels: labels || [],
      continueTarget: start,
      breakPatches: [],
      continuePatches: []
    });

    this.compileExpression(node.test);
    const exitJump = this.emit(OP.JMP_IF_FALSE, 0);
    this.compileStatement(node.body, []);
    this.emit(OP.JMP, start);

    const end = this.current.code.length;
    this.patch(exitJump, 0, end);
    this.popControl(context, end);
  }

  compileDoWhile(node, labels) {
    const start = this.current.code.length;
    const context = this.pushControl({
      type: "loop",
      labels: labels || [],
      continueTarget: 0,
      breakPatches: [],
      continuePatches: []
    });

    this.compileStatement(node.body, []);
    context.continueTarget = this.current.code.length;
    this.compileExpression(node.test);
    this.emit(OP.JMP_IF_TRUE, start);

    const end = this.current.code.length;
    this.popControl(context, end);
  }

  compileFor(node, labels) {
    if (node.init) {
      if (node.init.type === "VariableDeclaration") {
        this.compileVariableDeclaration(node.init);
      } else {
        this.compileExpression(node.init);
        this.emit(OP.POP);
      }
    }

    const testStart = this.current.code.length;
    let exitJump = -1;
    if (node.test) {
      this.compileExpression(node.test);
      exitJump = this.emit(OP.JMP_IF_FALSE, 0);
    }

    const context = this.pushControl({
      type: "loop",
      labels: labels || [],
      continueTarget: 0,
      breakPatches: [],
      continuePatches: []
    });

    this.compileStatement(node.body, []);

    context.continueTarget = this.current.code.length;
    if (node.update) {
      this.compileExpression(node.update);
      this.emit(OP.POP);
    }
    this.emit(OP.JMP, testStart);

    const end = this.current.code.length;
    if (exitJump !== -1) {
      this.patch(exitJump, 0, end);
    }
    this.popControl(context, end);
  }

  compileForIn(node, labels) {
    if (node.left.type === "VariableDeclaration" && node.left.declarations[0].init) {
      this.compileExpression(node.left.declarations[0].init);
      this.emit(OP.POP);
    }

    this.compileExpression(node.right);
    this.emit(OP.ENUM_INIT);

    const start = this.current.code.length;
    const context = this.pushControl({
      type: "loop",
      labels: labels || [],
      continueTarget: start,
      breakPatches: [],
      continuePatches: []
    });
    const next = this.emit(OP.ITER_NEXT, 0);

    if (node.left.type === "VariableDeclaration") {
      const declaration = node.left.declarations[0];
      if (!declaration || declaration.id.type !== "Identifier") {
        throw this.error(node.left, "Unsupported for-in declaration target");
      }
      this.emit(OP.STORE_NAME, declaration.id.name);
      this.emit(OP.POP);
    } else if (node.left.type === "Identifier") {
      this.emit(OP.STORE_NAME, node.left.name);
      this.emit(OP.POP);
    } else if (node.left.type === "MemberExpression") {
      this.withTemp((temp) => {
        this.emit(OP.SET_TEMP, temp);
        this.compileMemberReference(node.left);
        this.emit(OP.LOAD_TEMP, temp);
        this.emit(OP.SET_PROP);
        this.emit(OP.POP);
      });
    } else {
      throw this.error(node.left, "Unsupported for-in assignment target");
    }

    this.compileStatement(node.body, []);
    this.emit(OP.JMP, start);

    const end = this.current.code.length;
    this.patch(next, 0, end);
    this.popControl(context, end);
  }

  compileSwitch(node, labels) {
    this.compileExpression(node.discriminant);
    const temp = this.allocateTemp();
    this.emit(OP.SET_TEMP, temp);

    const testJumps = [];
    let defaultIndex = -1;
    for (let i = 0; i < node.cases.length; i += 1) {
      const switchCase = node.cases[i];
      if (!switchCase.test) {
        defaultIndex = i;
        continue;
      }
      this.emit(OP.LOAD_TEMP, temp);
      this.compileExpression(switchCase.test);
      this.emit(OP.BINARY_SEQ);
      testJumps.push({ caseIndex: i, instruction: this.emit(OP.JMP_IF_TRUE, 0) });
    }

    const defaultJump = this.emit(OP.JMP, 0);
    const context = this.pushControl({
      type: "switch",
      labels: labels || [],
      breakPatches: [],
      continuePatches: []
    });

    const casePositions = [];
    for (let i = 0; i < node.cases.length; i += 1) {
      casePositions[i] = this.current.code.length;
      this.compileStatements(node.cases[i].consequent);
    }

    const end = this.current.code.length;
    for (const testJump of testJumps) {
      this.patch(testJump.instruction, 0, casePositions[testJump.caseIndex]);
    }
    this.patch(defaultJump, 0, defaultIndex === -1 ? end : casePositions[defaultIndex]);
    this.popControl(context, end);
    this.releaseTemp();
  }

  compileTry(node) {
    const tryInstruction = this.emit(OP.TRY_BEGIN, -1, -1, -1);
    this.tryDepth += 1;
    if (node.finalizer) {
      this.finallyDepth += 1;
    }
    this.compileBlock(node.block);
    const tryNormal = this.emit(OP.TRY_NORMAL, node.finalizer ? 0 : -1, 0);

    let catchNormal = -1;
    if (node.handler) {
      const catchStart = this.current.code.length;
      this.patch(tryInstruction, 0, catchStart);

      const param = node.handler.param;
      if (param) {
        if (param.type !== "Identifier") {
          throw this.error(param, "Catch destructuring is not supported");
        }
        this.emit(OP.BIND_NAME, param.name);
        this.emit(OP.POP);
      }
      this.compileBlock(node.handler.body);
      this.emit(OP.POP_SCOPE);
      catchNormal = this.emit(OP.TRY_NORMAL, node.finalizer ? 0 : -1, 0);
    }

    this.tryDepth -= 1;
    if (node.finalizer) {
      this.finallyDepth -= 1;
    }

    let finallyStart = -1;
    if (node.finalizer) {
      finallyStart = this.current.code.length;
      this.patch(tryInstruction, 1, finallyStart);
      this.patch(tryNormal, 0, finallyStart);
      if (catchNormal !== -1) {
        this.patch(catchNormal, 0, finallyStart);
      }
      this.compileBlock(node.finalizer);
      this.emit(OP.END_FINALLY);
    }

    const end = this.current.code.length;
    this.patch(tryInstruction, 2, end);
    this.patch(tryNormal, 1, end);
    if (catchNormal !== -1) {
      this.patch(catchNormal, 1, end);
    }
  }

  compileBreak(node) {
    const label = node.label ? node.label.name : "";
    const context = this.findBreakContext(label);
    if (!context) {
      throw this.error(node, label ? `Unknown break label: ${label}` : "break used outside a loop or switch");
    }
    const instruction = this.emit(
      OP.COMPLETE,
      "break",
      0,
      label,
      this.tryDepth - context.tryDepth,
      this.finallyDepth - context.finallyDepth
    );
    context.breakPatches.push(instruction);
  }

  compileContinue(node) {
    const label = node.label ? node.label.name : "";
    const context = this.findContinueContext(label);
    if (!context) {
      throw this.error(node, label ? `Unknown continue label: ${label}` : "continue used outside a loop");
    }
    const instruction = this.emit(
      OP.COMPLETE,
      "continue",
      0,
      label,
      this.tryDepth - context.tryDepth,
      this.finallyDepth - context.finallyDepth
    );
    context.continuePatches.push(instruction);
  }

  compileLabeled(node, inheritedLabels) {
    const label = node.label.name;
    const body = node.body;
    const labels = inheritedLabels.concat([label]);

    if (
      body.type === "WhileStatement" ||
      body.type === "DoWhileStatement" ||
      body.type === "ForStatement" ||
      body.type === "ForInStatement" ||
      body.type === "SwitchStatement"
    ) {
      this.compileStatement(body, labels);
      return;
    }

    const context = this.pushControl({
      type: "label",
      labels: [label],
      breakPatches: [],
      continuePatches: []
    });
    this.compileStatement(body, labels);
    const end = this.current.code.length;
    this.popControl(context, end);
  }

  pushControl(context) {
    context.tryDepth = this.tryDepth;
    context.finallyDepth = this.finallyDepth;
    this.controls.push(context);
    return context;
  }

  popControl(context, end) {
    for (const instruction of context.breakPatches) {
      this.patch(instruction, 1, end);
    }
    for (const instruction of context.continuePatches) {
      this.patch(instruction, 1, context.continueTarget);
    }
    this.controls.pop();
  }

  findBreakContext(label) {
    for (let i = this.controls.length - 1; i >= 0; i -= 1) {
      const context = this.controls[i];
      if (label) {
        if (context.labels && context.labels.indexOf(label) !== -1) {
          return context;
        }
      } else if (context.type !== "label" || context.labels.length > 0) {
        return context;
      }
    }
    return null;
  }

  findContinueContext(label) {
    for (let i = this.controls.length - 1; i >= 0; i -= 1) {
      const context = this.controls[i];
      if (context.type !== "loop") {
        continue;
      }
      if (!label || (context.labels && context.labels.indexOf(label) !== -1)) {
        return context;
      }
    }
    return null;
  }

  compileExpression(node) {
    if (!node) {
      throw this.error(node, "Missing expression");
    }

    switch (node.type) {
      case "ThisExpression":
        this.emit(OP.PUSH_THIS);
        return;

      case "Identifier":
        if (node.name === "undefined") {
          this.emit(OP.PUSH_UNDEFINED);
        } else {
          this.emit(OP.LOAD_NAME, node.name);
        }
        return;

      case "Literal":
        this.compileLiteral(node);
        return;

      case "ArrayExpression":
        for (const element of node.elements) {
          if (element) {
            this.compileExpression(element);
          } else {
            this.emit(OP.PUSH_UNDEFINED);
          }
        }
        this.emit(OP.MAKE_ARRAY, node.elements.length);
        return;

      case "ObjectExpression":
        this.compileObject(node);
        return;

      case "FunctionExpression":
        this.emit(OP.MAKE_FUNCTION, this.functionIds.get(node));
        return;

      case "SequenceExpression":
        for (let i = 0; i < node.expressions.length; i += 1) {
          this.compileExpression(node.expressions[i]);
          if (i !== node.expressions.length - 1) {
            this.emit(OP.POP);
          }
        }
        return;

      case "UnaryExpression":
        this.compileUnary(node);
        return;

      case "BinaryExpression":
        this.compileBinary(node);
        return;

      case "LogicalExpression":
        this.compileLogical(node);
        return;

      case "AssignmentExpression":
        this.compileAssignment(node);
        return;

      case "UpdateExpression":
        this.compileUpdate(node);
        return;

      case "ConditionalExpression":
        this.compileConditional(node);
        return;

      case "CallExpression":
        this.compileCall(node);
        return;

      case "NewExpression":
        this.compileNew(node);
        return;

      case "MemberExpression":
        this.compileMemberReference(node);
        this.emit(OP.GET_PROP);
        return;

      default:
        throw this.error(node, `Unsupported expression: ${node.type}`);
    }
  }

  compileLiteral(node) {
    if (node.regex) {
      this.emit(OP.PUSH_REGEX, node.regex.pattern, node.regex.flags || "");
      return;
    }

    const value = node.value;
    if (value === null) {
      this.emit(OP.PUSH_NULL);
    } else if (value === true) {
      this.emit(OP.PUSH_TRUE);
    } else if (value === false) {
      this.emit(OP.PUSH_FALSE);
    } else {
      this.emit(OP.PUSH_CONST, value);
    }
  }

  compileObject(node) {
    for (const property of node.properties) {
      if (property.kind && property.kind !== "init") {
        throw this.error(property, `${property.kind} properties are not supported by ExtendScript`);
      }
      if (property.computed) {
        throw this.error(property, "Computed object properties are not supported");
      }
      this.emit(OP.PUSH_CONST, this.propertyName(property.key));
      this.compileExpression(property.value);
    }
    this.emit(OP.MAKE_OBJECT, node.properties.length);
  }

  compileUnary(node) {
    if (node.operator === "typeof" && node.argument.type === "Identifier") {
      this.emit(OP.TYPEOF_NAME, node.argument.name);
      return;
    }

    if (node.operator === "delete") {
      if (node.argument.type === "MemberExpression") {
        this.compileMemberReference(node.argument);
        this.emit(OP.DEL_PROP);
        return;
      }
      if (node.argument.type === "Identifier") {
        this.emit(OP.DEL_NAME, node.argument.name);
        return;
      }
      this.compileExpression(node.argument);
      this.emit(OP.POP);
      this.emit(OP.PUSH_TRUE);
      return;
    }

    if (node.operator === "void") {
      this.compileExpression(node.argument);
      this.emit(OP.POP);
      this.emit(OP.PUSH_UNDEFINED);
      return;
    }

    if (!UNARY_OPERATORS.has(node.operator)) {
      throw this.error(node, `Unsupported unary operator: ${node.operator}`);
    }
    this.compileExpression(node.argument);
    var unaryOpcode = UNARY_OPCODES[node.operator];
    if (unaryOpcode) {
      this.emit(unaryOpcode);
    } else {
      this.emit(OP.UNARY, node.operator);
    }
  }

  compileBinary(node) {
    if (!BINARY_OPERATORS.has(node.operator)) {
      throw this.error(node, `Unsupported binary operator: ${node.operator}`);
    }
    this.compileExpression(node.left);
    this.compileExpression(node.right);
    this.emit(BINARY_OPCODES[node.operator]);
  }

  compileLogical(node) {
    if (node.operator !== "&&" && node.operator !== "||") {
      throw this.error(node, `Unsupported logical operator: ${node.operator}`);
    }

    this.compileExpression(node.left);
    this.emit(OP.DUP);
    const jump = this.emit(node.operator === "&&" ? OP.JMP_IF_FALSE : OP.JMP_IF_TRUE, 0);
    this.emit(OP.POP);
    this.compileExpression(node.right);
    this.patch(jump, 0, this.current.code.length);
  }

  compileAssignment(node) {
    if (node.operator === "=") {
      if (node.left.type === "Identifier") {
        this.compileExpression(node.right);
        this.emit(OP.STORE_NAME, node.left.name);
        return;
      }
      if (node.left.type === "MemberExpression") {
        this.compileMemberReference(node.left);
        this.compileExpression(node.right);
        this.emit(OP.SET_PROP);
        return;
      }
      throw this.error(node.left, "Invalid assignment target");
    }

    const operator = node.operator.slice(0, -1);
    if (!BINARY_OPERATORS.has(operator) || operator === "in" || operator === "instanceof") {
      throw this.error(node, `Unsupported compound assignment: ${node.operator}`);
    }

    if (node.left.type === "Identifier") {
      this.emit(OP.LOAD_NAME, node.left.name);
      this.compileExpression(node.right);
      this.emit(BINARY_OPCODES[operator]);
      this.emit(OP.STORE_NAME, node.left.name);
      return;
    }

    if (node.left.type === "MemberExpression") {
      this.compileMemberReference(node.left);
      this.emit(OP.DUP2);
      this.emit(OP.GET_PROP);
      this.compileExpression(node.right);
      this.emit(BINARY_OPCODES[operator]);
      this.emit(OP.SET_PROP);
      return;
    }

    throw this.error(node.left, "Invalid assignment target");
  }

  compileUpdate(node) {
    if (node.operator !== "++" && node.operator !== "--") {
      throw this.error(node, `Unsupported update operator: ${node.operator}`);
    }
    const binaryOperator = node.operator === "++" ? "+" : "-";

    this.withTemp((temp) => {
      if (node.argument.type === "Identifier") {
        this.emit(OP.LOAD_NAME, node.argument.name);
        this.emit(OP.UNARY, "+");
        this.emit(OP.SET_TEMP, temp);
        this.emit(OP.LOAD_TEMP, temp);
        this.emit(OP.PUSH_CONST, 1);
        this.emit(BINARY_OPCODES[binaryOperator]);
        this.emit(OP.STORE_NAME, node.argument.name);
      } else if (node.argument.type === "MemberExpression") {
        this.compileMemberReference(node.argument);
        this.emit(OP.DUP2);
        this.emit(OP.GET_PROP);
        this.emit(OP.UNARY, "+");
        this.emit(OP.SET_TEMP, temp);
        this.emit(OP.LOAD_TEMP, temp);
        this.emit(OP.PUSH_CONST, 1);
        this.emit(BINARY_OPCODES[binaryOperator]);
        this.emit(OP.SET_PROP);
      } else {
        throw this.error(node.argument, "Invalid update target");
      }

      if (node.prefix) {
        return;
      }
      this.emit(OP.POP);
      this.emit(OP.LOAD_TEMP, temp);
    });
  }

  compileConditional(node) {
    this.compileExpression(node.test);
    const alternateJump = this.emit(OP.JMP_IF_FALSE, 0);
    this.compileExpression(node.consequent);
    const endJump = this.emit(OP.JMP, 0);
    this.patch(alternateJump, 0, this.current.code.length);
    this.compileExpression(node.alternate);
    this.patch(endJump, 0, this.current.code.length);
  }

  compileCall(node) {
    if (node.callee.type === "MemberExpression") {
      this.compileExpression(node.callee.object);
      this.emit(OP.DUP);
      this.compileProperty(node.callee);
      this.emit(OP.GET_PROP);
    } else {
      this.emit(OP.PUSH_UNDEFINED);
      this.compileExpression(node.callee);
    }

    for (const argument of node.arguments) {
      this.compileExpression(argument);
    }
    this.emit(OP.CALL, node.arguments.length);
  }

  compileNew(node) {
    this.compileExpression(node.callee);
    for (const argument of node.arguments) {
      this.compileExpression(argument);
    }
    this.emit(OP.NEW, node.arguments.length);
  }

  compileMemberReference(node) {
    this.compileExpression(node.object);
    this.compileProperty(node);
  }

  compileProperty(node) {
    if (node.computed) {
      this.compileExpression(node.property);
      return;
    }
    this.emit(OP.PUSH_CONST, this.propertyName(node.property));
  }

  propertyName(node) {
    if (node.type === "Identifier") {
      return node.name;
    }
    if (node.type === "Literal") {
      return String(node.value);
    }
    throw this.error(node, "Unsupported property name");
  }

  identifierName(node) {
    if (!node || node.type !== "Identifier") {
      throw this.error(node, "Expected an identifier");
    }
    return node.name;
  }

  error(node, message) {
    const location = node && node.loc ? ` at ${node.loc.start.line}:${node.loc.start.column + 1}` : "";
    return new Error(`${message}${location}`);
  }
}

  return {
    BINARY_OPERATORS,
    Compiler,
    UNARY_OPERATORS
  };
});
