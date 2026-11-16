// A fast CommonMark 0.31.2 + GFM 0.29 renderer that produces byte-identical
// HTML to marked 18.1.3 with its default options (GFM on, breaks off).
//
// Written from scratch in this session. The design is my own: a block pass
// builds a small node tree (link reference definitions are collected as the
// pass runs, exactly like marked defers inline work until the whole block
// pass is done), then a render walk turns the tree into HTML, rendering
// inline spans as it goes. Inline emphasis follows the CommonMark delimiter
// rules (left/right flanking, rules 9 and 10) with a masked-source scan, so
// delimiters hiding inside code spans, links and raw HTML cannot pair.
//
// Speed comes from the shape of the work, not from shortcuts: plain
// paragraphs take a fast inline path, output is built with array push and
// one join per run, and no token objects are allocated for the common
// constructs. Nothing is kept from one parse() call to the next.

const ESC_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

// Escape &, <, >, " and '. With encode=false (the default) an & that already
// starts a character reference (&amp; &#65; &copy;) is left alone; with
// encode=true every & becomes &amp;.
const RE_ESC_TEST = /[&<>"']/;
const RE_ESC_REPLACE = /[&<>"']/g;
const RE_ESC_TEST_NOENC = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const RE_ESC_REPLACE_NOENC = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
function escHtml(s, encode) {
  if (encode) {
    return RE_ESC_TEST.test(s) ? s.replace(RE_ESC_REPLACE, (c) => ESC_MAP[c]) : s;
  }
  return RE_ESC_TEST_NOENC.test(s) ? s.replace(RE_ESC_REPLACE_NOENC, (c) => ESC_MAP[c]) : s;
}

const RE_NUM_REF_TEST = /&#[0-9]{1,7};|&#[Xx][A-Fa-f0-9]{1,6};/;
const RE_NUM_REF_OR_AMP = /&#[0-9]{1,7};|&#[Xx][A-Fa-f0-9]{1,6};|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
// Numeric character references stand for the character they name. Zero, out
// of range and surrogate values become the replacement character, and a
// decoded & must not join its neighbours into a new reference.
function decodeNumericRefs(s) {
  if (!RE_NUM_REF_TEST.test(s)) return s;
  return s.replace(/&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g, (m, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '\uFFFD';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

function cleanHref(href) {
  try {
    return encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
}

// A link label, folded the way CommonMark asks: surrounding whitespace
// stripped, inner runs collapsed to one space, Unicode case folded.
function normLabel(label) {
  return label.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Index of the ')' that closes the '(' at the start of str's balance, or -1
// when the brackets balance out and -2 when more open than close. A '\'
// skips the next character.
function findClosingBracket(str, pair) {
  if (str.indexOf(pair[0]) === -1 && str.indexOf(pair[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    const ch = str[i];
    if (ch === '\\') { i++; continue; }
    if (ch === pair[0]) level++;
    else if (ch === pair[1]) {
      level--;
      if (level < 0) return i;
    }
  }
  return level > 0 ? -2 : -1;
}

function expandTabs(line, indent = 0) {
  let col = indent;
  let out = '';
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (ch === '\t') {
      const added = 4 - (col % 4);
      out += '    '.slice(0, added);
      col += added;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

// Remove a suffix of c's (or, inverted, of non-c's).
function rtrimChar(str, c, invert) {
  const l = str.length;
  if (l === 0) return '';
  let n = 0;
  while (n < l) {
    const ch = str.charAt(l - n - 1);
    if (ch === c && !invert) n++;
    else if (ch !== c && invert) n++;
    else break;
  }
  return str.slice(0, l - n);
}

const RE_BLANK_LINE = /^[ \t]*$/;
function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let end = lines.length - 1;
  while (end >= 0 && RE_BLANK_LINE.test(lines[end])) end--;
  if (lines.length - end <= 2) return str;
  return lines.slice(0, end + 1).join('\n');
}

// Split a GFM table row on unescaped pipes. Escaped pipes are kept as \|
// until the end, then turned back into |.
function splitCells(tableRow, count) {
  const row = tableRow.replace(/\|/g, (m, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = row.split(' |');
  let i = 0;
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (; i < cells.length; i++) cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  return cells;
}

// ---------------------------------------------------------------------------
// Block grammar. Each pattern is anchored at the start of the remaining
// source, matching what the corresponding CommonMark construct consumes.
// ---------------------------------------------------------------------------

const TAG_LIST = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';

const RE_SPACE = /^(?:[ \t]*(?:\n|$))+/;
const RE_INDENT_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const RE_CODE_INDENT = /^(?: {0,3}\t| {1,4})/gm;
const RE_HR = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;
const RE_ATX = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const RE_LIST_START = /^( {0,3}(?:[*+-]|\d{1,9}[.)]))([ \t][^\n]*?)?(?:\n|$)/;

// Block HTML, types 1-7 of the CommonMark spec. Type 1 is script/pre/style/
// textarea up to its close tag; 2 a comment; 3 a processing instruction; 4 a
// declaration; 5 CDATA; 6 a block-level tag (open or close) up to a blank
// line; 7 a complete open or close tag of any other kind on its own line,
// also up to a blank line.
const RE_HTML_BLOCK = new RegExp(
  '^ {0,3}(?:'
  + '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)'
  + '|<!--(?:-?>|[\\s\\S]*?(?:-->|$))[^\\n]*(\\n+|$)'
  + '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)'
  + '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)'
  + '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)'
  + '|</?(?:' + TAG_LIST + ')(?:[ \\t]+|\\n|/?>)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?: +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + ')', 'i');

// A link reference definition: [label]: destination "optional title".
// The label may hold escapes and may wrap onto a following non-blank line.
const BLOCK_LABEL = /(?:\\[\s\S]|[^\[\]\\]|\n(?![ \t]*\n))+/;
const DEF_TITLE = /(?:\"(?:\\[\s\S]|[^\"\\])*\"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))/;
const RE_DEF = new RegExp(
  '^ {0,3}\\[(?!\\s*\\])(' + BLOCK_LABEL.source + ')\\]: *(?:\\n[ \\t]*)?'
  + '([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)(' + DEF_TITLE.source + '))? *(?:\\n+|$)');

// GFM table: header line, delimiter row, then body rows until a blank line
// or a line that starts another block.
const TABLE_INTERRUPT = ' {0,3}(?:[*+-]|1[.)])[ \\t]';
const RE_TABLE = new RegExp(
  '^ *([^\\n ].*)\\n'
  + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)'
  + '(?:\\n((?:(?! *\\n'
  + '| {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)'
  + '| {0,3}#{1,6}(?:\\s|$)'
  + '| {0,3}>'
  + '|(?: {4}| {0,3}\\t)[^\\n]'
  + '| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)'
  + '|' + TABLE_INTERRUPT
  + '| {0,3}(?:</?(?:' + TAG_LIST + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)'
  + ').*(?:\\n|$))*)\\n*|$)');

// Setext heading: text lines, then a line of = or -. A line that starts a
// list, a fence, a blockquote, an ATX heading, a thematic break, an HTML
// block or (in GFM) a table delimiter row cannot be part of the text, and a
// blank line ends it.
const BULLET = / {0,3}(?:[*+-]|\d{1,9}[.)])/;
const SETEXT_TEXT_STOP = '(?!\\s*?\\n'
  + '| {0,3}(?:[*+-]|\\d{1,9}[.)]) '
  + '| {0,3}(?:`{3,}|~{3,})'
  + '| {0,3}>'
  + '| {0,3}#{1,6}(?:\\s|$)'
  + '| {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)'
  + '| {0,3}<[^\\n>]+>\\n'
  + '| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n)';
const RE_LHEADING = new RegExp(
  '^(?! {0,3}(?:[*+-]|\\d{1,9}[.)]) |(?: {4}| {0,3}\\t)| {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\\s|$)| {0,3}<[^\\n>]+>\\n| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n)'
  + '((?:.|\\n' + SETEXT_TEXT_STOP + ')+?)\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)');

// A paragraph runs until a line that starts an interrupting construct:
// thematic break, ATX heading, blockquote, fence, list (bullet, or 1./1)),
// HTML block of types 1-6, or a table. Setext underlines do not interrupt:
// the lheading rule above claims them first, at the top of the loop.
const PARA_STOP = '(?!'
  + ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)'
  + '| {0,3}#{1,6}(?:\\s|$)'
  + '| {0,3}>'
  + '| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)'
  + '| {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]'
  + '| {0,3}(?:</?(?:' + TAG_LIST + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)'
  + '|' + RE_TABLE.source.slice(1)
  + '|[ \\t]+\\n)';
const RE_PARAGRAPH = new RegExp('^([^\\n]+(?:\\n' + PARA_STOP + '[^\\n]+)*)');
// Inside a blockquote a bare list marker (any number, even an empty item)
// starts a sibling list, so it must not be lazily continued as paragraph.
const RE_BQ_PARAGRAPH = new RegExp('^([^\\n]+(?:\\n(?!'
  + ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)'
  + '| {0,3}#{1,6}(?:\\s|$)'
  + '| {0,3}>'
  + '| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)'
  + '| {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)'
  + '| {0,3}(?:</?(?:' + TAG_LIST + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)'
  + '|[ \\t]+\\n)[^\\n]+)*)');
const RE_BLOCKQUOTE = new RegExp(
  '^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(' + RE_BQ_PARAGRAPH.source.slice(1) + ')|[^\\n]*)(?:\\n|$))+');
const RE_TEXT = /^[^\n]+/;

// ---------------------------------------------------------------------------
// Inline grammar
// ---------------------------------------------------------------------------

const RE_INLINE_ESCAPE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\\\]^_`{|}~])/;
const RE_INLINE_CODE = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const RE_BR = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const RE_ANY_PUNCT = /\\([\p{P}\p{S}])/gu;

const TAG_ATTR = / +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?/;
const INLINE_TAG_ATTR = /\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?/;
const RE_TAG = new RegExp(
  '^<!--(?:-?>|[\\s\\S]*?-->)'
  + '|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>'
  + '|^<[a-zA-Z][a-zA-Z0-9-]*(?:' + INLINE_TAG_ATTR.source + ')*?\\s*/?>'
  + '|^<\\?[\\s\\S]*?\\?>'
  + '|^<![a-zA-Z]+\\s[\\s\\S]*?>'
  + '|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>');

const RE_AUTOLINK = /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/;

const INLINE_LABEL_BRACKETS = /\[(?:\\[\s\S]|[^\[\]\\])*\]/;
const INLINE_LABEL = new RegExp(
  '(?:\\[(?:' + INLINE_LABEL_BRACKETS.source + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]'
  + '|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?');
const RE_LINK = new RegExp(
  '^!?\\[(' + INLINE_LABEL.source + ')\\]\\([ \\t\\n]*'
  + '(<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\)))'
  + '(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)'
  + '("(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)))?[ \\t\\n]*\\)');
const RE_REFLINK = new RegExp(
  '^!?\\[(' + INLINE_LABEL.source + ')\\]\\[((?!\\s*\\])' + BLOCK_LABEL.source + ')\\]');
const RE_NOLINK = new RegExp(
  '^!?\\[((?!\\s*\\])' + BLOCK_LABEL.source + ')\\](?:\\[\\])?');

const EMAIL_LOCAL = '[A-Za-z0-9._+-]+';
const EMAIL_DOMAIN = '[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+';
const RE_URL = new RegExp(
  '^(?:mailto:' + EMAIL_LOCAL + '@' + EMAIL_DOMAIN + '(?![\\w-])'
  + '|xmpp:' + EMAIL_LOCAL + '@' + EMAIL_DOMAIN + '(?![\\w-])(?:\\/[A-Za-z0-9@.]+)?'
  + '|((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*'
  + '|' + EMAIL_LOCAL + '(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-]))');
const RE_BACKPEDAL = /(?:[^?!.,:;*_'\"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'\"~)]+(?!$))+/;

// Plain text runs stop just before anything that could start another
// construct: a backslash, <, !, [, backtick, *, ~, _, a hard-break (two
// spaces before a newline), a scheme://, a www. at a word start, or an
// email address. The first alternative lets a single non-alphanumeric
// character be swallowed just before a mailto:/xmpp: scheme so the scheme
// itself is left for the autolink rule.
const RE_INLINE_TEXT = /^(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|(?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|(?<![^\s*_~(])www\.|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/;

// Emphasis delimiters. A run may open only when the character after it is
// punctuation or a non-space character (groups 1/2 for *, 3/4 for _); the
// right-delimiter scans below classify each later run as left-only,
// right-only or either, from its neighbours.
const RE_EM_L = /^(?:\*+(?:((?!\*)(?!~)[\p{P}\p{S}])|([^\s*]))?)|^_+(?:((?!_)(?!~)[\p{P}\p{S}])|([^\s_]))?/u;
const RE_PUNCT = /^((?![*_])[\s\p{P}\p{S}])/u;
const RE_ALPHA_NUM = /[\p{L}\p{N}]/u;
const PUNCT_GFM = '(?!~)[\\p{P}\\p{S}]';
const PUNCT_SPACE_GFM = '(?!~)[\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE_GFM = '(?:[^\\s\\p{P}\\p{S}]|~)';
const RE_EM_R_AST = new RegExp(
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)'
  + '|[^*]+(?=[^*])'
  + '|(?!\\*)' + PUNCT_GFM + '(\\*+)(?=[\\s]|$)'
  + '|' + NOT_PUNCT_SPACE_GFM + '(\\*+)(?!\\*)(?=' + PUNCT_SPACE_GFM + '|$)'
  + '|(?!\\*)' + PUNCT_SPACE_GFM + '(\\*+)(?=' + NOT_PUNCT_SPACE_GFM + ')'
  + '|[\\s](\\*+)(?!\\*)(?=' + PUNCT_GFM + ')'
  + '|(?!\\*)' + PUNCT_GFM + '(\\*+)(?!\\*)(?=' + PUNCT_GFM + ')'
  + '|' + NOT_PUNCT_SPACE_GFM + '(\\*+)(?=' + NOT_PUNCT_SPACE_GFM + ')', 'gu');
const RE_EM_R_UND = new RegExp(
  '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)'
  + '|[^_]+(?=[^_])'
  + '|(?!_)[\\p{P}\\p{S}](_+)(?=[\\s]|$)'
  + '|[^\\s\\p{P}\\p{S}](_+)(?!_)(?=[\\s\\p{P}\\p{S}]|$)'
  + '|(?!_)[\\s\\p{P}\\p{S}](_+)(?=[^\\s\\p{P}\\p{S}])'
  + '|[\\s](_+)(?!_)(?=[\\p{P}\\p{S}])'
  + '|(?!_)[\\p{P}\\p{S}](_+)(?!_)(?=[\\p{P}\\p{S}])', 'gu');
const RE_DEL_L = /^~~?(?:((?!~)[\p{P}\p{S}])|[^\s~])/u;
const RE_DEL_R = new RegExp(
  '^[^~]+(?=[^~])'
  + '|(?!~)[\\p{P}\\p{S}](~~?)(?=[\\s]|$)'
  + '|[^\\s\\p{P}\\p{S}](~~?)(?!~)(?=[\\s\\p{P}\\p{S}]|$)'
  + '|(?!~)[\\s\\p{P}\\p{S}](~~?)(?=[^\\s\\p{P}\\p{S}])'
  + '|[\\s](~~?)(?!~)(?=[\\p{P}\\p{S}])'
  + '|(?!~)[\\p{P}\\p{S}](~~?)(?!~)(?=[\\p{P}\\p{S}])'
  + '|[^\\s\\p{P}\\p{S}](~~?)(?=[^\\s\\p{P}\\p{S}])', 'gu');

// Masking: hide links, code spans, HTML and escapes from the emphasis scan
// by replacing them with same-length filler, so a * inside `code` or a
// [link](url) can never pair with a delimiter outside it.
const BOUNDED_BLOCK_LABEL = /(?:\\[\s\S]|[^\[\]\\]){1,999}/;
const BOUNDED_INLINE_LABEL = new RegExp(
  '(?:[^\\[\\]\\\\`]*(?:\\[(?:' + INLINE_LABEL_BRACKETS.source + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]'
  + '|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?');
const RE_REFLINK_SEARCH = new RegExp(
  '!?\\[(' + BOUNDED_INLINE_LABEL.source + ')\\]\\[((?!\\s*\\])' + BOUNDED_BLOCK_LABEL.source + ')\\]'
  + '|!?\\[((?!\\s*\\])' + BOUNDED_BLOCK_LABEL.source + ')\\](?:\\[\\])?(?!\\()', 'g');
const RE_BLOCK_SKIP = /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)|(?<!`)()(?<b>`+)[^`]+\k<b>(?!`)|<(?! )[^<>]*?>/g;
const RE_ANY_PUNCT_OUTSIDE_CODE = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;

// ---------------------------------------------------------------------------
// Inline rendering. ctx is per-parse state shared by a run and its nested
// runs: links (the reference definitions), inLink (inside <a> or a link
// label), inRaw (inside an inline <pre>/<code>/<kbd>/<script>), linkEmitted
// (a link was produced in the current label) and parenOk (the run holds a
// ')', so an inline link could match at all).
// ---------------------------------------------------------------------------

function linkInText(text, ctx) {
  if (!text.includes('[')) return false;
  for (const m of text.matchAll(RE_BLOCK_SKIP)) {
    if (RE_LINK.test(m[0]) && text.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of text.matchAll(RE_REFLINK_SEARCH)) {
    const m0 = m[0];
    const refStart = m0.lastIndexOf('[');
    if (m0.charAt(0) === '!' || !ctx.links.has(normLabel(m0.slice(refStart + 1, -1)))) continue;
    if (refStart > 1 && linkInText(m0.slice(1, refStart - 1), ctx)) continue;
    return true;
  }
  return false;
}

function maskInline(src, ctx) {
  let masked = src;
  if (ctx.links.size && src.includes('[')) {
    const maskReflink = (m0) => {
      const refStart = m0.lastIndexOf('[');
      if (!ctx.links.has(normLabel(m0.slice(refStart + 1, -1)))) return m0;
      // A candidate that already holds a link never becomes one, so only
      // mask the links it holds and leave its emphasis visible.
      if (refStart > 1 && m0.charAt(0) !== '!') {
        const text = m0.slice(1, refStart - 1);
        if (linkInText(text, ctx)) {
          return '[' + text.replace(RE_REFLINK_SEARCH, maskReflink)
            + '][' + 'a'.repeat(m0.length - refStart - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(m0.length - 2) + ']';
    };
    masked = masked.replace(RE_REFLINK_SEARCH, maskReflink);
  }
  // Escapes are masked; backslashes inside code spans are literal, so mask
  // the backticks of the span instead and let the skip below cover it.
  // With no backslash or backtick in the run there is nothing to mask.
  if (src.includes('\\') || src.includes('`')) {
    masked = masked.replace(RE_ANY_PUNCT_OUTSIDE_CODE, (m0, code, punct) => {
      if (punct) return '+'.repeat(m0.length);
      if (code) return code + m0.slice(code.length, -code.length).replace(/`/g, '+') + code;
      return m0;
    });
  }
  // Links, code spans and HTML tags flatten to [aaa...]. With no '[',
  // backtick or '<' in the run there is nothing to flatten.
  if (src.includes('[') || src.includes('`') || src.includes('<')) {
    masked = masked.replace(RE_BLOCK_SKIP, (m0, _link, context) => {
      const offset = context ? context.length : 0;
      return m0.slice(0, offset) + '[' + 'a'.repeat(m0.length - offset - 2) + ']';
    });
  }
  return masked;
}

// Last run of each delimiter that could close emphasis or strikethrough:
// a run whose first character is not preceded by whitespace (or the start).
function scanClosers(masked) {
  const out = { star: -1, under: -1, tilde: -1 };
  const len = masked.length;
  for (let i = 0; i < len; i++) {
    const ch = masked[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : masked[i - 1];
    let j = i + 1;
    while (j < len && masked[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') out.tilde = i;
      else if (ch === '*') out.star = i;
      else out.under = i;
    }
    i = j - 1;
  }
  return out;
}

// Does the label end inside an <a ...> tag or an autolink that reaches past
// the label's closing bracket? Then the bracket is not the label's end.
function labelEndInsideToken(src, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') { i++; continue; }
    if (label[i] === '`') {
      const code = RE_INLINE_CODE.exec(label.slice(i));
      if (code) { i += code[0].length - 1; continue; }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(labelStart + i);
    const tok = RE_TAG.exec(tokenSrc) || RE_AUTOLINK.exec(tokenSrc);
    if (!tok) continue;
    if (tok[0].length > label.length - i) return true;
    i += tok[0].length - 1;
  }
  return false;
}

function renderLinkOrImage(cap, href, title, raw, ctx, mode) {
  const text = cap[1].replace(/\\([\[\]])/g, '$1');
  const isImage = cap[0].charAt(0) === '!';
  const outerInLink = ctx.inLink;
  const outerEmitted = ctx.linkEmitted;
  const outerRaw = ctx.inRaw;
  ctx.inLink = true;
  ctx.linkEmitted = false;
  // A link's label is rendered as HTML; an image's label is flattened to
  // plain text for the alt attribute, so it is rendered in text mode.
  const labelHtml = renderInline(text, ctx, isImage ? 'text' : mode);
  const textHasLink = ctx.linkEmitted;
  ctx.linkEmitted = outerEmitted;
  ctx.inLink = outerInLink;
  if (!isImage) {
    // Links may not contain other links, at any level of nesting.
    if (textHasLink) {
      ctx.inRaw = outerRaw;
      return null;
    }
    ctx.linkEmitted = true;
    if (mode === 'text') return labelHtml;
    const clean = cleanHref(href);
    if (clean === null) return labelHtml;
    let out = '<a href="' + escHtml(clean, false) + '"';
    if (title) out += ' title="' + escHtml(title) + '"';
    return out + '>' + labelHtml + '</a>';
  }
  if (mode === 'text') return labelHtml;
  const clean = cleanHref(href);
  if (clean === null) return escHtml(labelHtml);
  let out = '<img src="' + escHtml(clean) + '" alt="' + escHtml(labelHtml) + '"';
  if (title) out += ' title="' + escHtml(title) + '"';
  return out + '>';
}

// Try an inline link or image at the start of rest. Returns the HTML (or
// null when the text is not a link after all, so the caller falls through
// to plain text).
function tryLink(rest, ctx, mode) {
  if (!ctx.parenOk) return null;
  const cap = RE_LINK.exec(rest);
  if (!cap) return null;
  const labelStart = rest.charAt(0) === '!' ? 2 : 1;
  if (labelEndInsideToken(rest, cap[1], labelStart)) return null;
  const trimmedUrl = cap[2].trim();
  if (trimmedUrl.charAt(0) === '<') {
    if (trimmedUrl.charAt(trimmedUrl.length - 1) !== '>') return null;
    // The closing bracket only counts when it is not escaped: an odd run
    // of backslashes before it means it is.
    const unslashed = rtrimChar(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - unslashed.length) % 2 === 0) return null;
  } else {
    const lastParen = findClosingBracket(cap[2], '()');
    if (lastParen === -2) return null;
    if (lastParen > -1) {
      const start = rest.charAt(0) === '!' ? 5 : 4;
      const linkLen = start + cap[1].length + lastParen;
      cap[2] = cap[2].substring(0, lastParen);
      cap[0] = cap[0].substring(0, linkLen).trim();
      cap[3] = '';
    }
  }
  // The ')' that ends the match is the link closer only when unescaped.
  const unescaped = rtrimChar(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - unescaped.length) % 2 === 0) return null;
  let href = cap[2];
  const title = cap[3] ? cap[3].slice(1, -1) : '';
  href = href.trim();
  if (href.charAt(0) === '<') href = href.slice(1, -1);
  const out = renderLinkOrImage(cap,
    href ? href.replace(RE_ANY_PUNCT, '$1') : href,
    title ? title.replace(RE_ANY_PUNCT, '$1') : title,
    cap[0], ctx, mode);
  return out === null ? null : { html: out, len: cap[0].length };
}

function tryReflink(rest, ctx, mode) {
  const cap = RE_REFLINK.exec(rest) || RE_NOLINK.exec(rest);
  if (!cap) return null;
  const labelStart = rest.charAt(0) === '!' ? 2 : 1;
  if (labelEndInsideToken(rest, cap[1], labelStart)) return null;
  const link = ctx.links.get(normLabel(cap[2] || cap[1]));
  if (!link) return { html: rest.charAt(0), len: 1 };
  const out = renderLinkOrImage(cap, link.href, link.title, cap[0], ctx, mode);
  return out === null ? null : { html: out, len: cap[0].length };
}

// Emphasis and strong emphasis, following the delimiter rules: a run can
// open when it is left-flanking (or has no next character, or follows
// punctuation), and the scan for its closer classifies each later run as
// left-only, right-only or either. Rules 9 and 10 keep a run whose length
// and the closer's length sum to a multiple of 3 from pairing when the
// opener's own length is a multiple of 3.
function tryEmStrong(rest, masked, prevChar, ctx, mode, closers) {
  const m = RE_EM_L.exec(rest);
  if (!m) return null;
  if (!m[1] && !m[2] && !m[3] && !m[4]) return null;
  const delim = m[0][0];
  const midRun = prevChar === delim;
  const srcStart = masked.length - rest.length;
  let runStart = srcStart;
  while (runStart > 0 && masked[runStart - 1] === delim) runStart--;
  const before = masked.slice(Math.max(0, runStart - 2), runStart);
  const runPrevChar = [...before].at(-1) ?? '';
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || !!RE_PUNCT.exec(runPrevChar);
  if (runStart < srcStart) prevChar = runPrevChar;
  const prevPunct = runStart < srcStart ? runPrevPunct : !!RE_PUNCT.exec(prevChar);
  // _ cannot open between two alphanumerics.
  if (m[4] && RE_ALPHA_NUM.test(prevChar)) return null;
  const nextChar = m[1] || m[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    const lLen = [...m[0]].length - 1;
    const runLen = srcStart - runStart + lLen;
    const openerCanClose = !!runPrevChar.trim()
      && (!!nextChar || (delim === '*' && !runPrevPunct));
    const endRe = delim === '*' ? RE_EM_R_AST : RE_EM_R_UND;
    const lastCloser = delim === '*' ? closers.star : closers.under;
    const winStart = masked.length - rest.length + lLen;
    if (lastCloser < winStart) return null;
    const clipped = masked.slice(-rest.length + lLen);
    const lastInWin = lastCloser - winStart;
    endRe.lastIndex = 0;
    let delimTotal = lLen;
    let midTotal = 0;
    let match;
    while ((match = endRe.exec(clipped)) !== null) {
      if (match.index > lastInWin) break;
      const rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      const rLen = [...rDelim].length;
      if (match[3] || match[4]) {
        delimTotal += rLen;
        continue;
      } else if (match[5] || match[6] || openerCanClose) {
        // A mid-run opener cannot close against a delimiter that can also
        // open; that delimiter opens its own span instead.
        if (midRun && (match[5] || match[6])) break;
        if (runLen % 3 && !((runLen + rLen) % 3)) {
          midTotal += rLen;
          continue;
        }
      }
      delimTotal -= rLen;
      if (delimTotal > 0) continue;
      const rLen2 = Math.min(rLen, rLen + delimTotal + midTotal);
      const firstLen = [...match[0]][0].length;
      const raw = rest.slice(0, lLen + match.index + firstLen + rLen2);
      if (Math.min(lLen, rLen2) % 2) {
        const inner = raw.slice(1, -1);
        const innerHtml = renderInline(inner, ctx, mode);
        return { html: mode === 'text' ? innerHtml : '<em>' + innerHtml + '</em>', len: raw.length };
      }
      const inner = raw.slice(2, -2);
      const innerHtml = renderInline(inner, ctx, mode);
      return { html: mode === 'text' ? innerHtml : '<strong>' + innerHtml + '</strong>', len: raw.length };
    }
  }
  return null;
}

// Strikethrough, the same delimiter machinery with ~ runs. Only a closer
// run of exactly the opener's length pairs.
function tryDel(rest, masked, prevChar, ctx, mode, closers) {
  const m = RE_DEL_L.exec(rest);
  if (!m) return null;
  const nextChar = m[1] || '';
  if (!nextChar || !prevChar || RE_PUNCT.exec(prevChar)) {
    const lLen = [...m[0]].length - 1;
    let delimTotal = lLen;
    const winStart = masked.length - rest.length + lLen;
    if (closers.tilde < winStart) return null;
    const clipped = masked.slice(-rest.length + lLen);
    const lastInWin = closers.tilde - winStart;
    RE_DEL_R.lastIndex = 0;
    let match;
    while ((match = RE_DEL_R.exec(clipped)) !== null) {
      if (match.index > lastInWin) break;
      const rDelim = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!rDelim) continue;
      const rLen0 = [...rDelim].length;
      if (rLen0 !== lLen) continue;
      if (match[3] || match[4]) {
        delimTotal += rLen0;
        continue;
      }
      delimTotal -= rLen0;
      if (delimTotal > 0) continue;
      const rLen = Math.min(rLen0, rLen0 + delimTotal);
      const firstLen = [...match[0]][0].length;
      const raw = rest.slice(0, lLen + match.index + firstLen + rLen);
      const inner = raw.slice(lLen, -lLen);
      const innerHtml = renderInline(inner, ctx, mode);
      return { html: mode === 'text' ? innerHtml : '<del>' + innerHtml + '</del>', len: raw.length };
    }
  }
  return null;
}

function tryAutolink(rest, ctx, mode) {
  const cap = RE_AUTOLINK.exec(rest);
  if (!cap) return null;
  let text;
  let href;
  if (cap[2] === '@') {
    text = cap[1];
    href = 'mailto:' + text;
  } else {
    text = cap[1];
    href = text;
  }
  if (mode === 'text') return { html: text, len: cap[0].length };
  const clean = cleanHref(href);
  if (clean === null) return { html: escHtml(text, true), len: cap[0].length };
  return { html: '<a href="' + escHtml(clean, true) + '">' + escHtml(text, true) + '</a>', len: cap[0].length };
}

function tryUrl(rest, ctx, mode) {
  const cap = RE_URL.exec(rest);
  if (!cap) return null;
  let text;
  let href;
  if (cap[2] === '@') {
    text = cap[0];
    href = 'mailto:' + text;
  } else {
    // Trim trailing punctuation the autolink must not swallow.
    let prev = '';
    do {
      prev = cap[0];
      cap[0] = RE_BACKPEDAL.exec(cap[0])?.[0] ?? '';
    } while (prev !== cap[0]);
    text = cap[0];
    href = cap[1] === 'www.' ? 'http://' + cap[0] : cap[0];
  }
  if (mode === 'text') return { html: text, len: cap[0].length };
  const clean = cleanHref(href);
  if (clean === null) return { html: escHtml(text, true), len: cap[0].length };
  return { html: '<a href="' + escHtml(clean, true) + '">' + escHtml(text, true) + '</a>', len: cap[0].length };
}

// Render one inline run to HTML (mode 'html') or to flattened plain text
// (mode 'text', for image alt attributes). isTop marks the runs the block
// pass queued: each starts with a closed <pre> state, while nested runs
// (link labels, emphasis contents) share the caller's state.
function renderInline(src, ctx, mode, isTop) {
  if (!src) return '';
  if (isTop) ctx.inRaw = false;
  const prevParenOk = ctx.parenOk;
  ctx.parenOk = prevParenOk && src.includes(')');
  try {
    return renderInlineInner(src, ctx, mode);
  } finally {
    ctx.parenOk = prevParenOk;
  }
}

// --- plain-text chunk scanner (replaces the inline text regex) ---
// A text chunk runs until something that could start another construct:
// a backslash, <, !, [, backtick, *, ~ or _, a hard break (two spaces
// before a newline), a scheme://, a www. at a word start, an email
// address, or a non-alphanumeric character just before mailto:/xmpp:.
// The first character is always taken (a backtick or tilde run whole).
// --- plain-text chunk scanner (replaces the inline text regex) ---
// A text chunk runs until something that could start another construct:
// a backslash, <, !, [, backtick, *, ~ or _, a hard break (two spaces
// before a newline), a scheme://, a www. at a word start, an email
// address, or a non-alphanumeric character just before mailto:/xmpp:.
// The first character is always taken (a backtick or tilde run whole).
// Character classes as 128-entry tables so the hot loop does no
// per-character function calls.
const CC_STOP = new Uint8Array(128);   // \ < ! [ ` * ~ _
for (const c of [92, 60, 33, 91, 96, 42, 126, 95]) CC_STOP[c] = 1;
const CC_ALNUM = new Uint8Array(128);  // A-Z a-z 0-9
for (let c = 48; c <= 57; c++) CC_ALNUM[c] = 1;
for (let c = 65; c <= 90; c++) CC_ALNUM[c] = 1;
for (let c = 97; c <= 122; c++) CC_ALNUM[c] = 1;
const CC_EMAIL = new Uint8Array(128);  // alnum + .!#$%&'*+/=?_`{|}~-
CC_EMAIL.set(CC_ALNUM);
for (const c of '.!#$%&\'*+/=?_`{|}~-'.split('').map(ch => ch.charCodeAt(0))) CC_EMAIL[c] = 1;
// Characters that can only start a text chunk: not a construct starter,
// not an email/protocol starter (alnum, '.', '+', '-').
const CC_TEXTONLY = new Uint8Array(128);
for (let c = 0; c < 128; c++) {
  if (!CC_STOP[c] && !CC_ALNUM[c] && c !== 46 && c !== 43 && c !== 45) CC_TEXTONLY[c] = 1;
}
function protoAt(s, p) {
  const c = s[p];
  if (c === 'h' || c === 'H') {
    if ((s[p + 1] === 't' || s[p + 1] === 'T') && (s[p + 2] === 't' || s[p + 2] === 'T')
      && (s[p + 3] === 'p' || s[p + 3] === 'P')) {
      if (s[p + 4] === ':' && s[p + 5] === '/' && s[p + 6] === '/') return true;
      if ((s[p + 4] === 's' || s[p + 4] === 'S') && s[p + 5] === ':' && s[p + 6] === '/' && s[p + 7] === '/') return true;
    }
  } else if (c === 'f' || c === 'F') {
    if ((s[p + 1] === 't' || s[p + 1] === 'T') && (s[p + 2] === 'p' || s[p + 2] === 'P')
      && s[p + 3] === ':' && s[p + 4] === '/' && s[p + 5] === '/') return true;
  }
  return false;
}
const RE_WWW_PREV = /[\s*_~(]/;
function textChunkLen(rest) {
  const c0 = rest[0];
  const cc0 = rest.charCodeAt(0);
  if (cc0 < 128 && !CC_ALNUM[cc0] && (rest.startsWith('mailto:', 1) || rest.startsWith('xmpp:', 1))) return 1;
  let i = 0;
  if (c0 === '`') { while (rest[i] === '`') i++; }
  else if (c0 === '~') { while (rest[i] === '~') i++; }
  else i = 1;
  const len = rest.length;
  // Earliest position where an email address starts: for each '@', walk
  // back over email characters; the chunk stops at that run's start.
  // The walk-backs cover disjoint runs, so this is linear in total.
  let emailStop = Infinity;
  let at = rest.indexOf('@', i);
  while (at !== -1) {
    let s = at - 1;
    while (s >= i) {
      const c = rest.charCodeAt(s);
      if (c >= 128 || !CC_EMAIL[c]) break;
      s--;
    }
    const stop = s < i ? i : s + 1;
    if (stop < at && stop < emailStop) emailStop = stop;
    at = rest.indexOf('@', at + 1);
  }
  let spaceSkip = 0;
  let p = i;
  while (p < len) {
    const cc = rest.charCodeAt(p);
    if (cc < 128 && CC_STOP[cc]) return p;
    if (cc === 32 && p >= spaceSkip) {
      let q = p;
      while (rest[q] === ' ') q++;
      if (q - p >= 2 && rest[q] === '\n') return p;
      spaceSkip = q;
    }
    if (cc === 104 || cc === 72 || cc === 102 || cc === 70) {
      if (protoAt(rest, p)) return p;
    }
    if (cc === 119 && rest[p + 1] === 'w' && rest[p + 2] === 'w' && rest[p + 3] === '.'
      && (p === 0 || RE_WWW_PREV.test(rest[p - 1]))) return p;
    if (p === emailStop) return p;
    const n1 = rest[p + 1];
    if ((n1 === 'm' || n1 === 'x') && (cc >= 128 || !CC_ALNUM[cc])
      && (rest.startsWith('mailto:', p + 1) || rest.startsWith('xmpp:', p + 1))) return p + 1;
    p++;
  }
  return len;
}

const RE_TEXT_NEEDS = /[&<>"']/;

const RE_FAST = /[\\`*_!\[<~]|www\.|:\/\/|@| {2}\n/;

function renderInlineInner(src, ctx, mode) {
  // Fast path: nothing here can start a construct, open an autolink, or
  // make a hard break, so the run is one text chunk. One regex test
  // replaces thirteen separate scans.
  if (!RE_FAST.test(src)) {
    const decoded = decodeNumericRefs(src);
    return mode === 'text' ? decoded : escHtml(decoded);
  }
  const hasDelim = src.includes('*') || src.includes('_') || src.includes('~');
  const masked = hasDelim ? maskInline(src, ctx) : src;
  const closers = hasDelim ? scanClosers(masked) : { star: -1, under: -1, tilde: -1 };
  const out = [];
  let rest = src;
  let prevChar = '';
  let keepPrev = false;
  while (rest.length) {
    if (!keepPrev) prevChar = '';
    keepPrev = false;
    let r = null;
    let textChunk = 0;
    const ch = rest[0];
    const cc0 = rest.charCodeAt(0);
    if (cc0 < 128 && CC_TEXTONLY[cc0]) {
      // A space run of 2+ before a newline is a hard break, not text.
      let hardBreak = false;
      if (cc0 === 32) {
        let q = 1;
        while (rest[q] === ' ') q++;
        hardBreak = q >= 2 && rest[q] === '\n';
      }
      if (!hardBreak) textChunk = textChunkLen(rest) || 1;
    }
    if (!r && !textChunk) {
      if (ch === '\\') {
        const cap = RE_INLINE_ESCAPE.exec(rest);
        if (cap) r = { html: mode === 'text' ? cap[1] : escHtml(cap[1]), len: 2 };
      } else if (ch === '<') {
        const cap = RE_TAG.exec(rest);
        if (cap) {
          if (!ctx.inLink && /^<a /i.test(cap[0])) ctx.inLink = true;
          else if (ctx.inLink && /^<\/a>/i.test(cap[0])) ctx.inLink = false;
          if (!ctx.inRaw && /^<(pre|code|kbd|script)(\s|>)/i.test(cap[0])) ctx.inRaw = true;
          else if (ctx.inRaw && /^<\/(pre|code|kbd|script)(\s|>)/i.test(cap[0])) ctx.inRaw = false;
          r = { html: cap[0], len: cap[0].length };
        }
      } else if (ch === '[' || (ch === '!' && rest[1] === '[')) {
        r = tryLink(rest, ctx, mode) || tryReflink(rest, ctx, mode);
      } else if (ch === '*' || ch === '_') {
        r = tryEmStrong(rest, masked, prevChar, ctx, mode, closers);
      } else if (ch === '`') {
        const cap = RE_INLINE_CODE.exec(rest);
        if (cap) {
          let text = cap[2].replace(/\n/g, ' ');
          const hasNonSpace = /[^ ]/.test(text);
          const spaceBothEnds = text.charAt(0) === ' ' && text.charAt(text.length - 1) === ' ';
          if (hasNonSpace && spaceBothEnds) text = text.substring(1, text.length - 1);
          r = { html: mode === 'text' ? text : '<code>' + escHtml(text, true) + '</code>', len: cap[0].length };
        }
      } else if (ch === ' ' || ch === '\\') {
        const cap = RE_BR.exec(rest);
        if (cap) r = { html: mode === 'text' ? '' : '<br>', len: cap[0].length };
      } else if (ch === '~') {
        r = tryDel(rest, masked, prevChar, ctx, mode, closers);
      }
      if (!r && ch === '<') r = tryAutolink(rest, ctx, mode);
      if (!r && (ch === ' ' || ch === '\\')) {
        const cap = RE_BR.exec(rest);
        if (cap) r = { html: mode === 'text' ? '' : '<br>', len: cap[0].length };
      }
      if (!r && !ctx.inLink) {
        // Gate the URL regex: it can only match a mailto:/xmpp: scheme,
        // an http(s):// or ftp:// scheme, www., or an email address
        // (local-part characters then '@'). Anything else cannot match,
        // so skip the regex entirely.
        const c0 = rest.charCodeAt(0);
        let urlMaybe = false;
        if (c0 === 109) urlMaybe = rest.startsWith('mailto:', 0);
        else if (c0 === 120) urlMaybe = rest.startsWith('xmpp:', 0);
        else if (c0 === 104 || c0 === 72 || c0 === 102 || c0 === 70) urlMaybe = protoAt(rest, 0);
        else if (c0 === 119) urlMaybe = rest.startsWith('www.', 0);
        if (!urlMaybe) {
          let k = 0;
          while (k < rest.length) {
            const cc = rest.charCodeAt(k);
            if ((cc >= 48 && cc <= 57) || (cc >= 65 && cc <= 90) || (cc >= 97 && cc <= 122)
              || cc === 46 || cc === 95 || cc === 43 || cc === 45) k++;
            else break;
          }
          urlMaybe = k > 0 && rest[k] === '@';
        }
        if (urlMaybe) r = tryUrl(rest, ctx, mode);
      }
    }
    if (!r && !textChunk) {
      textChunk = textChunkLen(rest) || 1;
    }
    if (textChunk) {
      // Text chunks are the common case: emit them without allocating a
      // result object. When the chunk holds none of & < > " ', both the
      // numeric-reference decode and the escape are identity, so one test
      // replaces two regex passes.
      const raw = rest.slice(0, textChunk);
      if (ctx.inRaw || !RE_TEXT_NEEDS.test(raw)) {
        out.push(raw);
      } else {
        const text = decodeNumericRefs(raw);
        out.push(mode === 'text' ? text : escHtml(text));
      }
      if (rest[textChunk - 1] !== '_') prevChar = rest[textChunk - 1];
      keepPrev = true;
      rest = rest.slice(textChunk);
      continue;
    }
    if (!r) {
      // Nothing matched: emit one literal character rather than stalling.
      // (Marked throws here; a single character keeps the run moving.)
      r = { html: mode === 'text' ? rest[0] : escHtml(rest[0]), len: 1, isText: true };
    }
    out.push(r.html);
    if (r.isText) {
      if (r.len > 0 && rest[r.len - 1] !== '_') prevChar = rest[r.len - 1];
      keepPrev = true;
    }
    rest = rest.slice(r.len);
  }
  return out.join('');
}

// ---------------------------------------------------------------------------
// Block parsing. lexBlocks walks the source front to back, trying each
// construct in the order marked does (blank lines, indented code, fences,
// ATX heading, thematic break, blockquote, list, HTML block, link
// definition, table, setext heading, paragraph, plain text), and returns
// the node tree plus whether a blank line was seen (which decides whether
// a list is loose).
// ---------------------------------------------------------------------------

const RE_LIST_IS_TASK = /^\[[ xX]\][ \t]+\S/;
const RE_LIST_REPLACE_TASK = /^\[[ xX]\][ \t]+/;
const RE_LIST_TASK_CHECKBOX = /\[[ xX]\]/;

const INDENT_RES = new Map();
function indentRe(kind, indent) {
  const c = Math.max(0, Math.min(3, indent - 1));
  const key = kind + ':' + c;
  let re = INDENT_RES.get(key);
  if (re) return re;
  let src;
  if (kind === 'bullet') src = `^ {0,${c}}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))`;
  else if (kind === 'hr') src = `^ {0,${c}}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)`;
  else if (kind === 'fences') src = `^ {0,${c}}(?:\`\`\`|~~~)`;
  else if (kind === 'heading') src = `^ {0,${c}}#{1,6}(?:\\s|$)`;
  else if (kind === 'html') src = `^ {0,${c}}(?:</?(?:${TAG_LIST})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`;
  else src = `^ {0,${c}}>`;
  re = new RegExp(src, kind === 'html' ? 'i' : '');
  INDENT_RES.set(key, re);
  return re;
}

// A fenced code block, matched by hand: the closing fence must be at least
// as long as the opening one, on its own line, and a backtick fence's info
// string may hold no backtick.
function tryFences(src) {
  let i = 0;
  while (i < 3 && src[i] === ' ') i++;
  const fenceCh = src[i];
  if (fenceCh !== '`' && fenceCh !== '~') return null;
  let j = i;
  while (src[j] === fenceCh) j++;
  const fenceLen = j - i;
  if (fenceLen < 3) return null;
  let k = j;
  while (k < src.length && src[k] !== '\n') {
    if (fenceCh === '`' && src[k] === '`') return null;
    k++;
  }
  const info = src.slice(j, k);
  const pos = k < src.length ? k + 1 : k;
  let closeStart = -1;
  let closeEnd = -1;
  let lineStart = pos;
  while (lineStart <= src.length) {
    let ls = lineStart;
    let sp = 0;
    while (sp < 3 && src[ls] === ' ') { ls++; sp++; }
    if (src[ls] === fenceCh) {
      let e = ls;
      while (src[e] === fenceCh) e++;
      if (e - ls >= fenceLen) {
        let t = e;
        while (src[t] === ' ') t++;
        if (t === src.length || src[t] === '\n') {
          closeStart = lineStart;
          closeEnd = t;
          break;
        }
      }
    }
    if (lineStart >= src.length) break;
    const nl = src.indexOf('\n', lineStart);
    if (nl === -1) break;
    lineStart = nl + 1;
  }
  let content;
  let rawLen;
  if (closeStart === -1) {
    content = src.slice(pos);
    rawLen = src.length;
  } else {
    const contentEnd = closeStart > 0 && src[closeStart - 1] === '\n' ? closeStart - 1 : closeStart;
    content = contentEnd > pos ? src.slice(pos, contentEnd) : '';
    rawLen = closeEnd;
  }
  // An indented backtick fence loses up to its own indentation from every
  // content line.
  const raw = src.slice(0, rawLen);
  const indentMatch = /^(\s+)(?:```)/.exec(raw);
  if (indentMatch) {
    const indentToCode = indentMatch[1];
    content = content.split('\n').map((line) => {
      const lead = /^(\s+)/.exec(line);
      if (!lead) return line;
      return line.slice(Math.min(lead[1].length, indentToCode.length));
    }).join('\n');
  }
  const lang = info ? info.trim().replace(RE_ANY_PUNCT, '$1') : info;
  return { node: { k: 'c', txt: content, lang }, len: rawLen };
}

function tryTable(src, ctx) {
  // A table's second line is its delimiter row: it must hold a '-' and a
  // '|' or ':'. Without one the full pattern cannot match.
  const nl = src.indexOf('\n');
  if (nl === -1) return null;
  const nl2 = src.indexOf('\n', nl + 1);
  const delimLine = nl2 === -1 ? src.slice(nl + 1) : src.slice(nl + 1, nl2);
  if (!delimLine.includes('-') || (!delimLine.includes('|') && !delimLine.includes(':'))) return null;
  const cap = RE_TABLE.exec(src);
  if (!cap) return null;
  if (!/[:|]/.test(cap[2])) return null;
  const headers = splitCells(cap[1]);
  const aligns = cap[2].replace(/^\||\| *$/g, '').split('|');
  const rows = cap[3] && cap[3].trim() ? cap[3].replace(/\n[ \t]*$/, '').split('\n') : [];
  if (headers.length !== aligns.length) return null;
  const align = aligns.map((a) => {
    if (/^ *-+: *$/.test(a)) return 'right';
    if (/^ *:-+: *$/.test(a)) return 'center';
    if (/^ *:-+ *$/.test(a)) return 'left';
    return null;
  });
  const head = headers.map((h, i) => ({ s: h, align: align[i], head: true }));
  const body = rows.map((row) => splitCells(row, headers.length)
    .map((cell, i) => ({ s: cell, align: align[i], head: false })));
  const raw = rtrimChar(cap[0], '\n');
  return { node: { k: 'table', head, rows: body }, len: raw.length };
}

function tryDef(src, ctx) {
  const cap = RE_DEF.exec(src);
  if (!cap) return null;
  // Outside angle brackets a destination holds only balanced parentheses.
  if (cap[2].charAt(0) !== '<' && findClosingBracket(cap[2], '()') !== -1) return null;
  const tag = normLabel(cap[1]);
  const href = cap[2] ? cap[2].replace(/^<(.*)>$/, '$1').replace(RE_ANY_PUNCT, '$1') : '';
  const title = cap[3] ? cap[3].substring(1, cap[3].length - 1).replace(RE_ANY_PUNCT, '$1') : cap[3];
  const raw = rtrimChar(cap[0], '\n');
  return { tag, href, title, raw, len: raw.length };
}

// What a line can start, for the list-item break tests below. Every break
// pattern is anchored with at most three leading spaces, so a line with
// four or more, or one starting with any other character, can match none
// of them and skips all six regexes. The return value says which tests
// could still match: 1 = fence/heading/html/blockquote, 2 = bullet/hr,
// 3 = ordered bullet only.
function lineBreakKind(line) {
  let i = 0;
  while (i < 3 && line.charCodeAt(i) === 32) i++;
  if (i === 3 && line.charCodeAt(3) === 32) return 0;
  const c = line.charCodeAt(i);
  if (c === 62 || c === 35 || c === 96 || c === 126 || c === 60) return 1;
  if (c === 45 || c === 42 || c === 95 || c === 43) return 2;
  if (c >= 48 && c <= 57) return 3;
  return 0;
}

// Index of the first character that is not a space, or -1 (like
// s.search(/[^ ]/)). True when a single line holds only whitespace
// (like !s.trim()). Column of the first non-space character with each
// tab counting as four spaces (like s.replace(/\t/g, '    ').search(...)).
function firstNonSpace(s) {
  let k = 0;
  while (s.charCodeAt(k) === 32) k++;
  return k < s.length ? k : -1;
}
const RE_BLANK_ONLY = /^\s*$/;
function expandedIndent(s) {
  let col = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 32) col++;
    else if (c === 9) col += 4;
    else return col;
  }
  return -1;
}
function tryList(src, ctx) {
  // A list starts with a bullet (-, *, +) or a digit after at most three
  // spaces; anything else cannot match, so skip the regex entirely.
  let i = 0;
  while (i < 3 && src.charCodeAt(i) === 32) i++;
  const c0 = src.charCodeAt(i);
  if (c0 !== 45 && c0 !== 42 && c0 !== 43 && !(c0 >= 48 && c0 <= 57)) return null;
  const cap0 = RE_LIST_START.exec(src);
  if (!cap0) return null;
  const listSrc = src;
  let rest = src;
  let bull = cap0[1].trim();
  const isOrdered = bull.length > 1;
  const list = {
    k: 'list', ord: isOrdered, start: isOrdered ? +bull.slice(0, -1) : 0,
    loose: false, items: [], raw: '',
  };
  bull = isOrdered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;
  const itemRe = new RegExp(`^( {0,3}${bull})((?:[\\t ][^\\n]*)?(?:\\n|$))`);
  let endsWithBlank = false;
  while (rest.length) {
    let endEarly = false;
    const itemParts = [];
    const cap = itemRe.exec(rest);
    if (!cap) break;
    if (RE_HR.test(rest)) break;
    const itemStart = listSrc.length - rest.length;
    rest = rest.slice(cap[0].length);
    const firstLine = cap[2].split('\n', 1)[0];
    const bulletIndent = cap[1].length;
    const line0 = firstLine.replace(/^[ \t]+/, (ws) => expandTabs(ws, bulletIndent));
    let line = line0;
    const nl0 = rest.indexOf('\n');
    let nextLine = nl0 === -1 ? rest : rest.slice(0, nl0);
    let blankLine = RE_BLANK_ONLY.test(line);
    let indent;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = firstNonSpace(line);
      indent = indent > 4 ? 1 : indent;
      itemParts.push(line.slice(indent));
      indent += bulletIndent;
    }
    if (blankLine && RE_BLANK_LINE.test(nextLine)) {
      rest = rest.slice(nextLine.length + 1);
      endEarly = true;
    }
    if (!endEarly) {
      const nextBulletRe = indentRe('bullet', indent);
      const hrRe = indentRe('hr', indent);
      const fencesRe = indentRe('fences', indent);
      const headingRe = indentRe('heading', indent);
      const htmlRe = indentRe('html', indent);
      const bqRe = indentRe('bq', indent);
      while (rest.length) {
        const nl = rest.indexOf('\n');
        const rawLine = nl === -1 ? rest : rest.slice(0, nl);
        nextLine = rawLine;
        const nextLineNoTabs = (rawLine.charCodeAt(0) === 32 || rawLine.charCodeAt(0) === 9)
          ? rawLine.replace(/^[ \t]+/, (ws) => expandTabs(ws)) : rawLine;
        const kind = lineBreakKind(nextLine);
        if (kind === 1) {
          if (fencesRe.test(nextLine)) break;
          if (headingRe.test(nextLine)) break;
          if (htmlRe.test(nextLine)) break;
          if (bqRe.test(nextLine)) break;
        } else if (kind === 2) {
          if (nextBulletRe.test(nextLine)) break;
          if (hrRe.test(nextLine)) break;
        } else if (kind === 3) {
          if (nextBulletRe.test(nextLine)) break;
        }
        if (firstNonSpace(nextLineNoTabs) >= indent || RE_BLANK_ONLY.test(nextLine)) {
          itemParts.push(nextLineNoTabs.slice(indent));
        } else {
          if (blankLine) break;
          if (expandedIndent(line) >= 4) break;
          const lkind = lineBreakKind(line);
          if (lkind === 1) {
            if (fencesRe.test(line)) break;
            if (headingRe.test(line)) break;
            if (htmlRe.test(line)) break;
          } else if (lkind === 2) {
            if (hrRe.test(line)) break;
          }
          // A lazy continuation that looks like a setext underline stays
          // in the paragraph, indented so it cannot become one.
          const setextCont = /^ {0,3}(?:=+|-+) *$/.test(nextLine)
            && RE_LHEADING.test(line + '\n' + nextLine);
          const cont = setextCont
            ? '    ' + nextLineNoTabs.replace(/^ {0,3}/, '')
            : nextLine;
          itemParts.push(cont);
        }
        blankLine = RE_BLANK_ONLY.test(nextLine);
        rest = nl === -1 ? '' : rest.slice(nl + 1);
        line = nextLineNoTabs.slice(indent);
      }
    }
    const raw = listSrc.slice(itemStart, listSrc.length - rest.length);
    if (!list.loose) {
      if (endsWithBlank) list.loose = true;
      else if (/\n[ \t]*\n[ \t]*$/.test(raw)) endsWithBlank = true;
    }
    list.items.push({ task: false, text: itemParts.join('\n'), kids: [], raw });
  }
  const lastItem = list.items[list.items.length - 1];
  if (!lastItem) return null;
  lastItem.raw = lastItem.raw.trimEnd();
  lastItem.text = lastItem.text.trimEnd();
  list.raw = listSrc.slice(0, listSrc.length - rest.length).trimEnd();
  // Tokenize the items, then decide looseness from blank lines inside them.
  for (const item of list.items) {
    item.task = RE_LIST_IS_TASK.test(item.text);
    const inner = lexBlocks(item.text, false, ctx);
    item.kids = inner.nodes;
    if (!list.loose && inner.blank) list.loose = true;
  }
  // Place the task checkboxes, using the final looseness.
  for (const item of list.items) {
    const first = item.kids[0];
    if (item.task && first && (first.k === 't' || first.k === 'p')) {
      item.text = item.text.replace(RE_LIST_REPLACE_TASK, '');
      first.s = first.s.replace(RE_LIST_REPLACE_TASK, '');
      const taskRaw = RE_LIST_TASK_CHECKBOX.exec(item.raw);
      if (taskRaw) {
        const checked = taskRaw[0] !== '[ ]';
        const chk = '<input ' + (checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        if (list.loose) {
          first.pre = chk;
        } else {
          item.kids.unshift({ k: 'chk', checked });
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (list.loose) {
    for (const item of list.items) {
      for (const kid of item.kids) {
        if (kid.k === 't') kid.k = 'p';
      }
    }
  }
  return { node: list, len: list.raw.length };
}

function tryBlockquote(src, ctx) {
  const cap = RE_BLOCKQUOTE.exec(src);
  if (!cap) return null;
  let lines = rtrimChar(cap[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const kids = [];
  const st = { lastKind: 'none' };
  while (lines.length > 0) {
    let inBq = false;
    const cur = [];
    let i;
    for (i = 0; i < lines.length; i++) {
      if (/^ {0,3}>/.test(lines[i])) {
        cur.push(lines[i]);
        inBq = true;
      } else if (!inBq) {
        cur.push(lines[i]);
      } else {
        break;
      }
    }
    lines = lines.slice(i);
    const curRaw = cur.join('\n');
    const curText = curRaw
      .replace(/^( {0,3}>)([ \t]+)/gm, (_, marker, ws) => marker + expandTabs(ws, marker.length))
      .replace(/\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g, '\n    $1')
      .replace(/^ {0,3}>[ \t]?/gm, '');
    raw = raw ? raw + '\n' + curRaw : curRaw;
    text = text ? text + '\n' + curText : curText;
    const inner = lexBlocks(curText, true, ctx, kids, true, st);
    if (lines.length === 0) break;
    const last = kids[kids.length - 1];
    if (!last) continue;
    if (last.k === 'c' || last.k === 'h' || last.k === 'hr' || last.k === 'html' || last.k === 'table') break;
    if (last.k === 'bq') {
      // Lazy lines after a nested blockquote belong to it, with one more
      // marker stripped.
      const continuation = lines.join('\n');
      const newText = last.raw + '\n' + continuation.replace(/^ {0,3}>[ \t]?/gm, '');
      const nt = tryBlockquote(newText, ctx);
      if (!nt) break;
      kids[kids.length - 1] = nt.node;
      const leftover = newText.slice(nt.node.raw.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw = raw + '\n' + consumed.join('\n');
      text = text.slice(0, text.length - last.text.length) + nt.node.text;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && /^ {0,3}>/.test(lines[0])) continue;
      break;
    }
    if (last.k === 'list') {
      const newText = last.raw + '\n' + lines.join('\n');
      const nt = tryList(newText, ctx);
      if (!nt) break;
      kids[kids.length - 1] = nt.node;
      const consumedCount = nt.node.raw.length > last.raw.length
        ? newText.slice(last.raw.length + 1, nt.node.raw.length).split('\n').length
        : 0;
      if (consumedCount > 0) {
        const consumed = lines.slice(0, consumedCount).join('\n');
        raw = raw + '\n' + consumed;
        text = text + '\n' + consumed;
      }
      lines = lines.slice(consumedCount);
      continue;
    }
  }
  return { node: { k: 'bq', kids, raw, text }, len: raw.length };
}

function lexBlocks(src, top, ctx, target, continuation, st) {
  const nodes = target || [];
  const state = st || { lastKind: 'none' };
  let blank = false;
  let guard = src.length + 1;
  let mergedThisCall = false;
  while (src.length) {
    if (src.length >= guard) throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
    guard = src.length;
    let m;
    if ((m = RE_SPACE.exec(src))) {
      if ((m[0].match(/\n/g) || []).length >= 2) blank = true;
      // A lone newline is folded into the previous token; a longer run of
      // blank lines is a token of its own, so later merges must not see
      // the paragraph or text token behind it.
      if (m[0].length !== 1) state.lastKind = 'space';
      src = src.slice(m[0].length);
      continue;
    }
    if ((m = RE_INDENT_CODE.exec(src))) {
      const raw = trimTrailingBlankLines(m[0]);
      const text = raw.replace(RE_CODE_INDENT, '');
      const last = nodes[nodes.length - 1];
      if (last && (state.lastKind === 'p' || state.lastKind === 't')) {
        last.s += '\n' + text;
      } else {
        nodes.push({ k: 'c', txt: text, lang: '' });
        state.lastKind = 'c';
      }
      src = src.slice(raw.length);
      continue;
    }
    const fenced = tryFences(src);
    if (fenced) {
      nodes.push(fenced.node);
      state.lastKind = 'c';
      src = src.slice(fenced.len);
      continue;
    }
    if ((m = RE_ATX.exec(src))) {
      let text = m[2].trim();
      if (/#$/.test(text)) {
        const trimmed = rtrimChar(text, '#');
        if (!trimmed || /[ \t]$/.test(trimmed)) text = trimmed.trim();
      }
      const raw = rtrimChar(m[0], '\n');
      nodes.push({ k: 'h', d: m[1].length, s: text });
      state.lastKind = 'h';
      src = src.slice(raw.length);
      continue;
    }
    if ((m = RE_HR.exec(src))) {
      const raw = rtrimChar(m[0], '\n');
      nodes.push({ k: 'hr' });
      state.lastKind = 'hr';
      src = src.slice(raw.length);
      continue;
    }
    const bq = tryBlockquote(src, ctx);
    if (bq) {
      nodes.push(bq.node);
      state.lastKind = 'bq';
      src = src.slice(bq.len);
      continue;
    }
    const list = tryList(src, ctx);
    if (list) {
      nodes.push(list.node);
      state.lastKind = 'list';
      src = src.slice(list.len);
      continue;
    }
    if ((m = RE_HTML_BLOCK.exec(src))) {
      const raw = trimTrailingBlankLines(m[0]);
      nodes.push({ k: 'html', s: raw });
      state.lastKind = 'html';
      src = src.slice(raw.length);
      continue;
    }
    const def = tryDef(src, ctx);
    if (def) {
      const last = nodes[nodes.length - 1];
      if (last && (state.lastKind === 'p' || state.lastKind === 't')) {
        last.s += '\n' + def.raw;
      } else {
        if (!ctx.links.has(def.tag)) ctx.links.set(def.tag, { href: def.href, title: def.title });
      }
      src = src.slice(def.len);
      continue;
    }
    const table = tryTable(src, ctx);
    if (table) {
      nodes.push(table.node);
      state.lastKind = 'table';
      src = src.slice(table.len);
      continue;
    }
    if ((m = RE_LHEADING.exec(src))) {
      const raw = rtrimChar(m[0], '\n');
      nodes.push({ k: 'h', d: m[2].charAt(0) === '=' ? 1 : 2, s: m[1].trim() });
      state.lastKind = 'h';
      src = src.slice(raw.length);
      continue;
    }
    if (top && (m = RE_PARAGRAPH.exec(src))) {
      let text = m[1];
      if (text.charAt(text.length - 1) === '\n') text = text.slice(0, -1);
      const last = nodes[nodes.length - 1];
      if (continuation && !mergedThisCall && last && state.lastKind === 'p') {
        // A continuation chunk's first paragraph joins the paragraph the
        // previous chunk ended with.
        last.s += '\n' + text;
      } else {
        nodes.push({ k: 'p', s: text });
      }
      state.lastKind = 'p';
      mergedThisCall = true;
      src = src.slice(m[0].length);
      continue;
    }
    if ((m = RE_TEXT.exec(src))) {
      const last = nodes[nodes.length - 1];
      if (last && state.lastKind === 't') {
        last.s += '\n' + m[0];
      } else {
        nodes.push({ k: 't', s: m[0] });
        state.lastKind = 't';
      }
      src = src.slice(m[0].length);
      continue;
    }
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
  }
  return { nodes, blank };
}

// ---------------------------------------------------------------------------
// Rendering the node tree to HTML.
// ---------------------------------------------------------------------------

function tableCell(cell, ctx) {
  const content = renderInline(cell.s, ctx, 'html', true);
  const tag = cell.head ? 'th' : 'td';
  const open = cell.align ? `<${tag} align="${cell.align}">` : `<${tag}>`;
  return open + content + `</${tag}>\n`;
}

function renderNodes(nodes, ctx) {
  const out = [];
  for (const n of nodes) {
    switch (n.k) {
      case 'p':
        out.push('<p>' + (n.pre || '') + renderInline(n.s, ctx, 'html', true) + '</p>\n');
        break;
      case 't':
        out.push(renderInline(n.s, ctx, 'html', true));
        break;
      case 'h':
        out.push('<h' + n.d + '>' + renderInline(n.s, ctx, 'html', true) + '</h' + n.d + '>\n');
        break;
      case 'c': {
        const langStr = (n.lang || '').match(/^\S*/)?.[0];
        const code = n.txt ? n.txt.replace(/\n$/, '') + '\n' : '';
        const body = escHtml(code, true);
        out.push(langStr
          ? '<pre><code class="language-' + escHtml(langStr) + '">' + body + '</code></pre>\n'
          : '<pre><code>' + body + '</code></pre>\n');
        break;
      }
      case 'hr':
        out.push('<hr>\n');
        break;
      case 'html':
        out.push(n.s);
        break;
      case 'bq':
        out.push('<blockquote>\n' + renderNodes(n.kids, ctx) + '</blockquote>\n');
        break;
      case 'list': {
        let body = '';
        for (const item of n.items) body += '<li>' + renderNodes(item.kids, ctx) + '</li>\n';
        const tag = n.ord ? 'ol' : 'ul';
        const startAttr = (n.ord && n.start !== 1) ? ' start="' + n.start + '"' : '';
        out.push('<' + tag + startAttr + '>\n' + body + '</' + tag + '>\n');
        break;
      }
      case 'chk':
        out.push('<input ' + (n.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ');
        break;
      case 'table': {
        let header = '';
        for (const cell of n.head) header += tableCell(cell, ctx);
        let body = '';
        for (const row of n.rows) {
          let cells = '';
          for (const cell of row) cells += tableCell(cell, ctx);
          body += '<tr>\n' + cells + '</tr>\n';
        }
        if (body) body = '<tbody>' + body + '</tbody>';
        out.push('<table>\n<thead>\n<tr>\n' + header + '</tr>\n</thead>\n' + body + '</table>\n');
        break;
      }
    }
  }
  return out.join('');
}

export function parse(markdown) {
  const ctx = {
    links: new Map(),
    inLink: false,
    inRaw: false,
    linkEmitted: false,
    parenOk: true,
  };
  const src = markdown.replace(/\r\n|\r/g, '\n');
  const { nodes } = lexBlocks(src, true, ctx);
  return renderNodes(nodes, ctx);
}
