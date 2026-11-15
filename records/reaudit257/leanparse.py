"""Lean ファイルを宣言ごとに分ける（再照合の入力づくり用）。"""
import re

DECL_RE = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?'
                     r'(theorem|lemma|def|abbrev|instance|structure)\b\s*([^\s:({\[]*)')
CTX_RE = re.compile(r'^(open |variable |namespace |end |section|omit |set_option |universe )')


def strip_comments(text):
    """/- -/ のブロック（docstring・節の見出しを含む）と -- のコメントを除く。"""
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    out = []
    for line in text.split('\n'):
        # 文字列の中の -- はこのコードベースにはない前提
        i = line.find('--')
        if i >= 0:
            line = line[:i].rstrip()
            if not line.strip():
                continue
        out.append(line)
    return '\n'.join(out)


def top_level_assign(text):
    """最初のトップレベルの ':=' の位置（括弧の外）。なければ -1。"""
    depth = 0
    pairs = {'(': ')', '[': ']', '{': '}', '⟨': '⟩'}
    closers = set(pairs.values())
    i = 0
    while i < len(text):
        c = text[i]
        if c in pairs:
            depth += 1
        elif c in closers:
            depth -= 1
        elif c == ':' and text[i:i + 2] == ':=' and depth == 0:
            return i
        i += 1
    return -1


def parse(path):
    s = open(path, encoding='utf-8').read()
    lines = s.split('\n')
    # モジュールの docstring（先頭の /-! ... -/ または /- ... -/）
    module_doc = ''
    m = re.search(r'/-[!]?(.*?)-/', s, flags=re.S)
    if m and s[:m.start()].strip().startswith('import') is False and m.start() < 200:
        module_doc = m.group(0)
    decls = []
    i = 0
    pending_doc = None
    pending_prefix = []
    while i < len(lines):
        l = lines[i]
        if l.startswith('/--'):
            j = i
            buf = [l]
            while '-/' not in lines[j]:
                j += 1
                buf.append(lines[j])
            pending_doc = '\n'.join(buf)
            i = j + 1
            continue
        if l.startswith('open Classical in') or re.match(r'^omit .* in\s*$', l):
            pending_prefix.append(l)
            i += 1
            continue
        mm = DECL_RE.match(l)
        if mm:
            kind, name = mm.group(1), mm.group(2)
            j = i + 1
            while j < len(lines):
                lj = lines[j]
                if (DECL_RE.match(lj) or lj.startswith('/--') or lj.startswith('#print')
                        or CTX_RE.match(lj) or lj.startswith('open Classical in')
                        or re.match(r'^omit .* in\s*$', lj)):
                    break
                j += 1
            body = '\n'.join(lines[i:j]).rstrip()
            decls.append(dict(kind=kind, name=name, doc=pending_doc, prefix=list(pending_prefix),
                              text=body, line=i + 1))
            pending_doc = None
            pending_prefix = []
            i = j
            continue
        if l.strip() and not l.startswith('#print'):
            pending_prefix = []
        i += 1
    return module_doc, decls


def statement(decl):
    """定理なら証明を除いた文、定義なら全文（コメントを除く）。"""
    t = strip_comments(decl['text'])
    if decl['kind'] in ('theorem', 'lemma'):
        k = top_level_assign(t)
        if k >= 0:
            t = t[:k].rstrip()
    pre = '\n'.join(decl['prefix'])
    return (pre + '\n' if pre else '') + t
