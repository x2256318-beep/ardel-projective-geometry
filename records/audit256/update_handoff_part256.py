#!/usr/bin/env python3
"""引き継ぎメモを Part 256 完了時点に更新する（final74 → final75）。"""
SRC = '/home/claude/out/final74/PAG2_handoff_part255.md'
DST = '/home/claude/out/final75/PAG2_handoff_part256.md'
s = open(SRC, encoding='utf-8').read()


def rep(a, b, count=1):
    global s
    n = s.count(a)
    assert n == count, (n, a[:80])
    s = s.replace(a, b)


rep('# PAG 2.0 引き継ぎメモ（Part 255 完了時点、2026-11-13）', '# PAG 2.0 引き継ぎメモ（Part 256 完了時点、2026-11-13）')
rep('## 進め方のルール（そのまま継続）\n', '''## 進め方のルール（そのまま継続）
- **（Part 256 の盲検と独立照合 B の教訓）ルート数・ε 因子について「大域は局所の積ではない」と書かない。** 大域の ε 因子は局所の ε 因子の積（Tate、Deligne）。ずれるのは、ディリクレ指標を中国剰余定理で分けた成分のルート数の積。存在の例で支える主張には「一般には」を付ける。題と問いは、形式文が答える範囲（どの指標の上か、原始か、法はいくつか）に合わせる。
''')
rep('- 次の番号：Part 256 ＝ PAG260 ＝ step279。xlsx は 3529 項目・手順 275 から続ける（', '- 次の番号：Part 257 ＝ PAG261 ＝ step280。xlsx は 3552 項目・手順 276 から続ける（')
rep('## これまでの成果（Part 155〜255）', '## これまでの成果（Part 155〜256）')

item77 = '''77. **互いに素な法の原始指標の積の上での、貼り合わせ U の固有値：交差項の法則（Part 256、PAG260、step279。著者が 2026-11-13 18:15 に候補 M1 を選んだ）**
   - 問い：互いに素な法 M, N の貼り合わせから、法 M·N の貼り合わせは決まるか。Lean が答えるのは、原始指標の積 1 つの上の固有値まで。
   - def `prodChar`（法 M·N の指標 χ₁χ₂）、`crtMap`（(a₁, a₂) ↦ a₁N + a₂M）、`crossSign`（s：両方が奇なら −1、それ以外は 1）。
   - 中身のある文（独立照合 A・B の区別）：`crtMap_bijective`（中国剰余定理）、**`gaussSum_prodChar`**（τ(χ₁χ₂) = χ₁(N)χ₂(M)τ(χ₁)τ(χ₂)。原始性は要らない）、**`rootNum_prodChar`**（W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)）、`isPrimitive_prodChar`（原始指標の積は原始）。
   - 言い換え・帰結：`parFac_prodChar`（偶奇の因子のずれ）、`phaseA1_prodChar`・`UA1_charU_prodChar`（公準 A1 の位相と U での形。指標 1 つの上の固有値の式）、`norm_cross`（交差項の絶対値 1）、`cross_eq_sign_of_rootNum_one`（3 つの位相が 1 なら s·交差項 = 1。相互法則と同じ形だが、相互法則を示してはいない。h は余分）。
   - 存在の例：`rootNum_prodChar_ne_mul`・`phaseA1_prodChar_ne_mul`（法 15、奇の原始指標の組で W(χ₁χ₂) ≠ W(χ₁)W(χ₂)）、`rootNum_prodChar_eq_neg_mul`（法 39、交差項 1 で W(χ₁χ₂) = −W(χ₁)W(χ₂)。符号だけでずれる例。独立照合 B の後に足した）、`exists_primitive_odd_five`。
   - 補助：`cast_crtMap_fst`・`cast_crtMap_snd`・`stdAddChar_crtMap`・`prodChar_apply`・`prodChar_neg_one`・`crossSign_of_odd`・`crossSign_of_even_left`・`crossSign_of_even_right`・`norm_char_unit`・`charU_prodChar`。
   - 既知（確信度：高）。Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合。新規候補なし。A1 は公準のまま（この法則はルート数についての恒等式で、A1 から何かを出すものではない）。
   - 読み：交差項は相手の法を自分の指標で読んだ値。符号 s は偶奇の因子（文献では無限素点の局所因子）から出る。文献の名前（独立照合 C）：不分岐な指標でひねったときの ε 因子の変化、(−1)^{a₁a₂}（ヒルベルト記号 (−1, −1)_∞ と同じ形）。
   - Lean にしていないこと：法 M·N のすべての指標が積の形に一意に書けること、原始でない指標の法則（導手での交差項 χ₁*(d₂)χ₂*(d₁)。数値 (4)）、作用素全体の式、3 つ以上の法（数値 (7)）、互いに素を外した形（両辺 0。数値 (10)）、交差項だけでずれる例と等号の例（数値 (13)）、F_q[t]（数値 (5)）、イデール類指標の局所成分。
   - 数値（step279、13 項目すべて合格、1 回目で通った。(13) は B の後に足した）。
   - コンパイル：試しのファイルで段階的に通した。組み立ての 1 回目は docstring を `omit … in` の前に置いて rc = 1、2 回目で rc = 0。B の後に 1 文を足して組み立て直し rc = 0。sorry 0、警告 0、#print axioms 23 行（21 行が [propext, Classical.choice, Quot.sound]、2 行が [propext, Quot.sound]）。
   - 独立照合：ノートの §7、`pag2_part256_independent_audit.md`、`audit256/`。A・B・C ともツール使用 0。A「22 文は正しく読め、標準」、C「標準を超える内容はない」、B「偽・空虚・別物なし。題の問いに答え切っていない、『積ではない』は全称に読める、符号だけの例がない」。弱点：B への入力は A の要約とノートの一部、B の出力は要点だけ保存、23 個目の文は照合の後に足したので A・B・C は見ていない。

## 点検（2026-10-24、Part 204 の後）'''
rep('\n## 点検（2026-10-24、Part 204 の後）', '\n' + item77)

a = '- Part 255 の後（2026-11-13）：PAG.lean〜PAG259.lean の危険な構文 0'
i = s.index(a); j = s.index('\n', i)
s = s[:j] + '\n- Part 256 の後（2026-11-13）：PAG.lean〜PAG260.lean の危険な構文 0、theorem/lemma 3525・#print axioms 3826（PAG_axioms_supplement の 36 行を除く）、xlsx（final75）3552 行で問題 0（Part 256 は行 3531〜3553、23 行 = theorem 数）、検証手順 276。PAG260 の #print axioms 23 行は標準の公理の範囲（2 行は [propext, Quot.sound]）。xlsx は LibreOffice で再計算し、式 5 個にエラーなし（集計の値：検証完了 3552、完了した手順 276/276）。' + s[j:]

a = '- PAG259（PAG.Part259）：'
i = s.index(a); j = s.index('\n', i)
s = s[:j] + '\n- PAG260（PAG.Part260）：`prodChar`・`crtMap`・`crossSign`（def）, `cast_crtMap_fst`, `cast_crtMap_snd`, `crtMap_bijective`, `stdAddChar_crtMap`, `prodChar_apply`, `gaussSum_prodChar`, `prodChar_neg_one`, `crossSign_of_odd`, `crossSign_of_even_left`, `crossSign_of_even_right`, `parFac_prodChar`, `rootNum_prodChar`, `isPrimitive_prodChar`, `phaseA1_prodChar`, `UA1_charU_prodChar`, `cross_eq_sign_of_rootNum_one`, `exists_primitive_odd_five`, `rootNum_prodChar_ne_mul`, `rootNum_prodChar_eq_neg_mul`, `phaseA1_prodChar_ne_mul`, `norm_char_unit`, `norm_cross`, `charU_prodChar`' + s[j:]

errs = '''- （Part 256）`Finset.sum_mul_sum` で 2 重の和を積に直す前に、被加数を `mul_assoc` などで (a₁ の式)·(a₂ の式) の形に並べる。
- （Part 256）命題の `if`（`if χ₁.Odd ∧ χ₂.Odd then −1 else 1`）には Decidable の instance がない。`open Classical in` を def に付け、値は補題（`crossSign_of_odd` など）で取り出す。
- （Part 256）`decide` は、文脈に `Fact` の仮定があると「自由変数」で止まる。`decide` で示す事実を、`Fact` を置く前に `have` で並べる。`Nat.Prime 13` は `norm_num` で示せず `by decide` で通った。
- （Part 256）`Mathlib.NumberTheory.DirichletCharacter.Bounds`（`unit_norm_eq_one`）はこの環境で未ビルド。同じ証明を `norm_char_unit` として置いた。
- （Part 256）docstring は `omit … in` の後に置く（前に置くと構文エラー）。
- （Part 256）使った Mathlib の名前：`ZMod.stdAddChar_coe`、`DirichletCharacter.changeLevel_eq_cast_of_dvd`、`conductor_mul_dvd_lcm_conductor`、`conductor_inv`、`conductor_changeLevel`、`DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity`。

## 収束アラームの状況（CLAUDE.md §7、Part 256 の後）
- 辞書の未記入の件数：0（Part 256 の名前は辞書 §16）。
- 文献照合の未実施の連続パート数：0（着手前の盲検の問いテスト。独立照合 C の名前のウェブでの確認：Rosen 第 3 章 Theorem 3.3、Tate (3.2.6.3)、Buzzard のノート、Iwaniec–Kowalski Section 3.4（式番号は未確認）。ヒルベルト記号との対応は未確認）。
- **兆候 4（既知の事実だけ）：8 パート連続**（Part 249〜256）。着手前に報告し、著者が M1 を選んだ。
- **第 3 の型（主張の格上げ）の検知**：着手前の盲検で言い方 3 つ（「局所の積ではない」「ℚ に固有なのは符号だけ」「相互法則になる」）、独立照合 B で題と「積ではない」の範囲が直された。Part 255 に続いて同じ向き（解釈の言葉に寄せて広く書く）。
- **第 2 の型（注入→回収）**：A1 を外すと位相は自由に戻り、交差項の法則は位相の選び方への制約ではなくなる。A1 は公準のまま。
- **第 11 の型（仮定の除去）**：互いに素を外しても等式は成り立つが両辺 0（数値 (10)、A の手計算）。Lean は仮定つきのまま。
- 兆候 1〜3：出ていない。

## 収束アラームの状況（CLAUDE.md §7、Part 255 の後）'''
rep('\n## 収束アラームの状況（CLAUDE.md §7、Part 255 の後）', '\n' + errs)
rep('## 収束アラームの状況（CLAUDE.md §7、Part 255 の後）\n', '## 収束アラームの状況（CLAUDE.md §7、Part 255 の後。記録として残す）\n')

a = '- **Part 256 の着手前（2026-11-13 夕。17:58 の「進めてください」を受けて）**：'
rep('**著者の選択待ち。Lean と Part 256 は始めていない。**', '著者が M1 を選び（18:15）、Part 256 として実施した（上の成果の 77）。')
rep(a, '''- **Part 256 の後（2026-11-13 夜）**：M1 は、原始指標の積 1 つの上の固有値の法則として、既知の事実の Lean 化で書けた（上の成果の 77）。次（Part 257 ＝ PAG261 ＝ step280）は著者が選ぶ。**Part 257 は始めていない。** 着手前の 4 点、盲検の問いテスト、パートを閉じるときの独立照合は続く。M1 の続きとして残るもの：原始でない指標を含めた法則、作用素の形、イデール類指標の局所成分での書き直し。残る大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象、有限レベルの Bost–Connes。兆候 4 は 8 パート連続。
''' + a.replace('**：', '**（済み）：'))

a = 'Part 255 の後は theorem/lemma 3,502、xlsx 3,529、次は Part 256 ＝ PAG260 ＝ step279。'
rep(a, a + 'Part 256 の後は theorem/lemma 3,525、xlsx 3,552、次は Part 257 ＝ PAG261 ＝ step280。')
s = s.rstrip('\n') + '\n- 2026-11-13：`pag2_part256_preregistration.md` の候補 M1 の題「貼り合わせ U は素点ごとに分かれるか」と、ノートの最初の版（`audit256/note_v1_before_audit.md`・`note_v2_before_B_fixes.md`）の「固有値は積ではありません」は、形式文より広い。Part 256 のノートでは「互いに素な法の原始指標の積の上での固有値」「一般には積ではない」に直した。着手前の文書の本文は未修正。\n'
open(DST, 'w', encoding='utf-8').write(s)
print('saved', DST, len(s))
