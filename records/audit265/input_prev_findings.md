# 入力 3：前回の照合の指摘（成果物 4）

## 成果物 4：散文と形式文のずれ

問題のなかった点：A の 11 宣言はすべて正しい名前で散文に出ている。28 行目（局所的な単位元）と 29 行目（左単位元がない）は形式文と同じ範囲で、30〜31 行目の証明の筋も A と一致。「範囲（Lean にしていないもの）」の 3 項目は確かに A にない。A にあるのに外と書かれたものもない。Part と PAG の番号の対応（254 = 258、260 = 264、261 = 265）は合っている。

指摘：
1. （中）「局所単位元をもつ環」は A より強い文。49 行目「局所的な単位元を持つ非単位的な環（rings with local units）は標準の概念」、40 行目「極限は局所的な単位元を持つ非単位的な代数になる」。標準の定義（Ánh–Márki、Abrams）は、有限集合ごとに冪等元 e があって F ⊆ eRe となることを要求する。A にあるのは 1 元ごとの両側単位元だけで、冪等性も有限集合への共通化もない（1 元ごとの形はむしろ Tominaga の s-unital に近い。定義の確信度は中、記憶によるもので文献は照合していない）。直し方：(a) Lean に `ofCorner a 1 * ofCorner a 1 = ofCorner a 1` と a ∣ b のときの `ofCorner a 1 * ofCorner b 1 = ofCorner a 1`（両側）を足す、または (b) 文面を「各元を両側から固定する e_a = ι_a(1) がある（冪等性・有限集合への共通化は Lean の外、直ちに出る見込み）」に直す。
2. （中、出所：入力外）40 行目「D 側で殻の span に入らない角の写像（Part 260）」は、37 行目で「前の Part の Lean の文との並置」と位置づけているが、入力 1 にこの文はない。CLAUDE.md の要約では Part 260 で Lean にあるのは (2,4) の証人だけで、一般の場合は数値のみ。直し方：「D 側で殻の span に入らない（(2,4) は Lean、一般には数値。Part 260）」。
3. （低〜中）38〜40 行目の対比の並べ方は、素数冪の段が極限が非単位的になる原因のように読める。成果物 3 のとおり not_exists_left_one は狭義の段 c → 2c と φ(1) ≠ 1 だけで出て、無平方数の部分系でも同じ証明が通る。直し方：「単位元がないことは素数冪の段によらない（cornerOp がどの狭義の段でも非単位的であることによる。部分系での文は Lean にしていない）」を 1 行足す。
4. （低）17 行目「`DirectLimit`（Mathlib/Algebra/Colimit/DirectLimit.lean）による帰納極限」：入力 1 の B では、型の定義は Mathlib/Order/DirectedInverseSystem.lean、環・代数の構造が Algebra/Colimit 側。直し方：「Order/DirectedInverseSystem.lean の `DirectLimit`（非単位的な環・代数の構造は Algebra/Colimit/DirectLimit.lean）」。
5. （低）62 行目「対象 11 件、候補上位 20、380 回」：11 × 20 = 220 で、380 は 19 × 20。内訳を書く。
6. （低）34 行目「正規化なしでも成り立ち」：手計算では確かめられるが、Lean の文は正規化つきの cornerOp についてのもの。「（手計算。Lean の文は正規化つき）」を添える。
7. （低）40 行目「単位元を保たず」：φ_{a,a} = id は単位元を保つ。cornerHom_one_ne_one の仮定は N < M。「N < M の段で単位元を保たず」。
8. （低、出所：入力外）44 行目「像が角全体であること（Part 260 の範囲）」：Part 260 で示したとも読めるが、CLAUDE.md によれば Part 260 でも Lean の外。「（Part 260 でも Lean の外）」。
9. （確認できない）exists_compatible_hom_iff、not_isDirected_udvd、Lim、ofL_injective、sqLim、sqLim_of_injective は入力にない。「2 と 4 にユニタリ約数の順序の共通の上界がない」は手計算で確かめた（v_2(c) = 1 と v_2(c) = 2 が両立しない）。54 行目の「同じ型の上の」は、sqLim の添字が Lvl そのものでない場合は言い換えが要る。
10. （入力 1 の不備）入力 1 の 114〜115 行目で cornerOp_one_mul・cornerOp_one_ne_one が「-- Mathlib」の見出しの下に置かれている。PAG264 の欄にあるのは cornerHom_one_ne_one だが、証明が使うのは cornerOp_one_ne_one。次回の入力の雛形で直すことを勧める。

