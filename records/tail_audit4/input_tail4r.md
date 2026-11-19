# 再照合の入力（索引の尾の統合照合の後の直し、2026-11-19 夕方）

§A は前回の統合照合の照合者の出力の全文（指摘）。§B は、その指摘を受けた直しの差分（照合の直前の状態 2dd85ec から現在まで）。照合の対象は §B で追加・変更された文です。§C〜§E は根拠です。

## §A 前回の統合照合の出力（全文）

# 統合照合の報告（索引の第 5 版の後の尾、2026-11-19 夕方）— 照合者の出力の全文

読んだのは入力ファイルだけです。CLAUDE.md はセッションの文脈として最初から読み込まれていたので、照らし合わせに使った箇所は「CLAUDE.md（文脈）」と断っています。

計算はすべて `/tmp/indep_tail4/` で行いました。§E の 4 本を写して再実行し、ログ（interaction・sign_corner・control）はすべて同じものが出ました。記録にない項目は `extra_checks.py`・`corner_driver.py`・`control_dbg.py` で足して計算しました。ウェブは arXiv:0809.1052 の著者の確認に 1 回だけ使いました。

## 1. 形式文と食い違う文、形式文より強い文

**1-1［重］6.3「T(0) の側の単位的な写像は互いに素な段だけ（5.1・5.2）」**
- 条件が落ちています。(i) 引き戻しとの両立と、(ii) 殻を混ぜない（強い読み）です。
- 5.1 の見出し（`PAG.Part262.exists_compatible_hom_iff`）は条件つきです。ただし PAG262 は §C にないので、見出しの文と照らしました。
- 引き継ぎメモの同じ観察には「引き戻しと両立し殻を混ぜない」が入っており、索引だけが強くなっています。候補 3 に関わる文です。

**1-2［重］2.9「射影の変換 J∘H（2.4）は、A_N の上で…（Ad(JH) = Ad(H) = Ad(F)）」**
- 2.4 の `PAG.Part256.JH` は、ℤ/N の関数を単数の上の関数に送る写像です。`JH_eq_rootNum_mul` の docstring にも「同じ空間の上の固有値方程式ではない」とあります。V_N の自己準同型ではないので、Ad は定義されません。
- 2.9 の J は、ℤ/N 全体の殻の反転の CRT の積です（D-2 §0 に「ℤ/N 全体の上の殻の反転は鎖にない」）。H は Hartley/√N です。つまり Lean の外の、別の作用素です。

**1-3［重］2.9「range(D_1)∩range(E_1) は…V_prim で、J∘H はこれを保ち、そこでの制限が U_N の制限」**
- この 3 つはどれも Lean の外です。
  - `PAG.Part257.Vprim` は (ZMod N)ˣ→ℂ の部分空間で、range(D_1)∩range(E_1) は ZMod N→ℂ の中にあります（0 拡張で同一視している）。
  - `JH_eq_rootNum_mul` の docstring は「U と A1 は文に出てこない」と書いています。
  - `phaseA1` の定義は §C にありません。
- それなのに 2.9 の「Lean の外」の行にこの 3 つが入っていません。一方で「Lean（既にあるもの）」に `Vprim`・`JH_eq_rootNum_mul`・`UA1` が並んでいるので、Lean に支えられているように読めます。
- 辞書 §19 は「等式は Lean の外」と書いており、索引のほうが強くなっています。

**1-4［中］2.9「P ∈ A_N も N ∣ 12 のときだけ」と、Lean の欄の `fullComm_commute_iff_dvd_twelve`**
- この Lean の文は「A′ が可換 ⇔ N ∣ 12」で、P ∈ A_N の文ではありません。
- N∣12 ⇒ P∈A_N は、この定理に二重可換子（Lean の外）を足せば出ます。逆向きは数値（N≤36）だけです。
- 盲検の照合者も「同じ型で、同じ文ではない」と書いています。

**1-5［低］5.5 の見出し「非単位的な代数準同型」（N∣M の全称）**
- Lean の型は `→ₙₐ[ℂ]`（単位元を保つとは限らない、の意）です。単位元を保たないと言えるのは N<M のときだけです（`cornerHom_one_ne_one`）。
- N=M では `cornerHom_self` により恒等写像です。

**1-6［低］辞書 §17「非単位的な *準同型」**
- `*` の保存は Lean の文にありません。引き継ぎメモも「随伴」を Lean の外に挙げています。

**1-7［低］5.5「局所的な単位元の文はどの直極限でも成り立つ一般論」**
- 実際に要るのは、各段が単位的で、移行写像が乗法を保つことです。CLAUDE.md（文脈）も同じ言い方なので、両方直す必要があります。

**形式文と合っていたもの**：差分に出る §C の 28 宣言の範囲では、次の文は形式文と合っていました。
- 生成元の像
- 引き戻しとの両立
- 一意性の条件 (a)(b)
- 合成と恒等
- (2,4) の証人
- 極限の 8 宣言

**確かめられなかったこと**：次の定義は §C にありません。
- `cornerOp`・`fsum`・`ofCorner`・`cornerSys`・`Lvl`
- `DirectedSystem` のインスタンス
- `phaseA1`
- `PAG.Part262.*`

φ(S)=(N/M)·π^*∘S∘π_* は、docstring とだけ照らしました。

## 2. 数値の記録との食い違い、範囲の拡大、スクリプトの誤り

**2-1［中］F_M ι = V F_N**
- スクリプトが比べているのは k=2,3 で M=kN≤36 の 28 組だけです。
- N=19〜36 では何も比べないまま ok=True が残り、ログの「偽となる N = []（35 個）」に数えられています。スクリプトの数え方の欠陥です。
- 引き継ぎメモの「数値（N = 2〜36）：… F_M ι = V F_N」は範囲を広げています。
- 恒等式そのものは、手計算で正確に成り立つことを確かめました。

**2-2［中］range(D_1)∩range(E_1) = V_prim**
- スクリプトが比べているのは次元だけです。
- 私の追加計算では、0 拡張した原始指標の張る空間と一致しました（N=2〜36）。ただし、記録のスクリプトはそこまでは示していません。

**2-3［中］スクリプトが計算していない主張が 2 つある**
- 対象は次の 2 つです。
  - 「J∘H を V_prim に制限すると U_N の制限に一致する」（2.9、盲検 Q5）
  - 「A_N′ = span{R_u} ⇔ N∣12」（盲検 Q1）
- したがって、D-2 §3 の「すべて構築側の数値と一致した」と、引き継ぎメモの「全項目が数値と一致」は言い過ぎです。
- 私の追加計算では、どちらも N=2〜36 で成り立ちました。A′ が可換になる N、A′=span{R_u} となる N は、どちらも {2,3,4,6,12} でした。

**2-4［中］N∣24（U_N が角に入る）、N∣12（符号、P∈A_N）**
- 数値は N=2〜36 だけで、一般の N は盲検の手計算（確信度：中〜高）です。索引 2.9 は範囲も確信度も書かずに全称で言っています。
- スクリプトの U_N は phaseA1 = （誘導する原始指標の）rootNum と置いていますが、Lean の `UA1` と同じものかは確かめられません。

**2-5［中］対照群のスクリプト（control_fqt_interaction.py）**
- 調べているのは次の項目だけです。
  - R_u・J の可換
  - F による入れ替えと正規化
  - 角の次元
  - 位相の幅
  - JF の制限が角に入るか
- P（符号）、range∩、F_M ι=V F_N、ψ は調べていません。
- 範囲は p=2 で e≤4、p=3 で e≤3、p=5 で e≤2 です。ノートの「e≤4」は上限だけを書いています。
- 引き継ぎメモの「対照群でも同じ形」は、直前の項目すべてにかかるように読め、広げすぎです。

**2-6［低］対照群の U の類比が ℚ の U_N と別物**
- U の類比は、どの指標でも λ=(JFχ)(1)/χ(1) を 1 点で読んでいます。
- 原始的でない指標では λ は 0 か −1/√p で、ユニタリではありません。ℚ 側の U_N とは別物です。
- 確認したところ、2 元以上ある原始的でない導手の類では λ がすべて 0 でした。したがって出力の True/False は変わりません。
- True になった (2,1)、(2,2)、(3,1) は、どれも導手の類が 1 元ずつの自明な場合です。

**2-7［低］139 組の中身**
- 139 組は、2≤M≤36 の約数の組すべてです（N=1 と N=M を含む）。
- φ(P_N)=P_M φ(1) なので、実質は P_N∈A_N を確かめ直しています。

**2-8［低］111 組と 81 組の中身**
- 111 組は M≤30 で、N=M の 30 組を含みます。N<M に限ると 81 組です。
- 再実行で、81 組のすべての s∣N について、φ(D_s) は D_t の span に入りませんでした。文面の「すべての s」は「s∣N」と書くべきです。

**2-9 確かめられないもの**
- crt_corner_check.py は入力にないので、1098 回の中身は確かめられません。

## 3. 地位・ラベル・確信度・決定者・出所

**3-1［重］2.9 の対照群の行「i^a を無限素点の因子と読むこと（2.8 の規約 T）に依存する」**
- 2.7・2.8 によると、規約 T のもとで無限素点の局所定数は (−i)^a（`parFac`）です。i^a を無限素点の因子と読むのは、逆の規約のほうです。
- 値 τ/(i^a√N) は、どちらの規約でも同じです。依存しているのは規約 T ではなく、Hartley 核の 1/i^a を含めることです。
- 数値の裏づけとして、素朴な核 τ/√f で同じ判定をすると、角に入るのは {2,3,4,6,12} になり、8 と 24 が外れます（N≤36）。

**3-2［中］5.5「ℤ/p^e の段に当たる場合…に限って同じ文が成り立つ」**
- 「その場合だけ試した」を「その場合にしか成り立たない」と読ませる文になっています。

**3-3［中］5.5「p によらない見込みで、A_∞ に入る算術は素点が可算個あることだけ」**
- D-1 の「そうなら」という条件が落ちています。
- また、有限段の次元は p=2 と奇素数で違います。A_{2^e} は 4, 10, 19, 31、p=3,5,7 では 5, 12, 22 です（私の計算）。

**3-4［中］5.1 の新しい行**
- 「WebFetch の要約を通して」という限定が落ちています。

**3-5［中］5.5「三重正則性からの短い帰結の見込み」**
- 辞書と CLAUDE.md（文脈）は「帰結の見込み」です。
- 引き継ぎメモの γ の項は「短い帰結（…一致）」で、「見込み」がありません。

**3-6［低］5.5 の ⊗'_p の箇条に出所がない**
- D-1 では、照合者の答えで確信度：高です。

**3-7［低］2.9 の 17:17 の決定の書き方**
- 「構築側はこの線で新しい問いを開かない」が落ちています（D-2 §4）。
- 引き継ぎメモの「見出しを…狭めた」は、著者がしたのか構築側がしたのかが読めません。

**3-8［低］Bhattacharyya–Song と Bhattacharyya–Song–Tanaka**
- 2.9 と辞書 §18 は「Bhattacharyya–Song（arXiv:0809.1052）」、辞書 §17・6.1・CLAUDE.md（文脈）は「Bhattacharyya–Song–Tanaka 2010」です。
- [arXiv:0809.1052](https://arxiv.org/abs/0809.1052) は Bhattacharyya と Song の 2 人による「…Wreath Powers…」です。JACO 31 巻 3 号の「…wreath products…」とは別の文献である可能性があります（後者の著者は確かめていません）。

## 4. ファイルどうしの食い違い

**4-1［中］5.5 と 2.9**
- 5.5 は「無限素点・スケーリング・U は A_∞ に現れない」と書いています。
- 2.9 では次のように例外や現れ方があります。
  - 符号は N∣12 の角で A_∞ に入る。
  - U_N は N∣24 で角に入る（そのとき U_N=I）。
  - スケーリングはフーリエを通して φ↔ψ として現れる。

**4-2［中］5.1 の文献照合の残り**
- 既存の行は、Bastian–Humphries の本文を未了に数えています。
- 新しい行、§6、CLAUDE.md §3（文脈）では、残りは MathSciNet・zbMATH と Hanaki–Kim–Maekawa だけです。

**4-3［中］引き継ぎメモの対照群と γ の項**
- 「関数体でも成り立つので」「（対照群でも成り立つ）」は、索引 5.5 の「ℤ/p^e の段だけ試した」より広くなっています。
- γ の項は、「像は角全体」「整除の順序全体で直極限」「BC の ρ」も、数値・見込みの区別なしに言い切っています。

**4-4［中］BC に対応するのは D 側か E 側か**
- 引き継ぎメモの γ 文献の項は「D_s を含む T(0) の側は出てこない」と書いています。
- 6.3 と辞書 §17 は「L²(Ẑ) で D 側が BC に対応、E 側は外」と書いており、逆向きに読めます。
- 6.3 の中でも、平行移動の表示で φ=ρ と書いた直後に、D 側が対応すると書いています。
- これは表示によって入れ替わる話で、2.9 のフーリエによる φ↔ψ そのものです。どちらの表示かを書く必要があります。
- 6.3 の「延びる」は当たりません。群環は T(0) に含まれないからです。

**4-5［中］記号の衝突**
- §0 は反転（0 と ∞ の入れ替え）を「ι とも書く」としていますが、2.9 の ι は正規化した引き戻しで、索引の中で定義されていません。
- V は、0 拡張の写像と、関数の空間 V_N・V_∞・V_prim の両方に使われています。
- J は、2.4 の J（単数の上の u↦u⁻¹）と、2.9 の CRT の殻の反転の両方に使われています。

**4-6［低］辞書の未記入の数え方**
- 辞書 §17 の前書きは「Part 257〜259 の名前は未記入」と書いています。それなのに「未記入の件数：0」なので、§7 で報告する指標が実態より小さく見えます。
- 抜けている名前の例は `listChar`、`shellLift`、`twLift`、`UDvd`、`sqLim`、`canon` です。

## 5. 記録の整合

**5-1［重］版・§7・§8 が更新されていない**
- 索引の冒頭は「この第 5 版」のままです。§8 には、今回の追加を記録した版も、それが照合前であることも書かれていません。
- §7 は「102 件」のままで、引き継ぎメモは「113/113」です。
- 私の数えでは、固有の宣言名は 129 件です。内訳は 102 ＋ PAG264 の 11 ＋ PAG265 の 8 ＋ 2.9 で新しく出た 8 で、`UA1` は 2.6 に既出です。
- 113 が合うのは、午後に足された `cornerHom_self` を含めた場合だけです。どの時点で数えたかは確かめられません。
- 差分の 28 宣言は、すべて §C にあります。

**5-2［重］Part と PAG の対応の誤り（引き継ぎメモ）**
- 「Part 218 の `shellAlg_comm_dil`」は誤りで、Part 214（PAG218）です。
- 「N∣12 の判定（Part 225）」は誤りで、Part 221（PAG225）です。
- スクリプトの docstring の「Part 218 の dil」も同じずれの疑いがあります。
- ほかの併記（Part 220/224、242/246、252/256、253/257、254/258、260/264、261/265）は合っています。

**5-3［低］そのほか**
- 2.9 の Lean の欄に「Part n（PAGm）」が併記されていません。
- 5.5 の「§1 の 08:41」は参照先が不明で、CLAUDE.md §1（索引 3.1）を指すはずです。
- §6 に 2.9 の Lean の外の項目が入っていません。
- 「final82」が二つの状態（行 2〜3705 と行 2〜3708）に使われています。件数の算術自体は合っています。
- 第 5 章が 5.1, 5.2, 5.5, 5.3, 5.4 の順に並んでいます。

## 6. 直すべき点（重要度順）

1. **6.3**：「引き戻しと両立し殻を混ぜない（強い読み）単位的な写像は互いに素な段だけ」と、条件を書き戻す（1-1）。
2. **2.9 の対照群の行**：「（2.8 の規約 T）」を消し、次のように書く（3-1）。
   - 「ℚ の値は Gauss の符号定理と、位相に無限素点の因子（Hartley 核の 1/i^a、2.4）を含めることに依存する（素朴な核では N=8, 24 が外れる。数値 N≤36）」
3. **2.9 の J∘H**：「2.4 の JH の反転を ℤ/N 全体の殻の反転 J（CRT の積）に延ばした J∘H（H は Hartley/√N。Lean の外）」と書く。あわせて ι と V を 2.9 で定義するか、§0 の「ι とも書く」を外す（1-2、4-5）。
4. **2.9 と §6 の「Lean の外」に次を足す**（1-3、1-4、5-3）。
   - V_prim の等式
   - J∘H がこれを保つこと
   - U_N の制限との一致
   - A_N = End(V_N)^{G_N}
   - P∈A_N⇔N∣12（Lean の定理は A′ の可換性の文で、⇒ の向きは二重可換子経由、⇐ ではなく逆向きは数値だけ）
5. **索引の冒頭・§7・§8**：版番号を上げ、宣言名を数え直し（129 件のはず）、照合前であることを記録する（5-1）。
6. **引き継ぎメモの Part 番号**：Part 218 → Part 214（PAG218）、Part 225 → Part 221（PAG225）（5-2）。
7. **数値の範囲を明記する**（2-1〜2-5）。
   - F_M ι=V F_N は 28 組（k=2,3、M≤36）。
   - V_prim はスクリプトでは次元だけ。
   - N∣24・N∣12 は N≤36 の数値と、盲検の手計算（確信度：中〜高）。
   - 対照群は p と e の範囲と、調べた項目だけ。
   - 「すべて一致」は、数値で確かめた項目に限る。今回の追加計算（2-2、2-3）を記録に加えてもよい。
   - スクリプトの Fphi_psi の数え方も直す。
8. **5.5 と引き継ぎメモの対照群の文**：「ℤ/p^e の段に当たる場合だけを試し、そこでは同じ文が成り立った」と揃える（3-2、4-3）。
9. **5.5 の極限の具体形**（3-3、3-5、3-6、4-1）。
   - 「そうなら」の条件を戻し、有限段の次元が p=2 だけ違うことを添える。
   - 2.9 の例外を参照する。
   - ⊗'_p の箇条の出所（照合者、確信度：高）を書く。
   - 「短い帰結」の「短い」を外す。
10. **5.1**：既存の行から Bastian–Humphries を外し、新しい行に「（WebFetch の要約を通して）」を足す（3-4、4-2）。
11. **6.3 の表示と「延びる」**：次のように書き換え、D 側か E 側かを表示ごとに書いて 2.9 を参照する（4-4）。
    - 「同じ式 ι S ι^† は、群環の側では ρ と一致し（数値）、T(0) の上では単位元を保つとは限らない代数準同型を与える（Lean）」
12. **小さい直し**：1-5〜1-7、2-7、2-8、3-7、3-8、4-6、5-3。

**確かめられなかったこと**
- §C にない定義（1 節の末尾に挙げたもの）
- crt_corner_check.py
- 盲検の出力の原文
- 文献の本文と定理番号
- JACO 2010 の論文の著者

所要時間は、追加計算を含めて目安の 15 分を超えました。

## §B 直しの差分
```diff
diff --git a/CLAUDE.en.md b/CLAUDE.en.md
index ebbd746..12eefeb 100644
--- a/CLAUDE.en.md
+++ b/CLAUDE.en.md
@@ -31,7 +31,7 @@ The purpose of this procedure is not to avoid mapping to existing mathematics. T
 ## 2. Structure of the project and current position
 
 - Monograph layer (1.0): an operator system on the idele class group $C_{\mathbb Q}$ ($D$, $T_p$, $W$, dihedral relations). The central problem P1 is the compatibility classification of the boundary conditions $U$ of self-adjoint extensions (Theorem 2.6). Axiom A1 is a restatement of the value at $\lambda=0$ of the gluing of Tate's $\gamma$-factors, and is **still treated as an axiom**. Do not write "derived".
-- PAG 2.0 (finite level): Lean formalization. Completed up to design Part 256 = PAG260.lean (2026-11-13. Part 255 is the dense/discrete dichotomy for the image of the subgroup generated by finitely many primes and the choice of topology; Part 256 = candidate M1 is the factorization of Gauss sums and root numbers for coprime moduli and the law of the eigenvalues of the gluing $U$. All known facts, no new candidates. The registration of the premise of direction β (the inductive system of $A_N$), pre-registered by the author side, remained open because its text had not reached the construction side, but on 2026-11-14 it was transmitted by transcribing it in full in Supplement 4). Parts 252, 253 and 254 were carried out not as new Parts but as small notes of the short-term layer (Part 252: Lean formalization of the claim $U = JH_N$. Part 253 = candidate K1: linearization of the operator $T$ and unitarity on $V_{\mathrm{prim}}$. Part 254: the two remaining questions of Part 252 — the orthogonal direct sum decomposition by conductor, and the uniqueness of the family $U_N$ by pullback compatibility and its assembly into the inductive limit $U_\infty$. All labeled [re-derived], no new candidates. $U_N$ is an operator into which the phase of A1 is put as a definition; A1 is not derived and remains a postulate). At the end of Part 256, the xlsx has 3,552 items. The three start conditions of Part 257 were all resolved on 2026-11-14 (handoff Supplement 4): the re-check of Parts 252–256 was completed, and there were no false, vacuous or different statements and no new candidates in the formal statements (all discrepancies were on the wording side, due to the post-check corrections not having been put into the Lean docstrings and opening explanations. As remaining items, the fact that reverse translation A of the 33 statements S18–S50 of Part 254 had not been carried out in any round, and the collation of the record-only corrections after B4 (record §9), are attached as closing conditions of Part 257). Since the text of the direction β registration had not reached the construction side, it was transmitted by full transcription in Supplement 4 (collating it with the result of Part 255 and stating its fate is the job of the construction side's next report). The "08:41 definition" had been sent on the construction side but its original text did not remain on the author side, so it was closed as a start condition (collation with the wording of §1 is remaining work on the author side). For Part 257, it had been decided under the delegation that, if the collation of the registration confirmed that the premise question was unanswered, the premise of β would be asked in the three stages of registration §6 (blind question test + literature check → numerics → Lean); in fact, however, on 2026-11-14 it was closed as candidate P1 (factorization of Gauss sums and root numbers for sequences of coprime moduli, PAG261, 25 theorems), and the collation with the β registration remained undone. Parts 255, 256 and 257 were three Parts in a row in which a question different from the one decided and registered was closed, and the remaining items made closing conditions of Part 257 in Supplement 4 §1 (reverse translation A of S18–S50, collation of record §9, the duplicate-annotation round) also did not appear in the report. The corrections for checker B's 14 wording findings were closed without being checked (disclosed by the construction side). On the other hand, the mechanical duplicate check before closing (new rule) worked as designed for the first time, removing before closing two declarations with identical statements and one lemma with the same statement as Mathlib. Signal 4 reached nine Parts in a row, and under the author's policy (departure from convergence) it was decided not to start Part 258 and to make a direction audit the next task (Supplement 6: β collation, full inventory of unchecked remaining items, audit of the replacement of questions, residue assessment of the next direction). The three files of Part 257 said to have been sent did not reach the author side. Later, at 21:45 the same day, the construction side received the full text of the registration and completed the collation, and start condition 2 was closed (record `pag2_beta_registration_check.md`; the full text also reached the author side): Part 255 was not a β Part (the author chose L1 at 08:38 in a construction-side session), and none of stages 1–3 of the β question had been tried. The start of Part 257 was also due to the author's own judgment at 20:59 on 2026-11-14 (start while keeping condition 2 on hold; this replaced the earlier judgment the same day, "proceed with the audit, wait on Part 257"), and candidate P1 was also chosen by the author. That is, the choice of questions for Parts 255–257 was the author's choice in construction-side sessions, and the double route with the author side's handoffs and registrations was the cause of the discrepancy (the wording of Supplement 6 §2 (a) was corrected in Supplement 7). The handoff memo `PAG2_handoff_part257.md` has been saved on the author side, and the original text of the 08:41 definition was in it (transcribed into §1). β remains open with a split: for coprime steps ($N$ and $M/N$ coprime), the answer is expected to be nearly available through Part 228 (PAG232) `shellAlgTensorEquiv` and `leftHom` (condition 1 is satisfied; conditions 2 and 3 are expected by hand calculation but unconfirmed; confidence: medium), and the statement in registration §2 that "the direct product theorem does not answer this question" is corrected as an overstatement for the coprime case. The residue is the prime-power steps $p^e \to p^{e+1}$ (e.g. $(2,4), (2,8), (3,9)$), for which no corresponding declaration has been found in the chain. The duplicate audit was completed up to F2 (second round of corrections: 22 fixed, 2 partially, 16 new findings, no change to formal statements. The corrections after F2 are record-only and unchecked — added to the remaining items). Part 258 (PAG262, closed 2026-11-15) decided the premise of direction β in the registration's reading (unital algebra homomorphism, compatibility with pullback, the strong reading of not mixing shells): when $N \mid M$, such a map exists if and only if $\gcd(N, M/N) = 1$ (`exists_compatible_hom_iff`, 23 theorems, sorry 0). The existence side is the tensor product (known), and the non-existence side is candidate 3 of §3. As a reading, the path of setting up β as the inductive limit of these maps is closed, because a cofinal system in the divisibility order always contains steps that raise an exponent (weak readings, non-unital maps and other compatibility conditions are outside the answer. A system of coprime steps only is a separate matter). The four closing conditions of Supplement 7 (reverse translation A of S18–S50, record §9, the corrections after F2, the corrections to Part 257) were all closed after being checked (F3). The remaining unchecked tail consists of two items, the record-only corrections after F3 and the wording corrections after checker B of Part 258 (including rephrasings concerning the scope of claims), and together with the stop convention of Supplement 8 (after an integrated check, only corrections that do not change claims are allowed; corrections that change claims are conditional on one more integrated check) they were made the object of the next integrated check. Signal 4 was ten Parts in a row for Parts 249–258. However, Part 258 is a complete answer in both directions to a pre-registered question with residue, and "judging the premise" actually changed the direction (paths (1)–(3) of β were closed, and the remaining question moved to the side of reformulation). The total number of theorems and lemmas in the chain is 3,573. Part 259 had not been started, and next the direction round within the scope of Supplement 8 (integrated check of the tail, residue assessment of the reformulations R1–R3 of β, handling of the literature check for γ) was to be carried out and one recommendation for Part 259 given. After that, on 2026-11-15 the author settled the purpose as "making a new geometry", and the main line moved to the foundational document (writing up the definitional layer as one document) (Supplement 9; the outline is `founding-document-outline-20261115.md`). Following the assessment of R1 (maps of coprime steps are not unique under (i)(ii), and for even moduli there is a twist by conjugation with $\chi(x) = (-1)^x$; adding (iii) Fourier compatibility makes it unique as `shellLift`, and the inductive system has the restricted tensor product as its limit over directed subsystems), Part 259 (PAG263, closed 2026-11-15, 67 theorems) was carried out as a Part filling a gap in Chapter 5: a map satisfying (i)(ii)(iii) exists exactly once if and only if $\gcd(N, M/N) = 1$ (`existsUnique_compatF_iff`). Without (iii), for $a = 2$ there is a twisted map `twLift` and the map is not unique (uniqueness in the odd case is numerical only). The order of the index (= the classical unitary divisors, E. Cohen 1960; in the chain it was the same concept as `InLayer` of Part 216) is not directed; on the square-free subsystem it forms an inductive system and embeds injectively into the $\mathbb{C}$-module limit `sqLim` (the algebra structure and the isomorphism with the restricted tensor product are outside Lean). The labels were fixed as: the properties of the order [known]; the uniqueness, non-uniqueness and inductive system [re-derived (small)] (Supplement 11). The whole chain has 3,640 items, and the xlsx is final80 (3,668 items). The integrated check of the tail, made a closing condition in Supplement 10, was not included in the report of Part 259, and in Supplement 11 it was decided to carry it out once as an independent deliverable and empty the tail ledger. The literature check for γ was split off as work on the author side. Signal 4 is eleven Parts in a row, but Part 259 has changed position as a Part serving a chapter of the foundational document. The remaining pre-registered candidates K2–K4 have residue that is only computation or empty, and are kept as stock in the short-term layer. On 2026-11-19, after the builder-accessible part of the γ literature check (5 searches; no description linking finite-level Bost–Connes with T(0) was found; confidence: low–medium), the author adopted at 09:37 the recommendation for the restated question (`notes/pag2_gamma_corner_preregistration.md`), carried out as Part 260 (PAG264, a small note in the short-term layer, 40 theorems): for N ∣ M, φ(S) = (N/M)·π^* ∘ S ∘ π_* (read as ι S ι^†) is a non-unital algebra homomorphism sending A_N into A_M (regardless of gcd(N, M/N); φ(1) ≠ 1 when N < M), with φ(E_s) = E_{(M/N)s}, φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s, compatibility with pullback, uniqueness under (a) compatibility with pullback and (b) the value of φ(1), and the composition and identity laws (the two laws of an inductive system over the divisibility order on positive integers). The D side does not land in the span of the shells (outside the strong reading of Part 258; witness (2,4), in general numerically). Outside Lean: packaging as a `DirectedSystem` and the limit, the image being the whole corner (expected to follow from triple regularity), agreement with the Bost–Connes ρ on the group-ring side (numerical). Labels: the E side is [known] (operator form of the corner by the idempotent of a quotient scheme), the rest [re-derivation (small)]; no new candidate (the control group was tried only for the case corresponding to steps of ℤ/p^e). The reservation in chapter 5 "it does not become the algebra version" is reread as a statement about unital maps (index 5.5). The checks were an independent check, a recheck and an integrated check; the tail ledger is empty. The whole chain has 3,680 theorems/lemmas; the xlsx is final82 (rows 2–3708). In the afternoon of the same day, the remainder of R-d of the recommendation was carried out as Part 261 (PAG265, short-term layer, 10 theorems): over the divisibility order on positive integers (`Lvl` of Part 254) the corner maps form a `DirectedSystem`, and the limit `CornerLim` via Mathlib's general `DirectLimit` carries a non-unital ring structure and ℂ-scalar multiplication. Each stage injects, and the limit has local units (a common idempotent for every finite set) but no left identity. The local-unit statements are general facts true for any such direct limit; only the absence of a left identity carries the non-unital content (its proof is expected not to need prime-power steps, by hand). Label [re-derivation (small)], no new candidate, the tail ledger is empty. The whole chain has 3,690 theorems/lemmas; the xlsx is final83 (rows 2–3718). With Part 248 the classification of generators was completed, and from Part 249 the work moved to the original path (B-3: the finite-level idele class group $C_{\mathbb Q}/U_N$). Part 250 is the formulation of resolution and emergence (proposals 1 + 2 adopted by the author on 2026-11-11: put the foundation on the group of positive rationals and look at it through the connectivity of ε-chains, chainIn). Honest summary of the result: what could be shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but connected by chains at every scale" (the logarithmic-coordinate version of a textbook example; no new candidate). "When the resolution is lowered, the line emerges" has not been shown — taking a quotient collapses it to one point, ℝ appears from the completion (the ε → 0 side), and ℝ is used in the definition from the start. Concerning the operation of "lowering the resolution / emergence", on 2026-11-12 the author chose candidate 3 (looking at all places coarsely at once), but blind identification showed that for finite S it stays a "shadow of the finite places" in which the omitted primes are invisible, and the author decided to proceed from the projective-limit side of Part 249. Part 251 is its implementation: in the group of compatible systems unitSys (a concrete model of $\varprojlim (\mathbb{Z}/N)^\times$) × ℝ, it showed the density of the subgroup generated by the prime classes $\kappa_p$ (the level-N component is the inverse of $w_p(N) = 1 + p^{N!}(p-1)$; for $p \nmid N$ it is $p^{-1}$, and at levels that are powers of $p$ it is 1) (+ uniqueness primeSys_unique). Re-derivation of the known, no new candidate. Not put into Lean: unitSys ≅ Ẑ^×, the universality, compactness and topological-group property of the limit, and the structure theorem $C_{\mathbb Q} \cong \widehat{\mathbb Z}^\times \times \mathbb{R}_{>0}$ ("dense in the idele class group" is a reading under this identification). Signal 4 (only combinations of elementary components) reached nine Parts in a row for Parts 249–257 (Parts 252, 253 and 254 were chosen knowing they were small notes). The inventory audit of remaining questions was completed by the construction side on 2026-11-12 (`pag2_audit_after_part251.md`; the author side's draft is `remaining-questions-inventory.md`): the restatement test over the whole period (Parts 155–251) succeeded in every period, and the breakdown of the 14 remaining questions is: known theorems or their consequences 10 (of which 4 are expectations from knowledge, not searched), the author's judgment comes first 2 (the operation of "lowering the resolution", the reading of the "overlap" at the infinite place), still a new candidate 1 (classification of generators; not checked against MathSciNet or zbMATH), still an axiom 1 (A1). The conclusion was that no question that is not a re-derivation of the known remains on the formalization side. Correspondences found in this search: on the limit side of Theorem 2.6, Burnol (an operator commuting with translations is a multiplication operator even if it is a closed operator); for unitSys, the ZHat of the FLT project (an explicit definition of Ẑ; precedent for the unit-group version unconfirmed); for the finite-level Bost–Connes, the original BC system. After that, the construction side carried out a re-audit with two agents not given the context (a blind one not shown the judgments = web search only, and a critique of the judgments = no tools), and weakened all three conclusions (audit record §8): being restatable shows only that "no new concepts were needed" (it does not show that there is no new content); only 4 of the 14 items were checked in the literature; "no questions remain" becomes "none has been found within the range checked" (confidence: medium or lower). The classification of generators does not contradict candidate 1 of §3, but its scope narrowed (what remains are items 66 and 67–69; a computation "at the level of a small note" that nobody has written). Rewriting §3 will be done after the author's approval. The construction side has proposed introducing pre-registration (writing, before the next Part, the known correspondences and the conditions for statements that are not re-derivations). The author side's answers to the matters for judgment have been compiled in the handoff to the construction side: A1 = a postulate of the interpretive layer (its content is Tate's theorem); the space of U in Theorem 2.6 = functions on $C_{\mathbb Q}$ (the side of the regular representation, with the reservation of the Λ-cutoff); the control-group test is adopted (codified in §7). The strategy (`strategy-nonconvergence.md`) was adopted by the author on 2026-11-12, including the rule changes; pre-registration was codified in §4 as "selection of questions by residue", and the blind question test in §7. On 2026-11-12 the author indicated the policy "proceed toward emergence", decided to review direction α (a ladder of quotients over the limit) without making it the main line in either form (a) or (b), and decided the reading of the "overlap" at the infinite place as "a twisted gluing (boundary unitary $U$)" (§1). Material for judging directions and the progress of the study are in `emergence-next-directions.md`, and the draft pre-registration of the first consequence of δ is in `preregistration-delta-first-consequence.md`.
+- PAG 2.0 (finite level): Lean formalization. Completed up to design Part 256 = PAG260.lean (2026-11-13. Part 255 is the dense/discrete dichotomy for the image of the subgroup generated by finitely many primes and the choice of topology; Part 256 = candidate M1 is the factorization of Gauss sums and root numbers for coprime moduli and the law of the eigenvalues of the gluing $U$. All known facts, no new candidates. The registration of the premise of direction β (the inductive system of $A_N$), pre-registered by the author side, remained open because its text had not reached the construction side, but on 2026-11-14 it was transmitted by transcribing it in full in Supplement 4). Parts 252, 253 and 254 were carried out not as new Parts but as small notes of the short-term layer (Part 252: Lean formalization of the claim $U = JH_N$. Part 253 = candidate K1: linearization of the operator $T$ and unitarity on $V_{\mathrm{prim}}$. Part 254: the two remaining questions of Part 252 — the orthogonal direct sum decomposition by conductor, and the uniqueness of the family $U_N$ by pullback compatibility and its assembly into the inductive limit $U_\infty$. All labeled [re-derived], no new candidates. $U_N$ is an operator into which the phase of A1 is put as a definition; A1 is not derived and remains a postulate). At the end of Part 256, the xlsx has 3,552 items. The three start conditions of Part 257 were all resolved on 2026-11-14 (handoff Supplement 4): the re-check of Parts 252–256 was completed, and there were no false, vacuous or different statements and no new candidates in the formal statements (all discrepancies were on the wording side, due to the post-check corrections not having been put into the Lean docstrings and opening explanations. As remaining items, the fact that reverse translation A of the 33 statements S18–S50 of Part 254 had not been carried out in any round, and the collation of the record-only corrections after B4 (record §9), are attached as closing conditions of Part 257). Since the text of the direction β registration had not reached the construction side, it was transmitted by full transcription in Supplement 4 (collating it with the result of Part 255 and stating its fate is the job of the construction side's next report). The "08:41 definition" had been sent on the construction side but its original text did not remain on the author side, so it was closed as a start condition (collation with the wording of §1 is remaining work on the author side). For Part 257, it had been decided under the delegation that, if the collation of the registration confirmed that the premise question was unanswered, the premise of β would be asked in the three stages of registration §6 (blind question test + literature check → numerics → Lean); in fact, however, on 2026-11-14 it was closed as candidate P1 (factorization of Gauss sums and root numbers for sequences of coprime moduli, PAG261, 25 theorems), and the collation with the β registration remained undone. Parts 255, 256 and 257 were three Parts in a row in which a question different from the one decided and registered was closed, and the remaining items made closing conditions of Part 257 in Supplement 4 §1 (reverse translation A of S18–S50, collation of record §9, the duplicate-annotation round) also did not appear in the report. The corrections for checker B's 14 wording findings were closed without being checked (disclosed by the construction side). On the other hand, the mechanical duplicate check before closing (new rule) worked as designed for the first time, removing before closing two declarations with identical statements and one lemma with the same statement as Mathlib. Signal 4 reached nine Parts in a row, and under the author's policy (departure from convergence) it was decided not to start Part 258 and to make a direction audit the next task (Supplement 6: β collation, full inventory of unchecked remaining items, audit of the replacement of questions, residue assessment of the next direction). The three files of Part 257 said to have been sent did not reach the author side. Later, at 21:45 the same day, the construction side received the full text of the registration and completed the collation, and start condition 2 was closed (record `pag2_beta_registration_check.md`; the full text also reached the author side): Part 255 was not a β Part (the author chose L1 at 08:38 in a construction-side session), and none of stages 1–3 of the β question had been tried. The start of Part 257 was also due to the author's own judgment at 20:59 on 2026-11-14 (start while keeping condition 2 on hold; this replaced the earlier judgment the same day, "proceed with the audit, wait on Part 257"), and candidate P1 was also chosen by the author. That is, the choice of questions for Parts 255–257 was the author's choice in construction-side sessions, and the double route with the author side's handoffs and registrations was the cause of the discrepancy (the wording of Supplement 6 §2 (a) was corrected in Supplement 7). The handoff memo `PAG2_handoff_part257.md` has been saved on the author side, and the original text of the 08:41 definition was in it (transcribed into §1). β remains open with a split: for coprime steps ($N$ and $M/N$ coprime), the answer is expected to be nearly available through Part 228 (PAG232) `shellAlgTensorEquiv` and `leftHom` (condition 1 is satisfied; conditions 2 and 3 are expected by hand calculation but unconfirmed; confidence: medium), and the statement in registration §2 that "the direct product theorem does not answer this question" is corrected as an overstatement for the coprime case. The residue is the prime-power steps $p^e \to p^{e+1}$ (e.g. $(2,4), (2,8), (3,9)$), for which no corresponding declaration has been found in the chain. The duplicate audit was completed up to F2 (second round of corrections: 22 fixed, 2 partially, 16 new findings, no change to formal statements. The corrections after F2 are record-only and unchecked — added to the remaining items). Part 258 (PAG262, closed 2026-11-15) decided the premise of direction β in the registration's reading (unital algebra homomorphism, compatibility with pullback, the strong reading of not mixing shells): when $N \mid M$, such a map exists if and only if $\gcd(N, M/N) = 1$ (`exists_compatible_hom_iff`, 23 theorems, sorry 0). The existence side is the tensor product (known), and the non-existence side is candidate 3 of §3. As a reading, the path of setting up β as the inductive limit of these maps is closed, because a cofinal system in the divisibility order always contains steps that raise an exponent (weak readings, non-unital maps and other compatibility conditions are outside the answer. A system of coprime steps only is a separate matter). The four closing conditions of Supplement 7 (reverse translation A of S18–S50, record §9, the corrections after F2, the corrections to Part 257) were all closed after being checked (F3). The remaining unchecked tail consists of two items, the record-only corrections after F3 and the wording corrections after checker B of Part 258 (including rephrasings concerning the scope of claims), and together with the stop convention of Supplement 8 (after an integrated check, only corrections that do not change claims are allowed; corrections that change claims are conditional on one more integrated check) they were made the object of the next integrated check. Signal 4 was ten Parts in a row for Parts 249–258. However, Part 258 is a complete answer in both directions to a pre-registered question with residue, and "judging the premise" actually changed the direction (paths (1)–(3) of β were closed, and the remaining question moved to the side of reformulation). The total number of theorems and lemmas in the chain is 3,573. Part 259 had not been started, and next the direction round within the scope of Supplement 8 (integrated check of the tail, residue assessment of the reformulations R1–R3 of β, handling of the literature check for γ) was to be carried out and one recommendation for Part 259 given. After that, on 2026-11-15 the author settled the purpose as "making a new geometry", and the main line moved to the foundational document (writing up the definitional layer as one document) (Supplement 9; the outline is `founding-document-outline-20261115.md`). Following the assessment of R1 (maps of coprime steps are not unique under (i)(ii), and for even moduli there is a twist by conjugation with $\chi(x) = (-1)^x$; adding (iii) Fourier compatibility makes it unique as `shellLift`, and the inductive system has the restricted tensor product as its limit over directed subsystems), Part 259 (PAG263, closed 2026-11-15, 67 theorems) was carried out as a Part filling a gap in Chapter 5: a map satisfying (i)(ii)(iii) exists exactly once if and only if $\gcd(N, M/N) = 1$ (`existsUnique_compatF_iff`). Without (iii), for $a = 2$ there is a twisted map `twLift` and the map is not unique (uniqueness in the odd case is numerical only). The order of the index (= the classical unitary divisors, E. Cohen 1960; in the chain it was the same concept as `InLayer` of Part 216) is not directed; on the square-free subsystem it forms an inductive system and embeds injectively into the $\mathbb{C}$-module limit `sqLim` (the algebra structure and the isomorphism with the restricted tensor product are outside Lean). The labels were fixed as: the properties of the order [known]; the uniqueness, non-uniqueness and inductive system [re-derived (small)] (Supplement 11). The whole chain has 3,640 items, and the xlsx is final80 (3,668 items). The integrated check of the tail, made a closing condition in Supplement 10, was not included in the report of Part 259, and in Supplement 11 it was decided to carry it out once as an independent deliverable and empty the tail ledger. The literature check for γ was split off as work on the author side. Signal 4 is eleven Parts in a row, but Part 259 has changed position as a Part serving a chapter of the foundational document. The remaining pre-registered candidates K2–K4 have residue that is only computation or empty, and are kept as stock in the short-term layer. On 2026-11-19, after the builder-accessible part of the γ literature check (5 searches; no description linking finite-level Bost–Connes with T(0) was found; confidence: low–medium), the author adopted at 09:37 the recommendation for the restated question (`notes/pag2_gamma_corner_preregistration.md`), carried out as Part 260 (PAG264, a small note in the short-term layer, 40 theorems): for N ∣ M, φ(S) = (N/M)·π^* ∘ S ∘ π_* (read as ι S ι^†) is a non-unital algebra homomorphism sending A_N into A_M (regardless of gcd(N, M/N); φ(1) ≠ 1 when N < M), with φ(E_s) = E_{(M/N)s}, φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s, compatibility with pullback, uniqueness under (a) compatibility with pullback and (b) the value of φ(1), and the composition and identity laws (the two laws of an inductive system over the divisibility order on positive integers). The D side does not land in the span of the shells (outside the strong reading of Part 258; witness (2,4), in general numerically). Outside Lean: packaging as a `DirectedSystem` and the limit, the image being the whole corner (expected to follow from triple regularity), agreement with the Bost–Connes ρ on the group-ring side (numerical). Labels: the E side is [known] (operator form of the corner by the idempotent of a quotient scheme), the rest [re-derivation (small)]; no new candidate (the control group was tried only for the case corresponding to steps of ℤ/p^e). The reservation in chapter 5 "it does not become the algebra version" is reread as a statement about unital maps (index 5.5). The checks were an independent check, a recheck and an integrated check; the tail ledger is empty. The whole chain has 3,680 theorems/lemmas; the xlsx is final82 (rows 2–3708). In the afternoon of the same day, the remainder of R-d of the recommendation was carried out as Part 261 (PAG265, short-term layer, 10 theorems): over the divisibility order on positive integers (`Lvl` of Part 254) the corner maps form a `DirectedSystem`, and the limit `CornerLim` via Mathlib's general `DirectLimit` carries a non-unital ring structure and ℂ-scalar multiplication. Each stage injects, and the limit has local units (a common idempotent for every finite set) but no left identity. The local-unit statements are general facts true for any direct limit whose stages are unital and whose transition maps preserve multiplication; only the absence of a left identity carries the non-unital content (its proof is expected not to need prime-power steps, by hand). Label [re-derivation (small)], no new candidate, the tail ledger is empty. The whole chain has 3,690 theorems/lemmas; the xlsx is final83 (rows 2–3718). With Part 248 the classification of generators was completed, and from Part 249 the work moved to the original path (B-3: the finite-level idele class group $C_{\mathbb Q}/U_N$). Part 250 is the formulation of resolution and emergence (proposals 1 + 2 adopted by the author on 2026-11-11: put the foundation on the group of positive rationals and look at it through the connectivity of ε-chains, chainIn). Honest summary of the result: what could be shown is that "the foundation sits inside ℝ as a dense subset that is totally disconnected but connected by chains at every scale" (the logarithmic-coordinate version of a textbook example; no new candidate). "When the resolution is lowered, the line emerges" has not been shown — taking a quotient collapses it to one point, ℝ appears from the completion (the ε → 0 side), and ℝ is used in the definition from the start. Concerning the operation of "lowering the resolution / emergence", on 2026-11-12 the author chose candidate 3 (looking at all places coarsely at once), but blind identification showed that for finite S it stays a "shadow of the finite places" in which the omitted primes are invisible, and the author decided to proceed from the projective-limit side of Part 249. Part 251 is its implementation: in the group of compatible systems unitSys (a concrete model of $\varprojlim (\mathbb{Z}/N)^\times$) × ℝ, it showed the density of the subgroup generated by the prime classes $\kappa_p$ (the level-N component is the inverse of $w_p(N) = 1 + p^{N!}(p-1)$; for $p \nmid N$ it is $p^{-1}$, and at levels that are powers of $p$ it is 1) (+ uniqueness primeSys_unique). Re-derivation of the known, no new candidate. Not put into Lean: unitSys ≅ Ẑ^×, the universality, compactness and topological-group property of the limit, and the structure theorem $C_{\mathbb Q} \cong \widehat{\mathbb Z}^\times \times \mathbb{R}_{>0}$ ("dense in the idele class group" is a reading under this identification). Signal 4 (only combinations of elementary components) reached nine Parts in a row for Parts 249–257 (Parts 252, 253 and 254 were chosen knowing they were small notes). The inventory audit of remaining questions was completed by the construction side on 2026-11-12 (`pag2_audit_after_part251.md`; the author side's draft is `remaining-questions-inventory.md`): the restatement test over the whole period (Parts 155–251) succeeded in every period, and the breakdown of the 14 remaining questions is: known theorems or their consequences 10 (of which 4 are expectations from knowledge, not searched), the author's judgment comes first 2 (the operation of "lowering the resolution", the reading of the "overlap" at the infinite place), still a new candidate 1 (classification of generators; not checked against MathSciNet or zbMATH), still an axiom 1 (A1). The conclusion was that no question that is not a re-derivation of the known remains on the formalization side. Correspondences found in this search: on the limit side of Theorem 2.6, Burnol (an operator commuting with translations is a multiplication operator even if it is a closed operator); for unitSys, the ZHat of the FLT project (an explicit definition of Ẑ; precedent for the unit-group version unconfirmed); for the finite-level Bost–Connes, the original BC system. After that, the construction side carried out a re-audit with two agents not given the context (a blind one not shown the judgments = web search only, and a critique of the judgments = no tools), and weakened all three conclusions (audit record §8): being restatable shows only that "no new concepts were needed" (it does not show that there is no new content); only 4 of the 14 items were checked in the literature; "no questions remain" becomes "none has been found within the range checked" (confidence: medium or lower). The classification of generators does not contradict candidate 1 of §3, but its scope narrowed (what remains are items 66 and 67–69; a computation "at the level of a small note" that nobody has written). Rewriting §3 will be done after the author's approval. The construction side has proposed introducing pre-registration (writing, before the next Part, the known correspondences and the conditions for statements that are not re-derivations). The author side's answers to the matters for judgment have been compiled in the handoff to the construction side: A1 = a postulate of the interpretive layer (its content is Tate's theorem); the space of U in Theorem 2.6 = functions on $C_{\mathbb Q}$ (the side of the regular representation, with the reservation of the Λ-cutoff); the control-group test is adopted (codified in §7). The strategy (`strategy-nonconvergence.md`) was adopted by the author on 2026-11-12, including the rule changes; pre-registration was codified in §4 as "selection of questions by residue", and the blind question test in §7. On 2026-11-12 the author indicated the policy "proceed toward emergence", decided to review direction α (a ladder of quotients over the limit) without making it the main line in either form (a) or (b), and decided the reading of the "overlap" at the infinite place as "a twisted gluing (boundary unitary $U$)" (§1). Material for judging directions and the progress of the study are in `emergence-next-directions.md`, and the draft pre-registration of the first consequence of δ is in `preregistration-delta-first-consequence.md`.
 - Note on numbering: in the third period, the Part numbers of the design memos are 4 smaller than the Lean file numbers. For the correspondence table see `archive-catalog.md`.
 - Counts: 3,344 theorems/lemmas and 3,371 xlsx items (at the end of Part 251, by the author's audit). Do not confuse these with other ways of counting, such as the total number of declarations.
 
diff --git a/CLAUDE.md b/CLAUDE.md
index c3272ff..65dc916 100644
--- a/CLAUDE.md
+++ b/CLAUDE.md
@@ -28,7 +28,7 @@
 ## 2. プロジェクトの構成と現在地
 
 - モノグラフ層（1.0）：イデール類群 $C_{\mathbb Q}$ 上の作用素系（$D$、$T_p$、$W$、二面体関係）。中心問題 P1 は自己共役拡張の境界条件 $U$ の両立分類（定理2.6）。公理 A1 は Tate の $\gamma$ 因子の貼り合わせの $\lambda=0$ での値への言い換えであり、**依然として公理**として扱う。「導出済み」と書かない。
-- PAG 2.0（有限レベル）：Lean 形式化。設計 Part 256 ＝ PAG260.lean まで完了（2026-11-13。Part 255 は有限個の素数が生成する部分群の像の稠密／離散の二分法と位相の選び方、Part 256＝候補 M1 は互いに素な法でのガウス和・ルート数の因数分解と貼り合わせ $U$ の固有値の法則。すべて既知の事実、新規候補なし。著者側が事前登録した方向βの前提（$A_N$ の帰納系）の登録は、構築側に本文が届いておらず開いたままだったが、2026-11-14 の補足4で全文転記して伝達した）。Part 252・253・254 は新規パートではなく短期層の小さいノートとして実施された（Part 252：主張 $U = JH_N$ の Lean 化。Part 253＝候補 K1：作用素 $T$ の線形化と $V_{\mathrm{prim}}$ 上でのユニタリ性。Part 254：Part 252 の残る問い2つ — 導手ごとの直交直和分解と、引き戻し両立性による族の一意性 $U_N$・帰納極限への組み立て $U_\infty$。いずれもラベルは［再導出］、新規候補なし。$U_N$ は A1 の位相を定義として入れた作用素であり、A1 は導かれておらず公準のまま）。Part 256 終了時点で xlsx 3,552 項目。Part 257 の開始条件3件は 2026-11-14 にすべて解消した（申し送り補足4）：Part 252〜256 の再照合は完了し、形式文に偽・空虚・別物はなく新規候補もなかった（ずれはすべて文面側で、照合後の直しが Lean の docstring と冒頭説明に入っていなかったことに寄っていた。残件として、Part 254 の33文 S18〜S50 の逆翻訳 A がどの回でも未実施であることと、B4 後の記録のみの直し（記録 §9）の突き合わせを、Part 257 の閉鎖条件として付随させる）。方向β登録は本文が構築側に届いていなかったため補足4に全文転記して伝達した（Part 255 の結果との突き合わせと運命の明示は構築側の次回報告の仕事）。「08:41 の定義」は構築側では送付済みだが著者側に原文が残っておらず、開始条件としては閉じた（§1 の文面との照合は著者側の残作業）。Part 257 は、登録の突き合わせで前提の問いが未回答と確認されれば、登録 §6 の3段階（盲検の問いテスト＋文献照合→数値→Lean）で β の前提を問うことが委任のもとで決定済みだったが、実際には 2026-11-14 に候補 P1（互いに素な法の列に対するガウス和・ルート数の因数分解、PAG261、25 定理）として閉じられ、β 登録の突き合わせは未了のままである。決定・登録した問いと違う問いが閉じられるのは Part 255・256・257 と3パート連続であり、補足4 §1 で Part 257 の閉鎖条件とした残件（S18〜S50 の逆翻訳 A、記録 §9 の突き合わせ、重複注記ラウンド）も報告に現れていない。照合者 B の文面指摘14件の直しは未照合のまま閉じられた（構築側が開示）。一方、閉じる前の機械的な重複照合（新規則）は初めて設計どおりに働き、同一文の宣言2つと Mathlib と同じ文の補題1つを閉鎖前に除去した。兆候4は9パート連続となり、著者の方針（収束からの離脱）のもと、Part 258 は始めず方向の監査を次の作業と決定した（補足6：β 突き合わせ、未照合残件の全棚卸し、問いの置き換わりの監査、次方向の残余査定）。送付されたとされる Part 257 の3ファイルは著者側に未達。その後、同日 21:45 に構築側が登録全文を受け取って突き合わせを完了し、開始条件2は閉じた（記録 `pag2_beta_registration_check.md`、著者側にも全文が届いた）：Part 255 は β のパートではなく（著者が構築側のセッションで 08:38 に L1 を選択）、β の問いは段階 1〜3 のどれも試していない。Part 257 の開始も、2026-11-14 20:59 の著者自身の判断（条件2を保留のまま始める。それ以前の同日の判断「監査は進め、Part 257 は待つ」を置き換えた）によるもので、候補 P1 も著者が選んだ。すなわち Part 255〜257 の問いの選択は構築側のセッションでの著者の選択であり、著者側の申し送り・登録との二重の経路がずれの原因だった（補足6 §2 (a) の書き方は補足7で訂正）。引き継ぎメモ `PAG2_handoff_part257.md` は著者側に保存済みで、08:41 の定義の原文もその中にあった（§1 に転記）。β は切り分けをもって開いたままである：互いに素な段（$N$ と $M/N$ が互いに素）は Part 228（PAG232）の `shellAlgTensorEquiv`・`leftHom` でほぼ答えがある見込み（条件 1 は満たす。条件 2・3 は手計算の見込みで未確認。確信度：中）で、登録 §2 の「直積の定理はこの問いを答えない」は互いに素な場合については言い過ぎだったと訂正する。残余は素数冪の段 $p^e \to p^{e+1}$（例：$(2,4), (2,8), (3,9)$）で、鎖に該当する宣言は見つかっていない。重複監査は F2 まで完了した（2 回目の直し：22 件が直り、2 件が一部、新しい指摘 16 件、形式文の変更なし。F2 の後の直しは記録のみで未照合 — 残件に加わる）。Part 258（PAG262、2026-11-15 閉鎖）は方向βの前提を登録の読み（単位元を保つ代数準同型、引き戻しとの両立、殻を混ぜない強い読み）で判定した：$N \mid M$ のとき、そのような写像があるのは $\gcd(N, M/N) = 1$ のとき、そのときに限る（`exists_compatible_hom_iff`、23 定理、sorry 0）。存在の側はテンソル積（既知）で、不在の側は §3 の候補3。読みとして、β をこの写像たちの帰納極限として立てる道は、整除順序の共終な系が指数を上げる段を必ず含むため閉じる（弱い読み・非単位的な写像・別の両立条件は答えの外。互いに素な段だけの系は別）。補足7の閉鎖条件4件（S18〜S50 の逆翻訳 A、記録 §9、F2 後の直し、Part 257 の直し）は照合（F3）を受けてすべて閉じた。残る未照合の尾は、F3 の後の記録のみの直しと、Part 258 の照合者 B の後の文面の直し（主張の範囲に関わる言い換えを含む）の2件で、補足8で停止の規約（統合照合の後は主張を変えない直しだけを許し、変える直しはもう1回の統合照合を条件とする）と合わせて次回の統合照合の対象とした。兆候4は Part 249〜258 で10パート連続。ただし Part 258 は、事前登録された残余のある問いへの両方向の完全な答えであり、「前提の判定」が方向を実際に変えた（β の (1)〜(3) の道は閉じ、残る問いは再定式化の側に移った）。鎖全体の定理・補題は 3,573 件。Part 259 は未着手で、次は補足8の範囲の方向ラウンド（尾の統合照合、β の再定式化 R1〜R3 の残余査定、γ の文献照合の扱い）を行い、Part 259 の推薦を1つ出す。その後、著者が 2026-11-15 に目的を「新しい幾何を作ること」と確定し、本線は基礎文書（定義層を1つの文書として書き上げること）に移った（補足9、骨格は `founding-document-outline-20261115.md`）。R1 の査定（互いに素な段の写像は (i)(ii) では一意でなく、偶数の法では $\chi(x) = (-1)^x$ の共役の捩れがある。(iii) フーリエ両立を足すと `shellLift` に一意化し、帰納系は有向な部分系の上で制限テンソル積を極限とする）を受けて、Part 259（PAG263、2026-11-15 閉鎖、67 定理）が第5章の不足を埋めるパートとして実施された：(i)(ii)(iii) を満たす写像がちょうど1つあるのは $\gcd(N, M/N) = 1$ のとき、そのときに限る（`existsUnique_compatF_iff`）。(iii) を外すと $a = 2$ では捩れた写像 `twLift` があり一意でない（奇数の場合の一意性は数値のみ）。添字の順序（＝古典的なユニタリ約数、E. Cohen 1960。鎖では Part 216 の `InLayer` と同じ概念だった）は有向でなく、無平方数の部分系では帰納系になり $\mathbb{C}$ 加群の極限 `sqLim` に単射に入る（代数構造と制限テンソル積との同型は Lean の外）。ラベルは、順序の性質が［既知］、一意性・非一意性・帰納系が［再導出（小さい）］で確定した（補足11）。鎖全体は 3,640 件、xlsx は final80（3,668 項目）。補足10で閉鎖条件とした尾の統合照合は Part 259 の報告に含まれず、補足11で独立の納品物として1回だけ行い尾の台帳を空にすることにした。γ の文献照合は著者側の作業に切り分けた。兆候4は11パート連続だが、Part 259 は基礎文書の章に仕えるパートとして位置づけが変わっている。事前登録の残候補 K2〜K4 は残余が計算だけか空であり、短期層の在庫として保持する。2026-11-19、方向 γ の構築側で開ける範囲の文献照合（検索 5 回、有限レベルの Bost–Connes と T(0) を結ぶ記述は見つからず、確信度：低〜中）の後、立て直した問いの推薦案（`notes/pag2_gamma_corner_preregistration.md`）を著者が 09:37 に採用し、Part 260（PAG264、短期層の小さいノート、定理 40）として実施した：N ∣ M のとき、φ(S) = (N/M)·π^* ∘ S ∘ π_*（読みでは ι S ι^†）は A_N を A_M に送る非単位的な代数準同型（gcd(N, M/N) によらない。N < M なら φ(1) ≠ 1）で、φ(E_s) = E_{(M/N)s}、φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s、引き戻しと両立、(a) 引き戻しとの両立と (b) φ(1) の値による一意性、合成と恒等の法則（正の整数の整除の順序の上の帰納系の 2 法則）を満たす。D 側は殻の span に入らない（Part 258 の強い読みの外。(2,4) の証人、一般には数値）。Lean の外：`DirectedSystem` としての束ねと極限、像が角全体であること（三重正則性からの帰結の見込み）、群環の側で Bost–Connes の ρ と一致すること（数値）。ラベルは E 側が［既知］（商スキームのべき等元による角の作用素版）、ほかは［再導出（小さい）］で、新規候補はない（対照群は ℤ/p^e の段に当たる場合だけ試した）。第 5 章の留保「代数版にはならない」は単位元を保つ写像についての文と読み直す（索引 5.5）。照合は独立照合・再照合・統合照合を受け、尾の台帳は空。鎖全体は 3,680 件、xlsx は final82（行 2〜3708）。同日午後、推薦案の R-d の残りを Part 261（PAG265、短期層、定理 10）として実施した：正の整数の整除の順序（Part 254 の `Lvl`）の上で角の写像は `DirectedSystem` をなし、Mathlib の一般の `DirectLimit` による極限 `CornerLim` は非単位的な環の構造と ℂ のスカラー倍を持つ。各段は単射に入り、極限は局所的な単位元（有限集合ごとに共通のべき等元）を持つが、左単位元を持たない。局所的な単位元の文はどの直極限でも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ（その証明は素数冪の段を要らない見込み、手計算）。ラベルは［再導出（小さい）］、新規候補なし、尾の台帳は空。鎖全体は 3,690 件、xlsx は final83（行 2〜3718）。Part 248 で生成の分類は完結し、Part 249 から本来の道（B-3：有限レベルのイデール類群 $C_{\mathbb Q}/U_N$）に移っている。Part 250 は解像度と創発の定式化（著者が 2026-11-11 に採用した案1＋案2：基礎を正の有理数の群に置き、ε-鎖の連結性 chainIn で見る）。結果の正直な要約：示せたのは「ℝ の中に基礎が、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として入っている」こと（教科書的な例の対数座標版、新規候補なし）。「解像度を落とすと直線が創発する」は示せていない — 商を取ると1点につぶれ、ℝ は完備化（ε → 0 の側）から現れるうえ、ℝ は定義に最初から使われている。「解像度を落とす／創発」の操作については、2026-11-12 に著者が候補3（全素点を同時に粗く見る）を選んだが、盲検同定の結果、有限の S では外した素数が見えない「有限素点の影」に留まることが分かり、著者は Part 249 の射影極限の側から進めることにした。Part 251 はその実施：両立する系の群 unitSys（$\varprojlim (\mathbb{Z}/N)^\times$ の具体モデル）× ℝ の中で、素数の類 $\kappa_p$（レベル N の成分は $w_p(N) = 1 + p^{N!}(p-1)$ の逆元。$p \nmid N$ では $p^{-1}$、$p$ の冪のレベルでは 1）が生成する部分群の稠密性を示した（＋一意性 primeSys_unique）。既知の再導出で新規候補なし。Lean にしていないもの：unitSys ≅ Ẑ^×、極限の普遍性・コンパクト性・位相群性、構造定理 $C_{\mathbb Q} \cong \widehat{\mathbb Z}^\times \times \mathbb{R}_{>0}$（「イデール類群で稠密」はこの同一視のもとでの読み）。兆候4（初等的な部品の組み合わせだけ）は Part 249〜257 と9パート連続になった（Part 252・253・254 は小さいノートと分かったうえで選ばれたもの）。残る問いの棚卸し監査は 2026-11-12 に構築側が完了した（`pag2_audit_after_part251.md`、著者側の素案は `remaining-questions-inventory.md`）：全期間（Part 155〜251）の言い直しテストは全期で成功し、残る問い14件の内訳は、既知の定理かその帰結 10 件（うち4件は未検索で知識による見込み）、著者の判断が先 2 件（「解像度を落とす」の操作、無限素点の「重なり」の読み）、新規候補のまま 1 件（生成の分類。MathSciNet・zbMATH 未照合）、公理のまま 1 件（A1）。結論として、既知の再導出でない問いは形式化の側には残っていない。今回の検索で付いた対応：定理 2.6 の極限の側に Burnol（平行移動と可換な作用素は閉作用素でも掛け算作用素）、unitSys に FLT プロジェクトの ZHat（Ẑ の明示的定義。単数群版の先行は未確認）、有限レベル Bost–Connes に元の BC 系。その後、構築側は文脈を渡さないエージェント2つ（判定を見せない盲検＝ウェブ検索のみ、判定への批判＝ツールなし）で再監査を行い、結論3つをすべて弱めた（監査記録 §8）：言い直せることは「新しい概念が要らなかった」ことだけを示す（新しい内容がないことは示さない）、文献で照合したのは14件中4件、「問いは残らない」は「照合した範囲では見つかっていない」（確信度：中以下）。生成の分類は §3 の候補1と矛盾しないが範囲が狭まった（残るのは項目66と67〜69。「小さいノートの水準」の、誰も書いていない計算）。§3 の書き換えは著者の承認の後に行う。構築側からは事前登録（次のパートの前に、既知の対応と再導出でない文の条件を書く）の導入が提案されている。判断事項への著者側の回答は構築側への申し送りにまとめ済み：A1 ＝ 解釈の層の公準（内容は Tate の定理）、定理2.6 の U の空間 ＝ $C_{\mathbb Q}$ 上の関数（正則表現の側。Λ 切断の留保つき）、対照群テストは採用（§7 に条文化済み）。作戦（`strategy-nonconvergence.md`）は規則変更も含めて 2026-11-12 に著者が採用し、事前登録は §4 に「残余による問いの選択」として、盲検の問いテストは §7 に条文化した。2026-11-12 に著者は「創発に向けて進む」方針を示し、方向α（極限の上の商のはしご）は (a)(b) どちらの形でも本線にせず見直すことを決め、無限素点の「重なり」の読みは「ねじれた貼り合わせ（境界ユニタリ $U$）」と決定した（§1）。方向の判断材料と検討の進展は `emergence-next-directions.md`、δ の帰結の事前登録案は `preregistration-delta-first-consequence.md`。
+- PAG 2.0（有限レベル）：Lean 形式化。設計 Part 256 ＝ PAG260.lean まで完了（2026-11-13。Part 255 は有限個の素数が生成する部分群の像の稠密／離散の二分法と位相の選び方、Part 256＝候補 M1 は互いに素な法でのガウス和・ルート数の因数分解と貼り合わせ $U$ の固有値の法則。すべて既知の事実、新規候補なし。著者側が事前登録した方向βの前提（$A_N$ の帰納系）の登録は、構築側に本文が届いておらず開いたままだったが、2026-11-14 の補足4で全文転記して伝達した）。Part 252・253・254 は新規パートではなく短期層の小さいノートとして実施された（Part 252：主張 $U = JH_N$ の Lean 化。Part 253＝候補 K1：作用素 $T$ の線形化と $V_{\mathrm{prim}}$ 上でのユニタリ性。Part 254：Part 252 の残る問い2つ — 導手ごとの直交直和分解と、引き戻し両立性による族の一意性 $U_N$・帰納極限への組み立て $U_\infty$。いずれもラベルは［再導出］、新規候補なし。$U_N$ は A1 の位相を定義として入れた作用素であり、A1 は導かれておらず公準のまま）。Part 256 終了時点で xlsx 3,552 項目。Part 257 の開始条件3件は 2026-11-14 にすべて解消した（申し送り補足4）：Part 252〜256 の再照合は完了し、形式文に偽・空虚・別物はなく新規候補もなかった（ずれはすべて文面側で、照合後の直しが Lean の docstring と冒頭説明に入っていなかったことに寄っていた。残件として、Part 254 の33文 S18〜S50 の逆翻訳 A がどの回でも未実施であることと、B4 後の記録のみの直し（記録 §9）の突き合わせを、Part 257 の閉鎖条件として付随させる）。方向β登録は本文が構築側に届いていなかったため補足4に全文転記して伝達した（Part 255 の結果との突き合わせと運命の明示は構築側の次回報告の仕事）。「08:41 の定義」は構築側では送付済みだが著者側に原文が残っておらず、開始条件としては閉じた（§1 の文面との照合は著者側の残作業）。Part 257 は、登録の突き合わせで前提の問いが未回答と確認されれば、登録 §6 の3段階（盲検の問いテスト＋文献照合→数値→Lean）で β の前提を問うことが委任のもとで決定済みだったが、実際には 2026-11-14 に候補 P1（互いに素な法の列に対するガウス和・ルート数の因数分解、PAG261、25 定理）として閉じられ、β 登録の突き合わせは未了のままである。決定・登録した問いと違う問いが閉じられるのは Part 255・256・257 と3パート連続であり、補足4 §1 で Part 257 の閉鎖条件とした残件（S18〜S50 の逆翻訳 A、記録 §9 の突き合わせ、重複注記ラウンド）も報告に現れていない。照合者 B の文面指摘14件の直しは未照合のまま閉じられた（構築側が開示）。一方、閉じる前の機械的な重複照合（新規則）は初めて設計どおりに働き、同一文の宣言2つと Mathlib と同じ文の補題1つを閉鎖前に除去した。兆候4は9パート連続となり、著者の方針（収束からの離脱）のもと、Part 258 は始めず方向の監査を次の作業と決定した（補足6：β 突き合わせ、未照合残件の全棚卸し、問いの置き換わりの監査、次方向の残余査定）。送付されたとされる Part 257 の3ファイルは著者側に未達。その後、同日 21:45 に構築側が登録全文を受け取って突き合わせを完了し、開始条件2は閉じた（記録 `pag2_beta_registration_check.md`、著者側にも全文が届いた）：Part 255 は β のパートではなく（著者が構築側のセッションで 08:38 に L1 を選択）、β の問いは段階 1〜3 のどれも試していない。Part 257 の開始も、2026-11-14 20:59 の著者自身の判断（条件2を保留のまま始める。それ以前の同日の判断「監査は進め、Part 257 は待つ」を置き換えた）によるもので、候補 P1 も著者が選んだ。すなわち Part 255〜257 の問いの選択は構築側のセッションでの著者の選択であり、著者側の申し送り・登録との二重の経路がずれの原因だった（補足6 §2 (a) の書き方は補足7で訂正）。引き継ぎメモ `PAG2_handoff_part257.md` は著者側に保存済みで、08:41 の定義の原文もその中にあった（§1 に転記）。β は切り分けをもって開いたままである：互いに素な段（$N$ と $M/N$ が互いに素）は Part 228（PAG232）の `shellAlgTensorEquiv`・`leftHom` でほぼ答えがある見込み（条件 1 は満たす。条件 2・3 は手計算の見込みで未確認。確信度：中）で、登録 §2 の「直積の定理はこの問いを答えない」は互いに素な場合については言い過ぎだったと訂正する。残余は素数冪の段 $p^e \to p^{e+1}$（例：$(2,4), (2,8), (3,9)$）で、鎖に該当する宣言は見つかっていない。重複監査は F2 まで完了した（2 回目の直し：22 件が直り、2 件が一部、新しい指摘 16 件、形式文の変更なし。F2 の後の直しは記録のみで未照合 — 残件に加わる）。Part 258（PAG262、2026-11-15 閉鎖）は方向βの前提を登録の読み（単位元を保つ代数準同型、引き戻しとの両立、殻を混ぜない強い読み）で判定した：$N \mid M$ のとき、そのような写像があるのは $\gcd(N, M/N) = 1$ のとき、そのときに限る（`exists_compatible_hom_iff`、23 定理、sorry 0）。存在の側はテンソル積（既知）で、不在の側は §3 の候補3。読みとして、β をこの写像たちの帰納極限として立てる道は、整除順序の共終な系が指数を上げる段を必ず含むため閉じる（弱い読み・非単位的な写像・別の両立条件は答えの外。互いに素な段だけの系は別）。補足7の閉鎖条件4件（S18〜S50 の逆翻訳 A、記録 §9、F2 後の直し、Part 257 の直し）は照合（F3）を受けてすべて閉じた。残る未照合の尾は、F3 の後の記録のみの直しと、Part 258 の照合者 B の後の文面の直し（主張の範囲に関わる言い換えを含む）の2件で、補足8で停止の規約（統合照合の後は主張を変えない直しだけを許し、変える直しはもう1回の統合照合を条件とする）と合わせて次回の統合照合の対象とした。兆候4は Part 249〜258 で10パート連続。ただし Part 258 は、事前登録された残余のある問いへの両方向の完全な答えであり、「前提の判定」が方向を実際に変えた（β の (1)〜(3) の道は閉じ、残る問いは再定式化の側に移った）。鎖全体の定理・補題は 3,573 件。Part 259 は未着手で、次は補足8の範囲の方向ラウンド（尾の統合照合、β の再定式化 R1〜R3 の残余査定、γ の文献照合の扱い）を行い、Part 259 の推薦を1つ出す。その後、著者が 2026-11-15 に目的を「新しい幾何を作ること」と確定し、本線は基礎文書（定義層を1つの文書として書き上げること）に移った（補足9、骨格は `founding-document-outline-20261115.md`）。R1 の査定（互いに素な段の写像は (i)(ii) では一意でなく、偶数の法では $\chi(x) = (-1)^x$ の共役の捩れがある。(iii) フーリエ両立を足すと `shellLift` に一意化し、帰納系は有向な部分系の上で制限テンソル積を極限とする）を受けて、Part 259（PAG263、2026-11-15 閉鎖、67 定理）が第5章の不足を埋めるパートとして実施された：(i)(ii)(iii) を満たす写像がちょうど1つあるのは $\gcd(N, M/N) = 1$ のとき、そのときに限る（`existsUnique_compatF_iff`）。(iii) を外すと $a = 2$ では捩れた写像 `twLift` があり一意でない（奇数の場合の一意性は数値のみ）。添字の順序（＝古典的なユニタリ約数、E. Cohen 1960。鎖では Part 216 の `InLayer` と同じ概念だった）は有向でなく、無平方数の部分系では帰納系になり $\mathbb{C}$ 加群の極限 `sqLim` に単射に入る（代数構造と制限テンソル積との同型は Lean の外）。ラベルは、順序の性質が［既知］、一意性・非一意性・帰納系が［再導出（小さい）］で確定した（補足11）。鎖全体は 3,640 件、xlsx は final80（3,668 項目）。補足10で閉鎖条件とした尾の統合照合は Part 259 の報告に含まれず、補足11で独立の納品物として1回だけ行い尾の台帳を空にすることにした。γ の文献照合は著者側の作業に切り分けた。兆候4は11パート連続だが、Part 259 は基礎文書の章に仕えるパートとして位置づけが変わっている。事前登録の残候補 K2〜K4 は残余が計算だけか空であり、短期層の在庫として保持する。2026-11-19、方向 γ の構築側で開ける範囲の文献照合（検索 5 回、有限レベルの Bost–Connes と T(0) を結ぶ記述は見つからず、確信度：低〜中）の後、立て直した問いの推薦案（`notes/pag2_gamma_corner_preregistration.md`）を著者が 09:37 に採用し、Part 260（PAG264、短期層の小さいノート、定理 40）として実施した：N ∣ M のとき、φ(S) = (N/M)·π^* ∘ S ∘ π_*（読みでは ι S ι^†）は A_N を A_M に送る非単位的な代数準同型（gcd(N, M/N) によらない。N < M なら φ(1) ≠ 1）で、φ(E_s) = E_{(M/N)s}、φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s、引き戻しと両立、(a) 引き戻しとの両立と (b) φ(1) の値による一意性、合成と恒等の法則（正の整数の整除の順序の上の帰納系の 2 法則）を満たす。D 側は殻の span に入らない（Part 258 の強い読みの外。(2,4) の証人、一般には数値）。Lean の外：`DirectedSystem` としての束ねと極限、像が角全体であること（三重正則性からの帰結の見込み）、群環の側で Bost–Connes の ρ と一致すること（数値）。ラベルは E 側が［既知］（商スキームのべき等元による角の作用素版）、ほかは［再導出（小さい）］で、新規候補はない（対照群は ℤ/p^e の段に当たる場合だけ試した）。第 5 章の留保「代数版にはならない」は単位元を保つ写像についての文と読み直す（索引 5.5）。照合は独立照合・再照合・統合照合を受け、尾の台帳は空。鎖全体は 3,680 件、xlsx は final82（行 2〜3708）。同日午後、推薦案の R-d の残りを Part 261（PAG265、短期層、定理 10）として実施した：正の整数の整除の順序（Part 254 の `Lvl`）の上で角の写像は `DirectedSystem` をなし、Mathlib の一般の `DirectLimit` による極限 `CornerLim` は非単位的な環の構造と ℂ のスカラー倍を持つ。各段は単射に入り、極限は局所的な単位元（有限集合ごとに共通のべき等元）を持つが、左単位元を持たない。局所的な単位元の文は、各段が単位的で移行写像が乗法を保つ直極限ならどれでも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ（その証明は素数冪の段を要らない見込み、手計算）。ラベルは［再導出（小さい）］、新規候補なし、尾の台帳は空。鎖全体は 3,690 件、xlsx は final83（行 2〜3718）。Part 248 で生成の分類は完結し、Part 249 から本来の道（B-3：有限レベルのイデール類群 $C_{\mathbb Q}/U_N$）に移っている。Part 250 は解像度と創発の定式化（著者が 2026-11-11 に採用した案1＋案2：基礎を正の有理数の群に置き、ε-鎖の連結性 chainIn で見る）。結果の正直な要約：示せたのは「ℝ の中に基礎が、全不連結だがどの尺度でも鎖でつながる稠密な部分集合として入っている」こと（教科書的な例の対数座標版、新規候補なし）。「解像度を落とすと直線が創発する」は示せていない — 商を取ると1点につぶれ、ℝ は完備化（ε → 0 の側）から現れるうえ、ℝ は定義に最初から使われている。「解像度を落とす／創発」の操作については、2026-11-12 に著者が候補3（全素点を同時に粗く見る）を選んだが、盲検同定の結果、有限の S では外した素数が見えない「有限素点の影」に留まることが分かり、著者は Part 249 の射影極限の側から進めることにした。Part 251 はその実施：両立する系の群 unitSys（$\varprojlim (\mathbb{Z}/N)^\times$ の具体モデル）× ℝ の中で、素数の類 $\kappa_p$（レベル N の成分は $w_p(N) = 1 + p^{N!}(p-1)$ の逆元。$p \nmid N$ では $p^{-1}$、$p$ の冪のレベルでは 1）が生成する部分群の稠密性を示した（＋一意性 primeSys_unique）。既知の再導出で新規候補なし。Lean にしていないもの：unitSys ≅ Ẑ^×、極限の普遍性・コンパクト性・位相群性、構造定理 $C_{\mathbb Q} \cong \widehat{\mathbb Z}^\times \times \mathbb{R}_{>0}$（「イデール類群で稠密」はこの同一視のもとでの読み）。兆候4（初等的な部品の組み合わせだけ）は Part 249〜257 と9パート連続になった（Part 252・253・254 は小さいノートと分かったうえで選ばれたもの）。残る問いの棚卸し監査は 2026-11-12 に構築側が完了した（`pag2_audit_after_part251.md`、著者側の素案は `remaining-questions-inventory.md`）：全期間（Part 155〜251）の言い直しテストは全期で成功し、残る問い14件の内訳は、既知の定理かその帰結 10 件（うち4件は未検索で知識による見込み）、著者の判断が先 2 件（「解像度を落とす」の操作、無限素点の「重なり」の読み）、新規候補のまま 1 件（生成の分類。MathSciNet・zbMATH 未照合）、公理のまま 1 件（A1）。結論として、既知の再導出でない問いは形式化の側には残っていない。今回の検索で付いた対応：定理 2.6 の極限の側に Burnol（平行移動と可換な作用素は閉作用素でも掛け算作用素）、unitSys に FLT プロジェクトの ZHat（Ẑ の明示的定義。単数群版の先行は未確認）、有限レベル Bost–Connes に元の BC 系。その後、構築側は文脈を渡さないエージェント2つ（判定を見せない盲検＝ウェブ検索のみ、判定への批判＝ツールなし）で再監査を行い、結論3つをすべて弱めた（監査記録 §8）：言い直せることは「新しい概念が要らなかった」ことだけを示す（新しい内容がないことは示さない）、文献で照合したのは14件中4件、「問いは残らない」は「照合した範囲では見つかっていない」（確信度：中以下）。生成の分類は §3 の候補1と矛盾しないが範囲が狭まった（残るのは項目66と67〜69。「小さいノートの水準」の、誰も書いていない計算）。§3 の書き換えは著者の承認の後に行う。構築側からは事前登録（次のパートの前に、既知の対応と再導出でない文の条件を書く）の導入が提案されている。判断事項への著者側の回答は構築側への申し送りにまとめ済み：A1 ＝ 解釈の層の公準（内容は Tate の定理）、定理2.6 の U の空間 ＝ $C_{\mathbb Q}$ 上の関数（正則表現の側。Λ 切断の留保つき）、対照群テストは採用（§7 に条文化済み）。作戦（`strategy-nonconvergence.md`）は規則変更も含めて 2026-11-12 に著者が採用し、事前登録は §4 に「残余による問いの選択」として、盲検の問いテストは §7 に条文化した。2026-11-12 に著者は「創発に向けて進む」方針を示し、方向α（極限の上の商のはしご）は (a)(b) どちらの形でも本線にせず見直すことを決め、無限素点の「重なり」の読みは「ねじれた貼り合わせ（境界ユニタリ $U$）」と決定した（§1）。方向の判断材料と検討の進展は `emergence-next-directions.md`、δ の帰結の事前登録案は `preregistration-delta-first-consequence.md`。
 - 番号対応の注意：第3期では設計メモの Part 番号が Lean ファイル番号より4小さい。対応表は `archive-catalog.md` を参照。
 - 件数：theorem/lemma は 3,344 件、xlsx 項目は 3,371 件（Part 251 終了時点、著者の監査による）。宣言総数など別の数え方と混同しない。
 
diff --git a/handoff/PAG2_handoff_part259.md b/handoff/PAG2_handoff_part259.md
index fb2e5c1..4013262 100644
--- a/handoff/PAG2_handoff_part259.md
+++ b/handoff/PAG2_handoff_part259.md
@@ -785,9 +785,9 @@
 - **方向 γ の文献照合（構築側で開ける範囲、2026-11-19、短期層）**：`notes/pag2_gamma_literature_builder.md`。内部照合で、これまでの照合は 2026-11-14 の盲検の検索 1 本だけと確かめてから行った。検索 5 回の範囲で、有限レベルの Bost–Connes と円分スキームの T(0) を結ぶ記述は見つからなかった（本文は開いていない。確信度：低〜中）。BC の有限レベルは群環 ℚ[ℤ/nℤ] の帰納系と ℕ^× の交差積（関数のレベル、既知）で、D_s を含む T(0) の側は出てこない。［観察］BC の帰納系は整除のすべての段を使うが、T(0) の側で引き戻しと両立し殻を混ぜない単位的な写像は互いに素な段だけ（Part 258・259）で、そのまま持ち上げる形は取れない。γ は開いたまま、MathSciNet・zbMATH は著者側。
 - **方向 γ の立て直し：着手前の 4 点と推薦案（2026-11-19）**：`notes/pag2_gamma_corner_preregistration.md`、数値と盲検の記録は `records/gamma_corner/`。
   - 内部照合：同じ構成が Part 258 の着手前の盲検の補足（問いの外）に 1 か所あるだけだった。Lean・xlsx にはない。
-  - 写像：φ(S) = ι S ι^†（ι は正規化した引き戻し）は単位元を保たず、どの段 N ∣ M でも A_N を A_M に送る（素数冪の段を含む）。像は角 Q A_M Q 全体。合成と両立し、整除の順序全体で直極限がとれる。群環の側では BC の ρ_{M/N}。
-  - 数値：M ≤ 30 の 111 組、鎖 276 本。像 = 角は三重正則性からの短い帰結（構築側と盲検の手計算が一致）。
-  - 対照群：関数体でも成り立つので、算術の内容はない。
+  - 写像：φ(S) = ι S ι^†（ι は正規化した引き戻し）は、N < M では単位元を保たず、どの段 N ∣ M でも A_N を A_M に送る（素数冪の段を含む）。像は角 Q A_M Q 全体（数値）。合成と両立し、整除の順序全体で直極限がとれる見込み（当時。のちに Part 260・261 で Lean）。群環の側では BC の ρ_{M/N}（数値）。
+  - 数値：M ≤ 30 の 111 組（N = M を含む）、鎖 276 本。像 = 角は三重正則性からの帰結の見込み（構築側と盲検の手計算が一致）。
+  - 対照群：ℤ/p^e の段に当たる場合（F_p[t]/(t^e)）だけを試し、そこでは同じ文が成り立った（互いに素な段は試していない）。
   - 盲検：Terwilliger 版の角の文、帰納系、BC と T(0) を結ぶ文献は、どれも見つからなかった（確信度：低〜中）。E 側は BC の表現の外。
   - 推薦：新しいパートは始めず、短期層で R-b・R-c・R-d を Lean にする（PAG264）。著者の決定待ち。
 - **Part 260（PAG264.lean、短期層の小さいノート、2026-11-19）**：09:37 に著者が上の推薦案を採用した。`notes/pag2_pag264_corner_maps.md`、記録は `records/audit264/`。
@@ -801,8 +801,8 @@
   - 照合：
     - 独立照合：偽・空虚なし。除去テストで (b)・(a)・積のどれを外しても一意でない。
     - 再照合：散文の 7 点（帰納系・非単位的の言い方など）を直した。その後の直しは尾。
-  - ラベル：E 側は［既知］、ほかは［再導出（小さい）］、新規候補なし（対照群でも成り立つ）。
-  - 件数：鎖全体の定理・補題は 3,677 件（3,640 + 37）。xlsx は final82（行 2〜3705）。
+  - ラベル：E 側は［既知］、ほかは［再導出（小さい）］、新規候補なし（対照群は ℤ/p^e の段に当たる場合だけを試し、そこでは成り立った）。
+  - 件数：鎖全体の定理・補題は 3,677 件（3,640 + 37）。xlsx は final82（行 2〜3705。恒等の法則を足す前の状態で、午後に同じ名前のまま行 2〜3708 に更新した。下の項）。
   - 索引に 5.5 を足し、5.2・6.3・§6 を直した（宣言名の確認 113/113）。辞書に §17 を足した。
 - **Part 260 の追加：恒等の法則と統合照合（2026-11-19 午後）**：
   - 足したもの：`fsum_self`・`cornerOp_self`・`cornerHom_self`（φ_{N,N} = id）。PAG264 は定理 40 になった。合成と合わせて帰納系の 2 法則が Lean に揃った。`DirectedSystem` としての束ねと極限は Lean の外。
@@ -818,7 +818,7 @@
     - 2 回目の照合で、局所的な単位元の標準の定義（有限集合ごとに共通のべき等元）に合わせて 3 定理を足した。
     - 3 回目の再照合の指摘 11 点を直し、尾の台帳は空。
   - 内部照合：`Lvl` は新しく作らず Part 254 のものを使った。下書きの `cornerSys_apply`（Part 260 の `cornerHom_coe` と同じ文）を消した。
-  - 読み：局所的な単位元の文はどの直極限でも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。
+  - 読み：局所的な単位元の文は、各段が単位的で移行写像が乗法を保つ直極限ならどれでも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。
   - 件数：鎖全体の定理・補題は 3,690 件。xlsx は final83（行 2〜3718）。
 - **極限の具体形：着手前の 4 点と推薦（2026-11-19 午後）**：`notes/pag2_limit_form_preregistration.md`、記録は `records/limit_form/`。
   - 数値：角の写像は中国剰余定理と両立する（1098 回）。
@@ -827,13 +827,14 @@
   - 推薦：Lean にせず、索引 5.5 に読みと文献を書くだけ（残余が空）。
   - 次に関門に通す候補：⊗'_p の外（無限素点・スケーリング・U）と A_∞ の相互作用。「射影」の章に直結。推薦ではなく、着手も未定。
 - **無限素点・スケーリング・貼り合わせ U と A_∞ の相互作用：着手前の 4 点と推薦（2026-11-19 夕方）**：`notes/pag2_projection_interaction_preregistration.md`、記録は `records/projection_interaction/`。
-  - 内部照合：単数との可換（Part 218 の `shellAlg_comm_dil`）、可換子 `fullComm`（Part 220）と N ∣ 12 の判定（Part 225）、フーリエ共役（Part 242）、`condPart`・`Vprim`・`JH_eq_rootNum_mul`・`UA1` が既にある。Hartley と殻の反転 J による共役、F_M ι = V F_N は鎖にない。
-  - 数値（N = 2〜36）：R_u・P・J（素数冪ごとの殻の反転の CRT の積）は A_N と可換。J∘H は A_N を正規化し D_s ↔ E_s。F_M ι = V F_N。単数の角は導手ごとの射影の張る代数。U_N が角に入るのは N ∣ 24（U_N = I）、符号は N ∣ 12 だけ。range(D_1) ∩ range(E_1) = V_prim。対照群 F_p[t]/(t^e) でも同じ形。
+  - 内部照合：単数との可換（Part 214（PAG218）の `shellAlg_comm_dil`）、可換子 `fullComm`（Part 220（PAG224））と N ∣ 12 の判定（Part 221（PAG225））、フーリエ共役（Part 242）、`condPart`・`Vprim`・`JH_eq_rootNum_mul`・`UA1` が既にある。Hartley と殻の反転 J による共役、F_M ι = V F_N は鎖にない。
+  - 数値（N = 2〜36）：R_u・P・J̃（素数冪ごとの殻の反転の CRT の積）は A_N と可換。J̃∘H は A_N を正規化し D_s ↔ E_s。単数の角は導手ごとの射影の張る代数。U_N が角に入るのは N ∣ 24（U_N = I）、符号は N ∣ 12 だけ。range(D_1) ∩ range(E_1) は次元が原始指標の数（空間としての一致は統合照合の後の追加計算）。F_M ι = V F_N は k = 2, 3、M ≤ 36 の 28 組。対照群 F_p[t]/(t^e)（p = 2 で e ≤ 4、p = 3 で e ≤ 3、p = 5 で e ≤ 2）では、可換・入れ替え・正規化・角の次元を調べて同じ形。
   - 失敗の記録（第 6 の型）：法 N の殻ごとの反転 s·w ↦ s·w⁻¹ は N = 10, 14, 15, … で A_N と可換でない（作業仮説を数値が否定した）。
-  - 盲検の問いテスト（ツール 35 回、約 962 秒）：全項目が数値と一致し、新しい内容は見つからなかった（確信度：中）。文献にない 4 つの短い計算は「せいぜい小さいノートの水準」。
+  - 盲検の問いテスト（ツール 35 回、約 962 秒）：数値で確かめた項目はすべて一致し、新しい内容は見つからなかった（確信度：中）。文献にない 4 つの短い計算は「せいぜい小さいノートの水準」。
   - 円環の検知：U の位相はガウス和と A1 から入り、A_∞ は導手の区分け以外の制約を課さない。
   - 推薦：Lean にせず、索引 2.9（新設）と 5.5 からの参照、辞書 §19 に読みと否定的な結果を書くだけ。構築側はこの線で新しい問いを開かず、著者側の起草からの依頼に応える側に回ることを提案。
-  - 著者の決定（2026-11-19 17:17）：「進めてください」で推薦を採った。索引 2.9 の見出しを内容の範囲（導手の区分けと N ∣ 24・N ∣ 12 の場合を除く）に狭めた。
+  - 著者の決定（2026-11-19 17:17）：「進めてください」で推薦（Lean にしない、記録だけ、構築側はこの線で新しい問いを開かない）を採った。その後、構築側が索引 2.9 の見出しを内容の範囲（導手の区分けと N ∣ 24・N ∣ 12 の場合を除く）に狭めた。
+- **索引の尾の統合照合（2026-11-19 夕方）**：第 5 版の後に足した索引の文・辞書 §17〜§19・この引き継ぎメモの差分を、照合者 1 人が照らした（`records/tail_audit4/`、約 20 分）。重い指摘 6 件（6.3 の条件の脱落、2.9 の `JH` への Ad の当て方と殻の反転の区別、2.9 の Lean の外の書き漏らし、2.9 の対照群の行の規約 T への誤った帰属、版・§7・§8 の未更新、このメモの Part 番号の取り違え）と、数値の範囲の書き広げなどの中くらいの指摘をすべて直し、索引を第 6 版にした（宣言名 131 件すべて実在）。2.9 の対照群の行の訂正は新しい数値の主張を含むので、再照合にかける。
 
 ## 点検（2026-10-24、Part 204 の後）
 - 全体の再ビルド：PAG.lean〜PAG208.lean（208 本）を空のディレクトリで最初からコンパイルし直した。208 本すべて成功、エラー・警告 0、約 10 分。#print axioms 1903 項目すべて標準の公理（またはその一部）。作業用の .out と 208/208 一致。
diff --git a/notes/pag2_founding_material_index.md b/notes/pag2_founding_material_index.md
index 6c8f613..373abf9 100644
--- a/notes/pag2_founding_material_index.md
+++ b/notes/pag2_founding_material_index.md
@@ -1,6 +1,6 @@
 # アーデル射影幾何 — 基礎文書の材料索引（骨格の 6 章ごと）
 
-（2026-11-18。短期層の作業。新しいパートではない。基礎文書の骨格（著者側、2026-11-15。以下「骨格」）の章ごとに、書く主張・その地位・支える Lean の宣言・ノート・照合の状態・開いている点を並べる。起草は著者側で行う。この索引は主張を足さない。地位とラベルは各ノート・CLAUDE.md・骨格の記載を写したもので、写すときに強めないことを方針とした。第 1 版を独立照合にかけ、その指摘で直した第 2 版を統合照合（2026-11-19）にかけ、その指摘で直したのが第 3 版、同日の著者の決定を記録したのが第 4 版、同日 07:10 の著者の確定を記録したのがこの第 5 版である（§8）。）
+（2026-11-18。短期層の作業。新しいパートではない。基礎文書の骨格（著者側、2026-11-15。以下「骨格」）の章ごとに、書く主張・その地位・支える Lean の宣言・ノート・照合の状態・開いている点を並べる。起草は著者側で行う。この索引は主張を足さない。地位とラベルは各ノート・CLAUDE.md・骨格の記載を写したもので、写すときに強めないことを方針とした。第 1 版を独立照合にかけ、その指摘で直した第 2 版を統合照合（2026-11-19）にかけ、その指摘で直したのが第 3 版、同日の著者の決定を記録したのが第 4 版、同日 07:10 の著者の確定を記録したのが第 5 版、同日の Part 260・261 と二つの関門（極限の具体形、A_∞ の相互作用）の記録を足し、その差分を統合照合にかけて直したのがこの第 6 版である（§8）。）
 
 ## §0 使い方と注意
 
@@ -15,7 +15,7 @@
   - 第 3 期（PAG 2.0）の Part n は PAG(n+4).lean。Lean の名前空間はファイル番号に従う（例：Part 252 の宣言は `PAG.Part256.…`、Part 23 の宣言は `PAG.Part27.…`）。初期のファイル（PAG.lean・PAG2〜PAG6）にはこの対応は当てはまらない。
   - この索引では「Part n（PAGm）」と併記し、宣言は完全修飾名で書く。
 - **記号の罠**：
-  - 反転（0 と ∞ の入れ替え）は、Lean の `PAG.Part23.W`・`PAG.Part26.Wpt`・`PAG.Part27.Wproj` とモノグラフの W。この索引では ι とも書く。
+  - 反転（0 と ∞ の入れ替え）は、Lean の `PAG.Part23.W`・`PAG.Part26.Wpt`・`PAG.Part27.Wproj` とモノグラフの W。この索引では反転に ι の記号を使わない（2.9・6.3 の引き戻しの記号 ι との衝突を避ける。第 6 版で改めた）。
   - `PAG.Part256.rootNum` の値（τ(χ)/(i^a√N)）は 𝔀(χ) と書く。PAG256 以降の docstring とノートでは記号 W(χ) がこの値を指すので、反転の W と混同しない。
 - **照合の状態**：各パートを閉じるときの独立照合と、その後の再照合・統合照合を指す。詳細は各ノートの照合の節。
 - **著者側のファイル**：骨格が引く次のファイルは、このリポジトリにない。索引ではファイル名だけを挙げる。
@@ -166,26 +166,28 @@
   - 局所定数との一致を書くときは、イデール類指標の正規化（2.7）も併記する（出所：索引の照合者の指摘と Part 257 の冒頭の説明。CLAUDE.md §1 に正規化を足すことを 2026-11-19 06:36 に著者が承認した）。
 - ノート：`pag2_literature_ia_sign.md`、CLAUDE.md §1。
 
-**2.9 有限素点の側の代数 A_∞ と、射影の変換・貼り合わせの位相・無限素点の符号。A_∞ は、導手の区分けと小さい法（位相は N ∣ 24、符号は N ∣ 12）の場合を除いて、位相も符号も見ない（否定的な結果、数値と手計算）。**
-- 地位：読みと否定的な結果（2026-11-19 夕方の関門、`pag2_projection_interaction_preregistration.md`）。新しい Lean はない。数値と盲検の手計算が一致した。Lean にしない推薦は、2026-11-19 17:17 に著者が「進めてください」で採った。
+**2.9 有限素点の側の代数 A_∞ と、射影の変換・貼り合わせの位相・無限素点の符号。A_∞ は、導手の区分けと小さい法（位相は N ∣ 24、符号は N ∣ 12。どちらも N ≤ 36 の数値と盲検の手計算）の場合を除いて、位相も符号も見ない（否定的な結果）。**
+- 地位：読みと否定的な結果（2026-11-19 夕方の関門、`pag2_projection_interaction_preregistration.md`）。新しい Lean はない。数値（N ≤ 36）と盲検の手計算が、数値で確かめた項目で一致した。Lean にしない・記録だけにする・構築側はこの線で新しい問いを開かない、という推薦を、2026-11-19 17:17 に著者が「進めてください」で採った。
+- 記号（この項だけ）：V_N = ℤ/N 上の関数。R_u f(x) = f(ux)、P = R_{−1}。H = Hartley 変換/√N（2.4 の `PAG.Part256.hartley` を √N で割ったもの）。J̃ = 素数冪ごとの殻の反転 p^k w ↦ p^k w⁻¹ を中国剰余定理でつないだ ℤ/N の置換（単数の上では u ↦ u⁻¹ で、2.4 の J を ℤ/N 全体に延ばしたもの。Lean の外）。
 - 内容：
-  - 単数の乗法 R_u・パリティ P = R_{−1}（無限素点の符号）・素数冪ごとの殻の反転の CRT の積 J は、どれも A_N と可換（可換子の側、イーデルの側）。読み：A_N = End(V_N)^{G_N}（G_N は 0 を固定し、すべての d ∣ N で合同関係を保つ置換の群）、可換子はその群環の像（二重可換子定理）。
-  - 射影の変換 J∘H（2.4）は、A_N の上で D_s ↔ E_s の双対の自己同型として働く（J が可換なので Ad(JH) = Ad(H) = Ad(F)）。
-  - フーリエは角の写像の系 φ（5.5）を 0 拡張の系 ψ（スケーリング、Bost–Connes の μ_n の型）に移す（F_M ι = V F_N。Pontryagin 双対）。
-  - 単数の角 D_1 A_N D_1 は導手ごとの射影の張る可換代数。U_N はこれと可換だが、属するのは N ∣ 24（そのとき U_N = I）のときだけ。符号の単数への制限が属するのは N ∣ 12 のときだけ。P ∈ A_N も N ∣ 12 のときだけで、極限では、符号は N ∣ 12 のレベルの角の上でだけ A_∞ に入る（数値 139 組）。
+  - R_u・P（無限素点の符号）・J̃ は、どれも A_N と可換（可換子の側、イーデルの側）。読み（盲検の手計算、確信度：中〜高、Lean の外）：A_N = End(V_N)^{G_N}（G_N は 0 を固定し、すべての d ∣ N で合同関係を保つ置換の群）、可換子はその群環の像（二重可換子定理）。
+  - J̃∘H（V_N の上の作用素。2.4 の `JH` は ℤ/N の関数を単数の上の関数に送る写像で、V_N の上の作用素ではない）による共役は、A_N の上で D_s ↔ E_s の双対の自己同型（J̃ が可換なので Ad(J̃H) = Ad(H) = Ad(F)。数値と手計算、Lean にあるのはフーリエ共役だけ）。
+  - フーリエは角の写像の系 φ（5.5）を 0 拡張の系 ψ（スケーリング、Bost–Connes の μ_n の型）に移す：F_M ∘（引き戻し/√(M/N)）＝（x ↦ (M/N)x に沿った 0 拡張）∘ F_N（Pontryagin 双対。数値は k = M/N = 2, 3、M ≤ 36 の 28 組、手計算で一般に成り立つ）。
+  - 単数の角 D_1 A_N D_1 は導手ごとの射影の張る可換代数（数値 N ≤ 36）。U_N はこれと可換だが、属するのは N ∣ 24 のときだけで、そのとき U_N = I。符号の単数への制限が属するのは N ∣ 12 のときだけ（どちらも数値 N ≤ 36 と盲検の手計算、確信度：中〜高）。
+  - P ∈ A_N となるのも N ≤ 36 では N ∣ 12 のときだけ（数値）。N ∣ 12 ⇒ P ∈ A_N は `PAG.Part225.fullComm_commute_iff_dvd_twelve`（Part 221（PAG225）：可換子が可換 ⇔ N ∣ 12。P ∈ A_N の文ではない）に二重可換子（Lean の外）を足せば出る。逆向きは数値だけ。極限では、符号は N ∣ 12 のレベルの角の上でだけ A_∞ に入る（数値：2 ≤ M ≤ 36 の約数の組 139 組。N = 1 と N = M を含み、φ(P_N) = P_M φ(1) なので実質は P_N ∈ A_N の確かめ直し）。
   - したがって A_∞ は、貼り合わせの位相（A1）にも無限素点の符号にも、導手の区分け以外の制約を課さない。位相はガウス和（H の中）と公準 A1 から入る。
-  - range(D_1) ∩ range(E_1) は原始指標の張る空間（2.5 の V_prim）で、J∘H はこれを保ち、そこでの制限が U_N の制限（2.5 のユニタリ性の構造上の理由づけ）。
-- 素朴な一般化の失敗（第 6 の型）：法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s）は、N = 10, 14, 15, … で A_N と可換でない。可換なのは素数冪ごとの反転の CRT の積。
+  - range(D_1) ∩ range(E_1)（V_N の中）は、0 拡張した原始指標の張る空間（2.5 の V_prim を 0 拡張で同一視したもの）。J̃∘H はこれを保ち、原始指標 χ に W(χ) = τ(χ)/(i^a √N) を掛ける（2.6 の U_N の原始指標での固有値と同じ値）。数値 N ≤ 36（空間としての一致と固有値は統合照合の後の追加計算）。2.5 のユニタリ性の構造上の理由づけとして読める。
+- 素朴な一般化の失敗（第 6 の型）：法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s）は、N = 10, 14, 15, … で A_N と可換でない（数値）。可換なのは J̃。
 - 書き方の規則：「A_∞ と射影の変換からルート数が出る」と書かない（円環の第 2 の型、注入→回収）。
-- Lean（既にあるもの）：
-  - 単数の乗法との可換：`PAG.Part218.shellAlg_comm_dil`。可換子 `PAG.Part224.fullComm`、可換子が可換 ⇔ N ∣ 12：`PAG.Part225.fullComm_commute_iff_dvd_twelve`。
-  - フーリエ共役：`PAG.Part246.fourierConj_convL_geps`・`PAG.Part246.fourierConj_mulLeft_dind`。
-  - 導手ごとの部分 `PAG.Part258.condPart`、原始部分 `PAG.Part257.Vprim`、`PAG.Part256.JH_eq_rootNum_mul`、U_N `PAG.Part258.UA1`。
-- Lean の外：Hartley 変換と殻の反転 J による共役の文、F_M ι = V F_N、単数の角の記述、N ∣ 24・N ∣ 12 の判定。
-- 対照群：関数体 F_p[t]/(t^e) でも同じ形（数値、p = 2, 3, 5）。判定の値（N ∣ 24 に当たるリスト）と位相の値は変わり、ℚ の値は Gauss の符号定理と i^a を無限素点の因子と読むこと（2.8 の規約 T）に依存する（照合者）。
-- 文献：Bastian–Humphries（arXiv:2606.19095）、Bhattacharyya–Song（arXiv:0809.1052）、arXiv:2510.17118 の式 (2)（T(v) ⊆ End_{G_v}）、Martin–Tanaka の解説（arXiv:0811.2475）、Kim–Kim（arXiv:1108.4947）、Montgomery–Vaughan 第 9 章、Shirbisheh（arXiv:0808.1767）、Arledge–Laca–Raeburn（1997）。照合者の WebSearch・WebFetch による。MathSciNet・zbMATH は未実施。
+- Lean（既にあるもの。どれもこの項の文そのものではない）：
+  - 単数の乗法との可換：`PAG.Part218.shellAlg_comm_dil`（Part 214（PAG218））。可換子 `PAG.Part224.fullComm`（Part 220（PAG224））、可換子が可換 ⇔ N ∣ 12：`PAG.Part225.fullComm_commute_iff_dvd_twelve`（Part 221（PAG225））。
+  - フーリエ共役：`PAG.Part246.fourierConj_convL_geps`・`PAG.Part246.fourierConj_mulLeft_dind`（Part 242（PAG246））。
+  - 導手ごとの部分 `PAG.Part258.condPart`（Part 254（PAG258））、原始部分 `PAG.Part257.Vprim`（Part 253（PAG257）、単数の上の関数の部分空間）、`PAG.Part256.JH_eq_rootNum_mul`（Part 252（PAG256）、U と A1 は文に出てこない）、U_N `PAG.Part258.UA1`（Part 254（PAG258））。
+- Lean の外：A_N = End(V_N)^{G_N} と可換子の群による記述、J̃ とその可換性、H と J̃∘H による共役の文、0 拡張とフーリエの等式、単数の角の記述、N ∣ 24・N ∣ 12 の判定、P ∈ A_N ⇔ N ∣ 12、range(D_1) ∩ range(E_1) = V_prim、J̃∘H がこれを保つこととその固有値。
+- 対照群：関数体 F_p[t]/(t^e)（p = 2 で e ≤ 4、p = 3 で e ≤ 3、p = 5 で e ≤ 2）で、R_u・J̃ の可換、F による入れ替えと正規化、単数の角の次元＝導手の数を調べ、同じ形だった（数値）。符号・0 拡張・V_prim は調べていない。判定の値（N ∣ 24 に当たるリスト）と位相の値は変わる（照合者）。ℚ の「N ∣ 24」は Gauss の符号定理と、位相に Hartley 核の 1/i^a（2.4）を含めることに依存する：素朴な核 τ/√f では、角に入るのは N = 2, 3, 4, 6, 12 で、8 と 24 が外れる（数値 N ≤ 36）。規約 T（2.8）のもとでは無限素点の局所定数は (−i)^a で、値 τ/(i^a √N) 自体はどちらの規約でも同じ。
+- 文献：Bastian–Humphries（arXiv:2606.19095）、Bhattacharyya–Song（arXiv:0809.1052、wreath powers。6.1 などの Bhattacharyya–Song–Tanaka 2010 とは別の文献の可能性がある、未照合）、arXiv:2510.17118 の式 (2)（T(v) ⊆ End_{G_v}）、Martin–Tanaka の解説（arXiv:0811.2475）、Kim–Kim（arXiv:1108.4947）、Montgomery–Vaughan 第 9 章、Shirbisheh（arXiv:0808.1767）、Arledge–Laca–Raeburn（1997）。照合者の WebSearch・WebFetch による。MathSciNet・zbMATH は未実施。
 - 推薦：Lean にしない。残余が空。
-- ノート：`pag2_projection_interaction_preregistration.md`。
+- ノート：`pag2_projection_interaction_preregistration.md`。数値：`records/projection_interaction/`（`interaction_check.log`、`extra_checks.log`、`sign_corner_check.log`、`control_fqt_interaction.log`）。
 
 ## 第 3 章　解像度と有効な姿（§1 の命題 3）
 
@@ -249,8 +251,8 @@
   - 条件の番号に注意。殻を混ぜない条件は、PAG262 の docstring・Part 259・CLAUDE.md §2 の番号では (ii)、Part 258 のノートでは (3)。強い読み（写像の像が殻ごとの span に入る：φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）は、Part 258 のノートでは「構築者の読みで、著者に確かめる事項」とされていた。2026-11-19 07:10 に著者が、Part 258 の定理が意味する条件として確定した。根拠は、2026-11-15 に強い読みの報告を受理したこと、事前登録の問いの鋭さと候補 3 の内容がこの読みに依存すること（CLAUDE.md §3）。弱い読みは将来の問いとして排除しない。
   - 答えの範囲の外：弱い読み、単位元を保たない写像、両立条件を別の形にした写像。
   - 対照群（盲検の申告で、未確認）の結果から、アーデル射影幾何に固有の内容としては数えない（Part 258 のノート）。
-  - 文献照合（MathSciNet・zbMATH と、Hanaki–Kim–Maekawa・Bastian–Humphries の本文）が済むまで、外部で新規性として使わない。
-  - 構築側で開ける範囲の文献照合（2026-11-19、`pag2_candidate3_literature_builder.md`）：Bastian–Humphries・Watanabe（arXiv:2305.19258）・Kim（arXiv:1109.1334）の本文に、商に沿った単位的な写像の記述は見つからなかった。Hanaki–Kim–Maekawa の本文は構築側の環境から取得できず、盲検の申告のまま。MathSciNet・zbMATH は著者側の作業として残る。
+  - 文献照合（MathSciNet・zbMATH と、Hanaki–Kim–Maekawa の本文）が済むまで、外部で新規性として使わない（Bastian–Humphries の本文は 2026-11-19 に構築側が WebFetch の要約を通して読んだ。下の行）。
+  - 構築側で開ける範囲の文献照合（2026-11-19、`pag2_candidate3_literature_builder.md`）：Bastian–Humphries・Watanabe（arXiv:2305.19258）・Kim（arXiv:1109.1334）の本文（WebFetch の要約を通した読み）に、商に沿った単位的な写像の記述は見つからなかった（見つからなかったは不存在の証明ではない）。Hanaki–Kim–Maekawa の本文は構築側の環境から取得できず、盲検の申告のまま。MathSciNet・zbMATH は著者側の作業として残る。
 - ノート：`pag2_part258_beta_premise.md`、CLAUDE.md §3。
 
 **5.2 Part 259：フーリエとの両立を足した一意性と、帰納系の添字。**
@@ -272,10 +274,37 @@
   - 非単位的な角の写像では、上の「代数版にはならない」は当てはまらない（5.5。上の文は単位元を保つ写像についての文）。
 - ノート：`pag2_part259_unitary_step_maps.md`、`pag2_R1_assessment.md`。
 
-**5.5 角の写像（非単位的）：N ∣ M のとき、φ(S) = (N/M)·π^* ∘ S ∘ π_* は A_N を A_M に送る非単位的な代数準同型で、合成と恒等の法則を満たす（gcd(N, M/N) によらない）。**
+**5.3 関数のレベルの帰納系。**
+- 地位：定理（Lean）。ラベルは、この索引では確かめていない。
+- Lean：
+  - Part 197（PAG201）：
+    - 引き戻し `PAG.Part201.pull`。
+    - ハール正規化の保存 `PAG.Part201.zket_pull`（仮定：t の素因数がすべて M を割る）。
+    - 法によらない定理 A `PAG.Part201.thmA_haar`（仮定：N の素因数がすべて d を割る。原始性）。
+  - Part 202（PAG206）：
+    - 引き戻しのフーリエ変換 `PAG.Part206.dft_pull_apply`。
+    - 旧部分 = 引き戻しの像 `PAG.Part206.oldP_eq_self_iff`。
+  - 単数の上の関数の帰納極限 `PAG.Part258.Lim`（2.6）。
+- 留保：
+  - 極限 ℂ[ℚ/ℤ] との同一視は骨格の記述で、この索引では Lean の文を確かめていない。
+  - `PAG.Part201.thmA_haar` の docstring は、この文を「Ẑ 上の定理 A」と呼ぶ。CLAUDE.md §0 は「Ẑ 上の定理 A」を未完の大域の問いに挙げ、§4 は 2026-11-12 の棚卸し監査で既知の定理かその帰結と判定したと書いている。
+- ノート：引き継ぎメモの項目 18・23。
+
+**5.4 互いに素な段のテンソル積。**
+- 地位：定理［既知］（直積スキームの一般定理 T(A×B) ≅ T(A)⊗T(B) の特別な場合）。
+- Lean：
+  - Part 228（PAG232）：`PAG.Part232.shellAlgTensorEquiv`、`PAG.Part232.leftHom`、`PAG.Part232.tensLift_injective`、`PAG.Part232.range_tensLift`。
+  - Part 236（PAG240）：
+    - 局所作用素 `PAG.Part240.locHom`。
+    - 一般の族の文 `PAG.Part240.tensEquiv`（A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
+    - 素数冪への分解 `PAG.Part240.ppEquiv`（これも A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
+- 留保：Part 258 の `shellLift` の作用素は、`locHom` の k = 0 と同じ式（Lean ではつないでいない。第 12 の型）。
+- ノート：引き継ぎメモの項目 49・57、CLAUDE.md §3。
+
+**5.5 角の写像：N ∣ M のとき、φ(S) = (N/M)·π^* ∘ S ∘ π_* は A_N を A_M に送る、単位元を保つとは限らない代数準同型（Lean の型 `→ₙₐ[ℂ]`。N < M では単位元を保たず、N = M では恒等）で、合成と恒等の法則を満たす（gcd(N, M/N) によらない）。**
 - 地位：定理（Part 260（PAG264）、短期層、2026-11-19）。
   - ラベル：E 側の像は［既知］（商スキームのべき等元による角）、ほかは［再導出（小さい）］。
-  - 対照群は ℤ/p^e の段に当たる場合（F_p[t]/(t^e)）に限って同じ文が成り立つ（数値。互いに素な段は試していない）。使うのは平行移動スキームの形式だけ（盲検の手計算）なので、アーデル射影幾何に固有の内容としては数えない。
+  - 対照群は ℤ/p^e の段に当たる場合（F_p[t]/(t^e)）だけを試し、そこでは同じ文が成り立った（数値。互いに素な段は試していない）。使うのは平行移動スキームの形式だけ（盲検の手計算）なので、アーデル射影幾何に固有の内容としては数えない。
 - Lean（Part 260（PAG264））：
   - A_M に入る：`PAG.Part264.cornerOp_mem`。写像 `PAG.Part264.cornerHom`。
   - 生成元の像：`PAG.Part264.cornerOp_geps`（φ(E_s) = E_{(M/N)s}）、`PAG.Part264.cornerOp_one`（φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s）、`PAG.Part264.cornerOp_dind`。
@@ -287,10 +316,10 @@
 - 留保：
   - 次のものは Lean の外。
     - 極限の具体形（Ẑ 上の局所定数関数への作用）。
-    - 像が角全体であること（数値 111 組、三重正則性からの短い帰結の見込み）。
+    - 像が角全体であること（数値 111 組（M ≤ 30、N = M の 30 組を含む）、三重正則性からの帰結の見込み）。
     - Bost–Connes の ρ との対応（6.3）。
-  - D 側は殻の span に入らないので、5.1 の強い読みの外。これは素数冪の段に固有ではない（N < M のすべての s：数値 81 組）。
-  - 極限は直極限（有限次元の代数の和集合）の側でとる。完備化は解像度が落ちる側の操作と読む（§1 の 08:41 の定義）。
+  - D 側は殻の span に入らないので、5.1 の強い読みの外。これは素数冪の段に固有ではない（数値：N < M の 81 組（M ≤ 30）のすべての s ∣ N で、φ(D_s) は D_t の span に入らない）。
+  - 極限は直極限（有限次元の代数の和集合）の側でとる。完備化は解像度が落ちる側の操作と読む（CLAUDE.md §1 の 08:41 の定義、索引 3.1）。
   - 照合：独立照合、再照合、統合照合（恒等の法則と尾）。統合照合の後の直しは主張を狭める・明確にするものだけで、尾の台帳は空。
 - 帰納系と極限（Part 261（PAG265）、短期層、2026-11-19 午後）：
   - 正の整数の整除の順序（Part 254 の `Lvl`）の上の `DirectedSystem`：`PAG.Part265.cornerSys_self`・`PAG.Part265.cornerSys_comp`。
@@ -298,44 +327,17 @@
   - 各段は単射に入る：`PAG.Part265.ofCorner_injective`。
   - 局所的な単位元：1 元ごとが `PAG.Part265.exists_local_unit`、有限集合ごとが `PAG.Part265.exists_local_unit_finset`。べき等元 e_a は a について増大する（`PAG.Part265.ofCorner_one_le`）。
   - 左単位元はない：`PAG.Part265.not_exists_left_one`。
-  - 局所的な単位元の文はどの直極限でも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。その証明は素数冪の段を要らない見込み（手計算）。
+  - 局所的な単位元の文は、各段が単位的で移行写像が乗法を保つ直極限ならどれでも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。その証明は素数冪の段を要らない見込み（手計算）。
   - 極限は直極限の側でとり、完備化は使っていない。
 - 極限の具体形（読み。Lean の外。2026-11-19 午後の盲検の問いテスト、`pag2_limit_form_preregistration.md`）：
   - 極限は Ẑ 上の局所定数関数の空間 V_∞ に、完備化なしに忠実に作用する（照合者の手計算）。
-  - 素点ごとに、局所の単位 e_1（定数への射影）に関する制限テンソル積 ⊗'_p に分かれる。Flath 型の当てはめ。角の写像が中国剰余定理と両立することは数値で 1098 回確かめた。
+  - 素点ごとに、局所の単位 e_1（定数への射影）に関する制限テンソル積 ⊗'_p に分かれる（照合者の答え、確信度：高）。Flath 型の当てはめ。角の写像が中国剰余定理と両立することは数値で 1098 回確かめた。
   - 文献：Flath（1979）、Deitmar（arXiv:1002.0475）、アデールの Schwartz–Bruhat 関数、Laca–Larsen–Neshveyev（arXiv:math/0609316、定理 3.2）。
-  - 否定的な観察（照合者、確信度：中）：局所の代数は抽象的な代数としては p によらない見込みで、A_∞ に入る算術は素点が可算個あることだけ。無限素点・スケーリング・貼り合わせ U は A_∞ に現れない。
+  - 否定的な観察（照合者、確信度：中）：局所の代数 A_{p^∞} は抽象的な代数としては p によらない見込みで、そうなら A_∞ に入る算術は素点が可算個あることだけ。ただし有限段の次元は p = 2 と奇素数で違う（A_{2^e} は e = 1〜4 で 4, 10, 19, 31、奇素数では e = 1〜3 で 5, 12, 22。統合照合の照合者の計算、Part 225–226 の次元公式と同じ）。無限素点・スケーリング・貼り合わせ U は A_∞ の元としてはほぼ現れない：例外と現れ方は 2.9（符号は N ∣ 12 の角の上で入る、U_N は N ∣ 24 で恒等、スケーリングはフーリエを通して φ ↔ ψ として現れる）。
   - 残余がないので、Lean にしない（推薦）。
 - 無限素点・スケーリング・貼り合わせ U との相互作用（読みと否定的な結果）：2.9。
 - ノート：`pag2_pag264_corner_maps.md`、`pag2_pag265_corner_limit.md`、`pag2_gamma_corner_preregistration.md`、`pag2_limit_form_preregistration.md`。
 
-**5.3 関数のレベルの帰納系。**
-- 地位：定理（Lean）。ラベルは、この索引では確かめていない。
-- Lean：
-  - Part 197（PAG201）：
-    - 引き戻し `PAG.Part201.pull`。
-    - ハール正規化の保存 `PAG.Part201.zket_pull`（仮定：t の素因数がすべて M を割る）。
-    - 法によらない定理 A `PAG.Part201.thmA_haar`（仮定：N の素因数がすべて d を割る。原始性）。
-  - Part 202（PAG206）：
-    - 引き戻しのフーリエ変換 `PAG.Part206.dft_pull_apply`。
-    - 旧部分 = 引き戻しの像 `PAG.Part206.oldP_eq_self_iff`。
-  - 単数の上の関数の帰納極限 `PAG.Part258.Lim`（2.6）。
-- 留保：
-  - 極限 ℂ[ℚ/ℤ] との同一視は骨格の記述で、この索引では Lean の文を確かめていない。
-  - `PAG.Part201.thmA_haar` の docstring は、この文を「Ẑ 上の定理 A」と呼ぶ。CLAUDE.md §0 は「Ẑ 上の定理 A」を未完の大域の問いに挙げ、§4 は 2026-11-12 の棚卸し監査で既知の定理かその帰結と判定したと書いている。
-- ノート：引き継ぎメモの項目 18・23。
-
-**5.4 互いに素な段のテンソル積。**
-- 地位：定理［既知］（直積スキームの一般定理 T(A×B) ≅ T(A)⊗T(B) の特別な場合）。
-- Lean：
-  - Part 228（PAG232）：`PAG.Part232.shellAlgTensorEquiv`、`PAG.Part232.leftHom`、`PAG.Part232.tensLift_injective`、`PAG.Part232.range_tensLift`。
-  - Part 236（PAG240）：
-    - 局所作用素 `PAG.Part240.locHom`。
-    - 一般の族の文 `PAG.Part240.tensEquiv`（A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
-    - 素数冪への分解 `PAG.Part240.ppEquiv`（これも A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
-- 留保：Part 258 の `shellLift` の作用素は、`locHom` の k = 0 と同じ式（Lean ではつないでいない。第 12 の型）。
-- ノート：引き継ぎメモの項目 49・57、CLAUDE.md §3。
-
 ## 第 6 章　位置づけ
 
 **6.1 殻代数 A_N は Terwilliger 代数 T(0) そのもの。**
@@ -360,8 +362,8 @@
 
 **6.3 Bost–Connes との接続。**
 - 地位（骨格の記述）：関数のレベルでは既知。T(0) の側に届くかは、方向 γ の文献照合の結果による。γ の文献照合は著者側の作業（CLAUDE.md §2）。
-- 構築側で開ける範囲の照合（2026-11-19、`pag2_gamma_literature_builder.md`）：検索 5 回の範囲で、有限レベルの Bost–Connes と T(0) を結ぶ記述は見つからなかった（本文は開いていない。確信度：低〜中）。BC の有限レベルは群環 ℚ[ℤ/nℤ] の帰納系（関数のレベル、既知）。［観察］BC の帰納系は整除のすべての段を使うが、T(0) の側の単位的な写像は互いに素な段だけ（5.1・5.2）。MathSciNet・zbMATH は著者側に残る。
-- 立て直しの結果（2026-11-19、Part 260（PAG264）、5.5）：BC の ρ_n（ρ_n(1) = μ_n μ_n^*）に倣った角の写像は、T(0) に非単位的な代数準同型として延びる（A_M に入ること・合成・一意性は Lean）。群環の側で ρ と一致することは数値で、Lean の外。盲検の手計算では、L²(Ẑ) の表現で T(0) の片側（D 側）が BC に対応し、もう片側（E 側）は BC の表現の外。Terwilliger 版の角の文と、BC と T(0) を結ぶ文献は見つからなかった（確信度：低〜中）。
+- 構築側で開ける範囲の照合（2026-11-19、`pag2_gamma_literature_builder.md`）：検索 5 回の範囲で、有限レベルの Bost–Connes と T(0) を結ぶ記述は見つからなかった（本文は開いていない。確信度：低〜中）。BC の有限レベルは群環 ℚ[ℤ/nℤ] の帰納系（関数のレベル、既知）。［観察］BC の帰納系は整除のすべての段を使うが、T(0) の側で引き戻しと両立し殻を混ぜない（強い読み）単位的な写像は互いに素な段だけ（5.1・5.2）。MathSciNet・zbMATH は著者側に残る。
+- 立て直しの結果（2026-11-19、Part 260（PAG264）、5.5）：BC の ρ_n（ρ_n(1) = μ_n μ_n^*）に倣った同じ式 ι S ι^†（ι は引き戻し/√(M/N)）は、群環 ℂ[ℤ/N]（平行移動）の上では ρ と一致し（数値、Lean の外）、T(0) の上では単位元を保つとは限らない代数準同型を与える（A_M に入ること・合成・一意性は Lean）。群環そのものは T(0) に含まれないので、「延びる」とは言わない。どちらの側が BC に対応するかは表示による：引き戻しの表示では平行移動の側（E 側を含む）が ρ に対応し、0 拡張の表示（γ の盲検の手計算では L²(Ẑ) の表現での μ_n）では乗法作用素の側（D 側）が対応する。二つの表示はフーリエで入れ替わる（2.9）。Terwilliger 版の角の文と、BC と T(0) を結ぶ文献は見つからなかった（確信度：低〜中）。
 - CLAUDE.md §2 には、有限レベル Bost–Connes に元の BC 系が対応する、という記載がある。
 - ノート：CLAUDE.md §2。
 
@@ -392,6 +394,7 @@
   - a が奇数のときの一意性（5.2）。
   - (i) と D の側だけを満たす写像の有無（5.2）。
   - 角の写像の像が角全体であること、極限の具体形、Bost–Connes の ρ との対応（5.5・6.3）。
+  - A_∞ と射影の変換・貼り合わせ・符号の相互作用の文（2.9 の「Lean の外」の行。Lean にしない推薦が採られている）。
 - **定式化の問い**：
   - 解像度の操作に、L1 を超える定式化が要るか。骨格の記述では、現時点では L1 と 08:41 の定義で文書は書ける。
   - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルについては 2.7。
@@ -401,7 +404,8 @@
 - この索引に出る完全修飾名を機械的に取り出し、`PAG.PartM.name` ごとに PAGM.lean の宣言の行（`theorem`・`def`・`abbrev`・`structure`・`instance` など）を検索した。
   - スクリプトは `records/founding_index/check_names.py`、出力は `check_names.log`。
   - 第 1 版は 85 件、第 2 版は照合者の指摘で足したものを含めて 102 件で、すべて実在した。第 3 版も 102 件ですべて実在した（`udvd_iff_inLayer` が加わり、`InLayer` は引数つきの書き方になったので機械的な抜き出しから外れた。`PAG.Part220.InLayer` の実在は第 2 版で確認済み）。
-- 「Part n（PAGm）」の併記がすべて m = n + 4 であることも、機械的に確かめた。
+  - 第 6 版（2026-11-19 夕方）は 131 件で、すべて実在した（5.5 の Part 260・261 の宣言、2.9 で新しく出た宣言と `PAG.Part256.hartley` を含む）。
+- 「Part n（PAGm）」の併記がすべて m = n + 4 であることも、機械的に確かめた（第 6 版でも確かめた。番号の列挙の書き方で機械的に拾われる組は手で確かめた）。
 - 照合者に渡した宣言の docstring と形式文の抜き出しには、`records/founding_index/extract_decls.py` を使った。
 
 ## §8 照合の記録
@@ -432,3 +436,11 @@
 - **著者の決定の記録（2026-11-19 06:36、第 4 版）**：「貼り合わせの合成」の貼り合わせは U（2.4、§6 の確認待ちから外した）。Part 257 の同定の確信度は高（2.7）。CLAUDE.md §3 の候補 1 の範囲は Part 245〜248 に訂正（6.2）。CLAUDE.md に足した ω の正規化は承認（2.8 の 3 つ目の規則の出所は、著者の承認を得た CLAUDE.md §1 の記載になった）。これは著者の決定の記録で、照合にはかけていない。
 
 - **著者の確定の記録（2026-11-19 07:10、第 5 版）**：Part 258 の殻を混ぜない条件は強い読みで確定（5.1。§6 の確認待ちから外した）。弱い (ii)・非単位的な写像・別の両立条件は、従来の記録どおり主張の外の別の問いとして残る。CLAUDE.md §3 の候補 3（日英）にも記録した。著者の決定の記録で、照合にはかけていない。
+
+- **統合照合（2026-11-19 夕方、第 6 版）**：第 5 版（コミット deab9f3）の後に足した文（5.1 の文献照合の行、5.2・5.5・6.3・§6、2.9）と、辞書 §17〜§19、引き継ぎメモの差分を、引く Lean の宣言 28 件の docstring と形式文、関門のノート 2 本、数値のスクリプトとログとともに、照合者 1 人が照らした（記録 `records/tail_audit4/`、所要 約 20 分）。照合者は数値のスクリプト 4 本を写して再実行し、ログは同じものが出た。
+  - 重い指摘：6.3 の［観察］から「引き戻しと両立し殻を混ぜない」の条件が落ちていた。2.9 で、2.4 の `JH`（単数の上の関数への写像）に Ad を当て、ℤ/N 全体の殻の反転と区別していなかった。2.9 の V_prim の等式・J∘H との一致・P ∈ A_N を、Lean の欄の宣言に支えられているように書き、「Lean の外」に入れていなかった。2.9 の対照群の行で、i^a を無限素点の因子とする読みを規約 T に帰していた（規約 T のもとでは無限素点の局所定数は (−i)^a）。版・§7・§8 を更新していなかった。引き継ぎメモの Part 番号の取り違え（Part 214（PAG218）、Part 221（PAG225））。
+  - 中くらいの指摘：数値の範囲の書き広げ（F_M ι = V F_N は 28 組、V_prim はスクリプトでは次元だけ、N ∣ 24・N ∣ 12 は N ≤ 36、対照群は調べた項目と p・e の範囲だけ、「すべて一致」は数値で確かめた項目だけ）。スクリプトの数え方の欠陥（比べない N も「偽でない」に数えていた）。5.5 の対照群の言い方（「に限って成り立つ」）、極限の具体形の否定的な観察の条件「そうなら」の脱落、5.5 と 2.9 の食い違い、5.1 の文献照合の残り、6.3 の BC の対応の表示、記号 ι・V・J の衝突。
+  - 直したこと：上のすべてを直した。2.9 は記号を定め、J̃（殻の反転の CRT の積）と 2.4 の J・`JH` を書き分け、主張ごとに数値の範囲と Lean の外を明記した。5.5 を 5.4 の後に移した。§0 の「ι とも書く」を外した。辞書 §17 の「*準同型」の * を外し、§17 の前書きに未記入の名前を書いた。CLAUDE.md と英語版、Part 261 のノート、引き継ぎメモの「どの直極限でも」を「各段が単位的で移行写像が乗法を保つ直極限なら」に狭めた。
+  - 追加の数値（照合者の追加計算と同じ項目を、構築側でも計算した。`records/projection_interaction/extra_checks.log`）：range(D_1) ∩ range(E_1) は空間として 0 拡張した原始指標の張る空間、J̃∘H は原始指標に W(χ) を掛ける、A_N' = span{R_u} となる N と A_N' が可換になる N はどちらも {2, 3, 4, 6, 12}、素朴な核 τ/√f では角に入るのは {2, 3, 4, 6, 12}（どれも N ≤ 36）。
+  - 照合の後の直しは、主張を狭める・範囲を書く・記録を事実に合わせる直しと、誤りの訂正（2.9 の対照群の行：規約 T への帰属を外し、依存先を Hartley 核の 1/i^a と書いた。新しい数値の主張を含む）。後者は補足 8 の「主張を変える直し」に当たるので、再照合にかける（下の行）。
+
diff --git a/notes/pag2_pag265_corner_limit.md b/notes/pag2_pag265_corner_limit.md
index b29ad22..a39750b 100644
--- a/notes/pag2_pag265_corner_limit.md
+++ b/notes/pag2_pag265_corner_limit.md
@@ -29,7 +29,7 @@ Lean は PAG265.lean：定理 10、sorry 0、警告 0。#print axioms 10 行は
 - 対比（前の Part の Lean の文との並置）：
   - 単位元を保ち殻を混ぜない写像の系は、互いに素な段にしかなく（Part 258（PAG262））、その順序は有向でない（Part 259（PAG263））。
   - 単位元を保たない角の写像の系は、整除の順序全体で帰納系をなし、極限は局所的な単位元を持つ非単位的な代数になる（この Part）。
-  - 局所的な単位元の 3 つの文は、どの直極限でも成り立つ一般の事実で、「非単位的」という内容を運ぶのは `not_exists_left_one` だけ。
+  - 局所的な単位元の 3 つの文は、各段が単位的で移行写像が乗法を保つ直極限ならどれでも成り立つ一般の事実で（2026-11-19 夕方の索引の統合照合の指摘で狭めた）、「非単位的」という内容を運ぶのは `not_exists_left_one` だけ。
   - その証明は d = 2c（c が偶数なら素数冪の段）をとるが、c を割らない素数 p で d = pc としても同じ筋が通るので、素数冪の段は要らない見込み（手計算）。効いているのは、N < M のどの段でも φ(1) ≠ 1（`cornerOp_one_ne_one`、gcd によらない）であることと単射性。
 
 ## §3 ラベルと範囲
diff --git a/notes/pag2_projection_interaction_preregistration.md b/notes/pag2_projection_interaction_preregistration.md
index c636df3..67f9240 100644
--- a/notes/pag2_projection_interaction_preregistration.md
+++ b/notes/pag2_projection_interaction_preregistration.md
@@ -9,9 +9,9 @@
   - 基礎文書の第 2 章（索引 2.4「射影」の変換と位相、2.6 U_N と U_∞）と第 5 章（索引 5.5）をつなぐ材料。§1 の「射影」の読み（アデール幾何とイーデル幾何を射影によって融合する）に仕える。
   - 2026-11-19 15:47 に著者が「進めてください」と言い、構築側が関門に通すことにした（着手の決定ではない）。
 - **内部照合**（Lean の全宣言を言葉で検索し、宣言を読んで確かめた）：
-  - 単数の乗法との可換：`PAG.Part218.shellAlg_comm_dil`（PAG218）。パリティ P = R_{−1} はその特別な場合。
-  - A_N の可換子：`PAG.Part224.fullComm`（Part 220、PAG224）とその次元 Σ_c m(c)²π(c)（`finrank_fullComm`）、可換子が可換 ⇔ N ∣ 12（`PAG.Part225.fullComm_commute_iff_dvd_twelve`）。根付き木の固定群 G_N による記述は鎖にない（極限の具体形の盲検の［観察］だけ）。
-  - フーリエ共役で D_s と E_s が入れ替わる：`PAG.Part246.fourierConj_convL_geps`・`fourierConj_mulLeft_dind`（Part 242）。Hartley 変換による共役の文は鎖にない。
+  - 単数の乗法との可換：`PAG.Part218.shellAlg_comm_dil`（Part 214（PAG218））。パリティ P = R_{−1} はその特別な場合。
+  - A_N の可換子：`PAG.Part224.fullComm`（Part 220、PAG224）とその次元 Σ_c m(c)²π(c)（`finrank_fullComm`）、可換子が可換 ⇔ N ∣ 12（`PAG.Part225.fullComm_commute_iff_dvd_twelve`、Part 221（PAG225））。根付き木の固定群 G_N による記述は鎖にない（極限の具体形の盲検の［観察］だけ）。
+  - フーリエ共役で D_s と E_s が入れ替わる：`PAG.Part246.fourierConj_convL_geps`・`fourierConj_mulLeft_dind`（Part 242（PAG246））。Hartley 変換による共役の文は鎖にない。
   - 導手ごとの部分：`PAG.Part258.condPart`（Part 254）。原始部分 `PAG.Part257.Vprim`。J∘H と原始指標：`PAG.Part256.JH_eq_rootNum_mul`（Part 252）。U_N：`PAG.Part258.UA1`。
   - 単数の上の反転：`PAG.Part256.JH` の中（u ↦ u⁻¹）と `PAG.Part253.globalInv`（単数の反転と実数の符号の組）。ℤ/N 全体の上の殻の反転は鎖にない。
   - 0 拡張の系 ψ：Part 260 の推薦案の数値（`records/gamma_corner/psi_corner.py`）だけで、Lean にない。
@@ -45,14 +45,16 @@
 | 法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s） | N = 10, 14, 15, 18, … で A_N と可換でない（素朴な一般化の失敗、第 6 の型。素数冪ごとの反転の CRT の積と、p² のような因子でずれる） |
 | H D_s H = E_s、H E_s H = D_s | すべての N |
 | J∘H が A_N を正規化 | すべての N（J が可換なので、共役は D_s ↔ E_s の入れ替え） |
-| F_M ι = V F_N | すべての組（k = 2, 3） |
+| F_M ι = V F_N | k = 2, 3、M = kN ≤ 36 の 28 組（統合照合の指摘で、比べた組だけを数えるようスクリプトを直した） |
 | D_1 A_N D_1 の単数への制限 | 導手ごとの射影の張る可換代数（次元＝現れる導手の数、射影そのものが入る） |
 | U_N と単数の角 | 可換。角に属するのは N = 2, 3, 4, 6, 8, 12, 24（単数群の指数が 2。U_N は恒等） |
 | P の単数への制限と角 | 属するのは N = 2, 3, 4, 6, 12 |
 | P ∈ A_N | N = 2, 3, 4, 6, 12（N ∣ 12。可換子が可換になる N で、`fullComm_commute_iff_dvd_twelve` と符合） |
-| P_M φ_{N,M}(1) ∈ A_M（N ∣ M ≤ 36、139 組） | N ∣ 12 のとき、そのときに限る（`sign_corner_check.log`）。符号は、N ∣ 12 のレベルから引き戻した関数の角の上でだけ A_∞ に入る |
-| range(D_1) ∩ range(E_1) | 次元＝原始指標の数。J∘H はこれを保つ |
-| 対照群 F_p[t]/(t^e)（p = 2, 3, 5） | 可換・入れ替え・正規化・角の次元＝導手の数が同じ形。J∘F の位相は原始指標の間で変わり、角に属さない（e が小さい場合を除く） |
+| P_M φ_{N,M}(1) ∈ A_M（2 ≤ M ≤ 36 の約数の組 139 組。N = 1 と N = M を含む） | N ∣ 12 のとき、そのときに限る（`sign_corner_check.log`）。φ(P_N) = P_M φ(1) なので、実質は P_N ∈ A_N の確かめ直し。符号は、N ∣ 12 のレベルから引き戻した関数の角の上でだけ A_∞ に入る |
+| range(D_1) ∩ range(E_1) | 次元＝原始指標の数。J∘H はこれを保つ。空間として 0 拡張した原始指標の張る空間と一致し、J∘H は原始指標に W(χ) を掛ける（統合照合の後の追加計算 `extra_checks.log`） |
+| 可換子 A_N'（追加計算） | A_N' = span{R_u}（次元の一致）となる N と、A_N' が可換になる N は、どちらも {2, 3, 4, 6, 12}（N ≤ 36） |
+| 素朴な核 τ/√f の位相（追加計算） | 角に入るのは N = 2, 3, 4, 6, 12（8 と 24 が外れる）。「N ∣ 24」は Hartley 核の 1/i^a を位相に含めることに依存する |
+| 対照群 F_p[t]/(t^e)（p = 2 で e ≤ 4、p = 3 で e ≤ 3、p = 5 で e ≤ 2） | R_u・J の可換、F による入れ替えと正規化、角の次元＝導手の数が同じ形。符号・0 拡張・V_prim は調べていない。J∘F の位相は原始指標の間で変わり、角に属さない（True になった (2,1)、(2,2)、(3,1) は導手の類が 1 元ずつの自明な場合）。U の類比は 1 点の値 λ = (JFχ)(1)/χ(1) で、原始的でない指標ではユニタリでなく、ℚ の U_N とは別物（統合照合の指摘。判定は変わらない） |
 
 - 分類：
   - (a) 可換子の側（R_u、P、J）と、双対の自己同型（J∘H）：既知の型の当てはめ。
@@ -66,7 +68,7 @@
 
 ### (4) 対照群テスト
 
-- 関数体 F_p[t]/(t^e)：同じ形で成り立つ（数値、p = 2, 3, 5、e ≤ 4）。
+- 関数体 F_p[t]/(t^e)：調べた項目（可換・入れ替え・正規化・角の次元）は同じ形で成り立つ（数値、p = 2 で e ≤ 4、p = 3 で e ≤ 3、p = 5 で e ≤ 2）。
 - Beurling の一般化素数：有限レベルの環がないので立たない（適用外）。
 - 扱い：形式の文で、ℚ に固有の算術はない。ℚ に固有に残るのは、無限素点の符号が実数の順序から来ること（関数体の無限素点は非アルキメデス的）だけで、その符号も A_∞ には見えない。
 
@@ -77,13 +79,13 @@
 ## §3 盲検の問いテスト
 
 - **条件**：新しいエージェントに WebSearch・WebFetch だけを使わせた（ツール 35 回、約 962 秒）。依頼文は `records/projection_interaction/prompt_blind.md`、出力の全文は `outputs/blind_output.md`、条件は `outputs/blind_meta.txt`。
-- **答え**（すべて構築側の数値と一致した。照合者は数値を使っていない）：
+- **答え**（構築側が数値で確かめた項目とはすべて一致した。Q1 の A_N' = span{R_u} ⇔ N ∣ 12 と Q5 の J∘H の固有値は、統合照合の後の追加計算で確かめた。照合者は数値を使っていない）：
   - Q1：R_u・P・J は A_N と可換（確信度：高）。J は 0 を固定するスキームの自己同型。A_N = End_{G_0}(V_N)（G_0 は 0 を固定し、すべての d ∣ N で合同関係を保つ置換の群。確信度：中〜高）。可換子は A_N' = ⊗_p A_{p^e}'、A_{p^e}' ≅ ℂ ⊕ ⊕_{c=1}^{e} M_{n_c(p)}(ℂ)^{⊕(e−c+1)}。A_N' = span{R_u} ⇔ N ∣ 12（手計算。鎖の `fullComm_commute_iff_dvd_twelve`（可換子が可換 ⇔ N ∣ 12）と同じ型で、同じ文ではない）。
   - Q2：H = F(Π_+ + iΠ_−)、H D_s H = E_s、H E_s H = D_s、H² = I。A_N の上で Ad(JH) = Ad(H) = Ad(F)（確信度：高）。
   - Q3：単数の角は導手ごとの射影 Π_f（f ∣ N、f ≢ 2 (mod 4)）の張る代数。U_N は常に可換で、角に属するのは N ∣ 24 のとき、そのときに限り、そのとき U_N = I（Gauss の符号の決定と、導手 p ≥ 5・9・16 での手計算。確信度：中〜高）。P の単数への制限は N ∣ 12 のときに限り角に属する。
   - Q4：F_M ι = V F_N。φ と ψ は Bost–Connes の共変関係 ρ_n をフーリエ変換で入れ替わる 2 つの見方（φ は平行移動の側、ψ は乗法作用素の側で μ_n の型。確信度：中〜高）。
   - Q5：range(D_1) ∩ range(E_1) は原始指標の張る空間（次元 φ*(N)、N ≡ 2 (mod 4) なら 0）。JH はこれを保ち、そこでの制限は U_N の制限と一致する（確信度：高）。
-  - Q6：関数体でも Q1・Q2・Q4・Q5 と Q3 の判定の形は同じ。ただし「N ∣ 24」に当たるリストと位相の値は変わる。ℚ の値は Gauss の符号定理と、i^a を無限素点の因子と読むことに依存する。
+  - Q6：関数体でも Q1・Q2・Q4・Q5 と Q3 の判定の形は同じ。ただし「N ∣ 24」に当たるリストと位相の値は変わる。ℚ の値は Gauss の符号定理と、i^a を無限素点の因子と読むことに依存する（照合者の言い方。統合照合の指摘で注記：依存するのは位相に Hartley 核の 1/i^a を含めることで、素朴な核 τ/√f では N = 8, 24 が外れる。規約 T（索引 2.8）のもとでは無限素点の局所定数は (−i)^a）。
   - Q7：照合した範囲で新しい数学の内容は見つからなかった（確信度：中。不存在の証明ではない）。文献に見つからなかったのは 4 つの短い計算（(1) 円分スキームの三重推移性・可換子の明示・N ∣ 12 の判定、(2) U_N ∈ 角 ⇔ N ∣ 24、P ∈ 角 ⇔ N ∣ 12、(3) φ と ψ を ρ_n の 2 つの見方として並べる整理、(4) D_1V ∩ E_1V の上で JH = U_N）で、評価は「せいぜい小さいノートの水準」。
   - 照合者の注意：U_N は A_N の角には（U_N = I の場合を除いて）入らず、可換子の側（単数群の群環）に属する。「A_N から U_N が出た」と読むと、ルート数を外から入れたものの読み替えになる。
 - **予想との照合**（`expected_note.md`）：Q1〜Q6 とも予想どおり。予想になかったのは、(i) 可換子の明示の形と A_N' = span{R_u} ⇔ N ∣ 12、(ii) Q3 の判定の値（N ∣ 24、N ∣ 12）が関数体では変わり、ℚ では無限素点の因子 i^a の読みに依存するという指摘、(iii) Q5 の次元の式。
@@ -96,8 +98,14 @@
 - **推薦**：この相互作用は Lean にせず、新しいパートも短期層も始めない。基礎文書の材料（索引の第 2 章に新しい項目 2.9、第 5 章 5.5 から参照）に、読みと否定的な結果と文献を書くだけにする。あわせて、構築側からこの線（角の写像の系 A_∞ のまわり）で新しい問いを関門に通すのは、ここで止める。
 - **理由**：
   1. 残余が空。Q1〜Q6 の核はどれも既知の型（Terwilliger 代数の構造と固定群、二重可換子定理、形式的自己双対性、原始指標のガウス和、Pontryagin 双対と Bost–Connes）の当てはめ。文献にない 4 つは短い計算で、§4 の規則では短期層に当たるが、どれも基礎文書の定義層に新しい内容を足さない（(4) は Part 253 の原始部分でのユニタリ性の構造上の理由づけで、ユニタリ性そのものは Lean にある）。
-  2. 対照群（関数体）でも同じ形。ℚ に固有に残るのは判定の値（N ∣ 24・N ∣ 12）だけで、その中身は U_N = I・符号が角の上で偶奇を混ぜないという自明な場合。
+  2. 対照群（関数体）でも、調べた項目は同じ形。ℚ に固有に残るのは判定の値（N ∣ 24・N ∣ 12）だけで、その中身は U_N = I・符号が角の上で偶奇を混ぜないという自明な場合。
   3. 円環の第 2 の型の検知：U の位相（ルート数）は H のガウス和と公準 A1 から入り、A_∞ は導手の区分け以外の制約を課さない。Lean にしても「A_∞ が A1 を選ぶ」ことは出ず、出るように書けば注入→回収になる。
-  4. 否定的な結果そのものが基礎文書に要る：有限素点の側の観測の代数 A_∞ は、貼り合わせの位相（A1）も無限素点の符号も、導手の区分けと N ∣ 12（符号）・N ∣ 24（位相）の自明な場合を除いて見ない。それらは可換子の側（単数群と殻の反転 J の側、イーデルの側）にある。射影の変換 JH は A_∞ に D_s ↔ E_s の双対として働き、フーリエは角の写像の系 φ を 0 拡張の系 ψ（スケーリング）に移す。第 2 章の「射影による融合」を、加法の側の代数とイーデルの側の可換子の対として書ける。
+  4. 否定的な結果そのものが基礎文書に要る：有限素点の側の観測の代数 A_∞ は、貼り合わせの位相（A1）も無限素点の符号も、導手の区分けと N ∣ 12（符号）・N ∣ 24（位相）の自明な場合を除いて見ない。それらは可換子の側（単数群と殻の反転 J の側、イーデルの側）にある。2.4 の JH の反転を ℤ/N 全体の殻の反転 J̃ に延ばした J̃∘H（Lean の外）は A_∞ に D_s ↔ E_s の双対として働き、フーリエは角の写像の系 φ を 0 拡張の系 ψ（スケーリング）に移す。第 2 章の「射影による融合」を、加法の側の代数とイーデルの側の可換子の対として書ける。
   5. 兆候 4 が続いている。極限の具体形に続いて、残余のない 2 回目の関門。有限レベルの代数のまわりで残余のある問いを構築側で見つけられていない、という事実を記録する。
 - **構築側で次に開ける問いについての正直な見立て**（推薦ではない）：残余のある問いは、公準 A1 を通るか（位相の選択。公準のまま）、完備化を通る（無限素点の連続な側。08:41 の定義では解像度が落ちる側の操作）かのどちらかに見え、どちらも有限レベルの Lean の問いとしては立たない。構築側は新しい問いを開かず、著者側の起草（第 1・2・5 章）から材料や照合の依頼が来たときに応える側に回ることを提案する。
+
+## §5 照合の記録
+
+- 2026-11-19 夕方、索引の尾の統合照合（`records/tail_audit4/`）で、このノートも引く文書として照らされた。直したこと：§0 の Part 番号の併記、§1 (3) の表（F_M ι = V F_N の組の数、139 組の中身、V_prim の空間としての一致と J∘H の固有値・可換子・素朴な核の追加計算、対照群の範囲と調べた項目と U の類比の注意）、§1 (4) の範囲、§3 の「すべて一致」の範囲と Q6 の注記、§4 の理由 2・4 の言い方。
+- 追加計算は `records/projection_interaction/extra_checks.py`（ログ `extra_checks.log`）。`interaction_check.py` は、比べた組だけを数えるように直して再実行した。
+
diff --git a/notes/pag2_terwilliger_dictionary.md b/notes/pag2_terwilliger_dictionary.md
index af09d02..02700c6 100644
--- a/notes/pag2_terwilliger_dictionary.md
+++ b/notes/pag2_terwilliger_dictionary.md
@@ -425,12 +425,12 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 
 ## 17. Part 260（PAG264、短期層）で足した名前（角の写像 A_N → A_M、2026-11-19）
 
-（Part 257〜259 の名前はこの辞書に未記入。今回の分だけ足す。）
+（Part 257〜259 の名前はこの辞書に未記入で、行そのものがない。例：`listChar`、`shellLift`、`twLift`、`UDvd`、`sqLim`、`canon`。下の「未記入の件数」はこの節の表の右列についての数で、行のない名前は含まない（2026-11-19 夕方の統合照合の指摘で明記した）。）
 
 | 名前・主張 | 文献の言葉 | 出典・注意 |
 |---|---|---|
 | `fsum`（繊維の和 π_*） | 押し出し（pushforward）、引き戻しの随伴（数え上げの内積で） | 標準 |
-| `cornerOp`・`cornerHom`（φ(S) = (N/M)·π^* ∘ S ∘ π_*） | 等長写像 ι = π^*/√(M/N) による共役 ι S ι^†（角への埋め込み、非単位的な *準同型）。Bose–Mesner の側では、商スキーム（部分群 H = Nℤ/Mℤ による商）の隣接代数がべき等元による角 e_H A e_H に同型という古典的事実 | 盲検（2026-11-19）が挙げた Zieschang, Theory of Association Schemes（2005）Thm 2.1.8(ii)・4.1.3、Kodalen 2019 §2.5（Lemma 2.13・2.14）。T(0) 版（T(X//H) が T(X) の角）の文献は見つからなかった（確信度：低〜中） |
+| `cornerOp`・`cornerHom`（φ(S) = (N/M)·π^* ∘ S ∘ π_*） | 等長写像 ι = π^*/√(M/N) による共役 ι S ι^†（角への埋め込み、単位元を保つとは限らない準同型。* の保存は Lean の文にない）。Bose–Mesner の側では、商スキーム（部分群 H = Nℤ/Mℤ による商）の隣接代数がべき等元による角 e_H A e_H に同型という古典的事実 | 盲検（2026-11-19）が挙げた Zieschang, Theory of Association Schemes（2005）Thm 2.1.8(ii)・4.1.3、Kodalen 2019 §2.5（Lemma 2.13・2.14）。T(0) 版（T(X//H) が T(X) の角）の文献は見つからなかった（確信度：低〜中） |
 | `cornerOp_one`（φ(1) = Σ_{(M/N) ∣ s} E_s） | 商スキームのべき等元 e_H = (1/|H|) σ_H（Bose–Mesner 代数の中） | 同上 |
 | 像 = 角全体（Lean の外） | 三重正則性（T = span{E*_i A_j E*_k}）からの帰結の見込み | Munemasa 1993 Lemma 4、Bhattacharyya–Song–Tanaka 2010 Thm 3.10（盲検が本文を開いた）、ℤ/p^e が K_p のリース冪であることは Bastian–Humphries 2026 Thm 3.7 |
 | 群環の側での φ（数値） | Bost–Connes の自己準同型 ρ_n（ρ_n(e(r)) = (1/n)Σ_{ns=r} e(s)、ρ_n(1) = μ_n μ_n^*） | 盲検の手計算（L²(Ẑ) の表現で ψ ↔ Ad μ_n）。T(0) の片側だけが BC に対応する |
@@ -445,7 +445,7 @@ Part の番号は使っていません。詳しい記録は `pag2_audit_after_pa
 | `exists_local_unit_finset`・`not_exists_left_one` | 局所的な単位元を持つが単位的でない環 | 同上 |
 | 極限の V_∞（Ẑ 上の局所定数関数）への作用（Lean の外） | Bruhat–Schwartz 関数の空間 C^∞(Ẑ) ≅ ⊗'_p C^∞(ℤ_p) | Bump、Ramakrishnan–Valenza（盲検が Wikipedia 経由で挙げた。未照合） |
 | 極限の素点ごとの分解 ⊗'_p（Lean の外） | Flath 型の制限テンソル積（球関数のべき等元 ↔ 定数への射影 e_1） | Flath 1979、Deitmar arXiv:1002.0475。Bost–Connes 型は Laca–Larsen–Neshveyev arXiv:math/0609316 定理 3.2 |
-| A_N = End(V_N)^{G_N}（照合者の手計算、Lean の外） | 根付き p 分木の頂点の固定部分群の中心化代数（Terwilliger 代数 = 中心化代数） | 次元の一致（Bhattacharyya–Song、Bastian–Humphries の命題 3.3）。文献での明記は未確認 |
+| A_N = End(V_N)^{G_N}（照合者の手計算、Lean の外） | 根付き p 分木の頂点の固定部分群の中心化代数（Terwilliger 代数 = 中心化代数） | 次元の一致（Bhattacharyya–Song（arXiv:0809.1052、wreath powers。§17 の Bhattacharyya–Song–Tanaka 2010 とは別の文献の可能性がある、未照合）、Bastian–Humphries の命題 3.3）。文献での明記は未確認 |
 
 - 未記入の件数（この節）：0。
 
diff --git a/records/projection_interaction/interaction_check.py b/records/projection_interaction/interaction_check.py
index 567edb9..b4de491 100644
--- a/records/projection_interaction/interaction_check.py
+++ b/records/projection_interaction/interaction_check.py
@@ -1,6 +1,6 @@
 """無限素点・スケーリング・貼り合わせ U と、有限素点の側の代数 A_N の相互作用（着手前の見込み確認。数値。証明ではない）。2026-11-19。
 
-記号：V_N = ℤ/N 上の関数。A_N = ⟨D_s, E_s⟩（Part 214 の shellAlg）。R_u f(x) = f(ux)（Part 218 の dil）。
+記号：V_N = ℤ/N 上の関数。A_N = ⟨D_s, E_s⟩（Part 214（PAG218）の shellAlg）。R_u f(x) = f(ux)（Part 214（PAG218）の dil）。
 P = R_{-1}（パリティ、無限素点の符号）。H = 離散 Hartley 変換/√N（核 cas(2πxy/N)）。F = フーリエ（e(−kx/N)/√N）。
 J = 殻ごとの反転：x = s·w（s = gcd(x, N)、w は法 N/s の単数）↦ s·w⁻¹（w⁻¹ は法 N/s）。
 U_N = Σ_χ phaseA1(χ)·P_χ（Part 254 の UA1、単数の上の関数）。phaseA1(χ) = rootNum(χ の原始指標)。
@@ -115,13 +115,12 @@ def run(Nmax):
         rep['H_swap'].append((N, all(np.allclose(H @ D[s] @ H, E[s]) and np.allclose(H @ E[s] @ H, D[s]) for s in dvs)))
         rep['JH_norm'].append((N, normalizes(B, J @ H, N)))
         # F φ F⁻¹ = ψ(F · F⁻¹)（M = N·k、k ≤ 3）
-        ok = True
+        # 比べた組だけを数える（統合照合 tail_audit4 の指摘 2-1 で直した。以前は比べない N も「偽でない」に数えていた）
         for k in (2, 3):
             M = N * k
             if M > Nmax: continue
             FN, FM = fourier(N), fourier(M); I, V = iota(N, M), vemb(N, M)
-            ok &= np.allclose(FM @ I, V @ FN)
-        rep['Fphi_psi'].append((N, ok))
+            rep['Fphi_psi'].append(((N, M), np.allclose(FM @ I, V @ FN)))
         # 単数の角：D_1 A_N D_1 を単数の上の関数に制限
         Ui = units(N)
         S = np.zeros((N, len(Ui)), dtype=complex)
```

## §C 直した後の索引の全文

# アーデル射影幾何 — 基礎文書の材料索引（骨格の 6 章ごと）

（2026-11-18。短期層の作業。新しいパートではない。基礎文書の骨格（著者側、2026-11-15。以下「骨格」）の章ごとに、書く主張・その地位・支える Lean の宣言・ノート・照合の状態・開いている点を並べる。起草は著者側で行う。この索引は主張を足さない。地位とラベルは各ノート・CLAUDE.md・骨格の記載を写したもので、写すときに強めないことを方針とした。第 1 版を独立照合にかけ、その指摘で直した第 2 版を統合照合（2026-11-19）にかけ、その指摘で直したのが第 3 版、同日の著者の決定を記録したのが第 4 版、同日 07:10 の著者の確定を記録したのが第 5 版、同日の Part 260・261 と二つの関門（極限の具体形、A_∞ の相互作用）の記録を足し、その差分を統合照合にかけて直したのがこの第 6 版である（§8）。）

## §0 使い方と注意

- **地位の語**：
  - 「定義」＝著者の文面（CLAUDE.md §1）。
  - 「読み」＝解釈の層。誰が出し、誰が採用したかを添える。
  - 「定理」＝Lean の文。ラベル［既知］［再導出］［新規候補］を添える。
  - 「公準」＝A1。
  - 「数値のみ」＝数値確認だけで、証明はない。
  - 「Lean の外」＝文献か手計算による。
- **番号の罠**：
  - 第 3 期（PAG 2.0）の Part n は PAG(n+4).lean。Lean の名前空間はファイル番号に従う（例：Part 252 の宣言は `PAG.Part256.…`、Part 23 の宣言は `PAG.Part27.…`）。初期のファイル（PAG.lean・PAG2〜PAG6）にはこの対応は当てはまらない。
  - この索引では「Part n（PAGm）」と併記し、宣言は完全修飾名で書く。
- **記号の罠**：
  - 反転（0 と ∞ の入れ替え）は、Lean の `PAG.Part23.W`・`PAG.Part26.Wpt`・`PAG.Part27.Wproj` とモノグラフの W。この索引では反転に ι の記号を使わない（2.9・6.3 の引き戻しの記号 ι との衝突を避ける。第 6 版で改めた）。
  - `PAG.Part256.rootNum` の値（τ(χ)/(i^a√N)）は 𝔀(χ) と書く。PAG256 以降の docstring とノートでは記号 W(χ) がこの値を指すので、反転の W と混同しない。
- **照合の状態**：各パートを閉じるときの独立照合と、その後の再照合・統合照合を指す。詳細は各ノートの照合の節。
- **著者側のファイル**：骨格が引く次のファイルは、このリポジトリにない。索引ではファイル名だけを挙げる。
  - `what-is-aadel-projective-geometry.md`
  - A8 の一次評価
  - δ の事前登録と帰結
  - モノグラフ層の記録
  - 骨格そのもの
- **宣言名の確認**：2026-11-18 に、この索引に出る宣言名をすべて Lean のファイルで検索し、実在を確かめた（§7）。

## 第 1 章　点と大域対象

**1.1 点は素数たちと無限素点。無限素点では無限大と無限小が重なり合う。**
- 地位：定義（著者の文面、CLAUDE.md §1）。
- Lean：定義そのものはない。関連する定理は次の 2 つで、どちらも Part 255（PAG259）の［既知］。
  - 正の有理数について、すべての素数（有限素点）の付値の組は単射：`PAG.Part259.eq_of_padicValRat_eq`。
  - 積公式 log q = Σ v_s(q) log s：`PAG.Part259.log_eq_sum_of_support`。∞ の座標は有限素点の座標から決まる。
- ノート：`pag2_part255_resolution_discrete_limit.md`。

**1.2 大域対象は、制限積の因子として最初から並列に共存する素点たち。有限レベル商と Λ 切断は、その全体への見方（切り方）。**
- 地位：読み。命題 3 の置き方として、著者側 Muse の決定（2026-11-13。著者はいつでも覆せる）。
- 書き方の規則：解像度を N・Λ と同一視する禁止は維持する。決まったのは問いの置き場であり、パラメータではない。
- Lean（関連するもの。支えではない）：
  - Ẑ^× の具体モデル `PAG.Part255.unitSys`（両立する系の群、Part 251（PAG255））。
  - 制限積・無限素点・ℚ^× での商は含まない。`unitSys` ≅ Ẑ^× と構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0} は Lean の外。
- ノート：CLAUDE.md §1、`pag2_part251_projective_limit.md`。A8 の一次評価は著者側のファイル。

**1.3 素数の類は、有限レベル (ℤ/N)^× × ℝ と、極限の具体モデル `unitSys` × ℝ で、稠密な部分群を生成する。**
- 地位：定理［既知］（再導出。新規候補なし）。
- Lean：
  - 有限レベルでは `PAG.Part253.exists_cls_near`（Part 249（PAG253））。正の有理数 m/n の類についての文。
  - 極限のモデルでは `PAG.Part255.dense_closure_allPrimes`・`PAG.Part255.dense_closure_primeGens`（Part 251（PAG255））。素数の類の一意性は `PAG.Part255.primeSys_unique`。
- 留保：「大域対象で稠密」「イデール類群で稠密」は、Lean の外の同一視（`unitSys` ≅ Ẑ^×、構造定理）を経た読み。
- ノート：`pag2_part249_idele_class_density.md`、`pag2_part251_projective_limit.md`。

**1.4 舞台は射影直線 P¹。反転が 0 と ∞ を入れ替える。**
- 地位：
  - 「舞台は P¹」は著者の言葉（2026-11-18 19:01、「射影」の読みの採用のとき）。
  - 「反転が 0 と ∞ を入れ替える」は構築側の読みで、2026-11-16 に著者が確認した。
  - P¹(ℤ/N) そのものは［既知］（モジュラー記号の標準の道具）。
- Lean（Part 19・22・23（PAG23・PAG26・PAG27））：
  - 射影直線 `PAG.Part27.ProjLine`、反転 [a:b] ↦ [b:a] の定義 `PAG.Part27.Wproj`、対合 `PAG.Part27.Wproj_Wproj`（一般の N）。
  - N = p^K（K ≥ 1）では、点モデル `PAG.Part26.Pt` との点集合の全単射 `PAG.Part27.projEquiv` と、点の数 `PAG.Part27.card_ProjLine`。
  - 2 チャートモデルの貼り合わせ条件 `PAG.Part23.Compat` と、その反転 `PAG.Part23.W`。点モデルの関数との線形同型 `PAG.Part26.ptEquiv`（一般の N）。
- 留保：
  - 「0 と ∞ は別の点で、反転がこの 2 点を入れ替える」という文は Lean にない（N ≥ 2 で正しい）。
  - N が 2 つ以上の素因数を持つとき、点モデルと P¹(ℤ/N) の点の数は一致しない（数え上げ、Lean の外）。
- ノート：`pag2_projection_material.md`（第 6 版）§1・§3。

## 第 2 章　無限素点の重なりと貼り合わせ

**2.1 重なりは、ねじれた貼り合わせ（境界ユニタリ U）と読む。**
- 地位：読み（著者の決定、2026-11-12）。
- 採らなかった読み：
  - 群の商として読む読み：A1 と両立しない。反例は法 9 の 3 次指標で、`pag2_resolution_overlap_materials.md` §3 の表に［批判］［数値］として記録されている。この反例の Lean の所在は、この索引では確かめていない。
  - W（反転）による商：A1 とは両立するが、D が商に降りない。
- ノート：`pag2_resolution_overlap_materials.md`、CLAUDE.md §1。

**2.2 モノグラフ層の作用素系（D、T_p、反転 W、二面体関係）、問題 P1、定理 2.6（境界条件 U の両立分類）。**
- 地位：モノグラフ層の記録（著者側、リポジトリにない）。
- Lean（有限レベル版だけ。Part 249（PAG253）、［再導出］）：
  - 素数の平行移動と可換なら、すべての単数の平行移動と可換：`PAG.Part253.commute_transl_of_prime`。
  - 指標ごとにスカラー：`PAG.Part253.eigenFun_of_commute_prime`。
  - (a)⇒(b) の完全な形：`PAG.Part253.thm26_full`。
  - 可換性を外した反例（N ≥ 3）：`PAG.Part253.thm26_needs_commute`。
- 留保：
  - 逆向き (b)⇒(a) は数値のみ。大域の Ẑ^× での形は Lean の外。
  - 証明は Dirichlet の算術級数定理を使わない簡略化で、新しい定理ではない。
- ノート：`pag2_part249_idele_class_density.md`。

**2.3 公準 A1（内容は Tate の定理）と、定理 2.6 との両立。**
- 地位：
  - A1 は公準（解釈の層の公準）で、導かれていない。
  - 両立は「既知の結果からの短い帰結」（確信度：高）。これはかつての新規候補 2 で、2026-11-12 に候補から外れた。
- 留保：
  - 定理 2.6 の反転の条件は、𝔀(χ⁻¹) = conj 𝔀(χ)（`PAG.Part258.rootNum_inv`。すべての指標で成り立つ短い計算）と、境界ユニタリの実性 KUK = U（`PAG.Part258.UA1_star`）に帰着する。|𝔀| = 1 には原始性と |τ|² = N が要る（`PAG.Part256.normSq_rootNum`・`PAG.Part258.normSq_phaseA1`）。A1 の算術の内容は、どの位相 α を選ぶかの部分だけ（`pag2_thm26_A1_collation.md` §11 の訂正）。
  - ルート数が条件を満たすことは整合性の確認にすぎず、A1 を導いたことにはならない。
  - 近い先行：Burnol、Ibort–Lledó–Pérez-Pardo の例 7.1・7.2（CLAUDE.md §3）。
- Lean：
  - ガウス和の側の部品の 3 定理（組み合わせた 1 つの文は形式化していない）：`PAG.Part16.normSq_gaussSum`、`PAG.Part173.gauss_inv_pair`、`PAG.Part198.gauss_sign_real`。番号の対応は各ファイルの冒頭の記載による：PAG16 は Part 12、PAG173 は Part 169、PAG198 は Part 194。
  - A1 の位相そのものについて（Part 254（PAG258））：
    - 𝔀(χ⁻¹) = conj 𝔀(χ)（すべての指標）：`PAG.Part258.rootNum_inv`。
    - 位相についての同じ式：`PAG.Part258.phaseA1_inv`。
    - 絶対値 1：`PAG.Part258.normSq_phaseA1`。
    - U_N は複素共役と可換（KUK = U）：`PAG.Part258.UA1_star`。
    - 内積を保つ：`PAG.Part258.ip_UA1`。
- ノート：`pag2_thm26_A1_collation.md`、`pag2_part254_full_gluing.md`、CLAUDE.md §3。

**2.4 「射影」の変換と位相：反転（乗法の側）と加法の変換（加法の側）の合成。**
- 地位：
  - 読み（2026-11-18 19:01、著者が留保つきで採用）。
  - 著者の言葉は「舞台は P¹、その上で働く貼り合わせの合成を射影と呼ぶ」。「反転と加法の変換の合成」は構築側の読みで、著者が 19:01 に留保つきで材料として採用した。著者の言葉「貼り合わせの合成」の貼り合わせは U（次の項）。
  - 「貼り合わせ」は U（ねじれた貼り合わせ）を指す（2026-11-19 06:36、著者の決定。`PAG.Part23.Compat`（ねじれのない座標の貼り合わせ）ではない）。
  - 標準の核は Hartley 核（著者の決定）。A1 の内容と揃うことは著者の判断で、根拠は PAG256 の冒頭のコメントの読み。モノグラフ本文とは照合していない（JH_N の正規化も本文で確かめていない）。
- Lean（Part 252（PAG256）、［再導出］）：
  - 写像 `PAG.Part256.JH`、値 `PAG.Part256.rootNum`（= 𝔀）、偶奇の因子 `PAG.Part256.parFac`。
  - すべての指標で、単数の上の式：`PAG.Part256.JH_eq_rootNum_mul_any`。
  - 原始指標で絶対値 1：`PAG.Part256.normSq_rootNum`。
  - 原始指標で単数の外に漏れない：`PAG.Part256.hartley_eq_zero_of_not_isUnit`。
  - 原始性を外した反例：`PAG.Part256.removal_counterexample`・`PAG.Part256.removal_counterexample_normSq`・`PAG.Part256.removal_counterexample_four`。
- 留保：
  - `JH` は ℤ/N の関数を単数の上の関数に送る写像で、P¹ の上の作用素ではない。照合した範囲（PAG23・PAG26・PAG27・PAG256）では、P¹ のモデルと結ぶ Lean の文はない（鎖全体は検索していない）。
  - 原始指標で 𝔀 がルート数であることは Lean の外。
  - 素朴なフーリエ核 e(xy) では値が τ(χ)/√N で、奇の指標で i 倍ずれる。このずれは滑らかにしない。
- ノート：`pag2_part252_hartley_gluing.md`、`pag2_projection_material.md`、`pag2_prereg_projection.md`。

**2.5 原始部分の作用素 T とユニタリ性。**
- 地位：定理［再導出］（Part 253（PAG257））。
- Lean：
  - すべての指標で T χ = 𝔀(χ)χ：`PAG.Part257.TopL_charU`。
  - 原始部分の上でユニタリ：`PAG.Part257.unitary_Vprim`。
  - 原始指標で A1 の位相を課した任意の線形写像は、原始部分の上で T と同じ値をとる：`PAG.Part257.TopL_eq_of_A1`（ほぼ同語反復）。
- 留保：Part 253 では U を Lean で定義していない（仮定の形でだけ現れる）。U_N の定義は 2.6。
- ノート：`pag2_part253_primitive_operator.md`。

**2.6 法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞。**
- 地位：定理［再導出］（Part 254（PAG258））。
- Lean：
  - 位相 `PAG.Part258.phaseA1` と U_N `PAG.Part258.UA1`。
  - 導手ごとの部分：`PAG.Part258.condPart_eq_map`。
  - 族の一意性：`PAG.Part258.UA1_family_unique`。
  - 帰納極限 `PAG.Part258.Lim`、その上の作用素 `PAG.Part258.Uinf`、一意性 `PAG.Part258.Uinf_unique`、内積の保存 `PAG.Part258.ipLim_Uinf`。
- 留保：
  - U_N は A1 の位相を定義として入れた作用素で、A1 は導かれていない。
  - 直和を 1 つの文にした定理はない。
  - `Lim` と Ẑ^× の上の局所定数関数との同一視、完備化 L²(Ẑ^×) は Lean の外。完備化は、読みとしては解像度が落ちる側の操作。
- ノート：`pag2_part254_full_gluing.md`。

**2.7 τ の素数冪の成分への分解と、互いに素な法の並びの形の指標についての 𝔀 の分解（交差項・符号つき。値のレベル）。**
- 地位：定理［既知（再導出）］（Part 256（PAG260）・Part 257（PAG261））。恒等式は原始性を使わない（原始的でない指標では 𝔀 は位相でないことがある：`PAG.Part256.removal_counterexample_normSq`・`PAG.Part256.removal_counterexample_four`。全称の文は Lean の外）。
- Lean：
  - 互いに素な 2 つの法：`PAG.Part260.rootNum_prodChar`・`PAG.Part260.parFac_prodChar`・`PAG.Part260.crossSign`。
  - 互いに素な法の並び：`PAG.Part261.rootNum_listChar_formII`・`PAG.Part261.parFac_listChar`。
  - 成分への分解とその一意性：`PAG.Part261.exists_listChar`・`PAG.Part261.listChar_injective`（並びの形で言う。法 n の形での一意性は文にしていない）。
  - すべての素数への τ の分解：`PAG.Part261.gaussSum_primeFactors`（τ の文で、𝔀 の文ではない）。
- Lean の外：
  - 原始指標で s = 1/2 のとき、形 (II) の素数ごとの因子は Tate の局所定数と、`parFac` は無限素点の局所定数 (−i)^a と値が一致する（値の一致で Lean の外。Part 257 では読みとして記録。文献照合ノートは PAG の量との対応に［再導出（小さい）］を付けている）。
  - この一致には、加法指標の規約 T と、イデール類指標の正規化 ω_q(q) = χ(q) の両方が要る。ω を χ̄ に対応させる規約では、積は 𝔀 の共役になる。
  - Part 257 で読みとして記録した（確信度：中〜高）ものを、2026-11-18 の文献照合で確かめ直した。確信度は、2026-11-19 06:36 の著者の判断で高とする（上の条件のもとでの値の一致として。Lean の外）。
  - 「局所因子」という語は読み。
- ノート：`pag2_part256_gluing_cross_term.md`、`pag2_part257_local_factor_decomposition.md`、`pag2_literature_ia_sign.md`。

**2.8 加法指標の規約は規約 T（Tate の学位論文の加法指標：ψ_∞(x) = e^{−2πix}、ψ_p(x) = e^{+2πi{x}_p}）。**
- 地位：著者の決定（2026-11-18 19:25）。基礎文書の標準とする。
- 書き方の規則：
  - 明示的な因子 i^{±a} が無限素点の局所定数であることは、規約によらない。
  - 符号 χ(−1) の置き場は規約による。規約 T を明示せずに「ε(χ) は無限素点から来る」と書かない。
  - 局所定数との一致を書くときは、イデール類指標の正規化（2.7）も併記する（出所：索引の照合者の指摘と Part 257 の冒頭の説明。CLAUDE.md §1 に正規化を足すことを 2026-11-19 06:36 に著者が承認した）。
- ノート：`pag2_literature_ia_sign.md`、CLAUDE.md §1。

**2.9 有限素点の側の代数 A_∞ と、射影の変換・貼り合わせの位相・無限素点の符号。A_∞ は、導手の区分けと小さい法（位相は N ∣ 24、符号は N ∣ 12。どちらも N ≤ 36 の数値と盲検の手計算）の場合を除いて、位相も符号も見ない（否定的な結果）。**
- 地位：読みと否定的な結果（2026-11-19 夕方の関門、`pag2_projection_interaction_preregistration.md`）。新しい Lean はない。数値（N ≤ 36）と盲検の手計算が、数値で確かめた項目で一致した。Lean にしない・記録だけにする・構築側はこの線で新しい問いを開かない、という推薦を、2026-11-19 17:17 に著者が「進めてください」で採った。
- 記号（この項だけ）：V_N = ℤ/N 上の関数。R_u f(x) = f(ux)、P = R_{−1}。H = Hartley 変換/√N（2.4 の `PAG.Part256.hartley` を √N で割ったもの）。J̃ = 素数冪ごとの殻の反転 p^k w ↦ p^k w⁻¹ を中国剰余定理でつないだ ℤ/N の置換（単数の上では u ↦ u⁻¹ で、2.4 の J を ℤ/N 全体に延ばしたもの。Lean の外）。
- 内容：
  - R_u・P（無限素点の符号）・J̃ は、どれも A_N と可換（可換子の側、イーデルの側）。読み（盲検の手計算、確信度：中〜高、Lean の外）：A_N = End(V_N)^{G_N}（G_N は 0 を固定し、すべての d ∣ N で合同関係を保つ置換の群）、可換子はその群環の像（二重可換子定理）。
  - J̃∘H（V_N の上の作用素。2.4 の `JH` は ℤ/N の関数を単数の上の関数に送る写像で、V_N の上の作用素ではない）による共役は、A_N の上で D_s ↔ E_s の双対の自己同型（J̃ が可換なので Ad(J̃H) = Ad(H) = Ad(F)。数値と手計算、Lean にあるのはフーリエ共役だけ）。
  - フーリエは角の写像の系 φ（5.5）を 0 拡張の系 ψ（スケーリング、Bost–Connes の μ_n の型）に移す：F_M ∘（引き戻し/√(M/N)）＝（x ↦ (M/N)x に沿った 0 拡張）∘ F_N（Pontryagin 双対。数値は k = M/N = 2, 3、M ≤ 36 の 28 組、手計算で一般に成り立つ）。
  - 単数の角 D_1 A_N D_1 は導手ごとの射影の張る可換代数（数値 N ≤ 36）。U_N はこれと可換だが、属するのは N ∣ 24 のときだけで、そのとき U_N = I。符号の単数への制限が属するのは N ∣ 12 のときだけ（どちらも数値 N ≤ 36 と盲検の手計算、確信度：中〜高）。
  - P ∈ A_N となるのも N ≤ 36 では N ∣ 12 のときだけ（数値）。N ∣ 12 ⇒ P ∈ A_N は `PAG.Part225.fullComm_commute_iff_dvd_twelve`（Part 221（PAG225）：可換子が可換 ⇔ N ∣ 12。P ∈ A_N の文ではない）に二重可換子（Lean の外）を足せば出る。逆向きは数値だけ。極限では、符号は N ∣ 12 のレベルの角の上でだけ A_∞ に入る（数値：2 ≤ M ≤ 36 の約数の組 139 組。N = 1 と N = M を含み、φ(P_N) = P_M φ(1) なので実質は P_N ∈ A_N の確かめ直し）。
  - したがって A_∞ は、貼り合わせの位相（A1）にも無限素点の符号にも、導手の区分け以外の制約を課さない。位相はガウス和（H の中）と公準 A1 から入る。
  - range(D_1) ∩ range(E_1)（V_N の中）は、0 拡張した原始指標の張る空間（2.5 の V_prim を 0 拡張で同一視したもの）。J̃∘H はこれを保ち、原始指標 χ に W(χ) = τ(χ)/(i^a √N) を掛ける（2.6 の U_N の原始指標での固有値と同じ値）。数値 N ≤ 36（空間としての一致と固有値は統合照合の後の追加計算）。2.5 のユニタリ性の構造上の理由づけとして読める。
- 素朴な一般化の失敗（第 6 の型）：法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s）は、N = 10, 14, 15, … で A_N と可換でない（数値）。可換なのは J̃。
- 書き方の規則：「A_∞ と射影の変換からルート数が出る」と書かない（円環の第 2 の型、注入→回収）。
- Lean（既にあるもの。どれもこの項の文そのものではない）：
  - 単数の乗法との可換：`PAG.Part218.shellAlg_comm_dil`（Part 214（PAG218））。可換子 `PAG.Part224.fullComm`（Part 220（PAG224））、可換子が可換 ⇔ N ∣ 12：`PAG.Part225.fullComm_commute_iff_dvd_twelve`（Part 221（PAG225））。
  - フーリエ共役：`PAG.Part246.fourierConj_convL_geps`・`PAG.Part246.fourierConj_mulLeft_dind`（Part 242（PAG246））。
  - 導手ごとの部分 `PAG.Part258.condPart`（Part 254（PAG258））、原始部分 `PAG.Part257.Vprim`（Part 253（PAG257）、単数の上の関数の部分空間）、`PAG.Part256.JH_eq_rootNum_mul`（Part 252（PAG256）、U と A1 は文に出てこない）、U_N `PAG.Part258.UA1`（Part 254（PAG258））。
- Lean の外：A_N = End(V_N)^{G_N} と可換子の群による記述、J̃ とその可換性、H と J̃∘H による共役の文、0 拡張とフーリエの等式、単数の角の記述、N ∣ 24・N ∣ 12 の判定、P ∈ A_N ⇔ N ∣ 12、range(D_1) ∩ range(E_1) = V_prim、J̃∘H がこれを保つこととその固有値。
- 対照群：関数体 F_p[t]/(t^e)（p = 2 で e ≤ 4、p = 3 で e ≤ 3、p = 5 で e ≤ 2）で、R_u・J̃ の可換、F による入れ替えと正規化、単数の角の次元＝導手の数を調べ、同じ形だった（数値）。符号・0 拡張・V_prim は調べていない。判定の値（N ∣ 24 に当たるリスト）と位相の値は変わる（照合者）。ℚ の「N ∣ 24」は Gauss の符号定理と、位相に Hartley 核の 1/i^a（2.4）を含めることに依存する：素朴な核 τ/√f では、角に入るのは N = 2, 3, 4, 6, 12 で、8 と 24 が外れる（数値 N ≤ 36）。規約 T（2.8）のもとでは無限素点の局所定数は (−i)^a で、値 τ/(i^a √N) 自体はどちらの規約でも同じ。
- 文献：Bastian–Humphries（arXiv:2606.19095）、Bhattacharyya–Song（arXiv:0809.1052、wreath powers。6.1 などの Bhattacharyya–Song–Tanaka 2010 とは別の文献の可能性がある、未照合）、arXiv:2510.17118 の式 (2)（T(v) ⊆ End_{G_v}）、Martin–Tanaka の解説（arXiv:0811.2475）、Kim–Kim（arXiv:1108.4947）、Montgomery–Vaughan 第 9 章、Shirbisheh（arXiv:0808.1767）、Arledge–Laca–Raeburn（1997）。照合者の WebSearch・WebFetch による。MathSciNet・zbMATH は未実施。
- 推薦：Lean にしない。残余が空。
- ノート：`pag2_projection_interaction_preregistration.md`。数値：`records/projection_interaction/`（`interaction_check.log`、`extra_checks.log`、`sign_corner_check.log`、`control_fqt_interaction.log`）。

## 第 3 章　解像度と有効な姿（§1 の命題 3）

**3.1 定義文と、その置き方と読み。**
- 地位：
  - 定義文（著者の文面）：直線は解像度を落としたときに創発する有効な姿。解像度のパラメータは未決定。
  - 置き方（2026-11-13）：見方の選択として解釈の層に置く（著者側 Muse の決定）。
  - 08:41 の定義（2026-11-13、著者の原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」
  - 読み L1（2026-11-13 08:38 に著者が採った読み。構築側の案）：解像度は測る素点の集合。
- Lean：なし（数学の文ではない）。
- 書き方の規則（CLAUDE.md §1）：
  - 解像度を N・K・Λ と同一視しない。
  - 閉包・完備化に現れる連続体を「有効な姿」や目標として書かない。
  - 完備化（L²、ℝ、直積の位相）を使うときは、「解像度が落ちる側の操作と読む」と読みとして断る。極限は直極限の側（すべての素点を同時に測る側）で取る。
  - 「直線の創発」と書かない。命題 3 には「§1 の命題 3（解像度と有効な姿）」と参照で触れ、何がどう変わるかを数学の言葉で書く。
- ノート：`pag2_author_definition_0841.md`、`pag2_part255_resolution_discrete_limit.md`、CLAUDE.md §1。

**3.2 Part 250 の試み（ε-鎖による定式化）。**
- 地位：
  - 定式化は Claude の案 1・2 を、著者が 2026-11-11 に了承したもの（Part 250 のノートの記載。CLAUDE.md §2 は「著者が採用した案 1＋案 2」と書く。著者の定義そのものではない）。
  - 定理は［既知］（教科書の例の対数座標版）。否定的な結果を含む。
- Lean（Part 250（PAG254））：
  - 定義 `PAG.Part254.chainIn`。
  - ∞ の側は、どの ε > 0 でも任意の 2 点が鎖でつながる：`PAG.Part254.chainIn_dInf`。
  - p の側では「どの ε > 0 でもすべての 2 点がつながる」が成り立たない：`PAG.Part254.not_forall_chainIn_dP`。ε > 1 ではすべてつながる（ノートの記載）。
  - 稠密性 `PAG.Part254.dense_logSet`、等長性 `PAG.Part254.dInf_eq_dist`。
- 否定的な結果：
  - 「解像度を落とすと直線が現れる」は示せていない。ε-鎖の商は 1 点につぶれ、ℝ は完備化から現れ、しかも ℝ は定義に使われている。ε-鎖の商は Lean にしていない。
  - 08:41 の定義の後（Part 255）、完備化は「解像度が落ちる側」の操作と読み、Part 250 の照合の記録にあった向きの判断は取り下げた。
- ノート：`pag2_part250_resolution_emergence.md`、`pag2_part255_resolution_discrete_limit.md`。

## 第 4 章　解像度ごとの姿（設計についての定理 1）

**4.1 Part 255 の二分法：測る素点と、像の離散・稠密。**
- 地位：定理［既知（再導出）］。骨格は、証明の部品が S 単数定理・積公式・弱近似（既知）であることを明記するとしている。
- Lean（Part 255（PAG259））：
  - 有限の基礎 ⟨S⟩（S は素数の有限集合、T ⊆ S）での閾値：`PAG.Part259.threshold_iff`。
  - 測らない素数が 2 つ以上なら稠密：`PAG.Part259.dense_imgST_iff`。高々 1 つなら閉かつ離散：`PAG.Part259.isClosed_discrete_imgST`。
  - 位相の対比：
    - 直積の位相では、すべての素点の座標への像は稠密：`PAG.Part259.dense_rho_image`。
    - 有限素点の座標 `PAG.Part259.BoxCoord`（`Nat.Primes → ℤ`）に離散位相を入れると、像は閉かつ離散：`PAG.Part259.isClosed_discrete_rhoBox_image`（写像 `PAG.Part259.rhoBox`）。
    - 「すべての素点を同時に測る位相」は読み。log の成分は使わない。再照合 A2 の判定は「自明（位相の選び方でほぼ決まり、ほぼ同語反復に近い。確信度：高）」。
  - 対照群の自明な Lean 版：通約的な 2 つの対数の整数結合は離れる：`PAG.Part259.sep_of_commensurable`。
- 留保：
  - 守備範囲：ℚ_{>0} を基礎にすると、∞ を測るどの有限の解像度でも像は稠密になる（`PAG.Part259.dense_rho_image` から射影で直ちに出る。独立の Lean の文はない）。有限の解像度の中では、離散の側は有限の基礎 ⟨S⟩ でだけ起こる。すべての素点を離散位相で測ると、ℚ_{>0} でも像は閉かつ離散になる（`PAG.Part259.isClosed_discrete_rhoBox_image`）。
  - 二分法を 1 つの文にはしていない。直極限の位相と `BoxCoord` の同一視は Lean の外。
  - 閉包に現れる直線は、読みとしては解像度が落ちた印（08:41 の定義）。その直線が無限素点の座標であること、および対照群 𝔽_q(t) で直線が現れないこと（ノルムの像は q^ℤ）は、骨格の記述で、Lean の外。
- ノート：`pag2_part255_resolution_discrete_limit.md`。

## 第 5 章　有限レベルの代数の組み立て（設計についての定理 2）

**5.1 Part 258 の二分法：N ∣ M のとき、(i) 引き戻しと両立し、(ii) 殻を混ぜない（強い読み）単位的な代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、そのときに限る。**
- 地位：定理。
  - 存在の側（テンソル積）は［既知］（Hanaki–Kim–Maekawa の直積の定理。構築側は文献を開いていない。確信度：中〜高は Part 258 のノートの記載）。
  - 不存在の側は［新規候補（小さい）］（確信度：低〜中。2026-11-15 の著者側の判断）。
- Lean（Part 258（PAG262））：
  - 二分法：`PAG.Part262.exists_compatible_hom_iff`。
  - 存在 `PAG.Part262.exists_compatible_hom`、その写像 `PAG.Part262.shellLift`。
  - 不存在：`PAG.Part262.no_compatible_hom`。
- 留保：
  - 条件の番号に注意。殻を混ぜない条件は、PAG262 の docstring・Part 259・CLAUDE.md §2 の番号では (ii)、Part 258 のノートでは (3)。強い読み（写像の像が殻ごとの span に入る：φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）は、Part 258 のノートでは「構築者の読みで、著者に確かめる事項」とされていた。2026-11-19 07:10 に著者が、Part 258 の定理が意味する条件として確定した。根拠は、2026-11-15 に強い読みの報告を受理したこと、事前登録の問いの鋭さと候補 3 の内容がこの読みに依存すること（CLAUDE.md §3）。弱い読みは将来の問いとして排除しない。
  - 答えの範囲の外：弱い読み、単位元を保たない写像、両立条件を別の形にした写像。
  - 対照群（盲検の申告で、未確認）の結果から、アーデル射影幾何に固有の内容としては数えない（Part 258 のノート）。
  - 文献照合（MathSciNet・zbMATH と、Hanaki–Kim–Maekawa の本文）が済むまで、外部で新規性として使わない（Bastian–Humphries の本文は 2026-11-19 に構築側が WebFetch の要約を通して読んだ。下の行）。
  - 構築側で開ける範囲の文献照合（2026-11-19、`pag2_candidate3_literature_builder.md`）：Bastian–Humphries・Watanabe（arXiv:2305.19258）・Kim（arXiv:1109.1334）の本文（WebFetch の要約を通した読み）に、商に沿った単位的な写像の記述は見つからなかった（見つからなかったは不存在の証明ではない）。Hanaki–Kim–Maekawa の本文は構築側の環境から取得できず、盲検の申告のまま。MathSciNet・zbMATH は著者側の作業として残る。
- ノート：`pag2_part258_beta_premise.md`、CLAUDE.md §3。

**5.2 Part 259：フーリエとの両立を足した一意性と、帰納系の添字。**
- 地位：定理。
  - 順序の性質は［既知］（ユニタリ約数、E. Cohen 1960）。
  - 一意性・非一意性・帰納系は［再導出（小さい）］。
- Lean（Part 259（PAG263））：
  - (i)(ii)(iii)（(iii) はフーリエとの両立）を満たす写像がちょうど 1 つある ⇔ gcd(N, M/N) = 1：`PAG.Part263.existsUnique_compatF_iff`。その写像の特定：`PAG.Part263.compatF_iff_eq_shellLift`。
  - (iii) を外すと一意でない場合がある：`PAG.Part263.not_existsUnique_compat`。Lean にあるのは、A_2 → A_{2b}（b > 1 は奇数）で捩れた写像 `PAG.Part263.twLift` がある場合だけ。
  - 標準の写像 `PAG.Part263.canon` は合成と両立する：`PAG.Part263.canon_comp`。
  - 添字の関係 `PAG.Part263.UDvd` は有向でない：`PAG.Part263.not_isDirected_udvd`。`UDvd N M` は Part 216（PAG220）の `PAG.Part220.InLayer N N M` と同値（N > 0。`PAG.Part263.udvd_iff_inLayer`。`InLayer` で c = d とした特別な場合）。
  - 無平方数の部分系の極限 `PAG.Part263.sqLim`。各段は単射で入る：`PAG.Part263.sqLim_of_injective`。
- 留保（Part 259 §2 の「併記する必要がある 3 点」と、その他）：
  - 無平方数の系は、極大な有向部分系のうち指数がすべて 1 の場合にすぎず、A_{p^k}（k ≥ 2）を含まない。
  - `sqLim` は ℂ 加群で、代数の構造と制限テンソル積との同型は Lean の外。
  - どの有向な部分系も、整除の順序で共終でない。したがって関数のレベルの極限 ℂ[ℚ/ℤ]（5.3）の代数版にはならない（初等的。Lean にしていない）。
  - a が奇数のときの一意性は、数値のみ。
  - gcd ≠ 1 で (i) と D の側だけを満たす写像があるかは、未確認（小さい数値では見つからなかった。証明ではない）。
  - 非単位的な角の写像では、上の「代数版にはならない」は当てはまらない（5.5。上の文は単位元を保つ写像についての文）。
- ノート：`pag2_part259_unitary_step_maps.md`、`pag2_R1_assessment.md`。

**5.3 関数のレベルの帰納系。**
- 地位：定理（Lean）。ラベルは、この索引では確かめていない。
- Lean：
  - Part 197（PAG201）：
    - 引き戻し `PAG.Part201.pull`。
    - ハール正規化の保存 `PAG.Part201.zket_pull`（仮定：t の素因数がすべて M を割る）。
    - 法によらない定理 A `PAG.Part201.thmA_haar`（仮定：N の素因数がすべて d を割る。原始性）。
  - Part 202（PAG206）：
    - 引き戻しのフーリエ変換 `PAG.Part206.dft_pull_apply`。
    - 旧部分 = 引き戻しの像 `PAG.Part206.oldP_eq_self_iff`。
  - 単数の上の関数の帰納極限 `PAG.Part258.Lim`（2.6）。
- 留保：
  - 極限 ℂ[ℚ/ℤ] との同一視は骨格の記述で、この索引では Lean の文を確かめていない。
  - `PAG.Part201.thmA_haar` の docstring は、この文を「Ẑ 上の定理 A」と呼ぶ。CLAUDE.md §0 は「Ẑ 上の定理 A」を未完の大域の問いに挙げ、§4 は 2026-11-12 の棚卸し監査で既知の定理かその帰結と判定したと書いている。
- ノート：引き継ぎメモの項目 18・23。

**5.4 互いに素な段のテンソル積。**
- 地位：定理［既知］（直積スキームの一般定理 T(A×B) ≅ T(A)⊗T(B) の特別な場合）。
- Lean：
  - Part 228（PAG232）：`PAG.Part232.shellAlgTensorEquiv`、`PAG.Part232.leftHom`、`PAG.Part232.tensLift_injective`、`PAG.Part232.range_tensLift`。
  - Part 236（PAG240）：
    - 局所作用素 `PAG.Part240.locHom`。
    - 一般の族の文 `PAG.Part240.tensEquiv`（A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
    - 素数冪への分解 `PAG.Part240.ppEquiv`（これも A_N に当てるには `PAG.Part240.crtMul_shellAlg`）。
- 留保：Part 258 の `shellLift` の作用素は、`locHom` の k = 0 と同じ式（Lean ではつないでいない。第 12 の型）。
- ノート：引き継ぎメモの項目 49・57、CLAUDE.md §3。

**5.5 角の写像：N ∣ M のとき、φ(S) = (N/M)·π^* ∘ S ∘ π_* は A_N を A_M に送る、単位元を保つとは限らない代数準同型（Lean の型 `→ₙₐ[ℂ]`。N < M では単位元を保たず、N = M では恒等）で、合成と恒等の法則を満たす（gcd(N, M/N) によらない）。**
- 地位：定理（Part 260（PAG264）、短期層、2026-11-19）。
  - ラベル：E 側の像は［既知］（商スキームのべき等元による角）、ほかは［再導出（小さい）］。
  - 対照群は ℤ/p^e の段に当たる場合（F_p[t]/(t^e)）だけを試し、そこでは同じ文が成り立った（数値。互いに素な段は試していない）。使うのは平行移動スキームの形式だけ（盲検の手計算）なので、アーデル射影幾何に固有の内容としては数えない。
- Lean（Part 260（PAG264））：
  - A_M に入る：`PAG.Part264.cornerOp_mem`。写像 `PAG.Part264.cornerHom`。
  - 生成元の像：`PAG.Part264.cornerOp_geps`（φ(E_s) = E_{(M/N)s}）、`PAG.Part264.cornerOp_one`（φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s）、`PAG.Part264.cornerOp_dind`。
  - 引き戻しと両立：`PAG.Part264.cornerOp_pull`。
  - 一意性：`PAG.Part264.existsUnique_corner`。条件は (a) 引き戻しとの両立と (b) φ(1) の値。(b) を外すと一意でない（照合者の手計算）。
  - 合成：`PAG.Part264.cornerHom_comp`。恒等の法則：`PAG.Part264.cornerHom_self`（2026-11-19 午後に追加）。合成と恒等の 2 法則で、正の整数の整除の順序の上の帰納系の法則が揃う。
  - N < M なら φ(1) ≠ 1：`PAG.Part264.cornerHom_one_ne_one`。
  - D 側の証人：`PAG.Part264.cornerOp_dind_not_mem_span`（(2,4)）。
- 留保：
  - 次のものは Lean の外。
    - 極限の具体形（Ẑ 上の局所定数関数への作用）。
    - 像が角全体であること（数値 111 組（M ≤ 30、N = M の 30 組を含む）、三重正則性からの帰結の見込み）。
    - Bost–Connes の ρ との対応（6.3）。
  - D 側は殻の span に入らないので、5.1 の強い読みの外。これは素数冪の段に固有ではない（数値：N < M の 81 組（M ≤ 30）のすべての s ∣ N で、φ(D_s) は D_t の span に入らない）。
  - 極限は直極限（有限次元の代数の和集合）の側でとる。完備化は解像度が落ちる側の操作と読む（CLAUDE.md §1 の 08:41 の定義、索引 3.1）。
  - 照合：独立照合、再照合、統合照合（恒等の法則と尾）。統合照合の後の直しは主張を狭める・明確にするものだけで、尾の台帳は空。
- 帰納系と極限（Part 261（PAG265）、短期層、2026-11-19 午後）：
  - 正の整数の整除の順序（Part 254 の `Lvl`）の上の `DirectedSystem`：`PAG.Part265.cornerSys_self`・`PAG.Part265.cornerSys_comp`。
  - 極限 `PAG.Part265.CornerLim`（Mathlib の一般の `DirectLimit`）は、非単位的な環の構造と ℂ のスカラー倍を持つ。
  - 各段は単射に入る：`PAG.Part265.ofCorner_injective`。
  - 局所的な単位元：1 元ごとが `PAG.Part265.exists_local_unit`、有限集合ごとが `PAG.Part265.exists_local_unit_finset`。べき等元 e_a は a について増大する（`PAG.Part265.ofCorner_one_le`）。
  - 左単位元はない：`PAG.Part265.not_exists_left_one`。
  - 局所的な単位元の文は、各段が単位的で移行写像が乗法を保つ直極限ならどれでも成り立つ一般論で、非単位的という内容を運ぶのは左単位元がないことだけ。その証明は素数冪の段を要らない見込み（手計算）。
  - 極限は直極限の側でとり、完備化は使っていない。
- 極限の具体形（読み。Lean の外。2026-11-19 午後の盲検の問いテスト、`pag2_limit_form_preregistration.md`）：
  - 極限は Ẑ 上の局所定数関数の空間 V_∞ に、完備化なしに忠実に作用する（照合者の手計算）。
  - 素点ごとに、局所の単位 e_1（定数への射影）に関する制限テンソル積 ⊗'_p に分かれる（照合者の答え、確信度：高）。Flath 型の当てはめ。角の写像が中国剰余定理と両立することは数値で 1098 回確かめた。
  - 文献：Flath（1979）、Deitmar（arXiv:1002.0475）、アデールの Schwartz–Bruhat 関数、Laca–Larsen–Neshveyev（arXiv:math/0609316、定理 3.2）。
  - 否定的な観察（照合者、確信度：中）：局所の代数 A_{p^∞} は抽象的な代数としては p によらない見込みで、そうなら A_∞ に入る算術は素点が可算個あることだけ。ただし有限段の次元は p = 2 と奇素数で違う（A_{2^e} は e = 1〜4 で 4, 10, 19, 31、奇素数では e = 1〜3 で 5, 12, 22。統合照合の照合者の計算、Part 225–226 の次元公式と同じ）。無限素点・スケーリング・貼り合わせ U は A_∞ の元としてはほぼ現れない：例外と現れ方は 2.9（符号は N ∣ 12 の角の上で入る、U_N は N ∣ 24 で恒等、スケーリングはフーリエを通して φ ↔ ψ として現れる）。
  - 残余がないので、Lean にしない（推薦）。
- 無限素点・スケーリング・貼り合わせ U との相互作用（読みと否定的な結果）：2.9。
- ノート：`pag2_pag264_corner_maps.md`、`pag2_pag265_corner_limit.md`、`pag2_gamma_corner_preregistration.md`、`pag2_limit_form_preregistration.md`。

## 第 6 章　位置づけ

**6.1 殻代数 A_N は Terwilliger 代数 T(0) そのもの。**
- 地位：［既知］（2026-11-07 の著者の定義照合）。定義からの等式で、T(0) を Lean で定義していないので Lean の定理ではない。
- Lean：A_N の定義 `PAG.Part218.shellAlg`（Part 214（PAG218））。
- 既知として扱う結果：
  - 素数冪の Wedderburn 分解と次元公式：Part 225–226（PAG229–PAG230）。
  - テンソル積分解：Part 228（PAG232）。
  - ⟨D_u, E_N⟩ の構造とフーリエ共役：Part 241–242（PAG245–PAG246）、確信度：中。
- 書き方の規則：構造が要るときは再証明せず、辞書経由で文献を引く。
- ノート：`pag2_terwilliger_dictionary.md`、CLAUDE.md §3。

**6.2 新規性の候補（未確定。断定しない）。**
- 候補 1：生成の分類。
  - 範囲は Part 245〜248（PAG249〜PAG252）。項目 66 の宣言が PAG249（Part 245）にあるため、CLAUDE.md §3 の「Part 246–248」を 2026-11-19 に著者の承認で訂正した。
  - 項目 66：`PAG.Part249.sumSub_eq_shellAlg_iff`。項目 68：`PAG.Part251.addEAlg_one_eq_shellAlg_iff`。完全な分類：`PAG.Part252.addEAlg_eq_shellAlg_iff_all`。
  - 新規候補として残る範囲は合成数の N（確信度：中）。評価は「小さいノートの水準」。
  - MathSciNet・zbMATH は未実施。ノートの言葉では「著者側か専門家への照会」をお願いしている。
  - ノート：`pag2_candidate1_generation_collation.md`、CLAUDE.md §3。
- 候補 3：Part 258 の不存在の側（5.1）。骨格は、その文献照合（MathSciNet・zbMATH）を著者自身の作業としている。
- かつての候補 2（定理 2.6 の提示形）は候補から外れた（2.3）。

**6.3 Bost–Connes との接続。**
- 地位（骨格の記述）：関数のレベルでは既知。T(0) の側に届くかは、方向 γ の文献照合の結果による。γ の文献照合は著者側の作業（CLAUDE.md §2）。
- 構築側で開ける範囲の照合（2026-11-19、`pag2_gamma_literature_builder.md`）：検索 5 回の範囲で、有限レベルの Bost–Connes と T(0) を結ぶ記述は見つからなかった（本文は開いていない。確信度：低〜中）。BC の有限レベルは群環 ℚ[ℤ/nℤ] の帰納系（関数のレベル、既知）。［観察］BC の帰納系は整除のすべての段を使うが、T(0) の側で引き戻しと両立し殻を混ぜない（強い読み）単位的な写像は互いに素な段だけ（5.1・5.2）。MathSciNet・zbMATH は著者側に残る。
- 立て直しの結果（2026-11-19、Part 260（PAG264）、5.5）：BC の ρ_n（ρ_n(1) = μ_n μ_n^*）に倣った同じ式 ι S ι^†（ι は引き戻し/√(M/N)）は、群環 ℂ[ℤ/N]（平行移動）の上では ρ と一致し（数値、Lean の外）、T(0) の上では単位元を保つとは限らない代数準同型を与える（A_M に入ること・合成・一意性は Lean）。群環そのものは T(0) に含まれないので、「延びる」とは言わない。どちらの側が BC に対応するかは表示による：引き戻しの表示では平行移動の側（E 側を含む）が ρ に対応し、0 拡張の表示（γ の盲検の手計算では L²(Ẑ) の表現での μ_n）では乗法作用素の側（D 側）が対応する。二つの表示はフーリエで入れ替わる（2.9）。Terwilliger 版の角の文と、BC と T(0) を結ぶ文献は見つからなかった（確信度：低〜中）。
- CLAUDE.md §2 には、有限レベル Bost–Connes に元の BC 系が対応する、という記載がある。
- ノート：CLAUDE.md §2。

**6.4 書かないこと。**
- CLAUDE.md §6 から：
  - リーマン予想へのアプローチと書くこと（スペクトルと零点の数え上げの不一致は確定事項）。
  - 既知の結果を新規と書くこと。
  - 著者の定義を、形式化済みの内容であるかのように書くこと。
  - A1 の導出。
  - 数値確認を証明と呼ぶこと。
- CLAUDE.md §1 から（2026-11-12 の著者の指示）：「直線の創発」という表現。

## §6 開いている点（文書に「開いている」と書くもの）

- **著者の確認待ち**：なし（2026-11-19 にすべて閉じた。「貼り合わせ」は U、Part 258 の条件は強い読み）。
- **著者側の作業**（担当は骨格と CLAUDE.md §2 の記載による）：
  - 方向 γ の文献照合（6.3）。構築側で開ける範囲は 2026-11-19 に済み、MathSciNet・zbMATH が残る。
  - 候補 3 の文献照合（5.1）。MathSciNet・zbMATH と、Hanaki–Kim–Maekawa の本文（構築側の環境から取得できない）が残る。
  - 候補 1 の MathSciNet・zbMATH（6.2。ノートの言葉では「著者側か専門家への照会」）。
- **Lean の外・数値のみで残るもの**：
  - 構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}（1.2・1.3）。
  - 定理 2.6 の逆向き（2.2）。
  - A1 と定理 2.6 の両立を 1 つにした文（2.3）。
  - `Lim` の同一視と完備化 L²(Ẑ^×)（2.6）。
  - 局所定数との同定（2.7）。
  - 二分法の 1 つの文（4.1）。
  - `sqLim` の代数構造（5.2）。
  - a が奇数のときの一意性（5.2）。
  - (i) と D の側だけを満たす写像の有無（5.2）。
  - 角の写像の像が角全体であること、極限の具体形、Bost–Connes の ρ との対応（5.5・6.3）。
  - A_∞ と射影の変換・貼り合わせ・符号の相互作用の文（2.9 の「Lean の外」の行。Lean にしない推薦が採られている）。
- **定式化の問い**：
  - 解像度の操作に、L1 を超える定式化が要るか。骨格の記述では、現時点では L1 と 08:41 の定義で文書は書ける。
  - 「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルについては 2.7。

## §7 宣言名の確認の記録

- この索引に出る完全修飾名を機械的に取り出し、`PAG.PartM.name` ごとに PAGM.lean の宣言の行（`theorem`・`def`・`abbrev`・`structure`・`instance` など）を検索した。
  - スクリプトは `records/founding_index/check_names.py`、出力は `check_names.log`。
  - 第 1 版は 85 件、第 2 版は照合者の指摘で足したものを含めて 102 件で、すべて実在した。第 3 版も 102 件ですべて実在した（`udvd_iff_inLayer` が加わり、`InLayer` は引数つきの書き方になったので機械的な抜き出しから外れた。`PAG.Part220.InLayer` の実在は第 2 版で確認済み）。
  - 第 6 版（2026-11-19 夕方）は 131 件で、すべて実在した（5.5 の Part 260・261 の宣言、2.9 で新しく出た宣言と `PAG.Part256.hartley` を含む）。
- 「Part n（PAGm）」の併記がすべて m = n + 4 であることも、機械的に確かめた（第 6 版でも確かめた。番号の列挙の書き方で機械的に拾われる組は手で確かめた）。
- 照合者に渡した宣言の docstring と形式文の抜き出しには、`records/founding_index/extract_decls.py` を使った。

## §8 照合の記録

- **第 1 回の独立照合**：
  - 第 1 版（`records/founding_index/before_index_v1.md`）を照合者 1 人に渡した。渡したのは、索引の全文、宣言の docstring と形式文（85 件）、引くノートの冒頭（各 45 行）、引き継ぎメモの該当項目、CLAUDE.md の全文。
  - 入力は `input_index.md`、依頼文は `request.md`、出力は `outputs/index_check_output.md`。所要は約 11 分。
- **結論**：宣言名はすべて実在した。指摘は次のとおり。
  - 形式文より強い見出し・文：10 件。
  - 地位・決定者・出所の違い：10 件。
  - 落としていた留保：14 件。
  - 宣言の当て方：8 件。
  - 番号・参照の誤り：8 件。最も重いのは、5.1 の「条件 (iii)」で、正しくは (ii)。
- **第 2 版で直したこと**：
  - 見出しを形式文の範囲に合わせた（1.3、2.7、5.1）。3.2・4.1・5.2 は本文の箇条を形式文の範囲に合わせた（第 3 版の注：統合照合の指摘で書き分けた）。
  - 記号 W と 𝔀 の注意を §0 に加えた。
  - 3.1 の規則を CLAUDE.md の文言どおりにし、08:41 の原文を全文で載せた。
  - 宣言を足した（2.3 の A1 の位相の側、2.7 の成分の一意性、4.1 の `dense_rho_image`・`sep_of_commensurable`、5.4 の `crtMul_shellAlg`・`ppEquiv`、6.2 の項目 66・68、5.3 の `Lim`、5.2 の `InLayer`・`canon`、§0 の `Wpt`。第 3 版の注：最後の 3 件は第 2 版の記録から抜けていた）。
  - 出所を書き分けた。骨格の記述（4.1 の部品、6.3、候補 3 の担当、「文書は書ける」）は骨格と明記した。決定者と時刻も直した（1.4、3.2）。
  - 留保を足した（2.3 の実性への帰着と近い先行、2.4 の未照合、2.6 の `Lim`、2.7 の ω の正規化、4.1 の守備範囲、5.1 の範囲の外と対照群、5.2 の 3 点、6.1 は Lean の定理ではないこと）。
  - 番号の併記と参照を直した（6.1・6.2、6.3 は §2 だけ、6.4 の出所）。
- **第 2 版の照合**：第 2 版は照合後の直しを照合にかけていない。直しは照合者の直し案に沿った狭め・書き分け・出所の明記と、足した宣言（実在は機械的に確認、§7）である。足した宣言の形式文は、照合者が「§B になく未確認」としたものを構築側が読んで当てた。たとえば `rootNum_inv`・`phaseA1_inv`・`UA1_star` の形式文は PAG258 の 363〜412 行で確かめた。次の統合照合の対象に含める。

- **統合照合（2026-11-19、第 3 版）**：第 2 版の差分を、前回の統合照合の後の直し（材料ノート・文献照合ノート・CLAUDE.md・概要・引き継ぎメモ）とあわせて照合者 1 人が照らした（記録 `records/tail_audit3/`、所要 約 12 分）。宣言 102 件と Part・PAG の対応は過不足なく一致した。形式文が偽・空虚・別物になったものはなかった。
  - 索引で直したこと：2.3（反転の条件の帰着と |𝔀| = 1 の条件を分けた）、2.7（見出しを形式文の範囲に、非原始指標の文に Lean の外と断った、局所定数との一致の地位）、2.8 の 3 つ目の規則の出所、4.1 の守備範囲（離散位相で測る場合と稠密の側の根拠）、2.4（構築側の読みの地位と、照合した範囲の限定）、5.2（`udvd_iff_inLayer` で同値と書いた）、5.3（`thmA_haar` の docstring と CLAUDE.md §4 の判定の併記）、2.2 の N ≥ 3、5.4 の `crtMul_shellAlg`、2.3 の番号の対応の根拠、3.2・5.1 の出所、§8 の記録。
  - 第 3 版の直しは、限定を足す・出所を書く・記録を事実に合わせる直しで、数学の主張を強めるものはない（補足 8 の「主張を変えない直し」。照合にはかけていない）。

- **著者の決定の記録（2026-11-19 06:36、第 4 版）**：「貼り合わせの合成」の貼り合わせは U（2.4、§6 の確認待ちから外した）。Part 257 の同定の確信度は高（2.7）。CLAUDE.md §3 の候補 1 の範囲は Part 245〜248 に訂正（6.2）。CLAUDE.md に足した ω の正規化は承認（2.8 の 3 つ目の規則の出所は、著者の承認を得た CLAUDE.md §1 の記載になった）。これは著者の決定の記録で、照合にはかけていない。

- **著者の確定の記録（2026-11-19 07:10、第 5 版）**：Part 258 の殻を混ぜない条件は強い読みで確定（5.1。§6 の確認待ちから外した）。弱い (ii)・非単位的な写像・別の両立条件は、従来の記録どおり主張の外の別の問いとして残る。CLAUDE.md §3 の候補 3（日英）にも記録した。著者の決定の記録で、照合にはかけていない。

- **統合照合（2026-11-19 夕方、第 6 版）**：第 5 版（コミット deab9f3）の後に足した文（5.1 の文献照合の行、5.2・5.5・6.3・§6、2.9）と、辞書 §17〜§19、引き継ぎメモの差分を、引く Lean の宣言 28 件の docstring と形式文、関門のノート 2 本、数値のスクリプトとログとともに、照合者 1 人が照らした（記録 `records/tail_audit4/`、所要 約 20 分）。照合者は数値のスクリプト 4 本を写して再実行し、ログは同じものが出た。
  - 重い指摘：6.3 の［観察］から「引き戻しと両立し殻を混ぜない」の条件が落ちていた。2.9 で、2.4 の `JH`（単数の上の関数への写像）に Ad を当て、ℤ/N 全体の殻の反転と区別していなかった。2.9 の V_prim の等式・J∘H との一致・P ∈ A_N を、Lean の欄の宣言に支えられているように書き、「Lean の外」に入れていなかった。2.9 の対照群の行で、i^a を無限素点の因子とする読みを規約 T に帰していた（規約 T のもとでは無限素点の局所定数は (−i)^a）。版・§7・§8 を更新していなかった。引き継ぎメモの Part 番号の取り違え（Part 214（PAG218）、Part 221（PAG225））。
  - 中くらいの指摘：数値の範囲の書き広げ（F_M ι = V F_N は 28 組、V_prim はスクリプトでは次元だけ、N ∣ 24・N ∣ 12 は N ≤ 36、対照群は調べた項目と p・e の範囲だけ、「すべて一致」は数値で確かめた項目だけ）。スクリプトの数え方の欠陥（比べない N も「偽でない」に数えていた）。5.5 の対照群の言い方（「に限って成り立つ」）、極限の具体形の否定的な観察の条件「そうなら」の脱落、5.5 と 2.9 の食い違い、5.1 の文献照合の残り、6.3 の BC の対応の表示、記号 ι・V・J の衝突。
  - 直したこと：上のすべてを直した。2.9 は記号を定め、J̃（殻の反転の CRT の積）と 2.4 の J・`JH` を書き分け、主張ごとに数値の範囲と Lean の外を明記した。5.5 を 5.4 の後に移した。§0 の「ι とも書く」を外した。辞書 §17 の「*準同型」の * を外し、§17 の前書きに未記入の名前を書いた。CLAUDE.md と英語版、Part 261 のノート、引き継ぎメモの「どの直極限でも」を「各段が単位的で移行写像が乗法を保つ直極限なら」に狭めた。
  - 追加の数値（照合者の追加計算と同じ項目を、構築側でも計算した。`records/projection_interaction/extra_checks.log`）：range(D_1) ∩ range(E_1) は空間として 0 拡張した原始指標の張る空間、J̃∘H は原始指標に W(χ) を掛ける、A_N' = span{R_u} となる N と A_N' が可換になる N はどちらも {2, 3, 4, 6, 12}、素朴な核 τ/√f では角に入るのは {2, 3, 4, 6, 12}（どれも N ≤ 36）。
  - 照合の後の直しは、主張を狭める・範囲を書く・記録を事実に合わせる直しと、誤りの訂正（2.9 の対照群の行：規約 T への帰属を外し、依存先を Hartley 核の 1/i^a と書いた。新しい数値の主張を含む）。後者は補足 8 の「主張を変える直し」に当たるので、再照合にかける（下の行）。


## §D 直しの差分と索引に出る Lean の宣言（docstring と形式文。定義は本体を含む）

### PAG.Part16.normSq_gaussSum（PAG16.lean）
```lean
/-- **|τ(χ)|² = N**（χ 原始的）。法 p^c なら |τ|² = p^c。 -/
theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ stdAddChar) = N :=
```

### PAG.Part23.Compat（PAG23.lean）
```lean
/-- 貼り合わせ条件: 赤道（単数）上で F_N(y) = F_S(y⁻¹)。 -/
def Compat (F : P1F N) : Prop := ∀ y : ZMod N, IsUnit y → F.2 y = F.1 y⁻¹
```

### PAG.Part23.W（PAG23.lean）
```lean
/-- 反転 W: [x:1] ↔ [1:x]、関数では南北の入れ替え。 -/
def W (F : P1F N) : P1F N := (F.2, F.1)
```

### PAG.Part26.Pt（PAG26.lean）
```lean
/-- P¹(Z/N) の点: 南の点 [x:1]（inl x）と北の内部点 [1:y]（inr y、y 非単数）。 -/
abbrev Pt (N : ℕ) := ZMod N ⊕ {y : ZMod N // ¬ IsUnit y}
```

### PAG.Part26.Wpt（PAG26.lean）
```lean
/-- 点の反転 [x:1] ↦ [1:x]。 -/
noncomputable def Wpt : Pt N → Pt N
  | Sum.inl x => if h : IsUnit x then Sum.inl x⁻¹ else Sum.inr ⟨x, h⟩
  | Sum.inr y => Sum.inl y.1
```

### PAG.Part26.ptEquiv（PAG26.lean）
```lean
/-- **点モデル ≃ 2 チャートモデル**（線形同型）。 -/
noncomputable def ptEquiv (N : ℕ) : (Pt N → ℂ) ≃ₗ[ℂ] compatSub N where
  toFun f := ⟨toP1 f, compat_toP1 f⟩
  invFun F := ofP1 F.1
  map_add' f g := by
    apply Subtype.ext
    ext y
    · rfl
    · simp only [toP1, Pi.add_apply, Submodule.coe_add, Prod.snd_add]
      split_ifs <;> rfl
  map_smul' a f := by
    apply Subtype.ext
    ext y
    · rfl
    · simp only [toP1, Pi.smul_apply, Submodule.coe_smul, Prod.smul_snd, RingHom.id_apply]
      split_ifs <;> rfl
  left_inv f := ofP1_toP1 f
  right_inv F := Subtype.ext (toP1_ofP1 F.2)
```

### PAG.Part27.ProjLine（PAG27.lean）
```lean
/-- **射影直線** P¹(Z/N)。 -/
def ProjLine (N : ℕ) := Quotient (projSetoid N)
```

### PAG.Part27.Wproj（PAG27.lean）
```lean
/-- 反転 W[a:b] = [b:a]（well-defined）。 -/
def Wproj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)
```

### PAG.Part27.Wproj_Wproj（PAG27.lean）
```lean

theorem Wproj_Wproj (q : ProjLine N) : Wproj (Wproj q) = q :=
```

### PAG.Part27.card_ProjLine（PAG27.lean）
```lean
/-- **点の数**: |P¹(Z/p^K)| = p^K + p^(K−1)。 -/
theorem card_ProjLine : Nat.card (ProjLine (p ^ K)) = p ^ K + p ^ (K - 1) :=
```

### PAG.Part27.projEquiv（PAG27.lean）
```lean
/-- **点モデル ≃ 射影直線** Pt(p^K) ≃ P¹(Z/p^K)。 -/
noncomputable def projEquiv : Pt (p ^ K) ≃ ProjLine (p ^ K) where
  toFun := toProj K
  invFun := ofProj K hK
  left_inv := ofProj_toProj K hK
  right_inv := toProj_ofProj K hK
```

### PAG.Part173.gauss_inv_pair（PAG173.lean）
```lean
/-- **2. z(χ) · z(χ⁻¹) = χ(−1)**（χ は法 N の原始指標）。 -/
theorem gauss_inv_pair {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt N : ℝ) : ℂ)) * (gaussSum χ⁻¹ stdAddChar / ((Real.sqrt N : ℝ) : ℂ))
      = χ (-1) :=
```

### PAG.Part198.gauss_sign_real（PAG198.lean）
```lean
/-- **4. ガウスの符号決定（すべての実原始指標）**：法 N の原始指標 χ で χ² = 1 なら、
  z(χ) = τ(χ)/√N は χ(−1) = 1 で 1、χ(−1) = −1 で i。 -/
theorem gauss_sign_real (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) : zN χ = gs χ :=
```

### PAG.Part201.pull（PAG201.lean）
```lean
/-- 引き戻し π^* f = f ∘ (mod N)（N ∣ N′）。 -/
noncomputable def pull {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) : ZMod N' → ℂ :=
  f ∘ (ZMod.castHom h (ZMod N)).toAddMonoidHom
```

### PAG.Part201.thmA_haar（PAG201.lean）
```lean
/-- **4. ハール正規化の定理 A（Ẑ 上の定理 A）**：thmA_general の仮定のもとで
(1/N)·zket(A) ⋆ zket(B) = φ(uc)^(−1/2)·J̃·zket(Ψ)。定数は N によらない。 -/
theorem thmA_haar (N u M c d u' M' : ℕ) [NeZero N] [NeZero c] [NeZero d] (h : u * M = N) (hc : c ∣ M)
    (hdc : d ∣ c) (h' : u' * M' = N) (hd : d ∣ M') (hu' : u' = u * (c / d))
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ d)
    (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive) (hprod : A * B = Ψ.changeLevel hdc) :
    hconv (zket u M N h c hc A) (zket u M N h c hc B)
      = ((((Real.sqrt (Nat.totient (u * c)))⁻¹ : ℝ) : ℂ) * jt c d A B Ψ) • zket u' M' N h' d hd Ψ :=
```

### PAG.Part201.zket_pull（PAG201.lean）
```lean
/-- **3a.** t の素因数がすべて M を割るなら π^* zket_N = zket_{Nt}。 -/
theorem zket_pull (u M N t : ℕ) [NeZero N] [NeZero t] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : ZMod c → ℂ) (ht : ∀ q : ℕ, q.Prime → q ∣ t → q ∣ M) :
    pull (dvd_mul_right N t) (zket u M N h c hc χ)
      = zket u (M * t) (N * t) (by rw [← h, mul_assoc]) c (hc.trans (dvd_mul_right M t)) χ :=
```

### PAG.Part206.dft_pull_apply（PAG206.lean）
```lean
/-- **1.** 𝓕(π^*f)(ξ) = [t ∣ ξ]·t·𝓕f(ξ/t)（π : ℤ/Nt → ℤ/N）。 -/
theorem dft_pull_apply (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod N → ℂ) (ξ : ZMod (N * t)) :
    𝓕 (pull (dvd_mul_right N t) f) ξ =
      if t ∣ ξ.val then (t : ℂ) * 𝓕 f ((ξ.val / t : ℕ) : ZMod N) else 0 :=
```

### PAG.Part206.oldP_eq_self_iff（PAG206.lean）
```lean
/-- **4c. 旧部分の特徴づけ**：Pg = g ⇔ g = π^*f となる f がある。 -/
theorem oldP_eq_self_iff (N t : ℕ) [NeZero N] [NeZero t] (g : ZMod (N * t) → ℂ) :
    oldP N t g = g ↔ ∃ f : ZMod N → ℂ, pull (dvd_mul_right N t) f = g :=
```

### PAG.Part218.shellAlg（PAG218.lean）
```lean
/-- 殻の射影が生成する代数 A = ⟨E_s, D_s⟩ ⊆ End(ℂ^{ℤ/N})（E_s = ε_s ⋆、D_s = 1_{D_s}·）。 -/
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))
```

### PAG.Part218.shellAlg_comm_dil（PAG218.lean）
```lean
/-- **5a.** A の元は U_a と可換。 -/
theorem shellAlg_comm_dil (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N)
    (a : (ZMod N)ˣ) (f : ZMod N → ℂ) : T (dil a f) = dil a (T f) :=
```

### PAG.Part220.InLayer（PAG220.lean）
```lean
/-- n は d の層に入る：n = d·e（e は c と互いに素）。 -/
abbrev InLayer (c d n : ℕ) : Prop := ∃ e : ℕ, n = d * e ∧ Nat.Coprime e c
```

### PAG.Part224.fullComm（PAG224.lean）
```lean
/-- 空間全体の可換子 A′：すべての E_s = ε_s ⋆ と D_s = 1_{D_s}· と可換な線形変換。 -/
noncomputable def fullComm (N : ℕ) [NeZero N] : Submodule ℂ (Module.End ℂ (ZMod N → ℂ)) where
  carrier := {T | ∀ (s : ℕ) (f : ZMod N → ℂ),
    T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f) ∧ T (dind N s * f) = dind N s * T f}
  add_mem' := by
    intro T₁ T₂ h₁ h₂
    simp only [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.add_apply, LinearMap.add_apply, (h₁ s f).1, (h₂ s f).1, ← PAG.Part15.convL_apply,
        ← PAG.Part15.convL_apply, ← PAG.Part15.convL_apply, map_add]
    · rw [LinearMap.add_apply, LinearMap.add_apply, (h₁ s f).2, (h₂ s f).2, mul_add]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, ← PAG.Part15.convL_apply, map_zero]
    · rw [LinearMap.zero_apply, LinearMap.zero_apply, mul_zero]
  smul_mem' := by
    intro r T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    intro s f
    refine ⟨?_, ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, (hT s f).1, ← PAG.Part15.convL_apply,
        ← PAG.Part15.convL_apply, map_smul]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, (hT s f).2, mul_smul_comm]
```

### PAG.Part225.fullComm_commute_iff_dvd_twelve（PAG225.lean）
```lean
/-- **4k. A′ が可換 ⇔ N ∣ 12**（step243 の (4) で数値だけだった読み取り）。 -/
theorem fullComm_commute_iff_dvd_twelve (N : ℕ) [NeZero N] :
    (∀ T ∈ fullComm N, ∀ T' ∈ fullComm N, Commute T T') ↔ N ∣ 12 :=
```

### PAG.Part232.leftHom（PAG232.lean）
```lean
/-- L：End(ℂ^{ℤ/a}) → End(ℂ^{ℤ/a × ℤ/b})（代数準同型）。 -/
noncomputable def leftHom (a b : ℕ) : Module.End ℂ (ZMod a → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  AlgHom.ofLinearMap
    { toFun := leftOp b
      map_add' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl }
    (LinearMap.ext fun _ => funext fun _ => rfl)
    (fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl)
```

### PAG.Part232.range_tensLift（PAG232.lean）
```lean
/-- **4b.** 像 = C(A_{ab})（= L(A_a) ⊔ R(A_b)）。 -/
theorem range_tensLift {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (tensLift a b).range = (shellAlg (a * b)).map (crtConj hab).toAlgHom :=
```

### PAG.Part232.shellAlgTensorEquiv（PAG232.lean）
```lean
/-- **代数同型** A_a ⊗ A_b ≅ A_{ab}（gcd(a, b) = 1）。 -/
noncomputable def shellAlgTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    TensorProduct ℂ (shellAlg a) (shellAlg b) ≃ₐ[ℂ] shellAlg (a * b) :=
  ((AlgEquiv.ofInjective (tensLift a b) (tensLift_injective hab)).trans
    (Subalgebra.equivOfEq _ _ (range_tensLift hab))).trans
    (Subalgebra.equivMapOfInjective (shellAlg (a * b)) (crtConj hab).toAlgHom (crtConj hab).injective).symm
```

### PAG.Part232.tensLift_injective（PAG232.lean）
```lean
/-- **4d.** S ⊗ T ↦ L(S)R(T) は単射（像の次元 = 定義域の次元）。 -/
theorem tensLift_injective {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Function.Injective (tensLift a b) :=
```

### PAG.Part240.crtMul_shellAlg（PAG240.lean）
```lean
/-- **4a.** A は中国剰余定理で分かれる（Part 228）。 -/
theorem crtMul_shellAlg : CRTMul shellAlg :=
```

### PAG.Part240.locHom（PAG240.lean）
```lean
/-- 局所作用素 ι_k：End(ℂ^{ℤ/a_k}) → End(ℂ^{ℤ/N})（N = prodList l、代数の準同型）。
  ι_0(S) = C⁻¹(L(S))、ι_{k+1}(T) = C⁻¹(R(ι′_k(T)))（C は Part 228 の crtConj、ι′ は残りのリストのもの）。 -/
noncomputable def locHom : (l : List ℕ+) → CoprimeList l → (k : Fin l.length) →
    Module.End ℂ (ZMod ((l.get k : ℕ+) : ℕ) → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod (prodList l) → ℂ)
  | a :: l, h, ⟨0, _⟩ => (crtConj h.head).symm.toAlgHom.comp (leftHom (a : ℕ) (prodList l))
  | a :: l, h, ⟨k + 1, hk⟩ => (crtConj h.head).symm.toAlgHom.comp
      ((rightHom (a : ℕ) (prodList l)).comp (locHom l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
```

### PAG.Part240.ppEquiv（PAG240.lean）
```lean
/-- **代数の同型** X_N ≅ X_{q₁^{k₁}} ⊗ (X_{q₂^{k₂}} ⊗ (⋯ ⊗ ℂ))（素冪のリスト）。 -/
noncomputable def ppEquiv (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) (N : ℕ) [NeZero N] : (tensAlg X (ppList N)).carrier ≃ₐ[ℂ] X N :=
  (tensEquiv X hX (ppList N) (coprimeList_ppList N)).trans (substEquiv X (prodList_ppList N))
```

### PAG.Part240.tensEquiv（PAG240.lean）
```lean
/-- **代数の同型** 繰り返しのテンソル積 ≅ X_N（N = prodList l。2 因子の同型（Part 229 の crtTensorEquiv）を繰り返す）。 -/
noncomputable def tensEquiv (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) : ∀ (l : List ℕ+) (_ : CoprimeList l), (tensAlg X l).carrier ≃ₐ[ℂ] X (prodList l)
  | [], _ => (Algebra.botEquiv ℂ (Module.End ℂ (ZMod 1 → ℂ))).symm.trans
      (Subalgebra.equivOfEq _ _ (eq_bot_of_one (X 1)).symm)
  | a :: l, h => (Algebra.TensorProduct.congr AlgEquiv.refl (tensEquiv X hX l h.tail)).trans
      (crtTensorEquiv h.head (X (a : ℕ)) (X (prodList l)) (X ((a : ℕ) * prodList l))
        (hX (a : ℕ) (prodList l) h.head))
```

### PAG.Part246.fourierConj_convL_geps（PAG246.lean）
```lean
/-- **5b.** 𝓕 E_s 𝓕⁻¹ = D_s。 -/
theorem fourierConj_convL_geps (N s : ℕ) [NeZero N] :
    fourierConj N (PAG.Part15.convL (geps N s)) = LinearMap.mulLeft ℂ (dind N s) :=
```

### PAG.Part246.fourierConj_mulLeft_dind（PAG246.lean）
```lean
/-- **5c.** 𝓕 D_s 𝓕⁻¹ = E_s。 -/
theorem fourierConj_mulLeft_dind (N s : ℕ) [NeZero N] :
    fourierConj N (LinearMap.mulLeft ℂ (dind N s)) = PAG.Part15.convL (geps N s) :=
```

### PAG.Part249.sumSub_eq_shellAlg_iff（PAG249.lean）
```lean
/-- **4b. ⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N ⇔ N = 1 ∨ N = 8 ∨ N = p ∨ N = p²（p は素数）。** -/
theorem sumSub_eq_shellAlg_iff (N : ℕ) [NeZero N] :
    sumSub N = Subalgebra.toSubmodule (shellAlg N) ↔
      N = 1 ∨ N = 8 ∨ ∃ p : ℕ, p.Prime ∧ (N = p ∨ N = p ^ 2) :=
```

### PAG.Part251.addEAlg_one_eq_shellAlg_iff（PAG251.lean）
```lean
/-- **7c.** B_1 = A_N ⇔ N は平方因子なし ∨ N = 8 ∨ N = p²（p は素数）。 -/
theorem addEAlg_one_eq_shellAlg_iff (N : ℕ) [NeZero N] :
    addEAlg N 1 = shellAlg N ↔ Squarefree N ∨ N = 8 ∨ ∃ p, p.Prime ∧ N = p * p :=
```

### PAG.Part252.addEAlg_eq_shellAlg_iff_all（PAG252.lean）
```lean
/-- **4c.** 主定理（除外なし）：s ∈ S′ なら B_s = A_N ⇔ |S′| ≤ 2 ∨ (N が平方因子なし ∧ (s = 1 ∨ s = 2))。 -/
theorem addEAlg_eq_shellAlg_iff_all {N s : ℕ} [NeZero N] (hs : s ∈ devSet N) :
    addEAlg N s = shellAlg N ↔ (devSet N).card ≤ 2 ∨ (Squarefree N ∧ (s = 1 ∨ s = 2)) :=
```

### PAG.Part253.commute_transl_of_prime（PAG253.lean）
```lean
/-- **2d. 定理 2.6 の前提（有限レベル）**：N と互いに素なすべての素数 p について T_{k_p} と可換なら、
(ℤ/N)^× のすべての平行移動と可換。モノグラフの証明は Dirichlet の算術級数定理で {k_p} の稠密性を使ったが、
素数の類が生成することで足りる。 -/
theorem commute_transl_of_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (g : (ZMod N)ˣ) : U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U :=
```

### PAG.Part253.eigenFun_of_commute_prime（PAG253.lean）
```lean
/-- **2f.** 指標ごとのスカラーを 1 つの関数 c にまとめた形（中身は 2e と同じ）。後半の含意「|c| = 1 と
c(χ⁻¹) = conj c(χ) なら実指標で c = ±1」は U によらず、どんな関数 c でも成り立つ（Part 1 の `real_sector_sign`）。
2026-11-11 に `thm26_prime` から改名した（独立照合で、名前が内容より強いと指摘された）。定理 2.6 (a)⇒(b) の
有限レベル版として中身のある文は §6 の `thm26_full`。 -/
theorem eigenFun_of_commute_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧
      ((∀ χ, ‖c χ‖ = 1) → (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) → ∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1) :=
```

### PAG.Part253.exists_cls_near（PAG253.lean）
```lean
/-- **3a. 稠密性**：(ℤ/N)^× × ℝ の任意の点 (a, t) と ε > 0 に対し、正の有理数 m/n（m, n は N と互いに素）の類
(k_m·k_n⁻¹, log n − log m)（素数イデールの積 ∏ π_p^{v_p(m/n)} の類）で、単数部分が a、対数座標が t の ε 以内のものがある。
m = 1 + Nj、n = a₀ + N⌊e^t·m/N⌋（a₀ = a の代表 + N）と取り、|n/m − e^t| < 2N/m と log の連続性を使う。 -/
theorem exists_cls_near {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime N) (hn : n.Coprime N), 0 < m ∧ 0 < n ∧
      kUnit m hm * (kUnit n hn)⁻¹ = a ∧ |Real.log n - Real.log m - t| < ε :=
```

### PAG.Part253.thm26_full（PAG253.lean）
```lean
/-- **6f. 定理 2.6 (a)⇒(b)（有限レベル、素数版、完全な形）**：U が N と互いに素なすべての素数 p の平行移動 T_{k_p} と
可換で、標準のエルミート形について等長（ユニタリ）で、JUJ が U の随伴（JUJ = U*）なら、各指標 χ に U χ = c(χ)·χ、
|c(χ)| = 1、c(χ⁻¹) = conj c(χ)（(ℤ/N)^× の上では χ̄ = χ⁻¹ なので α_χ̄ = −α_χ）、実指標では c = ±1。 -/
theorem thm26_full {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g)
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1) ∧
      (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) ∧ (∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1) :=
```

### PAG.Part253.thm26_needs_commute（PAG253.lean）
```lean
/-- **7d. 仮定の除去：素数の平行移動との可換性は外せない**（N ≥ 3）。U = M_s は等長で JUJ = U* も満たすが、
指標ごとのスカラー c は取れない（自明な指標 1 が、定数でない s に写る）。2026-11-10 の独立照合で、
6f の 3 つの仮定のうち可換性を外した例がないと指摘された。 -/
theorem thm26_needs_commute {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    (∀ f g : (ZMod N)ˣ → ℂ, ipG (signMul f) (signMul g) = ipG f g) ∧
    (∀ f g : (ZMod N)ˣ → ℂ, ipG (PAG.rev (signMul (PAG.rev f))) g = ipG f (signMul g)) ∧
    ¬ ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, ∀ χ, signMul (PAG.charFun χ) = c χ • PAG.charFun χ :=
```

### PAG.Part254.chainIn（PAG254.lean）
```lean
/-- S の中の、d で測った歩幅が ε 未満の鎖で x と y がつながる。 -/
def chainIn {α : Type*} (S : Set α) (d : α → α → ℝ) (ε : ℝ) (x y : α) : Prop :=
  ∃ (n : ℕ) (c : ℕ → α), c 0 = x ∧ c n = y ∧ (∀ i, i ≤ n → c i ∈ S) ∧ ∀ i, i < n → d (c i) (c (i + 1)) < ε
```

### PAG.Part254.chainIn_dInf（PAG254.lean）
```lean
/-- **3b. 無限素点の側は well-chained**：どの ε > 0 でも、正の有理数の任意の 2 点は d_∞ の歩幅 ε 未満の鎖でつながる
（q と r を結ぶ線分の等分点を通る）。 -/
theorem chainIn_dInf {ε : ℝ} (hε : 0 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat dInf ε q r :=
```

### PAG.Part254.dInf_eq_dist（PAG254.lean）
```lean
/-- **6a.** d_∞ は log による ℝ の距離の引き戻し：d_∞(q, r) = dist(log q, log r)。1e と合わせると、
(正の有理数, d_∞) は ℝ の稠密な部分集合と等長（完備化が ℝ であること自体は Lean にしていない）。 -/
theorem dInf_eq_dist (q r : ℚ) : dInf q r = dist (Real.log q) (Real.log r) :=
```

### PAG.Part254.dense_logSet（PAG254.lean）
```lean
/-- **1e.** logSet は ℝ の中で稠密。 -/
theorem dense_logSet : Dense logSet :=
```

### PAG.Part254.not_forall_chainIn_dP（PAG254.lean）
```lean
/-- **6d. 2 つの側を分ける基準**：素数 p では、「どの ε > 0 でもすべての 2 点が d_p の鎖でつながる」は成り立たない
（d_∞ では成り立つ：3b）。 -/
theorem not_forall_chainIn_dP (p : ℕ) (hp : p.Prime) :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ q r : ℚ, 0 < q → 0 < r → chainIn posRat (dP p) ε q r :=
```

### PAG.Part255.dense_closure_allPrimes（PAG255.lean）
```lean
/-- **3d. 射影極限での稠密性**：すべての素数の類 (κ_p, −log p) が生成する unitSys × ℝ の部分群は稠密。 -/
theorem dense_closure_allPrimes :
    Dense ((Subgroup.closure (primeGens 1) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ)) :=
```

### PAG.Part255.dense_closure_primeGens（PAG255.lean）
```lean
/-- **3c. 射影極限での稠密性（有限個の素数を除いた形）**：L ≥ 1 を割らない素数の類 (κ_p, −log p) が生成する
unitSys × ℝ の部分群は稠密。 -/
theorem dense_closure_primeGens (L : ℕ+) :
    Dense ((Subgroup.closure (primeGens L) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ)) :=
```

### PAG.Part255.primeSys_unique（PAG255.lean）
```lean
/-- **2d. κ_p の一意性**：両立する系 a が、p ∤ N のすべてのレベルで p⁻¹ に等しく、p の冪のレベルに落とすと 1 なら、a = κ_p。
2a・2c と合わせて、κ_p は「p 成分が 1、ほかの成分が p⁻¹」で決まるただ 1 つの元。 -/
theorem primeSys_unique (p : ℕ) (hp : p.Prime) (a : unitSys)
    (h1 : ∀ (N : ℕ+) (hpN : p.Coprime N), (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = kUnit p hpN)
    (h2 : ∀ (N : ℕ+) (k : ℕ) (h : p ^ k ∣ (N : ℕ)),
      ZMod.unitsMap h ((a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N) = 1) :
    a = primeSys p hp :=
```

### PAG.Part255.unitSys（PAG255.lean）
```lean
/-- 射影極限：レベル N ≥ 1 ごとの単数の、自然な写像で両立する系の全体。 -/
def unitSys : Subgroup (∀ N : ℕ+, (ZMod (N : ℕ))ˣ) where
  carrier := {a | ∀ (N M : ℕ+) (h : (N : ℕ) ∣ (M : ℕ)), ZMod.unitsMap h (a M) = a N}
  mul_mem' := by
    intro a b ha hb N M h
    rw [Pi.mul_apply, map_mul, ha N M h, hb N M h, Pi.mul_apply]
  one_mem' := by
    intro N M h
    rw [Pi.one_apply, map_one, Pi.one_apply]
  inv_mem' := by
    intro a ha N M h
    rw [Pi.inv_apply, map_inv, ha N M h, Pi.inv_apply]
```

### PAG.Part256.JH（PAG256.lean）
```lean
/-- 単数の上の関数への J∘H_N/√N：(J H_N f)(u)/√N = (H_N f)(u⁻¹)/√N。 -/
noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)
```

### PAG.Part256.JH_eq_rootNum_mul（PAG256.lean）
```lean
/-- χ が原始的なら、すべての単数 u で (H_N χ)(u⁻¹)/√N = W(χ)·χ(u)。式そのものは原始性なしで成り立つ
（`JH_eq_rootNum_mul_any`）。構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。
U と A1 は文に出てこない）。JH は ℤ/N の上の関数を単数の上の関数に送る写像で、同じ空間の上の固有値方程式ではない。 -/
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u :=
```

### PAG.Part256.JH_eq_rootNum_mul_any（PAG256.lean）
```lean
/-- **単数の上の固有値の式（すべての指標）**：(J H_N χ)(u)/√N = W(χ)·χ(u)。W(χ) = rootNum χ = ε(χ)τ(χ)/√N。
原始指標では W(χ) はルート数で |W(χ)| = 1（`normSq_rootNum`）。 -/
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u :=
```

### PAG.Part256.hartley（PAG256.lean）
```lean
/-- 離散 Hartley 変換 (H_N f)(y) = Σ_x f(x)·cas(2π xy/N)。 -/
noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)
```

### PAG.Part256.hartley_eq_zero_of_not_isUnit（PAG256.lean）
```lean
/-- **単数でないところで H_N χ = 0**（χ 原始的）。 -/
theorem hartley_eq_zero_of_not_isUnit {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : hartley (χ : ZMod N → ℂ) y = 0 :=
```

### PAG.Part256.normSq_rootNum（PAG256.lean）
```lean
/-- |W(χ)|² = 1（χ 原始的。Part 12（PAG16）の |τ(χ)|² = N から）。 -/
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1 :=
```

### PAG.Part256.parFac（PAG256.lean）
```lean
/-- パリティ因子 ε(χ) = ((1 − i) + (1 + i)χ(−1))/2。 -/
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2
```

### PAG.Part256.removal_counterexample（PAG256.lean）
```lean
/-- 除去テストの反例：原始性を外すと「単数でないところで 0」が破れる（法 2 の自明な指標、y = 0）。 -/
theorem removal_counterexample :
    ¬(1 : DirichletCharacter ℂ 2).IsPrimitive ∧ ¬IsUnit (0 : ZMod 2) ∧
      hartley ((1 : DirichletCharacter ℂ 2) : ZMod 2 → ℂ) 0 = 1 :=
```

### PAG.Part256.removal_counterexample_four（PAG256.lean）
```lean
/-- 除去テストの反例（原始指標がある法 4 で。独立照合 B の指摘を受けて追加）：法 4 には原始指標があるが
（Part 140 の `exists_primitive`）、自明な指標（原始的でない）では、単数でない 2 で H_N χ (2) = −2 ≠ 0、
|W|² = 0（τ = i − i = 0）。法 2 の反例と違い、原始指標のある法でも原始性を外すと 2 つの文が破れることを示す。 -/
theorem removal_counterexample_four :
    (∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive) ∧
    ¬(1 : DirichletCharacter ℂ 4).IsPrimitive ∧ ¬IsUnit (2 : ZMod 4) ∧
      hartley ((1 : DirichletCharacter ℂ 4) : ZMod 4 → ℂ) 2 = -2 ∧
      Complex.normSq (rootNum (1 : DirichletCharacter ℂ 4)) = 0 :=
```

### PAG.Part256.removal_counterexample_normSq（PAG256.lean）
```lean
/-- 法 2 の自明な指標で |rootNum|² = 1/2。原始的でないことは `removal_counterexample` の第 1 成分で、2 つを合わせて
|W| = 1 の除去テストの反例になる。 -/
theorem removal_counterexample_normSq :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ 2)) = 1 / 2 :=
```

### PAG.Part256.rootNum（PAG256.lean）
```lean
/-- W(χ) = τ(χ)/(i^a √N)（a = 0 は偶、a = 1 は奇）。χ が原始ならルート数（関数等式との一致は Lean の外）。原始的でない
χ ではルート数ではなく、0 にもなる（法 4 の自明な指標）。
内部照合（2026-11-14）：Part 192（PAG196）の `zN` を Part 194（PAG198）の `gs` で割ったものと同じ値（Lean で確認）。 -/
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))
```

### PAG.Part257.TopL_charU（PAG257.lean）
```lean
/-- **1.** すべての指標で T χ = W(χ)χ（Part 252 の `JH_eq_rootNum_mul_any` の作用素の形）。 -/
theorem TopL_charU (χ : DirichletCharacter ℂ N) : TopL (charU χ) = rootNum χ • charU χ :=
```

### PAG.Part257.TopL_eq_of_A1（PAG257.lean）
```lean
/-- **5.** 原始指標で U χ = W(χ)χ を満たす（A1 の位相を原始部分に課した）任意の線形写像 U は、V_prim の上で
T に等しい。A1 の読み替えで、A1 を外すと結論は消える。 -/
theorem TopL_eq_of_A1 (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → U (charU χ) = rootNum χ • charU χ)
    {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : U f = TopL f :=
```

### PAG.Part257.Vprim（PAG257.lean）
```lean
/-- 原始部分 V_prim：原始指標（を単数に制限したもの）が張る空間。 -/
noncomputable def Vprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.IsPrimitive} => charU χ.1)
```

### PAG.Part257.unitary_Vprim（PAG257.lean）
```lean
/-- **9a.** V_prim の上で T はユニタリ：V_prim の自己線形同型 e で、値は T、内積を保つものがある
（`TopL_mem_Vprim`・`map_TopL_Vprim`・`ip_TopL_of_mem_Vprim`・`eq_zero_of_ip_self` を 1 つの文に）。 -/
theorem unitary_Vprim : ∃ e : Vprim N ≃ₗ[ℂ] Vprim N,
    (∀ f : Vprim N, ((e f : Vprim N) : (ZMod N)ˣ → ℂ) = TopL (f : (ZMod N)ˣ → ℂ)) ∧
    ∀ f g : Vprim N, ip ((e f : Vprim N) : (ZMod N)ˣ → ℂ) ((e g : Vprim N) : (ZMod N)ˣ → ℂ) =
      ip (f : (ZMod N)ˣ → ℂ) (g : (ZMod N)ˣ → ℂ) :=
```

### PAG.Part258.Lim（PAG258.lean）
```lean
/-- 帰納極限 lim_N (単数の上の関数)。 -/
abbrev Lim : Type := Module.DirectLimit Gsp pullSys
```

### PAG.Part258.UA1（PAG258.lean）
```lean
/-- 法 N の A1 の境界ユニタリ U_N = Σ_χ phaseA1(χ)·P_χ。 -/
noncomputable def UA1 : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := ∑ χ : DirichletCharacter ℂ N,
    (phaseA1 χ * ip (charU χ) f / (Nat.totient N : ℂ)) • charU χ
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_add_right, mul_add, add_div, add_smul]
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_smul_right, smul_smul]
    congr 1
    ring
```

### PAG.Part258.UA1_family_unique（PAG258.lean）
```lean
/-- **両立する族の一意性**（独立照合 A の指摘で追加）：各法で原始部分の上では T と一致し、引き戻しと両立する
作用素の族は U_N だけ。原始的でない指標の上の位相は、両立から決まる（仮定に A1 の位相は原始部分にしか入らない）。 -/
theorem UA1_family_unique (U : ∀ a : Lvl, Gsp a →ₗ[ℂ] Gsp a)
    (hT : ∀ (a : Lvl) (f : Gsp a), f ∈ Vprim a.val → U a f = TopL f)
    (hc : ∀ (a b : Lvl) (h : a ≤ b) (f : Gsp a), U b (pullSys a b h f) = pullSys a b h (U a f))
    (a : Lvl) : U a = UA1 :=
```

### PAG.Part258.UA1_star（PAG258.lean）
```lean
/-- **実数性**：U_N は複素共役と可換（U_N の核は実数値。KUK = U）。 -/
theorem UA1_star (f : (ZMod N)ˣ → ℂ) :
    UA1 (fun u => (starRingEnd ℂ) (f u)) = fun u => (starRingEnd ℂ) (UA1 f u) :=
```

### PAG.Part258.Uinf（PAG258.lean）
```lean
/-- 極限の作用素 U_∞：各法の U_N が引き戻しと両立することから。 -/
noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)
```

### PAG.Part258.Uinf_unique（PAG258.lean）
```lean
/-- U_∞ は各法で U_N となる線形写像として一意。 -/
theorem Uinf_unique (V : Lim →ₗ[ℂ] Lim) (hV : ∀ a (f : Gsp a), V (ofL a f) = ofL a (UA1 f)) :
    V = Uinf :=
```

### PAG.Part258.condPart（PAG258.lean）
```lean
/-- 導手が q の指標が張る部分（法 N）。 -/
noncomputable def condPart (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => charU χ.1)
```

### PAG.Part258.condPart_eq_map（PAG258.lean）
```lean
/-- 導手が q の指標が張る部分は π_{q→M}(V_prim(q))（q ∣ M）。 -/
theorem condPart_eq_map {M : ℕ} [NeZero M] (hNM : N ∣ M) :
    condPart M N = (Vprim N).map (pullL hNM) :=
```

### PAG.Part258.ipLim_Uinf（PAG258.lean）
```lean
/-- U_∞ は極限の内積を保つ。 -/
theorem ipLim_Uinf (z w : Lim) : ipLim (Uinf z) (Uinf w) = ipLim z w :=
```

### PAG.Part258.ip_UA1（PAG258.lean）
```lean
/-- U_N は ⟨·,·⟩ を保つ（単数の上の関数の空間全体でユニタリ）。 -/
theorem ip_UA1 (f g : (ZMod N)ˣ → ℂ) : ip (UA1 f) (UA1 g) = ip f g :=
```

### PAG.Part258.normSq_phaseA1（PAG258.lean）
```lean
/-- |phaseA1 χ|² = 1（χ* は原始的）。 -/
theorem normSq_phaseA1 (χ : DirichletCharacter ℂ N) : Complex.normSq (phaseA1 χ) = 1 :=
```

### PAG.Part258.phaseA1（PAG258.lean）
```lean
/-- A1 の位相 phaseA1(χ) = W(χ*)（χ* は χ を誘導する原始指標）。 -/
noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter
```

### PAG.Part258.phaseA1_inv（PAG258.lean）
```lean
/-- phaseA1(χ⁻¹) = conj phaseA1(χ)。 -/
theorem phaseA1_inv (χ : DirichletCharacter ℂ N) :
    phaseA1 χ⁻¹ = (starRingEnd ℂ) (phaseA1 χ) :=
```

### PAG.Part258.rootNum_inv（PAG258.lean）
```lean
/-- W(χ⁻¹) = conj W(χ)（すべての指標で）。 -/
theorem rootNum_inv (χ : DirichletCharacter ℂ N) :
    rootNum χ⁻¹ = (starRingEnd ℂ) (rootNum χ) :=
```

### PAG.Part259.BoxCoord（PAG259.lean）
```lean
/-- 有限素点の座標の組（`Nat.Primes → ℤ`）に離散位相を入れた型（読みでは、すべての素点を同時に測る位相）。
`Nat.Primes → ℤ` の直積の位相（各近傍は有限個の素点しか測らない）と、集合としては同じで位相だけが違う。ℤ 値の座標では
離散位相は箱・一様の位相と同じ、は Lean の外の標準の事実。 -/
def BoxCoord : Type := Nat.Primes → ℤ
```

### PAG.Part259.dense_imgST_iff（PAG259.lean）
```lean
/-- **閾値の二分法（片側）**：S が素数の有限集合で T ⊆ S のとき、像 `imgST S T` が ℝ × ℤ^T で稠密 ⇔ T の外に S の異なる
素数が 2 つある（T ⊆ S は必要：S = {2, 3}、T = {5} では右辺は真で左辺は偽）。 -/
theorem dense_imgST_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    Dense (imgST S T) ↔ ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T :=
```

### PAG.Part259.dense_rho_image（PAG259.lean）
```lean
/-- **直積の位相では、像は稠密**：ℝ × (素数 → ℤ) のどの点 (x, k) の近傍（∞ の座標の ε 近傍と、有限個の素数の座標の
指定）にも、正の有理数の像がある。各近傍は有限個の素点しか見ない。これを著者の言葉の「完備化（極限）」にあたると読むのは読み。 -/
theorem dense_rho_image : Dense (rho '' {q : ℚ | 0 < q}) :=
```

### PAG.Part259.eq_of_padicValRat_eq（PAG259.lean）
```lean
/-- **1b. 全解像度の単射**（素因数分解の一意性）：すべての素数で付値が一致する正の有理数は等しい。 -/
theorem eq_of_padicValRat_eq {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = padicValRat p r) : q = r :=
```

### PAG.Part259.isClosed_discrete_imgST（PAG259.lean）
```lean
/-- **閾値の二分法（もう片側）**：T の外に S の異なる素数が 2 つないとき（測らない素数が高々 1 つ）、像 `imgST S T` は
ℝ × ℤ^T の中で閉かつ離散。 -/
theorem isClosed_discrete_imgST (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    IsClosed (imgST S T) ∧ DiscreteTopology (imgST S T) :=
```

### PAG.Part259.isClosed_discrete_rhoBox_image（PAG259.lean）
```lean
/-- **有限素点の座標に離散位相を入れると、像は閉かつ離散**（独立照合 B の指摘で追加）。素因数分解の一意性を離散位相で
言い直した文で、log の成分は使わない。同じ集合が直積の位相では稠密（`dense_rho_image`）で、離散になるかどうかは
有限台ではなく位相の選び方で決まる（`rho_one_mem_closure_ne_one` の近似点も正の有理数なので有限台）。 -/
theorem isClosed_discrete_rhoBox_image :
    IsClosed (rhoBox '' {q : ℚ | 0 < q}) ∧ DiscreteTopology (rhoBox '' {q : ℚ | 0 < q}) :=
```

### PAG.Part259.log_eq_sum_of_support（PAG259.lean）
```lean
/-- **1e. 積公式**：⟨S⟩ の元では log q = Σ_{s∈S} v_s(q)·log s（全解像度では ∞ の座標は有限素点の座標から決まる）。 -/
theorem log_eq_sum_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    Real.log q = ∑ s ∈ S, (padicValRat s q : ℝ) * Real.log s :=
```

### PAG.Part259.rhoBox（PAG259.lean）
```lean
/-- ρ と同じ写像を、値域の有限素点の座標に離散位相（すべての素点を同時に測る）を入れて考える。 -/
noncomputable def rhoBox (q : ℚ) : ℝ × BoxCoord := (Real.log q, fun p => padicValRat p q)
```

### PAG.Part259.sep_of_commensurable（PAG259.lean）
```lean
/-- 対照群のまとめ：通約的な 2 つの対数の整数結合は、異なれば L₁/n 以上離れる（連続体は現れない）。 -/
theorem sep_of_commensurable {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b a' b' : ℤ)
    (hne : (a : ℝ) * L₁ + b * L₂ ≠ a' * L₁ + b' * L₂) :
    L₁ / n ≤ |((a : ℝ) * L₁ + b * L₂) - (a' * L₁ + b' * L₂)| :=
```

### PAG.Part259.threshold_iff（PAG259.lean）
```lean
/-- **閾値の定理**（基礎 ⟨S⟩、T ⊆ S、∞ と T の素数を測る）：像の閉包がある水平な直線 ℝ × {k} 全体を含む
⇔ T の外に S の異なる素数が 2 つある（測らない素数が 2 つ以上）。 -/
theorem threshold_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    (∃ k : T → ℤ, ∀ x : ℝ, (x, k) ∈ closure (imgST S T)) ↔
      ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T :=
```

### PAG.Part260.crossSign（PAG260.lean）
```lean
/-- 偶奇の符号 s：χ₁, χ₂ がともに奇なら −1、それ以外は +1（交差項 χ₁(N)·χ₂(M) とは別の因子）。
内部照合（2026-11-14）：Part 194（PAG198）の `rs` と同じ値（式は違う。χ(−1) = ±1 による。Lean で確認）。 -/
noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1
```

### PAG.Part260.parFac_prodChar（PAG260.lean）
```lean
/-- 偶奇の因子のずれ：ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)（ε = parFac は偶で 1、奇で −i）。ε が無限素点の局所因子にあたる、は読み。 -/
theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.parFac (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * PAG.Part256.parFac χ₁ * PAG.Part256.parFac χ₂ :=
```

### PAG.Part260.rootNum_prodChar（PAG260.lean）
```lean
/-- **交差項の法則**：互いに素な法で W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)。原始性は要らない（W がルート数なのは原始のとき）。
内部照合（2026-11-14）：中身は Part 189（PAG193）の `z_mul_coprime`・`gaussSum_mul_coprime`（後者はこの Part の `gaussSum_prodChar` と同じ文）に、偶奇の因子のずれ（Part 194 の `gs_combine` と同じ形）を足したもの（照合者の判定は D で C との境目。Lean ではつないでいない）。 -/
theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) :=
```

### PAG.Part261.exists_listChar（PAG261.lean）
```lean
/-- **分解の存在**：法 lvl l（互いに素な法の積）の指標は、どれも成分の積 listChar χ l の形に書ける（Part 190 の `decomp` を使う）。 -/
theorem exists_listChar (l : List ι) (hnd : l.Nodup)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (Ψ : DirichletCharacter ℂ (lvl N l)) :
    ∃ χ : ∀ i, DirichletCharacter ℂ (N i), listChar χ l = Ψ :=
```

### PAG.Part261.gaussSum_primeFactors（PAG261.lean）
```lean
/-- **すべての素数への分解**：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)} の成分 χ_p の積で（自然数での値が ∏ χ_p）、
τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（形 (II)）。 -/
theorem gaussSum_primeFactors (n : ℕ) [NeZero n] (Ψ : DirichletCharacter ℂ n) :
    ∃ χ : ∀ p, DirichletCharacter ℂ (p ^ n.factorization p),
      (∀ x : ℕ, Ψ x = (n.primeFactors.toList.map fun p => χ p (x : ZMod (p ^ n.factorization p))).prod) ∧
      gaussSum Ψ stdAddChar = (n.primeFactors.toList.map fun p => gaussSum (χ p) stdAddChar *
        ((n.primeFactors.toList.erase p).map fun q => χ q ((p ^ n.factorization p : ℕ) : ZMod (q ^ n.factorization q))).prod).prod :=
```

### PAG.Part261.listChar_injective（PAG261.lean）
```lean
/-- **分解の一意性**：listChar χ l = listChar χ' l なら、l の各成分で χ_i = χ'_i（Part 232 の `charMul_injective` を使う）。 -/
theorem listChar_injective (l : List ι) (hl : l.Pairwise fun i j => (N i).Coprime (N j))
    {χ χ' : ∀ i, DirichletCharacter ℂ (N i)} (h : listChar χ l = listChar χ' l) :
    ∀ i ∈ l, χ i = χ' i :=
```

### PAG.Part261.parFac_listChar（PAG261.lean）
```lean
/-- **∞ の因子の符号**：ε_∞(χ) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数。Part 256 の s の一般化）。 -/
theorem parFac_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    PAG.Part256.parFac (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) *
        (l.map fun i => PAG.Part256.parFac (χ i)).prod :=
```

### PAG.Part261.rootNum_listChar_formII（PAG261.lean）
```lean
/-- **W の分解（形 (II)）**：W(χ) = ε_∞(χ)·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)。 -/
theorem rootNum_listChar_formII (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hnd : l.Nodup) :
    PAG.Part256.rootNum (listChar χ l) = PAG.Part256.parFac (listChar χ l) *
      (l.map fun i => gaussSum (χ i) stdAddChar / ((Real.sqrt (N i) : ℝ) : ℂ) *
        ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod).prod :=
```

### PAG.Part262.exists_compatible_hom（PAG262.lean）
```lean
/-- **存在（互いに素な段）**：gcd(a, b) = 1 なら、代数準同型 φ : A_a → A_{ab} で、
(i) すべての S で φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合、を満たすものがある。 -/
theorem exists_compatible_hom (hab : a.Coprime b) :
    ∃ φ : shellAlg a →ₐ[ℂ] shellAlg (a * b),
      (∀ (S : shellAlg a) (f : ZMod a → ℂ),
        (φ S : Module.End ℂ (ZMod (a * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right a b) f) =
          PAG.Part201.pull (dvd_mul_right a b) ((S : Module.End ℂ (ZMod a → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind (a * b) t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps (a * b) t))) :=
```

### PAG.Part262.exists_compatible_hom_iff（PAG262.lean）
```lean
/-- **二分法**：N ∣ M のとき、(i)(ii) を満たす代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、かつそのときに限る。 -/
theorem exists_compatible_hom_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) :
    (∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)))) ↔
    Nat.Coprime N (M / N) :=
```

### PAG.Part262.no_compatible_hom（PAG262.lean）
```lean
/-- **不存在（gcd(N, M/N) > 1 の段）**：素数 p が N と M/N の両方を割るなら、代数準同型 φ : A_N → A_M で、
(i) すべての S で φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合、を満たすものはない。
証明に使うのは s = N の D_N・E_N と、A_N の関係 D_N E_N D_N = (1/N) D_N、E_N² = E_N だけ。 -/
theorem no_compatible_hom {N M p : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (hp : p.Prime) (hpN : p ∣ N)
    (hpk : p ∣ M / N) :
    ¬ ∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) :=
```

### PAG.Part262.shellLift（PAG262.lean）
```lean
/-- 互いに素な a, b で、A_a → A_{ab}、S ↦ Θ(S ⊗ 1)（Θ は Part 228 の `shellAlgTensorEquiv`）。 -/
noncomputable def shellLift (hab : a.Coprime b) : shellAlg a →ₐ[ℂ] shellAlg (a * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : shellAlg a →ₐ[ℂ] TensorProduct ℂ (shellAlg a) (shellAlg b))
```

### PAG.Part263.UDvd（PAG263.lean）
```lean
/-- 互いに素な段：N ∣ M かつ gcd(N, M/N) = 1。 -/
def UDvd (N M : ℕ) : Prop := N ∣ M ∧ Nat.Coprime N (M / N)
```

### PAG.Part263.canon（PAG263.lean）
```lean
/-- 互いに素な段の標準の写像（(i)(ii)(iii) を満たす唯一の写像）。 -/
noncomputable def canon (hNM : N ∣ M) (hc : Nat.Coprime N (M / N)) : shellAlg N →ₐ[ℂ] shellAlg M :=
  ((existsUnique_compatF_iff hNM).mpr hc).exists.choose
```

### PAG.Part263.canon_comp（PAG263.lean）
```lean
/-- **帰納系**：互いに素な段 N → M → L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}。 -/
theorem canon_comp (h1 : UDvd N M) (h2 : UDvd M L) :
    (canon h2.1 h2.2).comp (canon h1.1 h1.2) = canon (udvd_trans h1 h2).1 (udvd_trans h1 h2).2 :=
```

### PAG.Part263.compatF_iff_eq_shellLift（PAG263.lean）
```lean
/-- (i)(ii)(iii) を満たす A_a → A_{ab} は `shellLift` だけ（gcd(a, b) = 1）。 -/
theorem compatF_iff_eq_shellLift (hab : a.Coprime b) (φ : shellAlg a →ₐ[ℂ] shellAlg (a * b)) :
    CompatF (dvd_mul_right a b) φ ↔ φ = shellLift hab :=
```

### PAG.Part263.existsUnique_compatF_iff（PAG263.lean）
```lean
/-- **一意な存在の二分法**：N ∣ M のとき、(i)(ii)(iii) を満たす代数準同型 A_N → A_M が
ちょうど 1 つあるのは gcd(N, M/N) = 1 のとき、かつそのときに限る。 -/
theorem existsUnique_compatF_iff (hNM : N ∣ M) :
    (∃! φ : shellAlg N →ₐ[ℂ] shellAlg M, CompatF hNM φ) ↔ Nat.Coprime N (M / N) :=
```

### PAG.Part263.not_existsUnique_compat（PAG263.lean）
```lean
/-- **(iii) を外すと一意でない場合がある（a = 2 の例）**：gcd(2, b) = 1、1 < b のとき、Part 258 の条件 (i)(ii) だけを
課すと、それを満たす A_2 → A_{2b} は一意でない（`shellLift` と φ'。2 つあることは `compat_twLift`・`compatF_shellLift`・
`twLift_ne_shellLift` による）。 -/
theorem not_existsUnique_compat (hab : Nat.Coprime 2 b) (hb : 1 < b) :
    ¬ ∃! φ : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b), Compat (dvd_mul_right 2 b) φ :=
```

### PAG.Part263.not_isDirected_udvd（PAG263.lean）
```lean
/-- **有向でない**（照合 B の指摘で追加）：ℕ の上の UDvd は有向でない（p = 2 の場合）。 -/
theorem not_isDirected_udvd : ¬ IsDirected ℕ UDvd :=
```

### PAG.Part263.sqLim（PAG263.lean）
```lean
/-- 無平方数の段の帰納極限（ℂ 加群として）。 -/
abbrev sqLim : Type :=
  Module.DirectLimit (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => (sqMap S T h).toLinearMap)
```

### PAG.Part263.sqLim_of_injective（PAG263.lean）
```lean
/-- 各段 A_{N_S} は極限に単射で入る。 -/
theorem sqLim_of_injective (S : Finset Nat.Primes) :
    Function.Injective (Module.DirectLimit.of ℂ (Finset Nat.Primes)
      (fun S : Finset Nat.Primes => shellAlg (primeProd S)) (fun S T h => (sqMap S T h).toLinearMap) S) :=
```

### PAG.Part263.twLift（PAG263.lean）
```lean
/-- **捩れた写像** A_2 → A_{2b}：φ'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))。 -/
noncomputable def twLift (hab : Nat.Coprime 2 b) : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp twTens
```

### PAG.Part263.udvd_iff_inLayer（PAG263.lean）
```lean
/-- 内部照合（2026-11-15）：互いに素な段は、Part 216（PAG220）の層 `InLayer`（n = d·e、e は c と互いに素）で
c = d = N とした場合と同じ（N > 0）。 -/
theorem udvd_iff_inLayer {N M : ℕ} (hN : 0 < N) : UDvd N M ↔ PAG.Part220.InLayer N N M :=
```

### PAG.Part264.cornerHom（PAG264.lean）
```lean
/-- **3d. 角の写像** A_N → A_M（単位元を保たない代数準同型、φ(S) = (N/M)·π^* ∘ S ∘ π_*）。 -/
noncomputable def cornerHom (h : N ∣ M) : shellAlg N →ₙₐ[ℂ] shellAlg M where
  toFun S := ⟨cornerOp h S, cornerOp_mem h S.2⟩
  map_smul' c S := Subtype.ext (show cornerOp h (c • (S : Module.End ℂ (ZMod N → ℂ))) = c • cornerOp h S from
    cornerOp_smul h c S)
  map_zero' := Subtype.ext (cornerOp_zero h)
  map_add' S T := Subtype.ext (cornerOp_add h S T)
  map_mul' S T := Subtype.ext (cornerOp_mul h S T)
```

### PAG.Part264.cornerHom_comp（PAG264.lean）
```lean

theorem cornerHom_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) :
    (cornerHom h2).comp (cornerHom h1) = cornerHom (h1.trans h2) :=
```

### PAG.Part264.cornerHom_one_ne_one（PAG264.lean）
```lean
/-- **4d.** N < M なら φ は単位元を保たない。 -/
theorem cornerHom_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerHom h 1 ≠ 1 :=
```

### PAG.Part264.cornerHom_self（PAG264.lean）
```lean

theorem cornerHom_self : cornerHom (dvd_refl N) = NonUnitalAlgHom.id ℂ (shellAlg N) :=
```

### PAG.Part264.cornerOp_dind（PAG264.lean）
```lean
/-- **3b.** φ(D_s) = (π^*1_{D_s})·φ(1)（D 側の像は殻の掛け算と φ(1) の積）。 -/
theorem cornerOp_dind (h : N ∣ M) (s : ℕ) :
    cornerOp h (LinearMap.mulLeft ℂ (dind N s)) =
      LinearMap.mulLeft ℂ (pull h (dind N s)) * cornerOp h 1 :=
```

### PAG.Part264.cornerOp_dind_not_mem_span（PAG264.lean）
```lean
/-- **5.** (N, M) = (2, 4)：φ(D_2) は D_t の線形結合でない（Part 258 の強い読みの D 側を満たさない）。 -/
theorem cornerOp_dind_not_mem_span :
    cornerOp (show 2 ∣ 4 by norm_num) (LinearMap.mulLeft ℂ (dind 2 2)) ∉
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind 4 u)) :=
```

### PAG.Part264.cornerOp_geps（PAG264.lean）
```lean
/-- **3a.** φ(E_s) = E_{(M/N)s}。 -/
theorem cornerOp_geps (h : N ∣ M) (s : ℕ) :
    cornerOp h (PAG.Part15.convL (geps N s)) = PAG.Part15.convL (geps M (M / N * s)) :=
```

### PAG.Part264.cornerOp_mem（PAG264.lean）
```lean
/-- **3c.** φ は A_N を A_M に送る（gcd(N, M/N) によらない）。 -/
theorem cornerOp_mem (h : N ∣ M) {S : Module.End ℂ (ZMod N → ℂ)} (hS : S ∈ shellAlg N) :
    cornerOp h S ∈ shellAlg M :=
```

### PAG.Part264.cornerOp_one（PAG264.lean）
```lean
/-- φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s。 -/
theorem cornerOp_one (h : N ∣ M) :
    cornerOp h 1 = ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) :=
```

### PAG.Part264.cornerOp_pull（PAG264.lean）
```lean
/-- **1b. 引き戻しと両立**：φ(S) π^* = π^* S。 -/
theorem cornerOp_pull (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (f : ZMod N → ℂ) :
    cornerOp h S (pull h f) = pull h (S f) :=
```

### PAG.Part264.existsUnique_corner（PAG264.lean）
```lean
/-- **4a. 一意性**：引き戻しと両立し、φ(1) = Σ_{(M/N) ∣ s} E_s を満たす単位元を保たない代数準同型は φ だけ。 -/
theorem existsUnique_corner (h : N ∣ M) :
    ∃! φ : shellAlg N →ₙₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (pull h f) = pull h ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (φ 1 : Module.End ℂ (ZMod M → ℂ)) =
        ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) :=
```

### PAG.Part265.CornerLim（PAG265.lean）
```lean
/-- 角の写像の帰納極限（Mathlib の一般の `DirectLimit`。非単位的な環の構造と ℂ のスカラー倍を持つ）。 -/
abbrev CornerLim : Type := DirectLimit (fun a : Lvl => shellAlg a.val) cornerSys
```

### PAG.Part265.cornerSys_comp（PAG265.lean）
```lean
/-- 合成の法則：φ_{b,c} ∘ φ_{a,b} = φ_{a,c}。 -/
theorem cornerSys_comp {a b c : Lvl} (hab : a ≤ b) (hbc : b ≤ c) (S : shellAlg a.val) :
    cornerSys b c hbc (cornerSys a b hab S) = cornerSys a c (hab.trans hbc) S :=
```

### PAG.Part265.cornerSys_self（PAG265.lean）
```lean
/-- 恒等の法則：φ_{a,a} = id。 -/
theorem cornerSys_self (a : Lvl) (S : shellAlg a.val) : cornerSys a a le_rfl S = S :=
```

### PAG.Part265.exists_local_unit（PAG265.lean）
```lean
/-- **局所的な単位元**：極限のどの元 x にも、ある a があって、e_a = (φ(1_a) の像) は x = e_a x = x e_a を満たす。 -/
theorem exists_local_unit (x : CornerLim) :
    ∃ a : Lvl, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x :=
```

### PAG.Part265.exists_local_unit_finset（PAG265.lean）
```lean
/-- **局所的な単位元（有限集合版）**：極限の有限部分集合 F ごとに、べき等元 e_a があって、F のどの元も両側から固定する
（F ⊆ e_a·極限·e_a。局所的な単位元を持つ環の、有限集合についての定義の形）。 -/
theorem exists_local_unit_finset (F : Finset CornerLim) :
    ∃ a : Lvl, ∀ x ∈ F, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x :=
```

### PAG.Part265.not_exists_left_one（PAG265.lean）
```lean
/-- **大域の単位元はない**：極限には左単位元がない（非単位的）。 -/
theorem not_exists_left_one : ¬ ∃ u : CornerLim, ∀ x : CornerLim, u * x = x :=
```

### PAG.Part265.ofCorner_injective（PAG265.lean）
```lean
/-- 各段 A_a は極限に単射で入る。 -/
theorem ofCorner_injective (a : Lvl) : Function.Injective (ofCorner a) :=
```

### PAG.Part265.ofCorner_one_le（PAG265.lean）
```lean
/-- a ≤ b なら e_b e_a = e_a = e_a e_b。 -/
theorem ofCorner_one_le {a b : Lvl} (h : a ≤ b) :
    ofCorner b 1 * ofCorner a 1 = ofCorner a 1 ∧ ofCorner a 1 * ofCorner b 1 = ofCorner a 1 :=
```

## §E 数値の記録

### records/projection_interaction/extra_checks.py
```
"""統合照合（records/tail_audit4）の指摘を受けた追加の数値（証明ではない）。2026-11-19。
(a) 素朴な核 τ/√f の位相で作った U'_N が単数の角に入る N。
(b) range(D_1) ∩ range(E_1) が、0 拡張した原始指標の張る空間と一致するか（次元だけでなく空間として）。
(c) その空間の上で J∘H（J は素数冪ごとの殻の反転の CRT の積、H は Hartley/√N）が、原始指標 χ に W(χ) を掛ける作用と一致するか
    （W(χ) = τ(χ)/(i^a √N)。単数の上の U_N の原始指標での固有値と同じ値）。
(d) A_N の可換子 A_N' の次元、A_N' = span{R_u} となる N、A_N' が可換になる N。
(e) F_M ι = V F_N を実際に比べた組（M = kN ≤ Nmax、k = 2, 3）の数。
"""
import math, sys, cmath
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/projection_interaction')
from corner_check import A, orth_basis, in_span, divisors, iota, vemb, fourier
from interaction_check import units, Rmat, hartley, shell_inv, characters, conductor, root_num_prim

def commutant_dim(N, gens):
    I = np.eye(N)
    K = sum((np.kron(G.T, I) - np.kron(I, G)).conj().T @ (np.kron(G.T, I) - np.kron(I, G)) for G in gens)
    ev = np.linalg.eigvalsh(K)
    return int((ev < 1e-8 * max(1.0, ev.max())).sum()), K

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 36
a_list, b_bad, c_bad, d_eq, d_comm, e_pairs = [], [], [], [], [], 0
for N in range(2, Nmax + 1):
    B, D, E = A(N); Ui = units(N); phi = len(Ui)
    chars = characters(N)
    S = np.zeros((N, phi), dtype=complex)
    for j, u in enumerate(Ui): S[u, j] = 1.0
    cor = orth_basis([S.T @ B[:, i].reshape(N, N) @ S for i in range(B.shape[1])])
    # (a)
    Un = np.zeros((phi, phi), dtype=complex)
    for c in chars:
        v = np.array([c[u] for u in Ui]); w, f, even = root_num_prim(N, c)
        naive = w * (1 if even else 1j)   # τ/√f
        Un += naive * np.outer(v, v.conj()) / phi
    if in_span(cor, Un): a_list.append(N)
    # (b)
    Q = D[1] @ E[1] @ D[1]; Qh = (Q + Q.conj().T) / 2
    ev, W = np.linalg.eigh(Qh); Wint = W[:, ev > 1 - 1e-8]
    prim = [c for c in chars if conductor(N, c) == N]
    P = np.array([[c.get(x, 0.0) if math.gcd(x, N) == 1 else 0.0 for x in range(N)] for c in prim]).T if prim else np.zeros((N, 0))
    if Wint.shape[1] != P.shape[1] or (P.shape[1] and not (np.allclose(Wint @ (Wint.conj().T @ P), P))):
        b_bad.append(N)
    # (c)
    J, _ = shell_inv(N); H = hartley(N)
    for k, c in enumerate(prim):
        w, f, even = root_num_prim(N, c)
        if not np.allclose(J @ H @ P[:, k], w * P[:, k]): c_bad.append(N); break
    # (d)
    gens = list(D.values()) + list(E.values())
    dc, K = commutant_dim(N, gens)
    dR = orth_basis([Rmat(N, u) for u in Ui]).shape[1]
    if dc == dR: d_eq.append(N)
    ev2, V2 = np.linalg.eigh(K); null = V2[:, ev2 < 1e-8 * max(1.0, ev2.max())]
    mats = [null[:, i].reshape(N, N, order='F') for i in range(null.shape[1])]
    if all(np.allclose(X @ Y, Y @ X) for X in mats for Y in mats): d_comm.append(N)
    # (e)
    for kk in (2, 3):
        M = N * kk
        if M <= Nmax:
            e_pairs += 1
            assert np.allclose(fourier(M) @ iota(N, M), vemb(N, M) @ fourier(N))
print(f'(a) 素朴な核 τ/√f の U\'_N が角に入る N（2〜{Nmax}）：{a_list}')
print(f'(b) range(D_1)∩range(E_1) ≠ 原始指標の span となる N：{b_bad}')
print(f'(c) J∘H χ ≠ W(χ)χ となる原始指標がある N：{c_bad}')
print(f'(d) A_N\' = span{{R_u}}（次元の一致）となる N：{d_eq}／A_N\' が可換となる N：{d_comm}')
print(f'(e) F_M ι = V F_N を比べた組（k = 2, 3、M ≤ {Nmax}）：{e_pairs} 組、すべて一致')
```

### records/projection_interaction/extra_checks.log
```
(a) 素朴な核 τ/√f の U'_N が角に入る N（2〜36）：[2, 3, 4, 6, 12]
(b) range(D_1)∩range(E_1) ≠ 原始指標の span となる N：[]
(c) J∘H χ ≠ W(χ)χ となる原始指標がある N：[]
(d) A_N' = span{R_u}（次元の一致）となる N：[2, 3, 4, 6, 12]／A_N' が可換となる N：[2, 3, 4, 6, 12]
(e) F_M ι = V F_N を比べた組（k = 2, 3、M ≤ 36）：28 組、すべて一致
```

### records/projection_interaction/interaction_check.py
```
"""無限素点・スケーリング・貼り合わせ U と、有限素点の側の代数 A_N の相互作用（着手前の見込み確認。数値。証明ではない）。2026-11-19。

記号：V_N = ℤ/N 上の関数。A_N = ⟨D_s, E_s⟩（Part 214（PAG218）の shellAlg）。R_u f(x) = f(ux)（Part 214（PAG218）の dil）。
P = R_{-1}（パリティ、無限素点の符号）。H = 離散 Hartley 変換/√N（核 cas(2πxy/N)）。F = フーリエ（e(−kx/N)/√N）。
J = 殻ごとの反転：x = s·w（s = gcd(x, N)、w は法 N/s の単数）↦ s·w⁻¹（w⁻¹ は法 N/s）。
U_N = Σ_χ phaseA1(χ)·P_χ（Part 254 の UA1、単数の上の関数）。phaseA1(χ) = rootNum(χ の原始指標)。
"""
import math, sys, cmath
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
from corner_check import A, orth_basis, in_span, divisors, iota, vemb, fourier

def units(N): return [x for x in range(N) if math.gcd(x, N) == 1] if N > 1 else [0]

def Rmat(N, u):
    R = np.zeros((N, N), dtype=complex)
    for x in range(N): R[x, (u * x) % N] = 1.0   # (R f)(x) = f(ux)
    return R

def hartley(N):
    return np.array([[math.cos(2*math.pi*x*y/N) + math.sin(2*math.pi*x*y/N) for y in range(N)] for x in range(N)], dtype=complex) / math.sqrt(N)

def factor(N):
    f, n, p = {}, N, 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def local_inv(q, x):
    """ℤ/q（q = p^e）の殻ごとの反転：p^k w ↦ p^k w⁻¹。"""
    if x % q == 0: return 0
    s = math.gcd(x, q); m = q // s
    return (s * pow((x // s) % m, -1, m)) % q

def crt(res):
    x, M = 0, 1
    for q, r in res:
        t = ((r - x) * pow(M, -1, q)) % q; x += M * t; M *= q
    return x % M

def shell_inv(N, naive=False):
    """naive = True：法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s）。False：素数冪ごとの反転の CRT の積。"""
    J = np.zeros((N, N), dtype=complex); img = {}
    qs = [p ** e for p, e in factor(N).items()]
    for x in range(N):
        if naive:
            s = math.gcd(x, N); m = N // s
            y = 0 if m == 1 else (s * pow((x // s) % m, -1, m)) % N
        else:
            y = crt([(q, local_inv(q, x % q)) for q in qs]) if N > 1 else 0
        img[x] = y; J[x, y] = 1.0  # (J f)(x) = f(J x)
    return J, img

def comm_all(B, X, N):
    return all(np.allclose(B[:, i].reshape(N, N) @ X, X @ B[:, i].reshape(N, N)) for i in range(B.shape[1]))

def normalizes(B, X, N):
    Xi = np.linalg.inv(X)
    return all(in_span(B, X @ B[:, i].reshape(N, N) @ Xi) for i in range(B.shape[1]))

def characters(N):
    """(ℤ/N)^× の指標を、R_u の同時対角化で求める（値の辞書 u ↦ χ(u)）。"""
    U = units(N); n = len(U)
    if n == 1: return [{U[0]: 1.0}]
    idx = {u: i for i, u in enumerate(U)}
    rng = np.random.default_rng(1)
    c = rng.normal(size=n) + 1j * rng.normal(size=n)
    Mx = np.zeros((n, n), dtype=complex)
    for k, a in enumerate(U):
        for u in U: Mx[idx[u], idx[(a * u) % N]] += c[k]
    w, V = np.linalg.eig(Mx)
    chars = []
    for j in range(n):
        v = V[:, j] / V[idx[1], j]
        chars.append({u: v[idx[u]] for u in U})
    return chars

def conductor(N, chi):
    for d in divisors(N):
        if all(abs(chi[u] - 1) < 1e-8 for u in chi if (u - 1) % d == 0): return d
    return N

def root_num_prim(N, chi):
    f = conductor(N, chi)
    # 法 f の原始指標：法 f の単数 y に、y ≡ u (mod f) となる法 N の単数 u をとる
    prim = {}
    for u in chi: prim.setdefault(u % f, chi[u])
    tau = sum(prim[y] * cmath.exp(2j*math.pi*y/f) for y in prim) if f > 1 else 1.0
    even = abs(prim.get(f - 1 if f > 1 else 0, 1.0) - 1) < 1e-8
    return tau / ((1 if even else 1j) * math.sqrt(f)), f, even

def run(Nmax):
    rep = {k: [] for k in ['Jnaive_comm', 'R_comm', 'P_comm', 'P_in_A', 'J_iso', 'J_comm', 'J_in_A', 'J_in_dil', 'JR', 'H_swap', 'JH_norm',
                           'Fphi_psi', 'corner_dim', 'U_comm_corner', 'U_in_corner', 'Pu_in_corner', 'Vprim', 'JH_Vprim']}
    for N in range(2, Nmax + 1):
        B, D, E = A(N); dvs = divisors(N)
        Rs = {u: Rmat(N, u) for u in units(N)}
        P = Rmat(N, N - 1)
        rep['R_comm'].append((N, all(comm_all(B, R, N) for R in Rs.values())))
        rep['P_comm'].append((N, comm_all(B, P, N)))
        rep['P_in_A'].append((N, in_span(B, P)))
        Jn, _ = shell_inv(N, naive=True)
        rep['Jnaive_comm'].append((N, comm_all(B, Jn, N)))
        J, img = shell_inv(N)
        rep.setdefault('J_units_inv', []).append((N, all(img[u] == pow(u, -1, N) for u in units(N)) if N > 1 else True))
        rep['J_iso'].append((N, all(math.gcd(img[x] - img[y], N) == math.gcd(x - y, N) for x in range(N) for y in range(N))))
        rep['J_comm'].append((N, comm_all(B, J, N)))
        rep['J_in_A'].append((N, in_span(B, J)))
        dilB = orth_basis(list(Rs.values()))
        rep['J_in_dil'].append((N, in_span(dilB, J)))
        rep['JR'].append((N, all(np.allclose(J @ Rs[u], Rs[pow(u, -1, N)] @ J) for u in units(N))))
        H = hartley(N)
        rep['H_swap'].append((N, all(np.allclose(H @ D[s] @ H, E[s]) and np.allclose(H @ E[s] @ H, D[s]) for s in dvs)))
        rep['JH_norm'].append((N, normalizes(B, J @ H, N)))
        # F φ F⁻¹ = ψ(F · F⁻¹)（M = N·k、k ≤ 3）
        # 比べた組だけを数える（統合照合 tail_audit4 の指摘 2-1 で直した。以前は比べない N も「偽でない」に数えていた）
        for k in (2, 3):
            M = N * k
            if M > Nmax: continue
            FN, FM = fourier(N), fourier(M); I, V = iota(N, M), vemb(N, M)
            rep['Fphi_psi'].append(((N, M), np.allclose(FM @ I, V @ FN)))
        # 単数の角：D_1 A_N D_1 を単数の上の関数に制限
        Ui = units(N)
        S = np.zeros((N, len(Ui)), dtype=complex)
        for j, u in enumerate(Ui): S[u, j] = 1.0
        cor = orth_basis([S.T @ B[:, i].reshape(N, N) @ S for i in range(B.shape[1])])
        chars = characters(N)
        conds = sorted({conductor(N, c) for c in chars})
        rep['corner_dim'].append((N, cor.shape[1], len(conds)))
        # U_N = Σ phase(χ) P_χ（単数の上）。P_χ = χ χ^* / φ(N)（関数 χ(u) をベクトルに）
        phi = len(Ui)
        Umat = np.zeros((phi, phi), dtype=complex); Pu = np.zeros((phi, phi), dtype=complex)
        for c in chars:
            v = np.array([c[u] for u in Ui]); Pc = np.outer(v, v.conj()) / phi
            w, f, even = root_num_prim(N, c)
            Umat += w * Pc; Pu += (1 if even else -1) * Pc
        Pd = {}
        for c in chars:
            v = np.array([c[u] for u in Ui]); d = conductor(N, c)
            Pd[d] = Pd.get(d, 0) + np.outer(v, v.conj()) / phi
        rep.setdefault('corner_eq_condproj', []).append((N, all(in_span(cor, X) for X in Pd.values()) and cor.shape[1] == len(Pd)))
        rep['U_comm_corner'].append((N, all(np.allclose(cor[:, i].reshape(phi, phi) @ Umat, Umat @ cor[:, i].reshape(phi, phi)) for i in range(cor.shape[1]))))
        rep['U_in_corner'].append((N, in_span(cor, Umat)))
        rep.setdefault('U_is_identity', []).append((N, np.allclose(Umat, np.eye(phi))))
        rep['Pu_in_corner'].append((N, in_span(cor, Pu)))
        # V_prim = range(D_1) ∩ range(E_1)：次元 = 原始指標の数
        Q = D[1] @ E[1] @ D[1]
        ev = np.linalg.eigvalsh((Q + Q.conj().T) / 2)
        dim_int = int((ev > 1 - 1e-8).sum())
        nprim = sum(1 for c in chars if conductor(N, c) == N)
        rep['Vprim'].append((N, dim_int, nprim))
        # JH は range(D_1) ∩ range(E_1) を保つ
        W = np.linalg.eigh((Q + Q.conj().T) / 2)[1][:, ev > 1 - 1e-8]
        X = J @ H @ W
        rep['JH_Vprim'].append((N, W.shape[1] == 0 or np.allclose(W @ (W.conj().T @ X), X)))
    return rep

if __name__ == '__main__':
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    rep = run(Nmax)
    for k, v in rep.items():
        if k in ('corner_dim', 'Vprim'):
            bad = [t for t in v if t[1] != t[2]]
            print(f'{k}: 組 {len(v)}、不一致 {bad}')
        elif k in ('P_in_A', 'J_in_A', 'J_in_dil', 'U_in_corner', 'Pu_in_corner', 'U_is_identity'):
            print(f'{k}: 真となる N = {[n for n, b in v if b]}')
        else:
            print(f'{k}: 偽となる N = {[n for n, b in v if not b]}（{len(v)} 個）')
```

### records/projection_interaction/interaction_check.log
```
Jnaive_comm: 偽となる N = [10, 14, 15, 18, 20, 21, 22, 26, 28, 30, 33, 34, 35, 36]（35 個）
R_comm: 偽となる N = []（35 個）
P_comm: 偽となる N = []（35 個）
P_in_A: 真となる N = [2, 3, 4, 6, 12]
J_iso: 偽となる N = []（35 個）
J_comm: 偽となる N = []（35 個）
J_in_A: 真となる N = [2, 3, 4, 6, 8, 12, 24]
J_in_dil: 真となる N = [2, 3, 4, 6, 8, 12, 24]
JR: 偽となる N = []（35 個）
H_swap: 偽となる N = []（35 個）
JH_norm: 偽となる N = []（35 個）
Fphi_psi: 偽となる N = []（28 個）
corner_dim: 組 35、不一致 []
U_comm_corner: 偽となる N = []（35 個）
U_in_corner: 真となる N = [2, 3, 4, 6, 8, 12, 24]
Pu_in_corner: 真となる N = [2, 3, 4, 6, 12]
Vprim: 組 35、不一致 []
JH_Vprim: 偽となる N = []（35 個）
J_units_inv: 偽となる N = []（35 個）
corner_eq_condproj: 偽となる N = []（35 個）
U_is_identity: 真となる N = [2, 3, 4, 6, 8, 12, 24]
```

### records/projection_interaction/sign_corner_check.log
```
組 139、「P_M φ(1) ∈ A_M ⇔ N ∣ 12」の不一致 []
```

### records/projection_interaction/control_fqt_interaction.log
```
p=2 e=1: dimA=4 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 1 導手の数 1 原始の位相の幅 0.000 JF|単数∈角 True
p=2 e=2: dimA=10 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 2 導手の数 2 原始の位相の幅 0.000 JF|単数∈角 True
p=2 e=3: dimA=19 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 3 導手の数 3 原始の位相の幅 1.414 JF|単数∈角 False
p=2 e=4: dimA=31 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 4 導手の数 4 原始の位相の幅 2.000 JF|単数∈角 False
p=3 e=1: dimA=5 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 2 導手の数 2 原始の位相の幅 0.000 JF|単数∈角 True
p=3 e=2: dimA=12 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 3 導手の数 3 原始の位相の幅 2.000 JF|単数∈角 False
p=3 e=3: dimA=22 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 4 導手の数 4 原始の位相の幅 2.000 JF|単数∈角 False
p=5 e=1: dimA=5 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 2 導手の数 2 原始の位相の幅 1.747 JF|単数∈角 False
p=5 e=2: dimA=12 R_u可換 True J可換 True F交換 True JF正規化 True 角の次元 3 導手の数 3 原始の位相の幅 2.000 JF|単数∈角 False
```

### records/gamma_corner/corner_check.py（共通の定義）
```
"""方向 γ の立て直し：着手前の見込み確認（数値。証明ではない）。2026-11-19。

N | M、π^*：ℤ/M → ℤ/N に沿った引き戻し（Part 197 の pull）、ι = π^*/√(M/N)（等長）。φ(T) = ι T ι^†。
V：部分群への埋め込み x ↦ (M/N)x に沿った 0 拡張（等長）、ψ(T) = V T V^†。
A_N：D_s（殻の指示関数の掛け算）と E_s（双対殻への射影）が生成する代数（Part 214 の shellAlg）。
"""
import itertools, math, sys
import numpy as np

def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]

def fourier(N):
    return np.array([[np.exp(-2j*np.pi*k*x/N) for x in range(N)] for k in range(N)]) / np.sqrt(N)

def gens(N):
    F = fourier(N)
    D = {s: np.diag([1.0 if math.gcd(N, x) == s else 0.0 for x in range(N)]).astype(complex) for s in divisors(N)}
    E = {s: F.conj().T @ np.diag([1.0 if math.gcd(N, k) == s else 0.0 for k in range(N)]) @ F for s in divisors(N)}
    return D, E

def orth_basis(mats, tol=1e-9):
    """行列の張る空間の正規直交基底（ベクトル化）。"""
    if not mats: return np.zeros((0, 0))
    A = np.array([m.ravel() for m in mats]).T
    U, S, _ = np.linalg.svd(A, full_matrices=False)
    r = int((S > tol * max(1.0, S[0])).sum())
    return U[:, :r]

def algebra(N):
    D, E = gens(N)
    G = list(D.values()) + list(E.values())
    B = orth_basis([np.eye(N, dtype=complex)] + G)
    while True:
        mats = [B[:, i].reshape(N, N) for i in range(B.shape[1])]
        prods = [a @ g for a in mats for g in G]
        B2 = orth_basis(mats + prods)
        if B2.shape[1] == B.shape[1]: return B, D, E
        B = B2

def in_span(B, X, tol=1e-7):
    v = X.ravel()
    return np.linalg.norm(v - B @ (B.conj().T @ v)) < tol * max(1.0, np.linalg.norm(v))

def iota(N, M):
    P = np.zeros((M, N), dtype=complex)
    for y in range(M): P[y, y % N] = 1.0
    return P / np.sqrt(M // N)

def vemb(N, M):
    k = M // N
    V = np.zeros((M, N), dtype=complex)
    for x in range(N): V[(k * x) % M, x] = 1.0
    return V

cache = {}
def A(N):
    if N not in cache: cache[N] = algebra(N)
    return cache[N]

def check_pair(N, M):
    k = M // N
    BN, DN, EN = A(N); BM, DM, EM = A(M)
    I = iota(N, M); V = vemb(N, M)
    out = {}
    out['iso'] = np.allclose(I.conj().T @ I, np.eye(N)) and np.allclose(V.conj().T @ V, np.eye(N))
    phi = lambda T: I @ T @ I.conj().T
    psi = lambda T: V @ T @ V.conj().T
    spanD = orth_basis(list(DM.values())); spanE = orth_basis(list(EM.values()))
    # φ
    out['phi_in_AM'] = all(in_span(BM, phi(X)) for X in list(DN.values()) + list(EN.values()))
    out['phi_E_strict'] = all(np.allclose(phi(EN[s]), EM[k * s]) for s in DN)
    out['phi_D_in_spanD'] = [s for s in DN if in_span(spanD, phi(DN[s]))]
    Q = sum(EM[t] for t in EM if t % k == 0)
    out['phi_one_is_Q'] = np.allclose(phi(np.eye(N)), Q)
    pullN = I * np.sqrt(k)
    out['cond_i'] = all(np.allclose(phi(X) @ pullN, pullN @ X) for X in list(DN.values()) + list(EN.values()))
    # 像の次元と角 Q A_M Q の次元
    imgs = [phi(BN[:, i].reshape(N, N)) for i in range(BN.shape[1])]
    corner = [Q @ BM[:, i].reshape(M, M) @ Q for i in range(BM.shape[1])]
    out['dimAN'] = BN.shape[1]; out['dimAM'] = BM.shape[1]
    out['dim_img'] = orth_basis(imgs).shape[1]; out['dim_corner'] = orth_basis(corner).shape[1]
    # ψ（0 拡張）
    out['psi_in_AM'] = all(in_span(BM, psi(X)) for X in list(DN.values()) + list(EN.values()))
    out['psi_D_strict'] = all(np.allclose(psi(DN[s]), DM[k * s]) for s in DN)
    out['psi_E_in_spanE'] = [s for s in EN if in_span(spanE, psi(EN[s]))]
    # フーリエ共役：F_M V F_N^† = c·ι（c は定数）
    W = fourier(M) @ V @ fourier(N).conj().T
    c = W[0, 0] / I[0, 0]
    out['fourier_conj'] = np.allclose(W, c * I) and abs(abs(c) - 1) < 1e-9
    # BC の ρ：φ(τ_x) = (N/M) Σ_{y ≡ x mod N} τ_y（τ は平行移動）
    def tau(n, x):
        T = np.zeros((n, n), dtype=complex)
        for z in range(n): T[(z + x) % n, z] = 1.0
        return T
    out['bc_rho'] = all(np.allclose(phi(tau(N, x)), sum(tau(M, y) for y in range(M) if y % N == x) / k) for x in range(N))
    return out

def check_chain(N, M, L):
    return np.allclose(iota(M, L) @ iota(N, M), iota(N, L)) and np.allclose(vemb(M, L) @ vemb(N, M), vemb(N, L))

if __name__ == '__main__':
    Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    pairs = [(N, M) for M in range(1, Mmax + 1) for N in divisors(M)]
    bad = []
    print('N M gcd(N,M/N) | dimA_N dimA_M dim像 dim角 | φ⊂A_M φ(E)厳密 φ(D)∈spanD(sの数/全) φ(1)=Q (i) | ψ⊂A_M ψ(D)厳密 ψ(E)∈spanE フーリエ共役 BCのρ')
    for N, M in pairs:
        o = check_pair(N, M)
        g = math.gcd(N, M // N)
        line = (f"{N} {M} {g} | {o['dimAN']} {o['dimAM']} {o['dim_img']} {o['dim_corner']} | {o['phi_in_AM']} {o['phi_E_strict']} "
                f"{len(o['phi_D_in_spanD'])}/{len(divisors(N))} {o['phi_one_is_Q']} {o['cond_i']} | {o['psi_in_AM']} {o['psi_D_strict']} "
                f"{len(o['psi_E_in_spanE'])}/{len(divisors(N))} {o['fourier_conj']} {o['bc_rho']}")
        print(line)
        if not (o['iso'] and o['phi_in_AM'] and o['phi_E_strict'] and o['phi_one_is_Q'] and o['cond_i'] and o['psi_in_AM']
                and o['psi_D_strict'] and o['fourier_conj'] and o['bc_rho'] and o['dim_img'] == o['dimAN']):
            bad.append((N, M))
    chains = [(N, M, L) for L in range(1, Mmax + 1) for M in divisors(L) for N in divisors(M)]
    cbad = [c for c in chains if not check_chain(*c)]
    print(f'組 {len(pairs)}、期待から外れた組 {bad}')
    print(f'合成の鎖 N|M|L：{len(chains)} 本、合成が合わない鎖 {cbad}')
    eq = [(N, M) for N, M in pairs if check_pair(N, M)['dim_img'] == check_pair(N, M)['dim_corner']]
    print(f'像 = 角（次元が等しい）組の数：{len(eq)}/{len(pairs)}')
```
