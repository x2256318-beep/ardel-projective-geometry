# MathSciNet・zbMATH での文献照合の試み（2026-11-26）

（著者の依頼「MathSciNet・zbMATH での文献照合」（2026-11-26 11:08）による。対象は候補 1・候補 3・方向 γ。記録の材料で、照合はまだ受けていない（台帳 L27）。）

## §1 結論

- **構築側の環境からは、MathSciNet と zbMATH Open の主題検索はできなかった。** zbMATH Open の検索結果のページ（`zbmath.org/?q=…`）は取得の許可リストになく、取得を断られた。ウェブ検索で `zbmath.org` に絞ると、出てくるのは雑誌と著者の紹介のページだけで、文書の検索結果は出なかった。MathSciNet は購読が必要で、無料で使えるのは書誌の照会（MR Lookup、最大 3 件）や著者の紹介のページなどに限られる。MR Lookup は、検索語を変えた URL の取得が許可リストで断られるので、ここからは使えなかった。
- したがって、候補 1・候補 3・方向 γ の MathSciNet・zbMATH の照合は、**著者側の作業のまま**（§3 に検索式）。
- 一般のウェブ検索で、次の 2 つが分かった（§2）。

## §2 一般のウェブ検索で分かったこと

1. **Hanaki–Kim–Maekawa の本文は、信州大学の機関リポジトリで公開されているとみられる**（ファイルは開けていない）（`soar-ir.repo.nii.ac.jp/record/11832/files/Terwilliger_algebras_direct_wreath_products.pdf`。題・著者・要旨はウェブ検索の抜粋で確認）。ただし、ファイルが長い署名つきの URL に転送され、構築側の取得の道具では開けなかった。著者がこの URL を開けば本文を確かめられる。書誌：J. Algebra 343 (2011) 195–200（Kim arXiv:1109.1334 の要旨による）。候補 3 で確かめたいのは、商 ℤ/M → ℤ/N に沿った写像（単位的な写像を含む）を扱っているかどうか。
2. **円分スキームの Terwilliger 代数と Jacobi 和の論文**：Bastian–Humphries（arXiv:2409.09167）の文献表の [23] は「Haruo Ishibashi, Tatsuro Ito, Mieko Tamada, Terwilliger algebras of cyclotomic schemes and Jacobi sums, European Journal of Combinatorics 20 (1999) 397–410」（取得ツールの要約による）。この鎖の記録（`pag2_candidate1_generation_collation.md`、辞書）では著者を「Ishibashi–Ito–Yamada」と書いており、3 人目の著者名が食い違う（どちらが正しいかは未確認。統合照合 IX の照合者のウェブ検索で、dblp のレコードのキーが `journals/ejc/IshibashiIY99`（3 人目の頭文字が Y）だったので、Yamada の見込みが高い。頁は開いていない）。Akiyama（Acta Arith. 75 (1996)）は、Jacobi 和の有理性が円分スキームの Terwilliger 代数の既約加群の特徴づけに使われると書いている（私的版の抜粋）。
   - 位置づけ（構築側の読み、確信度：中）：この論文の「円分スキーム」は有限体の上のもの（乗法群の部分群の剰余類）で、この鎖の ℤ/N 上の軌道 Schur 環（候補 1 の対象）とは別の対象（記録の既存の注意どおり）。ただし、Terwilliger 代数の構造に Jacobi 和が現れる点は、Part 262（PAG266）の赤道の係数（Jacobi 和の 𝔀 による書き換え）と近い。Part 262 のラベル（ガウス和の形［既知］、ほか［再導出（小さい）］）を変える根拠にはならないが、辞書 §20 の近い先行として載せる価値がある（本文は未確認）。
2b. **局所環の上の円分スキーム**（同日の追加の検索）：H. Ishibashi「The Terwilliger algebras of certain association schemes over the Galois rings of characteristic 4」Graphs and Combinatorics 12 (1996) 39–54（DOI 10.1007/BF01858443。unpaywall の頁の要旨と文献表で確認）。標数 4 の Galois 環の上の円分スキームについて、Terwilliger 代数の既約加群の多くが標準の形をとり、そうでない場合は環の上の Jacobi 和の関係が成り立つこと、class 3 では Jacobi 和で既約加群が完全に決まることを示す。有限体の場合の先行は Ishibashi–Ito–Munemasa「The Terwilliger algebras of cyclotomic schemes and the rationality of Jacobi sums」（Algebraic Combinatorics, Fukuoka 1993, pp. 43–44、同じ頁の文献表による）。
   - 位置づけ（構築側の読み、確信度：低〜中）：標数 4 の Galois 環の次数 1 は ℤ/4 なので、ℤ/p^k の上の軌道スキームの Terwilliger 代数と Jacobi 和の関係について、局所環の場合の先行に当たる可能性がある（この鎖の素数冪の結果はすでに［既知］）。Part 262（PAG266）の赤道の係数（素数冪の法での Jacobi 和）の近い先行の候補として辞書に載せる。本文は未確認で、「円分スキーム」の定義（単数群のどの部分群の剰余類か）がこの鎖の軌道スキームと一致するかも未確認。
3. 候補 3 の周辺：Muzychuk–Xu「Terwilliger algebras of wreath products of association schemes」（zbMATH の著者の紹介のページで Zbl 1329.05313、2016）。商に沿った写像を扱うかは未確認。

## §3 著者側で行う検索（検索式）

zbMATH Open（無料、`zbmath.org` の一行検索）：
- 候補 1：`ti:Terwilliger & (cyclic | cyclotomic | "Schur ring")`、`"Terwilliger algebra" & generat* & (cyclic | "Schur ring")`
- 候補 3：`ai:hanaki.akihide & ti:Terwilliger`（Hanaki–Kim–Maekawa の項目と、それを引用する文書の一覧を見る）、`"Terwilliger algebra" & (homomorphism | quotient | fusion | "quotient scheme")`
- 方向 γ：`"Bost-Connes" & ("association scheme" | Terwilliger | "Schur ring")`
- 書誌の確認：`Ishibashi & Ito & cyclotomic & Jacobi`（3 人目の著者名）

MathSciNet（購読が必要）：上と同じ語に加えて、Hanaki–Kim–Maekawa の MR 番号を引用する文献（`cp:` 検索）と、Ishibashi–Ito–(Tamada / Yamada) のレビュー。

確かめたい問い：
- 候補 1：ℤ/N 上の円分（軌道）Schur 環の Terwilliger 代数 T(0) の生成系の分類（とくに合成数の N）を書いた文献があるか。
- 候補 3：商 ℤ/M → ℤ/N に沿った、引き戻しと両立し殻を混ぜない単位的な代数準同型 T(0)_N → T(0)_M の存在・不存在を書いた文献があるか（Hanaki–Kim–Maekawa の本文を含む）。
- 方向 γ：有限レベルの Bost–Connes（群環 ℂ[ℤ/N] の上の ρ_n）と T(0) を結ぶ記述があるか。

## §4 検索ログ（構築側、2026-11-26 11:10〜11:20 ごろ）

- WebFetch `https://zbmath.org/?q=Terwilliger+algebra+cyclotomic`：許可リストにないとして断られた。
- WebSearch（`zbmath.org` に限定）：「Terwilliger algebra cyclotomic scheme」「Hanaki Kim Maekawa Terwilliger algebras direct product wreath product」「Terwilliger algebra Schur ring cyclic group generated」「Hanaki Akihide author profile zbMATH」「Terwilliger algebra quotient association scheme homomorphism」「Bost-Connes system finite level association scheme Terwilliger」「Ishibashi Ito Terwilliger algebras cyclotomic schemes Jacobi sums European Journal of Combinatorics 1999」。出たのは雑誌・著者の紹介のページだけ。
- WebSearch（`ams.org` に限定）：「MathSciNet MR Lookup free reference」。無料の道具の範囲を確認。
- WebSearch（限定なし）：「Hanaki Kim Maekawa "Terwilliger algebras" direct products association schemes」「Terwilliger algebra cyclotomic association scheme Z_n generators classification」「"Terwilliger algebras of direct and wreath products of association schemes" J. Algebra 343 2011」「Ishibashi Ito Tamada "Terwilliger algebras of cyclotomic schemes and Jacobi sums"」。
- WebFetch：Hanaki–Kim–Maekawa の PDF（転送先の URL が 250 文字を超え、取得できなかった）、arXiv:2409.09167（文献表の [23] を確認）。
- 「見つからなかった」は不存在の証明ではない。
