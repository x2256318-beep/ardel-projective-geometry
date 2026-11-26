# MathSciNet・zbMATH での文献照合の試み（2026-11-26）

（著者の依頼「MathSciNet・zbMATH での文献照合」（2026-11-26 11:08）による。対象は候補 1・候補 3・方向 γ。記録の材料で、照合はまだ受けていない（台帳 L27）。）

## §1 結論

- **構築側の環境からは、MathSciNet と zbMATH Open の主題検索はできなかった。** zbMATH Open の検索結果のページ（`zbmath.org/?q=…`）は取得の許可リストになく、取得を断られた。ウェブ検索で `zbmath.org` に絞ると、出てくるのは雑誌と著者の紹介のページだけで、文書の検索結果は出なかった。MathSciNet は購読が必要で、無料で使えるのは書誌の照会（MR Lookup、最大 3 件）や著者の紹介のページなどに限られる。MR Lookup は、検索語を変えた URL の取得が許可リストで断られるので、ここからは使えなかった。
- したがって、候補 1・候補 3・方向 γ の MathSciNet・zbMATH の照合は、**著者側の作業のまま**（§3 に検索式）。
- 一般のウェブ検索で、次の 2 つが分かった（§2）。

## §2 一般のウェブ検索で分かったこと

1. **Hanaki–Kim–Maekawa の本文は、信州大学の機関リポジトリで公開されているとみられる**（ファイルは開けていない）（`soar-ir.repo.nii.ac.jp/record/11832/files/Terwilliger_algebras_direct_wreath_products.pdf`。題・著者・要旨はウェブ検索の抜粋で確認）。ただし、ファイルが長い署名つきの URL に転送され、構築側の取得の道具では開けなかった。著者がこの URL を開けば本文を確かめられる。書誌：J. Algebra 343 (2011) 195–200（Kim arXiv:1109.1334 の要旨による）。候補 3 で確かめたいのは、商 ℤ/M → ℤ/N に沿った写像（単位的な写像を含む）を扱っているかどうか。（後注 2026-11-26 13:52、著者側（Muse）が信州大学の機関リポジトリの著者版プレプリント（2010-09-13 投稿）を読んだ結果による。構築側は本文を開いていない。定理 3.1 は仮定なしの同型、仮定は定理 4.1（輪積）だけ。商に沿った写像の記述はこの本文の範囲で見つからなかった。書誌は J. Algebra 343(1) (2011) 195–200、DOI 10.1016/j.jalgebra.2011.05.035 で、Kim の引用と一致。詳細は辞書 §3 の文献表の行の後注。）（後注 2026-11-26 15:0x、統合照合 XII の指摘を受けて構築側が足した：「信州大学の機関リポジトリ」は、著者の 13:46 のメッセージ（`records/ledger_XI/integrated/author_message_1346.md`）による同定で、13:52 の報告そのものはリポジトリ名を言っていない。）
2. **円分スキームの Terwilliger 代数と Jacobi 和の論文**：Bastian–Humphries（arXiv:2409.09167）の文献表の [23] は「Haruo Ishibashi, Tatsuro Ito, Mieko Tamada, Terwilliger algebras of cyclotomic schemes and Jacobi sums, European Journal of Combinatorics 20 (1999) 397–410」（取得ツールの要約による）。この鎖の記録（`pag2_candidate1_generation_collation.md`、辞書）では著者を「Ishibashi–Ito–Yamada」と書いており、3 人目の著者名が食い違う（どちらが正しいかは未確認。（後注 2026-11-26 14:25：zbMATH の項目 Zbl 0944.05101 で 3 人目は Yamada, Mieko と確定。著者側の API 検索による。DOI 10.1006/eujc.1998.0276。Bastian–Humphries の文献表の「Tamada」は誤記とみられる。）統合照合 IX の照合者のウェブ検索で、dblp のレコードのキーが `journals/ejc/IshibashiIY99`（3 人目の頭文字が Y）だったので、Yamada の見込み（dblp のキーによる。頁は未見））。Akiyama（Acta Arith. 75 (1996)）は、Jacobi 和の有理性が円分スキームの Terwilliger 代数の既約加群の特徴づけに使われると書いている（私的版の抜粋）。
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

## §5 2 回目の試み（2026-11-26 13:55〜14:00、著者の 13:55 の依頼「候補 1・候補 3・方向 γ の MathSciNet・zbMATH 照合」）

- WebFetch で `api.zbmath.org` の検索 API と `zbmath.org/?q=…` を構築側が組み立てて試した：許可リストにないとして断られた。
- Claude in Chrome：拡張がつながっておらず使えなかった（著者はモバイルのアプリから送信）。
- 著者が §3 の 6 つの検索式の URL をメッセージに貼って送った（許可リストの条件は満たした）。6 つとも WebFetch がサイト側のエラー（client_error）で失敗し、ページの中身は 1 文字も取れなかった。zbMATH の側が自動取得を受け付けないとみられる（原因の見立ては構築側の推測）。
- 結論：zbMATH・MathSciNet の照合は、構築側の環境からは実施できない。著者側（ブラウザで開く）の作業として残る。候補 1・候補 3・方向 γ の地位と留保は変えない。

## §6 著者側の zbMATH 照合（2026-11-26 14:25 受領）

- 方法（著者側の報告）：zbMATH のウェブ画面はクラウドブラウザから Cloudflare の検証で塞がれ、テキスト取得も 403。§3 の 6 つの検索文字列をそのまま zbMATH Open の公開 API に通した（同じデータベース）。HKM の「cited by」はウェブの項目ページにしかなく API で取れないので、Semantic Scholar の引用一覧（16 件。OpenAlex の被引用数 16 と一致）で代えた。構築側は zbMATH を開けておらず、以下は著者側の報告をもとに構築側が書いた。
- 候補 1：
  - `ti:Terwilliger & (cyclic | cyclotomic | "Schur ring")`：2 件。Zbl 0944.05101（Ishibashi–Ito–Yamada、Eur. J. Comb. 20(5) 397–410 (1999)。有限体の上の円分スキームで T が中心化代数と一致するかの問題、Gauss 和に帰着、e = 2 で完全な答え。ℤ/N でも生成系でもない）。arXiv:2606.19095（Bastian–Humphries 2026。巡回群の上の軌道 Schur 環のうち T が almost commutative になるものの分類。著者側が要旨を直接確認）。
  - `"Terwilliger algebra" & generat* & (cyclic | "Schur ring")`：4 件。arXiv:2409.09167（Bastian–Humphries 2024）、Zbl 1533.05301（Maleki、C_n ⋊ C_2 の群スキーム、Discrete Math. 347(2) 2024）、Zbl 0969.11029（Shiratani–Yamada、Jacobi 和の有理性、Colloq. Math. 73(2) 1997）、arXiv:2609.06747（Lu 2026）。
  - 結論：この 2 検索の範囲で、ℤ/N 上の円分（軌道）Schur 環の T(0) の生成系を分類した項目は見つからなかった（不存在の証明ではない）。
- 候補 3：
  - `ai:hanaki.akihide & ti:Terwilliger`：3 件（Zbl 1479.05366（2021、modular）、Zbl 1235.05157（HKM、J. Algebra 343(1) 195–200 (2011)）、Zbl 1516.05228（Hanaki–Yoshikawa 2023））。
  - HKM の被引用（Semantic Scholar、16 件）：Kim 2011、Maldonado–Penazzi 2012、Kim 2015、Muzychuk–Xu 2016、Song–Xu–Zhou 2017、Xu 2017・2019、Balmaceda–Briones 2022、Watanabe 2023、Bastian–Humphries 2024、Bastian 2024、Yang ほか 2024（2 本）・2025・2026、Herman 2024、Bastian–Humphries 2026。題を見た範囲では輪積・積構造の後続で、商に沿った写像は見えない（本文・要旨は見ていない）。
  - `"Terwilliger algebra" & (homomorphism | quotient | fusion | "quotient scheme")`：16 件。題とレビューの範囲で、異なるスキームの T のあいだの準同型・商スキームに沿った写像を扱う項目は見つからなかった。近いもの 3 件：Curtin 2008（原始的でない Bose–Mesner 代数。T ではない）、Huang–Lee 2026（普遍代数から T への全射準同型。スキームのあいだの写像ではない）、Jiang 2022（1 つの T の中の商加群）。
- 方向 γ：`"Bost-Connes" & ("association scheme" | Terwilliger | "Schur ring")`：0 件（API の応答「No results found」。対照として "Bost-Connes" 単独は 57 件）。
- 書誌：Ishibashi–Ito の論文の 3 人目は Yamada, Mieko（Zbl 0944.05101、DOI 10.1006/eujc.1998.0276）。
- 限界：検索はこの 6 つの式に限る。レビューのない項目は題だけで判断している。「見つからなかった」は不存在の証明ではない。
- 地位：候補 1・候補 3・方向 γ の地位は変えない。CLAUDE.md §3 の留保のうち未了は MathSciNet だけになり、外部（応募書類を含む）で新規性として使わない扱いは変わらない。（後注 2026-11-26 15:0x、統合照合 XII の指摘を受けて構築側が足した：「外部で新規性として使わない扱い」は CLAUDE.md §3 では候補 3 についてのもの。候補 1 に同じ扱いを採るかは著者に確かめている（索引 §6）。）（後注 2026-11-26 15:5x、著者の決定：候補 1 に「MathSciNet の照合が済むまで、外部（応募書類を含む）で新規性として使わない」扱いを採るかという構築側の問いに、著者は「採らない」と答えた。この留保は候補 3 だけに付く。候補 1 の地位（［新規候補］の範囲は合成数の N、確信度：中、「小さいノートの水準」）は変わらない。）CLAUDE.md の §3 の「MathSciNet・zbMATH は未実施」の文面は、著者のファイルなので構築側では書き換えていない。（後注 2026-11-26 14:5x、統合照合 XI の指摘を受けて構築側が足した：その後 14:35 に著者が「MathSciNet は未実施。zbMATH は 2026-11-26 に実施済みで、候補1・候補3・方向γのいずれについても地位を変える項目はなかった」と書き、構築側がこの文を CLAUDE.md の §2・§3 の 3 か所に後注として足した。元の文面は残っている。）

## §7 MathSciNet の扱い（2026-11-26 16:0x、著者の決定）

- 構築側が MathSciNet の利用の道（購読は機関単位で個人には一般に使えない、大学図書館の学外利用、所属のある共同研究者、やめる）を示し、著者は「MathSciNet はやめる」と答えた（16:01）。
- 続けて構築側が、候補 3 の留保（MathSciNet が済むまで外部で新規性として使わない）が解けなくなることを示して尋ね、著者は選択肢「留保を解く」を選んだ。選択肢の文面は「照合は zbMATH と HKM の本文で打ち切り。外部で使うときは『MathSciNet は未実施』と確信度（低〜中）を必ず添える」。
- 記録：CLAUDE.md §2・§3、材料索引 5.1・§6、下書き rev 119（5.1、著者側の作業の表、チェックリスト）、台帳 L33 の追記。
- 候補 1（留保はもともと付けない、15:5x の決定）・候補 3・方向 γ の地位は変えない。「見つからなかった」は不存在の証明ではない。

- 追記（2026-11-26 16:38、著者の決定）：候補 3 の留保は付いたまま（外部で新規性として使わない）。MathSciNet をやめたので条件は満たされないまま残る。上の「留保を解く」はこの決定で置き換わった。候補 1 には留保を付けない（15:5x）。
