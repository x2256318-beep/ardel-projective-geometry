# 監査 2026-11-26・照合 A の出力（言い直しテストと対照群）

（照合者の最終報告の全文を写した。依頼文は `../requests/request_A.md`、時刻は `meta.txt`。入力はコメントを取り除いた PAG256〜PAG268 で、`../inputs/lean_stripped/`。）

## 照合者 A の報告：PAG256〜PAG268（コメント除去版）

**読んだ範囲と前提**：13 ファイルの形式文と定義を全部読んだ（抽出スクリプトを使用。証明本体は読んでいない）。Lean はビルドしていない（入力に `sorry` の文字列がないことだけ grep で確認）。定義は前のファイル（PAG15・19・21・23・25・27・28・29・201・205・206・218・232・254・258）から grep で引いた。grep の出力に PAG206・218・232 の冒頭コメントが偶然混ざったが、判定の根拠には使っていない。

---

### 1. 主な定理の言い直し

**PAG256（Hartley 核とルート数）**
- `hartley_eq_of_isPrimitive`、`hartley_one`：cas 核 cos+sin による Hartley 変換で原始指標 χ を写すと ε(χ)τ(χ)χ̄(y)（ε は偶で 1、奇で −i）。分野：ガウス和の分離性。文献：Davenport『Multiplicative Number Theory』9 章、Iwaniec–Kowalski §3.4（確信度：高）。cas 核は Bracewell『The Hartley Transform』（確信度：中。指標との関係は分離性から直ちに出る）。
- `rootNum_eq`、`normSq_rootNum`：`rootNum` は L(s,χ) の関数等式に出る古典的ルート数 W(χ)=τ(χ)/(i^a√N) そのもので、原始指標では |W|=1。文献：同上（確信度：高）。
- `JH_eq_rootNum_mul_any`：JH は指標 χ を W(χ)χ に写す。上の 2 つの直ちの帰結。
- `removal_counterexample*`：原始でない場合の反例。自明指標では τ(1_N)=μ(N)（N=2 で 1、N=4 で 0）。ラマヌジャン和 c_N(1)=μ(N)、古典（確信度：高）。

**PAG257（単数上の作用素 T）**
- `TopL_charU`、`ip_charU`、`isCompl_Vprim_Vimprim`：T は指標基底で対角、固有値は W(χ)。原始指標の張る空間と非原始指標の張る空間は直交補空間。分野：指標の直交性・有限アーベル群上のフーリエ解析。文献：Davenport、Montgomery–Vaughan 9 章（確信度：高）。
- `unitary_Vprim`、`TopL_eq_of_A1`：T は Vprim 上でユニタリ。固有値を指定すれば作用素は一意。線形代数（|W|=1 と基底の直交性）から。
- `not_isometry_Vimprim_prime`、`Vprim_two`：非原始指標の上では |τ| ≠ √N なので等長でない。法 2 には原始指標がない。古典。

**PAG258（A1 の位相の作用素 U_N と帰納極限 U_∞）**
- `UA1_charU`、`ip_UA1`、`UA1_comp_pullL`、`UA1_unique`：U_N は各指標を「その指標を誘導する原始指標のルート数」倍する対角作用素で、ユニタリ、引き戻し (ℤ/M)^× → (ℤ/N)^× と可換。可換性は W(χ*) が導手だけで決まることによる（定義から）。分野：Dirichlet 指標の導手と誘導。
- `Uinf_unique`、`Uinf_bijective`、`ipLim_Uinf`、`eq_zero_of_ipLim_self`：(ℤ/N)^× 上の関数空間の整除順序での帰納極限は Ẑ^× 上の局所定数関数の空間で、φ(N) で正規化した内積は確率 Haar 測度による L² 内積。U_∞ はその上の χ ↦ W(χ)χ のユニタリ作用素。文献：Ramakrishnan–Valenza『Fourier Analysis on Number Fields』（確信度：中〜高）。
- `iSupIndep_condPart`、`condPart_eq_map`：導手ごとの直交直和分解。導手 q の成分は法 q の原始指標の空間の引き戻し。新形式・旧形式に当たる古典的分解（確信度：高）。
- `UA1_star`：W(χ̄) は W(χ) の複素共役。古典（Davenport 9 章、確信度：高）。

**PAG259（付値と log の像の稠密／離散）**
- `eq_of_padicValRat_eq`、`eq_prod_of_support`：一意素因数分解。
- `dense_closure_log_primes`、`irrational_log_div_log`：log r/log p は無理数なので ℤlog p + ℤlog r は ℝ で稠密。Kronecker 型の古典（Hardy–Wright、確信度：高）。
- `dense_imgST_iff`、`isClosed_discrete_imgST`、`threshold_iff`：S 単数群（S は有限個の素数）を (log, T での付値) で ℝ×ℤ^T に写す（T ⊆ S）。像が稠密 ⇔ S∖T に素数が 2 つ以上。それ以外は閉じた離散集合。分野：S 単数の埋め込みの離散性と Kronecker の稠密性。文献：Cassels–Fröhlich 2 章、Tate の学位論文（確信度：中〜高。この「しきい値」の形で書いた文献は確認していない）。
- `dense_rho_image`、`isClosed_discrete_rhoBox_image`：ℚ_{>0} を ℝ×ℤ^{素数} に写すと、直積位相では像は稠密、離散位相（box 側）では閉じた離散集合。後者は「ℚ^× はイデール群で離散」を I_ℚ/Ẑ^× の側で見たもの（確信度：中〜高）。

**PAG260（互いに素な二つの法でのガウス和・ルート数）**
- `gaussSum_prodChar`：τ(χ₁χ₂) = χ₁(N)χ₂(M)τ(χ₁)τ(χ₂)。古典。文献：Iwaniec–Kowalski §3.4、Berndt–Evans–Williams『Gauss and Jacobi Sums』（確信度：高）。
- `rootNum_prodChar`、`phaseA1_prodChar`：W(χ₁χ₂) = (符号)·χ₁(N)χ₂(M)·W(χ₁)W(χ₂)。符号は両方奇なら −1、それ以外 1（i^a の正規化から）。Tate の局所定数で読むと χ₁(N)χ₂(M) は不分岐成分の値、符号は無限素点の因子。文献：Tate「Number theoretic background」（Corvallis 1979）（確信度：中）。数値で確認：法の組 6 つ・80 組で不一致 0。
- `isPrimitive_prodChar`：導手の乗法性。古典。

**PAG261（有限個の法へのリスト版）**
- `gaussSum_listChar`、`cross_eq_formI/II`、`rootNum_listChar`：上の式を帰納で多因子にしたもの。符号は (−1)^{k(k−1)/2}（k は奇な因子の数）で、i^{−k} と i^{−(k mod 2)} の差に当たる。
- `gaussSum_primeFactors`：素冪成分へのガウス和の分解。Berndt–Evans–Williams 1 章（確信度：中〜高）。
- `isPrimitive_listChar_iff`、`exists_listChar`：CRT による指標群の直積分解。古典。

**PAG262（殻代数の持ち上げと二分法）**
- 前提：殻代数 `shellAlg` は ⟨D_s, E_s⟩ で、ℤ/N 上の円分スキーム（単数群の軌道）の Terwilliger 代数 T(0)。D_s は双対冪等元 E_s^*、E_s は Bose–Mesner 代数の原始冪等元に当たる。
- `shellLift_*`、`exists_compatible_hom`：gcd(a,b)=1 のとき、S ↦ S⊗1 を T(A_a)⊗T(A_b) ≅ T(A_ab) で送る写像。引き戻しと両立し、D_s ↦ Σ_{u|b} D_{su}、E_s ↦ Σ_{u|b} E_{su}。直積スキームのテンソル分解からの帰結。文献：Hanaki–Kim–Maekawa（直積・wreath 積の Terwilliger 代数。確信度：中、本文未確認）。
- `dTop_eTop_dTop`：E_0^* E_0 E_0^* = |X|^{-1} E_0^*。Terwilliger の基本関係。文献：Terwilliger 1992（J. Algebraic Combin. 1。確信度：中〜高、補題番号は未確認）。
- `no_compatible_hom`、`exists_compatible_hom_iff`：N | M のとき、単位元を保ち、引き戻しと両立し、D を D の span に・E を E の span に送る代数準同型 T(0)_N → T(0)_M が存在 ⇔ gcd(N, M/N)=1。存在の側は上の帰結。不在の側は 2 で扱う。

**PAG263（ユニタリ約数の順序と一意性）**
- `udvd_trans`、`not_isDirected_udvd`、`udvd_iff_inLayer`：UDvd はユニタリ約数（N ∥ M）の関係。反射的・推移的で有向でない（p と p² の両方を ∥ で割る数はない）。文献：E. Cohen, Math. Z. 74 (1960)（確信度：高）。
- `fC_dind`、`fC_geps`：フーリエ共役は D_s と E_s を入れ替える。ℤ/N の円分スキームの自己双対性（形式的自己双対）。文献：Bannai–Ito『Algebraic Combinatorics I』の並進スキームの双対（確信度：中）。
- `existsUnique_compatF_iff`、`compatF_iff_eq_shellLift`、`canon_comp`：フーリエ共役との可換性を足すと、両立写像は存在すれば `shellLift` ただ一つで、存在 ⇔ gcd=1。これらはユニタリ約数の前順序の上の関手をなす。
- `twLift_ne_shellLift`、`not_existsUnique_compat`：法 2 のとき、x ↦ (−1)^x による共役は D を固定し E_1 と E_2 を入れ替える A_2 の自己同型。これで捩った S⊗E_top + τ(S)⊗(1−E_top) も両立写像になり、一意性が崩れる。
- `sqLim_of_injective`：無平方数（素数の有限集合）の上の系は有向で、極限は単位元に関する制限無限テンソル積 ⊗'_p A_p にあたる（確信度：中。ただし Lean は ℂ 加群としての極限で、代数構造は入っていない）。

**PAG264（角の写像）**
- `cornerOp_mul`、`cornerHom_comp`、`cornerHom_self`、`cornerHom_one_ne_one`：φ(S) = ιSι^*（ι は正規化した引き戻しの等長写像）。等長写像 V に対し S ↦ VSV^* が単位元を保たない準同型になる一般論の場合。
- `cornerOp_one`、`cornerOp_geps`：φ(1) は「ℤ/N から来る旧部分」への射影 Σ_{(M/N)|s} E_s で、E_s ↦ E_{(M/N)s}。商スキームの冪等元の角。群環の側では Bost–Connes の ρ_n(e(r)) = (1/n)Σ_{ns=r} e(s)（ρ_n(1) = e_n が射影）に対応する見込み。文献：Bost–Connes 1995（Selecta Math.）。確信度：低〜中（本文の式はこのセッションで確認できなかった）。
- `existsUnique_corner`：引き戻しとの両立と φ(1) の値を指定すると写像は一意。
- `cornerOp_dind_not_mem_span`：(2,4) で D の像が D の span に入らない（具体例）。

**PAG265（角の直極限）**
- `ofCorner_injective`、`exists_local_unit_finset`、`not_exists_left_one`：単位元を保たない移行写像の直極限は、局所単位元を持つが左単位元を持たない非単位的代数。局所単位元を持つ代数の一般論。文献：Ánh–Márki, Tsukuba J. Math. 11 (1987)（確信度：中）。

**PAG266（Jacobi 和と赤道の係数）**
- `conj_Jhat_eq_gauss`：J(χ₁,χ₂) = τ(χ₁)τ(χ₂)/τ(χ₁χ₂)（素冪の法、3 つとも原始）を |τ|² = N で書き換えたもの。Berndt–Evans–Williams 2 章（確信度：高）。
- `conj_Jhat_eq_rootNum`：その W 版。両方奇なら符号 −1。直ちの帰結。数値で確認：法 6 つ・370 組で不一致 0。
- `conj_Jhat_sq_eq_rootNum`、`equator_intertwine_rootNum`、`equator_intertwine_proj_rootNum`：P¹(ℤ/p^K) の二つのチャートでの畳み込みの比は J̄/J = (J̄/√N)²。J(χ̄₁,χ̄₂) = J(χ₁,χ₂) の複素共役から。

**PAG267（P¹(ℤ/N) の射影系）**
- `red_comp`、`red_surjective`、`red_Wproj`：P¹(ℤ/M) → P¹(ℤ/N) は関手的で全射、反転 [a:b] ↦ [b:a] と可換。全射性は SL₂(ℤ) → SL₂(ℤ/N) の全射性と同種の事実。文献：Shimura『Introduction to the Arithmetic Theory of Automorphic Functions』1 章（確信度：高）。
- `ofP_injective`、`WL_WL`：関数空間の帰納極限は副有限集合 P¹(Ẑ) = lim P¹(ℤ/N) 上の局所定数関数の空間で、W はその上の対合。
- `resL_WL`、`resL_surjective`：赤道 {[x:1] : x 単数} への制限は W を x ↦ x^{-1} に移す。
- `extE_compat_iff`、`not_exists_extL`：0 拡張が両立 ⇔ rad(b) | a（素数の台が増えない）。極限の上に拡張写像はない。言い換えると、Ẑ^× は P¹(Ẑ) の中で閉だが開でない（無限個の真の開閉集合の直積のため）。位相の初等的事実（確信度：中〜高）。

**PAG268（P¹ 上の指標関数）**
- `chiPt_Wproj`、`chiPt_torus`：[a:b] ↦ χ(a)χ̄(b) は well-defined。対角トーラス diag(u,1) で χ(u) 倍、反転で χ^{-1} に移る。トーラスの固有関数で、GL₂ の主系列の有限環版に近い（確信度：低〜中）。
- `extChi_changeLevel`、`resE_extChi`：原始指標を経由すると法の変更と両立する。
- `ketS_proj_zero_eq`：PAG29 のケットは法 p^c からの指標関数を正規化して引き戻したもの。定義の書き換え。

### 2. 言い直せない、または「既知の定理の特別な場合・直ちに出る帰結」と言えない定理

「新しい概念が要る」定理は見つからなかった。ただし、既知の定理の引用だけでは出ず初等的な議論が要るものが次の 5 つ。
1. **PAG262 `no_compatible_hom`（不在の側）**：直積スキームの定理は存在の側しか答えない。不在の側は Terwilliger の関係 E_0^*E_0E_0^* = |X|^{-1}E_0^* と x = M/p（x² = 0）を使う初等的議論による。商 ℤ/M → ℤ/N に沿った単位的写像を扱った文献は、今回の検索の範囲では見つからなかった（不存在の証明ではない）。
2. **PAG263 `twLift`／`not_existsUnique_compat`**：「A_2 に D を固定し E を入れ替える自己同型がある」こと自体は自明。その捩れで両立写像の一意性が崩れることを書いた文献は確認していない。
3. **PAG263 `existsUnique_compatF_iff`**：1 と、フーリエ共役で E の像が決まることの組み合わせ。組み合わせとしては直ちに出る。
4. **PAG264 `existsUnique_corner`**：一般論（等長写像による角）の内容に、「像が A_M に入ること」と「一意性」が加わる。どちらも初等的だが、特定の文献の系とは言えなかった。
5. **PAG267 `extE_compat_iff`**：同値条件 rad(b) | a の形で書いた文献は確認していない。中身は上の位相の事実。

探したもの：Terwilliger の関係、Bost–Connes の ρ_n、Hartley 変換と Dirichlet 指標（ウェブ検索 3 回・取得 1 回。直接の答えは得られなかった）。

依存の観察（指摘として）：`rootNum` は定義に i^a を含み、Hartley 核の因子 parFac = (−i)^a がそれを打ち消すように効く。したがって JH の固有値が W(χ) になるのは核の選び方による構成上の帰結。`UA1` は固有値 W(χ*) を定義として入れており、ユニタリ性・両立・一意性は |W| = 1 と「W が導手だけで決まる」ことから出る。

### 3. 対照群テスト（ℤ/N を 𝔽_q[t]/(f) に置き換える）

| 定理 | 見込み | 理由 |
|---|---|---|
| 256 `hartley_eq_of_isPrimitive`、`rootNum` の i^a | 成り立たない（この形では） | cas 核と i^a は実数の無限素点（Γ 因子）から来る。𝔽_q(t) では符号の型が q−1 通りあり、因子の形が違う。 |
| 256 `normSq_rootNum` | 成り立つ | 原始指標で \|τ\|² = q^{deg f}（Rosen『Number Theory in Function Fields』）。 |
| 256/257 法 2・法 4 の反例、`Vprim_two` | 成り立つ（類似あり） | 𝔽_2[t]/(t) にも原始指標がない。「2」の特別さは剰余体の大きさ 2 で、ℚ 固有ではない。 |
| 257/258 全般（ユニタリ性・両立・極限・導手分解） | 成り立つ | 指標の直交性と \|W\| = 1 だけを使う。 |
| 259 `dense_imgST_iff`、`dense_rho_image` | **成り立たない** | 関数体ではノルムが q^ℤ で log が通約可能。像は常に閉じた離散集合で、稠密は起きない。log p/log r が無理数であること（ℚ の無限素点）を本質的に使う。 |
| 259 `isClosed_discrete_rhoBox_image` | 成り立つ | 主イデールの離散性は大域体に共通。 |
| 260/261 の CRT 交差項 χ₁(N)χ₂(M) | 成り立つ | 互いに素な多項式で同じ形。 |
| 260/261 の符号（両方奇で −1、(−1)^{k(k−1)/2}） | 成り立たない（この形では） | i^a の正規化、つまり無限素点に固有。 |
| 262 存在の側／不在の側 | 存在：成り立つ。不在：成り立つ見込み（不明寄り） | 直積スキームの分解は一般論。不在の議論は P² \| M での x² = 0 と数え上げで、形のうえでは移る（未確認）。 |
| 263 ユニタリ約数・有向でない・CompatF の一意性 | 成り立つ | 環論的性質だけ。 |
| 263 `twLift` の非一意性 | 剰余体 𝔽_2 の素点でだけ成り立つ | q = 2 の次数 1 の素点（t と t+1）でも同じ捩れ。ℚ 固有ではなく「剰余体の位数 2」に固有。 |
| 264/265 | 成り立つ | 有限アーベル群の商と等長写像の一般論。 |
| 266 符号つき版 | 成り立たない（この形では） | i^a による。 |
| 266 2 乗版・赤道の絡み | 成り立つ見込み | 2 乗で正規化の符号が消える（(i^a)² = χ(−1) が乗法的）。 |
| 267/268 | 成り立つ | P¹ の副有限な性質と CRT だけ。 |

ℚ に固有の算術を実際に使っている文：259 の稠密性（log の非通約性）と、256・260・261・266 の i^a 由来の符号（無限素点）。「2 の特別さ」（256・257・263）は ℚ 固有ではなく 𝔽_2[t] にも同じ類似がある。

### 4. 全体の判定（二つの問いを分けて書く）

**(a) 新しい概念が要ったか**：要らなかった。13 ファイルの主な定理は、ガウス和・ルート数、指標の直交性、Terwilliger 代数 T(0)、直積スキーム、ユニタリ約数、帰納極限・局所単位元、P¹(ℤ/N) の副有限系の言葉ですべて言い直せた。

**(b) 新しい内容がないか**：(a) からは結論できない（Lean で書けた定理は定義上すべて言い直せる）。文献に直接の該当を確認できなかった内容は 2 の 5 項目で、特に PAG262 の不在の側と PAG263 の 2 進の捩れによる非一意性。どちらも初等的な計算の水準で、文献照合は未完了。

ほかに確かめられなかったこと：「確信度」と書いた文献対応のうち本文で確認したものはない（すべて知識による見込み。特に Bost–Connes の ρ_n の式、Hanaki–Kim–Maekawa、Terwilliger 1992 の補題番号）。Lean のビルド。数値で確かめたのは 2 件（PAG260 `rootNum_prodChar`、PAG266 `conj_Jhat_eq_rootNum`）だけ。

### 使ったツールと読んだ範囲

ツール計 13 回（Bash 9：抽出・定義の grep 3 回・数値照合 1 回・sorry の確認 1 回など、WebSearch 3、WebFetch 1：arXiv:math/0409520 の前半 10 万字、該当章まで届かず）。Read は 0 回。入力 13 ファイルの宣言文と定義すべてを読み（証明本体は読まず）、前のファイルは定義の行だけ grep で引いた（PAG15・19・21・23・25・27・28・29・201・205・206・218・232・254）。notes・records・handoff などは読んでいない。計算ファイル：`/tmp/audit_A/ext.py`、`/tmp/audit_A/num.py`。検索結果（直接の答えは得られなかった）：arXiv:2301.08366、arXiv:math/0307269、arXiv:math/0409520、arXiv:0711.0477、Wikipedia の Hartley transform・Gauss sum。
