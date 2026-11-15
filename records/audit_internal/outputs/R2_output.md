## 1. 表

| 宣言 | 判定 | 前の宣言（ファイル::名前） | 根拠（1 行） | 確信度 |
|---|---|---|---|---|
| PAG255::dense_closure_allPrimes | D | | unitSys×ℝ 上の稠密性は前の鎖にない。同じファイルの dense_closure_primeGens の L=1 の場合 | 中 |
| PAG255::dense_closure_primeGens | D（一般化） | 一般化元：PAG253::exists_cls_near、PAG253::exists_cls_near_of_dvd（参考：PAG254::dense_logSet_coprime） | レベル N ごとの「類と対数差の同時近似」を、射影系全体での稠密性に強めたもの（生成する素数は p∤L に限る） | 中 |
| PAG255::exists_level | D | | 両立系の開集合が一つのレベルの値で決まるという位相の補題。unitSys もその位相も前の鎖にない | 中 |
| PAG255::exists_mem_closure_level | D | | PAG253::kUnit_mem_of_prime・invariant_kUnit と同じ型の素因数分解の帰納法を unitSys の closure で行う。数行では出ない | 中 |
| PAG255::kUnit_congr | C | PAG253::kUnit_mul_natCast、PAG253::kUnit | kUnit m·m=1、kUnit n·n=1、(m:ZMod N)=(n:ZMod N) から逆元の一意性で数行。定義を展開して Units.ext でも出る | 中 |
| PAG255::pow_dvd_pow_factorial | D | | a ≤ p^a ≤ N ≤ K ≤ K! を使う初等的な補題。読んだ範囲に対応するものはない | 中 |
| PAG255::pow_factorial_modEq | D | | p 部分と p と素な部分に分け、CRT と Euler の定理を使う。前の鎖に見つからない | 中 |
| PAG255::pow_factorial_modEq_one | D | | φ(M') ∣ K! を使った Euler の定理。前の鎖に見つからない | 中 |
| PAG255::primeCls | D | | wNat を使う新しい定義 | 中 |
| PAG255::primeCls_mem | D | | 同じファイルの wNat_cast_eq・kUnit_congr と PAG253::unitsMap_kUnit で示す。前の鎖だけでは出ない | 中 |
| PAG255::primeCls_of_coprime | D | | 同じファイルの wNat_cast_of_coprime・kUnit_congr からならすぐ出るが、前の鎖だけでは出ない | 中 |
| PAG255::primeGens | D | | 新しい定義 | 中 |
| PAG255::primeSys | D | | 新しい定義 | 中 |
| PAG255::primeSys_unique | D | | unitSys の元の一意性。前の鎖にない | 中 |
| PAG255::unitSys | D | | 両立系（射影極限）としての部分群。同じものを定義した宣言は前の鎖に見つからない | 中 |
| PAG255::unitsMap_primeCls_pow | D | | wNat ≡ 1 (mod p^a) から p^a 成分が 1 になる計算。前の鎖にない | 中 |
| PAG255::units_eq_of_coprime_parts | C | PAG196::crt_unique | crt_unique（ZMod N の元、castHom 版）を単元に移すだけ。Units.ext、unitsMap の値＝castHom、NeZero N から NeZero A・B を作る | 高 |
| PAG255::wNat | D | | 新しい定義 | 中 |
| PAG255::wNat_cast_eq | D | | 同じファイルの pow_factorial_modEq から出る。前の鎖だけでは出ない | 中 |
| PAG255::wNat_cast_of_coprime | D | | 同じファイルの pow_factorial_modEq_one（a=0）から出る。前の鎖だけでは出ない | 中 |
| PAG255::wNat_coprime | D | | 新しい補題 | 中 |
| PAG256::JH | D | | Hartley 変換を単元の逆で評価して √N で割る、新しい定義 | 中 |
| PAG256::JH_eq_rootNum_mul | C | PAG3::hartley_char、PAG3::casK、PAG2::parity_weight | hartley_char で DFT 型の和にし、単元による和の置換（Mathlib の gaussSum_mulShift 相当）と根数への換算をする。材料が多く、「数行」の上限 | 低 |
| PAG256::JH_eq_rootNum_mul_any | C | 同上 | 同上。u が単元なので原始性は要らない | 低 |
| PAG256::casKer | A | PAG3::casK | casK t = cas(stdAddChar t) = Re+Im = cos(2π·t.val/N)+sin(2π·t.val/N)。型も値も同じ（定義の書き方が違うので、一致の証明には数行かかる） | 高 |
| PAG256::casKer_eq | C | PAG3::casK_even_part、PAG3::casK_odd_part | 2 式を足して 2 で割ると (1−I)e(t)+(1+I)e(−t) になる。casKer=casK の換算が要る | 中 |
| PAG256::exists_primitive_even_five | C | PAG119::Lc、PAG119::Lc_ne_one、PAG171::primitive_of_ne_one、PAG167::Lc_neg_one_pow | χ=Lc 5 とする。≠1、素数レベルなので原始、Lc 5 (−1)=(−1)^2=1 なので偶 | 高 |
| PAG256::exists_primitive_odd_three | C | 同上の 4 宣言 | χ=Lc 3 とする。≠1、原始、Lc 3 (−1)=(−1)^1 なので奇 | 高 |
| PAG256::hartley | D | | 変換として定義した宣言は前の鎖にない。PAG3::hartley_char の左辺 Σ casK(x·y)·χ y は、f=χ の場合の同じ和 | 中 |
| PAG256::hartley_eq_of_isPrimitive | C | PAG3::hartley_char、PAG2::parity_weight、PAG203::dft_rk | hartley_char で (if Even then 1 else −I)·Σ e(xy)χ(x) にし、原始指標の DFT 公式（dft_rk の v=1 の場合、または Mathlib）を代入する | 低 |
| PAG256::hartley_eq_zero_of_not_isUnit | C | PAG3::hartley_char、PAG203::dft_rk | 上と同じ流れで、y が非単元なので χ⁻¹(y)=0 | 低 |
| PAG256::hartley_one | C | PAG3::hartley_char、PAG2::parity_weight、PAG3::casK | x=1 の hartley_char と r=1 の parity_weight を使い、和を gaussSum に書き換える | 中 |
| PAG256::hartley_units_inv | C | PAG3::hartley_char | x=u⁻¹ と x=1 の hartley_char を、単元による和の置換でつなぐ。置換だけで直接示すこともできる | 低 |
| PAG256::inv_apply_neg_one | A | PAG81::inv_neg_one、PAG25::chi_inv_neg_one、PAG9::inv_apply_neg_one | 同じ文。PAG9 は MulChar (ZMod N) ℂ 版で、DirichletCharacter の定義上同じ型 | 高 |
| PAG256::inv_apply_units_inv | B | PAG3::apply_inv_eq_inv_apply | χ⁻¹ と ↑u に適用し、inv_inv と ZMod.inv_coe_unit を使えば 1 行 | 高 |
| PAG256::isPrimitive_of_prime_of_ne_one | A | PAG171::primitive_of_ne_one、PAG32::prim_level_p_iff | PAG171 と同じ文（χ が明示か暗黙かの違いだけ）。PAG32 は iff 版 | 高 |
| PAG256::neg_one_mul_self | A | PAG29::chi_neg_one_sq'、PAG9::chi_neg_one_sq | 同じ文。PAG9 は MulChar 版 | 高 |
| PAG256::normSq_rootNum | C | PAG16::normSq_gaussSum | normSq(gaussSum)=N を normSq((if…)·√N)=N で割る計算 | 高 |
| PAG256::parFac | C | PAG198::gs、PAG198::neg_one_sq_eq（参考：PAG2::parity_weight） | 値は (gs χ)⁻¹（χ(−1)=±1 で場合分け）。式は parity_weight の左辺の r=1 と ring で一致する | 中 |
| PAG256::parFac_of_even | D（一般化） | 一般化元：PAG2::parity_weight | r=1 の parity_weight と if_pos で出るが、T は [NeZero N] を外している。中身は定義からの 1〜2 行の計算 | 中 |
| PAG256::parFac_of_odd | D（一般化） | 一般化元：PAG2::parity_weight | 同上（Odd から ¬Even を足す） | 中 |
| PAG256::removal_counterexample | D | | hartley の具体的な値は新しい。第 1 連言だけは PAG195::ne_one_of_isPrimitive（N=2）からすぐ出る | 中 |
| PAG256::removal_counterexample_four | D | | 第 1 連言は PAG72::exists_prim4 と同じ文、第 2 連言は PAG195::ne_one_of_isPrimitive から出る。hartley と rootNum の値は新しい | 中 |
| PAG256::removal_counterexample_normSq | D | | 自明指標 mod 2 の rootNum の値。PAG120::psi_two_one を使えば短い計算 | 中 |
| PAG256::rootNum | B | PAG196::zN、PAG198::gs（参考：PAG2::Wpow） | rootNum χ = zN χ / gs χ。χ.Even の定義が χ(−1)=1 なので、割り算の並べ替えだけで済む。値は Wpow χ 1 とも一致 | 中 |
| PAG256::rootNum_eq | C | PAG2::parity_weight | parFac を r=1 の parity_weight で if 式にし、偶奇で場合分けする（1/I=−I）。rootNum χ = Wpow χ 1 と同値 | 中 |
| PAG256::sum_mul_stdAddChar | D | | 左辺は PAG4::F χ y と同じ和だが、gaussSum(mulShift) との等式は前の鎖に見つからない。Mathlib の定義を展開すれば出る | 中 |
| PAG256::sum_mul_stdAddChar_neg | B | PAG3::sum_neg_twist | x=1 の場合に gaussSum を展開し、積を交換すれば 1 行 | 高 |

## 2. A・B・C の件数と一覧

- **A：4 件**：PAG256::casKer、inv_apply_neg_one、isPrimitive_of_prime_of_ne_one、neg_one_mul_self
- **B：3 件**：PAG256::inv_apply_units_inv、rootNum、sum_mul_stdAddChar_neg
- **C：14 件**
  - PAG255::kUnit_congr、units_eq_of_coprime_parts
  - PAG256::casKer_eq、exists_primitive_even_five、exists_primitive_odd_three、hartley_eq_of_isPrimitive、hartley_eq_zero_of_not_isUnit、hartley_one、hartley_units_inv、JH_eq_rootNum_mul、JH_eq_rootNum_mul_any、normSq_rootNum、parFac、rootNum_eq
- 参考：D は 27 件で、うち「一般化」が 3 件（dense_closure_primeGens、parFac_of_even、parFac_of_odd）。
- ファイル別：PAG255 は C 2・D 19、PAG256 は A 4・B 3・C 12・D 8。
- 境界にある判定は次のとおりです。
  - C のうち確信度「低」の 5 件（JH の 2 件、hartley_eq_of_isPrimitive、hartley_eq_zero_of_not_isUnit、hartley_units_inv）は、「数行」を厳しく読めば D になりえます。
  - parFac_of_even・parFac_of_odd は [NeZero N] を外しただけの一般化です。依頼文の規則どおり D に数えました。この差を無視すれば B・C 相当です。

## 3. 気づいたこと

**Part 252 の Hartley 部分は PAG3 と大きく重なっています。** PAG3 の section Hartley に次のものがありました（候補リストには一つも載っていませんでした）。
- casK（＝casKer）
- casK_even_part と casK_odd_part（→ casKer_eq）
- sum_neg_twist（→ sum_mul_stdAddChar_neg）
- hartley_char（Hartley 変換の偶奇分解。hartley_one、hartley_eq_of_isPrimitive、JH_eq_rootNum_mul_any の核）
- apply_inv_eq_inv_apply（→ inv_apply_units_inv）

PAG256 で新しいのは、変換としての定義（hartley、JH）、根数での正規化と |rootNum|=1、反例（removal_*）の部分と見られます。

**根数の三重定義。** PAG2::Wpow χ 1、PAG196::zN χ / PAG198::gs χ、PAG256::rootNum は同じ値です。PAG198::gs と PAG256::parFac は、χ(−1)=±1 のもとで互いに逆数です。

**前の鎖どうしの重複（読んだ範囲で見つけたもの）。**
- χ⁻¹(−1)=χ(−1)：PAG9::inv_apply_neg_one（MulChar 版）、PAG25::chi_inv_neg_one、PAG81::inv_neg_one（後の 2 つは同じ文）
- χ(−1)²=1：PAG9::chi_neg_one_sq、PAG29::chi_neg_one_sq'
- 素数レベルの原始性：PAG32::prim_level_p_iff から PAG171::primitive_of_ne_one が直ちに出る（B）
- 同じ定義：PAG15::shellSize と PAG19::sz
- 同じ instance：PAG8::neZero_pow と PAG9::neZero_pow'。PAG28::neZeroPow はその一般化
- PAG30::kk c = PAG32::gp 2 c
- 同じ文：PAG247::conv_single_apply と PAG250::conv_single
- PAG247::testFn N = PAG248::pairFn N 1 = PAG250::twoPt N (−1)
- レベル 1 の Gauss 和が 1：PAG195::z_level_one、PAG196::zN_level_one、PAG203::gaussSum_level_one
- PAG184::zOf は PAG196::zN の素数レベルの場合と同じ式
- PAG254::dense_logSet_coprime は PAG253::exists_cls_near（a=1）から直ちに出る（B）
- PAG253::eq_of_prime_invariant' は eq_of_prime_invariant の N=M の場合
- −1 を −1 に写す補題が 3 つ：PAG37::unitsMap_neg_one、PAG198::castHom_neg_one、PAG204::changeLevel_neg_one

**同じファイルの中の冗長。**
- PAG256::JH_eq_rootNum_mul は JH_eq_rootNum_mul_any の特殊化で、原始性の仮定は不要です。
- PAG255::dense_closure_allPrimes は dense_closure_primeGens の L=1 の場合です。
- PAG256::hartley_eq_zero_of_not_isUnit は hartley_eq_of_isPrimitive から χ⁻¹ y=0 で直ちに出ます。

**候補の選び方の弱点。** 型に現れる定数の近さで選んでいるため、名前の違う同じ概念を拾えていません。
- PAG3（casK・hartley_char・sum_neg_twist・apply_inv_eq_inv_apply）を拾えていません。
- units_eq_of_coprime_parts に対する PAG196::crt_unique（unitsMap ではなく castHom で書かれている）も拾えていません。
- exists_primitive_* に対する PAG119::Lc・Lc_ne_one・PAG167::Lc_neg_one_pow も同様です。
- rootNum については zN は載っていましたが、gs が漏れていました。
- PAG255 の階乗の補題と定義の候補は、ほぼ無関係でした。
- 定義を展開した形や、式の形を正規化したもので照合すれば改善できると思います。

**照合の限界。**
- PAG255 の instance 2 件（instTopUnitsLevel、instDiscreteUnitsLevel）は targets.md にないので、判定していません。
- PAG255 が open しているのは PAG.Part253 だけです。この事実と、PAG255 が (ZMod N)ˣ の位相を自分で定義していることから、射影系の先行定義はないと推測していますが、証明ではありません。
- D の判定はどれも「次節の範囲で見つからなかった」という意味です。

## 4. 使った検索語の一覧

**Grep は使っていません。** この実行環境のツール一覧に Grep がありませんでした。シェルの grep は禁止なので、これも使っていません。使ったのは Read だけで、3 つの場所の外は読んでいません。書き込み・シェル・ウェブ・エージェントの起動もしていません。

**全文を読んだ範囲。** targets.md、candidates.md、statements_all.txt の次の行です（計約 6,830 行で、全 22,569 行の約 30%）。
- 1–2006（PAG2〜PAG28 の途中）
- 6560–6900（PAG116〜PAG121）
- 8300–9100（PAG155〜PAG175）
- 10400–12010（PAG192〜PAG205）
- 13690–14000（PAG218〜PAG219）
- 20007–21766（PAG246〜PAG257 の冒頭）

**つまみ読みした位置**（各 6〜8 行）：1000、2000、4000、6000、6500、7000、8000、9000、9500、10000、12000、12500、13000、13500、14000、14500、15000、15500、16000、16500、17000、17500、18000、18500、19000、19500、20000、20500、21000、21500、22000。

**読んでいない主な範囲**：2007–6559（PAG28 後半〜PAG116）、6901–8299（PAG121〜PAG155）、9101–10399（PAG175〜PAG192）、12011–13689（PAG205〜PAG218 前半）、14001–20006（PAG219 後半〜PAG246）。つまみ読みで見た限り、これらの主題は殻・ket・中心代数・Ramanujan 和などでした。

**読んだ範囲で目で探した語**（機械的な検索ではありません）：cas、casK、hartley、Hartley、mulShift、gaussSum、stdAddChar (-、χ⁻¹ (-1)、χ (-1) * χ (-1)、IsPrimitive、≠ 1、Even、Odd、ℂ 3、ℂ 5、ZMod 3、Lc、Wpow、zN、gs、epsG、zOf、normSq、unitsMap、castHom、crt、chineseRemainder、kUnit、Dense、closure、ℕ+、factorial、!、Real.log、ModEq
