# 照合者（内部照合）の結果を見る前に書いた予想（2026-11-14 13:4x。Lean の機械的な確認の 1 回目（k = 8）の結果は見た後）

判定の型：A 同じ文（名前の違いを除く）／B 前の定理から直ちに出る（代入・定義の展開）／C 前の定理から数行で出る（短い系）／D 前の鎖に見つからない。

- PAG260（Part 256）：prodChar（＝ Part 195 の cmul、Part 232 の charMul）、prodChar_apply、crtMap_bijective、stdAddChar_crtMap、gaussSum_prodChar、isPrimitive_prodChar、charU_prodChar は A か B（確信度：高）。rootNum_prodChar は C（Part 189 の z_mul_coprime と偶奇の符号、高）。cross_eq_sign_of_rootNum_one は C、または Part 194 の real_reciprocity との関係を指摘される（中）。phaseA1_prodChar・UA1_charU_prodChar は C（中）。具体例・証人の定理（rootNum_prodChar_ne_mul など）は D（中）。
- PAG256（Part 252）：inv_apply_neg_one、neg_one_mul_self、isPrimitive_of_prime_of_ne_one は A（高）。normSq_rootNum は C（PAG16 の normSq_gaussSum から、高）。ハートレー変換まわり（hartley、JH）は D か、前の離散フーリエ変換の結果の C（低）。
- PAG257（Part 253）：eq_one_of_two は B（Part 194 の level_two_trivial、高）。Vprim の上のユニタリ性・span_charU_eq_top は、前の指標の直交性・基底の結果の C（中）。
- PAG258（Part 254）：直極限の構成（Lim、ofL、Uinf など）は D（中〜高）。condPart（導手ごとの分解）は、前のブロック分解（Part 216 など）の C の可能性（低〜中）。
- PAG253〜255（Part 249〜251）：kUnit・primeCls など単数群と素数の類の補題の一部は、前の (ℤ/N)^× の補題の A・B（中）。ipG_smul_left は PAG217 の inner_smul_left' より一般の形（低）。
- PAG259（Part 255）：稠密か離散かの二分法・閾値は、Part 250・251（PAG254・255）の結果の C を含む（中）。
- 全体：A・B は Part 252 と 256 に集中して 10〜15 件、C はさらに 15〜30 件、Part 249〜251・254・255 の大半は D（中）。
