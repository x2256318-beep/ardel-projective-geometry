"""尾の統合照合 T の指摘による直し。すべて主張を変えない直し（言い回し・記録・docstring）。形式文は変えない（補足8 の停止の規約）。"""
def apply(p, reps):
    s = open(p, encoding='utf-8').read()
    for a, b in reps:
        assert s.count(a) == 1, (p, s.count(a), a[:70]); s = s.replace(a, b)
    open(p, 'w', encoding='utf-8').write(s)
L='/home/claude/leanwork/pagpkg/'; N='/home/claude/out185/'; A='/home/claude/out/audit259/'
VAC_OLD_H = '（`compat_dind_unique`。文は N ∣ M だけを仮定するが、gcd(N, M/N) ≠ 1 なら Part 258 により (i)(ii) を\n   満たす φ はないので、その場合は空虚に真）。'
VAC_NEW_H = '（`compat_dind_unique`。文は N ∣ M だけを仮定する。Part 258 の不存在は (ii) の E の側も仮定する文なので、\n   gcd(N, M/N) ≠ 1 で (i) と D の側だけを満たす写像があるかは、Lean にも Part 258 にもない（照合 T の指摘で直した）。'
apply(L+'PAG263.lean', [
 (VAC_OLD_H, VAC_NEW_H),
 ('/-- **φ(D_s) は (i)(ii) の D の側から一意に決まる**（N ∣ M。互いに素は要らない）。 -/',
  '/-- **φ(D_s) は (i) と (ii) の D の側から一意に決まる**（文は N ∣ M だけを仮定する。gcd(N, M/N) ≠ 1 でこの前提を\n満たす写像があるかは未確認）。 -/'),
 ('/-- **(iii) を外すと一意でない**：gcd(2, b) = 1、1 < b のとき、Part 258 の条件 (i)(ii) を満たす\nA_2 → A_{2b} は少なくとも 2 つある（`shellLift` と φ\'）。 -/',
  '/-- **(iii) を外すと一意でない場合がある（a = 2 の例）**：gcd(2, b) = 1、1 < b のとき、Part 258 の条件 (i)(ii) だけを\n課すと、それを満たす A_2 → A_{2b} は一意でない（`shellLift` と φ\'。2 つあることは `compat_twLift`・`compatF_shellLift`・\n`twLift_ne_shellLift` による）。 -/'),
 ('/-- (i) を満たす写像は単射。 -/', '/-- (i)(ii)（`Compat`）を満たす写像は単射（証明は (i) だけを使う）。 -/'),
 ('（`sqLim_of_injective`。遷移写像の単射性 `compat_injective` からほぼ自動的に出る）。',
  '（`sqLim_of_injective`。遷移写像の単射性 `compat_injective`（仮定は `Compat`、証明は (i) だけを使う）からほぼ自動的に出る）。'),
])
apply(L+'PAG262.lean', [
 ('アーデル射影幾何 — Part 258（PAG 2.0）：N ∣ M のとき、(i) φ(S) π^* = π^* S、(ii) φ(D_s)・φ(E_s) が D_t・E_t の線形結合、\nを満たす単位的な代数準同型 φ : A_N → A_M がある ⇔ gcd(N, M/N) = 1（登録の言葉では「方向βの前提」の判定）',
  'アーデル射影幾何 — Part 258（PAG 2.0）：N, M ≥ 1、N ∣ M のとき、(i) φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の、φ(E_s) は E_t の\n線形結合、を満たす単位的な代数準同型 φ : A_N → A_M がある ⇔ gcd(N, M/N) = 1（登録の言葉では「方向βの前提」の判定）'),
 ('φ(E_1) = E_3 + E_2）も Lean にしていない。',
  'φ(E_1) = E_3 + E_2）も、ここでは Lean にしていない（a = 2 の場合は Part 259（PAG263）の `twLift`・`not_existsUnique_compat` で\nLean になった。照合 T の指摘で参照を足した）。'),
])
apply(L+'PAG261.lean', [
 ('/-- 成分がすべて原始なら、UA1 の固有値 phaseA1 も同じ式で分かれる（',
  '/-- 法がどの 2 つも互いに素で（`hl`）、成分がすべて原始なら、UA1 の固有値 phaseA1 も同じ式で分かれる（'),
])
apply(N+'pag2_part258_beta_premise.md', [
 ('# アーデル射影幾何 — Part 258（PAG 2.0）：N ∣ M のとき、(i) φ(S) π^* = π^* S、(ii) φ(D_s)・φ(E_s) が D_t・E_t の線形結合、を満たす',
  '# アーデル射影幾何 — Part 258（PAG 2.0）：N, M ≥ 1、N ∣ M のとき、(i) φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の、φ(E_s) は E_t の線形結合、を満たす'),
 ('| 互いに素な段の写像と条件 2・3 | `shellLift`・`crtConj_shellLift`・`shellLift_pull`・',
  '| 互いに素な段の写像と条件 2・3 | `shellLift`・`crtConj_shellLift`・`shellLift_pull`（補助：`castHom_crt_symm`・`crtLin_pull`）・'),
 ('`x_mul_N`・`mul_x_ne_zero`・`conv_single`・`castHom_crt_symm`・`crtLin_pull`） |',
  '`x_mul_N`・`mul_x_ne_zero`・`conv_single`。前の鎖から `PAG.Part207.gcd_val_unit_mul`・`PAG.Part201.card_ker_cast`。照合 T の指摘で、存在の側の補助 2 つを上の行へ移した） |'),
])
apply(N+'pag2_internal_audit_249_256.md', [
 ('- **F2 の後の直し（3 回目。Part 258 の閉鎖条件 3 の照合 R3 を受けた。§9）**：',
  '- **F2 の後の直し（3 回目。Part 258 の閉鎖条件 3 の照合 R3 を受けた。§9。R3 の後の直し（下の 9・10 の扱い、92 定理の内訳）は尾の統合照合 T（2026-11-18）を受けた）**：'),
])
apply(A+'pag2_part259_unitary_step_maps.md', [
 ('2. **(iii) を外すと一意でない場合がある**（`not_existsUnique_compat`）。gcd(2, b) = 1 かつ 1 < b のとき、(i)(ii) だけを満たす A_2 → A_{2b} は 2 つ以上ある。',
  '2. **(iii) を外すと一意でない場合がある**（`not_existsUnique_compat`）。gcd(2, b) = 1 かつ 1 < b のとき、(i)(ii) だけを課すと、それを満たす A_2 → A_{2b} は 2 つ以上ある（`compat_twLift`・`compatF_shellLift`・`twLift_ne_shellLift`）。'),
 ('規模：定理 67 個、定義 14 個、インスタンス 3 個。', '規模：定理 67 個、定義 15 個（`def` 14 個と `abbrev` 1 個）、インスタンス 3 個。'),
 ('(i) を定数 1 に当てると φ(D_s) が決まり（`compat_dind_unique`）、', '(ii) の D の側から φ(D_s) は掛け算の作用素で、(i) を定数 1 に当てるとそれが決まり（`compat_dind_unique`）、'),
 ('- **「互いに素は要らない」と書いた文について。** `compat_dind_unique`・`compatF_unique`・`compatF_comp` は N ∣ M だけを仮定する。しかし互いに素でなければ Part 258 により前提を満たす写像がないので、その場合は空虚に真である。',
  '- **「互いに素は要らない」と書いた文について。** `compat_dind_unique`・`compatF_unique`・`compatF_comp` は N ∣ M だけを仮定する。`compatF_unique`・`compatF_comp` は、互いに素でなければ Part 258 により前提を満たす写像がないので、その場合は空虚に真である。`compat_dind_unique` は (ii) の E の側を仮定しないので Part 258 は当てはまらず、gcd(N, M/N) ≠ 1 で前提を満たす写像があるかは未確認である（照合 T の指摘で直した。照合者の小さい数値では、(2,4)・(2,8)・(3,9) でそのような写像は見つからなかった。証明ではない）。'),
 ('全宣言 4424 件、TF-IDF の上位 20 件と照らして 3440 回、', '全宣言 4424 件、TF-IDF の上位 20 件と照らして 3440 回（対象 86 件＝定理・インスタンス 71、定義 15。定義も含めて両向きに数えた：86·20·2）、'),
])
apply(A+'update_xlsx_259.py', [
 ("'(i) と (ii) の D の側から φ(D_s) は一意に決まる（文は N ∣ M だけを仮定。互いに素でなければ空虚に真）'",
  "'(i) と (ii) の D の側から φ(D_s) は一意に決まる（文は N ∣ M だけを仮定。gcd(N, M/N) ≠ 1 で前提を満たす写像があるかは未確認）'"),
 ("('compat_injective','(i) を満たす写像は単射'", "('compat_injective','(i)(ii)（Compat）を満たす写像は単射（証明は (i) だけを使う）'"),
 ("'Part 89 の結合法則と Part 201 の geps_conv_geps'", "'Part 85（PAG89）の結合法則と Part 201 の geps_conv_geps'"),
])
print('ok')
