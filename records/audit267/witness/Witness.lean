import PAG267
open PAG.Part267 PAG.Part27 PAG.Part258

-- 非空虚性：N = 2 で 0 ≠ ∞
example : zeroPt 2 ≠ infPt 2 := zeroPt_ne_infPt (by norm_num)
-- 除去テスト：N = 1 では 0 = ∞（仮定 N ≠ 1 は外せない）
example : zeroPt 1 = infPt 1 := mk_eq_mk 1 (Subsingleton.elim _ _) (Subsingleton.elim _ _)
-- 非空虚性：還元 P¹(ℤ/12) → P¹(ℤ/4) は全射
example : Function.Surjective (red (N := 4) (M := 12) (by norm_num)) := red_surjective _
-- 判定の両側：(2, 4) では条件が成り立つ
def lv4 : Lvl := ⟨4, by norm_num⟩
theorem h24 : lv2 ≤ lv4 := (⟨2, rfl⟩ : 2 ∣ 4)
example : ∀ g : Gsp lv2, extE lv4 (pullSys lv2 lv4 h24 g) = pullP lv2 lv4 h24 (extE lv2 g) :=
  (extE_compat_iff lv2 lv4 h24).mpr (by
    intro p hp hp4
    have : p ∣ 2 ^ 2 := hp4
    exact hp.dvd_of_dvd_pow this)
-- 仮定の除去：判定の右辺の条件を外すと (1, 2) が反例（extE_not_compat）
#check extE_not_compat
