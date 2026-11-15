import PAG260
import PAG3
import PAG6
open Lean Elab Command

/-- `#dupcheck i T S`：T の文を S から（`exact`／`apply` と仮定で）示せるか試し、結果だけを記録する。 -/
elab "#dupcheck " i:num t:ident s:ident : command => do
  let saved := (← get).messages
  modify fun st => { st with messages := {} }
  let stx ← `(command|
    set_option maxHeartbeats 30000 in
    example : type_of% @$t := by
      intros
      first
      | exact $s
      | (apply $s <;> assumption)
      | (apply $s <;> simp_all)
      | (simp only [] at *; apply $s <;> assumption))
  try elabCommand stx catch _ => pure ()
  let bad := (← get).messages.hasErrors
  modify fun st => { st with messages := saved }
  logInfo m!"DUP {i.getNat} {if bad then "FAIL" else "OK"}"

/-- `#defeqcheck i T S`：2 つの定義が（型も含めて）定義的に等しいか。 -/
elab "#defeqcheck " i:num t:ident s:ident : command => do
  let saved := (← get).messages
  modify fun st => { st with messages := {} }
  let stx ← `(command|
    set_option maxHeartbeats 30000 in
    example : HEq @$t @$s := HEq.rfl)
  try elabCommand stx catch _ => pure ()
  let bad := (← get).messages.hasErrors
  modify fun st => { st with messages := saved }
  logInfo m!"DEF {i.getNat} {if bad then "FAIL" else "OK"}"
