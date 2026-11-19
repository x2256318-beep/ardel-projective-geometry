import PAG266
import PAG3
import PAG6
open Lean Meta Elab Command

/-- PAG の各宣言について、名前・モジュール・種類・型に現れる定数・（定義なら）値に現れる定数を JSON 行で書き出す。 -/
def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "ax"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut lines : Array String := #[]
  let mut cnt := 0
  for (n, ci) in env.constants.map₁.toList do
    if n.isInternalDetail then continue
    match env.getModuleIdxFor? n with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if !(mod.toString.startsWith "PAG") then continue
      let tyC := ci.type.getUsedConstants.map (·.toString)
      let valC : Array String := match ci with
        | .defnInfo d => d.value.getUsedConstants.map (·.toString)
        | _ => #[]
      let j := Json.mkObj [("name", toJson n.toString), ("module", toJson mod.toString),
        ("kind", toJson (kindOf ci)), ("type", toJson tyC), ("value", toJson valC)]
      lines := lines.push j.compress
      cnt := cnt + 1
    | none => pure ()
  IO.FS.writeFile "/home/claude/out/audit266/internal/decls_all266.jsonl" (String.intercalate "\n" lines.toList ++ "\n")
  logInfo m!"書き出した宣言：{cnt}"
