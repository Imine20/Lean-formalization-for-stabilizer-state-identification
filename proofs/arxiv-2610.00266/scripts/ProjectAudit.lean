import ExactCriticalCurve
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut declarations := 0
  let mut theorems := 0
  let mut closure : CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    let inProject := match env.getModuleIdxFor? name with
      | some idx => (`ExactCriticalCurve).isPrefixOf env.header.moduleNames[idx]!
      | none => false
    if inProject then
      declarations := declarations + 1
      if let .thmInfo _ := info then
        theorems := theorems + 1
      if let .axiomInfo _ := info then
        throwError "Unproved project axiom: {name}"
      let (_, next) := ((CollectAxioms.collect name).run env).run closure
      closure := next
      for ax in closure.axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Forbidden transitive axiom {ax} in {name}"
      let dependencies := info.getUsedConstantsAsSet.toList.map Name.toString
      let row := Json.mkObj [("declaration", toJson name.toString),
        ("direct_dependencies", toJson dependencies)]
      logInfo m!"DECLARATION_AUDIT {row.compress}"
  logInfo m!"PROJECT_AXIOMS_UNION {closure.axioms}"
  logInfo m!"PROJECT_AUDIT_OK declarations={declarations} theorems={theorems}"
