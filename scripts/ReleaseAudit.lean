import StabilizerLearning
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let name := `StabilizerLearning.fixedW_noCopyRateDiscount
  let target := `StabilizerLearning.FixedWNoCopyRateDiscount
  match env.find? name with
  | some (.thmInfo info) =>
    unless info.type == mkConst target do
      throwError "Release theorem must prove the exact reviewed target without extra hypotheses"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Release rejected: {ax} in main theorem"
    logInfo m!"MAIN_RELEASE_OK {name}: {axioms}"
  | _ => throwError "MAIN_RELEASE_BLOCKED: main theorem proof is absent (statement_only)"
