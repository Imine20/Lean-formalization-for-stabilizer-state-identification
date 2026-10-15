import ExactCriticalCurve.Binary.StochasticCounting
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section
open scoped BigOperators
open ExactCriticalCurve.Binary ExactCriticalCurve.Binary.StochasticCounting

namespace StochasticCountingExpected

def ImageDimension : Prop :=
  ∀ {k : ℕ}, 1≤k →
  ∀ W : Submodule (ZMod 2) ((Fin k → ZMod 2) × (Fin k → ZMod 2)),
  (allOnes k,allOnes k)∈W → W≤evenRelationSpace k →
    Module.finrank (ZMod 2)
      ((W.comap (evenRelationSpace k).subtype).map
        ((Submodule.span (ZMod 2) {(allOnes k,allOnes k)}).comap
          (evenRelationSpace k).subtype).mkQ) + 1 = Module.finrank (ZMod 2) W

def TotalCount : Prop :=
  ∀ {k : ℕ}, 1≤k →
    Nat.card (StochasticLagrangian k)=∏ j∈Finset.range (k-1), (1+2^j)

def ExtensionCount : Prop :=
  ∀ {k : ℕ}, 1≤k →
  ∀ W : Submodule (ZMod 2) ((Fin k → ZMod 2) × (Fin k → ZMod 2)),
  (allOnes k,allOnes k)∈W →
  (∀ p∈W, weightQuadratic p.1-weightQuadratic p.2=0) →
    Nat.card {T : StochasticLagrangian k // W≤T.carrier} =
      ∏ j∈Finset.range (k-Module.finrank (ZMod 2) W), (1+2^j)

def EmptyCount : Prop :=
  ∀ {k : ℕ},
  ∀ W : Submodule (ZMod 2) ((Fin k → ZMod 2) × (Fin k → ZMod 2)),
  (¬ ∀ p∈W, weightQuadratic p.1-weightQuadratic p.2=0) →
    Nat.card {T : StochasticLagrangian k // W≤T.carrier}=0

def ZeroCount : Prop := Nat.card (StochasticLagrangian 0)=1

end StochasticCountingExpected

open Lean Elab Command Meta in
def auditExactTheorem (actual expected : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? actual with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Expected a theorem declaration: {actual}"
  liftTermElabM do
    let actualInfo ← getConstInfo actual
    let expectedInfo ← getConstInfo expected
    unless actualInfo.levelParams.length == expectedInfo.levelParams.length do
      throwError "Universe generality mismatch: {actual}"
    let levelParams := (List.range actualInfo.levelParams.length).map
      (fun i => Name.mkSimple ("auditUniverse" ++ toString i))
    let levels := levelParams.map Level.param
    let term := mkConst actual levels
    let expectedTerm := mkConst expected levels
    let expectedType ← inferType expectedTerm
    -- Abstract all universe-polymorphic typeclass and index parameters on expected definitions.
    let expectedValue ← forallTelescope expectedType fun args _ => do
      let body := mkAppN expectedTerm args
      mkForallFVars args body
    unless ← isDefEq (← inferType term) expectedValue do
      throwError "Exact theorem type mismatch: {actual}\nactual: {← inferType term}\nexpected: {expectedValue}"
    -- Check both the theorem constant and its original proof body directly in
    -- the kernel against the independently constructed expected type.
    -- addDeclCore has no skipKernelTC option and returns synchronously.
    let kernelEnv := (← getEnv).toKernelEnv
    let heartbeatLimit := (Core.getMaxHeartbeats (← getOptions)).toUSize
    for (label, proof) in #[
        ("constant", term),
        ("body", actualInfo.instantiateValueLevelParams! levels)] do
      let witnessName ← mkFreshUserName (Name.mkSimple ("kernelAudit_" ++ label))
      let decl : Declaration := .thmDecl {
        name := witnessName
        levelParams := levelParams
        type := expectedValue
        value := proof
      }
      let _ ← ofExceptKernelException <|
        Kernel.Environment.addDeclCore kernelEnv heartbeatLimit decl none
      logInfo m!"KERNEL_EXPECTED_TYPE_OK {label} {actual}"
  let axioms ← collectAxioms actual
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Forbidden transitive axiom {ax} in {actual}"
  logInfo m!"EXACT_TYPE_AND_AXIOMS_OK {actual}"

open Lean Elab Command in
run_cmd do
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.finrank_relationQuotientImage_add `StochasticCountingExpected.ImageDimension
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.card_stochasticLagrangian `StochasticCountingExpected.TotalCount
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.card_stochasticExtensions `StochasticCountingExpected.ExtensionCount
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.card_stochasticExtensions_of_nonisotropic `StochasticCountingExpected.EmptyCount
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.card_stochasticLagrangian_zero `StochasticCountingExpected.ZeroCount
