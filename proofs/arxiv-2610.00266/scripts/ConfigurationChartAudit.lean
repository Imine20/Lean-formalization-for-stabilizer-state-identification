import ExactCriticalCurve.Binary.ConfigurationRelations
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section
open scoped BigOperators
open Classical
open ExactCriticalCurve.Binary

namespace ConfigurationChartExpected
def AffineEquality : Prop :=
  ∀ {m n k : ℕ} (a : Fin n → ZMod 2)
    (f : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)),
    Function.Injective f → ∀ X Y : Fin k → (Fin m → ZMod 2),
    Submodule.span (ZMod 2)
      (insert ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2)))
        (Set.range (fun j : Fin n => ((fun i => (a+f (X i)) j), (fun i => (a+f (Y i)) j))))) = Submodule.span (ZMod 2)
      (insert ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2)))
        (Set.range (fun j : Fin m => ((fun i => X i j), (fun i => Y i j)))))
def BasisChartEquality : Prop :=
  ∀ {m n k : ℕ} (L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : Module.Basis (Fin m) (ZMod 2) L) (a : Fin n → ZMod 2)
    (X Y : Fin k → (Fin m → ZMod 2)),
    Submodule.span (ZMod 2)
      (insert ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2)))
        (Set.range (fun j : Fin n => ((fun i => (a+(b.equivFun.symm (X i)).val) j), (fun i => (a+(b.equivFun.symm (Y i)).val) j))))) = Submodule.span (ZMod 2)
      (insert ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2)))
        (Set.range (fun j : Fin m => ((fun i => X i j), (fun i => Y i j)))))
def BasisChartStatistics : Prop :=
  ∀ {m n k : ℕ} (L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : Module.Basis (Fin m) (ZMod 2) L) (a : Fin n → ZMod 2)
    (X Y : Fin k → (Fin m → ZMod 2)),
    ((∀ j : Fin n, (∑ i, bitLift ((fun i => a+(b.equivFun.symm (X i)).val) i j)) - (∑ i, bitLift ((fun i => a+(b.equivFun.symm (Y i)).val) i j))=0) ∧
    (∀ p : {p : Fin n × Fin n // p.1<p.2},
      (∑ i, (fun i => a+(b.equivFun.symm (X i)).val) i p.val.1 * (fun i => a+(b.equivFun.symm (X i)).val) i p.val.2) - (∑ i, (fun i => a+(b.equivFun.symm (Y i)).val) i p.val.1 * (fun i => a+(b.equivFun.symm (Y i)).val) i p.val.2)=0)) ↔
    ((∀ j : Fin m, (∑ i, bitLift (X i j)) - (∑ i, bitLift (Y i j))=0) ∧
    (∀ p : {p : Fin m × Fin m // p.1<p.2},
      (∑ i, X i p.val.1 * X i p.val.2) - (∑ i, Y i p.val.1 * Y i p.val.2)=0))
end ConfigurationChartExpected

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
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.configurationRelationSpace_affine_eq `ConfigurationChartExpected.AffineEquality
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.configurationRelationSpace_basis_chart `ConfigurationChartExpected.BasisChartEquality
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.phaseStatisticsVanish_basis_chart `ConfigurationChartExpected.BasisChartStatistics
