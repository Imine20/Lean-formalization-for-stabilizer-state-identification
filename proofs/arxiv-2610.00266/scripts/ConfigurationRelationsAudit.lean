import ExactCriticalCurve.Binary.ConfigurationRelations
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section
open scoped BigOperators
open Classical
open ExactCriticalCurve.Binary

namespace ConfigurationRelationsExpected
def WuMembership : Prop :=
  ∀ {n k : ℕ} (X Y : Fin k → (Fin n → ZMod 2)),
    ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2))) ∈
      Submodule.span (ZMod 2)
        (insert ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2)))
          (Set.range (fun a : Fin n => ((fun i => X i a), (fun i => Y i a)))))
def NonemptySupport : Prop :=
  ∀ {n k : ℕ}, 1≤k → ∀ X Y : Fin k → (Fin n → ZMod 2),
    Nonempty (affineSpan (ZMod 2) (Set.range X ∪ Set.range Y))
def EntrySum : Prop :=
  ∀ {n k : ℕ} (X Y : Fin k → (Fin n → ZMod 2)),
    (∑ T : StochasticLagrangian k,
      ∏ a : Fin n, (if ((fun i => X i a),(fun i => Y i a))∈T.carrier
        then (1 : ℂ) else 0)) =
    (Nat.card {T : StochasticLagrangian k //
      Submodule.span (ZMod 2)
        (insert ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2)))
          (Set.range (fun a : Fin n => ((fun i => X i a), (fun i => Y i a))))) ≤ T.carrier} : ℂ)
def RelationDimension : Prop :=
  ∀ {n k : ℕ}, 1≤k → ∀ X Y : Fin k → (Fin n → ZMod 2),
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (insert ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2)))
          (Set.range (fun a : Fin n => ((fun i => X i a), (fun i => Y i a)))))) =
    Module.finrank (ZMod 2) (affineSpan (ZMod 2) (Set.range X ∪ Set.range Y)).direction + 1
def ConeDimension {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] : Prop :=
  ∀ {s : Set V}, s.Nonempty →
    Module.finrank K (Submodule.span K ((fun x : V => ((1 : K), x)) '' s)) =
    Module.finrank K (affineSpan K s).direction + 1

def PhaseIsotropy : Prop :=
  ∀ {n k : ℕ} (X Y : Fin k → (Fin n → ZMod 2)),
    ((∀ a : Fin n, (∑ i, bitLift (X i a)) - (∑ i, bitLift (Y i a))=0) ∧
      (∀ p : {p : Fin n × Fin n // p.1<p.2},
        (∑ i, X i p.val.1 * X i p.val.2) - (∑ i, Y i p.val.1 * Y i p.val.2)=0)) ↔
    ∀ x∈Submodule.span (ZMod 2)
      (insert ((fun _ : Fin k => (1 : ZMod 2)), (fun _ : Fin k => (1 : ZMod 2)))
        (Set.range (fun a : Fin n => ((fun i => X i a), (fun i => Y i a))))),
      (∑ i, bitLift (x.1 i)) - (∑ i, bitLift (x.2 i))=0

end ConfigurationRelationsExpected

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
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.wu_mem_configurationRelationSpace `ConfigurationRelationsExpected.WuMembership
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.configurationSupport_nonempty `ConfigurationRelationsExpected.NonemptySupport
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.relationOperator_configuration_sum_card `ConfigurationRelationsExpected.EntrySum
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.finrank_configurationRelationSpace `ConfigurationRelationsExpected.RelationDimension
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.finrank_affineCone `ConfigurationRelationsExpected.ConeDimension
  auditExactTheorem `ExactCriticalCurve.Binary.ConfigurationRelations.phaseStatisticsVanish_iff_relationQuadratic_zero `ConfigurationRelationsExpected.PhaseIsotropy
