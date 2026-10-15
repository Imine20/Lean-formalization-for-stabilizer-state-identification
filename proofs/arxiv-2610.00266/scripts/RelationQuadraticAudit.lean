import ExactCriticalCurve.Binary.RelationQuotient
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section
open ExactCriticalCurve.Binary ExactCriticalCurve.Binary.StochasticCounting
namespace RelationQuadraticExpected

def Z4Add : Prop :=
  ∀ {k : ℕ} (x y : (Fin k → ZMod 2) × (Fin k → ZMod 2)),
    weightQuadratic (x+y).1-weightQuadratic (x+y).2 =
      (weightQuadratic x.1-weightQuadratic x.2) +
      (weightQuadratic y.1-weightQuadratic y.2) +
      2*bitLift (binaryDot x.1 y.1+binaryDot x.2 y.2)

def HalfZero : Prop :=
  ∀ {k : ℕ} (x : evenRelationSpace k),
    relationHalfForm k x=0 ↔ weightQuadratic x.val.1-weightQuadratic x.val.2=0

def Bound : Prop :=
  ∀ {k : ℕ} (W : Submodule (ZMod 2) ((Fin k → ZMod 2) × (Fin k → ZMod 2))),
    (∀ p ∈ W, weightQuadratic p.1-weightQuadratic p.2=0) →
    Module.finrank (ZMod 2) W≤k

def EmptyCount : Prop :=
  ∀ {k : ℕ} (W : Submodule (ZMod 2) ((Fin k → ZMod 2) × (Fin k → ZMod 2))),
    (¬ ∀ p ∈ W, weightQuadratic p.1-weightQuadratic p.2=0) →
    Nat.card {T : StochasticLagrangian k // W≤T.carrier}=0

def Radical : Prop :=
  ∀ (k : ℕ) (x : evenRelationSpace k),
    (∀ y : evenRelationSpace k,
      relationHalfForm k (x+y)-relationHalfForm k x-relationHalfForm k y=0) ↔
    x.val ∈ Submodule.span (ZMod 2) {(allOnes k,allOnes k)}

def Nondegenerate : Prop :=
  ∀ k : ℕ, ∀ x : evenRelationSpace k ⧸
      (Submodule.span (ZMod 2) {(allOnes k,allOnes k)}).comap (evenRelationSpace k).subtype,
    (∀ y : evenRelationSpace k ⧸
      (Submodule.span (ZMod 2) {(allOnes k,allOnes k)}).comap (evenRelationSpace k).subtype,
      relationQuotientForm k (x+y)-relationQuotientForm k x-relationQuotientForm k y=0) →
      x=0

def Dimension : Prop :=
  ∀ {k : ℕ}, 1≤k →
    Module.finrank (ZMod 2) (evenRelationSpace k ⧸
      (Submodule.span (ZMod 2) {(allOnes k,allOnes k)}).comap (evenRelationSpace k).subtype) =
      2*(k-1)

def DiagonalSingular : Prop :=
  ∀ (k : ℕ) (x : RelationQuotient k),
    x ∈ quotientDiagonal k → relationQuotientForm k x=0

def DiagonalDimension : Prop :=
  ∀ {k : ℕ}, 1≤k → Module.finrank (ZMod 2) (quotientDiagonal k)=k-1

end RelationQuadraticExpected

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
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.relationQuadratic_add `RelationQuadraticExpected.Z4Add
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.relationHalfForm_zero_iff `RelationQuadraticExpected.HalfZero
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.finrank_le_of_relationQuadratic_zero `RelationQuadraticExpected.Bound
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.card_stochasticExtensions_of_nonisotropic `RelationQuadraticExpected.EmptyCount
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.wuDenominator_eq_radical `RelationQuadraticExpected.Radical
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.relationQuotientForm_nondegenerate `RelationQuadraticExpected.Nondegenerate
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.finrank_relationQuotient `RelationQuadraticExpected.Dimension
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.quotientDiagonal_singular `RelationQuadraticExpected.DiagonalSingular
  auditExactTheorem `ExactCriticalCurve.Binary.StochasticCounting.finrank_quotientDiagonal `RelationQuadraticExpected.DiagonalDimension
