import ExactCriticalCurve.FiniteQuadratic.MetabolicQuotient
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section
open ExactCriticalCurve.FiniteQuadratic
namespace MetabolicQuotientExpected
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

def Representatives : Prop :=
  ∀ (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V)
  (hU : ∀ x ∈ U, Q x = 0) (hRad : ∀ u ∈ U, ∀ v : V, Q (u+v)-Q u-Q v=0)
  (x : V), quotientForm Q U hU hRad (Submodule.Quotient.mk x) = Q x

def QuotientNondegenerate : Prop :=
  ∀ (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V)
  (hU : ∀ x ∈ U, Q x = 0) (hRad : ∀ u ∈ U, ∀ v : V, Q (u+v)-Q u-Q v=0),
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x ∈ U) →
    ∀ x : V ⧸ U,
      (∀ y : V ⧸ U, quotientForm Q U hU hRad (x+y) -
        quotientForm Q U hU hRad x - quotientForm Q U hU hRad y = 0) → x=0

def OrthogonalNondegenerate [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ (Q : QuadraticForm (ZMod 2) V),
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ (U : Submodule (ZMod 2) V) (hU : ∀ x ∈ U, Q x=0),
    ∀ x : (LinearMap.BilinForm.orthogonal Q.polarBilin U) ⧸
        U.comap (LinearMap.BilinForm.orthogonal Q.polarBilin U).subtype,
      (∀ y, orthogonalQuotientForm Q U hU (x+y) -
        orthogonalQuotientForm Q U hU x - orthogonalQuotientForm Q U hU y = 0) → x=0

def Dimension [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ (Q : QuadraticForm (ZMod 2) V),
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ U : Submodule (ZMod 2) V, (∀ x ∈ U, Q x=0) →
    Module.finrank (ZMod 2) ((LinearMap.BilinForm.orthogonal Q.polarBilin U) ⧸
      U.comap (LinearMap.BilinForm.orthogonal Q.polarBilin U).subtype) +
      2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V

def Witness [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ (Q : QuadraticForm (ZMod 2) V),
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ r : ℕ, Module.finrank (ZMod 2) V = 2*r →
  ∀ L U : Submodule (ZMod 2) V, (∀ x ∈ L, Q x=0) →
  Module.finrank (ZMod 2) L=r → ∀ hU : (∀ x ∈ U, Q x=0),
    ∃ M : Submodule (ZMod 2)
        ((LinearMap.BilinForm.orthogonal Q.polarBilin U) ⧸
          U.comap (LinearMap.BilinForm.orthogonal Q.polarBilin U).subtype),
      (∀ x ∈ M, orthogonalQuotientForm Q U hU x=0) ∧
      Module.finrank (ZMod 2) M=r-Module.finrank (ZMod 2) U

end MetabolicQuotientExpected

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
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.quotientForm_mk `MetabolicQuotientExpected.Representatives
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.quotientForm_nondegenerate `MetabolicQuotientExpected.QuotientNondegenerate
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.orthogonalQuotientForm_nondegenerate `MetabolicQuotientExpected.OrthogonalNondegenerate
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.finrank_orthogonalQuotient_add `MetabolicQuotientExpected.Dimension
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.orthogonalQuotient_metabolic `MetabolicQuotientExpected.Witness
