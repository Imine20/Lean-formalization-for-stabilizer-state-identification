import ExactCriticalCurve.FiniteQuadratic.ZeroCounting
import ExactCriticalCurve.FiniteQuadratic.SingularCorrespondence
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section
open ExactCriticalCurve.FiniteQuadratic

namespace QuadraticCountingLeavesExpected
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

def LinearFiber [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ f : V →ₗ[ZMod 2] ZMod 2, f≠0 → ∀ b : ZMod 2,
    Nat.card {x : V // f x=b} = 2^(Module.finrank (ZMod 2) V-1)

def ZeroVectors [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ Q : QuadraticForm (ZMod 2) V,
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ r : ℕ, Module.finrank (ZMod 2) V=2*r →
  ∀ L : Submodule (ZMod 2) V, (∀ x ∈ L, Q x=0) →
  Module.finrank (ZMod 2) L=r →
    Nat.card {v : V // Q v=0} = 2^r+(2^r-1)*2^(r-1)

def NonzeroVectors [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ Q : QuadraticForm (ZMod 2) V,
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ r : ℕ, Module.finrank (ZMod 2) V=2*r →
  ∀ L : Submodule (ZMod 2) V, (∀ x ∈ L, Q x=0) →
  Module.finrank (ZMod 2) L=r →
    Nat.card {v : V // Q v=0 ∧ v≠0} = (2^r-1)*(2^(r-1)+1)

def Correspondence [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V)
  (hU : ∀ x ∈ U, Q x=0) (r : ℕ),
    Nat.card {W : Submodule (ZMod 2) V //
      U≤W ∧ (∀ x ∈ W, Q x=0) ∧ Module.finrank (ZMod 2) W=r} =
    Nat.card {M : Submodule (ZMod 2)
      ((LinearMap.BilinForm.orthogonal Q.polarBilin U) ⧸
        U.comap (LinearMap.BilinForm.orthogonal Q.polarBilin U).subtype) //
      (∀ x ∈ M, orthogonalQuotientForm Q U hU x=0) ∧
      Module.finrank (ZMod 2) M+Module.finrank (ZMod 2) U=r}

end QuadraticCountingLeavesExpected

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
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.card_binaryLinear_fiber `QuadraticCountingLeavesExpected.LinearFiber
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.card_zeroVectors `QuadraticCountingLeavesExpected.ZeroVectors
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.card_nonzeroSingularVectors `QuadraticCountingLeavesExpected.NonzeroVectors
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.card_singularExtensions_eq_quotient `QuadraticCountingLeavesExpected.Correspondence
