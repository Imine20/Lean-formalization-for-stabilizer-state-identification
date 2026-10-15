import ExactCriticalCurve.FiniteQuadratic.MaximalCounting
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section
open scoped BigOperators

namespace MaximalCountingExpected
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

def HalfDimension [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ Q : QuadraticForm (ZMod 2) V,
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ r : ℕ, Module.finrank (ZMod 2) V=2*r →
  ∀ L : Submodule (ZMod 2) V, (∀ x ∈ L, Q x=0) →
  Module.finrank (ZMod 2) L=r →
    Nat.card {M : Submodule (ZMod 2) V //
      (∀ x ∈ M, Q x=0) ∧ Module.finrank (ZMod 2) M=r} =
      ∏ j ∈ Finset.range r, (1+2^j)

def OrderMaximal [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ Q : QuadraticForm (ZMod 2) V,
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ r : ℕ, Module.finrank (ZMod 2) V=2*r →
  ∀ L : Submodule (ZMod 2) V, (∀ x ∈ L, Q x=0) →
  Module.finrank (ZMod 2) L=r →
    Nat.card {M : Submodule (ZMod 2) V // (∀ x ∈ M, Q x=0) ∧
      ∀ W : Submodule (ZMod 2) V, (∀ x ∈ W, Q x=0) → M≤W → W=M} =
      ∏ j ∈ Finset.range r, (1+2^j)

def HalfDimensionExtensions [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ Q : QuadraticForm (ZMod 2) V,
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ r : ℕ, Module.finrank (ZMod 2) V=2*r →
  ∀ L U : Submodule (ZMod 2) V, (∀ x ∈ L, Q x=0) →
  Module.finrank (ZMod 2) L=r → (∀ x ∈ U, Q x=0) →
    Nat.card {W : Submodule (ZMod 2) V //
      U≤W ∧ (∀ x ∈ W, Q x=0) ∧ Module.finrank (ZMod 2) W=r} =
      ∏ j ∈ Finset.range (r-Module.finrank (ZMod 2) U), (1+2^j)

def OrderMaximalExtensions [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ Q : QuadraticForm (ZMod 2) V,
  (∀ x : V, (∀ y : V, Q (x+y)-Q x-Q y=0) → x=0) →
  ∀ r : ℕ, Module.finrank (ZMod 2) V=2*r →
  ∀ L U : Submodule (ZMod 2) V, (∀ x ∈ L, Q x=0) →
  Module.finrank (ZMod 2) L=r → (∀ x ∈ U, Q x=0) →
    Nat.card {W : Submodule (ZMod 2) V // U≤W ∧ (∀ x ∈ W, Q x=0) ∧
      ∀ T : Submodule (ZMod 2) V, (∀ x ∈ T, Q x=0) → W≤T → T=W} =
      ∏ j ∈ Finset.range (r-Module.finrank (ZMod 2) U), (1+2^j)

end MaximalCountingExpected

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
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.card_singularSubspaces `MaximalCountingExpected.HalfDimension
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.card_maximalSingularSubspaces `MaximalCountingExpected.OrderMaximal
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.card_singularExtensions `MaximalCountingExpected.HalfDimensionExtensions
  auditExactTheorem `ExactCriticalCurve.FiniteQuadratic.card_maximalSingularExtensions `MaximalCountingExpected.OrderMaximalExtensions
