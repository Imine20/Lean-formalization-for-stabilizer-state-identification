import ExactCriticalCurve.Counting.AffineContainment
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms

noncomputable section
namespace AffineContainmentExpected
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

def QuotientDimension [FiniteDimensional K V] : Prop :=
  ∀ p N : Submodule K V, p ≤ N →
    Module.finrank K (N.map p.mkQ) + Module.finrank K p = Module.finrank K N

def AffineCount [FiniteDimensional K V] : Prop :=
  ∀ A₀ : AffineSubspace K V, Nonempty A₀ → ∀ m : ℕ,
    Nat.card {A : AffineSubspace K V // A₀ ≤ A ∧ Module.finrank K A.direction = m} =
      Nat.card {U : Submodule K (V ⧸ A₀.direction) //
        Module.finrank K U + Module.finrank K A₀.direction = m}

def CoordinateCount [FiniteDimensional K V] : Prop :=
  ∀ A₀ : AffineSubspace K V, Nonempty A₀ → ∀ m : ℕ,
    Module.finrank K A₀.direction ≤ m →
    Nat.card {A : AffineSubspace K V // A₀ ≤ A ∧ Module.finrank K A.direction = m} =
      Nat.card {U : Submodule K (Fin
        (Module.finrank K V - Module.finrank K A₀.direction) → K) //
        Module.finrank K U = m - Module.finrank K A₀.direction}

def LowerEmpty [FiniteDimensional K V] : Prop :=
  ∀ (A₀ : AffineSubspace K V) (m : ℕ), m < Module.finrank K A₀.direction →
    IsEmpty {A : AffineSubspace K V // A₀ ≤ A ∧ Module.finrank K A.direction = m}

def FiniteFamily [Finite K] [FiniteDimensional K V] : Prop :=
  ∀ (A₀ : AffineSubspace K V) (m : ℕ),
    Finite {A : AffineSubspace K V // A₀ ≤ A ∧ Module.finrank K A.direction = m}

def SameDimension [FiniteDimensional K V] : Prop :=
  ∀ A₀ : AffineSubspace K V, Nonempty A₀ →
    Nat.card {A : AffineSubspace K V // A₀ ≤ A ∧
      Module.finrank K A.direction = Module.finrank K A₀.direction} = 1

def UpperEmpty [FiniteDimensional K V] : Prop :=
  ∀ (A₀ : AffineSubspace K V) (m : ℕ), Module.finrank K V < m →
    Nat.card {A : AffineSubspace K V // A₀ ≤ A ∧ Module.finrank K A.direction = m} = 0

def AmbientZero [FiniteDimensional K V] : Prop :=
  ∀ A₀ : AffineSubspace K V, Nonempty A₀ → Module.finrank K V = 0 → ∀ m : ℕ,
    Nat.card {A : AffineSubspace K V // A₀ ≤ A ∧ Module.finrank K A.direction = m} =
      if m = 0 then 1 else 0
end AffineContainmentExpected

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
  for (actual, expected) in #[
      (`ExactCriticalCurve.Counting.finrank_map_mkQ_add_of_le, `AffineContainmentExpected.QuotientDimension),
      (`ExactCriticalCurve.Counting.card_affineSupportsContaining, `AffineContainmentExpected.AffineCount),
      (`ExactCriticalCurve.Counting.card_affineSupportsContaining_eq_coordinateSubspaces, `AffineContainmentExpected.CoordinateCount),
      (`ExactCriticalCurve.Counting.isEmpty_affineSupportsContaining_of_lt, `AffineContainmentExpected.LowerEmpty),
      (`ExactCriticalCurve.Counting.finite_affineSupportsContaining, `AffineContainmentExpected.FiniteFamily),
      (`ExactCriticalCurve.Counting.card_affineSupportsContaining_self, `AffineContainmentExpected.SameDimension),
      (`ExactCriticalCurve.Counting.card_affineSupportsContaining_of_finrank_lt, `AffineContainmentExpected.UpperEmpty),
      (`ExactCriticalCurve.Counting.card_affineSupportsContaining_of_finrank_eq_zero, `AffineContainmentExpected.AmbientZero)] do
    auditExactTheorem actual expected
