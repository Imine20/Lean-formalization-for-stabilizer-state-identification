import ExactCriticalCurve.Counting.BinaryQBinomial
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section
open scoped BigOperators

namespace BinaryQBinomialExpected

def Product {R : Type u} [CommSemiring R] : Prop :=
  ∀ (n : ℕ) (x : R),
    (∑ r ∈ Finset.range (n + 1),
      ((Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
        Module.finrank (ZMod 2) U = r}) : R) * (2 : R) ^ (r.choose 2) * x ^ r) =
      ∏ j ∈ Finset.range n, (1 + (2 : R) ^ j * x)

def ProductDivTwo {R : Type u} [CommSemiring R] : Prop :=
  ∀ (n : ℕ) (x : R),
    (∑ r ∈ Finset.range (n + 1),
      ((Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
        Module.finrank (ZMod 2) U = r}) : R) * (2 : R) ^ (r * (r - 1) / 2) * x ^ r) =
      ∏ j ∈ Finset.range n, (1 + (2 : R) ^ j * x)

def PhaseSum : Prop :=
  ∀ n : ℕ,
    (∑ m ∈ Finset.range (n + 1),
      2 ^ (n - m) *
        Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
          Module.finrank (ZMod 2) U = m} *
          (4 ^ m * 2 ^ (m.choose 2))) =
      2 ^ n * ∏ j ∈ Finset.range n, (1 + 2 ^ (j + 1))

def AffineBridge : Prop :=
  ∀ (n : ℕ) (A₀ : AffineSubspace (ZMod 2) (Fin n → ZMod 2)),
    Nonempty A₀ → ∀ m : ℕ, Module.finrank (ZMod 2) A₀.direction ≤ m →
    Nat.card {A : AffineSubspace (ZMod 2) (Fin n → ZMod 2) //
      A₀ ≤ A ∧ Module.finrank (ZMod 2) A.direction = m} =
    Nat.card {U : Submodule (ZMod 2)
      (Fin (n - Module.finrank (ZMod 2) A₀.direction) → ZMod 2) //
      Module.finrank (ZMod 2) U = m - Module.finrank (ZMod 2) A₀.direction}

end BinaryQBinomialExpected

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
      (`ExactCriticalCurve.Counting.binaryGaussian_q_binomial, `BinaryQBinomialExpected.Product),
      (`ExactCriticalCurve.Counting.binaryGaussian_q_binomial_div_two, `BinaryQBinomialExpected.ProductDivTwo),
      (`ExactCriticalCurve.Counting.binaryGaussian_affine_phase_sum, `BinaryQBinomialExpected.PhaseSum),
      (`ExactCriticalCurve.Counting.card_affineSupportsContaining_binary, `BinaryQBinomialExpected.AffineBridge)] do
    auditExactTheorem actual expected
