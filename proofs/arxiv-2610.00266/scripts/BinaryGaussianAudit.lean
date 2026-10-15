import ExactCriticalCurve.Counting.BinaryGaussian
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
noncomputable section

namespace BinaryGaussianExpected

def Zero : Prop :=
  ∀ n : ℕ, Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
    Module.finrank (ZMod 2) U = 0} = 1

def Above : Prop :=
  ∀ {n r : ℕ}, n < r →
    Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
      Module.finrank (ZMod 2) U = r} = 0

def ProductRecurrence {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] : Prop :=
  ∀ r : ℕ,
    Nat.card {N : Submodule (ZMod 2) (V × ZMod 2) //
      Module.finrank (ZMod 2) N = r + 1} =
    Nat.card {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = r} +
      2 ^ (r + 1) *
        Nat.card {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = r + 1}

def Recurrence : Prop :=
  ∀ n r : ℕ,
    Nat.card {U : Submodule (ZMod 2) (Fin (n + 1) → ZMod 2) //
      Module.finrank (ZMod 2) U = r + 1} =
    Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
      Module.finrank (ZMod 2) U = r} +
    2 ^ (r + 1) *
      Nat.card {U : Submodule (ZMod 2) (Fin n → ZMod 2) //
        Module.finrank (ZMod 2) U = r + 1}
end BinaryGaussianExpected

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
      (`ExactCriticalCurve.Counting.binaryGaussian_zero, `BinaryGaussianExpected.Zero),
      (`ExactCriticalCurve.Counting.binaryGaussian_eq_zero_of_lt, `BinaryGaussianExpected.Above),
      (`ExactCriticalCurve.Counting.card_binarySubspaces_prod, `BinaryGaussianExpected.ProductRecurrence),
      (`ExactCriticalCurve.Counting.binaryGaussian_succ, `BinaryGaussianExpected.Recurrence)] do
    auditExactTheorem actual expected
