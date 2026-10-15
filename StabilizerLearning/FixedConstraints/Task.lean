import StabilizerLearning.Quantum.Stabilizer

/-! Original fixed-W task, not the smaller transverse-coordinate task.
The learner reports before the verifier's outcome is available. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.FixedConstraints
open Quantum

variable (p : ℕ) [Fact p.Prime]

structure Constraint (n m : ℕ) where
  subspace : Submodule (ZMod p) (PhaseSpace p n)
  dimension_allowed : m ≤ n
  isotropic : IsIsotropic subspace
  dimension : Module.finrank (ZMod p) subspace = n - m

variable {p} {n m : ℕ}

def ReportSubspace (W : Constraint p n m) :=
  {K : Submodule (ZMod p) (PhaseSpace p n) //
    IsIsotropic K ∧ Module.finrank (ZMod p) K = m ∧
    (∀ z ∈ K, z ∈ symplecticOrthogonal W.subspace) ∧
    K ⊓ W.subspace = ⊥}

instance reportSubspaceFinite (W : Constraint p n m) : Finite (ReportSubspace W) := by
  unfold ReportSubspace
  infer_instance

abbrev Report (W : Constraint p n m) :=
  (K : ReportSubspace W) × Assignment p n K.val

noncomputable instance reportFintype (W : Constraint p n m) : Fintype (Report W) :=
  Fintype.ofFinite _

/-- All announced operators have the proposed eigenvalue on the input ray.
No canonical choice among the several correct reports of an exceptional state is made. -/
def Valid (W : Constraint p n m) (x : StabilizerState p n) (r : Report W) : Prop :=
  ∀ z : r.1.val,
    pauli p n z * x.val = eigenPhase p (r.2.val z) • x.val

def reportProjector (W : Constraint p n m) (r : Report W) :=
  jointProjector p n r.1.val r.2

abbrev Learner (W : Constraint p n m) (k : ℕ) :=
  POVM (Fin k → Configuration p n) (Report W)

def exactStatewise (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) : ℝ := by
  classical
  exact ∑ r, if Valid W x r then born (M.effect r) (tensorPower x.val k) else 0

/-- The genuine outcome-averaged Lüders verification experiment on one independent
test copy. Zero-probability outcomes contribute zero. The test copy is not part of k. -/
def verificationPayoff (W : Constraint p n m) (x : StabilizerState p n)
    (r : Report W) : ℝ := by
  classical
  exact ∑ ν : Assignment p n W.subspace,
    let P := jointProjector p n W.subspace ν
    let q := born P x.val
    if 0 < q then
      q * born (P * reportProjector W r) (((q : ℂ)⁻¹) • (P * x.val * P))
    else 0

def verificationStatewise (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) : ℝ :=
  ∑ r, born (M.effect r) (tensorPower x.val k) * verificationPayoff W x r

inductive Criterion where
  | exact
  | verification
  deriving DecidableEq

inductive Aggregation where
  | worstCase
  | average
  deriving DecidableEq

def statewise (c : Criterion) (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) : ℝ :=
  match c with
  | .exact => exactStatewise W k M x
  | .verification => verificationStatewise W k M x

def performance (c : Criterion) (a : Aggregation) (W : Constraint p n m)
    (k : ℕ) (M : Learner W k) : ℝ :=
  match a with
  | .worstCase => sInf (Set.range (statewise c W k M))
  | .average => (∑ x, statewise c W k M x) / (Fintype.card (StabilizerState p n) : ℝ)

/-- Supremum over every normalized PSD collective learner POVM on the complete copy space. -/
def optimal (c : Criterion) (a : Aggregation) (W : Constraint p n m) (k : ℕ) : ℝ :=
  sSup (Set.range (performance c a W k))

end StabilizerLearning.FixedConstraints
