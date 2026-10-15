import StabilizerLearning.FixedConstraints.OperationalPrior

/-! Actual phase-compatible neighborhoods of the original basis-free reports.
Realizability is defined by the original generic physical states. -/
noncomputable section
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- Both assignments refer to exactly the same fixed physical Pauli section. -/
def ReportsCompatible (W : Constraint p n m) (y r : Report W) : Prop :=
  restrictAssignment p (inf_le_left : y.1.val ⊓ r.1.val ≤ y.1.val) y.2 =
    restrictAssignment p (inf_le_right : y.1.val ⊓ r.1.val ≤ r.1.val) r.2

/-- Intrinsic distance between two legal m-dimensional report subspaces. -/
def reportDistance (W : Constraint p n m) (y r : Report W) : ℕ :=
  m - Module.finrank (ZMod p) ↥(y.1.val ⊓ r.1.val)

/-- The paper target set, retaining only realizable generic exact reports. -/
def IsGenericTarget (W : Constraint p n m) (y : Report W) : Prop :=
  ∃ x : GenericState W, genericStateReport W x.val x.property = y

/-- The actual compatible list around an arbitrary original legal report. -/
def genericCompatibleList (W : Constraint p n m) (D : ℕ) (r : Report W) : Finset (Report W) :=
  Finset.univ.filter (fun y => IsGenericTarget W y ∧
    reportDistance W y r ≤ D ∧ ReportsCompatible W y r)

/-- Maximum actual list size; no transitivity or equality of list sizes assumed. -/
def genericCompatibleListSize (W : Constraint p n m) (D : ℕ) : ℕ :=
  Finset.univ.sup (fun r : Report W => (genericCompatibleList W D r).card)

@[simp] theorem mem_genericCompatibleList (W : Constraint p n m) (D : ℕ)
    (r y : Report W) : y ∈ genericCompatibleList W D r ↔
      IsGenericTarget W y ∧ reportDistance W y r ≤ D ∧ ReportsCompatible W y r := by
  simp [genericCompatibleList]

theorem card_genericCompatibleList_le_size (W : Constraint p n m) (D : ℕ)
    (r : Report W) : (genericCompatibleList W D r).card ≤ genericCompatibleListSize W D :=
  Finset.le_sup (f := fun r : Report W => (genericCompatibleList W D r).card)
    (Finset.mem_univ r)

end StabilizerLearning.FixedConstraints
