import StabilizerLearning.FixedConstraints.GenericIncidence
import StabilizerLearning.FixedConstraints.GenericNonempty
import StabilizerLearning.FiniteCopy.LabelTransport

/-! The original generic prior decomposes into the actual finite transverse
charts, with their true incidence marginal. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- Actual public Lagrangian completions of W, independent of any state. -/
abbrev ConstraintFrame (W : Constraint p n m) :=
  {M : Lagrangian p n // W.subspace ≤ M.val}

noncomputable instance constraintFrameFintype (W : Constraint p n m) :
    Fintype (ConstraintFrame W) := Fintype.ofFinite _

theorem nonempty_constraintFrame (W : Constraint p n m) : Nonempty (ConstraintFrame W) := by
  obtain ⟨M,hM⟩ := exists_lagrangian_containing W
  exact ⟨⟨M,hM⟩⟩

/-- All original distinct states transverse to a specified actual Lagrangian. -/
abbrev StateChart (M : Lagrangian p n) :=
  {x : StabilizerState p n //
    ((stabilizerLabelStateEquiv p n).symm x).1.val ⊓ M.val = ⊥}

noncomputable instance stateChartFintype (M : Lagrangian p n) :
    Fintype (StateChart M) := Fintype.ofFinite _

theorem nonempty_stateChart (M : Lagrangian p n) : Nonempty (StateChart M) := by
  obtain ⟨x,hx⟩ := exists_transverse_state M
  exact ⟨⟨x,hx⟩⟩

theorem stateChart_isGeneric (W : Constraint p n m) (M : ConstraintFrame W)
    (x : StateChart M.val) : IsGenericState W x.val :=
  isGenericLagrangian_of_completion W _ M.val M.property x.property

noncomputable instance stateCompletionFintype (W : Constraint p n m)
    (x : StabilizerState p n) : Fintype (StateCompletion W x) := Fintype.ofFinite _

/-- Actual compatible state-frame pairs, first indexed by the generic state. -/
abbrev GenericIncidence (W : Constraint p n m) :=
  (x : GenericState W) × StateCompletion W x.val

noncomputable instance genericIncidenceFintype (W : Constraint p n m) :
    Fintype (GenericIncidence W) := inferInstance

/-- The same actual incidence pairs, now indexed by their revealed frame. -/
def genericIncidenceChartEquiv (W : Constraint p n m) :
    GenericIncidence W ≃ ((M : ConstraintFrame W) × StateChart M.val) where
  toFun i := ⟨⟨i.2.val,i.2.property.1⟩,⟨i.1.val,i.2.property.2⟩⟩
  invFun i := ⟨⟨i.2.val,stateChart_isGeneric W i.1 i.2⟩,
    ⟨i.1.val,i.1.property,i.2.property⟩⟩
  left_inv i := by rcases i with ⟨⟨x,hx⟩,⟨M,hWM,hLM⟩⟩; rfl
  right_inv i := by rcases i with ⟨⟨M,hWM⟩,⟨x,hx⟩⟩; rfl

/-- A positive common degree, selected from the nonempty actual generic prior. -/
def genericIncidenceDegree (W : Constraint p n m) : ℕ :=
  Nat.card (StateCompletion W (Classical.choice (nonempty_genericState W)).val)

theorem card_stateCompletion_eq_degree (W : Constraint p n m) (x : GenericState W) :
    Nat.card (StateCompletion W x.val) = genericIncidenceDegree W :=
  card_stateCompletion_eq W x.val
    (Classical.choice (nonempty_genericState W)).val x.property
    (Classical.choice (nonempty_genericState W)).property

theorem genericIncidenceDegree_pos (W : Constraint p n m) :
    0 < genericIncidenceDegree W :=
  card_stateCompletion_pos W _ (Classical.choice (nonempty_genericState W)).property

theorem card_genericIncidence (W : Constraint p n m) :
    Nat.card (GenericIncidence W) = Nat.card (GenericState W) * genericIncidenceDegree W := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [← Nat.card_eq_fintype_card, card_stateCompletion_eq_degree]
  simp [Nat.card_eq_fintype_card]

theorem card_genericIncidence_pos (W : Constraint p n m) :
    0 < Nat.card (GenericIncidence W) := by
  letI := nonempty_genericState W
  rw [card_genericIncidence]
  exact Nat.mul_pos Nat.card_pos (genericIncidenceDegree_pos W)

/-- Uniform incidence gives exactly the original uniform generic-state marginal. -/
theorem uniform_incidence_state_marginal (W : Constraint p n m)
    (f : StabilizerState p n → ℝ) :
    uniformFiniteMean (fun i : GenericIncidence W => f i.1.val) =
      uniformFiniteMean (fun x : GenericState W => f x.val) := by
  unfold uniformFiniteMean
  rw [Fintype.sum_sigma, card_genericIncidence]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [← Nat.card_eq_fintype_card, card_stateCompletion_eq_degree]
  rw [← Finset.mul_sum]
  have hd : (genericIncidenceDegree W : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (genericIncidenceDegree_pos W))
  push_cast
  field_simp

/-- True marginal of the actual frame under uniform incidence sampling. -/
def incidenceFrameWeight (W : Constraint p n m) (M : ConstraintFrame W) : ℝ :=
  (Nat.card (StateChart M.val) : ℝ) / Nat.card (GenericIncidence W)

theorem incidenceFrameWeight_nonneg (W : Constraint p n m) (M : ConstraintFrame W) :
    0 ≤ incidenceFrameWeight W M := by
  unfold incidenceFrameWeight
  positivity

/-- Uniform conditioning within every actual frame chart. -/
theorem uniform_incidence_chart_decomposition (W : Constraint p n m)
    (f : StabilizerState p n → ℝ) :
    uniformFiniteMean (fun i : GenericIncidence W => f i.1.val) =
      ∑ M : ConstraintFrame W, incidenceFrameWeight W M *
        uniformFiniteMean (fun x : StateChart M.val => f x.val) := by
  have heq := uniformFiniteMean_comp_equiv (genericIncidenceChartEquiv W)
    (fun i : (M : ConstraintFrame W) × StateChart M.val => f i.2.val)
  change uniformFiniteMean (fun i : GenericIncidence W => f i.1.val) =
    uniformFiniteMean (fun i : (M : ConstraintFrame W) × StateChart M.val => f i.2.val) at heq
  rw [heq]
  unfold uniformFiniteMean incidenceFrameWeight
  rw [Fintype.sum_sigma, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro M _
  letI := nonempty_stateChart M.val
  have hc : (Nat.card (StateChart M.val) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt Nat.card_pos)
  have hi : (Nat.card (GenericIncidence W) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (card_genericIncidence_pos W))
  have hcard : Nat.card ((M : ConstraintFrame W) × StateChart M.val) =
      Nat.card (GenericIncidence W) :=
    (Nat.card_congr (genericIncidenceChartEquiv W)).symm
  rw [hcard]
  field_simp

/-- The genuine fixed-W incidence decomposition for every function on original
physical states; all regularity and nonemptiness hypotheses have been proved. -/
theorem generic_mean_eq_chart_mixture (W : Constraint p n m)
    (f : StabilizerState p n → ℝ) :
    uniformFiniteMean (fun x : GenericState W => f x.val) =
      ∑ M : ConstraintFrame W, incidenceFrameWeight W M *
        uniformFiniteMean (fun x : StateChart M.val => f x.val) := by
  rw [← uniform_incidence_state_marginal W f]
  exact uniform_incidence_chart_decomposition W f

theorem sum_incidenceFrameWeight (W : Constraint p n m) :
    ∑ M : ConstraintFrame W, incidenceFrameWeight W M = 1 := by
  have h := generic_mean_eq_chart_mixture W (fun _ => 1)
  letI := nonempty_genericState W
  have hc (M : ConstraintFrame W) : uniformFiniteMean (fun _ : StateChart M.val => (1:ℝ)) = 1 := by
    letI := nonempty_stateChart M.val
    simp [uniformFiniteMean, Nat.card_eq_fintype_card, Fintype.card_ne_zero]
  simp_rw [hc, mul_one] at h
  symm
  convert h using 1
  simp [uniformFiniteMean, Nat.card_eq_fintype_card, Fintype.card_ne_zero]

end StabilizerLearning.FixedConstraints
