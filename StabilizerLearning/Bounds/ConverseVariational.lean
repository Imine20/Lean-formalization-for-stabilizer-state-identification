import StabilizerLearning.Bounds.ConverseExponent

/-! Exact scalar optimization for the common converse exponent.

The two slack identities use only the full source domain. In particular, no
additional inequality on `ell + t` is imposed. The conclusion concerns the
scalar variational problem and does not assert the physical learning reduction.
-/

noncomputable section
namespace StabilizerLearning

/-- The completion deficit, with the source slacks `r` and `s` expanded. -/
theorem completion_deficit_slack_identity (N M a u ell t : ℝ) :
    visibleQuadraticExponent N M - completionQuadraticExponent N M a u ell t =
      (N-M-a+u-ell)*(M-ell)+(M-ell-t)^2/2 := by
  unfold visibleQuadraticExponent completionQuadraticExponent
  ring

/-- The hidden-cost identity, with `r`, `v`, and `delta` expanded. -/
theorem hidden_cost_slack_identity (N K M a u ell : ℝ) :
    hiddenQuadraticCost N K M a u - (N-M-a+u-ell)*ell =
      ell^2/2 + (N-M-a)*((K-a+u-2*ell)-(u-ell)) + (u-ell)^2/2 := by
  unfold hiddenQuadraticCost
  ring

/-- Both the probability-side constraint and the completion budget are needed
for the product in the hidden-cost identity to be nonnegative. -/
theorem hidden_cost_ge_slack_product (N K M a u ell t : ℝ)
    (hf : scalarCompletionFeasible N K M a u ell t) :
    (N-M-a+u-ell)*ell ≤ hiddenQuadraticCost N K M a u := by
  rcases hf with ⟨hu, hua, hauK, ha, hell, hellM, hellR, ht, htM, hbudget⟩
  have hleft : 0 ≤ N-M-a := by linarith
  have hdelta : 0 ≤ K-a+u-2*ell := by linarith
  have hdelta2v : 2*(u-ell) ≤ K-a+u-2*ell := by linarith
  have hright : 0 ≤ (K-a+u-2*ell)-(u-ell) := by linarith
  have hprod := mul_nonneg hleft hright
  have hid := hidden_cost_slack_identity N K M a u ell
  nlinarith [sq_nonneg ell, sq_nonneg (u-ell)]

/-- The elementary optimization over the two nonnegative residual slacks. -/
theorem converseCost_le_slack_objective (N K M r s : ℝ)
    (hM : 0 ≤ M) (hKN : K ≤ N) (hr : 0 ≤ r)
    (hbudget : N-K ≤ r+s) :
    converseCost N K M ≤ r*M+s^2/2 := by
  unfold converseCost
  split_ifs with hbranch
  · have hprod := mul_nonneg hM (sub_nonneg.mpr hbudget)
    nlinarith [sq_nonneg (M-s)]
  · have hprod₁ := mul_nonneg hr (show 0 ≤ M-(N-K) by linarith)
    have hprod₂ := mul_nonneg (sub_nonneg.mpr hKN) (sub_nonneg.mpr hbudget)
    nlinarith [sq_nonneg (s-(N-K))]

/-- The full source feasible domain yields the common variational cost. -/
theorem converseCost_le_quadratic_deficit (N K M a u ell t : ℝ)
    (hM : 0 ≤ M) (_hMN : M ≤ N) (_hK : 0 ≤ K) (hKN : K ≤ N)
    (hf : scalarCompletionFeasible N K M a u ell t) :
    converseCost N K M ≤ hiddenQuadraticCost N K M a u +
      visibleQuadraticExponent N M - completionQuadraticExponent N M a u ell t := by
  have hhidden := hidden_cost_ge_slack_product N K M a u ell t hf
  rcases hf with ⟨hu, hua, hauK, ha, hell, hellM, hellR, ht, htM, hbudget⟩
  have hr : 0 ≤ N-M-a+u-ell := by linarith
  have hrs : N-K ≤ (N-M-a+u-ell)+(M-ell-t) := by linarith
  have hscalar := converseCost_le_slack_objective N K M
    (N-M-a+u-ell) (M-ell-t) hM hKN hr hrs
  have hdeficit := completion_deficit_slack_identity N M a u ell t
  nlinarith

/-- On the full scalar domain, the homogeneous completion exponent is already
below the label exponent. The finite formulas need their own explicit clipping. -/
theorem completion_quadratic_le_visible (N K M a u ell t : ℝ)
    (hf : scalarCompletionFeasible N K M a u ell t) :
    completionQuadraticExponent N M a u ell t ≤ visibleQuadraticExponent N M := by
  rcases hf with ⟨hu, hua, hauK, ha, hell, hellM, hellR, ht, htM, hbudget⟩
  have hp := mul_nonneg (show 0 ≤ N-M-a+u-ell by linarith)
    (show 0 ≤ M-ell by linarith)
  have hid := completion_deficit_slack_identity N M a u ell t
  nlinarith [sq_nonneg (M-ell-t)]

/-- The clipped objective used in the probability reduction has the same upper
bound, without needing a clipping-removal premise. -/
theorem clipped_quadratic_objective_le (N K M a u ell t : ℝ)
    (hM : 0 ≤ M) (hMN : M ≤ N) (hK : 0 ≤ K) (hKN : K ≤ N)
    (hf : scalarCompletionFeasible N K M a u ell t) :
    -hiddenQuadraticCost N K M a u +
      min 0 (completionQuadraticExponent N M a u ell t - visibleQuadraticExponent N M)
      ≤ -converseCost N K M := by
  have hc := converseCost_le_quadratic_deficit N K M a u ell t hM hMN hK hKN hf
  have hm := min_le_right (0 : ℝ)
    (completionQuadraticExponent N M a u ell t - visibleQuadraticExponent N M)
  linarith

/-- Increasing the ambient dimension only increases the homogeneous cost.
No extra restriction `M ≤ N₁` is needed for this scalar statement. -/
theorem converseCost_mono_dimension (N₁ N₂ K M : ℝ)
    (hM : 0 ≤ M) (hKN : K ≤ N₁) (hN : N₁ ≤ N₂) :
    converseCost N₁ K M ≤ converseCost N₂ K M := by
  unfold converseCost
  split_ifs with h₁ h₂ h₂
  · have hp := mul_nonneg hM (sub_nonneg.mpr hN)
    nlinarith
  · linarith
  · have hp₁ := mul_nonneg (show 0 ≤ M-(N₁-K) by linarith)
      (show 0 ≤ M+(N₁-K) by linarith)
    have hp₂ := mul_nonneg hM (show 0 ≤ N₂-K-M by linarith)
    nlinarith
  · have hp := mul_nonneg (sub_nonneg.mpr hN)
      (show 0 ≤ (N₂-K)+(N₁-K) by linarith)
    nlinarith

/-- Exact homogeneity, valid for every real `K,M` and positive ambient scale. -/
theorem converseCost_eq_scaled_exponent (N K M : ℝ) (hN : 0 < N) :
    converseCost N K M = N^2 * converseExponent (K/N) (M/N) := by
  have hbranch : K/N ≤ 1-M/N ↔ K ≤ N-M := by
    rw [div_le_iff₀ hN]
    field_simp
  unfold converseCost converseExponent
  by_cases h : K ≤ N-M
  · rw [if_pos h, if_pos (hbranch.mpr h)]
    field_simp
  · rw [if_neg h, if_neg (fun h' => h (hbranch.mp h'))]
    field_simp

/-- Nonnegativity includes the zero-target and full-copy boundary cases. -/
theorem converseCost_nonneg (N K M : ℝ) (hM : 0 ≤ M) (hKN : K ≤ N) :
    0 ≤ converseCost N K M := by
  unfold converseCost
  split_ifs with hbranch
  · exact mul_nonneg hM (by linarith)
  · positivity

/-- The first extremizer leaves no residual radical, cross rank, or Schur rank. -/
theorem scalarCompletionFeasible_first_extremizer (N K M : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hbranch : K ≤ N-M) :
    scalarCompletionFeasible N K M K 0 0 0 := by
  unfold scalarCompletionFeasible
  and_intros <;> linarith

/-- The second extremizer uses all hidden dimension and the remaining Schur rank. -/
theorem scalarCompletionFeasible_second_extremizer (N K M : ℝ)
    (hM : 0 ≤ M) (hMN : M ≤ N) (hKN : K ≤ N) (hbranch : N-M ≤ K) :
    scalarCompletionFeasible N K M (N-M) 0 0 (K+M-N) := by
  unfold scalarCompletionFeasible
  and_intros <;> linarith

/-- Exact value at the first extremizer, including the transition itself. -/
theorem clipped_objective_first_extremizer (N K M : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hbranch : K ≤ N-M) :
    -hiddenQuadraticCost N K M K 0 +
      min 0 (completionQuadraticExponent N M K 0 0 0 - visibleQuadraticExponent N M)
      = -converseCost N K M := by
  have hf := scalarCompletionFeasible_first_extremizer N K M hM hK hbranch
  have he := completion_quadratic_le_visible N K M K 0 0 0 hf
  rw [min_eq_right (sub_nonpos.mpr he)]
  unfold hiddenQuadraticCost completionQuadraticExponent visibleQuadraticExponent converseCost
  rw [if_pos hbranch]
  ring

/-- Exact value at the second extremizer, including the transition itself. -/
theorem clipped_objective_second_extremizer (N K M : ℝ)
    (hM : 0 ≤ M) (hMN : M ≤ N) (hKN : K ≤ N) (hbranch : N-M ≤ K) :
    -hiddenQuadraticCost N K M (N-M) 0 +
      min 0 (completionQuadraticExponent N M (N-M) 0 0 (K+M-N) -
        visibleQuadraticExponent N M) = -converseCost N K M := by
  have hf := scalarCompletionFeasible_second_extremizer N K M hM hMN hKN hbranch
  have he := completion_quadratic_le_visible N K M (N-M) 0 0 (K+M-N) hf
  rw [min_eq_right (sub_nonpos.mpr he)]
  unfold hiddenQuadraticCost completionQuadraticExponent visibleQuadraticExponent converseCost
  split_ifs with hother
  · have heq : K = N-M := by linarith
    rw [heq]
    ring
  · ring

/-- The clipped scalar maximum is attained for every point of the closed
parameter domain, not merely approached along a sequence. -/
theorem exists_clipped_objective_eq_neg_converseCost (N K M : ℝ)
    (hM : 0 ≤ M) (hMN : M ≤ N) (hK : 0 ≤ K) (hKN : K ≤ N) :
    ∃ a u ell t : ℝ, scalarCompletionFeasible N K M a u ell t ∧
      -hiddenQuadraticCost N K M a u +
        min 0 (completionQuadraticExponent N M a u ell t - visibleQuadraticExponent N M)
        = -converseCost N K M := by
  by_cases hbranch : K ≤ N-M
  · exact ⟨K, 0, 0, 0, scalarCompletionFeasible_first_extremizer N K M hM hK hbranch,
      clipped_objective_first_extremizer N K M hM hK hbranch⟩
  · exact ⟨N-M, 0, 0, K+M-N,
      scalarCompletionFeasible_second_extremizer N K M hM hMN hKN (le_of_not_ge hbranch),
      clipped_objective_second_extremizer N K M hM hMN hKN (le_of_not_ge hbranch)⟩

/-- Exact maximum over the complete scalar domain. -/
theorem isGreatest_clipped_quadratic_objective (N K M : ℝ)
    (hM : 0 ≤ M) (hMN : M ≤ N) (hK : 0 ≤ K) (hKN : K ≤ N) :
    IsGreatest {z : ℝ | ∃ a u ell t : ℝ, scalarCompletionFeasible N K M a u ell t ∧
      z = -hiddenQuadraticCost N K M a u +
        min 0 (completionQuadraticExponent N M a u ell t - visibleQuadraticExponent N M)}
      (-converseCost N K M) := by
  constructor
  · obtain ⟨a, u, ell, t, hf, heq⟩ :=
      exists_clipped_objective_eq_neg_converseCost N K M hM hMN hK hKN
    exact ⟨a, u, ell, t, hf, heq.symm⟩
  · rintro z ⟨a, u, ell, t, hf, rfl⟩
    exact clipped_quadratic_objective_le N K M a u ell t hM hMN hK hKN hf

theorem converseCost_one_eq_exponent (α β : ℝ) :
    converseCost 1 α β = converseExponent α β := rfl

/-- The source limiting maximum is exactly `-J`, on the entire closed square. -/
theorem isGreatest_limiting_clipped_objective (α β : ℝ)
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    IsGreatest {z : ℝ | ∃ a u ell t : ℝ, scalarCompletionFeasible 1 α β a u ell t ∧
      z = -hiddenQuadraticCost 1 α β a u +
        min 0 (completionQuadraticExponent 1 β a u ell t - visibleQuadraticExponent 1 β)}
      (-converseExponent α β) :=
  isGreatest_clipped_quadratic_objective 1 α β hβ hβ1 hα hα1

theorem converseCost_at_transition (N M : ℝ) :
    converseCost N (N-M) M = M^2/2 := by
  unfold converseCost
  rw [if_pos (le_refl _)]
  ring

theorem converseCost_zero_visible (N K : ℝ) (hKN : K ≤ N) :
    converseCost N K 0 = 0 := by
  simp [converseCost, hKN]

theorem converseCost_zero_deficit (N M : ℝ) (hM : 0 ≤ M) :
    converseCost N N M = 0 := by
  unfold converseCost
  split_ifs with hbranch
  · have hM0 : M = 0 := by linarith
    simp [hM0]
  · simp

theorem converseCost_full_visible (N K : ℝ) (hK : 0 ≤ K) :
    converseCost N K N = (N-K)^2/2 := by
  unfold converseCost
  split_ifs with hbranch
  · have hK0 : K = 0 := by linarith
    rw [hK0]
    ring
  · rfl

theorem converseExponent_at_transition (β : ℝ) :
    converseExponent (1-β) β = β^2/2 := converseCost_at_transition 1 β

theorem converseExponent_zero_visible (α : ℝ) (hα : α ≤ 1) :
    converseExponent α 0 = 0 := converseCost_zero_visible 1 α hα

theorem converseExponent_at_one (β : ℝ) (hβ : 0 ≤ β) :
    converseExponent 1 β = 0 := converseCost_zero_deficit 1 β hβ

theorem converseExponent_full_visible (α : ℝ) (hα : 0 ≤ α) :
    converseExponent α 1 = (1-α)^2/2 := converseCost_full_visible 1 α hα

/-- Strict positivity in the source nontrivial learning regime. -/
theorem converseCost_pos (N K M : ℝ) (hM : 0 < M) (hKN : K < N) :
    0 < converseCost N K M := by
  unfold converseCost
  split_ifs with hbranch
  · exact mul_pos hM (by linarith)
  · exact div_pos (sq_pos_of_pos (sub_pos.mpr hKN)) (by norm_num)

theorem converseExponent_pos_on_source_domain (α β : ℝ) (hβ : 0 < β) (hα : α < 1) :
    0 < converseExponent α β := converseCost_pos 1 α β hβ hα

end StabilizerLearning
