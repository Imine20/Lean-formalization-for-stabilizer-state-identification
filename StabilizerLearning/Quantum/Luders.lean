import StabilizerLearning.Quantum.BornProbability

/-! Trace identities for the original normalized Lüders experiment. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning.Quantum
variable {ι : Type*} [Fintype ι]

theorem born_mul_projection_sandwich (P Q ρ : Matrix ι ι ℂ)
    (hPP : P * P = P) (hPQ : Commute P Q) :
    born (P * Q) (P * ρ * P) = born (P * Q) ρ := by
  have hPQP : P * Q * P = P * Q := by
    rw [hPQ.eq, Matrix.mul_assoc, hPP, ← hPQ.eq]
  have hp : P * (P * Q * P) = P * Q := by
    rw [hPQP, ← Matrix.mul_assoc, hPP]
  unfold born
  congr 1
  calc
    Matrix.trace (P * Q * (P * ρ * P)) =
        Matrix.trace ((P * Q * P) * ρ * P) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (P * (P * Q * P) * ρ) := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [hp]

theorem born_luders_renormalization (E σ : Matrix ι ι ℂ) (q : ℝ) (hq : q ≠ 0) :
    q * born E (((q : ℂ)⁻¹) • σ) = born E σ := by
  unfold born
  rw [Matrix.mul_smul, Matrix.trace_smul, ← Complex.ofReal_inv]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem commuting_projection_mul_isHermitian (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hPQ : Commute P Q) :
    (P * Q).IsHermitian := by
  change (P * Q).conjTranspose = P * Q
  rw [Matrix.conjTranspose_mul, hP.eq, hQ.eq, hPQ.eq]

theorem commuting_projection_mul_self (P Q : Matrix ι ι ℂ)
    (hPP : P * P = P) (hQQ : Q * Q = Q) (hPQ : Commute P Q) :
    (P * Q) * (P * Q) = P * Q := by
  calc
    _ = (P * Q * P) * Q := by simp only [Matrix.mul_assoc]
    _ = (Q * (P * P)) * Q := by rw [hPQ.eq]; simp only [Matrix.mul_assoc]
    _ = (P * Q) * Q := by rw [hPP, ← hPQ.eq]
    _ = _ := by rw [Matrix.mul_assoc, hQQ]

theorem commuting_projection_mul_posSemidef (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q) (hPQ : Commute P Q) :
    (P * Q).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (P * Q)
  rw [(commuting_projection_mul_isHermitian P Q hP hQ hPQ).eq,
    commuting_projection_mul_self P Q hPP hQQ hPQ] at h
  exact h

variable [DecidableEq ι]

theorem sum_born_of_sum_eq_one {Ω : Type*} [Fintype Ω]
    (P : Ω → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) (hP : ∑ i, P i = 1) :
    (∑ i, born (P i) ρ) = (Matrix.trace ρ).re := by
  simp only [born]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hP, one_mul]

/-- The zero-probability branch of the actual normalized instrument is justified
by positivity, rather than deleted from the statement. -/
theorem luders_outcome_eq_born (P Q ρ : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPQ : Commute P Q)
    (hρ : ρ.PosSemidef) :
    (let q := born P ρ
     if 0 < q then q * born (P * Q) (((q : ℂ)⁻¹) • (P * ρ * P)) else 0) =
      born (P * Q) ρ := by
  dsimp only
  by_cases hq : 0 < born P ρ
  · rw [if_pos hq, born_luders_renormalization _ _ _ (ne_of_gt hq),
      born_mul_projection_sandwich P Q ρ hPP hPQ]
  · rw [if_neg hq]
    have hn := born_nonneg_of_posSemidef P ρ (projection_posSemidef P hP hPP) hρ
    have hz : born P ρ = 0 := le_antisymm (le_of_not_gt hq) hn
    have hs := projection_sandwich_eq_zero_of_born_zero P ρ hP hPP hρ hz
    rw [← born_mul_projection_sandwich P Q ρ hPP hPQ, hs]
    simp [born]

/-- The positive-probability conditional state is an actual density matrix. -/
def normalizedLudersState (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (ρ : DensityMatrix ι)
    (hq : 0 < born P ρ.matrix) : DensityMatrix ι where
  matrix := ((born P ρ.matrix : ℂ)⁻¹) • (P * ρ.matrix * P)
  positive := by
    apply (projection_sandwich_posSemidef P ρ.matrix hP ρ.positive).smul
    rw [← Complex.ofReal_inv]
    exact_mod_cast (inv_nonneg.mpr (le_of_lt hq))
  trace_one := by
    rw [Matrix.trace_smul, trace_projection_sandwich P ρ.matrix hPP,
      trace_mul_eq_ofReal_born_of_posSemidef P ρ.matrix
        (projection_posSemidef P hP hPP) ρ.positive]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hq))

theorem conditional_luders_born_mem_Icc (P Q : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q) (hPQ : Commute P Q)
    (ρ : DensityMatrix ι) (hq : 0 < born P ρ.matrix) :
    born (P * Q) (((born P ρ.matrix : ℂ)⁻¹) • (P * ρ.matrix * P)) ∈
      Set.Icc (0 : ℝ) 1 := by
  let σ := normalizedLudersState P hP hPP ρ hq
  exact born_projection_mem_Icc (P * Q) σ.matrix
    (commuting_projection_mul_isHermitian P Q hP hQ hPQ)
    (commuting_projection_mul_self P Q hPP hQQ hPQ) σ.positive σ.trace_one

/-- Summing the genuine conditional experiment over a complete projective
measurement yields the undisturbed Born score for every commuting test effect. -/
theorem luders_average_eq_born {Ω : Type*} [Fintype Ω]
    (P : Ω → Matrix ι ι ℂ) (Q ρ : Matrix ι ι ℂ)
    (hP : ∀ i, (P i).IsHermitian) (hPP : ∀ i, P i * P i = P i)
    (hPQ : ∀ i, Commute (P i) Q) (hρ : ρ.PosSemidef) (hsum : ∑ i, P i = 1) :
    (∑ i, let q := born (P i) ρ
      if 0 < q then q * born (P i * Q) (((q : ℂ)⁻¹) • (P i * ρ * P i)) else 0) =
        born Q ρ := by
  simp_rw [luders_outcome_eq_born _ _ _ (hP _) (hPP _) (hPQ _) hρ]
  simp only [born]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    ← Matrix.sum_mul, hsum, one_mul]

end StabilizerLearning.Quantum
