import ExactCriticalCurve.Quantum.ShorteningExceptionalScalar

/-! # The exceptional physical scalar is derived from the actual ordinary product -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary

/-- The actual exceptional block has the transported closed product value. -/
theorem exceptionalRelation_scalar_closed_product (n r : ℕ) {m : ℕ} (h4 : 4 ∣ m+1)
    (N : ExceptionalDefect (m+1) (r+1)) (hn : m ≤ n) :
    ∃ θ : ℝ,
      (stochasticRelationSum n (m+1) * exceptionalCSSGrade n (m+1) (r+1) =
          θ • exceptionalCSSGrade n (m+1) (r+1) ∧
       exceptionalCSSGrade n (m+1) (r+1) * stochasticRelationSum n (m+1) =
          θ • exceptionalCSSGrade n (m+1) (r+1)) ∧
      (θ : ℂ) = ((2 : ℂ)^n+(2 : ℂ)^((m+1)-2)) *
        ((Fintype.card (StochasticIsometryGroup m) : ℂ) /
          ((2 : ℂ)^(r*(m-r-2)) * ∏ j ∈ Finset.range r, ((2 : ℂ)^(j+1)-1)) *
            ∏ j ∈ Finset.range r, ((2 : ℂ)^n+(2 : ℂ)^(m-r-1+j))) := by
  let M : OrdinaryDefect m r := (shorteningDefectEquiv h4 r).symm N
  obtain ⟨θ,hθ,hval⟩ := ordinaryRelation_scalar_closed_product (n := n) M hn
  let f : ℝ := (2 : ℝ)^n+(2 : ℝ)^((m+1)-2)
  have hf : (f : ℂ)=(2 : ℂ)^n+(2 : ℂ)^((m+1)-2) := by simp [f]
  have hc : stochasticRelationSum n m * ordinaryCSSGrade n m r =
      (θ : ℂ) • ordinaryCSSGrade n m r := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hθ.1
  have hl : stochasticRelationSum n (m+1) * exceptionalCSSGrade n (m+1) (r+1) =
      (f*θ) • exceptionalCSSGrade n (m+1) (r+1) := by
    have h := shortening_exceptional_scalar_of_ordinary n r h4 (θ : ℂ) hc
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change stochasticRelationSum n (m+1) * exceptionalCSSGrade n (m+1) (r+1) =
      ((f*θ : ℝ) : ℂ) • exceptionalCSSGrade n (m+1) (r+1)
    rw [Complex.ofReal_mul,hf]
    exact h
  have hA := compressedRelationSpan_isHermitian n (m+1)
    (stochasticRelationSum_mem_compressedRelationSpan n (m+1))
  have hE := exceptionalCSSGrade_isHermitian n (m+1) (r+1)
  have hr := congrArg Matrix.conjTranspose hl
  have hr' : exceptionalCSSGrade n (m+1) (r+1) * stochasticRelationSum n (m+1) =
      (f*θ) • exceptionalCSSGrade n (m+1) (r+1) := by
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_smul,star_trivial,hA.eq,hE.eq] using hr
  refine ⟨f*θ,⟨hl,hr'⟩,?_⟩
  rw [Complex.ofReal_mul,hf,hval]

/-- Positive-k form with the actual predecessor and no hidden subtraction convention. -/
theorem exceptionalRelation_scalar_closed_product_positive (n r : ℕ) {k : ℕ}
    (hk : 0<k) (h4 : 4 ∣ k) (N : ExceptionalDefect k (r+1)) (hn : k-1 ≤ n) :
    ∃ θ : ℝ,
      (stochasticRelationSum n k * exceptionalCSSGrade n k (r+1) = θ • exceptionalCSSGrade n k (r+1) ∧
       exceptionalCSSGrade n k (r+1) * stochasticRelationSum n k = θ • exceptionalCSSGrade n k (r+1)) ∧
      (θ : ℂ) = ((2 : ℂ)^n+(2 : ℂ)^(k-2)) *
        ((Fintype.card (StochasticIsometryGroup (k-1)) : ℂ) /
          ((2 : ℂ)^(r*((k-1)-r-2)) * ∏ j ∈ Finset.range r, ((2 : ℂ)^(j+1)-1)) *
            ∏ j ∈ Finset.range r, ((2 : ℂ)^n+(2 : ℂ)^((k-1)-r-1+j))) := by
  cases k with
  | zero => omega
  | succ m => exact exceptionalRelation_scalar_closed_product n r h4 N hn

end ExactCriticalCurve.Quantum
