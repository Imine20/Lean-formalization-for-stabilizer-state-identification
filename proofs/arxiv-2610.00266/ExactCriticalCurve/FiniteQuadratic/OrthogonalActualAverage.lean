import ExactCriticalCurve.FiniteQuadratic.OrthogonalWeightSum

/-! Genuine orthogonal fixed-space averages as exact quotient quadratic refinement sums. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Counting
variable {E V : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The complete quadratic realization data, grouped by actual kernel and quotient polar. -/
def quadraticQuotientPolarEquiv (Q : QuadraticForm (ZMod 2) V) :
    (Σ K : Submodule (ZMod 2) E, EmbeddableQuadraticForm Q (E ⧸ K)) ≃
      Σ p : QuotientAlternatingData E, BinaryQuadraticEmbeddableRefinements p.2.val Q :=
  (Equiv.sigmaCongrRight (fun K => embeddableQuadraticPolarEquiv (A := E ⧸ K) Q)).trans
    (Equiv.sigmaAssoc (fun (K : Submodule (ZMod 2) E) (B : BinaryAlternatingFormData (E ⧸ K)) =>
      BinaryQuadraticEmbeddableRefinements B.val Q)).symm

variable [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V] [Fintype V]

/-- The finite formal weights are independently proved to count every actual quotient quadratic form. -/
theorem quadraticQuotient_card_weightSum (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (m : ℕ)
    (hm : finrank (ZMod 2) V=2*m) (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hg : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m) :
    (Nat.card (Σ K : Submodule (ZMod 2) E, EmbeddableQuadraticForm Q (E ⧸ K)) : ℚ)=
      quotientQuadraticWeightSum E sigma m := by
  letI : Finite E := Finite.of_equiv (Fin (finrank (ZMod 2) E) → ZMod 2)
    (Module.finBasis (ZMod 2) E).equivFun.toEquiv.symm
  letI (K : Submodule (ZMod 2) E) : Finite (E ⧸ K) := Finite.of_surjective K.mkQ K.mkQ_surjective
  letI (K : Submodule (ZMod 2) E) : Fintype (E ⧸ K) := Fintype.ofFinite _
  rw [Nat.card_congr (quadraticQuotientPolarEquiv (E := E) Q),Nat.card_sigma,Nat.cast_sum]
  unfold quotientQuadraticWeightSum
  apply Finset.sum_congr rfl
  intro p _
  exact binaryQuadraticEmbeddable_card_signed p.2.val p.2.property Q hQ _ _ m rfl
    (quotientAlternating_dimension p) hm sigma hsigma hg

/-- Burnside's true group average equals the proved finite weight sum. -/
theorem quadraticTuple_fixedSpaceAverage_eq_weightSum
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (m n : ℕ) (hm : finrank (ZMod 2) V=2*m) (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hg : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m) :
    (∑ u : BinaryQuadraticIsometryGroup Q, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=
      quotientQuadraticWeightSum (Fin n → ZMod 2) sigma m := by
  rw [quadraticTuple_fixedSpaceAverage_eq_quotients Q hQ n,
    quadraticQuotient_card_weightSum Q hQ m hm sigma hsigma hg]

/-- The negative two-dimensional initial term uses the formal zero, with no imaginary zero-dimensional space. -/
theorem quadraticTuple_fixedSpaceAverage_minus_initial
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (n : ℕ) (hm : finrank (ZMod 2) V=2)
    (hg : binaryQuadraticGaussSum Q= -2) :
    (∑ u : BinaryQuadraticIsometryGroup Q, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=
      orthogonalIncrementNewSum n 1 (-1)+orthogonalIncrementOldSum n 1 (-1) := by
  rw [quadraticTuple_fixedSpaceAverage_eq_weightSum Q hQ 1 n (by simpa using hm) (-1)
    (Or.inr rfl) (by simpa using hg)]
  simpa using quotientQuadraticWeightSum_increment (E := Fin n → ZMod 2) (-1) 1 (by omega)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Fintype W]

/-- Actual same-sign orthogonal averages differ by the new and missing-old boundary sums. -/
theorem quadraticTuple_fixedSpaceAverage_increment_sums
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (P : QuadraticForm (ZMod 2) W) (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (m n : ℕ) (hm : 0<m) (hmQ : finrank (ZMod 2) V=2*m)
    (hmP : finrank (ZMod 2) W=2*(m-1)) (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hgQ : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m)
    (hgP : binaryQuadraticGaussSum P=(sigma : ℂ)*(2 : ℂ)^(m-1)) :
    (∑ u : BinaryQuadraticIsometryGroup Q, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) -
    (∑ u : BinaryQuadraticIsometryGroup P, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) W u)) /
        (Nat.card (BinaryQuadraticIsometryGroup P) : ℚ) =
      orthogonalIncrementNewSum n m sigma+orthogonalIncrementOldSum n m sigma := by
  rw [quadraticTuple_fixedSpaceAverage_eq_weightSum Q hQ m n hmQ sigma hsigma hgQ,
    quadraticTuple_fixedSpaceAverage_eq_weightSum P hP (m-1) n hmP sigma hsigma hgP]
  simpa using quotientQuadraticWeightSum_increment (E := Fin n → ZMod 2) sigma m hm

end ExactCriticalCurve.FiniteQuadratic
