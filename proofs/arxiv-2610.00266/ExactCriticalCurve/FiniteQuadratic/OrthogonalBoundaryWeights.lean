import ExactCriticalCurve.FiniteQuadratic.OrthogonalQuotientBoundary
import ExactCriticalCurve.Counting.BinaryGaussianIdentities

/-! Finite weighted boundary sums from the actual quotient polar data. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

instance quotientAlternatingDataFinite : Finite (QuotientAlternatingData E) := by
  letI : Finite E := Finite.of_equiv (Fin (finrank (ZMod 2) E) → ZMod 2)
    (Module.finBasis (ZMod 2) E).equivFun.toEquiv.symm
  letI : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun K : Submodule (ZMod 2) E => (K : Set E)) SetLike.coe_injective
  letI (K : Submodule (ZMod 2) E) : Finite (E ⧸ K) := Finite.of_surjective K.mkQ K.mkQ_surjective
  unfold QuotientAlternatingData
  infer_instance

instance quotientAlternatingDataFintype : Fintype (QuotientAlternatingData E) := Fintype.ofFinite _

/-- Weighted quotient boundaries have exactly the Gaussian flag fibers already counted. -/
theorem quotientAlternating_boundary_weighted_sum (ell : ℕ) (w : ℕ → ℚ) :
    (∑ p : QuotientAlternatingData E,
      if finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell
        then w (quotientAlternatingHalfRank p) else 0) =
      ∑ a ∈ Finset.range (ell+1),
        (Counting.binaryGaussian (finrank (ZMod 2) E) (ell+a) : ℚ) *
        (Counting.binaryGaussian (ell+a) (ell-a) : ℚ) *
        (nondegenerateAlternatingCount (2*a) : ℚ) * w a := by
  letI : Finite (AlternatingBoundaryInvariant E ell) :=
    Finite.of_equiv _ (quotientAlternatingBoundaryEquiv (E := E) ell)
  letI : Fintype (AlternatingBoundaryInvariant E ell) := Fintype.ofFinite _
  have hs : (∑ p : QuotientAlternatingData E,
      if finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell
        then w (quotientAlternatingHalfRank p) else 0) =
      ∑ p : {p : QuotientAlternatingData E //
        finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell},
          w (quotientAlternatingHalfRank p.val) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hs]
  rw [Fintype.sum_equiv (quotientAlternatingBoundaryEquiv (E := E) ell)
    (fun p => w (quotientAlternatingHalfRank p.val))
    (fun p => w (alternatingBoundaryIndex ell p).val)
    (fun p => congrArg w (quotientAlternatingBoundaryEquiv_index ell p).symm)]
  rw [← Fintype.sum_fiberwise' (alternatingBoundaryIndex (E := E) ell)
    (fun a => w a.val),← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    alternatingBoundaryIndexFiber_card]
  by_cases ha : ell+a.val ≤ finrank (ZMod 2) E
  · rw [if_pos ha,← Counting.binaryGaussian_symmetry _ _ ha]
    simp [Nat.cast_mul,mul_assoc]
  · rw [if_neg ha,Counting.binaryGaussian_eq_zero_of_lt (by omega : finrank (ZMod 2) E<ell+a.val)]
    simp

/-- The same boundary mask may be expressed by the radical plus half-rank height. -/
theorem quotientAlternating_height_weighted_sum (ell : ℕ) (w : ℕ → ℚ) :
    (∑ p : QuotientAlternatingData E,
      if finrank (ZMod 2) (LinearMap.ker p.2.val)+quotientAlternatingHalfRank p=ell
        then w (quotientAlternatingHalfRank p) else 0) =
      ∑ a ∈ Finset.range (ell+1),
        (Counting.binaryGaussian (finrank (ZMod 2) E) (ell+a) : ℚ) *
        (Counting.binaryGaussian (ell+a) (ell-a) : ℚ) *
        (nondegenerateAlternatingCount (2*a) : ℚ) * w a := by
  rw [← quotientAlternating_boundary_weighted_sum ell w]
  apply Finset.sum_congr rfl
  intro p _
  have hd := quotientAlternating_dimension p
  have he : (finrank (ZMod 2) (LinearMap.ker p.2.val)+quotientAlternatingHalfRank p=ell) ↔
    finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell := by omega
  simp only [he]

end ExactCriticalCurve.FiniteQuadratic
