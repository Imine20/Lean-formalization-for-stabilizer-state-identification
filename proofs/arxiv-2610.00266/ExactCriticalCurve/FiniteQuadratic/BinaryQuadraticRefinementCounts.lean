import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRefinementRadical

/-! Complete actual Gauss-fiber counts for one fixed alternating form.
No alternating-form stratum count or group-order formula enters these statements. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem binaryQuadraticRefinement_gauss_support
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (t : ℕ) (ht : finrank (ZMod 2) C = 2*t)
    (P : BinaryQuadraticRefinements q.polarBilin) :
    binaryQuadraticGaussSum P.val = 0 ∨
      binaryQuadraticGaussSum P.val = (2 : ℂ)^(finrank (ZMod 2) (binaryPolarRadical q)+t) ∨
      binaryQuadraticGaussSum P.val = -((2 : ℂ)^(finrank (ZMod 2) (binaryPolarRadical q)+t)) := by
  let e := binaryQuadraticRefinementSplitEquiv q C hC
  by_cases hl : (e P).2 = 0
  · right
    have hn : LinearMap.BilinForm.Nondegenerate (e P).1.val.polarBilin := by
      rw [(e P).1.property]
      exact binaryRadical_complement_nondegenerate q C hC
    have hs := binaryQuadraticGaussInteger_eq_signed_pow (e P).1.val hn t ht
    have hc : binaryQuadraticGaussSum (e P).1.val = (2 : ℂ)^t ∨
        binaryQuadraticGaussSum (e P).1.val = -((2 : ℂ)^t) := by
      rcases hs with hs | hs
      · left
        rw [← binaryQuadraticGaussInteger_cast,hs]
        push_cast
        rfl
      · right
        rw [← binaryQuadraticGaussInteger_cast,hs]
        push_cast
        rfl
    have hr : (Nat.card (binaryPolarRadical q) : ℂ) =
        (2 : ℂ)^finrank (ZMod 2) (binaryPolarRadical q) := by
      rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := ZMod 2)]
      norm_num
    have hg := binaryQuadraticRefinementSplitEquiv_gauss q C hC P
    change binaryQuadraticGaussSum P.val =
      binaryQuadraticGaussSum (e P).1.val * (if (e P).2 = 0 then _ else _) at hg
    rw [if_pos hl,hr] at hg
    rcases hc with hc | hc
    · left
      rw [hc] at hg
      simpa only [pow_add,mul_comm] using hg
    · right
      rw [hc] at hg
      simpa only [pow_add,neg_mul,mul_comm] using hg
  · left
    exact (binaryQuadraticRefinementSplitEquiv_zero_iff q C hC P).mpr hl

/-- For an actual fixed alternating form of dimension b+2t and radical dimension b:
the zero and both signed fibers are counted, and there are no other Gauss values. -/
theorem binaryQuadraticRefinements_gauss_counts
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt)
    (b t : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) V = b+2*t) :
    (Nat.card {P : BinaryQuadraticRefinements B // binaryQuadraticGaussSum P.val = 0} =
        (2^b-1)*2^(2*t)) ∧
    (2 * Nat.card {P : BinaryQuadraticRefinements B //
      binaryQuadraticGaussSum P.val = (2 : ℂ)^(b+t)} = 2^(2*t)+2^t) ∧
    (2 * Nat.card {P : BinaryQuadraticRefinements B //
      binaryQuadraticGaussSum P.val = -((2 : ℂ)^(b+t))} + 2^t = 2^(2*t)) ∧
    (∀ P : BinaryQuadraticRefinements B, binaryQuadraticGaussSum P.val = 0 ∨
      binaryQuadraticGaussSum P.val = (2 : ℂ)^(b+t) ∨
      binaryQuadraticGaussSum P.val = -((2 : ℂ)^(b+t))) := by
  let q := binaryAlternatingQuadratic B hB
  have hp : q.polarBilin = B := binaryAlternatingQuadratic_polar B hB
  have hbq : finrank (ZMod 2) (binaryPolarRadical q) = b := by
    change finrank (ZMod 2) (LinearMap.ker q.polarBilin) = b
    rw [hp]
    exact hb
  obtain ⟨C,hC⟩ := (binaryPolarRadical q).exists_isCompl
  have hc : finrank (ZMod 2) C = 2*t := by
    have hs := Submodule.finrank_add_eq_of_isCompl hC
    rw [hbq,hd] at hs
    omega
  refine ⟨?_,?_,?_,?_⟩
  · have h := binaryQuadraticRefinement_zero_card q C hC
    rw [hp,hbq,hc] at h
    simpa only [mul_comm] using h
  · have h := binaryQuadraticRefinement_radical_positive_card q C hC t hc
    rw [hbq,hp] at h
    exact h
  · have h := binaryQuadraticRefinement_radical_negative_card q C hC t hc
    rw [hbq,hp] at h
    exact h
  · have h := binaryQuadraticRefinement_gauss_support q C hC t hc
    rw [hbq,hp] at h
    exact h

end ExactCriticalCurve.FiniteQuadratic
