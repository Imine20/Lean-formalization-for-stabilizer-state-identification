import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRefinements

/-! Actual signed Gauss fibers of quadratic refinements of a fixed polar. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- For a nondegenerate polar, every genuine refinement is a unique polar shift. -/
def binaryQuadraticPolarShiftEquiv [FiniteDimensional (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) :
    V ≃ BinaryQuadraticRefinements q.polarBilin :=
  (LinearMap.BilinForm.toDual q.polarBilin.flip hq.flip).toEquiv.trans
    (binaryQuadraticRefinementEquivDualAt q).symm

@[simp] theorem binaryQuadraticPolarShiftEquiv_apply
    [FiniteDimensional (ZMod 2) V] (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) (v : V) :
    (binaryQuadraticPolarShiftEquiv q hq v).val =
      q + binaryLinearQuadratic (q.polarBilin.flip v) := rfl

theorem binaryQuadraticPolarShiftEquiv_gauss
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) (v : V) :
    binaryQuadraticGaussSum (binaryQuadraticPolarShiftEquiv q hq v).val =
      pauliSign (q v) * binaryQuadraticGaussSum q := by
  rw [binaryQuadraticPolarShiftEquiv_apply,binaryQuadratic_linear_shift_gauss]

/-- A genuine Gauss fiber is a genuine value fiber; no sign-distribution assumption. -/
def binaryQuadraticGaussFiberEquiv [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) (a : ZMod 2) :
    {v : V // q v = a} ≃
      {P : BinaryQuadraticRefinements q.polarBilin //
        binaryQuadraticGaussSum P.val = pauliSign a * binaryQuadraticGaussSum q} :=
  (binaryQuadraticPolarShiftEquiv q hq).subtypeEquiv (fun v => by
    rw [binaryQuadraticPolarShiftEquiv_gauss,mul_eq_mul_right_iff]
    have hn := binaryQuadraticGaussSum_ne_zero q hq
    simp only [hn,or_false]
    generalize q v = b
    fin_cases a <;> fin_cases b <;> norm_num [pauliSign,ZMod.val])

theorem binaryQuadratic_value_card [Fintype V]
    (q : QuadraticForm (ZMod 2) V) (a : ZMod 2) :
    2 * (Nat.card {v : V // q v = a} : ℂ) =
      (Nat.card V : ℂ) + pauliSign a * binaryQuadraticGaussSum q := by
  have h := congrArg (fun f : V → ℂ => ∑ v, f v)
    (funext (fun v => binaryCharacter_eq_indicator (q v) a))
  simp only [Finset.sum_add_distrib,pauliSign_add] at h
  rw [← Finset.sum_mul] at h
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hc : (∑ v : V, if q v = a then (2 : ℂ) else 0) =
      2 * ((Finset.univ.filter (fun v : V => q v = a)).card : ℂ) := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hc] at h
  simpa only [binaryQuadraticGaussSum,mul_comm] using h.symm

theorem binaryQuadraticRefinement_gauss_card
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) (a : ZMod 2) :
    2 * (Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = pauliSign a * binaryQuadraticGaussSum q} : ℂ) =
      (Nat.card V : ℂ) + pauliSign a * binaryQuadraticGaussSum q := by
  rw [← Nat.card_congr (binaryQuadraticGaussFiberEquiv q hq a)]
  exact binaryQuadratic_value_card q a

theorem binaryQuadraticGaussInteger_eq_signed_pow
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (t : ℕ) (ht : finrank (ZMod 2) V = 2*t) :
    binaryQuadraticGaussInteger q = (2 : ℤ)^t ∨
      binaryQuadraticGaussInteger q = -((2 : ℤ)^t) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  have hc := binaryQuadraticGaussSum_sq q hq
  rw [← binaryQuadraticGaussInteger_cast,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := V),ht] at hc
  norm_num only [ZMod.card,Nat.cast_pow,Nat.cast_ofNat] at hc
  have hi : binaryQuadraticGaussInteger q ^ 2 = (2 : ℤ) ^ (2*t) := by exact_mod_cast hc
  simpa [pow_mul,mul_comm] using hi

/-- The two actual signed fibers, uniformly including the zero-dimensional endpoint. -/
theorem binaryQuadraticRefinement_signed_card
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (t : ℕ) (ht : finrank (ZMod 2) V = 2*t) (a : ZMod 2) :
    2 * (Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = pauliSign a * (2 : ℂ)^t} : ℂ) =
      (2 : ℂ)^(2*t) + pauliSign a * (2 : ℂ)^t := by
  have hc : (Nat.card V : ℂ) = (2 : ℂ)^(2*t) := by
    rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := ZMod 2),ht]
    norm_num
  rcases binaryQuadraticGaussInteger_eq_signed_pow q hq t ht with hp | hm
  · have hg : binaryQuadraticGaussSum q = (2 : ℂ)^t := by
      rw [← binaryQuadraticGaussInteger_cast,hp]
      push_cast
      rfl
    simpa only [hc,hg] using binaryQuadraticRefinement_gauss_card q hq a
  · have hg : binaryQuadraticGaussSum q = -((2 : ℂ)^t) := by
      rw [← binaryQuadraticGaussInteger_cast,hm]
      push_cast
      rfl
    have hs : pauliSign (a+1) * binaryQuadraticGaussSum q =
        pauliSign a * (2 : ℂ)^t := by
      rw [pauliSign_add,pauliSign_one,hg]
      ring
    simpa only [hc,hs] using binaryQuadraticRefinement_gauss_card q hq (a+1)

theorem binaryQuadraticRefinement_positive_card
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (t : ℕ) (ht : finrank (ZMod 2) V = 2*t) :
    2 * Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = (2 : ℂ)^t} = 2^(2*t)+2^t := by
  have h := binaryQuadraticRefinement_signed_card q hq t ht 0
  simp only [pauliSign_zero,one_mul] at h
  exact_mod_cast h

theorem binaryQuadraticRefinement_negative_card
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (t : ℕ) (ht : finrank (ZMod 2) V = 2*t) :
    2 * Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = -((2 : ℂ)^t)} + 2^t = 2^(2*t) := by
  have h := binaryQuadraticRefinement_signed_card q hq t ht 1
  simp only [pauliSign_one,neg_one_mul] at h
  have h' : 2 * (Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = -((2 : ℂ)^t)} : ℂ) + (2 : ℂ)^t =
      (2 : ℂ)^(2*t) := by linear_combination h
  exact_mod_cast h'

end ExactCriticalCurve.FiniteQuadratic
