import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticEnvelope

/-! Actual linear refinements and character averaging for binary quadratic spaces. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Two actual quadratic forms with the same polar differ by a linear functional. -/
def binaryQuadraticDifferenceLinear (q p : QuadraticForm (ZMod 2) A)
    (h : q.polarBilin = p.polarBilin) : A →ₗ[ZMod 2] ZMod 2 where
  toFun x := q x + p x
  map_add' x y := by
    rw [quadratic_add,quadratic_add,h]
    have hz := CharTwo.add_self_eq_zero (p.polarBilin x y)
    linear_combination hz
  map_smul' a x := by
    change q (a • x) + p (a • x) = a • (q x + p x)
    fin_cases a <;> simp

theorem binaryLinearQuadratic_polar (l : A →ₗ[ZMod 2] ZMod 2) :
    (binaryLinearQuadratic l).polarBilin = 0 := by
  ext x y
  simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]

/-- Add a genuine linear quadratic form without changing the polar. -/
theorem binaryQuadratic_add_linear_polar (Q : QuadraticForm (ZMod 2) V)
    (l : V →ₗ[ZMod 2] ZMod 2) :
    (Q + binaryLinearQuadratic l).polarBilin = Q.polarBilin := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    QuadraticMap.add_apply,binaryLinearQuadratic_apply,map_add]
  ring

/-- Extend the actual discrepancy along an injective polar-preserving map. -/
theorem exists_binaryQuadratic_refinement (q : QuadraticForm (ZMod 2) A)
    (Q : QuadraticForm (ZMod 2) V) (f : A →ₗ[ZMod 2] V)
    (hf : Function.Injective f) (hp : ∀ x y, Q.polarBilin (f x) (f y) = q.polarBilin x y) :
    ∃ P : QuadraticForm (ZMod 2) V,
      P.polarBilin = Q.polarBilin ∧ ∀ x, P (f x) = q x := by
  have hpolar : q.polarBilin = (Q.comp f).polarBilin := by
    rw [QuadraticMap.polarBilin_comp]
    ext x y
    exact (hp x y).symm
  let l := binaryQuadraticDifferenceLinear q (Q.comp f) hpolar
  let e := LinearEquiv.ofInjective f hf
  obtain ⟨L,hL⟩ := (l.comp e.symm.toLinearMap).exists_extend
  have hLf (x : A) : L (f x) = q x + Q (f x) := by
    have he := congrArg (fun m : LinearMap.range f →ₗ[ZMod 2] ZMod 2 => m (e x)) hL
    simpa [l,binaryQuadraticDifferenceLinear] using he
  refine ⟨Q + binaryLinearQuadratic L,binaryQuadratic_add_linear_polar Q L,?_⟩
  intro x
  simp only [QuadraticMap.add_apply,binaryLinearQuadratic_apply,hLf]
  have hz := CharTwo.add_self_eq_zero (Q (f x))
  linear_combination hz

/-- Polar translation changes the actual signed Gauss sum by the value at the translator. -/
theorem binaryQuadratic_linear_shift_gauss [Fintype V]
    (P : QuadraticForm (ZMod 2) V) (v : V) :
    binaryQuadraticGaussSum (P + binaryLinearQuadratic (P.polarBilin.flip v)) =
      pauliSign (P v) * binaryQuadraticGaussSum P := by
  simpa [binaryQuadraticGaussSum] using binaryQuadratic_gauss_translate P v

abbrev binaryPolarOrthogonal (Q : QuadraticForm (ZMod 2) V)
    (S : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal Q.polarBilin S

/-- Averaging over a genuinely totally singular subspace leaves the orthogonal sum. -/
theorem binaryQuadraticGaussSum_eq_orthogonal_sum [Fintype V]
    (Q : QuadraticForm (ZMod 2) V) (S : Submodule (ZMod 2) V)
    (hS : ∀ s : S, Q s.val = 0) :
    binaryQuadraticGaussSum Q =
      binaryQuadraticGaussSum (Q.comp (binaryPolarOrthogonal Q S).subtype) := by
  have hind (v : V) :
      (∑ s : S, pauliSign (Q.polarBilin v s.val)) =
        if v ∈ binaryPolarOrthogonal Q S then (Fintype.card S : ℂ) else 0 := by
    have he : (∀ s : S, Q.polarBilin v s.val = 0) ↔
        v ∈ binaryPolarOrthogonal Q S := by
      constructor
      · intro h s hs
        exact ((polar_isSymm Q).eq s v).trans (h ⟨s,hs⟩)
      · intro h s
        exact ((polar_isSymm Q).eq v s.val).trans (h s.val s.property)
    have hz := binaryCharacter_constraint_sum Q S.subtype 0 v
    simp only [LinearMap.zero_apply,add_zero,Submodule.subtype_apply] at hz
    simp only [he] at hz
    exact hz
  have hsum :
      (Fintype.card S : ℂ) * binaryQuadraticGaussSum Q =
        (Fintype.card S : ℂ) *
          binaryQuadraticGaussSum (Q.comp (binaryPolarOrthogonal Q S).subtype) := by
    calc
      _ = ∑ s : S, ∑ v : V, pauliSign (Q v + Q.polarBilin v s.val) := by
        simp_rw [binaryQuadratic_gauss_translate,hS,pauliSign_zero,one_mul]
        simp [binaryQuadraticGaussSum]
      _ = ∑ v : V, pauliSign (Q v) *
          (if v ∈ binaryPolarOrthogonal Q S then (Fintype.card S : ℂ) else 0) := by
        rw [Finset.sum_comm]
        simp_rw [pauliSign_add,← Finset.mul_sum,hind]
      _ = _ := by
        simp only [mul_ite,mul_zero]
        rw [← Finset.sum_filter]
        rw [← Finset.sum_mul]
        have he : (∑ v ∈ Finset.univ.filter (fun v => v ∈ binaryPolarOrthogonal Q S),
            pauliSign (Q v)) =
            binaryQuadraticGaussSum (Q.comp (binaryPolarOrthogonal Q S).subtype) := by
          exact Finset.sum_subtype _ (by intro v; simp) (fun v => pauliSign (Q v))
        rw [he,mul_comm]
  exact (mul_left_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card S : ℂ) ≠ 0)) hsum

/-- The image of the actual radical equals the radical of the image restriction. -/
theorem binaryQuadratic_radical_image_eq (q : QuadraticForm (ZMod 2) A)
    (Q : QuadraticForm (ZMod 2) V) (f : A →ₗ[ZMod 2] V)
    (hfq : ∀ x, Q (f x) = q x) :
    LinearMap.range (f.comp (binaryPolarRadical q).subtype) =
      LinearMap.range f ⊓ binaryPolarOrthogonal Q (LinearMap.range f) := by
  have hp (x y : A) : Q.polarBilin (f x) (f y) = q.polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
    rw [← map_add,hfq,hfq,hfq]
  ext y
  constructor
  · rintro ⟨r,rfl⟩
    refine ⟨⟨r.val,rfl⟩,?_⟩
    rintro _ ⟨x,rfl⟩
    change Q.polarBilin (f x) (f r.val) = 0
    rw [hp,(polar_isSymm q).eq]
    exact (mem_binaryPolarRadical q r.val).mp r.property x
  · rintro ⟨⟨x,rfl⟩,hx⟩
    refine ⟨⟨x,?_⟩,rfl⟩
    apply (mem_binaryPolarRadical q x).mpr
    intro z
    rw [← hp,(polar_isSymm Q).eq]
    exact hx (f z) ⟨z,rfl⟩

theorem binaryQuadraticGaussSum_range [Fintype A] [Fintype V]
    (q : QuadraticForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V) (hf : Function.Injective f) (hfq : ∀ x, Q (f x) = q x) :
    binaryQuadraticGaussSum (Q.comp (LinearMap.range f).subtype) =
      binaryQuadraticGaussSum q := by
  let e := LinearEquiv.ofInjective f hf
  have he := Equiv.sum_comp e.toEquiv (fun z => pauliSign (Q z.val))
  simpa [binaryQuadraticGaussSum,e,hfq] using he.symm

end ExactCriticalCurve.FiniteQuadratic
