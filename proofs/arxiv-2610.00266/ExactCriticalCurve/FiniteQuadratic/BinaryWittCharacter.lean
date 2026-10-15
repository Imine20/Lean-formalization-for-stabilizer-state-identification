import ExactCriticalCurve.FiniteQuadratic.MetabolicCore
import ExactCriticalCurve.Quantum.BinaryPauli
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.BigOperators

/-! Character counts for genuine binary quadratic fibers. No Gauss-sum value
or nondegeneracy of the restricted subspace is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem binaryCharacter_linear_sum [Fintype V] (l : V →ₗ[ZMod 2] ZMod 2) :
    (∑ x, pauliSign (l x)) = if l = 0 then (Fintype.card V : ℂ) else 0 := by
  by_cases hl : l = 0
  · simp [hl]
  rw [if_neg hl]
  obtain ⟨a, ha⟩ : ∃ a, l a ≠ 0 := by
    by_contra! h
    exact hl (LinearMap.ext h)
  have ha1 : l a = 1 := by
    generalize hz : l a = z at ha ⊢
    fin_cases z <;> simp_all
  have hs := Equiv.sum_comp (Equiv.addLeft a) (fun x => pauliSign (l x))
  change (∑ x, pauliSign (l (a+x))) = _ at hs
  simp only [map_add, pauliSign_add, ha1, pauliSign_one] at hs
  rw [← Finset.mul_sum] at hs
  exact eq_zero_of_mul_eq_self_left (by norm_num : (-1 : ℂ) ≠ 1) hs

theorem binaryCharacter_eq_indicator (a b : ZMod 2) :
    1 + pauliSign (a + b) = if a = b then (2 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [pauliSign, ZMod.val]

theorem binaryCharacter_polar_sum [Fintype V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (z : V) :
    (∑ y, pauliSign (Q.polarBilin y z)) =
      if z = 0 then (Fintype.card V : ℂ) else 0 := by
  have he : Q.polarBilin.flip z = 0 ↔ z = 0 := by
    constructor
    · intro h
      apply hQ
      intro y
      rw [(polar_isSymm Q).eq]
      exact congrArg (fun l : V →ₗ[ZMod 2] ZMod 2 => l y) h
    · rintro rfl
      simp
  simpa only [he] using binaryCharacter_linear_sum (Q.polarBilin.flip z)

theorem binaryQuadratic_gauss_translate [Fintype V]
    (Q : QuadraticForm (ZMod 2) V) (z : V) :
    (∑ y, pauliSign (Q y + Q.polarBilin y z)) =
      pauliSign (Q z) * ∑ y, pauliSign (Q y) := by
  have hp (y : V) :
      pauliSign (Q y + Q.polarBilin y z) =
        pauliSign (Q z) * pauliSign (Q (y+z)) := by
    rw [quadratic_add]
    simp only [pauliSign_add]
    rw [show pauliSign (Q z) * (pauliSign (Q y) * pauliSign (Q z) *
      pauliSign (Q.polarBilin y z)) =
      (pauliSign (Q z) * pauliSign (Q z)) *
        (pauliSign (Q y) * pauliSign (Q.polarBilin y z)) by ring,
      pauliSign_mul_self, one_mul]
  simp_rw [hp]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (Equiv.addRight z) (fun y => pauliSign (Q y))

/-- Actual quadratic and polar constraints for an arbitrary linear embedding. -/
abbrev quadraticPolarFiber (Q : QuadraticForm (ZMod 2) V)
    (f : W →ₗ[ZMod 2] V) (a : ZMod 2) (l : W →ₗ[ZMod 2] ZMod 2) :=
  {y : V // Q y = a ∧ ∀ s, Q.polarBilin y (f s) = l s}

theorem binaryCharacter_constraint_sum [Fintype W]
    (Q : QuadraticForm (ZMod 2) V) (f : W →ₗ[ZMod 2] V)
    (l : W →ₗ[ZMod 2] ZMod 2) (y : V) :
    (∑ s, pauliSign (Q.polarBilin y (f s) + l s)) =
      if ∀ s, Q.polarBilin y (f s) = l s then (Fintype.card W : ℂ) else 0 := by
  let m := (Q.polarBilin y).comp f + l
  have he : m = 0 ↔ ∀ s, Q.polarBilin y (f s) = l s := by
    constructor
    · intro h s
      have hs := congrArg (fun p : W →ₗ[ZMod 2] ZMod 2 => p s) h
      change Q.polarBilin y (f s) + l s = 0 at hs
      exact (eq_neg_of_add_eq_zero_left hs).trans (CharTwo.neg_eq _)
    · intro h
      ext s
      change Q.polarBilin y (f s) + l s = 0
      rw [h s, CharTwo.add_self_eq_zero]
  simpa only [he] using binaryCharacter_linear_sum m


/-- Division-free fiber count, valid for every embedded subspace, including
degenerate restrictions. The Gauss sum is deliberately left unevaluated. -/
theorem quadraticPolarFiber_scaled_card [Fintype V] [Fintype W]
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (f : W →ₗ[ZMod 2] V) (hf : Function.Injective f)
    (a : ZMod 2) (l : W →ₗ[ZMod 2] ZMod 2) :
    (2 * (Fintype.card W : ℂ)) * Fintype.card (quadraticPolarFiber Q f a l) =
      (Fintype.card V : ℂ) + pauliSign a * (∑ y, pauliSign (Q y)) *
        ∑ s, pauliSign (Q (f s) + l s) := by
  have hind (y : V) :
      (1 + pauliSign (Q y + a)) *
        (∑ s, pauliSign (Q.polarBilin y (f s) + l s)) =
      if Q y = a ∧ ∀ s, Q.polarBilin y (f s) = l s
        then 2 * (Fintype.card W : ℂ) else 0 := by
    rw [binaryCharacter_eq_indicator, binaryCharacter_constraint_sum]
    split_ifs <;> simp_all
  have hcard :
      (2 * (Fintype.card W : ℂ)) * Fintype.card (quadraticPolarFiber Q f a l) =
      ∑ y, (1 + pauliSign (Q y + a)) *
        (∑ s, pauliSign (Q.polarBilin y (f s) + l s)) := by
    simp_rw [hind]
    unfold quadraticPolarFiber
    simp only [Fintype.card_subtype]
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hu : (∑ y : V, ∑ s : W, pauliSign (Q.polarBilin y (f s) + l s)) =
      (Fintype.card V : ℂ) := by
    rw [Finset.sum_comm]
    simp_rw [pauliSign_add, ← Finset.sum_mul, binaryCharacter_polar_sum Q hQ]
    rw [Finset.sum_eq_single (0 : W)]
    · simp
    · intro s _ hs
      have hfs : f s ≠ 0 := by intro h; apply hs; exact hf (by simpa using h)
      simp [hfs]
    · simp
  have hw :
      (∑ y : V, pauliSign (Q y + a) *
        ∑ s : W, pauliSign (Q.polarBilin y (f s) + l s)) =
      pauliSign a * (∑ y, pauliSign (Q y)) *
        ∑ s, pauliSign (Q (f s) + l s) := by
    conv =>
      lhs
      simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ s : W, (pauliSign a * pauliSign (l s)) *
          ∑ y : V, pauliSign (Q y + Q.polarBilin y (f s)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        simp only [pauliSign_add]
        ring
      _ = ∑ s : W, (pauliSign a * (∑ y, pauliSign (Q y))) *
          pauliSign (Q (f s) + l s) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [binaryQuadratic_gauss_translate, pauliSign_add]
        ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hcard]
  simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
  rw [hu, hw]


/-- Equal embedded quadratic data give equal complete fibers, without knowing
the Gauss sum or the rank of the restricted form. -/
theorem quadraticPolarFiber_card_eq [Fintype V] [Fintype W]
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (f g : W →ₗ[ZMod 2] V) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ s, Q (f s) = Q (g s)) (a : ZMod 2)
    (l : W →ₗ[ZMod 2] ZMod 2) :
    Fintype.card (quadraticPolarFiber Q f a l) =
      Fintype.card (quadraticPolarFiber Q g a l) := by
  have h1 := quadraticPolarFiber_scaled_card Q hQ f hf a l
  have h2 := quadraticPolarFiber_scaled_card Q hQ g hg a l
  simp_rw [hfg] at h1
  have hne : (2 * (Fintype.card W : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have he := mul_left_cancel₀ hne (h1.trans h2.symm)
  exact_mod_cast he

theorem quadratic_preserves_polar (Q : QuadraticForm (ZMod 2) V)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V)
    (hf : ∀ s : S, Q (f s) = Q s.val) (s t : S) :
    Q.polarBilin (f s) (f t) = Q.polarBilin s.val t.val := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← map_add, hf, hf, hf]
  rfl


/-- An exterior source vector always has an exterior target vector satisfying
the genuine quadratic and polar constraints. -/
theorem exists_external_quadraticFiber [Fintype V]
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfq : ∀ s : S, Q (f s) = Q s.val)
    (x : V) (hx : x ∉ S) :
    ∃ y : V, y ∉ LinearMap.range f ∧ Q y = Q x ∧
      ∀ s : S, Q.polarBilin y (f s) = Q.polarBilin x s.val := by
  let l := (Q.polarBilin x).comp S.subtype
  let A := quadraticPolarFiber Q S.subtype (Q x) l
  let B := quadraticPolarFiber Q f (Q x) l
  have hcard : Fintype.card A = Fintype.card B :=
    quadraticPolarFiber_card_eq Q hQ S.subtype f Subtype.val_injective hfi
      (fun s => (hfq s).symm) (Q x) l
  let A₀ := {z : A // z.val ∈ S}
  let B₀ := {z : B // z.val ∈ LinearMap.range f}
  let e : A₀ → B₀ := fun z =>
    ⟨⟨f ⟨z.val.val,z.property⟩, by
      constructor
      · exact (hfq _).trans z.val.property.1
      · intro s
        exact (quadratic_preserves_polar Q S f hfq _ s).trans (z.val.property.2 s)⟩,
      ⟨⟨z.val.val,z.property⟩,rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro z z' h
      have hval : f ⟨z.val.val,z.property⟩ = f ⟨z'.val.val,z'.property⟩ :=
        congrArg (fun z : B₀ => z.val.val) h
      have hs := congrArg Subtype.val (hfi hval)
      exact Subtype.ext (Subtype.ext hs)
    · intro z
      obtain ⟨s, hs⟩ := z.property
      have ha : Q s.val = Q x := (hfq s).symm.trans (hs ▸ z.val.property.1)
      have hb : ∀ t : S, Q.polarBilin s.val t.val = l t := by
        intro t
        rw [← quadratic_preserves_polar Q S f hfq s t, hs]
        exact z.val.property.2 t
      refine ⟨⟨⟨s.val,ha,hb⟩,s.property⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hs)
  have hinside : Fintype.card A₀ = Fintype.card B₀ :=
    Fintype.card_congr (Equiv.ofBijective e he)
  have hA := Fintype.card_subtype_compl (fun z : A => z.val ∈ S)
  have hB := Fintype.card_subtype_compl (fun z : B => z.val ∈ LinearMap.range f)
  have hpos : 0 < Fintype.card {z : A // z.val ∉ S} :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨x,rfl,fun _ => rfl⟩,hx⟩⟩
  have hpos' : 0 < Fintype.card {z : B // z.val ∉ LinearMap.range f} := by
    change Fintype.card {z : A // z.val ∉ S} = Fintype.card A - Fintype.card A₀ at hA
    change Fintype.card {z : B // z.val ∉ LinearMap.range f} = Fintype.card B - Fintype.card B₀ at hB
    omega
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp hpos'
  exact ⟨z.val.val,z.property,z.val.property.1,z.val.property.2⟩

end ExactCriticalCurve.FiniteQuadratic
