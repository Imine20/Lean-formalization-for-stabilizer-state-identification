import ExactCriticalCurve.Binary.Geometry
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Orthonormal bases over F2 for nonalternating symmetric nondegenerate forms.
The induction retains a nonzero characteristic vector until dimension zero.
No invertibility of two, classification, or orthonormal basis is assumed. -/

noncomputable section
open Classical Module
namespace ExactCriticalCurve

private theorem binary_module_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (x : V) : x + x = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c : ZMod 2 => c • x) h

private theorem binary_ne_zero_eq_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a <;> simp_all

/-- Choose a unit vector different from the characteristic vector unless the
whole space has dimension one. -/
theorem binary_exists_unit_vector
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (w : V) (hw : w ≠ 0) (hchar : ∀ x, B x x = B x w) :
    ∃ v : V, B v v = 1 ∧ (v ≠ w ∨ Module.finrank (ZMod 2) V = 1) := by
  have hex : ∃ v : V, B v v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw
    apply hnd
    intro x
    rw [hB.eq, ← hchar]
    exact h x
  obtain ⟨v, hv⟩ := hex
  have hv1 := binary_ne_zero_eq_one hv
  by_cases hvw : v ≠ w
  · exact ⟨v, hv1, Or.inl hvw⟩
  have hvw' : v = w := not_ne_iff.mp hvw
  subst v
  by_cases hdim : Module.finrank (ZMod 2) V = 1
  · exact ⟨w, hv1, Or.inr hdim⟩
  let W := B.orthogonal (Submodule.span (ZMod 2) {w})
  have hc := LinearMap.BilinForm.isCompl_span_singleton_orthogonal (B := B) hv
  have hd := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_span_singleton hw] at hd
  have hp : 0 < Module.finrank (ZMod 2) W := by
    change 1 + Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V at hd
    omega
  obtain ⟨y, hy⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
  have hwy : B w y.val = 0 := y.property w (Submodule.mem_span_singleton_self w)
  have hyw : B y.val w = 0 := (hB.eq _ _).trans hwy
  have hyy : B y.val y.val = 0 := (hchar y.val).trans hyw
  refine ⟨w + y.val, ?_, Or.inl ?_⟩
  · simp only [map_add, LinearMap.add_apply, hv1, hwy, hyw, hyy, add_zero]
  · intro he
    apply hy
    apply Subtype.val_injective
    exact add_left_cancel (show w + y.val = w + 0 by simpa using he)

/-- Orthonormality means the complete identity Gram matrix, including all
self-pairings. The zero-dimensional space is allowed separately. -/
theorem exists_binaryOrthonormalBasis
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (w : V) (hchar : ∀ x, B x x = B x w)
    (hw : w ≠ 0 ∨ Module.finrank (ZMod 2) V = 0) :
    ∃ b : Basis (Fin (Module.finrank (ZMod 2) V)) (ZMod 2) V,
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  suffices ∀ d, Module.finrank (ZMod 2) V = d →
    ∃ b : Basis (Fin d) (ZMod 2) V,
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 by
    exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero =>
    exact ⟨basisOfFinrankZero hd, fun i => Fin.elim0 i⟩
  | succ d ih =>
    have hw0 : w ≠ 0 := hw.resolve_right (by omega)
    obtain ⟨v, hv, hvw⟩ := binary_exists_unit_vector B hB hnd w hw0 hchar
    have hvn : B v v ≠ 0 := by rw [hv]; decide
    have hv0 : v ≠ 0 := by intro h; simp [h] at hvn
    let W := B.orthogonal (Submodule.span (ZMod 2) {v})
    have hc := LinearMap.BilinForm.isCompl_span_singleton_orthogonal (B := B) hvn
    have hdim := Submodule.finrank_add_eq_of_isCompl hc
    rw [finrank_span_singleton hv0] at hdim
    have hdW : Module.finrank (ZMod 2) W = d := by
      change 1 + Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V at hdim
      omega
    have hwW : w + v ∈ W := by
      intro z hz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      change B (a • v) (w + v) = 0
      rw [map_smul, LinearMap.smul_apply, map_add, ← hchar v, hv]
      rw [binary_module_add_self, smul_zero]
    let w' : W := ⟨w + v, hwW⟩
    have hcW (x : W) : (B.restrict W) x x = (B.restrict W) x w' := by
      have hxv : B x.val v = 0 :=
        (hB.eq _ _).trans (x.property v (Submodule.mem_span_singleton_self v))
      change B x.val x.val = B x.val (w + v)
      rw [map_add, hxv, add_zero, hchar]
    have hw' : w' ≠ 0 ∨ Module.finrank (ZMod 2) W = 0 := by
      rcases hvw with hne | hone
      · left
        intro he
        have he' : w + v = 0 := congrArg Subtype.val he
        have he'' := congrArg (fun z : V => z + v) he'
        have hwv : w = v := by
          simpa only [add_assoc, binary_module_add_self, add_zero, zero_add] using he''
        exact hne hwv.symm
      · right
        omega
    obtain ⟨b', hb'⟩ := ih (B := B.restrict W) (hB.restrict W)
      (B.restrict_nondegenerate_orthogonal_spanSingleton hnd hB.isRefl hvn)
      w' hcW hw' hdW
    let b := Basis.mkFinCons v b'
      (by
        rintro a y hy he
        have hh := congrArg (fun z => B v z) he
        have hvy : B v y = 0 := hy v (Submodule.mem_span_singleton_self v)
        simpa only [map_add, map_smul, hv, hvy, map_zero, smul_eq_mul, mul_one,
          add_zero] using hh)
      (by
        intro y
        refine ⟨B v y, ?_⟩
        intro z hz
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
        change B (a • v) (y + B v y • v) = 0
        rw [map_smul, LinearMap.smul_apply, map_add, map_smul, hv]
        simp [smul_eq_mul, binary_module_add_self])
    refine ⟨b, ?_⟩
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa [b, Basis.coe_mkFinCons] using hv
    · simpa [b, Basis.coe_mkFinCons] using
        (b' j).property v (Submodule.mem_span_singleton_self v)
    · simpa [b, Basis.coe_mkFinCons] using
        (hB.eq (b' i).val v).trans ((b' i).property v (Submodule.mem_span_singleton_self v))
    · simpa [b, Basis.coe_mkFinCons] using hb' i j

end ExactCriticalCurve
