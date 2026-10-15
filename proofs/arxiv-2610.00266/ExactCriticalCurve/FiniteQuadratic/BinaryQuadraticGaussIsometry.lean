import ExactCriticalCurve.FiniteQuadratic.QuadraticTupleOrbits
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-! Gauss sums classify actual binary quadratic spaces with nondegenerate polar.
The proof counts complete quadratic/polar fibers in the two ambient spaces and
extends an actual injective partial isometry one direction at a time. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {V W E : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup E] [Module (ZMod 2) E]

/-- The genuine character sum of the actual quadratic form. -/
def binaryQuadraticGaussSum [Fintype V] (Q : QuadraticForm (ZMod 2) V) : ℂ :=
  ∑ x : V, pauliSign (Q x)

/-- Character orthogonality determines the square without choosing a type sign. -/
theorem binaryQuadraticGaussSum_sq [Fintype V] (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) :
    binaryQuadraticGaussSum Q ^ 2 = (Fintype.card V : ℂ) := by
  change (∑ x : V, pauliSign (Q x)) ^ 2 = _
  calc
    _ = ∑ y : V, pauliSign (Q y) * ∑ x : V, pauliSign (Q x) := by
      rw [← Finset.sum_mul, pow_two]
    _ = ∑ y : V, ∑ x : V, pauliSign (Q x + Q.polarBilin x y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact (binaryQuadratic_gauss_translate Q y).symm
    _ = ∑ x : V, pauliSign (Q x) * ∑ y : V, pauliSign (Q.polarBilin y x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [pauliSign_add, (polar_isSymm Q).eq x]
      exact (Finset.mul_sum _ _ _).symm
    _ = _ := by
      simp_rw [binaryCharacter_polar_sum Q hQ]
      simp

theorem binaryQuadraticGaussSum_eq_of_isometry [Fintype V] [Fintype W]
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (e : Q.IsometryEquiv P) :
    binaryQuadraticGaussSum Q = binaryQuadraticGaussSum P := by
  unfold binaryQuadraticGaussSum
  calc
    _ = ∑ x : V, pauliSign (P (e x)) := by simp only [e.map_app]
    _ = _ := Equiv.sum_comp e.toLinearEquiv.toEquiv (fun w => pauliSign (P w))

/-- Full fibers in different ambient spaces agree from actual dimension and
Gauss data, even when the embedded subspace has degenerate restricted polar. -/
theorem quadraticPolarFiber_card_eq_of_gauss
    [Fintype V] [Fintype W] [Fintype E]
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (hcard : Fintype.card V = Fintype.card W)
    (hgauss : binaryQuadraticGaussSum Q = binaryQuadraticGaussSum P)
    (f : E →ₗ[ZMod 2] V) (g : E →ₗ[ZMod 2] W)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ s, Q (f s) = P (g s)) (a : ZMod 2)
    (l : E →ₗ[ZMod 2] ZMod 2) :
    Fintype.card (quadraticPolarFiber Q f a l) =
      Fintype.card (quadraticPolarFiber P g a l) := by
  have h1 := quadraticPolarFiber_scaled_card Q hQ f hf a l
  have h2 := quadraticPolarFiber_scaled_card P hP g hg a l
  change (2 * (Fintype.card E : ℂ)) * _ =
    (Fintype.card V : ℂ) + pauliSign a * binaryQuadraticGaussSum Q * _ at h1
  rw [hcard, hgauss] at h1
  simp_rw [hfg] at h1
  have hne : (2 * (Fintype.card E : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have he := mul_left_cancel₀ hne (h1.trans h2.symm)
  exact_mod_cast he

theorem quadratic_preserves_polar_between
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] W)
    (hf : ∀ s : S, P (f s) = Q s.val) (s t : S) :
    P.polarBilin (f s) (f t) = Q.polarBilin s.val t.val := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← map_add, hf, hf, hf]
  rfl

/-- Subtracting the actual inside fibers leaves a nonempty outside fiber. -/
theorem exists_external_quadraticFiber_of_gauss [Fintype V] [Fintype W]
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (hcard : Fintype.card V = Fintype.card W)
    (hgauss : binaryQuadraticGaussSum Q = binaryQuadraticGaussSum P)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] W)
    (hfi : Function.Injective f) (hfq : ∀ s : S, P (f s) = Q s.val)
    (x : V) (hx : x ∉ S) :
    ∃ y : W, y ∉ LinearMap.range f ∧ P y = Q x ∧
      ∀ s : S, P.polarBilin y (f s) = Q.polarBilin x s.val := by
  let l := (Q.polarBilin x).comp S.subtype
  let A := quadraticPolarFiber Q S.subtype (Q x) l
  let B := quadraticPolarFiber P f (Q x) l
  have hcount : Fintype.card A = Fintype.card B :=
    quadraticPolarFiber_card_eq_of_gauss Q P hQ hP hcard hgauss
      S.subtype f Subtype.val_injective hfi (fun s => (hfq s).symm) (Q x) l
  let A₀ := {z : A // z.val ∈ S}
  let B₀ := {z : B // z.val ∈ LinearMap.range f}
  let e : A₀ → B₀ := fun z =>
    ⟨⟨f ⟨z.val.val,z.property⟩, by
      constructor
      · exact (hfq _).trans z.val.property.1
      · intro s
        exact (quadratic_preserves_polar_between Q P S f hfq _ s).trans
          (z.val.property.2 s)⟩, ⟨⟨z.val.val,z.property⟩,rfl⟩⟩
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
        rw [← quadratic_preserves_polar_between Q P S f hfq s t, hs]
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

/-- A genuine one-direction extension into a different quadratic space. -/
theorem exists_quadratic_extension_step_of_gauss [Fintype V] [Fintype W]
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (hcard : Fintype.card V = Fintype.card W)
    (hgauss : binaryQuadraticGaussSum Q = binaryQuadraticGaussSum P)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] W)
    (hfi : Function.Injective f) (hfq : ∀ s : S, P (f s) = Q s.val)
    (x : V) (hx : x ∉ S) :
    ∃ g : ↥(S ⊔ Submodule.span (ZMod 2) {x}) →ₗ[ZMod 2] W,
      Function.Injective g ∧ (∀ z, P (g z) = Q z.val) ∧
      ∀ s : S, g ⟨s.val, (show S ≤ S ⊔ Submodule.span (ZMod 2) {x} from le_sup_left) s.property⟩ = f s := by
  obtain ⟨y, hy, hqy, hpy⟩ :=
    exists_external_quadraticFiber_of_gauss Q P hQ hP hcard hgauss S f hfi hfq x hx
  obtain ⟨g, hgf, hgx⟩ := f.exists_extend_of_notMem hx y
  have hgs (s : S) : g s.val = f s := congrArg (fun m : S →ₗ[ZMod 2] W => m s) hgf
  let T := S ⊔ Submodule.span (ZMod 2) {x}
  have decomp (z : T) : ∃ s : S, ∃ a : ZMod 2,
      z.val = s.val + a • x ∧ g z.val = f s + a • y := by
    obtain ⟨s, hs, t, ht, he⟩ := Submodule.mem_sup.mp z.property
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht
    refine ⟨⟨s,hs⟩,a,he.symm,?_⟩
    rw [← he, map_add, map_smul, hgs ⟨s,hs⟩, hgx]
  refine ⟨g.domRestrict T, ?_, ?_, hgs⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change g z.val = 0 at hz
    obtain ⟨s,a,hzv,hgz⟩ := decomp z
    rw [hgz] at hz
    fin_cases a
    · have hs : f s = 0 := by simpa using hz
      have hs0 : s = 0 := hfi (by simpa using hs)
      apply Subtype.ext
      simpa [hs0] using hzv
    · have hz' : f s + y = 0 := by simpa using hz
      exact False.elim (hy ⟨-s, by
        rw [map_neg]
        exact (eq_neg_of_add_eq_zero_right hz').symm⟩)
  · intro z
    change P (g z.val) = Q z.val
    obtain ⟨s,a,hzv,hgz⟩ := decomp z
    rw [hgz, hzv]
    have hp : P.polarBilin (f s) y = Q.polarBilin s.val x := by
      rw [(polar_isSymm P).eq (f s) y, hpy, (polar_isSymm Q).eq x s.val]
    fin_cases a <;> simp [quadratic_add, hfq, hqy, hp]

/-- Any actual partial isometry extends between nondegenerate ambient spaces
whose genuine dimensions and character sums agree. -/
theorem exists_quadraticIsometryEquiv_extension_of_gauss
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    [Fintype V] [Fintype W]
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (hdim : finrank (ZMod 2) V = finrank (ZMod 2) W)
    (hgauss : binaryQuadraticGaussSum Q = binaryQuadraticGaussSum P)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] W)
    (hfi : Function.Injective f) (hfq : ∀ s : S, P (f s) = Q s.val) :
    ∃ e : Q.IsometryEquiv P, ∀ s : S, e s.val = f s := by
  have hcard : Fintype.card V = Fintype.card W := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := V),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := W), hdim]
  suffices ∀ d (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] W),
      Function.Injective f → (∀ s : S, P (f s) = Q s.val) →
      finrank (ZMod 2) V - finrank (ZMod 2) S = d →
      ∃ e : Q.IsometryEquiv P, ∀ s : S, e s.val = f s by
    exact this _ S f hfi hfq rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro S f hfi hfq hd
    by_cases hS : S = ⊤
    · let j := LinearEquiv.ofTop S hS
      let g := f.comp j.symm.toLinearMap
      have hgi : Function.Injective g := hfi.comp j.symm.injective
      have hgs : Function.Surjective g :=
        (Fintype.bijective_iff_injective_and_card g).mpr ⟨hgi,hcard⟩ |>.surjective
      let e : V ≃ₗ[ZMod 2] W := LinearEquiv.ofBijective g ⟨hgi,hgs⟩
      refine ⟨⟨e, ?_⟩, ?_⟩
      · intro v
        change P (f (j.symm v)) = Q v
        rw [hfq]
        rfl
      · intro s
        change f (j.symm s.val) = f s
        exact congrArg f (j.symm_apply_apply s)
    · obtain ⟨x,hx⟩ : ∃ x : V, x ∉ S := by
        by_contra! h
        exact hS (top_unique (fun x _ => h x))
      let T := S ⊔ Submodule.span (ZMod 2) {x}
      have hST : S < T := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro he
        apply hx
        rw [he]
        exact (show Submodule.span (ZMod 2) {x} ≤ T from le_sup_right)
          (Submodule.mem_span_singleton_self x)
      have hdimST := Submodule.finrank_lt_finrank_of_lt hST
      have hbound := T.finrank_le
      have hgap : finrank (ZMod 2) V - finrank (ZMod 2) T < d := by omega
      obtain ⟨g,hgi,hgq,hgf⟩ :=
        exists_quadratic_extension_step_of_gauss Q P hQ hP hcard hgauss S f hfi hfq x hx
      obtain ⟨e,he⟩ := ih _ hgap T g hgi hgq rfl
      exact ⟨e, fun s => (he ⟨s.val,(show S ≤ T from le_sup_left) s.property⟩).trans (hgf s)⟩

/-- Complete actual isometry classification by dimension and genuine Gauss sum.
Neither a classification theorem nor an embedding criterion is a hypothesis. -/
theorem binaryQuadratic_isometryEquiv_iff_finrank_gauss
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    [Fintype V] [Fintype W]
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin) :
    Nonempty (Q.IsometryEquiv P) ↔
      finrank (ZMod 2) V = finrank (ZMod 2) W ∧
      binaryQuadraticGaussSum Q = binaryQuadraticGaussSum P := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toLinearEquiv.finrank_eq, binaryQuadraticGaussSum_eq_of_isometry Q P e⟩
  · rintro ⟨hdim,hgauss⟩
    let f : (⊥ : Submodule (ZMod 2) V) →ₗ[ZMod 2] W := 0
    have hfi : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
    have hfq (s : (⊥ : Submodule (ZMod 2) V)) : P (f s) = Q s.val := by
      have hs : s.val = 0 := s.property
      simp [f, hs]
    obtain ⟨e,_⟩ := exists_quadraticIsometryEquiv_extension_of_gauss
      Q P hQ hP hdim hgauss ⊥ f hfi hfq
    exact ⟨e⟩

/-- The zero-dimensional endpoint has positive Gauss sum one. -/
theorem binaryQuadraticGaussSum_of_subsingleton [Fintype V] [Subsingleton V]
    (Q : QuadraticForm (ZMod 2) V) : binaryQuadraticGaussSum Q = 1 := by
  have hzero (x : V) : x = 0 := Subsingleton.elim _ _
  have hcard : Fintype.card V = 1 := Fintype.card_eq_one_iff.mpr ⟨0,hzero⟩
  simp [binaryQuadraticGaussSum, hzero, hcard]

end ExactCriticalCurve.FiniteQuadratic
