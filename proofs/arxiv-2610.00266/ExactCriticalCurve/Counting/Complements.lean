import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

/-!
# Counting all complements of an actual subspace

For a fixed decomposition V = p ⊕ H, this file constructs a bijection
between every complement of p and the actual linear maps H → p.
In particular, this counts all complements, not just a parametrized family.
The binary cardinality follows from the dimension of this Hom space.
-/

noncomputable section

namespace ExactCriticalCurve.Counting

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Retractions onto p are exactly arbitrary linear maps on a fixed complement H. -/
def retractionEquivHom (p H : Submodule K V) (h : IsCompl p H) :
    {f : V →ₗ[K] p // ∀ x : p, f x = x} ≃ (H →ₗ[K] p) where
  toFun f := f.val.domRestrict H
  invFun g := ⟨LinearMap.ofIsCompl h LinearMap.id g, by intro x; simp⟩
  left_inv f := by
    apply Subtype.ext
    exact LinearMap.ofIsCompl_eq h (fun x => (f.property x).symm) (fun _ => rfl)
  right_inv g := by
    apply LinearMap.ext
    intro x
    exact LinearMap.ofIsCompl_right_apply h (φ := LinearMap.id) (ψ := g) x

/-- Every complement of p occurs exactly once, through its projection onto p
along that complement, restricted to the fixed H. -/
def complementsEquivHom (p H : Submodule K V) (h : IsCompl p H) :
    {q : Submodule K V // IsCompl p q} ≃ (H →ₗ[K] p) :=
  p.isComplEquivProj.trans (retractionEquivHom p H h)

/-- The inverse parameterization is the actual kernel of the extension
that is identity on p and the specified linear map on H. -/
@[simp] theorem complementsEquivHom_symm_apply
    (p H : Submodule K V) (h : IsCompl p H) (g : H →ₗ[K] p) :
    ((complementsEquivHom p H h).symm g).val =
      LinearMap.ker (LinearMap.ofIsCompl h LinearMap.id g) := rfl

/-- Cardinality of the full complement type over a finite field. -/
theorem card_complements [Finite K] [FiniteDimensional K V]
    (p H : Submodule K V) (h : IsCompl p H) :
    Nat.card {q : Submodule K V // IsCompl p q} =
      Nat.card K ^ (Module.finrank K H * Module.finrank K p) := by
  rw [Nat.card_congr (complementsEquivHom p H h),
    Module.natCard_eq_pow_finrank (K := K),
    Module.finrank_linearMap (R := K) (S := K)]

/-- The binary formula counts all complements of p. -/
theorem card_complements_binary
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (p H : Submodule (ZMod 2) V) (h : IsCompl p H) :
    Nat.card {q : Submodule (ZMod 2) V // IsCompl p q} =
      2 ^ (Module.finrank (ZMod 2) H * Module.finrank (ZMod 2) p) := by
  rw [card_complements p H h, Nat.card_eq_fintype_card, ZMod.card]

/-- A binary line with an r-dimensional fixed complement has exactly 2^r
complements. Both dimensions refer to the actual subspaces. -/
theorem card_complements_binary_line
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (p H : Submodule (ZMod 2) V) (h : IsCompl p H) (r : ℕ)
    (hp : Module.finrank (ZMod 2) p = 1) (hH : Module.finrank (ZMod 2) H = r) :
    Nat.card {q : Submodule (ZMod 2) V // IsCompl p q} = 2 ^ r := by
  rw [card_complements_binary p H h, hp, hH, mul_one]


/-- The hyperplanes missing a nonzero vector are exactly all complements
of its line. The dimension condition rules out smaller disjoint spaces. -/
theorem span_singleton_isCompl_iff [FiniteDimensional K V]
    (w : V) (hw : w ≠ 0) (q : Submodule K V) :
    IsCompl (Submodule.span K {w}) q ↔
      Module.finrank K q + 1 = Module.finrank K V ∧ w ∉ q := by
  have hline : Module.finrank K (Submodule.span K {w}) = 1 :=
    finrank_span_singleton hw
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [hline] using Submodule.finrank_add_eq_of_isCompl h.symm
    · exact (Submodule.disjoint_span_singleton' hw).mp h.symm.disjoint
  · rintro ⟨hdim, hnot⟩
    have hbound : Module.finrank K V ≤
        Module.finrank K q + Module.finrank K (Submodule.span K {w}) := by
      rw [hline, hdim]
    exact ((Submodule.isCompl_iff_disjoint q _ hbound).mpr
      (Submodule.disjoint_span_singleton_of_notMem hnot)).symm

/-- This equivalence includes every hyperplane missing w, with no chosen
family or graph parameterization imposed on the hyperplane index. -/
def missingHyperplanesEquivComplements [FiniteDimensional K V]
    (w : V) (hw : w ≠ 0) :
    {q : Submodule K V //
      Module.finrank K q + 1 = Module.finrank K V ∧ w ∉ q} ≃
    {q : Submodule K V // IsCompl (Submodule.span K {w}) q} where
  toFun q := ⟨q.val, (span_singleton_isCompl_iff w hw q.val).mpr q.property⟩
  invFun q := ⟨q.val, (span_singleton_isCompl_iff w hw q.val).mp q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full binary hyperplane count in an actual (r+1)-dimensional vector space. -/
theorem card_missingHyperplanes_binary
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (w : V) (hw : w ≠ 0) (r : ℕ) (hV : Module.finrank (ZMod 2) V = r + 1) :
    Nat.card {q : Submodule (ZMod 2) V //
      Module.finrank (ZMod 2) q + 1 = Module.finrank (ZMod 2) V ∧ w ∉ q} = 2 ^ r := by
  let p : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {w}
  obtain ⟨H, h⟩ := p.exists_isCompl
  have hp : Module.finrank (ZMod 2) p = 1 := finrank_span_singleton hw
  have hH : Module.finrank (ZMod 2) H = r := by
    have hd := Submodule.finrank_add_eq_of_isCompl h.symm
    rw [hp, hV] at hd
    exact Nat.add_right_cancel hd
  rw [Nat.card_congr (missingHyperplanesEquivComplements w hw)]
  exact card_complements_binary_line p H h r hp hH

end ExactCriticalCurve.Counting
