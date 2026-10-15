import ExactCriticalCurve.FiniteQuadratic.AlternatingRealizability
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Actual alternating forms on quotients and exact realization with prescribed kernel. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {E V : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Descend the complete alternating form in both variables through a radical subspace. -/
def alternatingQuotientForm (A : LinearMap.BilinForm (ZMod 2) E) (hA : A.IsAlt)
    (K : Submodule (ZMod 2) E) (hK : K ≤ LinearMap.ker A) :
    LinearMap.BilinForm (ZMod 2) (E ⧸ K) := by
  have hr : K ≤ LinearMap.ker A.flip := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    ext y
    change A y x = 0
    rw [(binaryAlternating_isSymm A hA).eq]
    exact congrArg (fun l : E →ₗ[ZMod 2] ZMod 2 => l y) (hK hx)
  let qR := K.liftQ A.flip hr
  have hl : K ≤ LinearMap.ker qR.flip := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    obtain ⟨y,rfl⟩ := K.mkQ_surjective z
    change A x y = 0
    exact congrArg (fun l : E →ₗ[ZMod 2] ZMod 2 => l y) (hK hx)
  exact K.liftQ qR.flip hl

@[simp] theorem alternatingQuotientForm_mk (A : LinearMap.BilinForm (ZMod 2) E)
    (hA : A.IsAlt) (K : Submodule (ZMod 2) E) (hK : K ≤ LinearMap.ker A) (x y : E) :
    alternatingQuotientForm A hA K hK (K.mkQ x) (K.mkQ y) = A x y := rfl

theorem alternatingQuotientForm_isAlt (A : LinearMap.BilinForm (ZMod 2) E)
    (hA : A.IsAlt) (K : Submodule (ZMod 2) E) (hK : K ≤ LinearMap.ker A) :
    (alternatingQuotientForm A hA K hK).IsAlt := by
  intro z
  obtain ⟨x,rfl⟩ := K.mkQ_surjective z
  exact hA.self_eq_zero x

/-- The quotient radical is the image of the full original radical. -/
theorem alternatingQuotientForm_ker (A : LinearMap.BilinForm (ZMod 2) E)
    (hA : A.IsAlt) (K : Submodule (ZMod 2) E) (hK : K ≤ LinearMap.ker A) :
    LinearMap.ker (alternatingQuotientForm A hA K hK) = (LinearMap.ker A).map K.mkQ := by
  ext z
  obtain ⟨x,rfl⟩ := K.mkQ_surjective z
  constructor
  · intro h
    refine ⟨x,?_,rfl⟩
    apply LinearMap.mem_ker.mpr
    ext y
    exact congrArg (fun l : (E ⧸ K) →ₗ[ZMod 2] ZMod 2 => l (K.mkQ y)) h
  · rintro ⟨y,hy,he⟩
    rw [← he]
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    obtain ⟨w,rfl⟩ := K.mkQ_surjective z
    exact congrArg (fun l : E →ₗ[ZMod 2] ZMod 2 => l w) hy

/-- Actual pullback along the quotient map has kernel exactly K precisely when the quotient map is injective. -/
theorem quotientForm_realization_iff_embedding
    (K : Submodule (ZMod 2) E) (A : LinearMap.BilinForm (ZMod 2) (E ⧸ K))
    (B : LinearMap.BilinForm (ZMod 2) V) :
    (∃ f : E →ₗ[ZMod 2] V, LinearMap.ker f = K ∧
      ∀ x y, B (f x) (f y) = A (K.mkQ x) (K.mkQ y)) ↔
    (∃ g : (E ⧸ K) →ₗ[ZMod 2] V, Function.Injective g ∧
      ∀ x y, B (g x) (g y) = A x y) := by
  constructor
  · rintro ⟨f,hf,hfp⟩
    let g := K.liftQ f (le_of_eq hf.symm)
    have hg : Function.Injective g := by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.ker_liftQ, hf, Submodule.mkQ_map_self]
    refine ⟨g,hg,?_⟩
    intro x y
    obtain ⟨x,rfl⟩ := K.mkQ_surjective x
    obtain ⟨y,rfl⟩ := K.mkQ_surjective y
    exact hfp x y
  · rintro ⟨g,hg,hgp⟩
    refine ⟨g.comp K.mkQ, ?_, fun x y => hgp (K.mkQ x) (K.mkQ y)⟩
    ext x
    change g (K.mkQ x) = 0 ↔ x ∈ K
    have hk : K.mkQ x = 0 ↔ x ∈ K := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    constructor
    · intro h
      exact hk.mp (hg (by simpa using h))
    · intro h
      simp [hk.mpr h]

/-- The exact specified-kernel criterion counts true quotient forms, including degenerate ones. -/
theorem quotientAlternating_realization_iff
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V]
    (K : Submodule (ZMod 2) E) (A : LinearMap.BilinForm (ZMod 2) (E ⧸ K))
    (hA : A.IsAlt) (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate) :
    (∃ f : E →ₗ[ZMod 2] V, LinearMap.ker f = K ∧
      ∀ x y, B (f x) (f y) = A (K.mkQ x) (K.mkQ y)) ↔
      finrank (ZMod 2) (E ⧸ K) + finrank (ZMod 2) (LinearMap.ker A) ≤ finrank (ZMod 2) V := by
  rw [quotientForm_realization_iff_embedding]
  exact exists_alternating_embedding_iff A hA B hB hBn

/-- The quotient radical dimension identity is additive, without truncated subtraction. -/
theorem alternatingQuotientForm_radical_finrank
    [FiniteDimensional (ZMod 2) E]
    (A : LinearMap.BilinForm (ZMod 2) E) (hA : A.IsAlt)
    (K : Submodule (ZMod 2) E) (hK : K ≤ LinearMap.ker A) :
    finrank (ZMod 2) (LinearMap.ker (alternatingQuotientForm A hA K hK)) +
      finrank (ZMod 2) K = finrank (ZMod 2) (LinearMap.ker A) := by
  let R := LinearMap.ker A
  let g := K.mkQ.domRestrict R
  have hr : LinearMap.range g = LinearMap.ker (alternatingQuotientForm A hA K hK) := by
    rw [alternatingQuotientForm_ker]
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have hk : finrank (ZMod 2) (LinearMap.ker g) = finrank (ZMod 2) K := by
    dsimp only [g]
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
    exact (Submodule.comapSubtypeEquivOfLe hK).finrank_eq
  have he := LinearMap.finrank_range_add_finrank_ker g
  rw [hr,hk] at he
  exact he

/-- Complete full-form invariant realizability with the actual prescribed kernel. -/
theorem exists_alternating_map_ker_iff
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V]
    (K : Submodule (ZMod 2) E) (A : LinearMap.BilinForm (ZMod 2) E)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate) :
    (∃ f : E →ₗ[ZMod 2] V, LinearMap.ker f = K ∧ ∀ x y, B (f x) (f y) = A x y) ↔
      A.IsAlt ∧ K ≤ LinearMap.ker A ∧
        finrank (ZMod 2) E + finrank (ZMod 2) (LinearMap.ker A) ≤
          finrank (ZMod 2) V + 2 * finrank (ZMod 2) K := by
  constructor
  · rintro ⟨f,hf,hfp⟩
    have hA : A.IsAlt := fun x => (hfp x x).symm.trans (hB.self_eq_zero (f x))
    have hK : K ≤ LinearMap.ker A := by
      intro x hx
      have hfx : f x = 0 := by rw [← hf] at hx; exact hx
      apply LinearMap.mem_ker.mpr
      ext y
      rw [← hfp,hfx]
      simp
    refine ⟨hA,hK,?_⟩
    have he := (quotientAlternating_realization_iff K (alternatingQuotientForm A hA K hK)
      (alternatingQuotientForm_isAlt A hA K hK) B hB hBn).mp
      ⟨f,hf,fun x y => (hfp x y).trans (alternatingQuotientForm_mk A hA K hK x y).symm⟩
    have hd₁ := Submodule.finrank_quotient_add_finrank K
    have hd₂ := alternatingQuotientForm_radical_finrank A hA K hK
    omega
  · rintro ⟨hA,hK,hd⟩
    have hd₁ := Submodule.finrank_quotient_add_finrank K
    have hd₂ := alternatingQuotientForm_radical_finrank A hA K hK
    have he : finrank (ZMod 2) (E ⧸ K) +
        finrank (ZMod 2) (LinearMap.ker (alternatingQuotientForm A hA K hK)) ≤
          finrank (ZMod 2) V := by omega
    obtain ⟨f,hf,hfp⟩ := (quotientAlternating_realization_iff K (alternatingQuotientForm A hA K hK)
      (alternatingQuotientForm_isAlt A hA K hK) B hB hBn).mpr he
    exact ⟨f,hf,fun x y => (hfp x y).trans (alternatingQuotientForm_mk A hA K hK x y)⟩

end ExactCriticalCurve.FiniteQuadratic
