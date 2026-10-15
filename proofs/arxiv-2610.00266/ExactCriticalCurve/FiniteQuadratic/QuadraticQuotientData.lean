import ExactCriticalCurve.FiniteQuadratic.Quotient
import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRealizability

/-! Full binary quadratic descent with its singular and polar-radical conditions retained. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {E V : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Pullback from a quotient is singular on the kernel and has that kernel in its polar radical. -/
theorem quadraticQuotient_pullback_descent (K : Submodule (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) (E ⧸ K)) :
    K ≤ LinearMap.ker (q.comp K.mkQ).polarBilin ∧ TotallySingular (q.comp K.mkQ) K := by
  have hz (x : E) (hx : x ∈ K) : K.mkQ x=0 := by
    rw [← LinearMap.mem_ker,Submodule.ker_mkQ]
    exact hx
  constructor
  · intro x hx
    apply LinearMap.mem_ker.mpr
    ext y
    have hx0 : (Submodule.Quotient.mk x : E ⧸ K)=0 := hz x hx
    simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hx0]
  · intro x hx
    simp [hz x hx]

/-- All full quadratic forms on the quotient correspond exactly to singular radical descent data. -/
def quadraticQuotientEquivDescent (K : Submodule (ZMod 2) E) :
    QuadraticForm (ZMod 2) (E ⧸ K) ≃
      {q : QuadraticForm (ZMod 2) E // K ≤ LinearMap.ker q.polarBilin ∧ TotallySingular q K} where
  toFun q := ⟨q.comp K.mkQ,quadraticQuotient_pullback_descent K q⟩
  invFun q := quotientForm q.val K q.property.2 (fun x hx y =>
    congrArg (fun l : E →ₗ[ZMod 2] ZMod 2 => l y) (q.property.1 hx))
  left_inv q := by
    ext z
    obtain ⟨x,rfl⟩ := K.mkQ_surjective z
    rfl
  right_inv q := by
    apply Subtype.ext
    ext x
    rfl

@[simp] theorem quadraticQuotientEquivDescent_apply (K : Submodule (ZMod 2) E)
    (q : QuadraticForm (ZMod 2) (E ⧸ K)) :
    (quadraticQuotientEquivDescent K q).val=q.comp K.mkQ := rfl

/-- A prescribed actual kernel is equivalent to an injective realization of the full quotient form. -/
theorem quotientQuadratic_realization_iff_embedding
    (K : Submodule (ZMod 2) E) (q : QuadraticForm (ZMod 2) (E ⧸ K))
    (Q : QuadraticForm (ZMod 2) V) :
    (∃ f : E →ₗ[ZMod 2] V, LinearMap.ker f=K ∧ ∀ x, Q (f x)=q (K.mkQ x)) ↔
    (∃ g : (E ⧸ K) →ₗ[ZMod 2] V, Function.Injective g ∧ ∀ x, Q (g x)=q x) := by
  constructor
  · rintro ⟨f,hf,hfq⟩
    let g := K.liftQ f (le_of_eq hf.symm)
    have hg : Function.Injective g := by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.ker_liftQ,hf,Submodule.mkQ_map_self]
    refine ⟨g,hg,?_⟩
    intro z
    obtain ⟨x,rfl⟩ := K.mkQ_surjective z
    exact hfq x
  · rintro ⟨g,hg,hgq⟩
    refine ⟨g.comp K.mkQ,?_,fun x => hgq (K.mkQ x)⟩
    ext x
    change g (K.mkQ x)=0 ↔ x ∈ K
    have hk : K.mkQ x=0 ↔ x ∈ K := by
      rw [← LinearMap.mem_ker,Submodule.ker_mkQ]
    constructor
    · intro h
      exact hk.mp (hg (by simpa using h))
    · intro h
      simp [hk.mpr h]

/-- The complete quotient criterion keeps the signed Gauss boundary and zero-dimensional cases. -/
theorem quotientQuadratic_realization_iff
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V] [Fintype V]
    (K : Submodule (ZMod 2) E) [Fintype (E ⧸ K)]
    (q : QuadraticForm (ZMod 2) (E ⧸ K)) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) :
    (∃ f : E →ₗ[ZMod 2] V, LinearMap.ker f=K ∧ ∀ x, Q (f x)=q (K.mkQ x)) ↔
      finrank (ZMod 2) (E ⧸ K)+finrank (ZMod 2) (binaryPolarRadical q) ≤ finrank (ZMod 2) V ∧
      (finrank (ZMod 2) (E ⧸ K)+finrank (ZMod 2) (binaryPolarRadical q) < finrank (ZMod 2) V ∨
        binaryQuadraticGaussSum q=0 ∨ binaryQuadraticGaussSum Q=binaryQuadraticGaussSum q) := by
  rw [quotientQuadratic_realization_iff_embedding]
  exact exists_binaryQuadratic_embedding_iff q Q hQ

end ExactCriticalCurve.FiniteQuadratic
