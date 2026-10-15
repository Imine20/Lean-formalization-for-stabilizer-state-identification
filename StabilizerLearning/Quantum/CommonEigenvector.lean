import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! A finite commuting family over an algebraically closed field has a common
nonzero eigenvector. The proof successively restricts to nonzero invariant
subspaces; no simultaneous eigenbasis is assumed. -/
noncomputable section
open scoped ComplexOrder
namespace StabilizerLearning.Quantum

variable {K V I : Type*} [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

/-- Simultaneous eigenvector existence for every finite commuting family. -/
theorem exists_common_eigenvector [Fintype I] (f : I → Module.End K V)
    (hcomm : ∀ i j, Commute (f i) (f j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, f i v = c • v := by
  classical
  have aux (s : Finset I) :
      ∃ E : Submodule K V, E ≠ ⊥ ∧
        (∀ i ∈ s, ∃ c : K, ∀ v ∈ E, f i v = c • v) ∧
        (∀ i, ∀ v ∈ E, f i v ∈ E) := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨⊤, top_ne_bot, by simp, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨E, hE, hscalar, hmap⟩ := ih
      letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE
      let g : Module.End K E := (f a).restrict (hmap a)
      obtain ⟨c, hc⟩ := g.exists_eigenvalue
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have hvnon : (v : V) ≠ 0 := by
        intro hz
        exact hv.2 (Subtype.ext hz)
      have hveig : (v : V) ∈ (f a).eigenspace c := by
        apply Module.End.mem_eigenspace_iff.mpr
        exact congrArg Subtype.val hv.apply_eq_smul
      refine ⟨E ⊓ (f a).eigenspace c, ?_, ?_, ?_⟩
      · intro heq
        have hmem : (v : V) ∈ E ⊓ (f a).eigenspace c := ⟨v.property, hveig⟩
        rw [heq, Submodule.mem_bot] at hmem
        exact hvnon hmem
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact ⟨c, fun _ hx => Module.End.mem_eigenspace_iff.mp hx.2⟩
        · obtain ⟨d, hd⟩ := hscalar i hi
          exact ⟨d, fun _ hx => hd _ hx.1⟩
      · intro i w hw
        refine ⟨hmap i w hw.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have heq : f a (f i w) = f i (f a w) :=
          congrArg (fun T : Module.End K V => T w) (hcomm a i).eq
        rw [heq, Module.End.mem_eigenspace_iff.mp hw.2, map_smul]
  obtain ⟨E, hE, hscalar, _⟩ := aux Finset.univ
  obtain ⟨v, hvE, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
  refine ⟨v, hv, fun i => ?_⟩
  obtain ⟨c, hc⟩ := hscalar i (Finset.mem_univ i)
  exact ⟨c, hc v hvE⟩

/-- An eigenvalue of a complex unitary matrix has unit modulus. -/
theorem unitary_eigenvalue_norm_eq_one {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (hunitary : A.conjTranspose * A = 1)
    (v : J → ℂ) (hv : v ≠ 0) (c : ℂ) (heig : A.mulVec v = c • v) :
    ‖c‖ = 1 := by
  have hq : dotProduct (star v) v ≠ 0 := by
    intro h
    exact hv (dotProduct_star_self_eq_zero.mp h)
  have hh : dotProduct (star (A.mulVec v)) (A.mulVec v) = dotProduct (star v) v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hunitary, Matrix.one_mulVec]
  rw [heig, star_smul, smul_dotProduct, dotProduct_smul] at hh
  have hc : star c * c = 1 := by
    apply mul_right_cancel₀ hq
    simpa only [smul_eq_mul, mul_assoc, one_mul] using hh
  have hn := congrArg norm hc
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg c]

end StabilizerLearning.Quantum
