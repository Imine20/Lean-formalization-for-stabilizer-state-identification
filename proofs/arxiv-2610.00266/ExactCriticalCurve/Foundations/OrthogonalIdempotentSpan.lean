import ExactCriticalCurve.Foundations.MatrixProjectionGrades
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The actual real span of orthogonal nonzero matrix idempotents

Coefficient extraction proves independence. A stated finite-dimensional bound on
a containing real submodule then gives its unique expansion; no spectral
decomposition or algebra closure is assumed.
-/
noncomputable section
open scoped BigOperators
open Matrix
namespace ExactCriticalCurve

variable {ι α : Type*} [Fintype ι] [Fintype α]
variable (F : α → Matrix ι ι ℂ)
    (hI : ∀ i, F i * F i = F i)
    (hO : ∀ i j, i ≠ j → F i * F j = 0)

include hI hO in
theorem orthogonalIdempotents_sum_mul (c : α → ℝ) (i : α) :
    (∑ j, c j • F j) * F i = c i • F i := by
  classical
  rw [Matrix.sum_mul]
  simp_rw [Matrix.smul_mul]
  rw [Finset.sum_eq_single i]
  · rw [hI]
  · intro j _ hji
    rw [hO j i hji, smul_zero]
  · simp

include hI hO in
theorem orthogonalIdempotents_mul_sum (c : α → ℝ) (i : α) :
    F i * (∑ j, c j • F j) = c i • F i := by
  classical
  rw [Matrix.mul_sum]
  simp_rw [Matrix.mul_smul]
  rw [Finset.sum_eq_single i]
  · rw [hI]
  · intro j _ hji
    rw [hO i j hji.symm, smul_zero]
  · simp

variable (hZ : ∀ i, F i ≠ 0)

include hI hO hZ in
theorem orthogonalIdempotents_linearIndependent : LinearIndependent ℝ F := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h : c i • F i = 0 := by
    rw [← orthogonalIdempotents_sum_mul F hI hO c i, hc, zero_mul]
  exact (smul_eq_zero.mp h).resolve_right (hZ i)

include hI hO hZ in
theorem orthogonalIdempotents_finrank_span :
    Module.finrank ℝ (Submodule.span ℝ (Set.range F)) = Fintype.card α :=
  finrank_span_eq_card (orthogonalIdempotents_linearIndependent F hI hO hZ)

include hI hO hZ in
theorem orthogonalIdempotents_expansion_injective :
    Function.Injective (fun c : α → ℝ => ∑ i, c i • F i) := by
  intro c d hcd
  change (∑ i, c i • F i) = ∑ i, d i • F i at hcd
  funext i
  have h : c i • F i = d i • F i := by
    rw [← orthogonalIdempotents_sum_mul F hI hO c i, hcd,
      orthogonalIdempotents_sum_mul F hI hO d i]
  have hz : (c i - d i) • F i = 0 := by
    rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (hZ i))

include hI hO hZ in
theorem orthogonalIdempotents_submodule_eq_span
    (A : Submodule ℝ (Matrix ι ι ℂ)) (hF : ∀ i, F i ∈ A)
    (hD : Module.finrank ℝ A ≤ Fintype.card α) :
    A = Submodule.span ℝ (Set.range F) := by
  have hs : Submodule.span ℝ (Set.range F) ≤ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hF i
  exact (Submodule.eq_of_le_of_finrank_le hs
    (by rwa [orthogonalIdempotents_finrank_span F hI hO hZ])).symm

include hI hO hZ in
theorem orthogonalIdempotents_existsUnique_expansion
    (A : Submodule ℝ (Matrix ι ι ℂ)) (hF : ∀ i, F i ∈ A)
    (hD : Module.finrank ℝ A ≤ Fintype.card α)
    (X : Matrix ι ι ℂ) (hX : X ∈ A) :
    ∃! c : α → ℝ, X = ∑ i, c i • F i := by
  rw [orthogonalIdempotents_submodule_eq_span F hI hO hZ A hF hD] at hX
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hX
  refine ⟨c, hc.symm, ?_⟩
  intro d hd
  exact orthogonalIdempotents_expansion_injective F hI hO hZ (hd.symm.trans hc.symm)

include hI hO in
theorem orthogonalIdempotents_scalar_action_of_expansion
    (X : Matrix ι ι ℂ) (c : α → ℝ) (hX : X = ∑ i, c i • F i) :
    ∀ i, X * F i = c i • F i ∧ F i * X = c i • F i := by
  intro i
  rw [hX]
  exact ⟨orthogonalIdempotents_sum_mul F hI hO c i,
    orthogonalIdempotents_mul_sum F hI hO c i⟩

include hI hO hZ in
theorem orthogonalIdempotents_corner_unit
    (A : Submodule ℝ (Matrix ι ι ℂ)) (hF : ∀ i, F i ∈ A)
    (hD : Module.finrank ℝ A ≤ Fintype.card α)
    (U : Matrix ι ι ℂ) (hU : U ∈ A) (hUF : ∀ i, U * F i = F i) :
    U = ∑ i, F i := by
  obtain ⟨c, hc, _⟩ := orthogonalIdempotents_existsUnique_expansion F hI hO hZ A hF hD U hU
  have hc1 : ∀ i, c i = 1 := by
    intro i
    have h : c i • F i = F i := by
      rw [← orthogonalIdempotents_sum_mul F hI hO c i, ← hc, hUF]
    have hz : (c i - 1) • F i = 0 := by rw [sub_smul, h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (hZ i))
  simpa only [hc1, one_smul] using hc

end ExactCriticalCurve
