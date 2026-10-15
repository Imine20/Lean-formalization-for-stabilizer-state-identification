import ExactCriticalCurve.Quantum.CompressedOrbitDimension
import ExactCriticalCurve.Quantum.CompressedCSSMembership
import ExactCriticalCurve.Quantum.PhysicalCSSGrades
import ExactCriticalCurve.Foundations.OrthogonalIdempotentSpan
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Actual physical sector exhaustion in the stable range

For positive copy number and k ≤ n, the nonempty ordinary/exceptional rank
classes give a basis of the actual compressed real relation span. The rank
bound, nonzero grades, and decomposition are conclusions, not assumptions.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Classical Matrix Module
namespace ExactCriticalCurve.Binary
variable {k r : ℕ}

theorem exceptionalDefect_four_dvd (N : ExceptionalDefect k r) : 4 ∣ k :=
  (weightQuadratic_allOnes_eq_zero_iff k).mp (N.property.1 _ N.property.2.2)

theorem exceptionalDefect_rank_pos (hk : 0 < k) (N : ExceptionalDefect k r) : 0 < r := by
  by_contra h
  have hr : r = 0 := by omega
  subst r
  letI := exceptionalDefect_zero_isEmpty hk
  exact isEmptyElim N

end ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum
open Binary
variable {n k : ℕ}

/-- Each index certifies that its actual defect class is nonempty. -/
abbrev PhysicalSectorLabel (k : ℕ) :=
  {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)} ⊕
  {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)}

/-- The genuine difference of consecutive fixed CSS support projections. -/
def physicalSectorGrade (n k : ℕ) : PhysicalSectorLabel k →
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ
  | .inl r => ordinaryCSSGrade n k r.val.val
  | .inr r => exceptionalCSSGrade n k r.val.val

theorem physicalSectorGrade_mem_span (n k : ℕ) (a : PhysicalSectorLabel k) :
    physicalSectorGrade n k a ∈ compressedRelationSpan n k := by
  cases a with
  | inl r => exact ordinaryFixedCSSProjection_sub_mem_compressedRelationSpan n k _ _
  | inr r => exact exceptionalFixedCSSProjection_sub_mem_compressedRelationSpan n k _ _

theorem physicalSectorGrade_isHermitian (n k : ℕ) (a : PhysicalSectorLabel k) :
    (physicalSectorGrade n k a).IsHermitian := by
  cases a with
  | inl r => exact ordinaryCSSGrade_isHermitian n k _
  | inr r => exact exceptionalCSSGrade_isHermitian n k _

theorem exceptionalCSSGrade_idempotent_of_nonempty (hk : 0 < k) (n r : ℕ)
    (h : Nonempty (ExceptionalDefect k r)) :
    exceptionalCSSGrade n k r * exceptionalCSSGrade n k r = exceptionalCSSGrade n k r := by
  obtain ⟨N⟩ := h
  have hr := exceptionalDefect_rank_pos hk N
  have h4 := exceptionalDefect_four_dvd N
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact exceptionalCSSGrade_idempotent hk h4 n s

theorem physicalSectorGrade_idempotent (hk : 0 < k) (n : ℕ) (a : PhysicalSectorLabel k) :
    physicalSectorGrade n k a * physicalSectorGrade n k a = physicalSectorGrade n k a := by
  cases a with
  | inl r => exact ordinaryCSSGrade_idempotent n k _
  | inr r => exact exceptionalCSSGrade_idempotent_of_nonempty hk n _ r.property

theorem physicalSectorGrade_posSemidef (hk : 0 < k) (n : ℕ) (a : PhysicalSectorLabel k) :
    (physicalSectorGrade n k a).PosSemidef :=
  matrixProjection_posSemidef _ (physicalSectorGrade_isHermitian n k a)
    (physicalSectorGrade_idempotent hk n a)

/-- Stable witnesses give nonzero grades for every realized label. -/
theorem physicalSectorGrade_ne_zero (hk : 0 < k) (hn : k ≤ n) (a : PhysicalSectorLabel k) :
    physicalSectorGrade n k a ≠ 0 := by
  cases a with
  | inl r =>
      obtain ⟨N⟩ := r.property
      exact ordinaryCSSGrade_ne_zero N (by omega)
  | inr r =>
      obtain ⟨N⟩ := r.property
      exact exceptionalCSSGrade_ne_zero N (by omega)

theorem ordinaryCSSGrade_mul_exceptional_of_nonempty (n r s : ℕ)
    (h : Nonempty (ExceptionalDefect k s)) :
    ordinaryCSSGrade n k r * exceptionalCSSGrade n k s = 0 := by
  obtain ⟨N⟩ := h
  have h4 := exceptionalDefect_four_dvd N
  simp only [ordinaryCSSGrade,exceptionalCSSGrade,Matrix.sub_mul,Matrix.mul_sub,
    ordinaryFixedCSSProjection_mul_exceptional h4,sub_self]

theorem exceptionalCSSGrade_mul_eq_zero_of_nonempty (hk : 0 < k) (n r s : ℕ)
    (hr : Nonempty (ExceptionalDefect k r)) (hs : Nonempty (ExceptionalDefect k s))
    (hrs : r ≠ s) :
    exceptionalCSSGrade n k r * exceptionalCSSGrade n k s = 0 := by
  obtain ⟨N⟩ := hr
  obtain ⟨M⟩ := hs
  have h4 := exceptionalDefect_four_dvd N
  have hr := exceptionalDefect_rank_pos hk N
  have hs := exceptionalDefect_rank_pos hk M
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  exact exceptionalCSSGrade_mul_eq_zero hk h4 n r s (by omega)

/-- All grades, including pairs from different branches, are orthogonal. -/
theorem physicalSectorGrade_mul_eq_zero (hk : 0 < k) (n : ℕ)
    (a b : PhysicalSectorLabel k) (hab : a ≠ b) :
    physicalSectorGrade n k a * physicalSectorGrade n k b = 0 := by
  cases a with
  | inl r =>
      cases b with
      | inl s =>
          exact ordinaryCSSGrade_mul_eq_zero n k _ _ (by
            intro h
            apply hab
            congr 1
            apply Subtype.ext
            exact Fin.ext h)
      | inr s => exact ordinaryCSSGrade_mul_exceptional_of_nonempty n _ _ s.property
  | inr r =>
      cases b with
      | inl s =>
          have h := congrArg Matrix.conjTranspose
            (ordinaryCSSGrade_mul_exceptional_of_nonempty n s.val.val r.val.val r.property)
          simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_zero,
            (ordinaryCSSGrade_isHermitian n k s.val.val).eq,
            (exceptionalCSSGrade_isHermitian n k r.val.val).eq] using h
      | inr s =>
          exact exceptionalCSSGrade_mul_eq_zero_of_nonempty hk n _ _ r.property s.property (by
            intro h
            apply hab
            congr 1
            apply Subtype.ext
            exact Fin.ext h)

theorem physicalSectorGrade_linearIndependent (hk : 0 < k) (hn : k ≤ n) :
    LinearIndependent ℝ (physicalSectorGrade n k) :=
  orthogonalIdempotents_linearIndependent _
    (physicalSectorGrade_idempotent hk n)
    (physicalSectorGrade_mul_eq_zero hk n) (physicalSectorGrade_ne_zero hk hn)

theorem compressedRelationSpan_finrank_le_sectors (n k : ℕ) :
    finrank ℝ (compressedRelationSpan n k) ≤ Fintype.card (PhysicalSectorLabel k) := by
  simpa only [PhysicalSectorLabel,Fintype.card_sum] using
    compressedRelationSpan_finrank_le_defect_classes n k

/-- The actual grades exhaust the compressed relation space in the stable range. -/
theorem compressedRelationSpan_eq_span_physicalSectors (hk : 0 < k) (hn : k ≤ n) :
    compressedRelationSpan n k = Submodule.span ℝ (Set.range (physicalSectorGrade n k)) :=
  orthogonalIdempotents_submodule_eq_span _
    (physicalSectorGrade_idempotent hk n) (physicalSectorGrade_mul_eq_zero hk n)
    (physicalSectorGrade_ne_zero hk hn) _ (physicalSectorGrade_mem_span n k)
    (compressedRelationSpan_finrank_le_sectors n k)

theorem compressedRelationSpan_finrank_eq_sectors (hk : 0 < k) (hn : k ≤ n) :
    finrank ℝ (compressedRelationSpan n k) = Fintype.card (PhysicalSectorLabel k) := by
  rw [compressedRelationSpan_eq_span_physicalSectors hk hn]
  exact finrank_span_eq_card (physicalSectorGrade_linearIndependent hk hn)

/-- A genuine basis of the actual real submodule, with grade vectors as its entries. -/
def physicalSectorBasis (hk : 0 < k) (hn : k ≤ n) :
    Basis (PhysicalSectorLabel k) ℝ (compressedRelationSpan n k) :=
  (Basis.span (physicalSectorGrade_linearIndependent hk hn)).map
    (LinearEquiv.ofEq _ _ (compressedRelationSpan_eq_span_physicalSectors hk hn).symm)

theorem physicalSectorBasis_apply (hk : 0 < k) (hn : k ≤ n) (a : PhysicalSectorLabel k) :
    (physicalSectorBasis hk hn a : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ) =
      physicalSectorGrade n k a := by
  simp only [physicalSectorBasis,Basis.map_apply,LinearEquiv.coe_ofEq_apply,Basis.span_apply]

theorem physicalSector_existsUnique_expansion (hk : 0 < k) (hn : k ≤ n)
    (A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ)
    (hA : A ∈ compressedRelationSpan n k) :
    ∃! c : PhysicalSectorLabel k → ℝ, A = ∑ a, c a • physicalSectorGrade n k a :=
  orthogonalIdempotents_existsUnique_expansion _
    (physicalSectorGrade_idempotent hk n) (physicalSectorGrade_mul_eq_zero hk n)
    (physicalSectorGrade_ne_zero hk hn) _ (physicalSectorGrade_mem_span n k)
    (compressedRelationSpan_finrank_le_sectors n k) A hA

/-- The actual fixed projection is the sum of all realized physical grades. -/
theorem stochasticFixedProjection_eq_sum_physicalSectors (hk : 0 < k) (hn : k ≤ n) :
    stochasticFixedProjection n k = ∑ a : PhysicalSectorLabel k, physicalSectorGrade n k a :=
  orthogonalIdempotents_corner_unit _
    (physicalSectorGrade_idempotent hk n) (physicalSectorGrade_mul_eq_zero hk n)
    (physicalSectorGrade_ne_zero hk hn) _ (physicalSectorGrade_mem_span n k)
    (compressedRelationSpan_finrank_le_sectors n k) _
    (stochasticFixedProjection_mem_compressedRelationSpan n k)
    (fun a => compressedRelationSpan_left_support n k (physicalSectorGrade_mem_span n k a))

/-- Existence and uniqueness of coefficients, together with their actual scalar action. -/
theorem physicalSector_existsUnique_scalar_decomposition (hk : 0 < k) (hn : k ≤ n)
    (A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ)
    (hA : A ∈ compressedRelationSpan n k) :
    ∃! c : PhysicalSectorLabel k → ℝ,
      (A = ∑ a, c a • physicalSectorGrade n k a) ∧
      ∀ a, A * physicalSectorGrade n k a = c a • physicalSectorGrade n k a ∧
        physicalSectorGrade n k a * A = c a • physicalSectorGrade n k a := by
  obtain ⟨c,hc,hu⟩ := physicalSector_existsUnique_expansion hk hn A hA
  refine ⟨c,⟨hc,?_⟩,?_⟩
  · exact orthogonalIdempotents_scalar_action_of_expansion _
      (physicalSectorGrade_idempotent hk n) (physicalSectorGrade_mul_eq_zero hk n) A c hc
  · intro d hd
    exact hu d hd.1

end ExactCriticalCurve.Quantum
