import ExactCriticalCurve.Quantum.CSS
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Products of projections for orthogonal disjoint binary defects

The relation product is proved by existence and uniqueness of an actual
intermediate binary vector. Cardinalities come from actual subspace dimensions.
All dimensions and tensor degrees may be zero.
-/

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Classical

namespace ExactCriticalCurve.Binary

variable {k : ℕ} {U N : Submodule (ZMod 2) (BinaryVector k)}

theorem orthogonal_le_comm (hUN : U ≤ orthogonal N) : N ≤ orthogonal U := by
  intro n hn u hu
  change binaryDot u n = 0
  rw [binaryDot_comm]
  exact hUN hu n hn

theorem mem_orthogonal_sup_iff (U N : Submodule (ZMod 2) (BinaryVector k))
    (x : BinaryVector k) :
    x ∈ orthogonal (U ⊔ N) ↔ x ∈ orthogonal U ∧ x ∈ orthogonal N := by
  constructor
  · intro hx
    exact ⟨fun u hu => hx u ((show U ≤ U ⊔ N from le_sup_left) hu), fun n hn => hx n ((show N ≤ U ⊔ N from le_sup_right) hn)⟩
  · rintro ⟨hU, hN⟩ z hz
    obtain ⟨u, hu, n, hn, rfl⟩ := Submodule.mem_sup.mp hz
    change binaryDot (u + n) x = 0
    have h := congrArg (fun f => f x) ((binaryDotForm k).map_add u n)
    change binaryDot (u + n) x = binaryDot u x + binaryDot n x at h
    have hu0 : binaryDot u x = 0 := hU u hu
    have hn0 : binaryDot n x = 0 := hN n hn
    rw [h, hu0, hn0, zero_add]

/-- Orthogonal mod-four defects have a mod-four-isotropic sum. -/
theorem IsDefect.sup_of_orthogonal (hU : IsDefect U) (hN : IsDefect N)
    (hUN : U ≤ orthogonal N) : IsDefect (U ⊔ N) := by
  intro x hx
  obtain ⟨u, hu, n, hn, rfl⟩ := Submodule.mem_sup.mp hx
  have hzero : binaryDot n u = 0 := hUN hu n hn
  rw [weightQuadratic_add, hU u hu, hN n hn,
    binaryDot_comm u n, hzero, bitLift_zero]
  simp

/-- Existence of a middle point is precisely membership in the sum relation. -/
theorem defectRelation_comp_iff (hU : IsDefect U) (hN : IsDefect N)
    (hUN : U ≤ orthogonal N) (x y : BinaryVector k) :
    (∃ z, (x, z) ∈ defectRelation U ∧ (z, y) ∈ defectRelation N) ↔
      (x, y) ∈ defectRelation (U ⊔ N) := by
  have hNU : N ≤ orthogonal U := orthogonal_le_comm hUN
  constructor
  · rintro ⟨z, hxz, hzy⟩
    rcases (mem_defectRelation U (x, z)).mp hxz with ⟨hxU, hzU, hxu⟩
    rcases (mem_defectRelation N (z, y)).mp hzy with ⟨hzN, hyN, hny⟩
    have hxN : x ∈ orthogonal N := by
      have h := (orthogonal N).add_mem (hUN hxu) hzN
      simpa only [sub_add_cancel] using h
    have hyU : y ∈ orthogonal U := by
      have h := (orthogonal U).sub_mem hzU (hNU hny)
      simpa only [sub_sub_cancel] using h
    refine (mem_defectRelation (U ⊔ N) (x, y)).mpr ⟨?_, ?_, ?_⟩
    · exact (mem_orthogonal_sup_iff U N x).mpr ⟨hxU, hxN⟩
    · exact (mem_orthogonal_sup_iff U N y).mpr ⟨hyU, hyN⟩
    · exact Submodule.mem_sup.mpr ⟨x - z, hxu, z - y, hny, by abel⟩
  · intro hxy
    rcases (mem_defectRelation (U ⊔ N) (x, y)).mp hxy with ⟨hx, hy, hxy⟩
    rcases (mem_orthogonal_sup_iff U N x).mp hx with ⟨hxU, hxN⟩
    rcases (mem_orthogonal_sup_iff U N y).mp hy with ⟨hyU, hyN⟩
    obtain ⟨u, hu, n, hn, heq⟩ := Submodule.mem_sup.mp hxy
    refine ⟨x - u, ?_, ?_⟩
    · exact ⟨hxU, (orthogonal U).sub_mem hxU (hU.le_orthogonal hu), by simpa⟩
    · have hd : x - u - y = n := by
        calc
          x - u - y = (x - y) - u := by abel
          _ = n := by rw [← heq]; abel
      have hzN : x - u ∈ orthogonal N := by
        have hh : x - u - y ∈ orthogonal N := by
          rw [hd]
          exact hN.le_orthogonal hn
        simpa only [sub_add_cancel] using (orthogonal N).add_mem hh hyN
      refine ⟨hzN, hyN, ?_⟩
      change x - u - y ∈ N
      simpa only [hd] using hn

/-- Disjointness gives at most one actual intermediate vector. -/
theorem defectRelation_middle_unique (hDis : Disjoint U N)
    {x y z w : BinaryVector k}
    (hxz : (x, z) ∈ defectRelation U) (hzy : (z, y) ∈ defectRelation N)
    (hxw : (x, w) ∈ defectRelation U) (hwy : (w, y) ∈ defectRelation N) : z = w := by
  have hU : z - w ∈ U := by
    have h := U.sub_mem hxw.2.2 hxz.2.2
    change (x - w) - (x - z) ∈ U at h
    convert h using 1
    abel
  have hN : z - w ∈ N := by
    have h := N.sub_mem hzy.2.2 hwy.2.2
    change (z - y) - (w - y) ∈ N at h
    convert h using 1
    abel
  exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hDis) _ hU hN)

end ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum
open Binary

variable {k : ℕ}

/-- Count the actual elements of a disjoint binary subspace sum. -/
theorem cssSubspace_card_sup (U N : Submodule (ZMod 2) (BinaryVector k))
    (hDis : Disjoint U N) : Nat.card (U ⊔ N : Submodule (ZMod 2) (BinaryVector k)) =
      Nat.card U * Nat.card N := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq U N
  rw [hDis.eq_bot, finrank_bot, add_zero] at hd
  rw [cssSubspace_card, cssSubspace_card, cssSubspace_card, hd, pow_add]

/-- Orthogonal disjoint defects compose through exactly one intermediate vector. -/
theorem relationMatrix_defectRelation_mul
    (U N : Submodule (ZMod 2) (BinaryVector k))
    (hU : IsDefect U) (hN : IsDefect N) (hUN : U ≤ orthogonal N)
    (hDis : Disjoint U N) :
    relationMatrix (defectRelation U) * relationMatrix (defectRelation N) =
      relationMatrix (defectRelation (U ⊔ N)) := by
  ext x y
  rw [Matrix.mul_apply]
  by_cases hxy : (x, y) ∈ defectRelation (U ⊔ N)
  · obtain ⟨z, hxz, hzy⟩ := (defectRelation_comp_iff hU hN hUN x y).mpr hxy
    rw [Finset.sum_eq_single z]
    · simp [relationMatrix, hxz, hzy, hxy]
    · intro w _ hw
      by_cases hxw : (x, w) ∈ defectRelation U
      · by_cases hwy : (w, y) ∈ defectRelation N
        · exact False.elim (hw (defectRelation_middle_unique hDis hxw hwy hxz hzy))
        · simp [relationMatrix, hwy]
      · simp [relationMatrix, hxw]
    · simp
  · have hn : ∀ z, ¬ ((x, z) ∈ defectRelation U ∧ (z, y) ∈ defectRelation N) := by
      intro z hz
      exact hxy ((defectRelation_comp_iff hU hN hUN x y).mp ⟨z, hz⟩)
    have hz : ∀ z, relationMatrix (defectRelation U) x z *
        relationMatrix (defectRelation N) z y = 0 := by
      intro z
      by_cases h : (x, z) ∈ defectRelation U
      · have h' : (z, y) ∉ defectRelation N := fun hh => hn z ⟨h, hh⟩
        simp [relationMatrix, h']
      · simp [relationMatrix, h]
    rw [Finset.sum_eq_zero (fun z _ => hz z)]
    simp only [relationMatrix, if_neg hxy]

/-- Cancel the proved cardinality normalization in the one-column relation product. -/
theorem cosetProjection_orthogonal_mul
    (U N : Submodule (ZMod 2) (BinaryVector k))
    (hU : IsDefect U) (hN : IsDefect N) (hUN : U ≤ orthogonal N)
    (hDis : Disjoint U N) :
    cosetProjection (orthogonal U) U * cosetProjection (orthogonal N) N =
      cosetProjection (orthogonal (U ⊔ N)) (U ⊔ N) := by
  have h := relationMatrix_defectRelation_mul U N hU hN hUN hDis
  simp only [relationMatrix_defectRelation,
    cosetRelationMatrix_eq_card_smul_projection, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul] at h
  have hc : (Nat.card (U ⊔ N : Submodule (ZMod 2) (BinaryVector k)) : ℂ) =
      (Nat.card U : ℂ) * (Nat.card N : ℂ) := by
    exact_mod_cast cssSubspace_card_sup U N hDis
  rw [hc, mul_comm (Nat.card N : ℂ) (Nat.card U : ℂ)] at h
  have hu0 : (Nat.card U : ℂ) ≠ 0 := by exact_mod_cast cosetCard_ne_zero U
  have hn0 : (Nat.card N : ℂ) ≠ 0 := by exact_mod_cast cosetCard_ne_zero N
  ext x y
  apply mul_left_cancel₀ (mul_ne_zero hu0 hn0)
  exact congrArg (fun M : Matrix (BinaryVector k) (BinaryVector k) ℂ => M x y) h

/-- Actual CSS projections multiply to the projection of the orthogonal disjoint sum. -/
theorem cssColumnProjection_mul (n : ℕ)
    (U N : Submodule (ZMod 2) (BinaryVector k))
    (hU : IsDefect U) (hN : IsDefect N) (hUN : U ≤ orthogonal N)
    (hDis : Disjoint U N) :
    cssColumnProjection n U * cssColumnProjection n N =
      cssColumnProjection n (U ⊔ N) := by
  simp only [cssColumnProjection_eq_tensorPower]
  rw [← matrixTensorPower_mul, cosetProjection_orthogonal_mul U N hU hN hUN hDis]

end ExactCriticalCurve.Quantum
