import ExactCriticalCurve.Binary.Quadratic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open scoped BigOperators ComplexOrder
open Matrix Classical

namespace ExactCriticalCurve.Quantum

open Binary

variable {k : ℕ}

/-- The actual quotient of H by the restriction of N. -/
abbrev CosetQuotient (H N : Submodule (ZMod 2) (BinaryVector k)) :=
  H ⧸ N.comap H.subtype

noncomputable instance cosetQuotientFintype
    (H N : Submodule (ZMod 2) (BinaryVector k)) : Fintype (CosetQuotient H N) :=
  Fintype.ofFinite _

/-- Membership of an ambient vector in a specified quotient coset. -/
def cosetMember (H N : Submodule (ZMod 2) (BinaryVector k))
    (x : BinaryVector k) (q : CosetQuotient H N) : Prop :=
  ∃ hx : x ∈ H, (Submodule.Quotient.mk (⟨x, hx⟩ : H) : CosetQuotient H N) = q

theorem cosetMember_iff_of_mem (H N : Submodule (ZMod 2) (BinaryVector k))
    {x : BinaryVector k} (hx : x ∈ H) (q : CosetQuotient H N) :
    cosetMember H N x q ↔ Submodule.Quotient.mk (⟨x, hx⟩ : H) = q := by
  constructor
  · rintro ⟨_, hq⟩
    exact hq
  · exact fun hq => ⟨hx, hq⟩

theorem cosetMember_mk_iff (H N : Submodule (ZMod 2) (BinaryVector k))
    (x : BinaryVector k) (y : H) :
    cosetMember H N x (Submodule.Quotient.mk y) ↔ x ∈ H ∧ x - y.val ∈ N := by
  constructor
  · rintro ⟨hx, hq⟩
    refine ⟨hx, ?_⟩
    exact (Submodule.Quotient.eq (N.comap H.subtype)).mp hq
  · rintro ⟨hx, hxy⟩
    exact ⟨hx, (Submodule.Quotient.eq (N.comap H.subtype)).mpr hxy⟩

/-- Translation by a representative is an actual bijection from N to its coset fiber. -/
def cosetFiberEquiv (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H)
    (y : H) :
    N ≃ {x : BinaryVector k // cosetMember H N x (Submodule.Quotient.mk y)} where
  toFun n := ⟨y.val + n.val, (cosetMember_mk_iff H N _ y).mpr
    ⟨H.add_mem y.property (hNH n.property), by simpa only [add_sub_cancel_left] using n.property⟩⟩
  invFun x := ⟨x.val - y.val, ((cosetMember_mk_iff H N _ y).mp x.property).2⟩
  left_inv n := by ext; simp
  right_inv x := by ext; simp

/-- Every actual coset fiber has exactly |N| elements. -/
theorem cosetFiber_card (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H)
    (q : CosetQuotient H N) :
    Nat.card {x : BinaryVector k // cosetMember H N x q} = Nat.card N := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (N.comap H.subtype) q
  exact Nat.card_congr (cosetFiberEquiv H N hNH y).symm

/-- The unnormalized indicator columns of the quotient cosets. -/
def cosetIndicator (H N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (BinaryVector k) (CosetQuotient H N) ℂ :=
  fun x q => if cosetMember H N x q then 1 else 0

/-- Equal-amplitude coset columns with the intended |N| normalization.
They are orthonormal under N ≤ H, as proved below. -/
def cosetSynthesis (H N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (BinaryVector k) (CosetQuotient H N) ℂ :=
  ((Real.sqrt (Nat.card N) : ℂ)⁻¹) • cosetIndicator H N

/-- The projection candidate is defined from its actual coset columns. -/
def cosetProjection (H N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (BinaryVector k) (BinaryVector k) ℂ :=
  cosetSynthesis H N * (cosetSynthesis H N)ᴴ

/-- The actual diagonal relation matrix, with entries zero or one. -/
def cosetRelationMatrix (H N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (BinaryVector k) (BinaryVector k) ℂ :=
  fun x y => if x ∈ H ∧ y ∈ H ∧ x - y ∈ N then 1 else 0

theorem cosetMember_unique (H N : Submodule (ZMod 2) (BinaryVector k))
    {x : BinaryVector k} {q r : CosetQuotient H N}
    (hq : cosetMember H N x q) (hr : cosetMember H N x r) : q = r := by
  obtain ⟨hx, hq⟩ := hq
  obtain ⟨_, hr⟩ := hr
  exact hq.symm.trans hr

theorem sum_cosetIndicator (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H)
    (q : CosetQuotient H N) :
    (∑ x, cosetIndicator H N x q) = (Nat.card N : ℂ) := by
  simp only [cosetIndicator, Finset.sum_boole]
  have hc := congrArg (fun c : ℕ => (c : ℂ)) (cosetFiber_card H N hNH q)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hc

/-- Actual coset fibers are disjoint and each has cardinality |N|. -/
theorem cosetIndicator_adjoint_mul_self
    (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H) :
    (cosetIndicator H N)ᴴ * cosetIndicator H N =
      (Nat.card N : ℂ) • (1 : Matrix (CosetQuotient H N) (CosetQuotient H N) ℂ) := by
  ext q r
  by_cases hqr : q = r
  · subst r
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.one_apply, ite_true, smul_eq_mul, mul_one]
    calc
      _ = ∑ x, cosetIndicator H N x q := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : cosetMember H N x q <;> simp [cosetIndicator, hx]
      _ = _ := sum_cosetIndicator H N hNH q
  · have hz : ∀ x, (starRingEnd ℂ) (cosetIndicator H N x q) * cosetIndicator H N x r = 0 := by
      intro x
      by_cases hxq : cosetMember H N x q
      · have hxr : ¬ cosetMember H N x r := fun h => hqr (cosetMember_unique H N hxq h)
        simp [cosetIndicator, hxr]
      · simp [cosetIndicator, hxq]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hz, Matrix.smul_apply, hqr]

/-- The other indicator product is exactly the relation matrix on the ambient space. -/
theorem cosetIndicator_mul_adjoint
    (H N : Submodule (ZMod 2) (BinaryVector k)) :
    cosetIndicator H N * (cosetIndicator H N)ᴴ = cosetRelationMatrix H N := by
  ext x y
  by_cases hx : x ∈ H
  · by_cases hy : y ∈ H
    · let qx : CosetQuotient H N := Submodule.Quotient.mk (⟨x, hx⟩ : H)
      have hsingle :
          (∑ q, cosetIndicator H N x q * star (cosetIndicator H N y q)) =
            cosetIndicator H N x qx * star (cosetIndicator H N y qx) := by
        apply Finset.sum_eq_single qx
        · intro q _ hq
          have hxq : ¬ cosetMember H N x q := by
            rw [cosetMember_iff_of_mem H N hx]
            exact Ne.symm hq
          simp [cosetIndicator, hxq]
        · simp
      rw [Matrix.mul_apply]
      simp only [Matrix.conjTranspose_apply]
      rw [hsingle]
      have hxm : cosetMember H N x qx := ⟨hx, rfl⟩
      have hym : cosetMember H N y qx ↔ x - y ∈ N := by
        rw [cosetMember_mk_iff, and_iff_right hy]
        constructor <;> intro h <;> simpa only [neg_sub] using N.neg_mem h
      by_cases hxy : x - y ∈ N <;>
        simp [cosetIndicator, hxm, hym, cosetRelationMatrix, hx, hy, hxy]
    · have hym : ∀ q, ¬ cosetMember H N y q := fun _ h => hy h.choose
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, cosetIndicator, hym,
        cosetRelationMatrix, hy]
  · have hxm : ∀ q, ¬ cosetMember H N x q := fun _ h => hx h.choose
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, cosetIndicator, hxm,
      cosetRelationMatrix, hx]

theorem cosetCard_ne_zero (N : Submodule (ZMod 2) (BinaryVector k)) :
    Nat.card N ≠ 0 := by
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_ne_zero

/-- The normalization factor is derived from the positive cardinality of N. -/
theorem coset_normalization (N : Submodule (ZMod 2) (BinaryVector k)) :
    ((Real.sqrt (Nat.card N) : ℂ)⁻¹ * (Real.sqrt (Nat.card N) : ℂ)⁻¹) *
      (Nat.card N : ℂ) = 1 := by
  have hc : 0 < (Nat.card N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (cosetCard_ne_zero N)
  have hs : (Real.sqrt (Nat.card N) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hc).ne'
  have hsq : (Real.sqrt (Nat.card N) : ℂ) * (Real.sqrt (Nat.card N) : ℂ) =
      (Nat.card N : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [← hsq]
  field_simp

theorem coset_amplitude_star (N : Submodule (ZMod 2) (BinaryVector k)) :
    star ((Real.sqrt (Nat.card N) : ℂ)⁻¹) = (Real.sqrt (Nat.card N) : ℂ)⁻¹ := by
  simp

/-- The actual normalized coset columns are orthonormal, proved from their fiber counts. -/
theorem cosetSynthesis_adjoint_mul_self
    (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H) :
    (cosetSynthesis H N)ᴴ * cosetSynthesis H N = 1 := by
  simp only [cosetSynthesis, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, coset_amplitude_star]
  rw [cosetIndicator_adjoint_mul_self H N hNH, smul_smul, coset_normalization, one_smul]

/-- The relation matrix equals |N| times the projection built from the actual coset columns. -/
theorem cosetRelationMatrix_eq_card_smul_projection
    (H N : Submodule (ZMod 2) (BinaryVector k)) :
    cosetRelationMatrix H N = (Nat.card N : ℂ) • cosetProjection H N := by
  simp only [cosetProjection, cosetSynthesis, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, coset_amplitude_star]
  rw [cosetIndicator_mul_adjoint H N, mul_comm (Nat.card N : ℂ),
    coset_normalization, one_smul]

theorem cosetProjection_isHermitian
    (H N : Submodule (ZMod 2) (BinaryVector k)) :
    (cosetProjection H N).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

theorem cosetProjection_posSemidef
    (H N : Submodule (ZMod 2) (BinaryVector k)) :
    (cosetProjection H N).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem cosetProjection_mul_synthesis
    (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H) :
    cosetProjection H N * cosetSynthesis H N = cosetSynthesis H N := by
  rw [cosetProjection, Matrix.mul_assoc, cosetSynthesis_adjoint_mul_self H N hNH,
    Matrix.mul_one]

theorem cosetProjection_idempotent
    (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H) :
    cosetProjection H N * cosetProjection H N = cosetProjection H N := by
  conv_lhs => rhs; unfold cosetProjection
  rw [← Matrix.mul_assoc, cosetProjection_mul_synthesis H N hNH]
  rfl

/-- Its range is exactly the span of the normalized coset columns. -/
theorem cosetProjection_range
    (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H) :
    LinearMap.range (cosetProjection H N).mulVecLin =
      Submodule.span ℂ (Set.range (cosetSynthesis H N).col) := by
  rw [← Matrix.range_mulVecLin]
  apply le_antisymm
  · rw [cosetProjection, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rintro f ⟨v, rfl⟩
    refine ⟨(cosetSynthesis H N).mulVecLin v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      cosetProjection_mul_synthesis H N hNH]

/-- The synthesis entries have exactly the stipulated coset amplitudes. -/
theorem cosetSynthesis_apply
    (H N : Submodule (ZMod 2) (BinaryVector k)) (x : BinaryVector k)
    (q : CosetQuotient H N) :
    cosetSynthesis H N x q =
      if cosetMember H N x q then (Real.sqrt (Nat.card N) : ℂ)⁻¹ else 0 := by
  by_cases h : cosetMember H N x q <;> simp [cosetSynthesis, cosetIndicator, h]

/-- The unnormalized relation has the exact scalar-idempotent normalization. -/
theorem cosetRelationMatrix_mul_self
    (H N : Submodule (ZMod 2) (BinaryVector k)) (hNH : N ≤ H) :
    cosetRelationMatrix H N * cosetRelationMatrix H N =
      (Nat.card N : ℂ) • cosetRelationMatrix H N := by
  rw [cosetRelationMatrix_eq_card_smul_projection H N]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    cosetProjection_idempotent H N hNH]

end ExactCriticalCurve.Quantum
