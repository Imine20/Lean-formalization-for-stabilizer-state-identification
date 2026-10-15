import ExactCriticalCurve.Quantum.ShorteningFiberCount
import ExactCriticalCurve.Quantum.StochasticRelationProduct

/-! # Actual relation composition under both Wu CSS projections -/
noncomputable section
open Classical
namespace ExactCriticalCurve.Binary
open StochasticCounting Quantum
variable {k : ℕ}

def shorteningWuRelation (h4 : 4 ∣ k) : StochasticLagrangian k :=
  (wuLine_isDefect h4).stochasticLagrangian

theorem shorteningWuRelation_leftDefect (h4 : 4 ∣ k) :
    (shorteningWuRelation h4).leftDefect = wuLine k := by
  ext x
  change (x ∈ orthogonal (wuLine k) ∧ (0 : BinaryVector k) ∈ orthogonal (wuLine k) ∧
    x - 0 ∈ wuLine k) ↔ x ∈ wuLine k
  simp only [sub_zero]
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨(wuLine_isDefect h4).le_orthogonal h,(orthogonal (wuLine k)).zero_mem,h⟩

theorem shorteningWuRelation_rightDefect (h4 : 4 ∣ k) :
    (shorteningWuRelation h4).rightDefect = wuLine k := by
  ext x
  change ((0 : BinaryVector k) ∈ orthogonal (wuLine k) ∧ x ∈ orthogonal (wuLine k) ∧
    0 - x ∈ wuLine k) ↔ x ∈ wuLine k
  simp only [zero_sub,Submodule.neg_mem_iff]
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨(orthogonal (wuLine k)).zero_mem,(wuLine_isDefect h4).le_orthogonal h,h⟩

theorem shorteningEvenPart_coordinates (T : StochasticLagrangian k)
    {p : RelationSpace k} (hp : p ∈ shorteningEvenPart T) :
    p.1 ∈ orthogonal (wuLine k) ∧ p.2 ∈ orthogonal (wuLine k) := by
  have h1 : binaryDot (allOnes k) p.1 = 0 := by
    have h := hp.2
    change binaryDot (allOnes k) p.1 + binaryDot 0 p.2 = 0 at h
    simpa [binaryDot] using h
  have hb := relationQuadratic_zero_pairwise T.quadratic_zero T.allOnes_mem hp.1
  change binaryDot (allOnes k) p.1 + binaryDot (allOnes k) p.2 = 0 at hb
  rw [h1,zero_add] at hb
  have ho {x : BinaryVector k} (hx : binaryDot (allOnes k) x = 0) :
      x ∈ orthogonal (wuLine k) := by
    intro z hz
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
    change (binaryDotForm k (c • allOnes k)) x = 0
    rw [map_smul,LinearMap.smul_apply,binaryDotForm_apply,hx,smul_zero]
  exact ⟨ho h1,ho hb⟩

theorem shorteningWuComposition_eq_saturation (hk : 0 < k) (h4 : 4 ∣ k)
    (T : StochasticLagrangian k) :
    (stochasticLagrangianComposition
      (stochasticLagrangianComposition (shorteningWuRelation h4) T)
      (shorteningWuRelation h4)).carrier = shorteningSaturationCarrier T := by
  let W := shorteningWuRelation h4
  let V := stochasticLagrangianComposition W T
  have hw : allOnes k ∈ orthogonal (wuLine k) :=
    (wuLine_isDefect h4).le_orthogonal (allOnes_mem_wuLine k)
  have hzero : (0 : BinaryVector k) ∈ orthogonal (wuLine k) := (orthogonal _).zero_mem
  have hle : shorteningSaturationCarrier T ≤ (stochasticLagrangianComposition V W).carrier := by
    apply sup_le
    · intro p hp
      have hc := shorteningEvenPart_coordinates T hp
      apply (mem_relationComposition V W p.1 p.2).mpr
      refine ⟨p.2,?_,?_⟩
      · apply (mem_relationComposition W T p.1 p.2).mpr
        exact ⟨p.1,⟨hc.1,hc.1,by simp⟩,hp.1⟩
      · exact ⟨hc.2,hc.2,by simp⟩
    · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
      apply (mem_relationComposition V W (allOnes k) 0).mpr
      refine ⟨0,?_,?_⟩
      · apply (mem_relationComposition W T (allOnes k) 0).mpr
        exact ⟨0,⟨hw,hzero,by simpa using allOnes_mem_wuLine k⟩,T.carrier.zero_mem⟩
      · exact ⟨hzero,hzero,by simp⟩
  exact (Submodule.eq_of_le_of_finrank_eq hle
    ((shorteningSaturationCarrier_finrank hk T).trans
      (stochasticLagrangianComposition V W).finrank_eq.symm)).symm

theorem shorteningWuComposition_rightWu (h4 : 4 ∣ k) (T : StochasticLagrangian k) :
    allOnes k ∈ (stochasticLagrangianComposition (shorteningWuRelation h4) T).rightDefect := by
  apply (mem_relationComposition (shorteningWuRelation h4) T 0 (allOnes k)).mpr
  refine ⟨allOnes k,?_,T.allOnes_mem⟩
  exact ⟨(orthogonal _).zero_mem,
    (wuLine_isDefect h4).le_orthogonal (allOnes_mem_wuLine k),by
      simpa using (wuLine k).neg_mem (allOnes_mem_wuLine k)⟩

theorem shorteningWu_firstRank (hk : 0 < k) (h4 : 4 ∣ k)
    (T : StochasticLagrangian k) :
    Module.finrank (ZMod 2) ↥((shorteningWuRelation h4).rightDefect ⊓ T.leftDefect) =
      if shorteningLeftWu k ∈ T.carrier then 1 else 0 := by
  rw [shorteningWuRelation_rightDefect]
  by_cases hT : shorteningLeftWu k ∈ T.carrier
  · rw [if_pos hT,inf_eq_left.mpr]
    · exact finrank_span_singleton (allOnes_ne_zero hk)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hT
  · rw [if_neg hT]
    have hd : Disjoint T.leftDefect (wuLine k) :=
      Submodule.disjoint_span_singleton_of_notMem hT
    rw [hd.symm.eq_bot,finrank_bot]

theorem shorteningWu_secondRank (hk : 0 < k) (h4 : 4 ∣ k)
    (T : StochasticLagrangian k) :
    Module.finrank (ZMod 2)
      ↥((stochasticLagrangianComposition (shorteningWuRelation h4) T).rightDefect ⊓
        (shorteningWuRelation h4).leftDefect) = 1 := by
  rw [shorteningWuRelation_leftDefect,inf_eq_right.mpr]
  · exact finrank_span_singleton (allOnes_ne_zero hk)
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (shorteningWuComposition_rightWu h4 T)

end ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- Exact physical compression before dividing by the two Wu normalizations. -/
theorem shorteningWu_relationOperator_product (n : ℕ) (hk : 0 < k) (h4 : 4 ∣ k)
    (T : StochasticLagrangian k) :
    relationOperator n (shorteningWuRelation h4).carrier *
      relationOperator n T.carrier * relationOperator n (shorteningWuRelation h4).carrier =
      (((2 : ℂ)^n) ^ (if shorteningLeftWu k ∈ T.carrier then 1 else 0) * (2 : ℂ)^n) •
        relationOperator n (shorteningSaturationCarrier T) := by
  rw [relationOperator_mul,Matrix.smul_mul,relationOperator_mul,smul_smul,
    shorteningWu_firstRank hk h4 T,shorteningWu_secondRank hk h4 T,pow_one,
    shorteningWuComposition_eq_saturation hk h4 T]


/-- After removing one Wu normalization, closed and transverse factors are D and 1. -/
theorem shorteningWu_compression_scaled (n : ℕ) (hk : 0 < k) (h4 : 4 ∣ k)
    (T : StochasticLagrangian k) :
    ((2 : ℂ)^n) • (cssColumnProjection n (wuLine k) * relationOperator n T.carrier *
      cssColumnProjection n (wuLine k)) =
      (if shorteningLeftWu k ∈ T.carrier then (2 : ℂ)^n else 1) •
        relationOperator n (shorteningSaturationCarrier T) := by
  have hW : relationOperator n (shorteningWuRelation h4).carrier =
      ((2 : ℂ)^n) • cssColumnProjection n (wuLine k) := by
    change relationOperator n (defectRelation (wuLine k)) = _
    have hN : Module.finrank (ZMod 2) (wuLine k) = 1 :=
      finrank_span_singleton (allOnes_ne_zero hk)
    rw [relationOperator_defectRelation,hN,pow_one]
  have h := shorteningWu_relationOperator_product n hk h4 T
  simp only [hW,Matrix.smul_mul,Matrix.mul_smul,smul_smul] at h
  have hn : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have he := congrArg (fun A => ((2 : ℂ)^n)⁻¹ • A) h
  simp only [smul_smul] at he
  have hc : ((2 : ℂ)^n)⁻¹ * ((2 : ℂ)^n * (2 : ℂ)^n) = (2 : ℂ)^n := by
    field_simp
  rw [hc] at he
  by_cases hT : shorteningLeftWu k ∈ T.carrier
  · simpa only [if_pos hT,pow_one,hc] using he
  · simpa only [if_neg hT,pow_zero,one_mul,inv_mul_cancel₀ hn,one_smul] using he

end ExactCriticalCurve.Quantum

