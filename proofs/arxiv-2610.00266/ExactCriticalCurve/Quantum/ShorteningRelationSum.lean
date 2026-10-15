import ExactCriticalCurve.Quantum.ShorteningRelationOperator
import ExactCriticalCurve.Quantum.StochasticIsometry

/-! # The actual shortening identity for the complete relation-operator sum -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary
variable {m : ℕ}
set_option maxHeartbeats 1000000

/-- Every actual relation has its own proved closed/transverse compression factor. -/
theorem shorteningSynthesis_compressed_relation (n : ℕ) (h4 : 4 ∣ m+1)
    (T : StochasticLagrangian (m+1)) :
    (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
      (cssColumnProjection n (wuLine (m+1)) * relationOperator n T.carrier *
        cssColumnProjection n (wuLine (m+1))) =
    (if shorteningLeftWu (m+1) ∈ T.carrier then (2 : ℂ)^n else 1) •
      (shorteningSynthesis n (shortening_predecessor_odd h4) *
        relationOperator n (shorteningRelation h4 T).carrier *
          (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ) := by
  have hc := shorteningSynthesis_relation n h4 (shorteningRelation h4 T)
  rw [shorteningClosedLift_shorteningRelation] at hc
  have h := congrArg (fun A => (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ A)
    (shorteningWu_compression_scaled n (by omega) h4 T)
  dsimp only at h
  simp only [Matrix.kronecker_smul] at h
  change ((2 : ℂ)^n) • _ =
    (if shorteningLeftWu (m+1) ∈ T.carrier then (2 : ℂ)^n else 1) •
      ((1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
        relationOperator n (shorteningSaturation (by omega) h4 T).carrier) at h
  rw [← hc,smul_smul] at h
  have hn : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have he := congrArg (fun A => ((2 : ℂ)^n)⁻¹ • A) h
  simp only [smul_smul,inv_mul_cancel₀ hn,one_smul] at he
  have hs (a : ℂ) : ((2 : ℂ)^n)⁻¹ * (a * (2 : ℂ)^n) = a := by field_simp
  rw [hs] at he
  exact he

/-- Weighted cardinality uses the unique closed member inside the complete actual fiber. -/
theorem shorteningFiber_weight (n : ℕ) (h4 : 4 ∣ m+1) (S : StochasticLagrangian m) :
    (∑ T : {T : StochasticLagrangian (m+1) // shorteningRelation h4 T = S},
      if shorteningLeftWu (m+1) ∈ T.val.carrier then (2 : ℂ)^n else 1) =
      (2 : ℂ)^n + (2 : ℂ)^((m+1)-2) := by
  let c : {T : StochasticLagrangian (m+1) // shorteningRelation h4 T = S} :=
    ⟨shorteningClosedLift h4 S,shorteningRelation_closedLift h4 S⟩
  have he (T : {T : StochasticLagrangian (m+1) // shorteningRelation h4 T = S}) :
      (if shorteningLeftWu (m+1) ∈ T.val.carrier then (2 : ℂ)^n else 1) =
        1 + if T = c then (2 : ℂ)^n - 1 else 0 := by
    by_cases ht : T = c
    · subst T
      have hw : shorteningLeftWu (m+1) ∈ c.val.carrier :=
        shorteningClosedCarrier_leftWu S.carrier
      simp [hw,add_sub_cancel_left]
    · have hw : shorteningLeftWu (m+1) ∉ T.val.carrier := by
        intro hw
        apply ht
        apply Subtype.ext
        exact shorteningRelation_closed_unique h4 T.val S T.property hw
      simp [hw,ht]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    nsmul_eq_mul,mul_one,← Nat.card_eq_fintype_card,shorteningFullFiber_card]
  push_cast
  ring

/-- Complete actual operator identity. The coefficient follows individual fibers,
actual coset normalization and actual relation multiplication. -/
theorem shortening_relationSum (n : ℕ) (h4 : 4 ∣ m+1) :
    (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
      (cssColumnProjection n (wuLine (m+1)) * stochasticRelationSum n (m+1) *
        cssColumnProjection n (wuLine (m+1))) =
    ((2 : ℂ)^n + (2 : ℂ)^((m+1)-2)) •
      (shorteningSynthesis n (shortening_predecessor_odd h4) *
        stochasticRelationSum n m *
          (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ) := by
  rw [stochasticRelationSum,Finset.mul_sum,Finset.sum_mul]
  have hsum : (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
      (∑ T : StochasticLagrangian (m+1), cssColumnProjection n (wuLine (m+1)) *
        relationOperator n T.carrier * cssColumnProjection n (wuLine (m+1))) =
      ∑ T : StochasticLagrangian (m+1),
        (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
          (cssColumnProjection n (wuLine (m+1)) * relationOperator n T.carrier *
            cssColumnProjection n (wuLine (m+1))) := by
    ext x y
    simp only [Matrix.kroneckerMap_apply,Matrix.sum_apply,Finset.mul_sum]
  rw [hsum]
  simp_rw [shorteningSynthesis_compressed_relation n h4]
  rw [← Fintype.sum_fiberwise (shorteningRelation h4)
    (fun T => (if shorteningLeftWu (m+1) ∈ T.carrier then (2 : ℂ)^n else 1) •
      (shorteningSynthesis n (shortening_predecessor_odd h4) *
        relationOperator n (shorteningRelation h4 T).carrier *
          (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ))]
  calc
    _ = ∑ S : StochasticLagrangian m,
        ((2 : ℂ)^n + (2 : ℂ)^((m+1)-2)) •
          (shorteningSynthesis n (shortening_predecessor_odd h4) *
            relationOperator n S.carrier *
              (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ) := by
      apply Finset.sum_congr rfl
      intro S _
      have he := fun (T : {T : StochasticLagrangian (m+1) // shorteningRelation h4 T = S}) =>
        T.property
      simp_rw [he]
      rw [← Finset.sum_smul,shorteningFiber_weight n h4 S]
    _ = _ := by
      rw [← Finset.smul_sum]
      simp only [stochasticRelationSum,Matrix.mul_sum,Matrix.sum_mul]

end ExactCriticalCurve.Quantum

