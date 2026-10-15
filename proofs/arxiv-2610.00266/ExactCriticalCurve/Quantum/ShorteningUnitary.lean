import ExactCriticalCurve.Quantum.ShorteningCoordinates
import ExactCriticalCurve.Foundations.PositiveFrameSupport
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # The actual physical shortening unitary onto the free-qubit Wu code -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary
variable {m : ℕ}

/-- Tensor all binary label bijections and regroup the free physical bits. -/
def shorteningColumnEquiv (n : ℕ) (hm : Odd m) :
    ColumnConfig n m ≃ (BinaryVector n × (Fin n → CSSQuotient (wuLine (m+1)))) where
  toFun X := (fun a => (shorteningLabelEquiv hm (X a)).1,
    fun a => (shorteningLabelEquiv hm (X a)).2)
  invFun Y := fun a => (shorteningLabelEquiv hm).symm (Y.1 a, Y.2 a)
  left_inv X := by
    funext a
    exact (shorteningLabelEquiv hm).symm_apply_apply (X a)
  right_inv Y := by
    apply Prod.ext <;> funext a
    · exact congrArg Prod.fst ((shorteningLabelEquiv hm).apply_symm_apply (Y.1 a, Y.2 a))
    · exact congrArg Prod.snd ((shorteningLabelEquiv hm).apply_symm_apply (Y.1 a, Y.2 a))

/-- Identity on the free physical register tensored with the actual Wu CSS synthesis. -/
def freeWuSynthesis (n : ℕ) (m : ℕ) :
    Matrix (BinaryVector n × ColumnConfig n (m+1))
      (BinaryVector n × (Fin n → CSSQuotient (wuLine (m+1)))) ℂ :=
  (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ cssColumnSynthesis n (wuLine (m+1))

/-- The actual map of computational k-1-copy columns to normalized Wu-code columns. -/
def shorteningSynthesis (n : ℕ) (hm : Odd m) :
    Matrix (BinaryVector n × ColumnConfig n (m+1)) (ColumnConfig n m) ℂ :=
  (freeWuSynthesis n m).submatrix id (shorteningColumnEquiv n hm)

theorem shorteningSynthesis_apply (n : ℕ) (hm : Odd m)
    (b : BinaryVector n) (Y : ColumnConfig n (m+1)) (X : ColumnConfig n m) :
    shorteningSynthesis n hm (b,Y) X =
      if b = fun a => shorteningParity m (X a) then
        cssColumnSynthesis n (wuLine (m+1)) Y
          (fun a => Submodule.Quotient.mk (shorteningIotaOrth m (X a))) else 0 := by
  change (if b = (shorteningColumnEquiv n hm X).1 then (1 : ℂ) else 0) *
    cssColumnSynthesis n (wuLine (m+1)) Y (shorteningColumnEquiv n hm X).2 = _
  change (if b = (fun a => shorteningParity m (X a)) then (1 : ℂ) else 0) * _ = _
  split_ifs <;> simp_all [shorteningColumnEquiv, shorteningLabelEquiv, shorteningLabelMap]

theorem freeWuSynthesis_adjoint_mul (n : ℕ) (h4 : 4 ∣ m+1) :
    (freeWuSynthesis n m)ᴴ * freeWuSynthesis n m = 1 := by
  unfold freeWuSynthesis
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul,
    cssColumnSynthesis_adjoint_mul_self n _ (wuLine_isDefect h4), Matrix.one_kronecker_one]

theorem freeWuSynthesis_mul_adjoint (n m : ℕ) :
    freeWuSynthesis n m * (freeWuSynthesis n m)ᴴ =
      (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ cssColumnProjection n (wuLine (m+1)) := by
  unfold freeWuSynthesis
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.mul_one]
  rfl

/-- Left unitary identity on the complete physical source, including n=0. -/
theorem shorteningSynthesis_adjoint_mul (n : ℕ) (h4 : 4 ∣ m+1) :
    (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ *
      shorteningSynthesis n (shortening_predecessor_odd h4) = 1 := by
  unfold shorteningSynthesis
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, freeWuSynthesis_adjoint_mul n h4]
  ext X Y
  simp only [Matrix.submatrix_apply, Matrix.one_apply,
    (shorteningColumnEquiv n (shortening_predecessor_odd h4)).injective.eq_iff]

/-- The right unitary identity is the actual free-register CSS projector. -/
theorem shorteningSynthesis_mul_adjoint (n : ℕ) (hm : Odd m) :
    shorteningSynthesis n hm * (shorteningSynthesis n hm)ᴴ =
      (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ cssColumnProjection n (wuLine (m+1)) := by
  unfold shorteningSynthesis
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ id _ id (shorteningColumnEquiv n hm).bijective,
    Matrix.submatrix_id_id, freeWuSynthesis_mul_adjoint]

/-- The target is the actual range of I_D tensor P_u in physical coordinates. -/
def freeWuCode (n m : ℕ) :
    Submodule ℂ ((BinaryVector n × ColumnConfig n (m+1)) → ℂ) :=
  LinearMap.range
    ((1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
      cssColumnProjection n (wuLine (m+1))).mulVecLin

theorem shorteningSynthesis_range (n : ℕ) (hm : Odd m) :
    LinearMap.range (shorteningSynthesis n hm).mulVecLin = freeWuCode n m := by
  rw [← matrix_range_self_mul_conjTranspose, shorteningSynthesis_mul_adjoint]
  rfl

theorem shorteningSynthesis_injective (n : ℕ) (h4 : 4 ∣ m+1) :
    Function.Injective (shorteningSynthesis n (shortening_predecessor_odd h4)).mulVecLin := by
  intro v w h
  have hh := congrArg (fun z => (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ *ᵥ z) h
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    shorteningSynthesis_adjoint_mul n h4, Matrix.one_mulVec] using hh

/-- A genuine complex linear equivalence onto the stated physical code. -/
def shorteningUnitaryLinearEquiv (n : ℕ) (h4 : 4 ∣ m+1) :
    (ColumnConfig n m → ℂ) ≃ₗ[ℂ] freeWuCode n m :=
  (LinearEquiv.ofInjective (shorteningSynthesis n (shortening_predecessor_odd h4)).mulVecLin
    (shorteningSynthesis_injective n h4)).trans
      (LinearEquiv.ofEq _ _ (shorteningSynthesis_range n (shortening_predecessor_odd h4)))

/-- The actual linear equivalence preserves the full complex inner product. -/
theorem shorteningSynthesis_inner (n : ℕ) (h4 : 4 ∣ m+1)
    (v w : ColumnConfig n m → ℂ) :
    star (shorteningSynthesis n (shortening_predecessor_odd h4) *ᵥ v) ⬝ᵥ
      (shorteningSynthesis n (shortening_predecessor_odd h4) *ᵥ w) =
        star v ⬝ᵥ w := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    shorteningSynthesis_adjoint_mul n h4, Matrix.one_mulVec]

end ExactCriticalCurve.Quantum
