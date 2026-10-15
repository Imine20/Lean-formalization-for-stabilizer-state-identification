import ExactCriticalCurve.Quantum.ShorteningFixedGrades
import ExactCriticalCurve.Quantum.CSSGammaScalar

/-! # Genuine exceptional scalar transfer from the proved ordinary scalar -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum
open Binary

theorem shortening_freeRegister_injective {α β : Type*} [Nonempty α] [DecidableEq α]
    (A B : Matrix β β ℂ)
    (h : (1 : Matrix α α ℂ) ⊗ₖ A = (1 : Matrix α α ℂ) ⊗ₖ B) : A=B := by
  let a : α := Classical.choice inferInstance
  ext x y
  have hh := congrArg (fun M : Matrix (α × β) (α × β) ℂ => M (a,x) (a,y)) h
  simpa [Matrix.kroneckerMap_apply,Matrix.one_apply] using hh

theorem shortening_wu_compression_grade (n k r : ℕ) (h4 : 4 ∣ k) :
    (cssColumnProjection n (wuLine k)*stochasticRelationSum n k*cssColumnProjection n (wuLine k)) *
      exceptionalCSSGrade n k r = stochasticRelationSum n k * exceptionalCSSGrade n k r := by
  let W := cssColumnProjection n (wuLine k)
  let A := stochasticRelationSum n k
  let E := exceptionalCSSGrade n k r
  have hWE : W*E=E := by
    simp only [W,E,exceptionalCSSGrade,Matrix.mul_sub,wu_mul_exceptionalFixedCSSProjection h4]
  have hAE : A*E=E*A := (compressedRelationSpan_commute n k
    (stochasticRelationSum_mem_compressedRelationSpan n k)
    (exceptionalFixedCSSProjection_sub_mem_compressedRelationSpan n k r (r+1))).eq
  change (W*A*W)*E=A*E
  calc
    _ = W*A*(W*E) := Matrix.mul_assoc _ _ _
    _ = W*(A*E) := by rw [hWE,Matrix.mul_assoc]
    _ = W*(E*A) := by rw [hAE]
    _ = (W*E)*A := (Matrix.mul_assoc _ _ _).symm
    _ = E*A := by rw [hWE]
    _ = A*E := hAE.symm

/-- An actual eigenvalue identity transports along the proved physical matrices. -/
theorem shortening_exceptional_scalar_of_ordinary (n r : ℕ) {m : ℕ} (h4 : 4 ∣ m+1)
    (c : ℂ) (hc : stochasticRelationSum n m * ordinaryCSSGrade n m r = c • ordinaryCSSGrade n m r) :
    stochasticRelationSum n (m+1) * exceptionalCSSGrade n (m+1) (r+1) =
      (((2 : ℂ)^n+(2 : ℂ)^((m+1)-2))*c) • exceptionalCSSGrade n (m+1) (r+1) := by
  let U := shorteningSynthesis n (shortening_predecessor_odd h4)
  let A := stochasticRelationSum n m
  let P := ordinaryCSSGrade n m r
  let E := exceptionalCSSGrade n (m+1) (r+1)
  let f : ℂ := (2 : ℂ)^n+(2 : ℂ)^((m+1)-2)
  have hU : Uᴴ*U=1 := shorteningSynthesis_adjoint_mul n h4
  have hgrade : U*P*Uᴴ=(1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ E :=
    shorteningSynthesis_grade n r h4
  apply shortening_freeRegister_injective (α := BinaryVector n)
  calc
    _ = ((1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
        (cssColumnProjection n (wuLine (m+1))*stochasticRelationSum n (m+1)*cssColumnProjection n (wuLine (m+1)))) *
          (1 ⊗ₖ E) := by
      rw [← Matrix.mul_kronecker_mul,Matrix.one_mul,shortening_wu_compression_grade n (m+1) (r+1) h4]
    _ = (f • (U*A*Uᴴ))*(U*P*Uᴴ) := by rw [shortening_relationSum n h4,← hgrade]
    _ = f • (U*(A*P)*Uᴴ) := by
      rw [Matrix.smul_mul]
      congr 1
      calc
        _ = U*A*(Uᴴ*U)*P*Uᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU,Matrix.mul_one];simp only [Matrix.mul_assoc]
    _ = (f*c) • (1 ⊗ₖ E) := by
      change f • (U*(stochasticRelationSum n m*ordinaryCSSGrade n m r)*Uᴴ)=_
      rw [hc,Matrix.mul_smul,Matrix.smul_mul,smul_smul,hgrade]
    _ = _ := by rw [Matrix.kronecker_smul]

end ExactCriticalCurve.Quantum
