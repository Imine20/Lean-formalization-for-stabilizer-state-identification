import ExactCriticalCurve.Quantum.ShorteningFixedSupport
import ExactCriticalCurve.Quantum.ShorteningFreeRegister

/-! # Ordinary to exceptional transport of the actual fixed CSS filtrations -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum
open Binary

theorem shortening_commuting_projection_range {ι : Type*} [Fintype ι]
    (P Q : Matrix ι ι ℂ) (hP : P*P=P) (hQ : Q*Q=Q) (hPQ : P*Q=Q*P) :
    LinearMap.range (P*Q).mulVecLin = LinearMap.range P.mulVecLin ⊓ LinearMap.range Q.mulVecLin := by
  ext v
  constructor
  · rintro ⟨x,rfl⟩
    constructor
    · exact ⟨Q*ᵥ x,by simp only [Matrix.mulVecLin_apply,Matrix.mulVec_mulVec]⟩
    · exact ⟨P*ᵥ x,by simp only [Matrix.mulVecLin_apply,Matrix.mulVec_mulVec,hPQ]⟩
  · rintro ⟨hp,hq⟩
    refine ⟨v,?_⟩
    change (P*Q)*ᵥ v=v
    rw [← Matrix.mulVec_mulVec,(matrixProjection_mem_range_iff Q hQ v).mp hq,
      (matrixProjection_mem_range_iff P hP v).mp hp]

theorem shortening_exceptional_filtration_le_wu (n k r : ℕ) (h4 : 4 ∣ k) :
    exceptionalCSSFiltration n k r ≤ LinearMap.range (cssColumnProjection n (wuLine k)).mulVecLin := by
  apply iSup_le
  intro N
  exact cssCode_antitone n _ N.val (wuLine_isDefect h4) N.property.1
    (Submodule.span_le.mpr (by
      intro x hx
      have he : x=allOnes k := Set.mem_singleton_iff.mp hx
      simpa [he] using N.property.2.2))

/-- The real fixed part of every filtration step is transported, including empty steps. -/
theorem shortening_fixedCSSFiltration_map (n r : ℕ) {m : ℕ} (h4 : 4 ∣ m+1) :
    (LinearMap.range (ordinaryFixedCSSProjection n m r).mulVecLin).map
      (shorteningSynthesis n (shortening_predecessor_odd h4)).mulVecLin =
    freeRegisterSpace (BinaryVector n)
      (LinearMap.range (exceptionalFixedCSSProjection n (m+1) (r+1)).mulVecLin) := by
  rw [ordinaryFixedCSSProjection_range,
    Submodule.map_inf _ (shorteningSynthesis_injective n h4),shortening_ordinaryCSSFiltration_map n r h4]
  rw [← shortening_projection_compression_range _ _ (stochasticFixedProjection_isHermitian n m)
    (stochasticFixedProjection_idempotent n m),shorteningSynthesis_fixed n h4,
    ← freeRegisterSpace_range,← freeRegisterSpace_inf]
  rw [shortening_commuting_projection_range _ _
    (cssColumnProjection_idempotent n _ (wuLine_isDefect h4))
    (stochasticFixedProjection_idempotent n (m+1))
    (stochasticFixedProjection_wu_commute n (m+1)).symm]
  rw [← inf_assoc,inf_eq_left.mpr (shortening_exceptional_filtration_le_wu n (m+1) (r+1) h4),
    exceptionalFixedCSSProjection_range]

/-- Equality of the actual orthogonal projections, not only an abstract dimension match. -/
theorem shorteningSynthesis_fixedCSSProjection (n r : ℕ) {m : ℕ} (h4 : 4 ∣ m+1) :
    shorteningSynthesis n (shortening_predecessor_odd h4) * ordinaryFixedCSSProjection n m r *
      (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ =
      (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
        exceptionalFixedCSSProjection n (m+1) (r+1) := by
  let U := shorteningSynthesis n (shortening_predecessor_odd h4)
  let P := ordinaryFixedCSSProjection n m r
  let Q := exceptionalFixedCSSProjection n (m+1) (r+1)
  have hU : Uᴴ*U=1 := shorteningSynthesis_adjoint_mul n h4
  have hP : P*P=P := ordinaryFixedCSSProjection_idempotent n m r
  have hQ : Q*Q=Q := exceptionalFixedCSSProjection_idempotent n (m+1) (r+1)
  apply shortening_projection_eq_of_range_eq
  · exact (ordinaryFixedCSSProjection_posSemidef n m r).mul_mul_conjTranspose_same U |>.isHermitian
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
      (exceptionalFixedCSSProjection_isHermitian n (m+1) (r+1)).eq]
  · change (U*P*Uᴴ)*(U*P*Uᴴ)=U*P*Uᴴ
    calc
      _ = U*P*(Uᴴ*U)*P*Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U*(P*P)*Uᴴ := by rw [hU,Matrix.mul_one];simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]
  · rw [← Matrix.mul_kronecker_mul,Matrix.one_mul,exceptionalFixedCSSProjection_idempotent]
  · rw [shortening_projection_compression_range _ _ (ordinaryFixedCSSProjection_isHermitian n m r)
      (ordinaryFixedCSSProjection_idempotent n m r),shortening_fixedCSSFiltration_map n r h4,
      freeRegisterSpace_range]

end ExactCriticalCurve.Quantum
