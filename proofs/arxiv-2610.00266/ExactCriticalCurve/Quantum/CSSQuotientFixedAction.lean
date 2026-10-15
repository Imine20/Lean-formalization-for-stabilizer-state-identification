import ExactCriticalCurve.Quantum.DefectStabilizerFactorization
import ExactCriticalCurve.Quantum.FixedCSSFiltration
import ExactCriticalCurve.Quantum.StochasticCompressedRelations

/-! Actual quotient permutation action and the averaged CSS synthesis map.
No injectivity or dimension equality is assumed here. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
set_option maxHeartbeats 2000000
variable {n k r : ℕ}

def cssQuotientHomPerm (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (g : CSSQuotientIsometryGroup N hN) :
    Equiv.Perm (CSSHom n N) where
  toFun f := g.val.toLinearMap.comp f
  invFun f := g.val.symm.toLinearMap.comp f
  left_inv f := by apply LinearMap.ext; intro x; exact g.val.symm_apply_apply (f x)
  right_inv f := by apply LinearMap.ext; intro x; exact g.val.apply_symm_apply (f x)

def cssQuotientIsometryMatrix (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (g : CSSQuotientIsometryGroup N hN) :
    Matrix (CSSHom n N) (CSSHom n N) ℂ :=
  (cssQuotientHomPerm n N hN g).symm.toPEquiv.toMatrix

theorem cssQuotientIsometryMatrix_mul (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : CSSQuotientIsometryGroup N hN) {ι : Type*} (M : Matrix (CSSHom n N) ι ℂ) :
    cssQuotientIsometryMatrix n N hN g * M =
      M.submatrix (cssQuotientHomPerm n N hN g).symm id :=
  PEquiv.toMatrix_toPEquiv_mul _ _

def cssQuotientIsometryRepresentation (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    CSSQuotientIsometryGroup N hN →*
      unitary (Matrix (CSSHom n N) (CSSHom n N) ℂ) where
  toFun g := ⟨cssQuotientIsometryMatrix n N hN g, by
    rw [Matrix.mem_unitaryGroup_iff']
    change (cssQuotientIsometryMatrix n N hN g)ᴴ *
      cssQuotientIsometryMatrix n N hN g = 1
    rw [cssQuotientIsometryMatrix, Matrix.conjTranspose_permMatrix,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.toMatrix_toPEquiv_eq]
    ext x y
    change (1 : Matrix (CSSHom n N) (CSSHom n N) ℂ)
      ((cssQuotientHomPerm n N hN g).symm ((cssQuotientHomPerm n N hN g) x)) y = _
    rw [Equiv.symm_apply_apply]⟩
  map_one' := by
    apply Subtype.ext
    change cssQuotientIsometryMatrix n N hN 1 = 1
    rw [cssQuotientIsometryMatrix, PEquiv.toMatrix_toPEquiv_eq]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    change cssQuotientIsometryMatrix n N hN (g*h) =
      cssQuotientIsometryMatrix n N hN g * cssQuotientIsometryMatrix n N hN h
    rw [cssQuotientIsometryMatrix_mul]
    simp only [cssQuotientIsometryMatrix, PEquiv.toMatrix_toPEquiv_eq]
    rfl

noncomputable instance cssQuotientGroupFintype
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Fintype (CSSQuotientIsometryGroup N hN) := Fintype.ofFinite _

def cssQuotientFixedProjection (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Matrix (CSSHom n N) (CSSHom n N) ℂ :=
  finiteGroupProjection (cssQuotientIsometryRepresentation n N hN)

theorem cssQuotientFixedProjection_idempotent (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssQuotientFixedProjection n N hN * cssQuotientFixedProjection n N hN =
      cssQuotientFixedProjection n N hN := finiteGroupProjection_idempotent _

theorem cssQuotientFixedProjection_mulVec_eq_iff (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (v : CSSHom n N → ℂ) :
    cssQuotientFixedProjection n N hN *ᵥ v = v ↔
      ∀ g : CSSQuotientIsometryGroup N hN,
        cssQuotientIsometryMatrix n N hN g *ᵥ v = v :=
  finiteGroupProjection_mulVec_eq_iff _ _

theorem cosetMember_stabilizer_iff
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : stochasticDefectStabilizer N) (x : BinaryVector k) (q : CSSQuotient N) :
    cosetMember (orthogonal N) N (g.val.val x)
      ((stochasticDefectQuotientAction N hN g).val q) ↔
      cosetMember (orthogonal N) N x q := by
  have hm (A : Submodule (ZMod 2) (BinaryVector k))
      (hA : stochasticSubspace g.val A = A) (z : BinaryVector k) :
      g.val.val z ∈ A ↔ z ∈ A := by
    conv_lhs => rw [← hA]
    rw [mem_stochasticSubspace, LinearEquiv.symm_apply_apply]
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [stochasticDefectQuotientAction_mk, cosetMember_mk_iff, cosetMember_mk_iff]
    change (g.val.val x ∈ orthogonal N ∧ g.val.val x-g.val.val y.val ∈ N) ↔ _
    rw [← map_sub, hm N g.property,
      hm (orthogonal N) (stochasticSubspace_orthogonal_of_eq g.val N g.property)]

/-- Genuine synthesis intertwining with the full induced quotient action. -/
theorem cssHomSynthesis_stabilizer_intertwine (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : stochasticDefectStabilizer N) :
    stochasticIsometryMatrix n g.val * cssHomSynthesis n N =
      cssHomSynthesis n N *
        cssQuotientIsometryMatrix n N hN (stochasticDefectQuotientAction N hN g) := by
  rw [stochasticIsometryMatrix_mul, cssQuotientIsometryMatrix,
    PEquiv.mul_toMatrix_toPEquiv]
  ext X f
  simp only [Matrix.submatrix_apply, id_eq, Equiv.symm_symm]
  rw [cssHomSynthesis_apply, cssHomSynthesis_apply]
  congr 1
  apply propext
  apply forall_congr'
  intro a
  have h := cosetMember_stabilizer_iff N hN g (g.val.val.symm (X a)) (f (Pi.single a 1))
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The actual ambient group average applied to a single normalized CSS code frame. -/
def averagedCSSHomSynthesis (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (ColumnConfig n k) (CSSHom n N) ℂ :=
  stochasticFixedProjection n k * cssHomSynthesis n N

theorem averagedCSSHomSynthesis_mul_quotient (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (h : CSSQuotientIsometryGroup N hN) :
    averagedCSSHomSynthesis n N * cssQuotientIsometryMatrix n N hN h =
      averagedCSSHomSynthesis n N := by
  obtain ⟨g,rfl⟩ := stochasticDefectQuotientAction_surjective N hN h
  unfold averagedCSSHomSynthesis
  rw [Matrix.mul_assoc, ← cssHomSynthesis_stabilizer_intertwine,
    ← Matrix.mul_assoc, stochasticFixedProjection_mul_isometry]

theorem averagedCSSHomSynthesis_mul_fixedProjection (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    averagedCSSHomSynthesis n N * cssQuotientFixedProjection n N hN =
      averagedCSSHomSynthesis n N := by
  unfold cssQuotientFixedProjection finiteGroupProjection
  rw [Matrix.mul_smul, Matrix.mul_sum]
  change (Fintype.card (CSSQuotientIsometryGroup N hN) : ℂ)⁻¹ •
    (∑ h, averagedCSSHomSynthesis n N * cssQuotientIsometryMatrix n N hN h) = _
  simp only [averagedCSSHomSynthesis_mul_quotient, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem cssHomSynthesis_range (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    LinearMap.range (cssHomSynthesis n N).mulVecLin = cssCode n N := by
  change _ = LinearMap.range (cssColumnProjection n N).mulVecLin
  rw [← cssHomSynthesis_mul_adjoint, matrix_range_self_mul_conjTranspose]

theorem averagedCSSHomSynthesis_range (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    LinearMap.range (averagedCSSHomSynthesis n N).mulVecLin =
      (cssCode n N).map (stochasticFixedProjection n k).mulVecLin := by
  rw [averagedCSSHomSynthesis, Matrix.mulVecLin_mul, LinearMap.range_comp,
    cssHomSynthesis_range n N hN]

theorem averagedCSSCode_stochastic_image (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : StochasticIsometryGroup k) :
    (cssCode n (stochasticSubspace g N)).map (stochasticFixedProjection n k).mulVecLin =
      (cssCode n N).map (stochasticFixedProjection n k).mulVecLin := by
  change (LinearMap.range (cssColumnProjection n (stochasticSubspace g N)).mulVecLin).map _ =
    (LinearMap.range (cssColumnProjection n N).mulVecLin).map _
  rw [← matrix_compressed_projection_range _ _ (cssColumnProjection_isHermitian _ _)
      (cssColumnProjection_idempotent _ _ (stochasticSubspace_isDefect g hN)),
    ← matrix_compressed_projection_range _ _ (cssColumnProjection_isHermitian _ _)
      (cssColumnProjection_idempotent _ _ hN),
    (stochasticFixedProjection_isHermitian n k).eq,
    ← stochasticIsometry_cssColumnProjection]
  congr 2
  calc
    _ = (stochasticFixedProjection n k * stochasticIsometryMatrix n g) *
      cssColumnProjection n N * ((stochasticIsometryMatrix n g)ᴴ * stochasticFixedProjection n k) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [stochasticFixedProjection_mul_isometry,isometry_adjoint_mul_stochasticFixedProjection]

/-- Transitivity identifies the range with the fixed part of the actual raw filtration. -/
theorem averagedCSSHomSynthesis_ordinary_range (n : ℕ) (N : OrdinaryDefect k r) :
    LinearMap.range (averagedCSSHomSynthesis n N.val).mulVecLin =
      rawCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  rw [← matrix_projection_map_eq_inf_range _ (stochasticFixedProjection_idempotent n k)
    _ (fun v hv => stochasticFixedProjection_rawCSSFiltration_mem hv)]
  rw [rawCSSFiltration, Submodule.map_iSup]
  have h (M : OrdinaryDefect k r) :
      (cssCode n M.val).map (stochasticFixedProjection n k).mulVecLin =
        LinearMap.range (averagedCSSHomSynthesis n N.val).mulVecLin := by
    obtain ⟨g,hg⟩ := exists_stochasticSubspace_eq N.val M.val N.property.1 M.property.1
      (N.property.2.1.trans M.property.2.1.symm) (iff_of_false N.property.2.2 M.property.2.2)
    rw [← hg, averagedCSSCode_stochastic_image n N.val N.property.1 g,
      averagedCSSHomSynthesis_range n N.val N.property.1]
  simp only [h]
  letI : Nonempty (OrdinaryDefect k r) := ⟨N⟩
  simp

end ExactCriticalCurve.Quantum

