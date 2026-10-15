import ExactCriticalCurve.Quantum.SelectivePauli

/-! Actual CSS covariance under every unitary in the full Pauli normalizer,
and the resulting genuine compressed unitary on the actual quotient labels. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
namespace ExactCriticalCurve.Quantum
open Binary

/-- The full constraint fixed space is exactly the space fixed by all selected
physical Paulis. The reverse direction proves generation from single-column X/Z. -/
theorem cssColumnProjection_fixed_iff_selective {n k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (w : ColumnConfig n k → ℂ) :
    cssColumnProjection n N *ᵥ w = w ↔
      ∀ (v : N) (g : PauliLabel n),
        copyMatrixInColumnOrder n k (selectivePauli v.val g) *ᵥ w = w := by
  rw [cssColumnProjection_eq_constraintAverage n N hN,
    finiteGroupProjection_mulVec_eq_iff]
  change (∀ g : CSSConstraintGroup n N, cssConstraintMatrix n N g *ᵥ w = w) ↔ _
  constructor
  · intro hw v g
    rw [selectivePauli_eq_constraint N hN]
    exact hw _
  · intro hw g
    let F : (Fin n → N × N) → Prop :=
      fun f => cssConstraintMatrix n N (Multiplicative.ofAdd f) *ᵥ w = w
    have hzero : F 0 := by
      change cssConstraintMatrix n N 1 *ᵥ w = w
      rw [cssConstraintMatrix_one, Matrix.one_mulVec]
    have hadd (f h : Fin n → N × N) (hf : F f) (hh : F h) : F (f+h) := by
      change cssConstraintMatrix n N (Multiplicative.ofAdd f * Multiplicative.ofAdd h) *ᵥ w = w
      rw [cssConstraintMatrix_mul n N hN, ← Matrix.mulVec_mulVec, hh, hf]
    have hx (a : Fin n) (v : N) : F (Pi.single a (v,0)) := by
      have hs := hw v (⟨0,Pi.single a 1,0⟩ : PauliLabel n)
      rw [selectivePauli_eq_constraint N hN] at hs
      have he : (fun b : Fin n => ((Pi.single a (1:ZMod 2) : BinaryVector n) b • v, (0:ZMod 2) • v)) =
          (Pi.single a (v,0) : Fin n → N × N) := by
        funext b
        by_cases hb : b=a <;> simp [Pi.single_apply, hb, eq_comm] <;> rfl
      change cssConstraintMatrix n N (Multiplicative.ofAdd
        (fun b => ((Pi.single a (1:ZMod 2) : BinaryVector n) b • v, (0:ZMod 2) • v))) *ᵥ w = w at hs
      rw [he] at hs
      exact hs
    have hz (a : Fin n) (v : N) : F (Pi.single a (0,v)) := by
      have hs := hw v (⟨0,0,Pi.single a 1⟩ : PauliLabel n)
      rw [selectivePauli_eq_constraint N hN] at hs
      have he : (fun b : Fin n => ((0:ZMod 2) • v, (Pi.single a (1:ZMod 2) : BinaryVector n) b • v)) =
          (Pi.single a (0,v) : Fin n → N × N) := by
        funext b
        by_cases hb : b=a <;> simp [Pi.single_apply, hb, eq_comm] <;> rfl
      change cssConstraintMatrix n N (Multiplicative.ofAdd
        (fun b => ((0:ZMod 2) • v, (Pi.single a (1:ZMod 2) : BinaryVector n) b • v))) *ᵥ w = w at hs
      rw [he] at hs
      exact hs
    have hp (a : Fin n) : F (Pi.single a (g.toAdd a)) := by
      have h := hadd _ _ (hx a (g.toAdd a).1) (hz a (g.toAdd a).2)
      have he : (Pi.single a ((g.toAdd a).1, (0:N)) : Fin n → N × N) +
          (Pi.single a ((0:N),(g.toAdd a).2) : Fin n → N × N) =
            (Pi.single a (g.toAdd a) : Fin n → N × N) := by
        funext b
        by_cases hb : b=a <;> simp [Pi.single_apply, hb, eq_comm] <;> rfl
      simpa only [he] using h
    have hsum : ∀ s : Finset (Fin n), F (∑ a ∈ s, Pi.single a (g.toAdd a)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hzero
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact hadd _ _ (hp a) ih
    have he : (∑ a : Fin n, Pi.single a (g.toAdd a)) = g.toAdd := by
      funext b
      simp [Pi.single_apply]
    simpa only [he] using hsum Finset.univ

/-- Every physical Clifford tensor preserves the actual CSS fixed vectors. -/
theorem cliffordColumnTensor_preserves_css {n k : ℕ} (U : CliffordGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (w : ColumnConfig n k → ℂ) (hw : cssColumnProjection n N *ᵥ w = w) :
    cssColumnProjection n N *ᵥ (cliffordColumnTensor U k *ᵥ w) =
      cliffordColumnTensor U k *ᵥ w := by
  rw [cssColumnProjection_fixed_iff_selective N hN] at hw ⊢
  intro v g
  let h := (cliffordPauliAut U).symm g
  have hc := selectivePauli_column_clifford U v.val h
  rw [MulEquiv.apply_symm_apply] at hc
  rw [← hc]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [cliffordColumnTensor_adjoint_mul, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, hw v h]

theorem cliffordColumnTensor_inv {n : ℕ} (U : CliffordGroup n) (k : ℕ) :
    cliffordColumnTensor U⁻¹ k = (cliffordColumnTensor U k)ᴴ := by
  change copyMatrixInColumnOrder n k (matrixTensorPower k (cliffordMatrix U)ᴴ) = _
  rw [matrixTensorPower_conjTranspose, copyMatrixInColumnOrder_adjoint]
  rfl

theorem cssColumnProjection_clifford_sandwich {n k : ℕ} (U : CliffordGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssColumnProjection n N * cliffordColumnTensor U k * cssColumnProjection n N =
      cliffordColumnTensor U k * cssColumnProjection n N := by
  ext X Y
  have hw : cssColumnProjection n N *ᵥ (cssColumnProjection n N).col Y =
      (cssColumnProjection n N).col Y :=
    congrArg (fun M => M.col Y) (cssColumnProjection_idempotent n N hN)
  have h := cliffordColumnTensor_preserves_css U N hN _ hw
  rw [Matrix.mulVec_mulVec] at h
  exact congrFun h X

/-- Commutation with the full physical Clifford tensor, with no gate-generation premise. -/
theorem cssColumnProjection_commutes_clifford {n k : ℕ} (U : CliffordGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssColumnProjection n N * cliffordColumnTensor U k =
      cliffordColumnTensor U k * cssColumnProjection n N := by
  have h := congrArg Matrix.conjTranspose (cssColumnProjection_clifford_sandwich U⁻¹ N hN)
  simp only [Matrix.conjTranspose_mul, cliffordColumnTensor_inv,
    Matrix.conjTranspose_conjTranspose, (cssColumnProjection_isHermitian n N).eq] at h
  calc
    _ = cssColumnProjection n N * cliffordColumnTensor U k * cssColumnProjection n N := by
      simpa only [Matrix.mul_assoc] using h.symm
    _ = _ := cssColumnProjection_clifford_sandwich U N hN

/-- Genuine CSS covariance under any unitary normalizing the phaseful Pauli group. -/
theorem clifford_cssColumnProjection {n k : ℕ} (U : CliffordGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cliffordColumnTensor U k * cssColumnProjection n N * (cliffordColumnTensor U k)ᴴ =
      cssColumnProjection n N := by
  rw [← cssColumnProjection_commutes_clifford U N hN, Matrix.mul_assoc,
    cliffordColumnTensor_mul_adjoint, Matrix.mul_one]

/-- The actual matrix compressed to the actual normalized CSS quotient basis. -/
def cssCompressedCliffordMatrix {n k : ℕ} (U : CliffordGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (Fin n → CSSQuotient N) (Fin n → CSSQuotient N) ℂ :=
  (cssColumnSynthesis n N)ᴴ * cliffordColumnTensor U k * cssColumnSynthesis n N

theorem cssCompressedCliffordMatrix_adjoint_mul {n k : ℕ} (U : CliffordGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (cssCompressedCliffordMatrix U N)ᴴ * cssCompressedCliffordMatrix U N = 1 := by
  unfold cssCompressedCliffordMatrix
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (cssColumnSynthesis n N)ᴴ * (cliffordColumnTensor U k)ᴴ *
        (cssColumnProjection n N * cliffordColumnTensor U k) * cssColumnSynthesis n N := by
      simp only [cssColumnProjection, Matrix.mul_assoc]
    _ = (cssColumnSynthesis n N)ᴴ * (cliffordColumnTensor U k)ᴴ *
        (cliffordColumnTensor U k * cssColumnProjection n N) * cssColumnSynthesis n N := by
      rw [cssColumnProjection_commutes_clifford U N hN]
    _ = (cssColumnSynthesis n N)ᴴ * (cssColumnProjection n N * cssColumnSynthesis n N) := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (cliffordColumnTensor U k)ᴴ,
        cliffordColumnTensor_adjoint_mul, Matrix.one_mul]
    _ = 1 := by
      rw [cssColumnProjection_mul_synthesis n N hN, cssColumnSynthesis_adjoint_mul_self n N hN]

/-- Actual compressed unitary; no equivalence with a lower-copy representation is assumed. -/
def cssCompressedClifford {n k : ℕ} (U : CliffordGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    unitary (Matrix (Fin n → CSSQuotient N) (Fin n → CSSQuotient N) ℂ) :=
  ⟨cssCompressedCliffordMatrix U N,
    (Matrix.mem_unitaryGroup_iff').mpr (cssCompressedCliffordMatrix_adjoint_mul U N hN)⟩

/-- The actual synthesis intertwines with its compression on the same CSS space. -/
theorem cssCompressedClifford_synthesis {n k : ℕ} (U : CliffordGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssColumnSynthesis n N * cssCompressedCliffordMatrix U N =
      cliffordColumnTensor U k * cssColumnSynthesis n N := by
  unfold cssCompressedCliffordMatrix
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change cssColumnProjection n N * cliffordColumnTensor U k * cssColumnSynthesis n N = _
  rw [cssColumnProjection_commutes_clifford U N hN, Matrix.mul_assoc,
    cssColumnProjection_mul_synthesis n N hN]

end ExactCriticalCurve.Quantum
