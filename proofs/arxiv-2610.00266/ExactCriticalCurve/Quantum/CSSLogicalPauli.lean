import ExactCriticalCurve.Quantum.CSSQuotientGeometry
import ExactCriticalCurve.Quantum.SelectivePauli

/-! # Actual Pauli action on normalized CSS quotient columns -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

theorem cosetMember_add_representative (H N : Submodule (ZMod 2) (BinaryVector k))
    (x : BinaryVector k) (v : H) (q : CosetQuotient H N) :
    cosetMember H N (x + v.val) (q + Submodule.Quotient.mk v) ↔
      cosetMember H N x q := by
  by_cases hx : x ∈ H
  · rw [cosetMember_iff_of_mem H N (H.add_mem hx v.property),
      cosetMember_iff_of_mem H N hx]
    change (N.comap H.subtype).mkQ ((⟨x,hx⟩ : H) + v) =
      q + (N.comap H.subtype).mkQ v ↔ _
    rw [map_add, add_left_inj]
    rfl
  · have hxv : x + v.val ∉ H := by
      intro h
      have hh := H.sub_mem h v.property
      exact hx (by simpa only [add_sub_cancel_right] using hh)
    exact ⟨fun h => (hxv h.choose).elim, fun h => (hx h.choose).elim⟩

theorem cssCosetMember_shift (N : Submodule (ZMod 2) (BinaryVector k))
    (v : orthogonal N) (a : ZMod 2) (x : BinaryVector k) (q : CSSQuotient N) :
    cosetMember (orthogonal N) N (x + a • v.val) q ↔
      cosetMember (orthogonal N) N x (q + a • Submodule.Quotient.mk v) := by
  have hv : v + v = 0 := Subtype.ext (pauliVector_add_self v.val)
  have hh : (a • (Submodule.Quotient.mk v : CSSQuotient N)) +
      a • Submodule.Quotient.mk v = 0 := by
    change a • (N.comap (orthogonal N).subtype).mkQ v +
      a • (N.comap (orthogonal N).subtype).mkQ v = 0
    rw [← smul_add, ← map_add, hv, map_zero, smul_zero]
  have h := cosetMember_add_representative (orthogonal N) N x (a • v)
    (q + a • Submodule.Quotient.mk v)
  change cosetMember (orthogonal N) N (x + a • v.val)
    ((q + a • Submodule.Quotient.mk v) +
      (N.comap (orthogonal N).subtype).mkQ (a • v)) ↔ _ at h
  simpa only [map_smul, Submodule.mkQ_apply, add_assoc, hh, add_zero] using h

/-- The quotient XZ operator is defined by the actual quotient shift and pairing. -/
def cssQuotientPauli (N : Submodule (ZMod 2) (BinaryVector k))
    (v : orthogonal N) (a b : ZMod 2) : Matrix (CSSQuotient N) (CSSQuotient N) ℂ :=
  fun p q => if p = q + a • Submodule.Quotient.mk v
    then pauliSign (b * cssQuotientBilinear N (Submodule.Quotient.mk v) q) else 0

/-- Exact single-column intertwining, with the actual normalized coset columns. -/
theorem pauliMatrix_cssCosetSynthesis (N : Submodule (ZMod 2) (BinaryVector k))
    (v : orthogonal N) (a b : ZMod 2) :
    pauliMatrix (a • v.val) (b • v.val) * cssCosetSynthesis N =
      cssCosetSynthesis N * cssQuotientPauli N v a b := by
  ext x q
  have hl : (pauliMatrix (a • v.val) (b • v.val) * cssCosetSynthesis N) x q =
      pauliSign (binaryDot (b • v.val) (x + a • v.val)) *
        cssCosetSynthesis N (x + a • v.val) q := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (x + a • v.val)]
    · have he : x = (x + a • v.val) + a • v.val := by
        rw [add_assoc, pauliVector_add_self, add_zero]
      simp only [pauliMatrix, if_pos he]
    · intro y _ hy
      have he : x ≠ y + a • v.val := by
        intro h
        exact hy ((pauliShift_iff (a • v.val) x y).mpr h)
      simp only [pauliMatrix, if_neg he, zero_mul]
    · simp
  have hr : (cssCosetSynthesis N * cssQuotientPauli N v a b) x q =
      cssCosetSynthesis N x (q + a • Submodule.Quotient.mk v) *
        pauliSign (b * cssQuotientBilinear N (Submodule.Quotient.mk v) q) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (q + a • Submodule.Quotient.mk v)]
    · simp only [cssQuotientPauli, ite_true]
    · intro p _ hp
      simp only [cssQuotientPauli, if_neg hp, mul_zero]
    · simp
  rw [hl, hr]
  have he : cssCosetSynthesis N (x + a • v.val) q =
      cssCosetSynthesis N x (q + a • Submodule.Quotient.mk v) := by
    simp only [cssCosetSynthesis, cosetSynthesis_apply, cssCosetMember_shift]
  by_cases hx : cosetMember (orthogonal N) N (x + a • v.val) q
  · obtain ⟨hx, hq⟩ := hx
    have hc : binaryDot (b • v.val) (x + a • v.val) =
        b * cssQuotientBilinear N (Submodule.Quotient.mk v) q := by
      rw [← hq]
      change (binaryDotForm k (b • v.val)) (x + a • v.val) =
        b * binaryDot v.val (x + a • v.val)
      rw [map_smul, LinearMap.smul_apply]
      rfl
    rw [hc, he, mul_comm]
  · have hz : cssCosetSynthesis N (x + a • v.val) q = 0 := by
      simp only [cssCosetSynthesis, cosetSynthesis_apply, if_neg hx]
    rw [← he, hz, mul_zero, zero_mul]


/-- Actual selective physical action in column order, including the full central phase. -/
theorem selectivePauli_column_factor {n : ℕ}
    (v : BinaryVector k) (g : PauliLabel n) :
    copyMatrixInColumnOrder n k (selectivePauli v g) =
      pauliPhase (g.phase * weightQuadratic v) •
        matrixTensorFamily n (fun a => pauliMatrix (g.shift a • v) (g.clock a • v)) := by
  rw [selectivePauli_factor]
  change pauliPhase (g.phase * weightQuadratic v) • copyMatrixInColumnOrder n k
    (matrixTensorFamily k (fun i => pauliMatrix ((v i) • g.shift) ((v i) • g.clock))) = _
  rw [pauliTensor_transpose]
  congr 1
  congr 1
  funext a
  congr 1 <;> funext i <;> simp [smul_eq_mul, mul_comm]

/-- The actual quotient action of one selected physical Pauli. -/
def cssQuotientSelectivePauli {n : ℕ} (N : Submodule (ZMod 2) (BinaryVector k))
    (v : orthogonal N) (g : PauliLabel n) :
    Matrix (Fin n → CSSQuotient N) (Fin n → CSSQuotient N) ℂ :=
  pauliPhase (g.phase * weightQuadratic v.val) •
    matrixTensorFamily n (fun a => cssQuotientPauli N v (g.shift a) (g.clock a))

/-- The full selected physical Pauli acts on the actual normalized quotient basis. -/
theorem selectivePauli_cssColumnSynthesis {n : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (v : orthogonal N) (g : PauliLabel n) :
    copyMatrixInColumnOrder n k (selectivePauli v.val g) * cssColumnSynthesis n N =
      cssColumnSynthesis n N * cssQuotientSelectivePauli N v g := by
  rw [selectivePauli_column_factor, cssQuotientSelectivePauli,
    Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  unfold cssColumnSynthesis
  rw [← matrixTensorFamily_const, ← matrixTensorFamily_mul, ← matrixTensorFamily_mul]
  congr 1
  funext a
  exact pauliMatrix_cssCosetSynthesis N v (g.shift a) (g.clock a)

end ExactCriticalCurve.Quantum
