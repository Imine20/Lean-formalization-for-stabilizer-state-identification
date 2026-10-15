import StabilizerLearning.Quantum.OddGraphState
import StabilizerLearning.Quantum.PhysicalChart
import StabilizerLearning.Bounds.OddCoordinateProbability

/-! Exact identification of the existing literal odd coordinate densities with
physical graph joint projectors, including the Fin-sum basis permutation. -/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum

/-- Relabel every symmetric and linear coefficient along an actual basis bijection. -/
def fullMomentReindexEquiv {ι κ F : Type*} (e : ι ≃ κ) :
    FullMoment ι F ≃ FullMoment κ F where
  toFun g := (⟨g.1.val.submatrix e.symm e.symm, g.1.property.submatrix e.symm⟩,
    g.2 ∘ e.symm)
  invFun g := (⟨g.1.val.submatrix e e, g.1.property.submatrix e⟩, g.2 ∘ e)
  left_inv g := by
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      simp
    · funext i
      simp
  right_inv g := by
    apply Prod.ext
    · apply Subtype.ext
      ext i j
      simp
    · funext i
      simp

variable (p m b : ℕ) [Fact p.Prime]

/-- Sum-indexed coordinate parameters and ordinary total-dimension parameters. -/
def oddParameterFinEquiv :
    FullMoment (Fin m ⊕ Fin b) (ZMod p) ≃ FullMoment (Fin (m+b)) (ZMod p) :=
  fullMomentReindexEquiv finSumFinEquiv

/-- The actual single-copy computational basis permutation. -/
def oddConfigurationEquiv :
    ((Fin m ⊕ Fin b) → ZMod p) ≃ Configuration p (m+b) where
  toFun x := x ∘ finSumFinEquiv.symm
  invFun x := x ∘ finSumFinEquiv
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

theorem oddGraphWave_reindex
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p))
    (x : (Fin m ⊕ Fin b) → ZMod p) :
    oddGraphWave p (m+b) (oddParameterFinEquiv p m b g).1.val
      (oddParameterFinEquiv p m b g).2 (oddConfigurationEquiv p m b x) =
      oddQuadraticPhase p m b g x := by
  unfold oddGraphWave oddGraphExponent oddQuadraticPhase
  rw [rootPhase_eq_stdAddChar]
  congr 1
  simp only [oddParameterFinEquiv, fullMomentReindexEquiv, oddConfigurationEquiv,
    Equiv.coe_fn_mk, Function.comp_apply, Matrix.submatrix_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum, ← mul_assoc]
  have hquad :
      (∑ i : Fin (m+b), ∑ j : Fin (m+b),
        (2 : ZMod p)⁻¹ * x (finSumFinEquiv.symm i) * g.1.val (finSumFinEquiv.symm i)
          (finSumFinEquiv.symm j) * x (finSumFinEquiv.symm j)) =
      ∑ i, ∑ j, (2 : ZMod p)⁻¹ * x i * g.1.val i j * x j := by
    rw [← finSumFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [← finSumFinEquiv.sum_comp]
    simp
  have hlin : (∑ i : Fin (m+b), g.2 (finSumFinEquiv.symm i) *
      x (finSumFinEquiv.symm i)) = ∑ i, g.2 i*x i := by
    rw [← finSumFinEquiv.sum_comp]
    simp
  rw [hquad, hlin]

/-- Original physical label carrying the actual odd assignment. -/
def oddCoordinateLabel (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) : StabilizerLabel p (m+b) :=
  ⟨graphLagrangian (oddParameterFinEquiv p m b g).1.val
      (oddParameterFinEquiv p m b g).1.property,
    oddGraphAssignment p (m+b) h2 (oddParameterFinEquiv p m b g).1.val
      (oddParameterFinEquiv p m b g).1.property (oddParameterFinEquiv p m b g).2⟩

/-- The pre-existing coordinate density is exactly the physical projector,
after only the explicit computational-basis permutation. -/
theorem labelProjector_oddCoordinateLabel (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    labelProjector p (m+b) (oddCoordinateLabel p m b h2 g) =
      (oddQuadraticDensity p m b g).submatrix
        (oddConfigurationEquiv p m b).symm (oddConfigurationEquiv p m b).symm := by
  unfold labelProjector oddCoordinateLabel
  dsimp only [graphLagrangian]
  rw [jointProjector_oddGraphAssignment]
  ext x y
  have hx := oddGraphWave_reindex p m b g ((oddConfigurationEquiv p m b).symm x)
  have hy := oddGraphWave_reindex p m b g ((oddConfigurationEquiv p m b).symm y)
  simp only [Equiv.apply_symm_apply] at hx hy
  simp only [oddQuadraticDensity, Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul, hx, hy,
    Fintype.card_fun, Fintype.card_sum, Fintype.card_fin, ZMod.card,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast, Nat.cast_pow]

/-- Ordinary total-dimension parameters enumerate all actual graph assignments. -/
def oddFinParameterGraphLabelEquiv (p n : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) :
    FullMoment (Fin n) (ZMod p) ≃
      ((A : SymmetricMatrices (Fin n) (ZMod p)) ×
        Assignment p n (graphSubmodule A.val)) where
  toFun g := ⟨g.1, oddGraphAssignmentEquiv p n h2 g.1.val g.1.property g.2⟩
  invFun z := (z.1, (oddGraphAssignmentEquiv p n h2 z.1.val z.1.property).symm z.2)
  left_inv g := by
    rcases g with ⟨A, c⟩
    simp only [Equiv.symm_apply_apply]
  right_inv z := by
    cases z with
    | mk A η =>
      simp

/-- Full original odd coordinate parameters enumerate every transverse physical label. -/
def oddCoordinateTransverseLabelEquiv (h2 : (2 : ZMod p) ≠ 0) :
    FullMoment (Fin m ⊕ Fin b) (ZMod p) ≃ TransverseLabel p (m + b) :=
  (oddParameterFinEquiv p m b).trans
    ((oddFinParameterGraphLabelEquiv p (m + b) h2).trans
      (graphLabelTransverseEquiv p (m + b)))

@[simp]
theorem oddCoordinateTransverseLabelEquiv_apply (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    (oddCoordinateTransverseLabelEquiv p m b h2 g).val =
      oddCoordinateLabel p m b h2 g := rfl

/-- The label equivalence preserves the literal source density after basis reindexing. -/
theorem labelProjector_oddCoordinateTransverseLabelEquiv
    (h2 : (2 : ZMod p) ≠ 0) (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    labelProjector p (m + b) (oddCoordinateTransverseLabelEquiv p m b h2 g).val =
      (oddQuadraticDensity p m b g).submatrix
        (oddConfigurationEquiv p m b).symm (oddConfigurationEquiv p m b).symm := by
  exact labelProjector_oddCoordinateLabel p m b h2 g

/-- The same parameter space enumerates distinct actual transverse stabilizer states. -/
def oddCoordinateTransverseStateEquiv (h2 : (2 : ZMod p) ≠ 0) :
    FullMoment (Fin m ⊕ Fin b) (ZMod p) ≃ TransverseState p (m + b) :=
  (oddCoordinateTransverseLabelEquiv p m b h2).trans
    (transverseLabelStateEquiv p (m + b))

@[simp]
theorem oddCoordinateTransverseStateEquiv_density
    (h2 : (2 : ZMod p) ≠ 0) (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    (oddCoordinateTransverseStateEquiv p m b h2 g).val.val =
      (oddQuadraticDensity p m b g).submatrix
        (oddConfigurationEquiv p m b).symm (oddConfigurationEquiv p m b).symm := by
  exact labelProjector_oddCoordinateLabel p m b h2 g

end StabilizerLearning.Quantum
