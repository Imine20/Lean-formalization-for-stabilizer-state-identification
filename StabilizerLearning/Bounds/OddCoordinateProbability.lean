import StabilizerLearning.FiniteCopy.CoordinateCharacters
import StabilizerLearning.FiniteCopy.LabelTransport
import StabilizerLearning.Bounds.FiniteProbabilityReduction

/-!
This module treats the original odd-prime quadratic coordinate ensemble.
Here m is the number of visible rows and n is the number of lower rows,
so the total number of coordinates is m+n. The visible linear report is
gamma=-b₁. The optimum ranges over every collective POVM on actual k-copy
tuples; no PGM optimality or postulated ensemble identification is used.
-/

noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning
open CoordinateCharacters

variable (p m n : ℕ) [Fact p.Prime]

/-- The original ordinary quadratic phase, on an actual single-copy vector. -/
def oddQuadraticPhase (g : FullMoment (Fin m ⊕ Fin n) (ZMod p))
    (x : (Fin m ⊕ Fin n) → ZMod p) : ℂ :=
  ZMod.stdAddChar ((2 : ZMod p)⁻¹ * (∑ i, ∑ j, x i * g.1.val i j * x j) +
    ∑ i, g.2 i * x i)

/-- Original coordinate state density: the normalized outer product of the
literal half-quadratic-plus-linear phase. No moment or character identity is a premise. -/
def oddQuadraticDensity (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) :
    Matrix ((Fin m ⊕ Fin n) → ZMod p) ((Fin m ⊕ Fin n) → ZMod p) ℂ :=
  (Fintype.card ((Fin m ⊕ Fin n) → ZMod p) : ℝ)⁻¹ •
    Matrix.vecMulVec (oddQuadraticPhase p m n g) (star (oddQuadraticPhase p m n g))

theorem oddQuadraticPhase_eq_character (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) (x : (Fin m ⊕ Fin n) → ZMod p) :
    oddQuadraticPhase p m n g x =
      CharacterEnsemble.phase (ordinarySingleCopyCode (ZMod p) m n)
        (oddSplitParameterCharacterEquiv p m n h2 g).1
        (oddSplitParameterCharacterEquiv p m n h2 g).2 x := by
  unfold CharacterEnsemble.phase ordinarySingleCopyCode
  rw [oddSplitParameterCharacterEquiv_apply]
  unfold oddQuadraticPhase
  congr 2
  · congr 1
    simp only [fullMoment, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_one]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [fullMoment, Matrix.mulVec, dotProduct]

theorem oddQuadraticDensity_eq_character (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) :
    oddQuadraticDensity p m n g =
      CharacterEnsemble.density (ordinarySingleCopyCode (ZMod p) m n)
        (oddSplitParameterCharacterEquiv p m n h2 g).1
        (oddSplitParameterCharacterEquiv p m n h2 g).2 := by
  have hp := funext (oddQuadraticPhase_eq_character p m n h2 g)
  unfold oddQuadraticDensity CharacterEnsemble.density
  rw [hp]

theorem oddQuadraticDensity_posSemidef
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) :
    (oddQuadraticDensity p m n g).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)

theorem oddQuadraticDensity_trace (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) :
    Matrix.trace (oddQuadraticDensity p m n g) = 1 := by
  rw [oddQuadraticDensity_eq_character p m n h2]
  exact CharacterEnsemble.density_trace _ _ _

/-- The unscaled independent parameter pair reconstructs the actual (A,b). -/
def oddUnscaledParameter (v : OrdinaryVisibleCoordinates (ZMod p) m n)
    (h : OrdinaryLowerCoordinates (ZMod p) n) :
    FullMoment (Fin m ⊕ Fin n) (ZMod p) :=
  (ordinaryMomentCodeEquiv m n).symm (v,h)

/-- Negating the linear last column records the paper's reported gamma=-b₁.
Every symmetric and cross-block coordinate stays fixed. -/
def oddReportSignEquiv :
    OrdinaryVisibleCoordinates (ZMod p) m n ≃ OrdinaryVisibleCoordinates (ZMod p) m n := by
  classical
  let f := fun v : OrdinaryVisibleCoordinates (ZMod p) m n =>
    (v.1, fun i j => if j = finSumFinEquiv (Sum.inr (0 : Fin 1)) then -v.2 i j else v.2 i j)
  have hf : Function.Involutive f := by
    intro v
    apply Prod.ext
    · rfl
    · funext i j
      dsimp [f]
      split_ifs <;> simp
  exact ⟨f, f, hf, hf⟩

theorem oddReportSignEquiv_linear
    (v : OrdinaryVisibleCoordinates (ZMod p) m n) (i : Fin m) :
    (oddReportSignEquiv p m n v).2 i (finSumFinEquiv (Sum.inr (0 : Fin 1))) =
      -v.2 i (finSumFinEquiv (Sum.inr (0 : Fin 1))) := by
  simp [oddReportSignEquiv]

theorem oddReportSignEquiv_cross
    (v : OrdinaryVisibleCoordinates (ZMod p) m n) (i : Fin m) (j : Fin n) :
    (oddReportSignEquiv p m n v).2 i (finSumFinEquiv (Sum.inl j)) =
      v.2 i (finSumFinEquiv (Sum.inl j)) := by
  have hne : finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin 1) ≠
      finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
    intro h
    exact Sum.noConfusion (finSumFinEquiv.injective h)
  change (if finSumFinEquiv (Sum.inl j) = finSumFinEquiv (Sum.inr (0 : Fin 1))
    then -v.2 i (finSumFinEquiv (Sum.inl j)) else v.2 i (finSumFinEquiv (Sum.inl j))) = _
  exact if_neg hne

def oddVisibleLabelCharacterEquiv (h2 : (2 : ZMod p) ≠ 0) :
    OrdinaryVisibleCoordinates (ZMod p) m n ≃
      AddChar (OrdinaryVisibleCoordinates (ZMod p) m n) ℂ :=
  (oddReportSignEquiv p m n).symm.trans
    ((oddVisibleParameterCoordinatesEquiv m n h2).trans
      (ordinaryVisibleCharacterEquiv p m n).toEquiv)

def oddHiddenLabelCharacterEquiv (h2 : (2 : ZMod p) ≠ 0) :
    OrdinaryLowerCoordinates (ZMod p) n ≃ AddChar (OrdinaryLowerCoordinates (ZMod p) n) ℂ :=
  (Equiv.prodCongr (diagonalHalfEquiv h2) (Equiv.refl _)).trans
    (ordinaryLowerCharacterEquiv p n).toEquiv

theorem odd_reportedDensity_eq_character (h2 : (2 : ZMod p) ≠ 0)
    (r : OrdinaryVisibleCoordinates (ZMod p) m n)
    (h : OrdinaryLowerCoordinates (ZMod p) n) :
    oddQuadraticDensity p m n (oddUnscaledParameter p m n ((oddReportSignEquiv p m n).symm r) h) =
    CharacterEnsemble.density (ordinarySingleCopyCode (ZMod p) m n)
      (oddVisibleLabelCharacterEquiv p m n h2 r)
      (oddHiddenLabelCharacterEquiv p n h2 h) := by
  rw [oddQuadraticDensity_eq_character p m n h2]
  simp only [oddUnscaledParameter, oddSplitParameterCharacterEquiv,
    oddSplitParameterCoordinatesEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.apply_symm_apply, oddVisibleLabelCharacterEquiv, oddHiddenLabelCharacterEquiv]
  rfl

/-- Actual tensor-copy experiment, with raw unscaled lower labels and gamma=-b₁
visible reports. The measurement acts on the complete tuple Hilbert basis. -/
def oddCoordinateSuccess (k : ℕ)
    (M : Quantum.POVM (Fin k → ((Fin m ⊕ Fin n) → ZMod p))
      (OrdinaryVisibleCoordinates (ZMod p) m n)) : ℝ :=
  hiddenUniformLabelSuccess
    (fun r h => Quantum.tensorPower
      (oddQuadraticDensity p m n (oddUnscaledParameter p m n
        ((oddReportSignEquiv p m n).symm r) h)) k) M

/-- Supremum over every normalized PSD collective POVM in the original basis. -/
def oddCoordinateOptimalSuccess (k : ℕ) : ℝ :=
  sSup (Set.range (oddCoordinateSuccess p m n k))

private theorem hiddenUniformLabelSuccess_basis {Ω Ω' Y H : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype Y] [Fintype H] (e : Ω ≃ Ω')
    (ρ : Y → H → Matrix Ω Ω ℂ) (M : Quantum.POVM Ω Y) :
    hiddenUniformLabelSuccess ρ M =
      hiddenUniformLabelSuccess (fun y h => (ρ y h).submatrix e.symm e.symm)
        (Quantum.POVM.reindex e M) := by
  unfold hiddenUniformLabelSuccess uniformLabelSuccess uniformFiniteMean
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  have hh : hiddenUniformState (fun h => (ρ y h).submatrix e.symm e.symm) =
      (hiddenUniformState (ρ y)).submatrix e.symm e.symm := by
    ext x x'
    simp only [hiddenUniformState, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.submatrix_apply]
  dsimp only
  rw [hh, Quantum.POVM.reindex_born]

/-- Both physical basis and original report alphabet are changed by reversible
maps, so this includes all collective measurements exactly. -/
def oddCoordinateMeasurementEquiv (h2 : (2 : ZMod p) ≠ 0) (k : ℕ) :
    Quantum.POVM (Fin k → ((Fin m ⊕ Fin n) → ZMod p))
      (OrdinaryVisibleCoordinates (ZMod p) m n) ≃
    Quantum.POVM (Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod p))
      (AddChar (OrdinaryVisibleCoordinates (ZMod p) m n) ℂ) :=
  (Quantum.POVM.reindexEquiv (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod p) k).symm).trans
    (Quantum.POVM.relabel (oddVisibleLabelCharacterEquiv p m n h2))

theorem oddCoordinateSuccess_eq_character (h2 : (2 : ZMod p) ≠ 0) (k : ℕ)
    (M : Quantum.POVM (Fin k → ((Fin m ⊕ Fin n) → ZMod p))
      (OrdinaryVisibleCoordinates (ZMod p) m n)) :
    oddCoordinateSuccess p m n k M =
      characterSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod p) =>
        ordinaryMomentCode (fullMoment X)) (oddCoordinateMeasurementEquiv p m n h2 k M) := by
  unfold oddCoordinateSuccess
  rw [hiddenUniformLabelSuccess_basis
    (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod p) k).symm]
  change hiddenUniformLabelSuccess
    (fun r h => Quantum.tensorPowerMatrixBasis
      (oddQuadraticDensity p m n (oddUnscaledParameter p m n
        ((oddReportSignEquiv p m n).symm r) h)) k)
    (Quantum.POVM.reindex (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod p) k).symm M) = _
  simp_rw [odd_reportedDensity_eq_character p m n h2]
  rw [tensor_character_uniform_success_transport]
  unfold uniformLabelSuccess
  simp_rw [ordinary_conditioned_tensorPower_eq_moment]
  simp only [uniformFiniteMean, characterSuccess,
    Nat.card_eq_fintype_card]
  rfl

theorem oddCoordinateOptimalSuccess_eq_character (h2 : (2 : ZMod p) ≠ 0) (k : ℕ) :
    oddCoordinateOptimalSuccess p m n k =
      characterOptimalSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod p) =>
        ordinaryMomentCode (fullMoment X)) := by
  unfold oddCoordinateOptimalSuccess characterOptimalSuccess
  congr 1
  ext s
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨oddCoordinateMeasurementEquiv p m n h2 k M,
      (oddCoordinateSuccess_eq_character p m n h2 k M).symm⟩
  · rintro ⟨M, rfl⟩
    let N := (oddCoordinateMeasurementEquiv p m n h2 k).symm M
    refine ⟨N, ?_⟩
    rw [oddCoordinateSuccess_eq_character p m n h2]
    exact congrArg _ ((oddCoordinateMeasurementEquiv p m n h2 k).apply_symm_apply M)

omit [Fact p.Prime] in
private theorem classicalZModDecEq :
    (fun a b : ZMod p => Classical.propDecidable (a = b)) = ZMod.decidableEq p :=
  Subsingleton.elim _ _

/-- The original quadratic-state optimum satisfies the exact finite
probability--completion bound, without a phase, ensemble, or counting premise. -/
theorem odd_coordinate_probability_completion_reduction
    (h2 : (2 : ZMod p) ≠ 0) (k : ℕ) :
    oddCoordinateOptimalSuccess p m n k ≤
      ∑ z ∈ positiveMassAugmentedRowParameters (ZMod p) n k (fun _ => 1),
        uniformMatrixProbability (augmentedRowSpaceEvent (ZMod p) n k z.1.val z.2.val
          (fun _ => 1)) * ordinaryExactClippedFactor (ZMod p) m n k z.1.val z.2.val := by
  rw [oddCoordinateOptimalSuccess_eq_character p m n h2]
  have h := ordinary_probability_completion_reduction (ZMod p) m n k
  rw [classicalZModDecEq p] at h
  exact h

theorem odd_coordinate_probability_finite_structural_bound
    (h2 : (2 : ZMod p) ≠ 0) (k : ℕ) :
    oddCoordinateOptimalSuccess p m n k ≤
      ∑ z ∈ positiveMassAugmentedRowParameters (ZMod p) n k (fun _ => 1),
        rowEventScalarBound (ZMod p) n k z.1.val z.2.val *
          ordinaryFiniteStructuralFactor (ZMod p) m n k z.1.val z.2.val := by
  rw [oddCoordinateOptimalSuccess_eq_character p m n h2]
  have h := ordinary_probability_finite_structural_bound (ZMod p) m n k
  rw [classicalZModDecEq p] at h
  exact h

theorem odd_coordinate_probability_source_bound (h2 : (2 : ZMod p) ≠ 0) (k : ℕ) :
    ∃ ell t : Fin (k+1) × Fin (k+1) → ℕ,
      (∀ z ∈ positiveMassAugmentedRowParameters (ZMod p) n k (fun _ => 1),
        sourceCompletionDomain m (n+1) k z.1.val z.2.val (ell z) (t z) ∧
        ∀ ell' t', sourceCompletionDomain m (n+1) k z.1.val z.2.val ell' t' →
          sourceFiniteExponent m (n+1) z.1.val z.2.val ell' t' ≤
            sourceFiniteExponent m (n+1) z.1.val z.2.val (ell z) (t z)) ∧
      oddCoordinateOptimalSuccess p m n k ≤
        ∑ z ∈ positiveMassAugmentedRowParameters (ZMod p) n k (fun _ => 1),
          rowEventScalarBound (ZMod p) n k z.1.val z.2.val *
            min 1 (16*((m+1 : ℕ) : ℝ)^2*(p : ℝ)^
              (sourceFiniteExponent m (n+1) z.1.val z.2.val (ell z) (t z) -
                (visibleLabelExponent m n : ℤ))) := by
  rw [oddCoordinateOptimalSuccess_eq_character p m n h2]
  have h := ordinary_probability_source_bound (ZMod p) m n k
  rw [classicalZModDecEq p] at h
  simpa only [ZMod.card] using h

end StabilizerLearning
