import StabilizerLearning.Quantum.OddCanonicalReportBridge
import StabilizerLearning.Quantum.BinaryCanonicalReportBridge
import StabilizerLearning.Bounds.CoordinateConverse

/-! Equality of the original standard-chart physical exact-identification
experiment and the already proved coordinate experiment.  Every state, target,
prior, and collective POVM is transported by proved concrete bijections. -/
noncomputable section
namespace StabilizerLearning
open Quantum CoordinateCharacters

def oddReportedPhysicalStateEquiv (p m b : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) :
    OrdinaryVisibleCoordinates (ZMod p) m b × OrdinaryLowerCoordinates (ZMod p) b ≃
      TransverseState p (m+b) :=
  (Equiv.prodCongr (oddReportSignEquiv p m b).symm (Equiv.refl _)).trans
    ((ordinaryMomentCodeEquiv m b).symm.trans (oddCoordinateTransverseStateEquiv p m b h2))

def oddPhysicalMeasurementEquiv (p m b k : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) :
    POVM (Fin k → ((Fin m ⊕ Fin b) → ZMod p)) (OrdinaryVisibleCoordinates (ZMod p) m b) ≃
      POVM (Fin k → Configuration p (m+b)) (CanonicalReport p m b) :=
  experimentPOVMEquiv (copyBasisEquiv (oddConfigurationEquiv p m b) k)
    (oddCanonicalReportEquiv p m b h2).symm

theorem oddReportedPhysicalState_target (p m b : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0)
    (z : OrdinaryVisibleCoordinates (ZMod p) m b × OrdinaryLowerCoordinates (ZMod p) b) :
    physicalCanonicalTarget (oddReportedPhysicalStateEquiv p m b h2 z) =
      (oddCanonicalReportEquiv p m b h2).symm z.1 := by
  apply (oddCanonicalReportEquiv p m b h2).injective
  rw [Equiv.apply_symm_apply]
  change oddCanonicalReportEquiv p m b h2
    (physicalCanonicalTarget (oddCoordinateTransverseStateEquiv p m b h2
      (oddUnscaledParameter p m b ((oddReportSignEquiv p m b).symm z.1) z.2))) = z.1
  rw [oddCanonicalReportEquiv_physicalCanonicalTarget]
  change oddReportSignEquiv p m b
    ((ordinaryMomentCodeEquiv m b)
      ((ordinaryMomentCodeEquiv m b).symm
        ((oddReportSignEquiv p m b).symm z.1, z.2))).1 = z.1
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Single-copy physical density after the proved state and report chart changes. -/
theorem oddReportedPhysicalState_density (p m b : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0)
    (z : OrdinaryVisibleCoordinates (ZMod p) m b × OrdinaryLowerCoordinates (ZMod p) b) :
    (oddReportedPhysicalStateEquiv p m b h2 z).val.val =
      (oddQuadraticDensity p m b
        (oddUnscaledParameter p m b ((oddReportSignEquiv p m b).symm z.1) z.2)).submatrix
          (oddConfigurationEquiv p m b).symm (oddConfigurationEquiv p m b).symm := by
  exact oddCoordinateTransverseStateEquiv_density p m b h2
    (oddUnscaledParameter p m b ((oddReportSignEquiv p m b).symm z.1) z.2)

/-- Tensor transport is proved before any hidden parameter is averaged. -/
theorem oddReportedPhysicalState_tensor_density (p m b k : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0)
    (z : OrdinaryVisibleCoordinates (ZMod p) m b × OrdinaryLowerCoordinates (ZMod p) b) :
    tensorPower (oddReportedPhysicalStateEquiv p m b h2 z).val.val k =
      (tensorPower (oddQuadraticDensity p m b
        (oddUnscaledParameter p m b ((oddReportSignEquiv p m b).symm z.1) z.2)) k).submatrix
          (copyBasisEquiv (oddConfigurationEquiv p m b) k).symm
          (copyBasisEquiv (oddConfigurationEquiv p m b) k).symm := by
  rw [oddReportedPhysicalState_density, tensorPower_basis_equiv]

/-- Pointwise equality for every arbitrary collective measurement; the original
state uniform prior becomes a product prior through an actual state bijection. -/
theorem odd_physicalIdentificationSuccess_eq (p m b k : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0)
    (M : POVM (Fin k → ((Fin m ⊕ Fin b) → ZMod p))
      (OrdinaryVisibleCoordinates (ZMod p) m b)) :
    physicalIdentificationSuccess p m b k (oddPhysicalMeasurementEquiv p m b k h2 M) =
      oddCoordinateSuccess p m b k M := by
  let ρ := fun z : OrdinaryVisibleCoordinates (ZMod p) m b ×
      OrdinaryLowerCoordinates (ZMod p) b =>
    tensorPower (oddQuadraticDensity p m b
      (oddUnscaledParameter p m b ((oddReportSignEquiv p m b).symm z.1) z.2)) k
  have h := uniformTargetSuccess_transport
    (copyBasisEquiv (oddConfigurationEquiv p m b) k)
    (oddReportedPhysicalStateEquiv p m b h2) (oddCanonicalReportEquiv p m b h2).symm
    ρ (fun s : TransverseState p (m+b) => tensorPower s.val.val k)
    Prod.fst physicalCanonicalTarget (oddReportedPhysicalState_tensor_density p m b k h2)
      (oddReportedPhysicalState_target p m b h2) M
  exact h.trans (uniformTargetSuccess_prod
    (fun r h => tensorPower (oddQuadraticDensity p m b
      (oddUnscaledParameter p m b ((oddReportSignEquiv p m b).symm r) h)) k) M)

theorem range_physicalIdentificationSuccess_odd (p m b k : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) :
    Set.range (physicalIdentificationSuccess p m b k) =
      Set.range (oddCoordinateSuccess p m b k) := by
  ext s
  constructor
  · rintro ⟨M, rfl⟩
    obtain ⟨N, rfl⟩ := (oddPhysicalMeasurementEquiv p m b k h2).surjective M
    exact ⟨N, (odd_physicalIdentificationSuccess_eq p m b k h2 N).symm⟩
  · rintro ⟨M, rfl⟩
    exact ⟨oddPhysicalMeasurementEquiv p m b k h2 M,
      odd_physicalIdentificationSuccess_eq p m b k h2 M⟩

theorem physicalIdentificationOptimal_eq_oddCoordinate (p m b k : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) :
    physicalIdentificationOptimal p m b k = oddCoordinateOptimalSuccess p m b k := by
  unfold physicalIdentificationOptimal oddCoordinateOptimalSuccess
  rw [range_physicalIdentificationSuccess_odd p m b k h2]

def binaryReportedPhysicalStateEquiv (m b : ℕ) :
    BinaryVisibleCoordinates m b × BinaryLowerCoordinates b ≃ TransverseState 2 (m+b) :=
  (binarySplitParameterCoordinatesEquiv m b).symm.trans
    (binaryCoordinateTransverseStateEquiv (m+b))

def binaryPhysicalMeasurementEquiv (m b k : ℕ) :
    POVM (Fin k → ((Fin m ⊕ Fin b) → ZMod 2)) (BinaryVisibleCoordinates m b) ≃
      POVM (Fin k → Configuration 2 (m+b)) (CanonicalReport 2 m b) :=
  experimentPOVMEquiv (copyBasisEquiv (binarySourceConfigurationEquiv m b) k)
    (binaryCanonicalReportEquiv m b).symm

theorem binaryReportedPhysicalState_target (m b : ℕ)
    (z : BinaryVisibleCoordinates m b × BinaryLowerCoordinates b) :
    physicalCanonicalTarget (binaryReportedPhysicalStateEquiv m b z) =
      (binaryCanonicalReportEquiv m b).symm z.1 := by
  apply (binaryCanonicalReportEquiv m b).injective
  rw [Equiv.apply_symm_apply]
  change binaryCanonicalReportEquiv m b (physicalCanonicalTarget
    (binaryCoordinateTransverseStateEquiv (m+b) (binaryCoordinateParameter m b z.1 z.2))) = z.1
  rw [binaryCanonicalReportEquiv_physicalCanonicalTarget, binaryCoordinateParameter_target]

theorem binary_physicalIdentificationSuccess_eq (m b k : ℕ)
    (M : POVM (Fin k → ((Fin m ⊕ Fin b) → ZMod 2)) (BinaryVisibleCoordinates m b)) :
    physicalIdentificationSuccess 2 m b k (binaryPhysicalMeasurementEquiv m b k M) =
      binaryCoordinateSuccess m b k M := by
  let ρ := fun z : BinaryVisibleCoordinates m b × BinaryLowerCoordinates b =>
    binaryCoordinateCopyState m b k z.1 z.2
  have hd : ∀ z, tensorPower (binaryReportedPhysicalStateEquiv m b z).val.val k =
      (ρ z).submatrix (copyBasisEquiv (binarySourceConfigurationEquiv m b) k).symm
        (copyBasisEquiv (binarySourceConfigurationEquiv m b) k).symm := by
    intro z
    change tensorPower
      (binaryCoordinateTransverseStateEquiv (m+b) (binaryCoordinateParameter m b z.1 z.2)).val.val k = _
    rw [binaryCoordinateTransverseStateEquiv_density, ← jointProjector_eq_binaryGraphDensity,
      ← binarySourceDensity_reindex_eq_jointProjector, tensorPower_basis_equiv]
    rfl
  have h := uniformTargetSuccess_transport
    (copyBasisEquiv (binarySourceConfigurationEquiv m b) k)
    (binaryReportedPhysicalStateEquiv m b) (binaryCanonicalReportEquiv m b).symm
    ρ (fun s : TransverseState 2 (m+b) => tensorPower s.val.val k)
    Prod.fst physicalCanonicalTarget hd (binaryReportedPhysicalState_target m b) M
  change physicalIdentificationSuccess 2 m b k
    (binaryPhysicalMeasurementEquiv m b k M) = uniformTargetSuccess ρ Prod.fst M at h
  rw [h]
  exact uniformTargetSuccess_prod _ M

theorem range_physicalIdentificationSuccess_binary (m b k : ℕ) :
    Set.range (physicalIdentificationSuccess 2 m b k) =
      Set.range (binaryCoordinateSuccess m b k) := by
  ext s
  constructor
  · rintro ⟨M, rfl⟩
    obtain ⟨N, rfl⟩ := (binaryPhysicalMeasurementEquiv m b k).surjective M
    exact ⟨N, (binary_physicalIdentificationSuccess_eq m b k N).symm⟩
  · rintro ⟨M, rfl⟩
    exact ⟨binaryPhysicalMeasurementEquiv m b k M,
      binary_physicalIdentificationSuccess_eq m b k M⟩

theorem physicalIdentificationOptimal_eq_binaryCoordinate (m b k : ℕ) :
    physicalIdentificationOptimal 2 m b k = binaryCoordinateOptimalSuccess m b k := by
  unfold physicalIdentificationOptimal binaryCoordinateOptimalSuccess
  rw [range_physicalIdentificationSuccess_binary m b k]

/-- The original physical P_id equals the existing coordinate optimum for all
primes and every finite m,b,k. No physical-equivalence premise is assumed. -/
theorem physicalIdentificationOptimal_eq_coordinate (p m b k : ℕ) [Fact p.Prime] :
    physicalIdentificationOptimal p m b k = coordinateOptimalSuccess p m b k := by
  by_cases hp : p = 2
  · subst p
    simpa [coordinateOptimalSuccess] using physicalIdentificationOptimal_eq_binaryCoordinate m b k
  · simpa [coordinateOptimalSuccess, hp] using
      physicalIdentificationOptimal_eq_oddCoordinate p m b k (prime_two_ne_zero p hp)

/-- Every publicly admissible canonical report really is the target of a
physical state; realizability is proved after defining the independent alphabet. -/
theorem physicalCanonicalTarget_surjective (p m b : ℕ) [Fact p.Prime] :
    Function.Surjective (physicalCanonicalTarget (p := p) (m := m) (b := b)) := by
  intro r
  by_cases hp : p = 2
  · subst p
    refine ⟨binaryReportedPhysicalStateEquiv m b (binaryCanonicalReportEquiv m b r, 0), ?_⟩
    rw [binaryReportedPhysicalState_target, Equiv.symm_apply_apply]
  · let h2 := prime_two_ne_zero p hp
    refine ⟨oddReportedPhysicalStateEquiv p m b h2 (oddCanonicalReportEquiv p m b h2 r, 0), ?_⟩
    rw [oddReportedPhysicalState_target, Equiv.symm_apply_apply]

end StabilizerLearning
