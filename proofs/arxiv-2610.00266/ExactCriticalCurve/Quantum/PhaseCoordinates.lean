import ExactCriticalCurve.Quantum.QuadraticRefinement
import ExactCriticalCurve.Quantum.PhaseAverage
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Coordinates of all binary quadratic refinements

A chosen basis gives an actual equivalence between every symmetric mod-four
quadratic refinement on a binary subspace and explicit linear/cross coefficients.
-/
noncomputable section
open scoped BigOperators
open ExactCriticalCurve.Binary Classical Module
namespace ExactCriticalCurve.Quantum

theorem StabilizerPhaseData.ext_of_phase_eq {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} {q r : StabilizerPhaseData L}
    (h : q.phase = r.phase) : q = r := by
  have hp : q.polar = r.polar := by
    apply LinearMap.ext
    intro t
    apply LinearMap.ext
    intro u
    apply doubled_bitLift_injective
    have hq := q.phase_add t u
    have hr := r.phase_add t u
    rw [h] at hq
    exact add_left_cancel (hq.symm.trans hr)
  cases q
  cases r
  cases hp
  cases h
  rfl

/-- The coefficients are actual phase and polar values on the selected basis. -/
def phaseDataCoefficients {n m : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (b : Basis (Fin m) (ZMod 2) L) (q : StabilizerPhaseData L) : QuadraticPhaseData m :=
  (fun i => q.phase (b i), fun p => q.polar (b p.val.1) (b p.val.2))

/-- Explicit coefficient formula transported along the actual basis coordinate equivalence. -/
def phaseDataOfCoefficients {n m : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (b : Basis (Fin m) (ZMod 2) L) (c : QuadraticPhaseData m) : StabilizerPhaseData L where
  polar := (quadraticPhasePolarForm c).compl₁₂ b.equivFun.toLinearMap b.equivFun.toLinearMap
  polar_symm t u := quadraticPhasePolar_symm c (b.equivFun t) (b.equivFun u)
  phase t := quadraticPhaseValue c (b.equivFun t)
  phase_zero := by simp
  phase_add t u := by
    rw [map_add]
    exact quadraticPhaseValue_add c _ _

theorem phaseBasis_coordinates {n m : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (b : Basis (Fin m) (ZMod 2) L) (i : Fin m) :
    b.equivFun (b i) = Pi.single i 1 := by
  ext j
  simp [Basis.equivFun_self, Pi.single_apply, eq_comm]

theorem phaseDataCoefficients_ofCoefficients {n m : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (b : Basis (Fin m) (ZMod 2) L)
    (c : QuadraticPhaseData m) :
    phaseDataCoefficients b (phaseDataOfCoefficients b c) = c := by
  apply Prod.ext
  · funext i
    change quadraticPhaseValue c (b.equivFun (b i)) = c.1 i
    rw [phaseBasis_coordinates, quadraticPhaseValue_single]
  · funext p
    change quadraticPhasePolarForm c (b.equivFun (b p.val.1)) (b.equivFun (b p.val.2)) = c.2 p
    rw [phaseBasis_coordinates, phaseBasis_coordinates, quadraticPhasePolarForm_single_single,
      if_neg p.property.ne, quadraticPhaseCross_of_lt _ _ _ p.property]

theorem phaseDataCoordinates_polar {n m : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (b : Basis (Fin m) (ZMod 2) L)
    (q : StabilizerPhaseData L) :
    (phaseDataOfCoefficients b (phaseDataCoefficients b q)).polar = q.polar := by
  apply LinearMap.BilinForm.ext_basis b
  intro i j
  change quadraticPhasePolarForm (phaseDataCoefficients b q)
    (b.equivFun (b i)) (b.equivFun (b j)) = q.polar (b i) (b j)
  rw [phaseBasis_coordinates, phaseBasis_coordinates, quadraticPhasePolarForm_single_single]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    apply doubled_bitLift_injective
    change (2 : ZMod 4) * bitLift (phaseParity (q.phase (b i))) =
      2 * bitLift (q.polar (b i) (b i))
    rw [two_mul_bitLift_phaseParity]
    exact q.phase_double (b i)
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with h | h
    · rw [quadraticPhaseCross_of_lt _ _ _ h]
      rfl
    · rw [quadraticPhaseCross_symm, quadraticPhaseCross_of_lt _ _ _ h]
      exact q.polar_symm (b j) (b i)


/-- Every given refinement has exactly the explicit polynomial in its basis coordinates. -/
theorem phaseDataCoordinates_phase {n m : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (b : Basis (Fin m) (ZMod 2) L)
    (q : StabilizerPhaseData L) (t : L) :
    quadraticPhaseValue (phaseDataCoefficients b q) (b.equivFun t) = q.phase t := by
  have he :
      (fun z : BinaryVector m => q.phase (b.equivFun.symm z)) =
        quadraticPhaseValue (phaseDataCoefficients b q) := by
    apply binary_function_eq_of_single_differences
    · simp [q.phase_zero]
    · intro z j
      have hb : b.equivFun.symm (Pi.single j 1) = b j := by
        apply b.equivFun.injective
        rw [b.equivFun.apply_symm_apply, phaseBasis_coordinates]
      have hp := congrArg
        (fun B : LinearMap.BilinForm (ZMod 2) L => B (b.equivFun.symm z) (b j))
        (phaseDataCoordinates_polar b q)
      change quadraticPhasePolar (phaseDataCoefficients b q)
        (b.equivFun (b.equivFun.symm z)) (b.equivFun (b j)) =
          q.polar (b.equivFun.symm z) (b j) at hp
      rw [b.equivFun.apply_symm_apply, phaseBasis_coordinates] at hp
      rw [map_add, hb, q.phase_add, quadraticPhaseValue_add,
        quadraticPhaseValue_single, hp]
      change _ = _ + q.phase (b j) + _ - _
      ring
  have ht := congrFun he (b.equivFun t)
  simpa only [b.equivFun.symm_apply_apply] using ht.symm

theorem phaseDataOfCoefficients_coefficients {n m : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (b : Basis (Fin m) (ZMod 2) L)
    (q : StabilizerPhaseData L) :
    phaseDataOfCoefficients b (phaseDataCoefficients b q) = q := by
  apply StabilizerPhaseData.ext_of_phase_eq
  funext t
  exact phaseDataCoordinates_phase b q t

/-- Full equivalence, with no coordinate-classification premise or restricted image. -/
def phaseDataCoordinatesEquiv {n m : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (b : Basis (Fin m) (ZMod 2) L) :
    StabilizerPhaseData L ≃ QuadraticPhaseData m where
  toFun := phaseDataCoefficients b
  invFun := phaseDataOfCoefficients b
  left_inv := phaseDataOfCoefficients_coefficients b
  right_inv := phaseDataCoefficients_ofCoefficients b


theorem phaseDataCoefficients_bijective {n m : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (b : Basis (Fin m) (ZMod 2) L) :
    Function.Bijective (phaseDataCoefficients b) :=
  (phaseDataCoordinatesEquiv b).bijective

/-- Finiteness is transported from actual coefficient functions through the proved equivalence. -/
instance stabilizerPhaseDataFintype {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) : Fintype (StabilizerPhaseData L) :=
  Fintype.ofEquiv (QuadraticPhaseData (Module.finrank (ZMod 2) L))
    (phaseDataCoordinatesEquiv (Module.finBasis (ZMod 2) L)).symm

/-- The number of actual refinements, obtained from the proved coordinate equivalence. -/
theorem stabilizerPhaseData_card {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n)) :
    Nat.card (StabilizerPhaseData L) =
      4 ^ (Module.finrank (ZMod 2) L) *
        2 ^ (Nat.choose (Module.finrank (ZMod 2) L) 2) := by
  rw [Nat.card_congr (phaseDataCoordinatesEquiv (Module.finBasis (ZMod 2) L))]
  exact quadraticPhaseData_card _

end ExactCriticalCurve.Quantum
