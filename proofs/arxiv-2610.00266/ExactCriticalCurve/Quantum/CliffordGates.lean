import ExactCriticalCurve.Quantum.CliffordAction
import ExactCriticalCurve.Quantum.PhaseStabilizerRecovery
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Concrete normalizer constructors and the actual quadratic diagonal gates. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
open Matrix Classical
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

instance pauliUnitarySubgroupFinite (n : ℕ) : Finite (pauliUnitarySubgroup n) :=
  Finite.of_equiv (PauliLabel n) (pauliRangeEquiv n).toEquiv

/-- For a finite Pauli image, verified forward conjugation implies membership
in its actual normalizer; no surjectivity premise is supplied. -/
def cliffordOfPauliConjugation {n : ℕ}
    (U : Matrix.unitaryGroup (BinaryVector n) ℂ)
    (h : ∀ g : PauliLabel n, ∃ f : PauliLabel n,
      pauliOperator f = U.val * pauliOperator g * U.valᴴ) : CliffordGroup n :=
  ⟨U, by
    letI : Finite (↑(pauliUnitarySubgroup n) : Set (Matrix.unitaryGroup (BinaryVector n) ℂ)) :=
      pauliUnitarySubgroupFinite n
    apply Subgroup.mem_normalizer_fintype
    rintro V ⟨g, rfl⟩
    obtain ⟨f, hf⟩ := h g
    refine ⟨f, ?_⟩
    exact Subtype.ext hf⟩

/-- Pauli translations and clocks are genuine members of the Clifford normalizer. -/
def pauliClifford {n : ℕ} (g : PauliLabel n) : CliffordGroup n :=
  ⟨pauliUnitaryRepresentation n g,
    (pauliUnitarySubgroup n).le_normalizer ⟨g, rfl⟩⟩

theorem linearForm_binaryDot {n : ℕ}
    (f : BinaryVector n →ₗ[ZMod 2] ZMod 2) (x : BinaryVector n) :
    binaryDot (fun i => f (Pi.single i 1)) x = f x := by
  have hx : (∑ i : Fin n, x i • Pi.single i (1 : ZMod 2)) = x := by
    ext j
    simp [Pi.single_apply]
  change (∑ i, f (Pi.single i 1) * x i) = f x
  calc
    _ = f (∑ i : Fin n, x i • Pi.single i (1 : ZMod 2)) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, mul_comm]
    _ = f x := by rw [hx]

/-- Extend a true quadratic refinement along any actual linear map to its space. -/
def quadraticDiagonalMatrix {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (p : BinaryVector n →ₗ[ZMod 2] L) (q : StabilizerPhaseData L) :
    Matrix (BinaryVector n) (BinaryVector n) ℂ :=
  Matrix.diagonal (fun x => pauliPhase (q.phase (p x)))

theorem pauliPhase_star_mul_self (r : ZMod 4) :
    star (pauliPhase r) * pauliPhase r = 1 := by
  rw [← pauliPhase_neg, ← pauliPhase_add, neg_add_cancel, pauliPhase_zero]

def quadraticDiagonalUnitary {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (p : BinaryVector n →ₗ[ZMod 2] L) (q : StabilizerPhaseData L) :
    Matrix.unitaryGroup (BinaryVector n) ℂ :=
  ⟨quadraticDiagonalMatrix p q, by
    rw [Matrix.mem_unitaryGroup_iff']
    simp only [quadraticDiagonalMatrix, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Pi.star_apply, pauliPhase_star_mul_self,
      Matrix.diagonal_one]⟩

def quadraticDiagonalClock {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (p : BinaryVector n →ₗ[ZMod 2] L) (q : StabilizerPhaseData L)
    (a : BinaryVector n) : BinaryVector n :=
  fun i => q.polar (p a) (p (Pi.single i 1))

theorem quadraticDiagonalClock_dot {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (p : BinaryVector n →ₗ[ZMod 2] L) (q : StabilizerPhaseData L)
    (a y : BinaryVector n) :
    binaryDot (quadraticDiagonalClock p q a) y = q.polar (p a) (p y) :=
  linearForm_binaryDot ((q.polar (p a)).comp p) y

/-- Exact conjugation of every phaseful Pauli under the quadratic gate. -/
theorem quadraticDiagonal_conjugation {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)}
    (p : BinaryVector n →ₗ[ZMod 2] L) (q : StabilizerPhaseData L)
    (g : PauliLabel n) :
    quadraticDiagonalMatrix p q * pauliOperator g * (quadraticDiagonalMatrix p q)ᴴ =
      pauliOperator ⟨g.phase + q.phase (p g.shift), g.shift,
        g.clock + quadraticDiagonalClock p q g.shift⟩ := by
  ext x y
  simp only [quadraticDiagonalMatrix, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply, pauliOperator,
    Matrix.smul_apply, smul_eq_mul, pauliMatrix]
  by_cases hxy : x = y + g.shift
  · simp only [hxy, ↓reduceIte, map_add, q.phase_add, pauliDot_add_left,
      quadraticDiagonalClock_dot, pauliPhase_add, pauliPhase_two_bitLift]
    rw [q.polar_symm (p y) (p g.shift)]
    have hp := pauliPhase_star_mul_self (q.phase (p y))
    rw [pauliSign_add]
    calc
      _ = (star (pauliPhase (q.phase (p y))) * pauliPhase (q.phase (p y))) *
        ((pauliPhase g.phase * pauliPhase (q.phase (p g.shift))) *
          (pauliSign (binaryDot g.clock y) * pauliSign (q.polar (p g.shift) (p y)))) := by ring
      _ = _ := by rw [hp, one_mul]
  · simp [hxy]

/-- Every extended mod-four quadratic phase is an actual Clifford unitary. -/
def quadraticDiagonalClifford {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)}
    (p : BinaryVector n →ₗ[ZMod 2] L) (q : StabilizerPhaseData L) : CliffordGroup n :=
  cliffordOfPauliConjugation (quadraticDiagonalUnitary p q)
    (fun g => ⟨⟨g.phase + q.phase (p g.shift), g.shift,
      g.clock + quadraticDiagonalClock p q g.shift⟩,
      (quadraticDiagonal_conjugation p q g).symm⟩)

end ExactCriticalCurve.Quantum
