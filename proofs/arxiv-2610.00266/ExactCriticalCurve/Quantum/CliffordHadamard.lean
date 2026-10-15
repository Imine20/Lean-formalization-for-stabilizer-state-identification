import ExactCriticalCurve.Quantum.CliffordGates
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Rank-one binary Hadamard gates, acting along a translation and a dual clock. -/
noncomputable section
open scoped BigOperators
open Matrix Classical
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

def pauliHadamardScale : ℂ := (Real.sqrt 2 : ℂ)⁻¹

theorem pauliHadamardScale_sq : pauliHadamardScale * pauliHadamardScale * 2 = 1 := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  unfold pauliHadamardScale
  field_simp
  simpa only [pow_two] using hs.symm

theorem pauliHadamardScale_star : star pauliHadamardScale = pauliHadamardScale := by
  simp [pauliHadamardScale]

def pauliHadamardMatrix {n : ℕ} (a b : BinaryVector n) :
    Matrix (BinaryVector n) (BinaryVector n) ℂ :=
  pauliHadamardScale • (pauliMatrix a 0 + pauliMatrix 0 b)

theorem pauliHadamardMatrix_adjoint {n : ℕ} (a b : BinaryVector n) :
    (pauliHadamardMatrix a b)ᴴ = pauliHadamardMatrix a b := by
  simp [pauliHadamardMatrix, Matrix.conjTranspose_smul,
    pauliHadamardScale_star, pauliMatrix_conjTranspose]

theorem pauliHadamardMatrix_square {n : ℕ} (a b : BinaryVector n)
    (hba : binaryDot b a = 1) :
    pauliHadamardMatrix a b * pauliHadamardMatrix a b = 1 := by
  simp only [pauliHadamardMatrix, Matrix.smul_mul, Matrix.mul_smul,
    add_mul, mul_add, pauliMatrix_mul, pauliDot_zero_left,
    pauliDot_zero_right, pauliSign_zero, one_smul, pauliVector_add_self,
    add_zero, zero_add, pauliMatrix_zero, hba, pauliSign_one, neg_one_smul]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  linear_combination (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) x y *
    pauliHadamardScale_sq

def pauliHadamardUnitary {n : ℕ} (a b : BinaryVector n)
    (hba : binaryDot b a = 1) : Matrix.unitaryGroup (BinaryVector n) ℂ :=
  ⟨pauliHadamardMatrix a b, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      pauliHadamardMatrix_adjoint, pauliHadamardMatrix_square a b hba]⟩

/-- The two possible Pauli images are obtained from an exact four-term expansion. -/
theorem pauliHadamardMatrix_conjugation {n : ℕ} (a b c d : BinaryVector n)
    (hba : binaryDot b a = 1) :
    pauliHadamardMatrix a b * pauliMatrix c d * pauliHadamardMatrix a b =
      if binaryDot d a = binaryDot b c
      then pauliSign (binaryDot d a) • pauliMatrix c d
      else pauliMatrix (c + a) (d + b) := by
  have haa : a + c + a = c := by
    rw [add_comm a c, add_assoc, pauliVector_add_self, add_zero]
  have hbb : b + d + b = d := by
    rw [add_comm b d, add_assoc, pauliVector_add_self, add_zero]
  simp only [pauliHadamardMatrix, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, add_mul, mul_add, pauliMatrix_mul, pauliDot_zero_left,
    pauliDot_zero_right, pauliSign_zero, one_smul, add_zero, zero_add,
    haa, hbb, pauliDot_add_left, hba, pauliSign_add,
    pauliSign_one, neg_one_mul]
  have hac : a + c = c + a := add_comm _ _
  have hbd : b + d = d + b := add_comm _ _
  rw [hac, hbd]
  generalize hda : binaryDot d a = s
  generalize hbc : binaryDot b c = t
  fin_cases s <;> fin_cases t <;>
    norm_num [pauliSign, ZMod.val] <;>
    ext x y <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul] <;>
    first
    | linear_combination pauliMatrix c d x y * pauliHadamardScale_sq
    | linear_combination -(pauliMatrix c d x y) * pauliHadamardScale_sq
    | linear_combination pauliMatrix (c + a) (d + b) x y * pauliHadamardScale_sq

/-- A Clifford gate exists for every genuinely dual translation/clock pair. -/
def pauliHadamardClifford {n : ℕ} (a b : BinaryVector n)
    (hba : binaryDot b a = 1) : CliffordGroup n :=
  cliffordOfPauliConjugation (pauliHadamardUnitary a b hba) (fun g => by
    by_cases hg : binaryDot g.clock a = binaryDot b g.shift
    · refine ⟨⟨g.phase + 2 * bitLift (binaryDot g.clock a), g.shift, g.clock⟩, ?_⟩
      change _ = pauliHadamardMatrix a b * pauliOperator g * (pauliHadamardMatrix a b)ᴴ
      rw [pauliHadamardMatrix_adjoint]
      simp only [pauliOperator, Matrix.mul_smul, Matrix.smul_mul,
        pauliHadamardMatrix_conjugation a b g.shift g.clock hba, if_pos hg,
        smul_smul, pauliPhase_add, pauliPhase_two_bitLift]
    · refine ⟨⟨g.phase, g.shift + a, g.clock + b⟩, ?_⟩
      change _ = pauliHadamardMatrix a b * pauliOperator g * (pauliHadamardMatrix a b)ᴴ
      rw [pauliHadamardMatrix_adjoint]
      simp only [pauliOperator, Matrix.mul_smul, Matrix.smul_mul,
        pauliHadamardMatrix_conjugation a b g.shift g.clock hba, if_neg hg])

end ExactCriticalCurve.Quantum
