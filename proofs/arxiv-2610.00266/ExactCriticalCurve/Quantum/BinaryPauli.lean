import ExactCriticalCurve.Binary.Geometry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Concrete binary Pauli matrices with their full central phase

The unphased convention is X(a) Z(b): entry (x,y) is
delta_(x=y+a) (-1)^(b dot y). The central phase is i^t for t in ZMod 4.
In GNW, §§2.1–2.2, tau=i and W_(p,q)=tau^(-p dot q) Z(p) X(q);
our convention retains the full central phase instead of identifying these lifts.
-/

noncomputable section
open scoped BigOperators Matrix
open Matrix Classical

namespace ExactCriticalCurve.Quantum
open Binary

/-- The faithful fourth-root-of-unity phase, with its actual ZMod 4 label. -/
def pauliPhase (t : ZMod 4) : ℂ := Complex.I ^ t.val

/-- The binary character taking 0 to 1 and 1 to -1. -/
def pauliSign (z : ZMod 2) : ℂ := (-1 : ℂ) ^ z.val

@[simp] theorem pauliPhase_zero : pauliPhase 0 = 1 := by norm_num [ZMod.val, pauliPhase]
@[simp] theorem pauliPhase_one : pauliPhase 1 = Complex.I := by norm_num [ZMod.val, pauliPhase]
@[simp] theorem pauliPhase_add (s t : ZMod 4) :
    pauliPhase (s + t) = pauliPhase s * pauliPhase t := by
  simp only [pauliPhase, ZMod.val_add]
  fin_cases s <;> fin_cases t <;> norm_num [ZMod.val, pow_succ, Complex.I_sq]
@[simp] theorem pauliPhase_neg (t : ZMod 4) :
    pauliPhase (-t) = star (pauliPhase t) := by
  fin_cases t
  · norm_num [pauliPhase]
  · change Complex.I ^ 3 = star (Complex.I ^ 1)
    norm_num [pow_succ, Complex.I_sq]
  · change Complex.I ^ 2 = star (Complex.I ^ 2)
    norm_num [Complex.I_sq]
  · change Complex.I ^ 1 = star (Complex.I ^ 3)
    norm_num [pow_succ, Complex.I_sq]
theorem pauliPhase_ne_zero (t : ZMod 4) : pauliPhase t ≠ 0 := by
  exact pow_ne_zero _ Complex.I_ne_zero
theorem pauliPhase_injective : Function.Injective pauliPhase := by
  intro s t h
  fin_cases s <;> fin_cases t <;>
    simp_all [pauliPhase, ZMod.val, pow_succ, Complex.ext_iff] <;> norm_num at *


@[simp] theorem pauliSign_zero : pauliSign 0 = 1 := by norm_num [ZMod.val, pauliSign]
@[simp] theorem pauliSign_one : pauliSign 1 = -1 := by norm_num [ZMod.val, pauliSign]
@[simp] theorem pauliSign_add (s t : ZMod 2) :
    pauliSign (s + t) = pauliSign s * pauliSign t := by
  fin_cases s <;> fin_cases t <;> norm_num [ZMod.val, pauliSign]
@[simp] theorem pauliSign_star (t : ZMod 2) : star (pauliSign t) = pauliSign t := by
  fin_cases t <;> norm_num [ZMod.val, pauliSign]
theorem pauliSign_ne_zero (t : ZMod 2) : pauliSign t ≠ 0 := by
  exact pow_ne_zero _ (by norm_num)
theorem pauliSign_injective : Function.Injective pauliSign := by
  intro s t h
  fin_cases s <;> fin_cases t <;> simp_all [ZMod.val, pauliSign] <;> norm_num at *
@[simp] theorem pauliSign_mul_self (t : ZMod 2) : pauliSign t * pauliSign t = 1 := by
  fin_cases t <;> norm_num [ZMod.val, pauliSign]
theorem pauliPhase_two_bitLift (t : ZMod 2) :
    pauliPhase (2 * bitLift t) = pauliSign t := by
  fin_cases t <;> norm_num [ZMod.val, pauliPhase, pauliSign, bitLift, pow_succ, Complex.I_sq]

variable {n : ℕ}

theorem pauliVector_add_self (x : BinaryVector n) : x + x = 0 := by
  ext i
  have h (t : ZMod 2) : t + t = 0 := by fin_cases t <;> decide
  exact h (x i)

theorem pauliDot_add_left (a b c : BinaryVector n) :
    binaryDot (a + b) c = binaryDot a c + binaryDot b c := by
  simp [binaryDot, add_mul, Finset.sum_add_distrib]

theorem pauliDot_add_right (a b c : BinaryVector n) :
    binaryDot a (b + c) = binaryDot a b + binaryDot a c := by
  simp [binaryDot, mul_add, Finset.sum_add_distrib]

@[simp] theorem pauliDot_zero_left (a : BinaryVector n) : binaryDot 0 a = 0 := by
  simp [binaryDot]
@[simp] theorem pauliDot_zero_right (a : BinaryVector n) : binaryDot a 0 = 0 := by
  simp [binaryDot]
@[simp] theorem pauliDot_single_right (a : BinaryVector n) (i : Fin n) :
    binaryDot a (Pi.single i 1) = a i := by
  simp [binaryDot, Pi.single_apply]

/-- The concrete, unphased X(a) Z(b) matrix in the computational basis. -/
def pauliMatrix (a b : BinaryVector n) : Matrix (BinaryVector n) (BinaryVector n) ℂ :=
  fun x y => if x = y + a then pauliSign (binaryDot b y) else 0


@[simp] theorem pauliMatrix_zero : pauliMatrix (0 : BinaryVector n) 0 = 1 := by
  ext x y
  simp [pauliMatrix, Matrix.one_apply]

/-- The ordered XZ convention has cocycle (-1)^(b dot c). -/
theorem pauliMatrix_mul (a b c d : BinaryVector n) :
    pauliMatrix a b * pauliMatrix c d =
      pauliSign (binaryDot b c) • pauliMatrix (a + c) (b + d) := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (y + c)]
  · have hs : (y + c) + a = y + (a + c) := by abel
    simp only [pauliMatrix, Matrix.smul_apply, smul_eq_mul, hs]
    split_ifs
    · rw [pauliDot_add_right, pauliDot_add_left, pauliSign_add, pauliSign_add]
      ring
    · simp
  · intro z _ hz
    simp [pauliMatrix, hz]
  · simp

theorem pauliShift_iff (a x y : BinaryVector n) : y = x + a ↔ x = y + a := by
  constructor <;> intro h
  · rw [h, add_assoc, pauliVector_add_self, add_zero]
  · rw [h, add_assoc, pauliVector_add_self, add_zero]

/-- Adjoint includes the phase of the ordered XZ product. -/
theorem pauliMatrix_conjTranspose (a b : BinaryVector n) :
    (pauliMatrix a b)ᴴ = pauliSign (binaryDot b a) • pauliMatrix a b := by
  ext x y
  by_cases h : x = y + a
  · have h' : y = x + a := (pauliShift_iff a x y).mpr h
    simp only [Matrix.conjTranspose_apply, pauliMatrix, if_pos h', if_pos h,
      pauliSign_star, Matrix.smul_apply, smul_eq_mul]
    rw [h, pauliDot_add_right, pauliSign_add, mul_comm]
  · have h' : ¬ y = x + a := fun hh => h ((pauliShift_iff a x y).mp hh)
    simp [Matrix.conjTranspose_apply, pauliMatrix, h, h']

@[simp] theorem pauliMatrix_adjoint_mul_self (a b : BinaryVector n) :
    (pauliMatrix a b)ᴴ * pauliMatrix a b = 1 := by
  rw [pauliMatrix_conjTranspose, Matrix.smul_mul, pauliMatrix_mul,
    pauliVector_add_self, pauliVector_add_self, pauliMatrix_zero,
    smul_smul, pauliSign_mul_self, one_smul]

@[simp] theorem pauliMatrix_mul_adjoint_self (a b : BinaryVector n) :
    pauliMatrix a b * (pauliMatrix a b)ᴴ = 1 := by
  rw [pauliMatrix_conjTranspose, Matrix.mul_smul, pauliMatrix_mul,
    pauliVector_add_self, pauliVector_add_self, pauliMatrix_zero,
    smul_smul, pauliSign_mul_self, one_smul]

/-- All three finite labels are retained, including the central fourth root. -/
@[ext] structure PauliLabel (n : ℕ) where
  phase : ZMod 4
  shift : BinaryVector n
  clock : BinaryVector n
  deriving DecidableEq, Fintype

/-- The actual matrix corresponding to a phaseful Pauli label. -/
def pauliOperator (g : PauliLabel n) : Matrix (BinaryVector n) (BinaryVector n) ℂ :=
  pauliPhase g.phase • pauliMatrix g.shift g.clock

/-- Multiplication of the concrete labels, with the full mod-four central cocycle. -/
def pauliLabelMul (g h : PauliLabel n) : PauliLabel n :=
  ⟨g.phase + h.phase + 2 * bitLift (binaryDot g.clock h.shift),
    g.shift + h.shift, g.clock + h.clock⟩

def pauliLabelOne (n : ℕ) : PauliLabel n := ⟨0, 0, 0⟩

def pauliLabelInv (g : PauliLabel n) : PauliLabel n :=
  ⟨-g.phase + 2 * bitLift (binaryDot g.clock g.shift), g.shift, g.clock⟩

theorem pauliOperator_labelMul (g h : PauliLabel n) :
    pauliOperator (pauliLabelMul g h) = pauliOperator g * pauliOperator h := by
  simp only [pauliOperator, pauliLabelMul, pauliPhase_add, pauliPhase_two_bitLift,
    Matrix.smul_mul, Matrix.mul_smul, pauliMatrix_mul, smul_smul]
  congr 1
  ring

@[simp] theorem pauliOperator_labelOne :
    pauliOperator (pauliLabelOne n) = 1 := by
  simp [pauliOperator, pauliLabelOne]

theorem pauliOperator_labelInv (g : PauliLabel n) :
    pauliOperator (pauliLabelInv g) = (pauliOperator g)ᴴ := by
  simp only [pauliOperator, pauliLabelInv, pauliPhase_add, pauliPhase_neg,
    pauliPhase_two_bitLift, Matrix.conjTranspose_smul, pauliMatrix_conjTranspose,
    smul_smul]

@[simp] theorem pauliOperator_adjoint_mul_self (g : PauliLabel n) :
    (pauliOperator g)ᴴ * pauliOperator g = 1 := by
  simp only [pauliOperator, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, pauliMatrix_adjoint_mul_self, smul_smul]
  rw [← pauliPhase_neg, ← pauliPhase_add, add_neg_cancel, pauliPhase_zero, one_smul]

@[simp] theorem pauliOperator_mul_adjoint_self (g : PauliLabel n) :
    pauliOperator g * (pauliOperator g)ᴴ = 1 := by
  simp only [pauliOperator, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, pauliMatrix_mul_adjoint_self, smul_smul]
  rw [← pauliPhase_neg, ← pauliPhase_add, neg_add_cancel, pauliPhase_zero, one_smul]

theorem pauliOperator_mem_unitaryGroup (g : PauliLabel n) :
    pauliOperator g ∈ Matrix.unitaryGroup (BinaryVector n) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (pauliOperator_adjoint_mul_self g)


/-- Distinct full phaseful Pauli labels give distinct actual matrices. -/
theorem pauliOperator_injective : Function.Injective (@pauliOperator n) := by
  intro g h hh
  have hs : g.shift = h.shift := by
    by_contra hs
    have he := congrArg (fun M : Matrix (BinaryVector n) (BinaryVector n) ℂ =>
      M g.shift 0) hh
    have hz : pauliPhase g.phase = 0 := by
      simpa [pauliOperator, pauliMatrix, hs] using he
    exact pauliPhase_ne_zero g.phase hz
  have hp : g.phase = h.phase := by
    apply pauliPhase_injective
    have he := congrArg (fun M : Matrix (BinaryVector n) (BinaryVector n) ℂ =>
      M g.shift 0) hh
    simpa [pauliOperator, pauliMatrix, hs] using he
  have hb : g.clock = h.clock := by
    ext i
    apply pauliSign_injective
    apply mul_left_cancel₀ (pauliPhase_ne_zero h.phase)
    have he := congrArg (fun M : Matrix (BinaryVector n) (BinaryVector n) ℂ =>
      M (Pi.single i 1 + g.shift) (Pi.single i 1)) hh
    simpa [pauliOperator, pauliMatrix, hs, hp] using he
  exact PauliLabel.ext hp hs hb

/-- The concrete Pauli group, verified through its faithful matrix representation. -/
instance instGroupPauliLabel : Group (PauliLabel n) where
  mul := pauliLabelMul
  one := pauliLabelOne n
  inv := pauliLabelInv
  mul_assoc g h j := pauliOperator_injective (by
    change pauliOperator (pauliLabelMul (pauliLabelMul g h) j) =
      pauliOperator (pauliLabelMul g (pauliLabelMul h j))
    simp only [pauliOperator_labelMul]
    exact Matrix.mul_assoc _ _ _)
  one_mul g := pauliOperator_injective (by
    change pauliOperator (pauliLabelMul (pauliLabelOne n) g) = pauliOperator g
    rw [pauliOperator_labelMul, pauliOperator_labelOne, Matrix.one_mul])
  mul_one g := pauliOperator_injective (by
    change pauliOperator (pauliLabelMul g (pauliLabelOne n)) = pauliOperator g
    rw [pauliOperator_labelMul, pauliOperator_labelOne, Matrix.mul_one])
  inv_mul_cancel g := pauliOperator_injective (by
    change pauliOperator (pauliLabelMul (pauliLabelInv g) g) = pauliOperator (pauliLabelOne n)
    rw [pauliOperator_labelMul, pauliOperator_labelInv,
      pauliOperator_adjoint_mul_self, pauliOperator_labelOne])

@[simp] theorem pauliOperator_one : pauliOperator (1 : PauliLabel n) = 1 :=
  pauliOperator_labelOne

theorem pauliOperator_mul (g h : PauliLabel n) :
    pauliOperator (g * h) = pauliOperator g * pauliOperator h :=
  pauliOperator_labelMul g h

theorem pauliOperator_inv (g : PauliLabel n) :
    pauliOperator g⁻¹ = (pauliOperator g)ᴴ :=
  pauliOperator_labelInv g

/-- A concrete faithful monoid representation, without an abstract representation hypothesis. -/
def pauliRepresentation (n : ℕ) :
    PauliLabel n →* Matrix (BinaryVector n) (BinaryVector n) ℂ where
  toFun := pauliOperator
  map_one' := pauliOperator_one
  map_mul' := pauliOperator_mul

/-- The same concrete representation with its unitary codomain. -/
def pauliUnitaryRepresentation (n : ℕ) :
    PauliLabel n →* Matrix.unitaryGroup (BinaryVector n) ℂ where
  toFun g := ⟨pauliOperator g, pauliOperator_mem_unitaryGroup g⟩
  map_one' := Subtype.ext pauliOperator_one
  map_mul' g h := Subtype.ext (pauliOperator_mul g h)

theorem pauliUnitaryRepresentation_injective :
    Function.Injective (pauliUnitaryRepresentation n) := by
  intro g h hh
  exact pauliOperator_injective (congrArg Subtype.val hh)


/-- Orthogonality of the actual binary coordinate characters, including n=0. -/
theorem pauliSign_sum (b : BinaryVector n) :
    (∑ y : BinaryVector n, pauliSign (binaryDot b y)) =
      if b = 0 then (2 : ℂ) ^ n else 0 := by
  by_cases hb : b = 0
  · subst b
    simp [BinaryVector, ZMod.card]
  · rw [if_neg hb]
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hb (funext h)
    have hb1 : b i = 1 := by
      have hbit (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
        fin_cases z <;> simp_all
      exact hbit (b i) hi
    have hs : (∑ y : BinaryVector n,
        pauliSign (binaryDot b (Pi.single i 1 + y))) =
        ∑ y : BinaryVector n, pauliSign (binaryDot b y) :=
      Fintype.sum_bijective _ (AddGroup.addLeft_bijective (Pi.single i 1)) _ _ (fun _ => rfl)
    simp_rw [pauliDot_add_right, pauliSign_add] at hs
    rw [pauliDot_single_right, hb1, pauliSign_one, ← Finset.mul_sum] at hs
    exact eq_zero_of_mul_eq_self_left (by norm_num : (-1 : ℂ) ≠ 1) hs

/-- The concrete unphased Pauli trace vanishes except at the identity label. -/
theorem pauliMatrix_trace (a b : BinaryVector n) :
    Matrix.trace (pauliMatrix a b) =
      if a = 0 ∧ b = 0 then (2 : ℂ) ^ n else 0 := by
  by_cases ha : a = 0
  · subst a
    simpa [Matrix.trace, pauliMatrix] using pauliSign_sum b
  · have hx : ∀ x : BinaryVector n, ¬ x = x + a := by
      intro x h
      have hz : (0 : BinaryVector n) = a :=
        add_left_cancel (show x + 0 = x + a by simpa only [add_zero] using h)
      exact ha hz.symm
    simp [Matrix.trace, pauliMatrix, hx, ha]

/-- Full central phases remain visible in the actual Pauli trace. -/
theorem pauliOperator_trace (g : PauliLabel n) :
    Matrix.trace (pauliOperator g) =
      if g.shift = 0 ∧ g.clock = 0 then pauliPhase g.phase * (2 : ℂ) ^ n else 0 := by
  rw [pauliOperator, Matrix.trace_smul, pauliMatrix_trace]
  split_ifs <;> simp [smul_eq_mul]

end ExactCriticalCurve.Quantum
