import StabilizerLearning.Quantum.Pauli
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Algebra and faithfulness of the concrete phases used by the all-prime Pauli section.
The phase formulas are identified with the standard additive character of a cyclic group;
no extra character or phase axioms are assumed. -/
noncomputable section

namespace StabilizerLearning.Quantum

variable (p : ℕ) [NeZero p]

theorem rootPhase_eq_stdAddChar (t : ZMod p) :
    rootPhase p t = ZMod.stdAddChar t := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

@[simp] theorem rootPhase_zero : rootPhase p 0 = 1 := by
  rw [rootPhase_eq_stdAddChar]
  exact AddChar.map_zero_eq_one _

theorem rootPhase_add (s t : ZMod p) :
    rootPhase p (s + t) = rootPhase p s * rootPhase p t := by
  simp only [rootPhase_eq_stdAddChar, AddChar.map_add_eq_mul]

theorem rootPhase_neg (t : ZMod p) :
    rootPhase p (-t) = (rootPhase p t)⁻¹ := by
  simp only [rootPhase_eq_stdAddChar, AddChar.map_neg_eq_inv]

@[simp] theorem norm_rootPhase (t : ZMod p) : ‖rootPhase p t‖ = 1 := by
  rw [rootPhase_eq_stdAddChar, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

omit [NeZero p] in
@[simp] theorem rootPhase_ne_zero (t : ZMod p) : rootPhase p t ≠ 0 :=
  Complex.exp_ne_zero _

theorem rootPhase_star (t : ZMod p) :
    star (rootPhase p t) = rootPhase p (-t) := by
  rw [rootPhase_neg, rootPhase_eq_stdAddChar, ZMod.stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle t)).symm

theorem star_rootPhase (t : ZMod p) :
    star (rootPhase p t) = rootPhase p (-t) := rootPhase_star p t

theorem rootPhase_injective : Function.Injective (rootPhase p) := by
  intro s t h
  exact ZMod.injective_stdAddChar (by simpa only [rootPhase_eq_stdAddChar] using h)

@[simp] theorem rootPhase_eq_one_iff (t : ZMod p) : rootPhase p t = 1 ↔ t = 0 := by
  rw [← rootPhase_zero p, (rootPhase_injective p).eq_iff]

theorem eigenPhase_eq_stdAddChar (t : ZMod (2 * p)) :
    eigenPhase p t = ZMod.stdAddChar t := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  simp only [eigenPhase, Nat.cast_mul, Nat.cast_ofNat]

@[simp] theorem eigenPhase_zero : eigenPhase p 0 = 1 := by
  rw [eigenPhase_eq_stdAddChar]
  exact AddChar.map_zero_eq_one _

theorem eigenPhase_add (s t : ZMod (2 * p)) :
    eigenPhase p (s + t) = eigenPhase p s * eigenPhase p t := by
  simp only [eigenPhase_eq_stdAddChar, AddChar.map_add_eq_mul]

theorem eigenPhase_neg (t : ZMod (2 * p)) :
    eigenPhase p (-t) = (eigenPhase p t)⁻¹ := by
  simp only [eigenPhase_eq_stdAddChar, AddChar.map_neg_eq_inv]

@[simp] theorem norm_eigenPhase (t : ZMod (2 * p)) : ‖eigenPhase p t‖ = 1 := by
  rw [eigenPhase_eq_stdAddChar, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

omit [NeZero p] in
@[simp] theorem eigenPhase_ne_zero (t : ZMod (2 * p)) : eigenPhase p t ≠ 0 :=
  Complex.exp_ne_zero _

theorem eigenPhase_star (t : ZMod (2 * p)) :
    star (eigenPhase p t) = eigenPhase p (-t) := by
  rw [eigenPhase_neg, eigenPhase_eq_stdAddChar, ZMod.stdAddChar_apply]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle t)).symm

theorem eigenPhase_injective : Function.Injective (eigenPhase p) := by
  intro s t h
  exact ZMod.injective_stdAddChar (by simpa only [eigenPhase_eq_stdAddChar] using h)

@[simp] theorem eigenPhase_eq_one_iff (t : ZMod (2 * p)) : eigenPhase p t = 1 ↔ t = 0 := by
  rw [← eigenPhase_zero p, (eigenPhase_injective p).eq_iff]

end StabilizerLearning.Quantum
