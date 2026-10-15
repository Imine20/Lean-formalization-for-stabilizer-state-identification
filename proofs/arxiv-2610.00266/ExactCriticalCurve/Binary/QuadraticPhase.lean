import ExactCriticalCurve.Binary.Quadratic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Explicit binary quadratic phases with values in ZMod 4

The linear coefficients retain all four phases; off-diagonal quadratic
coefficients are binary. This module proves their actual coordinate algebra.
-/
noncomputable section
open scoped BigOperators
open Classical
namespace ExactCriticalCurve.Binary

abbrev PhasePair (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}
abbrev QuadraticPhaseData (m : ℕ) :=
  (Fin m → ZMod 4) × (PhasePair m → ZMod 2)

def phaseParity : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

def quadraticPhaseValue {m : ℕ} (q : QuadraticPhaseData m) (z : BinaryVector m) : ZMod 4 :=
  ∑ i, q.1 i * bitLift (z i) +
    2 * ∑ p : PhasePair m, bitLift (q.2 p) * bitLift (z p.val.1) * bitLift (z p.val.2)

def quadraticPhaseCross {m : ℕ} (b : PhasePair m → ZMod 2)
    (i j : Fin m) : ZMod 2 :=
  if h : i < j then b ⟨(i, j), h⟩ else
    if h : j < i then b ⟨(j, i), h⟩ else 0

@[simp] theorem quadraticPhaseValue_zero {m : ℕ} (q : QuadraticPhaseData m) :
    quadraticPhaseValue q 0 = 0 := by
  simp [quadraticPhaseValue]

@[simp] theorem quadraticPhaseCross_self {m : ℕ} (b : PhasePair m → ZMod 2)
    (i : Fin m) : quadraticPhaseCross b i i = 0 := by
  simp [quadraticPhaseCross]

theorem quadraticPhaseCross_of_lt {m : ℕ} (b : PhasePair m → ZMod 2)
    (i j : Fin m) (h : i < j) : quadraticPhaseCross b i j = b ⟨(i, j), h⟩ := by
  simp [quadraticPhaseCross, h]

theorem quadraticPhaseCross_symm {m : ℕ} (b : PhasePair m → ZMod 2)
    (i j : Fin m) : quadraticPhaseCross b i j = quadraticPhaseCross b j i := by
  rcases lt_trichotomy i j with h | h | h
  · simp [quadraticPhaseCross, h, not_lt.mpr (le_of_lt h)]
  · subst j; rfl
  · simp [quadraticPhaseCross, h, not_lt.mpr (le_of_lt h)]

theorem phase_linear_flip (c : ZMod 4) (z : ZMod 2) :
    c * bitLift (z + 1) - c * bitLift z =
      c + 2 * bitLift (phaseParity c * z) := by
  fin_cases c <;> fin_cases z <;> decide

theorem phase_pair_flip (b x y : ZMod 2) :
    (2 : ZMod 4) * bitLift b * bitLift (x + 1) * bitLift y -
      2 * bitLift b * bitLift x * bitLift y = 2 * bitLift (b * y) := by
  fin_cases b <;> fin_cases x <;> fin_cases y <;> decide

/-- The ordered-pair sum incident to a coordinate is the symmetric coefficient row. -/
theorem quadraticPhase_incident_sum {m : ℕ} (b : PhasePair m → ZMod 2)
    (z : BinaryVector m) (j : Fin m) :
    (∑ p : PhasePair m,
      if p.val.1 = j then (2 : ZMod 4) * bitLift (b p * z p.val.2)
      else if p.val.2 = j then 2 * bitLift (b p * z p.val.1) else 0) =
    ∑ l ∈ Finset.univ.erase j, (2 : ZMod 4) * bitLift (quadraticPhaseCross b j l * z l) := by
  let s : Finset (PhasePair m) := Finset.univ.filter (fun p => p.val.1 = j ∨ p.val.2 = j)
  have hfilter :
      (∑ p : PhasePair m,
        if p.val.1 = j then (2 : ZMod 4) * bitLift (b p * z p.val.2)
        else if p.val.2 = j then 2 * bitLift (b p * z p.val.1) else 0) =
      ∑ p ∈ s, (2 : ZMod 4) * bitLift (b p * z (if p.val.1 = j then p.val.2 else p.val.1)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.val.1 = j <;> by_cases h' : p.val.2 = j <;> simp [h, h']
  rw [hfilter]
  refine Finset.sum_bij
    (fun p _ => if p.val.1 = j then p.val.2 else p.val.1) ?_ ?_ ?_ ?_
  · intro p hp
    have hh : p.val.1 = j ∨ p.val.2 = j := (Finset.mem_filter.mp hp).2
    have hlt := p.property
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    split_ifs with h <;> omega
  · intro p hp q hq he
    have hpj : p.val.1 = j ∨ p.val.2 = j := (Finset.mem_filter.mp hp).2
    have hqj : q.val.1 = j ∨ q.val.2 = j := (Finset.mem_filter.mp hq).2
    have hp' := p.property
    have hq' := q.property
    dsimp only at he
    apply Subtype.ext
    apply Prod.ext <;> split_ifs at he <;> omega
  · intro l hl
    have hne : l ≠ j := (Finset.mem_erase.mp hl).1
    by_cases h : j < l
    · refine ⟨⟨(j, l), h⟩, ?_, ?_⟩
      · simp [s]
      · simp
    · have h' : l < j := lt_of_le_of_ne (le_of_not_gt h) hne
      refine ⟨⟨(l, j), h'⟩, ?_, ?_⟩
      · simp [s]
      · simp [hne]
  · intro p hp
    have hpj : p.val.1 = j ∨ p.val.2 = j := (Finset.mem_filter.mp hp).2
    have hlt := p.property
    by_cases h : p.val.1 = j
    · have hj : j < p.val.2 := by omega
      simp only [if_pos h]
      rw [quadraticPhaseCross_of_lt _ _ _ hj]
      congr 3
      apply congrArg b
      apply Subtype.ext
      exact Prod.ext h rfl
    · have h' : p.val.2 = j := hpj.resolve_left h
      have hj : p.val.1 < j := by omega
      simp only [if_neg h]
      rw [quadraticPhaseCross_symm, quadraticPhaseCross_of_lt _ _ _ hj]
      congr 3
      apply congrArg b
      apply Subtype.ext
      exact Prod.ext rfl h'


theorem phase_pair_flip_right (b x y : ZMod 2) :
    (2 : ZMod 4) * bitLift b * bitLift x * bitLift (y + 1) -
      2 * bitLift b * bitLift x * bitLift y = 2 * bitLift (b * x) := by
  have h := phase_pair_flip b y x
  convert h using 1; ring

theorem quadraticPhase_linear_difference {m : ℕ} (c : Fin m → ZMod 4)
    (z : BinaryVector m) (j i : Fin m) :
    c i * bitLift ((z + (Pi.single j (1 : ZMod 2) : BinaryVector m)) i) - c i * bitLift (z i) =
      if i = j then c j + 2 * bitLift (phaseParity (c j) * z j) else 0 := by
  by_cases h : i = j
  · subst i
    simpa using phase_linear_flip (c j) (z j)
  · simp [h]

theorem quadraticPhase_pair_difference {m : ℕ} (b : PhasePair m → ZMod 2)
    (z : BinaryVector m) (j : Fin m) (p : PhasePair m) :
    (2 : ZMod 4) *
      (bitLift (b p) * bitLift ((z + (Pi.single j (1 : ZMod 2) : BinaryVector m)) p.val.1) *
          bitLift ((z + (Pi.single j (1 : ZMod 2) : BinaryVector m)) p.val.2) -
       bitLift (b p) * bitLift (z p.val.1) * bitLift (z p.val.2)) =
      if p.val.1 = j then 2 * bitLift (b p * z p.val.2)
      else if p.val.2 = j then 2 * bitLift (b p * z p.val.1) else 0 := by
  have hlt := p.property
  by_cases h1 : p.val.1 = j
  · have h2 : p.val.2 ≠ j := by omega
    simpa [Pi.add_apply, Pi.single_apply, h1, h2, Ne.symm h2,
      mul_sub, ← mul_assoc] using phase_pair_flip (b p) (z j) (z p.val.2)
  · by_cases h2 : p.val.2 = j
    · simpa [Pi.add_apply, Pi.single_apply, h1, h2, Ne.symm h1,
        mul_sub, ← mul_assoc] using phase_pair_flip_right (b p) (z p.val.1) (z j)
    · simp [Pi.add_apply, h1, h2]

/-- The exact mod-four coordinate difference, including the parity of the linear coefficient. -/
theorem quadraticPhaseValue_difference {m : ℕ} (q : QuadraticPhaseData m)
    (z : BinaryVector m) (j : Fin m) :
    quadraticPhaseValue q (z + (Pi.single j (1 : ZMod 2) : BinaryVector m)) - quadraticPhaseValue q z =
      q.1 j + 2 * bitLift (phaseParity (q.1 j) * z j +
        ∑ l ∈ Finset.univ.erase j, quadraticPhaseCross q.2 j l * z l) := by
  unfold quadraticPhaseValue
  rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← mul_sub,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [quadraticPhase_linear_difference, quadraticPhase_pair_difference]
  rw [Finset.sum_ite_eq', quadraticPhase_incident_sum,
    ← two_mul_bitLift_sum, two_mul_bitLift_add]
  simp only [Finset.mem_univ, if_true]
  ring


/-- The actual symmetric binary polarization, including linear-coefficient parity. -/
def quadraticPhasePolar {m : ℕ} (q : QuadraticPhaseData m)
    (z w : BinaryVector m) : ZMod 2 :=
  ∑ i, phaseParity (q.1 i) * z i * w i +
    ∑ p : PhasePair m, q.2 p * (z p.val.1 * w p.val.2 + z p.val.2 * w p.val.1)

theorem phase_linear_add (c : ZMod 4) (x y : ZMod 2) :
    c * bitLift (x + y) =
      c * bitLift x + c * bitLift y + 2 * bitLift (phaseParity c * x * y) := by
  fin_cases c <;> fin_cases x <;> fin_cases y <;> decide

theorem phase_pair_add (b x y u v : ZMod 2) :
    (2 : ZMod 4) * (bitLift b * bitLift (x + u) * bitLift (y + v)) =
      2 * (bitLift b * bitLift x * bitLift y) +
      2 * (bitLift b * bitLift u * bitLift v) +
      2 * bitLift (b * (x * v + y * u)) := by
  fin_cases b <;> fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;> decide

theorem quadraticPhaseValue_add {m : ℕ} (q : QuadraticPhaseData m)
    (z w : BinaryVector m) :
    quadraticPhaseValue q (z + w) =
      quadraticPhaseValue q z + quadraticPhaseValue q w +
        2 * bitLift (quadraticPhasePolar q z w) := by
  have hl : (∑ i, q.1 i * bitLift ((z + w) i)) =
      (∑ i, q.1 i * bitLift (z i)) + (∑ i, q.1 i * bitLift (w i)) +
        2 * bitLift (∑ i, phaseParity (q.1 i) * z i * w i) := by
    simp_rw [Pi.add_apply, phase_linear_add, Finset.sum_add_distrib, two_mul_bitLift_sum]
  have hp : (2 : ZMod 4) * (∑ p : PhasePair m,
      bitLift (q.2 p) * bitLift ((z + w) p.val.1) * bitLift ((z + w) p.val.2)) =
      2 * (∑ p : PhasePair m, bitLift (q.2 p) * bitLift (z p.val.1) * bitLift (z p.val.2)) +
      2 * (∑ p : PhasePair m, bitLift (q.2 p) * bitLift (w p.val.1) * bitLift (w p.val.2)) +
      2 * bitLift (∑ p : PhasePair m,
        q.2 p * (z p.val.1 * w p.val.2 + z p.val.2 * w p.val.1)) := by
    simp_rw [Pi.add_apply, Finset.mul_sum, phase_pair_add, Finset.sum_add_distrib,
      two_mul_bitLift_sum]
  unfold quadraticPhaseValue quadraticPhasePolar
  rw [hl, hp, two_mul_bitLift_add]
  ring

theorem quadraticPhasePolar_symm {m : ℕ} (q : QuadraticPhaseData m)
    (z w : BinaryVector m) :
    quadraticPhasePolar q z w = quadraticPhasePolar q w z := by
  unfold quadraticPhasePolar
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem quadraticPhasePolar_add_left {m : ℕ} (q : QuadraticPhaseData m)
    (x y z : BinaryVector m) :
    quadraticPhasePolar q (x + y) z = quadraticPhasePolar q x z + quadraticPhasePolar q y z := by
  simp only [quadraticPhasePolar, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem quadraticPhasePolar_smul_left {m : ℕ} (q : QuadraticPhaseData m)
    (a : ZMod 2) (z w : BinaryVector m) :
    quadraticPhasePolar q (a • z) w = a • quadraticPhasePolar q z w := by
  fin_cases a
  · simp [quadraticPhasePolar]
  · simp

/-- The concrete coordinate expression bundled as a bilinear form. -/
def quadraticPhasePolarForm {m : ℕ} (q : QuadraticPhaseData m) :
    LinearMap.BilinForm (ZMod 2) (BinaryVector m) :=
  LinearMap.mk₂ (ZMod 2) (quadraticPhasePolar q)
    (quadraticPhasePolar_add_left q) (quadraticPhasePolar_smul_left q)
    (by intro x y z; rw [quadraticPhasePolar_symm, quadraticPhasePolar_add_left,
      quadraticPhasePolar_symm q y x, quadraticPhasePolar_symm q z x])
    (by intro a x y; rw [quadraticPhasePolar_symm, quadraticPhasePolar_smul_left,
      quadraticPhasePolar_symm])

theorem quadraticPhasePolarForm_apply {m : ℕ} (q : QuadraticPhaseData m)
    (z w : BinaryVector m) :
    quadraticPhasePolarForm q z w = quadraticPhasePolar q z w := rfl

theorem quadraticPhasePolarForm_isSymm {m : ℕ} (q : QuadraticPhaseData m) :
    (quadraticPhasePolarForm q).IsSymm :=
  ⟨quadraticPhasePolar_symm q⟩


@[simp] theorem quadraticPhaseValue_single {m : ℕ} (q : QuadraticPhaseData m)
    (i : Fin m) :
    quadraticPhaseValue q (Pi.single i 1) = q.1 i := by
  simpa using quadraticPhaseValue_difference q 0 i

theorem quadraticPhaseValue_single_add_single {m : ℕ} (q : QuadraticPhaseData m)
    (i j : Fin m) (hij : i < j) :
    quadraticPhaseValue q (Pi.single i 1 + Pi.single j 1) =
      q.1 i + q.1 j + 2 * bitLift (q.2 ⟨(i, j), hij⟩) := by
  have h := quadraticPhaseValue_difference q (Pi.single i 1) j
  have hc : quadraticPhaseCross q.2 j i = q.2 ⟨(i, j), hij⟩ := by
    rw [quadraticPhaseCross_symm, quadraticPhaseCross_of_lt _ _ _ hij]
  simp [Pi.single_apply, hij.ne, Ne.symm hij.ne, hc] at h
  calc
    _ = (q.1 j + 2 * bitLift (q.2 ⟨(i, j), hij⟩)) + q.1 i :=
      (sub_eq_iff_eq_add).mp h
    _ = _ := by ring

theorem doubled_bitLift_injective :
    Function.Injective (fun b : ZMod 2 => (2 : ZMod 4) * bitLift b) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | contradiction

/-- The actual coefficient data are recovered by one- and two-coordinate evaluations. -/
theorem quadraticPhaseValue_injective {m : ℕ} :
    Function.Injective (@quadraticPhaseValue m) := by
  intro q r h
  have hc : q.1 = r.1 := by
    funext i
    simpa using congrFun h (Pi.single i 1)
  apply Prod.ext hc
  funext p
  apply doubled_bitLift_injective
  have hp := congrFun h (Pi.single p.val.1 1 + Pi.single p.val.2 1)
  rw [quadraticPhaseValue_single_add_single q _ _ p.property,
    quadraticPhaseValue_single_add_single r _ _ p.property, hc] at hp
  exact add_left_cancel hp

/-- On the binary cube, a value at zero and all actual coordinate differences determine a function. -/
theorem binary_function_eq_of_single_differences {m : ℕ}
    (f g : BinaryVector m → ZMod 4) (hzero : f 0 = g 0)
    (hdiff : ∀ z : BinaryVector m, ∀ j : Fin m,
      f (z + Pi.single j 1) - f z = g (z + Pi.single j 1) - g z) :
    f = g := by
  have hstep (z : BinaryVector m) (j : Fin m) :
      f (z + Pi.single j 1) - g (z + Pi.single j 1) = f z - g z := by
    linear_combination hdiff z j
  funext z
  have hsum (s : Finset (Fin m)) :
      f (∑ i ∈ s, Pi.single i (z i)) - g (∑ i ∈ s, Pi.single i (z i)) =
        f 0 - g 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hbit (t : ZMod 2) : t = 0 ∨ t = 1 := by
        fin_cases t
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hbit (z i) with hb | hb
      · simpa only [hb, Pi.single_zero, zero_add] using ih
      · rw [hb, add_comm]
        exact (hstep _ i).trans ih
  have h := hsum Finset.univ
  rw [Finset.univ_sum_single, hzero, sub_self] at h
  exact sub_eq_zero.mp h

/-- General function recovery; callers must prove the displayed coordinate equations. -/
theorem quadraticPhaseValue_unique {m : ℕ} (q : QuadraticPhaseData m)
    (f : BinaryVector m → ZMod 4) (hzero : f 0 = 0)
    (hdiff : ∀ z : BinaryVector m, ∀ j : Fin m,
      f (z + Pi.single j 1) - f z =
        q.1 j + 2 * bitLift (phaseParity (q.1 j) * z j +
          ∑ l ∈ Finset.univ.erase j, quadraticPhaseCross q.2 j l * z l)) :
    f = quadraticPhaseValue q :=
  binary_function_eq_of_single_differences f (quadraticPhaseValue q)
    (hzero.trans (quadraticPhaseValue_zero q).symm)
    (fun z j => (hdiff z j).trans (quadraticPhaseValue_difference q z j).symm)

end ExactCriticalCurve.Binary
