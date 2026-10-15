import ExactCriticalCurve.Binary.RelationHalf

noncomputable section
set_option maxHeartbeats 200000
namespace ExactCriticalCurve.Binary
open StochasticCounting

def weightParity (k : ℕ) : BinaryVector k →ₗ[ZMod 2] ZMod 2 :=
  binaryDotForm k (allOnes k)

@[simp] theorem weightParity_apply {k : ℕ} (x : BinaryVector k) :
    weightParity k x = binaryDot (allOnes k) x := rfl

theorem weightParity_self {k : ℕ} (x : BinaryVector k) :
    weightParity k x = binaryDot x x := by
  rw [weightParity_apply, binaryDot_comm, binaryDot_self_eq_dot_allOnes]

@[simp] theorem weightParity_wu (k : ℕ) :
    weightParity k (allOnes k) = (k : ZMod 2) := by
  simp [weightParity, binaryDot, allOnes]

theorem weightParity_corrected_even {k : ℕ} (x : BinaryVector k) :
    (weightQuadratic x - bitLift (weightParity k x)) +
      (weightQuadratic x - bitLift (weightParity k x)) = 0 := by
  have hxx : x + x = 0 := by ext i; exact binaryScalar_add_self _
  have he := weightQuadratic_add x x
  rw [hxx, weightQuadratic_zero, ← weightParity_self] at he
  have hn := two_mul_bitLift_neg (weightParity k x)
  linear_combination -he + hn

def stochasticHalfValue {k : ℕ} (x : BinaryVector k) : ZMod 2 :=
  halfEven (weightQuadratic x - bitLift (weightParity k x))

theorem stochasticHalfValue_reconstruct {k : ℕ} (x : BinaryVector k) :
    2 * bitLift (stochasticHalfValue x) + bitLift (weightParity k x) =
      weightQuadratic x := by
  rw [stochasticHalfValue, two_mul_bitLift_halfEven _ (weightParity_corrected_even x)]
  abel

def stochasticHalfBilinear (k : ℕ) : LinearMap.BilinForm (ZMod 2) (BinaryVector k) :=
  binaryDotForm k + LinearMap.BilinForm.linMulLin (weightParity k) (weightParity k)

@[simp] theorem stochasticHalfBilinear_apply {k : ℕ} (x y : BinaryVector k) :
    stochasticHalfBilinear k x y =
      binaryDot x y + weightParity k x * weightParity k y := rfl

private theorem correctedHalf_add_algebra (a b c p q r d u v : ZMod 4)
    (ha : a + p = u) (hb : b + q = v)
    (hc : c + (p + q + r) = u + v + d) (hr : -r = r) :
    c = a + b + (d + r) := by
  linear_combination hc - ha - hb + hr

theorem stochasticHalfValue_add {k : ℕ} (x y : BinaryVector k) :
    stochasticHalfValue (x+y) = stochasticHalfValue x + stochasticHalfValue y +
      stochasticHalfBilinear k x y := by
  apply two_mul_bitLift_injective
  dsimp only
  rw [two_mul_bitLift_add, two_mul_bitLift_add]
  have hx := stochasticHalfValue_reconstruct x
  have hy := stochasticHalfValue_reconstruct y
  have hxy := stochasticHalfValue_reconstruct (x+y)
  rw [map_add, bitLift_add, weightQuadratic_add] at hxy
  rw [stochasticHalfBilinear_apply, two_mul_bitLift_add]
  have hn := two_mul_bitLift_neg (weightParity k x * weightParity k y)
  exact correctedHalf_add_algebra _ _ _ _ _ _ _ _ _ hx hy hxy hn

def stochasticHalfForm (k : ℕ) : QuadraticForm (ZMod 2) (BinaryVector k) where
  toFun := stochasticHalfValue
  toFun_smul := by
    intro a x
    rcases (show a = (0 : ZMod 2) ∨ a = (1 : ZMod 2) by fin_cases a <;> simp) with rfl | rfl
    · simp only [zero_smul, stochasticHalfValue, map_zero, weightQuadratic_zero,
        bitLift_zero, sub_zero, halfEven_zero, zero_mul]
    · simp only [one_smul, one_mul]
  exists_companion' := ⟨stochasticHalfBilinear k, stochasticHalfValue_add⟩

@[simp] theorem stochasticHalfForm_apply {k : ℕ} (x : BinaryVector k) :
    stochasticHalfForm k x =
      halfEven (weightQuadratic x - bitLift (weightParity k x)) := rfl

theorem stochasticHalfForm_value {k : ℕ} (x : BinaryVector k) :
    stochasticHalfForm k x = stochasticHalfValue x := rfl

theorem stochasticHalfForm_polar (k : ℕ) :
    (stochasticHalfForm k).polarBilin = stochasticHalfBilinear k := by
  apply LinearMap.ext₂
  intro x y
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  simp only [stochasticHalfForm_value]
  rw [stochasticHalfValue_add]
  exact (show ∀ a b c : ZMod 2, a+b+c-a-b=c from by intros; abel) _ _ _

theorem stochasticHalfBilinear_wu {k : ℕ} (hk : (k : ZMod 2) = 0)
    (x : BinaryVector k) :
    stochasticHalfBilinear k (allOnes k) x = weightParity k x := by
  rw [stochasticHalfBilinear_apply, weightParity_wu, hk, zero_mul, add_zero]
  rfl

theorem stochasticHalfBilinear_nondegenerate {k : ℕ} (hk : (k : ZMod 2) = 0) :
    LinearMap.BilinForm.Nondegenerate (stochasticHalfBilinear k) := by
  intro x hx
  have hp : weightParity k x = 0 := by
    have hw := hx (allOnes k)
    rw [stochasticHalfBilinear_apply, weightParity_wu, hk, mul_zero, add_zero] at hw
    exact (binaryDot_comm _ _).trans hw
  apply binaryDotForm_nondegenerate k x
  intro y
  simpa only [stochasticHalfBilinear_apply, hp, zero_mul, add_zero,
    binaryDotForm_apply] using hx y

theorem stochasticHalfForm_nondegenerate {k : ℕ} (hk : (k : ZMod 2) = 0) :
    LinearMap.BilinForm.Nondegenerate (stochasticHalfForm k).polarBilin := by
  rw [stochasticHalfForm_polar]
  exact stochasticHalfBilinear_nondegenerate hk

theorem stochasticHalfForm_wu {k : ℕ} (hk : (k : ZMod 2) = 0) :
    stochasticHalfForm k (allOnes k) = halfEven (k : ZMod 4) := by
  rw [stochasticHalfForm_apply, weightParity_wu, hk, bitLift_zero, sub_zero,
    weightQuadratic_allOnes]

def evenWeightSpace (k : ℕ) : Submodule (ZMod 2) (BinaryVector k) :=
  LinearMap.ker (weightParity k)

@[simp] theorem mem_evenWeightSpace {k : ℕ} (x : BinaryVector k) :
    x ∈ evenWeightSpace k ↔ weightParity k x = 0 := Iff.rfl

def evenWeightHalfForm (k : ℕ) : QuadraticForm (ZMod 2) (evenWeightSpace k) :=
  (stochasticHalfForm k).comp (evenWeightSpace k).subtype

theorem evenWeightHalfForm_apply {k : ℕ} (x : evenWeightSpace k) :
    evenWeightHalfForm k x = halfEven (weightQuadratic x.val) := by
  change halfEven (weightQuadratic x.val - bitLift (weightParity k x.val)) = _
  rw [(mem_evenWeightSpace _).mp x.property, bitLift_zero, sub_zero]

theorem evenWeightHalfForm_polar {k : ℕ} (x y : evenWeightSpace k) :
    (evenWeightHalfForm k).polarBilin x y = binaryDot x.val y.val := by
  rw [evenWeightHalfForm, QuadraticMap.polarBilin_comp, stochasticHalfForm_polar]
  change stochasticHalfBilinear k x.val y.val = _
  rw [stochasticHalfBilinear_apply, (mem_evenWeightSpace _).mp x.property,
    zero_mul, add_zero]

theorem oddWuCorrection_mem {k : ℕ} (hk : (k : ZMod 2) = 1)
    (x : BinaryVector k) : x + (weightParity k x) • allOnes k ∈ evenWeightSpace k := by
  rw [mem_evenWeightSpace, map_add, map_smul, weightParity_wu, hk]
  simpa only [smul_eq_mul, mul_one] using binaryScalar_add_self (weightParity k x)

theorem evenWeightHalfForm_nondegenerate {k : ℕ} (hk : (k : ZMod 2) = 1) :
    LinearMap.BilinForm.Nondegenerate (evenWeightHalfForm k).polarBilin := by
  intro x hx
  apply Subtype.ext
  apply binaryDotForm_nondegenerate k x.val
  intro y
  have h := hx ⟨y + (weightParity k y) • allOnes k, oddWuCorrection_mem hk y⟩
  rw [evenWeightHalfForm_polar] at h
  have hp : binaryDot x.val (allOnes k) = 0 :=
    (binaryDot_comm _ _).trans ((mem_evenWeightSpace _).mp x.property)
  change binaryDotForm k x.val y = 0
  change binaryDotForm k x.val (y + (weightParity k y) • allOnes k) = 0 at h
  rw [map_add, map_smul] at h
  simpa only [binaryDotForm_apply, hp, smul_zero, add_zero] using h

theorem weightQuadratic_eq_iff_half_parity {k : ℕ} (x y : BinaryVector k)
    (hp : weightParity k x = weightParity k y) :
    weightQuadratic x = weightQuadratic y ↔
      stochasticHalfForm k x = stochasticHalfForm k y := by
  constructor
  · intro h; simp only [stochasticHalfForm_apply, hp, h]
  · intro h
    change stochasticHalfValue x = stochasticHalfValue y at h
    rw [← stochasticHalfValue_reconstruct x, ← stochasticHalfValue_reconstruct y, h, hp]

end ExactCriticalCurve.Binary
