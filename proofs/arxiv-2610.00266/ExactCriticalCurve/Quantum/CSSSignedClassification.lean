import ExactCriticalCurve.Foundations.BinaryOrthonormalBasis
import ExactCriticalCurve.Quantum.CSSQuotientGeometry
import ExactCriticalCurve.Binary.MixedSignature

/-! Ordinary CSS quotients have actual signed-Hamming coordinates.
The coordinate isomorphism is constructed from a proved binary orthonormal
basis; its refinement, pairing and Wu-vector identities are all conclusions.
No Clifford action, representation equivalence or Witt extension is asserted.
-/

noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve
open Binary

theorem binaryOrthonormalBasis_pairing_right
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ}
    (B : LinearMap.BilinForm (ZMod 2) V) (b : Basis (Fin m) (ZMod 2) V)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (i : Fin m) (x : V) : B (b i) x = b.equivFun x i := by
  change B (b i) x = b.repr x i
  calc
    B (b i) x = B (b i) (∑ j, b.repr x j • b j) :=
      congrArg (fun y => B (b i) y) (b.sum_repr x).symm
    _ = b.repr x i := by
      simp only [map_sum, map_smul, hb, smul_eq_mul]
      simp

theorem binaryOrthonormalBasis_pairing
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ}
    (B : LinearMap.BilinForm (ZMod 2) V) (b : Basis (Fin m) (ZMod 2) V)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (x y : V) : B x y = binaryDot (b.equivFun x) (b.equivFun y) := by
  calc
    B x y = B (∑ i, b.repr x i • b i) y :=
      congrArg (fun z => B z y) (b.sum_repr x).symm
    _ = binaryDot (b.equivFun x) (b.equivFun y) := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        binaryOrthonormalBasis_pairing_right B b hb, binaryDot, Basis.equivFun_apply,
        smul_eq_mul]

/-- Orthogonal binary summands have no mod-four polarization correction. -/
theorem binaryRefinement_sum_basis
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {m : ℕ}
    (B : LinearMap.BilinForm (ZMod 2) V) (b : Basis (Fin m) (ZMod 2) V)
    (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (q : V → ZMod 4) (hq0 : q 0 = 0)
    (hqa : ∀ x y, q (x+y) = q x + q y + 2 * bitLift (B x y))
    (c : Fin m → ZMod 2) (s : Finset (Fin m)) :
    q (∑ i ∈ s, c i • b i) = ∑ i ∈ s, bitLift (c i) * q (b i) := by
  have hscalar (a : ZMod 2) (x : V) : q (a • x) = bitLift a * q x := by
    fin_cases a
    · change q (0 • x) = bitLift 0 * q x
      rw [zero_smul, hq0, bitLift_zero, zero_mul]
    · change q ((1 : ZMod 2) • x) = bitLift 1 * q x
      rw [one_smul, bitLift_one, one_mul]
  induction s using Finset.induction_on with
  | empty => simp [hq0]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, hqa, ih, Finset.sum_insert hi, hscalar]
    have hcross : B (c i • b i) (∑ j ∈ s, c j • b j) = 0 := by
      rw [map_smul, LinearMap.smul_apply, map_sum]
      have hz : (∑ j ∈ s, B (b i) (c j • b j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [map_smul, hb, if_neg (by intro he; exact hi (he ▸ hj)), smul_zero]
      rw [hz, smul_zero]
    rw [hcross, bitLift_zero, mul_zero, add_zero]

namespace Quantum

set_option maxHeartbeats 800000 in
/-- Actual signed coordinates for every ordinary defect quotient. -/
theorem ordinaryCSSQuotient_signed_coordinates {k r : ℕ} (N : OrdinaryDefect k r) :
    ∃ (mask : Fin (Module.finrank (ZMod 2) (CSSQuotient N.val)) → Bool)
      (e : CSSQuotient N.val ≃ₗ[ZMod 2]
        BinaryVector (Module.finrank (ZMod 2) (CSSQuotient N.val))),
      (∀ x, cssQuotientQuadratic N.val N.property.1 x = signedWeightQuadratic mask (e x)) ∧
      (∀ x y, cssQuotientBilinear N.val x y = binaryDot (e x) (e y)) ∧
      e (cssQuotientWu N.val N.property.1) =
        allOnes (Module.finrank (ZMod 2) (CSSQuotient N.val)) := by
  let B := cssQuotientBilinear N.val
  let q := cssQuotientQuadratic N.val N.property.1
  let w := cssQuotientWu N.val N.property.1
  obtain ⟨b, hb⟩ := exists_binaryOrthonormalBasis B
    ⟨cssQuotientBilinear_symm N.val⟩ (cssQuotientBilinear_nondegenerate N.val)
    w (cssQuotientWu_characteristic N.val N.property.1)
    (Or.inl (ordinaryCSSQuotient_wu_ne_zero N))
  let mask : Fin (Module.finrank (ZMod 2) (CSSQuotient N.val)) → Bool :=
    fun i => decide (q (b i) = 3)
  have hq0 : q 0 = 0 := cssQuotientQuadratic_zero N.val N.property.1
  have hqa : ∀ x y, q (x+y) = q x + q y + 2 * bitLift (B x y) :=
    cssQuotientQuadratic_add N.val N.property.1
  have hunit (i) : q (b i) = 1 ∨ q (b i) = 3 := by
    have he : b i + b i = 0 := by
      have h : (1 + 1 : ZMod 2) = 0 := by decide
      simpa only [add_smul, one_smul, zero_smul] using
        congrArg (fun a : ZMod 2 => a • b i) h
    have h := hqa (b i) (b i)
    rw [he, hq0, hb i i, if_pos rfl, bitLift_one] at h
    have hfinite : ∀ z : ZMod 4, 0 = z + z + 2 * 1 → z = 1 ∨ z = 3 := by decide
    exact hfinite (q (b i)) h
  have hmask (i) : q (b i) = if mask i then -1 else 1 := by
    change q (b i) = if decide (q (b i) = 3) then -1 else 1
    rcases hunit i with h | h <;> rw [h] <;> decide
  refine ⟨mask, b.equivFun, ?_, ?_, ?_⟩
  · intro x
    change q x = signedWeightQuadratic mask (b.equivFun x)
    have hs := binaryRefinement_sum_basis B b hb q hq0 hqa (b.equivFun x) Finset.univ
    have hre : (∑ i, b.equivFun x i • b i) = x := b.sum_equivFun x
    rw [hre] at hs
    rw [hs]
    unfold signedWeightQuadratic
    apply Finset.sum_congr rfl
    intro i _
    rw [hmask i]
    cases mask i <;> simp
  · exact binaryOrthonormalBasis_pairing B b hb
  · funext i
    change b.equivFun w i = 1
    rw [← binaryOrthonormalBasis_pairing_right B b hb]
    change cssQuotientBilinear N.val (b i) w = 1
    rw [← cssQuotientWu_characteristic N.val N.property.1 (b i)]
    exact (hb i i).trans (if_pos rfl)

/-- The coordinate count is exactly k minus twice the actual ordinary defect rank. -/
theorem ordinaryCSSQuotient_signed_dimension {k r : ℕ} (N : OrdinaryDefect k r) :
    Module.finrank (ZMod 2) (CSSQuotient N.val) = k - 2 * r := by
  rw [cssQuotient_finrank N.val N.property.1, N.property.2.1]

end Quantum
end ExactCriticalCurve
