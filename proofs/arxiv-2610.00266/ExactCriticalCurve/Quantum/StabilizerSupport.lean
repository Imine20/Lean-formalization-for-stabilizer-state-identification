import ExactCriticalCurve.Quantum.StabilizerGeometry
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-! Exact support of the normalized vector obtained from an actual Pauli subgroup. -/
noncomputable section
open scoped BigOperators
open ExactCriticalCurve.Binary Matrix Classical
namespace ExactCriticalCurve.Quantum

/-- The actual matrix action, evaluated at the translated output coordinate. -/
theorem pauliOperator_mulVec_shift {n : ℕ} (g : PauliLabel n)
    (v : BinaryVector n → ℂ) (x : BinaryVector n) :
    (pauliOperator g *ᵥ v) (x + g.shift) =
      pauliPhase g.phase * pauliSign (binaryDot g.clock x) * v x := by
  classical
  change (∑ y : BinaryVector n,
    (pauliPhase g.phase * (if x + g.shift = y + g.shift
      then pauliSign (binaryDot g.clock y) else 0)) * v y) = _
  simp only [add_left_inj]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

theorem stabilizerVector_translation {n : ℕ} (S : StabilizerGroup n)
    (g : S.carrier) (x : BinaryVector n) :
    stabilizerVector S (x + g.val.shift) =
      pauliPhase g.val.phase * pauliSign (binaryDot g.val.clock x) * stabilizerVector S x := by
  have h := congrFun (stabilizerVector_fixed S g) (x + g.val.shift)
  rw [pauliOperator_mulVec_shift] at h
  exact h.symm

theorem stabilizerVector_translation_ne_zero {n : ℕ} (S : StabilizerGroup n)
    (g : S.carrier) (x : BinaryVector n) :
    stabilizerVector S (x + g.val.shift) ≠ 0 ↔ stabilizerVector S x ≠ 0 := by
  rw [stabilizerVector_translation]
  exact ⟨fun h => (mul_ne_zero_iff.mp h).2,
    fun h => mul_ne_zero (mul_ne_zero (pauliPhase_ne_zero _) (pauliSign_ne_zero _)) h⟩

theorem stabilizerVector_exists_nonzero {n : ℕ} (S : StabilizerGroup n) :
    ∃ a : BinaryVector n, stabilizerVector S a ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  have hn := stabilizerVector_normalized S
  simp [dotProduct, h] at hn

/-- Any two nonzero amplitudes satisfy every actual diagonal Pauli constraint. -/
theorem stabilizerVector_support_diagonal {n : ℕ} (S : StabilizerGroup n)
    (a x : BinaryVector n) (ha : stabilizerVector S a ≠ 0)
    (hx : stabilizerVector S x ≠ 0) (b : BinaryVector n)
    (hb : b ∈ stabilizerDiagonalSpace S) :
    binaryDot b (x + a) = 0 := by
  obtain ⟨g, hg⟩ := hb
  have hs : g.val.shift = 0 := congrArg Prod.fst hg
  have hc : g.val.clock = b := congrArg Prod.snd hg
  have hax := stabilizerVector_translation S g a
  have hxx := stabilizerVector_translation S g x
  rw [hs, hc, add_zero] at hax hxx
  have h₁ : pauliPhase g.val.phase * pauliSign (binaryDot b a) = 1 :=
    mul_right_cancel₀ ha (by simpa using hax.symm)
  have h₂ : pauliPhase g.val.phase * pauliSign (binaryDot b x) = 1 :=
    mul_right_cancel₀ hx (by simpa using hxx.symm)
  have he := pauliSign_injective
    (mul_left_cancel₀ (pauliPhase_ne_zero g.val.phase) (h₂.trans h₁.symm))
  rw [pauliDot_add_right, he]
  have hz (z : ZMod 2) : z + z = 0 := by fin_cases z <;> decide
  exact hz _

theorem binaryOrthogonal_orthogonal {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) : orthogonal (orthogonal L) = L :=
  LinearMap.BilinForm.orthogonal_orthogonal
    (binaryDotForm_nondegenerate n) (binaryDotForm_isRefl n) L

/-- Full support is exactly one affine coset of the actual translation image. -/
theorem stabilizerVector_ne_zero_iff {n : ℕ} (S : StabilizerGroup n)
    (a : BinaryVector n) (ha : stabilizerVector S a ≠ 0) (x : BinaryVector n) :
    stabilizerVector S x ≠ 0 ↔ x + a ∈ stabilizerTranslationSpace S := by
  constructor
  · intro hx
    have hm : x + a ∈ orthogonal (stabilizerDiagonalSpace S) :=
      fun b hb => stabilizerVector_support_diagonal S a x ha hx b hb
    rw [stabilizerDiagonalSpace_eq_orthogonal, binaryOrthogonal_orthogonal] at hm
    exact hm
  · intro hx
    obtain ⟨p, hp, he⟩ := hx
    obtain ⟨g, hg⟩ := hp
    have hshift : g.val.shift = x + a := (congrArg Prod.fst hg).trans he
    have ht := (stabilizerVector_translation_ne_zero S g a).mpr ha
    rw [hshift] at ht
    have hadd : a + (x + a) = x := by
      rw [add_left_comm, pauliVector_add_self, add_zero]
    rwa [hadd] at ht

/-- One support point chosen only after nonvanishing was proved. -/
def stabilizerSupportAnchor {n : ℕ} (S : StabilizerGroup n) : BinaryVector n :=
  (stabilizerVector_exists_nonzero S).choose

theorem stabilizerSupportAnchor_ne_zero {n : ℕ} (S : StabilizerGroup n) :
    stabilizerVector S (stabilizerSupportAnchor S) ≠ 0 :=
  (stabilizerVector_exists_nonzero S).choose_spec

/-- The nonzero support, as an actual nonempty affine subspace. -/
def stabilizerSupport {n : ℕ} (S : StabilizerGroup n) :
    AffineSubspace (ZMod 2) (BinaryVector n) :=
  AffineSubspace.mk' (stabilizerSupportAnchor S) (stabilizerTranslationSpace S)

theorem mem_stabilizerSupport {n : ℕ} (S : StabilizerGroup n) (x : BinaryVector n) :
    x ∈ stabilizerSupport S ↔ stabilizerVector S x ≠ 0 := by
  change x - stabilizerSupportAnchor S ∈ stabilizerTranslationSpace S ↔ _
  have hneg : -(stabilizerSupportAnchor S) = stabilizerSupportAnchor S :=
    (eq_neg_of_add_eq_zero_left (pauliVector_add_self (stabilizerSupportAnchor S))).symm
  rw [sub_eq_add_neg, hneg]
  exact (stabilizerVector_ne_zero_iff S _ (stabilizerSupportAnchor_ne_zero S) x).symm

theorem stabilizerSupport_direction {n : ℕ} (S : StabilizerGroup n) :
    (stabilizerSupport S).direction = stabilizerTranslationSpace S :=
  AffineSubspace.direction_mk' _ _

theorem stabilizerSupport_nonempty {n : ℕ} (S : StabilizerGroup n) :
    Nonempty (stabilizerSupport S) :=
  ⟨⟨stabilizerSupportAnchor S,
    (mem_stabilizerSupport S _).mpr (stabilizerSupportAnchor_ne_zero S)⟩⟩

/-- Translating by the chosen support point enumerates every support point once. -/
def stabilizerSupportEquiv {n : ℕ} (S : StabilizerGroup n) :
    stabilizerTranslationSpace S ≃ stabilizerSupport S where
  toFun t := ⟨t.val + stabilizerSupportAnchor S, by
    rw [mem_stabilizerSupport, stabilizerVector_ne_zero_iff S _
      (stabilizerSupportAnchor_ne_zero S)]
    simpa only [add_assoc, pauliVector_add_self, add_zero] using t.property⟩
  invFun x := ⟨x.val + stabilizerSupportAnchor S,
    (stabilizerVector_ne_zero_iff S _ (stabilizerSupportAnchor_ne_zero S) x.val).mp
      ((mem_stabilizerSupport S x.val).mp x.property)⟩
  left_inv t := by
    apply Subtype.ext
    exact (add_assoc _ _ _).trans (by rw [pauliVector_add_self, add_zero])
  right_inv x := by
    apply Subtype.ext
    exact (add_assoc _ _ _).trans (by rw [pauliVector_add_self, add_zero])

theorem stabilizerSupport_card {n : ℕ} (S : StabilizerGroup n) :
    Nat.card (stabilizerSupport S) =
      2 ^ Module.finrank (ZMod 2) (stabilizerTranslationSpace S) := by
  rw [← Nat.card_congr (stabilizerSupportEquiv S),
    Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp [Nat.card_eq_fintype_card]

theorem pauliPhase_normSq (t : ZMod 4) : Complex.normSq (pauliPhase t) = 1 := by
  simp [pauliPhase, map_pow]

theorem pauliSign_normSq (t : ZMod 2) : Complex.normSq (pauliSign t) = 1 := by
  simp [pauliSign, map_pow]

theorem stabilizerVector_translation_normSq {n : ℕ} (S : StabilizerGroup n)
    (g : S.carrier) (x : BinaryVector n) :
    Complex.normSq (stabilizerVector S (x + g.val.shift)) =
      Complex.normSq (stabilizerVector S x) := by
  rw [stabilizerVector_translation, Complex.normSq_mul, Complex.normSq_mul,
    pauliPhase_normSq, pauliSign_normSq, one_mul, one_mul]

/-- All nonzero amplitudes have exactly the same squared modulus. -/
theorem stabilizerVector_normSq_eq {n : ℕ} (S : StabilizerGroup n)
    (a x : BinaryVector n) (ha : stabilizerVector S a ≠ 0)
    (hx : stabilizerVector S x ≠ 0) :
    Complex.normSq (stabilizerVector S x) = Complex.normSq (stabilizerVector S a) := by
  obtain ⟨p, hp, he⟩ := (stabilizerVector_ne_zero_iff S a ha x).mp hx
  obtain ⟨g, hg⟩ := hp
  have hshift : g.val.shift = x + a := (congrArg Prod.fst hg).trans he
  have ht := stabilizerVector_translation_normSq S g a
  rw [hshift, add_left_comm, pauliVector_add_self, add_zero] at ht
  exact ht

theorem stabilizerVector_sum_normSq {n : ℕ} (S : StabilizerGroup n) :
    (∑ x, Complex.normSq (stabilizerVector S x)) = 1 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  exact stabilizerVector_normalized S

/-- The normalization constant is derived from the actual support cardinality. -/
theorem stabilizerVector_anchor_normSq {n : ℕ} (S : StabilizerGroup n) :
    Complex.normSq (stabilizerVector S (stabilizerSupportAnchor S)) =
      ((2 : ℝ) ^ Module.finrank (ZMod 2) (stabilizerTranslationSpace S))⁻¹ := by
  classical
  have hc : Fintype.card (stabilizerSupport S) =
      2 ^ Module.finrank (ZMod 2) (stabilizerTranslationSpace S) := by
    simpa only [Nat.card_eq_fintype_card] using stabilizerSupport_card S
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun x => x ∈ stabilizerSupport S)
    (fun x => Complex.normSq (stabilizerVector S x))
  have hz : (∑ x : {x // x ∉ stabilizerSupport S},
      Complex.normSq (stabilizerVector S x.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hn : stabilizerVector S x.val = 0 := by
      by_contra hn
      exact x.property ((mem_stabilizerSupport S x.val).mpr hn)
    rw [hn, map_zero]
  have he : (∑ x : stabilizerSupport S, Complex.normSq (stabilizerVector S x.val)) =
      (Fintype.card (stabilizerSupport S) : ℝ) *
        Complex.normSq (stabilizerVector S (stabilizerSupportAnchor S)) := by
    calc
      _ = ∑ _x : stabilizerSupport S,
          Complex.normSq (stabilizerVector S (stabilizerSupportAnchor S)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact stabilizerVector_normSq_eq S _ _ (stabilizerSupportAnchor_ne_zero S)
          ((mem_stabilizerSupport S x.val).mp x.property)
      _ = _ := by simp
  rw [hz, add_zero, he, hc, stabilizerVector_sum_normSq] at hs
  rw [← one_div]
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).mpr
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hs

/-- The physical probability distribution is uniform on its full affine support. -/
theorem stabilizerVector_normSq {n : ℕ} (S : StabilizerGroup n) (x : BinaryVector n) :
    Complex.normSq (stabilizerVector S x) =
      if x ∈ stabilizerSupport S then
        ((2 : ℝ) ^ Module.finrank (ZMod 2) (stabilizerTranslationSpace S))⁻¹ else 0 := by
  classical
  by_cases hx : x ∈ stabilizerSupport S
  · rw [if_pos hx, stabilizerVector_normSq_eq S _ _
      (stabilizerSupportAnchor_ne_zero S) ((mem_stabilizerSupport S x).mp hx)]
    exact stabilizerVector_anchor_normSq S
  · have hz : stabilizerVector S x = 0 := by
      by_contra hz
      exact hx ((mem_stabilizerSupport S x).mpr hz)
    rw [if_neg hx, hz, map_zero]

end ExactCriticalCurve.Quantum
