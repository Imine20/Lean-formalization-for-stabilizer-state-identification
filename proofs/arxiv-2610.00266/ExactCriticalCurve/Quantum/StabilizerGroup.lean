import ExactCriticalCurve.Quantum.BinaryPauli
import ExactCriticalCurve.Quantum.FiniteGroupProjection
import ExactCriticalCurve.Quantum.PureProjection
import ExactCriticalCurve.Quantum.Finite

/-!
# Actual scalar-free Pauli stabilizer groups

Labels are subgroups of the faithful, phaseful Pauli group. Scalar exclusion and
the cardinality 2^n are the defining algebraic conditions; positivity, trace one,
rank one and the state vector are all proved from the concrete matrices.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum

/-- A maximal Pauli stabilizer group, including the signs of its operators.
No nontrivial scalar Pauli is allowed. The conventional no-minus-identity
formulation and the Clifford orbit characterization are separate bridges. -/
structure StabilizerGroup (n : ℕ) where
  carrier : Subgroup (PauliLabel n)
  phase_free : ∀ g ∈ carrier, g.shift = 0 → g.clock = 0 → g.phase = 0
  card_eq : Nat.card carrier = 2 ^ n

@[ext] theorem StabilizerGroup.ext {n : ℕ} {S T : StabilizerGroup n}
    (h : S.carrier = T.carrier) : S = T := by
  cases S
  cases T
  cases h
  rfl

instance finiteStabilizerGroup (n : ℕ) : Finite (StabilizerGroup n) :=
  Finite.of_injective
    (fun S : StabilizerGroup n => (S.carrier : Set (PauliLabel n))) (by
      intro S T h
      exact StabilizerGroup.ext (SetLike.coe_injective h))

noncomputable instance fintypeStabilizerGroup (n : ℕ) : Fintype (StabilizerGroup n) :=
  Fintype.ofFinite _

noncomputable instance stabilizerCarrierFintype {n : ℕ} (S : StabilizerGroup n) :
    Fintype S.carrier := Fintype.ofFinite _

/-- The representation restricted to the actual subgroup. -/
def StabilizerGroup.representation {n : ℕ} (S : StabilizerGroup n) :
    S.carrier →* unitary (Matrix (BinaryVector n) (BinaryVector n) ℂ) :=
  (pauliUnitaryRepresentation n).comp S.carrier.subtype

/-- The actual Pauli average, with its true subgroup cardinality. -/
def stabilizerProjection {n : ℕ} (S : StabilizerGroup n) :
    Matrix (BinaryVector n) (BinaryVector n) ℂ :=
  finiteGroupProjection S.representation

theorem stabilizerProjection_isHermitian {n : ℕ} (S : StabilizerGroup n) :
    (stabilizerProjection S).IsHermitian :=
  finiteGroupProjection_isHermitian S.representation

theorem stabilizerProjection_idempotent {n : ℕ} (S : StabilizerGroup n) :
    stabilizerProjection S * stabilizerProjection S = stabilizerProjection S :=
  finiteGroupProjection_idempotent S.representation

theorem stabilizerProjection_posSemidef {n : ℕ} (S : StabilizerGroup n) :
    (stabilizerProjection S).PosSemidef :=
  finiteGroupProjection_posSemidef S.representation

/-- Within a scalar-free subgroup, only its identity has nonzero Pauli trace. -/
theorem StabilizerGroup.member_trace {n : ℕ} (S : StabilizerGroup n) (g : S.carrier) :
    Matrix.trace (pauliOperator g.val) = if g = 1 then (2 : ℂ) ^ n else 0 := by
  classical
  by_cases hg : g = 1
  · subst g
    simp [pauliOperator_one, Matrix.trace_one, BinaryVector]
  · rw [if_neg hg, pauliOperator_trace]
    have hn : ¬(g.val.shift = 0 ∧ g.val.clock = 0) := by
      rintro ⟨hs, hc⟩
      apply hg
      apply Subtype.ext
      apply PauliLabel.ext
      · exact S.phase_free g.val g.property hs hc
      · exact hs
      · exact hc
    rw [if_neg hn]

theorem stabilizerProjection_trace_one {n : ℕ} (S : StabilizerGroup n) :
    Matrix.trace (stabilizerProjection S) = 1 := by
  classical
  have hcard : Fintype.card S.carrier = 2 ^ n := by
    simpa only [Nat.card_eq_fintype_card] using S.card_eq
  have hD : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [stabilizerProjection, finiteGroupProjection_trace]
  change (Fintype.card S.carrier : ℂ)⁻¹ *
    ∑ g : S.carrier, Matrix.trace (pauliOperator g.val) = 1
  simp only [S.member_trace]
  rw [Fintype.sum_ite_eq', hcard, Nat.cast_pow, Nat.cast_ofNat, inv_mul_cancel₀ hD]

theorem stabilizerProjection_rank_one {n : ℕ} (S : StabilizerGroup n) :
    (stabilizerProjection S).rank = 1 :=
  rank_eq_one_of_projection_trace_one _ (stabilizerProjection_isHermitian S)
    (stabilizerProjection_idempotent S) (stabilizerProjection_trace_one S)

theorem stabilizerProjection_exists_vector {n : ℕ} (S : StabilizerGroup n) :
    ∃ v : BinaryVector n → ℂ, star v ⬝ᵥ v = 1 ∧
      Matrix.vecMulVec v (star v) = stabilizerProjection S :=
  exists_unit_vector_of_projection_trace_one _ (stabilizerProjection_isHermitian S)
    (stabilizerProjection_idempotent S) (stabilizerProjection_trace_one S)

/-- A gauge choice, made only after proving a normalized vector exists. -/
def stabilizerVector {n : ℕ} (S : StabilizerGroup n) : BinaryVector n → ℂ :=
  (stabilizerProjection_exists_vector S).choose

theorem stabilizerVector_normalized {n : ℕ} (S : StabilizerGroup n) :
    star (stabilizerVector S) ⬝ᵥ stabilizerVector S = 1 :=
  (stabilizerProjection_exists_vector S).choose_spec.1

theorem stabilizerVector_projector {n : ℕ} (S : StabilizerGroup n) :
    Matrix.vecMulVec (stabilizerVector S) (star (stabilizerVector S)) =
      stabilizerProjection S :=
  (stabilizerProjection_exists_vector S).choose_spec.2

/-- The actual subgroup fixes the chosen normalized state vector. -/
theorem stabilizerVector_fixed {n : ℕ} (S : StabilizerGroup n) (g : S.carrier) :
    pauliOperator g.val *ᵥ stabilizerVector S = stabilizerVector S := by
  apply (finiteGroupProjection_mulVec_eq_iff S.representation _).mp ?_ g
  change stabilizerProjection S *ᵥ stabilizerVector S = stabilizerVector S
  rw [← stabilizerVector_projector S, Matrix.vecMulVec_mulVec,
    stabilizerVector_normalized]
  simp

/-- This is a density matrix as a proved consequence of the algebraic subgroup data. -/
def stabilizerDensity {n : ℕ} (S : StabilizerGroup n) : DensityMatrix (BinaryVector n) where
  matrix := stabilizerProjection S
  positive := stabilizerProjection_posSemidef S
  trace_one := stabilizerProjection_trace_one S


/-- Scalar exclusion makes the projective Pauli labels injective on the subgroup. -/
theorem StabilizerGroup.projective_injective {n : ℕ} (S : StabilizerGroup n) :
    Function.Injective (fun g : S.carrier => (g.val.shift, g.val.clock)) := by
  intro g h he
  have hs : g.val.shift = h.val.shift := congrArg Prod.fst he
  have hc : g.val.clock = h.val.clock := congrArg Prod.snd he
  have hmem : g.val * h.val⁻¹ ∈ S.carrier := S.carrier.mul_mem g.property
    (S.carrier.inv_mem h.property)
  have hshift : (g.val * h.val⁻¹).shift = 0 := by
    change g.val.shift + h.val.shift = 0
    rw [hs, pauliVector_add_self]
  have hclock : (g.val * h.val⁻¹).clock = 0 := by
    change g.val.clock + h.val.clock = 0
    rw [hc, pauliVector_add_self]
  have hp : g.val * h.val⁻¹ = 1 :=
    PauliLabel.ext (S.phase_free _ hmem hshift hclock) hshift hclock
  exact Subtype.ext (mul_inv_eq_one.mp hp)

/-- Commutativity follows from scalar exclusion and the concrete Pauli cocycle. -/
theorem StabilizerGroup.mul_comm {n : ℕ} (S : StabilizerGroup n) (g h : S.carrier) :
    g * h = h * g := by
  apply S.projective_injective
  apply Prod.ext
  · change g.val.shift + h.val.shift = h.val.shift + g.val.shift
    exact add_comm _ _
  · change g.val.clock + h.val.clock = h.val.clock + g.val.clock
    exact add_comm _ _

/-- Every member is an involution; no non-Hermitian scalar lifts survive. -/
theorem StabilizerGroup.mul_self {n : ℕ} (S : StabilizerGroup n) (g : S.carrier) :
    g * g = 1 := by
  apply S.projective_injective
  apply Prod.ext
  · change g.val.shift + g.val.shift = 0
    exact pauliVector_add_self _
  · change g.val.clock + g.val.clock = 0
    exact pauliVector_add_self _

/-- The concrete negative identity label retains its full mod-four phase. -/
def pauliMinusIdentity (n : ℕ) : PauliLabel n := ⟨2, 0, 0⟩

theorem pauliMinusIdentity_operator (n : ℕ) :
    pauliOperator (pauliMinusIdentity n) = -(1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) := by
  norm_num [pauliMinusIdentity, pauliOperator, pauliPhase, ZMod.val, Complex.I_sq]

/-- Excluding all nontrivial central phases is equivalent to the conventional
exclusion of minus identity, for an actual subgroup. -/
theorem pauli_scalar_free_iff_minusIdentity_not_mem {n : ℕ}
    (S : Subgroup (PauliLabel n)) :
    (∀ g ∈ S, g.shift = 0 → g.clock = 0 → g.phase = 0) ↔
      pauliMinusIdentity n ∉ S := by
  constructor
  · intro h hm
    have ht := h (pauliMinusIdentity n) hm rfl rfl
    exact (by decide : (2 : ZMod 4) ≠ 0) ht
  · intro hm g hg hs hc
    rcases g with ⟨t, a, b⟩
    change a = 0 at hs
    change b = 0 at hc
    subst a
    subst b
    change t = 0
    have hmul (a : ZMod 4) :
        (⟨a, 0, 0⟩ : PauliLabel n) * ⟨a, 0, 0⟩ = ⟨a + a, 0, 0⟩ := by
      change pauliLabelMul _ _ = _
      apply PauliLabel.ext <;> simp [pauliLabelMul]
    fin_cases t
    · rfl
    · exfalso
      apply hm
      have ht := S.mul_mem hg hg
      rw [hmul] at ht
      exact ht
    · exact (hm hg).elim
    · exfalso
      apply hm
      have ht := S.mul_mem hg hg
      rw [hmul] at ht
      exact ht

theorem StabilizerGroup.minusIdentity_not_mem {n : ℕ} (S : StabilizerGroup n) :
    pauliMinusIdentity n ∉ S.carrier :=
  (pauli_scalar_free_iff_minusIdentity_not_mem S.carrier).mp S.phase_free

end ExactCriticalCurve.Quantum
