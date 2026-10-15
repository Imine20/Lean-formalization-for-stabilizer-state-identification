import ExactCriticalCurve.Quantum.StabilizerGroup
import ExactCriticalCurve.Binary.Geometry
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The actual binary label space of a signed Pauli stabilizer group.
The central phases are retained by the inverse label map; they are not discarded
from the ensemble labels. -/
noncomputable section
open scoped BigOperators
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

/-- The binary shift/clock image of the actual scalar-free subgroup. -/
def stabilizerLabelSpace {n : ℕ} (S : StabilizerGroup n) :
    Submodule (ZMod 2) (BinaryVector n × BinaryVector n) where
  carrier := {p | ∃ g : S.carrier, (g.val.shift, g.val.clock) = p}
  zero_mem' := ⟨1, rfl⟩
  add_mem' := by
    rintro p q ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, rfl⟩
  smul_mem' := by
    intro a p hp
    fin_cases a
    · change ∃ g : S.carrier, (g.val.shift, g.val.clock) = (0 : ZMod 2) • p
      rw [zero_smul]
      exact ⟨1, rfl⟩
    · change ∃ g : S.carrier, (g.val.shift, g.val.clock) = (1 : ZMod 2) • p
      rw [one_smul]
      exact hp

@[simp] theorem mem_stabilizerLabelSpace {n : ℕ} (S : StabilizerGroup n)
    (p : BinaryVector n × BinaryVector n) :
    p ∈ stabilizerLabelSpace S ↔ ∃ g : S.carrier, (g.val.shift, g.val.clock) = p := Iff.rfl

/-- Every binary label in this space has exactly one actual phaseful lift in S. -/
def stabilizerLabelEquiv {n : ℕ} (S : StabilizerGroup n) :
    S.carrier ≃ stabilizerLabelSpace S :=
  Equiv.ofBijective (fun g => ⟨(g.val.shift, g.val.clock), g, rfl⟩) (by
    constructor
    · intro g h he
      exact S.projective_injective (congrArg Subtype.val he)
    · intro p
      obtain ⟨g, hg⟩ := p.property
      exact ⟨g, Subtype.ext hg⟩)

theorem stabilizerLabelSpace_card {n : ℕ} (S : StabilizerGroup n) :
    Nat.card (stabilizerLabelSpace S) = 2 ^ n := by
  rw [← Nat.card_congr (stabilizerLabelEquiv S)]
  exact S.card_eq

theorem stabilizerLabelSpace_finrank {n : ℕ} (S : StabilizerGroup n) :
    Module.finrank (ZMod 2) (stabilizerLabelSpace S) = n := by
  have h := stabilizerLabelSpace_card S
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at h
  have htwo : Nat.card (ZMod 2) = 2 := by simp [Nat.card_eq_fintype_card]
  rw [htwo] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) h

/-- Equality of the doubled bit lifts retains the binary value. -/
theorem two_bitLift_injective : Function.Injective (fun b : ZMod 2 => (2 : ZMod 4) * bitLift b) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | contradiction

/-- The actual binary commutator vanishes on the stabilizer label space. -/
theorem stabilizerLabelSpace_isotropic {n : ℕ} (S : StabilizerGroup n)
    (p q : BinaryVector n × BinaryVector n)
    (hp : p ∈ stabilizerLabelSpace S) (hq : q ∈ stabilizerLabelSpace S) :
    binaryDot p.2 q.1 + binaryDot q.2 p.1 = 0 := by
  obtain ⟨g, rfl⟩ := hp
  obtain ⟨h, rfl⟩ := hq
  have hm := congrArg (fun z : S.carrier => z.val.phase) (S.mul_comm g h)
  change g.val.phase + h.val.phase + 2 * bitLift (binaryDot g.val.clock h.val.shift) =
    h.val.phase + g.val.phase + 2 * bitLift (binaryDot h.val.clock g.val.shift) at hm
  rw [add_comm h.val.phase g.val.phase] at hm
  have hb := two_bitLift_injective (add_left_cancel hm)
  rw [hb]
  have hz (b : ZMod 2) : b + b = 0 := by fin_cases b <;> decide
  exact hz _

/-- The set of physical translations occurring in the stabilizer group. -/
def stabilizerTranslationSpace {n : ℕ} (S : StabilizerGroup n) :
    Submodule (ZMod 2) (BinaryVector n) :=
  (stabilizerLabelSpace S).map (LinearMap.fst (ZMod 2) (BinaryVector n) (BinaryVector n))

/-- Clock labels of actual diagonal stabilizers; no dimension is assumed. -/
def stabilizerDiagonalSpace {n : ℕ} (S : StabilizerGroup n) :
    Submodule (ZMod 2) (BinaryVector n) :=
  (stabilizerLabelSpace S).comap
    (LinearMap.inr (ZMod 2) (BinaryVector n) (BinaryVector n))

theorem stabilizerDiagonalSpace_le_orthogonal {n : ℕ} (S : StabilizerGroup n) :
    stabilizerDiagonalSpace S ≤ orthogonal (stabilizerTranslationSpace S) := by
  intro b hb a ha
  obtain ⟨p, hp, rfl⟩ := ha
  have h := stabilizerLabelSpace_isotropic S p (0, b) hp hb
  change binaryDot p.1 b = 0
  simpa only [pauliDot_zero_right, zero_add, binaryDot_comm] using h

/-- The actual shift projection on the binary label space. -/
def stabilizerTranslationMap {n : ℕ} (S : StabilizerGroup n) :
    stabilizerLabelSpace S →ₗ[ZMod 2] BinaryVector n :=
  (LinearMap.fst (ZMod 2) (BinaryVector n) (BinaryVector n)).comp
    (stabilizerLabelSpace S).subtype

theorem stabilizerTranslationMap_range {n : ℕ} (S : StabilizerGroup n) :
    LinearMap.range (stabilizerTranslationMap S) = stabilizerTranslationSpace S := by
  ext a
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.val, p.property, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- Kernel labels are precisely the actual diagonal labels. -/
def stabilizerDiagonalKernelEquiv {n : ℕ} (S : StabilizerGroup n) :
    LinearMap.ker (stabilizerTranslationMap S) ≃ₗ[ZMod 2]
      stabilizerDiagonalSpace S where
  toFun p := ⟨p.val.val.2, by
    have hz : p.val.val.1 = 0 := p.property
    change (0, p.val.val.2) ∈ stabilizerLabelSpace S
    rw [← hz]
    exact p.val.property⟩
  invFun b := ⟨⟨(0, b.val), b.property⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (show p.val.val.1 = 0 from p.property).symm
    · rfl
  right_inv b := rfl
  map_add' p q := rfl
  map_smul' a p := rfl

theorem stabilizerDiagonalSpace_finrank_add {n : ℕ} (S : StabilizerGroup n) :
    Module.finrank (ZMod 2) (stabilizerDiagonalSpace S) +
      Module.finrank (ZMod 2) (stabilizerTranslationSpace S) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (stabilizerTranslationMap S)
  rw [stabilizerTranslationMap_range,
    (stabilizerDiagonalKernelEquiv S).finrank_eq, stabilizerLabelSpace_finrank] at h
  omega

/-- The diagonal constraints exhaust the orthogonal complement of all translations. -/
theorem stabilizerDiagonalSpace_eq_orthogonal {n : ℕ} (S : StabilizerGroup n) :
    stabilizerDiagonalSpace S = orthogonal (stabilizerTranslationSpace S) := by
  apply Submodule.eq_of_le_of_finrank_eq (stabilizerDiagonalSpace_le_orthogonal S)
  have h₁ := stabilizerDiagonalSpace_finrank_add S
  have h₂ := finrank_orthogonal_add (stabilizerTranslationSpace S)
  omega

end ExactCriticalCurve.Quantum
