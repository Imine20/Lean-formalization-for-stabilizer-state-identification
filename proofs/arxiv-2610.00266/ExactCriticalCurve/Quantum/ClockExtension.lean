import ExactCriticalCurve.Quantum.QuadraticRefinement
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual ambient clocks extending functionals on the translation space. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
open ExactCriticalCurve.Binary Classical
namespace ExactCriticalCurve.Quantum

def clockRestriction {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n)) :
    BinaryVector n →ₗ[ZMod 2] Module.Dual (ZMod 2) L where
  toFun b := ((binaryDotForm n) b).comp L.subtype
  map_add' b c := by
    ext u
    exact congrArg (fun f => f u.val) ((binaryDotForm n).map_add b c)
  map_smul' c b := by
    ext u
    exact congrArg (fun f => f u.val) ((binaryDotForm n).map_smul c b)

@[simp] theorem clockRestriction_apply {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) (b : BinaryVector n) (u : L) :
    clockRestriction L b u = binaryDot b u.val := rfl

/-- Every true linear functional on L has an ambient clock representative. -/
theorem clockRestriction_surjective {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) : Function.Surjective (clockRestriction L) := by
  intro f
  obtain ⟨g, hg⟩ := f.exists_extend
  refine ⟨fun i => g (Pi.single i 1), ?_⟩
  ext u
  change (∑ i, g (Pi.single i 1) * u.val i) = f u
  have hu : (∑ i : Fin n, u.val i • Pi.single i (1 : ZMod 2)) = u.val := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = g (∑ i : Fin n, u.val i • Pi.single i (1 : ZMod 2)) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, mul_comm]
    _ = f u := by
      rw [hu]
      exact congrArg (fun h : L →ₗ[ZMod 2] ZMod 2 => h u) hg

theorem clockRestriction_ker {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) :
    LinearMap.ker (clockRestriction L) = orthogonal L := by
  ext b
  constructor
  · intro hb u hu
    have h := congrArg (fun f : Module.Dual (ZMod 2) L => f ⟨u, hu⟩) hb
    change binaryDot b u = 0 at h
    change binaryDot u b = 0
    rwa [binaryDot_comm]
  · intro hb
    apply LinearMap.ext
    intro u
    change binaryDot b u.val = 0
    rw [binaryDot_comm]
    exact hb u.val u.property

/-- All actual pairs of a translation and a compatible ambient clock. -/
def phaseClockSpace {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (q : StabilizerPhaseData L) : Submodule (ZMod 2) (L × BinaryVector n) where
  carrier := {p | clockRestriction L p.2 = q.polar p.1}
  zero_mem' := by simp
  add_mem' := by
    intro p s hp hs
    change clockRestriction L (p.2 + s.2) = q.polar (p.1 + s.1)
    rw [map_add, map_add, hp, hs]
  smul_mem' := by
    intro c p hp
    change clockRestriction L (c • p.2) = q.polar (c • p.1)
    rw [map_smul, map_smul, hp]

def phaseClockTranslation {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (q : StabilizerPhaseData L) : phaseClockSpace q →ₗ[ZMod 2] L :=
  (LinearMap.fst (ZMod 2) L (BinaryVector n)).comp (phaseClockSpace q).subtype

theorem phaseClockTranslation_surjective {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (q : StabilizerPhaseData L) :
    Function.Surjective (phaseClockTranslation q) := by
  intro t
  obtain ⟨b, hb⟩ := clockRestriction_surjective L (q.polar t)
  exact ⟨⟨(t, b), hb⟩, rfl⟩

/-- The zero-translation fiber is exactly the real orthogonal clock space. -/
def phaseClockKernelEquiv {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (q : StabilizerPhaseData L) :
    LinearMap.ker (phaseClockTranslation q) ≃ₗ[ZMod 2] orthogonal L where
  toFun p := ⟨p.val.val.2, by
    rw [← clockRestriction_ker]
    change clockRestriction L p.val.val.2 = 0
    have hz : p.val.val.1 = 0 := p.property
    have hp := p.val.property
    change clockRestriction L p.val.val.2 = q.polar p.val.val.1 at hp
    rwa [hz, map_zero] at hp⟩
  invFun b := ⟨⟨(0, b.val), by
    change clockRestriction L b.val = q.polar 0
    rw [map_zero]
    have hb : b.val ∈ LinearMap.ker (clockRestriction L) := by
      rw [clockRestriction_ker]
      exact b.property
    exact hb⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (show p.val.val.1 = 0 from p.property).symm
    · rfl
  right_inv b := rfl
  map_add' p s := rfl
  map_smul' c p := rfl

theorem phaseClockSpace_finrank {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (q : StabilizerPhaseData L) :
    Module.finrank (ZMod 2) (phaseClockSpace q) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (phaseClockTranslation q)
  rw [LinearMap.range_eq_top.mpr (phaseClockTranslation_surjective q),
    finrank_top, (phaseClockKernelEquiv q).finrank_eq] at h
  have hL := finrank_orthogonal_add L
  omega

theorem phaseClockSpace_card {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (q : StabilizerPhaseData L) :
    Nat.card (phaseClockSpace q) = 2 ^ n := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), phaseClockSpace_finrank]
  simp [Nat.card_eq_fintype_card]

end ExactCriticalCurve.Quantum
