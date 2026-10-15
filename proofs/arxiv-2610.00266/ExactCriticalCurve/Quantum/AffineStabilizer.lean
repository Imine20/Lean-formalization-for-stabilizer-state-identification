import ExactCriticalCurve.Quantum.PhaseStabilizerRecovery
import ExactCriticalCurve.Quantum.PhaseCoordinates

/-! Canonical nonempty affine supports and the actual stabilizers attached to refinements. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open ExactCriticalCurve.Binary Classical
namespace ExactCriticalCurve.Quantum

abbrev NonemptyAffineSupport (n : ℕ) :=
  {A : AffineSubspace (ZMod 2) (BinaryVector n) // Nonempty A}

instance finiteNonemptyAffineSupport (n : ℕ) : Finite (NonemptyAffineSupport n) :=
  Finite.of_injective (fun A : NonemptyAffineSupport n => (A.val : Set (BinaryVector n)))
    (by intro A B h; exact Subtype.ext (SetLike.coe_injective h))

def affineSupportAnchor {n : ℕ} (A : NonemptyAffineSupport n) : BinaryVector n :=
  (Classical.choice A.property).val

theorem affineSupportAnchor_mem {n : ℕ} (A : NonemptyAffineSupport n) :
    affineSupportAnchor A ∈ A.val := (Classical.choice A.property).property

theorem affineSupport_mk_anchor {n : ℕ} (A : NonemptyAffineSupport n) :
    AffineSubspace.mk' (affineSupportAnchor A) A.val.direction = A.val :=
  AffineSubspace.mk'_eq (affineSupportAnchor_mem A)

/-- One fixed anchor is chosen per support; anchors are not ensemble labels. -/
def affineSupportDirectionEquiv {n : ℕ} (A : NonemptyAffineSupport n) :
    A.val.direction ≃ A.val where
  toFun t := ⟨t.val + affineSupportAnchor A,
    A.val.vadd_mem_of_mem_direction t.property (affineSupportAnchor_mem A)⟩
  invFun x := ⟨x.val - affineSupportAnchor A,
    A.val.vsub_mem_direction x.property (affineSupportAnchor_mem A)⟩
  left_inv _ := Subtype.ext (add_sub_cancel_right _ _)
  right_inv _ := Subtype.ext (sub_add_cancel _ _)

def phaseDataTransport {n : ℕ} {L M : Submodule (ZMod 2) (BinaryVector n)}
    (h : L = M) (q : StabilizerPhaseData L) : StabilizerPhaseData M := h ▸ q

theorem phaseStabilizer_transport {n : ℕ}
    {L M : Submodule (ZMod 2) (BinaryVector n)} (h : L = M) (a : BinaryVector n)
    (q : StabilizerPhaseData L) :
    phaseStabilizer a (phaseDataTransport h q) = phaseStabilizer a q := by
  cases h
  rfl

abbrev AffineRefinementData (n : ℕ) :=
  Σ A : NonemptyAffineSupport n, StabilizerPhaseData A.val.direction

def affineRefinementStabilizer {n : ℕ} (p : AffineRefinementData n) : StabilizerGroup n :=
  phaseStabilizer (affineSupportAnchor p.1) p.2

theorem affineRefinementStabilizer_support {n : ℕ} (p : AffineRefinementData n) :
    stabilizerSupport (affineRefinementStabilizer p) = p.1.val := by
  rw [affineRefinementStabilizer, phaseStabilizer_support, affineSupport_mk_anchor]

/-- Every actual stabilizer subgroup is obtained from its full affine support and true phases. -/
theorem affineRefinementStabilizer_surjective (n : ℕ) :
    Function.Surjective (@affineRefinementStabilizer n) := by
  intro S
  let A : NonemptyAffineSupport n := ⟨stabilizerSupport S, stabilizerSupport_nonempty S⟩
  have ha : stabilizerVector S (affineSupportAnchor A) ≠ 0 :=
    (mem_stabilizerSupport S _).mp (affineSupportAnchor_mem A)
  let q := stabilizerPhaseData S (affineSupportAnchor A) ha
  let r : StabilizerPhaseData A.val.direction :=
    phaseDataTransport (stabilizerSupport_direction S).symm q
  refine ⟨⟨A, r⟩, ?_⟩
  change phaseStabilizer (affineSupportAnchor A)
    (phaseDataTransport (stabilizerSupport_direction S).symm q) = S
  rw [phaseStabilizer_transport]
  exact phaseStabilizer_stabilizerPhaseData S _ ha

/-- Equality of the actual reconstructed subgroups recovers every mod-four phase value. -/
theorem phaseStabilizer_phase_eq {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q r : StabilizerPhaseData L) (h : phaseStabilizer a q = phaseStabilizer a r) :
    q.phase = r.phase := by
  funext t
  apply pauliPhase_injective
  apply mul_right_cancel₀ (phaseStabilizer_anchor_ne_zero a q)
  have hq := phaseStabilizer_vector_translation a q t
  have hr := phaseStabilizer_vector_translation a r t
  rw [← h] at hr
  exact hq.symm.trans hr

theorem affineRefinementStabilizer_injective (n : ℕ) :
    Function.Injective (@affineRefinementStabilizer n) := by
  rintro ⟨A, q⟩ ⟨B, r⟩ h
  have he : A = B := by
    apply Subtype.ext
    exact (affineRefinementStabilizer_support ⟨A, q⟩).symm.trans
      ((congrArg stabilizerSupport h).trans (affineRefinementStabilizer_support ⟨B, r⟩))
  subst B
  have hq : q = r :=
    StabilizerPhaseData.ext_of_phase_eq (phaseStabilizer_phase_eq _ q r h)
  subst r
  rfl

/-- Complete classification of actual scalar-free signed Pauli stabilizers. -/
def affineRefinementEquivStabilizer (n : ℕ) :
    AffineRefinementData n ≃ StabilizerGroup n :=
  Equiv.ofBijective _ ⟨affineRefinementStabilizer_injective n,
    affineRefinementStabilizer_surjective n⟩

/-- Every physical stabilizer occurs exactly once, with a canonical support anchor
and all mod-four linear / binary cross coefficients retained. -/
def stabilizerAffineNormalForm (n : ℕ) :
    StabilizerGroup n ≃ Σ A : NonemptyAffineSupport n,
      QuadraticPhaseData (Module.finrank (ZMod 2) A.val.direction) :=
  (affineRefinementEquivStabilizer n).symm.trans
    (Equiv.sigmaCongrRight (fun A =>
      phaseDataCoordinatesEquiv (Module.finBasis (ZMod 2) A.val.direction)))

theorem stabilizerAffineNormalForm_bijective (n : ℕ) :
    Function.Bijective (stabilizerAffineNormalForm n) :=
  (stabilizerAffineNormalForm n).bijective

end ExactCriticalCurve.Quantum
