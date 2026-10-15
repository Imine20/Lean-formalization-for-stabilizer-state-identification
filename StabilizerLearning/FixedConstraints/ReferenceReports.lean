import StabilizerLearning.FixedConstraints.AdaptedFrame
import StabilizerLearning.Quantum.ReferenceFrameDirections
import StabilizerLearning.Quantum.StabilizerEquivalence

/-! Forgetting an adapted-frame report preserves its full physical assignment and
embeds the complete refined alphabet in the original fixed-constraint alphabet. -/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning
namespace Quantum
variable {p m b : ℕ} [Fact p.Prime]

/-- Coordinates on an actual reference-relative report span. -/
def referenceSpanCoordinates (R : OrderedLagrangianFrame p (m+b)) (S : ReferenceDirections R) :
    referenceSpan S ≃ₗ[ZMod p] Configuration p m :=
  (referenceSpanEquivCanonical R S).trans
    (canonicalSpanLinearEquiv (referenceDirectionsEquivCanonical R S)).symm

@[simp] theorem referenceSpanCoordinates_apply (R : OrderedLagrangianFrame p (m+b))
    (S : ReferenceDirections R) (z : referenceSpan S) (i : Fin m) :
    referenceSpanCoordinates R S z i = referencePairingMap R z.val (i.castAdd b) := by
  change (frameStandardization R z.val).1 (i.castAdd b) = _
  rw [frameStandardization_first]

/-- The reported subspace is genuinely transverse to the announced Lagrangian. -/
theorem referenceSpan_disjoint_frame (R : OrderedLagrangianFrame p (m+b))
    (S : ReferenceDirections R) : Disjoint (referenceSpan S) R.1.val := by
  apply disjoint_iff_inf_le.mpr
  intro z hz
  have hc : referenceSpanCoordinates R S ⟨z, hz.1⟩ = 0 := by
    ext i
    rw [referenceSpanCoordinates_apply]
    exact congrFun ((referencePairingMap_eq_zero_iff R z).mpr hz.2) (i.castAdd b)
  have he : (⟨z, hz.1⟩ : referenceSpan S) = 0 :=
    (referenceSpanCoordinates R S).injective (by simpa using hc)
  exact congrArg Subtype.val he

/-- The reference-duality requirement uniquely orders a legal basis of its span. -/
theorem referenceSpan_injective (R : OrderedLagrangianFrame p (m+b)) :
    Function.Injective (referenceSpan (R := R)) := by
  intro S T hST
  apply Subtype.ext
  funext i
  have hS : S.val i ∈ referenceSpan S := Submodule.subset_span ⟨i, rfl⟩
  have hT : T.val i ∈ referenceSpan S := by
    rw [hST]
    exact Submodule.subset_span ⟨i, rfl⟩
  have he : (⟨S.val i, hS⟩ : referenceSpan S) = ⟨T.val i, hT⟩ := by
    apply (referenceSpanCoordinates R S).injective
    ext j
    simp only [referenceSpanCoordinates_apply, referencePairingMap_apply,
      S.property.1, T.property.1]
  exact congrArg Subtype.val he
end Quantum

namespace FixedConstraints
open Quantum
variable {p m b : ℕ} [Fact p.Prime]

/-- Every legal refined report of an actual W-adapted frame is a legal original report subspace. -/
def referenceReportSubspace (W : Constraint p (m+b) m) (M : Lagrangian p (m+b))
    (hWM : W.subspace ≤ M.val)
    (S : ReferenceDirections (adaptedReferenceFrame W M hWM)) : ReportSubspace W := by
  let R := adaptedReferenceFrame W M hWM
  refine ⟨referenceSpan S, isIsotropic_referenceSpan R S, finrank_referenceSpan R S, ?_, ?_⟩
  · intro z hz w hw
    have htail (j : Fin b) : symplecticBilinForm z (frameVector R (j.natAdd m)) = 0 := by
      have hspan : referenceSpan S ≤ LinearMap.ker
          (symplecticBilinForm.flip (frameVector R (j.natAdd m))) := by
        apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        change symplecticPairing (S.val i) (frameVector R (j.natAdd m)) = 0
        rw [S.property.1]
        have hne : i.castAdd b ≠ j.natAdd m := by
          intro he
          have hv := congrArg Fin.val he
          change i.val = m + j.val at hv
          omega
        simp [hne]
      exact hspan hz
    have hW : W.subspace ≤ LinearMap.ker (symplecticBilinForm z) := by
      rw [← adaptedReferenceFrame_tail_span W M hWM]
      apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      exact htail j
    exact hW hw
  · exact ((referenceSpan_disjoint_frame R S).mono_right hWM).eq_bot

@[simp] theorem referenceReportSubspace_val (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val)
    (S : ReferenceDirections (adaptedReferenceFrame W M hWM)) :
    (referenceReportSubspace W M hWM S).val = referenceSpan S := rfl

/-- Forget only the reference-dual ordering, retaining the whole physical assignment. -/
def referenceReportForget (W : Constraint p (m+b) m) (M : Lagrangian p (m+b))
    (hWM : W.subspace ≤ M.val)
    (r : (S : ReferenceDirections (adaptedReferenceFrame W M hWM)) ×
      Assignment p (m+b) (referenceSpan S)) : Report W :=
  ⟨referenceReportSubspace W M hWM r.1, r.2⟩

/-- Forgetting the ordering leaves the actual verification projector unchanged. -/
@[simp] theorem reportProjector_referenceReportForget (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val)
    (r : (S : ReferenceDirections (adaptedReferenceFrame W M hWM)) ×
      Assignment p (m+b) (referenceSpan S)) :
    reportProjector W (referenceReportForget W M hWM r) =
      jointProjector p (m+b) (referenceSpan r.1) r.2 := rfl

/-- The forgetful map is an embedding because the span determines the unique reference-dual basis. -/
theorem referenceReportForget_injective (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) :
    Function.Injective (referenceReportForget W M hWM) := by
  rintro ⟨S, η⟩ ⟨T, θ⟩ h
  have hST : referenceSpan S = referenceSpan T :=
    congrArg (fun r : Report W => r.1.val) h
  have hd := referenceSpan_injective (adaptedReferenceFrame W M hWM) hST
  subst T
  have ha : η = θ := Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
  subst θ
  rfl

/-- The actual reference-dual target, with the original assignment restricted,
is a valid original fixed-W report for the same distinct physical state. -/
theorem referenceLabelTarget_forget_valid (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val)
    (ℓ : StabilizerLabel p (m+b)) (hLM : Disjoint ℓ.1.val M.val) :
    Valid W (stabilizerLabelStateEquiv p (m+b) ℓ)
      (referenceReportForget W M hWM
        ⟨referenceTargetDirections (adaptedReferenceFrame W M hWM) ℓ.1 hLM,
          restrictAssignment p
            (referenceTargetSpan_le (adaptedReferenceFrame W M hWM) ℓ.1 hLM) ℓ.2⟩) := by
  intro z
  let zL : ℓ.1.val := ⟨z.val,
    referenceTargetSpan_le (adaptedReferenceFrame W M hWM) ℓ.1 hLM z.property⟩
  exact pauli_mul_jointProjector p (m+b) ℓ.1.val ℓ.2 zL

end FixedConstraints
end StabilizerLearning
