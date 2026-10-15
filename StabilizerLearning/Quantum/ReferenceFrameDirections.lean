import StabilizerLearning.Quantum.ReferenceFrame
import StabilizerLearning.Quantum.CanonicalReports

/-! Full frame-relative direction alphabets and transport of the intrinsic target. -/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum
variable {p m b : ℕ} [Fact p.Prime]

/-- All legal partial direction families relative to the actual announced frame. -/
abbrev ReferenceDirections (R : OrderedLagrangianFrame p (m+b)) :=
  {S : Fin m → PhaseSpace p (m+b) //
    (∀ i j, symplecticPairing (S i) (frameVector R j) =
      if i.castAdd b = j then 1 else 0) ∧
    ∀ i j, symplecticPairing (S i) (S j) = 0}

/-- Standardization bijects the entire legal direction alphabet with canonical directions. -/
def referenceDirectionsEquivCanonical (R : OrderedLagrangianFrame p (m+b)) :
    ReferenceDirections R ≃ CanonicalDirections p m b where
  toFun S := ⟨fun i => frameStandardization R (S.val i), by
    constructor
    · intro i
      rw [frameStandardization_first]
      ext j
      simp only [referencePairingMap_apply, S.property.1]
      simp [Pi.single_apply, eq_comm]
    · intro i j
      exact (pairing_frameStandardization R _ _).trans (S.property.2 i j)⟩
  invFun S := ⟨fun i => (frameStandardization R).symm (S.val i), by
    constructor
    · intro i j
      have h := pairing_frameStandardization R
        ((frameStandardization R).symm (S.val i)) (frameVector R j)
      rw [LinearEquiv.apply_symm_apply, frameStandardization_basis] at h
      rw [← h]
      simp [symplecticPairing, S.property.1 i, Pi.single_apply, eq_comm]
    · intro i j
      exact (symplecticPairing_symm _ (pairing_frameStandardization R) _ _).trans
        (S.property.2 i j)⟩
  left_inv S := by apply Subtype.ext; funext i; exact LinearEquiv.symm_apply_apply _ _
  right_inv S := by apply Subtype.ext; funext i; exact LinearEquiv.apply_symm_apply _ _

@[simp] theorem referenceDirectionsEquivCanonical_apply
    (R : OrderedLagrangianFrame p (m+b)) (S : ReferenceDirections R) (i : Fin m) :
    (referenceDirectionsEquivCanonical R S).val i = frameStandardization R (S.val i) := rfl

@[simp] theorem referenceDirectionsEquivCanonical_symm_apply
    (R : OrderedLagrangianFrame p (m+b)) (S : CanonicalDirections p m b) (i : Fin m) :
    ((referenceDirectionsEquivCanonical R).symm S).val i =
      (frameStandardization R).symm (S.val i) := rfl

/-- The actual first m reference-dual directions in a transverse input Lagrangian. -/
def referenceTargetDirections (R : OrderedLagrangianFrame p (m+b))
    (L : Lagrangian p (m+b)) (hLR : Disjoint L.val R.1.val) : ReferenceDirections R :=
  ⟨fun i => (referenceDualVector R L hLR (i.castAdd b)).val,
    ⟨fun i j => pairing_referenceDualVector R L hLR (i.castAdd b) j,
      fun i j => L.property.1 _ (referenceDualVector R L hLR (i.castAdd b)).property _
        (referenceDualVector R L hLR (j.castAdd b)).property⟩⟩

/-- The transported intrinsic target is exactly the existing canonical label target's directions. -/
theorem referenceDirectionsEquivCanonical_target
    (R : OrderedLagrangianFrame p (m+b)) (L : Lagrangian p (m+b))
    (hLR : Disjoint L.val R.1.val) (ℓ : TransverseLabel p (m+b))
    (hℓ : ℓ.val.1 = frameMapLagrangian R L) :
    referenceDirectionsEquivCanonical R (referenceTargetDirections R L hLR) =
      (canonicalLabelTarget (m := m) (b := b) ℓ).1 := by
  apply Subtype.ext
  funext i
  let z := frameStandardization R (referenceDualVector R L hLR (i.castAdd b)).val
  have hz : z ∈ ℓ.val.1.val := by
    rw [hℓ]
    exact ⟨(referenceDualVector R L hLR (i.castAdd b)).val,
      (referenceDualVector R L hLR (i.castAdd b)).property, rfl⟩
  have hfst : z.1 = Pi.single (i.castAdd b) 1 :=
    (referenceDirectionsEquivCanonical R (referenceTargetDirections R L hLR)).property.1 i
  have he : (⟨z, hz⟩ : ℓ.val.1.val) =
      (transverseProjectionEquiv ℓ.val.1 ℓ.property).symm (Pi.single (i.castAdd b) 1) := by
    apply (transverseProjectionEquiv ℓ.val.1 ℓ.property).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hfst
  exact congrArg Subtype.val he

/-- The physical subspace spanned by a frame-relative report. -/
def referenceSpan {R : OrderedLagrangianFrame p (m+b)} (S : ReferenceDirections R) :
    Submodule (ZMod p) (PhaseSpace p (m+b)) :=
  Submodule.span (ZMod p) (Set.range S.val)

theorem referenceTargetSpan_le (R : OrderedLagrangianFrame p (m+b))
    (L : Lagrangian p (m+b)) (hLR : Disjoint L.val R.1.val) :
    referenceSpan (referenceTargetDirections R L hLR) ≤ L.val := by
  apply Submodule.span_le.mpr
  rintro z ⟨i, rfl⟩
  exact (referenceDualVector R L hLR (i.castAdd b)).property

/-- Standardization carries actual direction spans onto the canonical report spans. -/
theorem referenceSpan_map (R : OrderedLagrangianFrame p (m+b)) (S : ReferenceDirections R) :
    (referenceSpan S).map (frameStandardization R).toLinearMap =
      canonicalSpan (referenceDirectionsEquivCanonical R S) := by
  rw [referenceSpan, canonicalSpan, Submodule.map_span]
  congr 1
  exact Set.range_comp (frameStandardization R) S.val |>.symm

/-- The restriction of standardization to a report's physical span. -/
def referenceSpanEquivCanonical (R : OrderedLagrangianFrame p (m+b)) (S : ReferenceDirections R) :
    referenceSpan S ≃ₗ[ZMod p] canonicalSpan (referenceDirectionsEquivCanonical R S) :=
  ((frameStandardization R).submoduleMap (referenceSpan S)).trans
    (LinearEquiv.ofEq _ _ (referenceSpan_map R S))

@[simp] theorem referenceSpanEquivCanonical_apply
    (R : OrderedLagrangianFrame p (m+b)) (S : ReferenceDirections R) (z : referenceSpan S) :
    (referenceSpanEquivCanonical R S z).val = frameStandardization R z.val := rfl


/-- Every legal report has the actual prescribed dimension. -/
theorem finrank_referenceSpan (R : OrderedLagrangianFrame p (m+b)) (S : ReferenceDirections R) :
    Module.finrank (ZMod p) (referenceSpan S) = m :=
  (referenceSpanEquivCanonical R S).finrank_eq.trans (finrank_canonicalSpan _)

/-- Pairwise commuting reported generators make their entire physical span isotropic. -/
theorem isIsotropic_referenceSpan (R : OrderedLagrangianFrame p (m+b))
    (S : ReferenceDirections R) : IsIsotropic (referenceSpan S) := by
  have hker (i : Fin m) : referenceSpan S ≤
      LinearMap.ker (symplecticBilinForm.flip (S.val i)) := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, rfl⟩
    exact S.property.2 j i
  have horth : referenceSpan S ≤ symplecticBilinForm.orthogonal (referenceSpan S) := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩ w hw
    exact hker i hw
  intro z hz w hw
  exact horth hw z hz

end StabilizerLearning.Quantum
