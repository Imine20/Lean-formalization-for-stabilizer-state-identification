import StabilizerLearning.Quantum.PhaseAlgebra

/-! Completeness of the finite phase encoding for arbitrary complex
cocycle-compatible assignments. No existence or root-of-unity property is
included in the complex assignment definition. -/
noncomputable section
namespace StabilizerLearning.Quantum


section PhaseImage
variable (p : ℕ) [NeZero p]

@[simp] theorem rootPhase_pow_modulus (t : ZMod p) : rootPhase p t ^ p = 1 := by
  rw [rootPhase_eq_stdAddChar, ← AddChar.map_nsmul_eq_pow,
    ZModModule.char_nsmul_eq_zero, AddChar.map_zero_eq_one]

@[simp] theorem eigenPhase_pow_two_mul (t : ZMod (2 * p)) :
    eigenPhase p t ^ (2 * p) = 1 := by
  rw [eigenPhase_eq_stdAddChar, ← AddChar.map_nsmul_eq_pow,
    ZModModule.char_nsmul_eq_zero, AddChar.map_zero_eq_one]

/-- The literal phase map covers exactly all complex (2p)-th roots of unity. -/
theorem eigenPhase_exists_iff (w : ℂ) :
    (∃ t : ZMod (2 * p), eigenPhase p t = w) ↔ w ^ (2 * p) = 1 := by
  constructor
  · rintro ⟨t, rfl⟩
    exact eigenPhase_pow_two_mul p t
  · intro hw
    obtain ⟨t, ht⟩ := surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar
      (2 * p) (rootsOfUnity.mkOfPowEq w hw)
    refine ⟨t, ?_⟩
    have hv := congrArg (fun r : rootsOfUnity (2 * p) ℂ => (r.val : ℂ)) ht
    calc
      eigenPhase p t = ZMod.stdAddChar t := eigenPhase_eq_stdAddChar p t
      _ = ((rootsOfUnityCircleEquiv (2 * p)
          (ZMod.rootsOfUnityAddChar (2 * p) t)).val : ℂ) := by
        simp [ZMod.stdAddChar_apply]
      _ = w := by simpa only [Function.comp_apply, rootsOfUnity.coe_mkOfPowEq] using hv

end PhaseImage

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

def ComplexCompatible (χ : U → ℂ) : Prop :=
  (∀ z, ‖χ z‖ = 1) ∧
  ∀ z w, χ (z + w) = (sectionCocycle p n z w)⁻¹ * χ z * χ w

abbrev ComplexAssignment := {χ : U → ℂ // ComplexCompatible p n U χ}

@[simp] theorem complexAssignment_norm (χ : ComplexAssignment p n U) (z : U) :
    ‖χ.val z‖ = 1 := χ.property.1 z

@[simp] theorem complexAssignment_ne_zero (χ : ComplexAssignment p n U) (z : U) :
    χ.val z ≠ 0 := by
  intro h
  have hn := complexAssignment_norm p n U χ z
  rw [h, norm_zero] at hn
  norm_num at hn

@[simp] theorem complexAssignment_zero (χ : ComplexAssignment p n U) :
    χ.val 0 = 1 := by
  have h := χ.property.2 0 0
  have hc : sectionCocycle p n (0 : PhaseSpace p n) 0 = 1 := by
    simp [sectionCocycle, rootPhase, dotProduct]
  have hh : χ.val 0 = χ.val 0 * χ.val 0 := by
    simpa only [zero_add, ZeroMemClass.coe_zero, hc, inv_one, one_mul] using h
  exact (mul_left_cancel₀ (complexAssignment_ne_zero p n U χ 0)
    (by simpa only [mul_one] using hh)).symm


/-- Taking the ratio at opposite vectors cancels the section cocycle. -/
def complexAssignmentRatioCharacter (χ : ComplexAssignment p n U) : AddChar U ℂ where
  toFun z := χ.val z / χ.val (-z)
  map_zero_eq_one' := by simp
  map_add_eq_mul' z w := by
    change χ.val (z + w) / χ.val (-(z + w)) =
      (χ.val z / χ.val (-z)) * (χ.val w / χ.val (-w))
    rw [neg_add, χ.property.2, χ.property.2]
    have hc : sectionCocycle p n ((-z : U) : PhaseSpace p n)
        ((-w : U) : PhaseSpace p n) = sectionCocycle p n z w := by
      simp [sectionCocycle, neg_dotProduct, dotProduct_neg]
    rw [hc]
    have hc0 : sectionCocycle p n z w ≠ 0 := rootPhase_ne_zero _ _
    field_simp

/-- Compatibility itself forces the root-of-unity bound; no isotropy or
finite-root premise is imposed on the complex assignment. -/
theorem complexAssignment_pow_two_mul (χ : ComplexAssignment p n U) (z : U) :
    χ.val z ^ (2 * p) = 1 := by
  have hr : (χ.val z / χ.val (-z)) ^ p = 1 := by
    change (complexAssignmentRatioCharacter p n U χ z) ^ p = 1
    rw [← AddChar.map_nsmul_eq_pow, ZModModule.char_nsmul_eq_zero,
      AddChar.map_zero_eq_one]
  have hm : χ.val z * χ.val (-z) =
      rootPhase p (-dotProduct z.val.2 z.val.1) := by
    have h := χ.property.2 z (-z)
    have hc0 := rootPhase_ne_zero p (-dotProduct z.val.2 z.val.1)
    simpa [sectionCocycle, dotProduct_neg, mul_assoc, hc0] using
      congrArg (fun w => rootPhase p (-dotProduct z.val.2 z.val.1) * w) h.symm
  have hp : (χ.val z * χ.val (-z)) ^ p = 1 := by
    rw [hm, rootPhase_pow_modulus]
  have hratio : χ.val z ^ p = χ.val (-z) ^ p := by
    rw [div_pow] at hr
    exact (div_eq_one_iff_eq (pow_ne_zero _ (complexAssignment_ne_zero p n U χ (-z)))).mp hr
  rw [mul_pow, ← hratio] at hp
  simpa only [pow_mul, pow_two, mul_pow] using hp


/-- Encode each complex value by its unique finite phase exponent. Compatibility
has already proved that the value belongs to the required root-of-unity group. -/
def complexAssignmentEncode (χ : ComplexAssignment p n U) : Assignment p n U := by
  let f : U → ZMod (2 * p) := fun z =>
    Classical.choose ((eigenPhase_exists_iff p (χ.val z)).mpr
      (complexAssignment_pow_two_mul p n U χ z))
  have hf (z : U) : eigenPhase p (f z) = χ.val z :=
    Classical.choose_spec ((eigenPhase_exists_iff p (χ.val z)).mpr
      (complexAssignment_pow_two_mul p n U χ z))
  refine ⟨f, ?_, ?_⟩
  · intro z
    rw [hf]
    exact χ.property.1 z
  · intro z w
    simp only [hf]
    exact χ.property.2 z w

@[simp] theorem eigenPhase_complexAssignmentEncode (χ : ComplexAssignment p n U) (z : U) :
    eigenPhase p ((complexAssignmentEncode p n U χ).val z) = χ.val z :=
  Classical.choose_spec ((eigenPhase_exists_iff p (χ.val z)).mpr
    (complexAssignment_pow_two_mul p n U χ z))

/-- The original finite phase assignments and unrestricted complex assignments
are genuinely equivalent, without a root-of-unity or isotropy hypothesis. -/
def assignmentComplexEquiv : Assignment p n U ≃ ComplexAssignment p n U where
  toFun η := ⟨fun z => eigenPhase p (η.val z), η.property⟩
  invFun := complexAssignmentEncode p n U
  left_inv η := by
    apply Subtype.ext
    funext z
    apply eigenPhase_injective p
    exact eigenPhase_complexAssignmentEncode p n U _ z
  right_inv χ := by
    apply Subtype.ext
    funext z
    exact eigenPhase_complexAssignmentEncode p n U χ z

@[simp] theorem assignmentComplexEquiv_apply (η : Assignment p n U) (z : U) :
    (assignmentComplexEquiv p n U η).val z = eigenPhase p (η.val z) := rfl

@[simp] theorem eigenPhase_assignmentComplexEquiv_symm_apply
    (χ : ComplexAssignment p n U) (z : U) :
    eigenPhase p (((assignmentComplexEquiv p n U).symm χ).val z) = χ.val z :=
  eigenPhase_complexAssignmentEncode p n U χ z

end StabilizerLearning.Quantum
