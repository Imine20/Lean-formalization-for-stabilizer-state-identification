import StabilizerLearning.Quantum.AssignmentAlgebra

/-! Restriction and section-preserving transport of the public physical
assignments, with their cocycle compatibility proved after transport. -/
noncomputable section
namespace StabilizerLearning.Quantum

variable (p : ℕ) [Fact p.Prime]

def restrictAssignment {n : ℕ}
    {U V : Submodule (ZMod p) (PhaseSpace p n)} (h : V ≤ U)
    (η : Assignment p n U) : Assignment p n V := by
  let f := Submodule.inclusion h
  refine ⟨fun z => η.val (f z), ?_, ?_⟩
  · intro z
    exact η.property.1 (f z)
  · intro z w
    dsimp only
    rw [f.map_add]
    exact η.property.2 (f z) (f w)

@[simp] theorem restrictAssignment_apply {n : ℕ}
    {U V : Submodule (ZMod p) (PhaseSpace p n)} (h : V ≤ U)
    (η : Assignment p n U) (z : V) :
    (restrictAssignment p h η).val z = η.val ⟨z.val, h z.property⟩ := rfl

/-- An additive identification preserving the actual XZ cocycle transports the
entire assignment space, in both directions, including its finite phase encoding. -/
def assignmentCocycleEquiv {n n' : ℕ}
    (U : Submodule (ZMod p) (PhaseSpace p n))
    (V : Submodule (ZMod p) (PhaseSpace p n')) (e : U ≃+ V)
    (hc : ∀ z w, sectionCocycle p n' (e z) (e w) = sectionCocycle p n z w) :
    Assignment p n U ≃ Assignment p n' V where
  toFun η := ⟨fun z => η.val (e.symm z),
    (by intro z; exact η.property.1 _), by
      intro z w
      dsimp only
      rw [e.symm.map_add, η.property.2]
      rw [← hc, e.apply_symm_apply, e.apply_symm_apply]⟩
  invFun η := ⟨fun z => η.val (e z),
    (by intro z; exact η.property.1 _), by
      intro z w
      dsimp only
      rw [e.map_add, η.property.2, hc]⟩
  left_inv η := by
    apply Subtype.ext
    funext z
    exact congrArg η.val (e.symm_apply_apply z)
  right_inv η := by
    apply Subtype.ext
    funext z
    exact congrArg η.val (e.apply_symm_apply z)

end StabilizerLearning.Quantum
