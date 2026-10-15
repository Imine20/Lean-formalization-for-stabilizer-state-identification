import StabilizerLearning.Quantum.StabilizerEquivalence
import StabilizerLearning.Quantum.TransverseGraph
import StabilizerLearning.FiniteCopy.UniformExperiment

/-! The physical standard transverse ensemble is a subtype of the original
distinct density matrices.  Membership is defined by its recovered physical
Lagrangian, before any quadratic coordinate parametrization. -/
noncomputable section
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

abbrev TransverseLabel :=
  {ℓ : StabilizerLabel p n // IsTransverse ℓ.1.val}

abbrev TransverseState :=
  {ρ : StabilizerState p n //
    IsTransverse ((stabilizerLabelStateEquiv p n).symm ρ).1.val}

noncomputable instance transverseLabelFintype : Fintype (TransverseLabel p n) :=
  Fintype.ofFinite _

noncomputable instance transverseStateFintype : Fintype (TransverseState p n) :=
  Fintype.ofFinite _

/-- Restrict the already proved injective/surjective physical label-to-state map
to the actual transverse condition.  The original state prior has no label
multiplicity. -/
def transverseLabelStateEquiv : TransverseLabel p n ≃ TransverseState p n :=
  Equiv.subtypeEquiv (stabilizerLabelStateEquiv p n) (by
    intro ℓ
    simp only [Equiv.symm_apply_apply])

@[simp] theorem transverseLabelStateEquiv_density (ℓ : TransverseLabel p n) :
    (transverseLabelStateEquiv p n ℓ).val.val = labelProjector p n ℓ.val := rfl

/-- Uniform averaging over the physical distinct matrices equals uniform
averaging over legal transverse labels, by a proved physical bijection. -/
theorem transverse_uniform_prior (f : TransverseState p n → ℝ) :
    uniformFiniteMean (fun ℓ => f (transverseLabelStateEquiv p n ℓ)) =
      uniformFiniteMean f :=
  uniformFiniteMean_comp_equiv (transverseLabelStateEquiv p n) f

def transverseSigmaLabelEquiv :
    ((L : TransverseLagrangian p n) × Assignment p n L.val.val) ≃
      TransverseLabel p n where
  toFun ℓ := ⟨⟨ℓ.1.val, ℓ.2⟩, ℓ.1.property⟩
  invFun ℓ := ⟨⟨ℓ.val.1, ℓ.property⟩, ℓ.val.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every actual transverse physical label has unique graph data, retaining
its entire original compatible phase assignment. -/
def graphLabelTransverseEquiv :
    ((A : SymmetricMatrices (Fin n) (ZMod p)) ×
      Assignment p n (graphSubmodule A.val)) ≃ TransverseLabel p n :=
  (Equiv.sigmaCongrLeft
    (transverseLagrangianEquivSymmetricMatrices (p := p) (n := n)).symm).trans
      (transverseSigmaLabelEquiv p n)

@[simp] theorem graphLabelTransverseEquiv_apply
    (A : SymmetricMatrices (Fin n) (ZMod p))
    (η : Assignment p n (graphSubmodule A.val)) :
    (graphLabelTransverseEquiv p n ⟨A, η⟩).val =
      ⟨graphLagrangian A.val A.property, η⟩ := rfl

@[simp] theorem transverseProjectionEquiv_graph_symm
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (hT : IsTransverse (graphSubmodule A)) (u : Configuration p n) :
    (transverseProjectionEquiv (graphLagrangian A hA) hT).symm u =
      graphLinearEquiv A u := by
  apply (transverseProjectionEquiv (graphLagrangian A hA) hT).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

end StabilizerLearning.Quantum
