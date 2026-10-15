import StabilizerLearning.FixedConstraints.Task
import StabilizerLearning.Foundations.IsotropicComplement
import StabilizerLearning.Quantum.ReferenceFrame
import StabilizerLearning.Quantum.AssignmentTransport
import StabilizerLearning.Quantum.StabilizerEquivalence

/-! Actual generic fixed-constraint target geometry. No incidence, transitivity,
or operational comparison hypothesis is included in these definitions. -/
noncomputable section
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- Genericity refers to the original constraint subspace. -/
def IsGenericLagrangian (W : Constraint p n m) (L : Lagrangian p n) : Prop :=
  L.val ⊓ W.subspace = ⊥

/-- The actual surviving stabilizer directions. -/
def genericTargetSubspace (W : Constraint p n m) (L : Lagrangian p n) :
    Submodule (ZMod p) (PhaseSpace p n) :=
  L.val ⊓ symplecticBilinForm.orthogonal W.subspace

theorem mem_symplecticBilinForm_orthogonal_iff
    (U : Submodule (ZMod p) (PhaseSpace p n)) (z : PhaseSpace p n) :
    z ∈ symplecticBilinForm.orthogonal U ↔ z ∈ symplecticOrthogonal U := by
  constructor <;> intro hz w hw
  · exact symplecticBilinForm_isAlt.isRefl w z (hz w hw)
  · exact symplecticBilinForm_isAlt.isRefl z w (hz w hw)

theorem finrank_genericTargetSubspace (W : Constraint p n m) (L : Lagrangian p n)
    (hL : IsGenericLagrangian W L) :
    Module.finrank (ZMod p) (genericTargetSubspace W L) = m := by
  have h := finrank_lagrangian_inf_orthogonal symplecticBilinForm
    symplecticBilinForm_nondegenerate symplecticBilinForm_isAlt
    (show Module.finrank (ZMod p) (PhaseSpace p n) = 2*n by
      simp [PhaseSpace, Configuration, Module.finrank_prod]; omega)
    L.val W.subspace (lagrangian_orthogonal_eq L) L.property.2 hL
  rw [W.dimension] at h
  have hm := W.dimension_allowed
  change Module.finrank (ZMod p) (genericTargetSubspace W L) + (n-m) = n at h
  omega

/-- The surviving directions satisfy every original report-space side condition. -/
def genericReportSubspace (W : Constraint p n m) (L : Lagrangian p n)
    (hL : IsGenericLagrangian W L) : ReportSubspace W :=
  ⟨genericTargetSubspace W L,
    ⟨fun z hz w hw => L.property.1 z hz.1 w hw.1,
      finrank_genericTargetSubspace W L hL,
      fun z hz => (mem_symplecticBilinForm_orthogonal_iff W.subspace z).mp hz.2,
      by
        apply le_antisymm
        · calc
            genericTargetSubspace W L ⊓ W.subspace ≤ L.val ⊓ W.subspace :=
              inf_le_inf inf_le_left le_rfl
            _ = ⊥ := hL
        · exact bot_le⟩⟩

/-- An admissible m-dimensional report supported in the input Lagrangian has
exactly the generic target subspace. -/
theorem reportSubspace_eq_genericTarget (W : Constraint p n m)
    (L : Lagrangian p n) (hL : IsGenericLagrangian W L)
    (K : ReportSubspace W) (hK : K.val ≤ L.val) :
    K.val = genericTargetSubspace W L := by
  apply Submodule.eq_of_le_of_finrank_le
  · intro z hz
    exact ⟨hK hz,
      (mem_symplecticBilinForm_orthogonal_iff W.subspace z).mpr (K.property.2.2.1 z hz)⟩
  · rw [finrank_genericTargetSubspace W L hL, K.property.2.1]

def IsGenericLabel (W : Constraint p n m) (x : StabilizerLabel p n) : Prop :=
  IsGenericLagrangian W x.1

def IsGenericState (W : Constraint p n m) (x : StabilizerState p n) : Prop :=
  IsGenericLabel W ((stabilizerLabelStateEquiv p n).symm x)

/-- Restriction of the entire original Pauli assignment gives a legal report. -/
def genericLabelReport (W : Constraint p n m) (x : StabilizerLabel p n)
    (hx : IsGenericLabel W x) : Report W :=
  ⟨genericReportSubspace W x.1 hx, restrictAssignment p inf_le_left x.2⟩

/-- Actual Lagrangian completions containing the original constraint and
transverse to the actual input Lagrangian. -/
abbrev LagrangianCompletion (W : Constraint p n m) (L : Lagrangian p n) :=
  {M : Lagrangian p n // W.subspace ≤ M.val ∧ L.val ⊓ M.val = ⊥}

/-- Every generic input has a completion, in all prime characteristics and
also when m=0 or n=0. -/
theorem nonempty_lagrangianCompletion (W : Constraint p n m) (L : Lagrangian p n)
    (hL : IsGenericLagrangian W L) : Nonempty (LagrangianCompletion W L) := by
  obtain ⟨M, hWM, hM, hdM, hLM⟩ :=
    exists_isotropic_complement_containing (symplecticBilinForm (p := p) (n := n))
      symplecticBilinForm_nondegenerate symplecticBilinForm_isAlt
      (show Module.finrank (ZMod p) (PhaseSpace p n) = 2*n by
        simp [PhaseSpace, Configuration, Module.finrank_prod]; omega)
      L.val W.subspace (lagrangian_orthogonal_eq L) L.property.2
      (fun z hz w hw => W.isotropic w hw z hz) hL
  exact ⟨⟨⟨M, ⟨fun z hz w hw => hM hw z hz, hdM⟩⟩, hWM, hLM⟩⟩

/-- Containment in a transverse completion already implies genericity. -/
theorem isGenericLagrangian_of_completion (W : Constraint p n m)
    (L M : Lagrangian p n) (hWM : W.subspace ≤ M.val) (hLM : L.val ⊓ M.val = ⊥) :
    IsGenericLagrangian W L := by
  apply le_antisymm
  · exact (inf_le_inf le_rfl hWM).trans (le_of_eq hLM)
  · exact bot_le

end StabilizerLearning.FixedConstraints
