import StabilizerLearning.FiniteCopy.UniformExperiment
import StabilizerLearning.Quantum.UnitaryTransport

/-! Bijections of all collective POVMs under an actual unitary, with exact
finite-prior normalization and statewise Born scores retained. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning
open Quantum

def unitaryExperimentPOVMEquiv {Ω Y Y' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Y] [Fintype Y']
    (U : Matrix.unitaryGroup Ω ℂ) (er : Y ≃ Y') : POVM Ω Y ≃ POVM Ω Y' :=
  (POVM.unitaryEquiv U).trans (POVM.relabel er)

theorem uniformTargetSuccess_unitary {Ω X Y : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype X] [Fintype Y]
    (U : Matrix.unitaryGroup Ω ℂ) (ρ : X → Matrix Ω Ω ℂ) (t : X → Y)
    (M : POVM Ω Y) :
    uniformTargetSuccess (fun x => unitaryConjugate U (ρ x)) t (POVM.unitaryEquiv U M) =
      uniformTargetSuccess ρ t M := by
  simp only [uniformTargetSuccess, POVM.unitaryEquiv_effect, born_unitaryConjugate]

theorem uniformTargetSuccess_unitary_transport {Ω X X' Y Y' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (U : Matrix.unitaryGroup Ω ℂ) (ex : X ≃ X') (er : Y ≃ Y')
    (ρ : X → Matrix Ω Ω ℂ) (ρ' : X' → Matrix Ω Ω ℂ)
    (t : X → Y) (t' : X' → Y')
    (hρ : ∀ x, ρ' (ex x) = unitaryConjugate U (ρ x))
    (ht : ∀ x, t' (ex x) = er (t x)) (M : POVM Ω Y) :
    uniformTargetSuccess ρ' t' (unitaryExperimentPOVMEquiv U er M) =
      uniformTargetSuccess ρ t M := by
  rw [← uniformTargetSuccess_state_equiv ex]
  unfold uniformTargetSuccess
  congr 1
  funext x
  simp only [Function.comp_apply, hρ, ht, unitaryExperimentPOVMEquiv, Equiv.trans_apply,
    POVM.relabel_effect, Equiv.symm_apply_apply, POVM.unitaryEquiv_effect,
    born_unitaryConjugate]

theorem range_uniformTargetSuccess_unitary_transport {Ω X X' Y Y' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (U : Matrix.unitaryGroup Ω ℂ) (ex : X ≃ X') (er : Y ≃ Y')
    (ρ : X → Matrix Ω Ω ℂ) (ρ' : X' → Matrix Ω Ω ℂ)
    (t : X → Y) (t' : X' → Y')
    (hρ : ∀ x, ρ' (ex x) = unitaryConjugate U (ρ x))
    (ht : ∀ x, t' (ex x) = er (t x)) :
    Set.range (uniformTargetSuccess ρ' t') = Set.range (uniformTargetSuccess ρ t) := by
  ext s
  constructor
  · rintro ⟨M, rfl⟩
    obtain ⟨N, rfl⟩ := (unitaryExperimentPOVMEquiv U er).surjective M
    exact ⟨N, (uniformTargetSuccess_unitary_transport U ex er ρ ρ' t t' hρ ht N).symm⟩
  · rintro ⟨M, rfl⟩
    exact ⟨unitaryExperimentPOVMEquiv U er M,
      uniformTargetSuccess_unitary_transport U ex er ρ ρ' t t' hρ ht M⟩

end StabilizerLearning
