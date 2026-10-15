import ExactCriticalCurve.Quantum.ShorteningFiltration
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The actual row spaces of a free physical register -/
noncomputable section
open Classical Matrix
namespace ExactCriticalCurve.Quantum

 theorem freeRegisterSpace_mem_iff {α β : Type*} [Fintype α]
    (W : Submodule ℂ (β → ℂ)) (v : (α × β) → ℂ) :
    v ∈ freeRegisterSpace α W ↔ ∀ b, (fun x => v (b,x)) ∈ W := by
  constructor
  · intro hv
    refine Submodule.iSup_induction (motive := fun v => ∀ b, (fun x => v (b,x)) ∈ W)
      (fun b => W.map (freeRegisterSlot b)) hv ?_ ?_ ?_
    · intro b v hv a
      obtain ⟨w,hw,rfl⟩ := hv
      by_cases hab : a=b
      · simpa [freeRegisterSlot_apply,hab] using hw
      · simpa only [freeRegisterSlot_apply,if_neg hab] using W.zero_mem
    · intro b
      exact W.zero_mem
    · intro v w hv hw b
      exact W.add_mem (hv b) (hw b)
  · intro hv
    rw [← freeRegisterSlot_sum v]
    apply Submodule.sum_mem
    intro b _
    exact (le_iSup (fun b => W.map (freeRegisterSlot b)) b) ⟨_,hv b,rfl⟩

theorem freeRegisterSpace_inf {α β : Type*} [Fintype α]
    (V W : Submodule ℂ (β → ℂ)) :
    freeRegisterSpace α (V ⊓ W) = freeRegisterSpace α V ⊓ freeRegisterSpace α W := by
  ext v
  simp only [Submodule.mem_inf,freeRegisterSpace_mem_iff]
  exact forall_and

/-- A vector in the actual free-register span is exactly a family of actual rows. -/
def freeRegisterSpaceEquiv {α β : Type*} [Fintype α]
    (W : Submodule ℂ (β → ℂ)) : freeRegisterSpace α W ≃ₗ[ℂ] (α → W) where
  toFun v b := ⟨fun x => v.val (b,x), (freeRegisterSpace_mem_iff W v.val).mp v.property b⟩
  invFun w := ⟨fun x => (w x.1).val x.2, (freeRegisterSpace_mem_iff W _).mpr (fun b => (w b).property)⟩
  left_inv v := by rfl
  right_inv w := by rfl
  map_add' v w := by rfl
  map_smul' a v := by rfl

theorem freeRegisterSpace_finrank {α β : Type*} [Fintype α] [Fintype β]
    (W : Submodule ℂ (β → ℂ)) :
    Module.finrank ℂ (freeRegisterSpace α W) = Fintype.card α * Module.finrank ℂ W := by
  rw [(freeRegisterSpaceEquiv W).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp

end ExactCriticalCurve.Quantum
