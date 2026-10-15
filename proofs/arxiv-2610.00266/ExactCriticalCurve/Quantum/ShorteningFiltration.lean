import ExactCriticalCurve.Quantum.ShorteningCSS

/-! # Actual CSS filtration transport under the physical shortening map -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary

def freeRegisterSlot {α β : Type*} (b : α) :
    (β → ℂ) →ₗ[ℂ] ((α × β) → ℂ) where
  toFun v := fun x => if x.1 = b then v x.2 else 0
  map_add' v w := by ext x; split_ifs <;> simp_all
  map_smul' a v := by ext x; split_ifs <;> simp_all

@[simp] theorem freeRegisterSlot_apply {α β : Type*} (b : α) (v : β → ℂ) (x : α × β) :
    freeRegisterSlot b v x = if x.1 = b then v x.2 else 0 := rfl

/-- The actual span of all free-register basis vectors tensored with W. -/
def freeRegisterSpace (α : Type*) {β : Type*} (W : Submodule ℂ (β → ℂ)) :
    Submodule ℂ ((α × β) → ℂ) := ⨆ b : α, W.map (freeRegisterSlot b)

theorem freeRegisterSpace_iSup {α β ι : Type*}
    (W : ι → Submodule ℂ (β → ℂ)) :
    freeRegisterSpace α (⨆ i, W i) = ⨆ i, freeRegisterSpace α (W i) := by
  unfold freeRegisterSpace
  simp_rw [Submodule.map_iSup]
  exact iSup_comm

theorem freeRegisterSlot_sum {α β : Type*} [Fintype α] (v : (α × β) → ℂ) :
    (∑ b, freeRegisterSlot b (fun x => v (b,x))) = v := by
  funext x
  simp only [Finset.sum_apply, freeRegisterSlot_apply]
  simp

theorem freeRegister_kronecker_mulVec {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : Matrix β β ℂ) (v : (α × β) → ℂ) (b : α) (x : β) :
    (((1 : Matrix α α ℂ) ⊗ₖ P) *ᵥ v) (b,x) =
      (P *ᵥ (fun y => v (b,y))) x := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem freeRegister_kronecker_slot {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : Matrix β β ℂ) (b : α) (v : β → ℂ) :
    ((1 : Matrix α α ℂ) ⊗ₖ P) *ᵥ freeRegisterSlot b v =
      freeRegisterSlot b (P *ᵥ v) := by
  funext x
  rw [freeRegister_kronecker_mulVec]
  by_cases hx : x.1 = b
  · simp only [freeRegisterSlot_apply, hx, ite_true]
  · simp [freeRegisterSlot_apply, hx, Matrix.mulVec, dotProduct]

theorem freeRegisterSpace_range {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (P : Matrix β β ℂ) :
    freeRegisterSpace α (LinearMap.range P.mulVecLin) =
      LinearMap.range ((1 : Matrix α α ℂ) ⊗ₖ P).mulVecLin := by
  apply le_antisymm
  · apply iSup_le
    intro b
    rintro v ⟨z, ⟨y,rfl⟩,rfl⟩
    exact ⟨freeRegisterSlot b y, freeRegister_kronecker_slot P b y⟩
  · rintro v ⟨y,rfl⟩
    change (((1 : Matrix α α ℂ) ⊗ₖ P) *ᵥ y) ∈ _
    rw [← freeRegisterSlot_sum (((1 : Matrix α α ℂ) ⊗ₖ P) *ᵥ y)]
    apply Submodule.sum_mem
    intro b _
    apply (le_iSup (fun b => (LinearMap.range P.mulVecLin).map (freeRegisterSlot b)) b)
    refine ⟨fun x => (((1 : Matrix α α ℂ) ⊗ₖ P) *ᵥ y) (b,x), ?_, rfl⟩
    refine ⟨fun x => y (b,x), ?_⟩
    funext x
    exact (freeRegister_kronecker_mulVec P y b x).symm

variable {m : ℕ}

set_option maxHeartbeats 800000 in
/-- Each actual CSS code transports onto the free-register extended code. -/
theorem shortening_cssCode_map (n : ℕ) (h4 : 4 ∣ m+1)
    (M : Submodule (ZMod 2) (BinaryVector m)) (hM : IsDefect M) :
    (cssCode n M).map
      (shorteningSynthesis n (shortening_predecessor_odd h4)).mulVecLin =
    freeRegisterSpace (BinaryVector n) (cssCode n (shorteningExtend M)) := by
  let U := shorteningSynthesis n (shortening_predecessor_odd h4)
  let P := cssColumnProjection n M
  have h : (U*P)*(U*P)ᴴ = U*P*Uᴴ := by
    rw [Matrix.conjTranspose_mul, (cssColumnProjection_isHermitian n M).eq]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, cssColumnProjection_idempotent n M hM]
  rw [cssCode, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul,
    ← matrix_range_self_mul_conjTranspose]
  change LinearMap.range ((U*P)*(U*P)ᴴ).mulVecLin = _
  rw [h]
  change LinearMap.range
    (shorteningSynthesis n (shortening_predecessor_odd h4) * cssColumnProjection n M *
      (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ).mulVecLin = _
  rw [shorteningSynthesis_css n h4 M hM]
  exact (freeRegisterSpace_range (α := BinaryVector n)
    (cssColumnProjection n (shorteningExtend M))).symm

/-- Exact ordinary-to-exceptional CSS filtration transport, with the rank shift. -/
theorem shortening_ordinaryCSSFiltration_map (n r : ℕ) (h4 : 4 ∣ m+1) :
    (ordinaryCSSFiltration n m r).map
      (shorteningSynthesis n (shortening_predecessor_odd h4)).mulVecLin =
    freeRegisterSpace (BinaryVector n) (exceptionalCSSFiltration n (m+1) (r+1)) := by
  have hm4 : ¬ 4 ∣ m := by
    intro h
    obtain ⟨a,ha⟩ := h
    obtain ⟨b,hb⟩ := h4
    omega
  rw [ordinaryCSSFiltration, if_neg hm4, rawCSSFiltration, Submodule.map_iSup]
  have hmap (N : OrdinaryDefect m r) :
      (cssCode n N.val).map (shorteningSynthesis n (shortening_predecessor_odd h4)).mulVecLin =
        freeRegisterSpace (BinaryVector n) (cssCode n (shorteningExtend N.val)) :=
    shortening_cssCode_map n h4 N.val N.property.1
  simp_rw [hmap]
  rw [exceptionalCSSFiltration, freeRegisterSpace_iSup]
  apply le_antisymm
  · apply iSup_le
    intro N
    exact le_iSup (fun M : ExceptionalDefect (m+1) (r+1) =>
      freeRegisterSpace (BinaryVector n) (cssCode n M.val)) (shorteningDefectEquiv h4 r N)
  · apply iSup_le
    intro M
    obtain ⟨N,rfl⟩ := (shorteningDefectEquiv h4 r).surjective M
    exact le_iSup (fun N : OrdinaryDefect m r =>
      freeRegisterSpace (BinaryVector n) (cssCode n (shorteningExtend N.val))) N

end ExactCriticalCurve.Quantum

