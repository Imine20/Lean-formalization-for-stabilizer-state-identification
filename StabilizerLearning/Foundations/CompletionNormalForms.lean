import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

noncomputable section
namespace StabilizerLearning
open Matrix LinearMap Module

variable {F : Type*} [Field F]

/-- A kernel complement maps isomorphically onto the actual image. -/
def complementRangeEquiv {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W)
    (K : Submodule F V) (hK : IsCompl (LinearMap.ker f) K) :
    K ≃ₗ[F] LinearMap.range f :=
  (Submodule.quotientEquivOfIsCompl (LinearMap.ker f) K hK).symm.trans
    f.quotKerEquivRange

@[simp] theorem complementRangeEquiv_apply {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W)
    (K : Submodule F V) (hK : IsCompl (LinearMap.ker f) K) (x : K) :
    (complementRangeEquiv f K hK x : W) = f x := by
  simp [complementRangeEquiv]

@[simp] theorem complementRangeEquiv_symm_apply {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W)
    (K : Submodule F V) (hK : IsCompl (LinearMap.ker f) K)
    (x : LinearMap.range f) :
    f (complementRangeEquiv f K hK |>.symm x) = x := by
  have h := congrArg Subtype.val ((complementRangeEquiv f K hK).apply_symm_apply x)
  rw [complementRangeEquiv_apply] at h
  exact h

/-- Coordinate maps constructed from complements, with the image coordinates shared.
This proves existence of rectangular rank normal form without assuming it. -/
theorem exists_rank_coordinates {m n : ℕ} (C : Matrix (Fin m) (Fin n) F) :
    ∃ e : (Fin C.rank ⊕ Fin (n - C.rank) → F) ≃ₗ[F] (Fin n → F),
      ∃ g : (Fin C.rank ⊕ Fin (m - C.rank) → F) ≃ₗ[F] (Fin m → F),
        ∀ v, C *ᵥ e v = g (Sum.elim (fun i => v (Sum.inl i)) (fun _ => 0)) := by
  let f := C.toLin'
  obtain ⟨K, hK⟩ := (LinearMap.ker f).exists_isCompl
  obtain ⟨L, hL⟩ := (LinearMap.range f).exists_isCompl
  have hr : Module.finrank F (LinearMap.range f) = C.rank := rfl
  have hk : Module.finrank F (LinearMap.ker f) = n - C.rank := by
    have h := f.finrank_range_add_finrank_ker
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    rw [hr] at h
    omega
  have hl : Module.finrank F L = m - C.rank := by
    have h := (Submodule.prodEquivOfIsCompl (LinearMap.range f) L hL).finrank_eq
    simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] at h
    rw [hr] at h
    omega
  let bR := (Module.finBasisOfFinrankEq F (LinearMap.range f) hr).equivFun.symm
  let bK := (Module.finBasisOfFinrankEq F (LinearMap.ker f) hk).equivFun.symm
  let bL := (Module.finBasisOfFinrankEq F L hl).equivFun.symm
  let e := (LinearEquiv.sumArrowLequivProdArrow (Fin C.rank) (Fin (n-C.rank)) F F).trans
    (((bR.trans (complementRangeEquiv f K hK).symm).prodCongr bK).trans
      (Submodule.prodEquivOfIsCompl K (LinearMap.ker f) hK.symm))
  let g := (LinearEquiv.sumArrowLequivProdArrow (Fin C.rank) (Fin (m-C.rank)) F F).trans
    ((bR.prodCongr bL).trans (Submodule.prodEquivOfIsCompl (LinearMap.range f) L hL))
  refine ⟨e, g, ?_⟩
  intro v
  change f _ = _
  simp only [e, g, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    Submodule.coe_prodEquivOfIsCompl', map_add, complementRangeEquiv_symm_apply]
  have hz : f (bK (fun i => v (Sum.inr i))) = 0 :=
    (bK (fun i => v (Sum.inr i))).property
  change (bR (fun i => v (Sum.inl i)) : Fin m → F) +
    f (bK (fun i => v (Sum.inr i))) =
    (bR (fun i => v (Sum.inl i)) : Fin m → F) + ↑(bL 0)
  rw [hz]
  simp

/-- The matrices of a linear coordinate equivalence and its inverse are two-sided inverses,
including when their finite index types are different. -/
theorem coordinate_matrices_inverse {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : (ι → F) ≃ₗ[F] (κ → F)) :
    LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1 ∧
    LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
  constructor
  · rw [← LinearMap.toMatrix'_comp, e.comp_symm, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, e.symm_comp, LinearMap.toMatrix'_id]

/-- Rectangular normal form with explicit inverses.  The rank is the actual matrix rank. -/
theorem exists_rectangular_normal_form {m n : ℕ} (C : Matrix (Fin m) (Fin n) F) :
    ∃ R : Matrix (Fin C.rank ⊕ Fin (m-C.rank)) (Fin m) F,
      ∃ R' : Matrix (Fin m) (Fin C.rank ⊕ Fin (m-C.rank)) F,
      ∃ S : Matrix (Fin n) (Fin C.rank ⊕ Fin (n-C.rank)) F,
      ∃ S' : Matrix (Fin C.rank ⊕ Fin (n-C.rank)) (Fin n) F,
        R * R' = 1 ∧ R' * R = 1 ∧ S * S' = 1 ∧ S' * S = 1 ∧
        R * C * S = Matrix.fromBlocks 1 0 0 0 := by
  obtain ⟨e, g, h⟩ := exists_rank_coordinates C
  let R := LinearMap.toMatrix' g.symm.toLinearMap
  let R' := LinearMap.toMatrix' g.toLinearMap
  let S := LinearMap.toMatrix' e.toLinearMap
  let S' := LinearMap.toMatrix' e.symm.toLinearMap
  obtain ⟨hg, hg'⟩ := coordinate_matrices_inverse g
  obtain ⟨he, he'⟩ := coordinate_matrices_inverse e
  refine ⟨R, R', S, S', hg', hg, he, he', ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_mul, LinearMap.comp_apply, R, S,
    Matrix.toLin'_toMatrix', LinearEquiv.coe_coe, Matrix.toLin'_apply]
  rw [h, g.symm_apply_apply]
  ext i
  cases i with
  | inl i => simp [Matrix.fromBlocks_mulVec]
  | inr i => simp [Matrix.fromBlocks_mulVec]

/-- A left inverse proves injectivity even for matrices with different index types. -/
theorem mulVec_injective_of_matrix_left_inverse {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (P : Matrix κ ι F) (Q : Matrix ι κ F) (h : Q * P = 1) :
    Function.Injective P.mulVec := by
  intro a b hab
  have hh := congrArg (fun v => Q *ᵥ v) hab
  simpa only [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] using hh

/-- Every symmetric matrix has a nonsingular block and its true radical as complementary
coordinates. This is valid also in characteristic two; no diagonalization is assumed. -/
theorem exists_symmetric_normal_form {n : ℕ} (B : Matrix (Fin n) (Fin n) F)
    (hB : B.IsSymm) :
    ∃ P : Matrix (Fin n) (Fin B.rank ⊕ Fin (n-B.rank)) F,
      ∃ P' : Matrix (Fin B.rank ⊕ Fin (n-B.rank)) (Fin n) F,
      ∃ D : Matrix (Fin B.rank) (Fin B.rank) F,
        P * P' = 1 ∧ P' * P = 1 ∧ IsUnit D ∧ D.IsSymm ∧
        Pᵀ * B * P = Matrix.fromBlocks D 0 0 0 := by
  obtain ⟨e, g, h⟩ := exists_rank_coordinates B
  let P := LinearMap.toMatrix' e.toLinearMap
  let P' := LinearMap.toMatrix' e.symm.toLinearMap
  let H := Pᵀ * B * P
  let D := H.submatrix Sum.inl Sum.inl
  obtain ⟨he, he'⟩ := coordinate_matrices_inverse e
  have hP : P * P' = 1 := he
  have hP' : P' * P = 1 := he'
  have hHs : H.IsSymm := by
    dsimp [H]
    rw [Matrix.IsSymm]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hB.eq,
      Matrix.mul_assoc]
  have hright : ∀ j : Fin (n-B.rank), ∀ i, H i (Sum.inr j) = 0 := by
    intro j
    have hsingle : B *ᵥ e (Pi.single (Sum.inr j) 1) = 0 := by
      rw [h]
      have hs : (Sum.elim (fun i : Fin B.rank => (Pi.single (Sum.inr j) (1 : F) :
          Fin B.rank ⊕ Fin (n-B.rank) → F) (Sum.inl i)) (fun _ : Fin (n-B.rank) => 0) :
          Fin B.rank ⊕ Fin (n-B.rank) → F) = 0 := by
        ext i
        cases i <;> simp
      rw [hs, map_zero]
    have hh : H *ᵥ Pi.single (Sum.inr j) 1 = 0 := by
      simp only [H, ← Matrix.mulVec_mulVec, P, LinearMap.toMatrix'_mulVec,
        LinearEquiv.coe_coe, hsingle, Matrix.mulVec_zero]
    simpa only [Matrix.mulVec_single_one, Pi.zero_apply] using congrFun hh
  have hblocks : H = Matrix.fromBlocks D 0 0 0 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact hright j (Sum.inl i)
    | inr i =>
      cases j with
      | inl j => simpa only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply] using
          (hHs.apply (Sum.inr i) (Sum.inl j)).symm.trans (hright i (Sum.inl j))
      | inr j => exact hright j (Sum.inr i)
  have hDs : D.IsSymm := hHs.submatrix _
  have hDi : IsUnit D := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    change Function.Injective D.mulVecLin
    rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    intro x hx
    let v : Fin B.rank ⊕ Fin (n-B.rank) → F := Sum.elim x (fun _ => 0)
    have hv : H *ᵥ v = 0 := by
      rw [hblocks]
      ext i
      cases i <;> simp [Matrix.fromBlocks_mulVec, v, hx]
    have htrans : P'ᵀ * Pᵀ = 1 := by
      rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
    have hinj := mulVec_injective_of_matrix_left_inverse Pᵀ P'ᵀ htrans
    have hb : B *ᵥ e v = 0 := by
      apply hinj
      simpa only [H, ← Matrix.mulVec_mulVec, P, LinearMap.toMatrix'_mulVec,
        LinearEquiv.coe_coe, Matrix.mulVec_zero] using hv
    have hg : g v = 0 := by simpa only [v] using (h v).symm.trans hb
    have hz : v = 0 := g.injective (hg.trans g.map_zero.symm)
    ext i
    exact congrFun hz (Sum.inl i)
  exact ⟨P, P', D, hP, hP', hDi, hDs, hblocks⟩

structure RectangularNormalization {m n : ℕ} (C : Matrix (Fin m) (Fin n) F) where
  R : Matrix (Fin C.rank ⊕ Fin (m-C.rank)) (Fin m) F
  Ri : Matrix (Fin m) (Fin C.rank ⊕ Fin (m-C.rank)) F
  S : Matrix (Fin n) (Fin C.rank ⊕ Fin (n-C.rank)) F
  Si : Matrix (Fin C.rank ⊕ Fin (n-C.rank)) (Fin n) F
  hRRi : R * Ri = 1
  hRiR : Ri * R = 1
  hSSi : S * Si = 1
  hSiS : Si * S = 1
  normal_form : R * C * S = Matrix.fromBlocks 1 0 0 0

/-- Chosen coordinates from the proved existence theorem. Choice supplies no mathematical premise. -/
def rectangularNormalization {m n : ℕ} (C : Matrix (Fin m) (Fin n) F) :
    RectangularNormalization C := Classical.choice (by
  obtain ⟨R, Ri, S, Si, hRRi, hRiR, hSSi, hSiS, h⟩ := exists_rectangular_normal_form C
  exact ⟨⟨R, Ri, S, Si, hRRi, hRiR, hSSi, hSiS, h⟩⟩)

structure SymmetricNormalization {n : ℕ} (B : Matrix (Fin n) (Fin n) F) where
  P : Matrix (Fin n) (Fin B.rank ⊕ Fin (n-B.rank)) F
  Pi : Matrix (Fin B.rank ⊕ Fin (n-B.rank)) (Fin n) F
  D : Matrix (Fin B.rank) (Fin B.rank) F
  hPPi : P * Pi = 1
  hPiP : Pi * P = 1
  isUnit_D : IsUnit D
  isSymm_D : D.IsSymm
  normal_form : Pᵀ * B * P = Matrix.fromBlocks D 0 0 0

def symmetricNormalization {n : ℕ} (B : Matrix (Fin n) (Fin n) F)
    (hB : B.IsSymm) : SymmetricNormalization B := Classical.choice (by
  obtain ⟨P, Pi, D, hPPi, hPiP, isUnit_D, isSymm_D, h⟩ := exists_symmetric_normal_form B hB
  exact ⟨⟨P, Pi, D, hPPi, hPiP, isUnit_D, isSymm_D, h⟩⟩)

end StabilizerLearning
