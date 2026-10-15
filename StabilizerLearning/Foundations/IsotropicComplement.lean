import StabilizerLearning.Foundations.Symplectic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Preorder.Finite

/-! Characteristic-free extension inside the actual symplectic space. -/
noncomputable section
namespace StabilizerLearning

open Module Submodule LinearMap

section General
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite (Submodule K V)]
variable (B : LinearMap.BilinForm K V)
  (hB : B.Nondegenerate) (ha : B.IsAlt)
  {n : ℕ} (hdim : Module.finrank K V = 2*n)

omit [Finite (Submodule K V)] in
include hB ha hdim in
/-- An isotropic subspace cannot exceed half the ambient dimension. -/
theorem isotropic_finrank_le_half
    (U : Submodule K V) (hU : U ≤ B.orthogonal U) :
    Module.finrank K U ≤ n := by
  have hd := Submodule.finrank_mono hU
  rw [B.finrank_orthogonal hB ha.isRefl U, hdim] at hd
  omega

omit [Finite (Submodule K V)] in
include hB ha hdim in
/-- The orthogonal slice of a Lagrangian loses exactly one dimension for each
independent transverse constraint. -/
theorem finrank_lagrangian_inf_orthogonal
    (L U : Submodule K V) (hL : B.orthogonal L = L)
    (hdL : Module.finrank K L = n) (hLU : L ⊓ U = ⊥) :
    Module.finrank K (L ⊓ B.orthogonal U : Submodule K V) + Module.finrank K U = n := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq L U
  rw [hLU, finrank_bot, add_zero, hdL] at hs
  have horth : B.orthogonal (L ⊔ U) = L ⊓ B.orthogonal U := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, fun u hu => hx u (Submodule.mem_sup_right hu)⟩
      rw [← hL]
      exact fun l hl => hx l (Submodule.mem_sup_left hl)
    · rintro ⟨hxL, hxU⟩ y hy
      obtain ⟨l, hl, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
      have hx : x ∈ B.orthogonal L := hL.symm ▸ hxL
      change B (l+u) x = 0
      rw [map_add, LinearMap.add_apply, hx l hl, hxU u hu, add_zero]
  have hd := B.finrank_orthogonal hB ha.isRefl (L ⊔ U)
  rw [horth, hdim, hs] at hd
  have hle := Submodule.finrank_le (L ⊔ U)
  rw [hdim, hs] at hle
  omega

omit [FiniteDimensional K V] [Finite (Submodule K V)] in
include ha in
/-- A vector orthogonal to an isotropic subspace extends it isotropically,
including over fields of characteristic two. -/
theorem isotropic_sup_span_singleton
    (U : Submodule K V) (hU : U ≤ B.orthogonal U)
    (v : V) (hv : v ∈ B.orthogonal U) :
    U ⊔ (K ∙ v) ≤ B.orthogonal (U ⊔ (K ∙ v)) := by
  intro x hx y hy
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx₁
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy₁
  change B (y₀ + b • v) (x₀ + a • v) = 0
  have hxy : B y₀ x₀ = 0 := hU hx₀ y₀ hy₀
  have hxv : B x₀ v = 0 := hv x₀ hx₀
  have hyv : B y₀ v = 0 := hv y₀ hy₀
  have hvx : B v x₀ = 0 := ha.isRefl _ _ hxv
  simp [map_add, map_smul, hxy, hyv, hvx, ha v]

omit [FiniteDimensional K V] [Finite (Submodule K V)] in
/-- Adjoining a vector outside the sum preserves transversality. -/
theorem inf_sup_span_singleton_eq_bot
    (L U : Submodule K V) (hLU : L ⊓ U = ⊥)
    (v : V) (hv : v ∉ L ⊔ U) :
    L ⊓ (U ⊔ (K ∙ v)) = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp hx.2
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  by_cases ha : a = 0
  · have hxu : x = u := by simpa [ha] using hsum.symm
    have hmem : x ∈ L ⊓ U := ⟨hx.1, hxu ▸ hu⟩
    simpa [hLU] using hmem
  · exfalso
    apply hv
    have hav : a • v ∈ L ⊔ U := by
      have hmem := (L ⊔ U).sub_mem
        (show x ∈ L ⊔ U from Submodule.mem_sup_left hx.1)
        (show u ∈ L ⊔ U from Submodule.mem_sup_right hu)
      have heq : x-u = a • v := by rw [← hsum]; abel
      rwa [heq] at hmem
    exact (Submodule.smul_mem_iff _ ha).mp hav

include hB ha hdim in
/-- Every isotropic subspace disjoint from a Lagrangian is contained in an
actual Lagrangian complement. No complement or transitivity assumption is used. -/
theorem exists_isotropic_complement_containing
    (L W : Submodule K V) (hL : B.orthogonal L = L)
    (hdL : Module.finrank K L = n)
    (hW : W ≤ B.orthogonal W) (hLW : L ⊓ W = ⊥) :
    ∃ M : Submodule K V, W ≤ M ∧ M ≤ B.orthogonal M ∧
      Module.finrank K M = n ∧ L ⊓ M = ⊥ := by
  classical
  let S : Set (Submodule K V) :=
    {M | W ≤ M ∧ M ≤ B.orthogonal M ∧ L ⊓ M = ⊥}
  obtain ⟨M, hM, hmax⟩ := S.toFinite.exists_maximal ⟨W, le_rfl, hW, hLW⟩
  refine ⟨M, hM.1, hM.2.1, ?_, hM.2.2⟩
  have hdM := isotropic_finrank_le_half B hB ha hdim M hM.2.1
  by_contra hne
  have hlt : Module.finrank K M < n := lt_of_le_of_ne hdM hne
  have hslice := finrank_lagrangian_inf_orthogonal B hB ha hdim
    L M hL hdL hM.2.2
  have hmod : (L ⊔ M) ⊓ B.orthogonal M = (L ⊓ B.orthogonal M) ⊔ M := by
    apply le_antisymm
    · intro x hx
      obtain ⟨l, hl, u, hu, rfl⟩ := Submodule.mem_sup.mp hx.1
      have hlu : l + u ∈ B.orthogonal M := hx.2
      have hlorth : l ∈ B.orthogonal M := by
        have ht := (B.orthogonal M).sub_mem hlu (hM.2.1 hu)
        simpa using ht
      exact Submodule.mem_sup.mpr ⟨l, ⟨hl, hlorth⟩, u, hu, rfl⟩
    · apply sup_le
      · exact inf_le_inf le_sup_left le_rfl
      · exact le_inf le_sup_right hM.2.1
  have hdisj : (L ⊓ B.orthogonal M) ⊓ M = ⊥ := by
    apply le_antisymm
    · calc
        (L ⊓ B.orthogonal M) ⊓ M ≤ L ⊓ M := inf_le_inf inf_le_left le_rfl
        _ = ⊥ := hM.2.2
    · exact bot_le
  have hsliceDim : Module.finrank K ((L ⊔ M) ⊓ B.orthogonal M : Submodule K V) = n := by
    rw [hmod]
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (L ⊓ B.orthogonal M) M
    rw [hdisj, finrank_bot, add_zero, hslice] at hd
    exact hd
  have hnot : ¬ B.orthogonal M ≤ L ⊔ M := by
    intro hle
    have heq : (L ⊔ M) ⊓ B.orthogonal M = B.orthogonal M := inf_eq_right.mpr hle
    rw [heq, B.finrank_orthogonal hB ha.isRefl M, hdim] at hsliceDim
    omega
  obtain ⟨v, hv, hvo⟩ := SetLike.not_le_iff_exists.mp hnot
  let N := M ⊔ (K ∙ v)
  have hN : N ∈ S := ⟨hM.1.trans le_sup_left,
    isotropic_sup_span_singleton B ha M hM.2.1 v hv,
    inf_sup_span_singleton_eq_bot L M hM.2.2 v hvo⟩
  have hNM : N ≤ M := hmax hN le_sup_left
  apply hvo
  exact Submodule.mem_sup_right (hNM (Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self v)))


include hB ha hdim in
/-- Every isotropic subspace extends to half dimension, by actual finite
maximization and nondegeneracy. -/
theorem exists_isotropic_extension
    (W : Submodule K V) (hW : W ≤ B.orthogonal W) :
    ∃ M : Submodule K V, W ≤ M ∧ M ≤ B.orthogonal M ∧ Module.finrank K M = n := by
  classical
  let S : Set (Submodule K V) := {M | W ≤ M ∧ M ≤ B.orthogonal M}
  obtain ⟨M,hM,hmax⟩ := S.toFinite.exists_maximal ⟨W,le_rfl,hW⟩
  refine ⟨M,hM.1,hM.2,?_⟩
  have hbound := isotropic_finrank_le_half B hB ha hdim M hM.2
  by_contra hne
  have hlt : Module.finrank K M < n := lt_of_le_of_ne hbound hne
  have hnot : ¬ B.orthogonal M ≤ M := by
    intro hle
    have h := Submodule.finrank_mono hle
    rw [B.finrank_orthogonal hB ha.isRefl M, hdim] at h
    omega
  obtain ⟨v,hv,hvo⟩ := SetLike.not_le_iff_exists.mp hnot
  have hN : M ⊔ (K ∙ v) ∈ S :=
    ⟨hM.1.trans le_sup_left, isotropic_sup_span_singleton B ha M hM.2 v hv⟩
  have hNM : M ⊔ (K ∙ v) ≤ M := hmax hN le_sup_left
  exact hvo (hNM (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))

end General
end StabilizerLearning
