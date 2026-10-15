import StabilizerLearning.FixedConstraints.GenericGeometry
import Mathlib.LinearAlgebra.Projection

/-! Concrete symplectic transport between generic fixed-W Lagrangians. -/
noncomputable section
namespace StabilizerLearning

section LinearExtension
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Equal-dimensional subspaces containing W admit a linear equivalence that
fixes every vector of W. This is a linear-algebra construction, not a symmetry
assumption on the input ensemble. -/
theorem exists_linearEquiv_fixing_subspace
    (W M N : Submodule K V) (hWM : W ≤ M) (hWN : W ≤ N)
    (hd : Module.finrank K M = Module.finrank K N) :
    ∃ e : M ≃ₗ[K] N, ∀ w : W,
      e ⟨w.val, hWM w.property⟩ = ⟨w.val, hWN w.property⟩ := by
  let U := W.comap M.subtype
  let U' := W.comap N.subtype
  let eU : U ≃ₗ[K] U' :=
    (Submodule.comapSubtypeEquivOfLe hWM).trans
      (Submodule.comapSubtypeEquivOfLe hWN).symm
  obtain ⟨A, hA⟩ := U.exists_isCompl
  obtain ⟨A', hA'⟩ := U'.exists_isCompl
  have heqdim : Module.finrank K A = Module.finrank K A' := by
    have h₁ := Submodule.finrank_add_eq_of_isCompl hA
    have h₂ := Submodule.finrank_add_eq_of_isCompl hA'
    have h₃ := eU.finrank_eq
    omega
  let eA : A ≃ₗ[K] A' := LinearEquiv.ofFinrankEq _ _ heqdim
  let d := Submodule.prodEquivOfIsCompl U A hA
  let d' := Submodule.prodEquivOfIsCompl U' A' hA'
  refine ⟨d.symm.trans ((eU.prodCongr eA).trans d'), ?_⟩
  intro w
  let wU : U := ⟨⟨w.val, hWM w.property⟩, w.property⟩
  change d' ((eU.prodCongr eA) (d.symm (wU : M))) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp only [LinearEquiv.prodCongr_apply, map_zero]
  change (eU wU : N) + 0 = _
  rw [add_zero]
  rfl

end LinearExtension

namespace Quantum
variable {p n : ℕ} [Fact p.Prime]

theorem isCompl_of_lagrangian_inf_eq_bot (L M : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) : IsCompl L.val M.val := by
  refine ⟨disjoint_iff.mpr hLM, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq L.val M.val
  rw [hLM, finrank_bot, add_zero, L.property.2, M.property.2] at h
  simpa [PhaseSpace, Configuration, Module.finrank_prod] using h

/-- Actual pairing of two complementary Lagrangians. -/
def lagrangianPairingMap (L M : Lagrangian p n) :
    L.val →ₗ[ZMod p] Module.Dual (ZMod p) M.val :=
  LinearMap.comp M.val.dualRestrict
    (LinearMap.comp (symplecticBilinForm (p := p) (n := n)) L.val.subtype)

@[simp] theorem lagrangianPairingMap_apply (L M : Lagrangian p n)
    (l : L.val) (w : M.val) :
    lagrangianPairingMap L M l w = symplecticPairing l.val w.val := rfl

/-- Complementarity makes the restricted pairing an actual dual equivalence. -/
def lagrangianPairingEquiv (L M : Lagrangian p n) (hLM : L.val ⊓ M.val = ⊥) :
    L.val ≃ₗ[ZMod p] Module.Dual (ZMod p) M.val :=
  LinearMap.linearEquivOfInjective (lagrangianPairingMap L M)
    (by
      intro l l' h
      apply Subtype.ext
      apply sub_eq_zero.mp
      have hm : l.val-l'.val ∈ symplecticBilinForm.orthogonal M.val := by
        intro w hw
        have heq := congrArg (fun f : Module.Dual (ZMod p) M.val => f ⟨w, hw⟩) h
        have hz : symplecticBilinForm (l.val-l'.val) w = 0 := by
          change symplecticPairing l.val w = symplecticPairing l'.val w at heq
          rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
          exact heq
        exact symplecticBilinForm_isAlt.isRefl _ _ hz
      rw [lagrangian_orthogonal_eq M] at hm
      have hx : l.val-l'.val ∈ L.val ⊓ M.val :=
        ⟨L.val.sub_mem l.property l'.property, hm⟩
      simpa [hLM] using hx)
    (by rw [Subspace.dual_finrank_eq, L.property.2, M.property.2])

@[simp] theorem lagrangianPairingEquiv_apply (L M : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (l : L.val) (w : M.val) :
    lagrangianPairingEquiv L M hLM l w = symplecticPairing l.val w.val := rfl

/-- Transport on the first Lagrangian is forced by transport on its dual
complement. -/
def complementaryLagrangianTransport
    (L M L' M' : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (hLM' : L'.val ⊓ M'.val = ⊥)
    (e : M.val ≃ₗ[ZMod p] M'.val) : L.val ≃ₗ[ZMod p] L'.val :=
  (lagrangianPairingEquiv L M hLM).trans
    (e.symm.dualMap.trans (lagrangianPairingEquiv L' M' hLM').symm)

theorem complementaryLagrangianTransport_pairing
    (L M L' M' : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (hLM' : L'.val ⊓ M'.val = ⊥)
    (e : M.val ≃ₗ[ZMod p] M'.val) (l : L.val) (w : M.val) :
    symplecticPairing (complementaryLagrangianTransport L M L' M' hLM hLM' e l).val
      (e w).val = symplecticPairing l.val w.val := by
  change lagrangianPairingEquiv L' M' hLM'
    (complementaryLagrangianTransport L M L' M' hLM hLM' e l) (e w) = _
  simp [complementaryLagrangianTransport]

/-- Symplectic extension of an arbitrary linear equivalence of complementary
Lagrangians. -/
def complementarySymplecticTransport
    (L M L' M' : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (hLM' : L'.val ⊓ M'.val = ⊥)
    (e : M.val ≃ₗ[ZMod p] M'.val) :
    PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n :=
  (Submodule.prodEquivOfIsCompl L.val M.val
    (isCompl_of_lagrangian_inf_eq_bot L M hLM)).symm.trans
      (((complementaryLagrangianTransport L M L' M' hLM hLM' e).prodCongr e).trans
        (Submodule.prodEquivOfIsCompl L'.val M'.val
          (isCompl_of_lagrangian_inf_eq_bot L' M' hLM')))

@[simp] theorem complementarySymplecticTransport_apply_add
    (L M L' M' : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (hLM' : L'.val ⊓ M'.val = ⊥)
    (e : M.val ≃ₗ[ZMod p] M'.val) (l : L.val) (w : M.val) :
    complementarySymplecticTransport L M L' M' hLM hLM' e (l.val+w.val) =
      (complementaryLagrangianTransport L M L' M' hLM hLM' e l).val + (e w).val := by
  change (Submodule.prodEquivOfIsCompl L'.val M'.val (isCompl_of_lagrangian_inf_eq_bot L' M' hLM'))
    (((complementaryLagrangianTransport L M L' M' hLM hLM' e).prodCongr e)
      ((Submodule.prodEquivOfIsCompl L.val M.val (isCompl_of_lagrangian_inf_eq_bot L M hLM)).symm
        ((Submodule.prodEquivOfIsCompl L.val M.val (isCompl_of_lagrangian_inf_eq_bot L M hLM)) (l,w)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem complementarySymplecticTransport_pairing
    (L M L' M' : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (hLM' : L'.val ⊓ M'.val = ⊥)
    (e : M.val ≃ₗ[ZMod p] M'.val) (z w : PhaseSpace p n) :
    symplecticPairing (complementarySymplecticTransport L M L' M' hLM hLM' e z)
      (complementarySymplecticTransport L M L' M' hLM hLM' e w) =
      symplecticPairing z w := by
  obtain ⟨⟨l, a⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl L.val M.val
    (isCompl_of_lagrangian_inf_eq_bot L M hLM)).surjective z
  obtain ⟨⟨l', a'⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl L.val M.val
    (isCompl_of_lagrangian_inf_eq_bot L M hLM)).surjective w
  change symplecticPairing
    (complementarySymplecticTransport L M L' M' hLM hLM' e (l.val+a.val))
    (complementarySymplecticTransport L M L' M' hLM hLM' e (l'.val+a'.val)) =
    symplecticPairing (l.val+a.val) (l'.val+a'.val)
  rw [complementarySymplecticTransport_apply_add, complementarySymplecticTransport_apply_add]
  let f := complementaryLagrangianTransport L M L' M' hLM hLM' e
  change symplecticBilinForm ((f l).val+(e a).val) ((f l').val+(e a').val) =
    symplecticBilinForm (l.val+a.val) (l'.val+a'.val)
  simp only [map_add, LinearMap.add_apply]
  have hll := L.property.1 l.val l.property l'.val l'.property
  have haa := M.property.1 a.val a.property a'.val a'.property
  have hff := L'.property.1 (f l).val (f l).property (f l').val (f l').property
  have hee := M'.property.1 (e a).val (e a).property (e a').val (e a').property
  have hcross := complementaryLagrangianTransport_pairing L M L' M' hLM hLM' e l a'
  have hcross' := complementaryLagrangianTransport_pairing L M L' M' hLM hLM' e l' a
  simp only [symplecticBilinForm_apply]
  rw [hll, haa, hff, hee, hcross]
  rw [symplecticPairing_swap (e a).val (f l').val, hcross',
    symplecticPairing_swap a.val l'.val]


@[simp] theorem complementarySymplecticTransport_apply_right
    (L M L' M' : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (hLM' : L'.val ⊓ M'.val = ⊥)
    (e : M.val ≃ₗ[ZMod p] M'.val) (w : M.val) :
    complementarySymplecticTransport L M L' M' hLM hLM' e w.val = (e w).val := by
  simpa using complementarySymplecticTransport_apply_add L M L' M' hLM hLM' e 0 w

@[simp] theorem complementarySymplecticTransport_apply_left
    (L M L' M' : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (hLM' : L'.val ⊓ M'.val = ⊥)
    (e : M.val ≃ₗ[ZMod p] M'.val) (l : L.val) :
    complementarySymplecticTransport L M L' M' hLM hLM' e l.val =
      (complementaryLagrangianTransport L M L' M' hLM hLM' e l).val := by
  simpa using complementarySymplecticTransport_apply_add L M L' M' hLM hLM' e l 0

theorem complementarySymplecticTransport_map_left
    (L M L' M' : Lagrangian p n)
    (hLM : L.val ⊓ M.val = ⊥) (hLM' : L'.val ⊓ M'.val = ⊥)
    (e : M.val ≃ₗ[ZMod p] M'.val) :
    L.val.map (complementarySymplecticTransport L M L' M' hLM hLM' e).toLinearMap =
      L'.val := by
  ext z
  constructor
  · rintro ⟨l, hl, rfl⟩
    change complementarySymplecticTransport L M L' M' hLM hLM' e
      (⟨l,hl⟩ : L.val).val ∈ L'.val
    rw [complementarySymplecticTransport_apply_left]
    exact (complementaryLagrangianTransport L M L' M' hLM hLM' e ⟨l,hl⟩).property
  · intro hz
    obtain ⟨l, hl⟩ :=
      (complementaryLagrangianTransport L M L' M' hLM hLM' e).surjective ⟨z,hz⟩
    refine ⟨l.val, l.property, ?_⟩
    change complementarySymplecticTransport L M L' M' hLM hLM' e l.val = z
    rw [complementarySymplecticTransport_apply_left, hl]

end Quantum

namespace FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- The actual setwise stabilizer of W is transitive on the generic Lagrangian
stratum; the constructed map in fact fixes W pointwise. -/
theorem exists_symplectic_map_fixing_constraint
    (W : Constraint p n m) (L L' : Lagrangian p n)
    (hL : IsGenericLagrangian W L) (hL' : IsGenericLagrangian W L') :
    ∃ g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n,
      (∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) ∧
      (∀ w ∈ W.subspace, g w = w) ∧ L.val.map g.toLinearMap = L'.val := by
  obtain ⟨⟨M, hWM, hLM⟩⟩ := nonempty_lagrangianCompletion W L hL
  obtain ⟨⟨M', hWM', hLM'⟩⟩ := nonempty_lagrangianCompletion W L' hL'
  obtain ⟨e, he⟩ := exists_linearEquiv_fixing_subspace
    W.subspace M.val M'.val hWM hWM' (M.property.2.trans M'.property.2.symm)
  refine ⟨complementarySymplecticTransport L M L' M' hLM hLM' e,
    complementarySymplecticTransport_pairing L M L' M' hLM hLM' e, ?_,
    complementarySymplecticTransport_map_left L M L' M' hLM hLM' e⟩
  intro w hw
  change complementarySymplecticTransport L M L' M' hLM hLM' e
    (⟨w,hWM hw⟩ : M.val).val = w
  rw [complementarySymplecticTransport_apply_right, he ⟨w,hw⟩]

end FixedConstraints
end StabilizerLearning
