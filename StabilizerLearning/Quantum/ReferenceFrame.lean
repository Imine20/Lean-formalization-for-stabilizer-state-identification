import StabilizerLearning.Quantum.TransverseGraph
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Ordered Lagrangian frames and symplectic coordinates, in every characteristic. -/
noncomputable section
open scoped BigOperators Matrix
open Module
namespace StabilizerLearning
variable {p n : ℕ} [Fact p.Prime]

/-- The concrete alternating pairing, packaged as a bilinear form. -/
def symplecticBilinForm : LinearMap.BilinForm (ZMod p) (PhaseSpace p n) where
  toFun z :=
    { toFun := symplecticPairing z
      map_add' := by intro x y; simp [symplecticPairing, dotProduct_add, sub_add_sub_comm]
      map_smul' := by intro c x; simp [symplecticPairing, dotProduct_smul, mul_sub] }
  map_add' := by
    intro x y; apply LinearMap.ext; intro z
    change symplecticPairing (x + y) z = symplecticPairing x z + symplecticPairing y z
    simp [symplecticPairing, add_dotProduct, sub_add_sub_comm]
  map_smul' := by
    intro c x; apply LinearMap.ext; intro z
    change symplecticPairing (c • x) z = c * symplecticPairing x z
    simp [symplecticPairing, smul_dotProduct, mul_sub]

@[simp] theorem symplecticBilinForm_apply (z w : PhaseSpace p n) :
    symplecticBilinForm z w = symplecticPairing z w := rfl

theorem symplecticBilinForm_isAlt :
    (symplecticBilinForm (p := p) (n := n)).IsAlt := symplecticPairing_self

theorem symplecticPairing_swap (z w : PhaseSpace p n) :
    symplecticPairing z w = -symplecticPairing w z := by
  simp [symplecticPairing, dotProduct_comm, neg_sub]

theorem symplecticPairing_nondegenerate (z : PhaseSpace p n)
    (hz : ∀ w, symplecticPairing z w = 0) : z = 0 := by
  apply Prod.ext <;> ext i
  · simpa [symplecticPairing] using hz (0, Pi.single i 1)
  · have h := hz (Pi.single i 1, 0)
    simpa [symplecticPairing] using h

theorem symplecticBilinForm_nondegenerate :
    (symplecticBilinForm (p := p) (n := n)).Nondegenerate := by
  intro z hz
  exact symplecticPairing_nondegenerate z hz

/-- Nondegeneracy identifies the phase space with its full linear dual. -/
def symplecticDualEquiv :
    PhaseSpace p n ≃ₗ[ZMod p] Module.Dual (ZMod p) (PhaseSpace p n) :=
  LinearMap.linearEquivOfInjective symplecticBilinForm
    (by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot.mpr
      intro z w h
      apply sub_eq_zero.mp
      apply symplecticPairing_nondegenerate
      intro v
      have h' := congrArg (fun f : Module.Dual (ZMod p) (PhaseSpace p n) => f v) h
      change symplecticBilinForm (z - w) v = 0
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
      exact h')
    (by simp)

namespace Quantum
/-- Every ordered basis of every public Lagrangian is a reference frame. -/
abbrev OrderedLagrangianFrame (p n : ℕ) [Fact p.Prime] :=
  (L : Lagrangian p n) × Basis (Fin n) (ZMod p) L.val

/-- Maximal isotropy is proved from the actual half-dimension condition. -/
theorem lagrangian_orthogonal_eq (L : Lagrangian p n) :
    symplecticBilinForm.orthogonal L.val = L.val := by
  apply (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
  · intro z hz w hw
    exact L.property.1 w hw z hz
  · rw [LinearMap.BilinForm.finrank_orthogonal symplecticBilinForm_nondegenerate
      symplecticBilinForm_isAlt.isRefl, L.property.2]
    simp [PhaseSpace, Configuration, Module.finrank_prod]


/-- The vectors of the supplied ordered basis, in ambient phase space. -/
def frameVector (R : OrderedLagrangianFrame p n) (i : Fin n) : PhaseSpace p n :=
  (R.2 i).val

@[simp] theorem pairing_frameVector (R : OrderedLagrangianFrame p n) (i j : Fin n) :
    symplecticBilinForm (frameVector R i) (frameVector R j) = 0 :=
  R.1.property.1 _ (R.2 i).property _ (R.2 j).property

/-- Extend a coordinate functional, then represent it by the nondegenerate pairing. -/
def frameDualLift (R : OrderedLagrangianFrame p n) (i : Fin n) : PhaseSpace p n :=
  symplecticDualEquiv.symm (Subspace.dualLift R.1.val (R.2.coord i))

@[simp] theorem pairing_frameDualLift_frameVector (R : OrderedLagrangianFrame p n)
    (i j : Fin n) :
    symplecticBilinForm (frameDualLift R i) (frameVector R j) = if i = j then 1 else 0 := by
  change symplecticDualEquiv (symplecticDualEquiv.symm _) (R.2 j).val = _
  rw [LinearEquiv.apply_symm_apply, Subspace.dualLift_of_subtype]
  simp [Basis.coord_apply, Finsupp.single_apply, eq_comm]

@[simp] theorem pairing_frameVector_frameDualLift (R : OrderedLagrangianFrame p n)
    (i j : Fin n) :
    symplecticBilinForm (frameVector R i) (frameDualLift R j) =
      -(if j = i then 1 else 0) := by
  change symplecticPairing _ _ = _
  rw [symplecticPairing_swap]
  exact congrArg Neg.neg (pairing_frameDualLift_frameVector R j i)

/-- Upper-triangular correction coefficients; no division by two occurs. -/
def frameCorrection (R : OrderedLagrangianFrame p n) (i j : Fin n) : ZMod p :=
  if i < j then symplecticBilinForm (frameDualLift R i) (frameDualLift R j) else 0

/-- An isotropic dual family constructed from the original frame. -/
def frameDualVector (R : OrderedLagrangianFrame p n) (i : Fin n) : PhaseSpace p n :=
  frameDualLift R i + ∑ j, frameCorrection R i j • frameVector R j

@[simp] theorem pairing_frameDualVector_frameVector (R : OrderedLagrangianFrame p n)
    (i j : Fin n) :
    symplecticBilinForm (frameDualVector R i) (frameVector R j) = if i = j then 1 else 0 := by
  simp only [frameDualVector, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, pairing_frameVector,
    pairing_frameDualLift_frameVector, smul_zero, Finset.sum_const_zero, add_zero]

@[simp] theorem pairing_frameVector_frameDualVector (R : OrderedLagrangianFrame p n)
    (i j : Fin n) :
    symplecticBilinForm (frameVector R i) (frameDualVector R j) =
      -(if j = i then 1 else 0) := by
  change symplecticPairing _ _ = _
  rw [symplecticPairing_swap]
  exact congrArg Neg.neg (pairing_frameDualVector_frameVector R j i)

@[simp] theorem pairing_frameDualVector (R : OrderedLagrangianFrame p n) (i j : Fin n) :
    symplecticBilinForm (frameDualVector R i) (frameDualVector R j) = 0 := by
  have hcalc : symplecticBilinForm (frameDualVector R i) (frameDualVector R j) =
      symplecticBilinForm (frameDualLift R i) (frameDualLift R j) -
        frameCorrection R i j + frameCorrection R j i := by
    conv_lhs => rhs; rw [frameDualVector]
    simp only [map_add, map_sum, map_smul, pairing_frameDualVector_frameVector, smul_eq_mul]
    rw [frameDualVector]
    simp [-symplecticBilinForm_apply, map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, pairing_frameVector_frameDualLift, smul_eq_mul, sub_eq_add_neg]
  rw [hcalc]
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [frameCorrection, hij, not_lt_of_gt hij]
  · subst j
    simp [frameCorrection, symplecticPairing_self]
  · simp only [frameCorrection, hij, not_lt_of_gt hij, if_false, if_true, sub_zero]
    change symplecticPairing _ _ + symplecticPairing _ _ = 0
    rw [symplecticPairing_swap (frameDualLift R i), neg_add_cancel]


/-- Assemble a symplectic basis from the corrected dual family and the supplied frame. -/
def frameAssembly (R : OrderedLagrangianFrame p n) :
    PhaseSpace p n →ₗ[ZMod p] PhaseSpace p n where
  toFun z := ∑ i, z.1 i • frameDualVector R i + ∑ i, z.2 i • frameVector R i
  map_add' := by
    intro z w
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' := by
    intro c z
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add, Finset.smul_sum]

@[simp] theorem pairing_frameAssembly_frameVector (R : OrderedLagrangianFrame p n)
    (z : PhaseSpace p n) (j : Fin n) :
    symplecticBilinForm (frameAssembly R z) (frameVector R j) = z.1 j := by
  change symplecticBilinForm (∑ i, z.1 i • frameDualVector R i +
    ∑ i, z.2 i • frameVector R i) _ = _
  simp [-symplecticBilinForm_apply, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem pairing_frameAssembly_frameDualVector (R : OrderedLagrangianFrame p n)
    (z : PhaseSpace p n) (j : Fin n) :
    symplecticBilinForm (frameAssembly R z) (frameDualVector R j) = -z.2 j := by
  change symplecticBilinForm (∑ i, z.1 i • frameDualVector R i +
    ∑ i, z.2 i • frameVector R i) _ = _
  simp [-symplecticBilinForm_apply, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-- The assembled linear map preserves the original symplectic pairing. -/
theorem pairing_frameAssembly (R : OrderedLagrangianFrame p n) (z w : PhaseSpace p n) :
    symplecticPairing (frameAssembly R z) (frameAssembly R w) = symplecticPairing z w := by
  change symplecticBilinForm (frameAssembly R z)
    (∑ i, w.1 i • frameDualVector R i + ∑ i, w.2 i • frameVector R i) = _
  simp only [map_add, map_sum, map_smul, pairing_frameAssembly_frameVector,
    pairing_frameAssembly_frameDualVector, smul_eq_mul]
  simp only [symplecticPairing, dotProduct]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem frameAssembly_injective (R : OrderedLagrangianFrame p n) :
    Function.Injective (frameAssembly R) := by
  intro z w h
  apply Prod.ext <;> ext i
  · have he := congrArg (fun v => symplecticBilinForm v (frameVector R i)) h
    simpa only [pairing_frameAssembly_frameVector] using he
  · have he := congrArg (fun v => symplecticBilinForm v (frameDualVector R i)) h
    simpa only [pairing_frameAssembly_frameDualVector, neg_inj] using he

/-- An isomorphism from standard coordinates to the completed supplied frame. -/
def frameAssemblyEquiv (R : OrderedLagrangianFrame p n) :
    PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n :=
  LinearMap.linearEquivOfInjective (frameAssembly R) (frameAssembly_injective R) rfl

/-- Standardize any ordered Lagrangian basis, without a completion hypothesis. -/
def frameStandardization (R : OrderedLagrangianFrame p n) :
    PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n := (frameAssemblyEquiv R).symm

theorem pairing_frameStandardization (R : OrderedLagrangianFrame p n)
    (z w : PhaseSpace p n) :
    symplecticPairing (frameStandardization R z) (frameStandardization R w) =
      symplecticPairing z w := by
  have h := pairing_frameAssembly R (frameStandardization R z) (frameStandardization R w)
  change symplecticPairing (frameAssemblyEquiv R ((frameAssemblyEquiv R).symm z))
    (frameAssemblyEquiv R ((frameAssemblyEquiv R).symm w)) = _ at h
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

@[simp] theorem frameStandardization_basis (R : OrderedLagrangianFrame p n) (i : Fin n) :
    frameStandardization R (frameVector R i) = (0, Pi.single i 1) := by
  apply (frameAssemblyEquiv R).injective
  change (frameAssemblyEquiv R) ((frameAssemblyEquiv R).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change frameVector R i = ∑ j, (0 : Configuration p n) j • frameDualVector R j +
    ∑ j, (Pi.single i (1 : ZMod p) : Configuration p n) j • frameVector R j
  simp [Pi.single_apply]

/-- Existential form of all-prime ordered-frame standardization. -/
theorem exists_frame_standardization (R : OrderedLagrangianFrame p n) :
    ∃ g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n,
      (∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) ∧
      ∀ i, g (R.2 i).val = (0, Pi.single i 1) :=
  ⟨frameStandardization R, pairing_frameStandardization R, frameStandardization_basis R⟩


/-- Pairing coordinates against the supplied reference basis. -/
def referencePairingMap (R : OrderedLagrangianFrame p n) :
    PhaseSpace p n →ₗ[ZMod p] Configuration p n :=
  LinearMap.pi fun i => symplecticBilinForm.flip (frameVector R i)

@[simp] theorem referencePairingMap_apply (R : OrderedLagrangianFrame p n)
    (z : PhaseSpace p n) (i : Fin n) :
    referencePairingMap R z i = symplecticPairing z (frameVector R i) := rfl

/-- The pairing kernel is precisely the reference Lagrangian itself. -/
theorem referencePairingMap_eq_zero_iff (R : OrderedLagrangianFrame p n)
    (z : PhaseSpace p n) : referencePairingMap R z = 0 ↔ z ∈ R.1.val := by
  constructor
  · intro hz
    rw [← lagrangian_orthogonal_eq R.1]
    intro w hw
    have hri (i : Fin n) : symplecticBilinForm (frameVector R i) z = 0 := by
      change symplecticPairing _ _ = 0
      rw [symplecticPairing_swap]
      have hi := congrFun hz i
      change symplecticPairing z (frameVector R i) = 0 at hi
      rw [hi, neg_zero]
    have hwrepr : (∑ i, R.2.repr ⟨w, hw⟩ i • frameVector R i) = w := by
      have h := congrArg (fun v : R.1.val => v.val) (R.2.sum_repr ⟨w, hw⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, frameVector] using h
    change symplecticBilinForm w z = 0
    rw [← hwrepr]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      hri, smul_zero, Finset.sum_const_zero]
  · intro hz
    ext i
    exact R.1.property.1 z hz _ (R.2 i).property

/-- Restriction of the intrinsic pairing coordinates to a transverse Lagrangian. -/
def transverseReferencePairingEquiv (R : OrderedLagrangianFrame p n)
    (L : Lagrangian p n) (hLR : Disjoint L.val R.1.val) :
    L.val ≃ₗ[ZMod p] Configuration p n :=
  LinearMap.linearEquivOfInjective ((referencePairingMap R).comp L.val.subtype)
    (by
      intro z w hzw
      have hr : referencePairingMap R (z.val - w.val) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hzw
      have hm : z.val - w.val ∈ L.val ⊓ R.1.val :=
        ⟨L.val.sub_mem z.property w.property, (referencePairingMap_eq_zero_iff R _).mp hr⟩
      rw [hLR.eq_bot] at hm
      exact Subtype.ext (sub_eq_zero.mp hm))
    (by simpa [Configuration] using L.property.2)

@[simp] theorem transverseReferencePairingEquiv_apply (R : OrderedLagrangianFrame p n)
    (L : Lagrangian p n) (hLR : Disjoint L.val R.1.val) (z : L.val) (i : Fin n) :
    transverseReferencePairingEquiv R L hLR z i = symplecticPairing z.val (frameVector R i) := rfl

/-- The uniquely determined reference-dual stabilizer directions. -/
def referenceDualVector (R : OrderedLagrangianFrame p n) (L : Lagrangian p n)
    (hLR : Disjoint L.val R.1.val) (i : Fin n) : L.val :=
  (transverseReferencePairingEquiv R L hLR).symm (Pi.single i 1)

@[simp] theorem pairing_referenceDualVector (R : OrderedLagrangianFrame p n)
    (L : Lagrangian p n) (hLR : Disjoint L.val R.1.val) (i j : Fin n) :
    symplecticPairing (referenceDualVector R L hLR i).val (frameVector R j) =
      if i = j then 1 else 0 := by
  have h := congrFun ((transverseReferencePairingEquiv R L hLR).apply_symm_apply
    (Pi.single i 1)) j
  simpa [referenceDualVector, Pi.single_apply, eq_comm] using h

/-- The standardized first coordinate is the intrinsic reference-pairing coordinate. -/
theorem frameStandardization_first (R : OrderedLagrangianFrame p n) (z : PhaseSpace p n) :
    (frameStandardization R z).1 = referencePairingMap R z := by
  ext i
  have h := pairing_frameStandardization R z (frameVector R i)
  rw [frameStandardization_basis] at h
  simpa [symplecticPairing] using h


/-- Transport a public Lagrangian along any proved symplectic linear equivalence. -/
def symplecticMapLagrangian (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (L : Lagrangian p n) : Lagrangian p n :=
  ⟨L.val.map g.toLinearMap, by
    constructor
    · rintro z ⟨x, hx, rfl⟩ w ⟨y, hy, rfl⟩
      exact (hg x y).trans (L.property.1 x hx y hy)
    · rw [g.finrank_map_eq]
      exact L.property.2⟩

@[simp] theorem symplecticMapLagrangian_val
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (L : Lagrangian p n) : (symplecticMapLagrangian g hg L).val = L.val.map g.toLinearMap := rfl

/-- The actual restriction of the ambient map to the source Lagrangian. -/
def symplecticLagrangianLinearEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (L : Lagrangian p n) : L.val ≃ₗ[ZMod p] (symplecticMapLagrangian g hg L).val :=
  g.submoduleMap L.val

@[simp] theorem symplecticLagrangianLinearEquiv_apply
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (L : Lagrangian p n) (z : L.val) :
    (symplecticLagrangianLinearEquiv g hg L z).val = g z.val := rfl

theorem symplecticPairing_symm
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) (z w) :
    symplecticPairing (g.symm z) (g.symm w) = symplecticPairing z w := by
  simpa using (hg (g.symm z) (g.symm w)).symm

/-- Symplectic transport is a bijection on the original public Lagrangian type. -/
def symplecticLagrangianEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) :
    Lagrangian p n ≃ Lagrangian p n where
  toFun := symplecticMapLagrangian g hg
  invFun := symplecticMapLagrangian g.symm (symplecticPairing_symm g hg)
  left_inv L := by
    apply Subtype.ext
    change (L.val.map g.toLinearMap).map g.symm.toLinearMap = L.val
    ext x
    simp
  right_inv L := by
    apply Subtype.ext
    change (L.val.map g.symm.toLinearMap).map g.toLinearMap = L.val
    ext x
    simp

/-- The standardized image of an arbitrary Lagrangian. -/
def frameMapLagrangian (R : OrderedLagrangianFrame p n) (L : Lagrangian p n) :
    Lagrangian p n :=
  symplecticMapLagrangian (frameStandardization R) (pairing_frameStandardization R) L

/-- Original transversality is exactly what puts the image in the graph chart. -/
theorem frameMapLagrangian_transverse (R : OrderedLagrangianFrame p n)
    (L : Lagrangian p n) (hLR : Disjoint L.val R.1.val) :
    IsTransverse (frameMapLagrangian R L).val := by
  rintro z ⟨w, hw, rfl⟩ hz
  change (frameStandardization R w).1 = 0 at hz
  rw [frameStandardization_first] at hz
  have hm : w ∈ L.val ⊓ R.1.val :=
    ⟨hw, (referencePairingMap_eq_zero_iff R w).mp hz⟩
  rw [hLR.eq_bot] at hm
  change w = 0 at hm
  simp [hm]

/-- Under standardization, intrinsic dual directions become the unique first-projection lifts. -/
theorem frameStandardization_referenceDualVector (R : OrderedLagrangianFrame p n)
    (L : Lagrangian p n) (hLR : Disjoint L.val R.1.val) (i : Fin n) :
    frameStandardization R (referenceDualVector R L hLR i).val =
      ((transverseProjectionEquiv (frameMapLagrangian R L)
        (frameMapLagrangian_transverse R L hLR)).symm (Pi.single i 1)).val := by
  let v : (frameMapLagrangian R L).val :=
    symplecticLagrangianLinearEquiv (frameStandardization R) (pairing_frameStandardization R)
      L (referenceDualVector R L hLR i)
  have hfst : v.val.1 = Pi.single i 1 := by
    change (frameStandardization R (referenceDualVector R L hLR i).val).1 = _
    rw [frameStandardization_first]
    exact (transverseReferencePairingEquiv R L hLR).apply_symm_apply _
  have he : v = (transverseProjectionEquiv (frameMapLagrangian R L)
      (frameMapLagrangian_transverse R L hLR)).symm (Pi.single i 1) := by
    apply (transverseProjectionEquiv _ _).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hfst
  exact congrArg Subtype.val he


/-- The graph-chart condition is equivalent to the original intrinsic transversality. -/
theorem frameMapLagrangian_transverse_iff (R : OrderedLagrangianFrame p n)
    (L : Lagrangian p n) :
    IsTransverse (frameMapLagrangian R L).val ↔ Disjoint L.val R.1.val := by
  constructor
  · intro h
    apply disjoint_iff_inf_le.mpr
    intro z hz
    have hfst : (frameStandardization R z).1 = 0 := by
      rw [frameStandardization_first]
      exact (referencePairingMap_eq_zero_iff R z).mpr hz.2
    have he := h (frameStandardization R z) ⟨z, hz.1, rfl⟩ hfst
    have hz0 : z = 0 := (frameStandardization R).injective (by simpa using he)
    exact hz0
  · exact frameMapLagrangian_transverse R L

/-- Standardization bijects all intrinsically transverse original Lagrangians with the graph chart. -/
def referenceTransverseLagrangianEquiv (R : OrderedLagrangianFrame p n) :
    {L : Lagrangian p n // Disjoint L.val R.1.val} ≃ TransverseLagrangian p n where
  toFun L := ⟨frameMapLagrangian R L.val, frameMapLagrangian_transverse R L.val L.property⟩
  invFun L := ⟨(symplecticLagrangianEquiv (frameStandardization R)
    (pairing_frameStandardization R)).symm L.val, by
      apply (frameMapLagrangian_transverse_iff R _).mp
      change IsTransverse ((symplecticLagrangianEquiv (frameStandardization R)
        (pairing_frameStandardization R))
        ((symplecticLagrangianEquiv (frameStandardization R)
          (pairing_frameStandardization R)).symm L.val)).val
      rw [Equiv.apply_symm_apply]
      exact L.property⟩
  left_inv L := by
    apply Subtype.ext
    exact (symplecticLagrangianEquiv (frameStandardization R)
      (pairing_frameStandardization R)).symm_apply_apply L.val
  right_inv L := by
    apply Subtype.ext
    exact (symplecticLagrangianEquiv (frameStandardization R)
      (pairing_frameStandardization R)).apply_symm_apply L.val

/-- A prescribed reference-pairing coordinate has exactly one lift inside the input Lagrangian. -/
theorem referenceDualVector_unique (R : OrderedLagrangianFrame p n) (L : Lagrangian p n)
    (hLR : Disjoint L.val R.1.val) (i : Fin n) (z : L.val)
    (hz : ∀ j, symplecticPairing z.val (frameVector R j) = if i = j then 1 else 0) :
    z = referenceDualVector R L hLR i := by
  apply (transverseReferencePairingEquiv R L hLR).injective
  ext j
  exact (hz j).trans (pairing_referenceDualVector R L hLR i j).symm


/-- The full reference-dual basis of the actual transverse input Lagrangian. -/
def referenceDualBasis (R : OrderedLagrangianFrame p n) (L : Lagrangian p n)
    (hLR : Disjoint L.val R.1.val) : Basis (Fin n) (ZMod p) L.val :=
  Basis.ofEquivFun (transverseReferencePairingEquiv R L hLR)

@[simp] theorem referenceDualBasis_apply (R : OrderedLagrangianFrame p n)
    (L : Lagrangian p n) (hLR : Disjoint L.val R.1.val) (i : Fin n) :
    referenceDualBasis R L hLR i = referenceDualVector R L hLR i := by
  change (Basis.ofEquivFun (transverseReferencePairingEquiv R L hLR) : Fin n → L.val) i = _
  rw [Basis.coe_ofEquivFun]
  rfl

@[simp] theorem pairing_referenceDualBasis (R : OrderedLagrangianFrame p n)
    (L : Lagrangian p n) (hLR : Disjoint L.val R.1.val) (i j : Fin n) :
    symplecticPairing (referenceDualBasis R L hLR i).val (frameVector R j) =
      if i = j then 1 else 0 := by
  rw [referenceDualBasis_apply]
  exact pairing_referenceDualVector R L hLR i j

end Quantum
end StabilizerLearning
