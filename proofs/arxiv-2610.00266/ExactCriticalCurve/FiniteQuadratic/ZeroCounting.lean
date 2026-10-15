import ExactCriticalCurve.FiniteQuadratic.MetabolicCore
import Mathlib.LinearAlgebra.Projection
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card

noncomputable section
namespace ExactCriticalCurve.FiniteQuadratic
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem binaryLinear_surjective_of_ne_zero (f : V →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) :
    Function.Surjective f := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    apply hf
    ext x
    exact h x
  intro b
  refine ⟨(b / f x) • x, ?_⟩
  simp [map_smul, smul_eq_mul, div_mul_cancel₀ b hx]

/-- Translation gives a genuine equivalence between a nonempty linear fiber and its kernel. -/
def linearFiberEquivKer (f : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2)
    (x₀ : V) (hx₀ : f x₀ = b) : {x : V // f x = b} ≃ LinearMap.ker f where
  toFun x := ⟨x.val - x₀, by simp [LinearMap.mem_ker, map_sub, x.property, hx₀]⟩
  invFun z := ⟨z.val + x₀, by simp [map_add, LinearMap.mem_ker.mp z.property, hx₀]⟩
  left_inv x := by ext; simp
  right_inv z := by ext; simp

theorem card_binaryLinear_fiber [FiniteDimensional (ZMod 2) V]
    (f : V →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (b : ZMod 2) :
    Nat.card {x : V // f x = b} = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
  obtain ⟨x₀, hx₀⟩ := binaryLinear_surjective_of_ne_zero f hf b
  rw [Nat.card_congr (linearFiberEquivKer f b x₀ hx₀)]
  have hd := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (binaryLinear_surjective_of_ne_zero f hf),
    finrank_top, Module.finrank_self] at hd
  have hk : Module.finrank (ZMod 2) (LinearMap.ker f) = Module.finrank (ZMod 2) V - 1 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hk]
  norm_num

/-- Singularity on a coset of a singular subspace is the fiber of an actual linear functional. -/
def polarFunctional (Q : QuadraticForm (ZMod 2) V)
    (L : Submodule (ZMod 2) V) (y : V) : L →ₗ[ZMod 2] ZMod 2 :=
  (Q.polarBilin y).comp L.subtype

theorem quadratic_add_singular_left {Q : QuadraticForm (ZMod 2) V}
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L) (x : L) (y : V) :
    Q (x.val + y) = Q y + polarFunctional Q L y x := by
  rw [quadratic_add, hL x.val x.property, zero_add]
  rw [(polar_isSymm Q).eq]
  rfl

theorem polarFunctional_ne_zero [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2*r)
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) {y : V} (hy : y ∉ L) :
    polarFunctional Q L y ≠ 0 := by
  intro hz
  apply hy
  have hyorth : y ∈ (LinearMap.BilinForm.orthogonal Q.polarBilin L) := by
    intro x hx
    change Q.polarBilin x y = 0
    rw [(polar_isSymm Q).eq]
    exact congrArg (fun f : L →ₗ[ZMod 2] ZMod 2 => f ⟨x, hx⟩) hz
  rw [show (LinearMap.BilinForm.orthogonal Q.polarBilin L) = L from orthogonal_eq_of_half_dim hQ hV hL hdL] at hyorth
  exact hyorth


/-- A complete decomposition by the actual complementary coordinate. -/
def singularVectorsEquivFibers (Q : QuadraticForm (ZMod 2) V)
    (L H : Submodule (ZMod 2) V) (hLH : IsCompl L H) :
    {v : V // Q v = 0} ≃
      Σ y : H, {x : L // Q (x.val + y.val) = 0} where
  toFun v := by
    let p := (Submodule.prodEquivOfIsCompl L H hLH).symm v.val
    refine ⟨p.2, p.1, ?_⟩
    change Q ((Submodule.prodEquivOfIsCompl L H hLH) p) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact v.property
  invFun p := ⟨p.2.val.val + p.1.val, p.2.property⟩
  left_inv v := by
    apply Subtype.ext
    exact (Submodule.prodEquivOfIsCompl L H hLH).apply_symm_apply v.val
  right_inv p := by
    rcases p with ⟨y, x, hx⟩
    dsimp
    have he := (Submodule.prodEquivOfIsCompl L H hLH).symm_apply_apply (x, y)
    change (Submodule.prodEquivOfIsCompl L H hLH).symm (x.val + y.val) = (x, y) at he
    have hy : ((Submodule.prodEquivOfIsCompl L H hLH).symm (x.val+y.val)).2 = y :=
      congrArg Prod.snd he
    apply Sigma.ext hy
    apply (Subtype.heq_iff_coe_eq (fun z => by
      change Q (z.val + ((Submodule.prodEquivOfIsCompl L H hLH).symm (x.val+y.val)).2.val)=0 ↔
        Q (z.val+y.val)=0
      rw [hy])).mpr
    exact congrArg Prod.fst he

theorem card_singular_coset [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2*r)
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) (y : V) (hy : y ∉ L) :
    Nat.card {x : L // Q (x.val + y) = 0} = 2 ^ (r-1) := by
  have he : ∀ x : L, Q (x.val+y)=0 ↔ polarFunctional Q L y x = -Q y := by
    intro x
    rw [quadratic_add_singular_left hL]
    exact add_eq_zero_iff_eq_neg'
  rw [Nat.card_congr (Equiv.subtypeEquivRight he),
    card_binaryLinear_fiber _ (polarFunctional_ne_zero hQ hV hL hdL hy), hdL]

theorem card_zeroVectors [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2*r)
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) :
    Nat.card {v : V // Q v = 0} = 2^r + (2^r-1) * 2^(r-1) := by
  classical
  letI : Finite V := Finite.of_equiv (Fin (Module.finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨H, hLH⟩ := L.exists_isCompl
  letI : Fintype L := Fintype.ofFinite L
  letI : Fintype H := Fintype.ofFinite H
  have hdH : Module.finrank (ZMod 2) H = r := by
    have hd := Submodule.finrank_add_eq_of_isCompl hLH
    omega
  have hcL : Fintype.card L = 2^r := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), hdL]
    norm_num
  have hcH : Fintype.card H = 2^r := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), hdH]
    norm_num
  have hzero : Fintype.card {x : L // Q (x.val + (0 : H).val)=0} = 2^r := by
    have he : ∀ x : L, Q (x.val + (0 : H).val)=0 ↔ True := by
      intro x
      simp [hL x.val x.property]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
    simpa using hcL
  have hnonzero : ∀ y : H, y ≠ 0 →
      Fintype.card {x : L // Q (x.val+y.val)=0} = 2^(r-1) := by
    intro y hy
    have hyL : y.val ∉ L := by
      intro hym
      apply hy
      apply Subtype.ext
      exact Submodule.disjoint_def.mp hLH.disjoint y.val hym y.property
    rw [← Nat.card_eq_fintype_card]
    exact card_singular_coset hQ hV hL hdL y.val hyL
  rw [Nat.card_congr (singularVectorsEquivFibers Q L H hLH),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  have he : (∑ y : H, Fintype.card {x : L // Q (x.val+y.val)=0}) =
      2^r + (Fintype.card H-1)*2^(r-1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : H))]
    rw [hzero]
    have hs : ∑ y ∈ (Finset.univ.erase (0 : H)),
        Fintype.card {x : L // Q (x.val+y.val)=0} =
        (Fintype.card H-1)*2^(r-1) := by
      rw [Finset.sum_congr rfl (fun y hy => hnonzero y (Finset.mem_erase.mp hy).1)]
      simp
    rw [hs]
    omega
  rw [he, hcH]


/-- The actual nonzero singular vectors, including the rank-zero endpoint. -/
theorem card_nonzeroSingularVectors [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2*r)
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) :
    Nat.card {v : V // Q v = 0 ∧ v ≠ 0} = (2^r-1) * (2^(r-1)+1) := by
  classical
  letI : Finite V := Finite.of_equiv (Fin (Module.finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  letI : Fintype V := Fintype.ofFinite V
  let z : {v : V // Q v = 0} := ⟨0, Q.map_zero⟩
  let e : {v : V // Q v = 0 ∧ v ≠ 0} ≃ {v : {v : V // Q v = 0} // v ≠ z} :=
    { toFun := fun v => ⟨⟨v.val, v.property.1⟩, fun he => v.property.2 (congrArg Subtype.val he)⟩
      invFun := fun v => ⟨v.val.val, v.val.property,
        fun he => v.property (Subtype.ext he)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : Nat.card {v : V // Q v=0 ∧ v≠0} = Nat.card {v : V // Q v=0} - 1 := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun v : {v : V // Q v=0} => v=z)]
    simp [Nat.card_eq_fintype_card]
  rw [hc, card_zeroVectors hQ hV hL hdL, Nat.mul_add, Nat.mul_one]
  have hp : 0 < 2^r := pow_pos (by omega) _
  omega

end ExactCriticalCurve.FiniteQuadratic
