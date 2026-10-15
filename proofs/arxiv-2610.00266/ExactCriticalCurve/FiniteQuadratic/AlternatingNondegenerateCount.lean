import ExactCriticalCurve.FiniteQuadratic.AlternatingFirstFiber
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The actual cardinal recurrence for nondegenerate binary alternating forms. -/
noncomputable section
open scoped BigOperators
open Module
namespace ExactCriticalCurve.FiniteQuadratic

instance finiteBinaryDual {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U] :
    Finite (Module.Dual (ZMod 2) U) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

instance finiteBinaryBilin {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [Finite U] :
    Finite (LinearMap.BilinForm (ZMod 2) U) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- Actual forms on the full coordinate vector space, including dimension zero. -/
def nondegenerateAlternatingCount (d : ℕ) : ℕ :=
  Nat.card (NondegenerateAlternatingForm (Fin d → ZMod 2))

theorem nondegenerateAlternating_card_of_finrank
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    {d : ℕ} (hd : finrank (ZMod 2) U = d) :
    Nat.card (NondegenerateAlternatingForm U) = nondegenerateAlternatingCount d := by
  let b := (Module.finBasis (ZMod 2) U).reindex (finCongr hd)
  exact Nat.card_congr (nondegenerateAlternatingCongr b.equivFun)

theorem nonzeroBinaryDual_card {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] :
    Nat.card {l : Module.Dual (ZMod 2) U // l ≠ 0} = 2 ^ finrank (ZMod 2) U - 1 := by
  classical
  letI : Finite U := Finite.of_equiv (Fin (finrank (ZMod 2) U) → ZMod 2)
    (Module.finBasis (ZMod 2) U).equivFun.toEquiv.symm
  letI : Fintype (Module.Dual (ZMod 2) U) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun l : Module.Dual (ZMod 2) U => l = 0)]
  simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq]
  norm_num

theorem nondegenerateAlternatingCount_add_two (d : ℕ) :
    nondegenerateAlternatingCount (d+2) =
      (2^(d+1)-1) * 2^d * nondegenerateAlternatingCount d := by
  let U := Fin (d+1) → ZMod 2
  let e : (Fin (d+2) → ZMod 2) ≃ₗ[ZMod 2] (ZMod 2 × U) :=
    (Counting.binaryCoordinatesSucc (d+1)).trans
      (LinearEquiv.prodComm (ZMod 2) U (ZMod 2))
  have hd : finrank (ZMod 2) U = d+1 := by simp [U]
  have hk : ∀ l : {l : Module.Dual (ZMod 2) U // l ≠ 0},
      finrank (ZMod 2) (LinearMap.ker l.val) = d := by
    intro l
    have hh := l.val.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (binaryLinear_surjective_of_ne_zero l.val l.property),
      finrank_top, Module.finrank_self, hd] at hh
    omega
  have hf : ∀ l : {l : Module.Dual (ZMod 2) U // l ≠ 0},
      Nat.card (Module.Dual (ZMod 2) (LinearMap.ker l.val) ×
        NondegenerateAlternatingForm (LinearMap.ker l.val)) =
          2^d * nondegenerateAlternatingCount d := by
    intro l
    rw [Nat.card_prod, nondegenerateAlternating_card_of_finrank (hk l),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq, hk]
    norm_num
  letI : Fintype {l : Module.Dual (ZMod 2) U // l ≠ 0} := Fintype.ofFinite _
  unfold nondegenerateAlternatingCount at ⊢
  rw [Nat.card_congr (nondegenerateAlternatingCongr e),
    Nat.card_congr nondegenerateAlternatingFirstEquiv, Nat.card_sigma]
  simp_rw [hf]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, nonzeroBinaryDual_card, hd]
  exact (Nat.mul_assoc _ _ _).symm

theorem nondegenerateAlternatingCount_zero : nondegenerateAlternatingCount 0 = 1 := by
  let A : NondegenerateAlternatingForm (Fin 0 → ZMod 2) :=
    ⟨0, fun x => rfl, fun x _ => Subsingleton.elim _ _⟩
  letI : Unique (NondegenerateAlternatingForm (Fin 0 → ZMod 2)) :=
    ⟨⟨A⟩, fun B => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_unique

theorem nondegenerateAlternatingCount_odd (d : ℕ) :
    nondegenerateAlternatingCount (2*d+1) = 0 := by
  have he : IsEmpty (NondegenerateAlternatingForm (Fin (2*d+1) → ZMod 2)) := by
    constructor
    intro A
    have h := alternating_nondegenerate_even_finrank A.val A.property.1 A.property.2
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    obtain ⟨k,hk⟩ := h
    omega
  letI := he
  simp [nondegenerateAlternatingCount]

/-- The recurrence evaluates the cardinal of actual forms as a finite product. -/
theorem nondegenerateAlternatingCount_even_product (a : ℕ) :
    nondegenerateAlternatingCount (2*a) =
      ∏ j ∈ Finset.range a, ((2^(2*j+1)-1) * 2^(2*j)) := by
  induction a with
  | zero => simpa using nondegenerateAlternatingCount_zero
  | succ a ih =>
    rw [show 2*(a+1)=2*a+2 by omega, nondegenerateAlternatingCount_add_two,
      ih, Finset.prod_range_succ]
    ring

end ExactCriticalCurve.FiniteQuadratic
