import ExactCriticalCurve.FiniteQuadratic.BinaryAlternatingWitt
import Mathlib.LinearAlgebra.BilinearForm.Hom
import ExactCriticalCurve.Counting.FunctionOrbits
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Setoid.Basic

/-! # Actual binary symplectic tuple orbits

Two linear tuples are in the same actual symplectic orbit precisely when
their kernels and their full pulled-back bilinear forms coincide.
No fixed-space distribution, group-order formula or embedding count is assumed.
-/
noncomputable section
open Classical Module
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual group of binary linear automorphisms preserving B. -/
def binarySymplecticIsometrySubgroup (B : LinearMap.BilinForm (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {u | ∀ x y, B (u x) (u y) = B x y}
  one_mem' _ _ := rfl
  mul_mem' hu hv x y := (hu _ _).trans (hv x y)
  inv_mem' := by
    intro u hu x y
    simpa using (hu (u.symm x) (u.symm y)).symm

abbrev BinarySymplecticIsometryGroup (B : LinearMap.BilinForm (ZMod 2) V) :=
  binarySymplecticIsometrySubgroup B

instance finiteBinarySymplecticIsometryGroup [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) : Finite (BinarySymplecticIsometryGroup B) := by
  letI : Finite V := Finite.of_equiv (Fin (finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  exact Finite.of_injective
    (fun u : BinarySymplecticIsometryGroup B => (u.val : V → V))
    (by intro u v h; apply Subtype.ext; exact LinearEquiv.ext (congrFun h))

instance fintypeBinarySymplecticIsometryGroup [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) : Fintype (BinarySymplecticIsometryGroup B) :=
  Fintype.ofFinite _

section LinearTuples
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- Equal kernels identify the actual ranges by sending f(x) to g(x). -/
def symplecticTupleRangeEquiv (f g : E →ₗ[ZMod 2] V) (h : (LinearMap.ker f) = (LinearMap.ker g)) :
    (LinearMap.range f) ≃ₗ[ZMod 2] (LinearMap.range g) :=
  f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ h).trans g.quotKerEquivRange)

@[simp] theorem symplecticTupleRangeEquiv_apply
    (f g : E →ₗ[ZMod 2] V) (h : (LinearMap.ker f) = (LinearMap.ker g)) (x : E) :
    (symplecticTupleRangeEquiv f g h ⟨f x, ⟨x,rfl⟩⟩).val = g x := by
  simp [symplecticTupleRangeEquiv]

/-- Full pullback B, together with the kernel, classifies the actual linear tuple orbit. -/
theorem exists_symplecticIsometry_comp_iff [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (f g : E →ₗ[ZMod 2] V) :
    (∃ u : BinarySymplecticIsometryGroup B, u.val.toLinearMap.comp f = g) ↔
      (LinearMap.ker f) = (LinearMap.ker g) ∧ B.comp f f = B.comp g g := by
  constructor
  · rintro ⟨u, rfl⟩
    constructor
    · ext x
      change f x = 0 ↔ u.val (f x) = 0
      exact u.val.map_eq_zero_iff.symm
    · ext x y
      exact (u.property (f x) (f y)).symm
  · rintro ⟨hk,hq⟩
    let e := symplecticTupleRangeEquiv f g hk
    have heq (x y : (LinearMap.range f)) : B (e x).val (e y).val = B x.val y.val := by
      rcases x with ⟨_, x, rfl⟩
      rcases y with ⟨_, y, rfl⟩
      simpa only [e, symplecticTupleRangeEquiv_apply, LinearMap.BilinForm.comp_apply] using
        (congrArg (fun b : LinearMap.BilinForm (ZMod 2) E => b x y) hq).symm
    obtain ⟨u,hu,he⟩ := binary_alternating_witt_extension B hB hnd
      (LinearMap.range f) (LinearMap.range g) e heq
    refine ⟨⟨u,hu⟩,?_⟩
    ext x
    exact (he ⟨f x,⟨x,rfl⟩⟩).trans (symplecticTupleRangeEquiv_apply f g hk x)

end LinearTuples

/-- Coordinate tuples are exactly linear maps from the binary coordinate space. -/
def symplecticTupleLinearEquiv (n : ℕ) :
    (Fin n → V) ≃ₗ[ZMod 2] ((Fin n → ZMod 2) →ₗ[ZMod 2] V) :=
  (Pi.basisFun (ZMod 2) (Fin n)).constr (ZMod 2)

/-- Actual invariant data; its range contains only data realized in the given ambient B. -/
def symplecticTupleInvariant (B : LinearMap.BilinForm (ZMod 2) V) (n : ℕ) (x : Fin n → V) :
    Submodule (ZMod 2) (Fin n → ZMod 2) × LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
  let f := symplecticTupleLinearEquiv n x
  ((LinearMap.ker f), B.comp f f)

theorem symplecticTupleLinearEquiv_smul (B : LinearMap.BilinForm (ZMod 2) V)
    (n : ℕ) (u : BinarySymplecticIsometryGroup B) (x : Fin n → V) :
    symplecticTupleLinearEquiv n (u • x) =
      u.val.toLinearMap.comp (symplecticTupleLinearEquiv n x) := by
  apply (Pi.basisFun (ZMod 2) (Fin n)).ext
  intro i
  simp only [symplecticTupleLinearEquiv, Basis.constr_basis, LinearMap.comp_apply]
  rfl

/-- Equality of the actual realized data is precisely orbit equivalence on coordinate tuples. -/
theorem symplecticTuple_orbit_iff [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (n : ℕ) (x y : Fin n → V) :
    y ∈ MulAction.orbit (BinarySymplecticIsometryGroup B) x ↔
      symplecticTupleInvariant B n x = symplecticTupleInvariant B n y := by
  rw [MulAction.mem_orbit_iff]
  change (∃ u : BinarySymplecticIsometryGroup B, u • x = y) ↔
    ((LinearMap.ker (symplecticTupleLinearEquiv n x)), B.comp (symplecticTupleLinearEquiv n x) (symplecticTupleLinearEquiv n x)) =
      ((LinearMap.ker (symplecticTupleLinearEquiv n y)), B.comp (symplecticTupleLinearEquiv n y) (symplecticTupleLinearEquiv n y))
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨u,rfl⟩
    exact (exists_symplecticIsometry_comp_iff B hB hnd _ _).mp
      ⟨u,(symplecticTupleLinearEquiv_smul B n u x).symm⟩
  · intro h
    obtain ⟨u,hu⟩ := (exists_symplecticIsometry_comp_iff B hB hnd _ _).mpr h
    refine ⟨u,?_⟩
    apply (symplecticTupleLinearEquiv n).injective
    rw [symplecticTupleLinearEquiv_smul]
    exact hu

/-- The actual orbit quotient bijects with the range of actual kernel/pullback data. -/
def symplecticTupleOrbitEquivRealized [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate) (n : ℕ) :
    MulAction.orbitRel.Quotient (BinarySymplecticIsometryGroup B) (Fin n → V) ≃
      Set.range (symplecticTupleInvariant B n) :=
  (Quotient.congrRight (fun x y =>
    (symplecticTuple_orbit_iff B hB hnd n y x).trans eq_comm)).trans
      (Setoid.quotientKerEquivRange (symplecticTupleInvariant B n))

/-- Burnside's fixed-space average equals the cardinality of actually realized data. -/
theorem symplecticTuple_fixedSpaceAverage_eq_realized [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate) (n : ℕ) :
    (∑ u : BinarySymplecticIsometryGroup B, ((2 : ℚ) ^ n) ^
      finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinarySymplecticIsometryGroup B) : ℚ) =
      (Nat.card (Set.range (symplecticTupleInvariant B n)) : ℚ) := by
  letI : Finite V := Finite.of_equiv (Fin (finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  letI : Fintype V := Fintype.ofFinite V
  have h := Counting.binary_fixedSpaceAverage_eq_orbits
    (G := BinarySymplecticIsometryGroup B) (V := V) n
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (symplecticTupleOrbitEquivRealized B hB hnd n)] at h
  exact h

end ExactCriticalCurve.FiniteQuadratic
