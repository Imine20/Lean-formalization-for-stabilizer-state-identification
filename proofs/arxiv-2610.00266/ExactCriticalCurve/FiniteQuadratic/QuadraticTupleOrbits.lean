import ExactCriticalCurve.FiniteQuadratic.BinaryWittExtension
import ExactCriticalCurve.Counting.FunctionOrbits
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Setoid.Basic

/-! # Actual binary quadratic tuple orbits

Two linear tuples are in the same actual orthogonal orbit precisely when
their kernels and their full pulled-back quadratic forms coincide.
No fixed-space distribution, group-order formula or embedding count is assumed.
-/
noncomputable section
open Classical Module
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual group of binary linear automorphisms preserving Q. -/
def binaryQuadraticIsometrySubgroup (Q : QuadraticForm (ZMod 2) V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {u | ∀ x, Q (u x) = Q x}
  one_mem' _ := rfl
  mul_mem' hu hv x := (hu _).trans (hv x)
  inv_mem' := by
    intro u hu x
    simpa using (hu (u.symm x)).symm

abbrev BinaryQuadraticIsometryGroup (Q : QuadraticForm (ZMod 2) V) :=
  binaryQuadraticIsometrySubgroup Q

instance finiteBinaryQuadraticIsometryGroup [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) : Finite (BinaryQuadraticIsometryGroup Q) := by
  letI : Finite V := Finite.of_equiv (Fin (finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  exact Finite.of_injective
    (fun u : BinaryQuadraticIsometryGroup Q => (u.val : V → V))
    (by intro u v h; apply Subtype.ext; exact LinearEquiv.ext (congrFun h))

instance fintypeBinaryQuadraticIsometryGroup [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) : Fintype (BinaryQuadraticIsometryGroup Q) :=
  Fintype.ofFinite _

section LinearTuples
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- Equal kernels identify the actual ranges by sending f(x) to g(x). -/
def quadraticTupleRangeEquiv (f g : E →ₗ[ZMod 2] V) (h : (LinearMap.ker f) = (LinearMap.ker g)) :
    (LinearMap.range f) ≃ₗ[ZMod 2] (LinearMap.range g) :=
  f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ h).trans g.quotKerEquivRange)

@[simp] theorem quadraticTupleRangeEquiv_apply
    (f g : E →ₗ[ZMod 2] V) (h : (LinearMap.ker f) = (LinearMap.ker g)) (x : E) :
    (quadraticTupleRangeEquiv f g h ⟨f x, ⟨x,rfl⟩⟩).val = g x := by
  simp [quadraticTupleRangeEquiv]

/-- Full pullback Q, together with the kernel, classifies the actual linear tuple orbit. -/
theorem exists_quadraticIsometry_comp_iff [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (f g : E →ₗ[ZMod 2] V) :
    (∃ u : BinaryQuadraticIsometryGroup Q, u.val.toLinearMap.comp f = g) ↔
      (LinearMap.ker f) = (LinearMap.ker g) ∧ Q.comp f = Q.comp g := by
  constructor
  · rintro ⟨u, rfl⟩
    constructor
    · ext x
      change f x = 0 ↔ u.val (f x) = 0
      exact u.val.map_eq_zero_iff.symm
    · ext x
      exact (u.property (f x)).symm
  · rintro ⟨hk,hq⟩
    let e := quadraticTupleRangeEquiv f g hk
    have heq (x : (LinearMap.range f)) : Q (e x).val = Q x.val := by
      rcases x with ⟨_, x, rfl⟩
      simpa only [e, quadraticTupleRangeEquiv_apply] using
        (congrArg (fun q : QuadraticForm (ZMod 2) E => q x) hq).symm
    obtain ⟨u,hu,he⟩ := binary_witt_extension Q hQ (LinearMap.range f) (LinearMap.range g) e heq
    refine ⟨⟨u,hu⟩,?_⟩
    ext x
    exact (he ⟨f x,⟨x,rfl⟩⟩).trans (quadraticTupleRangeEquiv_apply f g hk x)

end LinearTuples

/-- Coordinate tuples are exactly linear maps from the binary coordinate space. -/
def quadraticTupleLinearEquiv (n : ℕ) :
    (Fin n → V) ≃ₗ[ZMod 2] ((Fin n → ZMod 2) →ₗ[ZMod 2] V) :=
  (Pi.basisFun (ZMod 2) (Fin n)).constr (ZMod 2)

/-- Actual invariant data; its range contains only data realized in the given ambient Q. -/
def quadraticTupleInvariant (Q : QuadraticForm (ZMod 2) V) (n : ℕ) (x : Fin n → V) :
    Submodule (ZMod 2) (Fin n → ZMod 2) × QuadraticForm (ZMod 2) (Fin n → ZMod 2) :=
  let f := quadraticTupleLinearEquiv n x
  ((LinearMap.ker f), Q.comp f)

theorem quadraticTupleLinearEquiv_smul (Q : QuadraticForm (ZMod 2) V)
    (n : ℕ) (u : BinaryQuadraticIsometryGroup Q) (x : Fin n → V) :
    quadraticTupleLinearEquiv n (u • x) =
      u.val.toLinearMap.comp (quadraticTupleLinearEquiv n x) := by
  apply (Pi.basisFun (ZMod 2) (Fin n)).ext
  intro i
  simp only [quadraticTupleLinearEquiv, Basis.constr_basis, LinearMap.comp_apply]
  rfl

/-- Equality of the actual realized data is precisely orbit equivalence on coordinate tuples. -/
theorem quadraticTuple_orbit_iff [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (n : ℕ) (x y : Fin n → V) :
    y ∈ MulAction.orbit (BinaryQuadraticIsometryGroup Q) x ↔
      quadraticTupleInvariant Q n x = quadraticTupleInvariant Q n y := by
  rw [MulAction.mem_orbit_iff]
  change (∃ u : BinaryQuadraticIsometryGroup Q, u • x = y) ↔
    ((LinearMap.ker (quadraticTupleLinearEquiv n x)), Q.comp (quadraticTupleLinearEquiv n x)) =
      ((LinearMap.ker (quadraticTupleLinearEquiv n y)), Q.comp (quadraticTupleLinearEquiv n y))
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨u,rfl⟩
    exact (exists_quadraticIsometry_comp_iff Q hQ _ _).mp
      ⟨u,(quadraticTupleLinearEquiv_smul Q n u x).symm⟩
  · intro h
    obtain ⟨u,hu⟩ := (exists_quadraticIsometry_comp_iff Q hQ _ _).mpr h
    refine ⟨u,?_⟩
    apply (quadraticTupleLinearEquiv n).injective
    rw [quadraticTupleLinearEquiv_smul]
    exact hu

/-- The actual orbit quotient bijects with the range of actual kernel/pullback data. -/
def quadraticTupleOrbitEquivRealized [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (n : ℕ) :
    MulAction.orbitRel.Quotient (BinaryQuadraticIsometryGroup Q) (Fin n → V) ≃
      Set.range (quadraticTupleInvariant Q n) :=
  (Quotient.congrRight (fun x y =>
    (quadraticTuple_orbit_iff Q hQ n y x).trans eq_comm)).trans
      (Setoid.quotientKerEquivRange (quadraticTupleInvariant Q n))

/-- Burnside's fixed-space average equals the cardinality of actually realized data. -/
theorem quadraticTuple_fixedSpaceAverage_eq_realized [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (n : ℕ) :
    (∑ u : BinaryQuadraticIsometryGroup Q, ((2 : ℚ) ^ n) ^
      finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) =
      (Nat.card (Set.range (quadraticTupleInvariant Q n)) : ℚ) := by
  letI : Finite V := Finite.of_equiv (Fin (finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  letI : Fintype V := Fintype.ofFinite V
  have h := Counting.binary_fixedSpaceAverage_eq_orbits
    (G := BinaryQuadraticIsometryGroup Q) (V := V) n
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (quadraticTupleOrbitEquivRealized Q hQ n)] at h
  exact h

end ExactCriticalCurve.FiniteQuadratic
