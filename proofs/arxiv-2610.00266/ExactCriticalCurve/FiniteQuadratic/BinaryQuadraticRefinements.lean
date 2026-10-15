import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticAdjustment
import ExactCriticalCurve.Foundations.BinaryAlternatingCard

/-! The genuine fiber of binary quadratic forms with a fixed actual polar.
Strict upper coordinates construct a member; every other member differs by an actual linear form. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The full actual refinement fiber, not a family indexed by a prescribed count. -/
abbrev BinaryQuadraticRefinements (B : LinearMap.BilinForm (ZMod 2) V) :=
  {q : QuadraticForm (ZMod 2) V // q.polarBilin = B}

/-- A quadratic form obtained from the strict upper half of alternating coordinates. -/
def basisQuadraticRefinement {n : ℕ} (b : Basis (Fin n) (ZMod 2) V)
    (f : StrictPair n → ZMod 2) : QuadraticForm (ZMod 2) V :=
  (∑ p : StrictPair n, f p •
    LinearMap.BilinForm.linMulLin (b.coord p.val.1) (b.coord p.val.2)).toQuadraticMap

theorem basisQuadraticRefinement_polar {n : ℕ} (b : Basis (Fin n) (ZMod 2) V)
    (f : StrictPair n → ZMod 2) :
    (basisQuadraticRefinement b f).polarBilin = basisAlternatingForm b f := by
  rw [basisQuadraticRefinement,LinearMap.BilinMap.polarBilin_toQuadraticMap]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [basisAlternatingForm,LinearMap.sum_apply,LinearMap.add_apply,
    LinearMap.smul_apply,LinearMap.flip_apply,LinearMap.BilinForm.linMulLin_apply,
    smul_eq_mul,Finset.sum_add_distrib,mul_add]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- A genuine quadratic refinement for every finite-dimensional alternating form. -/
def binaryAlternatingQuadratic [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) : QuadraticForm (ZMod 2) V :=
  basisQuadraticRefinement (Module.finBasis (ZMod 2) V)
    (binaryAlternatingDataEquiv (Module.finBasis (ZMod 2) V) ⟨B,hB⟩)

theorem binaryAlternatingQuadratic_polar [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) :
    (binaryAlternatingQuadratic B hB).polarBilin = B := by
  rw [binaryAlternatingQuadratic,basisQuadraticRefinement_polar]
  exact congrArg Subtype.val
    ((binaryAlternatingDataEquiv (Module.finBasis (ZMod 2) V)).symm_apply_apply ⟨B,hB⟩)

/-- The actual refinement fiber based at any genuine quadratic form is its full dual. -/
def binaryQuadraticRefinementEquivDualAt (q₀ : QuadraticForm (ZMod 2) V) :
    BinaryQuadraticRefinements q₀.polarBilin ≃ Module.Dual (ZMod 2) V where
  toFun q := binaryQuadraticDifferenceLinear q.val q₀ q.property
  invFun l := ⟨q₀ + binaryLinearQuadratic l,binaryQuadratic_add_linear_polar q₀ l⟩
  left_inv q := by
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    change q₀ x + binaryLinearQuadratic (binaryQuadraticDifferenceLinear q.val q₀ q.property) x = q.val x
    rw [binaryLinearQuadratic_apply]
    change q₀ x + (q.val x + q₀ x) = q.val x
    have h := CharTwo.add_self_eq_zero (q₀ x)
    linear_combination h
  right_inv l := by
    apply LinearMap.ext
    intro x
    change (q₀ x + binaryLinearQuadratic l x) + q₀ x = l x
    rw [binaryLinearQuadratic_apply]
    have h := CharTwo.add_self_eq_zero (q₀ x)
    linear_combination h

@[simp] theorem binaryQuadraticRefinementEquivDualAt_apply
    (q₀ : QuadraticForm (ZMod 2) V) (q : BinaryQuadraticRefinements q₀.polarBilin) (x : V) :
    binaryQuadraticRefinementEquivDualAt q₀ q x = q.val x + q₀ x := rfl

@[simp] theorem binaryQuadraticRefinementEquivDualAt_symm_apply
    (q₀ : QuadraticForm (ZMod 2) V) (l : Module.Dual (ZMod 2) V) (x : V) :
    ((binaryQuadraticRefinementEquivDualAt q₀).symm l).val x = q₀ x + l x := by
  change q₀ x + binaryLinearQuadratic l x = _
  rw [binaryLinearQuadratic_apply]

/-- No refinement-existence hypothesis is required for an alternating polar. -/
def binaryQuadraticRefinementEquivDual [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) :
    BinaryQuadraticRefinements B ≃ Module.Dual (ZMod 2) V :=
  (Equiv.subtypeEquivRight (fun q : QuadraticForm (ZMod 2) V => by
    rw [binaryAlternatingQuadratic_polar B hB])).trans
      (binaryQuadraticRefinementEquivDualAt (binaryAlternatingQuadratic B hB))

instance finiteBinaryQuadraticRefinements [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) : Finite (BinaryQuadraticRefinements B) := by
  letI : Finite V := Finite.of_equiv (Fin (finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  exact Finite.of_injective (fun q : BinaryQuadraticRefinements B => (q.val : V → ZMod 2))
    (fun q p h => Subtype.ext (QuadraticMap.ext (congrFun h)))

/-- The number is derived from the genuine dual equivalence, including dimension zero. -/
theorem binaryQuadraticRefinements_card [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) :
    Nat.card (BinaryQuadraticRefinements B) = 2 ^ finrank (ZMod 2) V := by
  rw [Nat.card_congr (binaryQuadraticRefinementEquivDual B hB),
    Module.natCard_eq_pow_finrank (K := ZMod 2),Subspace.dual_finrank_eq]
  simp

theorem binaryQuadraticRefinements_nonempty_iff [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) :
    Nonempty (BinaryQuadraticRefinements B) ↔ B.IsAlt := by
  constructor
  · rintro ⟨q⟩
    rw [← q.property]
    exact binaryQuadratic_polar_isAlt q.val
  · intro hB
    exact ⟨⟨binaryAlternatingQuadratic B hB,binaryAlternatingQuadratic_polar B hB⟩⟩

end ExactCriticalCurve.FiniteQuadratic
