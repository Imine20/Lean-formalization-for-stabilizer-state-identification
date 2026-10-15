import ExactCriticalCurve.FiniteQuadratic.AlternatingNondegenerateCount
import ExactCriticalCurve.FiniteQuadratic.SymplecticRealizedData

/-! Actual radical fibers and flags for all realizable alternating invariants. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- A surjective pullback has exactly the inverse image of the original radical. -/
theorem bilin_surjective_pullback_ker (C : LinearMap.BilinForm (ZMod 2) F)
    (q : E →ₗ[ZMod 2] F) (hq : Function.Surjective q) :
    LinearMap.ker (C.comp q q) = (LinearMap.ker C).comap q := by
  ext x
  change (C.comp q q) x = 0 ↔ C (q x) = 0
  constructor
  · intro h
    apply LinearMap.ext
    intro z
    obtain ⟨y,rfl⟩ := hq z
    exact congrArg (fun l : E →ₗ[ZMod 2] ZMod 2 => l y) h
  · intro h
    apply LinearMap.ext
    intro y
    exact congrArg (fun l : F →ₗ[ZMod 2] ZMod 2 => l (q y)) h

/-- Fixing the exact radical gives precisely the nondegenerate forms on the quotient. -/
def alternatingRadicalFiberEquiv (R : Submodule (ZMod 2) E) :
    {A : LinearMap.BilinForm (ZMod 2) E // A.IsAlt ∧ LinearMap.ker A = R} ≃
      NondegenerateAlternatingForm (E ⧸ R) where
  toFun A := ⟨alternatingQuotientForm A.val A.property.1 R (le_of_eq A.property.2.symm),
    alternatingQuotientForm_isAlt _ _ _ _, by
      apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
      rw [alternatingQuotientForm_ker, A.property.2, Submodule.mkQ_map_self]⟩
  invFun C := ⟨C.val.comp R.mkQ R.mkQ,
    (fun x => C.property.1.self_eq_zero (R.mkQ x)), by
      rw [bilin_surjective_pullback_ker _ _ R.mkQ_surjective,
        C.property.2.ker_eq_bot, Submodule.comap_bot, Submodule.ker_mkQ]⟩
  left_inv A := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl
  right_inv C := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := R.mkQ_surjective x
    obtain ⟨y,rfl⟩ := R.mkQ_surjective y
    rfl

abbrev BinaryAlternatingFormData (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] :=
  {A : LinearMap.BilinForm (ZMod 2) E // A.IsAlt}

/-- All actual alternating forms decompose by their actual radical, including the zero form. -/
def alternatingRadicalEquiv :
    BinaryAlternatingFormData E ≃
      Σ R : Submodule (ZMod 2) E, NondegenerateAlternatingForm (E ⧸ R) :=
  (Equiv.sigmaFiberEquiv (fun A : BinaryAlternatingFormData E => LinearMap.ker A.val)).symm.trans
    (Equiv.sigmaCongrRight (fun R =>
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun A : LinearMap.BilinForm (ZMod 2) E => A.IsAlt)
        (fun A => LinearMap.ker A = R)).trans (alternatingRadicalFiberEquiv R)))

@[simp] theorem alternatingRadicalEquiv_radical (A : BinaryAlternatingFormData E) :
    (alternatingRadicalEquiv A).1 = LinearMap.ker A.val := rfl

/-- The literal radical-containment and additive realizability bound. -/
def alternatingFlagAdmissible (m : ℕ) (K R : Submodule (ZMod 2) E) : Prop :=
  K ≤ R ∧ finrank (ZMod 2) E + finrank (ZMod 2) R ≤ m + 2*finrank (ZMod 2) K

/-- Repackage actual kernel/form data without changing either mathematical component. -/
def realizableAlternatingKernelEquiv (m : ℕ) :
    RealizableAlternatingInvariant E m ≃
      Σ K : Submodule (ZMod 2) E,
        {A : BinaryAlternatingFormData E // alternatingFlagAdmissible m K (LinearMap.ker A.val)} where
  toFun p := ⟨p.val.1, ⟨p.val.2,p.property.1⟩,p.property.2⟩
  invFun p := ⟨(p.1,p.2.val.val),p.2.val.property,p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact realizable invariants are actual flags with a nondegenerate quotient form. -/
def realizableAlternatingFlagEquiv (m : ℕ) :
    RealizableAlternatingInvariant E m ≃
      Σ K : Submodule (ZMod 2) E,
        Σ R : {R : Submodule (ZMod 2) E // alternatingFlagAdmissible m K R},
          NondegenerateAlternatingForm (E ⧸ R.val) :=
  (realizableAlternatingKernelEquiv m).trans
    (Equiv.sigmaCongrRight (fun K =>
      (alternatingRadicalEquiv.subtypeEquiv
        (fun A => (Iff.rfl : alternatingFlagAdmissible m K (LinearMap.ker A.val) ↔
          alternatingFlagAdmissible m K (alternatingRadicalEquiv A).1))).trans
      (Equiv.subtypeSigmaEquiv
        (fun R : Submodule (ZMod 2) E => NondegenerateAlternatingForm (E ⧸ R))
        (alternatingFlagAdmissible m K))))

@[simp] theorem realizableAlternatingFlagEquiv_kernel
    (m : ℕ) (p : RealizableAlternatingInvariant E m) :
    (realizableAlternatingFlagEquiv m p).1 = p.val.1 := rfl

@[simp] theorem realizableAlternatingFlagEquiv_radical
    (m : ℕ) (p : RealizableAlternatingInvariant E m) :
    (realizableAlternatingFlagEquiv m p).2.1.val = LinearMap.ker p.val.2 := rfl

/-- Any literal condition on the two actual kernels transports through radical classification. -/
def alternatingKernelPredicateEquiv
    (P : Submodule (ZMod 2) E → Submodule (ZMod 2) E → Prop) :
    {p : Submodule (ZMod 2) E × LinearMap.BilinForm (ZMod 2) E //
      p.2.IsAlt ∧ P p.1 (LinearMap.ker p.2)} ≃
      Σ K : Submodule (ZMod 2) E,
        Σ R : {R : Submodule (ZMod 2) E // P K R}, NondegenerateAlternatingForm (E ⧸ R.val) := by
  let pack : {p : Submodule (ZMod 2) E × LinearMap.BilinForm (ZMod 2) E //
      p.2.IsAlt ∧ P p.1 (LinearMap.ker p.2)} ≃
      Σ K : Submodule (ZMod 2) E, {A : BinaryAlternatingFormData E // P K (LinearMap.ker A.val)} :=
    { toFun := fun p => ⟨p.val.1, ⟨p.val.2,p.property.1⟩,p.property.2⟩
      invFun := fun p => ⟨(p.1,p.2.val.val),p.2.val.property,p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact pack.trans (Equiv.sigmaCongrRight (fun K =>
    (alternatingRadicalEquiv.subtypeEquiv (fun _ => Iff.rfl)).trans
      (Equiv.subtypeSigmaEquiv
        (fun R : Submodule (ZMod 2) E => NondegenerateAlternatingForm (E ⧸ R)) (P K))))

end ExactCriticalCurve.FiniteQuadratic
