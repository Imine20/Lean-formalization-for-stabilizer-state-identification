import ExactCriticalCurve.FiniteQuadratic.QuadraticTupleOrbits
import ExactCriticalCurve.FiniteQuadratic.QuadraticQuotientData

/-! The true orthogonal tuple invariant range, parameterized by actual quotient quadratic forms. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Full quadratic forms admitting a genuine injective realization in the specified ambient. -/
abbrev EmbeddableQuadraticForm (Q : QuadraticForm (ZMod 2) V)
    (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] :=
  {q : QuadraticForm (ZMod 2) E //
    ∃ f : E →ₗ[ZMod 2] V, Function.Injective f ∧ ∀ x, Q (f x)=q x}

/-- The actual quotient form determines a realized kernel/full-pullback invariant. -/
def quadraticQuotientInvariantMap (Q : QuadraticForm (ZMod 2) V) (n : ℕ)
    (p : Σ K : Submodule (ZMod 2) (Fin n → ZMod 2),
      EmbeddableQuadraticForm Q ((Fin n → ZMod 2) ⧸ K)) :
    Set.range (quadraticTupleInvariant Q n) := by
  refine ⟨(p.1,p.2.val.comp p.1.mkQ),?_⟩
  obtain ⟨f,hf,hfq⟩ := (quotientQuadratic_realization_iff_embedding p.1 p.2.val Q).mpr p.2.property
  refine ⟨(quadraticTupleLinearEquiv n).symm f,?_⟩
  unfold quadraticTupleInvariant
  rw [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · exact hf
  · ext x
    exact hfq x

theorem quadraticQuotientInvariantMap_injective (Q : QuadraticForm (ZMod 2) V) (n : ℕ) :
    Function.Injective (quadraticQuotientInvariantMap Q n) := by
  rintro ⟨K,q⟩ ⟨L,r⟩ h
  have hK : K=L := congrArg (fun x => x.val.1) h
  subst L
  have hq : q=r := by
    apply Subtype.ext
    ext z
    obtain ⟨x,rfl⟩ := K.mkQ_surjective z
    exact congrArg (fun y => y.val.2 x) h
  subst r
  rfl

theorem quadraticQuotientInvariantMap_surjective (Q : QuadraticForm (ZMod 2) V) (n : ℕ) :
    Function.Surjective (quadraticQuotientInvariantMap Q n) := by
  rintro ⟨p,x,hx⟩
  subst p
  let f := quadraticTupleLinearEquiv n x
  let K := LinearMap.ker f
  let g := K.liftQ f le_rfl
  have hg : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_liftQ,Submodule.mkQ_map_self]
  refine ⟨⟨K,⟨Q.comp g,g,hg,fun _ => rfl⟩⟩,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext z
    rfl

/-- The exact realized range contains all and only the genuine embeddable quotient forms. -/
def quadraticTupleRealizedEquivQuotients (Q : QuadraticForm (ZMod 2) V) (n : ℕ) :
    Set.range (quadraticTupleInvariant Q n) ≃
      Σ K : Submodule (ZMod 2) (Fin n → ZMod 2),
        EmbeddableQuadraticForm Q ((Fin n → ZMod 2) ⧸ K) :=
  (Equiv.ofBijective (quadraticQuotientInvariantMap Q n)
    ⟨quadraticQuotientInvariantMap_injective Q n,quadraticQuotientInvariantMap_surjective Q n⟩).symm

/-- Actual orthogonal orbits biject with the complete quotient-form data. -/
def quadraticTupleOrbitEquivQuotients [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (n : ℕ) :
    MulAction.orbitRel.Quotient (BinaryQuadraticIsometryGroup Q) (Fin n → V) ≃
      Σ K : Submodule (ZMod 2) (Fin n → ZMod 2),
        EmbeddableQuadraticForm Q ((Fin n → ZMod 2) ⧸ K) :=
  (quadraticTupleOrbitEquivRealized Q hQ n).trans (quadraticTupleRealizedEquivQuotients Q n)

/-- Burnside's actual fixed-space average counts the true full quadratic quotient data. -/
theorem quadraticTuple_fixedSpaceAverage_eq_quotients [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (n : ℕ) :
    (∑ u : BinaryQuadraticIsometryGroup Q, ((2 : ℚ)^n)^
      finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) =
      (Nat.card (Σ K : Submodule (ZMod 2) (Fin n → ZMod 2),
        EmbeddableQuadraticForm Q ((Fin n → ZMod 2) ⧸ K)) : ℚ) := by
  rw [quadraticTuple_fixedSpaceAverage_eq_realized Q hQ,
    Nat.card_congr (quadraticTupleRealizedEquivQuotients Q n)]

end ExactCriticalCurve.FiniteQuadratic
