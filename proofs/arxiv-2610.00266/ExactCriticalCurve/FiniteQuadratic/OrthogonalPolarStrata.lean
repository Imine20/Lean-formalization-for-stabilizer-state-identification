import ExactCriticalCurve.FiniteQuadratic.OrthogonalRealizedData
import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticEmbeddableRefinements
import ExactCriticalCurve.FiniteQuadratic.AlternatingBoundaryCount

/-! Actual polar strata retain every quadratic refinement, including nonzero radical restrictions. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Decomposition by the actual polar retains the complete quadratic form and its embedding. -/
def embeddableQuadraticPolarEquiv (Q : QuadraticForm (ZMod 2) V) :
    EmbeddableQuadraticForm Q A ≃
      Σ B : BinaryAlternatingFormData A, BinaryQuadraticEmbeddableRefinements B.val Q where
  toFun q := ⟨⟨q.val.polarBilin,binaryQuadratic_polar_isAlt q.val⟩,⟨⟨q.val,rfl⟩,q.property⟩⟩
  invFun p := ⟨p.2.val.val,p.2.property⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨B,hB⟩,⟨⟨q,hq⟩,he⟩⟩
    change q.polarBilin=B at hq
    subst B
    rfl

@[simp] theorem embeddableQuadraticPolarEquiv_polar (Q : QuadraticForm (ZMod 2) V)
    (q : EmbeddableQuadraticForm Q A) :
    (embeddableQuadraticPolarEquiv Q q).1.val=q.val.polarBilin := rfl

/-- Only the alternating polar descends through its radical; the full refinement stays on A. -/
def embeddableQuadraticRadicalEquiv (Q : QuadraticForm (ZMod 2) V) :
    EmbeddableQuadraticForm Q A ≃
      Σ R : Submodule (ZMod 2) A, Σ C : NondegenerateAlternatingForm (A ⧸ R),
        BinaryQuadraticEmbeddableRefinements (C.val.comp R.mkQ R.mkQ) Q :=
  ((embeddableQuadraticPolarEquiv Q).trans
    (Equiv.sigmaCongrLeft' (alternatingRadicalEquiv (E := A)))).trans
      (Equiv.sigmaAssoc (fun (R : Submodule (ZMod 2) A)
        (C : NondegenerateAlternatingForm (A ⧸ R)) =>
          BinaryQuadraticEmbeddableRefinements (C.val.comp R.mkQ R.mkQ) Q))

@[simp] theorem embeddableQuadraticRadicalEquiv_radical (Q : QuadraticForm (ZMod 2) V)
    (q : EmbeddableQuadraticForm Q A) :
    (embeddableQuadraticRadicalEquiv Q q).1=LinearMap.ker q.val.polarBilin := rfl

/-- Fixing the actual radical rank gives all subspaces of that rank and nondegenerate quotient forms. -/
def alternatingRadicalRankEquiv (b : ℕ) :
    {B : BinaryAlternatingFormData A // finrank (ZMod 2) (LinearMap.ker B.val)=b} ≃
      Σ R : Counting.BinarySubspaces A b, NondegenerateAlternatingForm (A ⧸ R.val) :=
  (alternatingRadicalEquiv.subtypeEquiv (fun _ => Iff.rfl)).trans
    (Equiv.subtypeSigmaEquiv
      (fun R : Submodule (ZMod 2) A => NondegenerateAlternatingForm (A ⧸ R))
      (fun R => finrank (ZMod 2) R=b))

/-- Count actual alternating polars of each radical rank, with no assumed sign distribution. -/
theorem alternatingRadicalRank_card [FiniteDimensional (ZMod 2) A]
    (b t : ℕ) (hd : finrank (ZMod 2) A=b+2*t) :
    Nat.card {B : BinaryAlternatingFormData A // finrank (ZMod 2) (LinearMap.ker B.val)=b} =
      Counting.binaryGaussian (b+2*t) b * nondegenerateAlternatingCount (2*t) := by
  letI : Finite A := Finite.of_equiv (Fin (finrank (ZMod 2) A) → ZMod 2)
    (Module.finBasis (ZMod 2) A).equivFun.toEquiv.symm
  letI : Finite (Submodule (ZMod 2) A) :=
    Finite.of_injective (fun K : Submodule (ZMod 2) A => (K : Set A)) SetLike.coe_injective
  letI (R : Submodule (ZMod 2) A) : Finite (A ⧸ R) :=
    Finite.of_surjective R.mkQ R.mkQ_surjective
  letI : Fintype (Counting.BinarySubspaces A b) := Fintype.ofFinite _
  rw [Nat.card_congr (alternatingRadicalRankEquiv (A := A) b),Nat.card_sigma]
  have hc (R : Counting.BinarySubspaces A b) :
      Nat.card (NondegenerateAlternatingForm (A ⧸ R.val))=nondegenerateAlternatingCount (2*t) := by
    apply nondegenerateAlternating_card_of_finrank
    have hq := R.val.finrank_quotient_add_finrank
    have hr := R.property
    omega
  simp_rw [hc]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card,
    binarySubspace_card_of_finrank hd]
  simp

end ExactCriticalCurve.FiniteQuadratic
