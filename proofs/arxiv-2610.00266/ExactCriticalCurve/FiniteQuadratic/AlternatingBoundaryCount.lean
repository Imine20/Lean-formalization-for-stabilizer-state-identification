import ExactCriticalCurve.FiniteQuadratic.AlternatingBoundary

/-! Count each actual boundary flag fiber through quotient subspaces. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

theorem binarySubspace_card_of_finrank {d : ℕ} (hd : finrank (ZMod 2) E = d) (t : ℕ) :
    Nat.card (Counting.BinarySubspaces E t) = Counting.binaryGaussian d t := by
  let b := (Module.finBasis (ZMod 2) E).reindex (finCongr hd)
  exact Nat.card_congr (Counting.subspacesOfFinrankEquiv b.equivFun t)

/-- Dimension-graded actual superspaces of K are precisely quotient subspaces. -/
def binarySuperspaceRankEquiv (K : Submodule (ZMod 2) E) (t : ℕ) :
    {R : Submodule (ZMod 2) E // K ≤ R ∧ finrank (ZMod 2) R = finrank (ZMod 2) K+t} ≃
      Counting.BinarySubspaces (E ⧸ K) t := by
  refine (Equiv.subtypeSubtypeEquivSubtypeInter (fun R => K ≤ R)
    (fun R => finrank (ZMod 2) R=finrank (ZMod 2) K+t)).symm.trans ?_
  refine K.comapMkQRelIso.toEquiv.symm.subtypeEquiv ?_
  intro R
  change finrank (ZMod 2) R.val = finrank (ZMod 2) K+t ↔
    finrank (ZMod 2) (R.val.map K.mkQ) = t
  have hd := Counting.finrank_map_mkQ_add_of_le K R.val R.property
  omega

abbrev AlternatingBoundaryFlagFiber (K : Submodule (ZMod 2) E) (ell : ℕ) :=
  Σ R : {R : Submodule (ZMod 2) E // K ≤ R ∧
    finrank (ZMod 2) E + finrank (ZMod 2) R = 2*ell+2*finrank (ZMod 2) K},
      NondegenerateAlternatingForm (E ⧸ R.val)

theorem alternatingBoundaryFlagFiber_card (ell a : ℕ) (ha : a ≤ ell)
    (K : Submodule (ZMod 2) E)
    (hK : finrank (ZMod 2) K + (ell+a) = finrank (ZMod 2) E) :
    Nat.card (AlternatingBoundaryFlagFiber K ell) =
      Counting.binaryGaussian (ell+a) (ell-a) * nondegenerateAlternatingCount (2*a) := by
  letI : Finite E := Finite.of_equiv (Fin (finrank (ZMod 2) E) → ZMod 2)
    (Module.finBasis (ZMod 2) E).equivFun.toEquiv.symm
  letI : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun K : Submodule (ZMod 2) E => (K : Set E)) SetLike.coe_injective
  letI (R : Submodule (ZMod 2) E) : Finite (E ⧸ R) :=
    Finite.of_surjective R.mkQ R.mkQ_surjective
  let Rtype := {R : Submodule (ZMod 2) E // K ≤ R ∧
    finrank (ZMod 2) E+finrank (ZMod 2) R=2*ell+2*finrank (ZMod 2) K}
  letI : Fintype Rtype := Fintype.ofFinite _
  have hq : finrank (ZMod 2) (E ⧸ K) = ell+a := by
    have hd := K.finrank_quotient_add_finrank
    omega
  have hc : ∀ R : Rtype, Nat.card (NondegenerateAlternatingForm (E ⧸ R.val)) =
      nondegenerateAlternatingCount (2*a) := by
    intro R
    apply nondegenerateAlternating_card_of_finrank
    have hd := R.val.finrank_quotient_add_finrank
    have hr := R.property.2
    omega
  have he : Rtype ≃ Counting.BinarySubspaces (E ⧸ K) (ell-a) :=
    (Equiv.subtypeEquivRight (fun R => by
      constructor
      · rintro ⟨hKR,hR⟩
        exact ⟨hKR, by omega⟩
      · rintro ⟨hKR,hR⟩
        exact ⟨hKR, by omega⟩)).trans (binarySuperspaceRankEquiv K (ell-a))
  change Nat.card (Σ R : Rtype, NondegenerateAlternatingForm (E ⧸ R.val)) = _
  rw [Nat.card_sigma]
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    Nat.card_congr he, binarySubspace_card_of_finrank hq]
  simp

/-- The boundary fixes codimension between ell and 2 ell, including all endpoints. -/
theorem alternatingBoundary_codimension_bounds (ell : ℕ) (p : AlternatingBoundaryInvariant E ell) :
    ell ≤ finrank (ZMod 2) E-finrank (ZMod 2) p.val.1 ∧
      finrank (ZMod 2) E-finrank (ZMod 2) p.val.1 ≤ 2*ell := by
  have hkr := Submodule.finrank_mono p.property.2.1
  have hr := (LinearMap.ker p.val.2).finrank_le
  have hk := p.val.1.finrank_le
  have he := p.property.2.2
  omega

/-- Actual half-rank index, recovered from the exact kernel codimension on the boundary. -/
def alternatingBoundaryIndex (ell : ℕ) (p : AlternatingBoundaryInvariant E ell) : Fin (ell+1) :=
  ⟨finrank (ZMod 2) E-finrank (ZMod 2) p.val.1-ell, by
    obtain ⟨_,h⟩ := alternatingBoundary_codimension_bounds ell p
    omega⟩

theorem alternatingBoundaryIndex_eq_iff (ell : ℕ) (p : AlternatingBoundaryInvariant E ell)
    (a : Fin (ell+1)) :
    alternatingBoundaryIndex ell p = a ↔
      finrank (ZMod 2) p.val.1+(ell+a.val)=finrank (ZMod 2) E := by
  obtain ⟨hl,hu⟩ := alternatingBoundary_codimension_bounds ell p
  have hk := p.val.1.finrank_le
  rw [Fin.ext_iff]
  change finrank (ZMod 2) E-finrank (ZMod 2) p.val.1-ell=a.val ↔ _
  omega

/-- The complete index fiber, retaining every actual flag and quotient form. -/
def alternatingBoundaryIndexFiberEquiv (ell : ℕ) (a : Fin (ell+1)) :
    {p : AlternatingBoundaryInvariant E ell // alternatingBoundaryIndex ell p=a} ≃
      Σ K : {K : Submodule (ZMod 2) E //
        finrank (ZMod 2) K+(ell+a.val)=finrank (ZMod 2) E},
        AlternatingBoundaryFlagFiber K.val ell :=
  ((alternatingBoundaryFlagEquiv ell).subtypeEquiv
    (fun p => alternatingBoundaryIndex_eq_iff ell p a)).trans
    (Equiv.subtypeSigmaEquiv (fun K : Submodule (ZMod 2) E => AlternatingBoundaryFlagFiber K ell)
      (fun K => finrank (ZMod 2) K+(ell+a.val)=finrank (ZMod 2) E))

theorem alternatingBoundaryIndexFiber_card (ell : ℕ) (a : Fin (ell+1)) :
    Nat.card {p : AlternatingBoundaryInvariant E ell // alternatingBoundaryIndex ell p=a} =
      if ell+a.val ≤ finrank (ZMod 2) E then
        Counting.binaryGaussian (finrank (ZMod 2) E) (finrank (ZMod 2) E-(ell+a.val)) *
          Counting.binaryGaussian (ell+a.val) (ell-a.val) * nondegenerateAlternatingCount (2*a.val)
      else 0 := by
  letI : Finite E := Finite.of_equiv (Fin (finrank (ZMod 2) E) → ZMod 2)
    (Module.finBasis (ZMod 2) E).equivFun.toEquiv.symm
  letI : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun K : Submodule (ZMod 2) E => (K : Set E)) SetLike.coe_injective
  letI (R : Submodule (ZMod 2) E) : Finite (E ⧸ R) :=
    Finite.of_surjective R.mkQ R.mkQ_surjective
  let Ktype := {K : Submodule (ZMod 2) E // finrank (ZMod 2) K+(ell+a.val)=finrank (ZMod 2) E}
  letI : Fintype Ktype := Fintype.ofFinite _
  have ha : a.val ≤ ell := Nat.le_of_lt_succ a.isLt
  rw [Nat.card_congr (alternatingBoundaryIndexFiberEquiv ell a), Nat.card_sigma]
  have hc : ∀ K : Ktype, Nat.card (AlternatingBoundaryFlagFiber K.val ell) =
      Counting.binaryGaussian (ell+a.val) (ell-a.val) * nondegenerateAlternatingCount (2*a.val) :=
    fun K => alternatingBoundaryFlagFiber_card ell a.val ha K.val K.property
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  by_cases h : ell+a.val ≤ finrank (ZMod 2) E
  · rw [if_pos h]
    have he : Ktype ≃ Counting.BinarySubspaces E (finrank (ZMod 2) E-(ell+a.val)) :=
      Equiv.subtypeEquivRight (fun K => by omega)
    rw [Nat.card_congr he, binarySubspace_card_of_finrank rfl]
    simpa using (Nat.mul_assoc (Counting.binaryGaussian (finrank (ZMod 2) E) (finrank (ZMod 2) E-(ell+a.val))) (Counting.binaryGaussian (ell+a.val) (ell-a.val)) (nondegenerateAlternatingCount (2*a.val))).symm
  · rw [if_neg h]
    haveI : IsEmpty Ktype := ⟨fun K => by have hk := K.property; omega⟩
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_mul]

theorem alternatingBoundary_card_sum (ell : ℕ) :
    Nat.card (AlternatingBoundaryInvariant E ell) =
      ∑ a : Fin (ell+1), if ell+a.val ≤ finrank (ZMod 2) E then
        Counting.binaryGaussian (finrank (ZMod 2) E) (finrank (ZMod 2) E-(ell+a.val)) *
          Counting.binaryGaussian (ell+a.val) (ell-a.val) * nondegenerateAlternatingCount (2*a.val)
      else 0 := by
  letI : Finite E := Finite.of_equiv (Fin (finrank (ZMod 2) E) → ZMod 2)
    (Module.finBasis (ZMod 2) E).equivFun.toEquiv.symm
  letI : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun K : Submodule (ZMod 2) E => (K : Set E)) SetLike.coe_injective
  letI (R : Submodule (ZMod 2) E) : Finite (E ⧸ R) :=
    Finite.of_surjective R.mkQ R.mkQ_surjective
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv (alternatingBoundaryIndex (E:=E) ell)).symm,
    Nat.card_sigma]
  exact Finset.sum_congr rfl (fun a _ => alternatingBoundaryIndexFiber_card ell a)

end ExactCriticalCurve.FiniteQuadratic
