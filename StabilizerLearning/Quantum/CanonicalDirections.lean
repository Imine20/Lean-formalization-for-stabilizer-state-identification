import StabilizerLearning.Quantum.TransverseGraph
import Mathlib.Data.Fin.Tuple.Basic

/-! Actual canonical reference-dual direction families and their first-column
coordinates. Pairwise isotropy imposes exactly symmetry of the top block. The
span is parametrized by actual linear combinations of the reported directions.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum

variable {p m b : ℕ} [Fact p.Prime]

/-- The reported physical directions have the prescribed first components and
commute in the symplectic sense. -/
abbrev CanonicalDirections (p m b : ℕ) [Fact p.Prime] :=
  {S : Fin m → PhaseSpace p (m+b) //
    (∀ i, (S i).1 = Pi.single (i.castAdd b) 1) ∧
    ∀ i j, symplecticPairing (S i) (S j) = 0}

/-- The top square block of a proposed list of first columns. -/
def firstColumnsTop (C : Matrix (Fin (m+b)) (Fin m) (ZMod p)) :
    Matrix (Fin m) (Fin m) (ZMod p) := fun i j => C (i.castAdd b) j

/-- Exactly the feasible first-column alphabet: only the top block is constrained. -/
abbrev FeasibleFirstColumns (p m b : ℕ) :=
  {C : Matrix (Fin (m+b)) (Fin m) (ZMod p) // (firstColumnsTop C).IsSymm}

/-- The vector family is recovered uniquely from its second components. -/
def canonicalDirectionsEquivFirstColumns :
    CanonicalDirections p m b ≃ FeasibleFirstColumns p m b where
  toFun S := ⟨fun r i => (S.val i).2 r, by
    apply Matrix.IsSymm.ext
    intro i j
    have hij := S.property.2 i j
    unfold symplecticPairing at hij
    rw [S.property.1 i, S.property.1 j] at hij
    simp only [single_one_dotProduct, dotProduct_single_one] at hij
    exact (sub_eq_zero.mp hij).symm⟩
  invFun C := ⟨fun i => (Pi.single (i.castAdd b) 1, fun r => C.val r i),
    ⟨fun _ => rfl, by
      intro i j
      simp only [symplecticPairing, single_one_dotProduct, dotProduct_single_one]
      exact sub_eq_zero.mpr (C.property.apply i j).symm⟩⟩
  left_inv S := by
    apply Subtype.ext
    funext i
    exact Prod.ext (S.property.1 i).symm rfl
  right_inv C := by
    apply Subtype.ext
    rfl

@[simp]
theorem canonicalDirectionsEquivFirstColumns_apply
    (S : CanonicalDirections p m b) (r : Fin (m+b)) (i : Fin m) :
    (canonicalDirectionsEquivFirstColumns S).val r i = (S.val i).2 r := rfl

@[simp]
theorem canonicalDirectionsEquivFirstColumns_symm_apply
    (C : FeasibleFirstColumns p m b) (i : Fin m) :
    ((canonicalDirectionsEquivFirstColumns (p := p) (m := m) (b := b)).symm C).val i =
      (Pi.single (i.castAdd b) 1, fun r => C.val r i) := rfl

/-- Assemble the unconstrained bottom block below the symmetric top block. -/
def firstColumnsOfBlocks (A : Matrix (Fin m) (Fin m) (ZMod p))
    (B : Matrix (Fin b) (Fin m) (ZMod p)) : Matrix (Fin (m+b)) (Fin m) (ZMod p) :=
  fun r i => Fin.addCases (fun j => A j i) (fun j => B j i) r

omit [Fact p.Prime] in
@[simp]
theorem firstColumnsOfBlocks_castAdd (A : Matrix (Fin m) (Fin m) (ZMod p))
    (B : Matrix (Fin b) (Fin m) (ZMod p)) (i j : Fin m) :
    firstColumnsOfBlocks A B (i.castAdd b) j = A i j := by
  simp [firstColumnsOfBlocks]

omit [Fact p.Prime] in
@[simp]
theorem firstColumnsOfBlocks_natAdd (A : Matrix (Fin m) (Fin m) (ZMod p))
    (B : Matrix (Fin b) (Fin m) (ZMod p)) (i : Fin b) (j : Fin m) :
    firstColumnsOfBlocks A B (i.natAdd m) j = B i j := by
  simp [firstColumnsOfBlocks]

omit [Fact p.Prime] in
@[simp]
theorem firstColumnsTop_ofBlocks (A : Matrix (Fin m) (Fin m) (ZMod p))
    (B : Matrix (Fin b) (Fin m) (ZMod p)) :
    firstColumnsTop (firstColumnsOfBlocks A B) = A := by
  ext i j
  simp [firstColumnsTop]

/-- Every feasible first-column list is uniquely a symmetric top block and an
arbitrary rectangular bottom block. -/
def feasibleFirstColumnsEquivBlocks :
    FeasibleFirstColumns p m b ≃
      SymmetricMatrices (Fin m) (ZMod p) × Matrix (Fin b) (Fin m) (ZMod p) where
  toFun C := (⟨firstColumnsTop C.val, C.property⟩, fun i j => C.val (i.natAdd m) j)
  invFun AB := ⟨firstColumnsOfBlocks AB.1.val AB.2, by
    simpa only [firstColumnsTop_ofBlocks] using AB.1.property⟩
  left_inv C := by
    apply Subtype.ext
    funext r i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) r
    · simp [firstColumnsTop]
    · simp
  right_inv AB := by
    apply Prod.ext
    · apply Subtype.ext
      exact firstColumnsTop_ofBlocks AB.1.val AB.2
    · funext i j
      exact firstColumnsOfBlocks_natAdd AB.1.val AB.2 i j

/-- The complete direction alphabet in actual physical phase space. -/
def canonicalDirectionsEquivBlocks :
    CanonicalDirections p m b ≃
      SymmetricMatrices (Fin m) (ZMod p) × Matrix (Fin b) (Fin m) (ZMod p) :=
  canonicalDirectionsEquivFirstColumns.trans feasibleFirstColumnsEquivBlocks

/-- The actual span of the announced physical directions. -/
def canonicalSpan (S : CanonicalDirections p m b) :
    Submodule (ZMod p) (PhaseSpace p (m+b)) :=
  Submodule.span (ZMod p) (Set.range S.val)

/-- Actual linear combination of a canonical direction family. -/
def canonicalLinearCombination (S : CanonicalDirections p m b) :
    Configuration p m →ₗ[ZMod p] PhaseSpace p (m+b) where
  toFun u := ∑ i, u i • S.val i
  map_add' u v := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c u := by
    simp [Finset.smul_sum, smul_smul]

@[simp]
theorem canonicalLinearCombination_apply (S : CanonicalDirections p m b)
    (u : Configuration p m) :
    canonicalLinearCombination S u = ∑ i, u i • S.val i := rfl

/-- First components of the actual sum of directions. -/
theorem canonicalLinearCombination_fst (S : CanonicalDirections p m b)
    (u : Configuration p m) :
    (canonicalLinearCombination S u).1 = ∑ i, u i • (S.val i).1 := by
  change (LinearMap.fst (ZMod p) (Configuration p (m+b)) (Configuration p (m+b)))
    (∑ i, u i • S.val i) = _
  rw [map_sum]
  simp only [map_smul, LinearMap.fst_apply]

/-- Second components of the actual sum of directions. -/
theorem canonicalLinearCombination_snd_sum (S : CanonicalDirections p m b)
    (u : Configuration p m) :
    (canonicalLinearCombination S u).2 = ∑ i, u i • (S.val i).2 := by
  change (LinearMap.snd (ZMod p) (Configuration p (m+b)) (Configuration p (m+b)))
    (∑ i, u i • S.val i) = _
  rw [map_sum]
  simp only [map_smul, LinearMap.snd_apply]

/-- Reading the first m first-component entries recovers every coefficient. -/
@[simp]
theorem canonicalLinearCombination_fst_castAdd (S : CanonicalDirections p m b)
    (u : Configuration p m) (j : Fin m) :
    (canonicalLinearCombination S u).1 (j.castAdd b) = u j := by
  rw [canonicalLinearCombination_fst]
  simp [S.property.1, Finset.sum_apply, Pi.single_apply]

/-- No nontrivial relation among the reported directions is possible. -/
theorem canonicalLinearCombination_injective (S : CanonicalDirections p m b) :
    Function.Injective (canonicalLinearCombination S) := by
  intro u v huv
  funext i
  have h := congrArg (fun z : PhaseSpace p (m+b) => z.1 (i.castAdd b)) huv
  simpa only [canonicalLinearCombination_fst_castAdd] using h

/-- The combinations fill precisely the actual span, not a larger space. -/
theorem range_canonicalLinearCombination (S : CanonicalDirections p m b) :
    LinearMap.range (canonicalLinearCombination S) = canonicalSpan S := by
  apply le_antisymm
  · rintro z ⟨u, rfl⟩
    change (∑ i, u i • S.val i) ∈ Submodule.span (ZMod p) (Set.range S.val)
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ (u i) (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [canonicalLinearCombination, Pi.single_apply]

/-- The remaining first-component entries vanish. -/
@[simp]
theorem canonicalLinearCombination_fst_natAdd (S : CanonicalDirections p m b)
    (u : Configuration p m) (j : Fin b) :
    (canonicalLinearCombination S u).1 (j.natAdd m) = 0 := by
  have hne (i : Fin m) : j.natAdd m ≠ i.castAdd b := by
    intro h
    have hv : m+j.val = i.val := congrArg Fin.val h
    omega
  rw [canonicalLinearCombination_fst]
  simp [S.property.1, Finset.sum_apply, hne]

/-- The second component is multiplication by the actual feasible first columns. -/
theorem canonicalLinearCombination_snd (S : CanonicalDirections p m b)
    (u : Configuration p m) :
    (canonicalLinearCombination S u).2 =
      (canonicalDirectionsEquivFirstColumns S).val *ᵥ u := by
  rw [canonicalLinearCombination_snd_sum]
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

@[simp]
theorem canonicalLinearCombination_snd_castAdd (S : CanonicalDirections p m b)
    (u : Configuration p m) (j : Fin m) :
    (canonicalLinearCombination S u).2 (j.castAdd b) =
      (firstColumnsTop (canonicalDirectionsEquivFirstColumns S).val *ᵥ u) j := by
  rw [canonicalLinearCombination_snd]
  rfl

theorem canonicalLinearCombination_mem (S : CanonicalDirections p m b)
    (u : Configuration p m) : canonicalLinearCombination S u ∈ canonicalSpan S := by
  rw [← range_canonicalLinearCombination S]
  exact ⟨u, rfl⟩

/-- Explicit coefficient parametrization of the actual span. Its inverse is
restriction of the first phase-space component to the first m positions. -/
def canonicalSpanLinearEquiv (S : CanonicalDirections p m b) :
    Configuration p m ≃ₗ[ZMod p] canonicalSpan S where
  toFun u := ⟨canonicalLinearCombination S u, canonicalLinearCombination_mem S u⟩
  invFun z := fun i => z.val.1 (i.castAdd b)
  left_inv u := by
    funext i
    exact canonicalLinearCombination_fst_castAdd S u i
  right_inv z := by
    have hz : z.val ∈ LinearMap.range (canonicalLinearCombination S) := by
      rw [range_canonicalLinearCombination S]
      exact z.property
    obtain ⟨u, hu⟩ := hz
    apply Subtype.ext
    change canonicalLinearCombination S (fun i => z.val.1 (i.castAdd b)) = z.val
    rw [← hu]
    congr 1
    funext i
    exact canonicalLinearCombination_fst_castAdd S u i
  map_add' u v := Subtype.ext (map_add (canonicalLinearCombination S) u v)
  map_smul' c u := Subtype.ext (map_smul (canonicalLinearCombination S) c u)

@[simp]
theorem coe_canonicalSpanLinearEquiv_apply (S : CanonicalDirections p m b)
    (u : Configuration p m) :
    ((canonicalSpanLinearEquiv S u : canonicalSpan S) : PhaseSpace p (m+b)) =
      ∑ i, u i • S.val i := rfl

@[simp]
theorem canonicalSpanLinearEquiv_symm_apply (S : CanonicalDirections p m b)
    (z : canonicalSpan S) (i : Fin m) :
    (canonicalSpanLinearEquiv S).symm z i = z.val.1 (i.castAdd b) := rfl

@[simp]
theorem finrank_canonicalSpan (S : CanonicalDirections p m b) :
    Module.finrank (ZMod p) (canonicalSpan S) = m := by
  simpa only [Configuration, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
    (canonicalSpanLinearEquiv S).finrank_eq.symm


@[simp]
theorem canonicalLinearCombination_single (S : CanonicalDirections p m b) (i : Fin m) :
    canonicalLinearCombination S (Pi.single i 1) = S.val i := by
  simp [canonicalLinearCombination, Pi.single_apply]

@[simp]
theorem coe_canonicalSpanLinearEquiv_single (S : CanonicalDirections p m b) (i : Fin m) :
    ((canonicalSpanLinearEquiv S (Pi.single i 1) : canonicalSpan S) :
      PhaseSpace p (m+b)) = S.val i :=
  canonicalLinearCombination_single S i

/-- The canonical directions of a symmetric graph are its first m graph columns. -/
def canonicalDirectionsOfGraph
    (A : Matrix (Fin (m+b)) (Fin (m+b)) (ZMod p)) (hA : A.IsSymm) :
    CanonicalDirections p m b :=
  ⟨fun i => (Pi.single (i.castAdd b) 1, A *ᵥ Pi.single (i.castAdd b) 1),
    ⟨fun _ => rfl, fun i j =>
      (isIsotropic_graphSubmodule_iff A).mpr hA
        (Pi.single (i.castAdd b) 1, A *ᵥ Pi.single (i.castAdd b) 1) rfl
        (Pi.single (j.castAdd b) 1, A *ᵥ Pi.single (j.castAdd b) 1) rfl⟩⟩

@[simp]
theorem canonicalDirectionsOfGraph_apply
    (A : Matrix (Fin (m+b)) (Fin (m+b)) (ZMod p)) (hA : A.IsSymm) (i : Fin m) :
    (canonicalDirectionsOfGraph (m := m) (b := b) A hA).val i =
      (Pi.single (i.castAdd b) 1, A.col (i.castAdd b)) := by
  simp [canonicalDirectionsOfGraph, Matrix.mulVec_single_one]

@[simp]
theorem canonicalDirectionsEquivFirstColumns_ofGraph
    (A : Matrix (Fin (m+b)) (Fin (m+b)) (ZMod p)) (hA : A.IsSymm)
    (r : Fin (m+b)) (i : Fin m) :
    (canonicalDirectionsEquivFirstColumns
      (canonicalDirectionsOfGraph (m := m) (b := b) A hA)).val r i = A r (i.castAdd b) := by
  change (A *ᵥ Pi.single (i.castAdd b) 1) r = A r (i.castAdd b)
  rw [Matrix.mulVec_single_one]
  rfl

theorem canonicalDirectionsOfGraph_mem
    (A : Matrix (Fin (m+b)) (Fin (m+b)) (ZMod p)) (hA : A.IsSymm) (i : Fin m) :
    (canonicalDirectionsOfGraph (m := m) (b := b) A hA).val i ∈ graphSubmodule A := rfl

theorem canonicalSpan_ofGraph_le
    (A : Matrix (Fin (m+b)) (Fin (m+b)) (ZMod p)) (hA : A.IsSymm) :
    canonicalSpan (canonicalDirectionsOfGraph (m := m) (b := b) A hA) ≤ graphSubmodule A := by
  apply Submodule.span_le.mpr
  rintro z ⟨i, rfl⟩
  exact canonicalDirectionsOfGraph_mem A hA i

end StabilizerLearning.Quantum
