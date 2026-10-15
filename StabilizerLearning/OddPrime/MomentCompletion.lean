import StabilizerLearning.Foundations.CompletionCounting

noncomputable section
namespace StabilizerLearning
open Matrix

variable {F : Type*} [Field F]

/-- Both quadratic and linear moments are retained. -/
abbrev FullMoment (ι F : Type*) := SymmetricMatrices ι F × (ι → F)

/-- The genuine moment of an ordered k-tuple, represented by its column matrix. -/
def fullMoment {ι : Type*} {k : ℕ} (X : Matrix ι (Fin k) F) : FullMoment ι F :=
  (⟨X * X.transpose, by simp only [Matrix.IsSymm, Matrix.transpose_mul,
    Matrix.transpose_transpose]⟩, X *ᵥ (fun _ => 1))

/-- Lower coordinates of a full moment, with no chosen realization. -/
def lowerMoment {m n : ℕ} (z : FullMoment (Fin m ⊕ Fin n) F) : FullMoment (Fin n) F :=
  (⟨z.1.val.submatrix Sum.inr Sum.inr, z.1.property.submatrix Sum.inr⟩,
    fun i => z.2 (Sum.inr i))

/-- Visible coordinates (Q₁₁,(Q₁₂,S₁)), retaining the linear moment as a last column. -/
def visibleMoment {m n : ℕ} (z : FullMoment (Fin m ⊕ Fin n) F) :
    SymmetricMatrices (Fin m) F × Matrix (Fin m) (Fin (n+1)) F :=
  (⟨z.1.val.submatrix Sum.inl Sum.inl, z.1.property.submatrix Sum.inl⟩,
    fun i j => Sum.elim (fun a => z.1.val (Sum.inl i) (Sum.inr a))
      (fun _ : Fin 1 => z.2 (Sum.inl i)) (finSumFinEquiv.symm j))

/-- Occurring full moments above a prescribed lower moment.  Existence ranges
over every tuple X, not tuples above a single preselected lower factor X₂. -/
abbrev OccurringMomentFiber (F : Type*) [Field F] (m n k : ℕ)
    (ζ : FullMoment (Fin n) F) :=
  {z : FullMoment (Fin m ⊕ Fin n) F //
    (∃ X : Matrix (Fin m ⊕ Fin n) (Fin k) F, fullMoment X = z) ∧ lowerMoment z = ζ}

/-- The actual visible image, defined at the moment level. -/
abbrev VisibleMomentSet (F : Type*) [Field F] (m n k : ℕ)
    (ζ : FullMoment (Fin n) F) :=
  {v : SymmetricMatrices (Fin m) F × Matrix (Fin m) (Fin (n+1)) F //
    ∃ z : OccurringMomentFiber F m n k ζ, visibleMoment z.val = v}

/-- Fixing the lower moment makes deletion of its coordinates injective. -/
theorem moment_eq_of_lower_visible {m n : ℕ}
    (z w : FullMoment (Fin m ⊕ Fin n) F)
    (hlower : lowerMoment z = lowerMoment w)
    (hvisible : visibleMoment z = visibleMoment w) : z = w := by
  have hQ11 : z.1.val.submatrix Sum.inl Sum.inl = w.1.val.submatrix Sum.inl Sum.inl :=
    congrArg (fun v => v.1.val) hvisible
  have hQ22 : z.1.val.submatrix Sum.inr Sum.inr = w.1.val.submatrix Sum.inr Sum.inr :=
    congrArg (fun v => v.1.val) hlower
  have hC := congrArg Prod.snd hvisible
  have hS2 := congrArg Prod.snd hlower
  have hQ12 (i : Fin m) (j : Fin n) :
      z.1.val (Sum.inl i) (Sum.inr j) = w.1.val (Sum.inl i) (Sum.inr j) := by
    simpa [visibleMoment] using congrFun (congrFun hC i) (finSumFinEquiv (Sum.inl j))
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    rcases i with (i | i) <;> rcases j with (j | j)
    · exact congrFun (congrFun hQ11 i) j
    · exact hQ12 i j
    · exact (z.1.property.apply (Sum.inl j) (Sum.inr i)).trans
        ((hQ12 j i).trans (w.1.property.apply (Sum.inr i) (Sum.inl j)))
    · exact congrFun (congrFun hQ22 i) j
  · ext i
    cases i with
    | inl i =>
      simpa [visibleMoment] using congrFun (congrFun hC i)
        (finSumFinEquiv (Sum.inr (0 : Fin 1)))
    | inr i => exact congrFun hS2 i

/-- Actual full moments and their visible image are bijective. -/
def momentFiberVisibleEquiv {m n k : ℕ} (ζ : FullMoment (Fin n) F) :
    OccurringMomentFiber F m n k ζ ≃ VisibleMomentSet F m n k ζ :=
  Equiv.ofBijective (fun z => ⟨visibleMoment z.val, z, rfl⟩) (by
    constructor
    · intro z w h
      apply Subtype.ext
      exact moment_eq_of_lower_visible z.val w.val (z.property.2.trans w.property.2.symm)
        (congrArg Subtype.val h)
    · intro v
      obtain ⟨z, hz⟩ := v.property
      exact ⟨z, Subtype.ext hz⟩)

/-- The fixed augmented lower matrix. Its final entry is the field image of k;
no nonzero hypothesis is imposed when the characteristic divides k. -/
def lowerAugmentedMatrix {n : ℕ} (ζ : FullMoment (Fin n) F) (k : ℕ) :
    SymmetricMatrices (Fin (n+1)) F :=
  let S : Matrix (Fin n) (Fin 1) F := fun i _ => ζ.2 i
  let K : Matrix (Fin 1) (Fin 1) F := fun _ _ => (k : F)
  let B : SymmetricMatrices (Fin n ⊕ Fin 1) F :=
    ⟨Matrix.fromBlocks ζ.1.val S S.transpose K,
      ζ.1.property.fromBlocks rfl (by rfl)⟩
  ⟨B.val.submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    B.property.submatrix finSumFinEquiv.symm⟩

/-- Append the all-ones row while placing it with the lower-coordinate block. -/
def augmentedRealization {m n k : ℕ} (X : Matrix (Fin m ⊕ Fin n) (Fin k) F) :
    Matrix (Fin m ⊕ Fin (n+1)) (Fin k) F := fun i j =>
  Sum.elim (fun i => X (Sum.inl i) j)
    (fun b => Sum.elim (fun a => X (Sum.inr a) j) (fun _ : Fin 1 => 1)
      (finSumFinEquiv.symm b)) i

/-- Exact augmented Gram factorization of every realized completion. -/
theorem realized_completion_gram {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) F) :
    Matrix.fromBlocks (visibleMoment (fullMoment X)).1.val
      (visibleMoment (fullMoment X)).2 (visibleMoment (fullMoment X)).2.transpose
      (lowerAugmentedMatrix (lowerMoment (fullMoment X)) k).val =
      augmentedRealization X * (augmentedRealization X).transpose := by
  ext i j
  rcases i with (i | i) <;> rcases j with (j | j)
  · rfl
  · obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases j <;> simp [visibleMoment, fullMoment, augmentedRealization,
      Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    cases i <;> simp [visibleMoment, fullMoment, augmentedRealization,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases i <;> cases j <;> simp [lowerAugmentedMatrix, lowerMoment,
      fullMoment, augmentedRealization, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, mul_comm]

/-- Every actually realized visible value satisfies the ambient rank budget. -/
theorem realized_completion_rank_le {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) F) :
    (Matrix.fromBlocks (visibleMoment (fullMoment X)).1.val
      (visibleMoment (fullMoment X)).2 (visibleMoment (fullMoment X)).2.transpose
      (lowerAugmentedMatrix (lowerMoment (fullMoment X)) k).val).rank ≤ k := by
  rw [realized_completion_gram]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa only [Fintype.card_fin] using (Matrix.rank_le_card_width (augmentedRealization X)))

/-- The augmented lower factor, again appending the literal all-ones row. -/
def lowerAugmentedRealization {n k : ℕ} (X : Matrix (Fin n) (Fin k) F) :
    Matrix (Fin (n+1)) (Fin k) F := fun i j =>
  Sum.elim (fun a => X a j) (fun _ : Fin 1 => 1) (finSumFinEquiv.symm i)

/-- The exact lower-moment/augmented-Gram bridge, including k = 0. -/
theorem lowerAugmentedMatrix_realized_gram {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) F) :
    (lowerAugmentedMatrix (fullMoment X) k).val =
      lowerAugmentedRealization X * (lowerAugmentedRealization X).transpose := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [lowerAugmentedMatrix, fullMoment,
    lowerAugmentedRealization, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- The inclusion into the actual low-rank completion type. Its rank certificate
is derived from a realization, never supplied as a premise. -/
def visibleToCompletion {m n k : ℕ} (ζ : FullMoment (Fin n) F)
    (v : VisibleMomentSet F m n k ζ) : CompletionPairs (lowerAugmentedMatrix ζ k) m k :=
  ⟨v.val, by
    obtain ⟨z, hv⟩ := v.property
    obtain ⟨X, hX⟩ := z.property.1
    have hvisible : visibleMoment (fullMoment X) = v.val :=
      (congrArg visibleMoment hX).trans hv
    have hlower : lowerMoment (fullMoment X) = ζ :=
      (congrArg lowerMoment hX).trans z.property.2
    rw [← hvisible, ← hlower]
    exact realized_completion_rank_le X⟩

theorem visibleToCompletion_injective {m n k : ℕ} (ζ : FullMoment (Fin n) F) :
    Function.Injective (visibleToCompletion (m := m) (k := k) ζ) := by
  intro v w h
  have hh := congrArg (fun x : CompletionPairs (lowerAugmentedMatrix ζ k) m k => x.val) h
  exact Subtype.ext hh

/-- Literal d_ζ: the number of occurring full moments above ζ. -/
def occurringMomentCount (F : Type*) [Field F] (m n k : ℕ)
    (ζ : FullMoment (Fin n) F) : ℕ := Nat.card (OccurringMomentFiber F m n k ζ)

/-- Deleting the fixed lower coordinates preserves the number of moment values. -/
theorem card_momentFiber_eq_visible {m n k : ℕ} (ζ : FullMoment (Fin n) F) :
    Nat.card (OccurringMomentFiber F m n k ζ) = Nat.card (VisibleMomentSet F m n k ζ) :=
  Nat.card_congr (momentFiberVisibleEquiv ζ)

/-- Cardinality version of the actual-to-ambient inclusion. -/
theorem card_visible_le_completion [Fintype F] {m n k : ℕ}
    (ζ : FullMoment (Fin n) F) :
    Nat.card (VisibleMomentSet F m n k ζ) ≤
      Nat.card (CompletionPairs (lowerAugmentedMatrix ζ k) m k) :=
  Nat.card_le_card_of_injective _ (visibleToCompletion_injective ζ)

/-- The actual fibre is bounded by the actual ambient completion set. -/
theorem occurringMomentCount_le_completion [Fintype F] {m n k : ℕ}
    (ζ : FullMoment (Fin n) F) :
    occurringMomentCount F m n k ζ ≤
      Nat.card (CompletionPairs (lowerAugmentedMatrix ζ k) m k) := by
  unfold occurringMomentCount
  rw [card_momentFiber_eq_visible]
  exact card_visible_le_completion ζ

/-- Substitute the proved exact count of the actual ambient set. This is an
upper bound for moment values, not a claim that every ambient pair is realizable. -/
theorem occurringMomentCount_le_exact_completion [Fintype F] {m n k : ℕ}
    (ζ : FullMoment (Fin n) F) :
    occurringMomentCount F m n k ζ ≤
      completionCountExpression F m (n+1-(lowerAugmentedMatrix ζ k).val.rank)
        (lowerAugmentedMatrix ζ k).val.rank k := by
  rw [← card_completionPairs]
  exact occurringMomentCount_le_completion ζ

/-- The proved prescribed-rank estimates now bound the original occurring-moment
fibre, via the proved injection and exact ambient count. -/
theorem occurringMomentCount_bound [Fintype F] {m n k : ℕ}
    (ζ : FullMoment (Fin n) F) :
    (occurringMomentCount F m n k ζ : ℝ) ≤
      16 * ((m+1 : ℕ) : ℝ)^2 * (Fintype.card F : ℝ)^
        (completionRankGrid m (n+1-(lowerAugmentedMatrix ζ k).val.rank)
          (lowerAugmentedMatrix ζ k).val.rank k).sup
          (fun z => completionRankExponent m (n+1-(lowerAugmentedMatrix ζ k).val.rank)
            (lowerAugmentedMatrix ζ k).val.rank z.1 z.2) := by
  have hi : (occurringMomentCount F m n k ζ : ℝ) ≤
      (Nat.card (CompletionPairs (lowerAugmentedMatrix ζ k) m k) : ℝ) := by
    exact_mod_cast occurringMomentCount_le_completion (m := m) ζ
  exact hi.trans (completionPairs_count_bound (lowerAugmentedMatrix ζ k) m k)

/-- If the fixed augmented block alone exceeds the budget, the occurring fibre
is actually empty. This also covers prescribed lower moments with no realization. -/
theorem occurringMomentFiber_isEmpty_of_rank_gt {m n k : ℕ}
    (ζ : FullMoment (Fin n) F) (h : k < (lowerAugmentedMatrix ζ k).val.rank) :
    IsEmpty (OccurringMomentFiber F m n k ζ) := by
  letI := completionPairs_isEmpty (lowerAugmentedMatrix ζ k) m k h
  exact ⟨fun z => isEmptyElim (visibleToCompletion ζ (momentFiberVisibleEquiv ζ z))⟩

/-- Taking lower moments commutes with taking the lower rows of a realization. -/
theorem lowerMoment_fullMoment {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) F) :
    lowerMoment (fullMoment X) = fullMoment (X.submatrix Sum.inr id) := rfl

/-- A prescribed lower moment with no realization has no occurring full moment
above it. No arbitrary witness is chosen for such a fibre. -/
theorem occurringMomentFiber_isEmpty_of_no_lower_realization {m n k : ℕ}
    (ζ : FullMoment (Fin n) F)
    (h : ¬ ∃ X : Matrix (Fin n) (Fin k) F, fullMoment X = ζ) :
    IsEmpty (OccurringMomentFiber F m n k ζ) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨X, hX⟩ := z.property.1
  apply h
  refine ⟨X.submatrix Sum.inr id, ?_⟩
  rw [← lowerMoment_fullMoment, hX]
  exact z.property.2

/-- The whole visible coordinate space has the target-coordinate cardinality. -/
theorem card_visible_coordinate_space [Fintype F] (m n : ℕ) :
    Nat.card (SymmetricMatrices (Fin m) F × Matrix (Fin m) (Fin (n+1)) F) =
      Fintype.card F ^ (m * (m+1) / 2 + m * (n+1)) := by
  rw [Nat.card_prod, card_matrix_fin, Nat.card_eq_fintype_card,
    card_symmetricMatrices, pow_add]

/-- The fibre count is bounded by the whole visible coordinate space as well
as by the low-rank ambient set, allowing the usual clipped completion factor. -/
theorem occurringMomentCount_le_visible_space [Fintype F] {m n k : ℕ}
    (ζ : FullMoment (Fin n) F) :
    occurringMomentCount F m n k ζ ≤ Fintype.card F ^ (m * (m+1) / 2 + m * (n+1)) := by
  unfold occurringMomentCount
  rw [card_momentFiber_eq_visible, ← card_visible_coordinate_space]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

end StabilizerLearning
