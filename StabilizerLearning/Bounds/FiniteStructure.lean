import StabilizerLearning.Bounds.MomentProbabilityBridge

noncomputable section
namespace StabilizerLearning
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The finite support consists of actual nonempty row-space events. -/
def positiveMassRowParameters (F : Type*) [Field F] [Fintype F] (b k : ℕ) :
    Finset (Fin (k+1) × Fin (k+1)) := by
  classical
  exact Finset.univ.filter fun z => (rowSpaceEvent F b k z.1.val z.2.val).Nonempty

/-- The augmented support uses the prescribed vector and actual lower matrices. -/
def positiveMassAugmentedRowParameters (F : Type*) [Field F] [Fintype F]
    (b k : ℕ) (v : Fin k → F) : Finset (Fin (k+1) × Fin (k+1)) := by
  classical
  exact Finset.univ.filter fun z =>
    (augmentedRowSpaceEvent F b k z.1.val z.2.val v).Nonempty

theorem mem_positiveMassRowParameters [Fintype F] (b k : ℕ)
    (z : Fin (k+1) × Fin (k+1)) :
    z ∈ positiveMassRowParameters F b k ↔
      (rowSpaceEvent F b k z.1.val z.2.val).Nonempty := by
  classical
  simp [positiveMassRowParameters]

theorem mem_positiveMassAugmentedRowParameters [Fintype F] (b k : ℕ)
    (v : Fin k → F) (z : Fin (k+1) × Fin (k+1)) :
    z ∈ positiveMassAugmentedRowParameters F b k v ↔
      (augmentedRowSpaceEvent F b k z.1.val z.2.val v).Nonempty := by
  classical
  simp [positiveMassAugmentedRowParameters]

/-- Uniform finite matrix mass is positive exactly on a nonempty actual event. -/
theorem uniformMatrixProbability_pos_iff_nonempty [Fintype F] {b k : ℕ}
    (E : Set (Matrix (Fin b) (Fin k) F)) :
    0 < uniformMatrixProbability E ↔ E.Nonempty := by
  rw [uniformMatrixProbability_eq_card]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_pos_iff_of_pos_right (pow_pos hq _), Nat.cast_pos, Nat.card_pos_iff]
  exact ⟨fun h => Set.nonempty_coe_sort.mp h.1,
    fun h => ⟨Set.nonempty_coe_sort.mpr h, inferInstance⟩⟩

theorem positiveMassRowParameters_probability [Fintype F] (b k : ℕ)
    (z : Fin (k+1) × Fin (k+1)) :
    z ∈ positiveMassRowParameters F b k ↔
      0 < uniformMatrixProbability (rowSpaceEvent F b k z.1.val z.2.val) := by
  rw [mem_positiveMassRowParameters, uniformMatrixProbability_pos_iff_nonempty]

theorem positiveMassAugmentedRowParameters_probability [Fintype F] (b k : ℕ)
    (v : Fin k → F) (z : Fin (k+1) × Fin (k+1)) :
    z ∈ positiveMassAugmentedRowParameters F b k v ↔
      0 < uniformMatrixProbability (augmentedRowSpaceEvent F b k z.1.val z.2.val v) := by
  rw [mem_positiveMassAugmentedRowParameters, uniformMatrixProbability_pos_iff_nonempty]

theorem rowSpace_finrank_le_rows {b k : ℕ} (Y : Matrix (Fin b) (Fin k) F) :
    Module.finrank F (rowSpace Y) ≤ b := by
  simpa only [rowSpace, Module.finrank_pi, Fintype.card_fin] using
    Y.transpose.mulVecLin.finrank_range_le

/-- Feasibility comes from the actual standard-dot radical, in every characteristic. -/
theorem positiveMassRowParameters_feasible [Fintype F] {b k : ℕ}
    {z : Fin (k+1) × Fin (k+1)} (hz : z ∈ positiveMassRowParameters F b k) :
    z.2.val ≤ z.1.val ∧ z.1.val + z.2.val ≤ k ∧ z.1.val ≤ b := by
  obtain ⟨Y, hY⟩ := (mem_positiveMassRowParameters b k z).mp hz
  have hf := prescribedRadical_feasible
    (⟨rowSpace Y, hY⟩ : PrescribedRadicalSubspaces F k z.1.val z.2.val)
  exact ⟨hf.1, hf.2, hY.1 ▸ rowSpace_finrank_le_rows Y⟩

theorem positiveMassAugmentedRowParameters_feasible [Fintype F] {b k : ℕ}
    (v : Fin k → F) {z : Fin (k+1) × Fin (k+1)}
    (hz : z ∈ positiveMassAugmentedRowParameters F b k v) :
    z.2.val ≤ z.1.val ∧ z.1.val + z.2.val ≤ k ∧ z.1.val ≤ b+1 := by
  obtain ⟨Y, hY⟩ := (mem_positiveMassAugmentedRowParameters b k v z).mp hz
  have hf := prescribedRadical_feasible
    (⟨augmentedRowSpace v Y, hY⟩ : PrescribedRadicalSubspaces F k z.1.val z.2.val)
  have hd := rowSpace_finrank_le_rows (augmentRows Y v)
  rw [rowSpace_augmentRows] at hd
  exact ⟨hf.1, hf.2, hY.1 ▸ hd⟩

/-- The paper's completion domain. Dimension differences are signed integers. -/
def sourceCompletionDomain (m h k a u ell t : ℕ) : Prop :=
  ell ≤ m ∧ (ell : ℤ) ≤ (h : ℤ) - a + u ∧ t ≤ m-ell ∧
    (a : ℤ) - u + 2*ell + t ≤ k

/-- Both ordinary and binary domains are exactly the actual completion rank grid;
use h=b+1 or h=b respectively. -/
theorem completionRankGrid_iff_source (m h k a u ell t : ℕ)
    (hua : u ≤ a) (hah : a-u ≤ h) :
    (ell,t) ∈ completionRankGrid m (h-(a-u)) (a-u) k ↔
      sourceCompletionDomain m h k a u ell t := by
  rw [completionRankGrid_mem]
  unfold sourceCompletionDomain
  omega

/-- Integer-valued source exponent. The natural half-factors are precisely the
nonnegative integral block dimensions on the completion domain. All dimension
differences involving a,u and the later normalization remain signed integers. -/
def sourceFiniteExponent (m h a u ell t : ℕ) : ℤ :=
  (m : ℤ)*((a : ℤ)-u) + (ell : ℤ)*((m : ℤ)+h-a+u-ell) +
    (ell*m-ell*(ell-1)/2 : ℕ) + (t*(2*(m-ell)-t+1)/2 : ℕ)

def sourceBinaryFiniteExponent (m b a u ell t : ℕ) : ℤ :=
  (m : ℤ) + sourceFiniteExponent m b a u ell t

/-- The full visible-label exponent is fixed and common to both branches. -/
def visibleLabelExponent (m b : ℕ) : ℕ :=
  m*(b+1) + m*(m+1)/2

theorem sourceFiniteExponent_eq_completionRankExponent (m h a u ell t : ℕ)
    (hua : u ≤ a) (hah : a-u ≤ h) (hell : ell ≤ m) (ht : t ≤ m-ell) :
    sourceFiniteExponent m h a u ell t =
      (completionRankExponent m (h-(a-u)) (a-u) ell t : ℤ) := by
  unfold completionRankExponent
  rw [completionFreeExponent_eq_paper m ell hell, rankExponent_eq_paper (m-ell) t ht]
  unfold sourceFiniteExponent
  have hs : ell ≤ m + (h-(a-u)) := by omega
  push_cast [Nat.cast_sub hua, Nat.cast_sub hah, Nat.cast_sub hs]
  ring

/-- The characteristic-two lift changes the finite exponent by exactly m-ell. -/
theorem sourceBinaryFiniteExponent_correction (m b a u ell t : ℕ) :
    sourceBinaryFiniteExponent m b a u ell t =
      sourceFiniteExponent m (b+1) a u ell t + ((m : ℤ)-ell) := by
  unfold sourceBinaryFiniteExponent sourceFiniteExponent
  push_cast
  ring

theorem sourceBinaryFiniteExponent_correction_bounds (m b a u ell t : ℕ)
    (hell : ell ≤ m) :
    0 ≤ sourceBinaryFiniteExponent m b a u ell t -
      sourceFiniteExponent m (b+1) a u ell t ∧
    sourceBinaryFiniteExponent m b a u ell t -
      sourceFiniteExponent m (b+1) a u ell t ≤ m := by
  rw [sourceBinaryFiniteExponent_correction]
  omega

/-- In the feasible range, the free-block term equals the literal signed
subtraction appearing in the paper; no subtraction is being silently clipped. -/
theorem sourceFiniteExponent_eq_signed (m h a u ell t : ℕ) (hell : ell ≤ m) :
    sourceFiniteExponent m h a u ell t =
      (m : ℤ)*((a : ℤ)-u) + (ell : ℤ)*((m : ℤ)+h-a+u-ell) +
      (ell : ℤ)*m - (ell*(ell-1)/2 : ℕ) +
      (t*(2*(m-ell)-t+1)/2 : ℕ) := by
  have hd : ell*(ell-1)/2 ≤ ell*m :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left ell (by omega))
  simp only [sourceFiniteExponent, Nat.cast_sub hd, Nat.cast_mul]
  ring

/-- The fixed label exponent has the paper's equivalent total-row expression. -/
theorem visibleLabelExponent_eq_source (m b : ℕ) :
    (visibleLabelExponent m b : ℤ) =
      ((m+b+1 : ℕ) : ℤ)*m - (m*(m-1)/2 : ℕ) := by
  have htri := Nat.two_dvd_mul_add_one m
  have hpred : 2 ∣ m*(m-1) := by
    cases m with
    | zero => simp
    | succ m => simpa [Nat.mul_comm] using Nat.two_dvd_mul_add_one m
  have h1 := Nat.mod_add_div (m*(m+1)) 2
  have h2 := Nat.mod_add_div (m*(m-1)) 2
  have hp : m*(m-1)+m = m*m := by
    cases m with
    | zero => simp
    | succ m => simp only [Nat.add_sub_cancel]; ring
  rw [Nat.mod_eq_zero_of_dvd htri] at h1
  rw [Nat.mod_eq_zero_of_dvd hpred] at h2
  unfold visibleLabelExponent
  push_cast
  have hsum : m*(m+1)/2 + m*(m-1)/2 = m*m := by nlinarith
  have hsumz : ((m*(m+1)/2 : ℕ) : ℤ) + (m*(m-1)/2 : ℕ) = (m : ℤ)*m := by
    exact_mod_cast hsum
  nlinarith

/-- A natural maximum is used only with an explicit nonempty-grid guard. -/
def completionMaximumExponent (m s r k : ℕ) : ℕ :=
  (completionRankGrid m s r k).sup
    (fun z => completionRankExponent m s r z.1 z.2)

/-- This signed maximum is genuinely attained at a source-admissible pair. -/
theorem sourceFiniteMaximum_attained (m h k a u : ℕ)
    (hua : u ≤ a) (hah : a-u ≤ h)
    (hne : (completionRankGrid m (h-(a-u)) (a-u) k).Nonempty) :
    ∃ ell t, sourceCompletionDomain m h k a u ell t ∧
      sourceFiniteExponent m h a u ell t =
        (completionMaximumExponent m (h-(a-u)) (a-u) k : ℤ) := by
  obtain ⟨⟨ell,t⟩, hz, he⟩ := Finset.exists_mem_eq_sup _ hne
    (fun z => completionRankExponent m (h-(a-u)) (a-u) z.1 z.2)
  have hg := (completionRankGrid_mem m (h-(a-u)) (a-u) k ell t).mp hz
  refine ⟨ell,t,(completionRankGrid_iff_source m h k a u ell t hua hah).mp hz,?_⟩
  rw [sourceFiniteExponent_eq_completionRankExponent m h a u ell t hua hah
    (hg.1.trans (min_le_left _ _)) hg.2.1]
  exact_mod_cast he.symm

theorem sourceFiniteExponent_le_maximum (m h k a u ell t : ℕ)
    (hua : u ≤ a) (hah : a-u ≤ h)
    (hz : sourceCompletionDomain m h k a u ell t) :
    sourceFiniteExponent m h a u ell t ≤
      (completionMaximumExponent m (h-(a-u)) (a-u) k : ℤ) := by
  have hg := (completionRankGrid_iff_source m h k a u ell t hua hah).mpr hz
  rw [sourceFiniteExponent_eq_completionRankExponent m h a u ell t hua hah hz.1 hz.2.2.1]
  exact_mod_cast Finset.le_sup
    (f := fun z => completionRankExponent m (h-(a-u)) (a-u) z.1 z.2) hg

/-- Empty grids contribute zero. In the nonempty case the exponent is a real
maximum, and normalization uses signed integer subtraction. The lift is zero
ordinarily and m in the characteristic-two enhanced branch. -/
def finiteCompletionFactor (F : Type*) [Field F] [Fintype F]
    (m h r k D lift : ℕ) : ℝ :=
  if (completionRankGrid m (h-r) r k).Nonempty then
    min 1 (16 * ((m+1 : ℕ) : ℝ)^2 * (Fintype.card F : ℝ)^
      ((completionMaximumExponent m (h-r) r k : ℤ) + lift - D))
  else 0

theorem finiteCompletionFactor_of_empty [Fintype F] (m h r k D lift : ℕ)
    (he : completionRankGrid m (h-r) r k = ∅) :
    finiteCompletionFactor F m h r k D lift = 0 := by
  simp [finiteCompletionFactor, he]

/-- The exact sum vanishes on an empty grid, including degenerate dimensions. -/
theorem completionCountExpression_of_empty [Fintype F] (m s r k : ℕ)
    (he : completionRankGrid m s r k = ∅) :
    completionCountExpression F m s r k = 0 := by
  simp [completionCountExpression, he]

/-- The clipped normalized exact count is bounded by the fully finite
structural factor with explicit constant 16. No probability or count estimate
is a hypothesis: the rank-count estimates are invoked by the proof. -/
theorem clipped_completionCountExpression_le [Fintype F] (m h r k D lift : ℕ) :
    min 1 ((Fintype.card F : ℝ)^lift *
      (completionCountExpression F m (h-r) r k : ℝ) / (Fintype.card F : ℝ)^D) ≤
        finiteCompletionFactor F m h r k D lift := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  by_cases hne : (completionRankGrid m (h-r) r k).Nonempty
  · rw [finiteCompletionFactor, if_pos hne]
    apply min_le_min_left
    have hb := completion_count_expression_bound F m (h-r) r k
    have hs := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (pow_nonneg (le_of_lt hq) lift))
      (pow_nonneg (le_of_lt hq) D)
    refine hs.trans_eq ?_
    change (Fintype.card F : ℝ)^lift *
      (16 * ((m+1 : ℕ) : ℝ)^2 * (Fintype.card F : ℝ)^
        (completionMaximumExponent m (h-r) r k)) / (Fintype.card F : ℝ)^D = _
    rw [zpow_sub₀ (ne_of_gt hq), zpow_add₀ (ne_of_gt hq)]
    simp only [zpow_natCast]
    ring
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [finiteCompletionFactor, hne, completionCountExpression_of_empty m (h-r) r k he]

/-- The same bound applies to the literal set of rank-constrained completions
via its proved exact cardinality, with no parameterization assumptions. -/
theorem clipped_completionPairs_le [Fintype F] {h : ℕ}
    (B : SymmetricMatrices (Fin h) F) (m k D lift : ℕ) :
    min 1 ((Fintype.card F : ℝ)^lift * (Nat.card (CompletionPairs B m k) : ℝ) /
      (Fintype.card F : ℝ)^D) ≤ finiteCompletionFactor F m h B.val.rank k D lift := by
  rw [card_completionPairs]
  exact clipped_completionCountExpression_le m h B.val.rank k D lift

/-- Ordinary finite structural factor, normalized by the fixed full label alphabet. -/
def ordinaryFiniteStructuralFactor (F : Type*) [Field F] [Fintype F]
    (m b k a u : ℕ) : ℝ :=
  finiteCompletionFactor F m (b+1) (a-u) k (visibleLabelExponent m b) 0

/-- Binary factor includes the actual enhanced-diagonal multiplicity 2^m. -/
def binaryFiniteStructuralFactor (m b k a u : ℕ) : ℝ :=
  finiteCompletionFactor (ZMod 2) m b (a-u) k (visibleLabelExponent m b) m

theorem clipped_ordinary_completion_le (F : Type*) [Field F] [Fintype F]
    (m b k a u : ℕ) :
    min 1 ((completionCountExpression F m (b+1-(a-u)) (a-u) k : ℝ) /
      (Fintype.card F : ℝ)^(visibleLabelExponent m b)) ≤
      ordinaryFiniteStructuralFactor F m b k a u := by
  simpa [ordinaryFiniteStructuralFactor] using
    (clipped_completionCountExpression_le (F := F) m (b+1) (a-u) k
      (visibleLabelExponent m b) 0)

theorem clipped_binary_completion_le (m b k a u : ℕ) :
    min 1 ((2 : ℝ)^m *
      (completionCountExpression (ZMod 2) m (b-(a-u)) (a-u) k : ℝ) /
      (2 : ℝ)^(visibleLabelExponent m b)) ≤
      binaryFiniteStructuralFactor m b k a u := by
  simpa [binaryFiniteStructuralFactor, ZMod.card] using
    (clipped_completionCountExpression_le (F := ZMod 2) m b (a-u) k
      (visibleLabelExponent m b) m)

/-- The support is exactly the image of the actual row-parameter classifier. -/
theorem positiveMassRowParameters_eq_image [Fintype F] (b k : ℕ) :
    positiveMassRowParameters F b k =
      Finset.univ.image (fun Y : Matrix (Fin b) (Fin k) F =>
        rowParameterIndex (rowSpace Y)) := by
  classical
  ext z
  rw [mem_positiveMassRowParameters]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, rowParameterIndex_eq_iff]
  rfl

theorem positiveMassAugmentedRowParameters_eq_image [Fintype F]
    (b k : ℕ) (v : Fin k → F) :
    positiveMassAugmentedRowParameters F b k v =
      Finset.univ.image (fun Y : Matrix (Fin b) (Fin k) F =>
        rowParameterIndex (augmentedRowSpace v Y)) := by
  classical
  ext z
  rw [mem_positiveMassAugmentedRowParameters]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, rowParameterIndex_eq_iff]
  rfl

theorem completionRankGrid_nonempty_iff (m s r k : ℕ) :
    (completionRankGrid m s r k).Nonempty ↔ r ≤ k := by
  constructor
  · rintro ⟨⟨ell,t⟩, hz⟩
    have := (completionRankGrid_mem m s r k ell t).mp hz
    omega
  · intro h
    exact ⟨(0,0), (completionRankGrid_mem m s r k 0 0).mpr (by omega)⟩

/-- The guarded factor is always a nonnegative probability-side cap. -/
theorem finiteCompletionFactor_bounds [Fintype F] (m h r k D lift : ℕ) :
    0 ≤ finiteCompletionFactor F m h r k D lift ∧
      finiteCompletionFactor F m h r k D lift ≤ 1 := by
  unfold finiteCompletionFactor
  split_ifs
  · constructor
    · apply le_min (by norm_num)
      positivity
    · exact min_le_left _ _
  · norm_num

/-- Ordinary support parameters have exactly the source grid and an attained maximum. -/
theorem positiveMassAugmented_sourceMaximum [Fintype F] {b k : ℕ} (m : ℕ)
    (v : Fin k → F) {z : Fin (k+1) × Fin (k+1)}
    (hz : z ∈ positiveMassAugmentedRowParameters F b k v) :
    ∃ ell t, sourceCompletionDomain m (b+1) k z.1.val z.2.val ell t ∧
      sourceFiniteExponent m (b+1) z.1.val z.2.val ell t =
        (completionMaximumExponent m (b+1-(z.1.val-z.2.val))
          (z.1.val-z.2.val) k : ℤ) := by
  have hf := positiveMassAugmentedRowParameters_feasible v hz
  exact sourceFiniteMaximum_attained m (b+1) k z.1.val z.2.val hf.1
    (by omega) ((completionRankGrid_nonempty_iff _ _ _ _).mpr (by omega))

/-- Binary support uses h=b and adds the enhanced-diagonal lift to the genuine maximum. -/
theorem positiveMassRow_sourceBinaryMaximum [Fintype F] {b k : ℕ} (m : ℕ)
    {z : Fin (k+1) × Fin (k+1)} (hz : z ∈ positiveMassRowParameters F b k) :
    ∃ ell t, sourceCompletionDomain m b k z.1.val z.2.val ell t ∧
      sourceBinaryFiniteExponent m b z.1.val z.2.val ell t =
        (completionMaximumExponent m (b-(z.1.val-z.2.val))
          (z.1.val-z.2.val) k : ℤ) + m := by
  have hf := positiveMassRowParameters_feasible hz
  obtain ⟨ell,t,hg,he⟩ := sourceFiniteMaximum_attained m b k z.1.val z.2.val
    hf.1 (by omega) ((completionRankGrid_nonempty_iff _ _ _ _).mpr (by omega))
  refine ⟨ell,t,hg,?_⟩
  rw [sourceBinaryFiniteExponent, he, add_comm]

/-- Literal signed-integer version of the source formula, including both exact
halves. This rules out hidden natural-subtraction clipping in E_fin itself. -/
theorem sourceFiniteExponent_eq_integer_formula (m h a u ell t : ℕ)
    (hell : ell ≤ m) (ht : t ≤ m-ell) :
    sourceFiniteExponent m h a u ell t =
      (m : ℤ)*((a : ℤ)-u) + (ell : ℤ)*((m : ℤ)+h-a+u-ell) +
      (ell : ℤ)*m - (ell : ℤ)*((ell : ℤ)-1)/2 +
      (t : ℤ)*(2*((m : ℤ)-ell)-t+1)/2 := by
  rw [sourceFiniteExponent_eq_signed m h a u ell t hell]
  have hp : ((ell*(ell-1) : ℕ) : ℤ) = (ell : ℤ)*((ell : ℤ)-1) := by
    cases ell with
    | zero => norm_num
    | succ ell => push_cast; ring
  have hts : t ≤ 2*(m-ell) := by omega
  rw [Int.natCast_div, hp, Int.natCast_div]
  push_cast [Nat.cast_sub hell, Nat.cast_sub hts]
  rfl

/-- On actual ordinary positive-mass parameters, the displayed structural
factor has a genuine maximizing source-admissible pair. -/
theorem ordinaryFiniteStructuralFactor_source [Fintype F] {b k : ℕ}
    (m : ℕ) (v : Fin k → F) {z : Fin (k+1) × Fin (k+1)}
    (hz : z ∈ positiveMassAugmentedRowParameters F b k v) :
    ∃ ell t, sourceCompletionDomain m (b+1) k z.1.val z.2.val ell t ∧
      (∀ ell' t', sourceCompletionDomain m (b+1) k z.1.val z.2.val ell' t' →
        sourceFiniteExponent m (b+1) z.1.val z.2.val ell' t' ≤
          sourceFiniteExponent m (b+1) z.1.val z.2.val ell t) ∧
      ordinaryFiniteStructuralFactor F m b k z.1.val z.2.val =
        min 1 (16*((m+1 : ℕ) : ℝ)^2*(Fintype.card F : ℝ)^
          (sourceFiniteExponent m (b+1) z.1.val z.2.val ell t -
            (visibleLabelExponent m b : ℤ))) := by
  have hf := positiveMassAugmentedRowParameters_feasible v hz
  obtain ⟨ell,t,hg,he⟩ := positiveMassAugmented_sourceMaximum m v hz
  refine ⟨ell,t,hg,?_,?_⟩
  · intro ell' t' hh
    rw [he]
    exact sourceFiniteExponent_le_maximum m (b+1) k z.1.val z.2.val ell' t'
      hf.1 (by omega) hh
  · have hne := (completionRankGrid_nonempty_iff m
      (b+1-(z.1.val-z.2.val)) (z.1.val-z.2.val) k).mpr (by omega)
    simp [ordinaryFiniteStructuralFactor, finiteCompletionFactor, hne, he]

/-- The binary maximum includes the enhanced lift before the common fixed
normalization; its completion domain is h=b, not the ordinary h=b+1. -/
theorem binaryFiniteStructuralFactor_source {b k : ℕ} (m : ℕ)
    {z : Fin (k+1) × Fin (k+1)}
    (hz : z ∈ positiveMassRowParameters (ZMod 2) b k) :
    ∃ ell t, sourceCompletionDomain m b k z.1.val z.2.val ell t ∧
      (∀ ell' t', sourceCompletionDomain m b k z.1.val z.2.val ell' t' →
        sourceBinaryFiniteExponent m b z.1.val z.2.val ell' t' ≤
          sourceBinaryFiniteExponent m b z.1.val z.2.val ell t) ∧
      binaryFiniteStructuralFactor m b k z.1.val z.2.val =
        min 1 (16*((m+1 : ℕ) : ℝ)^2*(2 : ℝ)^
          (sourceBinaryFiniteExponent m b z.1.val z.2.val ell t -
            (visibleLabelExponent m b : ℤ))) := by
  have hf := positiveMassRowParameters_feasible hz
  obtain ⟨ell,t,hg,he⟩ := positiveMassRow_sourceBinaryMaximum m hz
  refine ⟨ell,t,hg,?_,?_⟩
  · intro ell' t' hh
    have hu := sourceFiniteExponent_le_maximum m b k z.1.val z.2.val ell' t'
      hf.1 (by omega) hh
    rw [he, sourceBinaryFiniteExponent]
    omega
  · have hne := (completionRankGrid_nonempty_iff m
      (b-(z.1.val-z.2.val)) (z.1.val-z.2.val) k).mpr (by omega)
    simp [binaryFiniteStructuralFactor, finiteCompletionFactor, hne, he, ZMod.card]

end StabilizerLearning
