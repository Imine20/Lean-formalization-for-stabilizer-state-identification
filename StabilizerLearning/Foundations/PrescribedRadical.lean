import StabilizerLearning.Foundations.RowSpaceDefs
import StabilizerLearning.Foundations.UniformRank
import StabilizerLearning.Foundations.IntervalSubspaces
import StabilizerLearning.Foundations.PrescribedRadicalArithmetic
import Mathlib.FieldTheory.Finiteness

noncomputable section
namespace StabilizerLearning

open scoped BigOperators

/-- Actual subspaces of prescribed dimension and prescribed standard-dot radical. -/
abbrev PrescribedRadicalSubspaces (F : Type*) [Field F] (k a u : ℕ) :=
  {W : Submodule F (Fin k → F) //
    Module.finrank F W = a ∧ Module.finrank F (rowRadical W) = u}

/-- Actual totally isotropic subspaces. -/
abbrev TotallyIsotropicSubspaces (F : Type*) [Field F] (k u : ℕ) :=
  {W : Submodule F (Fin k → F) //
    Module.finrank F W = u ∧ W ≤ standardOrthogonal W}

/-- Independent ordered isotropic frames, including the empty frame. -/
abbrev IsotropicFrame (F : Type*) [Field F] (k u : ℕ) :=
  {v : Fin u → (Fin k → F) // LinearIndependent F v ∧
    ∀ i j, dotProduct (v i) (v j) = 0}

instance prescribedRadicalSubspacesFinite (F : Type*) [Field F] [Fintype F]
    (k a u : ℕ) : Finite (PrescribedRadicalSubspaces F k a u) := by
  apply Finite.of_injective (fun W : PrescribedRadicalSubspaces F k a u =>
    (W.val : Set (Fin k → F)))
  intro W V h
  exact Subtype.ext (SetLike.coe_injective h)

instance totallyIsotropicSubspacesFinite (F : Type*) [Field F] [Fintype F]
    (k u : ℕ) : Finite (TotallyIsotropicSubspaces F k u) := by
  apply Finite.of_injective (fun W : TotallyIsotropicSubspaces F k u =>
    (W.val : Set (Fin k → F)))
  intro W V h
  exact Subtype.ext (SetLike.coe_injective h)

variable {F : Type*} [Field F]

/-- Orthogonality to generators is orthogonality to their full span. -/
theorem mem_standardOrthogonal_span {k : ℕ} {ι : Type*}
    (v : ι → Fin k → F) (x : Fin k → F) :
    x ∈ standardOrthogonal (Submodule.span F (Set.range v)) ↔
      ∀ i, dotProduct (v i) x = 0 := by
  rw [mem_standardOrthogonal]
  constructor
  · intro h i
    exact h (v i) (Submodule.subset_span ⟨i, rfl⟩)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem z hz => rcases hz with ⟨i, rfl⟩; exact h i
    | zero => simp
    | add y z _ _ hy hz => simp [add_dotProduct, hy, hz]
    | smul c y _ hy => simp [smul_dotProduct, hy]

/-- Delete the last vector of an independent isotropic frame. -/
def isotropicFrameInit {k u : ℕ} (v : IsotropicFrame F k (u+1)) :
    IsotropicFrame F k u :=
  ⟨v.val ∘ Fin.castSucc, v.property.1.comp _ (Fin.castSucc_injective _),
    fun i j => v.property.2 i.castSucc j.castSucc⟩

/-- Encode an extended frame by its prefix and a vector orthogonal to that prefix. -/
def isotropicFrameStep {k u : ℕ} (v : IsotropicFrame F k (u+1)) :
    (w : IsotropicFrame F k u) ×
      standardOrthogonal (Submodule.span F (Set.range w.val)) :=
  ⟨isotropicFrameInit v, ⟨v.val (Fin.last u),
    (mem_standardOrthogonal_span _ _).mpr (fun i => v.property.2 i.castSucc (Fin.last u))⟩⟩

theorem isotropicFrameStep_injective {k u : ℕ} :
    Function.Injective (isotropicFrameStep (F := F) (k := k) (u := u)) := by
  intro v w h
  have hi : isotropicFrameInit v = isotropicFrameInit w := congrArg Sigma.fst h
  have hl : v.val (Fin.last u) = w.val (Fin.last u) := by
    have ht := congrArg (fun z => (z.2 : Fin k → F)) h
    exact ht
  apply Subtype.ext
  funext i
  refine Fin.lastCases hl (fun j => ?_) i
  exact congrFun (congrArg Subtype.val hi) j

/-- Successively choosing a frame uses at most q^(k-u) extensions at step u. -/
theorem card_isotropicFrame_succ_le [Fintype F] (k u : ℕ) :
    Nat.card (IsotropicFrame F k (u+1)) ≤
      Nat.card (IsotropicFrame F k u) * Fintype.card F ^ (k-u) := by
  classical
  letI := Fintype.ofFinite (IsotropicFrame F k u)
  have hh := Nat.card_le_card_of_injective
    (isotropicFrameStep (F := F) (k := k) (u := u)) isotropicFrameStep_injective
  rw [Nat.card_sigma] at hh
  have hc (v : IsotropicFrame F k u) :
      Nat.card (standardOrthogonal (Submodule.span F (Set.range v.val))) =
        Fintype.card F ^ (k-u) := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_standardOrthogonal,
      finrank_span_eq_card v.property.1, Fintype.card_fin, Nat.card_eq_fintype_card]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card] at hh ⊢
  exact hh

/-- Full ordered-frame bound, proved by actual extension fibers. -/
theorem card_isotropicFrame_le [Fintype F] (k u : ℕ) :
    Nat.card (IsotropicFrame F k u) ≤
      Fintype.card F ^ (∑ j ∈ Finset.range u, (k-j)) := by
  induction u with
  | zero =>
    have h := Nat.card_le_card_of_injective
      (Subtype.val : IsotropicFrame F k 0 → (Fin 0 → Fin k → F)) Subtype.val_injective
    simpa using h
  | succ u ih =>
    calc
      _ ≤ Nat.card (IsotropicFrame F k u) * Fintype.card F ^ (k-u) :=
        card_isotropicFrame_succ_le k u
      _ ≤ (Fintype.card F ^ (∑ j ∈ Finset.range u, (k-j))) *
          Fintype.card F ^ (k-u) := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [Finset.sum_range_succ, pow_add]

/-- Encode each isotropic subspace together with every one of its bases as an
actual ambient isotropic frame. -/
def isotropicSubspaceFrameEncoding (F : Type*) [Field F] (k u : ℕ) :
    TotallyIsotropicSubspaces F k u ×
      {v : Fin u → (Fin u → F) // LinearIndependent F v} → IsotropicFrame F k u := by
  intro z
  let W : RankSubspaces F k u := ⟨z.1.val, z.1.property.1⟩
  let e := rankSubspaceCoordinates F k u W
  refine ⟨fun i => (e (z.2.val i) : Fin k → F), ?_, ?_⟩
  · have hv := z.2.property.map' e.toLinearMap e.ker
    exact hv.map' W.val.subtype (Submodule.ker_subtype _)
  · intro i j
    exact z.1.property.2 (e (z.2.val j)).property _ (e (z.2.val i)).property

theorem isotropicSubspaceFrameEncoding_injective (F : Type*) [Field F] (k u : ℕ) :
    Function.Injective (isotropicSubspaceFrameEncoding F k u) := by
  intro a b h
  rcases a with ⟨W, v⟩
  rcases b with ⟨U, w⟩
  have hh : ((⟨W.val, W.property.1⟩ : RankSubspaces F k u), v) =
      ((⟨U.val, U.property.1⟩ : RankSubspaces F k u), w) :=
    subspaceFamilyEncoding_injective F k u (congrArg Subtype.val h)
  have hWU : W = U := Subtype.ext (congrArg (fun z => z.1.val) hh)
  have hvw : v = w := congrArg Prod.snd hh
  exact Prod.ext hWU hvw

/-- Dividing frame counts by the genuine number of bases is justified by injection. -/
theorem card_isotropic_mul_GL_le [Fintype F] (k u : ℕ) :
    Nat.card (TotallyIsotropicSubspaces F k u) *
      Nat.card (Matrix.GeneralLinearGroup (Fin u) F) ≤
        Fintype.card F ^ (∑ j ∈ Finset.range u, (k-j)) := by
  have hh := (Nat.card_le_card_of_injective (isotropicSubspaceFrameEncoding F k u)
    (isotropicSubspaceFrameEncoding_injective F k u)).trans (card_isotropicFrame_le k u)
  rw [Nat.card_prod] at hh
  rwa [Nat.card_congr (Matrix.equiv_GL_linearindependent (𝔽 := F) u)]

/-- Every subspace lies in the orthogonal complement of its own radical. -/
theorem le_standardOrthogonal_rowRadical {k : ℕ} (W : Submodule F (Fin k → F)) :
    W ≤ standardOrthogonal (rowRadical W) := by
  intro x hx y hy
  change dotProduct y x = 0
  rw [dotProduct_comm]
  exact hy.2 x hx

/-- The actual radical is itself totally isotropic. -/
theorem rowRadical_totallyIsotropic {k : ℕ} (W : Submodule F (Fin k → F)) :
    rowRadical W ≤ standardOrthogonal (rowRadical W) :=
  inf_le_left.trans (le_standardOrthogonal_rowRadical W)

/-- Geometric feasibility is proved for each counted subspace. -/
theorem prescribedRadical_feasible {k a u : ℕ}
    (W : PrescribedRadicalSubspaces F k a u) :
    u ≤ a ∧ a + u ≤ k := by
  have hu : Module.finrank F (rowRadical W.val) ≤ Module.finrank F W.val :=
    Submodule.finrank_mono inf_le_left
  have ha := Submodule.finrank_mono (le_standardOrthogonal_rowRadical W.val)
  rw [finrank_standardOrthogonal, W.property.1, W.property.2] at ha
  rw [W.property.1, W.property.2] at hu
  have huk : u ≤ k := by
    have h := (rowRadical W.val).finrank_le
    simpa only [Module.finrank_pi, Fintype.card_fin, W.property.2] using h
  exact ⟨hu, by omega⟩

/-- The frame exponent is retained as an integer identity, so no negative
prescribed-radical exponent is truncated. -/
theorem isotropicFrame_exponent_identity (k u : ℕ) (huk : u ≤ k) :
    (∑ j ∈ Finset.range u, (k-j)) + u * (u+1) / 2 = u*k+u := by
  have hs : (∑ j ∈ Finset.range u, (k-j)) + (∑ j ∈ Finset.range u, j) = u*k := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _j ∈ Finset.range u, k := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        omega
      _ = _ := by simp
  have ht : u * (u+1) / 2 = (∑ j ∈ Finset.range u, j) + u := by
    have h := Finset.sum_range_succ (fun j : ℕ => j) u
    rw [Finset.sum_range_id] at h
    simpa only [Nat.add_sub_cancel, Nat.mul_comm] using h
  omega

instance intervalCoordinateFinite [Fintype F] {k : ℕ}
    (R S : Submodule F (Fin k → F)) (a : ℕ) : Finite (IntervalSubspaces R S a) := by
  apply Finite.of_injective (fun W : IntervalSubspaces R S a => (W.val : Set (Fin k → F)))
  intro W U h
  exact Subtype.ext (SetLike.coe_injective h)

/-- A prescribed-radical subspace determines its actual isotropic radical and
an actual interval subspace between that radical and its orthogonal complement. -/
def prescribedRadicalEncoding (k a u : ℕ) :
    PrescribedRadicalSubspaces F k a u →
      (R : TotallyIsotropicSubspaces F k u) ×
        IntervalSubspaces R.val (standardOrthogonal R.val) a := fun W =>
  ⟨⟨rowRadical W.val, W.property.2, rowRadical_totallyIsotropic W.val⟩,
    ⟨W.val, inf_le_left, le_standardOrthogonal_rowRadical W.val, W.property.1⟩⟩

theorem prescribedRadicalEncoding_injective (k a u : ℕ) :
    Function.Injective (prescribedRadicalEncoding (F := F) k a u) := by
  intro W U h
  exact Subtype.ext (congrArg (fun z => z.2.val) h)

/-- Count by the genuine radical, with the quotient interval bound proved in
`IntervalSubspaces`. Nondegeneracy of the residual quotient is not assumed. -/
theorem card_prescribedRadical_le_isotropic [Fintype F] (k a u : ℕ)
    (hua : u ≤ a) (hauk : a+u ≤ k) :
    (Nat.card (PrescribedRadicalSubspaces F k a u) : ℝ) ≤
      (Nat.card (TotallyIsotropicSubspaces F k u) : ℝ) *
        (4 * (Fintype.card F : ℝ)^((a-u)*(k-u-a))) := by
  classical
  letI := Fintype.ofFinite (TotallyIsotropicSubspaces F k u)
  have hc := Nat.card_le_card_of_injective (prescribedRadicalEncoding (F := F) k a u)
    (prescribedRadicalEncoding_injective k a u)
  rw [Nat.card_sigma] at hc
  have hcr : (Nat.card (PrescribedRadicalSubspaces F k a u) : ℝ) ≤
      ∑ R : TotallyIsotropicSubspaces F k u,
        (Nat.card (IntervalSubspaces R.val (standardOrthogonal R.val) a) : ℝ) := by
    exact_mod_cast hc
  calc
    _ ≤ ∑ R : TotallyIsotropicSubspaces F k u,
        (Nat.card (IntervalSubspaces R.val (standardOrthogonal R.val) a) : ℝ) := hcr
    _ ≤ ∑ _R : TotallyIsotropicSubspaces F k u,
        4 * (Fintype.card F : ℝ)^((a-u)*(k-u-a)) := by
      apply Finset.sum_le_sum
      intro R _
      have hu : Module.finrank F R.val = u := R.property.1
      have hs : Module.finrank F (standardOrthogonal R.val) = k-u := by
        rw [finrank_standardOrthogonal, hu]
      simpa only [hu, hs] using card_intervalSubspaces_le
        R.val (standardOrthogonal R.val) R.property.2 a (by omega) (by omega)
    _ = _ := by simp [Nat.card_eq_fintype_card]

/-- Clear the GL denominator with the proved finite-product GL lower bound. -/
theorem card_isotropic_mul_pow_le [Fintype F] (k u : ℕ) :
    (Nat.card (TotallyIsotropicSubspaces F k u) : ℝ) *
      (Fintype.card F : ℝ)^(u*u) ≤
        4 * (Fintype.card F : ℝ)^(∑ j ∈ Finset.range u, (k-j)) := by
  have hi : (Nat.card (TotallyIsotropicSubspaces F k u) : ℝ) *
      (Nat.card (Matrix.GeneralLinearGroup (Fin u) F) : ℝ) ≤
        (Fintype.card F : ℝ)^(∑ j ∈ Finset.range u, (k-j)) := by
    exact_mod_cast (card_isotropic_mul_GL_le (F := F) k u)
  have hh := mul_le_mul_of_nonneg_left (card_GL_lower F u)
    (Nat.cast_nonneg (Nat.card (TotallyIsotropicSubspaces F k u)) :
      (0 : ℝ) ≤ Nat.card (TotallyIsotropicSubspaces F k u))
  nlinarith

/-- The genuine prescribed-radical count with its GL denominator cleared. -/
theorem card_prescribedRadical_mul_pow_le [Fintype F] (k a u : ℕ)
    (hua : u ≤ a) (hauk : a+u ≤ k) :
    (Nat.card (PrescribedRadicalSubspaces F k a u) : ℝ) *
      (Fintype.card F : ℝ)^(u*u) ≤
        16 * (Fintype.card F : ℝ)^((∑ j ∈ Finset.range u, (k-j)) + (a-u)*(k-u-a)) := by
  let q : ℝ := Fintype.card F
  have hq : 0 ≤ q := Nat.cast_nonneg _
  calc
    _ ≤ ((Nat.card (TotallyIsotropicSubspaces F k u) : ℝ) *
        (4*q^((a-u)*(k-u-a)))) * q^(u*u) :=
      mul_le_mul_of_nonneg_right (card_prescribedRadical_le_isotropic k a u hua hauk)
        (pow_nonneg hq _)
    _ = (4*q^((a-u)*(k-u-a))) *
        ((Nat.card (TotallyIsotropicSubspaces F k u) : ℝ) * q^(u*u)) := by ring
    _ ≤ (4*q^((a-u)*(k-u-a))) *
        (4*q^(∑ j ∈ Finset.range u, (k-j))) :=
      mul_le_mul_of_nonneg_left (card_isotropic_mul_pow_le k u) (by positivity)
    _ = _ := by dsimp only [q]; rw [pow_add]; ring

/-- Exact natural-number balance underlying the signed exponent. -/
theorem prescribedRadical_exponent_balance (k a u : ℕ)
    (hua : u ≤ a) (hauk : a+u ≤ k) :
    (∑ j ∈ Finset.range u, (k-j)) + (a-u)*(k-u-a) + u*(u+1)/2 =
      a*(k-a) + u*u + u := by
  have hsum := isotropicFrame_exponent_identity k u (by omega)
  have h1 := Nat.sub_add_cancel hua
  have h2 : k-u-a+a+u = k := by omega
  have h3 : k-a+a = k := by omega
  nlinarith

/-- The source exponent is signed: subtraction is in ℤ, never truncated in ℕ. -/
def prescribedRadicalExponent (k a u : ℕ) : ℤ :=
  (a : ℤ) * ((k : ℤ) - a) - (u*(u+1)/2 : ℕ)

theorem prescribedRadical_exponent_identity (k a u : ℕ)
    (hua : u ≤ a) (hauk : a+u ≤ k) :
    (((∑ j ∈ Finset.range u, (k-j)) + (a-u)*(k-u-a) : ℕ) : ℤ) =
      ((u*u : ℕ) : ℤ) + prescribedRadicalExponent k a u + u := by
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (prescribedRadical_exponent_balance k a u hua hauk)
  have hak : a ≤ k := by omega
  simp only [Nat.cast_add, Nat.cast_mul] at h ⊢
  rw [Int.ofNat_sub hak] at h
  unfold prescribedRadicalExponent
  omega

/-- The original infeasible parameter convention follows from actual emptiness. -/
theorem card_prescribedRadical_eq_zero_of_infeasible [Fintype F] (k a u : ℕ)
    (h : ¬(u ≤ a ∧ 2*u ≤ k ∧ a-u ≤ k-2*u)) :
    Nat.card (PrescribedRadicalSubspaces F k a u) = 0 := by
  letI : IsEmpty (PrescribedRadicalSubspaces F k a u) := ⟨fun W => by
    have hw := prescribedRadical_feasible W
    apply h
    omega⟩
  exact Nat.card_of_isEmpty

/-- At zero ambient dimension the actual family has at most one member. -/
theorem card_prescribedRadical_zero_ambient (F : Type*) [Field F] (a u : ℕ) :
    Nat.card (PrescribedRadicalSubspaces F 0 a u) ≤ 1 := by
  have h := Nat.card_le_card_of_injective
    (Subtype.val : PrescribedRadicalSubspaces F 0 a u → Submodule F (Fin 0 → F))
    Subtype.val_injective
  simpa only [Nat.card_of_subsingleton (⊥ : Submodule F (Fin 0 → F))] using h

/-- All-characteristic prescribed-radical bound for the actual subspaces.
The only inputs are the finite field and dimensions. Negative exponents are
integer powers; impossible dimensions contribute the cardinality of an empty set. -/
theorem prescribed_radical_subspace_bound (F : Type*) [Field F] [Fintype F]
    (k a u : ℕ) :
    (Nat.card (PrescribedRadicalSubspaces F k a u) : ℝ) ≤
      (16 * (Fintype.card F : ℝ))^k *
        (Fintype.card F : ℝ)^((a : ℤ)*((k : ℤ)-a)-(u*(u+1)/2 : ℕ)) := by
  classical
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  by_cases hne : Nonempty (PrescribedRadicalSubspaces F k a u)
  · obtain ⟨W⟩ := hne
    obtain ⟨hua, hauk⟩ := prescribedRadical_feasible W
    by_cases hk : k = 0
    · subst k
      have ha : a = 0 := by omega
      have hu : u = 0 := by omega
      subst a
      subst u
      have hc : (Nat.card (PrescribedRadicalSubspaces F 0 0 0) : ℝ) ≤ 1 := by
        exact_mod_cast card_prescribedRadical_zero_ambient F 0 0
      simpa using hc
    · simpa only [prescribedRadicalExponent] using absorb_radical_prefactor
        (Fintype.card F : ℝ) (Nat.card (PrescribedRadicalSubspaces F k a u) : ℝ)
        k u ((∑ j ∈ Finset.range u, (k-j)) + (a-u)*(k-u-a)) (u*u)
        (prescribedRadicalExponent k a u) hq (Nat.pos_of_ne_zero hk) (by omega)
        (prescribedRadical_exponent_identity k a u hua hauk)
        (card_prescribedRadical_mul_pow_le k a u hua hauk)
  · letI : IsEmpty (PrescribedRadicalSubspaces F k a u) := not_nonempty_iff.mp hne
    simp only [Nat.card_of_isEmpty, Nat.cast_zero]
    have hq0 : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le zero_lt_one hq
    positivity

/-- Requiring an arbitrary prescribed vector only selects a subfamily. -/
theorem prescribed_radical_containing_bound (F : Type*) [Field F] [Fintype F]
    (k a u : ℕ) (v : Fin k → F) :
    (Nat.card {W : PrescribedRadicalSubspaces F k a u // v ∈ W.val} : ℝ) ≤
      (16 * (Fintype.card F : ℝ))^k *
        (Fintype.card F : ℝ)^((a : ℤ)*((k : ℤ)-a)-(u*(u+1)/2 : ℕ)) := by
  have hc := Nat.card_le_card_of_injective
    (Subtype.val : {W : PrescribedRadicalSubspaces F k a u // v ∈ W.val} →
      PrescribedRadicalSubspaces F k a u) Subtype.val_injective
  exact (show (Nat.card {W : PrescribedRadicalSubspaces F k a u // v ∈ W.val} : ℝ) ≤
      Nat.card (PrescribedRadicalSubspaces F k a u) by exact_mod_cast hc).trans
    (prescribed_radical_subspace_bound F k a u)

/-- The source existential constant can be witnessed explicitly by 16q. -/
theorem exists_prescribed_radical_constant (F : Type*) [Field F] [Fintype F] :
    ∃ K : ℝ, 1 < K ∧ ∀ k a u : ℕ,
      (Nat.card (PrescribedRadicalSubspaces F k a u) : ℝ) ≤
        K^k * (Fintype.card F : ℝ)^((a : ℤ)*((k : ℤ)-a)-(u*(u+1)/2 : ℕ)) := by
  refine ⟨16 * Fintype.card F, ?_, prescribed_radical_subspace_bound F⟩
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  linarith

end StabilizerLearning
