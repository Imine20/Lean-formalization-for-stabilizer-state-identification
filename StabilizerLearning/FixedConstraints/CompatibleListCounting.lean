import StabilizerLearning.FixedConstraints.CompatibleList
import StabilizerLearning.Foundations.IntervalSubspaces
import StabilizerLearning.Quantum.AssignmentExtension

/-! Uniform finite neighborhood bounds from actual subspace covers. The first
cover overcounts all assignments; the strengthened cover uses the exact proved
assignment-restriction fiber and retains phase compatibility. Both use the full
phase space and do not assert the paper's sharper Gaussian shell formula.
Every covering map and cardinal bound is proved below. -/
noncomputable section
open Classical
open scoped BigOperators
namespace StabilizerLearning

/-- Every finite-dimensional subspace contains an actual subspace of any
smaller prescribed dimension. -/
theorem exists_le_finrank_eq {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [Module.Finite F V] (S : Submodule F V) (a : ℕ)
    (ha : a ≤ Module.finrank F S) :
    ∃ I : Submodule F V, I ≤ S ∧ Module.finrank F I = a := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank ha
  let I := (Submodule.span F (Set.range v)).map S.subtype
  refine ⟨I, ?_, ?_⟩
  · exact Submodule.map_le_iff_le_comap.mpr (by simp)
  · dsimp [I]
    rw [Submodule.finrank_map_subtype_eq]
    simpa using finrank_span_eq_card hv

namespace FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- Even without isotropy, the set of assignments has at most the character
count: if it is nonempty, an actual assignment supplies the torsor base point. -/
theorem card_assignment_le (K : Submodule (ZMod p) (PhaseSpace p n)) :
    Fintype.card (Assignment p n K) ≤ p ^ Module.finrank (ZMod p) K := by
  by_cases h : Nonempty (Assignment p n K)
  · exact le_of_eq (card_assignment_of_base p n K (Classical.choice h))
  · letI : IsEmpty (Assignment p n K) := not_nonempty_iff.mp h
    simp

/-- The ambient pair used for the covering count. -/
abbrev ReportCover (W : Constraint p n m) (a : ℕ) (r : Report W) :=
  (I : IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) r.1.val a) ×
    (K : IntervalSubspaces I.val (⊤ : Submodule (ZMod p) (PhaseSpace p n)) m) ×
      Assignment p n K.val

/-- An actual small-distance report has a common (m-D)-subspace with the center. -/
theorem exists_common_report_subspace (W : Constraint p n m) (D : ℕ)
    (r y : Report W) (hy : reportDistance W y r ≤ D) :
    ∃ I : Submodule (ZMod p) (PhaseSpace p n),
      I ≤ y.1.val ⊓ r.1.val ∧ Module.finrank (ZMod p) I = m - D := by
  apply exists_le_finrank_eq
  dsimp [reportDistance] at hy
  omega

def reportCoverEncode (W : Constraint p n m) (D : ℕ) (r : Report W) :
    {y : Report W // reportDistance W y r ≤ D} → ReportCover W (m-D) r := fun y =>
  let I := Classical.choose (exists_common_report_subspace W D r y.val y.property)
  let hI := Classical.choose_spec (exists_common_report_subspace W D r y.val y.property)
  ⟨⟨I, bot_le, hI.1.trans inf_le_right, hI.2⟩,
    ⟨y.val.1.val, hI.1.trans inf_le_left, le_top, y.val.1.property.2.1⟩, y.val.2⟩

theorem reportCoverEncode_injective (W : Constraint p n m) (D : ℕ) (r : Report W) :
    Function.Injective (reportCoverEncode W D r) := by
  intro y z h
  have hK : y.val.1.val = z.val.1.val := congrArg (fun v => v.2.1.val) h
  have hb : (⟨y.val.1.val, y.val.2⟩ :
      (K : Submodule (ZMod p) (PhaseSpace p n)) × Assignment p n K) =
      ⟨z.val.1.val, z.val.2⟩ :=
    congrArg (fun v : ReportCover W (m-D) r =>
      (⟨v.2.1.val, v.2.2⟩ :
        (K : Submodule (ZMod p) (PhaseSpace p n)) × Assignment p n K)) h
  have hη : HEq y.val.2 z.val.2 := (Sigma.mk.inj_iff.mp hb).2
  apply Subtype.ext
  exact Sigma.ext (Subtype.ext hK) hη

/-- The covering family is counted from two genuine interval Grassmannians and
the whole assignment family. -/
theorem card_reportCover_le (W : Constraint p n m) (a : ℕ) (r : Report W)
    (ha : a ≤ m) :
    (Nat.card (ReportCover W a r) : ℝ) ≤
      16 * (p : ℝ) ^ (a * (m-a) + (m-a) * (2*n-m) + m) := by
  let B := IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) r.1.val a
  let C (I : B) := IntervalSubspaces I.val
    (⊤ : Submodule (ZMod p) (PhaseSpace p n)) m
  letI : Fintype B := Fintype.ofFinite B
  letI (I : B) : Fintype (C I) := Fintype.ofFinite (C I)
  have hphase : Module.finrank (ZMod p) (PhaseSpace p n) = 2*n := by
    simp [PhaseSpace, Configuration, Module.finrank_prod]; omega
  have hmn : m ≤ 2*n := le_trans W.dimension_allowed (by omega)
  have hB : (Nat.card B : ℝ) ≤ 4 * (p : ℝ) ^ (a * (m-a)) := by
    simpa only [B, finrank_bot, r.1.property.2.1, Nat.sub_zero, ZMod.card]
      using card_intervalSubspaces_le
        (⊥ : Submodule (ZMod p) (PhaseSpace p n)) r.1.val bot_le a
        (by simp) (by simpa only [r.1.property.2.1] using ha)
  have hC (I : B) : (Nat.card (C I) : ℝ) ≤
      4 * (p : ℝ) ^ ((m-a)*(2*n-m)) := by
    simpa only [C, I.property.2.2, finrank_top, hphase, ZMod.card]
      using card_intervalSubspaces_le I.val
        (⊤ : Submodule (ZMod p) (PhaseSpace p n)) le_top m
        (by simpa only [I.property.2.2] using ha)
        (by simpa only [finrank_top, hphase] using hmn)
  have hK (I : B) :
      (Nat.card ((K : C I) × Assignment p n K.val) : ℝ) ≤
        (4 * (p : ℝ) ^ ((m-a)*(2*n-m))) * (p : ℝ)^m := by
    rw [Nat.card_sigma, Nat.cast_sum]
    calc
      ∑ K : C I, (Nat.card (Assignment p n K.val) : ℝ) ≤
          ∑ _K : C I, (p : ℝ)^m := by
        apply Finset.sum_le_sum
        intro K _
        have hh := card_assignment_le K.val
        rw [K.property.2.2] at hh
        simpa only [Nat.card_eq_fintype_card, Nat.cast_pow] using (Nat.cast_le.mpr hh :
          (Fintype.card (Assignment p n K.val) : ℝ) ≤ (p^m : ℕ))
      _ = (Nat.card (C I) : ℝ) * (p : ℝ)^m := by
        simp [Nat.card_eq_fintype_card]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hC I) (by positivity)
  change (Nat.card ((I : B) × (K : C I) × Assignment p n K.val) : ℝ) ≤ _
  rw [Nat.card_sigma, Nat.cast_sum]
  calc
    ∑ I : B, (Nat.card ((K : C I) × Assignment p n K.val) : ℝ) ≤
        ∑ _I : B, (4 * (p : ℝ) ^ ((m-a)*(2*n-m))) * (p : ℝ)^m :=
      Finset.sum_le_sum (fun I _ => hK I)
    _ = (Nat.card B : ℝ) *
        ((4 * (p : ℝ) ^ ((m-a)*(2*n-m))) * (p : ℝ)^m) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ (4 * (p : ℝ) ^ (a*(m-a))) *
        ((4 * (p : ℝ) ^ ((m-a)*(2*n-m))) * (p : ℝ)^m) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    _ = _ := by simp only [pow_add]; ring

/-- A uniform finite bound for the real, phase-compatible, generically realizable
list. Dropping compatibility only enlarges the constructed finite cover. -/
theorem card_genericCompatibleList_le_allAssignments (W : Constraint p n m)
    (D : ℕ) (r : Report W) (hD : D ≤ m) :
    ((genericCompatibleList W D r).card : ℝ) ≤
      16 * (p : ℝ) ^ (2*n*D + m) := by
  let encode : ↥(genericCompatibleList W D r) →
      {y : Report W // reportDistance W y r ≤ D} :=
    fun y => ⟨y.val, (mem_genericCompatibleList W D r y.val).mp y.property |>.2.1⟩
  have hinj : Function.Injective encode := by
    intro y z h
    exact Subtype.ext (congrArg (fun y => y.val) h)
  have hcard := Nat.card_le_card_of_injective
    ((reportCoverEncode W D r) ∘ encode)
    ((reportCoverEncode_injective W D r).comp hinj)
  have hcardR : ((genericCompatibleList W D r).card : ℝ) ≤
      (Nat.card (ReportCover W (m-D) r) : ℝ) := by
    have hh : (genericCompatibleList W D r).card ≤ Nat.card (ReportCover W (m-D) r) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
    exact_mod_cast hh
  have hq : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  calc
    _ ≤ (Nat.card (ReportCover W (m-D) r) : ℝ) := hcardR
    _ ≤ 16 * (p : ℝ)^((m-D)*(m-(m-D))+(m-(m-D))*(2*n-m)+m) :=
      card_reportCover_le W (m-D) r (Nat.sub_le _ _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_right₀ hq
      have hm := W.dimension_allowed
      have hsub : m-(m-D)=D := by omega
      rw [hsub]
      have hmn : m ≤ 2*n := by omega
      nlinarith [Nat.sub_add_cancel hD, Nat.sub_add_cancel hmn]

/-- The maximum is bounded uniformly in the center and in the original fixed W. -/
theorem genericCompatibleListSize_le_allAssignments (W : Constraint p n m)
    (D : ℕ) (hD : D ≤ m) :
    (genericCompatibleListSize W D : ℝ) ≤
      16 * (p : ℝ) ^ (2*n*D + m) := by
  have hb (r : Report W) :=
    card_genericCompatibleList_le_allAssignments W D r hD
  unfold genericCompatibleListSize
  induction (Finset.univ : Finset (Report W)) using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih =>
    rw [Finset.sup_insert, Nat.cast_max]
    exact max_le (hb r) ih

/-- Compatibility on the intersection implies compatibility on every common
subspace; these are restrictions of the original finite Pauli assignments. -/
theorem ReportsCompatible.restrict_common (W : Constraint p n m) (y r : Report W)
    (h : ReportsCompatible W y r)
    (I : Submodule (ZMod p) (PhaseSpace p n)) (hI : I ≤ y.1.val ⊓ r.1.val) :
    restrictAssignment p (hI.trans inf_le_left) y.2 =
      restrictAssignment p (hI.trans inf_le_right) r.2 := by
  apply Subtype.ext
  funext z
  exact congrArg (fun η : Assignment p n (y.1.val ⊓ r.1.val) =>
    η.val ⟨z.val, hI z.property⟩) h

/-- The cover now retains the actual assignment restriction on its chosen
common subspace, rather than all assignments on the report subspace. -/
abbrev PhaseReportCover (W : Constraint p n m) (a : ℕ) (r : Report W) :=
  (I : IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) r.1.val a) ×
    (K : {K : ReportSubspace W // I.val ≤ K.val}) ×
      {η : Assignment p n K.val.val //
        restrictAssignment p K.property η =
          restrictAssignment p I.property.2.1 r.2}

def phaseReportCoverEncode (W : Constraint p n m) (D : ℕ) (r : Report W) :
    ↥(genericCompatibleList W D r) → PhaseReportCover W (m-D) r := fun y =>
  let hy := (mem_genericCompatibleList W D r y.val).mp y.property
  let I := Classical.choose (exists_common_report_subspace W D r y.val hy.2.1)
  let hI := Classical.choose_spec (exists_common_report_subspace W D r y.val hy.2.1)
  ⟨⟨I, bot_le, hI.1.trans inf_le_right, hI.2⟩,
    ⟨y.val.1, hI.1.trans inf_le_left⟩,
      ⟨y.val.2, hy.2.2.restrict_common W y.val r I hI.1⟩⟩

theorem phaseReportCoverEncode_injective (W : Constraint p n m) (D : ℕ)
    (r : Report W) : Function.Injective (phaseReportCoverEncode W D r) := by
  intro y z h
  have hb : y.val = z.val :=
    congrArg (fun v : PhaseReportCover W (m-D) r =>
      (⟨v.2.1.val, v.2.2.val⟩ : Report W)) h
  exact Subtype.ext hb

/-- The genuine phase-compatible cover uses the proved exact extension fiber,
which contributes p^(m-a), including a=m and m=0. -/
theorem card_phaseReportCover_le (W : Constraint p n m) (a : ℕ) (r : Report W)
    (ha : a ≤ m) :
    (Nat.card (PhaseReportCover W a r) : ℝ) ≤
      16 * (p : ℝ) ^ (a*(m-a) + (m-a)*(2*n-m) + (m-a)) := by
  let B := IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) r.1.val a
  let C (I : B) := {K : ReportSubspace W // I.val ≤ K.val}
  let T (I : B) (K : C I) := {η : Assignment p n K.val.val //
    restrictAssignment p K.property η =
      restrictAssignment p I.property.2.1 r.2}
  letI : Fintype B := Fintype.ofFinite B
  letI (I : B) : Fintype (C I) := Fintype.ofFinite (C I)
  have hphase : Module.finrank (ZMod p) (PhaseSpace p n) = 2*n := by
    simp [PhaseSpace, Configuration, Module.finrank_prod]; omega
  have hmn : m ≤ 2*n := le_trans W.dimension_allowed (by omega)
  have hB : (Nat.card B : ℝ) ≤ 4 * (p : ℝ) ^ (a*(m-a)) := by
    simpa only [B, finrank_bot, r.1.property.2.1, Nat.sub_zero, ZMod.card]
      using card_intervalSubspaces_le
        (⊥ : Submodule (ZMod p) (PhaseSpace p n)) r.1.val bot_le a
        (by simp) (by simpa only [r.1.property.2.1] using ha)
  have hC (I : B) : (Nat.card (C I) : ℝ) ≤
      4 * (p : ℝ) ^ ((m-a)*(2*n-m)) := by
    let f : C I → IntervalSubspaces I.val
        (⊤ : Submodule (ZMod p) (PhaseSpace p n)) m :=
      fun K => ⟨K.val.val, K.property, le_top, K.val.property.2.1⟩
    have hf : Function.Injective f := by
      intro K L h
      have hv : K.val.val = L.val.val := congrArg
        (fun z : IntervalSubspaces I.val
          (⊤ : Submodule (ZMod p) (PhaseSpace p n)) m => z.val) h
      exact Subtype.ext (Subtype.ext hv)
    have hnat := Nat.card_le_card_of_injective f hf
    have hh : (Nat.card (C I) : ℝ) ≤
        Nat.card (IntervalSubspaces I.val
          (⊤ : Submodule (ZMod p) (PhaseSpace p n)) m) := by exact_mod_cast hnat
    refine hh.trans ?_
    simpa only [I.property.2.2, finrank_top, hphase, ZMod.card]
      using card_intervalSubspaces_le I.val
        (⊤ : Submodule (ZMod p) (PhaseSpace p n)) le_top m
        (by simpa only [I.property.2.2] using ha)
        (by simpa only [finrank_top, hphase] using hmn)
  have hT (I : B) (K : C I) : Nat.card (T I K) = p^(m-a) := by
    simpa only [T, K.val.property.2.1, I.property.2.2] using
      natCard_assignmentRestrictionFiber p n K.property K.val.property.1
        (restrictAssignment p I.property.2.1 r.2)
  have hK (I : B) :
      (Nat.card ((K : C I) × T I K) : ℝ) ≤
        (4 * (p : ℝ) ^ ((m-a)*(2*n-m))) * (p : ℝ)^(m-a) := by
    rw [Nat.card_sigma]
    simp_rw [hT]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow]
    exact mul_le_mul_of_nonneg_right (by simpa only [Nat.card_eq_fintype_card] using hC I)
      (by positivity)
  change (Nat.card ((I : B) × (K : C I) × T I K) : ℝ) ≤ _
  rw [Nat.card_sigma, Nat.cast_sum]
  calc
    ∑ I : B, (Nat.card ((K : C I) × T I K) : ℝ) ≤
        ∑ _I : B, (4 * (p : ℝ) ^ ((m-a)*(2*n-m))) * (p : ℝ)^(m-a) :=
      Finset.sum_le_sum (fun I _ => hK I)
    _ = (Nat.card B : ℝ) *
        ((4 * (p : ℝ) ^ ((m-a)*(2*n-m))) * (p : ℝ)^(m-a)) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ (4 * (p : ℝ) ^ (a*(m-a))) *
        ((4 * (p : ℝ) ^ ((m-a)*(2*n-m))) * (p : ℝ)^(m-a)) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    _ = _ := by simp only [pow_add]; ring

theorem card_genericCompatibleList_le_phase (W : Constraint p n m)
    (D : ℕ) (r : Report W) (hD : D ≤ m) :
    ((genericCompatibleList W D r).card : ℝ) ≤
      16 * (p : ℝ) ^ (2*n*D + D) := by
  have hh := Nat.card_le_card_of_injective (phaseReportCoverEncode W D r)
    (phaseReportCoverEncode_injective W D r)
  have hcard : (genericCompatibleList W D r).card ≤ Nat.card (PhaseReportCover W (m-D) r) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hh
  have hcardR : ((genericCompatibleList W D r).card : ℝ) ≤
      Nat.card (PhaseReportCover W (m-D) r) := by exact_mod_cast hcard
  have hq : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  calc
    _ ≤ (Nat.card (PhaseReportCover W (m-D) r) : ℝ) := hcardR
    _ ≤ 16 * (p : ℝ)^((m-D)*(m-(m-D))+(m-(m-D))*(2*n-m)+(m-(m-D))) :=
      card_phaseReportCover_le W (m-D) r (Nat.sub_le _ _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_right₀ hq
      have hm := W.dimension_allowed
      have hsub : m-(m-D)=D := by omega
      rw [hsub]
      have hmn : m ≤ 2*n := by omega
      nlinarith [Nat.sub_add_cancel hD, Nat.sub_add_cancel hmn]

/-- A uniform maximum bound whose phase factor follows from exact assignment
extension fibers, not an assumed compatibility count. -/
theorem genericCompatibleListSize_le_phase (W : Constraint p n m)
    (D : ℕ) (hD : D ≤ m) :
    (genericCompatibleListSize W D : ℝ) ≤
      16 * (p : ℝ) ^ (2*n*D + D) := by
  have hb (r : Report W) := card_genericCompatibleList_le_phase W D r hD
  unfold genericCompatibleListSize
  induction (Finset.univ : Finset (Report W)) using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih =>
    rw [Finset.sup_insert, Nat.cast_max]
    exact max_le (hb r) ih

/-- The original coarse interface now follows from the phase-compatible bound. -/
theorem card_genericCompatibleList_le_coarse (W : Constraint p n m)
    (D : ℕ) (r : Report W) (hD : D ≤ m) :
    ((genericCompatibleList W D r).card : ℝ) ≤
      16 * (p : ℝ) ^ (2*n*D + m) := by
  refine (card_genericCompatibleList_le_phase W D r hD).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply pow_le_pow_right₀ _ (Nat.add_le_add_left hD _)
  exact_mod_cast (Fact.out : p.Prime).one_lt.le

theorem genericCompatibleListSize_le_coarse (W : Constraint p n m)
    (D : ℕ) (hD : D ≤ m) :
    (genericCompatibleListSize W D : ℝ) ≤
      16 * (p : ℝ) ^ (2*n*D + m) := by
  refine (genericCompatibleListSize_le_phase W D hD).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply pow_le_pow_right₀ _ (Nat.add_le_add_left hD _)
  exact_mod_cast (Fact.out : p.Prime).one_lt.le

end FixedConstraints
end StabilizerLearning
