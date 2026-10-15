import StabilizerLearning.FixedConstraints.OperationalPrior
import StabilizerLearning.FiniteCopy.POVMCoarsening

/-! Complete-state identification admits a deterministic reduction to the
original fixed-constraint task on every physical input, including exceptional
inputs. All reports and all collective POVMs retain the original definitions. -/
noncomputable section
open scoped BigOperators
open Classical
attribute [local instance] Classical.propDecidable
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- The surviving stabilizer space on an arbitrary input has m dimensions in
addition to the stabilizers already present in the constraint. -/
theorem finrank_fullTargetSlice (W : Constraint p n m) (L : Lagrangian p n) :
    Module.finrank (ZMod p) ↥(L.val ⊓ symplecticBilinForm.orthogonal W.subspace) =
      m + Module.finrank (ZMod p) ↥(L.val ⊓ W.subspace) := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq L.val W.subspace
  rw [L.property.2, W.dimension] at hs
  have horth : symplecticBilinForm.orthogonal (L.val ⊔ W.subspace) =
      L.val ⊓ symplecticBilinForm.orthogonal W.subspace := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, fun w hw => hx w (Submodule.mem_sup_right hw)⟩
      rw [← lagrangian_orthogonal_eq L]
      exact fun l hl => hx l (Submodule.mem_sup_left hl)
    · rintro ⟨hxL,hxW⟩ z hz
      obtain ⟨l,hl,w,hw,rfl⟩ := Submodule.mem_sup.mp hz
      have hx : x ∈ symplecticBilinForm.orthogonal L.val :=
        (lagrangian_orthogonal_eq L).symm ▸ hxL
      change symplecticBilinForm (l+w) x = 0
      rw [map_add, LinearMap.add_apply, hx l hl, hxW w hw, add_zero]
  have hd := symplecticBilinForm.finrank_orthogonal
    symplecticBilinForm_nondegenerate symplecticBilinForm_isAlt.isRefl (L.val ⊔ W.subspace)
  have hphase : Module.finrank (ZMod p) (PhaseSpace p n) = 2*n := by
    simp [PhaseSpace, Configuration, Module.finrank_prod]; omega
  rw [horth,hphase] at hd
  have hle := Submodule.finrank_le (L.val ⊔ W.subspace)
  rw [hphase] at hle
  have hm := W.dimension_allowed
  omega

/-- Every input Lagrangian, without a genericity assumption, contains a legal
report complement to its intersection with the constraint. -/
theorem exists_fullReportSubspace (W : Constraint p n m) (L : Lagrangian p n) :
    ∃ K : ReportSubspace W, K.val ≤ L.val ∧
      (L.val ⊓ W.subspace) ⊔ K.val =
        L.val ⊓ symplecticBilinForm.orthogonal W.subspace := by
  let A := L.val ⊓ symplecticBilinForm.orthogonal W.subspace
  let J := L.val ⊓ W.subspace
  have hJA : J ≤ A := by
    intro z hz
    exact ⟨hz.1, fun w hw => W.isotropic w hw z hz.2⟩
  obtain ⟨C,hC⟩ := J.exists_isCompl
  let K := A ⊓ C
  have hsup : J ⊔ K = A := by
    apply le_antisymm (sup_le hJA inf_le_left)
    intro z hz
    have hzTop : z ∈ J ⊔ C := by rw [hC.codisjoint.eq_top]; trivial
    obtain ⟨j,hj,c,hc,hjc⟩ := Submodule.mem_sup.mp hzTop
    apply Submodule.mem_sup.mpr
    refine ⟨j,hj,c,⟨?_,hc⟩,hjc⟩
    have hsub := A.sub_mem hz (hJA hj)
    have he : z-j=c := by rw [← hjc]; abel
    simpa only [he] using hsub
  have hinf : J ⊓ K = ⊥ := by
    apply le_antisymm _ bot_le
    exact (inf_le_inf_left J (inf_le_right : K ≤ C)).trans_eq hC.disjoint.eq_bot
  have hdim : Module.finrank (ZMod p) K = m := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq J K
    rw [hsup,hinf,finrank_bot,add_zero] at h
    have hA := finrank_fullTargetSlice W L
    change Module.finrank (ZMod p) A = m + Module.finrank (ZMod p) J at hA
    omega
  have hKL : K ≤ L.val := inf_le_left.trans inf_le_left
  have hKW : K ⊓ W.subspace = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    have hjk : z ∈ J ⊓ K := ⟨⟨hKL hz.1,hz.2⟩,hz.1⟩
    simpa only [hinf,Submodule.mem_bot] using hjk
  refine ⟨⟨K,?_,hdim,?_,hKW⟩,hKL,hsup⟩
  · intro z hz w hw
    exact L.property.1 z (hKL hz) w (hKL hw)
  · intro z hz
    exact (mem_symplecticBilinForm_orthogonal_iff W.subspace z).mp hz.1.2

/-- A deterministic subspace choice made before seeing any verifier outcome. -/
def fullReportSubspace (W : Constraint p n m) (L : Lagrangian p n) : ReportSubspace W :=
  Classical.choose (exists_fullReportSubspace W L)

theorem fullReportSubspace_le (W : Constraint p n m) (L : Lagrangian p n) :
    (fullReportSubspace W L).val ≤ L.val :=
  (Classical.choose_spec (exists_fullReportSubspace W L)).1

theorem fullReportSubspace_sup (W : Constraint p n m) (L : Lagrangian p n) :
    (L.val ⊓ W.subspace) ⊔ (fullReportSubspace W L).val =
      L.val ⊓ symplecticBilinForm.orthogonal W.subspace :=
  (Classical.choose_spec (exists_fullReportSubspace W L)).2

/-- Restrict the original physical phase assignment to the chosen legal space. -/
def fullLabelReport (W : Constraint p n m) (ℓ : StabilizerLabel p n) : Report W :=
  ⟨fullReportSubspace W ℓ.1, restrictAssignment p (fullReportSubspace_le W ℓ.1) ℓ.2⟩

/-- A total decoder on the actual distinct density-matrix alphabet. -/
def fullStateReport (W : Constraint p n m) (x : StabilizerState p n) : Report W :=
  fullLabelReport W ((stabilizerLabelStateEquiv p n).symm x)

theorem valid_fullStateReport (W : Constraint p n m) (x : StabilizerState p n) :
    Valid W x (fullStateReport W x) := by
  let ℓ := (stabilizerLabelStateEquiv p n).symm x
  have hℓ : labelProjector p n ℓ = x.val :=
    congrArg Subtype.val ((stabilizerLabelStateEquiv p n).apply_symm_apply x)
  rw [valid_iff_label_restriction W x (fullStateReport W x) ℓ hℓ]
  exact ⟨fullReportSubspace_le W ℓ.1,rfl⟩

theorem verificationPayoff_fullStateReport (W : Constraint p n m) (x : StabilizerState p n) :
    verificationPayoff W x (fullStateReport W x) = 1 :=
  verificationPayoff_eq_one_of_valid W x _ (valid_fullStateReport W x)

/-- Complete identification uses every distinct original physical state as a
measurement outcome, on the same full k-copy space as the fixed-W learner. -/
abbrev FullIdentificationMeasurement (p n k : ℕ) [Fact p.Prime] :=
  POVM (Fin k → Configuration p n) (StabilizerState p n)

/-- Deterministic postprocessing of an arbitrary normalized complete-state
measurement. No property of its success probabilities is assumed. -/
def fixedWPostprocess (W : Constraint p n m) (k : ℕ)
    (M : FullIdentificationMeasurement p n k) : Learner W k :=
  POVM.pushforward (fullStateReport W) M

theorem fullIdentification_born_le_exactStatewise (W : Constraint p n m) (k : ℕ)
    (M : FullIdentificationMeasurement p n k) (x : StabilizerState p n) :
    born (M.effect x) (tensorPower x.val k) ≤
      exactStatewise W k (fixedWPostprocess W k M) x := by
  have hρ := tensorPower_posSemidef x.val x.property.1 k
  have hp : born (M.effect x) (tensorPower x.val k) ≤
      born ((fixedWPostprocess W k M).effect (fullStateReport W x)) (tensorPower x.val k) := by
    rw [fixedWPostprocess, POVM.born_pushforward]
    have hsingle := Finset.single_le_sum (s := Finset.univ)
      (f := fun y : StabilizerState p n => if fullStateReport W y = fullStateReport W x then
        born (M.effect y) (tensorPower x.val k) else 0)
      (fun y _ => by
        dsimp only
        split_ifs
        · exact born_nonneg_of_posSemidef _ _ (M.positive y) hρ
        · exact le_rfl)
      (Finset.mem_univ x)
    convert hsingle using 1
    · simp
    · apply Finset.sum_congr rfl
      intro y hy
      by_cases h : fullStateReport W y = fullStateReport W x <;> simp [h]
  refine hp.trans ?_
  have hsingle := Finset.single_le_sum (s := Finset.univ)
    (f := fun r : Report W => if Valid W x r then
      born ((fixedWPostprocess W k M).effect r) (tensorPower x.val k) else 0)
    (fun r _ => by
      dsimp only
      split_ifs
      · exact learner_born_nonneg W k _ x r
      · exact le_rfl)
    (Finset.mem_univ (fullStateReport W x))
  simpa only [if_pos (valid_fullStateReport W x)] using hsingle

theorem fullIdentification_born_le_verificationStatewise (W : Constraint p n m) (k : ℕ)
    (M : FullIdentificationMeasurement p n k) (x : StabilizerState p n) :
    born (M.effect x) (tensorPower x.val k) ≤
      verificationStatewise W k (fixedWPostprocess W k M) x :=
  (fullIdentification_born_le_exactStatewise W k M x).trans
    (exactStatewise_le_verificationStatewise W k _ x)

/-- The original two aggregations applied to complete-state identification. -/
def fullIdentificationPerformance (a : Aggregation) (k : ℕ)
    (M : FullIdentificationMeasurement p n k) : ℝ :=
  match a with
  | .worstCase => sInf (Set.range (fun x : StabilizerState p n =>
      born (M.effect x) (tensorPower x.val k)))
  | .average => uniformFiniteMean (fun x : StabilizerState p n =>
      born (M.effect x) (tensorPower x.val k))

def fullIdentificationOptimal (p n k : ℕ) [Fact p.Prime] (a : Aggregation) : ℝ :=
  sSup (Set.range (fullIdentificationPerformance (p := p) (n := n) a k))

theorem fullIdentificationPerformance_le_exactPerformance (W : Constraint p n m)
    (k : ℕ) (M : FullIdentificationMeasurement p n k) (a : Aggregation) :
    fullIdentificationPerformance a k M ≤
      performance .exact a W k (fixedWPostprocess W k M) := by
  letI : Nonempty (StabilizerState p n) := stabilizerState_nonempty
  cases a with
  | worstCase =>
    have hb : BddBelow (Set.range (fun x : StabilizerState p n =>
        born (M.effect x) (tensorPower x.val k))) := by
      refine ⟨0,?_⟩
      rintro _ ⟨x,rfl⟩
      exact born_nonneg_of_posSemidef _ _ (M.positive x)
        (tensorPower_posSemidef x.val x.property.1 k)
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨x,rfl⟩
    exact (csInf_le hb ⟨x,rfl⟩).trans
      (fullIdentification_born_le_exactStatewise W k M x)
  | average =>
    change (∑ x, born (M.effect x) (tensorPower x.val k)) / Nat.card (StabilizerState p n) ≤ _
    simp only [performance,statewise,Nat.card_eq_fintype_card]
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun x _ => fullIdentification_born_le_exactStatewise W k M x)
      (Nat.cast_nonneg _)

theorem fullIdentificationPerformance_le_verificationPerformance (W : Constraint p n m)
    (k : ℕ) (M : FullIdentificationMeasurement p n k) (a : Aggregation) :
    fullIdentificationPerformance a k M ≤
      performance .verification a W k (fixedWPostprocess W k M) :=
  (fullIdentificationPerformance_le_exactPerformance W k M a).trans
    (exactPerformance_le_verificationPerformance a W k _)

theorem fullIdentificationPerformance_le_optimal_exact (W : Constraint p n m)
    (k : ℕ) (M : FullIdentificationMeasurement p n k) (a : Aggregation) :
    fullIdentificationPerformance a k M ≤ optimal .exact a W k := by
  have hb : BddAbove (Set.range (performance .exact a W k)) := by
    refine ⟨1,?_⟩
    rintro _ ⟨N,rfl⟩
    exact (performance_mem_Icc .exact a W k N).2
  exact (fullIdentificationPerformance_le_exactPerformance W k M a).trans
    (le_csSup hb ⟨fixedWPostprocess W k M,rfl⟩)

theorem fullIdentificationOptimal_le_optimal_exact (W : Constraint p n m)
    (k : ℕ) (a : Aggregation) :
    fullIdentificationOptimal p n k a ≤ optimal .exact a W k := by
  letI : Nonempty (StabilizerState p n) := stabilizerState_nonempty
  letI : Nonempty (FullIdentificationMeasurement p n k) :=
    ⟨POVM.deterministic (Classical.choice (inferInstance : Nonempty (StabilizerState p n)))⟩
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨M,rfl⟩
  exact fullIdentificationPerformance_le_optimal_exact W k M a

theorem fullIdentificationOptimal_le_optimal_verification (W : Constraint p n m)
    (k : ℕ) (a : Aggregation) :
    fullIdentificationOptimal p n k a ≤ optimal .verification a W k :=
  (fullIdentificationOptimal_le_optimal_exact W k a).trans
    (optimal_exact_le_verification a W k)

/-- A proved per-state lower bound for any actual complete-identification
measurement immediately gives a worst-case lower bound in the original task.
This wrapper is intended for the actual decoder construction, not as a premise
of a final direct theorem. -/
theorem le_optimal_exact_worstCase_of_fullIdentification (W : Constraint p n m)
    (k : ℕ) (M : FullIdentificationMeasurement p n k) (c : ℝ)
    (h : ∀ x : StabilizerState p n, c ≤ born (M.effect x) (tensorPower x.val k)) :
    c ≤ optimal .exact .worstCase W k := by
  letI : Nonempty (StabilizerState p n) := stabilizerState_nonempty
  have hc : c ≤ fullIdentificationPerformance .worstCase k M := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨x,rfl⟩
    exact h x
  exact hc.trans (fullIdentificationPerformance_le_optimal_exact W k M .worstCase)

theorem le_all_optimal_of_fullIdentification (W : Constraint p n m)
    (k : ℕ) (M : FullIdentificationMeasurement p n k) (c : ℝ)
    (h : ∀ x : StabilizerState p n, c ≤ born (M.effect x) (tensorPower x.val k)) :
    c ≤ optimal .exact .worstCase W k ∧
    c ≤ optimal .exact .average W k ∧
    c ≤ optimal .verification .worstCase W k ∧
    c ≤ optimal .verification .average W k := by
  have hw := le_optimal_exact_worstCase_of_fullIdentification W k M c h
  have ha := hw.trans (optimal_worstCase_le_average .exact W k)
  exact ⟨hw,ha,hw.trans (optimal_exact_le_verification .worstCase W k),
    ha.trans (optimal_exact_le_verification .average W k)⟩

end StabilizerLearning.FixedConstraints
