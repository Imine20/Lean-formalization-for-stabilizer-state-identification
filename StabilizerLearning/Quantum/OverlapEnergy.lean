import StabilizerLearning.Quantum.AssignmentExtension
import StabilizerLearning.Quantum.ProjectorOverlap
import StabilizerLearning.Quantum.StabilizerEquivalence
import StabilizerLearning.Quantum.TensorProbability

/-! Actual overlap row energy of the complete ensemble of distinct stabilizer
states. The assignment contribution is counted exactly on each intersection. -/
noncomputable section
open scoped BigOperators ComplexOrder
open Classical
namespace StabilizerLearning.Quantum
variable (p n : ℕ) [Fact p.Prime]

local instance : Fintype (Lagrangian p n) := Fintype.ofFinite _

/-- Intersection codimension in a genuine full stabilizer Lagrangian. -/
def lagrangianDistance (L M : Lagrangian p n) : ℕ :=
  n - Module.finrank (ZMod p) ↥(M.val ⊓ L.val)

theorem lagrangianDistance_le (L M : Lagrangian p n) : lagrangianDistance p n L M ≤ n :=
  Nat.sub_le _ _

@[simp] theorem lagrangianDistance_self (L : Lagrangian p n) :
    lagrangianDistance p n L L = 0 := by
  unfold lagrangianDistance
  rw [inf_idem, L.property.2, Nat.sub_self]

@[simp] theorem lagrangianDistance_eq_zero_iff (L M : Lagrangian p n) :
    lagrangianDistance p n L M = 0 ↔ M = L := by
  have hdim : Module.finrank (ZMod p) ↥(M.val ⊓ L.val) ≤ n := by
    simpa only [M.property.2] using (Submodule.finrank_mono
      (inf_le_left : M.val ⊓ L.val ≤ M.val))
  constructor
  · intro h
    have hd : Module.finrank (ZMod p) ↥(M.val ⊓ L.val) = n := by
      unfold lagrangianDistance at h
      omega
    have he : M.val ⊓ L.val = M.val :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (hd.trans M.property.2.symm)
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_eq (inf_eq_left.mp he)
      (M.property.2.trans L.property.2.symm)
  · rintro rfl
    exact lagrangianDistance_self p n M

/-- Literal cardinality of a Lagrangian intersection shell. -/
def lagrangianShellCount (L : Lagrangian p n) (r : ℕ) : ℕ :=
  Nat.card {M : Lagrangian p n // lagrangianDistance p n L M = r}

@[simp] theorem lagrangianShellCount_zero (L : Lagrangian p n) :
    lagrangianShellCount p n L 0 = 1 := by
  simp [lagrangianShellCount]

/-- The genuine row energy, with the identical physical state excluded. -/
def stabilizerOverlapEnergy (k : ℕ) (x : StabilizerState p n) : ℝ :=
  ∑ y : StabilizerState p n, if y = x then 0 else
    born (tensorPower y.val k) (tensorPower x.val k)

theorem stabilizerOverlapEnergy_nonneg (k : ℕ) (x : StabilizerState p n) :
    0 ≤ stabilizerOverlapEnergy p n k x := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact le_rfl
  · exact born_nonneg_of_posSemidef _ _
      (tensorPower_posSemidef _ y.property.1 k) (tensorPower_posSemidef _ x.property.1 k)

/-- Tensoring the actual positive density matrices raises their Born overlap to k. -/
theorem born_tensorPower (A B : Matrix (Configuration p n) (Configuration p n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (k : ℕ) :
    born (tensorPower A k) (tensorPower B k) = (born A B)^k := by
  have ht := trace_mul_eq_ofReal_born_of_posSemidef A B hA hB
  unfold born
  rw [← tensorPower_mul, trace_tensorPower, ht]
  rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re]

@[simp] theorem born_stabilizer_self (x : StabilizerState p n) : born x.val x.val = 1 := by
  obtain ⟨ℓ,hℓ⟩ := x.property.2.2.2
  rw [← hℓ]
  change born (jointProjector p n ℓ.1.val ℓ.2) (jointProjector p n ℓ.1.val ℓ.2) = 1
  unfold born
  rw [jointProjector_mul_self]
  change (labelProjector p n ℓ).trace.re = 1
  rw [labelProjector_trace]
  rfl

theorem stabilizerOverlapEnergy_add_one (k : ℕ) (x : StabilizerState p n) :
    stabilizerOverlapEnergy p n k x + 1 =
      ∑ y : StabilizerState p n, (born y.val x.val)^k := by
  unfold stabilizerOverlapEnergy
  have hpow (y : StabilizerState p n) :=
    born_tensorPower p n y.val x.val y.property.1 x.property.1 k
  simp_rw [hpow]
  have heq (y : StabilizerState p n) :
      (if y = x then 0 else (born y.val x.val)^k) +
        (if y = x then (1:ℝ) else 0) = (born y.val x.val)^k := by
    by_cases h : y = x
    · subst y; simp
    · simp [h]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun y _ => heq y)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hsum

/-- The spectrum uses the full finite section-compatible assignment. -/
theorem born_labelProjector_eq (L M : Lagrangian p n)
    (η : Assignment p n L.val) (θ : Assignment p n M.val) :
    born (labelProjector p n ⟨M,θ⟩) (labelProjector p n ⟨L,η⟩) =
      if restrictAssignment p (inf_le_left : M.val ⊓ L.val ≤ M.val) θ =
          restrictAssignment p (inf_le_right : M.val ⊓ L.val ≤ L.val) η then
        ((p : ℝ) ^ lagrangianDistance p n L M)⁻¹ else 0 := by
  unfold labelProjector
  rw [born_jointProjector_overlap]
  split_ifs
  · have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hd : Module.finrank (ZMod p) ↥(M.val ⊓ L.val) ≤ n := by
      simpa only [M.property.2] using (Submodule.finrank_mono
        (inf_le_left : M.val ⊓ L.val ≤ M.val))
    rw [M.property.2, lagrangianDistance]
    rw [← one_div, div_eq_div_iff (pow_ne_zero _ hp) (pow_ne_zero _ hp)]
    rw [← pow_add, Nat.add_sub_of_le hd, one_mul]
  · rfl

private theorem sum_indicator_constant {A : Type*} [Fintype A]
    (C : A → Prop) [DecidablePred C] (c : ℝ) :
    (∑ a : A, if C a then c else 0) = (Fintype.card {a : A // C a} : ℝ) * c := by
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]

/-- Exact contribution of all phases over one fixed Lagrangian. The positive
copy condition excludes the spurious 0^0 overlap of orthogonal inputs. -/
theorem sum_assignment_overlap_pow (L M : Lagrangian p n)
    (η : Assignment p n L.val) (k : ℕ) (hk : 0 < k) :
    (∑ θ : Assignment p n M.val,
      (born (labelProjector p n ⟨M,θ⟩) (labelProjector p n ⟨L,η⟩))^k) =
      ((p : ℝ)⁻¹) ^ (lagrangianDistance p n L M * (k-1)) := by
  simp_rw [born_labelProjector_eq, ite_pow, zero_pow (Nat.ne_of_gt hk)]
  let C (θ : Assignment p n M.val) :=
    restrictAssignment p (inf_le_left : M.val ⊓ L.val ≤ M.val) θ =
      restrictAssignment p (inf_le_right : M.val ⊓ L.val ≤ L.val) η
  have hs := sum_indicator_constant C ((((p : ℝ)^lagrangianDistance p n L M)⁻¹)^k)
  change (∑ θ : Assignment p n M.val, if C θ then _ else 0) = _
  trans (Fintype.card {θ : Assignment p n M.val // C θ} : ℝ) *
    (((p : ℝ)^lagrangianDistance p n L M)⁻¹)^k
  · refine Eq.trans ?_ hs
    apply Finset.sum_congr rfl
    intro θ _
    by_cases h : C θ
    · simp only [if_pos h]
    · simp only [if_neg h]
  rw [card_compatibleAssignments p n M.property.1 η, M.property.2]
  change (p ^ lagrangianDistance p n L M : ℕ) *
    (((p : ℝ) ^ lagrangianDistance p n L M)⁻¹)^k = _
  rw [Nat.cast_pow]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
  rw [pow_succ, mul_comm ((((p:ℝ) ^ lagrangianDistance p n L M)⁻¹)^t),
    ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp), one_mul, ← inv_pow, ← pow_mul]

/-- The whole physical ensemble sum is the exact sum over all actual labels. -/
theorem stabilizerOverlapEnergy_add_one_eq_lagrangian_sum
    (ℓ : StabilizerLabel p n) (k : ℕ) (hk : 0 < k) :
    stabilizerOverlapEnergy p n k (stabilizerLabelStateEquiv p n ℓ) + 1 =
      ∑ M : Lagrangian p n,
        ((p : ℝ)⁻¹) ^ (lagrangianDistance p n ℓ.1 M * (k-1)) := by
  rw [stabilizerOverlapEnergy_add_one,
    ← (stabilizerLabelStateEquiv p n).sum_comp]
  change (∑ y : StabilizerLabel p n,
    (born (labelProjector p n y) (labelProjector p n ℓ))^k) = _
  rw [show stabilizerLabelFintype p n = Sigma.instFintype from Subsingleton.elim _ _]
  have hs := @Fintype.sum_sigma (Lagrangian p n) (fun L => Assignment p n L.val) ℝ _ _ _
    (fun y => (born (labelProjector p n y) (labelProjector p n ℓ))^k)
  trans ∑ M : Lagrangian p n, ∑ θ : Assignment p n M.val,
    (born (labelProjector p n ⟨M,θ⟩) (labelProjector p n ℓ))^k
  · exact hs
  apply Finset.sum_congr rfl
  intro M _
  exact sum_assignment_overlap_pow p n ℓ.1 M ℓ.2 k hk

end StabilizerLearning.Quantum
