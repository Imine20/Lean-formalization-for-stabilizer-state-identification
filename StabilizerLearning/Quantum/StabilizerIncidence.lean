import StabilizerLearning.Quantum.CliffordStates
import StabilizerLearning.Quantum.SymplecticTransitivity

/-! Direction incidence in the original uniform ensemble of distinct stabilizer
states, derived by actual symplectic transport and finite double counting. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace StabilizerLearning.Quantum
variable (p n : ℕ) [Fact p.Prime]

/-- The uniquely recovered Lagrangian of an original stabilizer density matrix. -/
def stabilizerLagrangian (ρ : StabilizerState p n) : Lagrangian p n :=
  ((stabilizerLabelStateEquiv p n).symm ρ).1

@[simp] theorem stabilizerLagrangian_symplecticStabilizerStateEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (ρ : StabilizerState p n) :
    stabilizerLagrangian p n (symplecticStabilizerStateEquiv p n g hg ρ) =
      symplecticMapLagrangian g hg (stabilizerLagrangian p n ρ) := by
  simp [stabilizerLagrangian, symplecticStabilizerStateEquiv,
    cliffordStabilizerStateEquiv_recoveredLabel]

/-- A concrete graph state proves the original ensemble is nonempty, including n=0. -/
theorem nonempty_stabilizerState : Nonempty (StabilizerState p n) := by
  let L : Lagrangian p n := graphLagrangian 0 (by simp [Matrix.IsSymm])
  obtain ⟨η⟩ := nonempty_assignment_of_isIsotropic p n L.val L.property.1
  exact ⟨stabilizerLabelStateEquiv p n ⟨L, η⟩⟩

abbrev NonzeroPhase := {z : PhaseSpace p n // z ≠ 0}
noncomputable instance nonzeroPhaseFintype : Fintype (NonzeroPhase p n) := Fintype.ofFinite _

/-- The actual uniform probability that the recovered Lagrangian contains a direction. -/
def directionIncidence (v : PhaseSpace p n) : ℝ := by
  classical
  exact uniformFiniteMean (fun ρ : StabilizerState p n =>
    if v ∈ (stabilizerLagrangian p n ρ).val then 1 else 0)

/-- Uniform direction incidence follows from a proved bijection of actual states. -/
theorem directionIncidence_eq (v w : PhaseSpace p n) (hv : v ≠ 0) (hw : w ≠ 0) :
    directionIncidence p n v = directionIncidence p n w := by
  classical
  obtain ⟨g, hg, hgv⟩ := exists_symplectic_map_nonzero v w hv hw
  subst w
  have h := uniformFiniteMean_comp_equiv (symplecticStabilizerStateEquiv p n g hg)
    (fun ρ : StabilizerState p n =>
      if g v ∈ (stabilizerLagrangian p n ρ).val then (1 : ℝ) else 0)
  have hmem (ρ : StabilizerState p n) :
      g v ∈ (stabilizerLagrangian p n ρ).val.map g.toLinearMap ↔
        v ∈ (stabilizerLagrangian p n ρ).val := by
    constructor
    · rintro ⟨x, hx, hxv⟩
      have he : x = v := g.injective hxv
      simpa only [he] using hx
    · intro hv
      exact ⟨v, hv, rfl⟩
  simpa only [directionIncidence, stabilizerLagrangian_symplecticStabilizerStateEquiv,
    symplecticMapLagrangian_val, hmem] using h

/-- Counting nonzero ambient vectors inside a submodule is the same as counting
nonzero vectors of the submodule itself. -/
def nonzeroPhaseMemEquiv (U : Submodule (ZMod p) (PhaseSpace p n)) :
    {v : NonzeroPhase p n // v.val ∈ U} ≃ {z : U // z ≠ 0} where
  toFun v := ⟨⟨v.val.val, v.property⟩, fun h => v.val.property (congrArg Subtype.val h)⟩
  invFun z := ⟨⟨z.val.val, fun h => z.property (Subtype.ext h)⟩, z.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_nonzeroPhase : Fintype.card (NonzeroPhase p n) = (p ^ n)^2 - 1 := by
  classical
  simp [NonzeroPhase, Fintype.card_subtype_compl, PhaseSpace, Configuration,
    pow_two]

/-- Exact count of nonzero directions in every actual linear subspace. -/
theorem sum_nonzeroPhase_mem (U : Submodule (ZMod p) (PhaseSpace p n)) :
    (∑ v : NonzeroPhase p n, if v.val ∈ U then (1 : ℝ) else 0) =
      (p : ℝ) ^ Module.finrank (ZMod p) U - 1 := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  rw [Finset.sum_boole, ← Fintype.card_subtype, Fintype.card_congr (nonzeroPhaseMemEquiv p n U),
    Fintype.card_subtype_compl]
  have hcard : Fintype.card U = p ^ Module.finrank (ZMod p) U := by
    simpa only [Nat.card_eq_fintype_card] using card_submodule_eq_prime_pow p n U
  have hp : 1 ≤ p ^ Module.finrank (ZMod p) U := one_le_pow₀ (Fact.out : p.Prime).one_lt.le
  simp [hcard, Nat.cast_sub hp]

/-- Double-count all nonzero directions in the original state ensemble. -/
theorem sum_directionIncidence :
    (∑ v : NonzeroPhase p n, directionIncidence p n v.val) = (p : ℝ)^n - 1 := by
  classical
  letI : Nonempty (StabilizerState p n) := nonempty_stabilizerState p n
  have hcard : (Nat.card (StabilizerState p n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card (StabilizerState p n) ≠ 0)
  unfold directionIncidence uniformFiniteMean
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [sum_nonzeroPhase_mem, (stabilizerLagrangian p n _).property.2]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  field_simp

/-- The exact incidence of one nonzero direction, derived without a counting premise. -/
theorem directionIncidence_nonzero (v : PhaseSpace p n) (hv : v ≠ 0) :
    directionIncidence p n v = 1 / ((p : ℝ)^n + 1) := by
  classical
  have hsum := sum_directionIncidence p n
  have heq (w : NonzeroPhase p n) : directionIncidence p n w.val =
      directionIncidence p n v := directionIncidence_eq p n w.val v w.property hv
  simp_rw [heq] at hsum
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_nonzeroPhase] at hsum
  have hn : n ≠ 0 := by
    intro hn
    subst n
    apply hv
    ext i <;> exact Fin.elim0 i
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpn : 1 < (p : ℝ)^n := one_lt_pow₀ hp hn
  have hnat : 1 ≤ (p^n)^2 := one_le_pow₀ (one_le_pow₀ (Fact.out : p.Prime).one_lt.le)
  rw [Nat.cast_sub hnat, Nat.cast_pow, Nat.cast_pow, Nat.cast_one] at hsum
  apply (eq_div_iff (by positivity : (p : ℝ)^n + 1 ≠ 0)).mpr
  have hc : ((p : ℝ)^n - 1) *
      (directionIncidence p n v * ((p : ℝ)^n + 1) - 1) = 0 := by nlinarith [hsum]
  have he := (mul_eq_zero.mp hc).resolve_left (by linarith)
  linarith


/-- Expected nonzero intersection size with any actual subspace, from the
original full uniform prior. No isotropy or positive-dimension assumption is needed. -/
theorem expected_nonzero_intersection
    (U : Submodule (ZMod p) (PhaseSpace p n)) :
    uniformFiniteMean (fun ρ : StabilizerState p n =>
      ∑ v : NonzeroPhase p n,
        if v.val ∈ (stabilizerLagrangian p n ρ).val ⊓ U then (1 : ℝ) else 0) =
      ((p : ℝ)^Module.finrank (ZMod p) U - 1) / ((p : ℝ)^n + 1) := by
  classical
  unfold uniformFiniteMean
  rw [Finset.sum_comm, Finset.sum_div]
  have hterm (v : NonzeroPhase p n) :
      (∑ ρ : StabilizerState p n,
        if v.val ∈ (stabilizerLagrangian p n ρ).val ⊓ U then (1 : ℝ) else 0) /
          (Nat.card (StabilizerState p n) : ℝ) =
      if v.val ∈ U then directionIncidence p n v.val else 0 := by
    by_cases hv : v.val ∈ U
    · simp [Submodule.mem_inf, hv, directionIncidence, uniformFiniteMean]
    · simp [Submodule.mem_inf, hv]
  have hinc (v : NonzeroPhase p n) :
      directionIncidence p n v.val = 1 / ((p : ℝ)^n + 1) :=
    directionIncidence_nonzero p n v.val v.property
  simp_rw [hterm, hinc]
  calc
    (∑ v : NonzeroPhase p n, if v.val ∈ U then 1 / ((p : ℝ)^n + 1) else 0) =
        (∑ v : NonzeroPhase p n, if v.val ∈ U then (1 : ℝ) else 0) /
          ((p : ℝ)^n + 1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp
    _ = _ := by rw [sum_nonzeroPhase_mem]

/-- A nonzero linear intersection contains at least p−1 nonzero vectors.
Averaging this elementary inequality gives the sharp first-moment bound. -/
theorem nontrivial_intersection_probability_le
    (U : Submodule (ZMod p) (PhaseSpace p n)) :
    uniformFiniteMean (fun ρ : StabilizerState p n =>
      if (stabilizerLagrangian p n ρ).val ⊓ U = ⊥ then (0 : ℝ) else 1) ≤
      ((p : ℝ)^Module.finrank (ZMod p) U - 1) / (((p : ℝ)-1) * ((p : ℝ)^n+1)) := by
  classical
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpoint (ρ : StabilizerState p n) :
      ((p : ℝ)-1) * (if (stabilizerLagrangian p n ρ).val ⊓ U = ⊥ then (0 : ℝ) else 1) ≤
        ∑ v : NonzeroPhase p n,
          if v.val ∈ (stabilizerLagrangian p n ρ).val ⊓ U then (1 : ℝ) else 0 := by
    rw [sum_nonzeroPhase_mem]
    by_cases h : (stabilizerLagrangian p n ρ).val ⊓ U = ⊥
    · rw [if_pos h, mul_zero]
      exact sub_nonneg.mpr (one_le_pow₀ hp.le)
    · rw [if_neg h, mul_one]
      letI : Nontrivial ↥((stabilizerLagrangian p n ρ).val ⊓ U) :=
        Submodule.nontrivial_iff_ne_bot.mpr h
      exact sub_le_sub_right
        (le_self_pow₀ hp.le (Module.finrank_pos (R := ZMod p)
          (M := ↥((stabilizerLagrangian p n ρ).val ⊓ U))).ne') 1
  have hmean : ((p : ℝ)-1) * uniformFiniteMean (fun ρ : StabilizerState p n =>
      if (stabilizerLagrangian p n ρ).val ⊓ U = ⊥ then (0 : ℝ) else 1) ≤
      uniformFiniteMean (fun ρ : StabilizerState p n =>
        ∑ v : NonzeroPhase p n,
          if v.val ∈ (stabilizerLagrangian p n ρ).val ⊓ U then (1 : ℝ) else 0) := by
    unfold uniformFiniteMean
    rw [← mul_div_assoc, Finset.mul_sum]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ρ _ => hpoint ρ)) (by positivity)
  rw [expected_nonzero_intersection] at hmean
  calc
    _ ≤ (((p : ℝ)^Module.finrank (ZMod p) U - 1) / ((p : ℝ)^n+1)) / ((p : ℝ)-1) :=
      (le_div_iff₀ (by linarith)).mpr (by simpa only [mul_comm] using hmean)
    _ = _ := by rw [div_div]; congr 1; ring

end StabilizerLearning.Quantum
