import StabilizerLearning.Quantum.OverlapShellCounting
import StabilizerLearning.Quantum.LagrangianShellExact

/-!
Exact intersection-shell identities for the full physical stabilizer ensemble.
The Grassmann factor below is the cardinality of actual subspaces in the center
Lagrangian. This module does not identify that cardinality with a Gaussian
binomial product.
-/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.Quantum
variable (p n : ℕ) [Fact p.Prime]

/-- An actual shell is the disjoint union of its actual intersection fibers. -/
def lagrangianShellEquivIntersectionFibers (L : Lagrangian p n)
    (r : ℕ) (hr : r ≤ n) :
    {M : Lagrangian p n // lagrangianDistance p n L M = r} ≃
      Σ K : IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val (n-r),
        {M : Lagrangian p n // M.val ⊓ L.val = K.val} where
  toFun M :=
    ⟨⟨M.val.val ⊓ L.val, bot_le, inf_le_right, by
      have hd : Module.finrank (ZMod p) ↥(M.val.val ⊓ L.val) ≤ n := by
        simpa only [L.property.2] using (Submodule.finrank_mono
          (inf_le_right : M.val.val ⊓ L.val ≤ L.val))
      have he := M.property
      unfold lagrangianDistance at he
      omega⟩, ⟨M.val, rfl⟩⟩
  invFun KM := ⟨KM.2.val, by
    unfold lagrangianDistance
    rw [KM.2.property, KM.1.property.2.2]
    omega⟩
  left_inv M := by apply Subtype.ext; rfl
  right_inv KM := by
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact KM.2.property
    · rfl

/-- Cardinal decomposition before any evaluation of the geometric fibers. -/
theorem lagrangianShellCount_eq_sum_fibers (L : Lagrangian p n)
    (r : ℕ) (hr : r ≤ n) :
    lagrangianShellCount p n L r =
      ∑ K : IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val (n-r),
        Nat.card {M : Lagrangian p n // M.val ⊓ L.val = K.val} := by
  rw [lagrangianShellCount,
    Nat.card_congr (lagrangianShellEquivIntersectionFibers p n L r hr),
    Nat.card_sigma]


/-- Exact shell count. The Grassmann factor is the literal count of actual
subspaces in L, not a separately postulated Gaussian-binomial formula. -/
theorem lagrangianShellCount_eq (L : Lagrangian p n) (r : ℕ) (hr : r ≤ n) :
    lagrangianShellCount p n L r =
      Nat.card (IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val (n-r)) *
        p^(r*(r+1)/2) := by
  rw [lagrangianShellCount_eq_sum_fibers p n L r hr]
  trans ∑ _K : IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val (n-r),
    p^(r*(r+1)/2)
  · apply Finset.sum_congr rfl
    intro K _
    exact card_lagrangianIntersectionFiber_eq L K.val K.property.2.1 r hr K.property.2.2
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card]
    rfl

/-- Exact physical energy with each shell evaluated by its actual Grassmann
cardinality and its proved symmetric-matrix fiber cardinality. -/
theorem stabilizerOverlapEnergy_eq_grassmann_sum (ℓ : StabilizerLabel p n)
    (k : ℕ) (hk : 0 < k) :
    stabilizerOverlapEnergy p n k (stabilizerLabelStateEquiv p n ℓ) =
      ∑ r ∈ Finset.range n,
        (Nat.card (IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n))
          ℓ.1.val (n-(r+1))) : ℝ) *
          (p:ℝ)^((r+1)*(r+2)/2) * ((p:ℝ)⁻¹)^((r+1)*(k-1)) := by
  rw [stabilizerOverlapEnergy_eq_shell_sum p n ℓ k hk]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r+1 ≤ n := by simpa only [Finset.mem_range] using hr
  rw [lagrangianShellCount_eq p n ℓ.1 (r+1) hrn, Nat.cast_mul, Nat.cast_pow]

/-- The sharp all-prime shell estimate retains the triangular exponent. -/
theorem lagrangianShellCount_le_sharp (L : Lagrangian p n) (r : ℕ) (hr : r ≤ n) :
    (lagrangianShellCount p n L r : ℝ) ≤
      4 * (p:ℝ)^((n-r)*r + r*(r+1)/2) := by
  rw [lagrangianShellCount_eq p n L r hr, Nat.cast_mul, Nat.cast_pow]
  have hcard := card_intervalSubspaces_le (⊥ : Submodule (ZMod p) (PhaseSpace p n))
    L.val bot_le (n-r) (by simp) (by rw [L.property.2]; omega)
  have hcard' :
      (Nat.card (IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n))
        L.val (n-r)) : ℝ) ≤ 4 * (p:ℝ)^((n-r)*r) := by
    simpa only [finrank_bot, Nat.sub_zero, L.property.2, Nat.sub_sub_self hr,
      ZMod.card p] using hcard
  calc
    _ ≤ (4*(p:ℝ)^((n-r)*r)) * (p:ℝ)^(r*(r+1)/2) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = _ := by rw [mul_assoc, ← pow_add]

private theorem overlap_shell_exponent_balance (n k r : ℕ)
    (hr : r+1 ≤ n) (hk : n+1 ≤ k) :
    (r+1)*(k-1) =
      ((n-(r+1))*(r+1) + (r+1)*(r+2)/2) +
        ((r+1)*(k-n-1) + r*(r+1)/2) := by
  have hd0 := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one r)
  have hd1 := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one (r+1))
  norm_num only [Nat.add_assoc] at hd1
  have hn := congrArg (fun t => t*(r+1)) (Nat.sub_add_cancel hr)
  have hsub : k-1 = n+(k-n-1) := by omega
  have hkn := congrArg (fun t => (r+1)*t) hsub
  nlinarith

/-- The actual distinct-state tensor row energy satisfies the original damped
tail bound, using the exact geometric fibers. Valid also for p=2 and n=0. -/
theorem stabilizerOverlapEnergy_le_dampedTail (k : ℕ) (hk : n+1 ≤ k)
    (x : StabilizerState p n) :
    stabilizerOverlapEnergy p n k x ≤ 4 * dampedTail (p:ℝ)⁻¹ n (k-n-1) := by
  obtain ⟨ℓ, rfl⟩ := (stabilizerLabelStateEquiv p n).surjective x
  rw [stabilizerOverlapEnergy_eq_shell_sum p n ℓ k (by omega)]
  unfold dampedTail
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrn : r+1 ≤ n := by simpa only [Finset.mem_range] using hr
  have hs := lagrangianShellCount_le_sharp p n ℓ.1 (r+1) hrn
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he := overlap_shell_exponent_balance n k r hrn hk
  let a := (n-(r+1))*(r+1) + (r+1)*(r+2)/2
  let b := (r+1)*(k-n-1) + r*(r+1)/2
  have hab : (r+1)*(k-1) = a+b := he
  have hcancel : (p:ℝ)^a * ((p:ℝ)⁻¹)^a = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hp)]
  calc
    _ ≤ (4*(p:ℝ)^a) * ((p:ℝ)⁻¹)^((r+1)*(k-1)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 4 * ((p:ℝ)^a * ((p:ℝ)⁻¹)^a) * ((p:ℝ)⁻¹)^b := by
      rw [hab, pow_add]
      ring
    _ = _ := by rw [hcancel]; ring


/-- The sharp numerical bound tends to zero under the original real excess-copy
hypothesis, with no signed-overhead substitution. -/
theorem dampedOverlapBound_tendsto_zero (k : ℕ → ℕ)
    (hk : Filter.Tendsto (fun N => (k N:ℝ)-(N:ℝ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun N => 4 * dampedTail (p:ℝ)⁻¹ N (k N-N-1))
      Filter.atTop (nhds 0) := by
  have hp : 1 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  simpa only [mul_zero] using
    (primeBase_tail_tendsto_zero (p:ℝ) hp id (fun N => k N-N-1)
      (real_copy_overhead_tendsto_nat k hk)).const_mul 4

end StabilizerLearning.Quantum
