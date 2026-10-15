import StabilizerLearning.Quantum.OverlapEnergy
import StabilizerLearning.Quantum.LagrangianShellGeometry
import StabilizerLearning.Foundations.IntervalSubspaces
import StabilizerLearning.Bounds.OverlapEnergyAsymptotics

/-! Shell counts and row-energy bounds for the actual complete stabilizer
ensemble, using the proved intersection-fiber injection and exact phase fibers. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.Quantum
variable (p n : ℕ) [Fact p.Prime]

/-- Group each actual shell by its actual intersection with the center. -/
theorem lagrangianShellCount_le_intersections (L : Lagrangian p n)
    (r : ℕ) (hr : r ≤ n) :
    lagrangianShellCount p n L r ≤
      Nat.card (IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val (n-r)) *
        p^(r*r) := by
  let S := IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val (n-r)
  let C (K : S) := {M : Lagrangian p n // M.val ⊓ L.val = K.val}
  letI : Fintype S := Fintype.ofFinite _
  let f : {M : Lagrangian p n // lagrangianDistance p n L M = r} → Sigma C := fun M =>
    ⟨⟨M.val.val ⊓ L.val, bot_le, inf_le_right, by
      have hd : Module.finrank (ZMod p) ↥(M.val.val ⊓ L.val) ≤ n := by
        simpa only [L.property.2] using (Submodule.finrank_mono
          (inf_le_right : M.val.val ⊓ L.val ≤ L.val))
      have he := M.property
      unfold lagrangianDistance at he
      omega⟩, ⟨M.val, rfl⟩⟩
  have hf : Function.Injective f := by
    intro M N h
    apply Subtype.ext
    exact congrArg (fun z : Sigma C => z.2.val) h
  calc
    _ ≤ Nat.card (Sigma C) := Nat.card_le_card_of_injective f hf
    _ = ∑ K : S, Nat.card (C K) := Nat.card_sigma
    _ ≤ ∑ _K : S, p^(r*r) := by
      apply Finset.sum_le_sum
      intro K _
      exact card_lagrangianIntersectionFiber_le L K.val K.property.2.1 r hr K.property.2.2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
                rfl

/-- The coarse all-prime shell bound is enough for the original unit copy rate.
It counts actual Lagrangians, not coordinate representatives or a counting premise. -/
theorem lagrangianShellCount_le (L : Lagrangian p n) (r : ℕ) (hr : r ≤ n) :
    (lagrangianShellCount p n L r : ℝ) ≤ 4 * (p:ℝ)^(n*r) := by
  have hfirst : (lagrangianShellCount p n L r : ℝ) ≤
      (Nat.card (IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val (n-r)) : ℝ) *
        (p:ℝ)^(r*r) := by
    exact_mod_cast lagrangianShellCount_le_intersections p n L r hr
  have hcard := card_intervalSubspaces_le (⊥ : Submodule (ZMod p) (PhaseSpace p n))
    L.val bot_le (n-r) (by simp) (by rw [L.property.2]; omega)
  have hcard' :
      (Nat.card (IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val (n-r)) : ℝ) ≤
        4 * (p:ℝ)^((n-r)*r) := by
    simpa only [finrank_bot, Nat.sub_zero, L.property.2, Nat.sub_sub_self hr,
      ZMod.card p] using hcard
  calc
    _ ≤ _ := hfirst
    _ ≤ (4*(p:ℝ)^((n-r)*r)) * (p:ℝ)^(r*r) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = _ := by
      rw [mul_assoc, ← pow_add]
      congr 2
      have he := Nat.sub_add_cancel hr
      nlinarith

local instance : Fintype (Lagrangian p n) := Fintype.ofFinite _

/-- Exact shell decomposition of the row energy after the identical state is removed. -/
theorem stabilizerOverlapEnergy_eq_shell_sum (ℓ : StabilizerLabel p n)
    (k : ℕ) (hk : 0 < k) :
    stabilizerOverlapEnergy p n k (stabilizerLabelStateEquiv p n ℓ) =
      ∑ r ∈ Finset.range n, (lagrangianShellCount p n ℓ.1 (r+1) : ℝ) *
        ((p:ℝ)⁻¹)^((r+1)*(k-1)) := by
  have hs := Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.univ : Finset (Lagrangian p n))) (t := Finset.range (n+1))
    (g := lagrangianDistance p n ℓ.1)
    (fun M _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (lagrangianDistance_le p n ℓ.1 M)))
    (fun r => ((p:ℝ)⁻¹)^(r*(k-1)))
  have hc (r : ℕ) :
      (∑ M : Lagrangian p n with lagrangianDistance p n ℓ.1 M = r,
        ((p:ℝ)⁻¹)^(r*(k-1))) =
      (lagrangianShellCount p n ℓ.1 r : ℝ) * ((p:ℝ)⁻¹)^(r*(k-1)) := by
    simp only [Finset.sum_const, nsmul_eq_mul, lagrangianShellCount,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [hc] at hs
  rw [Finset.sum_range_succ'] at hs
  simp only [lagrangianShellCount_zero, Nat.cast_one, zero_mul, pow_zero, mul_one] at hs
  have he := stabilizerOverlapEnergy_add_one_eq_lagrangian_sum p n ℓ k hk
  linarith


/-- Actual tensor-overlap energy is bounded by one numerical expression for
every input. Only the copy count, never a shell estimate, is a premise. -/
theorem stabilizerOverlapEnergy_le_bound (k : ℕ) (hk : n+1 ≤ k)
    (x : StabilizerState p n) :
    stabilizerOverlapEnergy p n k x ≤ overlapEnergyBound (p:ℝ) n k := by
  obtain ⟨ℓ, rfl⟩ := (stabilizerLabelStateEquiv p n).surjective x
  rw [stabilizerOverlapEnergy_eq_shell_sum p n ℓ k (by omega)]
  unfold overlapEnergyBound geometricOverlapTail
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrn : r+1 ≤ n := by simpa only [Finset.mem_range] using hr
  have hs := lagrangianShellCount_le p n ℓ.1 (r+1) hrn
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsub : k-1 = n+(k-n-1) := by omega
  have hcancel : (p:ℝ)^(n*(r+1)) * ((p:ℝ)⁻¹)^((r+1)*n) = 1 := by
    rw [Nat.mul_comm (r+1) n, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hp)]
  calc
    _ ≤ (4*(p:ℝ)^(n*(r+1))) * ((p:ℝ)⁻¹)^((r+1)*(k-1)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 4 * ((p:ℝ)^(n*(r+1)) * ((p:ℝ)⁻¹)^((r+1)*n)) *
        ((p:ℝ)⁻¹)^((r+1)*(k-n-1)) := by
      rw [hsub, Nat.mul_add, pow_add]
      ring
    _ = _ := by rw [hcancel]; ring

/-- The original real excess-copy assumption makes the actual overlap energy
small simultaneously for all input states in each sufficiently large dimension. -/
theorem stabilizerOverlapEnergy_eventually_lt (k : ℕ → ℕ)
    (hk : Filter.Tendsto (fun N => (k N:ℝ)-(N:ℝ)) Filter.atTop Filter.atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop, ∀ x : StabilizerState p N,
      stabilizerOverlapEnergy p N (k N) x < ε := by
  have hp : 1 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hb := (overlapEnergyBound_tendsto_zero (p:ℝ) hp k hk).eventually
    (gt_mem_nhds hε)
  have hg := (Filter.tendsto_atTop.1 hk) 1
  filter_upwards [hb, hg] with N hN hgap
  intro x
  have hcopies : N+1 ≤ k N := by
    exact_mod_cast (show (N:ℝ)+1 ≤ (k N:ℝ) by linarith)
  exact (stabilizerOverlapEnergy_le_bound p N (k N) hcopies x).trans_lt hN

end StabilizerLearning.Quantum
