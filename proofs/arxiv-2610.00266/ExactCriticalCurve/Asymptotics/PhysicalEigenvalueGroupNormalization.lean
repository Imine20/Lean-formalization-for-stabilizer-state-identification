import ExactCriticalCurve.Asymptotics.PhysicalEigenvalueGroupCard
import ExactCriticalCurve.Asymptotics.PhysicalWeightProducts

/-! Leading powers of the genuine group orders and their common positive limit. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics
open Binary

theorem physicalStochasticOrthogonalFactor_normalized (m : ℕ) (hm : 0<m) (σ : ℝ) :
    physicalOrthogonalFactor m σ =
      (2:ℝ)^(2*(m:ℝ)^2-(m:ℝ)+1) *
        (1-σ*(2:ℝ)^(-(m:ℝ))) * physicalQPartial (m-1) := by
  have hc : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hp :
      2*(2:ℝ)^(m*(m-1))*(2:ℝ)^m*
        (2:ℝ)^(((m-1:ℕ):ℝ)*(((m-1:ℕ):ℝ)+1)) =
        (2:ℝ)^(2*(m:ℝ)^2-(m:ℝ)+1) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast]
    nth_rw 1 [show (2:ℝ)=(2:ℝ)^(1:ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
      ← Real.rpow_add (by norm_num : (0:ℝ)<2),
      ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    rw [Nat.cast_mul,hc]
    ring
  unfold physicalOrthogonalFactor
  rw [physical_four_minus_product,← hp,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
  have hn : (2:ℝ)^m≠0 := by positivity
  field_simp
  <;> ring

theorem physicalStochasticSymplecticFactor_normalized (m : ℕ) :
    physicalSymplecticFactor m =
      (2:ℝ)^(2*(m:ℝ)^2+(m:ℝ))*physicalQPartial m := by
  unfold physicalSymplecticFactor
  rw [physical_four_minus_product,← mul_assoc,← Real.rpow_natCast,
    ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 2
  push_cast
  ring

/-- The actual stochastic order divided by its universal leading power. -/
def physicalStochasticCorrection (k : ℕ) : ℝ :=
  (Nat.card (StochasticIsometryGroup k):ℝ) /
    (2:ℝ)^(((k:ℝ)-1)*((k:ℝ)-2)/2+1)

theorem physicalStochasticCorrection_pos (k : ℕ) : 0<physicalStochasticCorrection k := by
  unfold physicalStochasticCorrection
  exact div_pos (by exact_mod_cast Nat.card_pos) (Real.rpow_pos_of_pos (by norm_num) _)

/-- All residue classes retain their true signed correction or symplectic product. -/
theorem physicalStochasticCorrection_cases (k : ℕ) (hk : 3≤k) :
    let m := (k-1)/2
    (∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
      physicalStochasticCorrection k =
        (1-σ*(2:ℝ)^(-(m:ℝ)))*physicalQPartial (m-1)) ∨
    physicalStochasticCorrection k=physicalQPartial m := by
  dsimp only
  let m := (k-1)/2
  have hm : 0<m := by dsimp [m]; omega
  have hne : (2:ℝ)^(((k:ℝ)-1)*((k:ℝ)-2)/2+1)≠0 := by positivity
  rcases actualStochasticGroup_card_cases k hk with ⟨ho,σ,hσ,hg⟩ | ⟨he,hg⟩
  · left
    refine ⟨σ,hσ,?_⟩
    have hd : (k:ℝ)=2*(m:ℝ)+1 := by
      have h : k=2*m+1 := by dsimp [m]; omega
      exact_mod_cast h
    unfold physicalStochasticCorrection
    rw [hg,physicalStochasticOrthogonalFactor_normalized _ hm]
    have hp : 2*(m:ℝ)^2-(m:ℝ)+1=((k:ℝ)-1)*((k:ℝ)-2)/2+1 := by rw [hd]; ring
    rw [hp]
    field_simp
    rfl
  · have hd : (k:ℝ)=2*(m:ℝ)+2 := by
      have h : k=2*m+2 := by dsimp [m]; omega
      exact_mod_cast h
    rcases hg with ⟨σ,hσ,hg⟩ | hg
    · left
      refine ⟨σ,hσ,?_⟩
      unfold physicalStochasticCorrection
      rw [hg,physicalStochasticOrthogonalFactor_normalized _ hm]
      have hp : (2:ℝ)^(2*m)*(2:ℝ)^(2*(m:ℝ)^2-(m:ℝ)+1)=
          (2:ℝ)^(((k:ℝ)-1)*((k:ℝ)-2)/2+1) := by
        rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        congr 1
        rw [hd]
        push_cast
        ring
      rw [← mul_assoc,← mul_assoc,hp]
      field_simp
      rfl
    · right
      unfold physicalStochasticCorrection
      rw [hg,physicalStochasticSymplecticFactor_normalized]
      have hp : 2*(2:ℝ)^(2*(m:ℝ)^2+(m:ℝ))=
          (2:ℝ)^(((k:ℝ)-1)*((k:ℝ)-2)/2+1) := by
        nth_rw 1 [show (2:ℝ)=(2:ℝ)^(1:ℝ) by norm_num]
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        congr 1
        rw [hd]
        ring
      rw [← mul_assoc,hp]
      field_simp


/-- Uniform bounds for the actual signed corrections; no congruence class is discarded. -/
theorem physicalStochasticCorrection_bounds (k : ℕ) (hk : 3≤k) :
    let m := (k-1)/2
    (1-(1/2:ℝ)^m)*physicalQPartial (m-1) ≤ physicalStochasticCorrection k ∧
    physicalStochasticCorrection k ≤ (1+(1/2:ℝ)^m)*physicalQPartial (m-1) := by
  dsimp only
  let m := (k-1)/2
  have hm : 0<m := by dsimp [m]; omega
  have hp := (physicalQPartial_pos (m-1)).le
  have hb : 0≤(1/2:ℝ)^m := by positivity
  have he : (2:ℝ)^(-(m:ℝ))=(1/2:ℝ)^m := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,← inv_pow]
    norm_num
  rcases physicalStochasticCorrection_cases k hk with ⟨σ,hσ,h⟩ | h
  · rw [he] at h
    rcases hσ with rfl | rfl <;> rw [h] <;> constructor <;> nlinarith
  · have hsucc : m-1+1=m := by omega
    have hQ : physicalQPartial m=physicalQPartial (m-1)*(1-(1/4:ℝ)^m) := by
      conv_lhs => rw [← hsucc]
      simpa only [physicalQPartial,hsucc] using
        (Finset.prod_range_succ (fun j => (1-(1/4:ℝ)^(j+1))) (m-1))
    have hle : (1/4:ℝ)^m≤(1/2:ℝ)^m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
    have hnon : 0≤(1/4:ℝ)^m := by positivity
    rw [h,hQ]
    constructor <;> nlinarith

theorem physicalStochasticCorrection_tendsto :
    Tendsto physicalStochasticCorrection atTop (𝓝 criticalQ) := by
  have hm : Tendsto (fun k : ℕ => (k-1)/2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨2*b+3,fun k hk => by omega⟩
  have hm' : Tendsto (fun k : ℕ => (k-1)/2-1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨2*b+5,fun k hk => by omega⟩
  have hpow : Tendsto (fun k : ℕ => (1/2:ℝ)^((k-1)/2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp hm
  have hQ := physicalQPartial_tendsto.comp hm'
  have hlo : Tendsto (fun k : ℕ =>
      (1-(1/2:ℝ)^((k-1)/2))*physicalQPartial ((k-1)/2-1)) atTop (𝓝 criticalQ) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hpow).mul hQ
  have hhi : Tendsto (fun k : ℕ =>
      (1+(1/2:ℝ)^((k-1)/2))*physicalQPartial ((k-1)/2-1)) atTop (𝓝 criticalQ) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).add hpow).mul hQ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · exact eventually_atTop.2 ⟨3,fun k hk => (physicalStochasticCorrection_bounds k hk).1⟩
  · exact eventually_atTop.2 ⟨3,fun k hk => (physicalStochasticCorrection_bounds k hk).2⟩

end ExactCriticalCurve.Asymptotics
