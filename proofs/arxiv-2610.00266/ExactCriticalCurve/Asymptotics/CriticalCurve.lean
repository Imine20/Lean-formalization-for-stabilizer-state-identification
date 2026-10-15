import ExactCriticalCurve.Asymptotics.PhysicalCriticalLimit
import ExactCriticalCurve.Asymptotics.CriticalAmplitudeBounds
import ExactCriticalCurve.FiniteSpectrum.FiniteSpectrum

/-! The fixed-offset curve with genuine physical optimality and convergent numerical products. -/
noncomputable section
open Classical Filter
open scoped BigOperators Topology
namespace ExactCriticalCurve
open Binary Quantum FiniteSpectrum Asymptotics

/-- Theorem 2, including the normalization inherited from the actual finite Gram trace. -/
theorem criticalCurve (c : ℤ) :
    0<criticalA ∧ 0<criticalQ ∧
    Multipliable (fun j : ℕ => 1+(1/2:ℝ)^(j+1)) ∧
    Multipliable (fun j : ℕ => 1-(1/4:ℝ)^(j+1)) ∧
    criticalA=(∏' j : ℕ, (1+(1/2:ℝ)^(j+1))) ∧
    criticalQ=(∏' j : ℕ, (1-(1/4:ℝ)^(j+1))) ∧
    0<criticalR c ∧ criticalR 1=1 ∧
    (criticalR c=if c≤1 then ∏ j ∈ Finset.range (1-c).toNat, (1+(1/2:ℝ)^(j+1))
      else (∏ j ∈ Finset.range (c-1).toNat, (1+(2:ℝ)^j))⁻¹) ∧
    (∀ r : ℕ, 0<criticalWeight c r ∧ 0<criticalLambda c r) ∧
    Summable (fun r : ℕ => criticalWeight c r*Real.sqrt (criticalLambda c r)) ∧
    Summable (fun r : ℕ => criticalWeight c r*criticalLambda c r) ∧
    (∑' r : ℕ, criticalWeight c r*criticalLambda c r)=1 ∧
    Asymptotics.criticalCurve c=(∑' r : ℕ, criticalWeight c r*Real.sqrt (criticalLambda c r))^2 ∧
    (∀ᶠ n : ℕ in atTop, 1≤((n:ℤ)+c).toNat ∧ (((n:ℤ)+c).toNat:ℤ)=(n:ℤ)+c) ∧
    Tendsto (fun n : ℕ => closedFiniteSuccess n ((n:ℤ)+c).toNat)
      atTop (𝓝 (Asymptotics.criticalCurve c)) ∧
    Tendsto (fun n : ℕ => uniformSuccess
      (fun S : StabilizerGroup n => matrixTensorPower ((n:ℤ)+c).toNat (stabilizerProjection S))
      (stabilizerPrettyGoodMeasurement n ((n:ℤ)+c).toNat))
      atTop (𝓝 (Asymptotics.criticalCurve c)) ∧
    (∀ᶠ n : ℕ in atTop,
      IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n ((n:ℤ)+c).toNat) (StabilizerGroup n),
        uniformSuccess (fun S : StabilizerGroup n =>
          matrixTensorPower ((n:ℤ)+c).toNat (stabilizerProjection S)) M=v}
        (closedFiniteSuccess n ((n:ℤ)+c).toNat)) := by
  have hcopy := eventually_physicalCritical_copy_ge c 1
  have hlim := physicalFiniteSuccess_critical_tendsto c
  refine ⟨criticalA_pos,criticalQ_pos,
    geometric_plus_multipliable (1/2) (by norm_num) (by norm_num),
    geometric_minus_multipliable (1/4) (by norm_num) (by norm_num),
    rfl,rfl,criticalR_pos c,criticalR_one,rfl,
    (fun r => ⟨criticalWeight_pos c r,criticalLambda_pos c r⟩),?_,?_,
    criticalWeight_mul_lambda_tsum c,rfl,?_,?_,?_,?_⟩
  · exact summable_criticalAmplitude c
  · by_contra h
    have hz := tsum_eq_zero_of_not_summable h
    rw [criticalWeight_mul_lambda_tsum c] at hz
    norm_num at hz
  · exact hcopy.and (eventually_physicalCritical_window_exact c)
  · apply hlim.congr'
    filter_upwards [hcopy] with n hn
    exact (closedFiniteSuccess_eq_physical n (show 0<((n:ℤ)+c).toNat by omega)).symm
  · apply hlim.congr'
    filter_upwards [hcopy] with n hn
    exact (physicalFiniteSuccess_attained n (show 0<((n:ℤ)+c).toNat by omega)).symm
  · filter_upwards [hcopy] with n hn
    rw [closedFiniteSuccess_eq_physical n (show 0<((n:ℤ)+c).toNat by omega)]
    exact physicalFiniteSuccess_isGreatest n (by omega)

end ExactCriticalCurve
