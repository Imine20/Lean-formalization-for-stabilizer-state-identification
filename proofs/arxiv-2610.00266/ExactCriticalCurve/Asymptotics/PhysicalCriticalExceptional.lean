import ExactCriticalCurve.Asymptotics.PhysicalCriticalReindex
import ExactCriticalCurve.Quantum.ShorteningSectorLabels
import ExactCriticalCurve.Asymptotics.PhysicalCriticalWindow
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Classical Matrix Module
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics
open Binary Quantum

theorem physicalGramScale_shortening (n m : ℕ) :
    physicalGramScale n (m+2)*((2:ℝ)^n+(2:ℝ)^m)=physicalGramScale n (m+1) := by
  have hD : (2:ℝ)^n≠0 := by positivity
  have hP : (∏ j∈Finset.range m, ((2:ℝ)^n+(2:ℝ)^j))≠0 :=
    ne_of_gt (Finset.prod_pos (fun _ _ => by positivity))
  have hF : (2:ℝ)^n+(2:ℝ)^m≠0 := by positivity
  simp only [physicalGramScale,show m+2-1=m+1 by omega,Nat.add_sub_cancel,
    Finset.prod_range_succ]
  field_simp

theorem physicalExceptionalValue_shortening (n m r : ℕ) :
    physicalGramScale n (m+2)*
      (exceptionalSectorScalarPolynomial (m+2) (r+1)).eval ((2:ℝ)^n)=
    physicalGramScale n (m+1)*
      (ordinarySectorScalarPolynomial (m+1) r).eval ((2:ℝ)^n) := by
  simp only [exceptionalSectorScalarPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_C,Nat.add_sub_cancel,
    show m+2-1=m+1 by omega]
  rw [← mul_assoc,physicalGramScale_shortening]

theorem physicalExceptionalMoment_zero_of_not_four (n : ℕ) {k : ℕ}
    (h4 : ¬4∣k) : physicalExceptionalMoment n k=0 := by
  apply Finset.sum_eq_zero
  intro r _
  obtain ⟨N⟩ := r.property
  exact False.elim (h4 (exceptionalDefect_four_dvd N))

theorem physicalExceptionalAmplitude_zero_of_not_four (n : ℕ) {k : ℕ}
    (h4 : ¬4∣k) : physicalExceptionalAmplitude n k=0 := by
  apply Finset.sum_eq_zero
  intro r _
  obtain ⟨N⟩ := r.property
  exact False.elim (h4 (exceptionalDefect_four_dvd N))

theorem weighted_sqrt_sum_sq_le {ι : Type*} [Fintype ι] (w v : ι→ℝ)
    (hw : ∀i,0≤w i) (hv : ∀i,0≤v i) :
    (∑i,w i*Real.sqrt (v i))^2≤(∑i,w i)*(∑i,w i*v i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i)*Real.sqrt (v i))
  have he (i : ι) : Real.sqrt (w i)*(Real.sqrt (w i)*Real.sqrt (v i))=w i*Real.sqrt (v i) := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hw i)]
  simpa only [he,mul_pow,Real.sq_sqrt (hw _),Real.sq_sqrt (hv _)] using h

theorem physicalExceptionalAmplitude_sq_le_moment (n : ℕ) {k : ℕ} (hk : 0<k) :
    (physicalExceptionalAmplitude n k)^2≤physicalExceptionalMoment n k := by
  have h := weighted_sqrt_sum_sq_le
    (fun r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)} =>
      physicalSectorWeight n k (.inr r))
    (fun r => physicalGramSectorValue n k (.inr r))
    (fun _ => physicalSectorWeight_nonneg n k _) (fun _ => (physicalGramSectorValue_pos n k _).le)
  have hm := physicalSectorWeight_sum_le_one n hk
  rw [Fintype.sum_sum_type] at hm
  have ho : 0≤∑r : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)},
      physicalSectorWeight n k (.inl r) :=
    Finset.sum_nonneg (fun _ _ => physicalSectorWeight_nonneg n k _)
  have he : (∑r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
      physicalSectorWeight n k (.inr r))≤1 := by linarith
  exact h.trans ((mul_le_mul_of_nonneg_right he (physicalExceptionalMoment_nonneg n k)).trans_eq
    (one_mul _))

theorem physicalExceptionalMoment_mul_dimension (n : ℕ) {k : ℕ}
    (hk : 0<k) (h4 : 4∣k) :
    (2:ℝ)^n*physicalExceptionalMoment n k=1 := by
  have hk2 : 2≤k := by omega
  obtain ⟨m,hkm⟩ := Nat.exists_eq_add_of_le hk2
  have hkm' : k=m+2 := by omega
  clear hkm
  subst k
  have hm : 0<m+1 := by omega
  have hm4 : ¬4∣m+1 := by omega
  let f : ℕ→ℝ := fun r =>
    physicalGramScale n (m+2)*(exceptionalSectorScalarPolynomial (m+2) r).eval ((2:ℝ)^n)
  have hv (r : ℕ) : f (r+1)=
      physicalGramScale n (m+1)*(ordinarySectorScalarPolynomial (m+1) r).eval ((2:ℝ)^n) := by
    simpa only [f] using physicalExceptionalValue_shortening n m r
  have ht := stabilizerGram_trace_one_power n hm
  rw [Fintype.sum_sum_type] at ht
  have hz : (∑a : {r : Fin (m+1+1) // Nonempty (ExceptionalDefect (m+1) r.val)},
      (finrank ℂ (LinearMap.range (physicalSectorGrade n (m+1) (.inr a)).mulVecLin):ℝ)*
        physicalGramSectorValue n (m+1) (.inr a))=0 := by
    apply Finset.sum_eq_zero
    intro a _
    obtain ⟨N⟩ := a.property
    exact False.elim (hm4 (exceptionalDefect_four_dvd N))
  rw [hz,add_zero] at ht
  have hs := shortening_sector_weighted_rank_sum n
    (show 4∣(m+1)+1 by omega) f
  simp only [hv] at hs
  have he : (2:ℝ)^n*
      (∑a : {r : Fin ((m+2)+1) // Nonempty (ExceptionalDefect (m+2) r.val)},
        (finrank ℂ (LinearMap.range (exceptionalCSSGrade n (m+2) a.val.val).mulVecLin):ℝ)*
          f a.val.val)=(Fintype.card (StabilizerGroup n):ℝ) := by
    have hs' := hs.trans ht
    simpa only [Nat.add_assoc] using hs'
  unfold physicalExceptionalMoment physicalSectorWeight physicalGramSectorValue
  simp only [physicalSectorGrade,physicalSectorScalarPolynomial,div_mul_eq_mul_div,
    ← Finset.sum_div,← mul_div_assoc]
  change ((2:ℝ)^n*(∑a : {r : Fin ((m+2)+1) // Nonempty (ExceptionalDefect (m+2) r.val)},
    (finrank ℂ (LinearMap.range (exceptionalCSSGrade n (m+2) a.val.val).mulVecLin):ℝ)*
      f a.val.val))/(Fintype.card (StabilizerGroup n):ℝ)=1
  rw [he,div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

theorem physicalExceptionalMoment_eq (n : ℕ) {k : ℕ} (hk : 0<k) (h4 : 4∣k) :
    physicalExceptionalMoment n k=1/(2:ℝ)^n := by
  apply (eq_div_iff (by positivity : (2:ℝ)^n≠0)).mpr
  simpa only [mul_comm] using physicalExceptionalMoment_mul_dimension n hk h4

theorem physicalExceptionalMoment_le_geometric (n : ℕ) {k : ℕ} (hk : 0<k) :
    physicalExceptionalMoment n k≤(1/2:ℝ)^n := by
  by_cases h4 : 4∣k
  · rw [physicalExceptionalMoment_eq n hk h4]
    simp only [one_div,inv_pow]
    exact le_rfl
  · rw [physicalExceptionalMoment_zero_of_not_four n h4]
    positivity

theorem physicalExceptionalMoment_window_tendsto (c : ℤ) :
    Filter.Tendsto (fun n : ℕ => physicalExceptionalMoment n ((n:ℤ)+c).toNat)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => physicalExceptionalMoment_nonneg n _))
  · filter_upwards [eventually_physicalCritical_copy_ge c 1] with n hn
    exact physicalExceptionalMoment_le_geometric n (by omega)
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem physicalExceptionalAmplitude_window_tendsto (c : ℤ) :
    Filter.Tendsto (fun n : ℕ => physicalExceptionalAmplitude n ((n:ℤ)+c).toNat)
      Filter.atTop (nhds 0) := by
  have ht := (physicalExceptionalMoment_window_tendsto c).sqrt
  simp only [Real.sqrt_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => physicalExceptionalAmplitude_nonneg n _)) _ ht
  filter_upwards [eventually_physicalCritical_copy_ge c 1] with n hn
  have hs := physicalExceptionalAmplitude_sq_le_moment n (show 0<((n:ℤ)+c).toNat by omega)
  have hm := physicalExceptionalMoment_nonneg n ((n:ℤ)+c).toNat
  have ha := physicalExceptionalAmplitude_nonneg n ((n:ℤ)+c).toNat
  have hsq := Real.sq_sqrt hm
  have hp := Real.sqrt_nonneg (physicalExceptionalMoment n ((n:ℤ)+c).toNat)
  nlinarith

theorem physicalOrdinary_moment_window_tendsto (c : ℤ) :
    Filter.Tendsto (fun n : ℕ => ∑'r : ℕ,
      physicalOrdinaryWeight n ((n:ℤ)+c).toNat r*physicalOrdinaryValue n ((n:ℤ)+c).toNat r)
      Filter.atTop (nhds 1) := by
  have ht := (physicalExceptionalMoment_window_tendsto c).const_sub 1
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_physicalCritical_copy_ge c 1] with n hn
  have h := physicalOrdinary_moment_add_exceptional n (show 0<((n:ℤ)+c).toNat by omega)
  linarith

end ExactCriticalCurve.Asymptotics
