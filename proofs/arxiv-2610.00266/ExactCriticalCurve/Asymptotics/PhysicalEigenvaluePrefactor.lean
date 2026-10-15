import ExactCriticalCurve.Asymptotics.PhysicalEigenvalueGroupNormalization
import ExactCriticalCurve.Asymptotics.PhysicalEigenvalueProducts
import ExactCriticalCurve.Quantum.PhysicalGramSpectrum

/-! The prefactor is made from the actual ensemble, actual stochastic group and
actual Gram normalization. Its limiting value is derived from those objects. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics
open Quantum Binary

def physicalGramGroupPrefactor (n k : ℕ) : ℝ :=
  physicalGramScale n k*(Nat.card (StochasticIsometryGroup k):ℝ)

theorem physicalGramGroupPrefactor_pos (n k : ℕ) : 0<physicalGramGroupPrefactor n k :=
  mul_pos (physicalGramScale_pos n k) (by exact_mod_cast Nat.card_pos)

/-- Exact finite normalization; the only truncation condition is a positive copy number. -/
theorem physicalGramGroupPrefactor_eq (n k : ℕ) (hk : 0<k) :
    physicalGramGroupPrefactor n k =
      (2:ℝ)^(((k:ℝ)-(n:ℝ)-1)*((k:ℝ)-(n:ℝ)-2)/2+1) *
        criticalR ((k:ℤ)-(n:ℤ)) * physicalStochasticCorrection k := by
  have hc := physicalGram_positive_product_cancel n (k-1)
  have hi : ((k-1:ℕ):ℤ)+1-(n:ℤ)=(k:ℤ)-(n:ℤ) := by omega
  rw [hi] at hc
  have hp :
      (2:ℝ)^(((n:ℝ)^2+3*n)/2) *
          (2:ℝ)^(((k:ℝ)-1)*((k:ℝ)-2)/2+1) =
      (2:ℝ)^(((k:ℝ)-(n:ℝ)-1)*((k:ℝ)-(n:ℝ)-2)/2+1) *
          (2:ℝ)^((n:ℝ)*(k:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
      ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hz : (2:ℝ)^((n:ℝ)*(k:ℝ))≠0 := by positivity
  have hw : (2:ℝ)^(((k:ℝ)-1)*((k:ℝ)-2)/2+1)≠0 := by positivity
  have hprod : (∏ j ∈ Finset.range (k-1), (1+(2:ℝ)^((j:ℝ)-(n:ℝ))))≠0 :=
    ne_of_gt (Finset.prod_pos (fun j _ => by positivity))
  have algebra {x y z w p r g : ℝ} (hz : z≠0) (hw : w≠0) (hp : p≠0)
      (h : x*w=y*z) :
      x*(p*r)/(z*p)*g=y*r*(g/w) := by
    have he : x/z=y/w := (div_eq_div_iff hz hw).mpr h
    calc
      _ = (x/z)*r*g := by field_simp
      _ = (y/w)*r*g := by rw [he]
      _ = _ := by ring
  unfold physicalGramGroupPrefactor physicalGramScale physicalStochasticCorrection
  rw [← Nat.card_eq_fintype_card,stabilizerGroup_card_real_normalized,
    physicalGram_denominator_normalized n k hk,← hc]
  exact algebra hz hw hprod hp

theorem physical_critical_window_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ => ((n:ℤ)+c).toNat) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b+c.natAbs,fun n hn => by
    have hc : -c≤(c.natAbs:ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -c))
    omega⟩

theorem physical_critical_window_eventually (c : ℤ) :
    ∀ᶠ n : ℕ in atTop, 0<((n:ℤ)+c).toNat ∧
      (((n:ℤ)+c).toNat:ℤ)=(n:ℤ)+c := by
  refine eventually_atTop.2 ⟨c.natAbs+1,fun n hn => ?_⟩
  have hc : -c≤(c.natAbs:ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -c))
  constructor <;> omega

theorem physicalGramGroupPrefactor_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ => physicalGramGroupPrefactor n ((n:ℤ)+c).toNat)
      atTop (𝓝 (criticalLambdaZero c)) := by
  have hcor := physicalStochasticCorrection_tendsto.comp (physical_critical_window_tendsto c)
  have hl : Tendsto (fun n : ℕ =>
      ((2:ℝ)^(((c:ℝ)-1)*((c:ℝ)-2)/2+1)*criticalR c) *
        physicalStochasticCorrection ((n:ℤ)+c).toNat)
      atTop (𝓝 (criticalLambdaZero c)) := by
    convert hcor.const_mul ((2:ℝ)^(((c:ℝ)-1)*((c:ℝ)-2)/2+1)*criticalR c) using 1
    unfold criticalLambdaZero
    ring
  apply hl.congr'
  filter_upwards [physical_critical_window_eventually c] with n hn
  rw [physicalGramGroupPrefactor_eq n _ hn.1]
  have hi : ((((n:ℤ)+c).toNat:ℤ)-(n:ℤ))=c := by rw [hn.2]; ring
  have hr : (((n:ℤ)+c).toNat:ℝ)-(n:ℝ)=(c:ℝ) := by exact_mod_cast hi
  rw [hi,hr]

/-- A single eventual bound works for all ordinary ranks. -/
theorem eventually_physicalGramGroupPrefactor_le (c : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      physicalGramGroupPrefactor n ((n:ℤ)+c).toNat ≤ 2*criticalLambdaZero c := by
  have h := (physicalGramGroupPrefactor_tendsto c).eventually
    (gt_mem_nhds (show criticalLambdaZero c<2*criticalLambdaZero c by
      nlinarith [criticalLambdaZero_pos c]))
  exact h.mono (fun _ hn => hn.le)

end ExactCriticalCurve.Asymptotics
