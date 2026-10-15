import ExactCriticalCurve.Asymptotics.PhysicalEigenvalueGroupCard
import ExactCriticalCurve.Quantum.DefectStabilizerFactorization
import ExactCriticalCurve.Quantum.OddCSSMultiplicity
import ExactCriticalCurve.Quantum.EvenZeroCSSMultiplicity

/-! The full paper group order for the genuine stochastic isometry group,
including the determined original-dimension sign and the small endpoints. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
open Binary Quantum FiniteQuadratic
set_option maxHeartbeats 3000000

/-- The positive-dimensional orthogonal product, with the genuine zero-dimensional
plus endpoint and zero for the absent zero-dimensional minus tower. -/
def paperOrthogonalOrder (m : ℕ) (σ : ℝ) : ℝ :=
  if m = 0 then if σ = 1 then 1 else 0 else physicalOrthogonalFactor m σ

private def zeroOrdinaryDefect (k : ℕ) (hk : 0 < k) : OrdinaryDefect k 0 :=
  ⟨⊥, (by intro x hx; rw [show x = 0 from hx, weightQuadratic_zero]),
    (finrank_bot _ _), (by
      intro h
      have hx : allOnes k = 0 := h
      have h0 := congrFun hx ⟨0, hk⟩
      exact one_ne_zero h0)⟩

private theorem zeroOrdinaryDefect_card (k : ℕ) (hk : 0 < k) :
    Nat.card (OrdinaryDefect k 0) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨zeroOrdinaryDefect k hk, fun N => ?_⟩
  apply Subtype.ext
  exact Submodule.finrank_eq_zero.mp N.property.2.1

private theorem stochasticGroup_card_zero_quotient (k : ℕ) (hk : 0 < k) :
    Nat.card (StochasticIsometryGroup k) =
      Nat.card (CSSQuotientIsometryGroup (zeroOrdinaryDefect k hk).val
        (zeroOrdinaryDefect k hk).property.1) := by
  have h := ordinaryStochasticGroup_card_factorization_explicit (zeroOrdinaryDefect k hk)
  have hz : Nat.card ((Fin 0 → ZMod 2) ≃ₗ[ZMod 2] (Fin 0 → ZMod 2)) = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    exact ⟨LinearEquiv.refl _ _, fun g => Subsingleton.elim _ _⟩
  rw [zeroOrdinaryDefect_card k hk, hz] at h
  simpa only [Nat.zero_mul, pow_zero, Nat.one_mul, Nat.choose_zero_right, Nat.choose_eq_zero_of_lt (by decide : 0 < 2)] using h

private theorem signedOrthogonal_card_real
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (m : ℕ) (hd : finrank (ZMod 2) V = 2*m)
    (σ : ℚ) (hs : σ=1 ∨ σ= -1)
    (hg : binaryQuadraticGaussSum Q = (σ:ℂ)*(2:ℂ)^m) :
    (Nat.card (BinaryQuadraticIsometryGroup Q) : ℝ) =
      paperOrthogonalOrder m σ := by
  by_cases hm : m = 0
  · subst m
    have hd0 : finrank (ZMod 2) V = 0 := by simpa using hd
    haveI : Subsingleton V := (Module.finrank_zero_iff.mp hd0)
    have hg0 := binaryQuadraticGaussSum_of_subsingleton Q
    have hs1 : σ = 1 := by
      rw [hg0] at hg
      norm_num at hg
      exact_mod_cast hg.symm
    rw [binaryQuadraticIsometryGroup_zero_card Q hd0, hs1]
    norm_num [paperOrthogonalOrder]
  · have hc := congrArg (fun x : ℚ => (x:ℝ))
      (binaryQuadraticIsometryGroup_card Q hQ m (by omega) hd σ hs hg)
    simpa [paperOrthogonalOrder, hm, physicalOrthogonalFactor] using hc

/-- Odd dimensions have the exact original-k Gauss sign, including k=1. -/
theorem stochasticGroup_order_odd_mod_eight (k : ℕ) (hk : k%2=1) :
    (Nat.card (StochasticIsometryGroup k) : ℝ) =
      paperOrthogonalOrder ((k-1)/2) (if k%8=1 ∨ k%8=7 then 1 else -1) := by
  have hkp : 0 < k := by omega
  have hz : (k:ZMod 2)=1 := by
    apply ZMod.val_injective 2
    simpa using hk
  let N := zeroOrdinaryDefect k hkp
  rw [stochasticGroup_card_zero_quotient k hkp,
    Nat.card_congr (cssQuotientOddOrthogonalEquiv N.val N.property.1 hz).toEquiv]
  have hd := cssQuotient_evenHalfForm_finrank N.val N.property.1 hz
  have hg := cssQuotient_evenHalfForm_gauss_signed N.val N.property.1 hz
  have hm : k/2 = (k-1)/2 := by omega
  simp only [N.property.2.1, Nat.sub_zero, hm] at hd hg
  have hs : (if k%8=1 ∨ k%8=7 then (1:ℚ) else -1)=1 ∨
      (if k%8=1 ∨ k%8=7 then (1:ℚ) else -1)= -1 := by split_ifs <;> simp
  have hc := signedOrthogonal_card_real
    (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm
    (cssQuotient_evenHalfForm_nondegenerate N.val N.property.1 hz)
    ((k-1)/2) hd _ hs (by simpa only [apply_ite, Rat.cast_one, Rat.cast_neg] using hg)
  simpa only [apply_ite, Rat.cast_one, Rat.cast_neg] using hc

/-- The k=2 mod 4 branch, including its zero-dimensional symplectic endpoint. -/
theorem stochasticGroup_order_two_mod_four (k : ℕ) (hk : k%4=2) :
    (Nat.card (StochasticIsometryGroup k) : ℝ) =
      2*physicalSymplecticFactor ((k-2)/2) := by
  have he : (k:ZMod 2)=0 := by
    apply ZMod.val_injective 2
    simpa using (show k%2=0 by omega)
  let Q := stochasticHalfForm k
  let w := allOnes k
  have hQ := stochasticHalfForm_nondegenerate he
  have hw : Q w = 1 := by
    rw [stochasticHalfForm_wu he]
    have h4 : (k:ZMod 4)=2 := by
      apply ZMod.val_injective 4
      simpa using hk
    rw [h4]
    norm_num [StochasticCounting.halfEven, ZMod.val]
  obtain ⟨v,hp⟩ := NonsingularWu.exists_companion Q w hQ hw
  have hd : finrank (ZMod 2) (NonsingularWu.complement Q w v)=2*((k-2)/2) := by
    have h := NonsingularWu.complement_finrank_add_two Q w v hp
    have hv : finrank (ZMod 2) (BinaryVector k)=k := by simp [BinaryVector]
    rw [hv] at h
    omega
  have hc := actualSymplectic_card_real (NonsingularWu.complementPairing Q w v)
    (NonsingularWu.complementPairing_isAlt Q w v)
    (NonsingularWu.complementPairing_nondegenerate Q w v hQ hp) ((k-2)/2) hd
  have hg := NonsingularWu.stabilizer_card Q w v hp hQ hw
  have hgN : Nat.card (NonsingularWu.stabilizer Q w)=
      2*Nat.card (BinarySymplecticIsometryGroup (NonsingularWu.complementPairing Q w v)) := by
    simpa only [← Nat.card_eq_fintype_card] using hg
  rw [Nat.card_congr (stochasticEvenOrthogonalEquiv he).toEquiv, hgN]
  push_cast
  exact congrArg (fun x:ℝ => 2*x) hc

/-- The 4-divisible branch uses the original-k sign after removing the Wu plane. -/
theorem stochasticGroup_order_zero_mod_four (k : ℕ) (hk : 0<k) (h4 : 4∣k) :
    (Nat.card (StochasticIsometryGroup k) : ℝ) =
      (2:ℝ)^(k-2)*paperOrthogonalOrder ((k-2)/2) (if k%8=0 then 1 else -1) := by
  let N := zeroOrdinaryDefect k hk
  let E := extendWuDefect hk h4 N
  let D := cssFlagQuotientGeometry N.val N.property.1
  have he : (k:ZMod 2)=0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_trans (by decide : 2∣4) h4)
  have hQ := cssQuotient_halfForm_nondegenerate N.val N.property.1 he
  have hw := cssQuotient_halfForm_wu_zero N.val N.property.1 h4
  obtain ⟨v,hv,hp⟩ := exists_binaryHyperbolicPartner D.halfForm hQ D.wu
    (ordinaryCSSQuotient_wu_ne_zero N) hw
  obtain ⟨e⟩ := ordinaryWuComplement_isometry_extended hk h4 N v hv hp
  have hd := cssQuotient_halfForm_finrank E.val E.property.1 he
  have hg := cssQuotient_halfForm_gauss_even_zero_signed E.val E.property.1 h4
  have hm : k/2-(0+1)=(k-2)/2 := by omega
  simp only [E.property.2.1, hm] at hd hg
  have hs : (if k%8=0 then (1:ℚ) else -1)=1 ∨
      (if k%8=0 then (1:ℚ) else -1)= -1 := by split_ifs <;> simp
  have hc := signedOrthogonal_card_real
    (cssFlagQuotientGeometry E.val E.property.1).halfForm
    (cssQuotient_halfForm_nondegenerate E.val E.property.1 he)
    ((k-2)/2) hd _ hs (by simpa only [apply_ite, Rat.cast_one, Rat.cast_neg] using hg)
  have hcomp : finrank (ZMod 2) (binaryHyperbolicComplement D.halfForm D.wu v)=k-2 := by
    have hdN := cssQuotient_halfForm_finrank N.val N.property.1 he
    have hdC := binaryHyperbolicComplement_finrank D.halfForm D.wu v hp
    simp only [N.property.2.1, Nat.sub_zero] at hdN
    change finrank (ZMod 2) (CSSQuotient N.val)=_ at hdN
    omega
  rw [stochasticGroup_card_zero_quotient k hk,
    Nat.card_congr (cssQuotientEvenOrthogonalEquiv N.val N.property.1 he).toEquiv,
    binarySingularStabilizer_card D.halfForm hQ D.wu v hw hv hp,
    Nat.card_congr (binaryQuadraticGroupIsometryEquiv _ _ e), hcomp]
  push_cast
  rw [hc]
  split_ifs <;> simp_all only [Rat.cast_one, Rat.cast_neg] <;> ring


/-- The original-paper odd type exponent is exactly the modulo-eight Gauss sign. -/
theorem paperOddTypeSign_mod_eight (k : ℕ) (hk : k%2=1) :
    (-1:ℝ)^((k*k-1)/8) = if k%8=1 ∨ k%8=7 then 1 else -1 := by
  rw [pow_eq_pow_mod _ (by norm_num : (-1:ℝ)^2=1)]
  have hlt := Nat.mod_lt k (by decide : 0<8)
  interval_cases h : k%8
  all_goals first | omega | skip
  · have he : k*k=8*(8*(k/8)^2+2*(k/8))+1 := by
      conv_lhs => rw [show k=8*(k/8)+1 by omega]
      ring
    have hp : ((k*k-1)/8)%2=0 := by omega
    simp [hp]
  · have he : k*k=8*(8*(k/8)^2+6*(k/8)+1)+1 := by
      conv_lhs => rw [show k=8*(k/8)+3 by omega]
      ring
    have hp : ((k*k-1)/8)%2=1 := by omega
    simp [hp]
  · have he : k*k=8*(8*(k/8)^2+10*(k/8)+3)+1 := by
      conv_lhs => rw [show k=8*(k/8)+5 by omega]
      ring
    have hp : ((k*k-1)/8)%2=1 := by omega
    simp [hp]
  · have he : k*k=8*(8*(k/8)^2+14*(k/8)+6)+1 := by
      conv_lhs => rw [show k=8*(k/8)+7 by omega]
      ring
    have hp : ((k*k-1)/8)%2=0 := by omega
    simp [hp]

/-- The original-paper four-divisible type exponent is the modulo-eight Gauss sign. -/
theorem paperEvenZeroTypeSign_mod_eight (k : ℕ) (h4 : 4∣k) :
    (-1:ℝ)^(k/4) = if k%8=0 then 1 else -1 := by
  rw [pow_eq_pow_mod _ (by norm_num : (-1:ℝ)^2=1)]
  by_cases h : k%8=0
  · have hp : (k/4)%2=0 := by omega
    simp [h,hp]
  · have hp : (k/4)%2=1 := by omega
    simp [h,hp]

/-- Eq. (stochastic-order) and Eq. (type) of the frozen paper, on the actual
binary stochastic isometry group and for every physical copy number k≥1. -/
theorem paperStochasticGroup_order (k : ℕ) (hk : 1≤k) :
    (Nat.card (StochasticIsometryGroup k) : ℝ) =
      if k%2=1 then
        paperOrthogonalOrder ((k-1)/2) ((-1:ℝ)^((k*k-1)/8))
      else if k%4=2 then
        2*physicalSymplecticFactor ((k-2)/2)
      else
        (2:ℝ)^(k-2)*paperOrthogonalOrder ((k-2)/2) ((-1:ℝ)^(k/4)) := by
  by_cases ho : k%2=1
  · rw [if_pos ho, paperOddTypeSign_mod_eight k ho]
    exact stochasticGroup_order_odd_mod_eight k ho
  · rw [if_neg ho]
    by_cases ht : k%4=2
    · rw [if_pos ht]
      exact stochasticGroup_order_two_mod_four k ht
    · rw [if_neg ht]
      have h4 : 4∣k := by omega
      rw [paperEvenZeroTypeSign_mod_eight k h4]
      exact stochasticGroup_order_zero_mod_four k (by omega) h4

/-- The odd plus endpoint in the paper is the actual trivial group. -/
theorem stochasticGroup_order_one : Nat.card (StochasticIsometryGroup 1)=1 := by
  have h := paperStochasticGroup_order 1 (by decide)
  norm_num [paperOrthogonalOrder] at h
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast h

/-- The k=2 endpoint has exactly two elements, with Sp(0) of order one. -/
theorem stochasticGroup_order_two : Nat.card (StochasticIsometryGroup 2)=2 := by
  have h := paperStochasticGroup_order 2 (by decide)
  norm_num [physicalSymplecticFactor] at h
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast h

end ExactCriticalCurve.Asymptotics
