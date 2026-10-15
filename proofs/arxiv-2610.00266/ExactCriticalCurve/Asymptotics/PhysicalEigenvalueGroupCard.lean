import ExactCriticalCurve.Binary.StochasticOrthogonalReduction
import ExactCriticalCurve.FiniteQuadratic.OrthogonalClosedIncrement
import ExactCriticalCurve.FiniteQuadratic.SymplecticClosedIncrement
import ExactCriticalCurve.FiniteQuadratic.BinarySingularStabilizer
import ExactCriticalCurve.FiniteQuadratic.NonsingularWuAverage

/-! Genuine stochastic group orders, without a presupposed classical group model. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
open Binary FiniteQuadratic

/-- The signed numerical orthogonal factor. Its equality to a group cardinal
is proved below for an actual nondegenerate quadratic form. -/
def physicalOrthogonalFactor (m : ℕ) (σ : ℝ) : ℝ :=
  2*(2:ℝ)^(m*(m-1))*((2:ℝ)^m-σ)*
    ∏ j ∈ Finset.range (m-1), ((4:ℝ)^(j+1)-1)

def physicalSymplecticFactor (m : ℕ) : ℝ :=
  (2:ℝ)^(m*m)*∏ j ∈ Finset.range m, ((4:ℝ)^(j+1)-1)

theorem actualOrthogonal_card_signed
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (m : ℕ) (hm : 0<m) (hd : finrank (ZMod 2) V=2*m) :
    ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
      (Nat.card (BinaryQuadraticIsometryGroup Q) : ℝ)=physicalOrthogonalFactor m σ := by
  have hg := binaryQuadraticGaussInteger_eq_signed_pow Q hQ m hd
  have hs : ∃ σ : ℚ, (σ=1 ∨ σ= -1) ∧
      binaryQuadraticGaussSum Q=(σ:ℂ)*(2:ℂ)^m := by
    rcases hg with hp | hn
    · refine ⟨1,Or.inl rfl,?_⟩
      rw [← binaryQuadraticGaussInteger_cast,hp]
      norm_num
    · refine ⟨-1,Or.inr rfl,?_⟩
      rw [← binaryQuadraticGaussInteger_cast,hn]
      norm_num
  obtain ⟨σ,hσ,hg⟩ := hs
  refine ⟨σ,?_,?_⟩
  · rcases hσ with rfl | rfl <;> norm_num
  · have hc := congrArg (fun x : ℚ => (x:ℝ))
      (binaryQuadraticIsometryGroup_card Q hQ m hm hd σ hσ hg)
    simpa [physicalOrthogonalFactor] using hc

theorem actualSymplectic_card_real
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (m : ℕ) (hd : finrank (ZMod 2) V=2*m) :
    (Nat.card (BinarySymplecticIsometryGroup B) : ℝ)=physicalSymplecticFactor m := by
  have hc := congrArg (fun x : ℚ => (x:ℝ))
    (binarySymplecticIsometryGroup_card B hB hBn m hd)
  simpa [physicalSymplecticFactor] using hc

/-- Every actual stochastic group of dimension at least three has one of the
three orders obtained from the genuine Wu decomposition. The sign is furnished
by the actual quadratic form, never a classification premise. -/
theorem actualStochasticGroup_card_cases (k : ℕ) (hk : 3≤k) :
    let m := (k-1)/2
    ((k%2=1 ∧ ∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
      (Nat.card (StochasticIsometryGroup k) : ℝ)=physicalOrthogonalFactor m σ) ∨
     (k%2=0 ∧
       ((∃ σ : ℝ, (σ=1 ∨ σ= -1) ∧
          (Nat.card (StochasticIsometryGroup k) : ℝ)=
            (2:ℝ)^(2*m)*physicalOrthogonalFactor m σ) ∨
        (Nat.card (StochasticIsometryGroup k) : ℝ)=2*physicalSymplecticFactor m))) := by
  dsimp only
  let m := (k-1)/2
  have hm : 0<m := by dsimp [m]; omega
  by_cases hodd : k%2=1
  · left
    refine ⟨hodd,?_⟩
    have ho : (k:ZMod 2)=1 := by
      apply ZMod.val_injective 2
      simpa using hodd
    have hd : finrank (ZMod 2) (evenWeightSpace k)=2*m := by
      have h := evenWeightSpace_finrank_add_one ho
      dsimp [m]
      omega
    obtain ⟨σ,hσ,hcard⟩ := actualOrthogonal_card_signed (evenWeightHalfForm k)
      (evenWeightHalfForm_nondegenerate ho) m hm hd
    refine ⟨σ,hσ,?_⟩
    rw [Nat.card_congr (stochasticOddOrthogonalEquiv ho).toEquiv]
    exact hcard
  · right
    have heven : k%2=0 := by omega
    refine ⟨heven,?_⟩
    have he : (k:ZMod 2)=0 := by
      apply ZMod.val_injective 2
      simpa using heven
    let Q := stochasticHalfForm k
    let w := allOnes k
    have hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin :=
      stochasticHalfForm_nondegenerate he
    have hcard : Nat.card (StochasticIsometryGroup k)=
        Nat.card (MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w) :=
      Nat.card_congr (stochasticEvenOrthogonalEquiv he).toEquiv
    by_cases hw : Q w=0
    · left
      have hwne : w≠0 := by
        intro h
        have hi := congrFun h ⟨0,by omega⟩
        exact one_ne_zero hi
      obtain ⟨v,hv,hp⟩ := exists_binaryHyperbolicPartner Q hQ w hwne hw
      have hd : finrank (ZMod 2) (binaryHyperbolicComplement Q w v)=2*m := by
        have h := binaryHyperbolicComplement_finrank Q w v hp
        have hv : finrank (ZMod 2) (BinaryVector k)=k := by simp [BinaryVector]
        rw [hv] at h
        dsimp [m]
        omega
      obtain ⟨σ,hσ,hc⟩ := actualOrthogonal_card_signed (binaryHyperbolicComplementForm Q w v)
        (binaryHyperbolicComplement_nondegenerate Q hQ w v hp) m hm hd
      refine ⟨σ,hσ,?_⟩
      rw [hcard,binarySingularStabilizer_card Q hQ w v hw hv hp,hd]
      push_cast
      rw [hc,mul_comm]
    · right
      have hw1 : Q w=1 := by
        generalize Q w=a at hw ⊢
        fin_cases a <;> simp_all
      obtain ⟨v,hp⟩ := NonsingularWu.exists_companion Q w hQ hw1
      have hd : finrank (ZMod 2) (NonsingularWu.complement Q w v)=2*m := by
        have h := NonsingularWu.complement_finrank_add_two Q w v hp
        have hv : finrank (ZMod 2) (BinaryVector k)=k := by simp [BinaryVector]
        rw [hv] at h
        dsimp [m]
        omega
      have hc := actualSymplectic_card_real (NonsingularWu.complementPairing Q w v)
        (NonsingularWu.complementPairing_isAlt Q w v)
        (NonsingularWu.complementPairing_nondegenerate Q w v hQ hp) m hd
      have hg := NonsingularWu.stabilizer_card Q w v hp hQ hw1
      have hgN : Nat.card (NonsingularWu.stabilizer Q w)=
          2*Nat.card (BinarySymplecticIsometryGroup (NonsingularWu.complementPairing Q w v)) := by
        simpa only [← Nat.card_eq_fintype_card] using hg
      rw [hcard,hgN]
      push_cast
      exact congrArg (fun x:ℝ => 2*x) hc

end ExactCriticalCurve.Asymptotics
