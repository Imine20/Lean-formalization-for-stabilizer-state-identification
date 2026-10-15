import ExactCriticalCurve.Quantum.CSSQuotientGroupReduction
import ExactCriticalCurve.Quantum.CSSFiltrationEndpoints
import ExactCriticalCurve.FiniteQuadratic.NonsingularWuAverage
import ExactCriticalCurve.FiniteQuadratic.SymplecticClosedIncrement

/-! Genuine CSS quotient reduction when the ambient weight is two modulo four. -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
open FiniteQuadratic.ModFourQuadraticSpace
variable {k r : ℕ}

theorem evenTwo_cast_two (hk : k%4=2) : (k : ZMod 4)=2 := by
  calc
    (k : ZMod 4)=((4*(k/4)+2 : ℕ) : ZMod 4) := congrArg (fun a : ℕ => (a : ZMod 4)) (by omega)
    _ = (4 : ZMod 4)*(k/4 : ℕ)+2 := by push_cast; rfl
    _ = 2 := by rw [show (4 : ZMod 4)=0 by decide,zero_mul,zero_add]

theorem evenTwo_cast_zero (hk : k%4=2) : (k : ZMod 2)=0 := by
  calc
    (k : ZMod 2)=((4*(k/4)+2 : ℕ) : ZMod 2) := congrArg (fun a : ℕ => (a : ZMod 2)) (by omega)
    _ = (4 : ZMod 2)*(k/4 : ℕ)+2 := by push_cast; rfl
    _ = 0 := by rw [show (4 : ZMod 2)=0 by decide,show (2 : ZMod 2)=0 by decide,zero_mul,zero_add]

theorem evenTwo_not_four_dvd (hk : k%4=2) : ¬4∣k := by
  intro h
  have h0 := Nat.mod_eq_zero_of_dvd h
  omega

theorem cssEvenTwo_halfForm_wu (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : k%4=2) :
    (cssFlagQuotientGeometry N hN).halfForm (cssFlagQuotientGeometry N hN).wu=1 := by
  rw [halfForm_apply,cssFlagQuotientGeometry_parity_wu,evenTwo_cast_zero hk,bitLift_zero,sub_zero]
  change Binary.StochasticCounting.halfEven (cssQuotientQuadratic N hN (cssQuotientWu N hN))=1
  rw [cssQuotientQuadratic_wu,evenTwo_cast_two hk]
  decide

def cssEvenTwoCompanion (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : k%4=2) :
    CSSQuotient N :=
  (NonsingularWu.exists_companion (cssFlagQuotientGeometry N hN).halfForm
    (cssFlagQuotientGeometry N hN).wu
    (cssQuotient_halfForm_nondegenerate N hN (evenTwo_cast_zero hk))
    (cssEvenTwo_halfForm_wu N hN hk)).choose

theorem cssEvenTwoCompanion_pairing (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : k%4=2) :
    (cssFlagQuotientGeometry N hN).halfForm.polarBilin (cssFlagQuotientGeometry N hN).wu
      (cssEvenTwoCompanion N hN hk)=1 :=
  (NonsingularWu.exists_companion _ _ (cssQuotient_halfForm_nondegenerate N hN (evenTwo_cast_zero hk))
    (cssEvenTwo_halfForm_wu N hN hk)).choose_spec

abbrev CSSEvenTwoCore (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : k%4=2) :=
  NonsingularWu.complement (cssFlagQuotientGeometry N hN).halfForm
    (cssFlagQuotientGeometry N hN).wu (cssEvenTwoCompanion N hN hk)

def cssEvenTwoPairing (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : k%4=2) :
    LinearMap.BilinForm (ZMod 2) (CSSEvenTwoCore N hN hk) :=
  NonsingularWu.complementPairing (cssFlagQuotientGeometry N hN).halfForm
    (cssFlagQuotientGeometry N hN).wu (cssEvenTwoCompanion N hN hk)

theorem cssEvenTwoPairing_isAlt (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : k%4=2) : (cssEvenTwoPairing N hN hk).IsAlt :=
  NonsingularWu.complementPairing_isAlt _ _ _

theorem cssEvenTwoPairing_nondegenerate (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : k%4=2) :
    LinearMap.BilinForm.Nondegenerate (cssEvenTwoPairing N hN hk) :=
  NonsingularWu.complementPairing_nondegenerate _ _ _
    (cssQuotient_halfForm_nondegenerate N hN (evenTwo_cast_zero hk))
    (cssEvenTwoCompanion_pairing N hN hk)

theorem cssEvenTwoCore_finrank_add (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : k%4=2) :
    finrank (ZMod 2) (CSSEvenTwoCore N hN hk)+2+2*finrank (ZMod 2) N=k := by
  have hd := NonsingularWu.complement_finrank_add_two
    (cssFlagQuotientGeometry N hN).halfForm (cssFlagQuotientGeometry N hN).wu
    (cssEvenTwoCompanion N hN hk) (cssEvenTwoCompanion_pairing N hN hk)
  have hq := cssQuotient_finrank_add N hN
  change finrank (ZMod 2) (CSSEvenTwoCore N hN hk)+2=finrank (ZMod 2) (CSSQuotient N) at hd
  omega

theorem cssEvenTwo_quotientFixed_dimension (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : k%4=2) :
    (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N hN).mulVecLin) : ℚ)=
      ((2 : ℚ)^n*((2 : ℚ)^n+1)/2)*
        ((∑ h : BinarySymplecticIsometryGroup (cssEvenTwoPairing N hN hk),
          ((2 : ℚ)^n)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSEvenTwoCore N hN hk) h)) /
            (Nat.card (BinarySymplecticIsometryGroup (cssEvenTwoPairing N hN hk)) : ℚ)) := by
  rw [cssQuotientFixedDimension_even_reduction n N hN (evenTwo_cast_zero hk),Nat.card_eq_fintype_card]
  exact NonsingularWu.stabilizer_fixedSpace_average
    (cssFlagQuotientGeometry N hN).halfForm (cssFlagQuotientGeometry N hN).wu
    (cssEvenTwoCompanion N hN hk) (cssEvenTwoCompanion_pairing N hN hk)
    (cssQuotient_halfForm_nondegenerate N hN (evenTwo_cast_zero hk))
    (cssEvenTwo_halfForm_wu N hN hk) ((2 : ℚ)^n)

end ExactCriticalCurve.Quantum
