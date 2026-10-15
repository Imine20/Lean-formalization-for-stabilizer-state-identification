import ExactCriticalCurve.Quantum.PhysicalSectorPowerTraces

/-! Polynomial uniqueness for the actual relation trace. The rank-polynomial
interface in these lemmas is discharged by the separate actual rank construction;
these interface lemmas alone are not the paper's finite-spectrum theorem. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

def physicalTracePolynomial (k : ℕ) (M : PhysicalSectorLabel k → ℝ[X]) (p : ℕ) : ℂ[X] :=
  ∑ a : PhysicalSectorLabel k, (M a).map Complex.ofRealHom *
    ((physicalSectorScalarPolynomial k a).map Complex.ofRealHom)^p

theorem physicalTracePolynomial_eval (M : PhysicalSectorLabel k → ℝ[X]) (n p : ℕ) :
    (physicalTracePolynomial k M p).eval ((2:ℂ)^n)=
      ∑ a : PhysicalSectorLabel k, (Complex.ofReal ((M a).eval ((2:ℝ)^n))) *
        (Complex.ofReal ((physicalSectorScalarPolynomial k a).eval ((2:ℝ)^n)))^p := by
  simp only [physicalTracePolynomial,Polynomial.eval_finset_sum,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_map]
  apply Finset.sum_congr rfl
  intro a _
  have hx : (2:ℂ)^n=Complex.ofRealHom ((2:ℝ)^n) := by simp
  rw [hx,Polynomial.eval₂_at_apply,Polynomial.eval₂_at_apply]
  rfl

theorem relationTracePolynomial_eq_physicalTracePolynomial
    (hk : 0<k) (M : PhysicalSectorLabel k → ℝ[X])
    (hM : ∀ n (a : PhysicalSectorLabel k), (M a).eval ((2:ℝ)^n)=
      (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ))
    (p : ℕ) (hp : 0<p) :
    (relationTracePolynomial (fun T : StochasticLagrangian k => T.carrier) p).map
      (Nat.castRingHom ℂ)=physicalTracePolynomial k M p := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun j : ℕ => (2:ℂ)^(k+j)) := by
    intro a b he
    change (2:ℂ)^(k+a)=(2:ℂ)^(k+b) at he
    have hn : (2:ℕ)^(k+a)=2^(k+b) := by exact_mod_cast he
    have hh := Nat.pow_right_injective (by omega) hn
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨j,rfl⟩
  simp only [Set.mem_setOf_eq,Polynomial.eval_map,physicalTracePolynomial_eval,hM,
    Complex.ofReal_natCast]
  exact relationTracePolynomial_stable_sectors hk (Nat.le_add_right k j) p hp

theorem stochasticRelationSum_pos_pow_trace_of_rank_polynomials
    (hk : 0<k) (M : PhysicalSectorLabel k → ℝ[X])
    (hM : ∀ n (a : PhysicalSectorLabel k), (M a).eval ((2:ℝ)^n)=
      (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ))
    (n p : ℕ) (hp : 0<p) :
    Matrix.trace (stochasticRelationSum n k ^ p)=
      ∑ a : PhysicalSectorLabel k,
        (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℂ) *
          (Complex.ofReal ((physicalSectorScalarPolynomial k a).eval ((2:ℝ)^n)))^p := by
  have he := congrArg (fun P : ℂ[X] => P.eval ((2:ℂ)^n))
    (relationTracePolynomial_eq_physicalTracePolynomial hk M hM p hp)
  dsimp only at he
  rw [Polynomial.eval_map,physicalTracePolynomial_eval] at he
  simp only [hM,Complex.ofReal_natCast] at he
  rw [← relationOperator_sum_pow_trace] at he
  exact he

end ExactCriticalCurve.Quantum
