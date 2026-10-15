import ExactCriticalCurve.Quantum.PhysicalFiniteSuccess

/-! Physical ordinary and exceptional Gram values and exact shortening. -/
noncomputable section
open Classical Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary

def ordinaryGramValue (n k r : ℕ) : ℝ :=
  physicalGramScale n k*(ordinarySectorScalarPolynomial k r).eval ((2:ℝ)^n)

def exceptionalGramValue (n k r : ℕ) : ℝ :=
  physicalGramScale n k*(exceptionalSectorScalarPolynomial k r).eval ((2:ℝ)^n)

theorem ordinaryGramValue_pos (n k r : ℕ) : 0<ordinaryGramValue n k r :=
  mul_pos (physicalGramScale_pos n k) (ordinarySectorScalarPolynomial_pos n k r)

theorem exceptionalGramValue_pos (n k r : ℕ) : 0<exceptionalGramValue n k r :=
  mul_pos (physicalGramScale_pos n k) (exceptionalSectorScalarPolynomial_pos n k r)

theorem physicalGramSectorValue_ordinary (n k : ℕ)
    (r : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)}) :
    physicalGramSectorValue n k (.inl r)=ordinaryGramValue n k r.val.val := rfl

theorem physicalGramSectorValue_exceptional (n k : ℕ)
    (r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)}) :
    physicalGramSectorValue n k (.inr r)=exceptionalGramValue n k r.val.val := rfl

theorem physicalGramScale_succ (n k : ℕ) (hk : 1≤k) :
    physicalGramScale n (k+1)*((2:ℝ)^n+(2:ℝ)^(k-1))=physicalGramScale n k := by
  have hp : (∏ j ∈ Finset.range k, ((2:ℝ)^n+(2:ℝ)^j))=
      (∏ j ∈ Finset.range (k-1), ((2:ℝ)^n+(2:ℝ)^j))*
        ((2:ℝ)^n+(2:ℝ)^(k-1)) := by
    calc
      _ = ∏ j ∈ Finset.range ((k-1)+1), ((2:ℝ)^n+(2:ℝ)^j) := by
        rw [Nat.sub_add_cancel hk]
      _ = _ := Finset.prod_range_succ _ _
  have hs : (2:ℝ)^n+(2:ℝ)^(k-1) ≠ 0 := by positivity
  simp only [physicalGramScale,Nat.add_sub_cancel,hp]
  field_simp

theorem exceptionalGramValue_succ (n k r : ℕ) (hk : 1≤k) :
    exceptionalGramValue n (k+1) (r+1)=ordinaryGramValue n k r := by
  unfold exceptionalGramValue ordinaryGramValue exceptionalSectorScalarPolynomial
  simp only [Nat.add_sub_cancel,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_C]
  rw [show k+1-2=k-1 by omega,← mul_assoc,physicalGramScale_succ n k hk]

theorem exceptionalGramValue_shortening (n k r : ℕ) (hk : 2≤k) (hr : 1≤r) :
    exceptionalGramValue n k r=ordinaryGramValue n (k-1) (r-1) := by
  have h := exceptionalGramValue_succ n (k-1) (r-1) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 1≤k),Nat.sub_add_cancel hr] using h

end ExactCriticalCurve.Quantum
