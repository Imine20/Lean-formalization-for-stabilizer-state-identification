import ExactCriticalCurve.Quantum.PhysicalSectorRankPolynomialRaw

/-! A real rank polynomial for every actual physical sector, valid for all n. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k : ℕ}
set_option maxHeartbeats 3000000

def physicalSectorRankPolynomialQ (hk : 0<k) : PhysicalSectorLabel k → ℚ[X]
  | .inl r => if 4∣k then evenZeroGradeRankPolynomialQ k r.val.val
      else if k%4=2 then evenTwoGradeRankPolynomialQ k r.val.val
      else oddGradeRankPolynomialQ k r.val.val
  | .inr r => exceptionalGradeRankPolynomialQ k r.val.val

def physicalSectorRankPolynomial (hk : 0<k) (a : PhysicalSectorLabel k) : ℝ[X] :=
  (physicalSectorRankPolynomialQ hk a).map (Rat.castHom ℝ)

theorem physicalSectorRankPolynomialQ_eval (n : ℕ) (hk : 0<k) (a : PhysicalSectorLabel k) :
    (physicalSectorRankPolynomialQ hk a).eval ((2 : ℚ)^n)=
      (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) : ℚ) := by
  cases a with
  | inl r =>
    let N := Classical.choice r.property
    by_cases h4 : 4∣k
    · simp only [physicalSectorRankPolynomialQ,if_pos h4,physicalSectorGrade]
      exact evenZeroGradeRankPolynomialQ_eval n r.val.val hk h4
    · by_cases h2 : k%4=2
      · simp only [physicalSectorRankPolynomialQ,if_neg h4,if_pos h2,physicalSectorGrade]
        exact evenTwoGradeRankPolynomialQ_eval n N h2
      · have hm4 : k%4≠0 := fun h => h4 (Nat.dvd_of_mod_eq_zero h)
        have hmod : k%2=1 := by omega
        have ho : (k : ZMod 2)=1 := by
          apply ZMod.val_injective
          simpa using hmod
        simp only [physicalSectorRankPolynomialQ,if_neg h4,if_neg h2,physicalSectorGrade]
        exact oddGradeRankPolynomialQ_eval n ho N
  | inr r =>
    obtain ⟨N⟩ := r.property
    simp only [physicalSectorRankPolynomialQ,physicalSectorGrade]
    exact exceptionalGradeRankPolynomialQ_eval n hk (exceptionalDefect_four_dvd N)
      (exceptionalDefect_rank_pos hk N)

theorem physicalSectorRankPolynomial_eval (n : ℕ) (hk : 0<k) (a : PhysicalSectorLabel k) :
    (physicalSectorRankPolynomial hk a).eval ((2 : ℝ)^n)=
      (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) : ℝ) := by
  rw [physicalSectorRankPolynomial,rationalPolynomial_map_real_eval,physicalSectorRankPolynomialQ_eval]
  norm_cast

end ExactCriticalCurve.Quantum
