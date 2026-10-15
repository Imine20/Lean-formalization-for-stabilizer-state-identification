import StabilizerLearning.Quantum.JointProjector
import StabilizerLearning.Quantum.TensorProbability

/-! Pure-vector representatives of the original density matrices and their exact
tensor and Born/Gram identities. Global phases are choices, not new ensemble labels. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning.Quantum

variable {ι : Type*} [Fintype ι]

def pureVectorDensity (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec v (star v)

/-- A Hermitian rank-one matrix of trace one is an actual unit-vector density. -/
theorem exists_normalized_vector_of_hermitian_rank_one_trace_one
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hrank : A.rank = 1) (htrace : Matrix.trace A = 1) :
    ∃ v : ι → ℂ, dotProduct (star v) v = 1 ∧ A = pureVectorDensity v := by
  classical
  have hc : Fintype.card {i // hA.eigenvalues i ≠ 0} = 1 := by
    rw [← hA.rank_eq_card_non_zero_eigs, hrank]
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hc
  have hz (j : ι) (hj : j ≠ i.val) : hA.eigenvalues j = 0 := by
    by_contra hn
    exact hj (congrArg Subtype.val (hi ⟨j, hn⟩))
  have hone : hA.eigenvalues i.val = 1 := by
    have ht := hA.trace_eq_sum_eigenvalues
    rw [Finset.sum_eq_single i.val (fun j _ hj => by simp [hz j hj]) (by simp)] at ht
    have he : (hA.eigenvalues i.val : ℂ) = 1 := ht.symm.trans htrace
    exact_mod_cast he
  refine ⟨⇑(hA.eigenvectorBasis i.val), ?_, ?_⟩
  · rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i.val]
    norm_num
  · conv_lhs => rw [hA.spectral_theorem]
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, Function.comp_apply]
    rw [Finset.sum_eq_single i.val]
    · simp [hone, pureVectorDensity, Matrix.vecMulVec]
    · intro j _ hj
      simp [hz j hj]
    · simp

/-- Exact trace overlap of rank-one vector densities. -/
theorem trace_pureVectorDensity_mul (v w : ι → ℂ) :
    Matrix.trace (pureVectorDensity v * pureVectorDensity w) =
      (Complex.normSq (dotProduct (star v) w) : ℂ) := by
  rw [pureVectorDensity, pureVectorDensity, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_smul]
  have hc : dotProduct v (star w) = star (dotProduct (star v) w) := by
    rw [dotProduct_comm v, Matrix.star_dotProduct]
  rw [hc]
  exact Complex.mul_conj _

theorem born_pureVectorDensity (v w : ι → ℂ) :
    born (pureVectorDensity v) (pureVectorDensity w) =
      Complex.normSq (dotProduct (star v) w) := by
  unfold born
  rw [trace_pureVectorDensity_mul, Complex.ofReal_re]

def tensorVector (v : ι → ℂ) (k : ℕ) : (Fin k → ι) → ℂ :=
  fun x => ∏ i, v (x i)

omit [Fintype ι] in
/-- This includes zero copies and uses the original entrywise tensor power. -/
theorem tensorVector_density (v : ι → ℂ) (k : ℕ) :
    pureVectorDensity (tensorVector v k) = tensorPower (pureVectorDensity v) k := by
  ext x y
  simp [pureVectorDensity, tensorVector, tensorPower, Matrix.vecMulVec,
    Finset.prod_mul_distrib]

theorem tensorVector_inner (v w : ι → ℂ) (k : ℕ) :
    dotProduct (star (tensorVector v k)) (tensorVector w k) =
      dotProduct (star v) w ^ k := by
  classical
  simp only [dotProduct, tensorVector, Pi.star_apply, star_prod,
    ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin k) j => star (v j) * w j)]
  simp

theorem tensorVector_normalized (v : ι → ℂ)
    (hv : dotProduct (star v) v = 1) (k : ℕ) :
    dotProduct (star (tensorVector v k)) (tensorVector v k) = 1 := by
  rw [tensorVector_inner, hv, one_pow]

namespace StabilizerState

def stateVector (p n : ℕ) [Fact p.Prime] (x : StabilizerState p n) :
    Configuration p n → ℂ :=
  Classical.choose (exists_normalized_vector_of_hermitian_rank_one_trace_one
    x.val x.property.1.isHermitian x.property.2.2.1 x.property.2.1)

theorem stateVector_normalized (p n : ℕ) [Fact p.Prime] (x : StabilizerState p n) :
    dotProduct (star (stateVector p n x)) (stateVector p n x) = 1 :=
  (Classical.choose_spec (exists_normalized_vector_of_hermitian_rank_one_trace_one
    x.val x.property.1.isHermitian x.property.2.2.1 x.property.2.1)).1

theorem stateVector_density (p n : ℕ) [Fact p.Prime] (x : StabilizerState p n) :
    x.val = pureVectorDensity (stateVector p n x) :=
  (Classical.choose_spec (exists_normalized_vector_of_hermitian_rank_one_trace_one
    x.val x.property.1.isHermitian x.property.2.2.1 x.property.2.1)).2

theorem tensor_stateVector_density (p n : ℕ) [Fact p.Prime]
    (x : StabilizerState p n) (k : ℕ) :
    tensorPower x.val k = pureVectorDensity (tensorVector (stateVector p n x) k) := by
  rw [tensorVector_density, stateVector_density p n x]

theorem tensor_stateVector_normalized (p n : ℕ) [Fact p.Prime]
    (x : StabilizerState p n) (k : ℕ) :
    dotProduct (star (tensorVector (stateVector p n x) k))
      (tensorVector (stateVector p n x) k) = 1 :=
  tensorVector_normalized _ (stateVector_normalized p n x) k

theorem tensor_born_eq_normSq (p n : ℕ) [Fact p.Prime]
    (x y : StabilizerState p n) (k : ℕ) :
    born (tensorPower x.val k) (tensorPower y.val k) =
      Complex.normSq (dotProduct (star (tensorVector (stateVector p n x) k))
        (tensorVector (stateVector p n y) k)) := by
  rw [tensor_stateVector_density, tensor_stateVector_density, born_pureVectorDensity]

end StabilizerState

end StabilizerLearning.Quantum
