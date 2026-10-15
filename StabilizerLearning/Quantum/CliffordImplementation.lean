import StabilizerLearning.Quantum.AssignmentExistence
import Mathlib.LinearAlgebra.UnitaryGroup

/-! Every linear symplectic map is implemented by a unitary for the literal XZ
section. The proof uses simultaneous eigenvectors on matrix space and the scalar
commutant of the complete Pauli family, uniformly in all prime characteristics. -/
noncomputable section
open scoped BigOperators ComplexOrder Matrix
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- The complete concrete Pauli family has scalar commutant. -/
theorem pauli_commutant_scalar
    (A : Matrix (Configuration p n) (Configuration p n) ℂ)
    (hA : ∀ z, A * pauli p n z = pauli p n z * A) :
    ∃ c : ℂ, A = c • 1 := by
  classical
  have hz (v : Configuration p n) : pauli p n (0, v) =
      Matrix.diagonal (fun x => rootPhase p (dotProduct v x)) := by
    ext x y
    by_cases h : x = y
    · subst y; simp [pauli]
    · simp [pauli, h]
  have hoff (x y : Configuration p n) (hxy : x ≠ y) : A x y = 0 := by
    by_contra hne
    apply hxy
    funext i
    have h := congrFun (congrFun (hA (0, Pi.single i 1)) x) y
    rw [hz, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hp : rootPhase p (y i) = rootPhase p (x i) := by
      apply mul_left_cancel₀ hne
      simpa [single_dotProduct, mul_comm] using h
    exact (rootPhase_injective p hp).symm
  have hd : A = Matrix.diagonal (fun x => A x x) := by
    ext x y
    by_cases hxy : x = y
    · subst y; simp
    · simp [hxy, hoff x y hxy]
  have hconst (x : Configuration p n) : A x x = A 0 0 := by
    have h := congrFun (congrFun (hA (x, 0)) x) 0
    rw [hd, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    simpa [pauli] using h
  refine ⟨A 0 0, ?_⟩
  rw [hd]
  ext x y
  simp [Matrix.diagonal_apply, Matrix.one_apply, hconst]

section MatrixSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left and right multiplication by unitary matrices preserves Hilbert--Schmidt
length, so every nonzero eigenmatrix has a unit-modulus eigenvalue. -/
theorem unitary_sandwich_eigenvalue
    (L R T : Matrix ι ι ℂ)
    (hL : Lᴴ * L = 1) (hR : Rᴴ * R = 1)
    (hT : T ≠ 0) (c : ℂ) (he : L * T * Rᴴ = c • T) :
    star c * c = 1 := by
  have ht : Matrix.trace (Tᴴ * T) ≠ 0 :=
    fun h => hT (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h)
  have hh : Matrix.trace ((L * T * Rᴴ)ᴴ * (L * T * Rᴴ)) =
      Matrix.trace (Tᴴ * T) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      Matrix.trace (R * (Tᴴ * Lᴴ) * (L * T * Rᴴ)) =
          Matrix.trace (R * (Tᴴ * (Lᴴ * L) * T) * Rᴴ) := by
            congr 1; simp only [mul_assoc]
      _ = Matrix.trace (R * (Tᴴ * T) * Rᴴ) := by rw [hL]; simp
      _ = Matrix.trace ((Rᴴ * R) * (Tᴴ * T)) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (Tᴴ * T) := by rw [hR, one_mul]
  rw [he, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul] at hh
  apply mul_right_cancel₀ ht
  simpa only [smul_eq_mul, mul_assoc, one_mul] using hh

end MatrixSpace


/-- A conjugation operator comparing the original section with its symplectic image. -/
def pauliIntertwinerOperator
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n) (z : PhaseSpace p n) :
    Module.End ℂ (Matrix (Configuration p n) (Configuration p n) ℂ) where
  toFun T := pauli p n (g z) * T * (pauli p n z)ᴴ
  map_add' T S := by simp only [mul_add, add_mul]
  map_smul' c T := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- The two Pauli cocycles cancel their alternating part under a symplectic map. -/
theorem pauliIntertwinerOperator_mul
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n) (z w : PhaseSpace p n) :
    pauliIntertwinerOperator p n g z * pauliIntertwinerOperator p n g w =
      (sectionCocycle p n (g z) (g w) * star (sectionCocycle p n z w)) •
        pauliIntertwinerOperator p n g (z + w) := by
  apply LinearMap.ext
  intro T
  change pauli p n (g z) * (pauli p n (g w) * T * (pauli p n w)ᴴ) *
      (pauli p n z)ᴴ = _
  have hr : pauli p n (g z) * (pauli p n (g w) * T * (pauli p n w)ᴴ) *
      (pauli p n z)ᴴ = (pauli p n (g z) * pauli p n (g w)) * T *
        (pauli p n z * pauli p n w)ᴴ := by
    simp only [Matrix.conjTranspose_mul, mul_assoc]
  rw [hr, pauli_mul, pauli_mul, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.smul_mul, smul_smul, LinearMap.smul_apply,
    pauliIntertwinerOperator, LinearMap.coe_mk, AddHom.coe_mk, map_add]
  rw [mul_comm (star (sectionCocycle p n z w))]

/-- Symplecticity makes the comparison conjugation operators commute. -/
theorem pauliIntertwinerOperator_commute
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (z w : PhaseSpace p n) :
    Commute (pauliIntertwinerOperator p n g z) (pauliIntertwinerOperator p n g w) := by
  change _ * _ = _ * _
  rw [pauliIntertwinerOperator_mul, pauliIntertwinerOperator_mul]
  have hdot : dotProduct (g z).2 (g w).1 - dotProduct z.2 w.1 =
      dotProduct (g w).2 (g z).1 - dotProduct w.2 z.1 := by
    have h := hg z w
    change dotProduct (g z).1 (g w).2 - dotProduct (g z).2 (g w).1 =
      dotProduct z.1 w.2 - dotProduct z.2 w.1 at h
    rw [dotProduct_comm (g z).1, dotProduct_comm z.1] at h
    linear_combination -h
  have hc : sectionCocycle p n (g z) (g w) * star (sectionCocycle p n z w) =
      sectionCocycle p n (g w) (g z) * star (sectionCocycle p n w z) := by
    simp only [sectionCocycle, rootPhase_star, ← rootPhase_add, ← sub_eq_add_neg]
    rw [hdot]
  rw [hc, add_comm z w]

/-- An unconditional nonzero intertwiner for every symplectic map. -/
theorem exists_pauli_eigenmatrix
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) :
    ∃ T : Matrix (Configuration p n) (Configuration p n) ℂ,
      T ≠ 0 ∧ ∃ c : PhaseSpace p n → ℂ,
        (∀ z, star (c z) * c z = 1) ∧
        ∀ z, pauli p n (g z) * T * (pauli p n z)ᴴ = c z • T := by
  classical
  obtain ⟨T, hT, he⟩ := exists_common_eigenvector (pauliIntertwinerOperator p n g)
    (pauliIntertwinerOperator_commute p n g hg)
  choose c hc using he
  refine ⟨T, hT, c, ?_, hc⟩
  intro z
  exact unitary_sandwich_eigenvalue _ _ T
    (pauli_conjTranspose_mul_self p n (g z))
    (pauli_conjTranspose_mul_self p n z) hT (c z) (hc z)


/-- A common eigenmatrix has scalar Gram matrix. -/
theorem pauli_eigenmatrix_gram_scalar
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (T : Matrix (Configuration p n) (Configuration p n) ℂ)
    (c : PhaseSpace p n → ℂ) (hc : ∀ z, star (c z) * c z = 1)
    (he : ∀ z, pauli p n (g z) * T * (pauli p n z)ᴴ = c z • T) :
    ∃ a : ℂ, Tᴴ * T = a • 1 := by
  apply pauli_commutant_scalar p n
  intro z
  have h := congrArg (fun A => Aᴴ * A) (he z)
  have hl : (pauli p n (g z) * T * (pauli p n z)ᴴ)ᴴ *
      (pauli p n (g z) * T * (pauli p n z)ᴴ) =
      pauli p n z * (Tᴴ * T) * (pauli p n z)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = pauli p n z * Tᴴ *
          ((pauli p n (g z))ᴴ * pauli p n (g z)) * T * (pauli p n z)ᴴ := by
            simp only [mul_assoc]
      _ = _ := by rw [pauli_conjTranspose_mul_self]; simp only [mul_one, mul_assoc]
  dsimp only at h
  rw [hl, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hc z, one_smul] at h
  have hh := congrArg (fun A => A * pauli p n z) h
  simpa only [mul_assoc, pauli_conjTranspose_mul_self, mul_one] using hh.symm

/-- A nonzero matrix with scalar Gram matrix is a nonzero scalar multiple of a unitary. -/
theorem exists_unitary_smul_of_gram_scalar
    (T : Matrix (Configuration p n) (Configuration p n) ℂ) (hT : T ≠ 0)
    (hgram : ∃ a : ℂ, Tᴴ * T = a • 1) :
    ∃ r : ℂ, r ≠ 0 ∧ (r • T)ᴴ * (r • T) = 1 := by
  classical
  obtain ⟨a, ha⟩ := hgram
  have hap : 0 ≤ a := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self T).2
      (Pi.single (0 : Configuration p n) 1)
    rw [ha, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul] at h
    simpa [dotProduct, Pi.single_apply, Pi.star_apply] using h
  have ha0 : a ≠ 0 := by
    intro h
    apply hT
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    simp [ha, h]
  have har : 0 ≤ a.re := (Complex.nonneg_iff.mp hap).1
  have hai : a.im = 0 := (Complex.nonneg_iff.mp hap).2.symm
  let d : ℂ := (Real.sqrt a.re : ℝ)
  have hdstar : star d = d := by simp [d]
  have hdsq : d * d = a := by
    apply Complex.ext
    · simpa [d] using Real.mul_self_sqrt har
    · simp [d, hai]
  have hd0 : d ≠ 0 := by
    intro h
    apply ha0
    rw [← hdsq, h, zero_mul]
  refine ⟨d⁻¹, inv_ne_zero hd0, ?_⟩
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    ha, smul_smul, smul_smul]
  have hcoeff : star (d⁻¹) * d⁻¹ * a = 1 := by
    simp only [star_inv₀, hdstar, ← hdsq]
    field_simp
  rw [hcoeff, one_smul]


/-- A symplectic map is implemented by an actual unitary, up to unit section phases. -/
theorem exists_unitary_pauli_covariance
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) :
    ∃ U : Matrix.unitaryGroup (Configuration p n) ℂ,
      ∃ τ : PhaseSpace p n → ℂ, (∀ z, ‖τ z‖ = 1) ∧
        ∀ z, U.val * pauli p n z * U.valᴴ = τ z • pauli p n (g z) := by
  classical
  obtain ⟨T, hT, c, hc, he⟩ := exists_pauli_eigenmatrix p n g hg
  obtain ⟨r, _, hr⟩ := exists_unitary_smul_of_gram_scalar p n T hT
    (pauli_eigenmatrix_gram_scalar p n g T c hc he)
  let U : Matrix.unitaryGroup (Configuration p n) ℂ :=
    ⟨r • T, Matrix.mem_unitaryGroup_iff'.mpr hr⟩
  have hU : U.val * U.valᴴ = 1 := Matrix.mul_eq_one_comm.mp hr
  refine ⟨U, fun z => (c z)⁻¹, ?_, ?_⟩
  · intro z
    have h := congrArg norm (hc z)
    simp only [norm_mul, norm_star, norm_one] at h
    have hn : ‖c z‖ = 1 := by nlinarith [norm_nonneg (c z)]
    simp [hn]
  · intro z
    have hc0 : c z ≠ 0 := by
      intro h
      have hh := hc z
      simp [h] at hh
    have heU : pauli p n (g z) * U.val * (pauli p n z)ᴴ = c z • U.val := by
      change pauli p n (g z) * (r • T) * (pauli p n z)ᴴ = c z • (r • T)
      rw [Matrix.mul_smul, Matrix.smul_mul, he z, smul_smul, smul_smul, mul_comm r]
    have h := congrArg (fun A => A * pauli p n z * U.valᴴ) heU
    dsimp only at h
    have hl : pauli p n (g z) * U.val * (pauli p n z)ᴴ * pauli p n z * U.valᴴ =
        pauli p n (g z) := by
      calc
        _ = pauli p n (g z) * (U.val *
            ((pauli p n z)ᴴ * pauli p n z) * U.valᴴ) := by simp only [mul_assoc]
        _ = _ := by rw [pauli_conjTranspose_mul_self, mul_one, hU, mul_one]
    rw [hl, Matrix.smul_mul, Matrix.smul_mul] at h
    have hh := congrArg (fun A => (c z)⁻¹ • A) h
    simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using hh.symm

/-- The section cocycle identity is forced by the actual unitary covariance. -/
theorem unitary_pauli_covariance_cocycle
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (U : Matrix.unitaryGroup (Configuration p n) ℂ)
    (τ : PhaseSpace p n → ℂ)
    (hcov : ∀ z, U.val * pauli p n z * U.valᴴ = τ z • pauli p n (g z))
    (z w : PhaseSpace p n) :
    sectionCocycle p n z w * τ (z + w) =
      τ z * τ w * sectionCocycle p n (g z) (g w) := by
  classical
  have hU : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  have hprod : (U.val * pauli p n z * U.valᴴ) *
      (U.val * pauli p n w * U.valᴴ) = U.val *
      (pauli p n z * pauli p n w) * U.valᴴ := by
    calc
      _ = U.val * pauli p n z * (U.valᴴ * U.val) * pauli p n w * U.valᴴ := by
        simp only [mul_assoc]
      _ = _ := by rw [hU]; simp only [mul_one, mul_assoc]
  rw [hcov z, hcov w, Matrix.smul_mul, Matrix.mul_smul, pauli_mul,
    pauli_mul, Matrix.mul_smul, Matrix.smul_mul, hcov (z + w)] at hprod
  simp only [smul_smul, ← map_add] at hprod
  have hh := congrFun (congrFun hprod (g (z + w)).1) 0
  simpa [pauli, mul_comm, mul_left_comm, mul_assoc] using hh.symm

/-- Finite Pauli Clifford implementability for every prime (including two) and
all dimensions (including zero), with the exact XZ-section cocycle correction. -/
theorem exists_unitary_pauli_implementation
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) :
    ∃ U : Matrix.unitaryGroup (Configuration p n) ℂ,
      ∃ τ : PhaseSpace p n → ℂ, (∀ z, ‖τ z‖ = 1) ∧
        (∀ z, U.val * pauli p n z * U.valᴴ = τ z • pauli p n (g z)) ∧
        (∀ z w, sectionCocycle p n z w * τ (z + w) =
          τ z * τ w * sectionCocycle p n (g z) (g w)) := by
  obtain ⟨U, τ, hτ, hcov⟩ := exists_unitary_pauli_covariance p n g hg
  exact ⟨U, τ, hτ, hcov, unitary_pauli_covariance_cocycle p n g U τ hcov⟩

end StabilizerLearning.Quantum
