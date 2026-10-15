import ExactCriticalCurve.Quantum.StabilizerGroup

/-! The concrete computational-basis stabilizer, including zero qubits. -/
noncomputable section
open scoped BigOperators
open Matrix
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

/-- All actual Z Paulis with positive phase. -/
def computationalPauliGroup (n : ℕ) : Subgroup (PauliLabel n) where
  carrier := {g | g.phase = 0 ∧ g.shift = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    intro g h hg hh
    change (pauliLabelMul g h).phase = 0 ∧ (pauliLabelMul g h).shift = 0
    simp [pauliLabelMul, hg.1, hg.2, hh.1, hh.2]
  inv_mem' := by
    intro g hg
    change (pauliLabelInv g).phase = 0 ∧ (pauliLabelInv g).shift = 0
    simp [pauliLabelInv, hg.1, hg.2]

/-- The complete subgroup is parametrized without duplicates by its Z exponents. -/
def computationalPauliGroupEquiv (n : ℕ) :
    computationalPauliGroup n ≃ BinaryVector n where
  toFun g := g.val.clock
  invFun b := ⟨⟨0, 0, b⟩, rfl, rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply PauliLabel.ext
    · exact g.property.1.symm
    · exact g.property.2.symm
    · rfl
  right_inv b := rfl

theorem computationalPauliGroup_card (n : ℕ) :
    Nat.card (computationalPauliGroup n) = 2 ^ n := by
  rw [Nat.card_congr (computationalPauliGroupEquiv n)]
  simp [BinaryVector, Nat.card_eq_fintype_card]

/-- A concrete inhabitant of the exact maximal proper Pauli subgroup type. -/
def computationalStabilizerGroup (n : ℕ) : StabilizerGroup n where
  carrier := computationalPauliGroup n
  phase_free := fun _ hg _ _ => hg.1
  card_eq := computationalPauliGroup_card n

instance nonemptyStabilizerGroup (n : ℕ) : Nonempty (StabilizerGroup n) :=
  ⟨computationalStabilizerGroup n⟩

/-- The physical computational-basis vector, independently of the spectral gauge choice. -/
def computationalZeroVector (n : ℕ) : BinaryVector n → ℂ :=
  fun x => if x = 0 then 1 else 0

theorem computationalZeroVector_normalized (n : ℕ) :
    star (computationalZeroVector n) ⬝ᵥ computationalZeroVector n = 1 := by
  classical
  simp [computationalZeroVector, dotProduct, Pi.star_apply]

theorem computationalZeroVector_fixed (n : ℕ) (g : computationalPauliGroup n) :
    pauliOperator g.val *ᵥ computationalZeroVector n = computationalZeroVector n := by
  classical
  funext x
  simp [Matrix.mulVec, dotProduct, computationalZeroVector, pauliOperator, pauliMatrix,
    g.property.1, g.property.2]

/-- The chosen vector spans the actual computational stabilizer projection. -/
theorem computationalStabilizerProjection (n : ℕ) :
    stabilizerProjection (computationalStabilizerGroup n) =
      Matrix.vecMulVec (computationalZeroVector n) (star (computationalZeroVector n)) := by
  classical
  let S := computationalStabilizerGroup n
  let v := stabilizerVector S
  let z := computationalZeroVector n
  have hzfix : stabilizerProjection S *ᵥ z = z := by
    exact (finiteGroupProjection_mulVec_eq_iff S.representation z).mpr
      (computationalZeroVector_fixed n)
  have hv : star v ⬝ᵥ v = 1 := stabilizerVector_normalized S
  have hz : star z ⬝ᵥ z = 1 := computationalZeroVector_normalized n
  have heq : z = (star v ⬝ᵥ z) • v := by
    rw [← stabilizerVector_projector S, Matrix.vecMulVec_mulVec] at hzfix
    simpa using hzfix.symm
  let c : ℂ := star v ⬝ᵥ z
  have hc : Complex.normSq c = 1 := by
    have ht := hz
    rw [heq] at ht
    have hm : star (c • v) ⬝ᵥ (c • v) = (Complex.normSq c : ℂ) := by
      simp only [star_smul, smul_dotProduct, dotProduct_smul, hv, smul_eq_mul, mul_one]
      rw [Complex.star_def, Complex.mul_conj]
    change star (c • v) ⬝ᵥ (c • v) = 1 at ht
    rw [hm] at ht
    simpa using congrArg Complex.re ht
  change stabilizerProjection S = Matrix.vecMulVec z (star z)
  rw [← stabilizerVector_projector S]
  change Matrix.vecMulVec v (star v) = Matrix.vecMulVec z (star z)
  rw [heq]
  ext x y
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, StarMul.star_mul, smul_eq_mul]
  have hh : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hc, Complex.ofReal_one]
  change v x * star (v y) = (c * v x) * (star (v y) * star c)
  calc
    _ = (c * star c) * (v x * star (v y)) := by rw [hh, one_mul]
    _ = _ := by ring

end ExactCriticalCurve.Quantum
