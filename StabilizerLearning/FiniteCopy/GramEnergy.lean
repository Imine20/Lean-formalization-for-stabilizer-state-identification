import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! Statewise Gram energy control for the positive square root.  The proof
uses a positive matrix polynomial, and therefore also applies on singular support. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace StabilizerLearning.Quantum.PGM

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma posSemidef_diagonal_re_nonneg {A : Matrix Ω Ω ℂ}
    (hA : A.PosSemidef) (i : Ω) : 0 ≤ (A i i).re := by
  simpa [← Pi.single_star] using hA.re_dotProduct_nonneg (Pi.single i 1)

/-- The scalar inequality `2 sqrt x ≥ 3 x - x²`, proved as a positive
matrix polynomial instead of requiring an invertible square root. -/
theorem sqrt_polynomial_posSemidef (G : Matrix Ω Ω ℂ) (hG : G.PosSemidef) :
    (G * G - G - G - G + CFC.sqrt G + CFC.sqrt G).PosSemidef := by
  let H := CFC.sqrt G
  have hH : H.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)
  have hsq : H * H = G := CFC.sqrt_mul_sqrt_self G hG.nonneg
  have hpoly := ((hG.add hH).add hH).conjTranspose_mul_mul_same (H - 1)
  have heq : (H - 1)ᴴ * (G + H + H) * (H - 1) =
      G * G - G - G - G + H + H := by
    rw [Matrix.conjTranspose_sub, hH.isHermitian.eq, Matrix.conjTranspose_one, ← hsq]
    noncomm_ring
  rw [heq] at hpoly
  exact hpoly


/-- Off-diagonal row energy of a Gram matrix. -/
def gramRowEnergy (G : Matrix Ω Ω ℂ) (i : Ω) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, Complex.normSq (G i j)

lemma gramRowEnergy_nonneg (G : Matrix Ω Ω ℂ) (i : Ω) :
    0 ≤ gramRowEnergy G i := by
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

lemma gram_square_diagonal_re (G : Matrix Ω Ω ℂ) (hG : G.IsHermitian)
    (hdiag : ∀ i, G i i = 1) (i : Ω) :
    ((G * G) i i).re = 1 + gramRowEnergy G i := by
  have hentry : ∀ j, (G i j * G j i).re = Complex.normSq (G i j) := by
    intro j
    have hconj : star (G i j) = G j i := congrFun (congrFun hG.eq j) i
    rw [← hconj]
    simp [Complex.mul_conj]
  simp only [Matrix.mul_apply, Complex.re_sum, hentry]
  have hsplit := Finset.sum_erase_add (s := Finset.univ)
    (f := fun j => Complex.normSq (G i j)) (Finset.mem_univ i)
  simpa only [gramRowEnergy, hdiag, Complex.normSq_one, add_comm] using hsplit.symm

theorem sqrt_gram_diagonal_ge_one_sub_half_energy (G : Matrix Ω Ω ℂ)
    (hG : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (i : Ω) :
    1 - gramRowEnergy G i / 2 ≤ (CFC.sqrt G i i).re := by
  have hp := posSemidef_diagonal_re_nonneg (sqrt_polynomial_posSemidef G hG) i
  simp only [Matrix.add_apply, Matrix.sub_apply, Complex.add_re, Complex.sub_re,
    hdiag, Complex.one_re, gram_square_diagonal_re G hG.isHermitian hdiag i] at hp
  linarith

/-- Statewise PGM Gram bound, valid for singular matrices and every row energy. -/
theorem sqrt_gram_diagonal_sq_ge_one_sub_energy (G : Matrix Ω Ω ℂ)
    (hG : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (i : Ω) :
    1 - gramRowEnergy G i ≤ (CFC.sqrt G i i).re ^ 2 := by
  have hh := sqrt_gram_diagonal_ge_one_sub_half_energy G hG hdiag i
  have he := gramRowEnergy_nonneg G i
  have hs := posSemidef_diagonal_re_nonneg
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)) i
  by_cases hsmall : gramRowEnergy G i ≤ 1
  · nlinarith [sq_nonneg (gramRowEnergy G i), sq_nonneg ((CFC.sqrt G i i).re -
      (1 - gramRowEnergy G i / 2))]
  · have := sq_nonneg (CFC.sqrt G i i).re
    linarith


/-- The equivalent modulus-squared form used by Born probabilities. -/
theorem sqrt_gram_diagonal_normSq_ge_one_sub_energy (G : Matrix Ω Ω ℂ)
    (hG : G.PosSemidef) (hdiag : ∀ i, G i i = 1) (i : Ω) :
    1 - gramRowEnergy G i ≤ Complex.normSq (CFC.sqrt G i i) := by
  have hs : (CFC.sqrt G).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg G)).isHermitian
  have heq : Complex.normSq (CFC.sqrt G i i) = (CFC.sqrt G i i).re ^ 2 := by
    conv_lhs => rw [← hs.coe_re_apply_self i]
    simp [Complex.normSq_ofReal, pow_two]
  rw [heq]
  exact sqrt_gram_diagonal_sq_ge_one_sub_energy G hG hdiag i

end StabilizerLearning.Quantum.PGM


