import StabilizerLearning.Quantum.Finite
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic

/-! Actual finite character-labelled pure states and their hidden-character average.
The code is an arbitrary concrete map from the computational tuple space.  The
conditioned block identity is proved from character orthogonality, not assumed. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning.CharacterEnsemble

variable {Ω V L : Type*} [Fintype Ω] [AddCommGroup V] [Fintype V]
  [AddCommGroup L] [Fintype L]

/-- Phase on an actual computational tuple. -/
def phase (code : Ω → V × L) (y : AddChar V ℂ) (h : AddChar L ℂ) (x : Ω) : ℂ :=
  y (code x).1 * h (code x).2

/-- The normalized rank-one density for the actual complete character label. -/
def density (code : Ω → V × L) (y : AddChar V ℂ) (h : AddChar L ℂ) :
    Matrix Ω Ω ℂ :=
  ((Fintype.card Ω : ℝ)⁻¹) • Matrix.vecMulVec (phase code y h) (star (phase code y h))

/-- Uniformly average the hidden character, retaining the visible character label. -/
def conditioned (code : Ω → V × L) (y : AddChar V ℂ) : Matrix Ω Ω ℂ :=
  ((Fintype.card (AddChar L ℂ) : ℝ)⁻¹) • ∑ h : AddChar L ℂ, density code y h

@[simp] theorem card_visible_characters : Fintype.card (AddChar V ℂ) = Fintype.card V :=
  AddChar.card_eq

@[simp] theorem card_hidden_characters : Fintype.card (AddChar L ℂ) = Fintype.card L :=
  AddChar.card_eq

lemma character_mul_star {G : Type*} [AddCommGroup G] [Finite G]
    (χ : AddChar G ℂ) (a : G) : χ a * star (χ a) = 1 := by
  rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
    add_neg_cancel, AddChar.map_zero_eq_one]

omit [Fintype Ω] in
@[simp] theorem phase_mul_star (code : Ω → V × L) (y : AddChar V ℂ)
    (h : AddChar L ℂ) (x : Ω) : phase code y h x * star (phase code y h x) = 1 := by
  unfold phase
  rw [star_mul]
  calc
    _ = (y (code x).1 * star (y (code x).1)) *
        (h (code x).2 * star (h (code x).2)) := by ring
    _ = 1 := by rw [character_mul_star, character_mul_star]; norm_num

omit [Fintype V] [Fintype L] in
@[simp] theorem density_apply (code : Ω → V × L) (y : AddChar V ℂ)
    (h : AddChar L ℂ) (x x' : Ω) :
    density code y h x x' = (Fintype.card Ω : ℂ)⁻¹ *
      phase code y h x * star (phase code y h x') := by
  simp [density, Matrix.vecMulVec_apply, mul_assoc]

omit [Fintype V] [Fintype L] in
theorem density_posSemidef (code : Ω → V × L) (y : AddChar V ℂ)
    (h : AddChar L ℂ) : (density code y h).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)

@[simp] theorem density_diagonal (code : Ω → V × L) (y : AddChar V ℂ)
    (h : AddChar L ℂ) (x : Ω) : density code y h x x = (Fintype.card Ω : ℂ)⁻¹ := by
  rw [density_apply, mul_assoc, phase_mul_star, mul_one]

@[simp] theorem density_trace [Nonempty Ω] (code : Ω → V × L)
    (y : AddChar V ℂ) (h : AddChar L ℂ) : Matrix.trace (density code y h) = 1 := by
  simp only [Matrix.trace, Matrix.diag, density_diagonal]
  simp [Fintype.card_ne_zero]

/-- Character orthogonality on the genuine hidden-label average. -/
theorem hidden_character_average [DecidableEq L] (a b : L) :
    (Fintype.card (AddChar L ℂ) : ℂ)⁻¹ *
      (∑ h : AddChar L ℂ, h a * star (h b)) = if a = b then 1 else 0 := by
  classical
  simp_rw [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  rw [AddChar.sum_apply_eq_ite]
  simp [← sub_eq_add_neg, sub_eq_zero, AddChar.card_eq, Fintype.card_ne_zero]

omit [Fintype V] in
/-- The exact conditioned matrix entries: only equal lower-code values survive. -/
theorem conditioned_apply [DecidableEq L] (code : Ω → V × L) (y : AddChar V ℂ) (x x' : Ω) :
    conditioned code y x x' =
      if (code x).2 = (code x').2 then
        (Fintype.card Ω : ℂ)⁻¹ * y (code x).1 * star (y (code x').1)
      else 0 := by
  classical
  have hr (h : AddChar L ℂ) :
      density code y h x x' =
        ((Fintype.card Ω : ℂ)⁻¹ * y (code x).1 * star (y (code x').1)) *
          (h (code x).2 * star (h (code x').2)) := by
    rw [density_apply]
    simp only [phase, star_mul]
    ring
  simp only [conditioned, Matrix.smul_apply, Matrix.sum_apply, hr,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  change (Fintype.card (AddChar L ℂ) : ℂ)⁻¹ *
    (∑ h : AddChar L ℂ,
      ((Fintype.card Ω : ℂ)⁻¹ * y (code x).1 * star (y (code x').1)) *
        (h (code x).2 * star (h (code x').2))) = _
  rw [← Finset.mul_sum]
  rw [mul_left_comm, hidden_character_average]
  split_ifs <;> simp_all

private theorem sum_posSemidef {ι : Type*} [Fintype ι]
    (A : ι → Matrix Ω Ω ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (∑ i, A i).PosSemidef := by
  classical
  exact Finset.sum_induction A (fun B : Matrix Ω Ω ℂ => B.PosSemidef)
    (fun _ _ hB hC => hB.add hC) Matrix.PosSemidef.zero (fun i _ => hA i)

omit [Fintype V] in
theorem conditioned_posSemidef (code : Ω → V × L) (y : AddChar V ℂ) :
    (conditioned code y).PosSemidef :=
  (sum_posSemidef _ (density_posSemidef code y)).smul (by positivity)

@[simp] theorem conditioned_trace [Nonempty Ω] (code : Ω → V × L)
    (y : AddChar V ℂ) : Matrix.trace (conditioned code y) = 1 := by
  classical
  simp only [Matrix.trace, Matrix.diag, conditioned_apply,
    mul_assoc, character_mul_star, mul_one]
  simp [Fintype.card_ne_zero]

/-- Physical normalized positive state, with no success-probability premise. -/
def pureState [Nonempty Ω] (code : Ω → V × L) (y : AddChar V ℂ) (h : AddChar L ℂ) :
    Quantum.DensityMatrix Ω :=
  ⟨density code y h, density_posSemidef code y h, density_trace code y h⟩

def conditionedState [Nonempty Ω] (code : Ω → V × L) (y : AddChar V ℂ) :
    Quantum.DensityMatrix Ω :=
  ⟨conditioned code y, conditioned_posSemidef code y, conditioned_trace code y⟩

/-- The actual multi-copy code is the sum of the single-copy coordinates. -/
def tupleCode (code : Ω → V × L) (k : ℕ) (x : Fin k → Ω) : V × L :=
  (∑ i, (code (x i)).1, ∑ i, (code (x i)).2)

lemma character_sum {ι G : Type*} [Fintype ι] [AddCommGroup G]
    (χ : AddChar G ℂ) (f : ι → G) : χ (∑ i, f i) = ∏ i, χ (f i) := by
  classical
  have hsum (s : Finset ι) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs => simp [hi, AddChar.map_add_eq_mul, hs]
  exact hsum Finset.univ

omit [Fintype Ω] [Fintype V] [Fintype L] in
@[simp] theorem phase_tupleCode (code : Ω → V × L) (k : ℕ)
    (y : AddChar V ℂ) (h : AddChar L ℂ) (x : Fin k → Ω) :
    phase (tupleCode code k) y h x = ∏ i, phase code y h (x i) := by
  simp [phase, tupleCode, character_sum, Finset.prod_mul_distrib]

omit [Fintype V] [Fintype L] in
/-- Entrywise equality with the existing physical tensor-power definition,
including the zero-copy singleton. No orbit expansion is an input hypothesis. -/
theorem tensorPower_density (code : Ω → V × L) (k : ℕ)
    (y : AddChar V ℂ) (h : AddChar L ℂ) :
    Quantum.tensorPower (density code y h) k = density (tupleCode code k) y h := by
  classical
  ext x x'
  simp [Quantum.tensorPower, density_apply, phase_tupleCode,
    Finset.prod_mul_distrib, mul_assoc]

end StabilizerLearning.CharacterEnsemble
