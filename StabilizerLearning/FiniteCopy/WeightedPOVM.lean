import StabilizerLearning.FiniteCopy.MatrixOptimization
import StabilizerLearning.Quantum.Finite
import StabilizerLearning.FiniteCopy.MomentMass
import StabilizerLearning.FiniteCopy.CharacterEnsemble
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ComplexOrder Matrix
open Matrix
namespace StabilizerLearning
attribute [local instance] Classical.propDecidable

/-- The entry estimate follows from positivity; no diagonal restriction is
imposed on an arbitrary POVM effect. -/
theorem psd_twice_entry_re_le_diagonal_sum {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (i j : ι) :
    2 * (A i j).re ≤ (A i i).re + (A j j).re := by
  classical
  have hsym : (A j i).re = (A i j).re := by
    have h := congrArg Complex.re (hA.isHermitian.apply i j)
    simpa only [Complex.star_def, Complex.conj_re] using h
  have h := hA.re_dotProduct_nonneg (Pi.single i 1 - Pi.single j 1)
  change 0 ≤ (star (Pi.single i (1 : ℂ) - Pi.single j 1) ⬝ᵥ
    (A *ᵥ (Pi.single i 1 - Pi.single j 1))).re at h
  simp only [star_sub, ← Pi.single_star, star_one, mulVec_sub, sub_dotProduct,
    dotProduct_sub, mulVec_single_one, single_dotProduct, one_mul, col_apply,
    Complex.sub_re, hsym] at h
  linarith

/-- Finite support dimension bounds the all-ones quadratic form of any PSD
matrix. This is the operator inequality used in the weighted converse. -/
theorem psd_sum_entries_le_card_trace {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (∑ i, ∑ j, (A i j).re) ≤ (Fintype.card ι : ℝ) * ∑ i, (A i i).re := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      psd_twice_entry_re_le_diagonal_sum hA i j))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at h
  linarith

/-- Positivity survives compression to a finite family of tuple-sector vectors. -/
theorem psd_compressed_sum_le_card_trace {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    {A : Matrix Ω Ω ℂ} (hA : A.PosSemidef) (V : Matrix Ω Z ℂ) :
    (∑ i, ∑ j, ((Vᴴ * A * V) i j).re) ≤
      (Fintype.card Z : ℝ) * ∑ i, ((Vᴴ * A * V) i i).re := by
  exact psd_sum_entries_le_card_trace (hA.conjTranspose_mul_mul_same V)

/-- Distinct occurring codes above a fixed lower code, not tuple multiplicities. -/
abbrev OccurringCodeFiber {Ω Z L : Type*} (code : Ω → Z) (lower : Z → L) (ζ : L) :=
  ActualMomentSupport code lower ζ

/-- A fixed enumeration avoids switching between classical and finite-search
existence deciders when the tuple space acquires a Fintype instance. -/
noncomputable instance occurringCodeFiberFintype {Ω Z L : Type*} [Fintype Z]
    (code : Ω → Z) (lower : Z → L) (ζ : L) :
    Fintype (OccurringCodeFiber code lower ζ) := Fintype.ofFinite _

/-- Unnormalized sector columns; a column contains precisely the tuples with
that full code. Multiplication by a unit phase does not change its diagonal mass. -/
def sectorColumns {Ω Z L : Type*} (code : Ω → Z) (lower : Z → L) (ζ : L)
    (phase : Z → ℂ) : Matrix Ω (OccurringCodeFiber code lower ζ) ℂ := by
  classical
  exact fun x z => if code x = z.val then phase z.val else 0

theorem sector_compression_diagonal {Ω Z L : Type*} [Fintype Ω]
    [Fintype Z] (code : Ω → Z) (lower : Z → L) (ζ : L)
    (phase : Z → ℂ) (hphase : ∀ z, star (phase z) * phase z = 1)
    (A : Matrix Ω Ω ℂ) (z : OccurringCodeFiber code lower ζ) :
    ((sectorColumns code lower ζ phase)ᴴ * A * sectorColumns code lower ζ phase) z z =
    ((sectorColumns code lower ζ (fun _ => 1))ᴴ * A *
      sectorColumns code lower ζ (fun _ => 1)) z z := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : code x = z.val <;> by_cases hy : code y = z.val
  · simp only [sectorColumns, hx, hy, if_true, star_one, one_mul, mul_one]
    calc
      star (phase z.val) * A y x * phase z.val =
          (star (phase z.val) * phase z.val) * A y x := by ring
      _ = _ := by rw [hphase, one_mul]
  all_goals simp [sectorColumns, hx, hy]

theorem sector_compression_sum_diagonal {Ω Z L Y : Type*} [Fintype Ω]
    [DecidableEq Ω] [Fintype Z] [Fintype Y]
    (code : Ω → Z) (lower : Z → L) (ζ : L)
    (phase : Y → Z → ℂ) (hphase : ∀ y z, star (phase y z) * phase y z = 1)
    (M : Quantum.POVM Ω Y) (z : OccurringCodeFiber code lower ζ) :
    (∑ y, ((sectorColumns code lower ζ (phase y))ᴴ * M.effect y *
      sectorColumns code lower ζ (phase y)) z z) =
      (Nat.card {x // code x = z.val} : ℂ) := by
  classical
  simp_rw [sector_compression_diagonal code lower ζ _ (hphase _)]
  let V := sectorColumns code lower ζ (fun _ => (1 : ℂ))
  change (∑ y, (Vᴴ * M.effect y * V) z z) = _
  rw [← Matrix.sum_apply]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, M.normalized, Matrix.mul_one]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, sectorColumns]
  simp only [apply_ite star, star_one, star_zero]
  simp only [ite_mul, one_mul, zero_mul]
  have hnested (x : Ω) :
      (if code x = z.val then if code x = z.val then (1 : ℂ) else 0 else 0) =
        if code x = z.val then 1 else 0 := by
    by_cases hx : code x = z.val <;> simp [hx]
  simp_rw [hnested]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

/-- Summing an arbitrary POVM eliminates its diagonal allocations. The factor
is the number of distinct occurring codes, while the remaining sum counts tuples. -/
theorem sector_povm_sum_bound {Ω Z L Y : Type*} [Fintype Ω]
    [DecidableEq Ω] [Fintype Z] [Fintype Y]
    (code : Ω → Z) (lower : Z → L) (ζ : L)
    (phase : Y → Z → ℂ) (hphase : ∀ y z, star (phase y z) * phase y z = 1)
    (M : Quantum.POVM Ω Y) :
    (∑ y, ∑ i : OccurringCodeFiber code lower ζ,
      ∑ j : OccurringCodeFiber code lower ζ,
        (((sectorColumns code lower ζ (phase y))ᴴ * M.effect y *
          sectorColumns code lower ζ (phase y)) i j).re) ≤
      (Nat.card (OccurringCodeFiber code lower ζ) : ℝ) *
        ∑ z : OccurringCodeFiber code lower ζ,
          (Nat.card {x // code x = z.val} : ℝ) := by
  classical
  calc
    _ ≤ ∑ y, (Nat.card (OccurringCodeFiber code lower ζ) : ℝ) *
        ∑ z : OccurringCodeFiber code lower ζ,
          (((sectorColumns code lower ζ (phase y))ᴴ * M.effect y *
            sectorColumns code lower ζ (phase y)) z z).re := by
      apply Finset.sum_le_sum
      intro y _
      simpa only [Nat.card_eq_fintype_card] using
        psd_compressed_sum_le_card_trace (M.positive y) (sectorColumns code lower ζ (phase y))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      have h := congrArg Complex.re
        (sector_compression_sum_diagonal code lower ζ phase hphase M z)
      simpa using h

theorem sum_sectorColumns {Ω Z L : Type*} [Fintype Z]
    (code : Ω → Z) (lower : Z → L) (ζ : L) (phase : Z → ℂ) (x : Ω) :
    (∑ z : OccurringCodeFiber code lower ζ, sectorColumns code lower ζ phase x z) =
      if lower (code x) = ζ then phase (code x) else 0 := by
  classical
  by_cases hx : lower (code x) = ζ
  · rw [if_pos hx]
    let z : OccurringCodeFiber code lower ζ := ⟨code x, ⟨x, rfl⟩, hx⟩
    rw [Finset.sum_eq_single z]
    · simp [sectorColumns, z]
    · intro w _ hw
      have h : code x ≠ w.val := fun h => hw (Subtype.ext h.symm)
      simp [sectorColumns, h]
    · simp
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro z _
    have h : code x ≠ z.val := fun h => hx ((congrArg lower h).trans z.property.2)
    simp [sectorColumns, h]

def sectorOuter {Ω Z L : Type*} [Fintype Z]
    (code : Ω → Z) (lower : Z → L) (ζ : L) (phase : Z → ℂ) : Matrix Ω Ω ℂ :=
  let V := sectorColumns code lower ζ phase
  V * MatrixOptimization.rankOneSeed 1 * Vᴴ

theorem sectorOuter_apply {Ω Z L : Type*} [Fintype Z]
    (code : Ω → Z) (lower : Z → L) (ζ : L) (phase : Z → ℂ) (x x' : Ω) :
    sectorOuter code lower ζ phase x x' =
      (if lower (code x) = ζ then phase (code x) else 0) *
        star (if lower (code x') = ζ then phase (code x') else 0) := by
  classical
  let V := sectorColumns code lower ζ phase
  have hJ : MatrixOptimization.rankOneSeed (ι := OccurringCodeFiber code lower ζ) 1 =
      Matrix.vecMulVec (1 : OccurringCodeFiber code lower ζ → ℂ) 1 := by
    ext i j
    simp [MatrixOptimization.rankOneSeed, Matrix.vecMulVec]
  have hstar : (1 : OccurringCodeFiber code lower ζ → ℂ) ᵥ* Vᴴ = star (V *ᵥ 1) := by
    rw [star_mulVec, star_one]
  unfold sectorOuter
  rw [hJ, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  change (Matrix.vecMulVec (V *ᵥ 1) (1 ᵥ* Vᴴ)) x x' = _
  rw [hstar]
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Matrix.mulVec, dotProduct,
    Pi.one_apply, mul_one, V, sum_sectorColumns]

theorem born_compressed_seed {Ω Z : Type*} [Fintype Ω] [Fintype Z]
    (A : Matrix Ω Ω ℂ) (V : Matrix Ω Z ℂ) :
    Quantum.born A (V * MatrixOptimization.rankOneSeed 1 * Vᴴ) =
      ∑ i, ∑ j, ((Vᴴ * A * V) i j).re := by
  unfold Quantum.born
  have h : Matrix.trace (A * (V * MatrixOptimization.rankOneSeed 1 * Vᴴ)) =
      Matrix.trace ((Vᴴ * A * V) * MatrixOptimization.rankOneSeed 1) := by
    calc
      _ = Matrix.trace ((A * V * MatrixOptimization.rankOneSeed 1) * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Vᴴ * (A * V * MatrixOptimization.rankOneSeed 1)) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    MatrixOptimization.rankOneSeed, Complex.ofReal_one, mul_one, Complex.re_sum]

theorem born_sectorOuter {Ω Z L : Type*} [Fintype Ω] [Fintype Z]
    (code : Ω → Z) (lower : Z → L) (ζ : L) (phase : Z → ℂ)
    (A : Matrix Ω Ω ℂ) :
    Quantum.born A (sectorOuter code lower ζ phase) =
      ∑ i : OccurringCodeFiber code lower ζ, ∑ j : OccurringCodeFiber code lower ζ,
        (((sectorColumns code lower ζ phase)ᴴ * A *
          sectorColumns code lower ζ phase) i j).re := by
  classical
  unfold sectorOuter
  exact born_compressed_seed (Z := OccurringCodeFiber code lower ζ) A
    (sectorColumns code lower ζ phase)

/-- The already proved hidden-character average is the sum of the actual
occurring-moment sector outer products. This equality is not an ensemble premise. -/
theorem conditioned_eq_sector_sum {Ω V L : Type*} [Fintype Ω]
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (code : Ω → V × L) (y : AddChar V ℂ) :
    CharacterEnsemble.conditioned code y = (Fintype.card Ω : ℝ)⁻¹ •
      ∑ ζ : L, sectorOuter code Prod.snd ζ (fun z => y z.1) := by
  classical
  ext x x'
  have hs : (∑ ζ : L, sectorOuter code Prod.snd ζ (fun z => y z.1) x x') =
      if (code x).2 = (code x').2 then y (code x).1 * star (y (code x').1) else 0 := by
    rw [Finset.sum_eq_single (code x).2]
    · by_cases he : (code x).2 = (code x').2 <;> simp [sectorOuter_apply, he, eq_comm]
    · intro ζ _ hζ
      simp [sectorOuter_apply, Ne.symm hζ]
    · simp
  rw [CharacterEnsemble.conditioned_apply]
  simp only [Matrix.smul_apply, Matrix.sum_apply, hs, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]
  split_ifs <;> simp_all [mul_assoc]

/-- Actual uniform average of Born success over the full visible-character
alphabet, for every POVM on the full computational tuple space. -/
def characterSuccess {Ω V L : Type*} [Fintype Ω] [DecidableEq Ω]
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (code : Ω → V × L) (M : Quantum.POVM Ω (AddChar V ℂ)) : ℝ :=
  (∑ y, Quantum.born (M.effect y) (CharacterEnsemble.conditioned code y)) /
    Fintype.card (AddChar V ℂ)

theorem born_real_smul {Ω : Type*} [Fintype Ω]
    (A B : Matrix Ω Ω ℂ) (r : ℝ) : Quantum.born A (r • B) = r * Quantum.born A B := by
  simp [Quantum.born, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re]

theorem born_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (A : Matrix Ω Ω ℂ) (B : I → Matrix Ω Ω ℂ) :
    Quantum.born A (∑ i, B i) = ∑ i, Quantum.born A (B i) := by
  simp [Quantum.born, Matrix.mul_sum, Matrix.trace_sum]

/-- Direct weighted support bound for every actual POVM. All blocks, phases
and tuple multiplicities are derived from the concrete ensemble and its code. -/
theorem characterSuccess_le_weighted_count {Ω V L : Type*} [Fintype Ω]
    [DecidableEq Ω] [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (code : Ω → V × L) (M : Quantum.POVM Ω (AddChar V ℂ)) :
    characterSuccess code M ≤
      (∑ ζ : L, (Nat.card (ActualMomentSupport code Prod.snd ζ) : ℝ) *
        (Nat.card {x // (code x).2 = ζ} : ℝ)) /
          ((Nat.card V : ℝ) * (Nat.card Ω : ℝ)) := by
  classical
  have hp (y : AddChar V ℂ) (z : V × L) : star (y z.1) * y z.1 = 1 := by
    rw [mul_comm]
    exact CharacterEnsemble.character_mul_star y z.1
  have hs (ζ : L) :
      (∑ y : AddChar V ℂ, Quantum.born (M.effect y)
        (sectorOuter code Prod.snd ζ (fun z => y z.1))) ≤
      (Nat.card (ActualMomentSupport code Prod.snd ζ) : ℝ) *
        (Nat.card {x // (code x).2 = ζ} : ℝ) := by
    simp_rw [born_sectorOuter]
    have h := sector_povm_sum_bound code Prod.snd ζ (fun y z => y z.1) hp M
    have hm : (∑ z : ActualMomentSupport code Prod.snd ζ,
        (Nat.card {x // code x = z.val} : ℝ)) =
          (Nat.card {x // (code x).2 = ζ} : ℝ) := by
      rw [← momentCosetMass_eq_card code Prod.snd ζ, momentCosetMass, Nat.cast_sum]
      convert (sum_coset_eq_support code Prod.snd ζ (fun n => (n : ℝ)) (by simp)).symm using 1
      congr 1
      ext z
      simp
    simpa only [OccurringCodeFiber, hm] using h
  unfold characterSuccess
  simp_rw [conditioned_eq_sector_sum, born_real_smul, born_sum]
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    _ ≤ ((Fintype.card Ω : ℝ)⁻¹ *
        ∑ ζ : L, (Nat.card (ActualMomentSupport code Prod.snd ζ) : ℝ) *
          (Nat.card {x // (code x).2 = ζ} : ℝ)) / Fintype.card (AddChar V ℂ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ζ _ => hs ζ)) (by positivity)
    _ = _ := by
      rw [AddChar.card_eq]
      simp only [Nat.card_eq_fintype_card]
      ring

end StabilizerLearning
