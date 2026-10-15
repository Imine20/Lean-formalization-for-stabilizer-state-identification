import ExactCriticalCurve.Foundations.PowerSum
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Data.Multiset.Filter

/-! # Hermitian matrix spectra with multiplicity

The real spectrum below retains repetitions. Only the zero eigenvalues are
discarded in `nonzeroSpectrum`; matrices may be singular or have empty index types.
-/

namespace ExactCriticalCurve

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real eigenvalues of a Hermitian matrix, counted with multiplicity. -/
noncomputable def realSpectrum (A : Matrix n n ℂ) (hA : A.IsHermitian) : Multiset ℝ :=
  Finset.univ.val.map hA.eigenvalues

/-- The nonzero real eigenvalues, counted with multiplicity. -/
noncomputable def nonzeroSpectrum (A : Matrix n n ℂ) (hA : A.IsHermitian) : Multiset ℝ :=
  (realSpectrum A hA).filter (· ≠ 0)

/-- Unitary diagonalization commutes with every natural matrix power. -/
theorem pow_eq_eigenvectorUnitary_diagonal (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (p : ℕ) :
    A ^ p = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) ^ p *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  induction p with
  | zero =>
      simp only [pow_zero, mul_one]
      exact (unitary.coe_mul_star_self hA.eigenvectorUnitary).symm
  | succ p ih =>
      rw [pow_succ, ih]
      conv_lhs => rhs; rw [hA.spectral_theorem]
      rw [pow_succ]
      calc
        _ = (hA.eigenvectorUnitary : Matrix n n ℂ) *
            diagonal (RCLike.ofReal ∘ hA.eigenvalues) ^ p *
            (star (hA.eigenvectorUnitary : Matrix n n ℂ) *
              (hA.eigenvectorUnitary : Matrix n n ℂ)) *
            diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
            star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
              simp only [mul_assoc]
        _ = _ := by rw [unitary.coe_star_mul_self]; simp only [mul_one, mul_assoc]

/-- The trace of a power is the power sum of the real eigenvalues.
The statement includes the zeroth power and empty matrices. -/
theorem trace_pow_eq_sum_eigenvalues (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (p : ℕ) :
    Matrix.trace (A ^ p) = ((∑ i, hA.eigenvalues i ^ p : ℝ) : ℂ) := by
  rw [pow_eq_eigenvectorUnitary_diagonal A hA p, Matrix.trace_mul_cycle,
    unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp [Function.comp_def]

theorem mem_nonzeroSpectrum_ne_zero (A : Matrix n n ℂ)
    (hA : A.IsHermitian) {x : ℝ} (hx : x ∈ nonzeroSpectrum A hA) : x ≠ 0 := by
  exact (Multiset.mem_filter.mp hx).2

@[simp]
theorem realSpectrum_card (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (realSpectrum A hA).card = Fintype.card n := by
  simp [realSpectrum]

theorem nonzeroSpectrum_card_eq_rank (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (nonzeroSpectrum A hA).card = A.rank := by
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  simp only [nonzeroSpectrum, realSpectrum, Multiset.filter_map, Multiset.card_map]
  rfl

theorem nonzeroSpectrum_card_le (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (nonzeroSpectrum A hA).card ≤ Fintype.card n := by
  rw [nonzeroSpectrum_card_eq_rank]
  exact A.rank_le_card_width

/-- Positive power sums are unaffected by discarding zero eigenvalues. -/
theorem nonzeroSpectrum_pow_sum (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (p : ℕ) (hp : 0 < p) :
    ((nonzeroSpectrum A hA).map (fun x => x ^ p)).sum = ∑ i, hA.eigenvalues i ^ p := by
  classical
  simp only [nonzeroSpectrum, realSpectrum, Multiset.filter_map, Multiset.map_map]
  change (∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0),
    hA.eigenvalues i ^ p) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : hA.eigenvalues i = 0 <;> simp [h, Nat.ne_of_gt hp]

/-- Matrix traces determine every positive power sum of the nonzero spectrum. -/
theorem trace_pow_eq_nonzeroSpectrum_sum (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (p : ℕ) (hp : 0 < p) :
    Matrix.trace (A ^ p) = ((((nonzeroSpectrum A hA).map (fun x => x ^ p)).sum : ℝ) : ℂ) := by
  rw [nonzeroSpectrum_pow_sum A hA p hp, trace_pow_eq_sum_eigenvalues]

/-- The multiplicity of zero as a real eigenvalue. -/
noncomputable def zeroMultiplicity (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℕ :=
  (realSpectrum A hA).count 0

/-- The complete real spectrum splits into its zero and nonzero parts. -/
theorem realSpectrum_decomposition (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    Multiset.replicate (zeroMultiplicity A hA) 0 + nonzeroSpectrum A hA =
      realSpectrum A hA := by
  simpa only [Multiset.filter_eq', zeroMultiplicity, nonzeroSpectrum] using
    Multiset.filter_add_not (fun x : ℝ => x = 0) (realSpectrum A hA)

/-- A subtraction-free dimension identity, valid also for an empty matrix. -/
theorem zeroMultiplicity_add_nonzeroSpectrum_card (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    zeroMultiplicity A hA + (nonzeroSpectrum A hA).card = Fintype.card n := by
  simpa only [Multiset.card_add, Multiset.card_replicate, realSpectrum_card] using
    congrArg Multiset.card (realSpectrum_decomposition A hA)

/-- Zero multiplicity is ambient dimension minus the cardinality of the nonzero spectrum.
The preceding cardinality bound ensures this natural subtraction does not truncate. -/
theorem zeroMultiplicity_eq_card_sub_nonzeroSpectrum_card (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    zeroMultiplicity A hA = Fintype.card n - (nonzeroSpectrum A hA).card := by
  have hle := nonzeroSpectrum_card_le A hA
  have hadd := zeroMultiplicity_add_nonzeroSpectrum_card A hA
  omega

theorem zeroMultiplicity_eq_card_sub_rank (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    zeroMultiplicity A hA = Fintype.card n - A.rank := by
  rw [zeroMultiplicity_eq_card_sub_nonzeroSpectrum_card, nonzeroSpectrum_card_eq_rank]

/-- The multiset is the usual characteristic-polynomial root multiset after the real cast. -/
theorem roots_charpoly_eq_map_realSpectrum (A : Matrix n n ℂ)
    (hA : A.IsHermitian) :
    A.charpoly.roots = (realSpectrum A hA).map (fun x : ℝ => (x : ℂ)) := by
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [realSpectrum, Multiset.map_map]
  rfl

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Equal nonzero spectra determine the whole spectra when ambient dimensions agree. -/
theorem realSpectrum_eq_of_nonzeroSpectrum_eq (A : Matrix n n ℂ)
    (B : Matrix m m ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hdim : Fintype.card n = Fintype.card m)
    (hspec : nonzeroSpectrum A hA = nonzeroSpectrum B hB) :
    realSpectrum A hA = realSpectrum B hB := by
  have hz : zeroMultiplicity A hA = zeroMultiplicity B hB := by
    rw [zeroMultiplicity_eq_card_sub_nonzeroSpectrum_card,
      zeroMultiplicity_eq_card_sub_nonzeroSpectrum_card, hdim, hspec]
  rw [← realSpectrum_decomposition A hA, ← realSpectrum_decomposition B hB, hz, hspec]

/-- Named power-sum form of the trace bridge for composition with finite moment uniqueness. -/
theorem trace_pow_eq_nonzeroSpectrum_powerSum (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (p : ℕ) (hp : 0 < p) :
    Matrix.trace (A ^ p) = (powerSum (nonzeroSpectrum A hA) p : ℂ) :=
  trace_pow_eq_nonzeroSpectrum_sum A hA p hp

/-- Finitely many positive traces determine the nonzero spectrum, including multiplicities.
The matrices may have different dimensions. -/
theorem nonzeroSpectrum_eq_of_trace_pow_eq_fin (A : Matrix n n ℂ)
    (B : Matrix m m ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htrace : ∀ p : ℕ, 0 < p →
      p ≤ ((nonzeroSpectrum A hA).toFinset ∪ (nonzeroSpectrum B hB).toFinset).card →
      Matrix.trace (A ^ p) = Matrix.trace (B ^ p)) :
    nonzeroSpectrum A hA = nonzeroSpectrum B hB := by
  apply multiset_eq_of_pos_powerSum_eq_fin _ _
    (fun _ hx => mem_nonzeroSpectrum_ne_zero A hA hx)
    (fun _ hx => mem_nonzeroSpectrum_ne_zero B hB hx)
  intro p hp hbound
  apply Complex.ofReal_injective
  rw [← trace_pow_eq_nonzeroSpectrum_powerSum A hA p hp,
    ← trace_pow_eq_nonzeroSpectrum_powerSum B hB p hp]
  exact htrace p hp hbound

/-- Equality of all positive traces determines the nonzero spectrum.
No ambient-dimension equality or full-rank assumption is needed. -/
theorem nonzeroSpectrum_eq_of_trace_pow_eq (A : Matrix n n ℂ)
    (B : Matrix m m ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htrace : ∀ p : ℕ, 0 < p → Matrix.trace (A ^ p) = Matrix.trace (B ^ p)) :
    nonzeroSpectrum A hA = nonzeroSpectrum B hB :=
  nonzeroSpectrum_eq_of_trace_pow_eq_fin A B hA hB (fun p hp _ => htrace p hp)

/-- Positive traces are equivalent to the nonzero spectrum with multiplicities. -/
theorem nonzeroSpectrum_eq_iff_trace_pow_eq (A : Matrix n n ℂ)
    (B : Matrix m m ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    nonzeroSpectrum A hA = nonzeroSpectrum B hB ↔
      ∀ p : ℕ, 0 < p → Matrix.trace (A ^ p) = Matrix.trace (B ^ p) := by
  constructor
  · intro hspec p hp
    rw [trace_pow_eq_nonzeroSpectrum_powerSum A hA p hp,
      trace_pow_eq_nonzeroSpectrum_powerSum B hB p hp, hspec]
  · exact nonzeroSpectrum_eq_of_trace_pow_eq A B hA hB

theorem rank_eq_of_trace_pow_eq (A : Matrix n n ℂ)
    (B : Matrix m m ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htrace : ∀ p : ℕ, 0 < p → Matrix.trace (A ^ p) = Matrix.trace (B ^ p)) :
    A.rank = B.rank := by
  rw [← nonzeroSpectrum_card_eq_rank A hA, ← nonzeroSpectrum_card_eq_rank B hB,
    nonzeroSpectrum_eq_of_trace_pow_eq A B hA hB htrace]

/-- Equal dimensions recover the missing zero multiplicity. -/
theorem realSpectrum_eq_of_trace_pow_eq (A : Matrix n n ℂ)
    (B : Matrix m m ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hdim : Fintype.card n = Fintype.card m)
    (htrace : ∀ p : ℕ, 0 < p → Matrix.trace (A ^ p) = Matrix.trace (B ^ p)) :
    realSpectrum A hA = realSpectrum B hB :=
  realSpectrum_eq_of_nonzeroSpectrum_eq A B hA hB hdim
    (nonzeroSpectrum_eq_of_trace_pow_eq A B hA hB htrace)

end ExactCriticalCurve


