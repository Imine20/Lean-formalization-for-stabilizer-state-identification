import ExactCriticalCurve.Quantum.GNWMoment
import ExactCriticalCurve.Binary.MixedSignature
import ExactCriticalCurve.Quantum.RelationTracePolynomial
import ExactCriticalCurve.Counting.BinaryQBinomial
import Mathlib.Algebra.Polynomial.Roots

/-! Exact diagonal-intersection strata of the actual stochastic relation family.
The counting polynomial is determined from the proved physical GNW moment at
all qubit dimensions. No diagonal-distribution identity is assumed. -/
noncomputable section
open scoped BigOperators Polynomial
open Classical
open ExactCriticalCurve.Binary ExactCriticalCurve.Binary.StochasticCounting
open ExactCriticalCurve.Counting

namespace ExactCriticalCurve.Quantum

/-- Binary diagonal labels admitted by an actual relation. -/
def relationDiagonalSpace {k : ℕ}
    (T : Submodule (ZMod 2) (RelationSpace k)) :=
  T.comap (diagonalMap k)

/-- Diagonal labels are exactly the actual intersection with the diagonal. -/
def relationDiagonalEquiv {k : ℕ}
    (T : Submodule (ZMod 2) (RelationSpace k)) :
    relationDiagonalSpace T ≃ₗ[ZMod 2] (T ⊓ diagonal k : Submodule (ZMod 2) (RelationSpace k)) := by
  let f : relationDiagonalSpace T →ₗ[ZMod 2] (T ⊓ diagonal k : Submodule (ZMod 2) (RelationSpace k)) :=
    { toFun := fun x => ⟨diagonalMap k x.val, x.property, ⟨x.val, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (congrArg (fun z : (T ⊓ diagonal k : Submodule (ZMod 2) (RelationSpace k)) => z.val.1) h)
  · intro p
    obtain ⟨x, hx⟩ := p.property.2
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change diagonalMap k x ∈ T
    rw [hx]
    exact p.property.1

theorem relationMatrix_trace_diagonal {k : ℕ}
    (T : Submodule (ZMod 2) (RelationSpace k)) :
    Matrix.trace (relationMatrix T) =
      (2 : ℂ) ^ Module.finrank (ZMod 2) (T ⊓ diagonal k : Submodule (ZMod 2) (RelationSpace k)) := by
  have hc : Matrix.trace (relationMatrix T) = (Nat.card (relationDiagonalSpace T) : ℂ) := by
    simp [Matrix.trace, Matrix.diag, relationMatrix, relationDiagonalSpace, diagonalMap,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2),
    ZMod.card, Nat.cast_pow, Nat.cast_ofNat, (relationDiagonalEquiv T).finrank_eq]

theorem relationOperator_trace_diagonal (n : ℕ) {k : ℕ}
    (T : Submodule (ZMod 2) (RelationSpace k)) :
    Matrix.trace (relationOperator n T) =
      ((2 : ℂ)^n) ^ Module.finrank (ZMod 2) (T ⊓ diagonal k : Submodule (ZMod 2) (RelationSpace k)) := by
  rw [relationOperator, matrixTensorPower_trace, relationMatrix_trace_diagonal,
    ← pow_mul, Nat.mul_comm, pow_mul]

/-- A polynomial whose coefficients count the complete actual relation family. -/
def relationDiagonalPolynomial (k : ℕ) : ℂ[X] :=
  ∑ T : StochasticLagrangian k,
    Polynomial.monomial (Module.finrank (ZMod 2) (T.carrier ⊓ diagonal k : Submodule (ZMod 2) (RelationSpace k))) 1

theorem relationDiagonalPolynomial_eval (n k : ℕ) (hk : 1 ≤ k) :
    (relationDiagonalPolynomial k).eval ((2 : ℂ)^n) =
      (2 : ℂ)^n * ∏ j ∈ Finset.range (k-1), ((2 : ℂ)^n + (2 : ℂ)^j) := by
  have ht : Matrix.trace (stabilizerColumnMoment n k) = 1 := by
    rw [stabilizerColumnMoment, Matrix.trace]
    change (∑ x, stabilizerMoment n k ((copyColumnsEquiv n k).symm x)
      ((copyColumnsEquiv n k).symm x)) = 1
    rw [show (∑ x, stabilizerMoment n k ((copyColumnsEquiv n k).symm x)
      ((copyColumnsEquiv n k).symm x)) = ∑ x, stabilizerMoment n k x x from
      (copyColumnsEquiv n k).symm.sum_comp (fun x => stabilizerMoment n k x x)]
    exact stabilizerMoment_trace_one n k
  rw [stabilizerColumnMoment_eq_relation_sum n k hk, Matrix.trace_smul,
    Matrix.trace_sum] at ht
  simp only [relationOperator_trace_diagonal, smul_eq_mul] at ht
  have he : (relationDiagonalPolynomial k).eval ((2 : ℂ)^n) =
      ∑ T : StochasticLagrangian k,
        ((2 : ℂ)^n) ^ Module.finrank (ZMod 2) (T.carrier ⊓ diagonal k : Submodule (ZMod 2) (RelationSpace k)) := by
    simp only [relationDiagonalPolynomial, Polynomial.eval_finset_sum,
      Polynomial.eval_monomial, one_mul]
  rw [he]
  exact ((inv_mul_eq_one₀ (gnwNormalization_ne_zero n k)).mp ht).symm

theorem binaryGaussian_homogeneous (m : ℕ) (x : ℂ) (hx : x ≠ 0) :
    (∑ r ∈ Finset.range (m+1),
      (binaryGaussian m r : ℂ) * (2 : ℂ)^(r.choose 2) * x^(m-r)) =
      ∏ j ∈ Finset.range m, (x+(2 : ℂ)^j) := by
  have h := congrArg (fun z : ℂ => x^m*z) (binaryGaussian_q_binomial m x⁻¹)
  have hl :
      x^m * (∑ r ∈ Finset.range (m+1),
        (binaryGaussian m r : ℂ) * (2 : ℂ)^(r.choose 2) * (x⁻¹)^r) =
      ∑ r ∈ Finset.range (m+1),
        (binaryGaussian m r : ℂ) * (2 : ℂ)^(r.choose 2) * x^(m-r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [pow_sub₀ x hx (Nat.le_of_lt_succ (Finset.mem_range.mp hr)), inv_pow]
    ring
  have hr : x^m * (∏ j ∈ Finset.range m, (1+(2 : ℂ)^j*x⁻¹)) =
      ∏ j ∈ Finset.range m, (x+(2 : ℂ)^j) := by
    rw [show x^m = ∏ _j ∈ Finset.range m, x by simp, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    field_simp
  dsimp only at h
  rwa [hl, hr] at h

/-- The explicit coefficient polynomial, with no physical dimension parameter. -/
def relationDiagonalCandidate (k : ℕ) : ℂ[X] :=
  ∑ r ∈ Finset.range k,
    Polynomial.monomial (k-r) ((binaryGaussian (k-1) r : ℂ)*(2 : ℂ)^(r.choose 2))

theorem relationDiagonalCandidate_eval (n k : ℕ) (hk : 1 ≤ k) :
    (relationDiagonalCandidate k).eval ((2 : ℂ)^n) =
      (2 : ℂ)^n * ∏ j ∈ Finset.range (k-1), ((2 : ℂ)^n+(2 : ℂ)^j) := by
  let x : ℂ := (2 : ℂ)^n
  have hx : x ≠ 0 := pow_ne_zero _ (by norm_num)
  have h := congrArg (fun z : ℂ => x*z) (binaryGaussian_homogeneous (k-1) x hx)
  have hk' : k-1+1=k := by omega
  dsimp only at h
  rw [hk', Finset.mul_sum] at h
  rw [← h]
  simp only [relationDiagonalCandidate, Polynomial.eval_finset_sum,
    Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro r hr
  have hpow : k-r = (k-1-r)+1 := by have := Finset.mem_range.mp hr; omega
  rw [hpow, pow_succ]
  ring

/-- Equality is forced by the actual GNW traces at infinitely many dimensions. -/
theorem relationDiagonalPolynomial_eq_candidate (k : ℕ) (hk : 1 ≤ k) :
    relationDiagonalPolynomial k = relationDiagonalCandidate k := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => (2 : ℂ)^n) := by
    intro a b h
    change (2 : ℂ)^a = (2 : ℂ)^b at h
    have hn : (2 : ℕ)^a = 2^b := by exact_mod_cast h
    exact Nat.pow_right_injective (by omega) hn
  apply (Set.infinite_range_of_injective hi).mono
  rintro x ⟨n, rfl⟩
  change (relationDiagonalPolynomial k).eval ((2 : ℂ)^n) =
    (relationDiagonalCandidate k).eval ((2 : ℂ)^n)
  rw [relationDiagonalPolynomial_eval n k hk, relationDiagonalCandidate_eval n k hk]

/-- Each coefficient counts the full fiber of the actual intersection dimension. -/
theorem relationDiagonalPolynomial_coeff (k d : ℕ) :
    (relationDiagonalPolynomial k).coeff d =
      (Nat.card {T : StochasticLagrangian k //
        Module.finrank (ZMod 2) (T.carrier ⊓ diagonal k :
          Submodule (ZMod 2) (RelationSpace k)) = d} : ℂ) := by
  simp [relationDiagonalPolynomial, Polynomial.coeff_monomial,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem relationDiagonalCandidate_coeff (k ell : ℕ) (hk : 1 ≤ k) (hell : ell ≤ k-1) :
    (relationDiagonalCandidate k).coeff (k-ell) =
      (binaryGaussian (k-1) ell : ℂ)*(2 : ℂ)^(ell.choose 2) := by
  simp only [relationDiagonalCandidate, Polynomial.finset_sum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single ell]
  · simp
  · intro r hr hne
    have h : k-r ≠ k-ell := by
      have hr' := Finset.mem_range.mp hr
      omega
    simp [h]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

/-- The exact diagonal-intersection distribution for every positive copy number. -/
theorem card_stochasticLagrangian_diagonal_stratum (k ell : ℕ)
    (hk : 1 ≤ k) (hell : ell ≤ k-1) :
    Nat.card {T : StochasticLagrangian k //
      Module.finrank (ZMod 2) (T.carrier ⊓ diagonal k :
        Submodule (ZMod 2) (RelationSpace k)) = k-ell} =
      2^(ell.choose 2)*binaryGaussian (k-1) ell := by
  have h := congrArg (fun p : ℂ[X] => p.coeff (k-ell))
    (relationDiagonalPolynomial_eq_candidate k hk)
  dsimp only at h
  rw [relationDiagonalPolynomial_coeff, relationDiagonalCandidate_coeff k ell hk hell] at h
  rw [mul_comm] at h
  exact_mod_cast h

/-- The coordinate switch preserves the actual diagonal intersection pointwise. -/
theorem switchSubspace_inf_diagonal {k : ℕ} (mask : Fin k → Bool)
    (T : Submodule (ZMod 2) (RelationSpace k)) :
    switchSubspace mask T ⊓ diagonal k = T ⊓ diagonal k := by
  ext p
  constructor
  · rintro ⟨hT, hD⟩
    obtain ⟨x, rfl⟩ := hD
    exact ⟨(switchSubspace_diagonal_mem mask T x).mp hT, ⟨x, rfl⟩⟩
  · rintro ⟨hT, hD⟩
    obtain ⟨x, rfl⟩ := hD
    exact ⟨(switchSubspace_diagonal_mem mask T x).mpr hT, ⟨x, rfl⟩⟩

/-- The full ordinary and signed diagonal fibers correspond, at every dimension. -/
def signedDiagonalStratumEquiv {k : ℕ} (mask : Fin k → Bool) (d : ℕ) :
    {T : StochasticLagrangian k //
      Module.finrank (ZMod 2) (T.carrier ⊓ diagonal k :
        Submodule (ZMod 2) (RelationSpace k)) = d} ≃
    {T : SignedStochasticLagrangian mask //
      Module.finrank (ZMod 2) (T.carrier ⊓ diagonal k :
        Submodule (ZMod 2) (RelationSpace k)) = d} :=
  (signedStochasticLagrangianEquiv mask).subtypeEquiv (fun T => by
    rw [signedStochasticLagrangianEquiv_carrier, switchSubspace_inf_diagonal])

/-- Exact signed distribution; the signature is arbitrary and no stable range occurs. -/
theorem card_signedStochasticLagrangian_diagonal_stratum {k : ℕ}
    (mask : Fin k → Bool) (ell : ℕ) (hk : 1 ≤ k) (hell : ell ≤ k-1) :
    Nat.card {T : SignedStochasticLagrangian mask //
      Module.finrank (ZMod 2) (T.carrier ⊓ diagonal k :
        Submodule (ZMod 2) (RelationSpace k)) = k-ell} =
      2^(ell.choose 2)*binaryGaussian (k-1) ell := by
  rw [← Nat.card_congr (signedDiagonalStratumEquiv mask (k-ell))]
  exact card_stochasticLagrangian_diagonal_stratum k ell hk hell

end ExactCriticalCurve.Quantum
