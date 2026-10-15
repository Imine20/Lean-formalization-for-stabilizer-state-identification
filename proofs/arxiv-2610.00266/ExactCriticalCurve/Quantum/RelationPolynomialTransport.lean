import ExactCriticalCurve.Binary.ConfigurationRelations
import ExactCriticalCurve.Quantum.RelationDiagonalCount
import Mathlib.LinearAlgebra.LinearIndependent.Defs

noncomputable section
open Classical Matrix Module
open scoped BigOperators Polynomial
namespace ExactCriticalCurve.Quantum
open Binary Binary.StochasticCounting
variable {n k : ℕ}

/-- Actual basis columns padded with zero separate each full-dimensional relation. -/
theorem stochasticRelation_exists_entry_separator (T : StochasticLagrangian k) (hn : k ≤ n) :
    ∃ X Y : ColumnConfig n k, ∀ U : StochasticLagrangian k,
      relationOperator n U.carrier X Y = if U = T then 1 else 0 := by
  let b : Basis (Fin k) (ZMod 2) T.carrier :=
    (Module.finBasis (ZMod 2) T.carrier).reindex (finCongr T.finrank_eq)
  let Z : Fin n → RelationSpace k := fun i =>
    if h : i.val < k then (b ⟨i.val,h⟩).val else 0
  have hZ (i : Fin k) : Z ⟨i.val,lt_of_lt_of_le i.isLt hn⟩ = (b i).val := by
    simp [Z,i.isLt]
  have hZU (U : Submodule (ZMod 2) (RelationSpace k)) :
      (∀ a, Z a ∈ U) ↔ T.carrier ≤ U := by
    constructor
    · intro h
      have hb : (⊤ : Submodule (ZMod 2) T.carrier) ≤ U.comap T.carrier.subtype := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change (b i).val ∈ U
        rw [← hZ i]
        exact h _
      intro x hx
      exact hb (show (⟨x,hx⟩ : T.carrier) ∈ (⊤ : Submodule (ZMod 2) T.carrier) from trivial)
    · intro h a
      apply h
      dsimp only [Z]
      split_ifs with ha
      · exact (b ⟨a.val,ha⟩).property
      · exact T.carrier.zero_mem
  refine ⟨fun a => (Z a).1,fun a => (Z a).2,?_⟩
  intro U
  have he : (∀ a, Z a ∈ U.carrier) ↔ U = T := by
    rw [hZU]
    constructor
    · intro h
      apply StochasticLagrangian.ext
      exact (Submodule.eq_of_le_of_finrank_le h (by rw [U.finrank_eq,T.finrank_eq])).symm
    · rintro rfl
      exact le_rfl
  simp only [relationOperator,matrixTensorPower_apply,relationMatrix,Prod.mk.eta,
    Fintype.prod_ite_zero,Finset.prod_const_one,he]

theorem stochasticRelation_sum_coefficients_eq_zero (hn : k ≤ n)
    (c : StochasticLagrangian k → ℂ)
    (h : ∑ T, c T • relationOperator n T.carrier = 0) : ∀ T, c T = 0 := by
  intro T
  obtain ⟨X,Y,hXY⟩ := stochasticRelation_exists_entry_separator T hn
  have he := congrArg (fun A => A X Y) h
  simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,hXY,mul_ite,
    mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Matrix.zero_apply] using he

/-- Faithfulness of the uncompressed actual stochastic relation family in the
stable range; no statement of independence of the compressed family is used. -/
theorem stochasticRelation_linearIndependent (hn : k ≤ n) :
    LinearIndependent ℂ (fun T : StochasticLagrangian k => relationOperator n T.carrier) := by
  rw [Fintype.linearIndependent_iff]
  exact stochasticRelation_sum_coefficients_eq_zero hn

/-- A fixed family of polynomial relation coefficients that vanishes in every
stable tensor degree has every coefficient polynomial equal to zero. -/
theorem stochasticRelation_polynomial_coefficients_zero
    (p : StochasticLagrangian k → ℂ[X])
    (h : ∀ n, k ≤ n → ∑ T, (p T).eval ((2 : ℂ)^n) • relationOperator n T.carrier = 0) :
    ∀ T, p T = 0 := by
  intro T
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun j : ℕ => (2 : ℂ)^(k+j)) := by
    intro a b he
    change (2 : ℂ)^(k+a) = 2^(k+b) at he
    have hn : (2 : ℕ)^(k+a) = 2^(k+b) := by exact_mod_cast he
    have hh := Nat.pow_right_injective (by omega) hn
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨j,rfl⟩
  simp only [Set.mem_setOf_eq,Polynomial.eval_zero]
  exact stochasticRelation_sum_coefficients_eq_zero (Nat.le_add_right k j) _
    (h (k+j) (Nat.le_add_right k j)) T

/-- Continuation acts on fixed coefficients, so the varying physical matrix sizes
do not need to be identified. The conclusion includes n=0. -/
theorem stochasticRelation_polynomial_identity_all_n
    (p : StochasticLagrangian k → ℂ[X])
    (h : ∀ n, k ≤ n → ∑ T, (p T).eval ((2 : ℂ)^n) • relationOperator n T.carrier = 0) :
    ∀ n, ∑ T, (p T).eval ((2 : ℂ)^n) • relationOperator n T.carrier = 0 := by
  have hz := stochasticRelation_polynomial_coefficients_zero p h
  intro n
  simp only [hz,Polynomial.eval_zero,zero_smul,Finset.sum_const_zero]

end ExactCriticalCurve.Quantum
