import ExactCriticalCurve.Quantum.CSS
import ExactCriticalCurve.Foundations.TensorTrace
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-! # Actual closed linear constraints and relation traces

A word of p relations uses p + 1 vertices with equal endpoints.
In particular, the empty word retains one free vertex and its trace is
the ambient dimension, rather than the cardinality of a singleton.

This proves the individual trace monomials used in paper/main.tex
lines 2783–2793 directly from matrix entries. It does not use or prove
the GNW stabilizer moment identity or a physical module decomposition.
-/

noncomputable section

open scoped BigOperators Matrix
open Matrix Classical

namespace ExactCriticalCurve.Quantum

open Binary

private theorem sum_fin_cons {α : Type*} [Fintype α] (p : ℕ)
    (f : (Fin (p + 1) → α) → ℂ) :
    ∑ v, f v = ∑ x, ∑ v : Fin p → α, f (Fin.cons x v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (p + 1) => α)).sum_comp f]
  exact Fintype.sum_prod_type _

private def pathWeight {α : Type*} {p : ℕ}
    (A : Fin p → Matrix α α ℂ) (x : α) (v : Fin p → α) : ℂ :=
  ∏ i, A i ((Fin.cons x v : Fin (p + 1) → α) i.castSucc) (v i)

private theorem pathWeight_cons {α : Type*} {p : ℕ}
    (A : Fin (p + 1) → Matrix α α ℂ) (x z : α) (v : Fin p → α) :
    pathWeight A x (Fin.cons z v) =
      A 0 x z * pathWeight (fun i => A i.succ) z v := by
  simp only [pathWeight, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero,
    Fin.castSucc_succ, Fin.cons_succ]

private theorem orderedProduct_apply {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℕ) (A : Fin p → Matrix α α ℂ) (x y : α) :
    (List.ofFn A).prod x y =
      ∑ v : Fin p → α,
        if (Fin.cons x v : Fin (p + 1) → α) (Fin.last p) = y then pathWeight A x v else 0 := by
  induction p generalizing x y with
  | zero => simp [pathWeight, Matrix.one_apply]
  | succ p ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply, sum_fin_cons]
    apply Finset.sum_congr rfl
    intro z _
    rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [pathWeight_cons]
    simp only [Fin.cons_last]
    split_ifs <;> simp

/-- The trace is the actual finite sum over paths with equal endpoints. -/
theorem orderedProduct_trace_paths {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℕ) (A : Fin p → Matrix α α ℂ) :
    Matrix.trace (List.ofFn A).prod =
      ∑ v : Fin (p + 1) → α,
        if v 0 = v (Fin.last p)
        then ∏ i : Fin p, A i (v i.castSucc) (v i.succ) else 0 := by
  rw [sum_fin_cons]
  simp only [Matrix.trace, Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [orderedProduct_apply]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fin.cons_zero, Fin.cons_succ, pathWeight, eq_comm]

/-- The genuine linear space of closed paths obeying the specified relations. -/
def relationClosedSpace {k p : ℕ}
    (T : Fin p → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Submodule (ZMod 2) (Fin (p + 1) → BinaryVector k) where
  carrier := {v | v 0 = v (Fin.last p) ∧
    ∀ i : Fin p, (v i.castSucc, v i.succ) ∈ T i}
  zero_mem' := ⟨rfl, fun i => (T i).zero_mem⟩
  add_mem' hv hw := ⟨congrArg₂ (· + ·) hv.1 hw.1,
    fun i => (T i).add_mem (hv.2 i) (hw.2 i)⟩
  smul_mem' c _ hv := ⟨congrArg (c • ·) hv.1,
    fun i => (T i).smul_mem c (hv.2 i)⟩

@[simp] theorem mem_relationClosedSpace {k p : ℕ}
    (T : Fin p → Submodule (ZMod 2) (BinaryVector k × BinaryVector k))
    (v : Fin (p + 1) → BinaryVector k) :
    v ∈ relationClosedSpace T ↔
      v 0 = v (Fin.last p) ∧ ∀ i : Fin p, (v i.castSucc, v i.succ) ∈ T i := Iff.rfl


/-- The exact single-column trace counts the actual closed linear solutions. -/
theorem relationMatrix_orderedProduct_trace_card {k p : ℕ}
    (T : Fin p → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Matrix.trace (List.ofFn (fun i => relationMatrix (T i))).prod =
      (Nat.card (relationClosedSpace T) : ℂ) := by
  rw [orderedProduct_trace_paths]
  simp only [relationMatrix, Fintype.prod_boole, ← ite_and]
  simp_rw [← mem_relationClosedSpace]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- The closed solution count is computed from its actual binary dimension. -/
theorem relationClosedSpace_card {k p : ℕ}
    (T : Fin p → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Nat.card (relationClosedSpace T) =
      2 ^ Module.finrank (ZMod 2) (relationClosedSpace T) := by
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- The single-column trace is the resulting power of two. -/
theorem relationMatrix_orderedProduct_trace {k p : ℕ}
    (T : Fin p → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Matrix.trace (List.ofFn (fun i => relationMatrix (T i))).prod =
      (2 : ℂ) ^ Module.finrank (ZMod 2) (relationClosedSpace T) := by
  rw [relationMatrix_orderedProduct_trace_card, relationClosedSpace_card,
    Nat.cast_pow, Nat.cast_ofNat]

/-- Every physical-column trace is an actual monomial in D = 2^n. -/
theorem relationOperator_orderedProduct_trace {k p : ℕ} (n : ℕ)
    (T : Fin p → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Matrix.trace (List.ofFn (fun i => relationOperator n (T i))).prod =
      ((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) (relationClosedSpace T) := by
  have h := matrixTensorPower_list_prod_trace n
    (List.ofFn (fun i => relationMatrix (T i)))
  rw [List.map_ofFn] at h
  change Matrix.trace (List.ofFn (fun i => relationOperator n (T i))).prod =
    (Matrix.trace (List.ofFn (fun i => relationMatrix (T i))).prod) ^ n at h
  rw [h, relationMatrix_orderedProduct_trace, ← pow_mul, Nat.mul_comm, pow_mul]

/-- An empty word has one free vertex, with no relation constraint. -/
theorem relationClosedSpace_zero {k : ℕ}
    (T : Fin 0 → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    relationClosedSpace T = ⊤ := by
  ext v
  simp [mem_relationClosedSpace]

/-- The empty word has the ambient binary dimension, including k = 0. -/
theorem relationClosedSpace_zero_finrank {k : ℕ}
    (T : Fin 0 → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Module.finrank (ZMod 2) (relationClosedSpace T) = k := by
  rw [relationClosedSpace_zero, finrank_top]
  simp [Module.finrank_pi_fintype, BinaryVector]

/-- Thus the empty matrix product has trace D^k, with the correct tensor ambient space. -/
theorem relationOperator_emptyProduct_trace {k : ℕ} (n : ℕ)
    (T : Fin 0 → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Matrix.trace (List.ofFn (fun i => relationOperator n (T i))).prod =
      ((2 : ℂ) ^ n) ^ k := by
  rw [relationOperator_orderedProduct_trace, relationClosedSpace_zero_finrank]

end ExactCriticalCurve.Quantum
