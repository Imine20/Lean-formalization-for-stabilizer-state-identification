import StabilizerLearning.FiniteCopy.LabelTransport
import StabilizerLearning.FiniteCopy.WeightedPOVM

/-! Exact identification averaged over the original finite state ensemble.
Transport uses bijections of states, reports and Hilbert bases.  The hidden
mixture is derived from the full uniform prior, after taking tensor powers. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning

def uniformTargetSuccess {Ω X Y : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype X] [Fintype Y] (ρ : X → Matrix Ω Ω ℂ) (target : X → Y)
    (M : Quantum.POVM Ω Y) : ℝ :=
  uniformFiniteMean (fun x => Quantum.born (M.effect (target x)) (ρ x))

theorem uniformFiniteMean_prod {Y H : Type*} [Fintype Y] [Fintype H]
    (f : Y × H → ℝ) :
    uniformFiniteMean f =
      uniformFiniteMean (fun y => uniformFiniteMean (fun h => f (y, h))) := by
  simp only [uniformFiniteMean, Nat.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    Finset.sum_div]
  simp only [div_div, mul_comm]

/-- The independent visible/hidden uniform laws are a consequence of the
uniform law on the product parameter space, including zero-dimensional factors. -/
theorem uniformTargetSuccess_prod {Ω Y H : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype Y] [Fintype H] (ρ : Y → H → Matrix Ω Ω ℂ)
    (M : Quantum.POVM Ω Y) :
    uniformTargetSuccess (fun x : Y × H => ρ x.1 x.2) Prod.fst M =
      hiddenUniformLabelSuccess ρ M := by
  unfold uniformTargetSuccess hiddenUniformLabelSuccess uniformLabelSuccess
  rw [uniformFiniteMean_prod]
  congr 1
  funext y
  simp only [uniformFiniteMean, hiddenUniformState, born_real_smul, born_sum,
    div_eq_mul_inv, mul_comm]

/-- A complete relabeling of the state ensemble preserves its original uniform
prior, without a uniform-fiber or counting assumption. -/
theorem uniformTargetSuccess_state_equiv {Ω X X' Y : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype X] [Fintype X'] [Fintype Y]
    (e : X ≃ X') (ρ : X' → Matrix Ω Ω ℂ) (target : X' → Y)
    (M : Quantum.POVM Ω Y) :
    uniformTargetSuccess (ρ ∘ e) (target ∘ e) M =
      uniformTargetSuccess ρ target M := by
  exact uniformFiniteMean_comp_equiv e (fun x => Quantum.born (M.effect (target x)) (ρ x))

/-- Report transport is a bijection of all normalized positive measurements. -/
theorem uniformTargetSuccess_report_equiv {Ω X Y Y' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype X] [Fintype Y] [Fintype Y']
    (e : Y ≃ Y') (ρ : X → Matrix Ω Ω ℂ) (target : X → Y)
    (M : Quantum.POVM Ω Y) :
    uniformTargetSuccess ρ (e ∘ target) (Quantum.POVM.relabel e M) =
      uniformTargetSuccess ρ target M := by
  simp [uniformTargetSuccess, Quantum.POVM.relabel_effect]

/-- The basis transport applies to every collective POVM and every exact target. -/
theorem uniformTargetSuccess_basis_equiv {Ω Ω' X Y : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype X] [Fintype Y] (e : Ω ≃ Ω')
    (ρ : X → Matrix Ω Ω ℂ) (target : X → Y) (M : Quantum.POVM Ω Y) :
    uniformTargetSuccess (fun x => (ρ x).submatrix e.symm e.symm) target
        (Quantum.POVM.reindex e M) = uniformTargetSuccess ρ target M := by
  simp only [uniformTargetSuccess, Quantum.POVM.reindex_born]

/-- The actual tensor-copy basis bijection, also for zero copies. -/
def copyBasisEquiv {Ω Ω' : Type*} (e : Ω ≃ Ω') (k : ℕ) :
    (Fin k → Ω) ≃ (Fin k → Ω') := Equiv.piCongrRight (fun _ => e)

theorem tensorPower_basis_equiv {Ω Ω' : Type*} (e : Ω ≃ Ω')
    (ρ : Matrix Ω Ω ℂ) (k : ℕ) :
    Quantum.tensorPower (ρ.submatrix e.symm e.symm) k =
      (Quantum.tensorPower ρ k).submatrix
        (copyBasisEquiv e k).symm (copyBasisEquiv e k).symm := rfl

def experimentPOVMEquiv {Ω Ω' Y Y' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype Y] [Fintype Y'] (eb : Ω ≃ Ω') (er : Y ≃ Y') :
    Quantum.POVM Ω Y ≃ Quantum.POVM Ω' Y' :=
  (Quantum.POVM.reindexEquiv eb).trans (Quantum.POVM.relabel er)

/-- A reusable exact transport rule.  Its state and target identities must be
proved at the physical instantiation; it does not assert a physical equivalence. -/
theorem uniformTargetSuccess_transport {Ω Ω' X X' Y Y' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (eb : Ω ≃ Ω') (ex : X ≃ X') (er : Y ≃ Y')
    (ρ : X → Matrix Ω Ω ℂ) (ρ' : X' → Matrix Ω' Ω' ℂ)
    (t : X → Y) (t' : X' → Y')
    (hρ : ∀ x, ρ' (ex x) = (ρ x).submatrix eb.symm eb.symm)
    (ht : ∀ x, t' (ex x) = er (t x)) (M : Quantum.POVM Ω Y) :
    uniformTargetSuccess ρ' t' (experimentPOVMEquiv eb er M) =
      uniformTargetSuccess ρ t M := by
  rw [← uniformTargetSuccess_state_equiv ex]
  unfold uniformTargetSuccess
  congr 1
  funext x
  simp only [Function.comp_apply, hρ, ht, experimentPOVMEquiv, Equiv.trans_apply,
    Quantum.POVM.relabel_effect, Equiv.symm_apply_apply]
  exact Quantum.POVM.reindex_born eb M (ρ x) (t x)

/-- Equality of the complete ranges of arbitrary measurement scores. -/
theorem range_uniformTargetSuccess_transport {Ω Ω' X X' Y Y' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (eb : Ω ≃ Ω') (ex : X ≃ X') (er : Y ≃ Y')
    (ρ : X → Matrix Ω Ω ℂ) (ρ' : X' → Matrix Ω' Ω' ℂ)
    (t : X → Y) (t' : X' → Y')
    (hρ : ∀ x, ρ' (ex x) = (ρ x).submatrix eb.symm eb.symm)
    (ht : ∀ x, t' (ex x) = er (t x)) :
    Set.range (uniformTargetSuccess ρ' t') =
      Set.range (uniformTargetSuccess ρ t) := by
  ext s
  constructor
  · rintro ⟨M, rfl⟩
    obtain ⟨N, rfl⟩ := (experimentPOVMEquiv eb er).surjective M
    exact ⟨N, (uniformTargetSuccess_transport eb ex er ρ ρ' t t' hρ ht N).symm⟩
  · rintro ⟨M, rfl⟩
    exact ⟨experimentPOVMEquiv eb er M,
      uniformTargetSuccess_transport eb ex er ρ ρ' t t' hρ ht M⟩

end StabilizerLearning
