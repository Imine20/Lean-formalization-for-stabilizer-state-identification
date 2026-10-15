import StabilizerLearning.FiniteCopy.TensorEnsemble

noncomputable section
namespace StabilizerLearning
open scoped BigOperators

/-- Literal uniform finite mean; the denominator is the full finite alphabet. -/
def uniformFiniteMean {I : Type*} [Fintype I] (f : I → ℝ) : ℝ :=
  (∑ i, f i) / (Nat.card I : ℝ)

theorem uniformFiniteMean_comp_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (f : J → ℝ) :
    uniformFiniteMean (fun i => f (e i)) = uniformFiniteMean f := by
  unfold uniformFiniteMean
  rw [e.sum_comp, Nat.card_congr e]

/-- An actual hidden-label average of matrix states. -/
def hiddenUniformState {Ω H : Type*} [Fintype H]
    (ρ : H → Matrix Ω Ω ℂ) : Matrix Ω Ω ℂ :=
  (Nat.card H : ℝ)⁻¹ • ∑ h, ρ h

theorem hiddenUniformState_comp_equiv {Ω H H' : Type*}
    [Fintype H] [Fintype H'] (e : H ≃ H')
    (ρ : H' → Matrix Ω Ω ℂ) :
    hiddenUniformState (fun h => ρ (e h)) = hiddenUniformState ρ := by
  unfold hiddenUniformState
  rw [e.sum_comp, Nat.card_congr e]

namespace Quantum.POVM
variable {Ω Y Y' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Y] [Fintype Y']

/-- Relabel every report of an arbitrary POVM by a genuine bijection. The
inverse is proved, so no admissible measurement is removed or added. -/
def relabel (e : Y ≃ Y') : POVM Ω Y ≃ POVM Ω Y' where
  toFun M :=
    { effect := fun y => M.effect (e.symm y)
      positive := fun y => M.positive (e.symm y)
      normalized := by rw [e.symm.sum_comp, M.normalized] }
  invFun M :=
    { effect := fun y => M.effect (e y)
      positive := fun y => M.positive (e y)
      normalized := by rw [e.sum_comp, M.normalized] }
  left_inv M := by
    apply eq_of_effect_eq
    funext y
    exact congrArg M.effect (e.symm_apply_apply y)
  right_inv M := by
    apply eq_of_effect_eq
    funext y
    exact congrArg M.effect (e.apply_symm_apply y)

@[simp] theorem relabel_effect (e : Y ≃ Y') (M : POVM Ω Y) (y : Y') :
    (relabel e M).effect y = M.effect (e.symm y) := rfl

end Quantum.POVM

/-- Uniform exact identification score, with one report for each visible label. -/
def uniformLabelSuccess {Ω Y : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Y]
    (ρ : Y → Matrix Ω Ω ℂ) (M : Quantum.POVM Ω Y) : ℝ :=
  uniformFiniteMean (fun y => Quantum.born (M.effect y) (ρ y))

/-- The hidden labels are uniformly mixed for each visible label before the
uniform visible exact-identification score is evaluated. -/
def hiddenUniformLabelSuccess {Ω Y H : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype Y] [Fintype H] (ρ : Y → H → Matrix Ω Ω ℂ)
    (M : Quantum.POVM Ω Y) : ℝ :=
  uniformLabelSuccess (fun y => hiddenUniformState (ρ y)) M

theorem uniformLabelSuccess_relabel {Ω Y Y' : Type*} [Fintype Ω]
    [DecidableEq Ω] [Fintype Y] [Fintype Y'] (e : Y ≃ Y')
    (ρ : Y' → Matrix Ω Ω ℂ) (M : Quantum.POVM Ω Y) :
    uniformLabelSuccess (fun y => ρ (e y)) M =
      uniformLabelSuccess ρ (Quantum.POVM.relabel e M) := by
  have h := uniformFiniteMean_comp_equiv e
    (fun y => Quantum.born ((Quantum.POVM.relabel e M).effect y) (ρ y))
  simpa only [uniformLabelSuccess, Quantum.POVM.relabel_effect,
    Equiv.symm_apply_apply] using h

/-- Both original uniform laws are transported, not replaced by new priors. -/
theorem hiddenUniformLabelSuccess_relabel {Ω Y Y' H H' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Y] [Fintype Y']
    [Fintype H] [Fintype H'] (ev : Y ≃ Y') (eh : H ≃ H')
    (ρ : Y' → H' → Matrix Ω Ω ℂ) (M : Quantum.POVM Ω Y) :
    hiddenUniformLabelSuccess (fun y h => ρ (ev y) (eh h)) M =
      hiddenUniformLabelSuccess ρ (Quantum.POVM.relabel ev M) := by
  unfold hiddenUniformLabelSuccess
  simp_rw [hiddenUniformState_comp_equiv]
  exact uniformLabelSuccess_relabel ev (fun y => hiddenUniformState (ρ y)) M

/-- The complete sets of measurement scores are equal under report relabeling. -/
theorem range_uniformLabelSuccess_relabel {Ω Y Y' : Type*} [Fintype Ω]
    [DecidableEq Ω] [Fintype Y] [Fintype Y'] (e : Y ≃ Y')
    (ρ : Y' → Matrix Ω Ω ℂ) :
    Set.range (uniformLabelSuccess (fun y => ρ (e y))) =
      Set.range (uniformLabelSuccess ρ) := by
  ext s
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨Quantum.POVM.relabel e M, (uniformLabelSuccess_relabel e ρ M).symm⟩
  · rintro ⟨M, rfl⟩
    let N := (Quantum.POVM.relabel e).symm M
    refine ⟨N, ?_⟩
    rw [uniformLabelSuccess_relabel]
    exact congrArg (uniformLabelSuccess ρ) ((Quantum.POVM.relabel e).apply_symm_apply M)

theorem range_hiddenUniformLabelSuccess_relabel {Ω Y Y' H H' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Y] [Fintype Y']
    [Fintype H] [Fintype H'] (ev : Y ≃ Y') (eh : H ≃ H')
    (ρ : Y' → H' → Matrix Ω Ω ℂ) :
    Set.range (hiddenUniformLabelSuccess (fun y h => ρ (ev y) (eh h))) =
      Set.range (hiddenUniformLabelSuccess ρ) := by
  unfold hiddenUniformLabelSuccess
  simp_rw [hiddenUniformState_comp_equiv]
  exact range_uniformLabelSuccess_relabel ev (fun y => hiddenUniformState (ρ y))

/-- No optimizer-existence hypothesis is needed: the optimized success values
agree because the full ranges of arbitrary POVM scores agree. -/
theorem optimal_hiddenUniformLabelSuccess_relabel {Ω Y Y' H H' : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Y] [Fintype Y']
    [Fintype H] [Fintype H'] (ev : Y ≃ Y') (eh : H ≃ H')
    (ρ : Y' → H' → Matrix Ω Ω ℂ) :
    sSup (Set.range (hiddenUniformLabelSuccess (fun y h => ρ (ev y) (eh h)))) =
      sSup (Set.range (hiddenUniformLabelSuccess ρ)) := by
  rw [range_hiddenUniformLabelSuccess_relabel ev eh ρ]

/-- Instantiation to the concrete normalized character densities, retaining
the supplied original visible and hidden label alphabets through bijections. -/
theorem character_density_uniform_success_transport
    {Ω V L Y H : Type*} [Fintype Ω] [DecidableEq Ω]
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    [Fintype Y] [Fintype H] (ev : Y ≃ AddChar V ℂ) (eh : H ≃ AddChar L ℂ)
    (code : Ω → V × L) (M : Quantum.POVM Ω Y) :
    hiddenUniformLabelSuccess
      (fun y h => CharacterEnsemble.density code (ev y) (eh h)) M =
    uniformLabelSuccess (CharacterEnsemble.conditioned code) (Quantum.POVM.relabel ev M) := by
  simpa only [hiddenUniformLabelSuccess, hiddenUniformState,
    CharacterEnsemble.conditioned, Nat.card_eq_fintype_card] using
    hiddenUniformLabelSuccess_relabel ev eh (CharacterEnsemble.density code) M

/-- The same transport applies to actual tensor-copy densities in matrix basis;
the hidden average is precisely the tensor ensemble proved earlier. -/
theorem tensor_character_uniform_success_transport
    {ι F V L Y H : Type*} [Fintype ι] [DecidableEq ι] [Fintype F]
    [DecidableEq F] [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    [Fintype Y] [Fintype H] (ev : Y ≃ AddChar V ℂ) (eh : H ≃ AddChar L ℂ)
    (code : (ι → F) → V × L) (k : ℕ)
    (M : Quantum.POVM (Matrix ι (Fin k) F) Y) :
    hiddenUniformLabelSuccess
      (fun y h => Quantum.tensorPowerMatrixBasis
        (CharacterEnsemble.density code (ev y) (eh h)) k) M =
    uniformLabelSuccess (CharacterEnsemble.conditionedTensorPowerMatrixBasis code k)
      (Quantum.POVM.relabel ev M) := by
  simpa only [hiddenUniformLabelSuccess, hiddenUniformState,
    CharacterEnsemble.conditionedTensorPowerMatrixBasis, Nat.card_eq_fintype_card] using
    hiddenUniformLabelSuccess_relabel ev eh
      (fun y h => Quantum.tensorPowerMatrixBasis (CharacterEnsemble.density code y h) k) M

end StabilizerLearning
