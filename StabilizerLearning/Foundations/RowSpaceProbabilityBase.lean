import StabilizerLearning.Foundations.RowSpaceDefs
import Mathlib.FieldTheory.Finiteness
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

noncomputable section
namespace StabilizerLearning

variable {F : Type*} [Field F] [Fintype F]

/-- The probability is the mass of the actual event under the uniform matrix PMF. -/
def uniformMatrixProbability {r k : ℕ} (E : Set (Matrix (Fin r) (Fin k) F)) : ℝ :=
  ((PMF.uniformOfFintype (Matrix (Fin r) (Fin k) F)).toOuterMeasure E).toReal

theorem uniformMatrixProbability_eq_card {r k : ℕ}
    (E : Set (Matrix (Fin r) (Fin k) F)) :
    uniformMatrixProbability E =
      (Nat.card E : ℝ) / (Fintype.card F : ℝ) ^ (r * k) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  rw [uniformMatrixProbability, PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Nat.card_eq_fintype_card,
    Matrix, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ← pow_mul, Nat.mul_comm k r,
    ENNReal.toReal_pow]

/-- Count a genuine family of matrix events by classifying each matrix into its
subspace and retaining the actual rows. No row-generation estimate is assumed. -/
theorem card_subspaceClassified_matrices_le {r k a : ℕ}
    (C : Set (Submodule F (Fin k → F)))
    (hC : ∀ W ∈ C, Module.finrank F W = a)
    (E : Set (Matrix (Fin r) (Fin k) F))
    (classify : E → C)
    (hrows : ∀ Y : E, ∀ i, Y.val i ∈ (classify Y).val) :
    Nat.card E ≤ Nat.card C * Fintype.card F ^ (r * a) := by
  classical
  letI : Finite (Submodule F (Fin k → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin k → F) => (W : Set (Fin k → F)))
      SetLike.coe_injective
  letI : Fintype C := Fintype.ofFinite C
  let D : C → Type _ := fun W => Fin r → W.val
  let encode : E → Sigma D := fun Y => ⟨classify Y, fun i => ⟨Y.val i, hrows Y i⟩⟩
  have hinj : Function.Injective encode := by
    intro Y Z he
    apply Subtype.ext
    exact congrArg (fun t : Sigma D => fun i => (t.2 i : Fin k → F)) he
  calc
    Nat.card E ≤ Nat.card (Sigma D) := Nat.card_le_card_of_injective encode hinj
    _ = ∑ W : C, Nat.card (D W) := Nat.card_sigma
    _ = ∑ _W : C, Fintype.card F ^ (r * a) := by
      apply Finset.sum_congr rfl
      intro W _
      change Nat.card (Fin r → W.val) = _
      rw [Nat.card_fun, Module.natCard_eq_pow_finrank (K := F), hC W.val W.property]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, Nat.mul_comm a r]
    _ = Nat.card C * Fintype.card F ^ (r * a) := by
      simp [Nat.card_eq_fintype_card]

/-- The row-space event refers to its actual dimension and actual radical. -/
def rowSpaceEvent (F : Type*) [Field F] (r k a u : ℕ) :
    Set (Matrix (Fin r) (Fin k) F) :=
  {Y | Module.finrank F (rowSpace Y) = a ∧ Module.finrank F (rowRadical (rowSpace Y)) = u}

/-- Adjoining a prescribed vector really enlarges the row space. -/
def augmentedRowSpace {r k : ℕ} (v : Fin k → F) (Y : Matrix (Fin r) (Fin k) F) :
    Submodule F (Fin k → F) := rowSpace Y ⊔ Submodule.span F {v}

def augmentedRowSpaceEvent (F : Type*) [Field F] (r k a u : ℕ) (v : Fin k → F) :
    Set (Matrix (Fin r) (Fin k) F) :=
  {Y | Module.finrank F (augmentedRowSpace v Y) = a ∧
    Module.finrank F (rowRadical (augmentedRowSpace v Y)) = u}

theorem card_rowSpaceEvent_le (r k a u : ℕ) :
    Nat.card (rowSpaceEvent F r k a u) ≤
      Nat.card {W : Submodule F (Fin k → F) //
        Module.finrank F W = a ∧ Module.finrank F (rowRadical W) = u} *
          Fintype.card F ^ (r * a) := by
  apply card_subspaceClassified_matrices_le
    (C := {W | Module.finrank F W = a ∧ Module.finrank F (rowRadical W) = u})
    (fun _ h => h.1) (rowSpaceEvent F r k a u)
    (fun Y => ⟨rowSpace Y.val, Y.property⟩)
  intro Y i
  exact row_mem_rowSpace Y.val i

theorem card_augmentedRowSpaceEvent_le (r k a u : ℕ) (v : Fin k → F) :
    Nat.card (augmentedRowSpaceEvent F r k a u v) ≤
      Nat.card {W : Submodule F (Fin k → F) //
        Module.finrank F W = a ∧ Module.finrank F (rowRadical W) = u} *
          Fintype.card F ^ (r * a) := by
  apply card_subspaceClassified_matrices_le
    (C := {W | Module.finrank F W = a ∧ Module.finrank F (rowRadical W) = u})
    (fun _ h => h.1) (augmentedRowSpaceEvent F r k a u v)
    (fun Y => ⟨augmentedRowSpace v Y.val, Y.property⟩)
  intro Y i
  exact (show rowSpace Y.val ≤ augmentedRowSpace v Y.val from le_sup_left)
    (row_mem_rowSpace Y.val i)

theorem uniformMatrixProbability_mono {r k : ℕ}
    {E D : Set (Matrix (Fin r) (Fin k) F)} (h : E ⊆ D) :
    uniformMatrixProbability E ≤ uniformMatrixProbability D := by
  rw [uniformMatrixProbability_eq_card, uniformMatrixProbability_eq_card]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.card_le_card_of_injective (Set.inclusion h) (Set.inclusion_injective h)

/-- Exact exponent simplification uses integer subtraction, even for infeasible
parameters. It never clips a negative dimension difference to zero. -/
theorem rowSpace_probability_exponent_identity (q : ℝ) (hq : 0 < q) (r k a u : ℕ) :
    (q ^ ((a : ℤ) * ((k : ℤ) - a) - (u * (u + 1) / 2 : ℕ)) * q ^ (r * a)) /
      q ^ (r * k) =
        q ^ (-((k : ℤ) - a) * ((r : ℤ) - a) - (u * (u + 1) / 2 : ℕ)) := by
  rw [← zpow_natCast q (r * a), ← zpow_natCast q (r * k),
    ← zpow_add₀ (ne_of_gt hq), ← zpow_sub₀ (ne_of_gt hq)]
  congr 1
  push_cast
  ring

end StabilizerLearning
