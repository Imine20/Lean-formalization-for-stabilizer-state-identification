import ExactCriticalCurve.Quantum.CSSQuotientIsometryGroup

/-! # Actual ordinary defect orbit and stabilizer factorization of the ambient group -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary
variable {k r : ℕ}

def ordinaryDefectImage (g : StochasticIsometryGroup k) (N : OrdinaryDefect k r) :
    OrdinaryDefect k r :=
  ⟨stochasticSubspace g N.val,
    stochasticSubspace_isDefect g N.property.1,
    (stochasticSubspace_finrank g N.val).trans N.property.2.1,
    fun h => N.property.2.2 ((allOnes_mem_stochasticSubspace g N.val).mp h)⟩

instance ordinaryDefectMulAction : MulAction (StochasticIsometryGroup k) (OrdinaryDefect k r) where
  smul := ordinaryDefectImage
  one_smul N := Subtype.ext (stochasticSubspace_one N.val)
  mul_smul g h N := Subtype.ext (stochasticSubspace_mul g h N.val)

/-- The ambient subgroup is precisely the stabilizer for the genuine ordinary-defect action. -/
theorem stochasticDefectStabilizer_eq_mulAction (N : OrdinaryDefect k r) :
    stochasticDefectStabilizer N.val = MulAction.stabilizer (StochasticIsometryGroup k) N := by
  ext g
  change stochasticSubspace g N.val = N.val ↔ ordinaryDefectImage g N = N
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem ordinaryDefect_mem_orbit (N M : OrdinaryDefect k r) :
    M ∈ MulAction.orbit (StochasticIsometryGroup k) N := by
  obtain ⟨g,hg⟩ := exists_stochasticSubspace_eq N.val M.val N.property.1 M.property.1
    (N.property.2.1.trans M.property.2.1.symm) (iff_of_false N.property.2.2 M.property.2.2)
  exact ⟨g, Subtype.ext hg⟩

def ordinaryDefectOrbitEquiv (N : OrdinaryDefect k r) :
    MulAction.orbit (StochasticIsometryGroup k) N ≃ OrdinaryDefect k r where
  toFun := Subtype.val
  invFun M := ⟨M, ordinaryDefect_mem_orbit N M⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ordinaryStochasticGroup_card_orbit_stabilizer (N : OrdinaryDefect k r) :
    Nat.card (StochasticIsometryGroup k) =
      Nat.card (OrdinaryDefect k r) * Nat.card (stochasticDefectStabilizer N.val) := by
  calc
    Nat.card (StochasticIsometryGroup k) =
        Nat.card (MulAction.orbit (StochasticIsometryGroup k) N ×
          MulAction.stabilizer (StochasticIsometryGroup k) N) :=
      (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (StochasticIsometryGroup k) N)).symm
    _ = Nat.card (OrdinaryDefect k r) * Nat.card (stochasticDefectStabilizer N.val) := by
      rw [Nat.card_prod, Nat.card_congr (ordinaryDefectOrbitEquiv N),
        ← stochasticDefectStabilizer_eq_mulAction N]

/-- All three factors count actual mathematical objects: defects, ambient kernel,
and the full-q/Wu isometry group of the actual CSS quotient. -/
theorem ordinaryStochasticGroup_card_factorization (N : OrdinaryDefect k r) :
    Nat.card (StochasticIsometryGroup k) =
      Nat.card (OrdinaryDefect k r) * Nat.card (stochasticParabolicKernel N.val) *
        Nat.card (CSSQuotientIsometryGroup N.val N.property.1) := by
  rw [ordinaryStochasticGroup_card_orbit_stabilizer N,
    stochasticDefectStabilizer_card N.val N.property.1, Nat.mul_assoc]

theorem ordinaryStochasticGroup_card_factorization_explicit (N : OrdinaryDefect k r) :
    Nat.card (StochasticIsometryGroup k) =
      Nat.card (OrdinaryDefect k r) *
        (Nat.card ((Fin r → ZMod 2) ≃ₗ[ZMod 2] (Fin r → ZMod 2)) *
          2 ^ (r * (k - 2*r - 1)) * 2 ^ r.choose 2) *
        Nat.card (CSSQuotientIsometryGroup N.val N.property.1) := by
  rw [ordinaryStochasticGroup_card_factorization N, ordinaryParabolicKernel_card N]

end ExactCriticalCurve.Quantum
