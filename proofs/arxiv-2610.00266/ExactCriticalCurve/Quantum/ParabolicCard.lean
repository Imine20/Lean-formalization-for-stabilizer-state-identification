import ExactCriticalCurve.Quantum.ParabolicFixer
import ExactCriticalCurve.Foundations.BinaryAlternatingCard
import Mathlib.GroupTheory.Index

/-! # Cardinality of the actual ambient ordinary parabolic kernel -/
noncomputable section
open Classical
namespace ExactCriticalCurve

def linearAutomorphismCongr {R V W : Type*} [Field R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (e : V ≃ₗ[R] W) : (V ≃ₗ[R] V) ≃ (W ≃ₗ[R] W) where
  toFun f := e.symm.trans (f.trans e)
  invFun f := e.trans (f.trans e.symm)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

namespace Quantum
open Binary
variable {k : ℕ}

def parabolicRestrictionKernelEquiv (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) :
    (stochasticParabolicRestriction N hN).ker ≃ stochasticOrthogonalFixer N where
  toFun g := ⟨g.val.val, (stochasticParabolicRestriction_eq_one_iff N hN g.val).mp g.property⟩
  invFun g := ⟨⟨g.val, stochasticOrthogonalFixer_le_parabolic N hN g.property⟩,
    (stochasticParabolicRestriction_eq_one_iff N hN _).mpr g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stochasticOrthogonalFixer_card (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) :
    Nat.card (stochasticOrthogonalFixer N) = 2 ^ (Module.finrank (ZMod 2) N).choose 2 := by
  rw [Nat.card_congr (orthogonalFixerAlternatingEquiv N hN), binaryAlternating_card,
    orthogonalQuotient_finrank]

theorem stochasticParabolicKernel_card_factor
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Nat.card (stochasticParabolicKernel N) =
      Nat.card (PointedQuotientAutomorphism (N.comap (orthogonal N).subtype)
        (⟨allOnes k, hN.allOnes_mem_orthogonal⟩ : orthogonal N)) *
      2 ^ (Module.finrank (ZMod 2) N).choose 2 := by
  let f := stochasticParabolicRestriction N hN
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.mpr (stochasticParabolicRestriction_surjective N hN)
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, hr, Subgroup.card_top,
    Nat.card_congr (parabolicRestrictionKernelEquiv N hN), stochasticOrthogonalFixer_card N hN] at hc
  exact hc.symm.trans (Nat.mul_comm _ _)

/-- Ordinary Wu exclusion guarantees that subtracting its line removes exactly one dimension. -/
theorem ordinaryParabolicQuotient_finrank_pos {r : ℕ} (N : OrdinaryDefect k r) :
    0 < Module.finrank (ZMod 2) (CSSQuotient N.val) :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨cssQuotientWu N.val N.property.1, ordinaryCSSQuotient_wu_ne_zero N⟩

theorem ordinaryParabolic_rank_bound {r : ℕ} (N : OrdinaryDefect k r) : 2 * r < k := by
  have hp := ordinaryParabolicQuotient_finrank_pos N
  have hd := cssQuotient_finrank_add N.val N.property.1
  rw [N.property.2.1] at hd
  omega

theorem ordinaryParabolicKernel_card_intrinsic {r : ℕ} (N : OrdinaryDefect k r) :
    Nat.card (stochasticParabolicKernel N.val) =
      Nat.card (N.val ≃ₗ[ZMod 2] N.val) *
        2 ^ (r * (Module.finrank (ZMod 2) (CSSQuotient N.val) - 1)) *
        2 ^ r.choose 2 := by
  have hN := N.property.1
  let e := Submodule.comapSubtypeEquivOfLe hN.le_orthogonal
  have hd : Module.finrank (ZMod 2) (N.val.comap (orthogonal N.val).subtype) = r :=
    e.finrank_eq.trans N.property.2.1
  have hcard : Nat.card ((N.val.comap (orthogonal N.val).subtype) ≃ₗ[ZMod 2]
      (N.val.comap (orthogonal N.val).subtype)) = Nat.card (N.val ≃ₗ[ZMod 2] N.val) :=
    Nat.card_congr (linearAutomorphismCongr e)
  rw [stochasticParabolicKernel_card_factor N.val hN,
    pointedQuotientAutomorphism_card _ _ (ordinaryCSSQuotient_wu_ne_zero N),
    hcard, hd, N.property.2.1]
  simp only [Nat.card_eq_fintype_card, ZMod.card]
  rw [Nat.mul_comm (Module.finrank (ZMod 2) (CSSQuotient N.val) - 1) r]

/-- Exact κ for the subgroup of actual ambient full-q isometries preserving N and
inducing identity on N-perp/N. Every factor is counted through explicit parameters. -/
theorem ordinaryParabolicKernel_card {r : ℕ} (N : OrdinaryDefect k r) :
    Nat.card (stochasticParabolicKernel N.val) =
      Nat.card ((Fin r → ZMod 2) ≃ₗ[ZMod 2] (Fin r → ZMod 2)) *
        2 ^ (r * (k - 2 * r - 1)) * 2 ^ r.choose 2 := by
  let e : N.val ≃ₗ[ZMod 2] (Fin r → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using N.property.2.1)
  rw [ordinaryParabolicKernel_card_intrinsic N,
    Nat.card_congr (linearAutomorphismCongr e), cssQuotient_finrank N.val N.property.1,
    N.property.2.1]

end Quantum
end ExactCriticalCurve
