import ExactCriticalCurve.Quantum.CSSOverlapSphericalRow
import ExactCriticalCurve.Counting.BinaryGaussian

noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary Counting

/-- Every ambient intersection is exactly one actual subspace of the defect. -/
def cssIntersectionSubspacesEquiv {k r : ℕ} (N : OrdinaryDefect k r)
    (ell : Fin (r+1)) :
    CSSIntersectionsAtCodimension N ell ≃ BinarySubspaces N.val (r-ell.val) :=
  N.val.mapIic.symm.toEquiv.subtypeEquiv (fun K => by
    change finrank (ZMod 2) K.val + ell.val = r ↔
      finrank (ZMod 2) (K.val.comap N.val.subtype) = r-ell.val
    rw [(Submodule.comapSubtypeEquivOfLe K.property).finrank_eq]
    have h := ell.isLt
    omega)

/-- The actual nondegenerate dot pairing identifies dimension and codimension strata. -/
def binarySubspacesOrthogonalEquiv (r ell : ℕ) (h : ell ≤ r) :
    BinarySubspaces (BinaryVector r) (r-ell) ≃ BinarySubspaces (BinaryVector r) ell where
  toFun K := ⟨orthogonal K.val, by
    have hd := finrank_orthogonal_add K.val
    rw [K.property] at hd
    omega⟩
  invFun K := ⟨orthogonal K.val, by
    have hd := finrank_orthogonal_add K.val
    rw [K.property] at hd
    omega⟩
  left_inv K := Subtype.ext (LinearMap.BilinForm.orthogonal_orthogonal
    (binaryDotForm_nondegenerate r) (binaryDotForm_isRefl r) K.val)
  right_inv K := Subtype.ext (LinearMap.BilinForm.orthogonal_orthogonal
    (binaryDotForm_nondegenerate r) (binaryDotForm_isRefl r) K.val)

/-- This Gaussian coefficient counts the full actual intersection stratum. -/
theorem cssIntersectionsAtCodimension_card {k r : ℕ} (N : OrdinaryDefect k r)
    (ell : Fin (r+1)) :
    Nat.card (CSSIntersectionsAtCodimension N ell) = binaryGaussian r ell.val := by
  let e : N.val ≃ₗ[ZMod 2] BinaryVector r :=
    LinearEquiv.ofFinrankEq _ _ (by simpa [BinaryVector] using N.property.2.1)
  rw [Nat.card_congr (cssIntersectionSubspacesEquiv N ell),
    Nat.card_congr (subspacesOfFinrankEquiv e (r-ell.val)),
    Nat.card_congr (binarySubspacesOrthogonalEquiv r ell.val (by omega))]
  rfl

end ExactCriticalCurve.Quantum
