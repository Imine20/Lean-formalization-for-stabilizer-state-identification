import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Data.ZMod.Basic

/-!
# Exact count of symmetric matrices

This proves the independent symmetric-entry count used in the source paper's
Lagrangian-shell argument and in its free-block completion count. It does not
assert the Lagrangian graph correspondence, a prescribed-rank count, or the
complete shell formula.

The result holds for every finite entry type. In particular, it holds over
`ZMod p` for every positive modulus, so there is no exclusion of characteristic
two and no division in the coefficient field. The exponent is a natural-number
quotient. The zero-dimensional case is included.
-/

namespace StabilizerLearning

/-- Square matrices satisfying the standard transpose definition of symmetry. -/
abbrev SymmetricMatrices (ι R : Type*) := { A : Matrix ι ι R // A.IsSymm }

/-- The independent coordinates of a symmetric matrix are unordered index pairs. -/
def symmetricMatrixEquivCoordinates (ι R : Type*) :
    SymmetricMatrices ι R ≃ (Sym2 ι → R) where
  toFun A := Sym2.lift ⟨A.val, fun i j => (A.property.apply i j).symm⟩
  invFun f := ⟨fun i j => f (Sym2.mk (i, j)),
    Matrix.IsSymm.ext (fun _ _ => congrArg f Sym2.eq_swap)⟩
  left_inv A := by
    apply Subtype.ext
    rfl
  right_inv f := by
    funext ij
    induction ij using Sym2.ind with
    | _ i j => rfl

/-- Upper-triangle coordinates, including the diagonal. -/
abbrev UpperTriangle (ι : Type*) [LE ι] := { ij : ι × ι // ij.1 ≤ ij.2 }

/-- Restricting to the upper triangle is an equivalence, with no field hypothesis. -/
def symmetricMatrixEquivUpperTriangle (ι R : Type*) [LinearOrder ι] :
    SymmetricMatrices ι R ≃ (UpperTriangle ι → R) :=
  (symmetricMatrixEquivCoordinates ι R).trans
    (Equiv.arrowCongr Sym2.sortEquiv (Equiv.refl R))

/-- The forward equivalence is exactly restriction to an upper-triangle entry. -/
@[simp] theorem symmetricMatrixEquivUpperTriangle_apply
    {ι R : Type*} [LinearOrder ι] (A : SymmetricMatrices ι R) (ij : UpperTriangle ι) :
    symmetricMatrixEquivUpperTriangle ι R A ij = A.val ij.val.1 ij.val.2 := rfl

noncomputable instance symmetricMatricesFintype
    (ι R : Type*) [Fintype ι] [Fintype R] : Fintype (SymmetricMatrices ι R) := by
  classical
  exact Fintype.ofEquiv (Sym2 ι → R) (symmetricMatrixEquivCoordinates ι R).symm

/-- The number of diagonal-inclusive upper-triangle coordinates. -/
theorem card_upperTriangle (n : ℕ) :
    Fintype.card (UpperTriangle (Fin n)) = n * (n + 1) / 2 := by
  calc
    _ = Fintype.card (Sym2 (Fin n)) := Fintype.card_congr Sym2.sortEquiv.symm
    _ = _ := by
      rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right]
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm (n + 1) n]

/-- Exact symmetric-matrix count for every finite entry type, including `n = 0`. -/
theorem card_symmetricMatrices (n : ℕ) (R : Type*) [Fintype R] :
    Fintype.card (SymmetricMatrices (Fin n) R) =
      Fintype.card R ^ (n * (n + 1) / 2) := by
  calc
    _ = Fintype.card (UpperTriangle (Fin n) → R) :=
      Fintype.card_congr (symmetricMatrixEquivUpperTriangle (Fin n) R)
    _ = _ := by
      rw [Fintype.card_fun, card_upperTriangle]

/-- The paper's `p^(n(n+1)/2)` count, for every positive modulus. -/
theorem card_symmetricMatrices_zmod (p n : ℕ) [NeZero p] :
    Fintype.card (SymmetricMatrices (Fin n) (ZMod p)) = p ^ (n * (n + 1) / 2) := by
  rw [card_symmetricMatrices, ZMod.card]

/-- Prime-field specialization. This includes `p = 2` without extra assumptions. -/
theorem card_symmetricMatrices_prime (p n : ℕ) [Fact p.Prime] :
    Fintype.card (SymmetricMatrices (Fin n) (ZMod p)) = p ^ (n * (n + 1) / 2) := by
  exact card_symmetricMatrices_zmod p n

#print axioms symmetricMatrixEquivUpperTriangle
#print axioms card_upperTriangle
#print axioms card_symmetricMatrices
#print axioms card_symmetricMatrices_zmod
#print axioms card_symmetricMatrices_prime

end StabilizerLearning
