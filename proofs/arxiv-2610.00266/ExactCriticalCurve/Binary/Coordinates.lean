import ExactCriticalCurve.Binary.Quadratic
import Mathlib.LinearAlgebra.StdBasis

/-!
# Copy coordinates, physical-qubit columns, and linear maps

The paper labels a CSS coset by a linear map from the binary n-space.
The tensor relation operator instead uses n columns, each a k-bit vector.
These are explicit linear equivalences, including zero-dimensional cases.
-/

noncomputable section
namespace ExactCriticalCurve.Binary

open scoped BigOperators

abbrev ColumnConfig (n k : ℕ) := Fin n → BinaryVector k
abbrev CopyConfig (n k : ℕ) := Fin k → BinaryVector n

/-- Reindex the physical tensor basis from copies to qubit columns. -/
def copyColumnsEquiv (n k : ℕ) :
    CopyConfig n k ≃ₗ[ZMod 2] ColumnConfig n k where
  toFun F a i := F i a
  invFun X i a := X a i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem copyColumnsEquiv_apply (n k : ℕ) (F : CopyConfig n k)
    (a : Fin n) (i : Fin k) :
    copyColumnsEquiv n k F a i = F i a := rfl

@[simp] theorem copyColumnsEquiv_symm_apply (n k : ℕ) (X : ColumnConfig n k)
    (i : Fin k) (a : Fin n) :
    (copyColumnsEquiv n k).symm X i a = X a i := rfl

variable (n : ℕ) (Q : Type*) [AddCommMonoid Q] [Module (ZMod 2) Q]

/-- Standard-basis evaluation identifies an actual linear map with its columns. -/
def homColumnsEquiv :
    (BinaryVector n →ₗ[ZMod 2] Q) ≃ₗ[ZMod 2] (Fin n → Q) :=
  (Module.piEquiv (Fin n) (ZMod 2) Q).symm

@[simp] theorem homColumnsEquiv_apply
    (f : BinaryVector n →ₗ[ZMod 2] Q) (a : Fin n) :
    homColumnsEquiv n Q f a = f (Pi.single a 1) := by
  change f (Pi.basisFun (ZMod 2) (Fin n) a) = _
  rw [Pi.basisFun_apply]

@[simp] theorem homColumnsEquiv_symm_apply
    (X : Fin n → Q) (v : BinaryVector n) :
    (homColumnsEquiv n Q).symm X v = ∑ a, v a • X a :=
  Module.piEquiv_apply_apply (Fin n) (ZMod 2) Q X v

/-- Subspace-valued maps correspond to columns in that same subspace. -/
theorem homColumnsEquiv_range_le_iff
    (f : BinaryVector n →ₗ[ZMod 2] Q) (N : Submodule (ZMod 2) Q) :
    LinearMap.range f ≤ N ↔ ∀ a, homColumnsEquiv n Q f a ∈ N := by
  have hr : LinearMap.range f =
      Submodule.span (ZMod 2) (Set.range (homColumnsEquiv n Q f)) := by
    simpa only [homColumnsEquiv, LinearEquiv.apply_symm_apply] using
      (Module.range_piEquiv (Fin n) (ZMod 2) Q (homColumnsEquiv n Q f))
  rw [hr, Submodule.span_le]
  exact ⟨fun h a => h ⟨a, rfl⟩, fun h _ ⟨a, ha⟩ => ha ▸ h a⟩

/-- Quotient maps and other linear postcompositions act on the actual columns. -/
theorem homColumnsEquiv_comp {Q' : Type*} [AddCommMonoid Q']
    [Module (ZMod 2) Q'] (A : Q →ₗ[ZMod 2] Q')
    (f : BinaryVector n →ₗ[ZMod 2] Q) :
    homColumnsEquiv n Q' (A.comp f) = fun a => A (homColumnsEquiv n Q f a) := by
  ext a
  simp

end ExactCriticalCurve.Binary
