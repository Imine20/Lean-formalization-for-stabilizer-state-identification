import ExactCriticalCurve.FiniteQuadratic.MetabolicCore
import Mathlib.LinearAlgebra.Quotient.Basic

noncomputable section
namespace ExactCriticalCurve.FiniteQuadratic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Descent is allowed exactly along a singular submodule in the polar radical. -/
def quotientValue (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U)
    (hRad : ∀ u ∈ U, ∀ v : V, Q.polarBilin u v = 0) : V ⧸ U → ZMod 2 :=
  Quotient.lift (fun x : V => Q x) (by
    intro x y hxy
    have hm : x - y ∈ U := U.quotientRel_def.mp hxy
    have he : x = (x - y) + y := by abel
    change Q x = Q y
    rw [he, quadratic_add, hU _ hm, hRad _ hm]
    simp)

@[simp] theorem quotientValue_mk (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U)
    (hRad : ∀ u ∈ U, ∀ v : V, Q.polarBilin u v = 0) (x : V) :
    quotientValue Q U hU hRad (Submodule.Quotient.mk x) = Q x := rfl

/-- The actual quadratic form on the quotient, constructed from representative invariance. -/
def quotientForm (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U)
    (hRad : ∀ u ∈ U, ∀ v : V, Q.polarBilin u v = 0) :
    QuadraticForm (ZMod 2) (V ⧸ U) :=
  QuadraticMap.ofPolar (quotientValue Q U hU hRad)
    (by
      intro a x
      induction x using Submodule.Quotient.induction_on with
      | H x => exact Q.map_smul a x)
    (by
      intro x x' y
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        induction x' using Submodule.Quotient.induction_on with
        | H x' =>
          induction y using Submodule.Quotient.induction_on with
          | H y => exact Q.polar_add_left x x' y)
    (by
      intro a x y
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        induction y using Submodule.Quotient.induction_on with
        | H y => exact Q.polar_smul_left a x y)

@[simp] theorem quotientForm_mk (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U)
    (hRad : ∀ u ∈ U, ∀ v : V, Q.polarBilin u v = 0) (x : V) :
    quotientForm Q U hU hRad (Submodule.Quotient.mk x) = Q x := rfl

@[simp] theorem quotientForm_polar_mk (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U)
    (hRad : ∀ u ∈ U, ∀ v : V, Q.polarBilin u v = 0) (x y : V) :
    (quotientForm Q U hU hRad).polarBilin
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Q.polarBilin x y := rfl

theorem quotientForm_nondegenerate (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U)
    (hRad : ∀ u ∈ U, ∀ v : V, Q.polarBilin u v = 0)
    (hRadical : ∀ x : V, (∀ y : V, Q.polarBilin x y = 0) → x ∈ U) :
    LinearMap.BilinForm.Nondegenerate (quotientForm Q U hU hRad).polarBilin := by
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    apply (Submodule.Quotient.eq U).mpr
    simpa using hRadical x (fun y => hx (Submodule.Quotient.mk y))

end ExactCriticalCurve.FiniteQuadratic
