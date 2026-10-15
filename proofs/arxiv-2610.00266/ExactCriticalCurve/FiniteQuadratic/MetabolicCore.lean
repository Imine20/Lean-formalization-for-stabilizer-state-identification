import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section

namespace ExactCriticalCurve.FiniteQuadratic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual quadratic form vanishes on every vector of the actual submodule. -/
def TotallySingular (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V) : Prop :=
  ∀ x ∈ U, Q x = 0

theorem TotallySingular.mono {Q : QuadraticForm (ZMod 2) V}
    {U W : Submodule (ZMod 2) V} (hW : TotallySingular Q W) (h : U ≤ W) :
    TotallySingular Q U := fun x hx => hW x (h hx)

/-- This uses the true polarization, never division by two. -/
theorem polar_isSymm (Q : QuadraticForm (ZMod 2) V) : LinearMap.BilinForm.IsSymm Q.polarBilin :=
  ⟨QuadraticMap.polar_comm Q⟩

theorem quadratic_add (Q : QuadraticForm (ZMod 2) V) (x y : V) :
    Q (x + y) = Q x + Q y + Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

theorem TotallySingular.le_orthogonal {Q : QuadraticForm (ZMod 2) V}
    {U : Submodule (ZMod 2) V} (hU : TotallySingular Q U) :
    U ≤ LinearMap.BilinForm.orthogonal Q.polarBilin U := by
  intro x hx y hy
  change Q.polarBilin y x = 0
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    hU _ (U.add_mem hy hx), hU _ hy, hU _ hx, sub_self]

theorem TotallySingular.sup_of_le_orthogonal {Q : QuadraticForm (ZMod 2) V}
    {U W : Submodule (ZMod 2) V} (hU : TotallySingular Q U)
    (hW : TotallySingular Q W) (hUW : U ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W) :
    TotallySingular Q (U ⊔ W) := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [quadratic_add, hU _ hu, hW _ hw]
  have hb : Q.polarBilin u w = 0 :=
    ((polar_isSymm Q).eq u w).trans (hUW hu w hw)
  simp [hb]

/-- Orthogonal complements turn actual sums into intersections. -/
theorem polar_orthogonal_sup (Q : QuadraticForm (ZMod 2) V)
    (U W : Submodule (ZMod 2) V) :
    LinearMap.BilinForm.orthogonal Q.polarBilin (U ⊔ W) =
      LinearMap.BilinForm.orthogonal Q.polarBilin U ⊓ LinearMap.BilinForm.orthogonal Q.polarBilin W := by
  ext x
  constructor
  · intro hx
    exact ⟨fun u hu => hx u ((show U ≤ U ⊔ W from le_sup_left) hu), fun w hw => hx w ((show W ≤ U ⊔ W from le_sup_right) hw)⟩
  · rintro ⟨hu, hw⟩ y hy
    obtain ⟨u, hum, w, hwm, rfl⟩ := Submodule.mem_sup.mp hy
    change Q.polarBilin (u + w) x = 0
    rw [map_add, LinearMap.add_apply, hu u hum, hw w hwm, zero_add]

section FiniteDimensional

variable [FiniteDimensional (ZMod 2) V]

theorem TotallySingular.finrank_le {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) {r : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * r)
    {U : Submodule (ZMod 2) V} (hU : TotallySingular Q U) :
    Module.finrank (ZMod 2) U ≤ r := by
  have hle := Submodule.finrank_mono hU.le_orthogonal
  have hd := LinearMap.BilinForm.finrank_orthogonal hQ (polar_isSymm Q).isRefl U
  rw [hV] at hd
  omega

/-- A half-dimensional totally singular space is its own polar orthogonal complement. -/
theorem orthogonal_eq_of_half_dim {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) {r : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * r)
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) :
    LinearMap.BilinForm.orthogonal Q.polarBilin L = L := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq hL.le_orthogonal
  rw [LinearMap.BilinForm.finrank_orthogonal hQ (polar_isSymm Q).isRefl, hV, hdL]
  omega

/-- The concrete maximal singular extension used in the metabolic quotient proof. -/
def metabolicExtension (Q : QuadraticForm (ZMod 2) V)
    (L U : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  (L ⊓ LinearMap.BilinForm.orthogonal Q.polarBilin U) ⊔ U

omit [FiniteDimensional (ZMod 2) V] in
theorem le_metabolicExtension (Q : QuadraticForm (ZMod 2) V)
    (L U : Submodule (ZMod 2) V) :
    U ≤ metabolicExtension Q L U := le_sup_right

omit [FiniteDimensional (ZMod 2) V] in
theorem metabolicExtension_le_orthogonal {Q : QuadraticForm (ZMod 2) V}
    (L : Submodule (ZMod 2) V) {U : Submodule (ZMod 2) V}
    (hU : TotallySingular Q U) :
    metabolicExtension Q L U ≤ LinearMap.BilinForm.orthogonal Q.polarBilin U :=
  sup_le inf_le_right hU.le_orthogonal

omit [FiniteDimensional (ZMod 2) V] in
theorem metabolicExtension_totallySingular {Q : QuadraticForm (ZMod 2) V}
    {L U : Submodule (ZMod 2) V}
    (hL : TotallySingular Q L) (hU : TotallySingular Q U) :
    TotallySingular Q (metabolicExtension Q L U) :=
  (hL.mono inf_le_left).sup_of_le_orthogonal hU inf_le_right

/-- Dimension of the concrete extension, derived from orthogonal and lattice dimensions. -/
theorem finrank_metabolicExtension {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) {r : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * r)
    {L U : Submodule (ZMod 2) V}
    (hL : TotallySingular Q L) (hdL : Module.finrank (ZMod 2) L = r)
    (hU : TotallySingular Q U) :
    Module.finrank (ZMod 2) (metabolicExtension Q L U) = r := by
  have horthL := orthogonal_eq_of_half_dim hQ hV hL hdL
  have horthU := LinearMap.BilinForm.orthogonal_orthogonal
    hQ (polar_isSymm Q).isRefl U
  have hdU := LinearMap.BilinForm.finrank_orthogonal
    hQ (polar_isSymm Q).isRefl U
  have hdSup := LinearMap.BilinForm.finrank_orthogonal
    hQ (polar_isSymm Q).isRefl (L ⊔ LinearMap.BilinForm.orthogonal Q.polarBilin U)
  rw [polar_orthogonal_sup, horthL, horthU] at hdSup
  have hbound := (L ⊔ LinearMap.BilinForm.orthogonal Q.polarBilin U).finrank_le
  have hdim₁ := Submodule.finrank_sup_add_finrank_inf_eq L (LinearMap.BilinForm.orthogonal Q.polarBilin U)
  have hdim₂ := Submodule.finrank_sup_add_finrank_inf_eq
    (L ⊓ LinearMap.BilinForm.orthogonal Q.polarBilin U) U
  have hinf : (L ⊓ LinearMap.BilinForm.orthogonal Q.polarBilin U) ⊓ U = L ⊓ U := by
    rw [inf_assoc, inf_eq_right.mpr hU.le_orthogonal]
  rw [hinf] at hdim₂
  dsimp only [metabolicExtension]
  have hboundU := U.finrank_le
  omega

/-- Order maximality is proved equivalent to half dimension; it is not a counting assumption. -/
theorem totallySingular_maximal_iff_finrank {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) {r : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * r)
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r)
    {U : Submodule (ZMod 2) V} (hU : TotallySingular Q U) :
    (∀ W : Submodule (ZMod 2) V, TotallySingular Q W → U ≤ W → W = U) ↔
      Module.finrank (ZMod 2) U = r := by
  constructor
  · intro hm
    have he := hm (metabolicExtension Q L U)
      (metabolicExtension_totallySingular hL hU) (le_metabolicExtension Q L U)
    rw [← he]
    exact finrank_metabolicExtension hQ hV hL hdL hU
  · intro hdU W hW hUW
    exact (Submodule.eq_of_le_of_finrank_le hUW
      (by simpa [hdU] using hW.finrank_le hQ hV)).symm

end FiniteDimensional
end ExactCriticalCurve.FiniteQuadratic
