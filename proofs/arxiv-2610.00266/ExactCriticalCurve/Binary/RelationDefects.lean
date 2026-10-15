import ExactCriticalCurve.Binary.RelationHalf
import Mathlib.LinearAlgebra.Prod

/-! # Actual defects and coordinate images of stochastic relations -/

noncomputable section
namespace ExactCriticalCurve.Binary
open StochasticCounting
variable {k : ℕ}

namespace StochasticLagrangian

/-- The vectors related to zero on the output side. -/
def leftDefect (T : StochasticLagrangian k) : Submodule (ZMod 2) (BinaryVector k) :=
  T.carrier.comap (LinearMap.inl (ZMod 2) (BinaryVector k) (BinaryVector k))

/-- The vectors related to zero on the input side. -/
def rightDefect (T : StochasticLagrangian k) : Submodule (ZMod 2) (BinaryVector k) :=
  T.carrier.comap (LinearMap.inr (ZMod 2) (BinaryVector k) (BinaryVector k))

@[simp] theorem mem_leftDefect (T : StochasticLagrangian k) (x : BinaryVector k) :
    x ∈ T.leftDefect ↔ (x, 0) ∈ T.carrier := Iff.rfl

@[simp] theorem mem_rightDefect (T : StochasticLagrangian k) (y : BinaryVector k) :
    y ∈ T.rightDefect ↔ (0, y) ∈ T.carrier := Iff.rfl

theorem leftDefect_isDefect (T : StochasticLagrangian k) : IsDefect T.leftDefect := by
  intro x hx
  simpa [relationQuadratic] using T.quadratic_zero (x, 0) hx

theorem rightDefect_isDefect (T : StochasticLagrangian k) : IsDefect T.rightDefect := by
  intro y hy
  have h := T.quadratic_zero (0, y) hy
  simpa [relationQuadratic] using h

/-- Maximal full quadratic isotropy implies equality with the binary orthogonal. -/
theorem orthogonal_eq (T : StochasticLagrangian k) :
    (relationBilinear k).orthogonal T.carrier = T.carrier := by
  have hle : T.carrier ≤ (relationBilinear k).orthogonal T.carrier :=
    fun _ hx _ hy => relationQuadratic_zero_pairwise T.quadratic_zero hy hx
  have hd := LinearMap.BilinForm.finrank_orthogonal
    (relationBilinear_nondegenerate k) (relationBilinear_isSymm k).isRefl T.carrier
  have hv : Module.finrank (ZMod 2) (RelationSpace k) = 2 * k := by
    simp [RelationSpace, BinaryVector, Module.finrank_prod, two_mul]
  rw [hv, T.finrank_eq] at hd
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hd, T.finrank_eq]; omega)).symm

theorem orthogonal_leftImage (T : StochasticLagrangian k) :
    orthogonal (T.carrier.map (LinearMap.fst (ZMod 2) (BinaryVector k) (BinaryVector k))) =
      T.leftDefect := by
  ext z
  constructor
  · intro hz
    apply T.orthogonal_eq ▸ show (z, 0) ∈ (relationBilinear k).orthogonal T.carrier from ?_
    intro p hp
    have he := hz p.1 ⟨p, hp, rfl⟩
    change binaryDot p.1 z = 0 at he
    change relationBilinear k p (z, 0) = 0
    simpa [relationBilinear_apply, binaryDot] using he
  · intro hz x hx
    obtain ⟨p, hp, rfl⟩ := hx
    have he := relationQuadratic_zero_pairwise T.quadratic_zero hp hz
    simpa [relationBilinear_apply, binaryDot] using he

theorem orthogonal_rightImage (T : StochasticLagrangian k) :
    orthogonal (T.carrier.map (LinearMap.snd (ZMod 2) (BinaryVector k) (BinaryVector k))) =
      T.rightDefect := by
  ext z
  constructor
  · intro hz
    apply T.orthogonal_eq ▸ show (0, z) ∈ (relationBilinear k).orthogonal T.carrier from ?_
    intro p hp
    have he := hz p.2 ⟨p, hp, rfl⟩
    change binaryDot p.2 z = 0 at he
    change relationBilinear k p (0, z) = 0
    simpa [relationBilinear_apply, binaryDot] using he
  · intro hz x hx
    obtain ⟨p, hp, rfl⟩ := hx
    have he := relationQuadratic_zero_pairwise T.quadratic_zero hp hz
    simpa [relationBilinear_apply, binaryDot] using he

/-- The output coordinate image is the full orthogonal complement of the left defect. -/
theorem leftImage_eq (T : StochasticLagrangian k) :
    T.carrier.map (LinearMap.fst (ZMod 2) (BinaryVector k) (BinaryVector k)) =
      orthogonal T.leftDefect := by
  rw [← T.orthogonal_leftImage]
  exact (LinearMap.BilinForm.orthogonal_orthogonal
    (binaryDotForm_nondegenerate k) (binaryDotForm_isRefl k) _).symm

/-- The input coordinate image is the full orthogonal complement of the right defect. -/
theorem rightImage_eq (T : StochasticLagrangian k) :
    T.carrier.map (LinearMap.snd (ZMod 2) (BinaryVector k) (BinaryVector k)) =
      orthogonal T.rightDefect := by
  rw [← T.orthogonal_rightImage]
  exact (LinearMap.BilinForm.orthogonal_orthogonal
    (binaryDotForm_nondegenerate k) (binaryDotForm_isRefl k) _).symm

theorem left_mem_orthogonal (T : StochasticLagrangian k)
    {p : BinaryVector k × BinaryVector k} (hp : p ∈ T.carrier) :
    p.1 ∈ orthogonal T.leftDefect := by
  rw [← T.leftImage_eq]
  exact ⟨p, hp, rfl⟩

theorem right_mem_orthogonal (T : StochasticLagrangian k)
    {p : BinaryVector k × BinaryVector k} (hp : p ∈ T.carrier) :
    p.2 ∈ orthogonal T.rightDefect := by
  rw [← T.rightImage_eq]
  exact ⟨p, hp, rfl⟩

theorem left_mem_iff_right_mem (T : StochasticLagrangian k)
    {p : BinaryVector k × BinaryVector k} (hp : p ∈ T.carrier) :
    p.1 ∈ T.leftDefect ↔ p.2 ∈ T.rightDefect := by
  constructor
  · intro h
    have hh := T.carrier.sub_mem hp h
    cases p
    simpa using hh
  · intro h
    have hh := T.carrier.sub_mem hp h
    cases p
    simpa using hh

/-- Both actual defects lie in the same Wu branch. -/
theorem allOnes_mem_left_iff_right (T : StochasticLagrangian k) :
    allOnes k ∈ T.leftDefect ↔ allOnes k ∈ T.rightDefect :=
  T.left_mem_iff_right_mem T.allOnes_mem

end StochasticLagrangian
end ExactCriticalCurve.Binary
