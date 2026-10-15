import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! # Rank of an actual pulled-back bilinear pairing -/

noncomputable section
namespace ExactCriticalCurve

variable {K V Q : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- Rank means the dimension of the actual linear-map range of the pairing. -/
def bilinearRank (B : LinearMap.BilinForm K V) : ℕ :=
  Module.finrank K (LinearMap.range B)

/-- A pullback pairing cannot have rank larger than its actual intermediate space. -/
theorem bilinearRank_pullback_le (B : LinearMap.BilinForm K Q) (f : V →ₗ[K] Q) :
    bilinearRank (B.compl₁₂ f f) ≤ Module.finrank K Q := by
  have hk : LinearMap.ker f ≤ LinearMap.ker (B.compl₁₂ f f) := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    ext y
    change B (f x) (f y) = 0
    rw [LinearMap.mem_ker.mp hx, map_zero, LinearMap.zero_apply]
  have hmono := Submodule.finrank_mono hk
  have hp := LinearMap.finrank_range_add_finrank_ker (B.compl₁₂ f f)
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hq := Submodule.finrank_le (LinearMap.range f)
  unfold bilinearRank
  omega

omit [FiniteDimensional K V] [FiniteDimensional K Q] in
/-- Surjectivity and nondegeneracy identify the pullback radical exactly. -/
theorem ker_pullback_eq (B : LinearMap.BilinForm K Q) (hB : B.Nondegenerate)
    (f : V →ₗ[K] Q) (hf : Function.Surjective f) :
    LinearMap.ker (B.compl₁₂ f f) = LinearMap.ker f := by
  ext x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply hB
    intro y
    obtain ⟨z, rfl⟩ := hf y
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hx) z
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext y
    change B (f x) (f y) = 0
    rw [LinearMap.mem_ker.mp hx, map_zero, LinearMap.zero_apply]

omit [FiniteDimensional K Q] in
/-- An onto pullback of a nondegenerate pairing retains its entire rank. -/
theorem bilinearRank_pullback_eq (B : LinearMap.BilinForm K Q) (hB : B.Nondegenerate)
    (f : V →ₗ[K] Q) (hf : Function.Surjective f) :
    bilinearRank (B.compl₁₂ f f) = Module.finrank K Q := by
  have hp := LinearMap.finrank_range_add_finrank_ker (B.compl₁₂ f f)
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  rw [ker_pullback_eq B hB f hf] at hp
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hdim
  unfold bilinearRank
  omega

end ExactCriticalCurve
