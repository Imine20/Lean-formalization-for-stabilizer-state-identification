import ExactCriticalCurve.Quantum.CSSAffineOverlap
import ExactCriticalCurve.Quantum.DefectProjectionProduct

/-! # Pairing kernels forced by actual nonzero CSS overlap

The overlap support criterion forces both induced pairings to be nondegenerate
modulo the actual common defect. No ordinary or positive-dimension assumption is used.
-/
noncomputable section
namespace ExactCriticalCurve.Binary
variable {k : ℕ}

/-- A span containment forces the corresponding pairing kernel into the defect. -/
theorem cssPairingKernel_le
    (A B : Submodule (ZMod 2) (BinaryVector k))
    (h : orthogonal A ≤ A ⊔ orthogonal B) :
    orthogonal A ⊓ B ≤ A := by
  have hdd (L : Submodule (ZMod 2) (BinaryVector k)) :
      orthogonal (orthogonal L) = L :=
    LinearMap.BilinForm.orthogonal_orthogonal
      (binaryDotForm_nondegenerate k) (binaryDotForm_isRefl k) L
  have hr : orthogonal (A ⊔ orthogonal B) ≤ orthogonal (orthogonal A) :=
    LinearMap.BilinForm.orthogonal_le h
  intro x hx
  have hxBB : x ∈ orthogonal (orthogonal B) := by
    rw [hdd B]
    exact hx.2
  have hxAB : x ∈ orthogonal (A ⊔ orthogonal B) :=
    (mem_orthogonal_sup_iff A (orthogonal B) x).mpr ⟨hx.1, hxBB⟩
  have hxA := hr hxAB
  simpa only [hdd A] using hxA

/-- The actual overlap condition supplies both orthogonal span inclusions. -/
theorem cssOverlap_orthogonal_le
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : StochasticIsometryGroup k)
    (h : ∀ x ∈ orthogonal N, g.val x - x ∈ N ⊔ stochasticSubspace g N) :
    orthogonal N ≤ N ⊔ orthogonal (stochasticSubspace g N) ∧
      orthogonal (stochasticSubspace g N) ≤ stochasticSubspace g N ⊔ orthogonal N := by
  let M := stochasticSubspace g N
  have hM : IsDefect M := stochasticSubspace_isDefect g hN
  constructor
  · intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h x hx)
    have hgx : g.val x ∈ orthogonal M := by
      rw [stochasticSubspace_orthogonal]
      exact ⟨x, hx, rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨-a, N.neg_mem ha, g.val x - b,
      (orthogonal M).sub_mem hgx (hM.le_orthogonal hb), ?_⟩
    calc
      -a + (g.val x - b) = g.val x - (a + b) := by abel
      _ = x := by rw [hab]; abel
  · intro x hx
    rw [stochasticSubspace_orthogonal] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h y hy)
    apply Submodule.mem_sup.mpr
    refine ⟨b, hb, y + a, (orthogonal N).add_mem hy (hN.le_orthogonal ha), ?_⟩
    calc
      b + (y + a) = (a + b) + y := by abel
      _ = g.val y := by rw [hab]; abel

/-- Both pairing kernels are exactly the common defect, derived from overlap. -/
theorem cssOverlap_pairingKernels
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : StochasticIsometryGroup k)
    (h : ∀ x ∈ orthogonal N, g.val x - x ∈ N ⊔ stochasticSubspace g N) :
    N ⊓ orthogonal (stochasticSubspace g N) = N ⊓ stochasticSubspace g N ∧
      stochasticSubspace g N ⊓ orthogonal N = N ⊓ stochasticSubspace g N := by
  let M := stochasticSubspace g N
  have hM : IsDefect M := stochasticSubspace_isDefect g hN
  obtain ⟨hNM, hMN⟩ := cssOverlap_orthogonal_le N hN g h
  have hNK := cssPairingKernel_le M N hMN
  have hMK := cssPairingKernel_le N M hNM
  constructor
  · apply le_antisymm
    · intro x hx
      exact ⟨hx.1, hNK ⟨hx.2, hx.1⟩⟩
    · intro x hx
      exact ⟨hx.1, hM.le_orthogonal hx.2⟩
  · apply le_antisymm
    · intro x hx
      exact ⟨hMK ⟨hx.2, hx.1⟩, hx.1⟩
    · intro x hx
      exact ⟨hx.2, hN.le_orthogonal hx.1⟩

end ExactCriticalCurve.Binary
