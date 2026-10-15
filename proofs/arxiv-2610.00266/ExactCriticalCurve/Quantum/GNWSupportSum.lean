import ExactCriticalCurve.Binary.ConfigurationRelations
import ExactCriticalCurve.Quantum.PhaseStabilizerProjector
import ExactCriticalCurve.Quantum.AffineCounting
import ExactCriticalCurve.Counting.GNWCoefficients

/-! Enumeration of actual stabilizer tensor entries by their unique affine supports. -/
noncomputable section
open scoped BigOperators
open Classical Module ExactCriticalCurve.Binary ExactCriticalCurve.Counting
open ExactCriticalCurve.Binary.ConfigurationRelations
namespace ExactCriticalCurve.Quantum

theorem configurationSupport_le_iff {n k : ℕ} (X Y : CopyConfig n k)
    (A : AffineSubspace (ZMod 2) (BinaryVector n)) :
    configurationSupport X Y ≤ A ↔ (∀ i, X i ∈ A) ∧ ∀ i, Y i ∈ A := by
  rw [configurationSupport, affineSpan_le]
  constructor
  · intro h
    exact ⟨fun i => h (Or.inl ⟨i,rfl⟩), fun i => h (Or.inr ⟨i,rfl⟩)⟩
  · rintro ⟨hx,hy⟩ _ (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · exact hx i
    · exact hy i

theorem mem_affineSupport_iff_sub {n : ℕ} (A : NonemptyAffineSupport n)
    (x : BinaryVector n) :
    x ∈ A.val ↔ x - affineSupportAnchor A ∈ A.val.direction := by
  rw [← affineSupport_mk_anchor A, AffineSubspace.direction_mk']
  rfl

/-- Sum over all phase coefficients on one actual affine support. -/
theorem affineSupport_tensor_sum {n k : ℕ} (A : NonemptyAffineSupport n)
    (X Y : CopyConfig n k) :
    (∑ c : QuadraticPhaseData (Module.finrank (ZMod 2) A.val.direction),
      matrixTensorPower k (stabilizerProjection (phaseStabilizer (affineSupportAnchor A)
        (phaseDataOfCoefficients (Module.finBasis (ZMod 2) A.val.direction) c))) X Y) =
    if configurationSupport X Y ≤ A.val ∧ phaseStatisticsVanish X Y then
      stabilizerPhaseWeight (K := ℂ) (Module.finrank (ZMod 2) A.val.direction) k
    else 0 := by
  let b := Module.finBasis (ZMod 2) A.val.direction
  let a := affineSupportAnchor A
  by_cases hc : configurationSupport X Y ≤ A.val
  · obtain ⟨hx,hy⟩ := (configurationSupport_le_iff X Y A.val).mp hc
    let T : Fin k → A.val.direction :=
      fun i => ⟨X i - a, (mem_affineSupport_iff_sub A _).mp (hx i)⟩
    let U : Fin k → A.val.direction :=
      fun i => ⟨Y i - a, (mem_affineSupport_iff_sub A _).mp (hy i)⟩
    let Z := fun i => b.equivFun (T i)
    let V := fun i => b.equivFun (U i)
    have hX : (fun i => a + (b.equivFun.symm (Z i)).val) = X := by
      funext i
      simp [Z, T]
    have hY : (fun i => a + (b.equivFun.symm (V i)).val) = Y := by
      funext i
      simp [V, U]
    have hp : phaseStatisticsVanish Z V ↔ phaseStatisticsVanish X Y := by
      simpa only [hX,hY] using
        (phaseStatisticsVanish_basis_chart A.val.direction b a Z V).symm
    have hs := phaseDataCoefficients_tensor_sum_card a b Z V
    rw [hX,hY] at hs
    rw [hs, hp]
    simp only [hc, true_and]
    split_ifs
    · rw [stabilizerPhaseWeight_coefficients]
      push_cast
      rw [pow_mul, div_eq_mul_inv]
    · rfl
  · have hxy : (∃ i, X i - a ∉ A.val.direction) ∨
        (∃ i, Y i - a ∉ A.val.direction) := by
      have hnot : ¬ ((∀ i, X i - a ∈ A.val.direction) ∧
          ∀ i, Y i - a ∈ A.val.direction) := by
        intro h
        apply hc
        exact (configurationSupport_le_iff X Y A.val).mpr
          ⟨fun i => (mem_affineSupport_iff_sub A _).mpr (h.1 i),
            fun i => (mem_affineSupport_iff_sub A _).mpr (h.2 i)⟩
      by_cases hxall : ∀ i, X i - a ∈ A.val.direction
      · right
        push_neg at hnot
        exact hnot hxall
      · left
        push_neg at hxall
        exact hxall
    rw [phaseDataCoefficients_tensor_sum_zero a b X Y hxy]
    simp [hc]

abbrev ContainingAffineSupports {n : ℕ} (A₀ : NonemptyAffineSupport n) :=
  {A : NonemptyAffineSupport n // A₀.val ≤ A.val}

def containingAffineDimension {n : ℕ} (A₀ : NonemptyAffineSupport n)
    (A : ContainingAffineSupports A₀) :
    Fin (n - Module.finrank (ZMod 2) A₀.val.direction + 1) :=
  ⟨Module.finrank (ZMod 2) A.val.val.direction -
      Module.finrank (ZMod 2) A₀.val.direction, by
    have hlow := Submodule.finrank_mono (AffineSubspace.direction_le A.property)
    have hu := A.val.val.direction.finrank_le
    have hu₀ := A₀.val.direction.finrank_le
    have hn : Module.finrank (ZMod 2) (BinaryVector n) = n := by simp [BinaryVector]
    rw [hn] at hu hu₀
    omega⟩

theorem containingAffineDimension_add {n : ℕ} (A₀ : NonemptyAffineSupport n)
    (A : ContainingAffineSupports A₀) :
    Module.finrank (ZMod 2) A₀.val.direction + (containingAffineDimension A₀ A).val =
      Module.finrank (ZMod 2) A.val.val.direction := by
  have hlow := Submodule.finrank_mono (AffineSubspace.direction_le A.property)
  dsimp [containingAffineDimension]
  omega

def containingAffineDimensionFiberEquiv {n : ℕ} (A₀ : NonemptyAffineSupport n)
    (r : Fin (n - Module.finrank (ZMod 2) A₀.val.direction + 1)) :
    {A : ContainingAffineSupports A₀ // containingAffineDimension A₀ A = r} ≃
      AffineSupportsContaining A₀.val
        (Module.finrank (ZMod 2) A₀.val.direction + r.val) where
  toFun A := ⟨A.val.val.val, A.val.property, by
    have h := containingAffineDimension_add A₀ A.val
    rw [A.property] at h
    exact h.symm⟩
  invFun A := ⟨⟨⟨A.val, ⟨⟨affineSupportAnchor A₀,
      A.property.1 (affineSupportAnchor_mem A₀)⟩⟩⟩, A.property.1⟩, by
    apply Fin.ext
    change Module.finrank (ZMod 2) A.val.direction -
      Module.finrank (ZMod 2) A₀.val.direction = r.val
    rw [A.property.2]
    omega⟩
  left_inv A := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl

/-- Each containing affine support contributes exactly once, with its true dimension. -/
theorem sum_containingAffineSupports_dimension {n : ℕ} (A₀ : NonemptyAffineSupport n)
    (f : ℕ → ℂ) :
    (∑ A : ContainingAffineSupports A₀, f (Module.finrank (ZMod 2) A.val.val.direction)) =
      ∑ r ∈ Finset.range (n - Module.finrank (ZMod 2) A₀.val.direction + 1),
        (binaryGaussian (n - Module.finrank (ZMod 2) A₀.val.direction) r : ℂ) *
          f (Module.finrank (ZMod 2) A₀.val.direction + r) := by
  simp_rw [← containingAffineDimension_add A₀]
  rw [← Fintype.sum_fiberwise' (containingAffineDimension A₀)
    (fun r => f (Module.finrank (ZMod 2) A₀.val.direction + r.val))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc (r : Fin (n - Module.finrank (ZMod 2) A₀.val.direction + 1)) :
      Fintype.card {A : ContainingAffineSupports A₀ // containingAffineDimension A₀ A = r} =
        binaryGaussian (n - Module.finrank (ZMod 2) A₀.val.direction) r.val := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr (containingAffineDimensionFiberEquiv A₀ r),
      card_affineSupportsContaining_binary n A₀.val A₀.property _ (by omega)]
    congr 1
    omega
  simp_rw [hc]
  simpa using (Fin.sum_univ_eq_sum_range
    (fun r : ℕ => (binaryGaussian (n - Module.finrank (ZMod 2) A₀.val.direction) r : ℂ) *
      f (Module.finrank (ZMod 2) A₀.val.direction + r))
    (n - Module.finrank (ZMod 2) A₀.val.direction + 1))

/-- The indicator sum over every support equals the actual Gaussian extension sum. -/
theorem sum_affineSupport_containment {n : ℕ} (A₀ : NonemptyAffineSupport n)
    (f : ℕ → ℂ) :
    (∑ A : NonemptyAffineSupport n,
      if A₀.val ≤ A.val then f (Module.finrank (ZMod 2) A.val.direction) else 0) =
      ∑ r ∈ Finset.range (n - Module.finrank (ZMod 2) A₀.val.direction + 1),
        (binaryGaussian (n - Module.finrank (ZMod 2) A₀.val.direction) r : ℂ) *
          f (Module.finrank (ZMod 2) A₀.val.direction + r) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun A : NonemptyAffineSupport n => A₀.val ≤ A.val)
    _ (by simp) (fun A => f (Module.finrank (ZMod 2) A.val.direction))]
  exact sum_containingAffineSupports_dimension A₀ f

/-- The full physical ensemble is reindexed through its proved unique affine normal form. -/
theorem stabilizer_tensor_sum_affine {n k : ℕ} (X Y : CopyConfig n k) :
    (∑ S : StabilizerGroup n, matrixTensorPower k (stabilizerProjection S) X Y) =
      ∑ A : NonemptyAffineSupport n,
        if configurationSupport X Y ≤ A.val ∧ phaseStatisticsVanish X Y then
          stabilizerPhaseWeight (K := ℂ) (Module.finrank (ZMod 2) A.val.direction) k
        else 0 := by
  rw [← (stabilizerAffineNormalForm n).symm.sum_comp
    (fun S => matrixTensorPower k (stabilizerProjection S) X Y)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro A _
  change (∑ c : QuadraticPhaseData (Module.finrank (ZMod 2) A.val.direction),
      matrixTensorPower k (stabilizerProjection (phaseStabilizer (affineSupportAnchor A)
        (phaseDataOfCoefficients (Module.finBasis (ZMod 2) A.val.direction) c))) X Y) = _
  exact affineSupport_tensor_sum A X Y

/-- Entrywise ensemble sum with the ambient phase condition and no stable-range assumption. -/
theorem stabilizer_tensor_sum_gaussian {n k : ℕ} (hk : 1 ≤ k) (X Y : CopyConfig n k) :
    (∑ S : StabilizerGroup n, matrixTensorPower k (stabilizerProjection S) X Y) =
      if phaseStatisticsVanish X Y then
        ∑ r ∈ Finset.range (n - Module.finrank (ZMod 2)
          (configurationSupport X Y).direction + 1),
          (binaryGaussian (n - Module.finrank (ZMod 2)
            (configurationSupport X Y).direction) r : ℂ) *
          stabilizerPhaseWeight (K := ℂ)
            (Module.finrank (ZMod 2) (configurationSupport X Y).direction + r) k
      else 0 := by
  rw [stabilizer_tensor_sum_affine]
  by_cases hp : phaseStatisticsVanish X Y
  · simp only [hp, and_true, if_true]
    exact sum_affineSupport_containment
      ⟨configurationSupport X Y, configurationSupport_nonempty hk X Y⟩
      (fun m => stabilizerPhaseWeight (K := ℂ) m k)
  · simp [hp]

end ExactCriticalCurve.Quantum
