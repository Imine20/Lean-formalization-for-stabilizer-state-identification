import ExactCriticalCurve.Quantum.AffineStabilizer
import ExactCriticalCurve.Counting.BinaryQBinomial

/-! Actual nonempty affine supports are counted by their directions and quotient cosets. -/
noncomputable section
open scoped BigOperators
open ExactCriticalCurve.Binary ExactCriticalCurve.Counting Classical
namespace ExactCriticalCurve.Quantum

instance fintypeNonemptyAffineSupport (n : ℕ) : Fintype (NonemptyAffineSupport n) :=
  Fintype.ofFinite _

abbrev AffineDirectionFiber {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n)) :=
  {A : NonemptyAffineSupport n // A.val.direction = L}

def affineDirectionCoset {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n))
    (A : AffineDirectionFiber L) : BinaryVector n ⧸ L :=
  L.mkQ (affineSupportAnchor A.val)

/-- Supports of a fixed direction are exactly the actual quotient cosets. -/
def affineDirectionCosetEquiv {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n)) :
    AffineDirectionFiber L ≃ (BinaryVector n ⧸ L) :=
  Equiv.ofBijective (affineDirectionCoset L) (by
    constructor
    · intro A B h
      have hm : affineSupportAnchor A.val - affineSupportAnchor B.val ∈ L :=
        (Submodule.Quotient.eq L).mp h
      apply Subtype.ext
      apply Subtype.ext
      apply AffineSubspace.ext_of_direction_eq (A.property.trans B.property.symm)
      refine ⟨affineSupportAnchor A.val, affineSupportAnchor_mem A.val, ?_⟩
      rw [← affineSupport_mk_anchor B.val]
      change affineSupportAnchor A.val - affineSupportAnchor B.val ∈ B.val.val.direction
      rwa [B.property]
    · intro y
      obtain ⟨a, rfl⟩ := L.mkQ_surjective y
      let A : NonemptyAffineSupport n :=
        ⟨AffineSubspace.mk' a L, ⟨⟨a, AffineSubspace.self_mem_mk' a L⟩⟩⟩
      refine ⟨⟨A, AffineSubspace.direction_mk' a L⟩, ?_⟩
      apply (Submodule.Quotient.eq L).mpr
      exact affineSupportAnchor_mem A)

/-- No anchor multiplicity remains: each affine support is counted once. -/
theorem affineDirectionFiber_card {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n)) :
    Nat.card (AffineDirectionFiber L) = 2 ^ (n - Module.finrank (ZMod 2) L) := by
  rw [Nat.card_congr (affineDirectionCosetEquiv L)]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Submodule.finrank_quotient]
  simp [BinaryVector]

abbrev AffineSupportsOfDimension (n m : ℕ) :=
  {A : NonemptyAffineSupport n // Module.finrank (ZMod 2) A.val.direction = m}

def affineDimensionEquivDirections (n m : ℕ) :
    AffineSupportsOfDimension n m ≃
      Σ L : BinarySubspaces (BinaryVector n) m, AffineDirectionFiber L.val where
  toFun A := ⟨⟨A.val.val.direction, A.property⟩, ⟨A.val, rfl⟩⟩
  invFun p := ⟨p.2.val, by rw [p.2.property]; exact p.1.property⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨L, hL⟩, ⟨A, hA⟩⟩
    cases hA
    rfl

theorem affineSupportsOfDimension_card (n m : ℕ) :
    Nat.card (AffineSupportsOfDimension n m) = 2 ^ (n - m) * binaryGaussian n m := by
  letI : Fintype (BinarySubspaces (BinaryVector n) m) := Fintype.ofFinite _
  letI (L : BinarySubspaces (BinaryVector n) m) :
      Fintype (AffineDirectionFiber L.val) := Fintype.ofFinite _
  rw [Nat.card_congr (affineDimensionEquivDirections n m), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  simp_rw [← Nat.card_eq_fintype_card, affineDirectionFiber_card]
  have he (L : BinarySubspaces (BinaryVector n) m) :
      Module.finrank (ZMod 2) L.val = m := L.property
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  exact Nat.mul_comm _ _

def affineSupportDimension {n : ℕ} (A : NonemptyAffineSupport n) : Fin (n + 1) :=
  ⟨Module.finrank (ZMod 2) A.val.direction, by
    have h := A.val.direction.finrank_le
    have hn : Module.finrank (ZMod 2) (BinaryVector n) = n := by simp [BinaryVector]
    rw [hn] at h
    omega⟩

def affineDimensionFiberEquiv {n : ℕ} (m : Fin (n + 1)) :
    {A : NonemptyAffineSupport n // affineSupportDimension A = m} ≃
      AffineSupportsOfDimension n m :=
  Equiv.subtypeEquivRight (fun A => by
    change ((⟨_, _⟩ : Fin (n + 1)) = m) ↔ _
    exact Fin.ext_iff)

/-- Weighted enumeration of every actual nonempty affine support. -/
theorem sum_affineSupport_dimension (n : ℕ) (f : ℕ → ℕ) :
    (∑ A : NonemptyAffineSupport n, f (Module.finrank (ZMod 2) A.val.direction)) =
      ∑ m ∈ Finset.range (n + 1), (2 ^ (n - m) * binaryGaussian n m) * f m := by
  change (∑ A : NonemptyAffineSupport n, f (affineSupportDimension A).val) = _
  rw [← Fintype.sum_fiberwise' (@affineSupportDimension n)
    (fun m : Fin (n + 1) => f m.val)]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hc (m : Fin (n + 1)) :
      Fintype.card {A : NonemptyAffineSupport n // affineSupportDimension A = m} =
        2 ^ (n - m.val) * binaryGaussian n m.val := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (affineDimensionFiberEquiv m)]
    exact affineSupportsOfDimension_card _ _
  simp_rw [hc]
  simpa using (Fin.sum_univ_eq_sum_range (fun m : ℕ => (2 ^ (n - m) * binaryGaussian n m) * f m) (n + 1))

/-- Exact count of the physical signed stabilizer ensemble, derived through the full
normal-form bijection rather than included as a structural field. -/
theorem stabilizerGroup_card (n : ℕ) :
    Nat.card (StabilizerGroup n) =
      2 ^ n * ∏ j ∈ Finset.range n, (1 + 2 ^ (j + 1)) := by
  rw [Nat.card_congr (stabilizerAffineNormalForm n), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  simp_rw [← Nat.card_eq_fintype_card, quadraticPhaseData_card]
  rw [sum_affineSupport_dimension n (fun m => 4 ^ m * 2 ^ (m.choose 2))]
  exact binaryGaussian_affine_phase_sum n

end ExactCriticalCurve.Quantum
