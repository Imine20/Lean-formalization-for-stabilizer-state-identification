import StabilizerLearning.OddPrime.MomentCompletion
import StabilizerLearning.Binary.BinaryMomentCompletion

noncomputable section
namespace StabilizerLearning
attribute [local instance] Classical.propDecidable
open scoped BigOperators

/-- Actual multiplicity of a value under a finite map. -/
def tupleMultiplicity {Ω Z : Type*} (f : Ω → Z) (z : Z) : ℕ :=
  Nat.card {x : Ω // f x = z}

/-- The complete coordinate fibre, including values with zero multiplicity. -/
abbrev MomentCoset {Z L : Type*} (g : Z → L) (ζ : L) := {z : Z // g z = ζ}

/-- Full tuple mass in one lower-coordinate fibre. -/
def momentCosetMass {Ω Z L : Type*} [Fintype Z] (f : Ω → Z) (g : Z → L) (ζ : L) : ℕ := by
  classical
  exact ∑ z : MomentCoset g ζ, tupleMultiplicity f z.val

/-- Partition the actual tuple fibre by its actual full moment. -/
def tupleCosetPartitionEquiv {Ω Z L : Type*} (f : Ω → Z) (g : Z → L) (ζ : L) :
    ((z : MomentCoset g ζ) × {x : Ω // f x = z.val}) ≃ {x : Ω // g (f x) = ζ} where
  toFun z := ⟨z.2.val, (congrArg g z.2.property).trans z.1.property⟩
  invFun x := ⟨⟨f x.val, x.property⟩, ⟨x.val, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨⟨z, hz⟩, ⟨x, hx⟩⟩
    cases hx
    rfl
  right_inv x := rfl

theorem momentCosetMass_eq_card {Ω Z L : Type*} [Fintype Ω] [Fintype Z]
    (f : Ω → Z) (g : Z → L) (ζ : L) :
    momentCosetMass f g ζ = Nat.card {x : Ω // g (f x) = ζ} := by
  classical
  rw [← Nat.card_congr (tupleCosetPartitionEquiv f g ζ), Nat.card_sigma]
  rfl

/-- The full tuple fibre splits into unrestricted upper rows and actual lower
tuple realizations of ζ. No lower witness is selected. -/
def lowerTupleFiberEquiv {F L : Type*} (m n k : ℕ)
    (φ : Matrix (Fin n) (Fin k) F → L) (ζ : L) :
    {X : Matrix (Fin m ⊕ Fin n) (Fin k) F // φ (X.submatrix Sum.inr id) = ζ} ≃
      Matrix (Fin m) (Fin k) F × {Y : Matrix (Fin n) (Fin k) F // φ Y = ζ} where
  toFun X := (X.val.submatrix Sum.inl id, ⟨X.val.submatrix Sum.inr id, X.property⟩)
  invFun X := ⟨Sum.elim X.1 X.2.val, X.2.property⟩
  left_inv X := by apply Subtype.ext; ext i j; cases i <;> rfl
  right_inv X := rfl

theorem card_lowerTupleFiber {F L : Type*} [Fintype F] (m n k : ℕ)
    (φ : Matrix (Fin n) (Fin k) F → L) (ζ : L) :
    Nat.card {X : Matrix (Fin m ⊕ Fin n) (Fin k) F //
      φ (X.submatrix Sum.inr id) = ζ} =
    Fintype.card F ^ (m*k) * Nat.card {Y : Matrix (Fin n) (Fin k) F // φ Y = ζ} := by
  rw [Nat.card_congr (lowerTupleFiberEquiv m n k φ ζ), Nat.card_prod, card_matrix_fin]

/-- Exact ordinary moment mass Tζ=q^(mk)Mζ, obtained by double counting. -/
theorem ordinary_moment_mass_identity (F : Type*) [Field F] [Fintype F]
    (m n k : ℕ) (ζ : FullMoment (Fin n) F) :
    momentCosetMass (fullMoment (F := F) (ι := Fin m ⊕ Fin n) (k := k))
      lowerMoment ζ =
    Fintype.card F ^ (m*k) *
      Nat.card {Y : Matrix (Fin n) (Fin k) F // fullMoment Y = ζ} := by
  rw [momentCosetMass_eq_card]
  exact card_lowerTupleFiber m n k fullMoment ζ

/-- Exact enhanced binary mass Tζ=2^(mk)Mζ with all mod-four lower data retained. -/
theorem binary_moment_mass_identity (m n k : ℕ) (ζ : BinaryEnhancedMoment (Fin n)) :
    momentCosetMass (binaryEnhancedMoment (ι := Fin m ⊕ Fin n) (k := k))
      binaryLowerMoment ζ =
    2 ^ (m*k) *
      Nat.card {Y : Matrix (Fin n) (Fin k) (ZMod 2) // binaryEnhancedMoment Y = ζ} := by
  rw [momentCosetMass_eq_card]
  simpa only [ZMod.card] using card_lowerTupleFiber m n k binaryEnhancedMoment ζ

/-- Occurring full moments, retaining the entire lower coordinate constraint. -/
abbrev ActualMomentSupport {Ω Z L : Type*} (f : Ω → Z) (g : Z → L) (ζ : L) :=
  {z : Z // (∃ x, f x = z) ∧ g z = ζ}

/-- Flattening a support-restricted coordinate fibre changes no moment values. -/
def cosetSupportEquiv {Ω Z L : Type*} (f : Ω → Z) (g : Z → L) (ζ : L) :
    {z : MomentCoset g ζ // ∃ x, f x = z.val} ≃ ActualMomentSupport f g ζ where
  toFun z := ⟨z.val.val, z.property, z.val.property⟩
  invFun z := ⟨⟨z.val, z.property.2⟩, z.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Values outside the actual image contribute zero to any multiplicity
expression that vanishes at zero. -/
theorem sum_coset_eq_support {Ω Z L : Type*} [Fintype Ω] [Fintype Z]
    (f : Ω → Z) (g : Z → L) (ζ : L) (v : ℕ → ℝ) (hv : v 0 = 0) :
    (∑ z : MomentCoset g ζ, v (tupleMultiplicity f z.val)) =
      ∑ z : ActualMomentSupport f g ζ, v (tupleMultiplicity f z.val) := by
  classical
  have hz : (∑ z : {z : MomentCoset g ζ // ¬ ∃ x, f x = z.val},
      v (tupleMultiplicity f z.val.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    letI : IsEmpty {x : Ω // f x = z.val.val} :=
      ⟨fun x => z.property ⟨x.val, x.property⟩⟩
    simp only [tupleMultiplicity, Nat.card_of_isEmpty, hv]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun z : MomentCoset g ζ => ∃ x, f x = z.val)
    (fun z => v (tupleMultiplicity f z.val))
  rw [hz, add_zero] at hs
  rw [← hs]
  exact Fintype.sum_equiv (cosetSupportEquiv f g ζ) _ _ (fun _ => rfl)

/-- The literal square-root multiplicity sum in one complete coordinate fibre. -/
def momentCosetSqrtSum {Ω Z L : Type*} [Fintype Z]
    (f : Ω → Z) (g : Z → L) (ζ : L) : ℝ := by
  classical
  exact ∑ z : MomentCoset g ζ, Real.sqrt (tupleMultiplicity f z.val : ℝ)

/-- Cosetwise Cauchy--Schwarz for actual multiplicities, with the actual number
of occurring moments. Neither support size nor tuple mass is supplied as a bound. -/
theorem moment_coset_cauchy {Ω Z L : Type*} [Fintype Ω] [Fintype Z]
    (f : Ω → Z) (g : Z → L) (ζ : L) :
    (momentCosetSqrtSum f g ζ)^2 ≤
      (Nat.card (ActualMomentSupport f g ζ) : ℝ) * (momentCosetMass f g ζ : ℝ) := by
  classical
  rw [momentCosetSqrtSum, sum_coset_eq_support f g ζ
    (fun N => Real.sqrt (N : ℝ)) (by simp)]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ActualMomentSupport f g ζ => (1 : ℝ))
    (fun z => Real.sqrt (tupleMultiplicity f z.val : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Real.sq_sqrt (Nat.cast_nonneg _)] at h
  have hm : (momentCosetMass f g ζ : ℝ) =
      ∑ z : ActualMomentSupport f g ζ, (tupleMultiplicity f z.val : ℝ) := by
    rw [momentCosetMass, Nat.cast_sum]
    exact sum_coset_eq_support f g ζ (fun N => (N : ℝ)) (by simp)
  rw [hm, Nat.card_eq_fintype_card]
  exact h

/-- Ordinary coset Cauchy bound with the proved lower-tuple mass identity. -/
theorem ordinary_moment_coset_cauchy (F : Type*) [Field F] [Fintype F]
    (m n k : ℕ) (ζ : FullMoment (Fin n) F) :
    (momentCosetSqrtSum (fullMoment (F := F) (ι := Fin m ⊕ Fin n) (k := k))
      lowerMoment ζ)^2 ≤
      (occurringMomentCount F m n k ζ : ℝ) * ((Fintype.card F : ℝ)^(m*k) *
        (Nat.card {Y : Matrix (Fin n) (Fin k) F // fullMoment Y = ζ} : ℝ)) := by
  have h := moment_coset_cauchy
    (fullMoment (F := F) (ι := Fin m ⊕ Fin n) (k := k)) lowerMoment ζ
  rw [ordinary_moment_mass_identity, Nat.cast_mul, Nat.cast_pow] at h
  exact h

/-- Enhanced binary coset Cauchy bound with the independently proved binary mass. -/
theorem binary_moment_coset_cauchy (m n k : ℕ) (ζ : BinaryEnhancedMoment (Fin n)) :
    (momentCosetSqrtSum (binaryEnhancedMoment (ι := Fin m ⊕ Fin n) (k := k))
      binaryLowerMoment ζ)^2 ≤
      (Nat.card (BinaryOccurringFiber m n k ζ) : ℝ) * ((2 : ℝ)^(m*k) *
        (Nat.card {Y : Matrix (Fin n) (Fin k) (ZMod 2) //
          binaryEnhancedMoment Y = ζ} : ℝ)) := by
  have h := moment_coset_cauchy
    (binaryEnhancedMoment (ι := Fin m ⊕ Fin n) (k := k)) binaryLowerMoment ζ
  rw [binary_moment_mass_identity, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

end StabilizerLearning
