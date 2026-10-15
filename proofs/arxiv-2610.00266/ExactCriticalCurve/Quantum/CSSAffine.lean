import ExactCriticalCurve.Quantum.CSS
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The paper's affine description of CSS coset states

Actual linear lifts exist, and normalized Hom-labeled columns agree with
the sum over all noise maps into the defect. No lift is postulated globally.
-/

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Classical
namespace ExactCriticalCurve.Quantum
open Binary

variable {k : ℕ}

abbrev CSSNoise (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :=
  BinaryVector n →ₗ[ZMod 2] N

noncomputable instance cssNoiseFintype (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) : Fintype (CSSNoise n N) :=
  Fintype.ofEquiv (Fin n → N) (homColumnsEquiv n N).symm.toEquiv

/-- A label has a genuine linear lift through the actual quotient map. -/
theorem exists_cssLinearLift (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (f : CSSHom n N) :
    ∃ F : BinaryVector n →ₗ[ZMod 2] orthogonal N,
      (N.comap (orthogonal N).subtype).mkQ.comp F = f := by
  let π := (N.comap (orthogonal N).subtype).mkQ
  have hg : ∀ a : Fin n, ∃ y : orthogonal N, π y = f (Pi.single a 1) :=
    fun a => (N.comap (orthogonal N).subtype).mkQ_surjective (f (Pi.single a 1))
  choose g hg using hg
  refine ⟨(homColumnsEquiv n (orthogonal N)).symm g, ?_⟩
  apply (homColumnsEquiv n (CSSQuotient N)).injective
  rw [homColumnsEquiv_comp, LinearEquiv.apply_symm_apply]
  ext a
  simpa only [homColumnsEquiv_apply] using hg a

/-- The computational-basis configuration of the linear map F plus noise Z. -/
def cssAffineConfig (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) (Z : CSSNoise n N) :
    ColumnConfig n k :=
  fun a => (F (Pi.single a 1)).val + (Z (Pi.single a 1)).val

theorem cssAffineConfig_injective (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) :
    Function.Injective (cssAffineConfig n N F) := by
  intro Z W h
  apply (homColumnsEquiv n N).injective
  funext a
  apply Subtype.ext
  simp only [homColumnsEquiv_apply]
  exact add_left_cancel (congrFun h a)

/-- Pointwise quotient membership is precisely the paper's affine noise support. -/
theorem cssHom_support_iff_affine (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (F : BinaryVector n →ₗ[ZMod 2] orthogonal N)
    (hF : (N.comap (orthogonal N).subtype).mkQ.comp F = f)
    (X : ColumnConfig n k) :
    (∀ a, cosetMember (orthogonal N) N (X a) (f (Pi.single a 1))) ↔
      ∃ Z : CSSNoise n N, X = cssAffineConfig n N F Z := by
  have hf (a : Fin n) :
      (Submodule.Quotient.mk (F (Pi.single a 1)) : CSSQuotient N) =
        f (Pi.single a 1) :=
    LinearMap.congr_fun hF (Pi.single a 1)
  constructor
  · intro h
    have hd (a : Fin n) : X a - (F (Pi.single a 1)).val ∈ N := by
      have ha := h a
      rw [← hf a, cosetMember_mk_iff] at ha
      exact ha.2
    let g : Fin n → N := fun a => ⟨X a - (F (Pi.single a 1)).val, hd a⟩
    let Z : CSSNoise n N := (homColumnsEquiv n N).symm g
    refine ⟨Z, ?_⟩
    funext a
    have hz : Z (Pi.single a 1) = g a := by
      simpa only [homColumnsEquiv_apply] using
        congrFun ((homColumnsEquiv n N).apply_symm_apply g) a
    change X a = (F (Pi.single a 1)).val + (Z (Pi.single a 1)).val
    rw [hz]
    change X a = (F (Pi.single a 1)).val + (X a - (F (Pi.single a 1)).val)
    abel
  · rintro ⟨Z, rfl⟩ a
    rw [← hf a, cosetMember_mk_iff]
    exact ⟨(orthogonal N).add_mem (F (Pi.single a 1)).property
      (hN.le_orthogonal (Z (Pi.single a 1)).property),
      by simpa only [cssAffineConfig, add_sub_cancel_left] using
        (Z (Pi.single a 1)).property⟩

/-- The affine configuration is attained by at most one actual noise map. -/
theorem cssAffine_sum_indicator (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) (X : ColumnConfig n k) :
    (∑ Z : CSSNoise n N, if X = cssAffineConfig n N F Z then (1 : ℂ) else 0) =
      if ∃ Z : CSSNoise n N, X = cssAffineConfig n N F Z then 1 else 0 := by
  classical
  by_cases h : ∃ Z : CSSNoise n N, X = cssAffineConfig n N F Z
  · obtain ⟨Z, hZ⟩ := h
    rw [if_pos ⟨Z, hZ⟩]
    rw [Finset.sum_eq_single Z]
    · simp [hZ]
    · intro W _ hW
      have hn : X ≠ cssAffineConfig n N F W := by
        intro hX
        apply hW
        exact cssAffineConfig_injective n N F (hX.symm.trans hZ)
      simp [hn]
    · simp
  · have hn : ∀ Z : CSSNoise n N, X ≠ cssAffineConfig n N F Z :=
      fun Z hZ => h ⟨Z, hZ⟩
    simp [hn]


/-- The number of actual linear noise maps is D raised to the defect dimension. -/
theorem cssNoise_card (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    Nat.card (CSSNoise n N) = ((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N := by
  calc
    Nat.card (CSSNoise n N) = Nat.card (Fin n → N) :=
      Nat.card_congr (homColumnsEquiv n N).toEquiv
    _ = (Nat.card N) ^ n := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    _ = _ := by rw [cssSubspace_card, ← pow_mul, Nat.mul_comm, pow_mul]

/-- The exact affine-sum formula in the paper, expressed on computational basis entries. -/
theorem cssHomSynthesis_eq_affine_sum (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (F : BinaryVector n →ₗ[ZMod 2] orthogonal N)
    (hF : (N.comap (orthogonal N).subtype).mkQ.comp F = f)
    (X : ColumnConfig n k) :
    cssHomSynthesis n N X f =
      (Real.sqrt ((((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ Z : CSSNoise n N, if X = cssAffineConfig n N F Z then 1 else 0 := by
  rw [cssHomSynthesis_apply_sqrt, cssAffine_sum_indicator]
  by_cases h : ∀ a, cosetMember (orthogonal N) N (X a) (f (Pi.single a 1))
  · have he := (cssHom_support_iff_affine n N hN f F hF X).mp h
    simp only [if_pos h, if_pos he, mul_one]
  · have he : ¬ ∃ Z : CSSNoise n N, X = cssAffineConfig n N F Z :=
      fun he => h ((cssHom_support_iff_affine n N hN f F hF X).mpr he)
    simp only [if_neg h, if_neg he, mul_zero]

/-- The affine expression is independent of which actual linear lift is chosen. -/
theorem cssAffine_sum_lift_independent (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (F G : BinaryVector n →ₗ[ZMod 2] orthogonal N)
    (hF : (N.comap (orthogonal N).subtype).mkQ.comp F = f)
    (hG : (N.comap (orthogonal N).subtype).mkQ.comp G = f)
    (X : ColumnConfig n k) :
    (Real.sqrt ((((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ) : ℝ) : ℂ)⁻¹ *
        (∑ Z : CSSNoise n N, if X = cssAffineConfig n N F Z then 1 else 0) =
      (Real.sqrt ((((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ Z : CSSNoise n N, if X = cssAffineConfig n N G Z then 1 else 0 := by
  rw [← cssHomSynthesis_eq_affine_sum n N hN f F hF X,
    ← cssHomSynthesis_eq_affine_sum n N hN f G hG X]

/-- The same affine-sum identity on the paper's original copy-first basis indexing. -/
theorem cssCopySynthesis_eq_affine_sum (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (F : BinaryVector n →ₗ[ZMod 2] orthogonal N)
    (hF : (N.comap (orthogonal N).subtype).mkQ.comp F = f)
    (X : CopyConfig n k) :
    cssCopySynthesis n N X f =
      (Real.sqrt ((((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ) : ℝ) : ℂ)⁻¹ *
        ∑ Z : CSSNoise n N,
          if copyColumnsEquiv n k X = cssAffineConfig n N F Z then 1 else 0 :=
  cssHomSynthesis_eq_affine_sum n N hN f F hF (copyColumnsEquiv n k X)


/-- The paper's real-power normalization is exactly the inverse square root. -/
theorem css_normalization_rpow_eq_sqrt_inv (n r : ℕ) :
    ((2 : ℝ) ^ n) ^ (-(r : ℝ) / 2) =
      (Real.sqrt (((2 : ℕ) ^ n) ^ r : ℕ))⁻¹ := by
  have hbase : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  rw [neg_div, Real.rpow_neg hbase, Real.sqrt_eq_rpow]
  congr 1
  rw [show (r : ℝ) / 2 = (r : ℝ) * (1 / 2) by ring,
    Real.rpow_natCast_mul hbase]
  norm_cast

/-- The affine CSS sum with the literal D^(-r/2) coefficient from the paper. -/
theorem cssCopySynthesis_eq_affine_rpow (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (F : BinaryVector n →ₗ[ZMod 2] orthogonal N)
    (hF : (N.comap (orthogonal N).subtype).mkQ.comp F = f)
    (X : CopyConfig n k) :
    cssCopySynthesis n N X f =
      ((Real.rpow ((2 : ℝ) ^ n) (-(Module.finrank (ZMod 2) N : ℝ) / 2) : ℝ) : ℂ) *
        ∑ Z : CSSNoise n N,
          if copyColumnsEquiv n k X = cssAffineConfig n N F Z then 1 else 0 := by
  have hc : Real.rpow ((2 : ℝ) ^ n) (-(Module.finrank (ZMod 2) N : ℝ) / 2) =
      (Real.sqrt (((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ))⁻¹ :=
    css_normalization_rpow_eq_sqrt_inv n (Module.finrank (ZMod 2) N)
  rw [hc, Complex.ofReal_inv]
  exact cssCopySynthesis_eq_affine_sum n N hN f F hF X

end ExactCriticalCurve.Quantum
