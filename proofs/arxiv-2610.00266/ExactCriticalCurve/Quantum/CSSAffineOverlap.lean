import ExactCriticalCurve.Quantum.CSSAffine
import ExactCriticalCurve.Quantum.StochasticIsometry

/-! # Actual affine CSS support intersections

The overlap support is an actual intersection of affine column configurations.
A nonempty intersection is a torsor for the full intersection noise space.
No overlap condition or fiber cardinality is assumed.
-/

noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k : ℕ}

/-- Membership in the affine support translated by the given physical columns. -/
def cssAffineSupport (N : Submodule (ZMod 2) (BinaryVector k))
    (F X : ColumnConfig n k) : Prop :=
  ∀ a, X a - F a ∈ N

/-- The actual intersection of two affine supports. -/
abbrev CSSAffineIntersection (N M : Submodule (ZMod 2) (BinaryVector k))
    (F G : ColumnConfig n k) :=
  {X : ColumnConfig n k // cssAffineSupport N F X ∧ cssAffineSupport M G X}

/-- The support criterion uses every physical column, including the empty family. -/
theorem cssAffineIntersection_nonempty_iff
    (N M : Submodule (ZMod 2) (BinaryVector k)) (F G : ColumnConfig n k) :
    Nonempty (CSSAffineIntersection N M F G) ↔ ∀ a, G a - F a ∈ N ⊔ M := by
  constructor
  · rintro ⟨⟨X, hN, hM⟩⟩ a
    apply Submodule.mem_sup.mpr
    refine ⟨X a - F a, hN a, G a - X a, ?_, ?_⟩
    · simpa only [neg_sub] using M.neg_mem (hM a)
    · abel
  · intro h
    have hd := fun a => Submodule.mem_sup.mp (h a)
    choose u hu v hv huv using hd
    refine ⟨⟨fun a => F a + u a, ?_, ?_⟩⟩
    · intro a
      simpa only [add_sub_cancel_left] using hu a
    · intro a
      have he : F a + u a - G a = -v a := by
        calc
          F a + u a - G a = u a - (G a - F a) := by abel
          _ = u a - (u a + v a) := by rw [← huv a]
          _ = -v a := by abel
      rw [he]
      exact M.neg_mem (hv a)

/-- Translation by an actual intersection point gives every intersection point
exactly once, with all intersection-noise columns retained. -/
def cssAffineIntersectionEquiv
    (N M : Submodule (ZMod 2) (BinaryVector k)) (F G : ColumnConfig n k)
    (Y : CSSAffineIntersection N M F G) :
    (Fin n → ↥(N ⊓ M)) ≃ CSSAffineIntersection N M F G where
  toFun Z := ⟨fun a => Y.val a + (Z a).val, by
    constructor
    · intro a
      have he : Y.val a + (Z a).val - F a = (Y.val a - F a) + (Z a).val := by abel
      change Y.val a + (Z a).val - F a ∈ N
      rw [he]
      exact N.add_mem (Y.property.1 a) (Z a).property.1
    · intro a
      have he : Y.val a + (Z a).val - G a = (Y.val a - G a) + (Z a).val := by abel
      change Y.val a + (Z a).val - G a ∈ M
      rw [he]
      exact M.add_mem (Y.property.2 a) (Z a).property.2⟩
  invFun X a := ⟨X.val a - Y.val a, by
    constructor
    · convert N.sub_mem (X.property.1 a) (Y.property.1 a) using 1 <;> abel
    · convert M.sub_mem (X.property.2 a) (Y.property.2 a) using 1 <;> abel⟩
  left_inv Z := by funext a; apply Subtype.ext; simp
  right_inv X := by apply Subtype.ext; funext a; simp

/-- Exact cardinality of the actual nonempty intersection, including n=0. -/
theorem cssAffineIntersection_card_of_nonempty
    (N M : Submodule (ZMod 2) (BinaryVector k)) (F G : ColumnConfig n k)
    (h : Nonempty (CSSAffineIntersection N M F G)) :
    Nat.card (CSSAffineIntersection N M F G) =
      ((2 : ℕ)^n)^Module.finrank (ZMod 2) ↥(N ⊓ M) := by
  obtain ⟨Y⟩ := h
  rw [← Nat.card_congr (cssAffineIntersectionEquiv N M F G Y)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  rw [← Nat.card_eq_fintype_card, cssSubspace_card, ← pow_mul, Nat.mul_comm, pow_mul]

/-- Both the empty and nonempty branches are explicit. -/
theorem cssAffineIntersection_card
    (N M : Submodule (ZMod 2) (BinaryVector k)) (F G : ColumnConfig n k) :
    Nat.card (CSSAffineIntersection N M F G) =
      if ∀ a, G a - F a ∈ N ⊔ M
      then ((2 : ℕ)^n)^Module.finrank (ZMod 2) ↥(N ⊓ M) else 0 := by
  by_cases h : ∀ a, G a - F a ∈ N ⊔ M
  · rw [if_pos h]
    exact cssAffineIntersection_card_of_nonempty N M F G
      ((cssAffineIntersection_nonempty_iff N M F G).mpr h)
  · rw [if_neg h]
    letI : IsEmpty (CSSAffineIntersection N M F G) :=
      ⟨fun X => h ((cssAffineIntersection_nonempty_iff N M F G).mp ⟨X⟩)⟩
    simp


/-- The paper's normalized equal-amplitude affine vector on actual columns. -/
def cssAffineColumnVector (N : Submodule (ZMod 2) (BinaryVector k))
    (F : ColumnConfig n k) : ColumnConfig n k → ℂ :=
  fun X => if cssAffineSupport N F X
    then ((Real.sqrt (Nat.card N) : ℂ)⁻¹)^n else 0

/-- The affine vector is exactly the existing physical CSS synthesis column. -/
theorem cssAffineColumnVector_eq_synthesis
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) :
    cssAffineColumnVector N (fun a => (F (Pi.single a 1)).val) =
      (cssHomSynthesis n N).col ((N.comap (orthogonal N).subtype).mkQ.comp F) := by
  funext X
  rw [Matrix.col_apply, cssHomSynthesis_apply]
  have h : cssAffineSupport N (fun a => (F (Pi.single a 1)).val) X ↔
      ∀ a, cosetMember (orthogonal N) N (X a)
        (((N.comap (orthogonal N).subtype).mkQ.comp F) (Pi.single a 1)) := by
    constructor
    · intro hx a
      apply (cosetMember_mk_iff (orthogonal N) N (X a) (F (Pi.single a 1))).mpr
      refine ⟨?_, hx a⟩
      have hm := (orthogonal N).add_mem (hN.le_orthogonal (hx a))
        (F (Pi.single a 1)).property
      simpa only [sub_add_cancel] using hm
    · intro hx a
      exact ((cosetMember_mk_iff (orthogonal N) N _ _).mp (hx a)).2
  simp only [cssAffineColumnVector, h]

/-- Actual permutation action sends the affine support to the transported defect. -/
theorem stochasticIsometry_cssAffineColumnVector
    (N : Submodule (ZMod 2) (BinaryVector k)) (F : ColumnConfig n k)
    (g : StochasticIsometryGroup k) :
    stochasticIsometryMatrix n g *ᵥ cssAffineColumnVector N F =
      cssAffineColumnVector (stochasticSubspace g N) (fun a => g.val (F a)) := by
  rw [stochasticIsometryMatrix_mulVec]
  funext X
  have hs : cssAffineSupport N F ((stochasticColumnPerm n g).symm X) ↔
      cssAffineSupport (stochasticSubspace g N) (fun a => g.val (F a)) X := by
    simp only [cssAffineSupport, mem_stochasticSubspace, map_sub,
      LinearEquiv.symm_apply_apply]
    rfl
  have hc : Nat.card (stochasticSubspace g N) = Nat.card N := by
    rw [cssSubspace_card, stochasticSubspace_finrank, cssSubspace_card]
  simp only [Function.comp_apply, cssAffineColumnVector, hs, hc]

/-- The exact normalized overlap before the support count is substituted. -/
theorem cssAffineColumnVector_overlap_card
    (N M : Submodule (ZMod 2) (BinaryVector k)) (F G : ColumnConfig n k) :
    star (cssAffineColumnVector N F) ⬝ᵥ cssAffineColumnVector M G =
      (((Real.sqrt (Nat.card N) : ℂ)⁻¹)^n *
        ((Real.sqrt (Nat.card M) : ℂ)⁻¹)^n) *
        (Nat.card (CSSAffineIntersection N M F G) : ℂ) := by
  have hterm (X : ColumnConfig n k) :
      star (cssAffineColumnVector N F X) * cssAffineColumnVector M G X =
      (((Real.sqrt (Nat.card N) : ℂ)⁻¹)^n *
        ((Real.sqrt (Nat.card M) : ℂ)⁻¹)^n) *
      (if cssAffineSupport N F X ∧ cssAffineSupport M G X then 1 else 0) := by
    by_cases hN : cssAffineSupport N F X <;>
      by_cases hM : cssAffineSupport M G X <;>
      simp [cssAffineColumnVector, hN, hM]
  change (∑ X, star (cssAffineColumnVector N F X) * cssAffineColumnVector M G X) = _
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  simp [Nat.card_eq_fintype_card, CSSAffineIntersection, Fintype.card_subtype]

/-- A full lift makes the finite-column criterion exactly the paper's subspace criterion. -/
theorem cssAffineIntersection_stochastic_iff
    (N : Submodule (ZMod 2) (BinaryVector k))
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) (hF : Function.Surjective F)
    (g : StochasticIsometryGroup k) :
    Nonempty (CSSAffineIntersection N (stochasticSubspace g N)
      (fun a => (F (Pi.single a 1)).val)
      (fun a => g.val (F (Pi.single a 1)).val)) ↔
    ∀ x ∈ orthogonal N, g.val x - x ∈ N ⊔ stochasticSubspace g N := by
  rw [cssAffineIntersection_nonempty_iff]
  let A : BinaryVector n →ₗ[ZMod 2] BinaryVector k :=
    (g.val.toLinearMap - LinearMap.id).comp ((orthogonal N).subtype.comp F)
  constructor
  · intro h x hx
    have hr : LinearMap.range A ≤ N ⊔ stochasticSubspace g N :=
      (homColumnsEquiv_range_le_iff n (BinaryVector k) A _).mpr (by
        intro a
        rw [homColumnsEquiv_apply]
        exact h a)
    obtain ⟨v, hv⟩ := hF ⟨x, hx⟩
    have hv' : A v = g.val x - x := by
      change g.val (F v).val - (F v).val = _
      rw [hv]
    exact hr ⟨v, hv'⟩
  · intro h a
    exact h _ (F (Pi.single a 1)).property


/-- Squaring the existing CSS amplitude gives the inverse support cardinality. -/
theorem cssAffineAmplitude_square (N : Submodule (ZMod 2) (BinaryVector k)) :
    ((Real.sqrt (Nat.card N) : ℂ)⁻¹)^n *
      ((Real.sqrt (Nat.card N) : ℂ)⁻¹)^n =
      (((2 : ℂ)^n)^Module.finrank (ZMod 2) N)⁻¹ := by
  have hnz : (Nat.card N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (cosetCard_ne_zero N)
  have hnorm : (Real.sqrt (Nat.card N) : ℂ)⁻¹ *
      (Real.sqrt (Nat.card N) : ℂ)⁻¹ = (Nat.card N : ℂ)⁻¹ :=
    by
      apply mul_right_cancel₀ hnz
      rw [inv_mul_cancel₀ hnz]
      exact coset_normalization N
  rw [← mul_pow, hnorm]
  have hc : (Nat.card N : ℂ)^n = ((2 : ℂ)^n)^Module.finrank (ZMod 2) N := by
    rw [cssSubspace_card, Nat.cast_pow, Nat.cast_ofNat,
      ← pow_mul, Nat.mul_comm, pow_mul]
  rw [← hc, inv_pow]

/-- The complete normalized overlap, with the exact zero branch. -/
theorem cssAffineColumnVector_overlap
    (N M : Submodule (ZMod 2) (BinaryVector k)) (F G : ColumnConfig n k)
    (hdim : Module.finrank (ZMod 2) M = Module.finrank (ZMod 2) N) :
    star (cssAffineColumnVector N F) ⬝ᵥ cssAffineColumnVector M G =
      if ∀ a, G a - F a ∈ N ⊔ M
      then (((2 : ℂ)^n)^(Module.finrank (ZMod 2) N -
        Module.finrank (ZMod 2) ↥(N ⊓ M)))⁻¹ else 0 := by
  have hcard : Nat.card M = Nat.card N := by
    rw [cssSubspace_card, hdim, cssSubspace_card]
  rw [cssAffineColumnVector_overlap_card, hcard, cssAffineAmplitude_square,
    cssAffineIntersection_card]
  split_ifs with h
  · simp only [Nat.cast_pow, Nat.cast_ofNat]
    have hle : Module.finrank (ZMod 2) ↥(N ⊓ M) ≤ Module.finrank (ZMod 2) N :=
      Submodule.finrank_mono inf_le_left
    have hD : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_right_cancel₀ (pow_ne_zero
      (Module.finrank (ZMod 2) N - Module.finrank (ZMod 2) ↥(N ⊓ M)) hD)
    rw [inv_mul_cancel₀ (pow_ne_zero _ hD), mul_assoc, ← pow_add,
      Nat.add_sub_of_le hle, inv_mul_cancel₀ (pow_ne_zero _ hD)]
  · simp

/-- The actual physical CSS vector has the exact stochastic-isometry overlap
from the paper, with no ordinary-branch or positive-dimension restriction. -/
theorem cssHomSynthesis_stochastic_overlap
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) (hF : Function.Surjective F)
    (g : StochasticIsometryGroup k) :
    let v := (cssHomSynthesis n N).col ((N.comap (orthogonal N).subtype).mkQ.comp F)
    star v ⬝ᵥ (stochasticIsometryMatrix n g *ᵥ v) =
      if ∀ x ∈ orthogonal N, g.val x - x ∈ N ⊔ stochasticSubspace g N
      then (((2 : ℂ)^n)^(Module.finrank (ZMod 2) N -
        Module.finrank (ZMod 2) ↥(N ⊓ stochasticSubspace g N)))⁻¹ else 0 := by
  dsimp only
  rw [← cssAffineColumnVector_eq_synthesis N hN F,
    stochasticIsometry_cssAffineColumnVector,
    cssAffineColumnVector_overlap N (stochasticSubspace g N) _ _
      (stochasticSubspace_finrank g N)]
  have hc := (cssAffineIntersection_nonempty_iff N (stochasticSubspace g N)
    (fun a => (F (Pi.single a 1)).val)
    (fun a => g.val (F (Pi.single a 1)).val)).symm.trans
      (cssAffineIntersection_stochastic_iff N F hF g)
  simp only [hc]

end ExactCriticalCurve.Quantum
