import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRefinementCounts
import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRealizability

/-! Actual embeddable refinements of one fixed polar in a genuine quadratic target. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Membership means the existence of a genuine injective full-quadratic linear map. -/
abbrev BinaryQuadraticEmbeddableRefinements (B : LinearMap.BilinForm (ZMod 2) A)
    (Q : QuadraticForm (ZMod 2) V) :=
  {P : BinaryQuadraticRefinements B //
    ∃ f : A →ₗ[ZMod 2] V, Function.Injective f ∧ ∀ x, Q (f x) = P.val x}

variable [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) V]
  [Fintype A] [Fintype V]

theorem binaryRefinement_embeds_iff
    (B : LinearMap.BilinForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t) (hm : finrank (ZMod 2) V = 2*m)
    (P : BinaryQuadraticRefinements B) :
    (∃ f : A →ₗ[ZMod 2] V, Function.Injective f ∧ ∀ x, Q (f x) = P.val x) ↔
      b+t ≤ m ∧ (b+t < m ∨ binaryQuadraticGaussSum P.val = 0 ∨
        binaryQuadraticGaussSum Q = binaryQuadraticGaussSum P.val) := by
  have hr : finrank (ZMod 2) (binaryPolarRadical P.val) = b := by
    change finrank (ZMod 2) (LinearMap.ker P.val.polarBilin) = b
    rw [P.property]
    exact hb
  rw [exists_binaryQuadratic_embedding_iff P.val Q hQ]
  have hle : finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical P.val) ≤
      finrank (ZMod 2) V ↔ b+t ≤ m := by omega
  have hlt : finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical P.val) <
      finrank (ZMod 2) V ↔ b+t < m := by omega
  rw [hle,hlt]

/-- Strict room realizes every actual refinement, with no choice of its sign required. -/
def binaryQuadraticEmbeddableStrictEquiv
    (B : LinearMap.BilinForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t) (hm : finrank (ZMod 2) V = 2*m)
    (hs : b+t < m) :
    BinaryQuadraticEmbeddableRefinements B Q ≃ BinaryQuadraticRefinements B :=
  Equiv.subtypeUnivEquiv (fun P =>
    (binaryRefinement_embeds_iff B Q hQ b t m hb hd hm P).mpr ⟨hs.le,Or.inl hs⟩)

theorem binaryQuadraticEmbeddable_strict_card
    (B : LinearMap.BilinForm (ZMod 2) A) (hB : B.IsAlt)
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t) (hm : finrank (ZMod 2) V = 2*m)
    (hs : b+t < m) :
    Nat.card (BinaryQuadraticEmbeddableRefinements B Q) = 2^(b+2*t) := by
  rw [Nat.card_congr (binaryQuadraticEmbeddableStrictEquiv B Q hQ b t m hb hd hm hs),
    binaryQuadraticRefinements_card B hB,hd]

theorem binaryQuadraticEmbeddable_forbidden_card
    (B : LinearMap.BilinForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t) (hm : finrank (ZMod 2) V = 2*m)
    (hs : m < b+t) :
    Nat.card (BinaryQuadraticEmbeddableRefinements B Q) = 0 := by
  haveI : IsEmpty (BinaryQuadraticEmbeddableRefinements B Q) := ⟨fun P => by
    have he := ((binaryRefinement_embeds_iff B Q hQ b t m hb hd hm P.val).mp P.property).1
    omega⟩
  exact Nat.card_of_isEmpty

/-- On the exact boundary the actual embeddable fiber is the disjoint union of the zero
Gauss fiber and the fiber matching the actual target's full signed Gauss sum. -/
def binaryQuadraticEmbeddableBoundaryEquiv
    (B : LinearMap.BilinForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t) (hm : finrank (ZMod 2) V = 2*m)
    (he : b+t = m) :
    BinaryQuadraticEmbeddableRefinements B Q ≃
      {P : BinaryQuadraticRefinements B // binaryQuadraticGaussSum P.val = 0} ⊕
      {P : BinaryQuadraticRefinements B // binaryQuadraticGaussSum P.val = binaryQuadraticGaussSum Q} :=
  (Equiv.subtypeEquivRight (fun P => by
    rw [binaryRefinement_embeds_iff B Q hQ b t m hb hd hm P,he]
    simp only [le_refl,lt_self_iff_false,false_or,true_and,eq_comm])).trans
      (subtypeOrEquiv _ _ (Set.disjoint_left.mpr (fun P h0 hmatch =>
        binaryQuadraticGaussSum_ne_zero Q hQ (hmatch.symm.trans h0))))

theorem binaryQuadraticEmbeddable_boundary_card
    (B : LinearMap.BilinForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t) (hm : finrank (ZMod 2) V = 2*m)
    (he : b+t = m) :
    Nat.card (BinaryQuadraticEmbeddableRefinements B Q) =
      Nat.card {P : BinaryQuadraticRefinements B // binaryQuadraticGaussSum P.val = 0} +
      Nat.card {P : BinaryQuadraticRefinements B // binaryQuadraticGaussSum P.val = binaryQuadraticGaussSum Q} := by
  rw [Nat.card_congr (binaryQuadraticEmbeddableBoundaryEquiv B Q hQ b t m hb hd hm he),
    Nat.card_sum]

theorem binaryQuadraticEmbeddable_positive_boundary_card
    (B : LinearMap.BilinForm (ZMod 2) A) (hB : B.IsAlt)
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t) (hm : finrank (ZMod 2) V = 2*m)
    (he : b+t = m) (hg : binaryQuadraticGaussSum Q = (2 : ℂ)^m) :
    2 * Nat.card (BinaryQuadraticEmbeddableRefinements B Q) =
      2*((2^b-1)*2^(2*t))+2^(2*t)+2^t := by
  rw [binaryQuadraticEmbeddable_boundary_card B Q hQ b t m hb hd hm he,hg,← he,mul_add]
  obtain ⟨h0,hp,_,_⟩ := binaryQuadraticRefinements_gauss_counts B hB b t hb hd
  rw [h0,hp]
  omega

theorem binaryQuadraticEmbeddable_negative_boundary_card
    (B : LinearMap.BilinForm (ZMod 2) A) (hB : B.IsAlt)
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t) (hm : finrank (ZMod 2) V = 2*m)
    (he : b+t = m) (hg : binaryQuadraticGaussSum Q = -((2 : ℂ)^m)) :
    2 * Nat.card (BinaryQuadraticEmbeddableRefinements B Q) + 2^t =
      2*((2^b-1)*2^(2*t))+2^(2*t) := by
  rw [binaryQuadraticEmbeddable_boundary_card B Q hQ b t m hb hd hm he,hg,← he,mul_add]
  obtain ⟨h0,_,hn,_⟩ := binaryQuadraticRefinements_gauss_counts B hB b t hb hd
  rw [h0]
  omega

/-- For two genuine targets of opposite Gauss sign, the boundary difference is exactly 2^t.
The types and quadratic forms are supplied explicitly; no minus target is introduced in dimension zero. -/
theorem binaryQuadraticEmbeddable_boundary_sign_difference
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Fintype W]
    (B : LinearMap.BilinForm (ZMod 2) A) (hB : B.IsAlt)
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B) = b)
    (hd : finrank (ZMod 2) A = b+2*t)
    (hmQ : finrank (ZMod 2) V = 2*m) (hmP : finrank (ZMod 2) W = 2*m)
    (he : b+t = m) (hgQ : binaryQuadraticGaussSum Q = (2 : ℂ)^m)
    (hgP : binaryQuadraticGaussSum P = -((2 : ℂ)^m)) :
    Nat.card (BinaryQuadraticEmbeddableRefinements B Q) =
      Nat.card (BinaryQuadraticEmbeddableRefinements B P) + 2^t := by
  have hp := binaryQuadraticEmbeddable_positive_boundary_card B hB Q hQ b t m hb hd hmQ he hgQ
  have hn := binaryQuadraticEmbeddable_negative_boundary_card B hB P hP b t m hb hd hmP he hgP
  omega

end ExactCriticalCurve.FiniteQuadratic
