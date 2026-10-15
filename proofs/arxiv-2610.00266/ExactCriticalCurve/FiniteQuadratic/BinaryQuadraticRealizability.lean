import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticAdjustment

/-! Exact realizability of arbitrary genuine binary quadratic forms.
Only the actual radical dimension and signed Gauss sums occur in the criterion. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) V]
  [Fintype A] [Fintype V]

/-- If the orthogonal complement is totally singular, the embedding has minimal dimension
and the full ambient Gauss sum equals the actual source Gauss sum. -/
theorem binaryQuadratic_orthogonal_zero_boundary
    (q : QuadraticForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (f : A →ₗ[ZMod 2] V) (hf : Function.Injective f) (hfq : ∀ x, Q (f x) = q x)
    (hz : ∀ v : binaryPolarOrthogonal Q (LinearMap.range f), Q v.val = 0) :
    finrank (ZMod 2) V = finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical q) ∧
      binaryQuadraticGaussSum Q = binaryQuadraticGaussSum q := by
  let U := binaryPolarOrthogonal Q (LinearMap.range f)
  have hUU : binaryPolarOrthogonal Q U = LinearMap.range f :=
    LinearMap.BilinForm.orthogonal_orthogonal hQ (polar_isSymm Q).isRefl _
  have hUS : U ≤ LinearMap.range f := by
    rw [← hUU]
    intro x hx y hy
    change Q.polarBilin y x = 0
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
    rw [hz ⟨y+x,U.add_mem hy hx⟩,hz ⟨y,hy⟩,hz ⟨x,hx⟩]
    simp
  have hj : LinearMap.range (f.comp (binaryPolarRadical q).subtype) = U := by
    rw [binaryQuadratic_radical_image_eq q Q f hfq]
    exact inf_eq_right.mpr hUS
  have hr := congrArg (fun S : Submodule (ZMod 2) V => finrank (ZMod 2) S) hj
  have hji : Function.Injective (f.comp (binaryPolarRadical q).subtype) :=
    hf.comp Subtype.val_injective
  dsimp only at hr
  rw [LinearMap.finrank_range_of_inj hji] at hr
  have hdimU : finrank (ZMod 2) U = finrank (ZMod 2) V - finrank (ZMod 2) A := by
    dsimp only [U,binaryPolarOrthogonal]
    rw [LinearMap.BilinForm.finrank_orthogonal hQ (polar_isSymm Q).isRefl,
      LinearMap.finrank_range_of_inj hf]
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  refine ⟨by omega,?_⟩
  have hg := binaryQuadraticGaussSum_eq_orthogonal_sum Q U hz
  rw [hUU] at hg
  have hrange := binaryQuadraticGaussSum_range q Q f hf hfq
  have he : f.fintypeRange = Subtype.fintype (Membership.mem (LinearMap.range f)) :=
    Subsingleton.elim _ _
  rw [he] at hrange
  exact hg.trans hrange

/-- At minimal dimension, a singular radical restriction forces exact signed Gauss equality. -/
theorem binaryQuadratic_embedding_boundary_gauss
    (q : QuadraticForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (f : A →ₗ[ZMod 2] V) (hf : Function.Injective f) (hfq : ∀ x, Q (f x) = q x)
    (hd : finrank (ZMod 2) V =
      finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical q))
    (hg : binaryQuadraticGaussSum q ≠ 0) :
    binaryQuadraticGaussSum Q = binaryQuadraticGaussSum q := by
  let U := binaryPolarOrthogonal Q (LinearMap.range f)
  let j := f.comp (binaryPolarRadical q).subtype
  have hjU : LinearMap.range j ≤ U := by
    rw [binaryQuadratic_radical_image_eq q Q f hfq]
    exact inf_le_right
  have hdimU : finrank (ZMod 2) U = finrank (ZMod 2) (binaryPolarRadical q) := by
    dsimp only [U,binaryPolarOrthogonal]
    rw [LinearMap.BilinForm.finrank_orthogonal hQ (polar_isSymm Q).isRefl,
      LinearMap.finrank_range_of_inj hf,hd,Nat.add_sub_cancel_left]
  have hj : LinearMap.range j = U := by
    apply Submodule.eq_of_le_of_finrank_le hjU
    have hji : Function.Injective j := hf.comp Subtype.val_injective
    rw [hdimU,LinearMap.finrank_range_of_inj hji]
  have hl : binaryRadicalLinear q = 0 := by
    by_contra h
    exact hg ((binaryQuadraticGaussSum_zero_iff q).mpr h)
  apply (binaryQuadratic_orthogonal_zero_boundary q Q hQ f hf hfq ?_).2
  intro v
  have hv : v.val ∈ LinearMap.range j := by rw [hj]; exact v.property
  obtain ⟨r,hr⟩ := hv
  rw [← hr]
  change Q (f r.val) = 0
  rw [hfq]
  exact congrArg (fun l : binaryPolarRadical q →ₗ[ZMod 2] ZMod 2 => l r) hl

/-- Exact actual full-quadratic embedding criterion, with the true signed boundary condition.
The zero-dimensional source/ambient and both nondegenerate signs are included. -/
theorem exists_binaryQuadratic_embedding_iff
    (q : QuadraticForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) :
    (∃ f : A →ₗ[ZMod 2] V, Function.Injective f ∧ ∀ x, Q (f x) = q x) ↔
      finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical q) ≤ finrank (ZMod 2) V ∧
      (finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical q) < finrank (ZMod 2) V ∨
        binaryQuadraticGaussSum q = 0 ∨ binaryQuadraticGaussSum Q = binaryQuadraticGaussSum q) := by
  constructor
  · rintro ⟨f,hf,hfq⟩
    have hd := binaryQuadratic_embedding_dimension_bound q Q hQ f hf hfq
    refine ⟨hd,?_⟩
    by_cases hs : finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical q) <
        finrank (ZMod 2) V
    · exact Or.inl hs
    by_cases hg : binaryQuadraticGaussSum q = 0
    · exact Or.inr (Or.inl hg)
    exact Or.inr (Or.inr (binaryQuadratic_embedding_boundary_gauss q Q hQ f hf hfq
      (by omega) hg))
  · rintro ⟨hd,hcase⟩
    obtain ⟨f,hf,hfp⟩ := (exists_alternating_embedding_iff q.polarBilin
      (binaryQuadratic_polar_isAlt q) Q.polarBilin (binaryQuadratic_polar_isAlt Q) hQ).mpr hd
    obtain ⟨P,hpolar,hPf⟩ := exists_binaryQuadratic_refinement q Q f hf hfp
    have hP : LinearMap.BilinForm.Nondegenerate P.polarBilin := by rw [hpolar]; exact hQ
    have transport (T : QuadraticForm (ZMod 2) V)
        (hT : LinearMap.BilinForm.Nondegenerate T.polarBilin)
        (hTf : ∀ x, T (f x) = q x)
        (hG : binaryQuadraticGaussSum T = binaryQuadraticGaussSum Q) :
        ∃ g : A →ₗ[ZMod 2] V, Function.Injective g ∧ ∀ x, Q (g x) = q x := by
      obtain ⟨e⟩ := (binaryQuadratic_isometryEquiv_iff_finrank_gauss T Q hT hQ).mpr ⟨rfl,hG⟩
      refine ⟨e.toLinearEquiv.toLinearMap.comp f,e.toLinearEquiv.injective.comp hf,?_⟩
      intro x
      exact (e.map_app (f x)).trans (hTf x)
    by_cases hG : binaryQuadraticGaussSum P = binaryQuadraticGaussSum Q
    · exact transport P hP hPf hG
    have hneg : binaryQuadraticGaussSum P = -binaryQuadraticGaussSum Q := by
      apply (sq_eq_sq_iff_eq_or_eq_neg.mp ?_).resolve_left hG
      rw [binaryQuadraticGaussSum_sq P hP,binaryQuadraticGaussSum_sq Q hQ]
    obtain ⟨v,hv⟩ : ∃ v : binaryPolarOrthogonal P (LinearMap.range f), P v.val = 1 := by
      by_contra! hz
      have hz0 : ∀ v : binaryPolarOrthogonal P (LinearMap.range f), P v.val = 0 := by
        intro v
        have h := hz v
        generalize he : P v.val = a at h ⊢
        fin_cases a <;> simp_all
      obtain ⟨hmin,hgq⟩ := binaryQuadratic_orthogonal_zero_boundary q P hP f hf hPf hz0
      rcases hcase with hs | hzero | heq
      · omega
      · exact binaryQuadraticGaussSum_ne_zero P hP (hgq.trans hzero)
      · exact hG (hgq.trans heq.symm)
    let T := P + binaryLinearQuadratic (P.polarBilin.flip v.val)
    have hT : LinearMap.BilinForm.Nondegenerate T.polarBilin := by
      rw [binaryQuadratic_add_linear_polar]
      exact hP
    apply transport T hT
    · intro x
      simp only [T,QuadraticMap.add_apply,binaryLinearQuadratic_apply]
      change P (f x) + P.polarBilin (f x) v.val = q x
      rw [v.property (f x) ⟨x,rfl⟩,add_zero,hPf]
    · change binaryQuadraticGaussSum (P + binaryLinearQuadratic (P.polarBilin.flip v.val)) = _
      rw [binaryQuadratic_linear_shift_gauss,hv,pauliSign_one,hneg]
      ring

end ExactCriticalCurve.FiniteQuadratic
