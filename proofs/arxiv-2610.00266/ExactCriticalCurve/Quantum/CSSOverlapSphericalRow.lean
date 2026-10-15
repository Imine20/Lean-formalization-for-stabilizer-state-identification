import ExactCriticalCurve.Quantum.CSSOverlapLiftFiber

/-! # The actual spherical overlap row, indexed by paired defect flags

Only actual finite sets are reindexed. The lift-fiber multiplicity is proved by
its ambient-kernel bijection. The remaining intersection-family cardinalities
are genuine unevaluated counts, not assumed flag formulas.
-/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {k r : ℕ}

/-- All actual ambient isometries with nonzero full-support overlap. -/
abbrev CSSOverlapIsometry (N : Submodule (ZMod 2) (BinaryVector k)) :=
  {g : StochasticIsometryGroup k //
    ∀ x ∈ orthogonal N, g.val x-x ∈ N ⊔ stochasticSubspace g N}

/-- Actual ordinary target defects paired nondegenerately modulo their intersection. -/
abbrev CSSPairedOrdinaryDefect (N : OrdinaryDefect k r) :=
  {M : OrdinaryDefect k r //
    N.val ⊓ orthogonal M.val = N.val ⊓ M.val ∧
    M.val ⊓ orthogonal N.val = N.val ⊓ M.val}

/-- The complete fixed-intersection family of actual ordinary paired targets. -/
abbrev CSSIntersectionFamily (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) :=
  {M : OrdinaryDefect k r // N.val ⊓ M.val = K ∧
    N.val ⊓ orthogonal M.val = K ∧ M.val ⊓ orthogonal N.val = K}

/-- All actual subspaces of the source defect, represented in the ambient space. -/
abbrev CSSDefectIntersection (N : OrdinaryDefect k r) :=
  {K : Submodule (ZMod 2) (BinaryVector k) // K ≤ N.val}

instance cssDefectIntersectionFintype (N : OrdinaryDefect k r) :
    Fintype (CSSDefectIntersection N) := Fintype.ofFinite _

/-- Partition every good isometry by its actual target and retain every ambient lift. -/
def cssOverlapFiberDecomposition (N : OrdinaryDefect k r) :
    CSSOverlapIsometry N.val ≃
      Σ M : CSSPairedOrdinaryDefect N, ActualCSSOverlapFiber N.val M.val.val where
  toFun g := by
    let M : OrdinaryDefect k r := ⟨stochasticSubspace g.val N.val,
      stochasticSubspace_isDefect g.val N.property.1,
      (stochasticSubspace_finrank g.val N.val).trans N.property.2.1,
      fun h => N.property.2.2 ((allOnes_mem_stochasticSubspace g.val N.val).mp h)⟩
    exact ⟨⟨M,cssOverlap_pairingKernels N.val N.property.1 g.val g.property⟩,
      ⟨g.val,rfl,g.property⟩⟩
  invFun p := ⟨p.2.val, by
    rw [p.2.property.1]
    exact p.2.property.2⟩
  left_inv g := rfl
  right_inv p := by
    rcases p with ⟨⟨⟨M,hM⟩,hp⟩,⟨g,hg,hs⟩⟩
    dsimp at hg
    subst M
    rfl

/-- Exact weighted row before evaluating the actual paired-target count. -/
theorem cssOverlap_sum_by_target (N : OrdinaryDefect k r)
    (w : Submodule (ZMod 2) (BinaryVector k) → ℂ) :
    (∑ g : StochasticIsometryGroup k,
      if ∀ x ∈ orthogonal N.val, g.val x-x ∈ N.val ⊔ stochasticSubspace g N.val
      then w (stochasticSubspace g N.val) else 0) =
    (Nat.card (stochasticParabolicKernel N.val) : ℂ) *
      ∑ M : CSSPairedOrdinaryDefect N, w M.val.val := by
  letI (M : CSSPairedOrdinaryDefect N) : Fintype (ActualCSSOverlapFiber N.val M.val.val) := by
    unfold ActualCSSOverlapFiber
    infer_instance
  calc
    _ = ∑ g : CSSOverlapIsometry N.val, w (stochasticSubspace g.val N.val) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ p : (Σ M : CSSPairedOrdinaryDefect N, ActualCSSOverlapFiber N.val M.val.val),
        w p.1.val.val :=
      Fintype.sum_equiv (cssOverlapFiberDecomposition N) _ _ (fun _ => rfl)
    _ = ∑ M : CSSPairedOrdinaryDefect N,
        (Nat.card (ActualCSSOverlapFiber N.val M.val.val) : ℂ) * w M.val.val := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ = (Nat.card (stochasticParabolicKernel N.val) : ℂ) *
        ∑ M : CSSPairedOrdinaryDefect N, w M.val.val := by
      have hc (M : CSSPairedOrdinaryDefect N) :
          Nat.card (ActualCSSOverlapFiber N.val M.val.val) =
            Nat.card (stochasticParabolicKernel N.val) :=
        actualCSSOverlapFiber_card N.val M.val.val N.property.1 M.val.property.1
          M.property.1 M.property.2
      simp_rw [hc]
      exact (Finset.mul_sum _ _ _).symm

/-- The actual intersection as a subspace of the source. -/
def cssPairedIntersection (N : OrdinaryDefect k r) (M : CSSPairedOrdinaryDefect N) :
    CSSDefectIntersection N := ⟨N.val ⊓ M.val.val, inf_le_left⟩

/-- The fiber of the intersection map is the full literal fixed-K family. -/
def cssPairedIntersectionFiberEquiv (N : OrdinaryDefect k r) (K : CSSDefectIntersection N) :
    {M : CSSPairedOrdinaryDefect N // cssPairedIntersection N M = K} ≃
      CSSIntersectionFamily N K.val where
  toFun p := ⟨p.val.val, by
    have h := congrArg Subtype.val p.property
    exact ⟨h,p.val.property.1.trans h,p.val.property.2.trans h⟩⟩
  invFun M := ⟨⟨M.val,M.property.2.1.trans M.property.1.symm,
    M.property.2.2.trans M.property.1.symm⟩,Subtype.ext M.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex paired targets by their exact actual intersection, without assuming any count. -/
theorem cssPaired_sum_by_intersection (N : OrdinaryDefect k r)
    (w : CSSDefectIntersection N → ℂ) :
    (∑ M : CSSPairedOrdinaryDefect N, w (cssPairedIntersection N M)) =
      ∑ K : CSSDefectIntersection N, (Nat.card (CSSIntersectionFamily N K.val) : ℂ) * w K := by
  rw [← Fintype.sum_fiberwise' (cssPairedIntersection N) w]
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_congr (cssPairedIntersectionFiberEquiv N K)]

/-- The actual unnormalized spherical row, with all fixed-K counts still explicit. -/
theorem cssOverlap_spherical_row (n : ℕ) (N : OrdinaryDefect k r) :
    (∑ g : StochasticIsometryGroup k,
      if ∀ x ∈ orthogonal N.val, g.val x-x ∈ N.val ⊔ stochasticSubspace g N.val
      then (((2 : ℂ)^n)^(finrank (ZMod 2) N.val -
        finrank (ZMod 2) ↥(N.val ⊓ stochasticSubspace g N.val)))⁻¹ else 0) =
    (Nat.card (stochasticParabolicKernel N.val) : ℂ) *
      ∑ K : CSSDefectIntersection N,
        (Nat.card (CSSIntersectionFamily N K.val) : ℂ) *
          (((2 : ℂ)^n)^(r-finrank (ZMod 2) K.val))⁻¹ := by
  rw [cssOverlap_sum_by_target N (fun M =>
    (((2 : ℂ)^n)^(finrank (ZMod 2) N.val-finrank (ZMod 2) ↥(N.val ⊓ M)))⁻¹)]
  congr 1
  have h := cssPaired_sum_by_intersection N
    (fun K => (((2 : ℂ)^n)^(r-finrank (ZMod 2) K.val))⁻¹)
  simpa only [N.property.2.1, cssPairedIntersection] using h

/-- The actual codimension, with the full bound 0 ≤ ell ≤ r in its type. -/
def cssIntersectionCodimension (N : OrdinaryDefect k r) (K : CSSDefectIntersection N) :
    Fin (r+1) := ⟨r-finrank (ZMod 2) K.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

/-- On actual subspaces of N, truncated subtraction is exactly rank plus codimension. -/
theorem cssIntersectionCodimension_eq_iff (N : OrdinaryDefect k r)
    (K : CSSDefectIntersection N) (ell : Fin (r+1)) :
    cssIntersectionCodimension N K = ell ↔ finrank (ZMod 2) K.val + ell.val = r := by
  have hk : finrank (ZMod 2) K.val ≤ r :=
    (Submodule.finrank_mono K.property).trans_eq N.property.2.1
  rw [Fin.ext_iff]
  change r-finrank (ZMod 2) K.val = ell.val ↔ _
  omega

/-- The full feasible fixed-codimension intersection family. -/
abbrev CSSIntersectionsAtCodimension (N : OrdinaryDefect k r) (ell : Fin (r+1)) :=
  {K : CSSDefectIntersection N // finrank (ZMod 2) K.val + ell.val = r}

/-- Exact identification of the codimension map fiber with the feasible family. -/
def cssIntersectionCodimensionFiberEquiv (N : OrdinaryDefect k r) (ell : Fin (r+1)) :
    {K : CSSDefectIntersection N // cssIntersectionCodimension N K = ell} ≃
      CSSIntersectionsAtCodimension N ell where
  toFun K := ⟨K.val,(cssIntersectionCodimension_eq_iff N K.val ell).mp K.property⟩
  invFun K := ⟨K.val,(cssIntersectionCodimension_eq_iff N K.val ell).mpr K.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Group arbitrary actual intersection coefficients by their feasible codimension. -/
theorem cssIntersection_sum_by_codimension (n : ℕ) (N : OrdinaryDefect k r)
    (a : CSSDefectIntersection N → ℂ) :
    (∑ K : CSSDefectIntersection N, a K * (((2 : ℂ)^n)^(r-finrank (ZMod 2) K.val))⁻¹) =
      ∑ ell : Fin (r+1),
        (∑ K : CSSIntersectionsAtCodimension N ell, a K.val) * (((2 : ℂ)^n)^ell.val)⁻¹ := by
  rw [← Fintype.sum_fiberwise (cssIntersectionCodimension N)
    (fun K => a K * (((2 : ℂ)^n)^(r-finrank (ZMod 2) K.val))⁻¹)]
  apply Finset.sum_congr rfl
  intro ell _
  calc
    _ = ∑ K : CSSIntersectionsAtCodimension N ell, a K.val * (((2 : ℂ)^n)^ell.val)⁻¹ := by
      apply Fintype.sum_equiv (cssIntersectionCodimensionFiberEquiv N ell)
      intro K
      have hd : r-finrank (ZMod 2) K.val.val = ell.val := congrArg Fin.val K.property
      change a K.val * (((2 : ℂ)^n)^(r-finrank (ZMod 2) K.val.val))⁻¹ =
        a K.val * (((2 : ℂ)^n)^ell.val)⁻¹
      rw [hd]
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The actual spherical row stratified by all feasible ell, with literal flag counts. -/
theorem cssOverlap_spherical_row_codimension (n : ℕ) (N : OrdinaryDefect k r) :
    (∑ g : StochasticIsometryGroup k,
      if ∀ x ∈ orthogonal N.val, g.val x-x ∈ N.val ⊔ stochasticSubspace g N.val
      then (((2 : ℂ)^n)^(finrank (ZMod 2) N.val -
        finrank (ZMod 2) ↥(N.val ⊓ stochasticSubspace g N.val)))⁻¹ else 0) =
    (Nat.card (stochasticParabolicKernel N.val) : ℂ) *
      ∑ ell : Fin (r+1),
        (∑ K : CSSIntersectionsAtCodimension N ell,
          (Nat.card (CSSIntersectionFamily N K.val.val) : ℂ)) * (((2 : ℂ)^n)^ell.val)⁻¹ := by
  rw [cssOverlap_spherical_row]
  congr 1
  exact cssIntersection_sum_by_codimension n N
    (fun K => (Nat.card (CSSIntersectionFamily N K.val) : ℂ))

end ExactCriticalCurve.Quantum
