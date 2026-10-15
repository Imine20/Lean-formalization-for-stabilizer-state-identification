import ExactCriticalCurve.FiniteQuadratic.AlternatingRealizability

/-! Even rank of actual binary alternating forms, derived from genuine
embeddings and orthogonal complements without an assumed classification. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem alternating_nondegenerate_finrank_ne_one
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate) :
    finrank (ZMod 2) V ≠ 1 := by
  intro hd
  obtain ⟨v, hv, hspan⟩ := finrank_eq_one_iff'.mp hd
  apply hv
  apply hBn v
  intro w
  obtain ⟨c, rfl⟩ := hspan w
  simp [map_smul, hB.self_eq_zero]

/-- Every nondegenerate binary alternating ambient has even dimension, including zero. -/
theorem alternating_nondegenerate_even_finrank
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate) :
    Even (finrank (ZMod 2) V) := by
  let d := finrank (ZMod 2) V
  let E := Fin (d / 2) → ZMod 2
  let A : LinearMap.BilinForm (ZMod 2) E := 0
  let H := E × Module.Dual (ZMod 2) (LinearMap.ker A)
  obtain ⟨C,hC,hCn,_⟩ := exists_alternating_nondegenerate_envelope A (fun _ => rfl)
  have hk : LinearMap.ker A = ⊤ := by
    apply top_unique
    intro x _
    rfl
  have hdimH : finrank (ZMod 2) H = 2 * (d / 2) := by
    have hkerdim := (LinearEquiv.ofTop (LinearMap.ker A) hk).finrank_eq
    change finrank (ZMod 2) (E × Module.Dual (ZMod 2) (LinearMap.ker A)) = _
    rw [Module.finrank_prod, Subspace.dual_finrank_eq, hkerdim]
    simp [E, two_mul]
  have hle : finrank (ZMod 2) H ≤ finrank (ZMod 2) V := by
    rw [hdimH]
    omega
  obtain ⟨f,hf,hfp⟩ := exists_nondegenerateAlternating_embedding C hC hCn B hB hBn hle
  let W := LinearMap.range f
  have hWn : (B.restrict W).Nondegenerate := by
    intro z hz
    obtain ⟨x,hx⟩ := z.property
    have hx0 : x = 0 := hCn x (fun y => by
      have hz' := hz ⟨f y,⟨y,rfl⟩⟩
      change B z.val (f y) = 0 at hz'
      rw [← hx,hfp] at hz'
      exact hz')
    apply Subtype.ext
    change z.val = 0
    rw [← hx,hx0,map_zero]
  have hcompl : IsCompl W (B.orthogonal W) :=
    B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hWn
  let T := B.orthogonal W
  have hTn : (B.restrict T).Nondegenerate := by
    apply B.nondegenerate_restrict_of_disjoint_orthogonal hB.isRefl
    change Disjoint (B.orthogonal W) (B.orthogonal (B.orthogonal W))
    rw [LinearMap.BilinForm.orthogonal_orthogonal hBn hB.isRefl W]
    exact hcompl.symm.disjoint
  have hTa : (B.restrict T).IsAlt := fun x => hB.self_eq_zero x.val
  have hdimW : finrank (ZMod 2) W = 2 * (d / 2) := by
    rw [LinearMap.finrank_range_of_inj hf]
    exact hdimH
  have hdim := Submodule.finrank_add_eq_of_isCompl hcompl
  change finrank (ZMod 2) W + finrank (ZMod 2) T = d at hdim
  have hne := alternating_nondegenerate_finrank_ne_one (B.restrict T) hTa hTn
  refine ⟨d / 2, ?_⟩
  omega

/-- The rank of an arbitrary actual alternating form is even, including degenerate forms. -/
theorem alternating_even_rank (A : LinearMap.BilinForm (ZMod 2) V) (hA : A.IsAlt) :
    Even (finrank (ZMod 2) (LinearMap.range A)) := by
  obtain ⟨C,hC,hCn,_⟩ := exists_alternating_nondegenerate_envelope A hA
  have he := alternating_nondegenerate_even_finrank C hC hCn
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at he
  obtain ⟨t,ht⟩ := he
  have hr := LinearMap.finrank_range_add_finrank_ker A
  refine ⟨t - finrank (ZMod 2) (LinearMap.ker A), ?_⟩
  omega

end ExactCriticalCurve.FiniteQuadratic
