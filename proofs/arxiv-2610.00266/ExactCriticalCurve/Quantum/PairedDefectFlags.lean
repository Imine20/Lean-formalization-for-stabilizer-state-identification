import ExactCriticalCurve.Quantum.PairedDefectQuotient

/-! Exact cardinality and genuine graph parametrization of actual paired defect flags. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic
variable {k r : ℕ}

theorem pairedFlagKernel_isDefect (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) : IsDefect K :=
  fun x hx => N.property.1 x (hKN hx)

theorem pairedFlagSource_le_orthogonal (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) : N.val≤orthogonal K := by
  intro x hx y hy
  exact N.property.1.binaryDot_eq_zero (hKN hy) hx

abbrev PairedFlagOpposite (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) :=
  (cssFlagQuotientGeometry K (pairedFlagKernel_isDefect N K hKN)).SingularOpposite
    (cssFlagImage K N.val) (Module.finBasis (ZMod 2) (cssFlagImage K N.val))

def pairedFlagImage (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val)
    (M : PairedDefectFamily N K) : PairedFlagOpposite N K hKN := by
  have hKM : K≤M.val.val := M.property.1.symm.le.trans inf_le_right
  have hMP : M.val.val≤orthogonal K := by
    intro x hx y hy
    exact M.val.property.1.binaryDot_eq_zero (hKM hy) hx
  refine ⟨cssFlagImage K M.val.val,?_⟩
  apply (cssFlagImage_opposite_iff K N.val M.val.val (pairedFlagKernel_isDefect N K hKN)
    N.property.1 hKN hKM (pairedFlagSource_le_orthogonal N K hKN) hMP).mpr
  exact ⟨M.val.property.1,M.val.property.2.1.trans N.property.2.1.symm,M.property.2.2⟩

def pairedFlagPreimage (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val)
    (Q : PairedFlagOpposite N K hKN) : PairedDefectFamily N K := by
  let hK := pairedFlagKernel_isDefect N K hKN
  let D := cssFlagQuotientGeometry K hK
  let b := Module.finBasis (ZMod 2) (cssFlagImage K N.val)
  let M := cssFlagPreimage K Q.val
  have hKM : K≤M := le_cssFlagPreimage K hK Q.val
  have hMP : M≤orthogonal K := cssFlagPreimage_le_orthogonal K Q.val
  have hNP := pairedFlagSource_le_orthogonal N K hKN
  have hspec : IsDefect M ∧ finrank (ZMod 2) M=finrank (ZMod 2) N.val ∧
      M⊓orthogonal N.val=K := by
    apply (cssFlagImage_opposite_iff K N.val M hK N.property.1 hKN hKM hNP hMP).mp
    change D.IsSingular (cssFlagImage K (cssFlagPreimage K Q.val)) ∧
      Function.Bijective ((D.primalPair (cssFlagImage K N.val) b).domRestrict
        (cssFlagImage K (cssFlagPreimage K Q.val)))
    rw [cssFlagImage_preimage]
    exact Q.property
  have hwQ : D.wu∉Q.val := D.singularOpposite_wu_not_mem
    (cssFlagImage K N.val) (cssFlagImage_singular K N.val hK N.property.1) b Q
    (cssFlagImage_wu_not_mem K N.val hK hKN N.property.2.2)
  have hwM : allOnes k∉M := by
    intro h
    exact hwQ ((mem_cssFlagPreimage_iff K Q.val
      ⟨allOnes k,hK.allOnes_mem_orthogonal⟩).mp h)
  have hi : N.val⊓M=K := by
    apply le_antisymm
    · intro x hx
      exact hspec.2.2 ▸ (show x∈M⊓orthogonal N.val from ⟨hx.2,N.property.1.le_orthogonal hx.1⟩)
    · exact le_inf hKN hKM
  refine ⟨⟨M,hspec.1,hspec.2.1.trans N.property.2.1,hwM⟩,hi,?_,hspec.2.2⟩
  exact cssFlagPreimage_left_intersection K N.val hK N.property.1 hKN hNP Q

/-- An explicit actual-subspace quotient correspondence, not a cardinality comparison. -/
def pairedDefectFamilyOppositeEquiv (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) :
    PairedDefectFamily N K ≃ PairedFlagOpposite N K hKN where
  toFun := pairedFlagImage N K hKN
  invFun := pairedFlagPreimage N K hKN
  left_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    change cssFlagPreimage K (cssFlagImage K M.val.val)=M.val.val
    have hKM : K≤M.val.val := M.property.1.symm.le.trans inf_le_right
    apply cssFlagPreimage_image K M.val.val hKM
    intro x hx y hy
    exact M.val.property.1.binaryDot_eq_zero (hKM hy) hx
  right_inv Q := by
    apply Subtype.ext
    exact cssFlagImage_preimage K Q.val

/-- The full graph bijection for the literal family with its three actual intersections. -/
def pairedDefectFamilyGraphEquiv (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) :
    let D := cssFlagQuotientGeometry K (pairedFlagKernel_isDefect N K hKN)
    let U := cssFlagImage K N.val
    let b := Module.finBasis (ZMod 2) U
    PairedDefectFamily N K ≃
      ((Fin (finrank (ZMod 2) U) → ZMod 2) →ₗ[ZMod 2]
        D.CoreEven U (cssFlagImage_singular K N.val _ N.property.1)
          (cssFlagImage_wu_not_mem K N.val _ hKN N.property.2.2) b) ×
      {B : LinearMap.BilinForm (ZMod 2) (Fin (finrank (ZMod 2) U) → ZMod 2) // B.IsAlt} :=
  (pairedDefectFamilyOppositeEquiv N K hKN).trans
    (((cssFlagQuotientGeometry K (pairedFlagKernel_isDefect N K hKN)).singularSectionOppositeEquiv
      (cssFlagImage K N.val) (Module.finBasis (ZMod 2) (cssFlagImage K N.val))).symm.trans
      ((cssFlagQuotientGeometry K (pairedFlagKernel_isDefect N K hKN)).singularSectionEquiv
        (cssFlagImage K N.val) (cssFlagImage_singular K N.val _ N.property.1)
        (cssFlagImage_wu_not_mem K N.val _ hKN N.property.2.2)
        (Module.finBasis (ZMod 2) (cssFlagImage K N.val))))

theorem pairedDefectFamily_card_add (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) (ell : ℕ)
    (hcodim : finrank (ZMod 2) K+ell=r) :
    Nat.card (PairedDefectFamily N K)=2^(ell*(k-2*r-1)+ell.choose 2) := by
  let hK := pairedFlagKernel_isDefect N K hKN
  let D := cssFlagQuotientGeometry K hK
  let U := cssFlagImage K N.val
  let b := Module.finBasis (ZMod 2) U
  have hd := cssFlagImage_finrank_add K N.val hK hKN (pairedFlagSource_le_orthogonal N K hKN)
  rw [N.property.2.1] at hd
  have hdim : finrank (ZMod 2) U=ell := by dsimp only [U]; omega
  have hambient := cssQuotient_finrank_add K hK
  have he : finrank (ZMod 2) (CSSQuotient K)-2*ell-1=k-2*r-1 := by omega
  rw [Nat.card_congr (pairedDefectFamilyOppositeEquiv N K hKN)]
  change Nat.card (D.SingularOpposite U b)=_
  rw [D.singularOpposite_card U (cssFlagImage_singular K N.val hK N.property.1)
    (cssFlagImage_wu_not_mem K N.val hK hKN N.property.2.2) b,hdim,he]

/-- Exact codimension formulation; the genuine subspace inclusion supplies the rank bound. -/
theorem pairedDefectFamily_card (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) (ell : ℕ)
    (hcodim : r-finrank (ZMod 2) K=ell) :
    Nat.card (PairedDefectFamily N K)=2^(ell*(k-2*r-1)+ell.choose 2) := by
  apply pairedDefectFamily_card_add N K hKN ell
  have hle := Submodule.finrank_mono hKN
  rw [N.property.2.1] at hle
  omega

theorem pairedDefectFamily_card_codim_zero (N : OrdinaryDefect k r) :
    Nat.card (PairedDefectFamily N N.val)=1 := by
  have h := pairedDefectFamily_card N N.val le_rfl 0 (by rw [N.property.2.1,Nat.sub_self])
  simpa using h

theorem pairedDefectFamily_card_quotient_one (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) (ell : ℕ)
    (hcodim : r-finrank (ZMod 2) K=ell) (hs : k-2*r=1) :
    Nat.card (PairedDefectFamily N K)=2^ell.choose 2 := by
  rw [pairedDefectFamily_card N K hKN ell hcodim,hs]
  simp

/-- Literal downstream interface, with no family alias hiding any membership condition. -/
theorem pairedDefectFlags_card_literal (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) (hKN : K≤N.val) (ell : ℕ)
    (hcodim : r-finrank (ZMod 2) K=ell) :
    Nat.card {M : OrdinaryDefect k r // N.val⊓M.val=K ∧
      N.val⊓orthogonal M.val=K ∧ M.val⊓orthogonal N.val=K} =
      2^(ell*(k-2*r-1)+ell.choose 2) :=
  pairedDefectFamily_card N K hKN ell hcodim


end ExactCriticalCurve.Quantum
