import ExactCriticalCurve.FiniteQuadratic.OrdinarySingularGraphs
import ExactCriticalCurve.Quantum.CSSQuotientGeometry

/-! Actual quotient correspondence for paired defect flags. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic
variable {k : ℕ}

/-- The existing genuine CSS quotient, equipped with its full mod-four geometry. -/
def cssFlagQuotientGeometry (K : Submodule (ZMod 2) (BinaryVector k)) (hK : IsDefect K) :
    ModFourQuadraticSpace (CSSQuotient K) where
  pairing := cssQuotientBilinear K
  quadratic := cssQuotientQuadratic K hK
  quadratic_zero := cssQuotientQuadratic_zero K hK
  quadratic_add := cssQuotientQuadratic_add K hK
  symmetric := ⟨cssQuotientBilinear_symm K⟩
  nondegenerate := cssQuotientBilinear_nondegenerate K
  wu := cssQuotientWu K hK
  characteristic x := (cssQuotientWu_characteristic K hK x).trans (cssQuotientBilinear_symm K _ _)

def cssFlagImage (K M : Submodule (ZMod 2) (BinaryVector k)) :
    Submodule (ZMod 2) (CSSQuotient K) :=
  (M.comap (orthogonal K).subtype).map (K.comap (orthogonal K).subtype).mkQ

def cssFlagPreimage (K : Submodule (ZMod 2) (BinaryVector k))
    (Q : Submodule (ZMod 2) (CSSQuotient K)) :
    Submodule (ZMod 2) (BinaryVector k) :=
  (Q.comap (K.comap (orthogonal K).subtype).mkQ).map (orthogonal K).subtype

theorem cssFlagPreimage_image (K M : Submodule (ZMod 2) (BinaryVector k))
    (hKM : K≤M) (hMP : M≤orthogonal K) :
    cssFlagPreimage K (cssFlagImage K M)=M := by
  unfold cssFlagPreimage cssFlagImage
  rw [Submodule.comap_map_mkQ]
  have h : K.comap (orthogonal K).subtype≤M.comap (orthogonal K).subtype := fun _ hx => hKM hx
  rw [sup_eq_right.mpr h,Submodule.map_comap_subtype,inf_eq_right.mpr hMP]

theorem cssFlagImage_preimage (K : Submodule (ZMod 2) (BinaryVector k))
    (Q : Submodule (ZMod 2) (CSSQuotient K)) :
    cssFlagImage K (cssFlagPreimage K Q)=Q := by
  unfold cssFlagImage cssFlagPreimage
  rw [Submodule.comap_map_eq_of_injective (orthogonal K).injective_subtype]
  exact Submodule.map_comap_eq_self (by simp)

theorem cssFlagPreimage_le_orthogonal (K : Submodule (ZMod 2) (BinaryVector k))
    (Q : Submodule (ZMod 2) (CSSQuotient K)) :
    cssFlagPreimage K Q≤orthogonal K := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

theorem le_cssFlagPreimage (K : Submodule (ZMod 2) (BinaryVector k)) (hK : IsDefect K)
    (Q : Submodule (ZMod 2) (CSSQuotient K)) : K≤cssFlagPreimage K Q := by
  intro x hx
  refine ⟨⟨x,hK.le_orthogonal hx⟩,?_,rfl⟩
  change (K.comap (orthogonal K).subtype).mkQ _ ∈ Q
  have hz : (K.comap (orthogonal K).subtype).mkQ ⟨x,hK.le_orthogonal hx⟩=0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  rw [hz]
  exact Q.zero_mem

theorem cssFlagImage_singular (K M : Submodule (ZMod 2) (BinaryVector k))
    (hK : IsDefect K) (hM : IsDefect M) :
    (cssFlagQuotientGeometry K hK).IsSingular (cssFlagImage K M) := by
  rintro z ⟨x,hx,rfl⟩
  exact hM _ hx

theorem cssFlagPreimage_isDefect (K : Submodule (ZMod 2) (BinaryVector k)) (hK : IsDefect K)
    (Q : Submodule (ZMod 2) (CSSQuotient K))
    (hQ : (cssFlagQuotientGeometry K hK).IsSingular Q) :
    IsDefect (cssFlagPreimage K Q) := by
  rintro x ⟨y,hy,rfl⟩
  exact hQ _ hy

theorem cssFlagImage_finrank_add (K M : Submodule (ZMod 2) (BinaryVector k))
    (hK : IsDefect K) (hKM : K≤M) (hMP : M≤orthogonal K) :
    finrank (ZMod 2) (cssFlagImage K M)+finrank (ZMod 2) K=finrank (ZMod 2) M := by
  let A := M.comap (orthogonal K).subtype
  let p := K.comap (orthogonal K).subtype
  have hpA : p≤A := fun _ hx => hKM hx
  have hker : LinearMap.ker (p.mkQ.domRestrict A)=p.comap A.subtype := by
    ext x
    simp
  have hr := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2)
    (V := A) (V₂ := CSSQuotient K) (p.mkQ.domRestrict A)
  rw [LinearMap.range_domRestrict,hker,(Submodule.comapSubtypeEquivOfLe hpA).finrank_eq] at hr
  have hp : finrank (ZMod 2) p=finrank (ZMod 2) K :=
    (Submodule.comapSubtypeEquivOfLe hK.le_orthogonal).finrank_eq
  have ha : finrank (ZMod 2) A=finrank (ZMod 2) M :=
    (Submodule.comapSubtypeEquivOfLe hMP).finrank_eq
  change finrank (ZMod 2) (cssFlagImage K M)+finrank (ZMod 2) p=finrank (ZMod 2) A at hr
  rwa [hp,ha] at hr

theorem cssFlagPreimage_finrank (K : Submodule (ZMod 2) (BinaryVector k)) (hK : IsDefect K)
    (Q : Submodule (ZMod 2) (CSSQuotient K)) :
    finrank (ZMod 2) (cssFlagPreimage K Q)=finrank (ZMod 2) Q+finrank (ZMod 2) K := by
  have h := cssFlagImage_finrank_add K (cssFlagPreimage K Q) hK
    (le_cssFlagPreimage K hK Q) (cssFlagPreimage_le_orthogonal K Q)
  rw [cssFlagImage_preimage] at h
  exact h.symm

theorem mem_cssFlagImage_mk_iff (K M : Submodule (ZMod 2) (BinaryVector k))
    (hKM : K≤M) (x : orthogonal K) :
    (Submodule.Quotient.mk x : CSSQuotient K) ∈ cssFlagImage K M ↔ x.val∈M := by
  change x∈((M.comap (orthogonal K).subtype).map
    (K.comap (orthogonal K).subtype).mkQ).comap (K.comap (orthogonal K).subtype).mkQ ↔ _
  rw [Submodule.comap_map_mkQ,sup_eq_right.mpr (show
    K.comap (orthogonal K).subtype≤M.comap (orthogonal K).subtype from fun _ hx => hKM hx)]
  rfl

theorem mem_cssFlagPreimage_iff (K : Submodule (ZMod 2) (BinaryVector k))
    (Q : Submodule (ZMod 2) (CSSQuotient K)) (x : orthogonal K) :
    x.val∈cssFlagPreimage K Q ↔ (Submodule.Quotient.mk x : CSSQuotient K)∈Q := by
  constructor
  · rintro ⟨y,hy,he⟩
    have hxy : y=x := Subtype.ext he
    simpa [hxy] using hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem cssFlagImage_wu_not_mem (K M : Submodule (ZMod 2) (BinaryVector k))
    (hK : IsDefect K) (hKM : K≤M) (hw : allOnes k∉M) :
    (cssFlagQuotientGeometry K hK).wu∉cssFlagImage K M := by
  intro h
  exact hw ((mem_cssFlagImage_mk_iff K M hKM
    ⟨allOnes k,hK.allOnes_mem_orthogonal⟩).mp h)

theorem cssFlagImage_pairing_zero_iff (K M : Submodule (ZMod 2) (BinaryVector k))
    (hMP : M≤orthogonal K) (x : orthogonal K) :
    (∀ u∈cssFlagImage K M,cssQuotientBilinear K u (Submodule.Quotient.mk x)=0) ↔
      x.val∈orthogonal M := by
  constructor
  · intro h y hy
    exact h (Submodule.Quotient.mk (⟨y,hMP hy⟩ : orthogonal K)) ⟨⟨y,hMP hy⟩,hy,rfl⟩
  · intro h u hu
    obtain ⟨y,hy,rfl⟩ := hu
    exact h _ hy

/-- The literal actual family used in the physical spherical row: all three
intersections are equal to the specified subspace. -/
def PairedDefectFamily {r : ℕ} (N : OrdinaryDefect k r)
    (K : Submodule (ZMod 2) (BinaryVector k)) :=
  {M : OrdinaryDefect k r // N.val⊓M.val=K ∧
    N.val⊓orthogonal M.val=K ∧ M.val⊓orthogonal N.val=K}

theorem cssFlagImage_right_radical_iff
    (K N M : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hKN : K≤N) (hKM : K≤M)
    (hNP : N≤orthogonal K) (hMP : M≤orthogonal K) :
    (∀ x∈cssFlagImage K M,
      (∀ u∈cssFlagImage K N,cssQuotientBilinear K u x=0)→x=0) ↔
      M⊓orthogonal N=K := by
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      have hz : (Submodule.Quotient.mk (⟨x,hMP hx.1⟩ : orthogonal K) : CSSQuotient K)=0 :=
        h _ ⟨⟨x,hMP hx.1⟩,hx.1,rfl⟩
          ((cssFlagImage_pairing_zero_iff K N hNP ⟨x,hMP hx.1⟩).mpr hx.2)
      exact (Submodule.Quotient.mk_eq_zero (K.comap (orthogonal K).subtype)).mp hz
    · intro x hx
      exact ⟨hKM hx,hN.le_orthogonal (hKN hx)⟩
  · intro h z hz hp
    obtain ⟨x,hx,rfl⟩ := hz
    have hxN : x.val∈orthogonal N :=
      (cssFlagImage_pairing_zero_iff K N hNP x).mp hp
    have hxK : x.val∈K := h ▸ (show x.val∈M⊓orthogonal N from ⟨hx,hxN⟩)
    exact (Submodule.Quotient.mk_eq_zero _).mpr hxK

theorem cssFlagImage_opposite_iff
    (K N M : Submodule (ZMod 2) (BinaryVector k))
    (hK : IsDefect K) (hN : IsDefect N) (hKN : K≤N) (hKM : K≤M)
    (hNP : N≤orthogonal K) (hMP : M≤orthogonal K) :
    let D := cssFlagQuotientGeometry K hK
    let b := Module.finBasis (ZMod 2) (cssFlagImage K N)
    (D.IsSingular (cssFlagImage K M) ∧
      Function.Bijective ((D.primalPair (cssFlagImage K N) b).domRestrict (cssFlagImage K M))) ↔
      IsDefect M ∧ finrank (ZMod 2) M=finrank (ZMod 2) N ∧ M⊓orthogonal N=K := by
  dsimp only
  rw [(cssFlagQuotientGeometry K hK).mem_singularOpposite_iff]
  have hMd := cssFlagImage_finrank_add K M hK hKM hMP
  have hNd := cssFlagImage_finrank_add K N hK hKN hNP
  constructor
  · rintro ⟨hQ,hd,hr⟩
    refine ⟨?_,by omega,?_⟩
    · intro x hx
      exact hQ _ ⟨⟨x,hMP hx⟩,hx,rfl⟩
    · exact (cssFlagImage_right_radical_iff K N M hN hKN hKM hNP hMP).mp hr
  · rintro ⟨hM,hd,hr⟩
    exact ⟨cssFlagImage_singular K M hK hM,by omega,
      (cssFlagImage_right_radical_iff K N M hN hKN hKM hNP hMP).mpr hr⟩

theorem cssFlagPreimage_left_intersection
    (K N : Submodule (ZMod 2) (BinaryVector k))
    (hK : IsDefect K) (hN : IsDefect N) (hKN : K≤N) (hNP : N≤orthogonal K)
    (Q : (cssFlagQuotientGeometry K hK).SingularOpposite (cssFlagImage K N)
      (Module.finBasis (ZMod 2) (cssFlagImage K N))) :
    N⊓orthogonal (cssFlagPreimage K Q.val)=K := by
  apply le_antisymm
  · intro x hx
    have hz : (Submodule.Quotient.mk (⟨x,hNP hx.1⟩ : orthogonal K) : CSSQuotient K)=0 := by
      apply (cssFlagQuotientGeometry K hK).singularOpposite_left_nondegenerate
        (cssFlagImage K N) (Module.finBasis (ZMod 2) (cssFlagImage K N)) Q
        (show (Submodule.Quotient.mk (⟨x,hNP hx.1⟩ : orthogonal K) : CSSQuotient K)∈cssFlagImage K N
          from ⟨⟨x,hNP hx.1⟩,hx.1,rfl⟩)
      intro u hu
      have hu' : u∈cssFlagImage K (cssFlagPreimage K Q.val) := by rwa [cssFlagImage_preimage]
      obtain ⟨y,hy,rfl⟩ := hu'
      exact (binaryDot_comm x y.val).trans (hx.2 _ hy)
    exact (Submodule.Quotient.mk_eq_zero (K.comap (orthogonal K).subtype)).mp hz
  · intro x hx
    refine ⟨hKN hx,?_⟩
    intro y hy
    exact (binaryDot_comm y x).trans (cssFlagPreimage_le_orthogonal K Q.val hy x hx)


end ExactCriticalCurve.Quantum
