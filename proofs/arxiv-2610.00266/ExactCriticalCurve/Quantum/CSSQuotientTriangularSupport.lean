import ExactCriticalCurve.Quantum.CSSQuotientTupleOrbits
import ExactCriticalCurve.Quantum.CSSQuotientFixedAction
import ExactCriticalCurve.Quantum.CSSStableWitness

/-! Nonzero actual CSS synthesis coefficients satisfy a genuine rank/Wu order. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators ComplexOrder
namespace ExactCriticalCurve.Quantum
open Binary
set_option maxHeartbeats 3000000
variable {n k r : ℕ}

def cssQuotientSection (N : Submodule (ZMod 2) (BinaryVector k))
    (t : (CSSQuotient N × N.comap (orthogonal N).subtype) ≃ₗ[ZMod 2] orthogonal N) :
    CSSQuotient N →ₗ[ZMod 2] orthogonal N :=
  t.toLinearMap.comp (LinearMap.inl (ZMod 2) (CSSQuotient N) (N.comap (orthogonal N).subtype))

def cssSectionConfig (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (t : (CSSQuotient N × N.comap (orthogonal N).subtype) ≃ₗ[ZMod 2] orthogonal N)
    (f : CSSHom n N) : ColumnConfig n k :=
  homColumnsEquiv n (BinaryVector k)
    ((orthogonal N).subtype.comp ((cssQuotientSection N t).comp f))

theorem configurationLinearMap_stochastic (g : StochasticIsometryGroup k)
    (X : ColumnConfig n k) :
    configurationLinearMap ((stochasticColumnPerm n g).symm X) =
      g.val.symm.toLinearMap.comp (configurationLinearMap X) := by
  apply (homColumnsEquiv n (BinaryVector k)).injective
  rw [configurationLinearMap, LinearEquiv.apply_symm_apply, homColumnsEquiv_comp]
  funext a
  rw [homColumnsEquiv_apply,configurationLinearMap_single]
  rfl

theorem cssHomSynthesis_support_all (N : Submodule (ZMod 2) (BinaryVector k))
    (h : CSSHom n N) (X : ColumnConfig n k) (hx : cssHomSynthesis n N X h ≠ 0)
    (x : BinaryVector n) :
    cosetMember (orthogonal N) N (configurationLinearMap X x) (h x) := by
  have hs := cssHomSynthesis_support N h X hx
  let F := configurationInOrthogonal N X (fun a => (hs a).choose)
  have he : (N.comap (orthogonal N).subtype).mkQ.comp F=h := by
    apply (cssHom_coset_condition_iff_comp n N F h).mp
    intro a
    simpa only [F,configurationInOrthogonal_val,configurationLinearMap_single] using hs a
  exact ⟨(F x).property,LinearMap.congr_fun he x⟩

def cssHomOrder (N : OrdinaryDefect k r) (f : CSSHom n N.val) : ℕ :=
  2 * finrank (ZMod 2) (LinearMap.range f) +
    if cssQuotientWu N.val N.property.1 ∈ LinearMap.range f then 0 else 1

theorem cssSection_support_constraints (N : OrdinaryDefect k r)
    (t : (CSSQuotient N.val × N.val.comap (orthogonal N.val).subtype) ≃ₗ[ZMod 2] orthogonal N.val)
    (ht : ∀ q a, (Submodule.Quotient.mk (t (q,a)) : CSSQuotient N.val)=q)
    (htw : t (cssQuotientWu N.val N.property.1,0)=
      ⟨allOnes k,N.property.1.allOnes_mem_orthogonal⟩)
    (f h : CSSHom n N.val) (g : StochasticIsometryGroup k)
    (hs : cssHomSynthesis n N.val
      ((stochasticColumnPerm n g).symm (cssSectionConfig n N.val t f)) h ≠ 0) :
    LinearMap.ker f ≤ LinearMap.ker h ∧
    (∀ x, cssQuotientQuadratic N.val N.property.1 (h x)=
      cssQuotientQuadratic N.val N.property.1 (f x)) ∧
    (∀ x, f x=cssQuotientWu N.val N.property.1 → h x=cssQuotientWu N.val N.property.1) := by
  have hc (x : BinaryVector n) :
      cosetMember (orthogonal N.val) N.val
        (g.val.symm (t (f x,0)).val) (h x) := by
    have he := cssHomSynthesis_support_all N.val h _ hs x
    rw [configurationLinearMap_stochastic] at he
    simpa only [cssSectionConfig,configurationLinearMap,LinearEquiv.symm_apply_apply,
      LinearMap.comp_apply,cssQuotientSection,LinearMap.inl_apply,LinearEquiv.coe_coe,
      Submodule.subtype_apply] using he
  refine ⟨?_,?_,?_⟩
  · intro x hx
    change f x=0 at hx
    change h x=0
    obtain ⟨hm,hq⟩ := hc x
    have hz : g.val.symm (t (f x,0)).val=0 := by
      simp only [hx, show (0,0)=(0 : CSSQuotient N.val ×
        N.val.comap (orthogonal N.val).subtype) from rfl, map_zero, Submodule.coe_zero]
    have he : (⟨g.val.symm (t (f x,0)).val,hm⟩ : orthogonal N.val)=0 := Subtype.ext hz
    rw [he] at hq
    exact hq.symm
  · intro x
    obtain ⟨hm,hq⟩ := hc x
    rw [← hq]
    change weightQuadratic (g.val.symm (t (f x,0)).val)=
      cssQuotientQuadratic N.val N.property.1 (f x)
    have hg : weightQuadratic (g.val.symm (t (f x,0)).val)=weightQuadratic (t (f x,0)).val :=
      stochasticIsometry_weight g⁻¹ _
    have hh := congrArg (cssQuotientQuadratic N.val N.property.1) (ht (f x) 0)
    exact hg.trans hh
  · intro x hx
    obtain ⟨hm,hq⟩ := hc x
    have hg : g.val.symm (t (f x,0)).val=allOnes k := by
      rw [hx,htw]
      exact stochasticIsometry_allOnes g⁻¹
    have he : (⟨g.val.symm (t (f x,0)).val,hm⟩ : orthogonal N.val)=
      ⟨allOnes k,N.property.1.allOnes_mem_orthogonal⟩ := Subtype.ext hg
    rw [he] at hq
    exact hq.symm

theorem cssSection_support_order (N : OrdinaryDefect k r)
    (t : (CSSQuotient N.val × N.val.comap (orthogonal N.val).subtype) ≃ₗ[ZMod 2] orthogonal N.val)
    (ht : ∀ q a, (Submodule.Quotient.mk (t (q,a)) : CSSQuotient N.val)=q)
    (htw : t (cssQuotientWu N.val N.property.1,0)=
      ⟨allOnes k,N.property.1.allOnes_mem_orthogonal⟩)
    (f h : CSSHom n N.val) (g : StochasticIsometryGroup k)
    (hs : cssHomSynthesis n N.val
      ((stochasticColumnPerm n g).symm (cssSectionConfig n N.val t f)) h ≠ 0) :
    cssHomOrder N h ≤ cssHomOrder N f ∧
      (cssHomOrder N h=cssHomOrder N f →
        ∃ u : CSSQuotientIsometryGroup N.val N.property.1, u.val.toLinearMap.comp f=h) := by
  obtain ⟨hker,hq,hpoint⟩ := cssSection_support_constraints N t ht htw f h g hs
  have hfk := f.finrank_range_add_finrank_ker
  have hhk := h.finrank_range_add_finrank_ker
  have hdimker := Submodule.finrank_mono hker
  have hr : finrank (ZMod 2) (LinearMap.range h) ≤ finrank (ZMod 2) (LinearMap.range f) := by omega
  have hw : cssQuotientWu N.val N.property.1 ∈ LinearMap.range f →
      cssQuotientWu N.val N.property.1 ∈ LinearMap.range h := by
    rintro ⟨x,hx⟩
    exact ⟨x,hpoint x hx⟩
  have hord : cssHomOrder N h ≤ cssHomOrder N f := by
    unfold cssHomOrder
    split_ifs <;> first | omega | exact False.elim (by aesop)
  refine ⟨hord,?_⟩
  intro he
  have hdim : finrank (ZMod 2) (LinearMap.range f)=finrank (ZMod 2) (LinearMap.range h) := by
    unfold cssHomOrder at he
    split_ifs at he <;> omega
  have hwi : cssQuotientWu N.val N.property.1 ∈ LinearMap.range f ↔
      cssQuotientWu N.val N.property.1 ∈ LinearMap.range h := by
    unfold cssHomOrder at he
    rw [hdim] at he
    split_ifs at he <;> aesop
  have hk : LinearMap.ker f=LinearMap.ker h := by
    apply Submodule.eq_of_le_of_finrank_le hker
    omega
  exact ordinaryCSSQuotient_tuple_isometry N f h hk hq hwi hpoint

end ExactCriticalCurve.Quantum

