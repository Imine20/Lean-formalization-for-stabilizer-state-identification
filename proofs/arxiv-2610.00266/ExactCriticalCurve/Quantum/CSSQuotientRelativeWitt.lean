import ExactCriticalCurve.Quantum.CSSQuotientIsometryGroup

/-! Actual relative Witt extension on an ordinary CSS quotient. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary
set_option maxHeartbeats 10000000
variable {k r : ℕ}

/-- An actual quotient splitting with a prescribed nonzero quotient point. -/
theorem exists_quotientSplit_nonzero_point
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (K : Submodule (ZMod 2) V) (w : V)
    (hw : (Submodule.Quotient.mk w : V ⧸ K) ≠ 0) :
    ∃ t : ((V ⧸ K) × K) ≃ₗ[ZMod 2] V,
      (∀ q a, (Submodule.Quotient.mk (t (q,a)) : V ⧸ K) = q) ∧
      t (Submodule.Quotient.mk w,0) = w := by
  obtain ⟨s,hs⟩ := exists_quotientSplit K
  have ha : s (Submodule.Quotient.mk w,0) ≠ 0 := by
    intro h
    have hq := hs (Submodule.Quotient.mk w) 0
    rw [h] at hq
    exact hw hq.symm
  have hwb : w ≠ 0 := by
    intro h
    apply hw
    rw [h]
    rfl
  obtain ⟨u,hu,huq⟩ := exists_quotientFixingEquiv K
    (s (Submodule.Quotient.mk w,0)) w ha hwb (hs _ _)
  exact ⟨s.trans u, fun q a => (huq _).trans (hs q a),hu⟩

/-- The actual preimage coordinates of a subspace of the CSS quotient. -/
def cssQuotientSubspaceEmbedding (N : Submodule (ZMod 2) (BinaryVector k))
    (t : (CSSQuotient N × N.comap (orthogonal N).subtype) ≃ₗ[ZMod 2] orthogonal N)
    (S : Submodule (ZMod 2) (CSSQuotient N)) :
    (S × N.comap (orthogonal N).subtype) →ₗ[ZMod 2] BinaryVector k where
  toFun z := (t (z.1.val,z.2)).val
  map_add' x y := by
    change (t ((x.1.val,x.2)+(y.1.val,y.2))).val = _
    rw [map_add]
    rfl
  map_smul' a x := by
    change (t (a • (x.1.val,x.2))).val = _
    rw [map_smul]
    rfl

theorem cssQuotientSubspaceEmbedding_injective
    (N : Submodule (ZMod 2) (BinaryVector k))
    (t : (CSSQuotient N × N.comap (orthogonal N).subtype) ≃ₗ[ZMod 2] orthogonal N)
    (S : Submodule (ZMod 2) (CSSQuotient N)) :
    Function.Injective (cssQuotientSubspaceEmbedding N t S) := by
  intro x y h
  have he : (x.1.val,x.2)=(y.1.val,y.2) := t.injective (Subtype.ext h)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (congrArg (fun z : CSSQuotient N × N.comap (orthogonal N).subtype => z.2) he)

/-- Partial full-q isometries of the actual ordinary quotient extend to its actual group.
Only the necessary Wu incidence and value compatibility are hypotheses. -/
theorem ordinaryCSSQuotient_witt_extension (N : OrdinaryDefect k r)
    (S T : Submodule (ZMod 2) (CSSQuotient N.val))
    (e : S ≃ₗ[ZMod 2] T)
    (hq : ∀ x : S, cssQuotientQuadratic N.val N.property.1 (e x).val =
      cssQuotientQuadratic N.val N.property.1 x.val)
    (hw : cssQuotientWu N.val N.property.1 ∈ S ↔ cssQuotientWu N.val N.property.1 ∈ T)
    (hew : ∀ hs : cssQuotientWu N.val N.property.1 ∈ S,
      (e ⟨cssQuotientWu N.val N.property.1,hs⟩).val = cssQuotientWu N.val N.property.1) :
    ∃ g : CSSQuotientIsometryGroup N.val N.property.1,
      ∀ x : S, g.val x.val = (e x).val := by
  let K := N.val.comap (orthogonal N.val).subtype
  let w : orthogonal N.val := ⟨allOnes k,N.property.1.allOnes_mem_orthogonal⟩
  obtain ⟨t,ht,htw⟩ := exists_quotientSplit_nonzero_point K w (ordinaryCSSQuotient_wu_ne_zero N)
  let J := cssQuotientSubspaceEmbedding N.val t S
  let L := cssQuotientSubspaceEmbedding N.val t T
  let a := LinearEquiv.ofInjective J (cssQuotientSubspaceEmbedding_injective N.val t S)
  let b := LinearEquiv.ofInjective L (cssQuotientSubspaceEmbedding_injective N.val t T)
  let ep := e.prodCongr (LinearEquiv.refl (ZMod 2) K)
  let f := a.symm.trans (ep.trans b)
  have hjq (x : S × K) :
      cssQuotientQuadratic N.val N.property.1 x.1.val = weightQuadratic (J x) := by
    have hh := ht x.1.val x.2
    rw [← hh]
    rfl
  have hlq (x : T × K) :
      cssQuotientQuadratic N.val N.property.1 x.1.val = weightQuadratic (L x) := by
    have hh := ht x.1.val x.2
    rw [← hh]
    rfl
  have hf (x : S × K) : (f (a x)).val=L (ep x) := by
    simp only [f,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    rfl
  have hqf (x : LinearMap.range J) : weightQuadratic (f x).val=weightQuadratic x.val := by
    obtain ⟨z,rfl⟩ := a.surjective x
    rw [hf z]
    exact (hlq (ep z)).symm.trans ((hq z.1).trans (hjq z))
  have hwrange (U : Submodule (ZMod 2) (CSSQuotient N.val)) :
      allOnes k ∈ LinearMap.range (cssQuotientSubspaceEmbedding N.val t U) ↔
        cssQuotientWu N.val N.property.1 ∈ U := by
    constructor
    · rintro ⟨z,hz⟩
      have htz : t (z.1.val,z.2)=w := Subtype.ext hz
      have hh := ht z.1.val z.2
      rw [htz] at hh
      change cssQuotientWu N.val N.property.1=z.1.val at hh
      rw [hh]
      exact z.1.property
    · intro hu
      refine ⟨(⟨cssQuotientWu N.val N.property.1,hu⟩,0),?_⟩
      exact congrArg (fun v : orthogonal N.val => v.val) htw
  have hwf : allOnes k ∈ LinearMap.range J ↔ allOnes k ∈ LinearMap.range L :=
    (hwrange S).trans (hw.trans (hwrange T).symm)
  have hfw (hs : allOnes k ∈ LinearMap.range J) :
      (f ⟨allOnes k,hs⟩).val=allOnes k := by
    let z : S × K := (⟨cssQuotientWu N.val N.property.1,(hwrange S).mp hs⟩,0)
    have haz : a z=⟨allOnes k,hs⟩ := by
      apply Subtype.ext
      change (t (cssQuotientWu N.val N.property.1,0)).val=allOnes k
      exact congrArg (fun v : orthogonal N.val => v.val) htw
    have hh : (f ⟨allOnes k,hs⟩).val=L (ep z) :=
      (congrArg (fun v : LinearMap.range J => (f v).val) haz.symm).trans (hf z)
    rw [hh]
    change (t ((e z.1).val,0)).val=allOnes k
    rw [hew]
    exact congrArg (fun v : orthogonal N.val => v.val) htw
  obtain ⟨g,hg⟩ := stochastic_witt_extension (LinearMap.range J) (LinearMap.range L) f hqf hwf hfw
  have hgn (x : N.val) : g.val x.val=x.val := by
    let xh : orthogonal N.val := ⟨x.val,N.property.1.le_orthogonal x.property⟩
    obtain ⟨⟨q,z⟩,hz⟩ := t.surjective xh
    have hq0 : q=0 := by
      have hh := ht q z
      rw [hz] at hh
      exact hh.symm.trans ((Submodule.Quotient.mk_eq_zero K).mpr x.property)
    subst q
    have hj : J (0,z)=x.val := congrArg (fun v : orthogonal N.val => v.val) hz
    have he := hg (a (0,z))
    rw [hf] at he
    change g.val (J (0,z))=L (e 0,z) at he
    rw [map_zero] at he
    change g.val (J (0,z))=J (0,z) at he
    simpa only [hj] using he
  have hmap : stochasticSubspace g N.val=N.val := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro y ⟨x,hx,rfl⟩
      change g.val x ∈ N.val
      rw [hgn ⟨x,hx⟩]
      exact hx
    · rw [stochasticSubspace_finrank]
  refine ⟨stochasticDefectQuotientAction N.val N.property.1 ⟨g,hmap⟩,?_⟩
  intro x
  let xh := t (x.val,0)
  have hx : (Submodule.Quotient.mk xh : CSSQuotient N.val)=x.val := ht x.val 0
  rw [← hx,stochasticDefectQuotientAction_mk]
  have he := hg (a (x,0))
  rw [hf] at he
  have het : stabilizerOrthogonalEquiv N.val ⟨g,hmap⟩ xh=t ((e x).val,0) := Subtype.ext he
  rw [het,ht]

end ExactCriticalCurve.Quantum

