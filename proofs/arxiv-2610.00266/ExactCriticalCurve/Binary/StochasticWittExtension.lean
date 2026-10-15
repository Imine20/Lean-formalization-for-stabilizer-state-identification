import ExactCriticalCurve.Binary.StochasticQuadraticReduction
import ExactCriticalCurve.Binary.StochasticIsometry
import ExactCriticalCurve.FiniteQuadratic.BinaryWittExtension

/-! Actual ambient extensions preserving the full mod-four refinement and Wu vector. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Binary
open StochasticCounting FiniteQuadratic
variable {k : ℕ}

theorem weight_preserving_partial_dot (S : Submodule (ZMod 2) (BinaryVector k))
    (f : S →ₗ[ZMod 2] BinaryVector k)
    (hf : ∀ s : S, weightQuadratic (f s) = weightQuadratic s.val) (s t : S) :
    binaryDot (f s) (f t) = binaryDot s.val t.val := by
  apply two_mul_bitLift_injective
  have h := weightQuadratic_add (f s) (f t)
  rw [← map_add, hf, hf, hf] at h
  change weightQuadratic (s.val+t.val) =
    weightQuadratic s.val + weightQuadratic t.val + 2 * bitLift (binaryDot (f s) (f t)) at h
  rw [weightQuadratic_add] at h
  exact (add_left_cancel h).symm

theorem weight_preserving_partial_parity (S : Submodule (ZMod 2) (BinaryVector k))
    (f : S →ₗ[ZMod 2] BinaryVector k)
    (hf : ∀ s : S, weightQuadratic (f s) = weightQuadratic s.val) (s : S) :
    weightParity k (f s) = weightParity k s.val := by
  rw [weightParity_self, weightParity_self, weight_preserving_partial_dot S f hf]

theorem weight_preserving_partial_half (S : Submodule (ZMod 2) (BinaryVector k))
    (f : S →ₗ[ZMod 2] BinaryVector k)
    (hf : ∀ s : S, weightQuadratic (f s) = weightQuadratic s.val) (s : S) :
    stochasticHalfForm k (f s) = stochasticHalfForm k s.val :=
  (weightQuadratic_eq_iff_half_parity _ _ (weight_preserving_partial_parity S f hf s)).mp (hf s)

/-- Adjoin the actual Wu vector when it is outside both the source and image.
The extension's injectivity and full mod-four preservation are conclusions. -/
theorem weight_preserving_adjoin_wu
    (S : Submodule (ZMod 2) (BinaryVector k)) (f : S →ₗ[ZMod 2] BinaryVector k)
    (hfi : Function.Injective f)
    (hfq : ∀ s : S, weightQuadratic (f s) = weightQuadratic s.val)
    (hwS : allOnes k ∉ S) (hwf : allOnes k ∉ LinearMap.range f) :
    ∃ g : ↥(S ⊔ Submodule.span (ZMod 2) {allOnes k}) →ₗ[ZMod 2] BinaryVector k,
      Function.Injective g ∧ (∀ z, weightQuadratic (g z) = weightQuadratic z.val) ∧
      (∀ s : S, g ⟨s.val,(show S ≤ S ⊔ Submodule.span (ZMod 2) {allOnes k} from le_sup_left) s.property⟩ = f s) ∧
      g ⟨allOnes k,(show Submodule.span (ZMod 2) {allOnes k} ≤
        S ⊔ Submodule.span (ZMod 2) {allOnes k} from le_sup_right)
          (Submodule.mem_span_singleton_self _)⟩ = allOnes k := by
  obtain ⟨g,hgf,hgw⟩ := f.exists_extend_of_notMem hwS (allOnes k)
  have hgs (s : S) : g s.val = f s := congrArg (fun m : S →ₗ[ZMod 2] BinaryVector k => m s) hgf
  let T := S ⊔ Submodule.span (ZMod 2) {allOnes k}
  have decomp (z : T) : ∃ s : S, ∃ a : ZMod 2,
      z.val = s.val + a • allOnes k ∧ g z.val = f s + a • allOnes k := by
    obtain ⟨s,hs,t,ht,he⟩ := Submodule.mem_sup.mp z.property
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp ht
    refine ⟨⟨s,hs⟩,a,he.symm,?_⟩
    rw [← he, map_add, map_smul, hgs ⟨s,hs⟩, hgw]
  refine ⟨g.domRestrict T, ?_, ?_, hgs, hgw⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change g z.val = 0 at hz
    obtain ⟨s,a,hzv,hgz⟩ := decomp z
    rw [hgz] at hz
    fin_cases a
    · have hs : f s = 0 := by simpa using hz
      have hs0 : s = 0 := hfi (by simpa using hs)
      apply Subtype.ext
      simpa [hs0] using hzv
    · have hz' : f s + allOnes k = 0 := by simpa using hz
      exact False.elim (hwf ⟨-s,by
        rw [map_neg]
        exact (eq_neg_of_add_eq_zero_right hz').symm⟩)
  · intro z
    change weightQuadratic (g z.val) = weightQuadratic z.val
    obtain ⟨s,a,hzv,hgz⟩ := decomp z
    rw [hgz,hzv]
    have hp : binaryDot (f s) (allOnes k) = binaryDot s.val (allOnes k) := by
      rw [← binaryDot_self_eq_dot_allOnes, ← binaryDot_self_eq_dot_allOnes,
        weight_preserving_partial_dot S f hfq]
    fin_cases a <;> simp [weightQuadratic_add, hfq, hp]

theorem even_weight_extension_fixing_wu (hk : (k : ZMod 2) = 0)
    (S : Submodule (ZMod 2) (BinaryVector k)) (f : S →ₗ[ZMod 2] BinaryVector k)
    (hfi : Function.Injective f)
    (hfq : ∀ s : S, weightQuadratic (f s) = weightQuadratic s.val)
    (hw : allOnes k ∈ S) (hfw : f ⟨allOnes k,hw⟩ = allOnes k) :
    ∃ e : StochasticIsometryGroup k, ∀ s : S, e.val s.val = f s := by
  obtain ⟨e,heQ,hef⟩ := exists_binaryQuadratic_extension (stochasticHalfForm k)
    (stochasticHalfForm_nondegenerate hk) S f hfi (weight_preserving_partial_half S f hfq)
  have hew : e (allOnes k) = allOnes k := (hef ⟨_,hw⟩).trans hfw
  have heB (x y : BinaryVector k) :
      (stochasticHalfForm k).polarBilin (e x) (e y) =
        (stochasticHalfForm k).polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    rw [← map_add, heQ, heQ, heQ]
  have hep (x : BinaryVector k) : weightParity k (e x) = weightParity k x := by
    have h := heB (allOnes k) x
    rw [hew, stochasticHalfForm_polar, stochasticHalfBilinear_wu hk,
      stochasticHalfBilinear_wu hk] at h
    exact h
  refine ⟨⟨e,?_,hew⟩,hef⟩
  intro x
  exact (weightQuadratic_eq_iff_half_parity _ _ (hep x)).mpr (heQ x)


/-- Actual projection onto the even-weight summand in odd dimension. -/
def oddWuCorrectionLinear (hk : (k : ZMod 2) = 1) :
    BinaryVector k →ₗ[ZMod 2] evenWeightSpace k where
  toFun x := ⟨x + weightParity k x • allOnes k, oddWuCorrection_mem hk x⟩
  map_add' x y := by
    apply Subtype.ext
    change x+y+weightParity k (x+y) • allOnes k =
      (x+weightParity k x • allOnes k)+(y+weightParity k y • allOnes k)
    rw [map_add, add_smul]
    abel
  map_smul' a x := by
    apply Subtype.ext
    change a • x + weightParity k (a • x) • allOnes k =
      a • (x + weightParity k x • allOnes k)
    simp only [map_smul, smul_add, smul_smul, smul_eq_mul]

theorem oddWuCorrection_reconstruct (hk : (k : ZMod 2) = 1) (x : BinaryVector k) :
    (oddWuCorrectionLinear hk x).val + weightParity k x • allOnes k = x := by
  change (x+weightParity k x • allOnes k)+weightParity k x • allOnes k = x
  rw [add_assoc, ← add_smul, binaryScalar_add_self, zero_smul, add_zero]

theorem odd_weight_extension_fixing_wu (hk : (k : ZMod 2) = 1)
    (S : Submodule (ZMod 2) (BinaryVector k)) (f : S →ₗ[ZMod 2] BinaryVector k)
    (hfi : Function.Injective f)
    (hfq : ∀ s : S, weightQuadratic (f s) = weightQuadratic s.val)
    (hw : allOnes k ∈ S) (hfw : f ⟨allOnes k,hw⟩ = allOnes k) :
    ∃ e : StochasticIsometryGroup k, ∀ s : S, e.val s.val = f s := by
  let I := evenWeightSpace k
  let R : Submodule (ZMod 2) I := S.comap I.subtype
  let j : R →ₗ[ZMod 2] S :=
    LinearMap.codRestrict S (I.subtype.comp R.subtype) (fun r => r.property)
  let fR : R →ₗ[ZMod 2] I := LinearMap.codRestrict I (f.comp j) (by
    intro r
    change weightParity k (f (j r)) = 0
    rw [weight_preserving_partial_parity S f hfq]
    exact (mem_evenWeightSpace _).mp r.val.property)
  have hRi : Function.Injective fR := by
    intro a b he
    have h : f (j a) = f (j b) := congrArg Subtype.val he
    have h' := congrArg Subtype.val (hfi h)
    exact Subtype.ext (Subtype.ext h')
  have hRq (r : R) : evenWeightHalfForm k (fR r) = evenWeightHalfForm k r.val := by
    rw [evenWeightHalfForm_apply, evenWeightHalfForm_apply]
    congr 1
    exact hfq (j r)
  obtain ⟨h,hhQ,hhf⟩ := exists_binaryQuadratic_extension (evenWeightHalfForm k)
    (evenWeightHalfForm_nondegenerate hk) R fR hRi hRq
  let c := oddWuCorrectionLinear hk
  let g : BinaryVector k →ₗ[ZMod 2] BinaryVector k :=
    I.subtype.comp (h.toLinearMap.comp c) + (weightParity k).smulRight (allOnes k)
  have hg (x : BinaryVector k) : g x = (h (c x)).val + weightParity k x • allOnes k := rfl
  have hgp (x : BinaryVector k) : weightParity k (g x) = weightParity k x := by
    rw [hg, map_add, map_smul, weightParity_wu, hk]
    have hz := (mem_evenWeightSpace _).mp (h (c x)).property
    rw [hz]
    simp only [smul_eq_mul, mul_one, zero_add]
  have hgi : Function.Injective g := by
    intro x y he
    have hp : weightParity k x = weightParity k y := by
      have hh := congrArg (weightParity k) he
      simpa only [hgp] using hh
    rw [hg,hg,hp] at he
    have hhc : h (c x) = h (c y) := Subtype.ext (add_right_cancel he)
    have hc := congrArg Subtype.val (h.injective hhc)
    calc
      x = (c x).val + weightParity k x • allOnes k :=
        (oddWuCorrection_reconstruct hk x).symm
      _ = (c y).val + weightParity k y • allOnes k := by rw [hc,hp]
      _ = y := oddWuCorrection_reconstruct hk y
  have hqI (u : I) : weightQuadratic (h u).val = weightQuadratic u.val := by
    apply (weightQuadratic_eq_iff_half_parity _ _ ?_).mpr
    · exact hhQ u
    · exact ((mem_evenWeightSpace _).mp (h u).property).trans
        ((mem_evenWeightSpace _).mp u.property).symm
  have hcross (u : I) (a : ZMod 2) : binaryDot u.val (a • allOnes k) = 0 := by
    change binaryDotForm k u.val (a • allOnes k) = 0
    rw [map_smul]
    have hu : binaryDotForm k u.val (allOnes k) = 0 :=
      (binaryDot_comm _ _).trans ((mem_evenWeightSpace _).mp u.property)
    rw [hu, smul_zero]
  have hgq (x : BinaryVector k) : weightQuadratic (g x) = weightQuadratic x := by
    calc
      _ = weightQuadratic (c x).val + weightQuadratic (weightParity k x • allOnes k) := by
        rw [hg,weightQuadratic_add,hcross,hqI,bitLift_zero,mul_zero,add_zero]
      _ = weightQuadratic ((c x).val+weightParity k x • allOnes k) := by
        rw [weightQuadratic_add,hcross,bitLift_zero,mul_zero,add_zero]
      _ = _ := congrArg weightQuadratic (oddWuCorrection_reconstruct hk x)
  have hcw : c (allOnes k) = 0 := by
    apply Subtype.ext
    change allOnes k + weightParity k (allOnes k) • allOnes k = 0
    rw [weightParity_wu,hk,one_smul]
    ext i
    exact binaryScalar_add_self _
  have hgw : g (allOnes k) = allOnes k := by
    rw [hg,hcw,map_zero,Submodule.coe_zero,weightParity_wu,hk,one_smul,zero_add]
  refine ⟨⟨LinearEquiv.ofInjectiveEndo g hgi,hgq,hgw⟩,?_⟩
  intro s
  change g s.val = f s
  have hcs : (c s.val).val ∈ S := S.add_mem s.property (S.smul_mem _ hw)
  have hh := hhf ⟨c s.val,hcs⟩
  have hhv : (h (c s.val)).val = f (j ⟨c s.val,hcs⟩) := congrArg Subtype.val hh
  have hj : j ⟨c s.val,hcs⟩ = s + weightParity k s.val • (⟨allOnes k,hw⟩ : S) :=
    Subtype.ext rfl
  rw [hg,hhv,hj,map_add,map_smul,hfw,add_assoc,← add_smul,
    binaryScalar_add_self,zero_smul,add_zero]


theorem weight_extension_fixing_wu_of_mem
    (S : Submodule (ZMod 2) (BinaryVector k)) (f : S →ₗ[ZMod 2] BinaryVector k)
    (hfi : Function.Injective f)
    (hfq : ∀ s : S, weightQuadratic (f s) = weightQuadratic s.val)
    (hw : allOnes k ∈ S) (hfw : f ⟨allOnes k,hw⟩ = allOnes k) :
    ∃ e : StochasticIsometryGroup k, ∀ s : S, e.val s.val = f s := by
  have hcases : ∀ a : ZMod 2, a=0 ∨ a=1 := by decide
  rcases hcases (k : ZMod 2) with hk | hk
  · exact even_weight_extension_fixing_wu hk S f hfi hfq hw hfw
  · exact odd_weight_extension_fixing_wu hk S f hfi hfq hw hfw

/-- Full mod-four Witt extension with exactly the necessary Wu compatibility.
The ambient stochastic isometry is constructed, not supplied as a premise. -/
theorem stochastic_witt_extension
    (S T : Submodule (ZMod 2) (BinaryVector k)) (f : S ≃ₗ[ZMod 2] T)
    (hfq : ∀ s : S, weightQuadratic (f s).val = weightQuadratic s.val)
    (hw : allOnes k ∈ S ↔ allOnes k ∈ T)
    (hfw : ∀ hs : allOnes k ∈ S, (f ⟨allOnes k,hs⟩).val = allOnes k) :
    ∃ e : StochasticIsometryGroup k, ∀ s : S, e.val s.val = (f s).val := by
  let F := T.subtype.comp f.toLinearMap
  have hFi : Function.Injective F := Subtype.val_injective.comp f.injective
  by_cases hs : allOnes k ∈ S
  · exact weight_extension_fixing_wu_of_mem S F hFi hfq hs (hfw hs)
  · have ht : allOnes k ∉ T := fun ht => hs (hw.mpr ht)
    have hFr : allOnes k ∉ LinearMap.range F := by
      rintro ⟨s,he⟩
      apply ht
      rw [← he]
      exact (f s).property
    obtain ⟨G,hGi,hGq,hGF,hGw⟩ := weight_preserving_adjoin_wu S F hFi hfq hs hFr
    let U := S ⊔ Submodule.span (ZMod 2) {allOnes k}
    have hwu : allOnes k ∈ U :=
      (show Submodule.span (ZMod 2) {allOnes k} ≤ U from le_sup_right)
        (Submodule.mem_span_singleton_self _)
    obtain ⟨e,he⟩ := weight_extension_fixing_wu_of_mem U G hGi hGq hwu hGw
    refine ⟨e,fun s => ?_⟩
    exact (he ⟨s.val,(show S ≤ U from le_sup_left) s.property⟩).trans (hGF s)

/-- The Wu obstruction is also necessary; no further obstruction remains. -/
theorem stochastic_witt_extension_iff
    (S T : Submodule (ZMod 2) (BinaryVector k)) (f : S ≃ₗ[ZMod 2] T)
    (hfq : ∀ s : S, weightQuadratic (f s).val = weightQuadratic s.val) :
    (∃ e : StochasticIsometryGroup k, ∀ s : S, e.val s.val = (f s).val) ↔
      (allOnes k ∈ S ↔ allOnes k ∈ T) ∧
      (∀ hs : allOnes k ∈ S, (f ⟨allOnes k,hs⟩).val = allOnes k) := by
  constructor
  · rintro ⟨e,he⟩
    have hfw (hs : allOnes k ∈ S) : (f ⟨allOnes k,hs⟩).val = allOnes k :=
      (he ⟨_,hs⟩).symm.trans (stochasticIsometry_allOnes e)
    refine ⟨⟨?_,?_⟩,hfw⟩
    · intro hs
      rw [← hfw hs]
      exact (f ⟨_,hs⟩).property
    · intro ht
      let s := f.symm ⟨allOnes k,ht⟩
      have hes : e.val s.val = allOnes k := by
        rw [he]
        exact congrArg Subtype.val (f.apply_symm_apply ⟨_,ht⟩)
      have hsw : s.val = allOnes k :=
        e.val.injective (hes.trans (stochasticIsometry_allOnes e).symm)
      exact hsw ▸ s.property
  · rintro ⟨hw,hfw⟩
    exact stochastic_witt_extension S T f hfq hw hfw

end ExactCriticalCurve.Binary
