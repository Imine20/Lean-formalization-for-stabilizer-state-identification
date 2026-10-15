import ExactCriticalCurve.Quantum.ShorteningTransverse

/-! # Exhaustive actual transverse fibers, by genuine hyperplanes -/
noncomputable section
open Classical
namespace ExactCriticalCurve.Binary
open StochasticCounting
variable {k : ℕ}

theorem shorteningHyperplane_orthogonal_decomposition (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) :
    R.carrier ⊔ Submodule.span (ZMod 2) {shorteningTransverseVector h4 R hR H} =
      (relationBilinear k).orthogonal H.val := by
  have hs := shorteningTransverseVector_spec h4 R hR H
  have hn : shorteningTransverseVector h4 R hR H ∉ R.carrier := by
    intro h
    have hz := shorteningLeftParity_closed R hR h
    rw [hs.2.1] at hz
    exact one_ne_zero hz
  have hv : shorteningTransverseVector h4 R hR H ≠ 0 :=
    fun h => hn (h ▸ R.carrier.zero_mem)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq R.carrier
    (Submodule.span (ZMod 2) {shorteningTransverseVector h4 R hR H})
  rw [(Submodule.disjoint_span_singleton_of_notMem hn).eq_bot,
    finrank_bot,add_zero,finrank_span_singleton hv,R.finrank_eq] at hd
  have ho := LinearMap.BilinForm.finrank_orthogonal (relationBilinear_nondegenerate k)
    (relationBilinear_isSymm k).isRefl H.val
  have hvdim : Module.finrank (ZMod 2) (RelationSpace k) = 2*k := by
    simp [RelationSpace,BinaryVector,Module.finrank_prod,two_mul]
  rw [hvdim] at ho
  have ho' : Module.finrank (ZMod 2) ((relationBilinear k).orthogonal H.val) = k+1 := by
    have hh := H.property.2.1
    omega
  apply Submodule.eq_of_le_of_finrank_eq
  · apply sup_le
    · intro r hr x hx
      exact relationQuadratic_zero_pairwise R.quadratic_zero (H.property.1 hx) hr
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hs.1
  · exact hd.trans ho'.symm

/-- The parity kernel fixes the whole transverse relation uniquely. -/
theorem shorteningTransverseLift_unique (hk : 0 < k) (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) (T : StochasticLagrangian k)
    (hT : shorteningEvenPart T = H.val) :
    T = shorteningTransverseLift h4 R hR H := by
  have hs := shorteningTransverseVector_spec h4 R hR H
  have hHT : H.val ≤ T.carrier := by
    rw [← hT]
    exact inf_le_left
  have hto : T.carrier ≤ (relationBilinear k).orthogonal H.val := by
    intro p hp x hx
    exact relationQuadratic_zero_pairwise T.quadratic_zero (hHT hx) hp
  have hTR {x : RelationSpace k} (hxT : x ∈ T.carrier) (hxR : x ∈ R.carrier) : x ∈ H.val := by
    rw [← hT]
    exact ⟨hxT,shorteningLeftParity_closed R hR hxR⟩
  apply StochasticLagrangian.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · intro p hp
    have hpo := hto hp
    rw [← shorteningHyperplane_orthogonal_decomposition h4 R hR H] at hpo
    obtain ⟨r,hr,s,hs',rfl⟩ := Submodule.mem_sup.mp hpo
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hs'
    rcases (show c=0 ∨ c=1 by fin_cases c <;> simp) with rfl | rfl
    · simp only [zero_smul,add_zero] at hp ⊢
      exact (show H.val ≤ shorteningTransverseCarrier h4 R hR H from le_sup_left)
        (hTR hp hr)
    · simp only [one_smul] at hp ⊢
      have hb : relationBilinear k r (shorteningTransverseVector h4 R hR H) = 0 := by
        have hq := T.quadratic_zero _ hp
        rw [relationQuadratic_add,R.quadratic_zero r hr,hs.2.2] at hq
        apply (two_mul_bitLift_eq_zero_iff _).mp
        simpa only [zero_add] using hq
      have hr' : r ∈ H.val ⊔ Submodule.span (ZMod 2) {shorteningLeftWu k} := by
        rw [shorteningHyperplane_sup_leftWu hk R hR H]
        exact hr
      obtain ⟨x,hx,y,hy,he⟩ := Submodule.mem_sup.mp hr'
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
      have ha : a=0 := by
        rw [← he,map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,hs.1 x hx] at hb
        change 0 + a * shorteningLeftParity k (shorteningTransverseVector h4 R hR H) = 0 at hb
        simpa only [hs.2.1,zero_add,mul_one] using hb
      have hrH : r ∈ H.val := by
        rw [ha,zero_smul,add_zero] at he
        exact he ▸ hx
      exact (shorteningTransverseCarrier h4 R hR H).add_mem
        ((show H.val ≤ shorteningTransverseCarrier h4 R hR H from le_sup_left) hrH)
        ((show Submodule.span (ZMod 2) {shorteningTransverseVector h4 R hR H} ≤
            shorteningTransverseCarrier h4 R hR H from le_sup_right)
          (Submodule.mem_span_singleton_self _))
  · rw [T.finrank_eq,(shorteningTransverseLift h4 R hR H).finrank_eq]

abbrev ShorteningTransverseFiber (hk : 0 < k) (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) :=
  {T : StochasticLagrangian k //
    shorteningLeftWu k ∉ T.carrier ∧ shorteningSaturation hk h4 T = R}

def shorteningFiberHyperplane (hk : 0 < k) (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (T : ShorteningTransverseFiber hk h4 R) :
    ShorteningHyperplane R :=
  ⟨shorteningEvenPart T.val,by
    constructor
    · have h := congrArg StochasticLagrangian.carrier T.property.2
      change shorteningSaturationCarrier T.val = R.carrier at h
      rw [← h]
      exact le_sup_left
    · refine ⟨shorteningEvenPart_finrank T.val T.property.1,?_,?_⟩
      · exact ⟨T.val.allOnes_mem,shorteningLeftParity_wu h4⟩
      · exact fun h => T.property.1 h.1⟩

/-- All actual transverse lifts occur exactly once, with no additional family premise. -/
def shorteningTransverseFiberEquiv (hk : 0 < k) (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier) :
    ShorteningHyperplane R ≃ ShorteningTransverseFiber hk h4 R where
  toFun H := ⟨shorteningTransverseLift h4 R hR H,
    shorteningTransverseLift_missing h4 R hR H,
    shorteningTransverseLift_saturation hk h4 R hR H⟩
  invFun T := shorteningFiberHyperplane hk h4 R T
  left_inv H := by
    apply Subtype.ext
    exact shorteningTransverseLift_evenPart h4 R hR H
  right_inv T := by
    apply Subtype.ext
    exact (shorteningTransverseLift_unique hk h4 R hR
      (shorteningFiberHyperplane hk h4 R T) T.val rfl).symm

end ExactCriticalCurve.Binary

