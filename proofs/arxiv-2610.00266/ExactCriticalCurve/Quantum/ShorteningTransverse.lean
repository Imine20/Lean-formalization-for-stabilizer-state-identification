import ExactCriticalCurve.Quantum.ShorteningSaturation

/-! # Constructing the unique transverse lift of an actual closed hyperplane -/
noncomputable section
open Classical
namespace ExactCriticalCurve.Binary
open StochasticCounting
variable {k : ℕ}

abbrev ShorteningHyperplane (R : StochasticLagrangian k) :=
  {H : Submodule (ZMod 2) (RelationSpace k) //
    H ≤ R.carrier ∧ Module.finrank (ZMod 2) H + 1 = k ∧
      relationWu k ∈ H ∧ shorteningLeftWu k ∉ H}

theorem shorteningHyperplane_parity (R : StochasticLagrangian k)
    (hR : shorteningLeftWu k ∈ R.carrier) (H : ShorteningHyperplane R)
    {x : RelationSpace k} (hx : x ∈ H.val) : shorteningLeftParity k x = 0 :=
  shorteningLeftParity_closed R hR (H.property.1 hx)

theorem shorteningHyperplane_sup_leftWu (hk : 0 < k) (R : StochasticLagrangian k)
    (hR : shorteningLeftWu k ∈ R.carrier) (H : ShorteningHyperplane R) :
    H.val ⊔ Submodule.span (ZMod 2) {shorteningLeftWu k} = R.carrier := by
  have hd := Submodule.disjoint_span_singleton_of_notMem H.property.2.2.2
  have hw : shorteningLeftWu k ≠ 0 := by
    intro h
    exact allOnes_ne_zero hk (congrArg Prod.fst h)
  have hf := Submodule.finrank_sup_add_finrank_inf_eq H.val
    (Submodule.span (ZMod 2) {shorteningLeftWu k})
  rw [hd.eq_bot,finrank_bot,add_zero,finrank_span_singleton hw,H.property.2.1] at hf
  apply Submodule.eq_of_le_of_finrank_eq
    (sup_le H.property.1 ((Submodule.span_singleton_le_iff_mem _ _).mpr hR))
  exact hf.trans R.finrank_eq.symm

theorem shorteningHyperplane_leftWu_orthogonal (R : StochasticLagrangian k)
    (hR : shorteningLeftWu k ∈ R.carrier) (H : ShorteningHyperplane R) :
    shorteningLeftWu k ∈ (relationBilinear k).orthogonal H.val := by
  intro x hx
  exact relationQuadratic_zero_pairwise R.quadratic_zero (H.property.1 hx) hR

/-- Nondegeneracy produces an odd vector orthogonal to H; the full mod-four
value selects exactly one of its two Wu translates as a singular vector. -/
theorem shorteningHyperplane_exists_vector (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) :
    ∃ v : RelationSpace k, v ∈ (relationBilinear k).orthogonal H.val ∧
      shorteningLeftParity k v = 1 ∧ relationQuadratic v = 0 := by
  have hex : ∃ v : (relationBilinear k).orthogonal H.val,
      shorteningLeftParity k v.val ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply H.property.2.2.2
    have hh : shorteningLeftWu k ∈
        (relationBilinear k).orthogonal ((relationBilinear k).orthogonal H.val) := by
      intro v hv
      change relationBilinear k v (shorteningLeftWu k) = 0
      rw [(relationBilinear_isSymm k).eq]
      exact hn ⟨v,hv⟩
    rw [LinearMap.BilinForm.orthogonal_orthogonal (relationBilinear_nondegenerate k)
      (relationBilinear_isSymm k).isRefl] at hh
    exact hh
  obtain ⟨v,hv⟩ := hex
  have hv1 : shorteningLeftParity k v.val = 1 := by
    generalize shorteningLeftParity k v.val = a at *
    fin_cases a <;> simp_all
  have heven : relationQuadratic v.val + relationQuadratic v.val = 0 := by
    apply relationQuadratic_even ⟨v.val,?_⟩
    apply (mem_evenRelationSpace_iff _).mpr
    exact v.property _ H.property.2.2.1
  have hql : relationQuadratic (shorteningLeftWu k) = 0 :=
    R.quadratic_zero _ hR
  have hvl : relationBilinear k v.val (shorteningLeftWu k) = 1 := by
    rw [(relationBilinear_isSymm k).eq]
    exact hv1
  have hadd (a : ZMod 2) :
      relationQuadratic (v.val + a • shorteningLeftWu k) =
        relationQuadratic v.val + 2 * bitLift a := by
    rcases (show a=0 ∨ a=1 by fin_cases a <;> simp) with rfl | rfl
    · simp
    · rw [one_smul,relationQuadratic_add,hql,hvl,add_zero]
  let a := halfEven (relationQuadratic v.val)
  refine ⟨v.val+a • shorteningLeftWu k,
    ((relationBilinear k).orthogonal H.val).add_mem v.property
      (((relationBilinear k).orthogonal H.val).smul_mem a
        (shorteningHyperplane_leftWu_orthogonal R hR H)),?_,?_⟩
  · rw [map_add,map_smul,hv1,shorteningLeftParity_leftWu h4,smul_zero,add_zero]
  · rw [hadd,two_mul_bitLift_halfEven _ heven]
    exact heven

def shorteningTransverseVector (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) : RelationSpace k :=
  (shorteningHyperplane_exists_vector h4 R hR H).choose

theorem shorteningTransverseVector_spec (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) :
    shorteningTransverseVector h4 R hR H ∈ (relationBilinear k).orthogonal H.val ∧
      shorteningLeftParity k (shorteningTransverseVector h4 R hR H) = 1 ∧
      relationQuadratic (shorteningTransverseVector h4 R hR H) = 0 :=
  (shorteningHyperplane_exists_vector h4 R hR H).choose_spec

def shorteningTransverseCarrier (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) : Submodule (ZMod 2) (RelationSpace k) :=
  H.val ⊔ Submodule.span (ZMod 2) {shorteningTransverseVector h4 R hR H}

theorem shorteningTransverseCarrier_finrank (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) :
    Module.finrank (ZMod 2) (shorteningTransverseCarrier h4 R hR H) = k := by
  have hs := shorteningTransverseVector_spec h4 R hR H
  have hn : shorteningTransverseVector h4 R hR H ∉ H.val := by
    intro h
    have hz := shorteningHyperplane_parity R hR H h
    rw [hs.2.1] at hz
    exact one_ne_zero hz
  have hv : shorteningTransverseVector h4 R hR H ≠ 0 :=
    fun h => hn (h ▸ H.val.zero_mem)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq H.val
    (Submodule.span (ZMod 2) {shorteningTransverseVector h4 R hR H})
  rw [(Submodule.disjoint_span_singleton_of_notMem hn).eq_bot,finrank_bot,
    add_zero,finrank_span_singleton hv,H.property.2.1] at hd
  exact hd

theorem shorteningTransverseCarrier_quadratic (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) :
    ∀ p ∈ shorteningTransverseCarrier h4 R hR H, relationQuadratic p = 0 := by
  have hs := shorteningTransverseVector_spec h4 R hR H
  intro p hp
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hqx := R.quadratic_zero x (H.property.1 hx)
  have hb := hs.1 x hx
  rcases (show a=0 ∨ a=1 by fin_cases a <;> simp) with rfl | rfl
  · simpa only [zero_smul,add_zero] using hqx
  · rw [one_smul,relationQuadratic_add,hqx,hs.2.2,hb]
    simp

def shorteningTransverseLift (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) : StochasticLagrangian k where
  carrier := shorteningTransverseCarrier h4 R hR H
  finrank_eq := shorteningTransverseCarrier_finrank h4 R hR H
  quadratic_zero := shorteningTransverseCarrier_quadratic h4 R hR H
  allOnes_mem := (show H.val ≤ shorteningTransverseCarrier h4 R hR H from le_sup_left)
    H.property.2.2.1

theorem shorteningTransverseLift_evenPart (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) :
    shorteningEvenPart (shorteningTransverseLift h4 R hR H) = H.val := by
  have hs := shorteningTransverseVector_spec h4 R hR H
  ext p
  constructor
  · rintro ⟨hp,hpar⟩
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
    have ha : a=0 := by
      change shorteningLeftParity k (x+a • shorteningTransverseVector h4 R hR H)=0 at hpar
      rw [map_add,map_smul,shorteningHyperplane_parity R hR H hx,hs.2.1] at hpar
      simpa only [zero_add,smul_eq_mul,mul_one] using hpar
    simpa only [ha,zero_smul,add_zero] using hx
  · intro hp
    exact ⟨(show H.val ≤ shorteningTransverseCarrier h4 R hR H from le_sup_left) hp,
      shorteningHyperplane_parity R hR H hp⟩

theorem shorteningTransverseLift_missing (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) :
    shorteningLeftWu k ∉ (shorteningTransverseLift h4 R hR H).carrier := by
  intro h
  have hh : shorteningLeftWu k ∈ shorteningEvenPart (shorteningTransverseLift h4 R hR H) :=
    ⟨h,shorteningLeftParity_leftWu h4⟩
  rw [shorteningTransverseLift_evenPart] at hh
  exact H.property.2.2.2 hh

theorem shorteningTransverseLift_saturation (hk : 0 < k) (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier)
    (H : ShorteningHyperplane R) :
    shorteningSaturation hk h4 (shorteningTransverseLift h4 R hR H) = R := by
  apply StochasticLagrangian.ext
  change shorteningEvenPart (shorteningTransverseLift h4 R hR H) ⊔
    Submodule.span (ZMod 2) {shorteningLeftWu k} = R.carrier
  rw [shorteningTransverseLift_evenPart]
  exact shorteningHyperplane_sup_leftWu hk R hR H

end ExactCriticalCurve.Binary

