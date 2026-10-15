import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRefinementGauss

/-! Separating the actual radical restriction from the nondegenerate refinement. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def binaryRefinementRadicalLinear (q : QuadraticForm (ZMod 2) V)
    (P : BinaryQuadraticRefinements q.polarBilin) : Module.Dual (ZMod 2) (binaryPolarRadical q) where
  toFun r := P.val r.val
  map_add' x y := by
    change P.val (x.val+y.val) = P.val x.val + P.val y.val
    rw [quadratic_add,P.property,(mem_binaryPolarRadical q x.val).mp x.property y.val,add_zero]
  map_smul' a x := by
    change P.val (a • x.val) = a • P.val x.val
    rw [P.val.map_smul]
    fin_cases a <;> simp

def binaryRefinementComplement (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (P : BinaryQuadraticRefinements q.polarBilin) :
    BinaryQuadraticRefinements (q.comp C.subtype).polarBilin :=
  ⟨P.val.comp C.subtype,by rw [QuadraticMap.polarBilin_comp,P.property,QuadraticMap.polarBilin_comp]⟩

def binaryRefinementFromProduct (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (P : BinaryQuadraticRefinements (q.comp C.subtype).polarBilin)
    (l : Module.Dual (ZMod 2) (binaryPolarRadical q)) : QuadraticForm (ZMod 2) V :=
  (P.val.prod (binaryLinearQuadratic l)).comp
    (Submodule.prodEquivOfIsCompl C (binaryPolarRadical q) hC.symm).symm.toLinearMap

theorem binaryRefinementFromProduct_polar (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (P : BinaryQuadraticRefinements (q.comp C.subtype).polarBilin)
    (l : Module.Dual (ZMod 2) (binaryPolarRadical q)) :
    (binaryRefinementFromProduct q C hC P l).polarBilin = q.polarBilin := by
  let e := Submodule.prodEquivOfIsCompl C (binaryPolarRadical q) hC.symm
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨⟨c,r⟩,rfl⟩ := e.surjective x
  obtain ⟨⟨d,s⟩,rfl⟩ := e.surjective y
  have hleft (r : binaryPolarRadical q) (x : V) : q.polarBilin r.val x = 0 :=
    (mem_binaryPolarRadical q r.val).mp r.property x
  have hright (r : binaryPolarRadical q) (x : V) : q.polarBilin x r.val = 0 :=
    ((polar_isSymm q).eq _ _).trans (hleft r x)
  simp only [binaryRefinementFromProduct,e,QuadraticMap.polarBilin_comp,
    QuadraticMap.polarBilin_prod,binaryLinearQuadratic_polar,LinearMap.add_apply,
    LinearMap.compl₁₂_apply,LinearMap.zero_apply,add_zero,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,LinearMap.fst_apply,LinearMap.snd_apply]
  rw [P.property]
  change q.polarBilin c.val d.val = q.polarBilin (c.val+r.val) (d.val+s.val)
  simp only [map_add,LinearMap.add_apply,hleft,hright,add_zero]

/-- This is the actual full refinement fiber split by restriction, including its linear radical. -/
def binaryQuadraticRefinementSplitEquiv (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C) :
    BinaryQuadraticRefinements q.polarBilin ≃
      BinaryQuadraticRefinements (q.comp C.subtype).polarBilin ×
        Module.Dual (ZMod 2) (binaryPolarRadical q) where
  toFun P := (binaryRefinementComplement q C P,binaryRefinementRadicalLinear q P)
  invFun z := ⟨binaryRefinementFromProduct q C hC z.1 z.2,
    binaryRefinementFromProduct_polar q C hC z.1 z.2⟩
  left_inv P := by
    apply Subtype.ext
    apply QuadraticMap.ext
    intro x
    let e := Submodule.prodEquivOfIsCompl C (binaryPolarRadical q) hC.symm
    obtain ⟨⟨c,r⟩,rfl⟩ := e.surjective x
    change (P.val.comp C.subtype).prod (binaryLinearQuadratic (binaryRefinementRadicalLinear q P))
      (e.symm (e (c,r))) = P.val (c.val+r.val)
    rw [e.symm_apply_apply,QuadraticMap.prod_apply,binaryLinearQuadratic_apply]
    change P.val c.val + P.val r.val = P.val (c.val+r.val)
    rw [quadratic_add,P.property]
    have hz : q.polarBilin c.val r.val = 0 :=
      ((polar_isSymm q).eq _ _).trans ((mem_binaryPolarRadical q r.val).mp r.property c.val)
    rw [hz,add_zero]
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      apply QuadraticMap.ext
      intro c
      let e := Submodule.prodEquivOfIsCompl C (binaryPolarRadical q) hC.symm
      have he : (c.val : V) = e (c,0) := by simp [e,Submodule.prodEquivOfIsCompl]
      change z.1.val.prod (binaryLinearQuadratic z.2) (e.symm c.val) = z.1.val c
      rw [he,e.symm_apply_apply,QuadraticMap.prod_apply,binaryLinearQuadratic_apply]
      simp
    · apply LinearMap.ext
      intro r
      let e := Submodule.prodEquivOfIsCompl C (binaryPolarRadical q) hC.symm
      have he : (r.val : V) = e (0,r) := by simp [e,Submodule.prodEquivOfIsCompl]
      change z.1.val.prod (binaryLinearQuadratic z.2) (e.symm r.val) = z.2 r
      rw [he,e.symm_apply_apply,QuadraticMap.prod_apply,binaryLinearQuadratic_apply]
      simp

theorem binaryRefinementFromProduct_gauss [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (P : BinaryQuadraticRefinements (q.comp C.subtype).polarBilin)
    (l : Module.Dual (ZMod 2) (binaryPolarRadical q)) :
    binaryQuadraticGaussSum (binaryRefinementFromProduct q C hC P l) =
      binaryQuadraticGaussSum P.val *
        (if l = 0 then (Nat.card (binaryPolarRadical q) : ℂ) else 0) := by
  have he : (binaryRefinementFromProduct q C hC P l).IsometryEquiv
      (P.val.prod (binaryLinearQuadratic l)) :=
    { toLinearEquiv := (Submodule.prodEquivOfIsCompl C (binaryPolarRadical q) hC.symm).symm
      map_app' := fun _ => rfl }
  rw [binaryQuadraticGaussSum_eq_of_isometry _ _ he,
    binaryQuadraticGaussSum_prod,binaryLinearQuadratic_gauss,Nat.card_eq_fintype_card]

theorem binaryQuadraticRefinementSplitEquiv_gauss [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (P : BinaryQuadraticRefinements q.polarBilin) :
    binaryQuadraticGaussSum P.val =
      binaryQuadraticGaussSum (binaryQuadraticRefinementSplitEquiv q C hC P).1.val *
        (if (binaryQuadraticRefinementSplitEquiv q C hC P).2 = 0
          then (Nat.card (binaryPolarRadical q) : ℂ) else 0) := by
  have h := binaryRefinementFromProduct_gauss q C hC
    (binaryQuadraticRefinementSplitEquiv q C hC P).1
    (binaryQuadraticRefinementSplitEquiv q C hC P).2
  have he := congrArg Subtype.val ((binaryQuadraticRefinementSplitEquiv q C hC).symm_apply_apply P)
  change binaryRefinementFromProduct q C hC _ _ = P.val at he
  rw [he] at h
  exact h

theorem binaryQuadraticRefinementSplitEquiv_zero_iff [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (P : BinaryQuadraticRefinements q.polarBilin) :
    binaryQuadraticGaussSum P.val = 0 ↔
      (binaryQuadraticRefinementSplitEquiv q C hC P).2 ≠ 0 := by
  have hn : LinearMap.BilinForm.Nondegenerate
      (binaryQuadraticRefinementSplitEquiv q C hC P).1.val.polarBilin := by
    rw [(binaryQuadraticRefinementSplitEquiv q C hC P).1.property]
    exact binaryRadical_complement_nondegenerate q C hC
  have hne := binaryQuadraticGaussSum_ne_zero _ hn
  have hr : (Nat.card (binaryPolarRadical q) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [binaryQuadraticRefinementSplitEquiv_gauss q C hC P]
  split_ifs with h
  · exact iff_of_false (mul_ne_zero hne hr) (by simpa using h)
  · simp [h]

/-- The whole zero-Gauss fiber, not just its count, records a nonzero radical functional. -/
def binaryQuadraticRefinementZeroEquiv [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C) :
    {P : BinaryQuadraticRefinements q.polarBilin // binaryQuadraticGaussSum P.val = 0} ≃
      BinaryQuadraticRefinements (q.comp C.subtype).polarBilin ×
        {l : Module.Dual (ZMod 2) (binaryPolarRadical q) // l ≠ 0} :=
  ((binaryQuadraticRefinementSplitEquiv q C hC).subtypeEquiv
    (q := fun z => z.2 ≠ 0) (binaryQuadraticRefinementSplitEquiv_zero_iff q C hC)).trans
      { toFun := fun z => (z.val.1,⟨z.val.2,z.property⟩)
        invFun := fun z => ⟨(z.1,z.2.val),z.2.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

theorem binaryQuadraticRefinementSplitEquiv_nonzero_iff [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (P : BinaryQuadraticRefinements q.polarBilin) (z : ℂ) (hz : z ≠ 0) :
    binaryQuadraticGaussSum P.val = z * (Nat.card (binaryPolarRadical q) : ℂ) ↔
      binaryQuadraticGaussSum (binaryQuadraticRefinementSplitEquiv q C hC P).1.val = z ∧
        (binaryQuadraticRefinementSplitEquiv q C hC P).2 = 0 := by
  have hr : (Nat.card (binaryPolarRadical q) : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [binaryQuadraticRefinementSplitEquiv_gauss q C hC P]
  split_ifs with h
  · simp only [h,and_true,mul_eq_mul_right_iff,hr,or_false]
  · exact iff_of_false (by simpa only [mul_zero] using Ne.symm (mul_ne_zero hz hr))
      (fun h' => h h'.2)

/-- A nonzero actual Gauss fiber has a unique zero radical component. -/
def binaryQuadraticRefinementNonzeroEquiv [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (z : ℂ) (hz : z ≠ 0) :
    {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = z * (Nat.card (binaryPolarRadical q) : ℂ)} ≃
    {P : BinaryQuadraticRefinements (q.comp C.subtype).polarBilin //
      binaryQuadraticGaussSum P.val = z} :=
  ((binaryQuadraticRefinementSplitEquiv q C hC).subtypeEquiv
    (q := fun p => binaryQuadraticGaussSum p.1.val = z ∧ p.2 = 0)
    (fun P => binaryQuadraticRefinementSplitEquiv_nonzero_iff q C hC P z hz)).trans
      { toFun := fun p => ⟨p.val.1,p.property.1⟩
        invFun := fun p => ⟨(p.val,0),p.property,rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl p.property.2.symm)
        right_inv := fun _ => rfl }

theorem binaryQuadraticRefinement_zero_card
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C) :
    Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = 0} =
      2 ^ finrank (ZMod 2) C * (2 ^ finrank (ZMod 2) (binaryPolarRadical q) - 1) := by
  rw [Nat.card_congr (binaryQuadraticRefinementZeroEquiv q C hC),Nat.card_prod,
    binaryQuadraticRefinements_card _ (binaryQuadratic_polar_isAlt _)]
  congr 1
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,Fintype.card_subtype_eq,
    Module.card_eq_pow_finrank (K := ZMod 2),Subspace.dual_finrank_eq]
  simp

theorem binaryQuadraticRefinement_radical_positive_card
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (t : ℕ) (ht : finrank (ZMod 2) C = 2*t) :
    2 * Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = (2 : ℂ)^(finrank (ZMod 2) (binaryPolarRadical q)+t)} =
      2^(2*t)+2^t := by
  have hr : (Nat.card (binaryPolarRadical q) : ℂ) =
      (2 : ℂ)^finrank (ZMod 2) (binaryPolarRadical q) := by
    rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := ZMod 2)]
    norm_num
  have hp : (2 : ℂ)^t * (Nat.card (binaryPolarRadical q) : ℂ) =
      (2 : ℂ)^(finrank (ZMod 2) (binaryPolarRadical q)+t) := by
    rw [hr,pow_add,mul_comm]
  rw [← hp,Nat.card_congr (binaryQuadraticRefinementNonzeroEquiv q C hC
    ((2 : ℂ)^t) (pow_ne_zero _ (by norm_num)))]
  exact binaryQuadraticRefinement_positive_card (q.comp C.subtype)
    (binaryRadical_complement_nondegenerate q C hC) t ht

theorem binaryQuadraticRefinement_radical_negative_card
    [FiniteDimensional (ZMod 2) V] [Fintype V]
    (q : QuadraticForm (ZMod 2) V)
    (C : Submodule (ZMod 2) V) (hC : IsCompl (binaryPolarRadical q) C)
    (t : ℕ) (ht : finrank (ZMod 2) C = 2*t) :
    2 * Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
      binaryQuadraticGaussSum P.val = -((2 : ℂ)^(finrank (ZMod 2) (binaryPolarRadical q)+t))} +
        2^t = 2^(2*t) := by
  have hr : (Nat.card (binaryPolarRadical q) : ℂ) =
      (2 : ℂ)^finrank (ZMod 2) (binaryPolarRadical q) := by
    rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K := ZMod 2)]
    norm_num
  have hp : -((2 : ℂ)^t) * (Nat.card (binaryPolarRadical q) : ℂ) =
      -((2 : ℂ)^(finrank (ZMod 2) (binaryPolarRadical q)+t)) := by
    rw [hr,pow_add,neg_mul,mul_comm]
  rw [← hp,Nat.card_congr (binaryQuadraticRefinementNonzeroEquiv q C hC
    (-((2 : ℂ)^t)) (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))))]
  exact binaryQuadraticRefinement_negative_card (q.comp C.subtype)
    (binaryRadical_complement_nondegenerate q C hC) t ht

end ExactCriticalCurve.FiniteQuadratic
