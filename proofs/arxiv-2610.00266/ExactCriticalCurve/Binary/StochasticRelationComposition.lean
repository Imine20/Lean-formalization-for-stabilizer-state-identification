import ExactCriticalCurve.Binary.RelationDefects
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! # Actual composition and intermediate fibers of stochastic relations -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000
open Classical Module
namespace ExactCriticalCurve.Binary
variable {k : ℕ}

/-- The difference of the two intermediate coordinates. -/
def relationMiddleDifference (T U : StochasticLagrangian k) :
    (T.carrier × U.carrier) →ₗ[ZMod 2] BinaryVector k where
  toFun p := p.1.val.2 - p.2.val.1
  map_add' p q := by
    change (p.1.val.2 + q.1.val.2) - (p.2.val.1 + q.2.val.1) =
      (p.1.val.2 - p.2.val.1) + (q.1.val.2 - q.2.val.1)
    abel
  map_smul' a p := by
    change a • p.1.val.2 - a • p.2.val.1 = a • (p.1.val.2 - p.2.val.1)
    exact (smul_sub a _ _).symm

/-- Pairs of actual relation elements whose middle coordinates agree. -/
abbrev RelationMatching (T U : StochasticLagrangian k) :=
  LinearMap.ker (relationMiddleDifference T U)

/-- Forget the matching intermediate coordinate and keep the two endpoints. -/
def relationOuterMap (T U : StochasticLagrangian k) :
    RelationMatching T U →ₗ[ZMod 2] (BinaryVector k × BinaryVector k) where
  toFun p := (p.val.1.val.1, p.val.2.val.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Composition uses an actual intermediate vector. -/
def relationComposition (T U : StochasticLagrangian k) :
    Submodule (ZMod 2) (BinaryVector k × BinaryVector k) :=
  LinearMap.range (relationOuterMap T U)

theorem mem_relationComposition (T U : StochasticLagrangian k)
    (x z : BinaryVector k) :
    (x,z) ∈ relationComposition T U ↔
      ∃ y : BinaryVector k, (x,y) ∈ T.carrier ∧ (y,z) ∈ U.carrier := by
  constructor
  · rintro ⟨p, hp⟩
    have hx : p.val.1.val.1 = x := congrArg Prod.fst hp
    have hz : p.val.2.val.2 = z := congrArg Prod.snd hp
    have hm : p.val.1.val.2 = p.val.2.val.1 := sub_eq_zero.mp p.property
    refine ⟨p.val.1.val.2, ?_, ?_⟩
    · rw [← hx]
      exact p.val.1.property
    · rw [hm, ← hz]
      exact p.val.2.property
  · rintro ⟨y, ht, hu⟩
    exact ⟨⟨(⟨(x,y),ht⟩,⟨(y,z),hu⟩), sub_self y⟩, rfl⟩

/-- The orthogonal of the actual intermediate-difference image is exactly
the intersection of the two actual defects. -/
theorem relationMiddleDifference_range_orthogonal (T U : StochasticLagrangian k) :
    orthogonal (LinearMap.range (relationMiddleDifference T U)) =
      T.rightDefect ⊓ U.leftDefect := by
  ext x
  constructor
  · intro hx
    constructor
    · rw [← T.orthogonal_rightImage]
      rintro y ⟨t, ht, rfl⟩
      have h := hx (relationMiddleDifference T U (⟨t,ht⟩,0))
        ⟨(⟨t,ht⟩,0),rfl⟩
      change binaryDot (t.2 - 0) x = 0 at h
      change binaryDot t.2 x = 0
      simpa only [sub_zero] using h
    · rw [← U.orthogonal_leftImage]
      rintro y ⟨u, hu, rfl⟩
      have h := hx (relationMiddleDifference T U (0,-⟨u,hu⟩))
        ⟨(0,-⟨u,hu⟩),rfl⟩
      change binaryDot (0 - -u.1) x = 0 at h
      change binaryDot u.1 x = 0
      simpa only [zero_sub, neg_neg] using h
  · rintro ⟨ht,hu⟩ y ⟨p,rfl⟩
    have ht' : binaryDot p.1.val.2 x = 0 := by
      rw [← T.orthogonal_rightImage] at ht
      exact ht p.1.val.2 ⟨p.1.val,p.1.property,rfl⟩
    have hu' : binaryDot p.2.val.1 x = 0 := by
      rw [← U.orthogonal_leftImage] at hu
      exact hu p.2.val.1 ⟨p.2.val,p.2.property,rfl⟩
    change binaryDot (p.1.val.2 - p.2.val.1) x = 0
    change (binaryDotForm k (p.1.val.2 - p.2.val.1)) x = 0
    rw [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.mpr (ht'.trans hu'.symm)

/-- The kernel of endpoint projection is the actual shared middle defect. -/
def relationOuterKernelEquiv (T U : StochasticLagrangian k) :
    ↥(T.rightDefect ⊓ U.leftDefect) ≃ₗ[ZMod 2] LinearMap.ker (relationOuterMap T U) where
  toFun d := ⟨⟨(⟨(0,d.val),d.property.1⟩,⟨(d.val,0),d.property.2⟩),
    sub_self d.val⟩,rfl⟩
  invFun p := by
    have hx : p.val.val.1.val.1 = 0 := congrArg Prod.fst p.property
    have hz : p.val.val.2.val.2 = 0 := congrArg Prod.snd p.property
    have hm : p.val.val.1.val.2 = p.val.val.2.val.1 := sub_eq_zero.mp p.val.property
    refine ⟨p.val.val.1.val.2, ?_, ?_⟩
    · change (0,p.val.val.1.val.2) ∈ T.carrier
      rw [← hx]
      exact p.val.val.1.property
    · change (p.val.val.1.val.2,0) ∈ U.carrier
      rw [hm, ← hz]
      exact p.val.val.2.property
  left_inv d := rfl
  right_inv p := by
    have hx : p.val.val.1.val.1 = 0 := congrArg Prod.fst p.property
    have hz : p.val.val.2.val.2 = 0 := congrArg Prod.snd p.property
    have hm : p.val.val.1.val.2 = p.val.val.2.val.1 := sub_eq_zero.mp p.val.property
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (Prod.ext hx.symm rfl)
    · exact Subtype.ext (Prod.ext hm hz.symm)
  map_add' d e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Subtype.ext (Prod.ext (add_zero _).symm rfl))
      (Subtype.ext (Prod.ext rfl (add_zero _).symm))
  map_smul' a d := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Subtype.ext (Prod.ext (smul_zero a).symm rfl))
      (Subtype.ext (Prod.ext rfl (smul_zero a).symm))

/-- The genuine matching space has k plus the shared-defect dimension. -/
theorem relationMatching_finrank (T U : StochasticLagrangian k) :
    finrank (ZMod 2) (RelationMatching T U) =
      k + finrank (ZMod 2) ↥(T.rightDefect ⊓ U.leftDefect) := by
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal
    (binaryDotForm_isRefl k) (LinearMap.range (relationMiddleDifference T U))
  rw [(binaryDotForm k).orthogonal_top_eq_bot
    (binaryDotForm_nondegenerate k) (binaryDotForm_isRefl k),
    inf_bot_eq, finrank_bot, add_zero] at h
  change finrank (ZMod 2) (LinearMap.range (relationMiddleDifference T U)) +
    finrank (ZMod 2) (orthogonal (LinearMap.range (relationMiddleDifference T U))) =
      finrank (ZMod 2) (BinaryVector k) at h
  rw [relationMiddleDifference_range_orthogonal] at h
  have hv : finrank (ZMod 2) (BinaryVector k) = k := by simp [BinaryVector]
  rw [hv] at h
  have hr := (relationMiddleDifference T U).finrank_range_add_finrank_ker
  rw [Module.finrank_prod, T.finrank_eq, U.finrank_eq] at hr
  change finrank (ZMod 2) (LinearMap.range (relationMiddleDifference T U)) +
    finrank (ZMod 2) (RelationMatching T U) = k + k at hr
  omega

/-- No stable range or transversality is required for the composed dimension. -/
theorem relationComposition_finrank (T U : StochasticLagrangian k) :
    finrank (ZMod 2) (relationComposition T U) = k := by
  have h := (relationOuterMap T U).finrank_range_add_finrank_ker
  rw [← (relationOuterKernelEquiv T U).finrank_eq, relationMatching_finrank] at h
  change finrank (ZMod 2) (relationComposition T U) +
    finrank (ZMod 2) ↥(T.rightDefect ⊓ U.leftDefect) =
      k + finrank (ZMod 2) ↥(T.rightDefect ⊓ U.leftDefect) at h
  omega

/-- Actual composition is again a full mod-four stochastic Lagrangian. -/
def stochasticLagrangianComposition (T U : StochasticLagrangian k) :
    StochasticLagrangian k where
  carrier := relationComposition T U
  finrank_eq := relationComposition_finrank T U
  quadratic_zero := by
    rintro ⟨x,z⟩ hp
    obtain ⟨y,ht,hu⟩ := (mem_relationComposition T U x z).mp hp
    have ht' := T.quadratic_zero (x,y) ht
    have hu' := U.quadratic_zero (y,z) hu
    change weightQuadratic x - weightQuadratic y = 0 at ht'
    change weightQuadratic y - weightQuadratic z = 0 at hu'
    exact sub_eq_zero.mpr ((sub_eq_zero.mp ht').trans (sub_eq_zero.mp hu'))
  allOnes_mem := (mem_relationComposition T U _ _).mpr
    ⟨allOnes k,T.allOnes_mem,U.allOnes_mem⟩

/-- The genuine intermediate vectors for a fixed pair of endpoints. -/
abbrev RelationMiddleFiber (T U : StochasticLagrangian k) (x z : BinaryVector k) :=
  {y : BinaryVector k // (x,y) ∈ T.carrier ∧ (y,z) ∈ U.carrier}

/-- Every nonempty middle fiber is the actual translate of the shared defect. -/
theorem relationMiddleFiber_iff (T U : StochasticLagrangian k)
    (x z y₀ : BinaryVector k) (ht₀ : (x,y₀) ∈ T.carrier) (hu₀ : (y₀,z) ∈ U.carrier)
    (y : BinaryVector k) :
    ((x,y) ∈ T.carrier ∧ (y,z) ∈ U.carrier) ↔
      y - y₀ ∈ T.rightDefect ⊓ U.leftDefect := by
  constructor
  · rintro ⟨ht,hu⟩
    constructor
    · have h := T.carrier.sub_mem ht ht₀
      simpa only [Prod.mk_sub_mk, sub_self] using h
    · have h := U.carrier.sub_mem hu hu₀
      simpa only [Prod.mk_sub_mk, sub_self] using h
  · rintro ⟨ht,hu⟩
    have hy : y₀ + (y-y₀) = y := by abel
    constructor
    · have h := T.carrier.add_mem ht₀ ht
      change (x+0,y₀+(y-y₀)) ∈ T.carrier at h
      simpa only [add_zero,hy] using h
    · have h := U.carrier.add_mem hu₀ hu
      change (y₀+(y-y₀),z+0) ∈ U.carrier at h
      simpa only [add_zero,hy] using h

/-- Translation by an actual intermediate solution is a bijection. -/
def relationMiddleFiberEquiv (T U : StochasticLagrangian k)
    (x z y₀ : BinaryVector k) (ht₀ : (x,y₀) ∈ T.carrier) (hu₀ : (y₀,z) ∈ U.carrier) :
    ↥(T.rightDefect ⊓ U.leftDefect) ≃ RelationMiddleFiber T U x z where
  toFun d := ⟨y₀+d.val, (relationMiddleFiber_iff T U x z y₀ ht₀ hu₀ _).mpr
    (by simpa only [add_sub_cancel_left] using d.property)⟩
  invFun y := ⟨y.val-y₀, (relationMiddleFiber_iff T U x z y₀ ht₀ hu₀ y.val).mp y.property⟩
  left_inv d := by ext; simp
  right_inv y := by ext; simp

/-- Exact middle-fiber cardinality, including empty fibers and zero dimension. -/
theorem relationMiddleFiber_card (T U : StochasticLagrangian k) (x z : BinaryVector k) :
    Nat.card (RelationMiddleFiber T U x z) =
      if (x,z) ∈ relationComposition T U
      then 2 ^ finrank (ZMod 2) ↥(T.rightDefect ⊓ U.leftDefect) else 0 := by
  by_cases h : (x,z) ∈ relationComposition T U
  · rw [if_pos h]
    obtain ⟨y₀,ht₀,hu₀⟩ := (mem_relationComposition T U x z).mp h
    rw [Nat.card_congr (relationMiddleFiberEquiv T U x z y₀ ht₀ hu₀).symm,
      Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  · rw [if_neg h]
    letI : IsEmpty (RelationMiddleFiber T U x z) :=
      ⟨fun y => h ((mem_relationComposition T U x z).mpr ⟨y.val,y.property⟩)⟩
    simp [Nat.card_eq_fintype_card]

end ExactCriticalCurve.Binary
