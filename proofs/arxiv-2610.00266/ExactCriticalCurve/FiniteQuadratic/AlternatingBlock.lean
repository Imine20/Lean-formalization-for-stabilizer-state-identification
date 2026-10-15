import ExactCriticalCurve.FiniteQuadratic.AlternatingRankParity
import ExactCriticalCurve.FiniteQuadratic.ZeroCounting
import Mathlib.LinearAlgebra.BilinearForm.Hom

/-! Actual two-coordinate block decomposition of nondegenerate alternating forms. -/
noncomputable section
namespace ExactCriticalCurve.FiniteQuadratic
variable {K : Type*} [AddCommGroup K] [Module (ZMod 2) K]

abbrev NondegenerateAlternatingForm (K : Type*) [AddCommGroup K] [Module (ZMod 2) K] :=
  {A : LinearMap.BilinForm (ZMod 2) K // A.IsAlt ∧ A.Nondegenerate}

/-- The five actual bilinear terms of a form with prescribed first coordinate row. -/
def alternatingBlockForm (h : Module.Dual (ZMod 2) K)
    (C : LinearMap.BilinForm (ZMod 2) K) :
    LinearMap.BilinForm (ZMod 2) (ZMod 2 × (ZMod 2 × K)) :=
  let α := LinearMap.fst (ZMod 2) (ZMod 2) (ZMod 2 × K)
  let τ := LinearMap.snd (ZMod 2) (ZMod 2) (ZMod 2 × K)
  let β := (LinearMap.fst (ZMod 2) (ZMod 2) K).comp τ
  let π := (LinearMap.snd (ZMod 2) (ZMod 2) K).comp τ
  LinearMap.BilinForm.linMulLin α β + LinearMap.BilinForm.linMulLin β α +
    LinearMap.BilinForm.linMulLin β (h.comp π) +
    LinearMap.BilinForm.linMulLin (h.comp π) β + C.comp π π

@[simp] theorem alternatingBlockForm_apply (h : Module.Dual (ZMod 2) K)
    (C : LinearMap.BilinForm (ZMod 2) K) (x y : ZMod 2 × (ZMod 2 × K)) :
    alternatingBlockForm h C x y = x.1*y.2.1 + x.2.1*y.1 +
      x.2.1*h y.2.2 + h x.2.2*y.2.1 + C x.2.2 y.2.2 := rfl

theorem alternatingBlockForm_isAlt (h : Module.Dual (ZMod 2) K)
    (C : LinearMap.BilinForm (ZMod 2) K) (hC : C.IsAlt) :
    (alternatingBlockForm h C).IsAlt := by
  intro x
  simp only [alternatingBlockForm_apply, hC.self_eq_zero, add_zero]
  rw [mul_comm x.2.1 x.1, mul_comm (h x.2.2) x.2.1,
    CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]

theorem alternatingBlockForm_nondegenerate_iff (h : Module.Dual (ZMod 2) K)
    (C : LinearMap.BilinForm (ZMod 2) K) :
    (alternatingBlockForm h C).Nondegenerate ↔ C.Nondegenerate := by
  constructor
  · intro hA k hk
    have hz : (h k, (0, k)) = (0 : ZMod 2 × (ZMod 2 × K)) := by
      apply hA
      intro y
      simp [hk, CharTwo.add_self_eq_zero]
    exact congrArg (fun x : ZMod 2 × (ZMod 2 × K) => x.2.2) hz
  · intro hC x hx
    have hb : x.2.1 = 0 := by simpa using hx (1,(0,0))
    have hk : x.2.2 = 0 := by
      apply hC
      intro k
      simpa [hb] using hx (0,(0,k))
    have ha : x.1 = 0 := by simpa [hb,hk] using hx (0,(1,0))
    exact Prod.ext ha (Prod.ext hb hk)

@[simp] theorem alternatingBlockForm_first_row (h : Module.Dual (ZMod 2) K)
    (C : LinearMap.BilinForm (ZMod 2) K) (x : ZMod 2 × (ZMod 2 × K)) :
    alternatingBlockForm h C (1,(0,0)) x = x.2.1 := by simp

/-- The actual remaining row on K. -/
def alternatingBlockRow (A : LinearMap.BilinForm (ZMod 2) (ZMod 2 × (ZMod 2 × K))) :
    Module.Dual (ZMod 2) K :=
  (A (0,(1,0))).comp ((LinearMap.inr (ZMod 2) (ZMod 2) (ZMod 2 × K)).comp
    (LinearMap.inr (ZMod 2) (ZMod 2) K))

/-- The actual restriction to K. -/
def alternatingBlockRestriction
    (A : LinearMap.BilinForm (ZMod 2) (ZMod 2 × (ZMod 2 × K))) :
    LinearMap.BilinForm (ZMod 2) K :=
  let j := (LinearMap.inr (ZMod 2) (ZMod 2) (ZMod 2 × K)).comp
    (LinearMap.inr (ZMod 2) (ZMod 2) K)
  A.comp j j

@[simp] theorem alternatingBlockRow_block (h : Module.Dual (ZMod 2) K)
    (C : LinearMap.BilinForm (ZMod 2) K) :
    alternatingBlockRow (alternatingBlockForm h C) = h := by
  apply LinearMap.ext
  intro k
  change alternatingBlockForm h C (0,(1,0)) (0,(0,k)) = h k
  simp

@[simp] theorem alternatingBlockRestriction_block (h : Module.Dual (ZMod 2) K)
    (C : LinearMap.BilinForm (ZMod 2) K) :
    alternatingBlockRestriction (alternatingBlockForm h C) = C := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change alternatingBlockForm h C (0,(0,x)) (0,(0,y)) = C x y
  simp

theorem alternatingBlockForm_reconstruct
    (A : LinearMap.BilinForm (ZMod 2) (ZMod 2 × (ZMod 2 × K))) (hA : A.IsAlt)
    (hr : ∀ x, A (1,(0,0)) x = x.2.1) :
    alternatingBlockForm (alternatingBlockRow A) (alternatingBlockRestriction A) = A := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  have hx : x = x.1 • (1,(0,0)) + x.2.1 • (0,(1,0)) + (0,(0,x.2.2)) := by
    ext <;> simp
  have hy : y = y.1 • (1,(0,0)) + y.2.1 • (0,(1,0)) + (0,(0,y.2.2)) := by
    ext <;> simp
  have hs := binaryAlternating_isSymm A hA
  have h10 : A (0,(1,0)) (1,(0,0)) = 1 := by rw [hs.eq, hr]
  have hk0 : A (0,(0,x.2.2)) (1,(0,0)) = 0 := by rw [hs.eq, hr]
  have hk1 : A (0,(0,x.2.2)) (0,(1,0)) = alternatingBlockRow A x.2.2 := by
    rw [hs.eq]; rfl
  conv_rhs => rw [hx,hy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hr, h10, hk0, hk1, hA.self_eq_zero]
  simp only [alternatingBlockForm_apply]
  simp only [alternatingBlockRow, alternatingBlockRestriction, LinearMap.comp_apply,
    LinearMap.inr_apply, LinearMap.BilinForm.comp_apply]
  ring

/-- Actual fixed-first-row nondegenerate alternating forms, with no omitted constraints. -/
def alternatingBlockFiberEquiv :
    {A : NondegenerateAlternatingForm (ZMod 2 × (ZMod 2 × K)) //
      ∀ x, A.val (1,(0,0)) x = x.2.1} ≃
      Module.Dual (ZMod 2) K × NondegenerateAlternatingForm K where
  toFun A := ⟨alternatingBlockRow A.val.val,
    alternatingBlockRestriction A.val.val,
    (fun k => A.val.property.1 (0,(0,k))), by
      apply (alternatingBlockForm_nondegenerate_iff _ _).mp
      rw [alternatingBlockForm_reconstruct _ A.val.property.1 A.property]
      exact A.val.property.2⟩
  invFun p := ⟨⟨alternatingBlockForm p.1 p.2.val,
    alternatingBlockForm_isAlt _ _ p.2.property.1,
    (alternatingBlockForm_nondegenerate_iff _ _).mpr p.2.property.2⟩,
    alternatingBlockForm_first_row _ _⟩
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    exact alternatingBlockForm_reconstruct _ A.val.property.1 A.property
  right_inv p := by
    apply Prod.ext
    · exact alternatingBlockRow_block _ _
    · apply Subtype.ext
      exact alternatingBlockRestriction_block _ _

end ExactCriticalCurve.FiniteQuadratic
