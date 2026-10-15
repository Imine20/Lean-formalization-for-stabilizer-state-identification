import ExactCriticalCurve.FiniteQuadratic.AlternatingBlock
import ExactCriticalCurve.Counting.BinaryGaussian

/-! Decompose actual alternating forms by a nonzero first functional. -/
noncomputable section
namespace ExactCriticalCurve.FiniteQuadratic
variable {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Coordinate transport acts on the actual alternating nondegenerate subtype. -/
def nondegenerateAlternatingCongr (e : U ≃ₗ[ZMod 2] V) :
    NondegenerateAlternatingForm U ≃ NondegenerateAlternatingForm V := by
  refine (LinearMap.BilinForm.congr e).toEquiv.subtypeEquiv ?_
  intro A
  constructor
  · rintro ⟨hA,hAn⟩
    exact ⟨fun x => hA.self_eq_zero (e.symm x), hAn.congr e⟩
  · rintro ⟨hA,hAn⟩
    refine ⟨?_, (LinearMap.BilinForm.nondegenerate_congr_iff e).mp hAn⟩
    intro x
    have hh := hA.self_eq_zero (e x)
    change A (e.symm (e x)) (e.symm (e x)) = 0 at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh

/-- Split off a chosen vector on which the nonzero functional is one. -/
def binaryFunctionalSplit (l : Module.Dual (ZMod 2) U) (v : U) (hv : l v = 1) :
    U ≃ₗ[ZMod 2] (ZMod 2 × LinearMap.ker l) where
  toFun u := (l u, ⟨u - l u • v, by simp [LinearMap.mem_ker, hv]⟩)
  invFun p := p.1 • v + p.2.val
  left_inv u := by simp
  right_inv p := by
    apply Prod.ext
    · simp [hv, LinearMap.mem_ker.mp p.2.property]
    · apply Subtype.ext
      simp [hv, LinearMap.mem_ker.mp p.2.property]
  map_add' x y := by
    apply Prod.ext
    · exact map_add l x y
    · apply Subtype.ext
      change x+y-l (x+y) • v = (x-l x • v)+(y-l y • v)
      simp only [map_add, add_smul]
      abel
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul l c x
    · apply Subtype.ext
      simp [map_smul, smul_sub, smul_smul]

/-- The first functional is the actual row at (1,0), restricted to U. -/
def alternatingFirstFunctional
    (A : NondegenerateAlternatingForm (ZMod 2 × U)) :
    {l : Module.Dual (ZMod 2) U // l ≠ 0} :=
  ⟨(A.val (1,0)).comp (LinearMap.inr (ZMod 2) (ZMod 2) U), by
    intro hz
    have he : (1,0) = (0 : ZMod 2 × U) := by
      apply A.property.2
      rintro ⟨a,u⟩
      have hu : A.val (1,0) (0,u) = 0 :=
        congrArg (fun l : Module.Dual (ZMod 2) U => l u) hz
      have hd : (a,u) = a • (1,0) + (0,u) := by ext <;> simp
      rw [hd, map_add, map_smul, A.property.1.self_eq_zero, hu]
      simp
    exact one_ne_zero (congrArg Prod.fst he)⟩

theorem alternatingFirstFunctional_row
    (A : NondegenerateAlternatingForm (ZMod 2 × U)) (x : ZMod 2 × U) :
    A.val (1,0) x = (alternatingFirstFunctional A).val x.2 := by
  have hx : x = x.1 • (1,0) + (0,x.2) := by ext <;> simp
  conv_lhs => rw [hx]
  simp only [map_add, map_smul, A.property.1.self_eq_zero, smul_zero, zero_add]
  rfl

/-- A first-functional fiber is exactly the fixed-first-row block fiber after coordinate splitting. -/
def alternatingFirstFiberBlockEquiv
    (l : {l : Module.Dual (ZMod 2) U // l ≠ 0}) (v : U) (hv : l.val v = 1) :
    {A : NondegenerateAlternatingForm (ZMod 2 × U) // alternatingFirstFunctional A = l} ≃
      {A : NondegenerateAlternatingForm (ZMod 2 × (ZMod 2 × LinearMap.ker l.val)) //
        ∀ x, A.val (1,(0,0)) x = x.2.1} := by
  let e := LinearEquiv.prodCongr (LinearEquiv.refl (ZMod 2) (ZMod 2))
    (binaryFunctionalSplit l.val v hv)
  refine (nondegenerateAlternatingCongr e).subtypeEquiv ?_
  intro A
  change alternatingFirstFunctional A = l ↔
    ∀ x, A.val (e.symm (1,(0,0))) (e.symm x) = x.2.1
  have he0 : e.symm (1,(0,0)) = (1,0) := by
    change (1, (0 : ZMod 2) • v + (0 : U)) = (1,0)
    simp
  rw [he0]
  constructor
  · intro h x
    rw [alternatingFirstFunctional_row, h]
    change l.val (x.2.1 • v + x.2.2.val) = x.2.1
    simp [hv, LinearMap.mem_ker.mp x.2.2.property]
  · intro h
    apply Subtype.ext
    apply LinearMap.ext
    intro u
    have hu := h (e (0,u))
    rw [LinearEquiv.symm_apply_apply] at hu
    exact hu

/-- Every actual first-functional fiber is a dual vector and an actual smaller nondegenerate form. -/
def alternatingFirstFiberEquiv
    (l : {l : Module.Dual (ZMod 2) U // l ≠ 0}) :
    {A : NondegenerateAlternatingForm (ZMod 2 × U) // alternatingFirstFunctional A = l} ≃
      Module.Dual (ZMod 2) (LinearMap.ker l.val) ×
        NondegenerateAlternatingForm (LinearMap.ker l.val) :=
  (alternatingFirstFiberBlockEquiv l
    (Classical.choose (binaryLinear_surjective_of_ne_zero l.val l.property 1))
    (Classical.choose_spec (binaryLinear_surjective_of_ne_zero l.val l.property 1))).trans
    alternatingBlockFiberEquiv

/-- The full decomposition uses actual fibers of the first functional. -/
def nondegenerateAlternatingFirstEquiv :
    NondegenerateAlternatingForm (ZMod 2 × U) ≃
      Σ l : {l : Module.Dual (ZMod 2) U // l ≠ 0},
        Module.Dual (ZMod 2) (LinearMap.ker l.val) ×
          NondegenerateAlternatingForm (LinearMap.ker l.val) :=
  (Equiv.sigmaFiberEquiv alternatingFirstFunctional).symm.trans
    (Equiv.sigmaCongrRight alternatingFirstFiberEquiv)

end ExactCriticalCurve.FiniteQuadratic
