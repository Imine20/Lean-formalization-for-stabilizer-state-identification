import ExactCriticalCurve.Binary.Geometry
import ExactCriticalCurve.FiniteQuadratic.Quotient

noncomputable section
namespace ExactCriticalCurve.Binary.StochasticCounting
open ExactCriticalCurve.FiniteQuadratic

abbrev RelationSpace (k : ℕ) := BinaryVector k × BinaryVector k

def relationBilinear (k : ℕ) : LinearMap.BilinForm (ZMod 2) (RelationSpace k) :=
  (binaryDotForm k).compl₁₂ (LinearMap.fst _ _ _) (LinearMap.fst _ _ _) +
    (binaryDotForm k).compl₁₂ (LinearMap.snd _ _ _) (LinearMap.snd _ _ _)

@[simp] theorem relationBilinear_apply {k : ℕ} (x y : RelationSpace k) :
    relationBilinear k x y = binaryDot x.1 y.1 + binaryDot x.2 y.2 := rfl

def relationWu (k : ℕ) : RelationSpace k := (allOnes k, allOnes k)

theorem relationBilinear_isSymm (k : ℕ) :
    LinearMap.BilinForm.IsSymm (relationBilinear k) := by
  constructor
  intro x y
  simp only [relationBilinear_apply, binaryDot_comm]

theorem relationBilinear_nondegenerate (k : ℕ) :
    LinearMap.BilinForm.Nondegenerate (relationBilinear k) := by
  intro x hx
  apply Prod.ext
  · apply binaryDotForm_nondegenerate k x.1
    intro y
    simpa [relationBilinear_apply, binaryDot] using hx (y, 0)
  · apply binaryDotForm_nondegenerate k x.2
    intro y
    simpa [relationBilinear_apply, binaryDot] using hx (0, y)

theorem binaryScalar_add_self (a : ZMod 2) : a+a=0 := by fin_cases a <;> decide

theorem relation_add_self {k : ℕ} (x : RelationSpace k) : x+x=0 := by
  ext i <;> exact binaryScalar_add_self _

theorem relationBilinear_self {k : ℕ} (x : RelationSpace k) :
    relationBilinear k x x = relationBilinear k x (relationWu k) := by
  simp only [relationBilinear_apply, relationWu, binaryDot_self_eq_dot_allOnes]

@[simp] theorem relationQuadratic_wu (k : ℕ) : relationQuadratic (relationWu k)=0 := by
  simp [relationQuadratic, relationWu]

@[simp] theorem relationQuadratic_zero (k : ℕ) : relationQuadratic (0 : RelationSpace k)=0 := by
  simp [relationQuadratic]

theorem two_mul_bitLift_neg (a : ZMod 2) : -(2 * bitLift a : ZMod 4)=2*bitLift a := by
  fin_cases a <;> decide

/-- The negative quadratic summand has the same doubled binary polarization in ZMod 4. -/
theorem relationQuadratic_add {k : ℕ} (x y : RelationSpace k) :
    relationQuadratic (x+y) = relationQuadratic x + relationQuadratic y +
      2 * bitLift (relationBilinear k x y) := by
  simp only [relationQuadratic, Prod.fst_add, Prod.snd_add, weightQuadratic_add,
    relationBilinear_apply, two_mul_bitLift_add]
  have h := two_mul_bitLift_neg (binaryDot x.2 y.2)
  linear_combination h

def wuLine (k : ℕ) : Submodule (ZMod 2) (RelationSpace k) :=
  Submodule.span (ZMod 2) {relationWu k}

def evenRelationSpace (k : ℕ) : Submodule (ZMod 2) (RelationSpace k) :=
  LinearMap.BilinForm.orthogonal (relationBilinear k) (wuLine k)

theorem mem_evenRelationSpace_iff {k : ℕ} (x : RelationSpace k) :
    x ∈ evenRelationSpace k ↔ relationBilinear k (relationWu k) x=0 := by
  constructor
  · exact fun hx => hx _ (Submodule.mem_span_singleton_self _)
  · intro hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    change relationBilinear k (a • relationWu k) x=0
    rw [map_smul, LinearMap.smul_apply, hx, smul_zero]

theorem relationBilinear_wu_wu (k : ℕ) :
    relationBilinear k (relationWu k) (relationWu k)=0 := binaryScalar_add_self _

theorem wuLine_le_evenRelationSpace (k : ℕ) : wuLine k ≤ evenRelationSpace k := by
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact (mem_evenRelationSpace_iff _).mpr (relationBilinear_wu_wu k)

/-- The ZMod 4 value is proved even before its half is used. -/
theorem relationQuadratic_even {k : ℕ} (x : evenRelationSpace k) :
    relationQuadratic x.val + relationQuadratic x.val=0 := by
  have hx : relationBilinear k x.val x.val=0 := by
    rw [relationBilinear_self, (relationBilinear_isSymm k).eq]
    exact (mem_evenRelationSpace_iff _).mp x.property
  have he := relationQuadratic_add x.val x.val
  rw [relation_add_self, relationQuadratic_zero, hx, bitLift_zero, mul_zero, add_zero] at he
  exact he.symm

/-- Integer division on the retained representative; only even inputs are inverted below. -/
def halfEven (a : ZMod 4) : ZMod 2 := (a.val / 2 : ℕ)

@[simp] theorem halfEven_zero : halfEven 0=0 := rfl

theorem two_mul_bitLift_halfEven (a : ZMod 4) (ha : a+a=0) :
    2*bitLift (halfEven a)=a := by
  fin_cases a <;> revert ha <;> decide

theorem two_mul_bitLift_injective :
    Function.Injective (fun a : ZMod 2 => (2 : ZMod 4)*bitLift a) := by
  change ∀ a b : ZMod 2, (2 : ZMod 4)*bitLift a = 2*bitLift b → a=b
  decide

theorem halfEven_eq_zero_iff (a : ZMod 4) (ha : a+a=0) : halfEven a=0 ↔ a=0 := by
  constructor
  · intro h
    have hh := two_mul_bitLift_halfEven a ha
    simpa [h] using hh.symm
  · intro h
    simp [h]

def relationHalfValue {k : ℕ} (x : evenRelationSpace k) : ZMod 2 :=
  halfEven (relationQuadratic x.val)

theorem relationHalfValue_zero_iff {k : ℕ} (x : evenRelationSpace k) :
    relationHalfValue x=0 ↔ relationQuadratic x.val=0 :=
  halfEven_eq_zero_iff _ (relationQuadratic_even x)

theorem relationHalfValue_add {k : ℕ} (x y : evenRelationSpace k) :
    relationHalfValue (x+y) = relationHalfValue x + relationHalfValue y +
      relationBilinear k x.val y.val := by
  apply two_mul_bitLift_injective
  dsimp only
  rw [two_mul_bitLift_add, two_mul_bitLift_add]
  change 2*bitLift (halfEven (relationQuadratic (x.val+y.val))) =
    2*bitLift (halfEven (relationQuadratic x.val)) +
      2*bitLift (halfEven (relationQuadratic y.val)) +
      2*bitLift (relationBilinear k x.val y.val)
  have hxy : relationQuadratic (x.val+y.val)+relationQuadratic (x.val+y.val)=0 :=
    relationQuadratic_even (x+y)
  rw [two_mul_bitLift_halfEven _ hxy,
    two_mul_bitLift_halfEven _ (relationQuadratic_even x),
    two_mul_bitLift_halfEven _ (relationQuadratic_even y)]
  exact relationQuadratic_add x.val y.val

/-- The actual F2 quadratic form on c-perp, retaining the zero set of the ZMod 4 refinement. -/
def relationHalfForm (k : ℕ) : QuadraticForm (ZMod 2) (evenRelationSpace k) where
  toFun := relationHalfValue
  toFun_smul := by
    intro a x
    fin_cases a <;> simp [relationHalfValue, halfEven, relationQuadratic]
  exists_companion' := ⟨(relationBilinear k).compl₁₂
    (evenRelationSpace k).subtype (evenRelationSpace k).subtype, relationHalfValue_add⟩

@[simp] theorem relationHalfForm_apply {k : ℕ} (x : evenRelationSpace k) :
    relationHalfForm k x = halfEven (relationQuadratic x.val) := rfl

theorem relationHalfForm_polar (k : ℕ) :
    (relationHalfForm k).polarBilin =
      (relationBilinear k).compl₁₂ (evenRelationSpace k).subtype
        (evenRelationSpace k).subtype := by
  ext x y
  change relationHalfValue (x+y)-relationHalfValue x-relationHalfValue y =
    relationBilinear k x.val y.val
  rw [relationHalfValue_add]
  ring

theorem relationHalfForm_zero_iff {k : ℕ} (x : evenRelationSpace k) :
    relationHalfForm k x=0 ↔ relationQuadratic x.val=0 := relationHalfValue_zero_iff x


/-- Full mod-four isotropy forces pairwise binary orthogonality. -/
theorem relationQuadratic_zero_pairwise {k : ℕ}
    {W : Submodule (ZMod 2) (RelationSpace k)}
    (hW : ∀ p ∈ W, relationQuadratic p=0)
    {x y : RelationSpace k} (hx : x∈W) (hy : y∈W) :
    relationBilinear k x y=0 := by
  have he := relationQuadratic_add x y
  rw [hW _ (W.add_mem hx hy), hW _ hx, hW _ hy, zero_add, zero_add] at he
  exact (two_mul_bitLift_eq_zero_iff _).mp he.symm

/-- The dimension bound needs neither stochasticity nor a physical copy-number parameter. -/
theorem finrank_le_of_relationQuadratic_zero {k : ℕ}
    (W : Submodule (ZMod 2) (RelationSpace k))
    (hW : ∀ p ∈ W, relationQuadratic p=0) :
    Module.finrank (ZMod 2) W ≤ k := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal (relationBilinear k) W :=
    fun _ hx _ hy => relationQuadratic_zero_pairwise hW hy hx
  have hd := LinearMap.BilinForm.finrank_orthogonal
    (relationBilinear_nondegenerate k) (relationBilinear_isSymm k).isRefl W
  have hb := Submodule.finrank_mono hle
  have hV : Module.finrank (ZMod 2) (RelationSpace k)=2*k := by
    simp [RelationSpace, BinaryVector, Module.finrank_prod, two_mul]
  rw [hV] at hd
  omega

theorem isEmpty_stochasticExtensions_of_nonisotropic {k : ℕ}
    (W : Submodule (ZMod 2) (RelationSpace k))
    (hW : ¬ ∀ p ∈ W, relationQuadratic p=0) :
    IsEmpty {T : StochasticLagrangian k // W≤T.carrier} :=
  ⟨fun T => hW (fun p hp => T.val.quadratic_zero p (T.property hp))⟩

theorem card_stochasticExtensions_of_nonisotropic {k : ℕ}
    (W : Submodule (ZMod 2) (RelationSpace k))
    (hW : ¬ ∀ p ∈ W, relationQuadratic p=0) :
    Nat.card {T : StochasticLagrangian k // W≤T.carrier}=0 := by
  letI := isEmpty_stochasticExtensions_of_nonisotropic W hW
  exact Nat.card_of_isEmpty

end ExactCriticalCurve.Binary.StochasticCounting
