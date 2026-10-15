import ExactCriticalCurve.Binary.RelationHalf
import Mathlib.LinearAlgebra.Dimension.RankNullity

noncomputable section
namespace ExactCriticalCurve.Binary.StochasticCounting
open ExactCriticalCurve.FiniteQuadratic

def wuDenominator (k : ℕ) : Submodule (ZMod 2) (evenRelationSpace k) :=
  (wuLine k).comap (evenRelationSpace k).subtype

abbrev RelationQuotient (k : ℕ) := evenRelationSpace k ⧸ wuDenominator k

theorem relationQuadratic_zero_wuLine {k : ℕ} {x : RelationSpace k} (hx : x∈wuLine k) :
    relationQuadratic x=0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  fin_cases a <;> simp

theorem wuDenominator_singular (k : ℕ) :
    TotallySingular (relationHalfForm k) (wuDenominator k) := by
  intro x hx
  apply (relationHalfForm_zero_iff x).mpr
  exact relationQuadratic_zero_wuLine hx

theorem wuDenominator_radical (k : ℕ) :
    ∀ u ∈ wuDenominator k, ∀ v : evenRelationSpace k,
      (relationHalfForm k).polarBilin u v=0 := by
  intro u hu v
  rw [relationHalfForm_polar]
  exact v.property u.val hu

theorem wuDenominator_eq_radical (k : ℕ) (x : evenRelationSpace k) :
    (∀ y : evenRelationSpace k, (relationHalfForm k).polarBilin x y=0) ↔
      x∈wuDenominator k := by
  constructor
  · intro hx
    have hxorth : x.val ∈ LinearMap.BilinForm.orthogonal (relationBilinear k)
        (LinearMap.BilinForm.orthogonal (relationBilinear k) (wuLine k)) := by
      intro y hy
      change relationBilinear k y x.val=0
      rw [(relationBilinear_isSymm k).eq]
      have hy' := hx ⟨y, hy⟩
      rw [relationHalfForm_polar] at hy'
      exact hy'
    rw [LinearMap.BilinForm.orthogonal_orthogonal
      (relationBilinear_nondegenerate k) (relationBilinear_isSymm k).isRefl] at hxorth
    exact hxorth
  · intro hx
    exact wuDenominator_radical k x hx

/-- The actual nondegenerate quadratic form on c-perp / span(c). -/
def relationQuotientForm (k : ℕ) : QuadraticForm (ZMod 2) (RelationQuotient k) :=
  quotientForm (relationHalfForm k) (wuDenominator k)
    (wuDenominator_singular k) (wuDenominator_radical k)

@[simp] theorem relationQuotientForm_mk {k : ℕ} (x : evenRelationSpace k) :
    relationQuotientForm k (Submodule.Quotient.mk x)=halfEven (relationQuadratic x.val) := rfl

theorem relationQuotientForm_mk_zero_iff {k : ℕ} (x : evenRelationSpace k) :
    relationQuotientForm k (Submodule.Quotient.mk x)=0 ↔ relationQuadratic x.val=0 :=
  relationHalfForm_zero_iff x

theorem relationQuotientForm_nondegenerate (k : ℕ) :
    LinearMap.BilinForm.Nondegenerate (relationQuotientForm k).polarBilin :=
  quotientForm_nondegenerate _ _ _ _ (fun x hx => (wuDenominator_eq_radical k x).mp hx)

theorem relationWu_ne_zero {k : ℕ} (hk : 1≤k) : relationWu k ≠ 0 := by
  intro he
  have h := congrFun (congrArg Prod.fst he) ⟨0, by omega⟩
  norm_num [relationWu, allOnes] at h

theorem finrank_wuLine {k : ℕ} (hk : 1≤k) :
    Module.finrank (ZMod 2) (wuLine k)=1 := finrank_span_singleton (relationWu_ne_zero hk)

theorem finrank_wuDenominator {k : ℕ} (hk : 1≤k) :
    Module.finrank (ZMod 2) (wuDenominator k)=1 := by
  unfold wuDenominator
  rw [(Submodule.comapSubtypeEquivOfLe (wuLine_le_evenRelationSpace k)).finrank_eq]
  exact finrank_wuLine hk

theorem finrank_evenRelationSpace {k : ℕ} (hk : 1≤k) :
    Module.finrank (ZMod 2) (evenRelationSpace k)=2*k-1 := by
  change Module.finrank (ZMod 2)
    (LinearMap.BilinForm.orthogonal (relationBilinear k) (wuLine k))=_
  rw [LinearMap.BilinForm.finrank_orthogonal
    (relationBilinear_nondegenerate k) (relationBilinear_isSymm k).isRefl, finrank_wuLine hk]
  simp [RelationSpace, BinaryVector, Module.finrank_prod, two_mul]

theorem finrank_relationQuotient {k : ℕ} (hk : 1≤k) :
    Module.finrank (ZMod 2) (RelationQuotient k)=2*(k-1) := by
  have hd := (wuDenominator k).finrank_quotient_add_finrank
  rw [finrank_wuDenominator hk, finrank_evenRelationSpace hk] at hd
  change Module.finrank (ZMod 2) (RelationQuotient k)+1=2*k-1 at hd
  omega

def diagonalMap (k : ℕ) : BinaryVector k →ₗ[ZMod 2] RelationSpace k :=
  (LinearMap.id : BinaryVector k →ₗ[ZMod 2] BinaryVector k).prod LinearMap.id

def diagonal (k : ℕ) : Submodule (ZMod 2) (RelationSpace k) :=
  LinearMap.range (diagonalMap k)

theorem finrank_diagonal (k : ℕ) : Module.finrank (ZMod 2) (diagonal k)=k := by
  have hi : Function.Injective (diagonalMap k) := fun x y h => congrArg Prod.fst h
  rw [diagonal, LinearMap.finrank_range_of_inj hi]
  simp [BinaryVector]

theorem wuLine_le_diagonal (k : ℕ) : wuLine k ≤ diagonal k := by
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  exact ⟨allOnes k, rfl⟩

theorem diagonal_le_evenRelationSpace (k : ℕ) : diagonal k ≤ evenRelationSpace k := by
  rintro x ⟨v, rfl⟩
  apply (mem_evenRelationSpace_iff _).mpr
  exact binaryScalar_add_self _

theorem relationQuadratic_zero_diagonal {k : ℕ} {x : RelationSpace k}
    (hx : x∈diagonal k) : relationQuadratic x=0 := by
  obtain ⟨v, rfl⟩ := hx
  simp [relationQuadratic, diagonalMap]

def quotientDiagonal (k : ℕ) : Submodule (ZMod 2) (RelationQuotient k) :=
  ((diagonal k).comap (evenRelationSpace k).subtype).map (wuDenominator k).mkQ

theorem quotientDiagonal_singular (k : ℕ) :
    TotallySingular (relationQuotientForm k) (quotientDiagonal k) := by
  rintro z ⟨x, hx, rfl⟩
  exact (relationQuotientForm_mk_zero_iff x).mpr (relationQuadratic_zero_diagonal hx)

theorem finrank_quotientDiagonal_add {k : ℕ} (hk : 1≤k) :
    Module.finrank (ZMod 2) (quotientDiagonal k)+1=k := by
  let N := (diagonal k).comap (evenRelationSpace k).subtype
  let p := wuDenominator k
  have hpN : p≤N := fun _ hx => wuLine_le_diagonal k hx
  have hker : LinearMap.ker (p.mkQ.domRestrict N)=p.comap N.subtype := by
    ext x
    simp
  have hr := (p.mkQ.domRestrict N).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, hker,
    (Submodule.comapSubtypeEquivOfLe hpN).finrank_eq] at hr
  have hn : Module.finrank (ZMod 2) N=k := by
    rw [(Submodule.comapSubtypeEquivOfLe (diagonal_le_evenRelationSpace k)).finrank_eq,
      finrank_diagonal]
  change Module.finrank (ZMod 2) (quotientDiagonal k)+
    Module.finrank (ZMod 2) (wuDenominator k)=Module.finrank (ZMod 2) N at hr
  rwa [finrank_wuDenominator hk, hn] at hr

theorem finrank_quotientDiagonal {k : ℕ} (hk : 1≤k) :
    Module.finrank (ZMod 2) (quotientDiagonal k)=k-1 := by
  have := finrank_quotientDiagonal_add hk
  omega

end ExactCriticalCurve.Binary.StochasticCounting
