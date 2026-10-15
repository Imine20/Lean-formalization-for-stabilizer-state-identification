import ExactCriticalCurve.FiniteQuadratic.OrdinaryWittCoordinates
import ExactCriticalCurve.Foundations.BinaryAlternatingCard

/-! Actual singular graph sections and their free alternating parameters. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace
open Binary Binary.StochasticCounting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable (D : ModFourQuadraticSpace V)
variable {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U) (hw : D.wu ∉ U)
variable (b : Basis (Fin d) (ZMod 2) U)

theorem ordinaryCoordinates_pairing (a c a' c' : Fin d → ZMod 2)
    (x y : D.coreSpace U hw b) :
    D.pairing (D.ordinaryCoordinates U hU hw b (a,x,c))
      (D.ordinaryCoordinates U hU hw b (a',y,c')) =
      D.pairing x.val y.val+(∑ i,a i*c' i)+(∑ i,a' i*c i) := by
  change D.pairing (primalSum U b a+x.val+D.dualSum U hw b c)
    (primalSum U b a'+y.val+D.dualSum U hw b c')=_
  have hxP : D.pairing x.val (primalSum U b a')=0 := by
    rw [D.symmetric.eq,D.primalSum_pairing,D.core_primalPair]; simp
  have hxQ : D.pairing x.val (D.dualSum U hw b c')=0 := by
    rw [D.symmetric.eq,D.dualSum_pairing,D.core_dualPair]; simp
  calc
    _ = D.pairing (primalSum U b a) (primalSum U b a'+y.val+D.dualSum U hw b c')+
        D.pairing x.val (primalSum U b a'+y.val+D.dualSum U hw b c')+
        D.pairing (D.dualSum U hw b c) (primalSum U b a'+y.val+D.dualSum U hw b c') := by
      simp only [map_add,LinearMap.add_apply]
      abel
    _ = (∑ i,a i*c' i)+D.pairing x.val y.val+(∑ i,c i*a' i) := by
      rw [D.primalSum_pairing,D.dualSum_pairing,D.coordinate_primalPair U hU,
        D.coordinate_dualPair U hU,map_add,map_add,hxP,hxQ,zero_add,add_zero]
    _ = _ := by simp_rw [mul_comm (c _)]; abel

abbrev CoreEven := D.coreEvenSpace U hU hw b

/-- An actual linear section of the pairing projection with singular image. -/
def SingularSection :=
  {f : (Fin d → ZMod 2) →ₗ[ZMod 2] V //
    (∀ x,D.primalPair U b (f x)=x) ∧ ∀ x,D.quadratic (f x)=0}

def graphCoefficient
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) (j i : Fin d) : ZMod 2 :=
  if j=i then halfEven (D.quadratic (L (Pi.single i 1)).val.val)
  else if j < i then D.pairing (L (Pi.single i 1)).val.val (L (Pi.single j 1)).val.val
  else 0

def graphVector
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) (i : Fin d) : V :=
  D.ordinaryCoordinates U hU hw b
    (fun j => D.graphCoefficient U hU hw b L j i,
      (L (Pi.single i 1)).val,Pi.single i 1)

theorem graphVector_pair
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) (i : Fin d) :
    D.primalPair U b (D.graphVector U hU hw b L i)=Pi.single i 1 :=
  D.coordinate_primalPair U hU hw b _ _ _

theorem graphVector_core
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) (i : Fin d) :
    D.coreResidual U hw b (D.graphVector U hU hw b L i)=(L (Pi.single i 1)).val.val :=
  D.coordinate_residual U hU hw b _ _ _

theorem graphVector_quadratic
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) (i : Fin d) :
    D.quadratic (D.graphVector U hU hw b L i)=0 := by
  rw [graphVector,D.ordinaryCoordinates_quadratic U hU]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have he : D.pairing D.wu (L (Pi.single i 1)).val.val=0 := (L (Pi.single i 1)).property
  simp only [graphCoefficient,ite_true]
  rw [two_mul_bitLift_halfEven _ (D.quadratic_even_of_wu_orthogonal he)]
  exact D.quadratic_even_of_wu_orthogonal he

theorem graphVector_pairing
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) (i j : Fin d) :
    D.pairing (D.graphVector U hU hw b L i) (D.graphVector U hU hw b L j)=0 := by
  rw [graphVector,graphVector,D.ordinaryCoordinates_pairing U hU]
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases he : i=j
  · subst j
    rw [D.characteristic]
    have he : D.pairing D.wu (L (Pi.single i 1)).val.val=0 := (L (Pi.single i 1)).property
    rw [he,zero_add,binaryScalar_add_self]
  · rcases lt_or_gt_of_ne he with hij|hji
    · simp only [graphCoefficient,if_neg he,if_neg (Ne.symm he),if_pos hij,if_neg (not_lt_of_gt hij)]
      rw [D.symmetric.eq (L (Pi.single j 1)).val.val (L (Pi.single i 1)).val.val]
      simpa using binaryScalar_add_self (D.pairing (L (Pi.single i 1)).val.val (L (Pi.single j 1)).val.val)
    · simp only [graphCoefficient,if_neg he,if_neg (Ne.symm he),if_pos hji,if_neg (not_lt_of_gt hji)]
      simpa using binaryScalar_add_self (D.pairing (L (Pi.single i 1)).val.val (L (Pi.single j 1)).val.val)

def baseGraphLinear
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) :
    (Fin d → ZMod 2) →ₗ[ZMod 2] V :=
  Fintype.linearCombination (ZMod 2) (D.graphVector U hU hw b L)

theorem baseGraphLinear_pair
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) (x : Fin d → ZMod 2) :
    D.primalPair U b (D.baseGraphLinear U hU hw b L x)=x := by
  simp only [baseGraphLinear,Fintype.linearCombination_apply,map_sum,map_smul,D.graphVector_pair]
  ext i
  simp [Pi.single_apply,Finset.sum_apply]

theorem baseGraphLinear_core
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) (x : Fin d → ZMod 2) :
    D.coreResidual U hw b (D.baseGraphLinear U hU hw b L x)=(L x).val.val := by
  simp only [baseGraphLinear,Fintype.linearCombination_apply,map_sum,map_smul,D.graphVector_core]
  have hx : ∑ i,x i • Pi.single i (1 : ZMod 2)=x := by
    ext j
    simp [Pi.single_apply,Finset.sum_apply]
  have h := congrArg (fun z => (L z).val.val) hx
  simpa only [map_sum,map_smul,Submodule.coe_sum,Submodule.coe_smul] using h

def baseGraph
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) :
    D.SingularSection U b :=
  ⟨D.baseGraphLinear U hU hw b L,D.baseGraphLinear_pair U hU hw b L,
    D.quadratic_linearCombination _ (D.graphVector_quadratic U hU hw b L)
      (D.graphVector_pairing U hU hw b L)⟩

/-- Each actual section has a uniquely determined actual even residual map. -/
def sectionCore (f : D.SingularSection U b) :
    (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b where
  toFun x := ⟨⟨D.coreResidual U hw b (f.val x),D.coreResidual_mem U hU hw b _⟩,by
    change D.pairing D.wu (D.coreResidual U hw b (f.val x))=0
    rw [D.core_pairing_residual U hw b ⟨D.wu,D.coreSpace_wu U hU hw b⟩]
    have hh : D.IsSingular (LinearMap.range f.val) := by
      rintro _ ⟨z,rfl⟩
      exact f.property.2 z
    exact D.singular_wu_pairing hh ⟨x,rfl⟩⟩
  map_add' x y := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; apply Subtype.ext; simp

theorem sectionCore_baseGraph
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) :
    D.sectionCore U hU hw b (D.baseGraph U hU hw b L)=L := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact D.baseGraphLinear_core U hU hw b L x

/-- The coefficient matrix as an actual bilinear form on the pairing coordinates. -/
def coefficientForm (a : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2)) :
    LinearMap.BilinForm (ZMod 2) (Fin d → ZMod 2) :=
  ∑ i,LinearMap.BilinForm.linMulLin
    ((LinearMap.proj i).comp a) (LinearMap.proj i)

theorem coefficientForm_apply (a : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
    (x y : Fin d → ZMod 2) : coefficientForm a x y=∑ i,a x i*y i := by
  simp [coefficientForm,LinearMap.BilinForm.linMulLin_apply,LinearMap.sum_apply]

def formCoefficient (A : LinearMap.BilinForm (ZMod 2) (Fin d → ZMod 2)) :
    (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
  LinearMap.pi fun i => A.flip (Pi.single i 1)

theorem coefficientForm_formCoefficient
    (A : LinearMap.BilinForm (ZMod 2) (Fin d → ZMod 2)) :
    coefficientForm (formCoefficient A)=A := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [coefficientForm_apply]
  have hy : ∑ i,y i • Pi.single i (1 : ZMod 2)=y := by
    ext j
    simp [Pi.single_apply,Finset.sum_apply]
  conv_rhs => rw [← hy]
  simp only [map_sum,map_smul,smul_eq_mul,formCoefficient,LinearMap.pi_apply,LinearMap.flip_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem formCoefficient_coefficientForm
    (a : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2)) :
    formCoefficient (coefficientForm a)=a := by
  apply LinearMap.ext
  intro x
  ext i
  simp [formCoefficient,coefficientForm_apply,Pi.single_apply]

def sectionDelta (f : D.SingularSection U b) :
    (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
  (D.dualPair U hw b).comp
    (f.val-(D.baseGraph U hU hw b (D.sectionCore U hU hw b f)).val)

theorem section_eq_base_add (f : D.SingularSection U b) :
    f.val=(D.baseGraph U hU hw b (D.sectionCore U hU hw b f)).val+
      (primalSum U b).comp (D.sectionDelta U hU hw b f) := by
  apply LinearMap.ext
  intro x
  let g := D.baseGraph U hU hw b (D.sectionCore U hU hw b f)
  have hp : D.primalPair U b (f.val x-g.val x)=0 := by
    rw [map_sub,f.property.1,g.property.1,sub_self]
  have hr : D.coreResidual U hw b (f.val x-g.val x)=0 := by
    rw [map_sub]
    change D.coreResidual U hw b (f.val x)-
      D.coreResidual U hw b (D.baseGraphLinear U hU hw b (D.sectionCore U hU hw b f) x)=0
    rw [D.baseGraphLinear_core]
    exact sub_self _
  have hh := (D.ordinaryCoordinates U hU hw b).apply_symm_apply (f.val x-g.val x)
  change primalSum U b (D.dualPair U hw b (f.val x-g.val x))+
    D.coreResidual U hw b (f.val x-g.val x)+D.dualSum U hw b (D.primalPair U b (f.val x-g.val x))=
    f.val x-g.val x at hh
  rw [hp,hr,map_zero,add_zero,add_zero] at hh
  change f.val x=g.val x+primalSum U b (D.dualPair U hw b (f.val x-g.val x))
  rw [hh]
  abel

theorem sectionDelta_isAlt (f : D.SingularSection U b) :
    (coefficientForm (D.sectionDelta U hU hw b f)).IsAlt := by
  intro x
  let g := D.baseGraph U hU hw b (D.sectionCore U hU hw b f)
  have he := LinearMap.congr_fun (D.section_eq_base_add U hU hw b f) x
  change f.val x=g.val x+primalSum U b (D.sectionDelta U hU hw b f x) at he
  have hq := D.quadratic_add (g.val x) (primalSum U b (D.sectionDelta U hU hw b f x))
  rw [← he,f.property.2,g.property.2,D.primalSum_quadratic U hU,zero_add] at hq
  have hb : D.pairing (g.val x) (primalSum U b (D.sectionDelta U hU hw b f x))=
      coefficientForm (D.sectionDelta U hU hw b f) x x := by
    rw [D.symmetric.eq,D.primalSum_pairing,g.property.1,coefficientForm_apply]
  rw [hb] at hq
  exact (two_mul_bitLift_eq_zero_iff _).mp (by simpa using hq.symm)

def graphOfData
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b)
    (A : {B : LinearMap.BilinForm (ZMod 2) (Fin d → ZMod 2) // B.IsAlt}) :
    D.SingularSection U b :=
  ⟨(D.baseGraph U hU hw b L).val+(primalSum U b).comp (formCoefficient A.val),by
    constructor
    · intro x
      change D.primalPair U b ((D.baseGraph U hU hw b L).val x+primalSum U b (formCoefficient A.val x))=x
      rw [map_add,(D.baseGraph U hU hw b L).property.1,D.primalPair_primalSum U hU,add_zero]
    · intro x
      change D.quadratic ((D.baseGraph U hU hw b L).val x+primalSum U b (formCoefficient A.val x))=0
      rw [D.quadratic_add,(D.baseGraph U hU hw b L).property.2,D.primalSum_quadratic U hU,zero_add]
      rw [D.symmetric.eq,D.primalSum_pairing,(D.baseGraph U hU hw b L).property.1,
        ← coefficientForm_apply,coefficientForm_formCoefficient,A.property]
      simp⟩

include hU in
theorem coreResidual_primalSum (a : Fin d → ZMod 2) :
    D.coreResidual U hw b (primalSum U b a)=0 := by
  rw [D.coreResidual_apply,D.dualPair_primalSum U hU,D.primalPair_primalSum U hU,
    map_zero,add_zero,module_add_self]

theorem sectionCore_graphOfData
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b)
    (A : {B : LinearMap.BilinForm (ZMod 2) (Fin d → ZMod 2) // B.IsAlt}) :
    D.sectionCore U hU hw b (D.graphOfData U hU hw b L A)=L := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  change D.coreResidual U hw b ((D.baseGraph U hU hw b L).val x+primalSum U b (formCoefficient A.val x))=
    (L x).val.val
  rw [map_add,D.coreResidual_primalSum U hU,add_zero]
  exact D.baseGraphLinear_core U hU hw b L x

theorem sectionDelta_graphOfData
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b)
    (A : {B : LinearMap.BilinForm (ZMod 2) (Fin d → ZMod 2) // B.IsAlt}) :
    D.sectionDelta U hU hw b (D.graphOfData U hU hw b L A)=formCoefficient A.val := by
  unfold sectionDelta
  rw [D.sectionCore_graphOfData]
  apply LinearMap.ext
  intro x
  change D.dualPair U hw b
    ((D.baseGraph U hU hw b L).val x+primalSum U b (formCoefficient A.val x)-
      (D.baseGraph U hU hw b L).val x)=_
  rw [add_sub_cancel_left,D.dualPair_primalSum U hU]

/-- Every actual singular section, and only such a section, is represented by free
even residual vectors and a genuine alternating bilinear form. -/
def singularSectionEquiv :
    D.SingularSection U b ≃
      ((Fin d → ZMod 2) →ₗ[ZMod 2] D.CoreEven U hU hw b) ×
      {B : LinearMap.BilinForm (ZMod 2) (Fin d → ZMod 2) // B.IsAlt} where
  toFun f := (D.sectionCore U hU hw b f,
    ⟨coefficientForm (D.sectionDelta U hU hw b f),D.sectionDelta_isAlt U hU hw b f⟩)
  invFun p := D.graphOfData U hU hw b p.1 p.2
  left_inv f := by
    apply Subtype.ext
    change (D.baseGraph U hU hw b (D.sectionCore U hU hw b f)).val+
      (primalSum U b).comp (formCoefficient (coefficientForm (D.sectionDelta U hU hw b f)))=f.val
    rw [formCoefficient_coefficientForm]
    exact (D.section_eq_base_add U hU hw b f).symm
  right_inv p := by
    apply Prod.ext
    · exact D.sectionCore_graphOfData U hU hw b p.1 p.2
    · apply Subtype.ext
      change coefficientForm (D.sectionDelta U hU hw b (D.graphOfData U hU hw b p.1 p.2))=p.2.val
      rw [D.sectionDelta_graphOfData,coefficientForm_formCoefficient]

include hU hw in
theorem singularSection_card :
    Nat.card (D.SingularSection U b)=
      2^(d*(finrank (ZMod 2) V-2*d-1)+d.choose 2) := by
  rw [Nat.card_congr (D.singularSectionEquiv U hU hw b),Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := ZMod 2),binaryAlternating_card]
  have hdim := D.core_finrank_add U hU hw b
  have heven := D.coreEven_finrank_add_one U hU hw b
  have he : finrank (ZMod 2) (D.CoreEven U hU hw b)=finrank (ZMod 2) V-2*d-1 := by
    dsimp only [CoreEven]
    omega
  simp only [Module.finrank_linearMap,Module.finrank_pi,Fintype.card_fin,he]
  simp only [Nat.card_eq_fintype_card,ZMod.card,← pow_add]


/-- Actual singular subspaces paired perfectly with U by the ambient bilinear form. -/
def SingularOpposite :=
  {M : Submodule (ZMod 2) V // D.IsSingular M ∧
    Function.Bijective ((D.primalPair U b).domRestrict M)}

def sectionRange (f : D.SingularSection U b) : D.SingularOpposite U b :=
  ⟨LinearMap.range f.val,by
    constructor
    · rintro _ ⟨x,rfl⟩
      exact f.property.2 x
    · constructor
      · intro x y he
        obtain ⟨a,ha⟩ := x.property
        obtain ⟨c,hc⟩ := y.property
        have hx : D.primalPair U b x.val=a := by rw [← ha,f.property.1]
        have hy : D.primalPair U b y.val=c := by rw [← hc,f.property.1]
        have he' : a=c := hx.symm.trans (he.trans hy)
        exact Subtype.ext (ha.symm.trans ((congrArg f.val he').trans hc))
      · intro x
        exact ⟨⟨f.val x,⟨x,rfl⟩⟩,f.property.1 x⟩⟩

def oppositeSection (M : D.SingularOpposite U b) : D.SingularSection U b :=
  ⟨M.val.subtype.comp
      (LinearEquiv.ofBijective ((D.primalPair U b).domRestrict M.val) M.property.2).symm.toLinearMap,by
    constructor
    · intro x
      exact (LinearEquiv.ofBijective ((D.primalPair U b).domRestrict M.val) M.property.2).apply_symm_apply x
    · intro x
      exact M.property.1 _
        ((LinearEquiv.ofBijective ((D.primalPair U b).domRestrict M.val) M.property.2).symm x).property⟩

def singularSectionOppositeEquiv : D.SingularSection U b ≃ D.SingularOpposite U b where
  toFun := D.sectionRange U b
  invFun := D.oppositeSection U b
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    let e := LinearEquiv.ofBijective ((D.primalPair U b).domRestrict
      (D.sectionRange U b f).val) (D.sectionRange U b f).property.2
    have he : e.symm x=⟨f.val x,⟨x,rfl⟩⟩ := by
      apply e.injective
      exact (e.apply_symm_apply x).trans (f.property.1 x).symm
    exact congrArg Subtype.val he
  right_inv M := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ((LinearEquiv.ofBijective ((D.primalPair U b).domRestrict M.val) M.property.2).symm z).property
    · intro hx
      refine ⟨D.primalPair U b x,?_⟩
      have h := (LinearEquiv.ofBijective ((D.primalPair U b).domRestrict M.val) M.property.2).symm_apply_apply ⟨x,hx⟩
      exact congrArg Subtype.val h

include hU hw in
theorem singularOpposite_card :
    Nat.card (D.SingularOpposite U b)=
      2^(d*(finrank (ZMod 2) V-2*d-1)+d.choose 2) := by
  rw [← Nat.card_congr (D.singularSectionOppositeEquiv U b)]
  exact D.singularSection_card U hU hw b

theorem singularOpposite_finrank (M : D.SingularOpposite U b) :
    finrank (ZMod 2) M.val=d := by
  have h := (LinearEquiv.ofBijective ((D.primalPair U b).domRestrict M.val) M.property.2).finrank_eq
  simpa using h

include hU in
theorem singularOpposite_disjoint (M : D.SingularOpposite U b) : Disjoint U M.val := by
  rw [Submodule.disjoint_def]
  intro x hx hM
  have hp : D.primalPair U b x=0 := by
    ext i
    exact D.singular_pairing hU (b i).property hx
  have he : (⟨x,hM⟩ : M.val)=0 := M.property.2.1 (by exact hp.trans (map_zero _).symm)
  exact congrArg Subtype.val he

include hU in
theorem singularOpposite_wu_not_mem (M : D.SingularOpposite U b) (hw : D.wu ∉ U) :
    D.wu ∉ M.val := by
  intro hM
  have hp : D.primalPair U b D.wu=0 := by
    ext i
    exact (D.symmetric.eq _ _).trans (D.singular_wu_pairing hU (b i).property)
  have he : (⟨D.wu,hM⟩ : M.val)=0 := M.property.2.1 (by exact hp.trans (map_zero _).symm)
  exact hw (by rw [show D.wu=0 from congrArg Subtype.val he]; exact U.zero_mem)

theorem primalPair_eq_zero_iff (x : V) :
    D.primalPair U b x=0 ↔ ∀ u ∈ U,D.pairing u x=0 := by
  constructor
  · intro h u hu
    let f : U →ₗ[ZMod 2] (ZMod 2) := (D.pairing.flip x).comp U.subtype
    have hf : f=0 := by
      apply b.ext
      intro i
      exact congrFun h i
    exact DFunLike.congr_fun hf ⟨u,hu⟩
  · intro h
    ext i
    exact h _ (b i).property

theorem singularOpposite_right_nondegenerate (M : D.SingularOpposite U b)
    {x : V} (hx : x∈M.val) (hp : ∀ u∈U,D.pairing u x=0) : x=0 := by
  have hz := (D.primalPair_eq_zero_iff U b x).mpr hp
  have he : (⟨x,hx⟩ : M.val)=0 := M.property.2.1 (by exact hz.trans (map_zero _).symm)
  exact congrArg Subtype.val he

theorem singularOpposite_left_nondegenerate (M : D.SingularOpposite U b)
    {x : V} (hx : x∈U) (hp : ∀ u∈M.val,D.pairing x u=0) : x=0 := by
  have hcoeff : ∀ i,b.repr ⟨x,hx⟩ i=0 := by
    intro i
    obtain ⟨y,hy⟩ := M.property.2.2 (Pi.single i 1)
    change D.primalPair U b y.val=Pi.single i 1 at hy
    have h := hp y.val y.property
    have hs := congrArg Subtype.val (b.sum_repr ⟨x,hx⟩)
    simp only [Submodule.coe_sum,Submodule.coe_smul] at hs
    rw [← hs] at h
    change D.pairing (primalSum U b (fun j => b.repr ⟨x,hx⟩ j)) y.val=0 at h
    rw [D.primalSum_pairing,hy] at h
    simpa [Pi.single_apply] using h
  have hz : (⟨x,hx⟩ : U)=0 := b.repr.injective (by ext i; simpa using hcoeff i)
  exact congrArg Subtype.val hz

theorem mem_singularOpposite_iff (M : Submodule (ZMod 2) V) :
    (D.IsSingular M ∧ Function.Bijective ((D.primalPair U b).domRestrict M)) ↔
      D.IsSingular M ∧ finrank (ZMod 2) M=d ∧
        (∀ x∈M,(∀ u∈U,D.pairing u x=0)→x=0) := by
  constructor
  · intro h
    exact ⟨h.1,D.singularOpposite_finrank U b ⟨M,h⟩,
      fun x hx hp => D.singularOpposite_right_nondegenerate U b ⟨M,h⟩ hx hp⟩
  · rintro ⟨hq,hd,hp⟩
    have hi : Function.Injective ((D.primalPair U b).domRestrict M) := by
      apply LinearMap.ker_eq_bot.mp
      apply le_antisymm
      · intro x hx
        change x=0
        apply Subtype.ext
        apply hp _ x.property
        exact (D.primalPair_eq_zero_iff U b x.val).mp hx
      · exact bot_le
    exact ⟨hq,hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hd)).mp hi⟩

end ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace
