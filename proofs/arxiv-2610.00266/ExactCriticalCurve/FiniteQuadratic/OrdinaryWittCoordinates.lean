import ExactCriticalCurve.Binary.RelationHalf
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection

/-! Actual ordinary hyperbolic coordinates for full mod-four refinements.
No Witt decomposition or quadratic classification is assumed. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Binary Binary.StochasticCounting

structure ModFourQuadraticSpace (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  pairing : LinearMap.BilinForm (ZMod 2) V
  quadratic : V → ZMod 4
  quadratic_zero : quadratic 0=0
  quadratic_add : ∀ x y, quadratic (x+y)=quadratic x+quadratic y+2*bitLift (pairing x y)
  symmetric : pairing.IsSymm
  nondegenerate : pairing.Nondegenerate
  wu : V
  characteristic : ∀ x, pairing x x=pairing wu x

namespace ModFourQuadraticSpace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (D : ModFourQuadraticSpace V)

def IsSingular (U : Submodule (ZMod 2) V) : Prop := ∀ x ∈ U, D.quadratic x=0

theorem module_add_self (x : V) : x+x=0 := by
  rw [← two_smul (ZMod 2),show (2 : ZMod 2)=0 by decide,zero_smul]

theorem singular_pairing {U : Submodule (ZMod 2) V} (hU : D.IsSingular U)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) : D.pairing x y=0 := by
  have h := D.quadratic_add x y
  rw [hU _ hx,hU _ hy,hU _ (U.add_mem hx hy)] at h
  exact (two_mul_bitLift_eq_zero_iff _).mp (by simpa using h.symm)

theorem singular_wu_pairing {U : Submodule (ZMod 2) V} (hU : D.IsSingular U)
    {x : V} (hx : x ∈ U) : D.pairing D.wu x=0 := by
  rw [← D.characteristic]
  exact D.singular_pairing hU hx hx

theorem quadratic_even_of_wu_orthogonal {x : V} (hx : D.pairing D.wu x=0) :
    D.quadratic x+D.quadratic x=0 := by
  have h := D.quadratic_add x x
  rw [module_add_self,D.quadratic_zero,D.characteristic,hx] at h
  simpa using h.symm

variable [FiniteDimensional (ZMod 2) V]

/-- Ordinary Wu exclusion produces the actual correction direction inside U-perp. -/
theorem exists_ordinary_correction (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U) :
    ∃ t : D.pairing.orthogonal U, D.pairing D.wu t.val=1 := by
  have ht : ∃ t : D.pairing.orthogonal U, D.pairing D.wu t.val≠0 := by
    by_contra h
    push_neg at h
    apply hw
    have hm : D.wu ∈ D.pairing.orthogonal (D.pairing.orthogonal U) := by
      intro x hx
      exact (D.symmetric.eq _ _).trans (h ⟨x,hx⟩)
    rwa [D.pairing.orthogonal_orthogonal D.nondegenerate D.symmetric.isRefl] at hm
  obtain ⟨t,ht⟩ := ht
  refine ⟨t,?_⟩
  generalize D.pairing D.wu t.val=c at *
  fin_cases c <;> simp_all

def ordinaryCorrection (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U) :
    D.pairing.orthogonal U := (D.exists_ordinary_correction U hw).choose

theorem ordinaryCorrection_pairing (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U) :
    D.pairing D.wu (D.ordinaryCorrection U hw).val=1 :=
  (D.exists_ordinary_correction U hw).choose_spec

def rawDualVectors {d : ℕ} (U : Submodule (ZMod 2) V) (b : Basis (Fin d) (ZMod 2) U) :
    Fin d → V := fun i => (D.pairing.toDual D.nondegenerate).symm (Subspace.dualLift U (b.coord i))

theorem rawDualVectors_pairing {d : ℕ} (U : Submodule (ZMod 2) V)
    (b : Basis (Fin d) (ZMod 2) U) (i j : Fin d) :
    D.pairing (b j).val (D.rawDualVectors U b i) = if i=j then 1 else 0 := by
  rw [D.symmetric.eq]
  change D.pairing ((D.pairing.toDual D.nondegenerate).symm (Subspace.dualLift U (b.coord i))) (b j).val = _
  rw [LinearMap.BilinForm.apply_toDual_symm_apply,Subspace.dualLift_of_subtype]
  simp [Basis.coord_apply,Finsupp.single_apply,eq_comm]

def evenDualVectors {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i : Fin d) : V :=
  D.rawDualVectors U b i +
    D.pairing D.wu (D.rawDualVectors U b i) • (D.ordinaryCorrection U hw).val

theorem evenDualVectors_wu {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i : Fin d) :
    D.pairing D.wu (D.evenDualVectors U hw b i)=0 := by
  rw [evenDualVectors,map_add,map_smul,D.ordinaryCorrection_pairing]
  simpa using binaryScalar_add_self (D.pairing D.wu (D.rawDualVectors U b i))

theorem evenDualVectors_pairing {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i j : Fin d) :
    D.pairing (b j).val (D.evenDualVectors U hw b i)=if i=j then 1 else 0 := by
  have ht := (D.ordinaryCorrection U hw).property (b j).val (b j).property
  rw [evenDualVectors,map_add,map_smul,ht]
  simp only [smul_zero,add_zero,D.rawDualVectors_pairing]

def partnerCoefficient {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (j i : Fin d) : ZMod 2 :=
  if j=i then halfEven (D.quadratic (D.evenDualVectors U hw b i))
  else if j < i then D.pairing (D.evenDualVectors U hw b i) (D.evenDualVectors U hw b j)
  else 0

def partnerCorrection {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i : Fin d) : U :=
  ∑ j, D.partnerCoefficient U hw b j i • b j

def partnerVectors {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i : Fin d) : V :=
  D.evenDualVectors U hw b i+(D.partnerCorrection U hw b i).val

theorem partnerCorrection_pairing {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i j : Fin d) :
    D.pairing (D.partnerCorrection U hw b i).val (D.evenDualVectors U hw b j) =
      D.partnerCoefficient U hw b j i := by
  simp only [partnerCorrection,Submodule.coe_sum,Submodule.coe_smul,map_sum,LinearMap.sum_apply,
    map_smul,LinearMap.smul_apply,smul_eq_mul,D.evenDualVectors_pairing]
  simp

theorem partnerVectors_pairing_left {d : ℕ} (U : Submodule (ZMod 2) V)
    (hU : D.IsSingular U) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i j : Fin d) :
    D.pairing (b j).val (D.partnerVectors U hw b i)=if i=j then 1 else 0 := by
  rw [partnerVectors,map_add,D.evenDualVectors_pairing,
    D.singular_pairing hU (b j).property (D.partnerCorrection U hw b i).property,add_zero]

theorem partnerVectors_wu {d : ℕ} (U : Submodule (ZMod 2) V)
    (hU : D.IsSingular U) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i : Fin d) :
    D.pairing D.wu (D.partnerVectors U hw b i)=0 := by
  rw [partnerVectors,map_add,D.evenDualVectors_wu,
    D.singular_wu_pairing hU (D.partnerCorrection U hw b i).property,add_zero]

theorem partnerVectors_quadratic {d : ℕ} (U : Submodule (ZMod 2) V)
    (hU : D.IsSingular U) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i : Fin d) :
    D.quadratic (D.partnerVectors U hw b i)=0 := by
  rw [partnerVectors,D.quadratic_add,hU _ (D.partnerCorrection U hw b i).property,
    add_zero,D.symmetric.eq,D.partnerCorrection_pairing]
  simp only [partnerCoefficient,ite_true]
  rw [two_mul_bitLift_halfEven _
    (D.quadratic_even_of_wu_orthogonal (D.evenDualVectors_wu U hw b i))]
  exact D.quadratic_even_of_wu_orthogonal (D.evenDualVectors_wu U hw b i)

theorem partnerVectors_pairing {d : ℕ} (U : Submodule (ZMod 2) V)
    (hU : D.IsSingular U) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (i j : Fin d) :
    D.pairing (D.partnerVectors U hw b i) (D.partnerVectors U hw b j)=0 := by
  simp only [partnerVectors,map_add,LinearMap.add_apply]
  rw [
    D.singular_pairing hU (D.partnerCorrection U hw b i).property
      (D.partnerCorrection U hw b j).property,add_zero,
    D.partnerCorrection_pairing,D.symmetric.eq (D.evenDualVectors U hw b i) (D.partnerCorrection U hw b j).val,
    D.partnerCorrection_pairing]
  by_cases he : i=j
  · subst j
    rw [D.characteristic,D.evenDualVectors_wu]
    simp only [partnerCoefficient,ite_true,zero_add,binaryScalar_add_self]
  · rcases lt_or_gt_of_ne he with hij | hji
    · simp only [partnerCoefficient,if_neg he,if_neg (Ne.symm he),if_pos hij,if_neg (not_lt_of_gt hij)]
      rw [D.symmetric.eq (D.evenDualVectors U hw b j) _]
      simpa using binaryScalar_add_self (D.pairing (D.evenDualVectors U hw b i) (D.evenDualVectors U hw b j))
    · simp only [partnerCoefficient,if_neg he,if_neg (Ne.symm he),if_pos hji,if_neg (not_lt_of_gt hji)]
      simpa using binaryScalar_add_self (D.pairing (D.evenDualVectors U hw b i) (D.evenDualVectors U hw b j))


theorem quadratic_smul (c : ZMod 2) (x : V) :
    D.quadratic (c • x)=bitLift c * D.quadratic x := by
  rcases (show c=0 ∨ c=1 by fin_cases c <;> simp) with rfl|rfl <;>
    simp [D.quadratic_zero]

theorem quadratic_linearCombination {d : ℕ} (v : Fin d → V)
    (hq : ∀ i,D.quadratic (v i)=0) (hp : ∀ i j,D.pairing (v i) (v j)=0)
    (a : Fin d → ZMod 2) :
    D.quadratic (Fintype.linearCombination (ZMod 2) v a)=0 := by
  simp only [Fintype.linearCombination_apply]
  have hs : ∀ s : Finset (Fin d), D.quadratic (∑ i ∈ s,a i • v i)=0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [D.quadratic_zero]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,D.quadratic_add,ih,D.quadratic_smul,hq]
      simp only [map_sum,map_smul,LinearMap.smul_apply,hp,smul_zero,Finset.sum_const_zero,
        mul_zero,zero_add,bitLift_zero]
  exact hs _

def primalSum {d : ℕ} (U : Submodule (ZMod 2) V) (b : Basis (Fin d) (ZMod 2) U) :
    (Fin d → ZMod 2) →ₗ[ZMod 2] V :=
  Fintype.linearCombination (ZMod 2) (fun i => (b i).val)

def dualSum {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) : (Fin d → ZMod 2) →ₗ[ZMod 2] V :=
  Fintype.linearCombination (ZMod 2) (D.partnerVectors U hw b)

def primalPair {d : ℕ} (U : Submodule (ZMod 2) V) (b : Basis (Fin d) (ZMod 2) U) :
    V →ₗ[ZMod 2] (Fin d → ZMod 2) :=
  LinearMap.pi fun i => D.pairing (b i).val

def dualPair {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) : V →ₗ[ZMod 2] (Fin d → ZMod 2) :=
  LinearMap.pi fun i => D.pairing (D.partnerVectors U hw b i)

theorem primalSum_mem {d : ℕ} (U : Submodule (ZMod 2) V)
    (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) : primalSum U b a ∈ U := by
  change (∑ i,a i • (b i).val) ∈ U
  exact Submodule.sum_mem U fun i _ => U.smul_mem _ (b i).property

theorem primalPair_primalSum {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) :
    D.primalPair U b (primalSum U b a)=0 := by
  ext i
  exact D.singular_pairing hU (b i).property (primalSum_mem U b a)

theorem primalPair_dualSum {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) :
    D.primalPair U b (D.dualSum U hw b a)=a := by
  ext i
  simp only [primalPair,LinearMap.pi_apply,dualSum,Fintype.linearCombination_apply,
    map_sum,map_smul,D.partnerVectors_pairing_left U hU hw b,smul_eq_mul]
  simp

theorem dualPair_primalSum {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) :
    D.dualPair U hw b (primalSum U b a)=a := by
  ext i
  simp only [dualPair,LinearMap.pi_apply,primalSum,Fintype.linearCombination_apply,
    map_sum,map_smul,smul_eq_mul]
  simp_rw [D.symmetric.eq (D.partnerVectors U hw b i),D.partnerVectors_pairing_left U hU hw b]
  simp

theorem dualPair_dualSum {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) :
    D.dualPair U hw b (D.dualSum U hw b a)=0 := by
  ext i
  simp [dualPair,dualSum,Fintype.linearCombination_apply,map_sum,map_smul,
    D.partnerVectors_pairing U hU hw b]

theorem primalSum_quadratic {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) :
    D.quadratic (primalSum U b a)=0 := hU _ (primalSum_mem U b a)

theorem dualSum_quadratic {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) :
    D.quadratic (D.dualSum U hw b a)=0 :=
  D.quadratic_linearCombination _ (D.partnerVectors_quadratic U hU hw b)
    (D.partnerVectors_pairing U hU hw b) a

/-- The actual common orthogonal complement of the two dual singular frames. -/
def coreSpace {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) : Submodule (ZMod 2) V :=
  LinearMap.ker (D.primalPair U b) ⊓ LinearMap.ker (D.dualPair U hw b)

def coreResidual {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) : V →ₗ[ZMod 2] V :=
  LinearMap.id + (primalSum U b).comp (D.dualPair U hw b) +
    (D.dualSum U hw b).comp (D.primalPair U b)

theorem coreResidual_apply {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (x : V) :
    D.coreResidual U hw b x=x+primalSum U b (D.dualPair U hw b x)+
      D.dualSum U hw b (D.primalPair U b x) := rfl

theorem coreResidual_mem {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) (x : V) :
    D.coreResidual U hw b x ∈ D.coreSpace U hw b := by
  constructor
  · change D.primalPair U b (D.coreResidual U hw b x)=0
    rw [D.coreResidual_apply,map_add,map_add,D.primalPair_primalSum U hU,
      D.primalPair_dualSum U hU,add_zero]
    exact module_add_self _
  · change D.dualPair U hw b (D.coreResidual U hw b x)=0
    rw [D.coreResidual_apply,map_add,map_add,D.dualPair_primalSum U hU,
      D.dualPair_dualSum U hU,add_zero]
    exact module_add_self _

theorem coreSpace_wu {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) :
    D.wu ∈ D.coreSpace U hw b := by
  constructor
  · ext i
    exact (D.symmetric.eq _ _).trans (D.singular_wu_pairing hU (b i).property)
  · ext i
    exact (D.symmetric.eq _ _).trans (D.partnerVectors_wu U hU hw b i)


theorem primalSum_pairing {d : ℕ} (U : Submodule (ZMod 2) V)
    (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) (x : V) :
    D.pairing (primalSum U b a) x=∑ i,a i * D.primalPair U b x i := by
  simp [primalSum,Fintype.linearCombination_apply,map_sum,map_smul,LinearMap.sum_apply,
    LinearMap.smul_apply,primalPair,smul_eq_mul]

theorem dualSum_pairing {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (a : Fin d → ZMod 2) (x : V) :
    D.pairing (D.dualSum U hw b a) x=∑ i,a i * D.dualPair U hw b x i := by
  simp [dualSum,Fintype.linearCombination_apply,map_sum,map_smul,LinearMap.sum_apply,
    LinearMap.smul_apply,dualPair,smul_eq_mul]

theorem core_primalPair {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (x : D.coreSpace U hw b) :
    D.primalPair U b x.val=0 := x.property.1

theorem core_dualPair {d : ℕ} (U : Submodule (ZMod 2) V) (hw : D.wu ∉ U)
    (b : Basis (Fin d) (ZMod 2) U) (x : D.coreSpace U hw b) :
    D.dualPair U hw b x.val=0 := x.property.2

theorem coordinate_primalPair {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U)
    (a c : Fin d → ZMod 2) (x : D.coreSpace U hw b) :
    D.primalPair U b (primalSum U b a+x.val+D.dualSum U hw b c)=c := by
  rw [map_add,map_add,D.primalPair_primalSum U hU,D.core_primalPair,
    D.primalPair_dualSum U hU,zero_add,zero_add]

theorem coordinate_dualPair {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U)
    (a c : Fin d → ZMod 2) (x : D.coreSpace U hw b) :
    D.dualPair U hw b (primalSum U b a+x.val+D.dualSum U hw b c)=a := by
  rw [map_add,map_add,D.dualPair_primalSum U hU,D.core_dualPair,
    D.dualPair_dualSum U hU,add_zero,add_zero]

theorem coordinate_residual {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U)
    (a c : Fin d → ZMod 2) (x : D.coreSpace U hw b) :
    D.coreResidual U hw b (primalSum U b a+x.val+D.dualSum U hw b c)=x.val := by
  rw [D.coreResidual_apply,D.coordinate_primalPair U hU,D.coordinate_dualPair U hU]
  calc
    _ = x.val + (primalSum U b a+primalSum U b a)+
      (D.dualSum U hw b c+D.dualSum U hw b c) := by abel
    _ = _ := by rw [module_add_self,module_add_self,add_zero,add_zero]

/-- A true ambient coordinate equivalence, constructed from the full quadratic law. -/
def ordinaryCoordinates {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) :
    ((Fin d → ZMod 2) × D.coreSpace U hw b × (Fin d → ZMod 2)) ≃ₗ[ZMod 2] V where
  toFun x := primalSum U b x.1+x.2.1.val+D.dualSum U hw b x.2.2
  invFun x := (D.dualPair U hw b x,⟨D.coreResidual U hw b x,D.coreResidual_mem U hU hw b x⟩,
    D.primalPair U b x)
  left_inv x := by
    apply Prod.ext
    · exact D.coordinate_dualPair U hU hw b _ _ _
    · apply Prod.ext
      · exact Subtype.ext (D.coordinate_residual U hU hw b _ _ _)
      · exact D.coordinate_primalPair U hU hw b _ _ _
  right_inv x := by
    change primalSum U b (D.dualPair U hw b x)+D.coreResidual U hw b x+
      D.dualSum U hw b (D.primalPair U b x)=x
    rw [D.coreResidual_apply]
    calc
      _ = x+(primalSum U b (D.dualPair U hw b x)+primalSum U b (D.dualPair U hw b x))+
        (D.dualSum U hw b (D.primalPair U b x)+D.dualSum U hw b (D.primalPair U b x)) := by abel
      _ = _ := by rw [module_add_self,module_add_self,add_zero,add_zero]
  map_add' x y := by simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add,map_add]; abel
  map_smul' c x := by simp [smul_add]

theorem ordinaryCoordinates_quadratic {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U)
    (a c : Fin d → ZMod 2) (x : D.coreSpace U hw b) :
    D.quadratic (D.ordinaryCoordinates U hU hw b (a,x,c))=
      D.quadratic x.val+2*bitLift (∑ i,a i*c i) := by
  change D.quadratic (primalSum U b a+x.val+D.dualSum U hw b c)=_
  rw [D.quadratic_add,D.quadratic_add,D.primalSum_quadratic U hU,D.dualSum_quadratic U hU]
  have hpx : D.pairing (primalSum U b a) x.val=0 := by
    rw [D.primalSum_pairing,D.core_primalPair]; simp
  have hxc : D.pairing x.val (D.dualSum U hw b c)=0 := by
    rw [D.symmetric.eq,D.dualSum_pairing,D.core_dualPair]; simp
  have hpc : D.pairing (primalSum U b a) (D.dualSum U hw b c)=∑ i,a i*c i := by
    rw [D.primalSum_pairing,D.primalPair_dualSum U hU]
  simp only [hpx,bitLift_zero,mul_zero,add_zero,zero_add,map_add,LinearMap.add_apply,hxc,hpc]

theorem core_finrank_add {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) :
    finrank (ZMod 2) (D.coreSpace U hw b)+2*d=finrank (ZMod 2) V := by
  have h := (D.ordinaryCoordinates U hU hw b).finrank_eq
  simp only [Module.finrank_prod,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at h
  omega

theorem core_pairing_residual {d : ℕ} (U : Submodule (ZMod 2) V)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U)
    (x : D.coreSpace U hw b) (y : V) :
    D.pairing x.val (D.coreResidual U hw b y)=D.pairing x.val y := by
  rw [D.coreResidual_apply,map_add,map_add]
  have hp : D.pairing x.val (primalSum U b (D.dualPair U hw b y))=0 := by
    rw [D.symmetric.eq,D.primalSum_pairing,D.core_primalPair]; simp
  have hq : D.pairing x.val (D.dualSum U hw b (D.primalPair U b y))=0 := by
    rw [D.symmetric.eq,D.dualSum_pairing,D.core_dualPair]; simp
  rw [hp,hq,add_zero,add_zero]

def coreQuadraticSpace {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) :
    ModFourQuadraticSpace (D.coreSpace U hw b) where
  pairing := D.pairing.restrict (D.coreSpace U hw b)
  quadratic x := D.quadratic x.val
  quadratic_zero := D.quadratic_zero
  quadratic_add x y := D.quadratic_add x.val y.val
  symmetric := ⟨fun x y => D.symmetric.eq x.val y.val⟩
  nondegenerate := by
    intro x hx
    apply Subtype.ext
    apply D.nondegenerate x.val
    intro y
    have h := hx ⟨D.coreResidual U hw b y,D.coreResidual_mem U hU hw b y⟩
    exact (D.core_pairing_residual U hw b x y).symm.trans h
  wu := ⟨D.wu,D.coreSpace_wu U hU hw b⟩
  characteristic x := D.characteristic x.val

theorem core_wu_ne_zero {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) :
    (D.coreQuadraticSpace U hU hw b).wu≠0 := by
  intro h
  apply hw
  have hz : D.wu=0 := congrArg Subtype.val h
  rw [hz]
  exact U.zero_mem

/-- The actual even part of the residual quadratic space, not an abstract dimension label. -/
def coreEvenSpace {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) :
    Submodule (ZMod 2) (D.coreSpace U hw b) :=
  LinearMap.ker ((D.coreQuadraticSpace U hU hw b).pairing (D.coreQuadraticSpace U hU hw b).wu)

theorem coreEven_finrank_add_one {d : ℕ} (U : Submodule (ZMod 2) V) (hU : D.IsSingular U)
    (hw : D.wu ∉ U) (b : Basis (Fin d) (ZMod 2) U) :
    finrank (ZMod 2) (D.coreEvenSpace U hU hw b)+1=finrank (ZMod 2) (D.coreSpace U hw b) := by
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro h
  apply D.core_wu_ne_zero U hU hw b
  apply (D.coreQuadraticSpace U hU hw b).nondegenerate
  intro x
  exact DFunLike.congr_fun h x

end ModFourQuadraticSpace
end ExactCriticalCurve.FiniteQuadratic
