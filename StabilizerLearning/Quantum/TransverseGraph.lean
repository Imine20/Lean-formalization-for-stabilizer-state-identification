import StabilizerLearning.Quantum.Stabilizer
import StabilizerLearning.Foundations.FiniteCounting
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Graph coordinates on the standard transverse Lagrangian chart.
The graph is oriented as `(u, A *ᵥ u)`. All results include characteristic two
and dimension zero; no division by two or graph-classification assumption is used.
-/

noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum

variable {p n : ℕ}

/-- The actual graph of matrix multiplication in the fixed phase space. -/
def graphSubmodule (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    Submodule (ZMod p) (PhaseSpace p n) where
  carrier := {z | z.2 = A *ᵥ z.1}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    change z.2 + w.2 = A *ᵥ (z.1 + w.1)
    rw [Matrix.mulVec_add, hz, hw]
  smul_mem' := by
    intro c z hz
    change c • z.2 = A *ᵥ (c • z.1)
    rw [Matrix.mulVec_smul, hz]

@[simp]
theorem mem_graphSubmodule (A : Matrix (Fin n) (Fin n) (ZMod p))
    (z : PhaseSpace p n) : z ∈ graphSubmodule A ↔ z.2 = A *ᵥ z.1 := Iff.rfl

/-- Graph parameters are a linear equivalence, with explicit first projection inverse. -/
def graphLinearEquiv (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    Configuration p n ≃ₗ[ZMod p] graphSubmodule A where
  toFun u := ⟨(u, A *ᵥ u), rfl⟩
  invFun z := z.val.1
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl z.property.symm
  map_add' u v := by
    apply Subtype.ext
    exact Prod.ext rfl (Matrix.mulVec_add A u v)
  map_smul' c u := by
    apply Subtype.ext
    exact Prod.ext rfl (Matrix.mulVec_smul A c u)

@[simp]
theorem coe_graphLinearEquiv_apply (A : Matrix (Fin n) (Fin n) (ZMod p))
    (u : Configuration p n) :
    ((graphLinearEquiv A u : graphSubmodule A) : PhaseSpace p n) = (u, A *ᵥ u) := rfl

@[simp]
theorem graphLinearEquiv_symm_apply (A : Matrix (Fin n) (Fin n) (ZMod p))
    (z : graphSubmodule A) : (graphLinearEquiv A).symm z = z.val.1 := rfl

variable [Fact p.Prime]

@[simp]
theorem finrank_graphSubmodule (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    Module.finrank (ZMod p) (graphSubmodule A) = n := by
  simpa only [Configuration, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
    (graphLinearEquiv A).finrank_eq.symm

/-- Matrix symmetry is exactly graph isotropy for the fixed all-prime pairing. -/
theorem isIsotropic_graphSubmodule_iff (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    IsIsotropic (graphSubmodule A) ↔ A.IsSymm := by
  constructor
  · intro h
    apply Matrix.IsSymm.ext
    intro i j
    have hij := h (Pi.single i 1, A *ᵥ Pi.single i 1) rfl
      (Pi.single j 1, A *ᵥ Pi.single j 1) rfl
    simp only [symplecticPairing, Matrix.mulVec_single_one, single_one_dotProduct,
      dotProduct_single_one, Matrix.col_apply] at hij
    exact (sub_eq_zero.mp hij).symm
  · intro h z hz w hw
    change dotProduct z.1 w.2 - dotProduct z.2 w.1 = 0
    rw [(mem_graphSubmodule A z).mp hz, (mem_graphSubmodule A w).mp hw]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h.eq]
    exact sub_self _

/-- A symmetric graph, as a value of the public Lagrangian type. -/
def graphLagrangian (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm) :
    Lagrangian p n :=
  ⟨graphSubmodule A, (isIsotropic_graphSubmodule_iff A).mpr hA, finrank_graphSubmodule A⟩

@[simp]
theorem graphLagrangian_val (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm) :
    (graphLagrangian A hA).val = graphSubmodule A := rfl

/-- Transversality to the fixed vertical coordinate space. -/
def IsTransverse (U : Submodule (ZMod p) (PhaseSpace p n)) : Prop :=
  ∀ z ∈ U, z.1 = 0 → z = 0

theorem isTransverse_graphSubmodule (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    IsTransverse (graphSubmodule A) := by
  intro z hz hfst
  apply Prod.ext hfst
  have hsnd := (mem_graphSubmodule A z).mp hz
  simpa [hfst] using hsnd

omit [Fact p.Prime] in
/-- Distinct matrices give distinct graph subspaces, before imposing symmetry. -/
theorem graphSubmodule_injective :
    Function.Injective (graphSubmodule (p := p) (n := n)) := by
  intro A B h
  have hvec (u : Configuration p n) : A *ᵥ u = B *ᵥ u := by
    have hm : (u, A *ᵥ u) ∈ graphSubmodule B := by
      rw [← h]
      rfl
    exact hm
  exact Matrix.ext_of_mulVec_single fun i => hvec (Pi.single i 1)

/-- The graph has exactly one vector for each configuration. -/
theorem card_graphSubmodule (A : Matrix (Fin n) (Fin n) (ZMod p)) :
    Nat.card (graphSubmodule A) = p^n := by
  rw [Nat.card_congr (graphLinearEquiv A).symm.toEquiv]
  simp [Configuration]

/-- Transversality says precisely that the first projection has zero kernel. -/
theorem firstProjection_injective_of_isTransverse
    (U : Submodule (ZMod p) (PhaseSpace p n)) (hU : IsTransverse U) :
    Function.Injective
      ((LinearMap.fst (ZMod p) (Configuration p n) (Configuration p n)).comp U.subtype) := by
  intro z w hzw
  have hz : z.val-w.val = 0 := hU (z.val-w.val) (U.sub_mem z.property w.property)
    (show z.val.1-w.val.1 = 0 from sub_eq_zero.mpr hzw)
  exact Subtype.ext (sub_eq_zero.mp hz)

/-- The first projection is bijective on a transverse Lagrangian: injectivity
is transversality, and surjectivity follows from the actual dimension equality. -/
def transverseProjectionEquiv (L : Lagrangian p n) (hL : IsTransverse L.val) :
    L.val ≃ₗ[ZMod p] Configuration p n :=
  LinearMap.linearEquivOfInjective (K := ZMod p) (V := L.val) (V₂ := Configuration p n)
    ((LinearMap.fst (ZMod p) (Configuration p n) (Configuration p n)).comp L.val.subtype)
    (firstProjection_injective_of_isTransverse L.val hL)
    (by
      simpa only [Configuration, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using L.property.2)

@[simp]
theorem transverseProjectionEquiv_apply (L : Lagrangian p n)
    (hL : IsTransverse L.val) (z : L.val) :
    transverseProjectionEquiv L hL z = z.val.1 := rfl

@[simp]
theorem transverseProjectionEquiv_symm_fst (L : Lagrangian p n)
    (hL : IsTransverse L.val) (u : Configuration p n) :
    ((transverseProjectionEquiv L hL).symm u).val.1 = u :=
  (transverseProjectionEquiv L hL).apply_symm_apply u

/-- The matrix is constructed from the inverse first projection and the actual
second projection. Its existence is not assumed. -/
def transverseGraphMatrix (L : Lagrangian p n) (hL : IsTransverse L.val) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  LinearMap.toMatrix'
    ((LinearMap.snd (ZMod p) (Configuration p n) (Configuration p n)).comp
      (L.val.subtype.comp (transverseProjectionEquiv L hL).symm.toLinearMap))

@[simp]
theorem transverseGraphMatrix_mulVec (L : Lagrangian p n)
    (hL : IsTransverse L.val) (u : Configuration p n) :
    transverseGraphMatrix L hL *ᵥ u =
      ((transverseProjectionEquiv L hL).symm u).val.2 := by
  rw [transverseGraphMatrix, LinearMap.toMatrix'_mulVec]
  rfl

/-- Every vector of the given Lagrangian is in its constructed graph, and every
vector of the graph lies in that Lagrangian. -/
theorem graphSubmodule_transverseGraphMatrix (L : Lagrangian p n)
    (hL : IsTransverse L.val) :
    graphSubmodule (transverseGraphMatrix L hL) = L.val := by
  ext z
  constructor
  · intro hz
    change z.2 = transverseGraphMatrix L hL *ᵥ z.1 at hz
    have hw : (((transverseProjectionEquiv L hL).symm z.1 : L.val) : PhaseSpace p n) = z := by
      apply Prod.ext (transverseProjectionEquiv_symm_fst L hL z.1)
      exact (transverseGraphMatrix_mulVec L hL z.1).symm.trans hz.symm
    rw [← hw]
    exact ((transverseProjectionEquiv L hL).symm z.1).property
  · intro hz
    change z.2 = transverseGraphMatrix L hL *ᵥ z.1
    rw [transverseGraphMatrix_mulVec]
    exact (congrArg (fun w : L.val => w.val.2)
      ((transverseProjectionEquiv L hL).symm_apply_apply ⟨z, hz⟩)).symm

/-- Isotropy forces the constructed graph matrix to be symmetric, in all
characteristics. -/
theorem transverseGraphMatrix_isSymm (L : Lagrangian p n)
    (hL : IsTransverse L.val) : (transverseGraphMatrix L hL).IsSymm := by
  apply (isIsotropic_graphSubmodule_iff _).mp
  rw [graphSubmodule_transverseGraphMatrix L hL]
  exact L.property.1

/-- Unique symmetric graph coordinates for the full transverse Lagrangian chart. -/
theorem exists_unique_symmetric_graph (L : Lagrangian p n)
    (hL : IsTransverse L.val) :
    ∃! A : Matrix (Fin n) (Fin n) (ZMod p), A.IsSymm ∧ L.val = graphSubmodule A := by
  refine ⟨transverseGraphMatrix L hL,
    ⟨transverseGraphMatrix_isSymm L hL, (graphSubmodule_transverseGraphMatrix L hL).symm⟩, ?_⟩
  intro A hA
  apply graphSubmodule_injective
  exact hA.2.symm.trans (graphSubmodule_transverseGraphMatrix L hL).symm

/-- The actual standard transverse chart, as a subtype of the public
Lagrangian type. -/
abbrev TransverseLagrangian (p n : ℕ) [Fact p.Prime] :=
  {L : Lagrangian p n // IsTransverse L.val}

/-- Classification of every transverse Lagrangian by a unique symmetric matrix. -/
def transverseLagrangianEquivSymmetricMatrices :
    TransverseLagrangian p n ≃ SymmetricMatrices (Fin n) (ZMod p) where
  toFun L := ⟨transverseGraphMatrix L.val L.property,
    transverseGraphMatrix_isSymm L.val L.property⟩
  invFun A := ⟨graphLagrangian A.val A.property, isTransverse_graphSubmodule A.val⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    exact graphSubmodule_transverseGraphMatrix L.val L.property
  right_inv A := by
    apply Subtype.ext
    apply graphSubmodule_injective
    exact graphSubmodule_transverseGraphMatrix
      (graphLagrangian A.val A.property) (isTransverse_graphSubmodule A.val)

@[simp]
theorem transverseLagrangianEquivSymmetricMatrices_apply_val
    (L : TransverseLagrangian p n) :
    (transverseLagrangianEquivSymmetricMatrices L).val =
      transverseGraphMatrix L.val L.property := rfl

@[simp]
theorem transverseLagrangianEquivSymmetricMatrices_symm_val
    (A : SymmetricMatrices (Fin n) (ZMod p)) :
    ((transverseLagrangianEquivSymmetricMatrices (p := p) (n := n)).symm A).val.val =
      graphSubmodule A.val := rfl

end StabilizerLearning.Quantum
