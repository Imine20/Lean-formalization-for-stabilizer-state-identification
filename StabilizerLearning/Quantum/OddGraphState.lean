import StabilizerLearning.Quantum.GraphProjector
import StabilizerLearning.Quantum.TransverseGraph
import StabilizerLearning.FiniteCopy.CoordinateCharacters
import Mathlib.Tactic

/-! Literal odd-prime graph phases for the public XZ Pauli section. -/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- The actual even residue encoding of a p-th root among the 2p-th roots. -/
def oddPhaseLift (t : ZMod p) : ZMod (2*p) := (2*t.val : ℕ)

@[simp] theorem eigenPhase_oddPhaseLift (t : ZMod p) :
    eigenPhase p (oddPhaseLift p t) = rootPhase p t := by
  unfold oddPhaseLift
  rw [eigenPhase_eq_stdAddChar, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold rootPhase
  congr 1
  push_cast
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

/-- Literal half-quadratic-plus-linear exponent, without choosing a phase axiom. -/
def oddGraphExponent (A : Matrix (Fin n) (Fin n) (ZMod p))
    (b x : Configuration p n) : ZMod p :=
  (2 : ZMod p)⁻¹ * dotProduct x (A *ᵥ x) + dotProduct b x

def oddGraphWave (A : Matrix (Fin n) (Fin n) (ZMod p))
    (b : Configuration p n) (x : Configuration p n) : ℂ :=
  rootPhase p (oddGraphExponent p n A b x)

omit [Fact p.Prime] in
theorem symmetric_cross_pairing
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (x y : Configuration p n) :
    dotProduct x (A *ᵥ y) = dotProduct y (A *ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]

@[simp] theorem oddGraphExponent_zero
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (b : Configuration p n) :
    oddGraphExponent p n A b 0 = 0 := by
  simp [oddGraphExponent]

theorem oddGraphExponent_add
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b x y : Configuration p n) :
    oddGraphExponent p n A b (x+y) =
      oddGraphExponent p n A b x + oddGraphExponent p n A b y +
        dotProduct (A *ᵥ x) y := by
  unfold oddGraphExponent
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (A *ᵥ x) y]
  simp only [symmetric_cross_pairing p n A hA y x]
  field_simp
  ring

/-- The sign is forced by the actual XZ action: its eigenphase is -Q(u). -/
theorem oddGraph_phase_derivative
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b u y : Configuration p n) :
    rootPhase p (dotProduct (A *ᵥ u) y) * oddGraphWave p n A b y =
      rootPhase p (-oddGraphExponent p n A b u) *
        oddGraphWave p n A b (y+u) := by
  unfold oddGraphWave
  rw [oddGraphExponent_add p n h2 A hA b y u]
  rw [← rootPhase_add, ← rootPhase_add]
  apply congrArg (rootPhase p)
  rw [dotProduct_comm (A *ᵥ y) u, symmetric_cross_pairing p n A hA u y,
    dotProduct_comm (A *ᵥ u) y]
  ring

theorem oddGraph_pauli_eigenvector
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b u : Configuration p n) :
    pauli p n (u, A *ᵥ u) *ᵥ oddGraphWave p n A b =
      rootPhase p (-oddGraphExponent p n A b u) • oddGraphWave p n A b := by
  classical
  funext x
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (x-u)]
  · simp only [pauli, sub_add_cancel, ite_true, Pi.smul_apply,
      smul_eq_mul]
    simpa only [sub_add_cancel] using oddGraph_phase_derivative p n h2 A hA b u (x-u)
  · intro y _ hy
    have hx : x ≠ y+u := by
      intro h
      apply hy
      rw [h, add_sub_cancel_right]
    simp [pauli, hx]
  · simp

/-- The exact entry needed to identify the group projector with the graph density. -/
theorem oddGraph_outer_entry
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b u y : Configuration p n) :
    rootPhase p (oddGraphExponent p n A b u) *
      rootPhase p (dotProduct (A *ᵥ u) y) =
      oddGraphWave p n A b (y+u) * star (oddGraphWave p n A b y) := by
  unfold oddGraphWave
  rw [rootPhase_star, ← rootPhase_add, ← rootPhase_add,
    oddGraphExponent_add p n h2 A hA b y u]
  apply congrArg (rootPhase p)
  rw [dotProduct_comm (A *ᵥ y) u, symmetric_cross_pairing p n A hA u y,
    dotProduct_comm (A *ᵥ u) y]
  ring

/-- The public XZ section contributes its diagonal half-phase on a graph basis vector. -/
theorem oddGraphExponent_basis
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (b : Configuration p n) (i : Fin n) :
    oddGraphExponent p n A b (Pi.single i 1) = (2 : ZMod p)⁻¹ * A i i + b i := by
  classical
  simp [oddGraphExponent]

/-- Explicit physical assignment in the original 2p-residue encoding. -/
def oddGraphAssignment
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b : Configuration p n) : Assignment p n (graphSubmodule A) := by
  refine ⟨fun z => oddPhaseLift p (-oddGraphExponent p n A b z.val.1), ?_⟩
  constructor
  · intro z
    simp
  · intro z w
    simp only [eigenPhase_oddPhaseLift, Submodule.coe_add, Prod.fst_add]
    rw [oddGraphExponent_add p n h2 A hA]
    change rootPhase p (-(oddGraphExponent p n A b z.val.1 +
      oddGraphExponent p n A b w.val.1 + dotProduct (A *ᵥ z.val.1) w.val.1)) =
      (rootPhase p (dotProduct z.val.2 w.val.1))⁻¹ *
        rootPhase p (-oddGraphExponent p n A b z.val.1) *
        rootPhase p (-oddGraphExponent p n A b w.val.1)
    rw [z.property]
    simp only [rootPhase_neg, rootPhase_add, mul_inv_rev]
    ring

@[simp] theorem oddGraphAssignment_phase
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b u : Configuration p n) :
    eigenPhase p ((oddGraphAssignment p n h2 A hA b).val (graphLinearEquiv A u)) =
      rootPhase p (-oddGraphExponent p n A b u) := by
  simp [oddGraphAssignment, graphLinearEquiv]

theorem oddGraphAssignment_basis_phase
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b : Configuration p n) (i : Fin n) :
    eigenPhase p ((oddGraphAssignment p n h2 A hA b).val
      (graphLinearEquiv A (Pi.single i 1))) =
      rootPhase p (-(2 : ZMod p)⁻¹*A i i-b i) := by
  rw [oddGraphAssignment_phase, oddGraphExponent_basis]
  congr 1
  ring

/-- Equality of the original physical joint projector with the literal normalized
graph-phase density, proved from its defining group sum. -/
theorem jointProjector_oddGraphAssignment
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b : Configuration p n) :
    jointProjector p n (graphSubmodule A) (oddGraphAssignment p n h2 A hA b) =
      ((p : ℂ)^n)⁻¹ • Matrix.vecMulVec (oddGraphWave p n A b)
        (star (oddGraphWave p n A b)) := by
  ext x y
  rw [jointProjector_entry_of_graph_equiv p n _ (graphLinearEquiv A).toEquiv
    (fun _ => rfl) (finrank_graphSubmodule A)]
  simp only [LinearEquiv.coe_toEquiv, oddGraphAssignment_phase, rootPhase_neg, inv_inv,
    coe_graphLinearEquiv_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Pi.star_apply]
  rw [mul_assoc, oddGraph_outer_entry p n h2 A hA]
  congr 2
  simp

/-- The ratio of two actual assignments on the same graph is a genuine
additive character, since the public section cocycle cancels. -/
def graphAssignmentRatioChar
    (A : Matrix (Fin n) (Fin n) (ZMod p))
    (η η₀ : Assignment p n (graphSubmodule A)) : AddChar (Configuration p n) ℂ where
  toFun u := eigenPhase p (η.val (graphLinearEquiv A u)) /
    eigenPhase p (η₀.val (graphLinearEquiv A u))
  map_zero_eq_one' := by simp
  map_add_eq_mul' u v := by
    simp only [map_add, η.property.2, η₀.property.2]
    have hc : sectionCocycle p n (graphLinearEquiv A u) (graphLinearEquiv A v) ≠ 0 :=
      rootPhase_ne_zero _ _
    field_simp

theorem standardCoordinateEquiv_rootPhase (c u : Configuration p n) :
    CoordinateCharacters.standardCoordinateEquiv (fun _ : Fin n => p) c u =
      rootPhase p (dotProduct c u) := by
  rw [rootPhase_eq_stdAddChar]
  simp only [CoordinateCharacters.standardCoordinateEquiv_apply, dotProduct,
    CharacterEnsemble.character_sum]

theorem oddGraphAssignment_injective
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm) :
    Function.Injective (oddGraphAssignment p n h2 A hA) := by
  intro b c h
  have hd (u : Configuration p n) : dotProduct b u = dotProduct c u := by
    have hp := congrArg (fun η : Assignment p n (graphSubmodule A) =>
      eigenPhase p (η.val (graphLinearEquiv A u))) h
    simp only [oddGraphAssignment_phase] at hp
    have hQ := neg_injective ((rootPhase_injective p) hp)
    exact add_left_cancel hQ
  funext i
  simpa using hd (Pi.single i 1)

/-- Every cocycle-compatible encoded assignment is obtained from a linear
coefficient. Full character duality supplies the coefficient; injectivity of
the concrete 2p-th-root phase recovers the actual residue labels. -/
theorem oddGraphAssignment_surjective
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm) :
    Function.Surjective (oddGraphAssignment p n h2 A hA) := by
  intro η
  obtain ⟨c, hc⟩ := (CoordinateCharacters.standardCoordinateEquiv
    (fun _ : Fin n => p)).surjective
      (graphAssignmentRatioChar p n A η (oddGraphAssignment p n h2 A hA 0))
  refine ⟨-c, ?_⟩
  apply Subtype.ext
  funext z
  obtain ⟨u, rfl⟩ := (graphLinearEquiv A).surjective z
  apply eigenPhase_injective p
  rw [oddGraphAssignment_phase]
  have hr := DFunLike.congr_fun hc u
  rw [standardCoordinateEquiv_rootPhase p n] at hr
  change rootPhase p (dotProduct c u) =
    eigenPhase p (η.val (graphLinearEquiv A u)) /
      eigenPhase p ((oddGraphAssignment p n h2 A hA 0).val (graphLinearEquiv A u)) at hr
  rw [oddGraphAssignment_phase] at hr
  have hv := (eq_div_iff (rootPhase_ne_zero p _)).mp hr
  rw [← hv, ← rootPhase_add]
  apply congrArg (rootPhase p)
  simp only [oddGraphExponent, neg_dotProduct, zero_dotProduct, add_zero]
  ring

/-- Complete fixed-graph assignment parametrization, without an existence or
surjectivity assumption on assignments or characters. -/
def oddGraphAssignmentEquiv
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm) :
    Configuration p n ≃ Assignment p n (graphSubmodule A) :=
  Equiv.ofBijective (oddGraphAssignment p n h2 A hA)
    ⟨oddGraphAssignment_injective p n h2 A hA, oddGraphAssignment_surjective p n h2 A hA⟩

@[simp] theorem oddGraphAssignmentEquiv_apply
    (h2 : (2 : ZMod p) ≠ 0)
    (A : Matrix (Fin n) (Fin n) (ZMod p)) (hA : A.IsSymm)
    (b : Configuration p n) :
    oddGraphAssignmentEquiv p n h2 A hA b = oddGraphAssignment p n h2 A hA b := rfl

end StabilizerLearning.Quantum
