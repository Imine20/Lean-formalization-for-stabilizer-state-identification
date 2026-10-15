import StabilizerLearning.Quantum.GraphProjector
import StabilizerLearning.Quantum.TransverseGraph
import StabilizerLearning.FiniteCopy.CoordinatePhase

/-! Binary graph states in the original XZ Pauli section. The quadratic
refinement retains every mod-four diagonal coefficient. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning.Quantum
open CoordinateCharacters

/-- Doubling the literal bit lift is an additive homomorphism. -/
def binaryTwice : ZMod 2 →+ ZMod 4 where
  toFun x := 2*binaryBitLift x
  map_zero' := by decide
  map_add' x y := by fin_cases x <;> fin_cases y <;> decide

theorem binaryTwice_character (x : ZMod 2) :
    (ZMod.stdAddChar (binaryTwice x) : ℂ) = ZMod.stdAddChar x := by
  fin_cases x
  · change ZMod.stdAddChar (0 : ZMod 4) = ZMod.stdAddChar (0 : ZMod 2)
    simp
  · have h : binaryTwice (1 : ZMod 2) = (2 : ZMod 4) := by decide
    change ZMod.stdAddChar (binaryTwice (1 : ZMod 2)) = ZMod.stdAddChar (1 : ZMod 2)
    rw [h, standardCharacter_four, standardCharacter_two]
    change Complex.I^2 = (-1 : ℂ)^1
    norm_num

theorem binaryBitLift_polar (a : ZMod 4) (x y : ZMod 2) :
    a*binaryBitLift (x+y) =
      a*binaryBitLift x+a*binaryBitLift y+binaryTwice (binaryParity a*x*y) := by
  fin_cases a <;> fin_cases x <;> fin_cases y <;> decide

variable {n : ℕ}

/-- The actual symmetric binary shadow: diagonal parity and original edges. -/
def binaryGraphMatrix (g : BinaryParameters n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  (binaryEnhancedFromCoordinates g.1 g.2).val.2.val

theorem binaryGraphMatrix_isSymm (g : BinaryParameters n) : (binaryGraphMatrix g).IsSymm :=
  (binaryEnhancedFromCoordinates g.1 g.2).val.2.property

@[simp] theorem binaryGraphMatrix_diag (g : BinaryParameters n) (i : Fin n) :
    binaryGraphMatrix g i i = binaryParity (g.1 i) :=
  (binaryEnhancedFromCoordinates g.1 g.2).property i

theorem binaryGraphMatrix_upper (g : BinaryParameters n) (i j : Fin n) (h : i < j) :
    binaryGraphMatrix g i j = g.2 ⟨(i,j),h⟩ := by
  simp [binaryGraphMatrix, binaryEnhancedFromCoordinates, h]

/-- The source quadratic refinement q_g, valued in ZMod 4. -/
def binaryGraphQ (g : BinaryParameters n) (x : Configuration 2 n) : ZMod 4 :=
  (∑ i, g.1 i*binaryBitLift (x i)) +
    binaryTwice (∑ e, g.2 e*(x e.val.1*x e.val.2))

/-- Literal source phase: the diagonal fourth-root and edge sign factors. -/
def binaryGraphPhase (g : BinaryParameters n) (x : Configuration 2 n) : ℂ :=
  ZMod.stdAddChar (∑ i, g.1 i*binaryBitLift (x i)) *
    ZMod.stdAddChar (∑ e, g.2 e*(x e.val.1*x e.val.2))

theorem binaryGraphPhase_eq_character (g : BinaryParameters n) (x : Configuration 2 n) :
    binaryGraphPhase g x = ZMod.stdAddChar (binaryGraphQ g x) := by
  unfold binaryGraphPhase binaryGraphQ
  rw [AddChar.map_add_eq_mul, binaryTwice_character]

@[simp] theorem binaryGraphQ_zero (g : BinaryParameters n) : binaryGraphQ g 0 = 0 := by
  simp [binaryGraphQ, binaryBitLift]

@[simp] theorem binaryGraphPhase_zero (g : BinaryParameters n) : binaryGraphPhase g 0 = 1 := by
  rw [binaryGraphPhase_eq_character, binaryGraphQ_zero, AddChar.map_zero_eq_one]

theorem binaryGraphPhase_eq_eigenPhase (g : BinaryParameters n) (x : Configuration 2 n) :
    binaryGraphPhase g x = eigenPhase 2 (binaryGraphQ g x) := by
  rw [binaryGraphPhase_eq_character, eigenPhase_eq_stdAddChar]

@[simp] theorem norm_binaryGraphPhase (g : BinaryParameters n) (x : Configuration 2 n) :
    ‖binaryGraphPhase g x‖ = 1 := by
  rw [binaryGraphPhase_eq_eigenPhase]
  exact norm_eigenPhase 2 _

theorem binaryGraphPhase_ne_zero (g : BinaryParameters n) (x : Configuration 2 n) :
    binaryGraphPhase g x ≠ 0 := by
  rw [binaryGraphPhase_eq_eigenPhase]
  exact eigenPhase_ne_zero 2 _

theorem binaryGraphQ_add_expanded (g : BinaryParameters n) (x y : Configuration 2 n) :
    binaryGraphQ g (x+y) = binaryGraphQ g x+binaryGraphQ g y+
      binaryTwice ((∑ i, binaryParity (g.1 i)*x i*y i) +
        ∑ e, g.2 e*(x e.val.1*y e.val.2+y e.val.1*x e.val.2)) := by
  unfold binaryGraphQ
  simp only [Pi.add_apply, binaryBitLift_polar, Finset.sum_add_distrib, map_add]
  have he : (∑ e : BinaryOffDiagonal (Fin n),
      g.2 e*((x e.val.1+y e.val.1)*(x e.val.2+y e.val.2))) =
      (∑ e, g.2 e*(x e.val.1*x e.val.2)) +
      (∑ e, g.2 e*(y e.val.1*y e.val.2)) +
      (∑ e, g.2 e*(x e.val.1*y e.val.2+y e.val.1*x e.val.2)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he]
  simp only [map_add, map_sum]
  ring

private theorem sum_strict_pairs (f : Fin n → Fin n → ZMod 2) :
    (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + ∑ e : BinaryOffDiagonal (Fin n), (f e.val.1 e.val.2+f e.val.2 e.val.1) := by
  classical
  have ht (F : Fin n → Fin n → ZMod 2) :
      (∑ e : BinaryOffDiagonal (Fin n), F e.val.1 e.val.2) =
        ∑ i, ∑ j, if i < j then F i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2))
      (by simp) (fun ij => F ij.1 ij.2)]
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_add_distrib, ht f, ht (fun i j => f j i)]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j i else 0)]
  have he : (∑ i, f i i) = ∑ i, ∑ j, if i = j then f i j else 0 := by simp
  rw [he, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, not_lt.mpr h.le]
  · simp
  · simp [h, h.ne', not_lt.mpr h.le]

theorem binaryGraphMatrix_bilinear (g : BinaryParameters n) (x y : Configuration 2 n) :
    dotProduct ((binaryGraphMatrix g).mulVec x) y =
      (∑ i, binaryParity (g.1 i)*x i*y i) +
        ∑ e, g.2 e*(x e.val.1*y e.val.2+y e.val.1*x e.val.2) := by
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  rw [sum_strict_pairs]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [binaryGraphMatrix_diag]
  · apply Finset.sum_congr rfl
    intro e _
    rw [(binaryGraphMatrix_isSymm g).apply e.val.1 e.val.2,
      binaryGraphMatrix_upper g e.val.1 e.val.2 e.property]
    ring

/-- The defining binary polarization identity, including diagonal parity. -/
theorem binaryGraphQ_add (g : BinaryParameters n) (x y : Configuration 2 n) :
    binaryGraphQ g (x+y) = binaryGraphQ g x+binaryGraphQ g y+
      binaryTwice (dotProduct ((binaryGraphMatrix g).mulVec x) y) := by
  rw [binaryGraphQ_add_expanded, binaryGraphMatrix_bilinear]


theorem eigenPhase_binaryTwice (t : ZMod 2) :
    eigenPhase 2 (binaryTwice t) = rootPhase 2 t := by
  rw [eigenPhase_eq_stdAddChar, rootPhase_eq_stdAddChar, binaryTwice_character]

theorem binaryGraphPhase_add (g : BinaryParameters n) (x y : Configuration 2 n) :
    binaryGraphPhase g (x+y) = binaryGraphPhase g x*binaryGraphPhase g y*
      rootPhase 2 (dotProduct ((binaryGraphMatrix g).mulVec x) y) := by
  simp only [binaryGraphPhase_eq_character, binaryGraphQ_add,
    AddChar.map_add_eq_mul, binaryTwice_character, rootPhase_eq_stdAddChar]

/-- The actual compatible eigenvalue assignment is minus the quadratic refinement. -/
def binaryGraphAssignment (g : BinaryParameters n) :
    Assignment 2 n (graphSubmodule (binaryGraphMatrix g)) := by
  refine ⟨fun z => -binaryGraphQ g z.val.1, ?_, ?_⟩
  · intro z
    exact norm_eigenPhase 2 _
  · intro z w
    change eigenPhase 2 (-binaryGraphQ g (z.val.1+w.val.1)) =
      (sectionCocycle 2 n z w)⁻¹ * eigenPhase 2 (-binaryGraphQ g z.val.1) *
        eigenPhase 2 (-binaryGraphQ g w.val.1)
    rw [eigenPhase_neg, binaryGraphQ_add, eigenPhase_add, eigenPhase_add,
      eigenPhase_binaryTwice, eigenPhase_neg, eigenPhase_neg]
    have hz := (mem_graphSubmodule (binaryGraphMatrix g) z.val).mp z.property
    simp only [sectionCocycle, hz, mul_inv_rev]
    ring

@[simp] theorem binaryGraphAssignment_apply (g : BinaryParameters n)
    (u : Configuration 2 n) :
    (binaryGraphAssignment g).val (graphLinearEquiv (binaryGraphMatrix g) u) =
      -binaryGraphQ g u := rfl

theorem binaryGraphPhase_sub_ratio (g : BinaryParameters n) (x y : Configuration 2 n) :
    binaryGraphPhase g (x-y)*rootPhase 2 (dotProduct ((binaryGraphMatrix g).mulVec (x-y)) y) =
      binaryGraphPhase g x*star (binaryGraphPhase g y) := by
  have h := binaryGraphPhase_add g (x-y) y
  rw [sub_add_cancel] at h
  have hs : star (binaryGraphPhase g y) = (binaryGraphPhase g y)⁻¹ := by
    rw [binaryGraphPhase_eq_eigenPhase, eigenPhase_star, eigenPhase_neg]
  rw [hs, h]
  have hn := binaryGraphPhase_ne_zero g y
  field_simp

/-- The normalized literal source outer product, in total-dimension coordinates. -/
def binaryGraphDensity (g : BinaryParameters n) :
    Matrix (Configuration 2 n) (Configuration 2 n) ℂ :=
  ((2 : ℂ)^n)⁻¹ • Matrix.vecMulVec (binaryGraphPhase g) (star (binaryGraphPhase g))

theorem jointProjector_eq_binaryGraphDensity (g : BinaryParameters n) :
    jointProjector 2 n (graphSubmodule (binaryGraphMatrix g)) (binaryGraphAssignment g) =
      binaryGraphDensity g := by
  ext x y
  rw [jointProjector_entry_of_graph_equiv 2 n _ (graphLinearEquiv _).toEquiv
    (fun _ => rfl) (finrank_graphSubmodule _) (binaryGraphAssignment g)]
  change ((2 : ℂ)^n)⁻¹ * (eigenPhase 2 (-binaryGraphQ g (x-y)))⁻¹ *
      rootPhase 2 (dotProduct ((binaryGraphMatrix g).mulVec (x-y)) y) =
    ((2 : ℂ)^n)⁻¹ * (binaryGraphPhase g x*star (binaryGraphPhase g y))
  rw [eigenPhase_neg, inv_inv, ← binaryGraphPhase_eq_eigenPhase]
  rw [mul_assoc, binaryGraphPhase_sub_ratio]

/-- A concrete original physical stabilizer label for every source parameter. -/
def binaryGraphLabel (g : BinaryParameters n) : StabilizerLabel 2 n :=
  ⟨graphLagrangian (binaryGraphMatrix g) (binaryGraphMatrix_isSymm g), binaryGraphAssignment g⟩

theorem labelProjector_binaryGraphLabel (g : BinaryParameters n) :
    labelProjector 2 n (binaryGraphLabel g) = binaryGraphDensity g :=
  jointProjector_eq_binaryGraphDensity g

theorem binaryGraphDensity_isPureStabilizer (g : BinaryParameters n) :
    IsPureStabilizer 2 n (binaryGraphDensity g) := by
  rw [← labelProjector_binaryGraphLabel]
  exact labelProjector_isPureStabilizer 2 n (binaryGraphLabel g)

theorem binaryGraph_pauli_eigen (g : BinaryParameters n) (u : Configuration 2 n) :
    pauli 2 n (u,(binaryGraphMatrix g).mulVec u)*binaryGraphDensity g =
      eigenPhase 2 (-binaryGraphQ g u) • binaryGraphDensity g := by
  rw [← jointProjector_eq_binaryGraphDensity]
  exact pauli_mul_jointProjector 2 n _ (binaryGraphAssignment g)
    (graphLinearEquiv (binaryGraphMatrix g) u)

@[simp] theorem binaryGraphQ_basis (g : BinaryParameters n) (i : Fin n) :
    binaryGraphQ g (Pi.single i 1) = g.1 i := by
  classical
  have he (e : BinaryOffDiagonal (Fin n)) :
      ((Pi.single i (1 : ZMod 2) : Configuration 2 n) e.val.1)*
        ((Pi.single i (1 : ZMod 2) : Configuration 2 n) e.val.2) = 0 := by
    by_cases h : e.val.1 = i
    · have hj : e.val.2 ≠ i := by
        intro hj
        have hh := e.property
        rw [h, hj] at hh
        exact (lt_irrefl i) hh
      simp [Pi.single_apply, h, hj]
    · simp [Pi.single_apply, h]
  unfold binaryGraphQ
  simp only [he, mul_zero, Finset.sum_const_zero, map_zero, add_zero]
  rw [Finset.sum_eq_single i]
  · have h1 : binaryBitLift (1 : ZMod 2) = 1 := by decide
    simp [h1]
  · intro j _ hji
    have h0 : binaryBitLift (0 : ZMod 2) = 0 := by decide
    simp [hji, h0]
  · simp


/-- The encoded quadratic refinement associated to any actual compatible
assignment on a binary graph. -/
def binaryAssignmentQ (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (η : Assignment 2 n (graphSubmodule A)) (u : Configuration 2 n) : ZMod 4 :=
  -η.val (graphLinearEquiv A u)

@[simp] theorem binaryAssignmentQ_zero (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (η : Assignment 2 n (graphSubmodule A)) : binaryAssignmentQ A η 0 = 0 := by
  have h : η.val 0 = 0 :=
    (eigenPhase_eq_one_iff 2 _).mp (assignment_phase_zero 2 n _ η)
  simp [binaryAssignmentQ, h]

theorem binaryAssignmentQ_add (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (η : Assignment 2 n (graphSubmodule A)) (u v : Configuration 2 n) :
    binaryAssignmentQ A η (u+v) =
      binaryAssignmentQ A η u+binaryAssignmentQ A η v+
        binaryTwice (dotProduct (A.mulVec u) v) := by
  have hc := η.property.2 (graphLinearEquiv A u) (graphLinearEquiv A v)
  rw [← map_add] at hc
  have hc' : eigenPhase 2 (η.val (graphLinearEquiv A (u+v))) =
      (rootPhase 2 (dotProduct (A.mulVec u) v))⁻¹ *
        eigenPhase 2 (η.val (graphLinearEquiv A u)) *
        eigenPhase 2 (η.val (graphLinearEquiv A v)) := hc
  apply eigenPhase_injective 2
  unfold binaryAssignmentQ
  rw [eigenPhase_neg, hc', eigenPhase_add, eigenPhase_add,
    eigenPhase_neg, eigenPhase_neg, eigenPhase_binaryTwice]
  simp only [mul_inv_rev, inv_inv]
  ring

private theorem binaryParity_of_polar_self (a : ZMod 4) (d : ZMod 2)
    (h : 0 = a+a+binaryTwice d) : binaryParity a = d := by
  revert h
  fin_cases a <;> fin_cases d <;> decide

theorem binaryAssignmentQ_basis_parity (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (η : Assignment 2 n (graphSubmodule A)) (i : Fin n) :
    binaryParity (binaryAssignmentQ A η (Pi.single i 1)) = A i i := by
  have h := binaryAssignmentQ_add A η (Pi.single i 1) (Pi.single i 1)
  have he : (Pi.single i 1 : Configuration 2 n)+Pi.single i 1 = 0 := by
    funext j
    exact CharTwo.add_self_eq_zero ((Pi.single i (1 : ZMod 2) : Configuration 2 n) j)
  rw [he, binaryAssignmentQ_zero] at h
  apply binaryParity_of_polar_self
  simpa [Matrix.mulVec_single_one, dotProduct_single_one, Matrix.col_apply] using h

/-- Recover the complete original alpha/edge source parameter from physical data. -/
def binaryParametersOfAssignment (A : SymmetricMatrices (Fin n) (ZMod 2))
    (η : Assignment 2 n (graphSubmodule A.val)) : BinaryParameters n :=
  (fun i => binaryAssignmentQ A.val η (Pi.single i 1),
    fun e => A.val e.val.1 e.val.2)

theorem binaryGraphMatrix_parametersOfAssignment
    (A : SymmetricMatrices (Fin n) (ZMod 2))
    (η : Assignment 2 n (graphSubmodule A.val)) :
    binaryGraphMatrix (binaryParametersOfAssignment A η) = A.val := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [binaryGraphMatrix_upper _ i j h]
    rfl
  · rw [binaryGraphMatrix_diag]
    exact binaryAssignmentQ_basis_parity A.val η i
  · calc
      binaryGraphMatrix (binaryParametersOfAssignment A η) i j =
          binaryGraphMatrix (binaryParametersOfAssignment A η) j i :=
        ((binaryGraphMatrix_isSymm _).apply i j).symm
      _ = A.val j i := binaryGraphMatrix_upper _ j i h
      _ = A.val i j := A.property.apply i j


theorem binaryGraphQ_parametersOfAssignment
    (A : SymmetricMatrices (Fin n) (ZMod 2))
    (η : Assignment 2 n (graphSubmodule A.val)) (u : Configuration 2 n) :
    binaryGraphQ (binaryParametersOfAssignment A η) u = binaryAssignmentQ A.val η u := by
  classical
  let d : Configuration 2 n →+ ZMod 4 :=
    { toFun := fun x => binaryGraphQ (binaryParametersOfAssignment A η) x-binaryAssignmentQ A.val η x
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [binaryGraphQ_add, binaryAssignmentQ_add, binaryGraphMatrix_parametersOfAssignment]
        ring }
  have hd (i : Fin n) : d (Pi.single i 1) = 0 := by
    change binaryGraphQ (binaryParametersOfAssignment A η) (Pi.single i 1)-
      binaryAssignmentQ A.val η (Pi.single i 1) = 0
    rw [binaryGraphQ_basis]
    simp [binaryParametersOfAssignment]
  have hds (i : Fin n) (v : ZMod 2) : d (Pi.single i v) = 0 := by
    fin_cases v
    · simp
    · exact hd i
  have hdu : d u = 0 := by
    calc
      d u = d (∑ i, Pi.single i (u i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i, d (Pi.single i (u i)) := map_sum d _ _
      _ = 0 := by simp only [hds, Finset.sum_const_zero]
  exact sub_eq_zero.mp hdu

/-- All original graph labels, including every compatible assignment. -/
abbrev BinaryGraphPhysicalLabel (n : ℕ) :=
  (A : SymmetricMatrices (Fin n) (ZMod 2)) × Assignment 2 n (graphSubmodule A.val)

def binaryParametersToPhysicalGraph (g : BinaryParameters n) : BinaryGraphPhysicalLabel n :=
  ⟨⟨binaryGraphMatrix g, binaryGraphMatrix_isSymm g⟩, binaryGraphAssignment g⟩

def binaryPhysicalGraphToParameters (z : BinaryGraphPhysicalLabel n) : BinaryParameters n :=
  binaryParametersOfAssignment z.1 z.2

theorem binaryPhysicalGraphToParameters_left_inv :
    Function.LeftInverse (@binaryPhysicalGraphToParameters n) binaryParametersToPhysicalGraph := by
  intro g
  apply Prod.ext
  · funext i
    change -(-binaryGraphQ g (Pi.single i 1)) = g.1 i
    rw [neg_neg, binaryGraphQ_basis]
  · funext e
    exact binaryGraphMatrix_upper g e.val.1 e.val.2 e.property

private theorem binaryPhysicalGraph_ext (z w : BinaryGraphPhysicalLabel n)
    (hA : z.1 = w.1)
    (hη : ∀ u, z.2.val (graphLinearEquiv z.1.val u) =
      w.2.val (graphLinearEquiv w.1.val u)) : z = w := by
  rcases z with ⟨A, η⟩
  rcases w with ⟨B, θ⟩
  dsimp only at hA hη
  cases hA
  have he : η = θ := by
    apply Subtype.ext
    funext z
    have hz : graphLinearEquiv A.val z.val.1 = z :=
      (graphLinearEquiv A.val).apply_symm_apply z
    simpa only [hz] using hη z.val.1
  subst θ
  rfl

theorem binaryParametersToPhysicalGraph_surjective :
    Function.Surjective (@binaryParametersToPhysicalGraph n) := by
  rintro ⟨A, η⟩
  let g := binaryParametersOfAssignment A η
  have hm : (⟨binaryGraphMatrix g, binaryGraphMatrix_isSymm g⟩ :
      SymmetricMatrices (Fin n) (ZMod 2)) = A :=
    Subtype.ext (binaryGraphMatrix_parametersOfAssignment A η)
  have hq : ∀ u, -binaryGraphQ g u = η.val (graphLinearEquiv A.val u) := by
    intro u
    rw [binaryGraphQ_parametersOfAssignment]
    exact neg_neg _
  refine ⟨g, ?_⟩
  apply binaryPhysicalGraph_ext _ _ hm
  intro u
  exact hq u

/-- Exact original source-parameter / physical-graph-label correspondence.
No surjectivity, assignment-completion, or phase premise is supplied. -/
def binaryParametersPhysicalGraphEquiv (n : ℕ) :
    BinaryParameters n ≃ BinaryGraphPhysicalLabel n :=
  Equiv.ofBijective binaryParametersToPhysicalGraph
    ⟨binaryPhysicalGraphToParameters_left_inv.injective, binaryParametersToPhysicalGraph_surjective⟩

end StabilizerLearning.Quantum
