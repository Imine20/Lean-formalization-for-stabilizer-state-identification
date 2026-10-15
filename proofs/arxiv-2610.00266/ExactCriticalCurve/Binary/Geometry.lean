import ExactCriticalCurve.Binary.Quadratic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Binary defects and stochastic Lagrangian relations

All quadratic isotropy conditions use the full ZMod 4 refinement.
The bilinear form below is exactly the existing binary coordinate dot product.
See arXiv:2610.00266v1, main.tex lines 436–441 and 461–469.
-/

namespace ExactCriticalCurve.Binary

/-- The existing binary dot product, bundled with its two linearity proofs. -/
def binaryDotForm (k : ℕ) : LinearMap.BilinForm (ZMod 2) (BinaryVector k) :=
  dotProductBilin (ZMod 2) (ZMod 2)

@[simp] theorem binaryDotForm_apply {k : ℕ} (x y : BinaryVector k) :
    binaryDotForm k x y = binaryDot x y := rfl

theorem binaryDot_comm {k : ℕ} (x y : BinaryVector k) :
    binaryDot x y = binaryDot y x := dotProduct_comm x y

theorem binaryDotForm_isSymm (k : ℕ) : (binaryDotForm k).IsSymm :=
  ⟨binaryDot_comm⟩

theorem binaryDotForm_isRefl (k : ℕ) : (binaryDotForm k).IsRefl := by
  intro x y h
  simpa only [binaryDotForm_apply, binaryDot_comm y x] using h

theorem binaryDotForm_nondegenerate (k : ℕ) : (binaryDotForm k).Nondegenerate := by
  intro x hx
  exact dotProduct_eq_zero x hx

/-- The right orthogonal complement for the fixed binary dot product. -/
def orthogonal {k : ℕ} (N : Submodule (ZMod 2) (BinaryVector k)) :
    Submodule (ZMod 2) (BinaryVector k) :=
  (binaryDotForm k).orthogonal N

@[simp] theorem mem_orthogonal {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (x : BinaryVector k) :
    x ∈ orthogonal N ↔ ∀ z ∈ N, binaryDot z x = 0 := Iff.rfl

/-- A defect is totally isotropic for the full mod-four quadratic refinement. -/
def IsDefect {k : ℕ} (N : Submodule (ZMod 2) (BinaryVector k)) : Prop :=
  ∀ x ∈ N, weightQuadratic x = 0

/-- Quadratic isotropy forces binary pairwise orthogonality. -/
theorem IsDefect.binaryDot_eq_zero {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N)
    {x y : BinaryVector k} (hx : x ∈ N) (hy : y ∈ N) :
    binaryDot x y = 0 := by
  have h := weightQuadratic_add x y
  rw [hN _ (N.add_mem hx hy), hN _ hx, hN _ hy, zero_add, zero_add] at h
  exact (two_mul_bitLift_eq_zero_iff _).mp h.symm

theorem IsDefect.le_orthogonal {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    N ≤ orthogonal N := by
  intro x hx
  exact fun z hz => hN.binaryDot_eq_zero hz hx

theorem IsDefect.allOnes_mem_orthogonal {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    allOnes k ∈ orthogonal N := by
  intro z hz
  change binaryDot z (allOnes k) = 0
  rw [← binaryDot_self_eq_dot_allOnes]
  exact hN.binaryDot_eq_zero hz hz

/-- The mod-four relation form on the direct sum of two binary spaces. -/
def relationQuadratic {k : ℕ} (p : BinaryVector k × BinaryVector k) : ZMod 4 :=
  weightQuadratic p.1 - weightQuadratic p.2

/-- The actual identity relation on the quotient by a defect. -/
def defectRelation {k : ℕ} (N : Submodule (ZMod 2) (BinaryVector k)) :
    Submodule (ZMod 2) (BinaryVector k × BinaryVector k) :=
  (orthogonal N).comap (LinearMap.fst (ZMod 2) (BinaryVector k) (BinaryVector k)) ⊓
    ((orthogonal N).comap (LinearMap.snd (ZMod 2) (BinaryVector k) (BinaryVector k)) ⊓
      N.comap (LinearMap.fst (ZMod 2) (BinaryVector k) (BinaryVector k) -
        LinearMap.snd (ZMod 2) (BinaryVector k) (BinaryVector k)))

@[simp] theorem mem_defectRelation {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (p : BinaryVector k × BinaryVector k) :
    p ∈ defectRelation N ↔
      p.1 ∈ orthogonal N ∧ p.2 ∈ orthogonal N ∧ p.1 - p.2 ∈ N := Iff.rfl

/-- Actual binary relations satisfying the paper's three defining conditions. -/
structure StochasticLagrangian (k : ℕ) where
  carrier : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)
  finrank_eq : Module.finrank (ZMod 2) carrier = k
  quadratic_zero : ∀ p ∈ carrier, relationQuadratic p = 0
  allOnes_mem : (allOnes k, allOnes k) ∈ carrier


/-- The dimensions of a subspace and its binary orthogonal complement add to k. -/
theorem finrank_orthogonal_add {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    Module.finrank (ZMod 2) (orthogonal N) + Module.finrank (ZMod 2) N = k := by
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal
    (B := binaryDotForm k) (binaryDotForm_isRefl k) N
  rw [LinearMap.BilinForm.orthogonal_top_eq_bot
    (binaryDotForm_nondegenerate k) (binaryDotForm_isRefl k), inf_bot_eq,
    finrank_bot, add_zero] at h
  simpa only [orthogonal, BinaryVector, Module.finrank_pi, Fintype.card_fin,
    Nat.add_comm] using h

/-- Explicit coordinates on the defect relation: (y,d) maps to (y+d,y). -/
def defectRelationEquiv {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    (orthogonal N × N) ≃ₗ[ZMod 2] defectRelation N where
  toFun p := ⟨(p.1.val + p.2.val, p.1.val),
    ⟨(orthogonal N).add_mem p.1.property (hN.le_orthogonal p.2.property),
      p.1.property, by simp⟩⟩
  invFun p := (⟨p.val.2, p.property.2.1⟩,
    ⟨p.val.1 - p.val.2, p.property.2.2⟩)
  left_inv p := by
    ext <;> simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change p.val.2 + (p.val.1 - p.val.2) = p.val.1
      abel
    · rfl
  map_add' p q := by
    apply Subtype.ext
    apply Prod.ext
    · change (p.1.val + q.1.val) + (p.2.val + q.2.val) =
        (p.1.val + p.2.val) + (q.1.val + q.2.val)
      abel
    · rfl
  map_smul' a p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (smul_add a p.1.val p.2.val).symm
    · rfl

/-- The relation has the required dimension as a proved consequence of defect isotropy. -/
theorem IsDefect.finrank_defectRelation {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    Module.finrank (ZMod 2) (defectRelation N) = k := by
  rw [← (defectRelationEquiv hN).finrank_eq, Module.finrank_prod]
  exact finrank_orthogonal_add N

theorem IsDefect.relationQuadratic_zero {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N)
    (p : BinaryVector k × BinaryVector k) (hp : p ∈ defectRelation N) :
    relationQuadratic p = 0 := by
  have hd : binaryDot (p.1 - p.2) p.2 = 0 := hp.2.1 _ hp.2.2
  have hq : weightQuadratic (p.1 - p.2) = 0 := hN _ hp.2.2
  have h := weightQuadratic_add (p.1 - p.2) p.2
  rw [sub_add_cancel, hq, hd, bitLift_zero, mul_zero, zero_add, add_zero] at h
  exact sub_eq_zero.mpr h

theorem IsDefect.allOnes_mem_defectRelation {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    (allOnes k, allOnes k) ∈ defectRelation N := by
  exact ⟨hN.allOnes_mem_orthogonal, hN.allOnes_mem_orthogonal,
    by simp⟩

/-- A defect gives an actual stochastic Lagrangian relation, with all fields proved. -/
def IsDefect.stochasticLagrangian {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    StochasticLagrangian k where
  carrier := defectRelation N
  finrank_eq := hN.finrank_defectRelation
  quadratic_zero := hN.relationQuadratic_zero
  allOnes_mem := hN.allOnes_mem_defectRelation

@[simp] theorem IsDefect.stochasticLagrangian_carrier {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    hN.stochasticLagrangian.carrier = defectRelation N := rfl


@[ext] theorem StochasticLagrangian.ext {k : ℕ}
    {T U : StochasticLagrangian k} (h : T.carrier = U.carrier) : T = U := by
  cases T
  cases U
  cases h
  rfl

/-- The index type is finite because its actual relations inject into a finite powerset. -/
instance finiteStochasticLagrangian (k : ℕ) : Finite (StochasticLagrangian k) :=
  Finite.of_injective
    (fun T : StochasticLagrangian k =>
      (T.carrier : Set (BinaryVector k × BinaryVector k))) (by
        intro T U h
        exact StochasticLagrangian.ext (SetLike.coe_injective h))

noncomputable instance fintypeStochasticLagrangian (k : ℕ) :
    Fintype (StochasticLagrangian k) := Fintype.ofFinite _

end ExactCriticalCurve.Binary
