import ExactCriticalCurve.Foundations.MatrixTensorFamily
import ExactCriticalCurve.Quantum.CSS
import ExactCriticalCurve.Quantum.BinaryPauli
import ExactCriticalCurve.Quantum.FiniteGroupProjection

/-! The actual CSS projector as an average of its full finite Pauli constraint group. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- Character orthogonality on an actual binary subspace. -/
theorem pauliSign_subspace_sum (N : Submodule (ZMod 2) (BinaryVector k))
    (y : BinaryVector k) :
    (∑ b : N, pauliSign (binaryDot b.val y)) =
      if y ∈ orthogonal N then (Fintype.card N : ℂ) else 0 := by
  by_cases hy : y ∈ orthogonal N
  · have h : ∀ b : N, binaryDot b.val y = 0 := fun b => hy b.val b.property
    simp [hy, h]
  · rw [if_neg hy]
    obtain ⟨b, hb, hby⟩ : ∃ b ∈ N, binaryDot b y ≠ 0 := by
      simpa only [mem_orthogonal, not_forall, exists_prop] using hy
    let b0 : N := ⟨b,hb⟩
    have hb1 : binaryDot b y = 1 := by
      generalize hz : binaryDot b y = z at hby ⊢
      fin_cases z <;> simp_all
    have hs := Equiv.sum_comp (Equiv.addLeft b0) (fun c : N => pauliSign (binaryDot c.val y))
    change (∑ c : N, pauliSign (binaryDot (b+c.val) y)) = _ at hs
    simp_rw [pauliDot_add_left, pauliSign_add, hb1, pauliSign_one] at hs
    rw [← Finset.mul_sum] at hs
    exact eq_zero_of_mul_eq_self_left (by norm_num : (-1:ℂ) ≠ 1) hs

theorem pauliMatrix_subspace_sum (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) :
    (∑ p : N × N, pauliMatrix p.1.val p.2.val) =
      (Fintype.card N : ℂ) • cosetRelationMatrix (orthogonal N) N := by
  ext x y
  simp only [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul]
  have hi (a : N) :
      (∑ b : N, pauliMatrix a.val b.val x y) =
        if x = y+a.val then
          (if y ∈ orthogonal N then (Fintype.card N : ℂ) else 0) else 0 := by
    by_cases ha : x = y+a.val
    · simp [pauliMatrix, ha, pauliSign_subspace_sum]
    · simp [pauliMatrix, ha]
  simp_rw [hi]
  by_cases hy : y ∈ orthogonal N
  · simp only [if_pos hy]
    by_cases hxy : x-y ∈ N
    · let a0 : N := ⟨x-y,hxy⟩
      have he : x = y+a0.val := by dsimp [a0]; abel
      rw [Finset.sum_eq_single a0]
      · have hx : x ∈ orthogonal N := by
          have h := (orthogonal N).add_mem hy (hN.le_orthogonal hxy)
          simpa only [show y+(x-y)=x by abel] using h
        have hr : x ∈ orthogonal N ∧ y ∈ orthogonal N ∧ x-y ∈ N := ⟨hx,hy,hxy⟩
        simp only [if_pos he, cosetRelationMatrix, if_pos hr, mul_one]
      · intro a _ ha
        have he' : x ≠ y+a.val := by
          intro he'
          apply ha
          apply Subtype.ext
          dsimp [a0]
          rw [he']
          abel
        simp [he']
      · simp
    · have he : ∀ a : N, x ≠ y+a.val := by
        intro a he
        apply hxy
        have h : x-y=a.val := by rw [he]; abel
        simpa only [h] using a.property
      simp [he, cosetRelationMatrix, hxy]
  · simp [hy, cosetRelationMatrix]

theorem pauliMatrix_subspace_sum_eq_projection
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (∑ p : N × N, pauliMatrix p.1.val p.2.val) =
      ((Fintype.card N : ℂ)^2) • cosetProjection (orthogonal N) N := by
  rw [pauliMatrix_subspace_sum N hN, cosetRelationMatrix_eq_card_smul_projection,
    Nat.card_eq_fintype_card, smul_smul, pow_two]

/-- Every column carries an independent pair of shift/clock vectors in N. -/
abbrev CSSConstraintGroup (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :=
  Multiplicative (Fin n → N × N)

def cssConstraintMatrix (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (g : CSSConstraintGroup n N) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  matrixTensorFamily n (fun a => pauliMatrix (g.toAdd a).1.val (g.toAdd a).2.val)

theorem cssConstraintMatrix_one (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :
    cssConstraintMatrix n N 1 = 1 := by
  simp [cssConstraintMatrix]

theorem cssConstraintMatrix_mul (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (g h : CSSConstraintGroup n N) :
    cssConstraintMatrix n N (g*h) = cssConstraintMatrix n N g * cssConstraintMatrix n N h := by
  unfold cssConstraintMatrix
  rw [← matrixTensorFamily_mul]
  congr 1
  funext a
  rw [pauliMatrix_mul, hN.binaryDot_eq_zero (g.toAdd a).2.property (h.toAdd a).1.property,
    pauliSign_zero, one_smul]
  rfl

/-- This representation retains every genuine constraint; no desired covariance is assumed. -/
def cssConstraintRepresentation (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) :
    CSSConstraintGroup n N →* unitary (Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ) where
  toFun g := ⟨cssConstraintMatrix n N g, by
    rw [Matrix.mem_unitaryGroup_iff']
    exact matrixTensorFamily_column_isometry n _ (fun _ => pauliMatrix_adjoint_mul_self _ _)⟩
  map_one' := Subtype.ext (cssConstraintMatrix_one n N)
  map_mul' g h := Subtype.ext (cssConstraintMatrix_mul n N hN g h)

theorem cssConstraintMatrix_sum (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) :
    (∑ g : CSSConstraintGroup n N, cssConstraintMatrix n N g) =
      (Fintype.card (CSSConstraintGroup n N) : ℂ) • cssColumnProjection n N := by
  have hs : (∑ g : CSSConstraintGroup n N, cssConstraintMatrix n N g) =
      matrixTensorPower n (∑ p : N × N, pauliMatrix p.1.val p.2.val) := by
    ext X Y
    simp only [Matrix.sum_apply, matrixTensorPower_apply, cssConstraintMatrix,
      matrixTensorFamily_apply]
    let e : (Fin n → N × N) ≃ CSSConstraintGroup n N :=
      ⟨Multiplicative.ofAdd, Multiplicative.toAdd, fun _ => rfl, fun _ => rfl⟩
    calc
      _ = ∑ f : Fin n → N × N, ∏ a, pauliMatrix (f a).1.val (f a).2.val (X a) (Y a) :=
        (Equiv.sum_comp e (fun g : CSSConstraintGroup n N =>
          ∏ a, pauliMatrix (g.toAdd a).1.val (g.toAdd a).2.val (X a) (Y a))).symm
      _ = _ := (Fintype.prod_sum (fun a (p : N × N) =>
        pauliMatrix p.1.val p.2.val (X a) (Y a))).symm
  rw [hs, pauliMatrix_subspace_sum_eq_projection N hN, matrixTensorPower_smul,
    ← cssColumnProjection_eq_tensorPower]
  congr 1
  simp only [CSSConstraintGroup, Fintype.card_multiplicative, Fintype.card_fun,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_pow, Nat.cast_mul, pow_two]

/-- Exact group-average normalization of the actual CSS projector. -/
theorem cssColumnProjection_eq_constraintAverage (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssColumnProjection n N = finiteGroupProjection (cssConstraintRepresentation n N hN) := by
  unfold finiteGroupProjection
  change _ = (Fintype.card (CSSConstraintGroup n N) : ℂ)⁻¹ •
    (∑ g : CSSConstraintGroup n N, cssConstraintMatrix n N g)
  rw [cssConstraintMatrix_sum n N hN, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

end ExactCriticalCurve.Quantum
