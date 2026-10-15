import ExactCriticalCurve.Quantum.CSSQuotientGeometry
import ExactCriticalCurve.Quantum.PhaseStabilizerProjector
import ExactCriticalCurve.FiniteQuadratic.BinaryWittCharacter

/-! Actual fourth-root Gauss sums on the weight space and every defect quotient.
No signed-type or quotient Gauss value is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- The full mod-four weight sum, with the original ambient dimension. -/
theorem weightQuadratic_gauss_sum (k : ℕ) :
    (∑ x : BinaryVector k, pauliPhase (weightQuadratic x)) =
      (1 + Complex.I) ^ k := by
  simp_rw [weightQuadratic, pauliPhase_sum]
  rw [← Fintype.prod_sum (fun (_ : Fin k) (b : ZMod 2) => pauliPhase (bitLift b))]
  have h : (∑ b : ZMod 2, pauliPhase (bitLift b)) = 1 + Complex.I := by
    rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
    norm_num [bitLift, ZMod.val]
  simp_rw [h]
  simp

/-- Character orthogonality on the actual defect subspace. -/
theorem defect_character_sum (N : Submodule (ZMod 2) (BinaryVector k))
    (x : BinaryVector k) :
    (∑ n : N, pauliSign (binaryDot n.val x)) =
      if x ∈ orthogonal N then (Fintype.card N : ℂ) else 0 := by
  let l := ((binaryDotForm k).flip x).comp N.subtype
  have he : l = 0 ↔ x ∈ orthogonal N := by
    constructor
    · intro h n hn
      exact congrArg (fun f : N →ₗ[ZMod 2] ZMod 2 => f ⟨n, hn⟩) h
    · intro h
      ext n
      exact h n.val n.property
  simpa only [he] using FiniteQuadratic.binaryCharacter_linear_sum l

/-- Averaging over a genuine totally singular defect localizes the ambient sum. -/
theorem weightQuadratic_gauss_orthogonal
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (∑ x : BinaryVector k, pauliPhase (weightQuadratic x)) =
      ∑ x : orthogonal N, pauliPhase (weightQuadratic x.val) := by
  have ht (n : N) :
      (∑ x : BinaryVector k, pauliPhase (weightQuadratic x)) =
        ∑ x : BinaryVector k,
          pauliPhase (weightQuadratic x) * pauliSign (binaryDot n.val x) := by
    have h := Equiv.sum_comp (Equiv.addLeft n.val)
      (fun x => pauliPhase (weightQuadratic x))
    change (∑ x, pauliPhase (weightQuadratic (n.val + x))) = _ at h
    simpa only [weightQuadratic_add, hN n.val n.property, zero_add,
      pauliPhase_add, pauliPhase_two_bitLift] using h.symm
  have hs := congrArg (fun f : N → ℂ => ∑ n, f n) (funext ht)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  rw [Finset.sum_comm] at hs
  simp_rw [← Finset.mul_sum, defect_character_sum] at hs
  have hr :
      (∑ x : BinaryVector k, pauliPhase (weightQuadratic x) *
        if x ∈ orthogonal N then (Fintype.card N : ℂ) else 0) =
      (Fintype.card N : ℂ) *
        ∑ x : orthogonal N, pauliPhase (weightQuadratic x.val) := by
    simp_rw [mul_ite, mul_zero, mul_comm _ (Fintype.card N : ℂ)]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_subtype _ (by simp) _
  rw [hr] at hs
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hs

/-- The true quotient fibers each have cardinality |N|. -/
theorem cssQuotient_gauss_fiber_sum
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (∑ x : orthogonal N, pauliPhase (weightQuadratic x.val)) =
      (Nat.card N : ℂ) *
        ∑ z : CSSQuotient N, pauliPhase (cssQuotientQuadratic N hN z) := by
  let π : orthogonal N → CSSQuotient N := Submodule.Quotient.mk
  have hc (z : CSSQuotient N) : Nat.card {x : orthogonal N // π x = z} = Nat.card N := by
    let e : {x : orthogonal N // π x = z} ≃
        {x : BinaryVector k // cosetMember (orthogonal N) N x z} := {
      toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.choose⟩, x.property.choose_spec⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans (cosetFiber_card _ _ hN.le_orthogonal z)
  rw [← Fintype.sum_fiberwise π (fun x => pauliPhase (weightQuadratic x.val))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  have he (x : {x : orthogonal N // π x = z}) :
      pauliPhase (weightQuadratic x.val.val) = pauliPhase (cssQuotientQuadratic N hN z) := by
    exact congrArg (fun z => pauliPhase (cssQuotientQuadratic N hN z)) x.property
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, hc]

/-- Exact fourth-root Gauss scaling for every actual CSS quotient. -/
theorem cssQuotient_gauss_sum_scaled
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (2 : ℂ) ^ Module.finrank (ZMod 2) N *
      (∑ z : CSSQuotient N, pauliPhase (cssQuotientQuadratic N hN z)) =
        (1 + Complex.I) ^ k := by
  have h := (weightQuadratic_gauss_orthogonal N hN).trans
    (cssQuotient_gauss_fiber_sum N hN)
  rw [weightQuadratic_gauss_sum, cssSubspace_card, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.symm

/-- The descended sum never vanishes, including zero-dimensional quotients. -/
theorem cssQuotient_gauss_sum_ne_zero
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (∑ z : CSSQuotient N, pauliPhase (cssQuotientQuadratic N hN z)) ≠ 0 := by
  intro h
  have hs := cssQuotient_gauss_sum_scaled N hN
  rw [h, mul_zero] at hs
  have hi : (1 + Complex.I : ℂ) ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    norm_num at this
  exact pow_ne_zero k hi hs.symm

end ExactCriticalCurve.Quantum
