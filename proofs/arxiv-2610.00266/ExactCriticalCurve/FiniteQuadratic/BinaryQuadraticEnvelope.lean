import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRadical
import ExactCriticalCurve.FiniteQuadratic.AlternatingRealizability
import Mathlib.LinearAlgebra.QuadraticForm.Dual

/-! Genuine quadratic refinements of the minimal alternating envelope.
The parameter in the actual radical controls the signed Gauss sum. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {A R : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup R] [Module (ZMod 2) R]

theorem binaryQuadratic_polar_isAlt (q : QuadraticForm (ZMod 2) A) :
    q.polarBilin.IsAlt := by
  intro x
  change QuadraticMap.polar q x x = 0
  rw [q.polar_self]
  simp [two_smul,CharTwo.add_self_eq_zero]

/-- A full quadratic refinement on the actual source times its radical dual. -/
def binaryQuadraticEnvelope (q : QuadraticForm (ZMod 2) A)
    (p : A →ₗ[ZMod 2] binaryPolarRadical q) (u : binaryPolarRadical q) :
    QuadraticForm (ZMod 2) (A × Module.Dual (ZMod 2) (binaryPolarRadical q)) :=
  let π := LinearMap.fst (ZMod 2) A (Module.Dual (ZMod 2) (binaryPolarRadical q))
  let σ := LinearMap.snd (ZMod 2) A (Module.Dual (ZMod 2) (binaryPolarRadical q))
  q.comp π + (QuadraticForm.dualProd (ZMod 2) (binaryPolarRadical q)).comp
    (σ.prod (p.comp π)) +
    binaryLinearQuadratic ((Module.Dual.eval (ZMod 2) (binaryPolarRadical q) u).comp σ)

@[simp] theorem binaryQuadraticEnvelope_apply (q : QuadraticForm (ZMod 2) A)
    (p : A →ₗ[ZMod 2] binaryPolarRadical q) (u : binaryPolarRadical q)
    (x : A × Module.Dual (ZMod 2) (binaryPolarRadical q)) :
    binaryQuadraticEnvelope q p u x = q x.1 + x.2 (p x.1) + x.2 u := by
  simp [binaryQuadraticEnvelope]

/-- Its polar is exactly the already-proved minimal alternating envelope. -/
theorem binaryQuadraticEnvelope_polar (q : QuadraticForm (ZMod 2) A)
    (p : A →ₗ[ZMod 2] binaryPolarRadical q) (u : binaryPolarRadical q) :
    (binaryQuadraticEnvelope q p u).polarBilin = alternatingEnvelopeForm q.polarBilin p := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    binaryQuadraticEnvelope_apply,alternatingEnvelopeForm_apply,
    Prod.fst_add,Prod.snd_add,map_add,LinearMap.add_apply]
  ring

theorem binaryQuadraticEnvelope_nondegenerate (q : QuadraticForm (ZMod 2) A)
    (p : A →ₗ[ZMod 2] binaryPolarRadical q) (hp : ∀ r : binaryPolarRadical q, p r.val = r)
    (u : binaryPolarRadical q) :
    LinearMap.BilinForm.Nondegenerate (binaryQuadraticEnvelope q p u).polarBilin := by
  rw [binaryQuadraticEnvelope_polar]
  exact alternatingEnvelopeForm_nondegenerate q.polarBilin (binaryQuadratic_polar_isAlt q) p hp

@[simp] theorem binaryQuadraticEnvelope_inl (q : QuadraticForm (ZMod 2) A)
    (p : A →ₗ[ZMod 2] binaryPolarRadical q) (u : binaryPolarRadical q) (x : A) :
    binaryQuadraticEnvelope q p u (x,0) = q x := by simp

/-- Every binary quadratic space has an actual nondegenerate envelope on its source
times the dual of its actual polar radical. -/
theorem exists_binaryQuadratic_nondegenerate_envelope (q : QuadraticForm (ZMod 2) A) :
    ∃ P : QuadraticForm (ZMod 2) (A × Module.Dual (ZMod 2) (binaryPolarRadical q)),
      LinearMap.BilinForm.Nondegenerate P.polarBilin ∧ ∀ x : A, P (x,0) = q x := by
  obtain ⟨C,hC⟩ := (binaryPolarRadical q).exists_isCompl
  let p := (binaryPolarRadical q).linearProjOfIsCompl C hC
  exact ⟨binaryQuadraticEnvelope q p 0,
    binaryQuadraticEnvelope_nondegenerate q p
      (fun r => Submodule.linearProjOfIsCompl_apply_left hC r) 0,
    binaryQuadraticEnvelope_inl q p 0⟩

theorem binaryQuadraticEnvelope_finrank [FiniteDimensional (ZMod 2) A]
    (q : QuadraticForm (ZMod 2) A) :
    finrank (ZMod 2) (A × Module.Dual (ZMod 2) (binaryPolarRadical q)) =
      finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical q) := by
  rw [Module.finrank_prod,Subspace.dual_finrank_eq]

/-- Actual dual character orthogonality. -/
theorem binaryDual_character_sum [Fintype (Module.Dual (ZMod 2) R)] (r : R) :
    (∑ φ : Module.Dual (ZMod 2) R, pauliSign (φ r)) =
      if r = 0 then (Fintype.card (Module.Dual (ZMod 2) R) : ℂ) else 0 := by
  have he : Module.Dual.eval (ZMod 2) R r = 0 ↔ r = 0 := by
    constructor
    · intro h
      apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) r).mp
      intro φ
      exact congrArg (fun l : Module.Dual (ZMod 2) R →ₗ[ZMod 2] ZMod 2 => l φ) h
    · rintro rfl
      simp
  simpa only [he] using binaryCharacter_linear_sum (Module.Dual.eval (ZMod 2) R r)

theorem binaryLinearPair_gauss [Fintype R] [Fintype (Module.Dual (ZMod 2) R)]
    (l : R →ₗ[ZMod 2] ZMod 2) (u : R) :
    (∑ r : R, ∑ φ : Module.Dual (ZMod 2) R,
      pauliSign (l r + φ r + φ u)) =
      (Fintype.card (Module.Dual (ZMod 2) R) : ℂ) * pauliSign (l u) := by
  have he (r : R) :
      (∑ φ : Module.Dual (ZMod 2) R, pauliSign (l r + φ r + φ u)) =
        pauliSign (l r) *
          (if r = u then (Fintype.card (Module.Dual (ZMod 2) R) : ℂ) else 0) := by
    calc
      _ = ∑ φ : Module.Dual (ZMod 2) R, pauliSign (l r + φ (r+u)) := by
        simp only [map_add,add_assoc]
      _ = pauliSign (l r) * ∑ φ : Module.Dual (ZMod 2) R, pauliSign (φ (r+u)) := by
        simp only [pauliSign_add,Finset.mul_sum]
      _ = _ := by
        rw [binaryDual_character_sum]
        have hu : -u = u := by
          apply neg_eq_of_add_eq_zero_right
          calc
            u + u = (1 + 1 : ZMod 2) • u := by rw [add_smul,one_smul]
            _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 by decide,zero_smul]
        simp only [add_eq_zero_iff_eq_neg,hu]
  simp_rw [he,mul_ite,mul_zero]
  simp [mul_comm]

/-- A concrete finite enumeration of the dual of a finite-dimensional binary space. -/
noncomputable instance binaryDualFintype [FiniteDimensional (ZMod 2) R] :
    Fintype (Module.Dual (ZMod 2) R) :=
  Fintype.ofEquiv (Fin (finrank (ZMod 2) (Module.Dual (ZMod 2) R)) → ZMod 2)
    (Module.finBasis (ZMod 2) (Module.Dual (ZMod 2) R)).equivFun.toEquiv.symm

/-- The exact signed Gauss sum is computed using the actual complementary coordinates. -/
theorem binaryQuadraticEnvelope_gauss [FiniteDimensional (ZMod 2) A] [Fintype A]
    (q : QuadraticForm (ZMod 2) A) (C : Submodule (ZMod 2) A)
    (hC : IsCompl (binaryPolarRadical q) C) (u : binaryPolarRadical q) :
    binaryQuadraticGaussSum
      (binaryQuadraticEnvelope q ((binaryPolarRadical q).linearProjOfIsCompl C hC) u) =
      binaryQuadraticGaussSum (q.comp C.subtype) *
        (Fintype.card (binaryPolarRadical q) : ℂ) * pauliSign (binaryRadicalLinear q u) := by
  let R := binaryPolarRadical q
  let D := Module.Dual (ZMod 2) R
  let p := R.linearProjOfIsCompl C hC
  let e := (Submodule.prodEquivOfIsCompl C R hC.symm).toEquiv.prodCongr (Equiv.refl D)
  have he (c : C) (r : R) (φ : D) :
      pauliSign (binaryQuadraticEnvelope q p u (c.val+r.val,φ)) =
        pauliSign (q c.val) * pauliSign (binaryRadicalLinear q r + φ r + φ u) := by
    have hp : p (c.val+r.val) = r := by
      dsimp only [p]
      rw [map_add,Submodule.linearProjOfIsCompl_apply_right,
        Submodule.linearProjOfIsCompl_apply_left,zero_add]
    rw [binaryQuadraticEnvelope_apply,hp,quadratic_add]
    have hb : q.polarBilin c.val r.val = 0 :=
      ((polar_isSymm q).eq _ _).trans ((mem_binaryPolarRadical q r.val).mp r.property c.val)
    rw [hb,add_zero]
    change pauliSign (q c.val + q r.val + φ r + φ u) = _
    rw [show q c.val + q r.val + φ r + φ u =
      q c.val + (q r.val + φ r + φ u) by ring,pauliSign_add]
    rfl
  have hcD : Fintype.card D = Fintype.card R := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := D),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := R),Subspace.dual_finrank_eq]
  calc
    _ = ∑ z : (C × R) × D,
        pauliSign (binaryQuadraticEnvelope q p u (z.1.1.val+z.1.2.val,z.2)) := by
      exact (Equiv.sum_comp e (fun z => pauliSign (binaryQuadraticEnvelope q p u z))).symm
    _ = ∑ c : C, ∑ r : R, ∑ φ : D,
        pauliSign (q c.val) * pauliSign (binaryRadicalLinear q r + φ r + φ u) := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type,he]
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      have hpair := binaryLinearPair_gauss (binaryRadicalLinear q) u
      change (∑ r : R, ∑ φ : D, pauliSign (binaryRadicalLinear q r + φ r + φ u)) =
        (Fintype.card D : ℂ) * pauliSign (binaryRadicalLinear q u) at hpair
      rw [hpair]
      rw [← Finset.sum_mul,hcD]
      change binaryQuadraticGaussSum (q.comp C.subtype) *
        ((Fintype.card R : ℂ) * pauliSign (binaryRadicalLinear q u)) = _
      ring

/-- The exact dimension obstruction is inherited from the actual alternating embedding. -/
theorem binaryQuadratic_embedding_dimension_bound
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) A) (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (f : A →ₗ[ZMod 2] V) (hf : Function.Injective f) (hfq : ∀ x, Q (f x) = q x) :
    finrank (ZMod 2) A + finrank (ZMod 2) (binaryPolarRadical q) ≤ finrank (ZMod 2) V := by
  apply alternating_embedding_dimension_bound q.polarBilin Q.polarBilin
    (binaryQuadratic_polar_isAlt Q) hQ f hf
  intro x y
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  rw [← map_add,hfq,hfq,hfq]

end ExactCriticalCurve.FiniteQuadratic
