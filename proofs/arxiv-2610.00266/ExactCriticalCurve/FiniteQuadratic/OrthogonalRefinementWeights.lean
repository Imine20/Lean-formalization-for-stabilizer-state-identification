import ExactCriticalCurve.FiniteQuadratic.OrthogonalPolarStrata

/-! Exact rational counts of genuine embeddable refinement fibers and their two-layer differences. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic

/-- The rational expression for the independently counted strict, signed boundary and forbidden fibers. -/
def orthogonalRefinementWeight (sigma : ℚ) (m b t : ℕ) : ℚ :=
  if b+t<m then (2 : ℚ)^(b+2*t) else
    if b+t=m then ((2 : ℚ)^b-1)*(2 : ℚ)^(2*t)+((2 : ℚ)^(2*t)+sigma*(2 : ℚ)^t)/2 else 0

variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) V]
  [Fintype A] [Fintype V]

/-- The rational formula is proved from the actual refinement fibers for both genuine target signs. -/
theorem binaryQuadraticEmbeddable_card_signed
    (B : LinearMap.BilinForm (ZMod 2) A) (hB : B.IsAlt)
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B)=b)
    (hd : finrank (ZMod 2) A=b+2*t) (hm : finrank (ZMod 2) V=2*m)
    (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hg : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m) :
    (Nat.card (BinaryQuadraticEmbeddableRefinements B Q) : ℚ)=orthogonalRefinementWeight sigma m b t := by
  unfold orthogonalRefinementWeight
  by_cases hlt : b+t<m
  · rw [if_pos hlt,binaryQuadraticEmbeddable_strict_card B hB Q hQ b t m hb hd hm hlt]
    norm_cast
  rw [if_neg hlt]
  by_cases he : b+t=m
  · rw [if_pos he]
    have hpow : 1≤(2 : ℕ)^b := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    rcases hsigma with rfl | rfl
    · have hp := binaryQuadraticEmbeddable_positive_boundary_card B hB Q hQ b t m hb hd hm he
        (by simpa using hg)
      have hp' := congrArg (fun n : ℕ => (n : ℚ)) hp
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sub hpow,Nat.cast_one] at hp'
      linarith
    · have hn := binaryQuadraticEmbeddable_negative_boundary_card B hB Q hQ b t m hb hd hm he
        (by simpa using hg)
      have hn' := congrArg (fun n : ℕ => (n : ℚ)) hn
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sub hpow,Nat.cast_one] at hn'
      linarith
  · rw [if_neg he,binaryQuadraticEmbeddable_forbidden_card B Q hQ b t m hb hd hm (by omega)]
    norm_num

/-- Exactly two adjacent height layers change; the old boundary contributes its missing sign. -/
theorem orthogonalRefinementWeight_sub (sigma : ℚ) (m b t : ℕ) (hm : 0<m) :
    orthogonalRefinementWeight sigma m b t-orthogonalRefinementWeight sigma (m-1) b t =
      (if b+t=m then ((2 : ℚ)^b-1)*(2 : ℚ)^(2*t)+
        ((2 : ℚ)^(2*t)+sigma*(2 : ℚ)^t)/2 else 0) +
      (if b+t=m-1 then ((2 : ℚ)^(2*t)-sigma*(2 : ℚ)^t)/2 else 0) := by
  unfold orthogonalRefinementWeight
  by_cases he : b+t=m
  · have hne : b+t≠m-1 := by omega
    simp [he,hne,show ¬m<m-1 by omega,show m≠m-1 by omega]
  by_cases hp : b+t=m-1
  · have hlt : b+t<m := by omega
    simp only [if_neg he,if_pos hp,if_pos hlt,show ¬b+t<m-1 by omega,ite_false,zero_add]
    rw [pow_add]
    ring
  by_cases hl : b+t<m-1
  · have hlt : b+t<m := by omega
    simp [he,hp,hl,hlt]
  · have hlt : ¬b+t<m := by omega
    simp [he,hp,hl,hlt]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Fintype W]

/-- Comparing two actual same-sign targets gives the exact new and missing-old boundary fibers. -/
theorem binaryQuadraticEmbeddable_card_increment
    (B : LinearMap.BilinForm (ZMod 2) A) (hB : B.IsAlt)
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (P : QuadraticForm (ZMod 2) W) (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (b t m : ℕ) (hb : finrank (ZMod 2) (LinearMap.ker B)=b)
    (hd : finrank (ZMod 2) A=b+2*t) (hmQ : finrank (ZMod 2) V=2*m)
    (hmP : finrank (ZMod 2) W=2*(m-1)) (hm : 0<m)
    (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hgQ : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m)
    (hgP : binaryQuadraticGaussSum P=(sigma : ℂ)*(2 : ℂ)^(m-1)) :
    (Nat.card (BinaryQuadraticEmbeddableRefinements B Q) : ℚ)-
      (Nat.card (BinaryQuadraticEmbeddableRefinements B P) : ℚ) =
      (if b+t=m then ((2 : ℚ)^b-1)*(2 : ℚ)^(2*t)+
        ((2 : ℚ)^(2*t)+sigma*(2 : ℚ)^t)/2 else 0) +
      (if b+t=m-1 then ((2 : ℚ)^(2*t)-sigma*(2 : ℚ)^t)/2 else 0) := by
  rw [binaryQuadraticEmbeddable_card_signed B hB Q hQ b t m hb hd hmQ sigma hsigma hgQ,
    binaryQuadraticEmbeddable_card_signed B hB P hP b t (m-1) hb hd hmP sigma hsigma hgP]
  exact orthogonalRefinementWeight_sub sigma m b t hm

end ExactCriticalCurve.FiniteQuadratic
