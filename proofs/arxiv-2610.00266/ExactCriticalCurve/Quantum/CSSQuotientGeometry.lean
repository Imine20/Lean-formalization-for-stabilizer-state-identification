import ExactCriticalCurve.Quantum.CSSFiltration
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! # The genuine mod-four quadratic geometry of the CSS quotient

All forms are descended onto the existing CSSQuotient N = N-perp/(N restricted
to N-perp). The mod-four refinement is retained; it is not replaced by a
binary-valued quadratic form. No classification or Clifford intertwiner is
assumed or asserted.
-/

noncomputable section
open Classical
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- The mod-four weight of an actual CSS quotient class. -/
def cssQuotientQuadratic (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    CSSQuotient N → ZMod 4 :=
  Quotient.lift (fun x : orthogonal N => weightQuadratic x.val) (by
    intro x y hxy
    have hd : x.val - y.val ∈ N :=
      (N.comap (orthogonal N).subtype).quotientRel_def.mp hxy
    have he : x.val = (x.val - y.val) + y.val := by abel
    change weightQuadratic x.val = weightQuadratic y.val
    have hb : binaryDot (x.val - y.val) y.val = 0 := y.property _ hd
    rw [he, weightQuadratic_add, hN _ hd, hb]
    simp)

@[simp] theorem cssQuotientQuadratic_mk
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (x : orthogonal N) :
    cssQuotientQuadratic N hN (Submodule.Quotient.mk x) = weightQuadratic x.val := rfl

/-- The binary pairing descended in both actual quotient arguments. -/
def cssQuotientPairing (N : Submodule (ZMod 2) (BinaryVector k)) :
    CSSQuotient N → CSSQuotient N → ZMod 2 :=
  Quotient.lift (fun x : orthogonal N =>
    Quotient.lift (fun y : orthogonal N => binaryDot x.val y.val) (by
      intro y z hyz
      have hd : y.val - z.val ∈ N :=
        (N.comap (orthogonal N).subtype).quotientRel_def.mp hyz
      have hz : binaryDot (y.val - z.val) x.val = 0 := x.property _ hd
      rw [binaryDot_comm] at hz
      change (binaryDotForm k x.val) (y.val - z.val) = 0 at hz
      rw [map_sub, sub_eq_zero] at hz
      exact hz)) (by
        intro x y hxy
        funext z
        induction z using Submodule.Quotient.induction_on with
        | H z =>
          have hd : x.val - y.val ∈ N :=
            (N.comap (orthogonal N).subtype).quotientRel_def.mp hxy
          have hz := z.property _ hd
          change (binaryDotForm k) (x.val - y.val) z.val = 0 at hz
          rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at hz
          exact hz)

@[simp] theorem cssQuotientPairing_mk (N : Submodule (ZMod 2) (BinaryVector k))
    (x y : orthogonal N) :
    cssQuotientPairing N (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      binaryDot x.val y.val := rfl

/-- The descended pairing is genuinely bilinear over F2. -/
def cssQuotientBilinear (N : Submodule (ZMod 2) (BinaryVector k)) :
    LinearMap.BilinForm (ZMod 2) (CSSQuotient N) where
  toFun x := {
    toFun := cssQuotientPairing N x
    map_add' := by
      intro y z
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        induction y using Submodule.Quotient.induction_on with
        | H y =>
          induction z using Submodule.Quotient.induction_on with
          | H z => exact (binaryDotForm k x.val).map_add y.val z.val
    map_smul' := by
      intro a y
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        induction y using Submodule.Quotient.induction_on with
        | H y => exact (binaryDotForm k x.val).map_smul a y.val }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        induction z using Submodule.Quotient.induction_on with
        | H z =>
          exact congrArg (fun f => f z.val) ((binaryDotForm k).map_add x.val y.val)
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        exact congrArg (fun f => f y.val) ((binaryDotForm k).map_smul a x.val)

@[simp] theorem cssQuotientBilinear_mk (N : Submodule (ZMod 2) (BinaryVector k))
    (x y : orthogonal N) :
    cssQuotientBilinear N (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      binaryDot x.val y.val := rfl

theorem cssQuotientBilinear_symm (N : Submodule (ZMod 2) (BinaryVector k))
    (x y : CSSQuotient N) : cssQuotientBilinear N x y = cssQuotientBilinear N y x := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => exact binaryDot_comm x.val y.val

/-- The radical of the restricted dot product is precisely the quotient denominator. -/
theorem cssQuotientBilinear_nondegenerate
    (N : Submodule (ZMod 2) (BinaryVector k)) : (cssQuotientBilinear N).Nondegenerate := by
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have hxorth : x.val ∈ orthogonal (orthogonal N) := by
      intro y hy
      have h := hx (Submodule.Quotient.mk (⟨y, hy⟩ : orthogonal N))
      change binaryDot x.val y = 0 at h
      exact (binaryDot_comm y x.val).trans h
    change x.val ∈ (binaryDotForm k).orthogonal ((binaryDotForm k).orthogonal N) at hxorth
    rw [LinearMap.BilinForm.orthogonal_orthogonal (binaryDotForm_nondegenerate k)
      (binaryDotForm_isRefl k)] at hxorth
    apply (Submodule.Quotient.eq (N.comap (orthogonal N).subtype)).mpr
    simpa using hxorth

@[simp] theorem cssQuotientQuadratic_zero
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssQuotientQuadratic N hN 0 = 0 := weightQuadratic_zero k

/-- The original mod-four polarization law survives on the actual quotient. -/
theorem cssQuotientQuadratic_add
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (x y : CSSQuotient N) :
    cssQuotientQuadratic N hN (x + y) =
      cssQuotientQuadratic N hN x + cssQuotientQuadratic N hN y +
        2 * bitLift (cssQuotientBilinear N x y) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => exact weightQuadratic_add x.val y.val

/-- The dimension inequality is established before taking any natural subtraction. -/
theorem cssDefect_two_mul_finrank_le
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    2 * Module.finrank (ZMod 2) N ≤ k := by
  have hle := Submodule.finrank_mono hN.le_orthogonal
  have hsum := finrank_orthogonal_add N
  omega

/-- Additive dimension identity, including zero-dimensional quotients. -/
theorem cssQuotient_finrank_add
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Module.finrank (ZMod 2) (CSSQuotient N) + 2 * Module.finrank (ZMod 2) N = k := by
  have hd : Module.finrank (ZMod 2) (N.comap (orthogonal N).subtype) =
      Module.finrank (ZMod 2) N :=
    (Submodule.comapSubtypeEquivOfLe hN.le_orthogonal).finrank_eq
  have hq := (N.comap (orthogonal N).subtype).finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (CSSQuotient N) +
    Module.finrank (ZMod 2) (N.comap (orthogonal N).subtype) =
      Module.finrank (ZMod 2) (orthogonal N) at hq
  rw [hd] at hq
  have hsum := finrank_orthogonal_add N
  omega

theorem cssQuotient_finrank
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Module.finrank (ZMod 2) (CSSQuotient N) = k - 2 * Module.finrank (ZMod 2) N := by
  have hbound := cssDefect_two_mul_finrank_le N hN
  have hdim := cssQuotient_finrank_add N hN
  omega

/-- The actual class of the ambient Wu vector, not a separately selected vector. -/
def cssQuotientWu (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    CSSQuotient N :=
  Submodule.Quotient.mk (⟨allOnes k, hN.allOnes_mem_orthogonal⟩ : orthogonal N)

theorem cssQuotientWu_characteristic
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (x : CSSQuotient N) :
    cssQuotientBilinear N x x = cssQuotientBilinear N x (cssQuotientWu N hN) := by
  induction x using Submodule.Quotient.induction_on with
  | H x => exact binaryDot_self_eq_dot_allOnes x.val

theorem cssQuotientWu_eq_zero_iff
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssQuotientWu N hN = 0 ↔ allOnes k ∈ N := by
  change (Submodule.Quotient.mk
    (⟨allOnes k, hN.allOnes_mem_orthogonal⟩ : orthogonal N) :
      CSSQuotient N) = Submodule.Quotient.mk 0 ↔ _
  rw [Submodule.Quotient.eq]
  simp

theorem cssQuotientQuadratic_wu
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssQuotientQuadratic N hN (cssQuotientWu N hN) = (k : ZMod 4) :=
  weightQuadratic_allOnes k

theorem ordinaryCSSQuotient_wu_ne_zero {r : ℕ} (N : OrdinaryDefect k r) :
    cssQuotientWu N.val N.property.1 ≠ 0 := by
  intro h
  exact N.property.2.2 ((cssQuotientWu_eq_zero_iff N.val N.property.1).mp h)

theorem exceptionalCSSQuotient_wu_eq_zero {r : ℕ} (N : ExceptionalDefect k r) :
    cssQuotientWu N.val N.property.1 = 0 :=
  (cssQuotientWu_eq_zero_iff N.val N.property.1).mpr N.property.2.2

/-- The exceptional quotient has alternating bilinear form. -/
theorem exceptionalCSSQuotient_alternating {r : ℕ} (N : ExceptionalDefect k r)
    (x : CSSQuotient N.val) : cssQuotientBilinear N.val x x = 0 := by
  rw [cssQuotientWu_characteristic N.val N.property.1,
    exceptionalCSSQuotient_wu_eq_zero N, map_zero]

/-- The ordinary quotient is genuinely nonalternating. -/
theorem ordinaryCSSQuotient_not_alternating {r : ℕ} (N : OrdinaryDefect k r) :
    ¬ ∀ x : CSSQuotient N.val, cssQuotientBilinear N.val x x = 0 := by
  intro h
  apply ordinaryCSSQuotient_wu_ne_zero N
  apply cssQuotientBilinear_nondegenerate N.val
  intro x
  rw [cssQuotientBilinear_symm, ← cssQuotientWu_characteristic]
  exact h x

end ExactCriticalCurve.Quantum
