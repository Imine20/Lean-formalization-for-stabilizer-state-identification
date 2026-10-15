import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two

/-! # Actual quotient lifts fixing a distinguished vector over F2

An arbitrary splitting supplies the initial lift. A quotient-preserving
involutive shear corrects its distinguished vector, uniformly whether the
vector lies in the kernel or has nonzero quotient class.
-/

noncomputable section
open Classical
namespace ExactCriticalCurve

section Splitting
variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A linear splitting whose first coordinate is the actual quotient class. -/
theorem exists_quotientSplit (N : Submodule K V) :
    ∃ s : ((V ⧸ N) × N) ≃ₗ[K] V,
      ∀ (q : V ⧸ N) (n : N), (Submodule.Quotient.mk (s (q, n)) : V ⧸ N) = q := by
  obtain ⟨C, hC⟩ := N.exists_isCompl
  let s : ((V ⧸ N) × N) ≃ₗ[K] V :=
    ((N.quotientEquivOfIsCompl C hC).prodCongr (LinearEquiv.refl K N)).trans
      (C.prodEquivOfIsCompl N hC.symm)
  refine ⟨s, ?_⟩
  intro q n
  change N.mkQ ((N.quotientEquivOfIsCompl C hC q).val + n.val) = q
  rw [map_add]
  have hn : N.mkQ n.val = 0 := (Submodule.Quotient.mk_eq_zero N).mpr n.property
  rw [hn, add_zero]
  exact N.mk_quotientEquivOfIsCompl_apply C hC q

/-- Kernel and quotient equivalences lift to an equivalence of the actual spaces. -/
theorem exists_quotientLift (N : Submodule K V) (M : Submodule K W)
    (e : (V ⧸ N) ≃ₗ[K] (W ⧸ M)) (f : N ≃ₗ[K] M) :
    ∃ g : V ≃ₗ[K] W,
      ∀ x : V, (Submodule.Quotient.mk (g x) : W ⧸ M) = e (Submodule.Quotient.mk x) := by
  obtain ⟨s, hs⟩ := exists_quotientSplit N
  obtain ⟨t, ht⟩ := exists_quotientSplit M
  let g := s.symm.trans ((e.prodCongr f).trans t)
  refine ⟨g, ?_⟩
  intro x
  obtain ⟨⟨q, n⟩, rfl⟩ := s.surjective x
  simpa only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply, hs] using ht (e q) (f n)

end Splitting

section Binary
variable {V W : Type*}
variable [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup W] [Module (ZMod 2) W]

/-- A shear with direction annihilated by its functional is an involution over F2. -/
def binaryShear (l : V →ₗ[ZMod 2] ZMod 2) (d : V) (hd : l d = 0) : V ≃ₗ[ZMod 2] V where
  toFun x := x + l x • d
  invFun x := x + l x • d
  left_inv x := by
    simp only [map_add, map_smul, hd, smul_zero, add_zero]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  right_inv x := by
    simp only [map_add, map_smul, hd, smul_zero, add_zero]
    rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
  map_add' x y := by
    simp only [map_add, add_smul]
    abel
  map_smul' a x := by
    simp only [map_smul, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul]

@[simp] theorem binaryShear_apply (l : V →ₗ[ZMod 2] ZMod 2) (d : V) (hd : l d = 0)
    (x : V) : binaryShear l d hd x = x + l x • d := rfl

/-- A shear along the actual subspace fixes every quotient class. -/
theorem binaryShear_quotient (N : Submodule (ZMod 2) V)
    (l : V →ₗ[ZMod 2] ZMod 2) (d : V) (hd : l d = 0) (hN : d ∈ N) (x : V) :
    (Submodule.Quotient.mk (binaryShear l d hd x) : V ⧸ N) = Submodule.Quotient.mk x := by
  change N.mkQ (x + l x • d) = N.mkQ x
  rw [map_add, map_smul, show N.mkQ d = 0 from (Submodule.Quotient.mk_eq_zero N).mpr hN]
  simp

/-- Nonzero representatives of the same quotient class are related by a quotient-fixing
linear automorphism. The proof uses the actual F2 coefficients, including kernel classes. -/
theorem exists_quotientFixingEquiv (N : Submodule (ZMod 2) V)
    (a b : V) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : (Submodule.Quotient.mk a : V ⧸ N) = Submodule.Quotient.mk b) :
    ∃ u : V ≃ₗ[ZMod 2] V, u a = b ∧
      ∀ x : V, (Submodule.Quotient.mk (u x) : V ⧸ N) = Submodule.Quotient.mk x := by
  by_cases he : a = b
  · exact ⟨LinearEquiv.refl _ _, he, fun _ => rfl⟩
  let d := b - a
  let D : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {d}
  have had : a ∉ D := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    fin_cases c
    · exact ha (by simpa using hc.symm)
    · have hd' : b - a = a := by simpa [d] using hc
      have haa : a + a = 0 := by
        rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
      apply hb
      calc
        b = (b - a) + a := (sub_add_cancel b a).symm
        _ = a + a := by rw [hd']
        _ = 0 := haa
  obtain ⟨l, hl, hla⟩ := LinearMap.exists_extend_of_notMem (K := ZMod 2)
    (0 : D →ₗ[ZMod 2] ZMod 2) had (1 : ZMod 2)
  have hld : l d = 0 := by
    have h := LinearMap.congr_fun hl (⟨d, Submodule.mem_span_singleton_self d⟩ : D)
    exact h
  have hdN : d ∈ N := (Submodule.Quotient.eq N).mp hab.symm
  refine ⟨binaryShear l d hld, ?_, binaryShear_quotient N l d hld hdN⟩
  simp only [binaryShear_apply, hla, one_smul, d]
  abel

/-- An actual quotient equivalence lifts while carrying a specified vector exactly.
No prescribed lift or section is a hypothesis. -/
theorem exists_quotientLift_pointed (N : Submodule (ZMod 2) V)
    (M : Submodule (ZMod 2) W) (e : (V ⧸ N) ≃ₗ[ZMod 2] (W ⧸ M))
    (f : N ≃ₗ[ZMod 2] M) (v : V) (w : W)
    (hzero : v = 0 ↔ w = 0)
    (hpoint : e (Submodule.Quotient.mk v) = Submodule.Quotient.mk w) :
    ∃ g : V ≃ₗ[ZMod 2] W, g v = w ∧
      ∀ x : V, (Submodule.Quotient.mk (g x) : W ⧸ M) = e (Submodule.Quotient.mk x) := by
  obtain ⟨g, hg⟩ := exists_quotientLift (K := ZMod 2) (V := V) (W := W) N M e f
  by_cases hv : v = 0
  · refine ⟨g, ?_, hg⟩
    simp only [hv, map_zero, hzero.mp hv]
  · have hw : w ≠ 0 := fun h => hv (hzero.mpr h)
    have hgv : g v ≠ 0 := g.map_ne_zero_iff.mpr hv
    obtain ⟨u, huv, hu⟩ := exists_quotientFixingEquiv M (g v) w hgv hw
      ((hg v).trans hpoint)
    refine ⟨g.trans u, huv, ?_⟩
    intro x
    exact (hu (g x)).trans (hg x)

end Binary
end ExactCriticalCurve
