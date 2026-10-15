import ExactCriticalCurve.Quantum.DefectProjectionProduct

/-! # The actual Wu line and its CSS projector
The nonzero condition and dimension shift use k > 0. Mod-four isotropy
uses 4 ∣ k. Tensor degree n may be zero; no stable range is imposed.
-/
noncomputable section
namespace ExactCriticalCurve.Binary

def wuLine (k : ℕ) : Submodule (ZMod 2) (BinaryVector k) :=
  Submodule.span (ZMod 2) {allOnes k}

theorem allOnes_ne_zero {k : ℕ} (hk : 0 < k) : allOnes k ≠ 0 := by
  intro h
  have hh : (1 : ZMod 2) = 0 := congrFun h ⟨0, hk⟩
  exact one_ne_zero hh

theorem allOnes_mem_wuLine (k : ℕ) : allOnes k ∈ wuLine k :=
  Submodule.subset_span (Set.mem_singleton _)

theorem isDefect_span_singleton {k : ℕ} (w : BinaryVector k)
    (hw : weightQuadratic w = 0) :
    IsDefect (Submodule.span (ZMod 2) {w}) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  fin_cases c <;> simp_all

theorem wuLine_isDefect {k : ℕ} (hk : 4 ∣ k) : IsDefect (wuLine k) :=
  isDefect_span_singleton (allOnes k) ((weightQuadratic_allOnes_eq_zero_iff k).mpr hk)

theorem wuLine_finrank {k : ℕ} (hk : 0 < k) :
    Module.finrank (ZMod 2) (wuLine k) = 1 :=
  finrank_span_singleton (allOnes_ne_zero hk)

theorem wuLine_le_orthogonal {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    wuLine k ≤ orthogonal N := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact hN.allOnes_mem_orthogonal

theorem wuLine_disjoint {k : ℕ}
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : allOnes k ∉ N) :
    Disjoint (wuLine k) N :=
  (Submodule.disjoint_span_singleton_of_notMem hN).symm

theorem defect_sup_wuLine {k : ℕ} (hk : 4 ∣ k)
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    IsDefect (N ⊔ wuLine k) :=
  hN.sup_of_orthogonal (wuLine_isDefect hk) (orthogonal_le_comm (wuLine_le_orthogonal hN))

theorem finrank_sup_wuLine {k : ℕ} (hk : 0 < k)
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : allOnes k ∉ N) :
    Module.finrank (ZMod 2) (N ⊔ wuLine k : Submodule (ZMod 2) (BinaryVector k)) =
      Module.finrank (ZMod 2) N + 1 := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq N (wuLine k)
  rw [(wuLine_disjoint hN).symm.eq_bot, finrank_bot, add_zero, wuLine_finrank hk] at hd
  exact hd

theorem allOnes_mem_sup_wuLine {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    allOnes k ∈ N ⊔ wuLine k :=
  (show wuLine k ≤ N ⊔ wuLine k from le_sup_right) (allOnes_mem_wuLine k)

end ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum
open Binary

theorem cssWuLineProjection_mul {k : ℕ} (hk : 4 ∣ k) (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (hmissing : allOnes k ∉ N) :
    cssColumnProjection n (wuLine k) * cssColumnProjection n N =
      cssColumnProjection n (N ⊔ wuLine k) := by
  rw [cssColumnProjection_mul n (wuLine k) N (wuLine_isDefect hk) hN
    (wuLine_le_orthogonal hN) (wuLine_disjoint hmissing), sup_comm]

end ExactCriticalCurve.Quantum

