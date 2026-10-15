import ExactCriticalCurve.Quantum.WuProjectorSum
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Actual CSS code spaces and their defect filtrations

The spaces here are ranges of the physical CSS projection matrices. Increasing
the defect reverses code inclusion. Ordinary layers exclude the all-ones vector;
exceptional layers contain it, so their decreasing filtration starts at rank one.
The Wu projection image is identified using the actual extension fibers.
-/

noncomputable section
open scoped BigOperators
open Classical Matrix

namespace ExactCriticalCurve.Binary

/-- Every lower rank occurs inside an actual ordinary defect. -/
theorem ordinaryDefect_exists_le {k s r : ℕ} (M : OrdinaryDefect k s) (hrs : r ≤ s) :
    ∃ N : OrdinaryDefect k r, N.val ≤ M.val := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
    (R := ZMod 2) (M := M.val) (n := r) (by simpa [M.property.2.1] using hrs)
  let N := Submodule.span (ZMod 2) (Set.range (M.val.subtype ∘ v))
  have hNM : N ≤ M.val := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (v i).property
  have hdim : Module.finrank (ZMod 2) N = r := by
    simpa [N] using finrank_span_eq_card (hv.map' M.val.subtype (Submodule.ker_subtype _))
  exact ⟨⟨N, (fun x hx => M.property.1 x (hNM hx)), hdim,
    (fun hx => M.property.2.2 (hNM hx))⟩, hNM⟩

/-- The full Wu extension map is surjective, by its positive actual fiber size. -/
theorem extendWuDefect_surjective {k r : ℕ} (hk : 0 < k) (h4 : 4 ∣ k) :
    Function.Surjective (extendWuDefect (r := r) hk h4) := by
  intro M
  have hcard : 0 < Fintype.card
      {N : OrdinaryDefect k r // extendWuDefect hk h4 N = M} := by
    rw [← Nat.card_eq_fintype_card, wuExtensionFiber_card hk h4]
    exact pow_pos (by omega) _
  obtain ⟨N, hN⟩ := Fintype.card_pos_iff.mp hcard
  exact ⟨N, hN⟩

/-- Positive-dimensional exceptional defects have no rank-zero member. -/
theorem exceptionalDefect_zero_isEmpty {k : ℕ} (hk : 0 < k) :
    IsEmpty (ExceptionalDefect k 0) := by
  refine ⟨fun M => ?_⟩
  have hbot : M.val = ⊥ := Submodule.finrank_eq_zero.mp M.property.2.1
  exact allOnes_ne_zero hk (by simpa [hbot] using M.property.2.2)

/-- Each exceptional defect contains an exceptional defect of the previous
positive rank. Rank zero is deliberately excluded. -/
theorem exceptionalDefect_exists_le {k r : ℕ} (hk : 0 < k) (h4 : 4 ∣ k)
    (M : ExceptionalDefect k (r + 2)) :
    ∃ N : ExceptionalDefect k (r + 1), N.val ≤ M.val := by
  obtain ⟨A, hA⟩ := extendWuDefect_surjective (r := r + 1) hk h4 M
  obtain ⟨B, hBA⟩ := ordinaryDefect_exists_le A (Nat.le_succ r)
  refine ⟨extendWuDefect hk h4 B, ?_⟩
  have heq := congrArg Subtype.val hA
  change B.val ⊔ wuLine k ≤ M.val
  rw [← heq]
  exact sup_le_sup_right hBA _

end ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum
open Binary

/-- The physical CSS code on all `n` qubit columns. -/
def cssCode (n : ℕ) {k : ℕ} (N : Submodule (ZMod 2) (BinaryVector k)) :
    Submodule ℂ (ColumnConfig n k → ℂ) :=
  LinearMap.range (cssColumnProjection n N).mulVecLin

/-- The range consists exactly of the span of the actual normalized coset columns. -/
theorem cssCode_eq_span (n : ℕ) {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssCode n N = Submodule.span ℂ (Set.range (cssColumnSynthesis n N).col) :=
  cssColumnProjection_range n N hN

/-- The smaller defect projection absorbs the larger defect projection. -/
theorem cssColumnProjection_mul_of_le (n : ℕ) {k : ℕ}
    (N M : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hM : IsDefect M) (hNM : N ≤ M) :
    cssColumnProjection n N * cssColumnProjection n M = cssColumnProjection n M := by
  obtain ⟨V, hV⟩ := N.exists_isCompl
  let U := V ⊓ M
  have hNU : N ⊔ U = M := by
    rw [← sup_inf_assoc_of_le V hNM, hV.sup_eq_top, top_inf_eq]
  have hU : IsDefect U := fun x hx => hM x hx.2
  have horth : N ≤ orthogonal U := by
    intro x hx z hz
    exact hM.binaryDot_eq_zero hz.2 (hNM hx)
  have hdis : Disjoint N U := hV.disjoint.mono_right inf_le_left
  have hprod := cssColumnProjection_mul n N U hN hU horth hdis
  rw [hNU] at hprod
  rw [← hprod, ← Matrix.mul_assoc, cssColumnProjection_idempotent n N hN]

/-- Absorption also holds in the reverse matrix order. -/
theorem cssColumnProjection_mul_of_ge (n : ℕ) {k : ℕ}
    (N M : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hM : IsDefect M) (hNM : N ≤ M) :
    cssColumnProjection n M * cssColumnProjection n N = cssColumnProjection n M := by
  have h := congrArg Matrix.conjTranspose (cssColumnProjection_mul_of_le n N M hN hM hNM)
  simpa only [Matrix.conjTranspose_mul,
    (cssColumnProjection_isHermitian n N).eq,
    (cssColumnProjection_isHermitian n M).eq] using h

/-- Code inclusion reverses inclusion of actual defects. -/
theorem cssCode_antitone (n : ℕ) {k : ℕ}
    (N M : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hM : IsDefect M) (hNM : N ≤ M) :
    cssCode n M ≤ cssCode n N := by
  rintro x ⟨v, rfl⟩
  refine ⟨(cssColumnProjection n M).mulVecLin v, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    cssColumnProjection_mul_of_le n N M hN hM hNM]

/-- A fixed ordinary code maps onto the code extended by the Wu line. -/
theorem cssCode_map_wu (n : ℕ) {k : ℕ} (h4 : 4 ∣ k)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hmissing : allOnes k ∉ N) :
    (cssCode n N).map (cssColumnProjection n (wuLine k)).mulVecLin =
      cssCode n (N ⊔ wuLine k) := by
  ext x
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    refine ⟨v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      cssWuLineProjection_mul h4 n N hN hmissing]
  · rintro ⟨v, rfl⟩
    refine ⟨(cssColumnProjection n N).mulVecLin v, ⟨v, rfl⟩, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      cssWuLineProjection_mul h4 n N hN hmissing]

/-- Span of all rank-`r` codes whose defect excludes the Wu vector. -/
def rawCSSFiltration (n k r : ℕ) : Submodule ℂ (ColumnConfig n k → ℂ) :=
  ⨆ N : OrdinaryDefect k r, cssCode n N.val

/-- Span of all rank-`r` codes whose defect contains the Wu vector. -/
def exceptionalCSSFiltration (n k r : ℕ) : Submodule ℂ (ColumnConfig n k → ℂ) :=
  ⨆ N : ExceptionalDefect k r, cssCode n N.val

/-- The ordinary filtration, with the Wu component removed when it is a defect. -/
def ordinaryCSSFiltration (n k r : ℕ) : Submodule ℂ (ColumnConfig n k → ℂ) :=
  if 4 ∣ k then
    (rawCSSFiltration n k r).map
      (1 - cssColumnProjection n (wuLine k)).mulVecLin
  else rawCSSFiltration n k r

theorem rawCSSFiltration_antitone (n k : ℕ) : Antitone (rawCSSFiltration n k) := by
  intro r s hrs
  apply iSup_le
  intro M
  obtain ⟨N, hNM⟩ := ordinaryDefect_exists_le M hrs
  exact (cssCode_antitone n N.val M.val N.property.1 M.property.1 hNM).trans
    (le_iSup (fun N : OrdinaryDefect k r => cssCode n N.val) N)

/-- Fixed-rank codes span precisely the codes of every higher ordinary rank. -/
theorem rawCSSFiltration_eq_iSup_ge (n k r : ℕ) :
    rawCSSFiltration n k r =
      ⨆ N : {N : Submodule (ZMod 2) (BinaryVector k) //
        IsDefect N ∧ r ≤ Module.finrank (ZMod 2) N ∧ allOnes k ∉ N},
        cssCode n N.val := by
  apply le_antisymm
  · apply iSup_le
    intro N
    exact le_iSup (fun N : {N : Submodule (ZMod 2) (BinaryVector k) //
      IsDefect N ∧ r ≤ Module.finrank (ZMod 2) N ∧ allOnes k ∉ N} =>
      cssCode n N.val)
      ⟨N.val, N.property.1, by rw [N.property.2.1], N.property.2.2⟩
  · apply iSup_le
    intro M
    let M' : OrdinaryDefect k (Module.finrank (ZMod 2) M.val) :=
      ⟨M.val, M.property.1, rfl, M.property.2.2⟩
    obtain ⟨N, hNM⟩ := ordinaryDefect_exists_le M' M.property.2.1
    exact (cssCode_antitone n N.val M.val N.property.1 M.property.1 hNM).trans
      (le_iSup (fun N : OrdinaryDefect k r => cssCode n N.val) N)

theorem ordinaryCSSFiltration_antitone (n k : ℕ) :
    Antitone (ordinaryCSSFiltration n k) := by
  intro r s hrs
  unfold ordinaryCSSFiltration
  split_ifs
  · exact Submodule.map_mono (rawCSSFiltration_antitone n k hrs)
  · exact rawCSSFiltration_antitone n k hrs

/-- The Wu projection has exactly the next exceptional layer as its image. -/
theorem rawCSSFiltration_map_wu {k : ℕ} (hk : 0 < k) (h4 : 4 ∣ k) (n r : ℕ) :
    (rawCSSFiltration n k r).map (cssColumnProjection n (wuLine k)).mulVecLin =
      exceptionalCSSFiltration n k (r + 1) := by
  rw [rawCSSFiltration, Submodule.map_iSup]
  have hmap (N : OrdinaryDefect k r) :
      (cssCode n N.val).map (cssColumnProjection n (wuLine k)).mulVecLin =
        cssCode n (N.val ⊔ wuLine k) :=
    cssCode_map_wu n h4 N.val N.property.1 N.property.2.2
  simp_rw [hmap]
  apply le_antisymm
  · apply iSup_le
    intro N
    exact le_iSup (fun M : ExceptionalDefect k (r + 1) => cssCode n M.val)
      (extendWuDefect hk h4 N)
  · apply iSup_le
    intro M
    obtain ⟨N, rfl⟩ := extendWuDefect_surjective hk h4 M
    exact le_iSup (fun N : OrdinaryDefect k r => cssCode n (N.val ⊔ wuLine k)) N

/-- Exceptional layers descend from positive rank one onwards. -/
theorem exceptionalCSSFiltration_succ_le {k : ℕ} (hk : 0 < k) (h4 : 4 ∣ k)
    (n r : ℕ) :
    exceptionalCSSFiltration n k (r + 2) ≤ exceptionalCSSFiltration n k (r + 1) := by
  apply iSup_le
  intro M
  obtain ⟨N, hNM⟩ := exceptionalDefect_exists_le hk h4 M
  exact (cssCode_antitone n N.val M.val N.property.1 M.property.1 hNM).trans
    (le_iSup (fun N : ExceptionalDefect k (r + 1) => cssCode n N.val) N)

/-- The entire positive-rank exceptional sequence is antitone. -/
theorem exceptionalCSSFiltration_antitone {k : ℕ} (hk : 0 < k) (h4 : 4 ∣ k)
    (n : ℕ) : Antitone (fun r => exceptionalCSSFiltration n k (r + 1)) := by
  intro r s hrs
  change exceptionalCSSFiltration n k (s + 1) ≤ exceptionalCSSFiltration n k (r + 1)
  rw [← rawCSSFiltration_map_wu hk h4 n s, ← rawCSSFiltration_map_wu hk h4 n r]
  exact Submodule.map_mono (rawCSSFiltration_antitone n k hrs)

/-- For positive copy number the exceptional rank-zero layer is empty. -/
theorem exceptionalCSSFiltration_zero {k : ℕ} (hk : 0 < k) (n : ℕ) :
    exceptionalCSSFiltration n k 0 = ⊥ := by
  letI := exceptionalDefect_zero_isEmpty hk
  exact iSup_of_empty _

end ExactCriticalCurve.Quantum
