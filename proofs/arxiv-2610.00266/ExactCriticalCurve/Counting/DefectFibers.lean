import ExactCriticalCurve.Counting.Complements
import ExactCriticalCurve.Binary.Geometry

/-!
# Actual ambient subspaces and defect-extension fibers

Internal missing-vector hyperplanes are transported to all ambient subspaces
of the prescribed dimension contained in M. When M is a mod-four defect,
these are exactly the actual defects N with N ⊔ span{w} = M.
The extension equality follows from dimensions and is not assumed in the
ambient family. No ordinary/exceptional global interface is introduced.
-/

noncomputable section

namespace ExactCriticalCurve.Counting

section Ambient

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- All ambient r-dimensional subspaces of M missing the specified vector. -/
abbrev AmbientMissingHyperplanes (M : Submodule K V) (w : V) (r : ℕ) :=
  {N : Submodule K V // N ≤ M ∧ Module.finrank K N = r ∧ w ∉ N}

/-- Restriction and inclusion identify all ambient subspaces in the index
with all missing-vector hyperplanes internal to M. -/
def ambientMissingHyperplanesEquivInternal
    (M : Submodule K V) (w : V) (hwM : w ∈ M) (r : ℕ)
    (hM : Module.finrank K M = r + 1) :
    AmbientMissingHyperplanes M w r ≃
      {q : Submodule K M //
        Module.finrank K q + 1 = Module.finrank K M ∧ (⟨w, hwM⟩ : M) ∉ q} where
  toFun N := ⟨N.val.comap M.subtype, by
    constructor
    · rw [(Submodule.comapSubtypeEquivOfLe N.property.1).finrank_eq,
        N.property.2.1, hM]
    · exact N.property.2.2⟩
  invFun q := ⟨q.val.map M.subtype, M.map_subtype_le q.val, by
    rw [Submodule.finrank_map_subtype_eq]
    exact Nat.add_right_cancel (q.property.1.trans hM), by
    intro hw
    obtain ⟨x, hx, hxw⟩ := hw
    have heq : x = (⟨w, hwM⟩ : M) := Subtype.ext hxw
    exact q.property.2 (heq ▸ hx)⟩
  left_inv N := by
    apply Subtype.ext
    exact (Submodule.map_comap_subtype M N.val).trans (inf_eq_right.mpr N.property.1)
  right_inv q := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective M.subtype_injective q.val

/-- Every indexed ambient subspace extends to M by adjoining the missing
nonzero vector. This is proved by disjointness, dimension, and containment. -/
theorem ambientMissingHyperplanes_sup_span_eq
    (M : Submodule K V) (w : V) (hwM : w ∈ M) (hw : w ≠ 0) (r : ℕ)
    (hM : Module.finrank K M = r + 1) (N : AmbientMissingHyperplanes M w r) :
    N.val ⊔ Submodule.span K {w} = M := by
  have hline : Submodule.span K {w} ≤ M :=
    (Submodule.span_singleton_le_iff_mem w M).mpr hwM
  have hd : Disjoint N.val (Submodule.span K {w}) :=
    Submodule.disjoint_span_singleton_of_notMem N.property.2.2
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq N.val (Submodule.span K {w})
  rw [hd.eq_bot, finrank_bot, add_zero, N.property.2.1,
    finrank_span_singleton hw] at hdim
  exact Submodule.eq_of_le_of_finrank_eq
    (sup_le N.property.1 hline) (hdim.trans hM.symm)

end Ambient

section BinaryAmbient

variable {k : ℕ}

/-- The ambient binary count refers to every actual subspace N ≤ M. -/
theorem card_ambientMissingHyperplanes
    (M : Submodule (ZMod 2) (Binary.BinaryVector k)) (w : Binary.BinaryVector k)
    (hwM : w ∈ M) (hw : w ≠ 0) (r : ℕ)
    (hM : Module.finrank (ZMod 2) M = r + 1) :
    Nat.card (AmbientMissingHyperplanes M w r) = 2 ^ r := by
  rw [Nat.card_congr (ambientMissingHyperplanesEquivInternal M w hwM r hM)]
  apply card_missingHyperplanes_binary (⟨w, hwM⟩ : M) _ r hM
  exact fun h => hw (congrArg Subtype.val h)

/-- The actual fiber of extension by span{w}, restricted to mod-four defects. -/
abbrev DefectExtensionFiber
    (M : Submodule (ZMod 2) (Binary.BinaryVector k)) (w : Binary.BinaryVector k)
    (r : ℕ) :=
  {N : Submodule (ZMod 2) (Binary.BinaryVector k) //
    Binary.IsDefect N ∧ Module.finrank (ZMod 2) N = r ∧ w ∉ N ∧
      N ⊔ Submodule.span (ZMod 2) {w} = M}

/-- For a defect M, its actual extension fiber is exactly the complete ambient
missing-vector hyperplane family. Isotropy is inherited from M. -/
def defectExtensionFiberEquivAmbient
    (M : Submodule (ZMod 2) (Binary.BinaryVector k)) (hdef : Binary.IsDefect M)
    (w : Binary.BinaryVector k) (hwM : w ∈ M) (hw : w ≠ 0) (r : ℕ)
    (hM : Module.finrank (ZMod 2) M = r + 1) :
    DefectExtensionFiber M w r ≃ AmbientMissingHyperplanes M w r where
  toFun N := ⟨N.val,
    le_sup_left.trans_eq N.property.2.2.2,
    N.property.2.1, N.property.2.2.1⟩
  invFun N := ⟨N.val,
    (fun x hx => hdef x (N.property.1 hx)),
    N.property.2.1, N.property.2.2,
    ambientMissingHyperplanes_sup_span_eq M w hwM hw r hM N⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete mod-four defect-extension fiber has exactly 2^r members. -/
theorem card_defectExtensionFiber
    (M : Submodule (ZMod 2) (Binary.BinaryVector k)) (hdef : Binary.IsDefect M)
    (w : Binary.BinaryVector k) (hwM : w ∈ M) (hw : w ≠ 0) (r : ℕ)
    (hM : Module.finrank (ZMod 2) M = r + 1) :
    Nat.card (DefectExtensionFiber M w r) = 2 ^ r := by
  rw [Nat.card_congr (defectExtensionFiberEquivAmbient M hdef w hwM hw r hM)]
  exact card_ambientMissingHyperplanes M w hwM hw r hM

end BinaryAmbient

end ExactCriticalCurve.Counting
