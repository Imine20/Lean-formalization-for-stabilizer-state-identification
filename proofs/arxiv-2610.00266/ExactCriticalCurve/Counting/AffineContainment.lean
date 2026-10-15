import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

/-!
# Actual affine supports containing a fixed support

The correspondence uses the direction of a nonempty affine subspace and the
quotient by that direction. The dimension equation is additive, so that the
family is correctly empty below the dimension of the prescribed support.
-/

noncomputable section

namespace ExactCriticalCurve.Counting

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Every actual affine subspace containing A₀, with prescribed direction dimension. -/
def AffineSupportsContaining (A₀ : AffineSubspace K V) (m : ℕ) :=
  {A : AffineSubspace K V // A₀ ≤ A ∧ Module.finrank K A.direction = m}

/-- The dimension-graded actual subspaces of the quotient, with no truncated subtraction. -/
def QuotientSupports (A₀ : AffineSubspace K V) (m : ℕ) :=
  {U : Submodule K (V ⧸ A₀.direction) //
    Module.finrank K U + Module.finrank K A₀.direction = m}

/-- Choosing a point of A₀ identifies all affine superspaces with all
linear superspaces of its direction. -/
def affineSuperspacesEquivDirections (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) :
    Set.Ici A₀ ≃ Set.Ici A₀.direction where
  toFun A := ⟨A.val.direction, AffineSubspace.direction_le A.property⟩
  invFun M := ⟨AffineSubspace.mk' (Classical.choice hA₀).val M.val, by
    intro x hx
    exact M.property (A₀.vsub_mem_direction hx (Classical.choice hA₀).property)⟩
  left_inv A := by
    apply Subtype.ext
    exact AffineSubspace.mk'_eq (A.property (Classical.choice hA₀).property)
  right_inv M := by
    apply Subtype.ext
    exact AffineSubspace.direction_mk' _ _

/-- The complete correspondence with quotient subspaces, without a dimension condition. -/
def affineSuperspacesEquivQuotientSubmodules
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) :
    Set.Ici A₀ ≃ Submodule K (V ⧸ A₀.direction) :=
  (affineSuperspacesEquivDirections A₀ hA₀).trans
    A₀.direction.comapMkQRelIso.toEquiv.symm

@[simp] theorem affineSuperspacesEquivQuotientSubmodules_apply
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) (A : Set.Ici A₀) :
    affineSuperspacesEquivQuotientSubmodules A₀ hA₀ A =
      A.val.direction.map A₀.direction.mkQ := rfl

/-- Rank-nullity for the actual image in the quotient. -/
theorem finrank_map_mkQ_add_of_le [FiniteDimensional K V]
    (p N : Submodule K V) (h : p ≤ N) :
    Module.finrank K (N.map p.mkQ) + Module.finrank K p = Module.finrank K N := by
  have hker : LinearMap.ker (p.mkQ.domRestrict N) = p.comap N.subtype := by
    ext x
    simp
  have hr := (p.mkQ.domRestrict N).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, hker] at hr
  rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq] at hr
  exact hr

/-- The dimension loss in the quotient is proved from rank-nullity. -/
theorem affineSuperspacesEquivQuotientSubmodules_finrank [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) (A : Set.Ici A₀) :
    Module.finrank K (affineSuperspacesEquivQuotientSubmodules A₀ hA₀ A) +
      Module.finrank K A₀.direction = Module.finrank K A.val.direction :=
  finrank_map_mkQ_add_of_le _ _ (AffineSubspace.direction_le A.property)

/-- Dimension-graded complete affine/quotient correspondence. -/
def affineSupportsContainingEquivQuotientSupports [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) (m : ℕ) :
    AffineSupportsContaining A₀ m ≃ QuotientSupports A₀ m where
  toFun A := ⟨affineSuperspacesEquivQuotientSubmodules A₀ hA₀ ⟨A.val, A.property.1⟩,
    (affineSuperspacesEquivQuotientSubmodules_finrank A₀ hA₀
      ⟨A.val, A.property.1⟩).trans A.property.2⟩
  invFun U := by
    let A := (affineSuperspacesEquivQuotientSubmodules A₀ hA₀).symm U.val
    refine ⟨A.val, A.property, ?_⟩
    have hd := affineSuperspacesEquivQuotientSubmodules_finrank A₀ hA₀ A
    rw [Equiv.apply_symm_apply] at hd
    exact hd.symm.trans U.property
  left_inv A := by
    apply Subtype.ext
    exact congrArg (fun B : Set.Ici A₀ => B.val)
      ((affineSuperspacesEquivQuotientSubmodules A₀ hA₀).symm_apply_apply
        ⟨A.val, A.property.1⟩)
  right_inv U := by
    apply Subtype.ext
    exact (affineSuperspacesEquivQuotientSubmodules A₀ hA₀).apply_symm_apply U.val

/-- Counting the actual affine family is exactly counting actual quotient subspaces. -/
theorem card_affineSupportsContaining [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) (m : ℕ) :
    Nat.card (AffineSupportsContaining A₀ m) = Nat.card (QuotientSupports A₀ m) :=
  Nat.card_congr (affineSupportsContainingEquivQuotientSupports A₀ hA₀ m)

/-- Subtraction is used only after its required lower bound has been supplied. -/
def affineSupportsContainingEquivQuotientSubspaces [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) (m : ℕ)
    (hm : Module.finrank K A₀.direction ≤ m) :
    AffineSupportsContaining A₀ m ≃
      {U : Submodule K (V ⧸ A₀.direction) //
        Module.finrank K U = m - Module.finrank K A₀.direction} :=
  (affineSupportsContainingEquivQuotientSupports A₀ hA₀ m).trans
    (Equiv.subtypeEquivRight (fun U => by
      omega))

/-- Below the prescribed support dimension there are no containing supports. -/
theorem isEmpty_affineSupportsContaining_of_lt [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (m : ℕ) (hm : m < Module.finrank K A₀.direction) :
    IsEmpty (AffineSupportsContaining A₀ m) := by
  refine ⟨fun A => ?_⟩
  have h := Submodule.finrank_mono (AffineSubspace.direction_le A.property.1)
  rw [A.property.2] at h
  omega

theorem card_affineSupportsContaining_of_lt [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (m : ℕ) (hm : m < Module.finrank K A₀.direction) :
    Nat.card (AffineSupportsContaining A₀ m) = 0 := by
  letI := isEmpty_affineSupportsContaining_of_lt A₀ m hm
  exact Nat.card_of_isEmpty


/-- Over a finite field this is a genuinely finite family. -/
theorem finite_affineSupportsContaining [Finite K] [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (m : ℕ) :
    Finite (AffineSupportsContaining A₀ m) := by
  letI : Finite V := Finite.of_equiv (Fin (Module.finrank K V) → K)
    (Module.finBasis K V).equivFun.toEquiv.symm
  exact Finite.of_injective
    (fun A : AffineSupportsContaining A₀ m => (A.val : Set V))
    (fun A B h => Subtype.ext (SetLike.coe_injective h))

/-- At its own dimension, the only containing support is A₀ itself. -/
theorem card_affineSupportsContaining_self [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) :
    Nat.card (AffineSupportsContaining A₀ (Module.finrank K A₀.direction)) = 1 := by
  let a : A₀ := Classical.choice hA₀
  letI : Unique (AffineSupportsContaining A₀ (Module.finrank K A₀.direction)) := {
    default := ⟨A₀, le_rfl, rfl⟩
    uniq A := by
      apply Subtype.ext
      have hd := Submodule.eq_of_le_of_finrank_eq
        (AffineSubspace.direction_le A.property.1) A.property.2.symm
      exact AffineSubspace.ext_of_direction_eq hd.symm
        ⟨a.val, A.property.1 a.property, a.property⟩ }
  exact Nat.card_unique

/-- In particular, a nonempty zero-dimensional prescribed support has one
zero-dimensional extension, including in zero-dimensional ambient space. -/
theorem card_affineSupportsContaining_zero [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀)
    (hd : Module.finrank K A₀.direction = 0) :
    Nat.card (AffineSupportsContaining A₀ 0) = 1 := by
  simpa only [hd] using card_affineSupportsContaining_self A₀ hA₀

/-- A containing support cannot have dimension above the ambient space. -/
theorem card_affineSupportsContaining_of_finrank_lt [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (m : ℕ) (hm : Module.finrank K V < m) :
    Nat.card (AffineSupportsContaining A₀ m) = 0 := by
  letI : IsEmpty (AffineSupportsContaining A₀ m) := ⟨fun A => by
    have h := A.val.direction.finrank_le
    rw [A.property.2] at h
    omega⟩
  exact Nat.card_of_isEmpty


/-- Linear coordinates preserve the full family of fixed-dimensional subspaces. -/
def subspacesOfFinrankEquiv {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    (e : V ≃ₗ[K] V₂) (r : ℕ) :
    {U : Submodule K V // Module.finrank K U = r} ≃
      {U : Submodule K V₂ // Module.finrank K U = r} :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (fun U => by
    change Module.finrank K U = r ↔ Module.finrank K (U.map e.toLinearMap) = r
    rw [e.finrank_map_eq])

/-- The quotient can be replaced by a coordinate space of the proved dimension.
The right-hand side still counts actual subspaces; no Gaussian formula is assumed. -/
theorem card_affineSupportsContaining_eq_coordinateSubspaces [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀) (m : ℕ)
    (hm : Module.finrank K A₀.direction ≤ m) :
    Nat.card (AffineSupportsContaining A₀ m) =
      Nat.card {U : Submodule K (Fin
        (Module.finrank K V - Module.finrank K A₀.direction) → K) //
        Module.finrank K U = m - Module.finrank K A₀.direction} := by
  have h := Nat.card_congr
    ((affineSupportsContainingEquivQuotientSubspaces A₀ hA₀ m hm).trans
      (subspacesOfFinrankEquiv
        (Module.finBasis K (V ⧸ A₀.direction)).equivFun
        (m - Module.finrank K A₀.direction)))
  have hd : Module.finrank K (V ⧸ A₀.direction) =
      Module.finrank K V - Module.finrank K A₀.direction :=
    Submodule.finrank_quotient A₀.direction
  rw [hd] at h
  exact h

/-- The complete zero-dimensional ambient-space endpoint. -/
theorem card_affineSupportsContaining_of_finrank_eq_zero [FiniteDimensional K V]
    (A₀ : AffineSubspace K V) (hA₀ : Nonempty A₀)
    (hV : Module.finrank K V = 0) (m : ℕ) :
    Nat.card (AffineSupportsContaining A₀ m) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    have hd : Module.finrank K A₀.direction = 0 := by
      have h := A₀.direction.finrank_le
      omega
    simpa using card_affineSupportsContaining_zero A₀ hA₀ hd
  · have hlt : Module.finrank K V < m := by omega
    simpa [hm] using card_affineSupportsContaining_of_finrank_lt A₀ m hlt

end ExactCriticalCurve.Counting
