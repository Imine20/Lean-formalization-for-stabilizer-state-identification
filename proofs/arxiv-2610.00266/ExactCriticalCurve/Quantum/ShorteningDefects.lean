import ExactCriticalCurve.Quantum.ShorteningCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Actual shortening and extension of mod-four defects
The zero-last-coordinate inverse is proved on actual submodules. The rank
shift is additive before any natural-number subtraction is introduced.
-/
noncomputable section
open Classical
namespace ExactCriticalCurve.Binary
variable {m : ℕ}

def shorteningZeroAppend (m : ℕ) : BinaryVector m →ₗ[ZMod 2] BinaryVector (m+1) where
  toFun x := shorteningAppend x 0
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem shorteningZeroAppend_castSucc (x : BinaryVector m) (i : Fin m) :
    shorteningZeroAppend m x i.castSucc = x i := shorteningAppend_castSucc _ _ _

@[simp] theorem shorteningZeroAppend_last (x : BinaryVector m) :
    shorteningZeroAppend m x (Fin.last m) = 0 := shorteningAppend_last _ _

theorem shorteningZeroAppend_injective (m : ℕ) : Function.Injective (shorteningZeroAppend m) := by
  intro x y h
  funext i
  simpa only [shorteningZeroAppend_castSucc] using congrFun h i.castSucc

@[simp] theorem shorteningZeroAppend_quadratic (x : BinaryVector m) :
    weightQuadratic (shorteningZeroAppend m x) = weightQuadratic x := by
  change weightQuadratic (shorteningAppend x 0) = _
  rw [weightQuadratic_shorteningAppend, bitLift_zero, add_zero]

def shorteningHead (m : ℕ) : BinaryVector (m+1) →ₗ[ZMod 2] BinaryVector m where
  toFun x := fun i => x i.castSucc + x (Fin.last m)
  map_add' x y := by ext i; simp; ring
  map_smul' a x := by ext i; simp; ring

@[simp] theorem shorteningHead_zeroAppend (x : BinaryVector m) :
    shorteningHead m (shorteningZeroAppend m x) = x := by
  ext i
  simp [shorteningHead]

@[simp] theorem shorteningHead_allOnes (m : ℕ) :
    shorteningHead m (allOnes (m+1)) = 0 := by
  ext i
  change (1+1 : ZMod 2) = 0
  decide

theorem shortening_decomposition (z : BinaryVector (m+1)) :
    shorteningZeroAppend m (shorteningHead m z) +
      z (Fin.last m) • allOnes (m+1) = z := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [allOnes]
  · simp only [Pi.add_apply, shorteningZeroAppend_castSucc, shorteningHead,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, allOnes, smul_eq_mul, mul_one]
    generalize z j.castSucc = a
    generalize z (Fin.last m) = b
    fin_cases a <;> fin_cases b <;> decide

def shorteningExtend (M : Submodule (ZMod 2) (BinaryVector m)) :
    Submodule (ZMod 2) (BinaryVector (m+1)) :=
  M.map (shorteningZeroAppend m) ⊔ wuLine (m+1)

def shorteningRestrict (N : Submodule (ZMod 2) (BinaryVector (m+1))) :
    Submodule (ZMod 2) (BinaryVector m) :=
  N.comap (shorteningZeroAppend m)

theorem shorteningExtend_wu_mem (M : Submodule (ZMod 2) (BinaryVector m)) :
    allOnes (m+1) ∈ shorteningExtend M :=
  (show wuLine (m+1) ≤ shorteningExtend M from le_sup_right) (allOnes_mem_wuLine _)

theorem shorteningRestrict_extend (M : Submodule (ZMod 2) (BinaryVector m)) :
    shorteningRestrict (shorteningExtend M) = M := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, z, hz, he⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have h := congrArg (shorteningHead m) he
    rw [map_add, map_smul, shorteningHead_zeroAppend, shorteningHead_allOnes,
      smul_zero, add_zero, shorteningHead_zeroAppend] at h
    exact h ▸ hy
  · intro hx
    exact (show M.map (shorteningZeroAppend m) ≤ shorteningExtend M from le_sup_left)
      ⟨x, hx, rfl⟩

theorem shorteningExtend_restrict
    (N : Submodule (ZMod 2) (BinaryVector (m+1))) (hwu : allOnes (m+1) ∈ N) :
    shorteningExtend (shorteningRestrict N) = N := by
  apply le_antisymm
  · apply sup_le
    · rintro z ⟨x, hx, rfl⟩
      exact hx
    · apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact hwu
  · intro z hz
    have hh : shorteningZeroAppend m (shorteningHead m z) ∈ N := by
      have hd := N.sub_mem hz (N.smul_mem (z (Fin.last m)) hwu)
      have he := shortening_decomposition z
      have he' : z - z (Fin.last m) • allOnes (m+1) =
          shorteningZeroAppend m (shorteningHead m z) := by
        exact (eq_sub_iff_add_eq.mpr he).symm
      rwa [he'] at hd
    rw [← shortening_decomposition z]
    exact (shorteningExtend (shorteningRestrict N)).add_mem
      ((show (shorteningRestrict N).map (shorteningZeroAppend m) ≤
        shorteningExtend (shorteningRestrict N) from le_sup_left) ⟨shorteningHead m z, hh, rfl⟩)
      ((shorteningExtend (shorteningRestrict N)).smul_mem _
        (shorteningExtend_wu_mem _))

theorem shorteningExtend_mono {M L : Submodule (ZMod 2) (BinaryVector m)} (h : M ≤ L) :
    shorteningExtend M ≤ shorteningExtend L := sup_le_sup (Submodule.map_mono h) le_rfl

theorem shorteningExtend_disjoint (M : Submodule (ZMod 2) (BinaryVector m)) :
    Disjoint (M.map (shorteningZeroAppend m)) (wuLine (m+1)) := by
  rw [Submodule.disjoint_def]
  intro z hz hu
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu
  have hh := congrArg (shorteningHead m) hc
  rw [map_smul, shorteningHead_allOnes, smul_zero, shorteningHead_zeroAppend] at hh
  rw [← hh, map_zero]

theorem shorteningExtend_finrank (M : Submodule (ZMod 2) (BinaryVector m)) :
    Module.finrank (ZMod 2) (shorteningExtend M) = Module.finrank (ZMod 2) M + 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (M.map (shorteningZeroAppend m)) (wuLine (m+1))
  rw [(shorteningExtend_disjoint M).eq_bot, finrank_bot, add_zero,
    wuLine_finrank (by omega)] at h
  have he := (M.equivMapOfInjective (shorteningZeroAppend m) (shorteningZeroAppend_injective m)).finrank_eq
  change Module.finrank (ZMod 2) (shorteningExtend M) = _ at h
  rw [← he] at h
  exact h

theorem shorteningRestrict_isDefect
    (N : Submodule (ZMod 2) (BinaryVector (m+1))) (hN : IsDefect N) :
    IsDefect (shorteningRestrict N) := by
  intro x hx
  rw [← shorteningZeroAppend_quadratic x]
  exact hN _ hx

theorem shorteningExtend_isDefect (h4 : 4 ∣ m+1)
    (M : Submodule (ZMod 2) (BinaryVector m)) (hM : IsDefect M) :
    IsDefect (shorteningExtend M) := by
  have hJ : IsDefect (M.map (shorteningZeroAppend m)) := by
    rintro x ⟨y, hy, rfl⟩
    rw [shorteningZeroAppend_quadratic]
    exact hM y hy
  apply hJ.sup_of_orthogonal (wuLine_isDefect h4)
  rintro x ⟨y, hy, rfl⟩
  rw [mem_orthogonal_wuLine_iff, ← shorteningAppend_allOnes]
  change binaryDot (shorteningAppend (allOnes m) 1) (shorteningAppend y 0) = 0
  rw [binaryDot_shorteningAppend, mul_zero, add_zero, binaryDot_comm]
  exact hM.allOnes_mem_orthogonal y hy

theorem shortening_ordinary_of_defect (h4 : 4 ∣ m+1)
    (M : Submodule (ZMod 2) (BinaryVector m)) (hM : IsDefect M) :
    allOnes m ∉ M := by
  intro hw
  have hz := (weightQuadratic_allOnes_eq_zero_iff m).mp (hM _ hw)
  obtain ⟨a, ha⟩ := h4
  obtain ⟨b, hb⟩ := hz
  omega

def shorteningDefectEquiv (h4 : 4 ∣ m+1) (r : ℕ) :
    OrdinaryDefect m r ≃ ExceptionalDefect (m+1) (r+1) where
  toFun M := ⟨shorteningExtend M.val,
    shorteningExtend_isDefect h4 M.val M.property.1,
    by rw [shorteningExtend_finrank, M.property.2.1],
    shorteningExtend_wu_mem M.val⟩
  invFun N := ⟨shorteningRestrict N.val,
    shorteningRestrict_isDefect N.val N.property.1,
    by
      have h := shorteningExtend_finrank (shorteningRestrict N.val)
      rw [shorteningExtend_restrict N.val N.property.2.2, N.property.2.1] at h
      omega,
    shortening_ordinary_of_defect h4 _ (shorteningRestrict_isDefect N.val N.property.1)⟩
  left_inv M := Subtype.ext (shorteningRestrict_extend M.val)
  right_inv N := Subtype.ext (shorteningExtend_restrict N.val N.property.2.2)

end ExactCriticalCurve.Binary
