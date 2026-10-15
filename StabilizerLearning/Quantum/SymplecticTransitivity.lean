import StabilizerLearning.Quantum.ReferenceFrame

/-! Explicit symplectic transvections and transitivity on nonzero directions.
No odd-characteristic division by two and no transitivity premise is used. -/
noncomputable section
namespace StabilizerLearning
variable {p n : ℕ} [Fact p.Prime]

/-- An elementary symplectic transvection, including in characteristic two. -/
def symplecticTransvectionLinear (a : PhaseSpace p n) (c : ZMod p) :
    PhaseSpace p n →ₗ[ZMod p] PhaseSpace p n where
  toFun x := x + (c * symplecticBilinForm x a) • a
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, mul_add, add_smul]
    abel
  map_smul' r x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      smul_add, smul_smul, RingHom.id_apply]
    congr 1
    ring

@[simp] theorem symplecticTransvectionLinear_apply (a : PhaseSpace p n)
    (c : ZMod p) (x : PhaseSpace p n) :
    symplecticTransvectionLinear a c x = x + (c * symplecticBilinForm x a) • a := rfl

theorem symplecticTransvectionLinear_neg (a : PhaseSpace p n) (c : ZMod p)
    (x : PhaseSpace p n) :
    symplecticTransvectionLinear a (-c) (symplecticTransvectionLinear a c x) = x := by
  simp only [symplecticTransvectionLinear_apply, map_add, LinearMap.add_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, symplecticBilinForm_apply,
    symplecticPairing_self, mul_zero, add_zero, neg_mul, neg_smul, zero_smul]
  abel

/-- The inverse transvection uses the negative coefficient. -/
def symplecticTransvection (a : PhaseSpace p n) (c : ZMod p) :
    PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n :=
  { symplecticTransvectionLinear a c with
    invFun := symplecticTransvectionLinear a (-c)
    left_inv := symplecticTransvectionLinear_neg a c
    right_inv := by
      intro x
      simpa only [neg_neg] using symplecticTransvectionLinear_neg a (-c) x }

@[simp] theorem symplecticTransvection_apply (a : PhaseSpace p n)
    (c : ZMod p) (x : PhaseSpace p n) :
    symplecticTransvection a c x = x + (c * symplecticBilinForm x a) • a := rfl

theorem pairing_symplecticTransvection (a : PhaseSpace p n) (c : ZMod p)
    (x y : PhaseSpace p n) :
    symplecticPairing (symplecticTransvection a c x) (symplecticTransvection a c y) =
      symplecticPairing x y := by
  change symplecticBilinForm _ _ = symplecticBilinForm x y
  simp only [symplecticTransvection_apply, map_add, LinearMap.add_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, symplecticBilinForm_apply,
    symplecticPairing_self, mul_zero, add_zero]
  rw [symplecticPairing_swap a y]
  ring

/-- A nonorthogonal pair is joined by one explicit transvection. -/
theorem symplecticTransvection_maps (v w : PhaseSpace p n)
    (h : symplecticPairing v w ≠ 0) :
    symplecticTransvection (w - v) (symplecticPairing v w)⁻¹ v = w := by
  rw [symplecticTransvection_apply]
  have hv : symplecticBilinForm v (w - v) = symplecticPairing v w := by
    rw [map_sub]
    simp only [symplecticBilinForm_apply, symplecticPairing_self, sub_zero]
  rw [hv, inv_mul_cancel₀ h, one_smul]
  abel

/-- Two nonzero vectors have a common vector nonorthogonal to both, over every field. -/
theorem exists_common_nonorthogonal (v w : PhaseSpace p n) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ u, symplecticPairing v u ≠ 0 ∧ symplecticPairing w u ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, symplecticPairing v a ≠ 0 := by
    by_contra h
    exact hv (symplecticPairing_nondegenerate v (by simpa using h))
  by_cases hwa : symplecticPairing w a ≠ 0
  · exact ⟨a, ha, hwa⟩
  obtain ⟨b, hb⟩ : ∃ b, symplecticPairing w b ≠ 0 := by
    by_contra h
    exact hw (symplecticPairing_nondegenerate w (by simpa using h))
  by_cases hvb : symplecticPairing v b ≠ 0
  · exact ⟨b, hvb, hb⟩
  have hwa0 : symplecticPairing w a = 0 := not_not.mp hwa
  have hvb0 : symplecticPairing v b = 0 := not_not.mp hvb
  refine ⟨a + b, ?_, ?_⟩
  · change symplecticBilinForm v (a + b) ≠ 0
    rw [map_add]
    simpa only [symplecticBilinForm_apply, hvb0, add_zero] using ha
  · change symplecticBilinForm w (a + b) ≠ 0
    rw [map_add]
    simpa only [symplecticBilinForm_apply, hwa0, zero_add] using hb

/-- Actual linear symplectic maps act transitively on all nonzero phase-space vectors. -/
theorem exists_symplectic_map_nonzero (v w : PhaseSpace p n) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n,
      (∀ z t, symplecticPairing (g z) (g t) = symplecticPairing z t) ∧ g v = w := by
  obtain ⟨u, hvu, hwu⟩ := exists_common_nonorthogonal v w hv hw
  have huw : symplecticPairing u w ≠ 0 := by
    rw [symplecticPairing_swap u w]
    exact neg_ne_zero.mpr hwu
  let a := symplecticTransvection (u - v) (symplecticPairing v u)⁻¹
  let b := symplecticTransvection (w - u) (symplecticPairing u w)⁻¹
  refine ⟨a.trans b, ?_, ?_⟩
  · intro z t
    exact (pairing_symplecticTransvection _ _ (a z) (a t)).trans
      (pairing_symplecticTransvection _ _ z t)
  · change b (a v) = w
    rw [show a v = u from symplecticTransvection_maps v u hvu]
    exact symplecticTransvection_maps u w huw

end StabilizerLearning
