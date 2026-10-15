import StabilizerLearning.Quantum.PauliSupport
import StabilizerLearning.Quantum.AssignmentCharacters
import StabilizerLearning.Quantum.AssignmentTransport

/-! The exact overlap spectrum of an intrinsic projector with a pure stabilizer
state. The proof uses the actual XZ Pauli section in every prime characteristic. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- The Pauli expectation in a pure stabilizer state vanishes outside its
Lagrangian and is the prescribed eigenvalue inside it. -/
theorem trace_pauli_jointProjector_lagrangian
    (L : Lagrangian p n) (χ : Assignment p n L.val) (w : PhaseSpace p n) :
    Matrix.trace (pauli p n w * jointProjector p n L.val χ) =
      if h : w ∈ L.val then eigenPhase p (χ.val ⟨w, h⟩) else 0 := by
  by_cases hw : w ∈ L.val
  · rw [dif_pos hw]
    have he := pauli_mul_jointProjector p n L.val χ (⟨w, hw⟩ : L.val)
    rw [he, Matrix.trace_smul]
    have ht : Matrix.trace (jointProjector p n L.val χ) = 1 :=
      labelProjector_trace p n ⟨L, χ⟩
    simp [ht]
  · rw [dif_neg hw]
    have hn : -w ∉ L.val := by simpa using hw
    have he := trace_pauli_jointProjector p n L.val χ (-w)
    rw [dif_neg hn, pauli_conjTranspose, Matrix.smul_mul, Matrix.trace_smul] at he
    simp only [neg_neg, smul_eq_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (rootPhase_ne_zero p _)

/-- The phase ratio is an ordinary character, and its full sum exactly detects
equality of the assignments, without an assumed character-sum formula. -/
theorem sum_assignment_phase_ratio
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η χ : Assignment p n U) :
    (∑ z : U, eigenPhase p (χ.val z) / eigenPhase p (η.val z)) =
      if η = χ then (Nat.card U : ℂ) else 0 := by
  let ψ := assignmentCharacterEquiv p n U η χ
  have hz : ψ = 0 ↔ η = χ := by
    rw [AddChar.eq_zero_iff]
    constructor
    · intro h
      apply Subtype.ext
      funext z
      apply eigenPhase_injective p
      have he := h z
      change eigenPhase p (χ.val z) / eigenPhase p (η.val z) = 1 at he
      exact ((div_eq_one_iff_eq (eigenPhase_ne_zero p _)).mp he).symm
    · intro h
      subst χ
      intro z
      simp [ψ]
  change (∑ z : U, ψ z) = _
  rw [AddChar.sum_eq_ite]
  simp only [hz, Nat.card_eq_fintype_card]

/-- Expanding the actual projector leaves precisely the common stabilizer
coordinates, with their original section-compatible phase ratio. -/
theorem trace_jointProjector_overlap_sum
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val) :
    Matrix.trace (jointProjector p n U η * jointProjector p n L.val χ) =
      ((p : ℂ) ^ Module.finrank (ZMod p) U)⁻¹ *
        ∑ z : ↥(U ⊓ L.val),
          eigenPhase p ((restrictAssignment p inf_le_right χ).val z) /
            eigenPhase p ((restrictAssignment p inf_le_left η).val z) := by
  have hsmall :
      (∑ z : ↥(U ⊓ L.val),
        eigenPhase p ((restrictAssignment p inf_le_right χ).val z) /
          eigenPhase p ((restrictAssignment p inf_le_left η).val z)) =
      ∑ z : U, (eigenPhase p (η.val z))⁻¹ *
        (if h : z.val ∈ L.val then eigenPhase p (χ.val ⟨z.val, h⟩) else 0) := by
    apply Fintype.sum_of_injective (Submodule.inclusion (inf_le_left : U ⊓ L.val ≤ U))
      (Submodule.inclusion_injective _) 
    · intro z hz
      by_cases hL : z.val ∈ L.val
      · exact (hz ⟨⟨z.val, z.property, hL⟩, rfl⟩).elim
      · simp [hL]
    · intro z
      change eigenPhase p (χ.val ⟨z.val, z.property.2⟩) /
          eigenPhase p (η.val ⟨z.val, z.property.1⟩) =
        (eigenPhase p (η.val ⟨z.val, z.property.1⟩))⁻¹ *
          (if h : z.val ∈ L.val then eigenPhase p (χ.val ⟨z.val, h⟩) else 0)
      have hL : z.val ∈ L.val := z.property.2
      rw [dif_pos hL, div_eq_mul_inv, mul_comm]
  rw [hsmall]
  conv_lhs => arg 1; lhs; unfold jointProjector
  rw [show Fintype.ofFinite U = (inferInstance : Fintype U) from Subsingleton.elim _ _]
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [Matrix.smul_mul, Matrix.trace_smul, trace_pauli_jointProjector_lagrangian]
  rfl

/-- Exact complex overlap spectrum, with compatibility tested on the actual
intersection and with no chosen basis or odd-characteristic convention. -/
theorem trace_jointProjector_overlap
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val) :
    Matrix.trace (jointProjector p n U η * jointProjector p n L.val χ) =
      if restrictAssignment p (inf_le_left : U ⊓ L.val ≤ U) η =
          restrictAssignment p (inf_le_right : U ⊓ L.val ≤ L.val) χ then
        (p : ℂ) ^ Module.finrank (ZMod p) ↥(U ⊓ L.val) /
          (p : ℂ) ^ Module.finrank (ZMod p) U
      else 0 := by
  rw [trace_jointProjector_overlap_sum, sum_assignment_phase_ratio,
    card_submodule_eq_prime_pow p n (U ⊓ L.val)]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

/-- The physical Born overlap is the real-valued spectrum in the paper. -/
theorem born_jointProjector_overlap
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val) :
    born (jointProjector p n U η) (jointProjector p n L.val χ) =
      if restrictAssignment p (inf_le_left : U ⊓ L.val ≤ U) η =
          restrictAssignment p (inf_le_right : U ⊓ L.val ≤ L.val) χ then
        (p : ℝ) ^ Module.finrank (ZMod p) ↥(U ⊓ L.val) /
          (p : ℝ) ^ Module.finrank (ZMod p) U
      else 0 := by
  unfold born
  rw [trace_jointProjector_overlap]
  split_ifs
  · simp only [← Nat.cast_pow, Complex.div_natCast_re, Complex.natCast_re]
  · rfl

/-- If one subspace lies in another, compatibility on their intersection is
exactly equality with the restricted assignment. -/
theorem restrictAssignment_inf_eq_iff
    (U V : Submodule (ZMod p) (PhaseSpace p n))
    (η : Assignment p n U) (χ : Assignment p n V) (hUV : U ≤ V) :
    restrictAssignment p (inf_le_left : U ⊓ V ≤ U) η =
        restrictAssignment p (inf_le_right : U ⊓ V ≤ V) χ ↔
      η = restrictAssignment p hUV χ := by
  constructor
  · intro h
    apply Subtype.ext
    funext z
    have he := congrArg (fun θ : Assignment p n (U ⊓ V) =>
      θ.val ⟨z.val, z.property, hUV z.property⟩) h
    exact he
  · intro h
    subst η
    apply Subtype.ext
    funext z
    rfl

/-- Every actual overlap score is nonnegative. -/
theorem born_jointProjector_overlap_nonneg
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val) :
    0 ≤ born (jointProjector p n U η) (jointProjector p n L.val χ) := by
  rw [born_jointProjector_overlap]
  split_ifs <;> positivity

/-- The dimension of an intersection bounds every actual overlap score by one. -/
theorem born_jointProjector_overlap_le_one
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val) :
    born (jointProjector p n U η) (jointProjector p n L.val χ) ≤ 1 := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [born_jointProjector_overlap]
  split_ifs
  · apply (div_le_one (pow_pos (lt_trans zero_lt_one hp) _)).mpr
    exact (pow_le_pow_iff_right₀ hp).mpr (Submodule.finrank_mono inf_le_left)
  · norm_num

theorem born_jointProjector_overlap_mem_Icc
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val) :
    born (jointProjector p n U η) (jointProjector p n L.val χ) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨born_jointProjector_overlap_nonneg p n U η L χ,
    born_jointProjector_overlap_le_one p n U η L χ⟩

/-- Score one means the entire reported subspace and assignment are stabilizers
of the input, with no genericity or positive-dimension assumption. -/
theorem born_jointProjector_overlap_eq_one_iff
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val) :
    born (jointProjector p n U η) (jointProjector p n L.val χ) = 1 ↔
      ∃ hUL : U ≤ L.val, η = restrictAssignment p hUL χ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp
  constructor
  · intro hs
    rw [born_jointProjector_overlap] at hs
    split_ifs at hs with hc
    · have hd : Module.finrank (ZMod p) ↥(U ⊓ L.val) = Module.finrank (ZMod p) U :=
        (pow_right_injective₀ hp0 (ne_of_gt hp))
          ((div_eq_one_iff_eq (pow_ne_zero _ hp0.ne')).mp hs)
      have hUL : U ≤ L.val :=
        inf_eq_left.mp (Submodule.eq_of_le_of_finrank_eq inf_le_left hd)
      exact ⟨hUL, (restrictAssignment_inf_eq_iff p n U L.val η χ hUL).mp hc⟩
    · norm_num at hs
  · rintro ⟨hUL, hη⟩
    rw [born_jointProjector_overlap,
      if_pos ((restrictAssignment_inf_eq_iff p n U L.val η χ hUL).mpr hη),
      inf_eq_left.mpr hUL]
    exact div_self (pow_ne_zero _ hp0.ne')

/-- Every report failing the full stabilizer restriction condition has score
at most the strict one-prime gap, including all boundary subspaces. -/
theorem born_jointProjector_overlap_le_inv_prime_of_not_correct
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val)
    (hbad : ¬ ∃ hUL : U ≤ L.val, η = restrictAssignment p hUL χ) :
    born (jointProjector p n U η) (jointProjector p n L.val χ) ≤ (p : ℝ)⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp
  rw [born_jointProjector_overlap]
  split_ifs with hc
  · have hnotle : ¬ U ≤ L.val := by
      intro hUL
      exact hbad ⟨hUL, (restrictAssignment_inf_eq_iff p n U L.val η χ hUL).mp hc⟩
    have hdle : Module.finrank (ZMod p) ↥(U ⊓ L.val) ≤ Module.finrank (ZMod p) U :=
      Submodule.finrank_mono inf_le_left
    have hdne : Module.finrank (ZMod p) ↥(U ⊓ L.val) ≠ Module.finrank (ZMod p) U := by
      intro hd
      exact hnotle (inf_eq_left.mp (Submodule.eq_of_le_of_finrank_eq inf_le_left hd))
    have hdlt := lt_of_le_of_ne hdle hdne
    rw [← one_div, div_le_div_iff₀ (pow_pos hp0 _) hp0]
    simpa [pow_succ] using (pow_le_pow_iff_right₀ hp).mpr (Nat.succ_le_of_lt hdlt)
  · positivity

/-- A genuine intersection-codimension condition gives the corresponding
power-of-prime score bound, including the zero-threshold case. -/
theorem born_jointProjector_overlap_le_inv_prime_pow
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (L : Lagrangian p n) (χ : Assignment p n L.val) (t : ℕ)
    (hd : Module.finrank (ZMod p) ↥(U ⊓ L.val) + t ≤ Module.finrank (ZMod p) U) :
    born (jointProjector p n U η) (jointProjector p n L.val χ) ≤ ((p : ℝ) ^ t)⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : 0 < (p : ℝ) := lt_trans zero_lt_one hp
  rw [born_jointProjector_overlap]
  split_ifs
  · rw [← one_div, div_le_div_iff₀ (pow_pos hp0 _) (pow_pos hp0 t)]
    simpa only [← pow_add, one_mul] using (pow_le_pow_iff_right₀ hp).mpr hd
  · positivity

end StabilizerLearning.Quantum
