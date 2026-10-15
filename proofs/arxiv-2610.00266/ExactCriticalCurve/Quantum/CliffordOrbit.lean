import ExactCriticalCurve.Quantum.CliffordHadamard
import ExactCriticalCurve.Quantum.AffineStabilizer
import ExactCriticalCurve.Quantum.ComputationalStabilizer
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Transitivity of the actual Clifford normalizer on all maximal scalar-free
signed Pauli subgroups, derived from concrete gates and full normal form. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
open Matrix Classical
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

def zeroStabilizerPhase {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n)) :
    StabilizerPhaseData L where
  polar := 0
  polar_symm _ _ := rfl
  phase _ := 0
  phase_zero := rfl
  phase_add _ _ := by simp

def linearSupportStabilizer {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n)) :
    StabilizerGroup n := phaseStabilizer 0 (zeroStabilizerPhase L)

theorem mem_linearSupportStabilizer {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) (g : PauliLabel n) :
    g ∈ (linearSupportStabilizer L).carrier ↔
      g.phase = 0 ∧ g.shift ∈ L ∧ g.clock ∈ orthogonal L := by
  rw [linearSupportStabilizer, mem_phaseStabilizer]
  simp only [zeroStabilizerPhase, LinearMap.zero_apply, pauliDot_zero_right,
    bitLift_zero, mul_zero, add_zero]
  constructor
  · rintro ⟨t, ht, hb, hr⟩
    refine ⟨hr, ht ▸ t.property, ?_⟩
    rwa [← clockRestriction_ker]
  · rintro ⟨hr, ht, hb⟩
    refine ⟨⟨g.shift, ht⟩, rfl, ?_, hr⟩
    rwa [← clockRestriction_ker] at hb

theorem linearSupportStabilizer_bot (n : ℕ) :
    linearSupportStabilizer (⊥ : Submodule (ZMod 2) (BinaryVector n)) =
      computationalStabilizerGroup n := by
  apply StabilizerGroup.ext
  ext g
  rw [mem_linearSupportStabilizer]
  have hb : g.clock ∈ orthogonal (⊥ : Submodule (ZMod 2) (BinaryVector n)) := by
    intro x hx
    have hx0 : x = 0 := hx
    change binaryDot x g.clock = 0
    rw [hx0, pauliDot_zero_left]
  simp [Submodule.mem_bot, hb, computationalStabilizerGroup, computationalPauliGroup]

theorem pauliHadamardClifford_aut {n : ℕ} (a b : BinaryVector n)
    (hba : binaryDot b a = 1) (g : PauliLabel n) :
    cliffordPauliAut (pauliHadamardClifford a b hba) g =
      if binaryDot g.clock a = binaryDot b g.shift
      then ⟨g.phase + 2 * bitLift (binaryDot g.clock a), g.shift, g.clock⟩
      else ⟨g.phase, g.shift + a, g.clock + b⟩ := by
  apply pauliOperator_injective
  rw [cliffordPauliAut_operator]
  change pauliHadamardMatrix a b * pauliOperator g * (pauliHadamardMatrix a b)ᴴ = _
  rw [pauliHadamardMatrix_adjoint]
  simp only [pauliOperator, Matrix.mul_smul, Matrix.smul_mul,
    pauliHadamardMatrix_conjugation a b g.shift g.clock hba]
  split_ifs <;> simp [pauliPhase_add, pauliPhase_two_bitLift, smul_smul]

theorem binary_eq_one_of_ne_zero (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z <;> first | rfl | contradiction

def clockKernelSection {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n))
    (b : BinaryVector n) : Submodule (ZMod 2) (BinaryVector n) :=
  L ⊓ LinearMap.ker ((binaryDotForm n) b)

/-- A concrete Hadamard shrinks a linear support along an actual nonzero clock. -/
theorem pauliHadamard_linearSupport {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) (a b : BinaryVector n)
    (ha : a ∈ L) (hba : binaryDot b a = 1) :
    cliffordStabilizer (pauliHadamardClifford a b hba) (linearSupportStabilizer L) =
      linearSupportStabilizer (clockKernelSection L b) := by
  apply StabilizerGroup.eq_of_carrier_le
  rintro g ⟨f, hf, rfl⟩
  rcases (mem_linearSupportStabilizer L f).mp hf with ⟨hp, hs, hc⟩
  have hca : binaryDot f.clock a = 0 := by
    rw [binaryDot_comm]
    exact hc a ha
  change cliffordPauliAut (pauliHadamardClifford a b hba) f ∈
    (linearSupportStabilizer (clockKernelSection L b)).carrier
  rw [mem_linearSupportStabilizer, pauliHadamardClifford_aut]
  by_cases hbc : binaryDot b f.shift = 0
  · simp only [hca, hbc, hp, bitLift_zero, mul_zero, add_zero]
    refine ⟨rfl, ⟨hs, hbc⟩, ?_⟩
    intro x hx
    exact hc x hx.1
  · have hbc1 : binaryDot b f.shift = 1 := by
      exact binary_eq_one_of_ne_zero _ hbc
    simp only [hca, hbc1, zero_ne_one, if_false, hp]
    refine ⟨by trivial, ⟨L.add_mem hs ha, ?_⟩, ?_⟩
    · change binaryDot b (f.shift + a) = 0
      rw [pauliDot_add_right, hbc1, hba]
      decide
    · intro x hx
      change binaryDot x (f.clock + b) = 0
      have hcx : binaryDot x f.clock = 0 := hc x hx.1
      rw [pauliDot_add_right, hcx, zero_add, binaryDot_comm]
      exact hx.2

/-- Every unphased linear-support stabilizer is in the true computational orbit. -/
theorem linearSupportStabilizer_in_clifford_orbit {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) :
    ∃ U : CliffordGroup n,
      cliffordStabilizer U (computationalStabilizerGroup n) = linearSupportStabilizer L := by
  generalize hd : Module.finrank (ZMod 2) L = d
  induction d using Nat.strong_induction_on generalizing L with
  | h d ih =>
    by_cases hL : L = ⊥
    · subst L
      exact ⟨1, by rw [cliffordStabilizer_one, linearSupportStabilizer_bot]⟩
    · have hex : ∃ a ∈ L, a ≠ (0 : BinaryVector n) := by
        by_contra h
        push_neg at h
        apply hL
        apply le_antisymm _ bot_le
        intro x hx
        exact h x hx
      obtain ⟨a, ha, ha0⟩ := hex
      have hex : ∃ i : Fin n, a i ≠ 0 := by
        by_contra h
        push_neg at h
        exact ha0 (funext h)
      obtain ⟨i, hi⟩ := hex
      let b : BinaryVector n := Pi.single i 1
      have hba : binaryDot b a = 1 := by
        rw [binaryDot_comm, pauliDot_single_right]
        exact binary_eq_one_of_ne_zero _ hi
      let K := clockKernelSection L b
      have hKL : K < L := by
        apply lt_of_le_of_ne inf_le_left
        intro he
        have hm : a ∈ L ⊓ LinearMap.ker ((binaryDotForm n) b) := he.symm ▸ ha
        have hz : binaryDot b a = 0 := hm.2
        rw [hba] at hz
        exact one_ne_zero hz
      obtain ⟨V, hV⟩ := ih (Module.finrank (ZMod 2) K)
        (by simpa only [← hd] using Submodule.finrank_lt_finrank_of_lt hKL) K rfl
      let H := pauliHadamardClifford a b hba
      refine ⟨H⁻¹ * V, ?_⟩
      rw [cliffordStabilizer_mul, hV]
      rw [← pauliHadamard_linearSupport L a b ha hba,
        ← cliffordStabilizer_mul, inv_mul_cancel, cliffordStabilizer_one]

theorem quadraticDiagonalClifford_aut {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)}
    (p : BinaryVector n →ₗ[ZMod 2] L) (q : StabilizerPhaseData L)
    (g : PauliLabel n) :
    cliffordPauliAut (quadraticDiagonalClifford p q) g =
      ⟨g.phase + q.phase (p g.shift), g.shift,
        g.clock + quadraticDiagonalClock p q g.shift⟩ := by
  apply pauliOperator_injective
  rw [cliffordPauliAut_operator]
  exact quadraticDiagonal_conjugation p q g

/-- A genuine linear retraction extends all phases without changing the support. -/
theorem quadraticDiagonal_linearSupport {n : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n))
    (p : BinaryVector n →ₗ[ZMod 2] L) (hp : p.comp L.subtype = LinearMap.id)
    (q : StabilizerPhaseData L) :
    cliffordStabilizer (quadraticDiagonalClifford p q) (linearSupportStabilizer L) =
      phaseStabilizer 0 q := by
  have hleft (t : L) : p t.val = t := LinearMap.congr_fun hp t
  apply StabilizerGroup.eq_of_carrier_le
  rintro g ⟨f, hf, rfl⟩
  rcases (mem_linearSupportStabilizer L f).mp hf with ⟨hr, hs, hc⟩
  let t : L := ⟨f.shift, hs⟩
  have ht : p f.shift = t := hleft t
  change cliffordPauliAut (quadraticDiagonalClifford p q) f ∈ (phaseStabilizer 0 q).carrier
  rw [quadraticDiagonalClifford_aut, mem_phaseStabilizer]
  refine ⟨t, rfl, ?_, ?_⟩
  · ext u
    change binaryDot (f.clock + quadraticDiagonalClock p q f.shift) u.val = q.polar t u
    have hcu : binaryDot f.clock u.val = 0 := by
      rw [binaryDot_comm]
      exact hc u.val u.property
    rw [pauliDot_add_left, hcu, zero_add, quadraticDiagonalClock_dot, ht, hleft]
  · simp only [hr, ht, zero_add, pauliDot_zero_right, bitLift_zero, mul_zero, add_zero]

theorem pauliClifford_aut {n : ℕ} (h g : PauliLabel n) :
    cliffordPauliAut (pauliClifford h) g = h * g * h⁻¹ := by
  apply pauliOperator_injective
  rw [cliffordPauliAut_operator, pauliOperator_mul, pauliOperator_mul, pauliOperator_inv]
  rfl

theorem pauliTranslation_aut {n : ℕ} (a : BinaryVector n) (g : PauliLabel n) :
    cliffordPauliAut (pauliClifford (⟨0, a, 0⟩ : PauliLabel n)) g =
      ⟨g.phase + 2 * bitLift (binaryDot g.clock a), g.shift, g.clock⟩ := by
  rw [pauliClifford_aut]
  change pauliLabelMul (pauliLabelMul ⟨0, a, 0⟩ g) (pauliLabelInv ⟨0, a, 0⟩) = _
  apply PauliLabel.ext
  · simp [pauliLabelMul, pauliLabelInv]
  · change (a + g.shift) + a = g.shift
    rw [add_comm a g.shift, add_assoc, pauliVector_add_self, add_zero]
  · simp [pauliLabelMul, pauliLabelInv]

/-- Actual Pauli translation produces the signed affine-anchor phase. -/
theorem pauliTranslation_phaseStabilizer {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) :
    cliffordStabilizer (pauliClifford (⟨0, a, 0⟩ : PauliLabel n)) (phaseStabilizer 0 q) =
      phaseStabilizer a q := by
  apply StabilizerGroup.eq_of_carrier_le
  rintro g ⟨f, hf, rfl⟩
  obtain ⟨t, ht, hb, hr⟩ := (mem_phaseStabilizer 0 q f).mp hf
  simp only [pauliDot_zero_right, bitLift_zero, mul_zero, add_zero] at hr
  change cliffordPauliAut (pauliClifford (⟨0, a, 0⟩ : PauliLabel n)) f ∈
    (phaseStabilizer a q).carrier
  rw [pauliTranslation_aut, mem_phaseStabilizer]
  refine ⟨t, ht, hb, ?_⟩
  change f.phase + 2 * bitLift (binaryDot f.clock a) +
    2 * bitLift (binaryDot f.clock a) = q.phase t
  have hh : 2 * bitLift (binaryDot f.clock a) + 2 * bitLift (binaryDot f.clock a) = (0 : ZMod 4) := by
    generalize binaryDot f.clock a = z
    fin_cases z <;> rfl
  rw [add_assoc, hh, add_zero, hr]

/-- All full affine quadratic normal forms lie in the actual computational orbit. -/
theorem phaseStabilizer_in_clifford_orbit {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) :
    ∃ U : CliffordGroup n,
      cliffordStabilizer U (computationalStabilizerGroup n) = phaseStabilizer a q := by
  obtain ⟨V, hV⟩ := linearSupportStabilizer_in_clifford_orbit L
  obtain ⟨p, hp⟩ := L.subtype.exists_leftInverse_of_injective L.ker_subtype
  refine ⟨pauliClifford (⟨0, a, 0⟩ : PauliLabel n) * (quadraticDiagonalClifford p q * V), ?_⟩
  rw [cliffordStabilizer_mul, cliffordStabilizer_mul, hV,
    quadraticDiagonal_linearSupport L p hp q, pauliTranslation_phaseStabilizer]

/-- The actual scalar-free subgroup ensemble equals the orbit of the
computational zero stabilizer under the physical Clifford normalizer. -/
theorem stabilizer_in_clifford_orbit {n : ℕ} (S : StabilizerGroup n) :
    ∃ U : CliffordGroup n,
      cliffordStabilizer U (computationalStabilizerGroup n) = S := by
  obtain ⟨⟨A, q⟩, rfl⟩ := affineRefinementStabilizer_surjective n S
  exact phaseStabilizer_in_clifford_orbit (affineSupportAnchor A) q

/-- Genuine transitivity on the entire finite ensemble of signed Pauli groups. -/
theorem cliffordStabilizer_transitive {n : ℕ} (S T : StabilizerGroup n) :
    ∃ U : CliffordGroup n, cliffordStabilizer U S = T := by
  obtain ⟨U, hU⟩ := stabilizer_in_clifford_orbit S
  obtain ⟨V, hV⟩ := stabilizer_in_clifford_orbit T
  refine ⟨V * U⁻¹, ?_⟩
  rw [← hU, ← cliffordStabilizer_mul, mul_assoc, inv_mul_cancel, mul_one, hV]

/-- Physical rank-one projectors in the ensemble are exactly Clifford conjugates
of the independently defined computational zero projector. -/
theorem stabilizerProjection_range_eq_cliffordOrbit (n : ℕ) :
    Set.range (@stabilizerProjection n) =
      Set.range (fun U : CliffordGroup n =>
        cliffordMatrix U *
          Matrix.vecMulVec (computationalZeroVector n) (star (computationalZeroVector n)) *
            (cliffordMatrix U)ᴴ) := by
  ext P
  constructor
  · rintro ⟨S, rfl⟩
    obtain ⟨U, hU⟩ := stabilizer_in_clifford_orbit S
    refine ⟨U, ?_⟩
    dsimp only
    rw [← computationalStabilizerProjection, ← cliffordStabilizerProjection, hU]
  · rintro ⟨U, rfl⟩
    refine ⟨cliffordStabilizer U (computationalStabilizerGroup n), ?_⟩
    rw [cliffordStabilizerProjection, computationalStabilizerProjection]

end ExactCriticalCurve.Quantum
