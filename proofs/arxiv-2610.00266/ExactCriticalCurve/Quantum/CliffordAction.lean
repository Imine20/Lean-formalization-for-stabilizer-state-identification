import ExactCriticalCurve.Quantum.StabilizerGroup
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The actual Clifford normalizer and its action on Pauli stabilizers

The group is the normalizer of the represented phaseful Pauli subgroup inside
the unitary matrices. No abstract action or transitivity hypothesis is supplied.
-/
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix Classical
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

/-- The actual finite phaseful Pauli group, as a subgroup of the unitary matrices. -/
def pauliUnitarySubgroup (n : ℕ) :
    Subgroup (Matrix.unitaryGroup (BinaryVector n) ℂ) :=
  (pauliUnitaryRepresentation n).range

/-- All unitary matrices that normalize the actual represented Pauli subgroup. -/
abbrev CliffordGroup (n : ℕ) := (pauliUnitarySubgroup n).normalizer

/-- The faithful label-to-matrix identification with the actual image subgroup. -/
def pauliRangeEquiv (n : ℕ) : PauliLabel n ≃* pauliUnitarySubgroup n :=
  MonoidHom.ofInjective pauliUnitaryRepresentation_injective

/-- Transport actual unitary conjugation on the Pauli range to the faithful labels. -/
def cliffordPauliAut {n : ℕ} : CliffordGroup n →* MulAut (PauliLabel n) where
  toFun U := (pauliRangeEquiv n).trans
    (((pauliUnitarySubgroup n).normalizerMonoidHom U).trans (pauliRangeEquiv n).symm)
  map_one' := by
    apply MulEquiv.ext
    intro g
    simp only [MulEquiv.trans_apply, map_one, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' U V := by
    apply MulEquiv.ext
    intro g
    simp only [MulEquiv.trans_apply, map_mul, MulAut.mul_apply, MulEquiv.apply_symm_apply]

/-- The underlying physical unitary matrix of a Clifford normalizer element. -/
def cliffordMatrix {n : ℕ} (U : CliffordGroup n) :
    Matrix (BinaryVector n) (BinaryVector n) ℂ := U.val.val

theorem cliffordMatrix_adjoint_mul_self {n : ℕ} (U : CliffordGroup n) :
    (cliffordMatrix U)ᴴ * cliffordMatrix U = 1 :=
  (Matrix.mem_unitaryGroup_iff').mp U.val.property

theorem cliffordMatrix_mul_adjoint_self {n : ℕ} (U : CliffordGroup n) :
    cliffordMatrix U * (cliffordMatrix U)ᴴ = 1 :=
  (Matrix.mem_unitaryGroup_iff).mp U.val.property

/-- Label conjugation is exactly conjugation of the represented matrices. -/
theorem cliffordPauliAut_operator {n : ℕ} (U : CliffordGroup n) (g : PauliLabel n) :
    pauliOperator (cliffordPauliAut U g) =
      cliffordMatrix U * pauliOperator g * (cliffordMatrix U)ᴴ := by
  have h := MonoidHom.apply_ofInjective_symm pauliUnitaryRepresentation_injective
    ((pauliUnitarySubgroup n).normalizerMonoidHom U (pauliRangeEquiv n g))
  exact congrArg Subtype.val h

theorem cliffordPauliAut_trace {n : ℕ} (U : CliffordGroup n) (g : PauliLabel n) :
    Matrix.trace (pauliOperator (cliffordPauliAut U g)) =
      Matrix.trace (pauliOperator g) := by
  rw [cliffordPauliAut_operator, Matrix.trace_mul_cycle,
    cliffordMatrix_adjoint_mul_self, one_mul]


/-- Scalar exclusion is preserved by the actual normalizer action. -/
theorem clifford_image_phase_free {n : ℕ} (U : CliffordGroup n) (S : StabilizerGroup n) :
    ∀ g ∈ S.carrier.map (cliffordPauliAut U).toMonoidHom,
      g.shift = 0 → g.clock = 0 → g.phase = 0 := by
  intro g hg hs hc
  obtain ⟨h, hh, rfl⟩ := hg
  by_cases hh1 : h = 1
  · subst h
    rw [map_one]
    rfl
  · have ht : Matrix.trace (pauliOperator h) = 0 := by
      have hm := S.member_trace (⟨h, hh⟩ : S.carrier)
      simpa [show (⟨h, hh⟩ : S.carrier) ≠ 1 from fun he => hh1 (congrArg Subtype.val he)] using hm
    have hcj := cliffordPauliAut_trace U h
    rw [pauliOperator_trace, if_pos ⟨hs, hc⟩, ht] at hcj
    exact False.elim ((mul_ne_zero (pauliPhase_ne_zero _)
      (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))) hcj)

/-- The normalizer carries each actual maximal scalar-free subgroup to another. -/
def cliffordStabilizer {n : ℕ} (U : CliffordGroup n) (S : StabilizerGroup n) :
    StabilizerGroup n where
  carrier := S.carrier.map (cliffordPauliAut U).toMonoidHom
  phase_free := clifford_image_phase_free U S
  card_eq := (Nat.card_congr
    (S.carrier.equivMapOfInjective (cliffordPauliAut U).toMonoidHom
      (cliffordPauliAut U).injective).toEquiv).symm.trans S.card_eq

theorem cliffordStabilizer_one {n : ℕ} (S : StabilizerGroup n) :
    cliffordStabilizer 1 S = S := by
  apply StabilizerGroup.ext
  change S.carrier.map (cliffordPauliAut 1).toMonoidHom = S.carrier
  rw [map_one]
  change S.carrier.map (MonoidHom.id _) = S.carrier
  exact Subgroup.map_id _

theorem cliffordStabilizer_mul {n : ℕ} (U V : CliffordGroup n) (S : StabilizerGroup n) :
    cliffordStabilizer (U * V) S = cliffordStabilizer U (cliffordStabilizer V S) := by
  apply StabilizerGroup.ext
  change S.carrier.map (cliffordPauliAut (U * V)).toMonoidHom =
    (S.carrier.map (cliffordPauliAut V).toMonoidHom).map (cliffordPauliAut U).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro g
  exact congrArg (fun f : MulAut (PauliLabel n) => f g) (map_mul cliffordPauliAut U V)

/-- A genuine permutation of the entire finite stabilizer-group family. -/
def cliffordStabilizerPerm {n : ℕ} (U : CliffordGroup n) : Equiv.Perm (StabilizerGroup n) where
  toFun := cliffordStabilizer U
  invFun := cliffordStabilizer U⁻¹
  left_inv S := by rw [← cliffordStabilizer_mul, inv_mul_cancel, cliffordStabilizer_one]
  right_inv S := by rw [← cliffordStabilizer_mul, mul_inv_cancel, cliffordStabilizer_one]

/-- Covariance of the actual group-average pure projector. -/
theorem cliffordStabilizerProjection {n : ℕ} (U : CliffordGroup n) (S : StabilizerGroup n) :
    stabilizerProjection (cliffordStabilizer U S) =
      cliffordMatrix U * stabilizerProjection S * (cliffordMatrix U)ᴴ := by
  let e : S.carrier ≃* (cliffordStabilizer U S).carrier :=
    S.carrier.equivMapOfInjective (cliffordPauliAut U).toMonoidHom
    (cliffordPauliAut U).injective
  have hcard : Fintype.card (cliffordStabilizer U S).carrier = Fintype.card S.carrier :=
    (Fintype.card_congr e.toEquiv).symm
  change (Fintype.card (cliffordStabilizer U S).carrier : ℂ)⁻¹ •
      (∑ g : (cliffordStabilizer U S).carrier, pauliOperator g.val) =
    cliffordMatrix U *
      ((Fintype.card S.carrier : ℂ)⁻¹ • ∑ g : S.carrier, pauliOperator g.val) *
        (cliffordMatrix U)ᴴ
  rw [hcard, ← e.toEquiv.sum_comp (fun g => pauliOperator g.val)]
  change (Fintype.card S.carrier : ℂ)⁻¹ •
      (∑ g : S.carrier, pauliOperator (cliffordPauliAut U g.val)) = _
  simp_rw [cliffordPauliAut_operator]
  rw [← Finset.sum_mul, ← Finset.mul_sum, Matrix.mul_smul, Matrix.smul_mul]


/-- Membership in the image is an actual preimage criterion under the Pauli automorphism. -/
theorem cliffordStabilizer_mem_iff {n : ℕ} (U : CliffordGroup n)
    (S : StabilizerGroup n) (g : PauliLabel n) :
    g ∈ (cliffordStabilizer U S).carrier ↔
      (cliffordPauliAut U).symm g ∈ S.carrier :=
  Subgroup.mem_map_equiv

/-- The permutations respect multiplication in the concrete Clifford normalizer. -/
def cliffordStabilizerAction {n : ℕ} :
    CliffordGroup n →* Equiv.Perm (StabilizerGroup n) where
  toFun := cliffordStabilizerPerm
  map_one' := by
    apply Equiv.ext
    exact cliffordStabilizer_one
  map_mul' U V := by
    apply Equiv.ext
    exact cliffordStabilizer_mul U V

end ExactCriticalCurve.Quantum
