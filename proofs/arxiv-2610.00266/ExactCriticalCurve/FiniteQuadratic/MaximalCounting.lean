import ExactCriticalCurve.FiniteQuadratic.ZeroCounting
import ExactCriticalCurve.FiniteQuadratic.SingularCorrespondence

noncomputable section
namespace ExactCriticalCurve.FiniteQuadratic
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- All actual singular submodules of the given dimension. -/
abbrev SingularSubspaces (Q : QuadraticForm (ZMod 2) V) (r : ℕ) :=
  {L : Submodule (ZMod 2) V // TotallySingular Q L ∧ Module.finrank (ZMod 2) L = r}

theorem singular_span {Q : QuadraticForm (ZMod 2) V} {v : V} (hv : Q v=0) :
    TotallySingular Q (Submodule.span (ZMod 2) {v}) := by
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [Q.map_smul, hv, smul_zero]

theorem finite_binaryModule [FiniteDimensional (ZMod 2) V] : Finite V :=
  Finite.of_equiv (Fin (Module.finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm

theorem finite_binarySubmodules [FiniteDimensional (ZMod 2) V] :
    Finite (Submodule (ZMod 2) V) := by
  letI : Finite V := finite_binaryModule
  exact Finite.of_injective (fun U : Submodule (ZMod 2) V => (U : Set V)) SetLike.coe_injective

theorem card_nonzero_submodule [FiniteDimensional (ZMod 2) V]
    (L : Submodule (ZMod 2) V) :
    Nat.card {v : L // v ≠ 0} = 2^(Module.finrank (ZMod 2) L)-1 := by
  classical
  letI : Finite V := finite_binaryModule
  letI : Fintype L := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun v : L => v=0)]
  simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  norm_num

/-- Every nonzero vector in a singular submodule is a nonzero singular ambient vector. -/
def nonzeroSubmoduleEquivIncidence {Q : QuadraticForm (ZMod 2) V}
    {r : ℕ} (L : SingularSubspaces Q r) :
    {v : L.val // v≠0} ≃ {v : {v : V // Q v=0 ∧ v≠0} // v.val ∈ L.val} where
  toFun v := ⟨⟨v.val.val, L.property.1 _ v.val.property,
    fun h => v.property (Subtype.ext h)⟩, v.val.property⟩
  invFun v := ⟨⟨v.val.val, v.property⟩, fun h => v.val.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Incidence fibers over an ambient vector are exactly all singular extensions of its line. -/
def incidenceEquivExtensions (Q : QuadraticForm (ZMod 2) V) (r : ℕ)
    (v : {v : V // Q v=0 ∧ v≠0}) :
    {L : SingularSubspaces Q r // v.val ∈ L.val} ≃
    {W : Submodule (ZMod 2) V // Submodule.span (ZMod 2) {v.val} ≤ W ∧
      TotallySingular Q W ∧ Module.finrank (ZMod 2) W=r} where
  toFun L := ⟨L.val.val, (Submodule.span_singleton_le_iff_mem _ _).mpr L.property,
    L.val.property⟩
  invFun W := ⟨⟨W.val, W.property.2⟩, W.property.1 (Submodule.mem_span_singleton_self v.val)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_card_incidence {α β : Type*} [Fintype α] [Fintype β]
    (R : α → β → Prop) [DecidableRel R] :
    (∑ a : α, Fintype.card {b : β // R a b}) =
      ∑ b : β, Fintype.card {a : α // R a b} := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

theorem singular_incidence_count [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (r C : ℕ)
    (hFibers : ∀ v : {v : V // Q v=0 ∧ v≠0},
      Nat.card {L : SingularSubspaces Q r // v.val ∈ L.val}=C) :
    Nat.card (SingularSubspaces Q r) * (2^r-1) =
      Nat.card {v : V // Q v=0 ∧ v≠0} * C := by
  classical
  letI : Finite V := finite_binaryModule
  letI : Finite (Submodule (ZMod 2) V) := finite_binarySubmodules
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (Submodule (ZMod 2) V) := Fintype.ofFinite _
  have hs := sum_card_incidence
    (fun (L : SingularSubspaces Q r) (v : {v : V // Q v=0 ∧ v≠0}) => v.val ∈ L.val)
  have hleft : ∀ L : SingularSubspaces Q r,
      Fintype.card {v : {v : V // Q v=0 ∧ v≠0} // v.val∈L.val}=2^r-1 := by
    intro L
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr (nonzeroSubmoduleEquivIncidence L),
      card_nonzero_submodule, L.property.2]
  simp only [hleft, ← Nat.card_eq_fintype_card, hFibers] at hs
  simpa using hs


/-- The count is proved for every metabolic quadratic space, without a Witt classification. -/
theorem card_singularSubspaces [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2*r)
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) :
    Nat.card (SingularSubspaces Q r) = ∏ j ∈ Finset.range r, (1+2^j) := by
  classical
  induction r generalizing V with
  | zero =>
    letI : Unique (SingularSubspaces Q 0) := {
      default := ⟨⊥, (by intro x hx; have hx0 : x=0 := hx; rw [hx0, Q.map_zero]),
        by simp⟩
      uniq := fun U => Subtype.ext (Submodule.finrank_eq_zero.mp U.property.2) }
    simp
  | succ r ih =>
    have hFibers : ∀ v : {v : V // Q v=0 ∧ v≠0},
        Nat.card {M : SingularSubspaces Q (r+1) // v.val ∈ M.val} =
          ∏ j ∈ Finset.range r, (1+2^j) := by
      intro v
      let U : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {v.val}
      have hU : TotallySingular Q U := singular_span v.property.1
      have hdU : Module.finrank (ZMod 2) U = 1 := finrank_span_singleton v.property.2
      have hdquot : Module.finrank (ZMod 2) (OrthogonalQuotient Q U) = 2*r := by
        simpa [hdU] using finrank_orthogonalQuotient hQ hV hU
      obtain ⟨M, hM, hdM⟩ := orthogonalQuotient_metabolic hQ hV hL hdL hU
      have hdM' : Module.finrank (ZMod 2) M=r := by simpa [hdU] using hdM
      have hc := ih (orthogonalQuotientForm Q U hU)
        (orthogonalQuotientForm_nondegenerate hQ hU) hdquot hM hdM'
      rw [Nat.card_congr (incidenceEquivExtensions Q (r+1) v)]
      change Nat.card {W : Submodule (ZMod 2) V //
        U≤W ∧ TotallySingular Q W ∧ Module.finrank (ZMod 2) W=r+1} = _
      rw [card_singularExtensions_eq_quotient Q U hU]
      have he : ∀ N : Submodule (ZMod 2) (OrthogonalQuotient Q U),
          (TotallySingular (orthogonalQuotientForm Q U hU) N ∧
            Module.finrank (ZMod 2) N+Module.finrank (ZMod 2) U=r+1) ↔
          (TotallySingular (orthogonalQuotientForm Q U hU) N ∧ Module.finrank (ZMod 2) N=r) := by
        intro N
        simp [hdU]
      rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
      exact hc
    have hcount := singular_incidence_count Q (r+1) _ hFibers
    rw [card_nonzeroSingularVectors hQ hV hL hdL] at hcount
    simp only [Nat.add_sub_cancel] at hcount
    rw [Finset.prod_range_succ]
    have hp : 0 < 2^(r+1)-1 := by
      have hp' : 0 < 2^r := pow_pos (by omega) _
      rw [pow_succ]
      omega
    apply Nat.eq_of_mul_eq_mul_right hp
    calc
      Nat.card (SingularSubspaces Q (r+1)) * (2^(r+1)-1) =
          (2^(r+1)-1)*(2^r+1)*(∏ j ∈ Finset.range r, (1+2^j)) := hcount
      _ = ((∏ j ∈ Finset.range r, (1+2^j))*(1+2^r))*(2^(r+1)-1) := by ring

/-- Counting order-maximal singular submodules is a consequence of the proved dimension bridge. -/
theorem card_maximalSingularSubspaces [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2*r)
    {L : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) :
    Nat.card {U : Submodule (ZMod 2) V // TotallySingular Q U ∧
      ∀ W : Submodule (ZMod 2) V, TotallySingular Q W → U≤W → W=U} =
      ∏ j ∈ Finset.range r, (1+2^j) := by
  have he : ∀ U : Submodule (ZMod 2) V,
      (TotallySingular Q U ∧ ∀ W : Submodule (ZMod 2) V, TotallySingular Q W → U≤W → W=U) ↔
      (TotallySingular Q U ∧ Module.finrank (ZMod 2) U=r) := by
    intro U
    exact and_congr_right (fun hU => totallySingular_maximal_iff_finrank hQ hV hL hdL hU)
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact card_singularSubspaces Q hQ hV hL hdL


/-- Exact count of all half-dimensional singular extensions of any given singular submodule. -/
theorem card_singularExtensions [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2*r)
    {L U : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) (hU : TotallySingular Q U) :
    Nat.card {W : Submodule (ZMod 2) V // U≤W ∧ TotallySingular Q W ∧
      Module.finrank (ZMod 2) W=r} =
      ∏ j ∈ Finset.range (r-Module.finrank (ZMod 2) U), (1+2^j) := by
  have hbound := hU.finrank_le hQ hV
  obtain ⟨M, hM, hdM⟩ := orthogonalQuotient_metabolic hQ hV hL hdL hU
  have hc := card_singularSubspaces (orthogonalQuotientForm Q U hU)
    (orthogonalQuotientForm_nondegenerate hQ hU)
    (finrank_orthogonalQuotient hQ hV hU) hM hdM
  rw [card_singularExtensions_eq_quotient Q U hU]
  have he : ∀ N : Submodule (ZMod 2) (OrthogonalQuotient Q U),
      (TotallySingular (orthogonalQuotientForm Q U hU) N ∧
        Module.finrank (ZMod 2) N+Module.finrank (ZMod 2) U=r) ↔
      (TotallySingular (orthogonalQuotientForm Q U hU) N ∧
        Module.finrank (ZMod 2) N=r-Module.finrank (ZMod 2) U) := by
    intro N
    exact and_congr_right (fun _ => by omega)
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact hc

theorem card_maximalSingularExtensions [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {r : ℕ} (hV : Module.finrank (ZMod 2) V = 2*r)
    {L U : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) (hU : TotallySingular Q U) :
    Nat.card {W : Submodule (ZMod 2) V // U≤W ∧ TotallySingular Q W ∧
      ∀ T : Submodule (ZMod 2) V, TotallySingular Q T → W≤T → T=W} =
      ∏ j ∈ Finset.range (r-Module.finrank (ZMod 2) U), (1+2^j) := by
  have he : ∀ W : Submodule (ZMod 2) V,
      (U≤W ∧ TotallySingular Q W ∧
        ∀ T : Submodule (ZMod 2) V, TotallySingular Q T → W≤T → T=W) ↔
      (U≤W ∧ TotallySingular Q W ∧ Module.finrank (ZMod 2) W=r) := by
    intro W
    exact and_congr_right (fun _ =>
      and_congr_right (fun hW => totallySingular_maximal_iff_finrank hQ hV hL hdL hW))
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact card_singularExtensions Q hQ hV hL hdL hU

end ExactCriticalCurve.FiniteQuadratic
