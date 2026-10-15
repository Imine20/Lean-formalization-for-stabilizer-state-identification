import StabilizerLearning.Quantum.ReferenceFrame
import StabilizerLearning.Foundations.IntervalSubspaces
import Mathlib.LinearAlgebra.Projection

/-! Actual intersection fibres are encoded by complement projections on the
quotient K-perp/K. No cardinality or coordinate-equivalence premise is used. -/
noncomputable section
open Module
namespace StabilizerLearning

section Linear
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- Complements are recovered from the restriction of their projection to one
fixed complement. Choosing bases turns that actual map into a square matrix. -/
theorem exists_injective_complement_matrix (P : Submodule F V) (r : ℕ)
    (hP : finrank F P = r) (hV : finrank F V = r+r) :
    ∃ f : {Q : Submodule F V // IsCompl P Q} → Matrix (Fin r) (Fin r) F,
      Function.Injective f := by
  classical
  obtain ⟨Q₀, hQ₀⟩ := P.exists_isCompl
  have hdQ₀ : finrank F Q₀ = r := by
    have hh := Submodule.finrank_add_eq_of_isCompl hQ₀
    omega
  let bP := Module.finBasisOfFinrankEq F P hP
  let bQ := Module.finBasisOfFinrankEq F Q₀ hdQ₀
  refine ⟨fun Q => LinearMap.toMatrix bQ bP
    ((P.linearProjOfIsCompl Q.val Q.property).comp Q₀.subtype), ?_⟩
  intro Q T he
  have hc : (P.linearProjOfIsCompl Q.val Q.property).comp Q₀.subtype =
      (P.linearProjOfIsCompl T.val T.property).comp Q₀.subtype :=
    (LinearMap.toMatrix bQ bP).injective he
  apply P.isComplEquivProj.injective
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨u, v, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl hQ₀ x
  change P.linearProjOfIsCompl Q.val Q.property (u.val + v.val) =
    P.linearProjOfIsCompl T.val T.property (u.val + v.val)
  simp only [map_add, Submodule.linearProjOfIsCompl_apply_left]
  exact congrArg (fun z => u + z) (LinearMap.congr_fun hc v)

/-- An n-subspace with exact intersection K in P is recovered from its image
in S/K. The fixed quotient P/K has dimension r and every image complements it. -/
theorem exists_injective_intersection_matrix
    (K P S : Submodule F V) (n r : ℕ) (hr : r ≤ n)
    (hKP : K ≤ P) (hPS : P ≤ S)
    (hK : finrank F K = n-r) (hP : finrank F P = n)
    (hS : finrank F S = n+r) :
    ∃ f : {L : Submodule F V // L ≤ S ∧ finrank F L = n ∧ L ⊓ P = K} →
      Matrix (Fin r) (Fin r) F, Function.Injective f := by
  classical
  let K' := K.submoduleOf S
  let P' := P.submoduleOf S
  let Q := S ⧸ K'
  have hKS : K ≤ S := hKP.trans hPS
  have hdK : finrank F K' = n-r :=
    (Submodule.submoduleOfEquivOfLe hKS).finrank_eq.trans hK
  have hdP : finrank F P' = n :=
    (Submodule.submoduleOfEquivOfLe hPS).finrank_eq.trans hP
  have hdQ : finrank F Q = r+r := by
    change finrank F (S ⧸ K') = _
    rw [Submodule.finrank_quotient, hS, hdK]
    omega
  let Pq : Submodule F Q := P'.map K'.mkQ
  have hKP' : K' ≤ P' := Submodule.comap_mono hKP
  have hdPq : finrank F Pq = r := by
    dsimp [Pq]
    rw [finrank_map_mkQ_of_le K' P' hKP', hdP, hdK]
    omega
  let reduce (L : Submodule F V) : Submodule F Q :=
    (L.submoduleOf S).map K'.mkQ
  have hcompl (L : Submodule F V) (hLS : L ≤ S)
      (hdL : finrank F L = n) (hLP : L ⊓ P = K) :
      IsCompl Pq (reduce L) := by
    have hKL : K ≤ L := by rw [← hLP]; exact inf_le_left
    have hKL' : K' ≤ L.submoduleOf S := Submodule.comap_mono hKL
    have hdim : finrank F (reduce L) = r := by
      dsimp [reduce]
      rw [finrank_map_mkQ_of_le K' (L.submoduleOf S) hKL',
        (Submodule.submoduleOfEquivOfLe hLS).finrank_eq, hdL, hdK]
      omega
    have hinf : Pq ⊓ reduce L = ⊥ := by
      apply (Submodule.comap_injective_of_surjective K'.mkQ_surjective)
      change (P'.map K'.mkQ ⊓ (L.submoduleOf S).map K'.mkQ).comap K'.mkQ =
        (⊥ : Submodule F Q).comap K'.mkQ
      rw [Submodule.comap_inf, Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
        sup_eq_right.mpr hKP', sup_eq_right.mpr hKL', Submodule.comap_bot, Submodule.ker_mkQ]
      change P.comap S.subtype ⊓ L.comap S.subtype = K.comap S.subtype
      rw [← Submodule.comap_inf, inf_comm P L, hLP]
    have hsup : Pq ⊔ reduce L = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hh := Submodule.finrank_sup_add_finrank_inf_eq Pq (reduce L)
      rw [hinf, finrank_bot, hdPq, hdim, add_zero] at hh
      exact hh.trans hdQ.symm
    exact ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  let encode : {L : Submodule F V // L ≤ S ∧ finrank F L = n ∧ L ⊓ P = K} →
      {T : Submodule F Q // IsCompl Pq T} :=
    fun L => ⟨reduce L.val, hcompl L.val L.property.1 L.property.2.1 L.property.2.2⟩
  have hencode : Function.Injective encode := by
    intro L T he
    have hh := congrArg (fun Z : {Z : Submodule F Q // IsCompl Pq Z} =>
      Z.val.comap K'.mkQ) he
    have hKL : K' ≤ L.val.submoduleOf S := by
      apply Submodule.comap_mono
      exact L.property.2.2.symm.le.trans inf_le_left
    have hKT : K' ≤ T.val.submoduleOf S := by
      apply Submodule.comap_mono
      exact T.property.2.2.symm.le.trans inf_le_left
    change ((L.val.submoduleOf S).map K'.mkQ).comap K'.mkQ =
      ((T.val.submoduleOf S).map K'.mkQ).comap K'.mkQ at hh
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
      sup_eq_right.mpr hKL, sup_eq_right.mpr hKT] at hh
    have hv := congrArg (Submodule.map S.subtype) hh
    apply Subtype.ext
    simpa only [Submodule.submoduleOf, Submodule.map_comap_eq,
      Submodule.range_subtype, inf_of_le_right L.property.1,
      inf_of_le_right T.property.1] using hv
  obtain ⟨f, hf⟩ := exists_injective_complement_matrix Pq r hdPq hdQ
  exact ⟨f ∘ encode, hf.comp hencode⟩
end Linear


namespace Quantum
variable {p n : ℕ} [Fact p.Prime]

/-- The exact original Lagrangian intersection fibre is encoded by genuine
r-by-r matrices. The quotient, complement and reconstruction are all proved. -/
theorem exists_injective_lagrangianIntersectionFiber_matrix
    (L₀ : Lagrangian p n) (K : Submodule (ZMod p) (PhaseSpace p n))
    (hK : K ≤ L₀.val) (r : ℕ) (hr : r ≤ n)
    (hKr : finrank (ZMod p) K = n-r) :
    ∃ f : {L : Lagrangian p n // L.val ⊓ L₀.val = K} →
      Matrix (Fin r) (Fin r) (ZMod p), Function.Injective f := by
  classical
  let S := symplecticBilinForm.orthogonal K
  have hL₀S : L₀.val ≤ S := by
    intro z hz w hw
    exact L₀.property.1 w (hK hw) z hz
  have hdS : finrank (ZMod p) S = n+r := by
    dsimp [S]
    rw [LinearMap.BilinForm.finrank_orthogonal symplecticBilinForm_nondegenerate
      symplecticBilinForm_isAlt.isRefl, hKr]
    have hdV : finrank (ZMod p) (PhaseSpace p n) = 2*n := by
      simp [PhaseSpace, Configuration, Module.finrank_prod]; omega
    rw [hdV]
    omega
  let encode : {L : Lagrangian p n // L.val ⊓ L₀.val = K} →
      {L : Submodule (ZMod p) (PhaseSpace p n) //
        L ≤ S ∧ finrank (ZMod p) L = n ∧ L ⊓ L₀.val = K} := fun L =>
    ⟨L.val.val, ⟨by
      intro z hz w hw
      have hKL : K ≤ L.val.val := L.property.symm.le.trans inf_le_left
      exact L.val.property.1 w (hKL hw) z hz,
      L.val.property.2, L.property⟩⟩
  have he : Function.Injective encode := by
    intro L T h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun Z : {L : Submodule (ZMod p) (PhaseSpace p n) //
      L ≤ S ∧ finrank (ZMod p) L = n ∧ L ⊓ L₀.val = K} => Z.val) h
  obtain ⟨f, hf⟩ := exists_injective_intersection_matrix K L₀.val S n r hr
    hK hL₀S hKr L₀.property.2 hdS
  exact ⟨f ∘ encode, hf.comp he⟩

/-- Once-chosen coordinates on the complete actual fibre, not a redefinition
of its domain by matrices or by a symplectic-completion witness. -/
def lagrangianIntersectionFiberMatrix
    (L₀ : Lagrangian p n) (K : Submodule (ZMod p) (PhaseSpace p n))
    (hK : K ≤ L₀.val) (r : ℕ) (hr : r ≤ n)
    (hKr : finrank (ZMod p) K = n-r) :
    {L : Lagrangian p n // L.val ⊓ L₀.val = K} →
      Matrix (Fin r) (Fin r) (ZMod p) :=
  Classical.choose (exists_injective_lagrangianIntersectionFiber_matrix L₀ K hK r hr hKr)

theorem lagrangianIntersectionFiberMatrix_injective
    (L₀ : Lagrangian p n) (K : Submodule (ZMod p) (PhaseSpace p n))
    (hK : K ≤ L₀.val) (r : ℕ) (hr : r ≤ n)
    (hKr : finrank (ZMod p) K = n-r) :
    Function.Injective (lagrangianIntersectionFiberMatrix L₀ K hK r hr hKr) :=
  Classical.choose_spec (exists_injective_lagrangianIntersectionFiber_matrix L₀ K hK r hr hKr)

/-- A unit-rate-sufficient bound for the genuine fibre. This deliberately
counts all square matrices and does not assert the sharper symmetric count. -/
theorem card_lagrangianIntersectionFiber_le
    (L₀ : Lagrangian p n) (K : Submodule (ZMod p) (PhaseSpace p n))
    (hK : K ≤ L₀.val) (r : ℕ) (hr : r ≤ n)
    (hKr : finrank (ZMod p) K = n-r) :
    Nat.card {L : Lagrangian p n // L.val ⊓ L₀.val = K} ≤ p^(r*r) := by
  have h := Nat.card_le_card_of_injective
    (lagrangianIntersectionFiberMatrix L₀ K hK r hr hKr)
    (lagrangianIntersectionFiberMatrix_injective L₀ K hK r hr hKr)
  simpa only [Nat.card_eq_fintype_card, Matrix, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, ← pow_mul] using h

end Quantum

end StabilizerLearning
