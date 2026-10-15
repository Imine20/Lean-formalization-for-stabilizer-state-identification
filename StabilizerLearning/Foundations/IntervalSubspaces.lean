import StabilizerLearning.Foundations.UniformRank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section
namespace StabilizerLearning

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- Actual subspaces between two fixed endpoints, of a prescribed dimension. -/
abbrev IntervalSubspaces (R S : Submodule F V) (a : ℕ) :=
  {W : Submodule F V // R ≤ W ∧ W ≤ S ∧ Module.finrank F W = a}

/-- Quotienting a subspace which contains R subtracts exactly dim R. -/
theorem finrank_map_mkQ_of_le (R W : Submodule F V) (hRW : R ≤ W) :
    Module.finrank F (W.map R.mkQ) = Module.finrank F W - Module.finrank F R := by
  have h := (R.mkQ.domRestrict W).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h
  rw [(Submodule.comapSubtypeEquivOfLe hRW).finrank_eq] at h
  omega

/-- Inject interval subspaces into the Grassmannian of the genuine quotient S/R.
Both quotient dimension and injectivity are proved, rather than assumed. -/
theorem card_intervalSubspaces_le_rankSubspaces [Fintype F]
    (R S : Submodule F V) (hRS : R ≤ S) (a : ℕ) :
    Nat.card (IntervalSubspaces R S a) ≤
      Nat.card (RankSubspaces F (Module.finrank F S - Module.finrank F R)
        (a - Module.finrank F R)) := by
  let R' := R.submoduleOf S
  let Q := S ⧸ R'
  have hRdim : Module.finrank F R' = Module.finrank F R :=
    (Submodule.submoduleOfEquivOfLe hRS).finrank_eq
  have hQdim : Module.finrank F Q = Module.finrank F S - Module.finrank F R := by
    rw [show Module.finrank F Q = Module.finrank F (S ⧸ R') from rfl,
      Submodule.finrank_quotient, hRdim]
  let e := (Module.finBasisOfFinrankEq F Q hQdim).equivFun
  let encode : IntervalSubspaces R S a →
      RankSubspaces F (Module.finrank F S - Module.finrank F R)
        (a - Module.finrank F R) := fun W =>
    ⟨((W.val.submoduleOf S).map R'.mkQ).map e.toLinearMap, by
      rw [e.finrank_map_eq]
      rw [finrank_map_mkQ_of_le R' (W.val.submoduleOf S)
        (Submodule.comap_mono W.property.1)]
      rw [hRdim, (Submodule.submoduleOfEquivOfLe W.property.2.1).finrank_eq,
        W.property.2.2]⟩
  apply Nat.card_le_card_of_injective encode
  intro W U h
  have he := congrArg Subtype.val h
  have hm : (W.val.submoduleOf S).map R'.mkQ = (U.val.submoduleOf S).map R'.mkQ :=
    (Submodule.map_injective_of_injective e.injective) he
  have hc := congrArg (Submodule.comap R'.mkQ) hm
  have hRW : R' ≤ W.val.submoduleOf S := Submodule.comap_mono W.property.1
  have hRU : R' ≤ U.val.submoduleOf S := Submodule.comap_mono U.property.1
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
    sup_eq_right.mpr hRW, sup_eq_right.mpr hRU] at hc
  apply Subtype.ext
  have hh := congrArg (Submodule.map S.subtype) hc
  simpa only [Submodule.submoduleOf, Submodule.map_comap_eq,
    Submodule.range_subtype, inf_of_le_right W.property.2.1,
    inf_of_le_right U.property.2.1] using hh

/-- Dimension-independent interval Grassmann bound, with the previously proved constant 4. -/
theorem card_intervalSubspaces_le [Fintype F]
    (R S : Submodule F V) (hRS : R ≤ S) (a : ℕ)
    (hRa : Module.finrank F R ≤ a) (haS : a ≤ Module.finrank F S) :
    (Nat.card (IntervalSubspaces R S a) : ℝ) ≤
      4 * (Fintype.card F : ℝ) ^
        ((a - Module.finrank F R) * (Module.finrank F S - a)) := by
  have hnat := card_intervalSubspaces_le_rankSubspaces R S hRS a
  have hc : (Nat.card (IntervalSubspaces R S a) : ℝ) ≤
      Nat.card (RankSubspaces F (Module.finrank F S - Module.finrank F R)
        (a - Module.finrank F R)) := by exact_mod_cast hnat
  have hle : a - Module.finrank F R ≤ Module.finrank F S - Module.finrank F R := by omega
  have hb := card_rankSubspaces_le F (Module.finrank F S - Module.finrank F R)
    (a - Module.finrank F R) hle
  have he : Module.finrank F S - Module.finrank F R - (a - Module.finrank F R) =
      Module.finrank F S - a := by omega
  rw [he] at hb
  exact hc.trans hb

end StabilizerLearning
