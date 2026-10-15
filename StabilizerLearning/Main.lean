import StabilizerLearning.Verified
import StabilizerLearning.FixedConstraints.Rates

/-!
Target: paper/main-stabilizer2.tex, thm:fixed-W-no-discount.
The proposition below is unchanged. The theorem composes the physical converse,
the actual normalized direct decoder, and the original liminf/sInf rate proof.
Clean reproducibility and the exact-type axiom audit are separate release gates.
-/
namespace StabilizerLearning

def FixedWNoCopyRateDiscount : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    @FixedConstraints.NoCopyRateDiscountForPrime p ⟨hp⟩

/-- The complete original fixed-W no-copy-rate-discount theorem. -/
theorem fixedW_noCopyRateDiscount : FixedWNoCopyRateDiscount := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro β hβ hβ1
  refine ⟨?_,?_,?_⟩
  · intro α _ hα m k _ hm hk
    exact fixedConstraint_uniform_converse p hα hβ hm hk
  · intro m k _ _ hk
    exact fixedConstraint_four_uniform_limits_one p hk
  · intro ε hε0 hε1
    exact ⟨FixedConstraints.exactCopyRate_eq_one .worstCase hβ hβ1 hε0 hε1,
      FixedConstraints.exactCopyRate_eq_one .average hβ hβ1 hε0 hε1⟩

end StabilizerLearning
