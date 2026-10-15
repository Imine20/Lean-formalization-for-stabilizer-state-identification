import StabilizerLearning.Foundations.CompletionFormula

namespace StabilizerLearning

/-- Partition the genuine coordinate tuples by their two actual matrix ranks.
The inverse removes the rank tags and uses their proved equalities to recover
the original dependent block sizes. -/
noncomputable def completionFiberRankEquiv (F : Type*) [Field F] (m s r k : ℕ) :
    BudgetCompletionFiberData F m s r k ≃ CompletionRankData F m s r k where
  toFun d := ⟨⟨(d.val.1.rank, d.val.2.2.2.2.val.rank),
      (completionRankGrid_mem m s r k _ _).mpr
        ⟨le_min d.val.1.rank_le_height d.val.1.rank_le_width,
          d.val.2.2.2.2.val.rank_le_width, d.property⟩⟩,
    d.val.2.1, ⟨d.val.1, rfl⟩, d.val.2.2.1, d.val.2.2.2.1,
      ⟨d.val.2.2.2.2, rfl⟩⟩
  invFun := by
    rintro ⟨⟨⟨ell, t⟩, hg⟩, C₁, ⟨C₀, hC⟩, A₁₁, A₁₂, ⟨A₂₂, hA⟩⟩
    have hb := ((completionRankGrid_mem m s r k ell t).mp hg).2.2
    dsimp only at A₁₁ A₁₂ A₂₂ hC hA
    change C₀.rank = ell at hC
    change A₂₂.val.rank = t at hA
    subst ell
    subst t
    exact ⟨⟨C₀, C₁, A₁₁, A₁₂, A₂₂⟩, hb⟩
  left_inv := by
    rintro ⟨⟨C₀, C₁, A₁₁, A₁₂, A₂₂⟩, hb⟩
    rfl
  right_inv := by
    rintro ⟨⟨⟨ell, t⟩, hg⟩, C₁, ⟨C₀, hC⟩, A₁₁, A₁₂, ⟨A₂₂, hA⟩⟩
    dsimp only at A₁₁ A₁₂ A₂₂ hC hA
    change C₀.rank = ell at hC
    change A₂₂.val.rank = t at hA
    subst ell
    subst t
    rfl

end StabilizerLearning
