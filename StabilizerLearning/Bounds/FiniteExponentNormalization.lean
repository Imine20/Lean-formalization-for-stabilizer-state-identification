import StabilizerLearning.Bounds.FiniteStructure
import StabilizerLearning.Bounds.ConverseExponent

/-! Exact finite-to-quadratic conversion on the complete positive-mass domain.
The half-integer expressions below are proved from integral divisibility;
all dimension differences after conversion are signed real differences. -/
noncomputable section
namespace StabilizerLearning

/-- The integer hidden cost occurring in both proved row-space probability bounds. -/
def sourceHiddenCost (b k a u : ℕ) : ℤ :=
  ((k : ℤ)-a)*((b : ℤ)-a) + (u*(u+1)/2 : ℕ)

theorem nat_triangle_cast (n : ℕ) :
    ((n*(n+1)/2 : ℕ) : ℝ) = (n : ℝ)*((n : ℝ)+1)/2 := by
  rw [Nat.cast_div (Nat.two_dvd_mul_add_one n) (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast
  rfl

theorem nat_pred_triangle_cast (n : ℕ) :
    ((n*(n-1)/2 : ℕ) : ℝ) = (n : ℝ)*((n : ℝ)-1)/2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Nat.cast_div (by simpa [Nat.mul_comm] using Nat.two_dvd_mul_add_one n)
      (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    ring

theorem rankExponent_cast (D T : ℕ) (hTD : T ≤ D) :
    ((T*(2*D-T+1)/2 : ℕ) : ℝ) =
      (T : ℝ)*(2*(D : ℝ)-T+1)/2 := by
  have he := rankExponent_exact_half D T hTD
  have heR : (2 : ℝ)*((T*(2*D-T+1)/2 : ℕ) : ℝ) =
      (T : ℝ)*(2*(D : ℝ)-T+1) := by
    have hsub : T ≤ 2*D := by omega
    exact_mod_cast he
  linarith

/-- The ordinary source exponent differs from the homogeneous polynomial only
by the two exact linear half-terms. -/
theorem sourceFiniteExponent_cast (m h a u ell t : ℕ)
    (hell : ell ≤ m) (ht : t ≤ m-ell) :
    (sourceFiniteExponent m h a u ell t : ℝ) =
      completionQuadraticExponent ((m : ℝ)+h) m a u ell t +
        ((ell : ℝ)+t)/2 := by
  rw [sourceFiniteExponent_eq_signed m h a u ell t hell]
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [nat_pred_triangle_cast, rankExponent_cast (m-ell) t ht]
  rw [Nat.cast_sub hell]
  unfold completionQuadraticExponent
  ring

theorem visibleLabelExponent_cast (m b : ℕ) :
    (visibleLabelExponent m b : ℝ) =
      visibleQuadraticExponent ((m : ℝ)+b+1) m + (m : ℝ)/2 := by
  unfold visibleLabelExponent
  push_cast
  rw [nat_triangle_cast]
  unfold visibleQuadraticExponent
  ring

theorem sourceHiddenCost_cast (m b k a u : ℕ) :
    (sourceHiddenCost b k a u : ℝ) =
      hiddenQuadraticCost ((m : ℝ)+b) k m a u + (u : ℝ)/2 := by
  unfold sourceHiddenCost
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [nat_triangle_cast]
  unfold hiddenQuadraticCost
  ring

theorem sourceHiddenCost_augmented_cast (m b k a u : ℕ) :
    (sourceHiddenCost b k a u : ℝ) =
      hiddenQuadraticCost ((m : ℝ)+b+1) k m a u -
        ((k : ℝ)-a) + (u : ℝ)/2 := by
  rw [sourceHiddenCost_cast m]
  unfold hiddenQuadraticCost
  ring

/-- The full finite domain, including both probability-side constraints,
embeds exactly at total dimension m+h. -/
theorem sourceCompletionDomain_scalarFeasible {m h k a u ell t : ℕ}
    (hua : u ≤ a) (hauk : a+u ≤ k) (hah : a ≤ h)
    (hd : sourceCompletionDomain m h k a u ell t) :
    scalarCompletionFeasible ((m : ℝ)+h) k m a u ell t := by
  obtain ⟨hell, hellh, ht, hr⟩ := hd
  have huaR : (u : ℝ) ≤ a := by exact_mod_cast hua
  have haukR : (a : ℝ)+u ≤ k := by exact_mod_cast hauk
  have hahR : (a : ℝ) ≤ h := by exact_mod_cast hah
  have hellR : (ell : ℝ) ≤ m := by exact_mod_cast hell
  have hellhR : (ell : ℝ) ≤ (h : ℝ)-a+u := by exact_mod_cast hellh
  have htZ : (t : ℤ) ≤ (m : ℤ)-ell := by omega
  have htR : (t : ℝ) ≤ (m : ℝ)-ell := by exact_mod_cast htZ
  have hrR : (a : ℝ)-u+2*ell+t ≤ k := by exact_mod_cast hr
  unfold scalarCompletionFeasible
  exact ⟨by positivity, huaR, haukR, by linarith, by positivity,
    hellR, by linarith, by positivity, htR, hrR⟩

theorem positiveMassAugmented_scalarFeasible
    {F : Type*} [Field F] [Fintype F] {b k : ℕ} (m : ℕ)
    (v : Fin k → F) {z : Fin (k+1) × Fin (k+1)}
    (hz : z ∈ positiveMassAugmentedRowParameters F b k v)
    {ell t : ℕ}
    (hd : sourceCompletionDomain m (b+1) k z.1.val z.2.val ell t) :
    scalarCompletionFeasible ((m : ℝ)+b+1) k m z.1.val z.2.val ell t := by
  have hf := positiveMassAugmentedRowParameters_feasible v hz
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
    sourceCompletionDomain_scalarFeasible hf.1 hf.2.1 hf.2.2 hd

theorem positiveMassRow_scalarFeasible
    {F : Type*} [Field F] [Fintype F] {b k : ℕ} (m : ℕ)
    {z : Fin (k+1) × Fin (k+1)}
    (hz : z ∈ positiveMassRowParameters F b k)
    {ell t : ℕ}
    (hd : sourceCompletionDomain m b k z.1.val z.2.val ell t) :
    scalarCompletionFeasible ((m : ℝ)+b) k m z.1.val z.2.val ell t := by
  have hf := positiveMassRowParameters_feasible hz
  exact sourceCompletionDomain_scalarFeasible hf.1 hf.2.1 hf.2.2 hd

theorem ordinaryFinite_visible_cast (m b a u ell t : ℕ)
    (hell : ell ≤ m) (ht : t ≤ m-ell) :
    ((sourceFiniteExponent m (b+1) a u ell t -
      (visibleLabelExponent m b : ℤ) : ℤ) : ℝ) =
      completionQuadraticExponent ((m : ℝ)+b+1) m a u ell t -
      visibleQuadraticExponent ((m : ℝ)+b+1) m + ((ell : ℝ)+t-m)/2 := by
  push_cast
  rw [sourceFiniteExponent_cast m (b+1) a u ell t hell ht,
    visibleLabelExponent_cast]
  push_cast
  rw [← add_assoc]
  ring

theorem binaryFinite_visible_cast (m b a u ell t : ℕ)
    (hell : ell ≤ m) (ht : t ≤ m-ell) :
    ((sourceBinaryFiniteExponent m b a u ell t -
      (visibleLabelExponent m b : ℤ) : ℤ) : ℝ) =
      completionQuadraticExponent ((m : ℝ)+b) m a u ell t -
      visibleQuadraticExponent ((m : ℝ)+b) m + ((ell : ℝ)+t-m)/2 := by
  unfold sourceBinaryFiniteExponent
  push_cast
  rw [sourceFiniteExponent_cast m b a u ell t hell ht, visibleLabelExponent_cast]
  unfold visibleQuadraticExponent
  ring

theorem ordinaryFinite_visible_le {m b k a u ell t : ℕ}
    (hd : sourceCompletionDomain m (b+1) k a u ell t) :
    ((sourceFiniteExponent m (b+1) a u ell t -
      (visibleLabelExponent m b : ℤ) : ℤ) : ℝ) ≤
      completionQuadraticExponent ((m : ℝ)+b+1) m a u ell t -
      visibleQuadraticExponent ((m : ℝ)+b+1) m := by
  rw [ordinaryFinite_visible_cast m b a u ell t hd.1 hd.2.2.1]
  have h : ell+t ≤ m := by have := hd.1; have := hd.2.2.1; omega
  have hR : (ell : ℝ)+t ≤ m := by exact_mod_cast h
  linarith

theorem binaryFinite_visible_le {m b k a u ell t : ℕ}
    (hd : sourceCompletionDomain m b k a u ell t) :
    ((sourceBinaryFiniteExponent m b a u ell t -
      (visibleLabelExponent m b : ℤ) : ℤ) : ℝ) ≤
      completionQuadraticExponent ((m : ℝ)+b) m a u ell t -
      visibleQuadraticExponent ((m : ℝ)+b) m := by
  rw [binaryFinite_visible_cast m b a u ell t hd.1 hd.2.2.1]
  have h : ell+t ≤ m := by have := hd.1; have := hd.2.2.1; omega
  have hR : (ell : ℝ)+t ≤ m := by exact_mod_cast h
  linarith

theorem sourceHiddenCost_augmented_ge (m b k a u : ℕ) :
    hiddenQuadraticCost ((m : ℝ)+b+1) k m a u - k ≤
      (sourceHiddenCost b k a u : ℝ) := by
  rw [sourceHiddenCost_augmented_cast m]
  have ha : (0 : ℝ) ≤ a := by positivity
  have hu : (0 : ℝ) ≤ u := by positivity
  linarith

theorem sourceHiddenCost_ge (m b k a u : ℕ) :
    hiddenQuadraticCost ((m : ℝ)+b) k m a u ≤
      (sourceHiddenCost b k a u : ℝ) := by
  rw [sourceHiddenCost_cast m]
  exact le_add_of_nonneg_right (by positivity)

/-- Exact net finite exponent, with a uniform linear ordinary correction.
No feasibility constraints are dropped when the source maximum is selected. -/
theorem ordinaryFinite_net_le {m b k a u ell t : ℕ}
    (hd : sourceCompletionDomain m (b+1) k a u ell t) :
    ((-sourceHiddenCost b k a u + sourceFiniteExponent m (b+1) a u ell t -
      (visibleLabelExponent m b : ℤ) : ℤ) : ℝ) ≤
      -hiddenQuadraticCost ((m : ℝ)+b+1) k m a u -
      visibleQuadraticExponent ((m : ℝ)+b+1) m +
      completionQuadraticExponent ((m : ℝ)+b+1) m a u ell t + k := by
  have hv := ordinaryFinite_visible_le hd
  have hh := sourceHiddenCost_augmented_ge m b k a u
  push_cast at hv ⊢
  linarith

/-- Binary enhancement and label normalization cancel exactly at dimension m+b,
leaving a nonpositive linear correction. -/
theorem binaryFinite_net_le {m b k a u ell t : ℕ}
    (hd : sourceCompletionDomain m b k a u ell t) :
    ((-sourceHiddenCost b k a u + sourceBinaryFiniteExponent m b a u ell t -
      (visibleLabelExponent m b : ℤ) : ℤ) : ℝ) ≤
      -hiddenQuadraticCost ((m : ℝ)+b) k m a u -
      visibleQuadraticExponent ((m : ℝ)+b) m +
      completionQuadraticExponent ((m : ℝ)+b) m a u ell t := by
  have hv := binaryFinite_visible_le hd
  have hh := sourceHiddenCost_ge m b k a u
  push_cast at hv ⊢
  linarith

end StabilizerLearning
