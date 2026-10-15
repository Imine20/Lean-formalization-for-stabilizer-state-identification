import StabilizerLearning.Bounds.OddCoordinateProbability
import StabilizerLearning.Bounds.BinaryCoordinateProbability

/-! A concrete always-guess measurement makes the source optima strictly
positive. This justifies ordinary real logarithms without a positivity premise. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning

theorem characterSuccess_constantPOVM {Ω V L : Type*}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (code : Ω → V × L) (y : AddChar V ℂ) :
    characterSuccess code (constantPOVM Ω (AddChar V ℂ) y) =
      1 / (Fintype.card (AddChar V ℂ) : ℝ) := by
  classical
  simp [characterSuccess, constantPOVM, Quantum.born, ite_mul, apply_ite]

theorem characterOptimalSuccess_guess_le {Ω V L : Type*}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (code : Ω → V × L) :
    1 / (Fintype.card (AddChar V ℂ) : ℝ) ≤ characterOptimalSuccess code := by
  have hb : BddAbove (Set.range (characterSuccess code)) := by
    refine ⟨codedWeightedSupport code, ?_⟩
    rintro _ ⟨M, rfl⟩
    exact characterSuccess_le_weighted_count code M
  have h := le_csSup hb (Set.mem_range_self (constantPOVM Ω (AddChar V ℂ) 0))
  rwa [characterSuccess_constantPOVM] at h

theorem characterOptimalSuccess_pos {Ω V L : Type*}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (code : Ω → V × L) : 0 < characterOptimalSuccess code :=
  lt_of_lt_of_le (by positivity) (characterOptimalSuccess_guess_le code)

theorem oddCoordinateOptimalSuccess_pos (p m n k : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) : 0 < oddCoordinateOptimalSuccess p m n k := by
  rw [oddCoordinateOptimalSuccess_eq_character p m n h2]
  exact characterOptimalSuccess_pos _

theorem binaryCoordinateOptimalSuccess_pos (m n k : ℕ) :
    0 < binaryCoordinateOptimalSuccess m n k := by
  rw [binaryCoordinateOptimalSuccess_eq_character]
  exact characterOptimalSuccess_pos _

theorem oddCoordinateOptimalSuccess_guess_le (p m n k : ℕ) [Fact p.Prime]
    (h2 : (2 : ZMod p) ≠ 0) :
    ((p : ℝ)^visibleLabelExponent m n)⁻¹ ≤ oddCoordinateOptimalSuccess p m n k := by
  rw [oddCoordinateOptimalSuccess_eq_character p m n h2]
  have h := characterOptimalSuccess_guess_le (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod p) =>
    ordinaryMomentCode (fullMoment X))
  rw [AddChar.card_eq, ← Nat.card_eq_fintype_card] at h
  simpa only [card_ordinaryVisibleCoordinates, partialLabelExponent, visibleLabelExponent,
    ZMod.card, Nat.cast_pow, one_div] using h

theorem binaryCoordinateOptimalSuccess_guess_le (m n k : ℕ) :
    ((2 : ℝ)^visibleLabelExponent m n)⁻¹ ≤ binaryCoordinateOptimalSuccess m n k := by
  rw [binaryCoordinateOptimalSuccess_eq_character]
  have h := characterOptimalSuccess_guess_le (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
    binaryMomentCode (binaryEnhancedMoment X))
  rw [AddChar.card_eq, ← Nat.card_eq_fintype_card] at h
  simpa only [card_binaryVisibleCoordinates, partialLabelExponent, visibleLabelExponent,
    Nat.cast_pow, Nat.cast_ofNat, one_div] using h

/-- The same original coordinate experiment, selected by characteristic.
This does not identify it with the separate fixed-W operational task. -/
def coordinateOptimalSuccess (p m b k : ℕ) [Fact p.Prime] : ℝ :=
  if p = 2 then binaryCoordinateOptimalSuccess m b k
  else oddCoordinateOptimalSuccess p m b k

theorem prime_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  have he := (Nat.dvd_prime Nat.prime_two).mp hd
  exact he.elim (fun h1 => (Fact.out : p.Prime).ne_one h1) hp

theorem coordinateOptimalSuccess_guess_le (p m b k : ℕ) [Fact p.Prime] :
    ((p : ℝ)^visibleLabelExponent m b)⁻¹ ≤ coordinateOptimalSuccess p m b k := by
  unfold coordinateOptimalSuccess
  split_ifs with hp
  · subst p
    exact binaryCoordinateOptimalSuccess_guess_le m b k
  · exact oddCoordinateOptimalSuccess_guess_le p m b k (prime_two_ne_zero p hp)

theorem coordinateOptimalSuccess_pos (p m b k : ℕ) [Fact p.Prime] :
    0 < coordinateOptimalSuccess p m b k := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact lt_of_lt_of_le (inv_pos.mpr (pow_pos hp _))
    (coordinateOptimalSuccess_guess_le p m b k)

end StabilizerLearning
