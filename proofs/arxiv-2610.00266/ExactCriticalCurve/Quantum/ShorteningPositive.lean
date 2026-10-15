import ExactCriticalCurve.Quantum.ShorteningRelationSum
import ExactCriticalCurve.Quantum.ShorteningFiltration

/-! # Positive-degree actual shortening, in the paper's k and k-1 indices -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- The actual matrix, transported only across the successor identity k=(k-1)+1. -/
def shorteningSynthesisPositive (n : ℕ) (hk : 0 < k) (h4 : 4 ∣ k) :
    Matrix (BinaryVector n × ColumnConfig n k) (ColumnConfig n (k-1)) ℂ := by
  cases k with
  | zero => omega
  | succ m => exact shorteningSynthesis n (shortening_predecessor_odd h4)

theorem shorteningSynthesisPositive_adjoint_mul (n : ℕ) (hk : 0 < k) (h4 : 4 ∣ k) :
    (shorteningSynthesisPositive n hk h4)ᴴ * shorteningSynthesisPositive n hk h4 = 1 := by
  cases k with
  | zero => omega
  | succ m => exact shorteningSynthesis_adjoint_mul n h4

theorem shorteningSynthesisPositive_mul_adjoint (n : ℕ) (hk : 0 < k) (h4 : 4 ∣ k) :
    shorteningSynthesisPositive n hk h4 * (shorteningSynthesisPositive n hk h4)ᴴ =
      (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ cssColumnProjection n (wuLine k) := by
  cases k with
  | zero => omega
  | succ m => exact shorteningSynthesis_mul_adjoint n (shortening_predecessor_odd h4)

/-- The full actual operator identity for every n and positive k divisible by four. -/
theorem shortening_relationSum_positive (n : ℕ) (hk : 0 < k) (h4 : 4 ∣ k) :
    (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
      (cssColumnProjection n (wuLine k) * stochasticRelationSum n k *
        cssColumnProjection n (wuLine k)) =
    ((2 : ℂ)^n + (2 : ℂ)^(k-2)) •
      (shorteningSynthesisPositive n hk h4 * stochasticRelationSum n (k-1) *
        (shorteningSynthesisPositive n hk h4)ᴴ) := by
  cases k with
  | zero => omega
  | succ m => exact shortening_relationSum n h4

end ExactCriticalCurve.Quantum

