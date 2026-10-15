import ExactCriticalCurve.Counting.OrthogonalWeightedFlags

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting

/-- Consecutive layers cancel term by term after their true flag normalization. -/
theorem orthogonalFlagTerm_layer_recurrence (n t b : ℕ) :
    orthogonalFlagTerm n (t+b+1) t * ((4 : ℚ)^t-(2 : ℚ)^(t+b+1)*(2 : ℚ)^t) =
      orthogonalFlagTerm n (t+b) t *
        ((4 : ℚ)^t-(2 : ℚ)^n*(2 : ℚ)^t/(2 : ℚ)^(t+b)) := by
  rw [orthogonalFlagTerm,alternatingFlagTerm_eq_falling n (t+b+1) t (by omega),
    orthogonalFlagTerm,alternatingFlagTerm_eq_falling n (t+b) t (by omega)]
  have hs : t+b+1-t=b+1 := by omega
  have hd : t+b+1+t=(t+b+t)+1 := by omega
  have hp : (4 : ℚ)^t=((2 : ℚ)^t)^2 := by
    rw [← pow_mul,Nat.mul_comm t 2,pow_mul]
    norm_num
  rw [hs,Nat.add_sub_cancel_left,hd,binaryNewtonFalling_succ,binaryGLFactor_succ,hp]
  have he : 2*t*(b+1)=2*t*b+t+t := by ring
  have hq : (2 : ℚ)^(b+1)-1≠0 :=
    sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num) (by omega)))
  simp only [he,pow_add,pow_one,mul_one]
  have hq' : (2 : ℚ)^b*2-1≠0 := by simpa only [pow_succ] using hq
  field_simp [binaryGLFactor_ne_zero,binarySymplecticFactor_ne_zero,hq']
  <;> ring

/-- The two original boundaries reduce to two first-weighted flag sums. -/
theorem orthogonal_boundary_reduce (n s : ℕ) (sigma : ℚ) :
    orthogonalIncrementNewSum n (s+1) sigma + orthogonalIncrementOldSum n (s+1) sigma =
      (((2 : ℚ)^(s+1)+sigma)/2) *
        (∑ t ∈ Finset.range (s+2), orthogonalFlagTerm n (s+1) t*(2 : ℚ)^t) +
      (((2 : ℚ)^n/(2 : ℚ)^s-sigma)/2) *
        (∑ t ∈ Finset.range (s+1), orthogonalFlagTerm n s t*(2 : ℚ)^t) := by
  have hterm (t : ℕ) (ht : t∈Finset.range (s+1)) :
      orthogonalFlagTerm n (s+1) t * ((4 : ℚ)^t-(2 : ℚ)^(s+1)*(2 : ℚ)^t) =
        orthogonalFlagTerm n s t * ((4 : ℚ)^t-(2 : ℚ)^n*(2 : ℚ)^t/(2 : ℚ)^s) := by
    have hts : t≤s := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    simpa only [Nat.add_sub_of_le hts] using orthogonalFlagTerm_layer_recurrence n t (s-t)
  have hweight (t : ℕ) (ht : t∈Finset.range (s+2)) :
      ((2 : ℚ)^(s+1-t)-1)*(4 : ℚ)^t =
        (2 : ℚ)^(s+1)*(2 : ℚ)^t-(4 : ℚ)^t := by
    have hts : t≤s+1 := by have := Finset.mem_range.mp ht; omega
    have hp : (4 : ℚ)^t=(2 : ℚ)^t*(2 : ℚ)^t := by
      rw [← pow_add]
      change ((2 : ℚ)^2)^t=_
      rw [← pow_mul]
      congr 1
      omega
    have he : (2 : ℚ)^(s+1-t)*(2 : ℚ)^t=(2 : ℚ)^(s+1) := by
      rw [← pow_add,Nat.sub_add_cancel hts]
    rw [hp]
    linear_combination (2 : ℚ)^t*he
  have hsum := Finset.sum_congr rfl hterm
  have htop : orthogonalFlagTerm n (s+1) (s+1) *
      ((4 : ℚ)^(s+1)-(2 : ℚ)^(s+1)*(2 : ℚ)^(s+1))=0 := by
    have hp : (4 : ℚ)^(s+1)=(2 : ℚ)^(s+1)*(2 : ℚ)^(s+1) := by
      rw [← pow_add]
      change ((2 : ℚ)^2)^(s+1)=_
      rw [← pow_mul]
      congr 1
      omega
    rw [hp,sub_self,mul_zero]
  have hsum' : (∑ t ∈ Finset.range (s+2), orthogonalFlagTerm n (s+1) t *
      ((4 : ℚ)^t-(2 : ℚ)^(s+1)*(2 : ℚ)^t)) =
      ∑ t ∈ Finset.range (s+1), orthogonalFlagTerm n s t *
        ((4 : ℚ)^t-(2 : ℚ)^n*(2 : ℚ)^t/(2 : ℚ)^s) := by
    rw [Finset.sum_range_succ,htop,add_zero]
    exact hsum
  let A (m : ℕ) := ∑ t ∈ Finset.range (m+1), orthogonalFlagTerm n m t*(2 : ℚ)^t
  let B (m : ℕ) := ∑ t ∈ Finset.range (m+1), orthogonalFlagTerm n m t*(4 : ℚ)^t
  have hn : orthogonalIncrementNewSum n (s+1) sigma =
      ((2 : ℚ)^(s+1)+sigma/2)*A (s+1)-(1/2)*B (s+1) := by
    dsimp [orthogonalIncrementNewSum,A,B]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hweight t (by simpa only [show s+1+1=s+2 by omega] using ht)]
    ring
  have ho : orthogonalIncrementOldSum n (s+1) sigma = (1/2)*B s-(sigma/2)*A s := by
    dsimp [orthogonalIncrementOldSum,A,B]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hd : B (s+1)-(2 : ℚ)^(s+1)*A (s+1) = B s-((2 : ℚ)^n/(2 : ℚ)^s)*A s := by
    calc
      _ = ∑ t ∈ Finset.range (s+2), orthogonalFlagTerm n (s+1) t *
          ((4 : ℚ)^t-(2 : ℚ)^(s+1)*(2 : ℚ)^t) := by
        dsimp [A,B]
        rw [Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := hsum'
      _ = _ := by
        dsimp [A,B]
        rw [Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro t _
        ring
  change orthogonalIncrementNewSum n (s+1) sigma + orthogonalIncrementOldSum n (s+1) sigma =
    (((2 : ℚ)^(s+1)+sigma)/2)*A (s+1)+(((2 : ℚ)^n/(2 : ℚ)^s-sigma)/2)*A s
  rw [hn,ho]
  linear_combination -hd/2

end ExactCriticalCurve.Counting
