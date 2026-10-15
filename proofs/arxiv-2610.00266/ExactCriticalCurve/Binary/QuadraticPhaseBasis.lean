import ExactCriticalCurve.Binary.QuadraticPhase

/-! Basis values of the explicit quadratic phase polarization. -/
noncomputable section
namespace ExactCriticalCurve.Binary

theorem two_mul_bitLift_phaseParity (c : ZMod 4) :
    (2 : ZMod 4) * bitLift (phaseParity c) = 2 * c := by
  fin_cases c <;> decide

private theorem phase_diagonal_recover (c : ZMod 4) (b : ZMod 2)
    (h : 0 = c + c + 2 * bitLift b) : b = phaseParity c := by
  fin_cases c <;> fin_cases b <;>
    first | rfl | exact False.elim ((by decide : (0 : ZMod 4) ≠ 2) h)

theorem quadraticPhasePolarForm_single_single {m : ℕ} (q : QuadraticPhaseData m)
    (i j : Fin m) :
    quadraticPhasePolarForm q (Pi.single i 1) (Pi.single j 1) =
      if i = j then phaseParity (q.1 i) else quadraticPhaseCross q.2 i j := by
  change quadraticPhasePolar q _ _ = _
  have hlt (i j : Fin m) (hij : i < j) :
      quadraticPhasePolar q (Pi.single i 1) (Pi.single j 1) =
        quadraticPhaseCross q.2 i j := by
    have h := quadraticPhaseValue_add q (Pi.single i 1) (Pi.single j 1)
    rw [quadraticPhaseValue_single_add_single q i j hij,
      quadraticPhaseValue_single, quadraticPhaseValue_single] at h
    apply doubled_bitLift_injective
    rw [quadraticPhaseCross_of_lt _ _ _ hij]
    exact (add_left_cancel h).symm
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [if_neg hij.ne]
    exact hlt i j hij
  · subst j
    rw [if_pos rfl]
    have hz : (Pi.single i (1 : ZMod 2) : BinaryVector m) + Pi.single i 1 = 0 := by
      ext l
      by_cases hl : l = i
      · subst l; simp; decide
      · simp [hl]
    have h := quadraticPhaseValue_add q (Pi.single i 1) (Pi.single i 1)
    rw [hz, quadraticPhaseValue_zero, quadraticPhaseValue_single] at h
    exact phase_diagonal_recover _ _ h
  · rw [if_neg (Ne.symm hij.ne), quadraticPhasePolar_symm,
      quadraticPhaseCross_symm]
    exact hlt j i hij

end ExactCriticalCurve.Binary
