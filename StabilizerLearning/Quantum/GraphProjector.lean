import StabilizerLearning.Quantum.JointProjector

/-! Matrix entries of an original physical joint projector on a transverse graph.
The proof evaluates its defining Pauli sum; no eigenstate or projector identity
is supplied as a hypothesis. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- The projection to configuration space parametrizes every summand.  The
Kronecker shift leaves exactly the term indexed by `x - y`. -/
theorem jointProjector_entry_of_graph_equiv
    (U : Submodule (ZMod p) (PhaseSpace p n))
    (e : Configuration p n ≃ U)
    (he : ∀ u, (e u).val.1 = u)
    (hn : Module.finrank (ZMod p) U = n)
    (η : Assignment p n U) (x y : Configuration p n) :
    jointProjector p n U η x y =
      ((p : ℂ) ^ n)⁻¹ * (eigenPhase p (η.val (e (x - y))))⁻¹ *
        rootPhase p (dotProduct (e (x - y)).val.2 y) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  unfold jointProjector
  simp only [hn, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  rw [← e.sum_comp]
  have hs : (∑ u : Configuration p n,
      (eigenPhase p (η.val (e u)))⁻¹ * pauli p n (e u) x y) =
      (eigenPhase p (η.val (e (x - y))))⁻¹ *
        rootPhase p (dotProduct (e (x - y)).val.2 y) := by
    rw [Finset.sum_eq_single (x - y)]
    · simp [pauli, he]
    · intro u _ hu
      have hxy : x ≠ y + u := by
        intro h
        apply hu
        exact (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using h.symm)
      simp [pauli, he, hxy]
    · simp
  rw [hs]
  ring

end StabilizerLearning.Quantum
