import ExactCriticalCurve.Binary.Geometry

/-! Signed Hamming refinements and the actual coordinate switch of relation spaces. -/
noncomputable section
open scoped BigOperators
open Classical
namespace ExactCriticalCurve.Binary

variable {k : ℕ}

/-- True selects a complex-conjugate tensor slot. -/
def signedWeightQuadratic (mask : Fin k → Bool) (x : BinaryVector k) : ZMod 4 :=
  ∑ i, if mask i then -bitLift (x i) else bitLift (x i)

def signedRelationQuadratic (mask : Fin k → Bool)
    (p : BinaryVector k × BinaryVector k) : ZMod 4 :=
  signedWeightQuadratic mask p.1 - signedWeightQuadratic mask p.2

def signatureRow (mask : Fin k → Bool) (x y : BinaryVector k) : BinaryVector k :=
  fun i => if mask i then y i else x i

@[simp] theorem signatureRow_self (mask : Fin k → Bool) (x : BinaryVector k) :
    signatureRow mask x x = x := by
  funext i
  simp [signatureRow]

/-- Exchange row and column bits exactly in the conjugate tensor slots. -/
def signatureSwitch (mask : Fin k → Bool) :
    (BinaryVector k × BinaryVector k) ≃ₗ[ZMod 2]
      (BinaryVector k × BinaryVector k) where
  toFun p := (signatureRow mask p.1 p.2, signatureRow mask p.2 p.1)
  invFun p := (signatureRow mask p.1 p.2, signatureRow mask p.2 p.1)
  left_inv p := by
    apply Prod.ext <;> funext i <;> cases h : mask i <;> simp [signatureRow, h]
  right_inv p := by
    apply Prod.ext <;> funext i <;> cases h : mask i <;> simp [signatureRow, h]
  map_add' p q := by
    apply Prod.ext <;> funext i <;> cases h : mask i <;> simp [signatureRow, h]
  map_smul' a p := by
    apply Prod.ext <;> funext i <;> cases h : mask i <;> simp [signatureRow, h]

@[simp] theorem signatureSwitch_apply (mask : Fin k → Bool)
    (x y : BinaryVector k) :
    signatureSwitch mask (x,y) = (signatureRow mask x y, signatureRow mask y x) := rfl

@[simp] theorem signatureSwitch_symm (mask : Fin k → Bool) :
    (signatureSwitch mask).symm = signatureSwitch mask := rfl

@[simp] theorem signatureSwitch_involutive (mask : Fin k → Bool)
    (p : BinaryVector k × BinaryVector k) :
    signatureSwitch mask (signatureSwitch mask p) = p :=
  (signatureSwitch mask).symm_apply_apply p

@[simp] theorem signatureSwitch_diagonal (mask : Fin k → Bool) (x : BinaryVector k) :
    signatureSwitch mask (x,x) = (x,x) := by
  simp [signatureSwitch_apply, signatureRow]

/-- The target is the signed relation form, not the original unsigned relation form. -/
theorem signedRelationQuadratic_switch (mask : Fin k → Bool)
    (p : BinaryVector k × BinaryVector k) :
    signedRelationQuadratic mask (signatureSwitch mask p) = relationQuadratic p := by
  simp only [signedRelationQuadratic, signatureSwitch, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, signedWeightQuadratic, signatureRow,
    relationQuadratic, weightQuadratic, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases mask i <;> simp <;> ring

theorem relationQuadratic_switch (mask : Fin k → Bool)
    (p : BinaryVector k × BinaryVector k) :
    relationQuadratic (signatureSwitch mask p) = signedRelationQuadratic mask p := by
  simpa using (signedRelationQuadratic_switch mask (signatureSwitch mask p)).symm

/-- The actual signed stochastic Lagrangian index family. -/
structure SignedStochasticLagrangian (mask : Fin k → Bool) where
  carrier : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)
  finrank_eq : Module.finrank (ZMod 2) carrier = k
  quadratic_zero : ∀ p ∈ carrier, signedRelationQuadratic mask p = 0
  allOnes_mem : (allOnes k, allOnes k) ∈ carrier

@[ext] theorem SignedStochasticLagrangian.ext {mask : Fin k → Bool}
    {T U : SignedStochasticLagrangian mask} (h : T.carrier = U.carrier) : T = U := by
  cases T; cases U; cases h; rfl

instance finiteSignedStochasticLagrangian (mask : Fin k → Bool) :
    Finite (SignedStochasticLagrangian mask) :=
  Finite.of_injective
    (fun T : SignedStochasticLagrangian mask =>
      (T.carrier : Set (BinaryVector k × BinaryVector k))) (by
      intro T U h
      exact SignedStochasticLagrangian.ext (SetLike.coe_injective h))

instance fintypeSignedStochasticLagrangian (mask : Fin k → Bool) :
    Fintype (SignedStochasticLagrangian mask) := Fintype.ofFinite _

def switchSubspace (mask : Fin k → Bool)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :=
  T.map (signatureSwitch mask).toLinearMap

@[simp] theorem mem_switchSubspace (mask : Fin k → Bool)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k))
    (p : BinaryVector k × BinaryVector k) :
    p ∈ switchSubspace mask T ↔ signatureSwitch mask p ∈ T := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa using hx
  · intro h
    exact ⟨signatureSwitch mask p,h,signatureSwitch_involutive mask p⟩

@[simp] theorem switchSubspace_involutive (mask : Fin k → Bool)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    switchSubspace mask (switchSubspace mask T) = T := by
  ext p
  simp

theorem switchSubspace_finrank (mask : Fin k → Bool)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Module.finrank (ZMod 2) (switchSubspace mask T) =
      Module.finrank (ZMod 2) T :=
  (signatureSwitch mask).finrank_map_eq T

def signedStochasticLagrangianEquiv (mask : Fin k → Bool) :
    StochasticLagrangian k ≃ SignedStochasticLagrangian mask where
  toFun T := {
    carrier := switchSubspace mask T.carrier
    finrank_eq := (switchSubspace_finrank mask T.carrier).trans T.finrank_eq
    quadratic_zero := by
      intro p hp
      rw [← relationQuadratic_switch mask]
      exact T.quadratic_zero _ ((mem_switchSubspace mask T.carrier p).mp hp)
    allOnes_mem := by simpa using T.allOnes_mem }
  invFun T := {
    carrier := switchSubspace mask T.carrier
    finrank_eq := (switchSubspace_finrank mask T.carrier).trans T.finrank_eq
    quadratic_zero := by
      intro p hp
      rw [← signedRelationQuadratic_switch mask]
      exact T.quadratic_zero _ ((mem_switchSubspace mask T.carrier p).mp hp)
    allOnes_mem := by simpa using T.allOnes_mem }
  left_inv T := by apply StochasticLagrangian.ext; exact switchSubspace_involutive _ _
  right_inv T := by apply SignedStochasticLagrangian.ext; exact switchSubspace_involutive _ _

@[simp] theorem signedStochasticLagrangianEquiv_carrier (mask : Fin k → Bool)
    (T : StochasticLagrangian k) :
    (signedStochasticLagrangianEquiv mask T).carrier = switchSubspace mask T.carrier := rfl

/-- The coordinate switch fixes the physical diagonal pointwise. -/
theorem switchSubspace_diagonal_mem (mask : Fin k → Bool)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) (x : BinaryVector k) :
    (x,x) ∈ switchSubspace mask T ↔ (x,x) ∈ T := by simp

end ExactCriticalCurve.Binary
