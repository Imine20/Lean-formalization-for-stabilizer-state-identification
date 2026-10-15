import StabilizerLearning.Quantum.LagrangianShellGeometry
import StabilizerLearning.FixedConstraints.AdaptedFrame

/-! Exact intersection fibres, reduced by deleting the common vertical tail. -/
noncomputable section
open scoped BigOperators Matrix
open Module
namespace StabilizerLearning.Quantum
variable {p r b : ℕ} [Fact p.Prime]

def shellAssemble : (PhaseSpace p r × Configuration p b) →ₗ[ZMod p] PhaseSpace p (r+b) where
  toFun u := (Fin.append u.1.1 0, Fin.append u.1.2 u.2)
  map_add' u v := by
    apply Prod.ext <;> funext i <;> refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  map_smul' c u := by
    apply Prod.ext <;> funext i <;> refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

def shellReduce : PhaseSpace p (r+b) →ₗ[ZMod p] PhaseSpace p r where
  toFun z := (fun i => z.1 (i.castAdd b), fun i => z.2 (i.castAdd b))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def shellTailValue : PhaseSpace p (r+b) →ₗ[ZMod p] Configuration p b where
  toFun z := fun i => z.2 (i.natAdd r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def shellTail : Configuration p b →ₗ[ZMod p] PhaseSpace p (r+b) :=
  shellAssemble.comp (LinearMap.inr (ZMod p) (PhaseSpace p r) (Configuration p b))

def shellTailSubspace : Submodule (ZMod p) (PhaseSpace p (r+b)) := LinearMap.range shellTail

def shellVertical : Submodule (ZMod p) (PhaseSpace p (r+b)) :=
  LinearMap.ker (LinearMap.fst (ZMod p) (Configuration p (r+b)) (Configuration p (r+b)))

@[simp] theorem shellReduce_assemble (u : PhaseSpace p r) (t : Configuration p b) :
    shellReduce (shellAssemble (u,t)) = u := by
  apply Prod.ext <;> funext i <;> simp [shellReduce, shellAssemble]

@[simp] theorem shellTailValue_assemble (u : PhaseSpace p r) (t : Configuration p b) :
    shellTailValue (shellAssemble (u,t)) = t := by
  funext i; simp [shellTailValue, shellAssemble]

@[simp] theorem shellReduce_tail (t : Configuration p b) :
    shellReduce (shellTail (p:=p) (r:=r) t) = 0 := shellReduce_assemble 0 t

theorem shellAssemble_injective :
    Function.Injective (shellAssemble (p:=p) (r:=r) (b:=b)) := by
  rintro ⟨u,s⟩ ⟨v,t⟩ h
  apply Prod.ext
  · simpa using congrArg shellReduce h
  · simpa using congrArg shellTailValue h

theorem shellTail_injective :
    Function.Injective (shellTail (p:=p) (r:=r) (b:=b)) := by
  intro u v h
  simpa [shellTail] using congrArg shellTailValue h

@[simp] theorem finrank_shellTailSubspace :
    finrank (ZMod p) (shellTailSubspace (p:=p) (r:=r) (b:=b)) = b := by
  rw [shellTailSubspace, LinearMap.finrank_range_of_inj shellTail_injective]
  simp [Configuration]

@[simp] theorem mem_shellVertical (z : PhaseSpace p (r+b)) :
    z ∈ shellVertical (p:=p) (r:=r) (b:=b) ↔ z.1 = 0 := Iff.rfl

theorem shellAssemble_recover (z : PhaseSpace p (r+b))
    (hz : ∀ i : Fin b, z.1 (i.natAdd r) = 0) :
    shellAssemble (shellReduce z, shellTailValue z) = z := by
  apply Prod.ext <;> funext i <;> refine Fin.addCases ?_ ?_ i <;> intro j
  all_goals simp [shellAssemble, shellReduce, shellTailValue, hz]

theorem mem_shellTailSubspace_iff (z : PhaseSpace p (r+b)) :
    z ∈ shellTailSubspace (p:=p) (r:=r) (b:=b) ↔
      z.1 = 0 ∧ ∀ i : Fin r, z.2 (i.castAdd b) = 0 := by
  constructor
  · rintro ⟨t,rfl⟩
    constructor
    · funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [shellTail, shellAssemble]
    · intro i; simp [shellTail, shellAssemble]
  · rintro ⟨hx,hz⟩
    refine ⟨shellTailValue z, ?_⟩
    change shellAssemble (0, shellTailValue z) = z
    have hred : shellReduce z = 0 := by
      apply Prod.ext <;> funext i <;> simp [shellReduce, hx, hz]
    rw [← hred]
    exact shellAssemble_recover z (by simp [hx])

theorem symplecticPairing_shellAssemble (u v : PhaseSpace p r)
    (s t : Configuration p b) :
    symplecticPairing (shellAssemble (u,s)) (shellAssemble (v,t)) =
      symplecticPairing u v := by
  simp [shellAssemble, symplecticPairing, dotProduct, Fin.sum_univ_add]

theorem symplecticPairing_shellReduce (z w : PhaseSpace p (r+b))
    (hz : ∀ i : Fin b, z.1 (i.natAdd r) = 0)
    (hw : ∀ i : Fin b, w.1 (i.natAdd r) = 0) :
    symplecticPairing (shellReduce z) (shellReduce w) = symplecticPairing z w := by
  rw [← shellAssemble_recover z hz, ← shellAssemble_recover w hw]
  rw [shellReduce_assemble, shellReduce_assemble, symplecticPairing_shellAssemble]

abbrev StandardShellFiber (p r b : ℕ) [Fact p.Prime] :=
  {L : Lagrangian p (r+b) // L.val ⊓ shellVertical = shellTailSubspace}

theorem shellTail_le (L : StandardShellFiber p r b) :
    shellTailSubspace ≤ L.val.val := L.property.symm.le.trans inf_le_left

theorem shell_fst_tail_zero (L : StandardShellFiber p r b)
    (z : PhaseSpace p (r+b)) (hz : z ∈ L.val.val) (i : Fin b) :
    z.1 (i.natAdd r) = 0 := by
  have ht : shellTail (p:=p) (r:=r) (Pi.single i 1) ∈ L.val.val :=
    shellTail_le L (LinearMap.mem_range_self _ _)
  have h := L.val.property.1 z hz _ ht
  simpa [shellTail, shellAssemble, symplecticPairing, dotProduct,
    Fin.sum_univ_add, Pi.single_apply] using h

theorem shell_reduce_fst_zero (L : StandardShellFiber p r b)
    (z : PhaseSpace p (r+b)) (hz : z ∈ L.val.val)
    (hfst : (shellReduce z).1 = 0) : z ∈ shellTailSubspace := by
  rw [← L.property]
  refine ⟨hz, ?_⟩
  apply (mem_shellVertical z).mpr
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; exact congrFun hfst j
  · intro j; exact shell_fst_tail_zero L z hz j

theorem shell_reduce_transverse (L : StandardShellFiber p r b) :
    IsTransverse (L.val.val.map shellReduce) := by
  rintro z ⟨w,hw,rfl⟩ hz
  obtain ⟨t,ht⟩ := shell_reduce_fst_zero L w hw hz
  rw [← ht, shellReduce_tail]

theorem finrank_shell_reduce (L : StandardShellFiber p r b) :
    finrank (ZMod p) (L.val.val.map shellReduce) = r := by
  let f := (shellReduce (p:=p) (r:=r) (b:=b)).domRestrict L.val.val
  have hker : LinearMap.ker f = shellTailSubspace.comap L.val.val.subtype := by
    ext z
    constructor
    · intro hz
      exact shell_reduce_fst_zero L z.val z.property
        (congrArg Prod.fst (show shellReduce z.val = 0 from hz))
    · intro hz
      obtain ⟨t,ht⟩ := hz
      change shellTail t = z.val at ht
      change shellReduce z.val = 0
      rw [← ht, shellReduce_tail]
  have h := f.finrank_range_add_finrank_ker
  rw [show LinearMap.range f = L.val.val.map shellReduce from LinearMap.range_domRestrict _ _,
    hker, (Submodule.comapSubtypeEquivOfLe (shellTail_le L)).finrank_eq,
    finrank_shellTailSubspace, L.val.property.2] at h
  omega

def shellReducedLagrangian (L : StandardShellFiber p r b) : TransverseLagrangian p r :=
  ⟨⟨L.val.val.map shellReduce, ⟨by
    rintro z ⟨u,hu,rfl⟩ w ⟨v,hv,rfl⟩
    rw [symplecticPairing_shellReduce u v (shell_fst_tail_zero L u hu)
      (shell_fst_tail_zero L v hv)]
    exact L.val.property.1 u hu v hv,
    finrank_shell_reduce L⟩⟩, shell_reduce_transverse L⟩

def shellInflateMap (U : TransverseLagrangian p r) :
    (U.val.val × Configuration p b) →ₗ[ZMod p] PhaseSpace p (r+b) :=
  shellAssemble.comp (U.val.val.subtype.prodMap LinearMap.id)

@[simp] theorem shellInflateMap_apply (U : TransverseLagrangian p r)
    (u : U.val.val) (t : Configuration p b) :
    shellInflateMap U (u,t) = shellAssemble (u.val,t) := rfl

theorem shellInflateMap_injective (U : TransverseLagrangian p r) :
    Function.Injective (shellInflateMap (b:=b) U) := by
  rintro ⟨u,s⟩ ⟨v,t⟩ h
  have h' := shellAssemble_injective h
  change (u.val,s) = (v.val,t) at h'
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (congrArg (fun x : PhaseSpace p r × Configuration p b => x.2) h')

def shellInflatedLagrangian (U : TransverseLagrangian p r) : Lagrangian p (r+b) :=
  ⟨LinearMap.range (shellInflateMap U), ⟨by
    rintro z ⟨⟨u,s⟩,rfl⟩ w ⟨⟨v,t⟩,rfl⟩
    rw [shellInflateMap_apply, shellInflateMap_apply, symplecticPairing_shellAssemble]
    exact U.val.property.1 u.val u.property v.val v.property,
    by
      rw [LinearMap.finrank_range_of_inj (shellInflateMap_injective U),
        Module.finrank_prod, U.val.property.2]
      simp [Configuration]⟩⟩

theorem shellInflated_inf_vertical (U : TransverseLagrangian p r) :
    (shellInflatedLagrangian (b:=b) U).val ⊓ shellVertical = shellTailSubspace := by
  ext z
  constructor
  · rintro ⟨⟨⟨u,t⟩,rfl⟩, hz⟩
    have hu : u.val.1 = 0 := by
      funext i
      simpa [shellInflateMap, shellAssemble] using congrFun hz (i.castAdd b)
    have hu0 := U.property u.val u.property hu
    exact ⟨t, by simp [shellInflateMap, shellTail, hu0]⟩
  · rintro ⟨t,rfl⟩
    constructor
    · exact ⟨(0,t), rfl⟩
    · apply (mem_shellVertical _).mpr
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [shellTail, shellAssemble]

def shellInflatedFiber (U : TransverseLagrangian p r) : StandardShellFiber p r b :=
  ⟨shellInflatedLagrangian U, shellInflated_inf_vertical U⟩

theorem shellReduced_inflated (U : TransverseLagrangian p r) :
    shellReducedLagrangian (shellInflatedFiber (b:=b) U) = U := by
  apply Subtype.ext
  apply Subtype.ext
  ext z
  constructor
  · rintro ⟨w,⟨⟨u,t⟩,rfl⟩,rfl⟩
    simpa only [shellInflateMap_apply, shellReduce_assemble] using u.property
  · intro hz
    exact ⟨shellAssemble (z,0), ⟨(⟨z,hz⟩,0),rfl⟩, shellReduce_assemble z 0⟩

theorem shellInflated_reduced (L : StandardShellFiber p r b) :
    shellInflatedFiber (shellReducedLagrangian L) = L := by
  apply Subtype.ext
  apply Subtype.ext
  ext z
  constructor
  · rintro ⟨⟨u,t⟩,rfl⟩
    obtain ⟨w,hw,heq⟩ := u.property
    have htail : shellTail (t-shellTailValue w) ∈ L.val.val :=
      shellTail_le L (LinearMap.mem_range_self _ _)
    have heq' : shellAssemble (u.val,t) = w + shellTail (t-shellTailValue w) := by
      rw [← shellAssemble_recover w (shell_fst_tail_zero L w hw)]
      simp only [shellTailValue_assemble]
      change shellAssemble (u.val,t) =
        shellAssemble (shellReduce w,shellTailValue w) + shellAssemble (0,t-shellTailValue w)
      rw [← map_add]
      congr 1
      apply Prod.ext
      · simpa using heq.symm
      · simp
    rw [shellInflateMap_apply, heq']
    exact L.val.val.add_mem hw htail
  · intro hz
    exact ⟨(⟨shellReduce z, ⟨z,hz,rfl⟩⟩,shellTailValue z),
      shellAssemble_recover z (shell_fst_tail_zero L z hz)⟩

/-- Deleting the actual common tail and reinserting it are inverse operations. -/
def standardShellFiberEquivTransverse :
    StandardShellFiber p r b ≃ TransverseLagrangian p r where
  toFun := shellReducedLagrangian
  invFun := shellInflatedFiber
  left_inv := shellInflated_reduced
  right_inv := shellReduced_inflated

/-- Every standard exact intersection fibre has unique symmetric graph coordinates. -/
def standardShellFiberEquivSymmetricMatrices :
    StandardShellFiber p r b ≃ SymmetricMatrices (Fin r) (ZMod p) :=
  standardShellFiberEquivTransverse.trans transverseLagrangianEquivSymmetricMatrices

/-- Regard the given common intersection as the original isotropic constraint. -/
def shellConstraint (L₀ : Lagrangian p (r+b))
    (K : Submodule (ZMod p) (PhaseSpace p (r+b))) (hK : K ≤ L₀.val)
    (hKr : finrank (ZMod p) K = b) : FixedConstraints.Constraint p (r+b) r where
  subspace := K
  dimension_allowed := Nat.le_add_right _ _
  isotropic := fun z hz w hw => L₀.property.1 z (hK hz) w (hK hw)
  dimension := by simpa using hKr

def shellReferenceFrame (L₀ : Lagrangian p (r+b))
    (K : Submodule (ZMod p) (PhaseSpace p (r+b))) (hK : K ≤ L₀.val)
    (hKr : finrank (ZMod p) K = b) : OrderedLagrangianFrame p (r+b) :=
  FixedConstraints.adaptedReferenceFrame (shellConstraint L₀ K hK hKr) L₀ hK

theorem shellReferenceFrame_map_vertical (L₀ : Lagrangian p (r+b))
    (K : Submodule (ZMod p) (PhaseSpace p (r+b))) (hK : K ≤ L₀.val)
    (hKr : finrank (ZMod p) K = b) :
    L₀.val.map (frameStandardization (shellReferenceFrame L₀ K hK hKr)).toLinearMap =
      shellVertical := by
  let R := shellReferenceFrame L₀ K hK hKr
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    apply (mem_shellVertical _).mpr
    change (frameStandardization R w).1 = 0
    rw [frameStandardization_first]
    exact (referencePairingMap_eq_zero_iff R w).mpr hw
  · intro hz
    refine ⟨(frameStandardization R).symm z, ?_, (frameStandardization R).apply_symm_apply z⟩
    apply (referencePairingMap_eq_zero_iff R _).mp
    rw [← frameStandardization_first, LinearEquiv.apply_symm_apply]
    exact hz

theorem shellReferenceFrame_map_tail (L₀ : Lagrangian p (r+b))
    (K : Submodule (ZMod p) (PhaseSpace p (r+b))) (hK : K ≤ L₀.val)
    (hKr : finrank (ZMod p) K = b) :
    K.map (frameStandardization (shellReferenceFrame L₀ K hK hKr)).toLinearMap =
      shellTailSubspace := by
  let R := shellReferenceFrame L₀ K hK hKr
  have hspan : Submodule.span (ZMod p)
      (Set.range (fun i : Fin b => frameVector R (i.natAdd r))) = K :=
    FixedConstraints.adaptedReferenceFrame_tail_span (shellConstraint L₀ K hK hKr) L₀ hK
  apply Submodule.eq_of_le_of_finrank_eq
  · change K.map (frameStandardization R).toLinearMap ≤ shellTailSubspace
    rw [← hspan, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro z ⟨w,⟨i,rfl⟩,rfl⟩
    rw [LinearEquiv.coe_coe, frameStandardization_basis]
    apply (mem_shellTailSubspace_iff _).mpr
    refine ⟨rfl, ?_⟩
    intro j
    simp [Pi.single_apply]
    intro h
    have hv := congrArg Fin.val h
    change j.val = r + i.val at hv
    omega
  · rw [LinearEquiv.finrank_map_eq, hKr, finrank_shellTailSubspace]

/-- Standardizing a frame adapted to the actual K transports exactly the
original intersection predicate, in both directions. -/
theorem shellReferenceFrame_intersection_iff (L₀ : Lagrangian p (r+b))
    (K : Submodule (ZMod p) (PhaseSpace p (r+b))) (hK : K ≤ L₀.val)
    (hKr : finrank (ZMod p) K = b) (L : Lagrangian p (r+b)) :
    L.val ⊓ L₀.val = K ↔
      (frameMapLagrangian (shellReferenceFrame L₀ K hK hKr) L).val ⊓ shellVertical =
        shellTailSubspace := by
  let R := shellReferenceFrame L₀ K hK hKr
  let g := frameStandardization R
  rw [← shellReferenceFrame_map_vertical L₀ K hK hKr,
    ← shellReferenceFrame_map_tail L₀ K hK hKr]
  change L.val ⊓ L₀.val = K ↔
    L.val.map g.toLinearMap ⊓ L₀.val.map g.toLinearMap = K.map g.toLinearMap
  rw [← Submodule.map_inf g.toLinearMap g.injective]
  exact (Submodule.orderIsoMapComap g).injective.eq_iff.symm

/-- All original Lagrangians whose intersection with L₀ is exactly K,
with no completion or coordinate premise, have unique symmetric coordinates. -/
def lagrangianIntersectionFiberEquivSymmetricMatrices_add
    (L₀ : Lagrangian p (r+b))
    (K : Submodule (ZMod p) (PhaseSpace p (r+b))) (hK : K ≤ L₀.val)
    (hKr : finrank (ZMod p) K = b) :
    {L : Lagrangian p (r+b) // L.val ⊓ L₀.val = K} ≃
      SymmetricMatrices (Fin r) (ZMod p) :=
  (Equiv.subtypeEquiv
    (symplecticLagrangianEquiv
      (frameStandardization (shellReferenceFrame L₀ K hK hKr))
      (pairing_frameStandardization (shellReferenceFrame L₀ K hK hKr)))
    (shellReferenceFrame_intersection_iff L₀ K hK hKr)).trans
    standardShellFiberEquivSymmetricMatrices

theorem card_lagrangianIntersectionFiber_add
    (L₀ : Lagrangian p (r+b))
    (K : Submodule (ZMod p) (PhaseSpace p (r+b))) (hK : K ≤ L₀.val)
    (hKr : finrank (ZMod p) K = b) :
    Nat.card {L : Lagrangian p (r+b) // L.val ⊓ L₀.val = K} =
      p ^ (r * (r+1) / 2) := by
  rw [Nat.card_congr (lagrangianIntersectionFiberEquivSymmetricMatrices_add L₀ K hK hKr),
    Nat.card_eq_fintype_card, card_symmetricMatrices_prime]

/-- Exact graph coordinates for an arbitrary original intersection fibre.
The dimension assumptions include r=0 and n=0. -/
def lagrangianIntersectionFiberEquivSymmetricMatrices {n : ℕ}
    (L₀ : Lagrangian p n) (K : Submodule (ZMod p) (PhaseSpace p n))
    (hK : K ≤ L₀.val) (r : ℕ) (hr : r ≤ n)
    (hKr : finrank (ZMod p) K = n-r) :
    {L : Lagrangian p n // L.val ⊓ L₀.val = K} ≃
      SymmetricMatrices (Fin r) (ZMod p) := by
  apply Classical.choice
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hr
  exact ⟨lagrangianIntersectionFiberEquivSymmetricMatrices_add L₀ K hK (by simpa using hKr)⟩

/-- The original exact intersection-fibre formula, for every prime. -/
theorem card_lagrangianIntersectionFiber_eq {n : ℕ}
    (L₀ : Lagrangian p n) (K : Submodule (ZMod p) (PhaseSpace p n))
    (hK : K ≤ L₀.val) (r : ℕ) (hr : r ≤ n)
    (hKr : finrank (ZMod p) K = n-r) :
    Nat.card {L : Lagrangian p n // L.val ⊓ L₀.val = K} =
      p ^ (r * (r+1) / 2) := by
  rw [Nat.card_congr (lagrangianIntersectionFiberEquivSymmetricMatrices L₀ K hK r hr hKr),
    Nat.card_eq_fintype_card, card_symmetricMatrices_prime]

end StabilizerLearning.Quantum
