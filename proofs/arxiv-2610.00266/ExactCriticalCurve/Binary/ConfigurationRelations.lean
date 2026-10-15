import ExactCriticalCurve.Binary.StochasticCounting
import ExactCriticalCurve.Quantum.CSS
import ExactCriticalCurve.Quantum.PhaseAverage
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

noncomputable section
namespace ExactCriticalCurve.Binary.ConfigurationRelations
open scoped BigOperators
open Classical
open StochasticCounting ExactCriticalCurve.Quantum

def configurationColumn {n k : ℕ} (X Y : CopyConfig n k) (a : Fin n) : RelationSpace k :=
  (fun i => X i a, fun i => Y i a)

def configurationRelationSpace {n k : ℕ} (X Y : CopyConfig n k) :
    Submodule (ZMod 2) (RelationSpace k) :=
  Submodule.span (ZMod 2) (insert (relationWu k) (Set.range (configurationColumn X Y)))

def configurationSupport {n k : ℕ} (X Y : CopyConfig n k) :
    AffineSubspace (ZMod 2) (BinaryVector n) :=
  affineSpan (ZMod 2) (Set.range X ∪ Set.range Y)

theorem wu_mem_configurationRelationSpace {n k : ℕ} (X Y : CopyConfig n k) :
    relationWu k∈configurationRelationSpace X Y :=
  Submodule.subset_span (Set.mem_insert _ _)

theorem column_mem_configurationRelationSpace {n k : ℕ} (X Y : CopyConfig n k) (a : Fin n) :
    configurationColumn X Y a∈configurationRelationSpace X Y :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨a,rfl⟩)

theorem configurationRelationSpace_le_iff {n k : ℕ} (X Y : CopyConfig n k)
    (T : Submodule (ZMod 2) (RelationSpace k)) :
    configurationRelationSpace X Y≤T ↔ relationWu k∈T ∧ ∀ a, configurationColumn X Y a∈T := by
  rw [configurationRelationSpace, Submodule.span_le]
  constructor
  · intro h
    exact ⟨h (Set.mem_insert _ _), fun a => h (Set.mem_insert_of_mem _ ⟨a,rfl⟩)⟩
  · rintro ⟨hc, hcol⟩ _ (rfl | ⟨a,rfl⟩)
    · exact hc
    · exact hcol a

theorem configurationSupport_nonempty {n k : ℕ} (hk : 1≤k) (X Y : CopyConfig n k) :
    Nonempty (configurationSupport X Y) :=
  ⟨⟨X ⟨0,by omega⟩, subset_affineSpan (ZMod 2) _ (Or.inl ⟨_,rfl⟩)⟩⟩

theorem relationOperator_configuration_entry {n k : ℕ} (X Y : CopyConfig n k)
    (T : StochasticLagrangian k) :
    relationOperator n T.carrier (copyColumnsEquiv n k X) (copyColumnsEquiv n k Y) =
      if configurationRelationSpace X Y≤T.carrier then 1 else 0 := by
  classical
  simp only [relationOperator, matrixTensorPower_apply, relationMatrix, Fintype.prod_boole]
  have he : (∀ a : Fin n, (copyColumnsEquiv n k X a,copyColumnsEquiv n k Y a)∈T.carrier) ↔
      configurationRelationSpace X Y≤T.carrier := by
    rw [configurationRelationSpace_le_iff]
    exact ⟨fun h => ⟨T.allOnes_mem,h⟩, fun h => h.2⟩
  simp only [he]

theorem relationOperator_configuration_sum_card {n k : ℕ} (X Y : CopyConfig n k) :
    (∑ T : StochasticLagrangian k,
      relationOperator n T.carrier (copyColumnsEquiv n k X) (copyColumnsEquiv n k Y)) =
      (Nat.card {T : StochasticLagrangian k // configurationRelationSpace X Y≤T.carrier} : ℂ) := by
  classical
  simp only [relationOperator_configuration_entry]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

section AffineCone

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def affineCone (s : Set V) : Submodule K (K×V) :=
  Submodule.span K ((fun x : V => ((1 : K),x)) '' s)

def affineConeParameterization (p : V) (D : Submodule K V) : K×D →ₗ[K] K×V where
  toFun z := (z.1,z.1 • p + z.2.val)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
      abel
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, smul_smul,
        smul_eq_mul, RingHom.id_apply]

theorem affineConeParameterization_injective (p : V) (D : Submodule K V) :
    Function.Injective (affineConeParameterization p D) := by
  intro x y h
  change (x.1,x.1 • p + x.2.val)=(y.1,y.1 • p + y.2.val) at h
  have hfst : x.1=y.1 := congrArg (fun z : K×V => z.1) h
  have hsnd : x.1 • p + x.2.val=y.1 • p + y.2.val := congrArg (fun z : K×V => z.2) h
  rw [hfst] at hsnd
  exact Prod.ext hfst (Subtype.ext (add_left_cancel hsnd))

theorem affineCone_direction_mem {s : Set V} {p : V} (hp : p∈s)
    {d : V} (hd : d∈(affineSpan K s).direction) : ((0 : K),d)∈affineCone s := by
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right K hp] at hd
  induction hd using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y,hy,rfl⟩ := hx
    have hyc : ((1 : K),y)∈affineCone s := Submodule.subset_span ⟨y,hy,rfl⟩
    have hpc : ((1 : K),p)∈affineCone s := Submodule.subset_span ⟨p,hp,rfl⟩
    have h := (affineCone (K := K) s).sub_mem hyc hpc
    simpa using h
  | zero => exact (affineCone (K := K) s).zero_mem
  | add x y hx hy ihx ihy =>
    have h := (affineCone (K := K) s).add_mem ihx ihy
    simpa using h
  | smul a x hx ih =>
    have h := (affineCone (K := K) s).smul_mem a ih
    simpa using h

theorem affineCone_eq_range {s : Set V} {p : V} (hp : p∈s) :
    affineCone s=LinearMap.range (affineConeParameterization p (affineSpan K s).direction) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    have hd : x-p∈(affineSpan K s).direction :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan K s hx) (subset_affineSpan K s hp)
    refine ⟨(1,⟨x-p,hd⟩),?_⟩
    apply Prod.ext
    · rfl
    · change (1 : K) • p + (x-p)=x
      simp [sub_eq_add_neg]
  · rintro _ ⟨z,rfl⟩
    have hpc : ((1 : K),p)∈affineCone s := Submodule.subset_span ⟨p,hp,rfl⟩
    have h₁ := (affineCone (K := K) s).smul_mem z.1 hpc
    have h₂ := affineCone_direction_mem hp z.2.property
    have h := (affineCone (K := K) s).add_mem h₁ h₂
    simpa [affineConeParameterization] using h

theorem finrank_affineCone [FiniteDimensional K V] {s : Set V} (hs : s.Nonempty) :
    Module.finrank K (affineCone (K := K) s)=Module.finrank K (affineSpan K s).direction+1 := by
  obtain ⟨p,hp⟩ := hs
  rw [affineCone_eq_range hp, LinearMap.finrank_range_of_inj
    (affineConeParameterization_injective p _), Module.finrank_prod, Module.finrank_self]
  omega

end AffineCone


/-- The constant column is retained alongside every physical coordinate column. -/
def configurationMatrix {n k : ℕ} (X Y : CopyConfig n k) :
    Matrix (Fin k ⊕ Fin k) (Option (Fin n)) (ZMod 2) :=
  fun i a => match a with
  | none => 1
  | some j => Sum.elim (fun i => X i j) (fun i => Y i j) i

def configurationColumnEquiv (k : ℕ) :
    (Fin k ⊕ Fin k → ZMod 2) ≃ₗ[ZMod 2] RelationSpace k :=
  LinearEquiv.sumArrowLequivProdArrow _ _ _ _

def configurationRowEquiv (n : ℕ) :
    (Option (Fin n) → ZMod 2) ≃ₗ[ZMod 2] (ZMod 2) × BinaryVector n :=
  LinearEquiv.piOptionEquivProd (ZMod 2)

theorem map_configurationColumn_span {n k : ℕ} (X Y : CopyConfig n k) :
    (Submodule.span (ZMod 2) (Set.range (configurationMatrix X Y).col)).map
      (configurationColumnEquiv k).toLinearMap = configurationRelationSpace X Y := by
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_,⟨a,rfl⟩,rfl⟩
    cases a with
    | none => exact Set.mem_insert _ _
    | some a => exact Set.mem_insert_of_mem _ ⟨a,rfl⟩
  · rintro (rfl | ⟨a,rfl⟩)
    · exact ⟨_,⟨none,rfl⟩,rfl⟩
    · exact ⟨_,⟨some a,rfl⟩,rfl⟩

theorem map_configurationRow_span {n k : ℕ} (X Y : CopyConfig n k) :
    (Submodule.span (ZMod 2) (Set.range (configurationMatrix X Y).row)).map
      (configurationRowEquiv n).toLinearMap =
      affineCone (K := ZMod 2) (Set.range X ∪ Set.range Y) := by
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    cases i with
    | inl i => exact ⟨X i,Or.inl ⟨i,rfl⟩,rfl⟩
    | inr i => exact ⟨Y i,Or.inr ⟨i,rfl⟩,rfl⟩
  · rintro ⟨x,(⟨i,rfl⟩ | ⟨i,rfl⟩),rfl⟩
    · exact ⟨_,⟨Sum.inl i,rfl⟩,rfl⟩
    · exact ⟨_,⟨Sum.inr i,rfl⟩,rfl⟩

theorem finrank_configurationRelationSpace {n k : ℕ} (hk : 1≤k) (X Y : CopyConfig n k) :
    Module.finrank (ZMod 2) (configurationRelationSpace X Y) =
      Module.finrank (ZMod 2) (configurationSupport X Y).direction + 1 := by
  calc
    _ = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range (configurationMatrix X Y).col)) := by
      rw [← map_configurationColumn_span X Y]
      exact (configurationColumnEquiv k).finrank_map_eq _
    _ = (configurationMatrix X Y).rank := (Matrix.rank_eq_finrank_span_cols _).symm
    _ = Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range (configurationMatrix X Y).row)) :=
      Matrix.rank_eq_finrank_span_row _
    _ = Module.finrank (ZMod 2) (affineCone (K := ZMod 2) (Set.range X ∪ Set.range Y)) := by
      rw [← map_configurationRow_span X Y]
      exact ((configurationRowEquiv n).finrank_map_eq _).symm
    _ = _ := finrank_affineCone ⟨X ⟨0,by omega⟩,Or.inl ⟨_,rfl⟩⟩


theorem binary_sub_eq_add (a b : ZMod 2) : a-b=a+b := by
  fin_cases a <;> fin_cases b <;> decide

theorem relationQuadratic_configurationColumn {n k : ℕ} (X Y : CopyConfig n k) (a : Fin n) :
    relationQuadratic (configurationColumn X Y a)=phaseLinearStatistic X Y a := rfl

theorem relationBilinear_configurationPair {n k : ℕ} (X Y : CopyConfig n k)
    (p : PhasePair n) :
    relationBilinear k (configurationColumn X Y p.val.1) (configurationColumn X Y p.val.2) =
      phasePairStatistic X Y p := by
  simp only [relationBilinear_apply, configurationColumn, binaryDot,
    phasePairStatistic, binary_sub_eq_add]

theorem relationBilinear_self_zero_of_quadratic_zero {k : ℕ} (x : RelationSpace k)
    (hx : relationQuadratic x=0) : relationBilinear k x x=0 := by
  apply (two_mul_bitLift_eq_zero_iff _).mp
  have he := relationQuadratic_add x x
  simpa [relation_add_self, hx] using he.symm

theorem relationQuadratic_zero_on_span {k : ℕ} (S : Set (RelationSpace k))
    (hQ : ∀ x∈S, relationQuadratic x=0)
    (hB : ∀ x∈S, ∀ y∈S, relationBilinear k x y=0) :
    ∀ x∈Submodule.span (ZMod 2) S, relationQuadratic x=0 := by
  have hB₁ : ∀ x∈S, ∀ y∈Submodule.span (ZMod 2) S, relationBilinear k x y=0 := by
    intro x hx
    have hle : Submodule.span (ZMod 2) S ≤ LinearMap.ker (relationBilinear k x) :=
      Submodule.span_le.mpr (fun y hy => hB x hx y hy)
    exact fun y hy => hle hy
  have hB₂ : ∀ x∈Submodule.span (ZMod 2) S,
      ∀ y∈Submodule.span (ZMod 2) S, relationBilinear k x y=0 := by
    intro x hx y hy
    have hle : Submodule.span (ZMod 2) S ≤ LinearMap.ker (relationBilinear k y) := by
      apply Submodule.span_le.mpr
      intro z hz
      change relationBilinear k y z=0
      rw [(relationBilinear_isSymm k).eq]
      exact hB₁ z hz y hy
    rw [(relationBilinear_isSymm k).eq]
    exact hle hx
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hQ x hx
  | zero => exact relationQuadratic_zero k
  | add x y hx hy ihx ihy =>
    rw [relationQuadratic_add, ihx, ihy, hB₂ x hx y hy, bitLift_zero]
    simp
  | smul a x hx ih =>
    fin_cases a <;> simpa using ih

theorem phaseStatisticsVanish_iff_relationQuadratic_zero {n k : ℕ}
    (X Y : CopyConfig n k) :
    phaseStatisticsVanish X Y ↔
      ∀ x∈configurationRelationSpace X Y, relationQuadratic x=0 := by
  constructor
  · rintro ⟨hLinear,hPair⟩
    have hQcol : ∀ a, relationQuadratic (configurationColumn X Y a)=0 := hLinear
    have hdiag : ∀ a, relationBilinear k (configurationColumn X Y a)
        (configurationColumn X Y a)=0 :=
      fun a => relationBilinear_self_zero_of_quadratic_zero _ (hQcol a)
    have hcol : ∀ a b, relationBilinear k (configurationColumn X Y a)
        (configurationColumn X Y b)=0 := by
      intro a b
      rcases lt_trichotomy a b with hab | rfl | hba
      · exact (relationBilinear_configurationPair X Y ⟨(a,b),hab⟩).trans (hPair _)
      · exact hdiag a
      · rw [(relationBilinear_isSymm k).eq]
        exact (relationBilinear_configurationPair X Y ⟨(b,a),hba⟩).trans (hPair _)
    apply relationQuadratic_zero_on_span
    · rintro x (rfl | ⟨a,rfl⟩)
      · exact relationQuadratic_wu k
      · exact hQcol a
    · rintro x (rfl | ⟨a,rfl⟩) y (rfl | ⟨b,rfl⟩)
      · exact relationBilinear_wu_wu k
      · rw [(relationBilinear_isSymm k).eq, ← relationBilinear_self]
        exact hdiag b
      · rw [← relationBilinear_self]
        exact hdiag a
      · exact hcol a b
  · intro h
    constructor
    · intro a
      exact h _ (column_mem_configurationRelationSpace X Y a)
    · intro p
      rw [← relationBilinear_configurationPair]
      exact relationQuadratic_zero_pairwise h
        (column_mem_configurationRelationSpace X Y _) (column_mem_configurationRelationSpace X Y _)


/-- Every ambient linear image column is a combination of the genuine input columns. -/
theorem binaryVector_sum_smul_single {m : ℕ} (x : BinaryVector m) :
    (∑ j : Fin m, x j • (Pi.single j 1 : BinaryVector m))=x := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem binaryLinearMap_apply_eq_sum {m n : ℕ}
    (f : BinaryVector m →ₗ[ZMod 2] BinaryVector n) (x : BinaryVector m) (a : Fin n) :
    f x a = ∑ j : Fin m, x j * f (Pi.single j 1) a := by
  have h := congrArg (fun x => f x a) (binaryVector_sum_smul_single x)
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm

theorem configurationColumn_affine {m n k : ℕ} (a : BinaryVector n)
    (f : BinaryVector m →ₗ[ZMod 2] BinaryVector n) (X Y : CopyConfig m k) (t : Fin n) :
    configurationColumn (fun i => a+f (X i)) (fun i => a+f (Y i)) t =
      (a t) • relationWu k +
        ∑ j : Fin m, f (Pi.single j 1) t • configurationColumn X Y j := by
  ext i <;>
    simp only [configurationColumn, relationWu, allOnes, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_one, Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]
  all_goals
    rw [binaryLinearMap_apply_eq_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _

theorem configurationRelationSpace_affine_le {m n k : ℕ} (a : BinaryVector n)
    (f : BinaryVector m →ₗ[ZMod 2] BinaryVector n) (X Y : CopyConfig m k) :
    configurationRelationSpace (fun i => a+f (X i)) (fun i => a+f (Y i)) ≤
      configurationRelationSpace X Y := by
  apply (configurationRelationSpace_le_iff _ _ _).mpr
  refine ⟨wu_mem_configurationRelationSpace X Y,?_⟩
  intro t
  rw [configurationColumn_affine]
  exact (configurationRelationSpace X Y).add_mem
    ((configurationRelationSpace X Y).smul_mem _ (wu_mem_configurationRelationSpace X Y))
    ((configurationRelationSpace X Y).sum_mem (fun j _ =>
      (configurationRelationSpace X Y).smul_mem _ (column_mem_configurationRelationSpace X Y j)))

/-- Injective affine changes of coordinates preserve the full generated relation space. -/
theorem configurationRelationSpace_affine_eq {m n k : ℕ} (a : BinaryVector n)
    (f : BinaryVector m →ₗ[ZMod 2] BinaryVector n) (hf : Function.Injective f)
    (X Y : CopyConfig m k) :
    configurationRelationSpace (fun i => a+f (X i)) (fun i => a+f (Y i)) =
      configurationRelationSpace X Y := by
  apply le_antisymm (configurationRelationSpace_affine_le a f X Y)
  obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  have hinv (x : BinaryVector m) : -g a + g (a+f x)=x := by
    have hgf : g (f x)=x := LinearMap.congr_fun hg x
    simp [map_add, hgf]
  have h := configurationRelationSpace_affine_le (-g a) g
    (fun i => a+f (X i)) (fun i => a+f (Y i))
  simpa only [hinv] using h

/-- The chart may have any dimension; no full ambient support hypothesis is required. -/
theorem configurationRelationSpace_basis_chart {m n k : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) (b : Module.Basis (Fin m) (ZMod 2) L)
    (a : BinaryVector n) (X Y : CopyConfig m k) :
    configurationRelationSpace (fun i => a+(b.equivFun.symm (X i)).val)
      (fun i => a+(b.equivFun.symm (Y i)).val) = configurationRelationSpace X Y := by
  let f : BinaryVector m →ₗ[ZMod 2] BinaryVector n :=
    L.subtype.comp b.equivFun.symm.toLinearMap
  have hf : Function.Injective f := L.injective_subtype.comp b.equivFun.symm.injective
  exact configurationRelationSpace_affine_eq a f hf X Y

theorem phaseStatisticsVanish_basis_chart {m n k : ℕ}
    (L : Submodule (ZMod 2) (BinaryVector n)) (b : Module.Basis (Fin m) (ZMod 2) L)
    (a : BinaryVector n) (X Y : CopyConfig m k) :
    phaseStatisticsVanish (fun i => a+(b.equivFun.symm (X i)).val)
      (fun i => a+(b.equivFun.symm (Y i)).val) ↔ phaseStatisticsVanish X Y := by
  rw [phaseStatisticsVanish_iff_relationQuadratic_zero,
    phaseStatisticsVanish_iff_relationQuadratic_zero,
    configurationRelationSpace_basis_chart]

end ExactCriticalCurve.Binary.ConfigurationRelations
