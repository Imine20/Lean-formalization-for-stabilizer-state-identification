import ExactCriticalCurve.Quantum.CSSQuotientGaussType
import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRealizability

/-! Genuine successors of ordinary odd defects, constructed through the full mod-four quotient. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic
variable {k r : ℕ}
set_option maxHeartbeats 3000000

/-- Every nonterminal odd defect extends by one, preserving the full quadratic condition. -/
theorem ordinaryDefect_succ_exists_of_odd
    (N : OrdinaryDefect k r) (hk : (k : ZMod 2)=1)
    (hstep : 1<k/2-r ∨ (k/2-r=1 ∧ (k%8=1 ∨ k%8=7))) :
    ∃ M : OrdinaryDefect k (r+1), N.val≤M.val := by
  let D := cssFlagQuotientGeometry N.val N.property.1
  let Q := D.evenHalfForm
  let q : QuadraticForm (ZMod 2) (ZMod 2) := 0
  have hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin :=
    cssQuotient_evenHalfForm_nondegenerate N.val N.property.1 hk
  have hd : finrank (ZMod 2) D.evenSpace=2*(k/2-r) := by
    simpa only [N.property.2.1] using cssQuotient_evenHalfForm_finrank N.val N.property.1 hk
  have hp : q.polarBilin=0 := by
    ext x y
    simp [q,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  have hr : binaryPolarRadical q=⊤ := by
    change LinearMap.ker q.polarBilin=⊤
    rw [hp,LinearMap.ker_zero]
  have hdim : finrank (ZMod 2) (ZMod 2)+finrank (ZMod 2) (binaryPolarRadical q)=2 := by
    rw [hr]
    norm_num
  have hg : binaryQuadraticGaussSum q=2 := by
    norm_num [binaryQuadraticGaussSum,q]
  have he : ∃ f : ZMod 2 →ₗ[ZMod 2] D.evenSpace,
      Function.Injective f ∧ ∀ a, Q (f a)=q a := by
    apply (exists_binaryQuadratic_embedding_iff q Q hQ).mpr
    rw [hdim,hd]
    refine ⟨by rcases hstep with h | ⟨h,_⟩ <;> omega,?_⟩
    rcases hstep with h | ⟨hm,hs⟩
    · exact Or.inl (by omega)
    · right; right
      rw [hg]
      have h := cssQuotient_evenHalfForm_gauss N.val N.property.1 hk
      simpa only [N.property.2.1,hm,if_pos hs,pow_one] using h
  obtain ⟨f,hf,hfq⟩ := he
  let F : ZMod 2 →ₗ[ZMod 2] CSSQuotient N.val := D.evenSpace.subtype.comp f
  let S := LinearMap.range F
  have hF : Function.Injective F := D.evenSpace.injective_subtype.comp hf
  have hSd : finrank (ZMod 2) S=1 := by
    change finrank (ZMod 2) (LinearMap.range F)=1
    rw [← (LinearEquiv.ofInjective F hF).finrank_eq]
    simp
  have hSs : D.IsSingular S := by
    rintro y ⟨a,rfl⟩
    have hz : D.halfValue (F a)=0 := by
      change D.evenHalfForm (f a)=0
      exact hfq a
    have hpar : D.parity (F a)=0 := (f a).property
    have hrec := D.halfValue_reconstruct (F a)
    simpa only [hz,hpar,bitLift_zero,mul_zero,zero_add] using hrec.symm
  let M := cssFlagPreimage N.val S
  have hM : IsDefect M := cssFlagPreimage_isDefect N.val N.property.1 S hSs
  have hMd : finrank (ZMod 2) M=r+1 := by
    change finrank (ZMod 2) (cssFlagPreimage N.val S)=r+1
    rw [cssFlagPreimage_finrank N.val N.property.1 S,hSd,N.property.2.1]
    omega
  have hMw : allOnes k∉M := by
    intro hw
    have hwS : D.wu∈S :=
      (mem_cssFlagPreimage_iff N.val S
        ⟨allOnes k,N.property.1.allOnes_mem_orthogonal⟩).mp hw
    obtain ⟨a,ha⟩ := hwS
    have hpar : D.parity D.wu=0 := by
      rw [← ha]
      exact (f a).property
    have hodd : D.parity D.wu=1 :=
      (cssFlagQuotientGeometry_parity_wu N.val N.property.1).trans hk
    exact (zero_ne_one : (0 : ZMod 2)≠1) (hpar.symm.trans hodd)
  exact ⟨⟨M,hM,hMd,hMw⟩,le_cssFlagPreimage N.val N.property.1 S⟩

end ExactCriticalCurve.Quantum
