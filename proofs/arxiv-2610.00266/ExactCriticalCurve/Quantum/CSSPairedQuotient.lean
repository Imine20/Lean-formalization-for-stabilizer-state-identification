import ExactCriticalCurve.Quantum.CSSOverlapPairing
import ExactCriticalCurve.Quantum.RelationNormalForm
import ExactCriticalCurve.Binary.StochasticRelationComposition

/-! # The canonical CSS quotient isometry of paired defects

Compose the actual relations T_M and T_N, identify their actual defects, and
transport the existing quotient normal form. The canonical graph is an exact
membership criterion, with the full mod-four quadratic refinement and Wu class.
-/
noncomputable section
open Classical
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- The actual composition T_M ∘ T_N, with output M and input N. -/
def cssDefectComposition
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M) :
    StochasticLagrangian k :=
  stochasticLagrangianComposition hM.stochasticLagrangian hN.stochasticLagrangian

/-- A middle point exists exactly when the endpoints differ by M+N. -/
theorem mem_cssDefectComposition
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (x y : BinaryVector k) :
    (x,y) ∈ (cssDefectComposition N M hN hM).carrier ↔
      x ∈ orthogonal M ∧ y ∈ orthogonal N ∧ x-y ∈ M ⊔ N := by
  change (x,y) ∈ relationComposition hM.stochasticLagrangian hN.stochasticLagrangian ↔ _
  rw [mem_relationComposition]
  constructor
  · rintro ⟨z, hm, hn⟩
    rcases (mem_defectRelation M (x,z)).mp hm with ⟨hx, _, hxz⟩
    rcases (mem_defectRelation N (z,y)).mp hn with ⟨_, hy, hzy⟩
    exact ⟨hx, hy, Submodule.mem_sup.mpr ⟨x-z,hxz,z-y,hzy,by abel⟩⟩
  · rintro ⟨hx, hy, hd⟩
    obtain ⟨m, hm, n, hn, he⟩ := Submodule.mem_sup.mp hd
    have hzy : x-m = y+n := by
      calc
        x-m = y+(x-y)-m := by abel
        _ = y+n := by rw [← he]; abel
    refine ⟨x-m, ?_, ?_⟩
    · exact ⟨hx, (orthogonal M).sub_mem hx (hM.le_orthogonal hm), by simpa using hm⟩
    · refine ⟨?_, hy, ?_⟩
      · rw [hzy]
        exact (orthogonal N).add_mem hy (hN.le_orthogonal hn)
      · rw [hzy]
        simpa using hn

/-- The exact output defect of the composed relation. -/
theorem cssDefectComposition_leftDefect
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M) :
    (cssDefectComposition N M hN hM).leftDefect = M ⊔ (N ⊓ orthogonal M) := by
  ext x
  rw [StochasticLagrangian.mem_leftDefect, mem_cssDefectComposition]
  simp only [Submodule.zero_mem, sub_zero, true_and]
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hs
    apply Submodule.mem_sup.mpr
    refine ⟨m, hm, n, ⟨hn, ?_⟩, rfl⟩
    have hh := (orthogonal M).sub_mem hx (hM.le_orthogonal hm)
    simpa only [add_sub_cancel_left] using hh
  · intro hs
    obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hs
    exact ⟨(orthogonal M).add_mem (hM.le_orthogonal hm) hn.2,
      Submodule.mem_sup.mpr ⟨m,hm,n,hn.1,rfl⟩⟩

/-- The exact input defect of the composed relation. -/
theorem cssDefectComposition_rightDefect
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M) :
    (cssDefectComposition N M hN hM).rightDefect = N ⊔ (M ⊓ orthogonal N) := by
  ext y
  rw [StochasticLagrangian.mem_rightDefect, mem_cssDefectComposition]
  simp only [Submodule.zero_mem, zero_sub, true_and, Submodule.neg_mem_iff]
  constructor
  · rintro ⟨hy, hs⟩
    obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hs
    apply Submodule.mem_sup.mpr
    refine ⟨n, hn, m, ⟨hm, ?_⟩, add_comm n m⟩
    have hh := (orthogonal N).sub_mem hy (hN.le_orthogonal hn)
    simpa only [add_sub_cancel_right] using hh
  · intro hs
    obtain ⟨n, hn, m, hm, rfl⟩ := Submodule.mem_sup.mp hs
    exact ⟨(orthogonal N).add_mem (hN.le_orthogonal hn) hm.2,
      Submodule.mem_sup.mpr ⟨m,hm.1,n,hn,add_comm m n⟩⟩

/-- Paired-kernel equalities reduce the composed defects to precisely M and N. -/
theorem cssDefectComposition_paired_defects
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M) :
    (cssDefectComposition N M hN hM).leftDefect = M ∧
      (cssDefectComposition N M hN hM).rightDefect = N := by
  rw [cssDefectComposition_leftDefect, cssDefectComposition_rightDefect, hNM, hMN]
  exact ⟨sup_eq_left.mpr inf_le_right, sup_eq_left.mpr inf_le_left⟩

/-- Existence with a fully specified graph, full quadratic refinement and Wu class. -/
theorem exists_cssPairedQuotientEquiv
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M) :
    ∃ e : CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient M,
      (∀ q, cssQuotientQuadratic M hM (e q) = cssQuotientQuadratic N hN q) ∧
      e (cssQuotientWu N hN) = cssQuotientWu M hM ∧
      (∀ (x : orthogonal M) (y : orthogonal N),
        e (Submodule.Quotient.mk y) = Submodule.Quotient.mk x ↔ x.val-y.val ∈ M ⊔ N) := by
  let T := cssDefectComposition N M hN hM
  obtain ⟨hL,hR⟩ := cssDefectComposition_paired_defects N M hN hM hNM hMN
  have transport (L R : Submodule (ZMod 2) (BinaryVector k))
      (hLd : IsDefect L) (hRd : IsDefect R)
      (hl : T.leftDefect = L) (hr : T.rightDefect = R) :
      ∃ e : CSSQuotient R ≃ₗ[ZMod 2] CSSQuotient L,
        (∀ q, cssQuotientQuadratic L hLd (e q) = cssQuotientQuadratic R hRd q) ∧
        e (cssQuotientWu R hRd) = cssQuotientWu L hLd ∧
        (∀ (x : orthogonal L) (y : orthogonal R),
          e (Submodule.Quotient.mk y) = Submodule.Quotient.mk x ↔ (x.val,y.val) ∈ T.carrier) := by
    subst L
    subst R
    exact ⟨relationQuotientEquiv T, relationQuotientEquiv_quadratic T,
      relationQuotientEquiv_wu T, fun x y => (mem_relation_iff_quotient T x y).symm⟩
  obtain ⟨e,hq,hw,hg⟩ := transport M N hM hN hL hR
  refine ⟨e,hq,hw,?_⟩
  intro x y
  rw [hg]
  exact (mem_cssDefectComposition N M hN hM x.val y.val).trans
    (and_iff_right x.property |>.trans (and_iff_right y.property))

/-- The canonical input-to-output quotient isometry characterized by the exact graph. -/
def cssPairedQuotientEquiv
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M) :
    CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient M :=
  Classical.choose (exists_cssPairedQuotientEquiv N M hN hM hNM hMN)

theorem cssPairedQuotientEquiv_quadratic
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M)
    (q : CSSQuotient N) :
    cssQuotientQuadratic M hM (cssPairedQuotientEquiv N M hN hM hNM hMN q) =
      cssQuotientQuadratic N hN q :=
  (Classical.choose_spec (exists_cssPairedQuotientEquiv N M hN hM hNM hMN)).1 q

theorem cssPairedQuotientEquiv_wu
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M) :
    cssPairedQuotientEquiv N M hN hM hNM hMN (cssQuotientWu N hN) = cssQuotientWu M hM :=
  (Classical.choose_spec (exists_cssPairedQuotientEquiv N M hN hM hNM hMN)).2.1

theorem cssPairedQuotientEquiv_graph
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M)
    (x : orthogonal M) (y : orthogonal N) :
    cssPairedQuotientEquiv N M hN hM hNM hMN (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk x ↔ x.val-y.val ∈ M ⊔ N :=
  (Classical.choose_spec (exists_cssPairedQuotientEquiv N M hN hM hNM hMN)).2.2 x y

end ExactCriticalCurve.Quantum
