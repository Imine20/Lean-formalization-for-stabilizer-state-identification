import ExactCriticalCurve.Quantum.CSSPairedQuotient
import ExactCriticalCurve.Quantum.CSSQuotientLift
import ExactCriticalCurve.Quantum.ParabolicKernel

/-! # Actual ambient lifts of the canonical paired CSS quotient map

The fiber contains all ambient stochastic isometries sending N to M and having
nonzero full-support overlap. It is precisely the fiber inducing the canonical
quotient map, and multiplication by an actual lift identifies it with the
existing actual parabolic kernel. No fiber cardinality is assumed.
-/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- The full actual ambient overlap fiber for a fixed target defect. -/
def ActualCSSOverlapFiber (N M : Submodule (ZMod 2) (BinaryVector k)) :=
  {g : StochasticIsometryGroup k // stochasticSubspace g N = M ∧
    ∀ x ∈ orthogonal N, g.val x-x ∈ N ⊔ M}

/-- For a fixed target defect, overlap is equivalent to inducing the canonical map. -/
theorem cssOverlap_iff_canonical_lift
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M)
    (g : StochasticIsometryGroup k) (hg : stochasticSubspace g N = M) :
    (∀ x ∈ orthogonal N, g.val x-x ∈ N ⊔ M) ↔
      ∀ x : orthogonal N, ∃ hx : g.val x.val ∈ orthogonal M,
        cssPairedQuotientEquiv N M hN hM hNM hMN (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk (⟨g.val x.val,hx⟩ : orthogonal M) := by
  constructor
  · intro h x
    have hx : g.val x.val ∈ orthogonal M := by
      rw [← hg, stochasticSubspace_orthogonal]
      exact ⟨x.val,x.property,rfl⟩
    refine ⟨hx, (cssPairedQuotientEquiv_graph N M hN hM hNM hMN _ x).mpr ?_⟩
    simpa only [sup_comm] using h x.val x.property
  · intro h x hx
    obtain ⟨hy,he⟩ := h ⟨x,hx⟩
    have hd := (cssPairedQuotientEquiv_graph N M hN hM hNM hMN
      ⟨g.val x,hy⟩ ⟨x,hx⟩).mp he
    simpa only [sup_comm] using hd

/-- Every paired canonical quotient map has an actual ambient full-q/Wu lift. -/
theorem actualCSSOverlapFiber_nonempty
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M) :
    Nonempty (ActualCSSOverlapFiber N M) := by
  let e := cssPairedQuotientEquiv N M hN hM hNM hMN
  have hq := cssPairedQuotientEquiv_quadratic N M hN hM hNM hMN
  have hw := cssPairedQuotientEquiv_wu N M hN hM hNM hMN
  let f := cssQuotientLift N M hN hM e hq hw
  obtain ⟨g,hg⟩ := stochastic_witt_extension (orthogonal N) (orthogonal M) f
    (cssQuotientLift_quadratic N M hN hM e hq hw)
    (iff_of_true hN.allOnes_mem_orthogonal hM.allOnes_mem_orthogonal)
    (fun _ => congrArg Subtype.val (cssQuotientLift_wu N M hN hM e hq hw))
  have hdim : finrank (ZMod 2) N = finrank (ZMod 2) M := by
    have he := e.finrank_eq
    have hn := cssQuotient_finrank_add N hN
    have hm := cssQuotient_finrank_add M hM
    omega
  have hmap : stochasticSubspace g N = M := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro y ⟨x,hx,rfl⟩
      change g.val x ∈ M
      rw [hg ⟨x,hN.le_orthogonal hx⟩]
      exact (cssQuotientLift_mem_defect_iff N M hN hM e hq hw
        ⟨x,hN.le_orthogonal hx⟩).mpr hx
    · rw [stochasticSubspace_finrank, hdim]
  refine ⟨⟨g,hmap,?_⟩⟩
  intro x hx
  have he := cssQuotientLift_mk N M hN hM e hq hw (⟨x,hx⟩ : orthogonal N)
  have hd := (cssPairedQuotientEquiv_graph N M hN hM hNM hMN
    (f ⟨x,hx⟩) ⟨x,hx⟩).mp he.symm
  rw [hg ⟨x,hx⟩]
  simpa only [sup_comm] using hd

/-- Any two actual lifts differ on N-perp by an element of the target defect. -/
theorem actualCSSOverlapFiber_difference_mem
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M)
    (g₀ g : ActualCSSOverlapFiber N M) (x : orthogonal N) :
    g.val.val x.val - g₀.val.val x.val ∈ M := by
  have horth (f : ActualCSSOverlapFiber N M) : f.val.val x.val ∈ orthogonal M := by
    apply (show orthogonal (stochasticSubspace f.val N) ≤ orthogonal M from
      le_of_eq (congrArg orthogonal f.property.1))
    rw [stochasticSubspace_orthogonal]
    exact ⟨x.val,x.property,rfl⟩
  have hd := (N ⊔ M).sub_mem (g.property.2 x.val x.property)
    (g₀.property.2 x.val x.property)
  have hd' : g.val.val x.val-g₀.val.val x.val ∈ N ⊔ M := by
    convert hd using 1 <;> abel
  obtain ⟨n,hn,m,hm,he⟩ := Submodule.mem_sup.mp hd'
  have hdiff := (orthogonal M).sub_mem (horth g) (horth g₀)
  have hnorth : n ∈ orthogonal M := by
    have hh := (orthogonal M).sub_mem hdiff (hM.le_orthogonal hm)
    rw [← he] at hh
    simpa only [add_sub_cancel_right] using hh
  have hnM : n ∈ M := ((show N ⊓ orthogonal M ≤ N ⊓ M from le_of_eq hNM)
    ⟨hn,hnorth⟩).2
  rw [← he]
  exact M.add_mem hnM hm

/-- An explicit bijection with the existing ambient kernel, using right multiplication. -/
def actualCSSOverlapFiberEquiv
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (g₀ : ActualCSSOverlapFiber N M) :
    stochasticParabolicKernel N ≃ ActualCSSOverlapFiber N M where
  toFun h := ⟨g₀.val*h.val, by
    constructor
    · rw [stochasticSubspace_mul, h.property.1, g₀.property.1]
    · intro x hx
      have ht : g₀.val.val (h.val.val x-x) ∈ M := by
        exact (show stochasticSubspace g₀.val N ≤ M from le_of_eq g₀.property.1)
          ⟨h.val.val x-x,h.property.2 ⟨x,hx⟩,rfl⟩
      have hs := (N ⊔ M).add_mem
        ((show M ≤ N ⊔ M from le_sup_right) ht) (g₀.property.2 x hx)
      change g₀.val.val (h.val.val x)-x ∈ N ⊔ M
      simpa only [map_sub, sub_add_sub_cancel] using hs⟩
  invFun g := ⟨g₀.val⁻¹*g.val, by
    constructor
    · calc
        stochasticSubspace (g₀.val⁻¹*g.val) N =
            stochasticSubspace g₀.val⁻¹ (stochasticSubspace g.val N) :=
          stochasticSubspace_mul _ _ _
        _ = stochasticSubspace g₀.val⁻¹ (stochasticSubspace g₀.val N) :=
          congrArg (stochasticSubspace g₀.val⁻¹) (g.property.1.trans g₀.property.1.symm)
        _ = N := Binary.stochasticSubspace_inv_cancel g₀.val N
    · intro x
      have hd := actualCSSOverlapFiber_difference_mem N M hM hNM g₀ g x
      have hp : g.val.val x.val-g₀.val.val x.val ∈ stochasticSubspace g₀.val N := by
        rw [g₀.property.1]
        exact hd
      have hh := (mem_stochasticSubspace g₀.val N _).mp hp
      change g₀.val.val.symm (g.val.val x.val)-x.val ∈ N
      simpa only [map_sub, LinearEquiv.symm_apply_apply] using hh⟩
  left_inv h := by
    apply Subtype.ext
    change g₀.val⁻¹*(g₀.val*h.val)=h.val
    simp [mul_assoc]
  right_inv g := by
    apply Subtype.ext
    change g₀.val*(g₀.val⁻¹*g.val)=g.val
    simp [mul_assoc]

/-- The complete actual canonical lift fiber has exactly the actual kernel cardinality. -/
theorem actualCSSOverlapFiber_card
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (hNM : N ⊓ orthogonal M = N ⊓ M) (hMN : M ⊓ orthogonal N = N ⊓ M) :
    Nat.card (ActualCSSOverlapFiber N M) = Nat.card (stochasticParabolicKernel N) := by
  obtain ⟨g₀⟩ := actualCSSOverlapFiber_nonempty N M hN hM hNM hMN
  exact (Nat.card_congr (actualCSSOverlapFiberEquiv N M hM hNM g₀)).symm

end ExactCriticalCurve.Quantum
