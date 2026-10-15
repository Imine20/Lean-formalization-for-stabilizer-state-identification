import ExactCriticalCurve.Binary.StochasticWittExtension
import ExactCriticalCurve.FiniteQuadratic.QuadraticTupleOrbits

/-! Actual stochastic groups and their genuine fixed subspaces.
The even case keeps the distinguished Wu point in the full nondegenerate
half-quadratic space. The odd case splits off the actual Wu line. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Binary
open FiniteQuadratic Counting StochasticCounting
variable {k : ℕ}

theorem stochasticIsometry_parity_preserved (g : StochasticIsometryGroup k)
    (x : BinaryVector k) : weightParity k (g.val x)=weightParity k x := by
  change binaryDot (allOnes k) (g.val x)=binaryDot (allOnes k) x
  calc
    _ = binaryDot (g.val (allOnes k)) (g.val x) := by rw [stochasticIsometry_allOnes]
    _ = _ := stochasticIsometry_dot g _ _

theorem stochasticIsometry_half_preserved (g : StochasticIsometryGroup k)
    (x : BinaryVector k) : stochasticHalfForm k (g.val x)=stochasticHalfForm k x :=
  (weightQuadratic_eq_iff_half_parity _ _ (stochasticIsometry_parity_preserved g x)).mp
    (stochasticIsometry_weight g x)

/-- This is the actual point stabilizer inside the actual orthogonal group. -/
abbrev StochasticHalfWuStabilizer (k : ℕ) :=
  MulAction.stabilizer (BinaryQuadraticIsometryGroup (stochasticHalfForm k)) (allOnes k)

def stochasticToHalfWu (g : StochasticIsometryGroup k) : StochasticHalfWuStabilizer k :=
  ⟨⟨g.val,stochasticIsometry_half_preserved g⟩,g.property.2⟩

theorem halfWu_parity_preserved (hk : (k : ZMod 2)=0)
    (g : StochasticHalfWuStabilizer k) (x : BinaryVector k) :
    weightParity k (g.val.val x)=weightParity k x := by
  have hB (x y : BinaryVector k) :
      (stochasticHalfForm k).polarBilin (g.val.val x) (g.val.val y)=
        (stochasticHalfForm k).polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
    rw [← map_add,g.val.property,g.val.property,g.val.property]
  have hw : g.val.val (allOnes k)=allOnes k := g.property
  have h := hB (allOnes k) x
  rw [hw,stochasticHalfForm_polar,stochasticHalfBilinear_wu hk,
    stochasticHalfBilinear_wu hk] at h
  exact h

def halfWuToStochastic (hk : (k : ZMod 2)=0)
    (g : StochasticHalfWuStabilizer k) : StochasticIsometryGroup k :=
  ⟨g.val.val,fun x => (weightQuadratic_eq_iff_half_parity _ _
    (halfWu_parity_preserved hk g x)).mpr (g.val.property x),g.property⟩

/-- Full mod-four preservation is recovered, rather than assumed of O(Q). -/
def stochasticEvenOrthogonalEquiv (hk : (k : ZMod 2)=0) :
    StochasticIsometryGroup k ≃* StochasticHalfWuStabilizer k where
  toFun := stochasticToHalfWu
  invFun := halfWuToStochastic hk
  left_inv g := Subtype.ext rfl
  right_inv g := Subtype.ext (Subtype.ext rfl)
  map_mul' g h := Subtype.ext (Subtype.ext rfl)

@[simp] theorem stochasticEvenOrthogonalEquiv_apply (hk : (k : ZMod 2)=0)
    (g : StochasticIsometryGroup k) (x : BinaryVector k) :
    (stochasticEvenOrthogonalEquiv hk g).val.val x=g.val x := rfl

/-- The even transport leaves the actual fixed submodule unchanged. -/
theorem stochasticEven_fixedSubmodule (hk : (k : ZMod 2)=0)
    (g : StochasticIsometryGroup k) :
    fixedSubmodule (ZMod 2) (BinaryVector k) (stochasticEvenOrthogonalEquiv hk g)=
      fixedSubmodule (ZMod 2) (BinaryVector k) g := rfl

theorem stochasticEven_fixed_finrank (hk : (k : ZMod 2)=0)
    (g : StochasticIsometryGroup k) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k)
        (stochasticEvenOrthogonalEquiv hk g)) := rfl

/-- Explicit splitting by parity and correction along the actual Wu vector. -/
def oddWuSplit (hk : (k : ZMod 2)=1) :
    BinaryVector k ≃ₗ[ZMod 2] (evenWeightSpace k × ZMod 2) where
  toFun x := (oddWuCorrectionLinear hk x,weightParity k x)
  invFun z := z.1.val+z.2 • allOnes k
  left_inv x := oddWuCorrection_reconstruct hk x
  right_inv z := by
    rcases z with ⟨x,a⟩
    have hp : weightParity k (x.val+a • allOnes k)=a := by
      rw [map_add,map_smul,weightParity_wu,hk]
      rw [(mem_evenWeightSpace _).mp x.property]
      simp
    apply Prod.ext
    · apply Subtype.ext
      change (x.val+a • allOnes k)+weightParity k (x.val+a • allOnes k) • allOnes k=x.val
      rw [hp,add_assoc,← add_smul,binaryScalar_add_self,zero_smul,add_zero]
    · exact hp
  map_add' x y := Prod.ext (map_add (oddWuCorrectionLinear hk) x y)
    (map_add (weightParity k) x y)
  map_smul' a x := Prod.ext (map_smul (oddWuCorrectionLinear hk) a x)
    (map_smul (weightParity k) a x)

@[simp] theorem oddWuSplit_apply (hk : (k : ZMod 2)=1) (x : BinaryVector k) :
    oddWuSplit hk x=(oddWuCorrectionLinear hk x,weightParity k x) := rfl
@[simp] theorem oddWuSplit_symm_apply (hk : (k : ZMod 2)=1)
    (x : evenWeightSpace k) (a : ZMod 2) :
    (oddWuSplit hk).symm (x,a)=x.val+a • allOnes k := rfl

theorem oddWuSplit_even (hk : (k : ZMod 2)=1) (x : evenWeightSpace k) :
    oddWuSplit hk x.val=(x,0) := by
  apply Prod.ext
  · apply Subtype.ext
    change x.val+weightParity k x.val • allOnes k=x.val
    rw [(mem_evenWeightSpace _).mp x.property,zero_smul,add_zero]
  · exact (mem_evenWeightSpace _).mp x.property

theorem oddWuSplit_wu (hk : (k : ZMod 2)=1) :
    oddWuSplit hk (allOnes k)=(0,1) := by
  apply Prod.ext
  · apply Subtype.ext
    change allOnes k+weightParity k (allOnes k) • allOnes k=0
    rw [weightParity_wu,hk,one_smul]
    ext i
    exact binaryScalar_add_self _
  · exact (weightParity_wu k).trans hk

def stochasticEvenRestriction (g : StochasticIsometryGroup k) :
    evenWeightSpace k ≃ₗ[ZMod 2] evenWeightSpace k where
  toFun x := ⟨g.val x.val,by
    rw [mem_evenWeightSpace,stochasticIsometry_parity_preserved]
    exact (mem_evenWeightSpace _).mp x.property⟩
  invFun x := ⟨g.val.symm x.val,by
    have h := stochasticIsometry_parity_preserved g (g.val.symm x.val)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans ((mem_evenWeightSpace _).mp x.property)⟩
  left_inv x := Subtype.ext (g.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.val.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add g.val x.val y.val)
  map_smul' a x := Subtype.ext (map_smul g.val a x.val)

def stochasticToEvenOrthogonal (g : StochasticIsometryGroup k) :
    BinaryQuadraticIsometryGroup (evenWeightHalfForm k) :=
  ⟨stochasticEvenRestriction g,fun x => stochasticIsometry_half_preserved g x.val⟩

theorem even_add_wu_quadratic (x : evenWeightSpace k) (a : ZMod 2) :
    weightQuadratic (x.val+a • allOnes k)=weightQuadratic x.val+
      weightQuadratic (a • allOnes k) := by
  have hw : binaryDot x.val (allOnes k)=0 :=
    (binaryDot_comm _ _).trans ((mem_evenWeightSpace _).mp x.property)
  have h : binaryDot x.val (a • allOnes k)=0 := by
    change binaryDotForm k x.val (a • allOnes k)=0
    rw [map_smul]
    change a • binaryDot x.val (allOnes k)=0
    rw [hw,smul_zero]
  rw [weightQuadratic_add,h,bitLift_zero,mul_zero,add_zero]

def oddOrthogonalLinear (hk : (k : ZMod 2)=1)
    (h : BinaryQuadraticIsometryGroup (evenWeightHalfForm k)) :
    BinaryVector k ≃ₗ[ZMod 2] BinaryVector k :=
  ((oddWuSplit hk).trans (h.val.prodCongr (LinearEquiv.refl (ZMod 2) (ZMod 2)))).trans
    (oddWuSplit hk).symm

@[simp] theorem oddOrthogonalLinear_apply (hk : (k : ZMod 2)=1)
    (h : BinaryQuadraticIsometryGroup (evenWeightHalfForm k)) (x : BinaryVector k) :
    oddOrthogonalLinear hk h x=
      (h.val (oddWuCorrectionLinear hk x)).val+weightParity k x • allOnes k := rfl

theorem oddOrthogonalLinear_quadratic (hk : (k : ZMod 2)=1)
    (h : BinaryQuadraticIsometryGroup (evenWeightHalfForm k)) (x : BinaryVector k) :
    weightQuadratic (oddOrthogonalLinear hk h x)=weightQuadratic x := by
  have hq (y : evenWeightSpace k) : weightQuadratic (h.val y).val=weightQuadratic y.val := by
    apply (weightQuadratic_eq_iff_half_parity _ _ ?_).mpr (h.property y)
    change weightParity k (h.val y).val=weightParity k y.val
    rw [(mem_evenWeightSpace _).mp (h.val y).property,
      (mem_evenWeightSpace _).mp y.property]
  rw [oddOrthogonalLinear_apply,even_add_wu_quadratic,hq]
  rw [← even_add_wu_quadratic,oddWuCorrection_reconstruct]

theorem oddOrthogonalLinear_wu (hk : (k : ZMod 2)=1)
    (h : BinaryQuadraticIsometryGroup (evenWeightHalfForm k)) :
    oddOrthogonalLinear hk h (allOnes k)=allOnes k := by
  change (oddWuSplit hk).symm
    ((h.val.prodCongr (LinearEquiv.refl (ZMod 2) (ZMod 2))) (oddWuSplit hk (allOnes k)))=_
  rw [oddWuSplit_wu]
  simp

def oddOrthogonalToStochastic (hk : (k : ZMod 2)=1)
    (h : BinaryQuadraticIsometryGroup (evenWeightHalfForm k)) : StochasticIsometryGroup k :=
  ⟨oddOrthogonalLinear hk h,oddOrthogonalLinear_quadratic hk h,oddOrthogonalLinear_wu hk h⟩

/-- Actual full group equivalence; the inverse is the explicit Wu-line extension. -/
def stochasticOddOrthogonalEquiv (hk : (k : ZMod 2)=1) :
    StochasticIsometryGroup k ≃* BinaryQuadraticIsometryGroup (evenWeightHalfForm k) where
  toFun := stochasticToEvenOrthogonal
  invFun := oddOrthogonalToStochastic hk
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g.val (oddWuCorrectionLinear hk x).val+weightParity k x • allOnes k=g.val x
    calc
      _ = g.val ((oddWuCorrectionLinear hk x).val+weightParity k x • allOnes k) := by
        rw [map_add,map_smul,stochasticIsometry_allOnes]
      _ = _ := by rw [oddWuCorrection_reconstruct]
  right_inv h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change (h.val (oddWuCorrectionLinear hk x.val)).val+
      weightParity k x.val • allOnes k=(h.val x).val
    have hx := oddWuSplit_even hk x
    have hc : oddWuCorrectionLinear hk x.val=x := congrArg Prod.fst hx
    rw [hc,(mem_evenWeightSpace _).mp x.property,zero_smul,add_zero]
  map_mul' g h := Subtype.ext (LinearEquiv.ext (fun x => rfl))

/-- The genuine fixed space splits off precisely one fixed binary coordinate. -/
def stochasticOdd_fixedEquiv (hk : (k : ZMod 2)=1) (g : StochasticIsometryGroup k) :
    fixedSubmodule (ZMod 2) (BinaryVector k) g ≃ₗ[ZMod 2]
      (fixedSubmodule (ZMod 2) (evenWeightSpace k) (stochasticOddOrthogonalEquiv hk g) × ZMod 2) where
  toFun x := (⟨oddWuCorrectionLinear hk x.val,by
    apply Subtype.ext
    have hx : g.val x.val=x.val := x.property
    change g.val (x.val+weightParity k x.val • allOnes k)=
      x.val+weightParity k x.val • allOnes k
    rw [map_add,map_smul,hx,stochasticIsometry_allOnes]⟩,weightParity k x.val)
  invFun z := ⟨z.1.val.val+z.2 • allOnes k,by
    have hz : g.val z.1.val.val=z.1.val.val := congrArg Subtype.val z.1.property
    change g.val (z.1.val.val+z.2 • allOnes k)=_
    rw [map_add,map_smul,hz,stochasticIsometry_allOnes]⟩
  left_inv x := Subtype.ext (oddWuCorrection_reconstruct hk x.val)
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((oddWuSplit hk).apply_symm_apply (z.1.val,z.2))
    · exact congrArg (fun t : evenWeightSpace k × ZMod 2 => t.2)
        ((oddWuSplit hk).apply_symm_apply (z.1.val,z.2))
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_add (oddWuCorrectionLinear hk) x.val y.val
    · exact map_add (weightParity k) x.val y.val
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_smul (oddWuCorrectionLinear hk) a x.val
    · exact map_smul (weightParity k) a x.val

theorem stochasticOdd_fixed_finrank (hk : (k : ZMod 2)=1) (g : StochasticIsometryGroup k) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (evenWeightSpace k)
        (stochasticOddOrthogonalEquiv hk g))+1 := by
  rw [(stochasticOdd_fixedEquiv hk g).finrank_eq,Module.finrank_prod]
  simp

theorem evenWeightSpace_finrank_add_one (hk : (k : ZMod 2)=1) :
    finrank (ZMod 2) (evenWeightSpace k)+1=k := by
  have hp : weightParity k≠0 := by
    intro h
    have he := LinearMap.congr_fun h (allOnes k)
    rw [weightParity_wu,hk] at he
    exact one_ne_zero he
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hp
  simpa [evenWeightSpace,BinaryVector] using hd


section Enumerators
open scoped BigOperators
variable {R : Type*} [CommSemiring R]

/-- Transport of the actual finite fixed-space enumerator, at any scalar D. -/
theorem stochasticOdd_fixedSpace_sum (hk : (k : ZMod 2)=1) (D : R) :
    (∑ g : StochasticIsometryGroup k,
      D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) g)) =
    D * ∑ h : BinaryQuadraticIsometryGroup (evenWeightHalfForm k),
      D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (evenWeightSpace k) h) := by
  calc
    _ = ∑ g : StochasticIsometryGroup k,
        D * D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (evenWeightSpace k)
          (stochasticOddOrthogonalEquiv hk g)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [stochasticOdd_fixed_finrank hk,pow_succ,mul_comm]
    _ = D * ∑ g : StochasticIsometryGroup k,
        D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (evenWeightSpace k)
          (stochasticOddOrthogonalEquiv hk g)) := (Finset.mul_sum _ _ _).symm
    _ = _ := congrArg (fun x : R => D*x)
      ((stochasticOddOrthogonalEquiv hk).toEquiv.sum_comp (fun h =>
        D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (evenWeightSpace k) h)))

theorem stochasticEven_fixedSpace_sum (hk : (k : ZMod 2)=0) (D : R) :
    (∑ g : StochasticIsometryGroup k,
      D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) g)) =
    ∑ h : StochasticHalfWuStabilizer k,
      D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) h) := by
  exact (stochasticEvenOrthogonalEquiv hk).toEquiv.sum_comp (fun h =>
    D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) h))

end Enumerators
section Averages
open scoped BigOperators
variable {R : Type*} [Field R]

theorem stochasticOdd_fixedSpace_average (hk : (k : ZMod 2)=1) (D : R) :
    (∑ g : StochasticIsometryGroup k,
      D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) g)) /
        (Fintype.card (StochasticIsometryGroup k) : R) =
    D * ((∑ h : BinaryQuadraticIsometryGroup (evenWeightHalfForm k),
      D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (evenWeightSpace k) h)) /
        (Fintype.card (BinaryQuadraticIsometryGroup (evenWeightHalfForm k)) : R)) := by
  rw [stochasticOdd_fixedSpace_sum hk,
    Fintype.card_congr (stochasticOddOrthogonalEquiv hk).toEquiv,mul_div_assoc]

theorem stochasticEven_fixedSpace_average (hk : (k : ZMod 2)=0) (D : R) :
    (∑ g : StochasticIsometryGroup k,
      D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) g)) /
        (Fintype.card (StochasticIsometryGroup k) : R) =
    (∑ h : StochasticHalfWuStabilizer k,
      D ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector k) h)) /
        (Fintype.card (StochasticHalfWuStabilizer k) : R) := by
  rw [stochasticEven_fixedSpace_sum hk,
    Fintype.card_congr (stochasticEvenOrthogonalEquiv hk).toEquiv]

end Averages

theorem stochastic_zero_fixed_finrank (g : StochasticIsometryGroup 0) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector 0) g)=0 := by
  have h := (fixedSubmodule (ZMod 2) (BinaryVector 0) g).finrank_le
  simpa [BinaryVector] using h

theorem stochastic_one_fixed_finrank (g : StochasticIsometryGroup 1) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (BinaryVector 1) g)=1 := by
  have hi : finrank (ZMod 2) (evenWeightSpace 1)=0 := by
    have h := evenWeightSpace_finrank_add_one (k := 1) (by decide)
    omega
  have hz : finrank (ZMod 2) (fixedSubmodule (ZMod 2) (evenWeightSpace 1)
      (stochasticOddOrthogonalEquiv (by decide : (1 : ZMod 2)=1) g))=0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      _ ≤ finrank (ZMod 2) (evenWeightSpace 1) := Submodule.finrank_le _
      _ = 0 := hi
  calc
    _ = finrank (ZMod 2) (fixedSubmodule (ZMod 2) (evenWeightSpace 1)
        (stochasticOddOrthogonalEquiv (by decide : (1 : ZMod 2)=1) g))+1 :=
      stochasticOdd_fixed_finrank (by decide) g
    _ = 1 := by rw [hz]

end ExactCriticalCurve.Binary
