import ExactCriticalCurve.Binary.Geometry

/-! Full ordinary and exceptional defect index types, independent of quantum operators. -/
noncomputable section
namespace ExactCriticalCurve.Binary

abbrev OrdinaryDefect (k r : ℕ) :=
  {N : Submodule (ZMod 2) (BinaryVector k) //
    IsDefect N ∧ Module.finrank (ZMod 2) N = r ∧ allOnes k ∉ N}

abbrev ExceptionalDefect (k r : ℕ) :=
  {N : Submodule (ZMod 2) (BinaryVector k) //
    IsDefect N ∧ Module.finrank (ZMod 2) N = r ∧ allOnes k ∈ N}

instance finiteBinarySubmodule (k : ℕ) :
    Finite (Submodule (ZMod 2) (BinaryVector k)) :=
  Finite.of_injective (fun N : Submodule (ZMod 2) (BinaryVector k) =>
    (N : Set (BinaryVector k))) SetLike.coe_injective

noncomputable instance ordinaryDefectFintype (k r : ℕ) : Fintype (OrdinaryDefect k r) :=
  Fintype.ofFinite _
noncomputable instance exceptionalDefectFintype (k r : ℕ) : Fintype (ExceptionalDefect k r) :=
  Fintype.ofFinite _

end ExactCriticalCurve.Binary
