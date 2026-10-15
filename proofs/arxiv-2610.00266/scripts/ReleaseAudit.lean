import ExactCriticalCurve
import Lean.Util.CollectAxioms
import Lean.Elab.Command

import Lean.Meta

noncomputable section
open Classical Module Filter Matrix
open scoped BigOperators Topology
set_option maxHeartbeats 20000000

/- Independent literal expected types are copied from separately reviewed audit inputs.
   Each public main constant AND its original proof body is checked by the kernel.
   Definition guards retain the numerical products, sums and sector formulas. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for name in #[`ExactCriticalCurve.finiteSpectrum,
      `ExactCriticalCurve.criticalCurve, `ExactCriticalCurve.criticalCurveTails] do
    match env.find? name with
    | some (.thmInfo _) =>
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Forbidden main-theorem axiom {ax}"
    | _ => throwError "MAIN_RELEASE_BLOCKED: required paper theorem {name} is absent"

namespace FiniteSpectrumIndependentKernel
open Lean Elab Command Meta in
def auditExactTheorem (actual expected : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? actual with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Expected a theorem declaration: {actual}"
  liftTermElabM do
    let actualInfo ← getConstInfo actual
    let expectedInfo ← getConstInfo expected
    unless actualInfo.levelParams.length == expectedInfo.levelParams.length do
      throwError "Universe generality mismatch: {actual}"
    let levelParams := (List.range actualInfo.levelParams.length).map
      (fun i => Name.mkSimple ("auditUniverse" ++ toString i))
    let levels := levelParams.map Level.param
    let term := mkConst actual levels
    let expectedTerm := mkConst expected levels
    let expectedType ← inferType expectedTerm
    -- Abstract all universe-polymorphic typeclass and index parameters on expected definitions.
    let expectedValue ← forallTelescope expectedType fun args _ => do
      let body := mkAppN expectedTerm args
      mkForallFVars args body
    unless ← isDefEq (← inferType term) expectedValue do
      throwError "Exact theorem type mismatch: {actual}\nactual: {← inferType term}\nexpected: {expectedValue}"
    -- Check both the theorem constant and its original proof body directly in
    -- the kernel against the independently constructed expected type.
    -- addDeclCore has no skipKernelTC option and returns synchronously.
    let kernelEnv := (← getEnv).toKernelEnv
    let heartbeatLimit := (Core.getMaxHeartbeats (← getOptions)).toUSize
    for (label, proof) in #[
        ("constant", term),
        ("body", actualInfo.instantiateValueLevelParams! levels)] do
      let witnessName ← mkFreshUserName (Name.mkSimple ("kernelAudit_" ++ label))
      let decl : Declaration := .thmDecl {
        name := witnessName
        levelParams := levelParams
        type := expectedValue
        value := proof
      }
      let _ ← ofExceptKernelException <|
        Kernel.Environment.addDeclCore kernelEnv heartbeatLimit decl none
      logInfo m!"KERNEL_EXPECTED_TYPE_OK {label} {actual}"
  let axioms ← collectAxioms actual
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Forbidden transitive axiom {ax} in {actual}"
  logInfo m!"EXACT_TYPE_AND_AXIOMS_OK {actual}"

open Lean Elab Command Meta in
def auditExactDefinition (actual expected : Name) : CommandElabM Unit := do
  liftTermElabM do
    let actualInfo ← getConstInfo actual
    unless actualInfo matches .defnInfo _ do
      throwError "Expected definition: {actual}"
    let expectedInfo ← getConstInfo expected
    unless actualInfo.levelParams.length == expectedInfo.levelParams.length do
      throwError "Definition universe mismatch: {actual}"
    let params := (List.range actualInfo.levelParams.length).map (fun i => Name.mkSimple ("auditUniverse" ++ toString i))
    let levels := params.map Level.param
    let term := mkConst actual levels
    let expectedTerm := mkConst expected levels
    let expectedType ← inferType expectedTerm
    let expectedValue ← forallTelescope expectedType fun args _ =>
      mkForallFVars args (mkAppN expectedTerm args)
    unless ← isDefEq (← inferType term) expectedValue do
      throwError "Exact definition type mismatch {actual}: {← inferType term}"
    let env := (← getEnv).toKernelEnv
    let limit := (Core.getMaxHeartbeats (← getOptions)).toUSize
    for (label, value) in #[("constant",term),("body",actualInfo.instantiateValueLevelParams! levels)] do
      let name ← mkFreshUserName (Name.mkSimple ("kernelDefinition_" ++ label))
      let decl : Declaration := .defnDecl {
        name := name
        levelParams := params
        type := expectedValue
        value := value
        hints := .opaque
        safety := .safe
      }
      let _ ← ofExceptKernelException <| Kernel.Environment.addDeclCore env limit decl none
      logInfo m!"KERNEL_EXPECTED_DEFINITION_OK {label} {actual}"
    logInfo m!"EXACT_DEFINITION_TYPE_OK {actual}"

end FiniteSpectrumIndependentKernel
namespace FiniteSpectrumIndependentExpected
open ExactCriticalCurve ExactCriticalCurve.Binary ExactCriticalCurve.Quantum ExactCriticalCurve.Asymptotics ExactCriticalCurve.FiniteSpectrum

def E_ordinaryEigenvalue := ∀ (n k r : ℕ), ℝ
def E_sectorEigenvalue := ∀ (n k : ℕ), PhysicalSectorLabel k → ℝ
def E_closedGramSpectrum := ∀ (n k : ℕ), Multiset ℝ
def E_closedFiniteSuccess := ∀ (n k : ℕ), ℝ

def E_ordinaryEigenvalue_eq_gram := ∀ {k r : ℕ} (n : ℕ) (N : OrdinaryDefect k r),
  ordinaryEigenvalue n k r=ordinaryGramValue n k r

def E_sectorEigenvalue_eq_gram := ∀ (n : ℕ) {k : ℕ} (hk : 0<k) (a : PhysicalSectorLabel k),
  sectorEigenvalue n k a=physicalGramSectorValue n k a

def E_sectorEigenvalue_pos := ∀ (n : ℕ) {k : ℕ} (hk : 0<k) (a : PhysicalSectorLabel k),
  0<sectorEigenvalue n k a

def E_closedGramSpectrum_eq_physical := ∀ (n : ℕ) {k : ℕ} (hk : 0<k),
  closedGramSpectrum n k=physicalGramSpectrum n k

def E_closedGramSpectrum_count := ∀ (n k : ℕ) (x : ℝ),
  (closedGramSpectrum n k).count x=
    ∑ a : PhysicalSectorLabel k, if sectorEigenvalue n k a=x then ⌊physicalMultiplicity n k a⌋₊ else 0

def E_closedGramSpectrum_mem := ∀ (n : ℕ) {k : ℕ} (hk : 0<k) (x : ℝ),
  x∈closedGramSpectrum n k ↔ ∃ a : PhysicalSectorLabel k,
    0<physicalMultiplicity n k a ∧ sectorEigenvalue n k a=x

def E_closedMultiplicity_sum_le := ∀ (n : ℕ) {k : ℕ} (hk : 0<k),
  ∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊ ≤ Fintype.card (StabilizerGroup n)

def E_closedFiniteSuccess_eq_physical := ∀ (n : ℕ) {k : ℕ} (hk : 0<k),
  closedFiniteSuccess n k=physicalFiniteSuccess n k

def E_closedGramSpectrum_complete := ∀ (n : ℕ) {k : ℕ} (hk : 0<k),
  Multiset.replicate (Fintype.card (StabilizerGroup n)-
    ∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊) 0+closedGramSpectrum n k=
      realSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)

def E_finiteSpectrum := ∀ (n k : ℕ) (_hn : 1≤n) (hk : 1≤k),
    Fintype.card (StabilizerGroup n)=2^n*∏ j∈Finset.range n,(1+2^(j+1)) ∧
    (∀ r : ℕ, Nonempty (OrdinaryDefect k r) ↔ ordinaryAdmissible k r) ∧
    (∀ r : ℕ, Nonempty (ExceptionalDefect k r) ↔ exceptionalAdmissible k r) ∧
    (∀ r : ℕ, ∀ N : ExceptionalDefect k r,
      exceptionalMultiplicityQ n k r=(2:ℚ)^(-(n:ℤ))*ordinaryMultiplicityQ n (k-1) (r-1)) ∧
    (∀ a : PhysicalSectorLabel k,
      0<sectorEigenvalue n k a ∧ ∃ m : ℕ, physicalMultiplicity n k a=m) ∧
    nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)=closedGramSpectrum n k ∧
    (∀ x : ℝ,
      (nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)).count x=
        ∑ a : PhysicalSectorLabel k,
          if sectorEigenvalue n k a=x then ⌊physicalMultiplicity n k a⌋₊ else 0) ∧
    (∀ x : ℝ, x∈nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k) ↔
      ∃ a : PhysicalSectorLabel k, 0<physicalMultiplicity n k a ∧ sectorEigenvalue n k a=x) ∧
    (∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊ ≤
      Fintype.card (StabilizerGroup n)) ∧
    zeroMultiplicity (stabilizerGram n k) (stabilizerGram_isHermitian n k)=
      Fintype.card (StabilizerGroup n)-∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊ ∧
    (Multiset.replicate (Fintype.card (StabilizerGroup n)-
      ∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊) 0+closedGramSpectrum n k=
        realSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)) ∧
    uniformSuccess (fun S : StabilizerGroup n=>matrixTensorPower k (stabilizerProjection S))
      (stabilizerPrettyGoodMeasurement n k)=closedFiniteSuccess n k ∧
    IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n k) (StabilizerGroup n),
      uniformSuccess (fun S : StabilizerGroup n=>matrixTensorPower k (stabilizerProjection S)) M=v}
      (closedFiniteSuccess n k) ∧
    IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n k) (StabilizerGroup n),
      ∀ S : StabilizerGroup n, v≤born (M.effect S) (matrixTensorPower k (stabilizerProjection S))}
      (closedFiniteSuccess n k)
end FiniteSpectrumIndependentExpected
run_cmd FiniteSpectrumIndependentKernel.auditExactDefinition `ExactCriticalCurve.FiniteSpectrum.ordinaryEigenvalue `FiniteSpectrumIndependentExpected.E_ordinaryEigenvalue
run_cmd FiniteSpectrumIndependentKernel.auditExactDefinition `ExactCriticalCurve.FiniteSpectrum.sectorEigenvalue `FiniteSpectrumIndependentExpected.E_sectorEigenvalue
run_cmd FiniteSpectrumIndependentKernel.auditExactDefinition `ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum `FiniteSpectrumIndependentExpected.E_closedGramSpectrum
run_cmd FiniteSpectrumIndependentKernel.auditExactDefinition `ExactCriticalCurve.FiniteSpectrum.closedFiniteSuccess `FiniteSpectrumIndependentExpected.E_closedFiniteSuccess
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.ordinaryEigenvalue_eq_gram `FiniteSpectrumIndependentExpected.E_ordinaryEigenvalue_eq_gram
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.sectorEigenvalue_eq_gram `FiniteSpectrumIndependentExpected.E_sectorEigenvalue_eq_gram
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.sectorEigenvalue_pos `FiniteSpectrumIndependentExpected.E_sectorEigenvalue_pos
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum_eq_physical `FiniteSpectrumIndependentExpected.E_closedGramSpectrum_eq_physical
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum_count `FiniteSpectrumIndependentExpected.E_closedGramSpectrum_count
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum_mem `FiniteSpectrumIndependentExpected.E_closedGramSpectrum_mem
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.closedMultiplicity_sum_le `FiniteSpectrumIndependentExpected.E_closedMultiplicity_sum_le
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.closedFiniteSuccess_eq_physical `FiniteSpectrumIndependentExpected.E_closedFiniteSuccess_eq_physical
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum_complete `FiniteSpectrumIndependentExpected.E_closedGramSpectrum_complete
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.finiteSpectrum `FiniteSpectrumIndependentExpected.E_finiteSpectrum
namespace FiniteSpectrumIndependentGuards
open ExactCriticalCurve ExactCriticalCurve.Binary ExactCriticalCurve.Quantum ExactCriticalCurve.Asymptotics ExactCriticalCurve.FiniteSpectrum
example (n k r : ℕ) : ordinaryEigenvalue n k r=
  ((Fintype.card (StabilizerGroup n):ℝ)/((2:ℝ)^n*∏j∈Finset.range (k-1),((2:ℝ)^n+(2:ℝ)^j)))*
    (Nat.card (StochasticIsometryGroup k):ℝ)*
    ((2:ℝ)^((r:ℝ)*((r:ℝ)-1))/(∏j∈Finset.range r,((2:ℝ)^(j+1)-1))*
      ∏j∈Finset.range r,((2:ℝ)^((n:ℝ)+3-(k:ℝ))+(2:ℝ)^(1-(j:ℝ)))) := rfl
example (n k : ℕ) (r : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)}) :
  sectorEigenvalue n k (.inl r)=ordinaryEigenvalue n k r.val.val := rfl
example (n k : ℕ) (r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)}) :
  sectorEigenvalue n k (.inr r)=ordinaryEigenvalue n (k-1) (r.val.val-1) := rfl
example (n k : ℕ) : closedGramSpectrum n k=
  ∑a : PhysicalSectorLabel k,Multiset.replicate ⌊physicalMultiplicity n k a⌋₊ (sectorEigenvalue n k a) := rfl
example (n k : ℕ) : closedFiniteSuccess n k=
  ((∑a : PhysicalSectorLabel k,physicalMultiplicity n k a*Real.sqrt (sectorEigenvalue n k a))/Fintype.card (StabilizerGroup n))^2 := rfl
end FiniteSpectrumIndependentGuards
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes := #["ExactCriticalCurve.FiniteSpectrum.ordinaryEigenvalue","ExactCriticalCurve.FiniteSpectrum.sectorEigenvalue","ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum","ExactCriticalCurve.FiniteSpectrum.closedFiniteSuccess","ExactCriticalCurve.FiniteSpectrum.ordinaryEigenvalue_eq_gram","ExactCriticalCurve.FiniteSpectrum.sectorEigenvalue_eq_gram","ExactCriticalCurve.FiniteSpectrum.sectorEigenvalue_pos","ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum_eq_physical","ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum_count","ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum_mem","ExactCriticalCurve.FiniteSpectrum.closedMultiplicity_sum_le","ExactCriticalCurve.FiniteSpectrum.closedFiniteSuccess_eq_physical","ExactCriticalCurve.FiniteSpectrum.closedGramSpectrum_complete","ExactCriticalCurve.finiteSpectrum"]
  let mut count := 0
  for (name, _) in env.constants.toList do
    if prefixes.any (fun p => name.toString==p || name.toString.startsWith (p++".")) then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Forbidden transitive axiom {ax} in {name}"
      count := count+1
      logInfo m!"NEW_DECL_AXIOMS_OK {name}"
  logInfo m!"NEW_DECL_AXIOMS_COUNT {count}"

namespace MainCriticalAuditDriver
set_option maxHeartbeats 20000000
open Lean Elab Command Meta in
def auditExactTheorem (actual expected : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? actual with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Expected a theorem declaration: {actual}"
  liftTermElabM do
    let actualInfo ← getConstInfo actual
    let expectedInfo ← getConstInfo expected
    unless actualInfo.levelParams.length == expectedInfo.levelParams.length do
      throwError "Universe generality mismatch: {actual}"
    let levelParams := (List.range actualInfo.levelParams.length).map
      (fun i => Name.mkSimple ("auditUniverse" ++ toString i))
    let levels := levelParams.map Level.param
    let term := mkConst actual levels
    let expectedTerm := mkConst expected levels
    let expectedType ← inferType expectedTerm
    -- Abstract all universe-polymorphic typeclass and index parameters on expected definitions.
    let expectedValue ← forallTelescope expectedType fun args _ => do
      let body := mkAppN expectedTerm args
      mkForallFVars args body
    unless ← isDefEq (← inferType term) expectedValue do
      throwError "Exact theorem type mismatch: {actual}\nactual: {← inferType term}\nexpected: {expectedValue}"
    -- Check both the theorem constant and its original proof body directly in
    -- the kernel against the independently constructed expected type.
    -- addDeclCore has no skipKernelTC option and returns synchronously.
    let kernelEnv := (← getEnv).toKernelEnv
    let heartbeatLimit := (Core.getMaxHeartbeats (← getOptions)).toUSize
    for (label, proof) in #[
        ("constant", term),
        ("body", actualInfo.instantiateValueLevelParams! levels)] do
      let witnessName ← mkFreshUserName (Name.mkSimple ("kernelAudit_" ++ label))
      let decl : Declaration := .thmDecl {
        name := witnessName
        levelParams := levelParams
        type := expectedValue
        value := proof
      }
      let _ ← ofExceptKernelException <|
        Kernel.Environment.addDeclCore kernelEnv heartbeatLimit decl none
      logInfo m!"KERNEL_EXPECTED_TYPE_OK {label} {actual}"
  let axioms ← collectAxioms actual
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Forbidden transitive axiom {ax} in {actual}"
  logInfo m!"EXACT_TYPE_AND_AXIOMS_OK {actual}"





open Lean Elab Command Meta in
def auditCSSStageConstant (actual expected : Name) : CommandElabM Unit := do
  liftTermElabM do
    let info ← getConstInfo actual
    let ei ← getConstInfo expected
    unless info.levelParams.length == ei.levelParams.length do
      throwError "Definition universe mismatch {actual}"
    let levelParams := (List.range info.levelParams.length).map
      (fun i => Name.mkSimple ("auditUniverse" ++ toString i))
    let levels := levelParams.map Level.param
    let value := mkConst actual levels
    let et := mkConst expected levels
    let etype ← inferType et
    let expectedValue ← forallTelescope etype fun args _ => do
      mkForallFVars args (mkAppN et args)
    unless ← isDefEq (← inferType value) expectedValue do
      throwError "Independent constant type mismatch {actual}\nactual: {← inferType value}\nexpected: {expectedValue}"
    let kernelEnv := (← getEnv).toKernelEnv
    let limit := (Core.getMaxHeartbeats (← getOptions)).toUSize
    let mut terms := #[("constant",value)]
    if info.value?.isSome then
      terms := terms.push ("body",info.instantiateValueLevelParams! levels)
    for (label, term) in terms do
      let name ← mkFreshUserName (Name.mkSimple ("definitionAudit_" ++ label))
      let decl : Declaration := .defnDecl {
        name := name, levelParams := levelParams, type := expectedValue, value := term,
        hints := .opaque, safety := .safe
      }
      let _ ← ofExceptKernelException <| Kernel.Environment.addDeclCore kernelEnv limit decl none
      logInfo m!"KERNEL_EXPECTED_DEFINITION_OK {label} {actual}"
open Lean Elab Command in
def resolveModFourPrivate (suffix : String) : CommandElabM Name := do
 let env ← getEnv
 let names := env.constants.toList.filterMap fun (nm,_) =>
   if nm.toString.endsWith suffix then some nm else none
 if names.length != 1 then throwError "Private name resolution is not unique: {suffix}"
 pure names.head!


namespace MainCriticalExpected
open Classical Filter ExactCriticalCurve
open ExactCriticalCurve.Binary ExactCriticalCurve.Quantum ExactCriticalCurve.FiniteSpectrum
open scoped BigOperators Topology
def A : ℝ := ∏'j:ℕ,(1+(1/2:ℝ)^(j+1))
def Q : ℝ := ∏'j:ℕ,(1-(1/4:ℝ)^(j+1))
def F (r:ℕ) (x:ℝ) : ℝ :=
 (2:ℝ)^((r:ℝ)*((r:ℝ)-1))/(∏j∈Finset.range r,((2:ℝ)^(j+1)-1))*
   ∏j∈Finset.range r,(x+(2:ℝ)^(1-(j:ℝ)))
def R (c:ℤ) : ℝ := if c≤1 then
 ∏j∈Finset.range (1-c).toNat,(1+(1/2:ℝ)^(j+1))
 else (∏j∈Finset.range (c-1).toNat,(1+(2:ℝ)^j))⁻¹
def W (c:ℤ) (r:ℕ) : ℝ :=
 ((2:ℝ)^(-((2*(r:ℝ)-(c:ℝ))^2+3*(2*(r:ℝ)-(c:ℝ))+4)/2) *
 (1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-2)))/(A*Q)
def L (c:ℤ) (r:ℕ) : ℝ :=
 ((2:ℝ)^(((c:ℝ)-1)*((c:ℝ)-2)/2+1)*Q*R c)*F r ((2:ℝ)^(3-(c:ℝ)))
def Curve (c:ℤ) : ℝ := (∑'r:ℕ,W c r*Real.sqrt (L c r))^2
def Scale (n k:ℕ) : ℝ :=
 (Fintype.card (StabilizerGroup n):ℝ)/((2:ℝ)^n*∏j∈Finset.range (k-1),((2:ℝ)^n+(2:ℝ)^j))
def OE (n k r:ℕ) : ℝ :=
 Scale n k*(Nat.card (StochasticIsometryGroup k):ℝ)*F r ((2:ℝ)^((n:ℝ)+3-(k:ℝ)))
def EV (n k:ℕ) : PhysicalSectorLabel k→ℝ
 | .inl r => OE n k r.val.val
 | .inr r => OE n (k-1) (r.val.val-1)
def FiniteP (n k:ℕ) : ℝ :=
 ((∑a:PhysicalSectorLabel k,physicalMultiplicity n k a*Real.sqrt (EV n k a))/
   Fintype.card (StabilizerGroup n))^2
example (c:ℤ) : ExactCriticalCurve.Asymptotics.criticalCurve c=Curve c := rfl
example (c:ℤ) (r:ℕ) : ExactCriticalCurve.Asymptotics.criticalWeight c r=W c r := rfl
example (c:ℤ) (r:ℕ) : ExactCriticalCurve.Asymptotics.criticalLambda c r=L c r := rfl
example (n k:ℕ) : closedFiniteSuccess n k=FiniteP n k := rfl

def E_main (c:ℤ) : Prop :=
  0<A ∧ 0<Q ∧
  Multipliable (fun j:ℕ=>1+(1/2:ℝ)^(j+1)) ∧
  Multipliable (fun j:ℕ=>1-(1/4:ℝ)^(j+1)) ∧
  A=(∏'j:ℕ,(1+(1/2:ℝ)^(j+1))) ∧
  Q=(∏'j:ℕ,(1-(1/4:ℝ)^(j+1))) ∧
  0<R c ∧ R 1=1 ∧
  (R c=if c≤1 then ∏j∈Finset.range (1-c).toNat,(1+(1/2:ℝ)^(j+1))
   else (∏j∈Finset.range (c-1).toNat,(1+(2:ℝ)^j))⁻¹) ∧
  (∀r:ℕ,0<W c r ∧ 0<L c r) ∧
  Summable (fun r:ℕ=>W c r*Real.sqrt (L c r)) ∧
  Summable (fun r:ℕ=>W c r*L c r) ∧
  (∑'r:ℕ,W c r*L c r)=1 ∧
  Curve c=(∑'r:ℕ,W c r*Real.sqrt (L c r))^2 ∧
  (∀ᶠn:ℕ in atTop,1≤((n:ℤ)+c).toNat ∧ (((n:ℤ)+c).toNat:ℤ)=(n:ℤ)+c) ∧
  Tendsto (fun n:ℕ=>FiniteP n ((n:ℤ)+c).toNat) atTop (𝓝 (Curve c)) ∧
  Tendsto (fun n:ℕ=>uniformSuccess
    (fun S:StabilizerGroup n=>matrixTensorPower ((n:ℤ)+c).toNat (stabilizerProjection S))
    (stabilizerPrettyGoodMeasurement n ((n:ℤ)+c).toNat)) atTop (𝓝 (Curve c)) ∧
  (∀ᶠn:ℕ in atTop,
    IsGreatest {v:ℝ|∃M:POVM (CopyConfig n ((n:ℤ)+c).toNat) (StabilizerGroup n),
      uniformSuccess (fun S:StabilizerGroup n=>
        matrixTensorPower ((n:ℤ)+c).toNat (stabilizerProjection S)) M=v}
      (FiniteP n ((n:ℤ)+c).toNat))
end MainCriticalExpected
run_cmd auditExactTheorem `ExactCriticalCurve.criticalCurve `MainCriticalAuditDriver.MainCriticalExpected.E_main
end MainCriticalAuditDriver

namespace MainTailsAuditDriver
set_option maxHeartbeats 20000000
open Lean Elab Command Meta in
def auditExactTheorem (actual expected : Name) : CommandElabM Unit := do
  let env ← getEnv
  match env.find? actual with
  | some (.thmInfo _) => pure ()
  | _ => throwError "Expected a theorem declaration: {actual}"
  liftTermElabM do
    let actualInfo ← getConstInfo actual
    let expectedInfo ← getConstInfo expected
    unless actualInfo.levelParams.length == expectedInfo.levelParams.length do
      throwError "Universe generality mismatch: {actual}"
    let levelParams := (List.range actualInfo.levelParams.length).map
      (fun i => Name.mkSimple ("auditUniverse" ++ toString i))
    let levels := levelParams.map Level.param
    let term := mkConst actual levels
    let expectedTerm := mkConst expected levels
    let expectedType ← inferType expectedTerm
    -- Abstract all universe-polymorphic typeclass and index parameters on expected definitions.
    let expectedValue ← forallTelescope expectedType fun args _ => do
      let body := mkAppN expectedTerm args
      mkForallFVars args body
    unless ← isDefEq (← inferType term) expectedValue do
      throwError "Exact theorem type mismatch: {actual}\nactual: {← inferType term}\nexpected: {expectedValue}"
    -- Check both the theorem constant and its original proof body directly in
    -- the kernel against the independently constructed expected type.
    -- addDeclCore has no skipKernelTC option and returns synchronously.
    let kernelEnv := (← getEnv).toKernelEnv
    let heartbeatLimit := (Core.getMaxHeartbeats (← getOptions)).toUSize
    for (label, proof) in #[
        ("constant", term),
        ("body", actualInfo.instantiateValueLevelParams! levels)] do
      let witnessName ← mkFreshUserName (Name.mkSimple ("kernelAudit_" ++ label))
      let decl : Declaration := .thmDecl {
        name := witnessName
        levelParams := levelParams
        type := expectedValue
        value := proof
      }
      let _ ← ofExceptKernelException <|
        Kernel.Environment.addDeclCore kernelEnv heartbeatLimit decl none
      logInfo m!"KERNEL_EXPECTED_TYPE_OK {label} {actual}"
  let axioms ← collectAxioms actual
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Forbidden transitive axiom {ax} in {actual}"
  logInfo m!"EXACT_TYPE_AND_AXIOMS_OK {actual}"





open Lean Elab Command Meta in
def auditCSSStageConstant (actual expected : Name) : CommandElabM Unit := do
  liftTermElabM do
    let info ← getConstInfo actual
    let ei ← getConstInfo expected
    unless info.levelParams.length == ei.levelParams.length do
      throwError "Definition universe mismatch {actual}"
    let levelParams := (List.range info.levelParams.length).map
      (fun i => Name.mkSimple ("auditUniverse" ++ toString i))
    let levels := levelParams.map Level.param
    let value := mkConst actual levels
    let et := mkConst expected levels
    let etype ← inferType et
    let expectedValue ← forallTelescope etype fun args _ => do
      mkForallFVars args (mkAppN et args)
    unless ← isDefEq (← inferType value) expectedValue do
      throwError "Independent constant type mismatch {actual}\nactual: {← inferType value}\nexpected: {expectedValue}"
    let kernelEnv := (← getEnv).toKernelEnv
    let limit := (Core.getMaxHeartbeats (← getOptions)).toUSize
    let mut terms := #[("constant",value)]
    if info.value?.isSome then
      terms := terms.push ("body",info.instantiateValueLevelParams! levels)
    for (label, term) in terms do
      let name ← mkFreshUserName (Name.mkSimple ("definitionAudit_" ++ label))
      let decl : Declaration := .defnDecl {
        name := name, levelParams := levelParams, type := expectedValue, value := term,
        hints := .opaque, safety := .safe
      }
      let _ ← ofExceptKernelException <| Kernel.Environment.addDeclCore kernelEnv limit decl none
      logInfo m!"KERNEL_EXPECTED_DEFINITION_OK {label} {actual}"
open Lean Elab Command in
def resolveModFourPrivate (suffix : String) : CommandElabM Name := do
 let env ← getEnv
 let names := env.constants.toList.filterMap fun (nm,_) =>
   if nm.toString.endsWith suffix then some nm else none
 if names.length != 1 then throwError "Private name resolution is not unique: {suffix}"
 pure names.head!


namespace TailExpected
open Classical Filter
open scoped BigOperators Topology
def A : ℝ := ∏' j : ℕ, (1+(1/2:ℝ)^(j+1))
def Q : ℝ := ∏' j : ℕ, (1-(1/4:ℝ)^(j+1))
def F (r : ℕ) (x : ℝ) : ℝ :=
 (2:ℝ)^((r:ℝ)*((r:ℝ)-1))/(∏ j∈Finset.range r,((2:ℝ)^(j+1)-1))*
   ∏ j∈Finset.range r,(x+(2:ℝ)^(1-(j:ℝ)))
def R (c : ℤ) : ℝ := if c≤1 then
 ∏ j∈Finset.range (1-c).toNat,(1+(1/2:ℝ)^(j+1))
 else (∏ j∈Finset.range (c-1).toNat,(1+(2:ℝ)^j))⁻¹
def W (c : ℤ) (r : ℕ) : ℝ :=
 ((2:ℝ)^(-((2*(r:ℝ)-(c:ℝ))^2+3*(2*(r:ℝ)-(c:ℝ))+4)/2)*
  (1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-2)))/(A*Q)
def L (c : ℤ) (r : ℕ) : ℝ :=
 ((2:ℝ)^(((c:ℝ)-1)*((c:ℝ)-2)/2+1)*Q*R c)*
   F r ((2:ℝ)^(3-(c:ℝ)))
def Curve (c : ℤ) : ℝ := (∑' r : ℕ,W c r*Real.sqrt (L c r))^2

example : ExactCriticalCurve.Asymptotics.criticalA=A := rfl
example : ExactCriticalCurve.Asymptotics.criticalQ=Q := rfl
example (c : ℤ) : ExactCriticalCurve.Asymptotics.criticalR c=R c := rfl
example (r : ℕ) (x : ℝ) : ExactCriticalCurve.Asymptotics.criticalF r x=F r x := rfl
example (c : ℤ) (r : ℕ) : ExactCriticalCurve.Asymptotics.criticalWeight c r=W c r := rfl
example (c : ℤ) (r : ℕ) : ExactCriticalCurve.Asymptotics.criticalLambda c r=L c r := rfl
example (c : ℤ) : ExactCriticalCurve.Asymptotics.criticalCurve c=Curve c := rfl

/-- Independently written parameter-free four-tail main theorem type. -/
def E_main : Prop :=
  Tendsto (fun m : ℕ => Curve (-(m:ℤ))/
    ((2:ℝ)^(-((m:ℝ)^2+3*(m:ℝ)+4)/2)/(A*Q))) atTop (𝓝 1) ∧
  Tendsto (fun m : ℕ => (1-Curve (m:ℤ))/(2:ℝ)^(-(m:ℝ))) atTop (𝓝 1) ∧
  Tendsto (fun m : ℤ => Curve (-m)/
    ((2:ℝ)^(-((m:ℝ)^2+3*(m:ℝ)+4)/2)/(A*Q))) atTop (𝓝 1) ∧
  Tendsto (fun m : ℤ => (1-Curve m)/(2:ℝ)^(-(m:ℝ))) atTop (𝓝 1)
end TailExpected
end MainTailsAuditDriver

run_cmd MainTailsAuditDriver.auditExactTheorem `ExactCriticalCurve.criticalCurveTails `MainTailsAuditDriver.TailExpected.E_main


/- Independently written expected statements for the paper-correspondence closure.
   Preserve all preceding release targets and original-proof-body checks. -/
namespace CorrespondenceClosureExpected
open ExactCriticalCurve ExactCriticalCurve.Binary ExactCriticalCurve.Quantum ExactCriticalCurve.Asymptotics
open Classical Module Filter
open scoped BigOperators Topology

def O (m : ℕ) (σ : ℝ) : ℝ :=
  if m = 0 then (if σ = 1 then 1 else 0) else
    2 * (2:ℝ)^(m*(m-1)) * ((2:ℝ)^m-σ) *
      ∏ j ∈ Finset.range (m-1), ((4:ℝ)^(j+1)-1)
def S (m : ℕ) : ℝ :=
  (2:ℝ)^(m*m) * ∏ j ∈ Finset.range m, ((4:ℝ)^(j+1)-1)
def A : ℝ := ∏' j : ℕ, (1+(1/2:ℝ)^(j+1))
def Q : ℝ := ∏' j : ℕ, (1-(1/4:ℝ)^(j+1))
def W (c : ℤ) (r : ℕ) : ℝ :=
  ((2:ℝ)^(-((2*(r:ℝ)-(c:ℝ))^2+3*(2*(r:ℝ)-(c:ℝ))+4)/2) *
    (1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-2))) / (A*Q)
def Wn (n k r : ℕ) : ℝ :=
  (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin):ℝ) /
    (Nat.card (StabilizerGroup n):ℝ)

def E_group_order : Prop := ∀ (k : ℕ), 1 ≤ k →
  (Nat.card (StochasticIsometryGroup k):ℝ) =
    if k%2=1 then O ((k-1)/2) ((-1:ℝ)^((k*k-1)/8))
    else if k%4=2 then 2*S ((k-2)/2)
    else (2:ℝ)^(k-2)*O ((k-2)/2) ((-1:ℝ)^(k/4))

def E_ordinary_multiplicity_bridge : Prop := ∀ (n : ℕ) {k : ℕ}, 0<k →
  (∑' r : ℕ, Wn n k r) =
    ∑ a : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)},
      (ordinaryMultiplicityQ n k a.val.val:ℝ) / (Fintype.card (StabilizerGroup n):ℝ)
def E_finite_ordinary_bound : Prop := ∀ (n : ℕ) {k : ℕ}, 0<k →
  (∑' r : ℕ, Wn n k r) ≤ 1
def E_ordinary_limit : Prop := ∀ (c : ℤ),
  Tendsto (fun n : ℕ => ∑' r : ℕ, Wn n ((n:ℤ)+c).toNat r) atTop
    (𝓝 (∑' r : ℕ, W c r))
def E_explicit_ordinary_limit : Prop := ∀ (c : ℤ),
  Tendsto (fun n : ℕ =>
    ∑ a : {r : Fin (((n:ℤ)+c).toNat+1) //
      Nonempty (OrdinaryDefect ((n:ℤ)+c).toNat r.val)},
      (ordinaryMultiplicityQ n ((n:ℤ)+c).toNat a.val.val:ℝ) /
        (Fintype.card (StabilizerGroup n):ℝ)) atTop (𝓝 (∑' r : ℕ, W c r))
def E_exceptional_amplitude_bound : Prop := ∀ (n : ℕ) {k : ℕ}, 0<k →
  physicalExceptionalAmplitude n k ≤ ((2:ℝ)^n)⁻¹
def E_actual_nonzero_bridge : Prop := ∀ (n : ℕ) {k : ℕ}, 0<k →
  ((nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)).card:ℝ) /
      (Fintype.card (StabilizerGroup n):ℝ) =
    (∑' r : ℕ, Wn n k r) +
    ∑ a : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
      (finrank ℂ (LinearMap.range (exceptionalCSSGrade n k a.val.val).mulVecLin):ℝ) /
        (Nat.card (StabilizerGroup n):ℝ)
def E_actual_zero_bridge : Prop := ∀ (n k : ℕ),
  (zeroMultiplicity (stabilizerGram n k) (stabilizerGram_isHermitian n k):ℝ) /
      (Fintype.card (StabilizerGroup n):ℝ) =
    1 - ((nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)).card:ℝ) /
      (Fintype.card (StabilizerGroup n):ℝ)
def E_nonzero_limit : Prop := ∀ (c : ℤ),
  Tendsto (fun n : ℕ =>
    ((nonzeroSpectrum (stabilizerGram n ((n:ℤ)+c).toNat)
      (stabilizerGram_isHermitian n ((n:ℤ)+c).toNat)).card:ℝ) /
        (Fintype.card (StabilizerGroup n):ℝ)) atTop (𝓝 (∑' r : ℕ, W c r))
def E_zero_limit : Prop := ∀ (c : ℤ),
  Tendsto (fun n : ℕ =>
    (zeroMultiplicity (stabilizerGram n ((n:ℤ)+c).toNat)
      (stabilizerGram_isHermitian n ((n:ℤ)+c).toNat):ℝ) /
        (Fintype.card (StabilizerGroup n):ℝ)) atTop (𝓝 (1-∑' r : ℕ, W c r))
def E_spectral_mass : Prop := ∀ (c : ℤ),
  Summable (W c) ∧
  0 ≤ (∑' r : ℕ, W c r) ∧
  (∑' r : ℕ, W c r) ≤ 1 ∧
  Tendsto (fun n : ℕ => ∑' r : ℕ, Wn n ((n:ℤ)+c).toNat r) atTop
    (𝓝 (∑' r : ℕ, W c r)) ∧
  Tendsto (fun n : ℕ =>
    ((nonzeroSpectrum (stabilizerGram n ((n:ℤ)+c).toNat)
      (stabilizerGram_isHermitian n ((n:ℤ)+c).toNat)).card:ℝ) /
        (Fintype.card (StabilizerGroup n):ℝ)) atTop (𝓝 (∑' r : ℕ, W c r)) ∧
  Tendsto (fun n : ℕ =>
    (zeroMultiplicity (stabilizerGram n ((n:ℤ)+c).toNat)
      (stabilizerGram_isHermitian n ((n:ℤ)+c).toNat):ℝ) /
        (Fintype.card (StabilizerGroup n):ℝ)) atTop (𝓝 (1-∑' r : ℕ, W c r))

example (m : ℕ) : physicalSymplecticFactor m = S m := rfl
example (c : ℤ) (r : ℕ) : criticalWeight c r = W c r := rfl
example (n k r : ℕ) : physicalOrdinaryWeight n k r = Wn n k r := rfl

def E_paperOrthogonalOrder := ∀ (m : ℕ) (σ : ℝ), ℝ
def E_odd_branch : Prop := ∀ (k : ℕ), k % 2 = 1 →
  (Nat.card (StochasticIsometryGroup k) : ℝ) =
    O ((k-1)/2) (if k%8=1 ∨ k%8=7 then 1 else -1)
def E_two_branch : Prop := ∀ (k : ℕ), k % 4 = 2 →
  (Nat.card (StochasticIsometryGroup k) : ℝ) = 2 * S ((k-2)/2)
def E_zero_branch : Prop := ∀ (k : ℕ), 0 < k → 4 ∣ k →
  (Nat.card (StochasticIsometryGroup k) : ℝ) =
    (2:ℝ)^(k-2) * O ((k-2)/2) (if k%8=0 then 1 else -1)
def E_odd_sign : Prop := ∀ (k : ℕ), k%2=1 →
  (-1:ℝ)^((k*k-1)/8) = (if k%8=1 ∨ k%8=7 then 1 else -1)
def E_even_sign : Prop := ∀ (k : ℕ), 4 ∣ k →
  (-1:ℝ)^(k/4) = (if k%8=0 then 1 else -1)
def E_order_one : Prop := Nat.card (StochasticIsometryGroup 1) = 1
def E_order_two : Prop := Nat.card (StochasticIsometryGroup 2) = 2

noncomputable def G (n k : ℕ) : Multiset ℝ :=
  Finset.univ.val.map (stabilizerGram_isHermitian n k).eigenvalues
example (m : ℕ) (σ : ℝ) : paperOrthogonalOrder m σ = O m σ := rfl
example (n k : ℕ) :
    realSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k) = G n k := rfl
example (n k : ℕ) :
    nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k) =
      (G n k).filter (· ≠ 0) := rfl
example (n k : ℕ) :
    zeroMultiplicity (stabilizerGram n k) (stabilizerGram_isHermitian n k) =
      (G n k).count 0 := rfl

end CorrespondenceClosureExpected

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.physicalOrdinaryWeight_tsum_eq_multiplicity_sum `CorrespondenceClosureExpected.E_ordinary_multiplicity_bridge
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.physicalOrdinaryWeight_tsum_le_one `CorrespondenceClosureExpected.E_finite_ordinary_bound
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.physicalOrdinaryWeight_tsum_critical_tendsto `CorrespondenceClosureExpected.E_ordinary_limit
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.ordinaryMultiplicity_sum_critical_tendsto `CorrespondenceClosureExpected.E_explicit_ordinary_limit
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.physicalExceptionalAmplitude_le_inverse_dimension `CorrespondenceClosureExpected.E_exceptional_amplitude_bound
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.actual_nonzero_mass_eq_ordinary_exceptional `CorrespondenceClosureExpected.E_actual_nonzero_bridge
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.actual_zero_mass_eq_complement `CorrespondenceClosureExpected.E_actual_zero_bridge
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.actual_nonzero_mass_critical_tendsto `CorrespondenceClosureExpected.E_nonzero_limit
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.actual_zero_mass_critical_tendsto `CorrespondenceClosureExpected.E_zero_limit
run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.criticalSpectralMass `CorrespondenceClosureExpected.E_spectral_mass

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.stochasticGroup_order_odd_mod_eight `CorrespondenceClosureExpected.E_odd_branch

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.stochasticGroup_order_two_mod_four `CorrespondenceClosureExpected.E_two_branch

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.stochasticGroup_order_zero_mod_four `CorrespondenceClosureExpected.E_zero_branch

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.paperOddTypeSign_mod_eight `CorrespondenceClosureExpected.E_odd_sign

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.paperEvenZeroTypeSign_mod_eight `CorrespondenceClosureExpected.E_even_sign

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.paperStochasticGroup_order `CorrespondenceClosureExpected.E_group_order

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.stochasticGroup_order_one `CorrespondenceClosureExpected.E_order_one

run_cmd FiniteSpectrumIndependentKernel.auditExactTheorem `ExactCriticalCurve.Asymptotics.stochasticGroup_order_two `CorrespondenceClosureExpected.E_order_two

run_cmd FiniteSpectrumIndependentKernel.auditExactDefinition `ExactCriticalCurve.Asymptotics.paperOrthogonalOrder `CorrespondenceClosureExpected.E_paperOrthogonalOrder
