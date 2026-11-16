/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.MovingSofa.CertificateEvaluation
public import LeanPool.MovingSofa.CertificateCache

public import LeanPool.MovingSofa.KernelCertificate
public meta import LeanPool.MovingSofa.KernelCertificate

/-! # Kernel checking for closed interval certificates

Cache indices select exact trigonometric equalities; index 128 requests the original computation.
-/

public meta section

open Lean Meta Elab Tactic

namespace GerverSofa.PartE.Certificate

/-- Name one component of an exact interval cache entry. -/
def certificateCacheName (component : String) (index : Nat) : Name :=
  let suffix := String.ofList (List.replicate (3 - (toString index).length) '0') ++ toString index
  s!"GerverSofa.PartE.CertificateCache.{component}{suffix}".toName

/-- Supply an exact cached value, or retain the original trigonometric computation. -/
def certificateTrigonometricValue (operation : String) (interval depth : Expr) (index : Nat) :
    MetaM (Expr × Expr) := do
  if index < 128 then
    let name := certificateCacheName operation index
    return (mkConst name, mkConst (name.appendAfter "_eq"))
  unless index == 128 do throwError "Invalid certificate cache index"
  let functionName := if operation == "cos" then
    ``LeanCert.Core.IntervalRat.cosComputable else ``LeanCert.Core.IntervalRat.sinComputable
  let value := mkApp2 (mkConst functionName) interval depth
  return (value, ← mkEqRefl value)

/-- Assemble a rejection proof from exact trigonometric equalities and interval arithmetic. -/
def certificateProof (expectedType : Expr) (phiIndex thetaIndex : Nat) : MetaM Expr := do
  let some (_, lhs, rhs) ← matchEq? expectedType
    | throwError "Expected a Boolean rejection equality"
  unless lhs.isAppOfArity ``GerverSofa.PartE.AngleCell.rejected 2 && rhs.isConstOf ``Bool.true do
    throwError "Expected a closed rejection test"
  let arguments := lhs.getAppArgs
  let cell := arguments[0]!
  let configuration := arguments[1]!
  let phi := mkApp (mkConst ``GerverSofa.PartE.AngleCell.phiI) cell
  let theta := mkApp (mkConst ``GerverSofa.PartE.AngleCell.thetaI) cell
  let depth := mkApp (mkConst ``LeanCert.Engine.EvalConfig.taylorDepth) configuration
  let (cp, hcp) ← certificateTrigonometricValue "cos" phi depth phiIndex
  let (sp, hsp) ← certificateTrigonometricValue "sin" phi depth phiIndex
  let (ct, hct) ← certificateTrigonometricValue "cos" theta depth thetaIndex
  let (st, hst) ← certificateTrigonometricValue "sin" theta depth thetaIndex
  let residuals := mkAppN (mkConst ``GerverSofa.PartE.certificateResidualsFromTrig)
    #[phi, theta, cp, sp, ct, st]
  let evaluation := mkAppN (mkConst ``GerverSofa.PartE.certificateResiduals_eq_fromTrig)
    #[phi, theta, depth, cp, sp, ct, st, hcp, hsp, hct, hst]
  let checkType := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
    (mkApp (mkConst ``GerverSofa.PartE.certificateRejects) residuals) (mkConst ``Bool.true)
  let check ← mkDecideProof checkType
  return mkAppN (mkConst ``GerverSofa.PartE.rejected_of_computations)
    #[cell, configuration, residuals, evaluation, check]

/-- Check a rejection certificate while preserving its original auxiliary declaration type. -/
elab (name := certificateDecide) "certificate_decide" phi:num theta:num : tactic => do
  closeCertificate `certificate_decide fun expectedType =>
    certificateProof expectedType phi.getNat theta.getNat

end GerverSofa.PartE.Certificate
