/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.AuxLemma
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.CachedIntervals
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005

/-!
# A faster, exact evaluator for rejection certificates

Sign-based interval products avoid forming all four endpoint products in every
Taylor step. The original evaluator and all existing certificate statements are
preserved; the equalities below justify changing only their computational proofs.
-/

@[expose] public section

namespace GerverSofa.PartE

open GerverSofa.PartALeanCert LeanCert.Core LeanCert.Engine

/-- Horner evaluation with sign-based products rather than four-product hulls. -/
def fastTaylorSeries (coeffs : List ℚ) (I : IntervalRat) : IntervalRat :=
  coeffs.foldr (fun c acc => IntervalRat.add (IntervalRat.singleton c)
    (IntervalRat.mulFast acc I)) (IntervalRat.singleton 0)

/-- The original sine enclosure, using the faster Horner evaluation. -/
def fastSine (I : IntervalRat) (n : Nat) : IntervalRat :=
  let raw := IntervalRat.add (fastTaylorSeries (IntervalRat.sinTaylorCoeffs n) I)
    (IntervalRat.sinRemainderBoundComputable I n)
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match IntervalRat.intersect raw globalBound with
  | some refined => refined
  | none => raw

/-- The original cosine enclosure, using the faster Horner evaluation. -/
def fastCosine (I : IntervalRat) (n : Nat) : IntervalRat :=
  let raw := IntervalRat.add (fastTaylorSeries (IntervalRat.cosTaylorCoeffs n) I)
    (IntervalRat.cosRemainderBoundComputable I n)
  let globalBound : IntervalRat := ⟨-1, 1, by norm_num⟩
  match IntervalRat.intersect raw globalBound with
  | some refined => refined
  | none => raw

/-- Sign-based Horner evaluation preserves both original rational endpoints. -/
theorem fastTaylorSeries_eq
    (coeffs : List ℚ) (I : IntervalRat) :
    fastTaylorSeries coeffs I = IntervalRat.evalTaylorSeries coeffs I := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
      change IntervalRat.add (IntervalRat.singleton c)
        (IntervalRat.mulFast (fastTaylorSeries cs I) I) =
          IntervalRat.add (IntervalRat.singleton c)
            (IntervalRat.mul (IntervalRat.evalTaylorSeries cs I) I)
      rw [IntervalRat.mulFast_eq_mul, ih]

/-- The faster sine enclosure is exactly the original enclosure. -/
theorem fastSine_eq
    (I : IntervalRat) (n : Nat) : fastSine I n = IntervalRat.sinComputable I n := by
  simp only [fastSine, IntervalRat.sinComputable, fastTaylorSeries_eq]
  rfl

/-- The faster cosine enclosure is exactly the original enclosure. -/
theorem fastCosine_eq
    (I : IntervalRat) (n : Nat) : fastCosine I n = IntervalRat.cosComputable I n := by
  simp only [fastCosine, IntervalRat.cosComputable, fastTaylorSeries_eq]
  rfl

/-- The two residual intervals with the first-angle trigonometric values supplied explicitly. -/
def fastResidualIntervals (phi theta : IntervalRat) (configuration : EvalConfig)
    (cosinePhi sinePhi : IntervalRat) : IntervalRat × IntervalRat :=
  let subtract := fun a b => IntervalRat.add a (IntervalRat.neg b)
  let scale := fun q a => IntervalRat.mulFast (IntervalRat.singleton q) a
  let one := IntervalRat.singleton 1
  let half := IntervalRat.singleton (1 / 2)
  let delta := subtract theta phi
  let cosineTheta := fastCosine theta configuration.taylorDepth
  let sineTheta := fastSine theta configuration.taylorDepth
  let base := IntervalRat.add
    (IntervalRat.add (subtract (subtract (scale (1 / 2) kernelPiInterval) phi) theta)
      (scale (1 / 2) delta)) (scale (1 / 4) (IntervalRat.mulFast delta delta))
  let denominator := subtract cosinePhi
    (IntervalRat.mulFast (IntervalRat.add one (scale (1 / 2) delta)) sinePhi)
  let numerator := IntervalRat.add
    (IntervalRat.add (IntervalRat.add sinePhi half) (IntervalRat.neg (scale (1 / 2) cosinePhi)))
    (IntervalRat.mulFast base sinePhi)
  let numeratorB := IntervalRat.add
    (IntervalRat.mulFast numerator (IntervalRat.add one (scale (1 / 2) delta)))
    (IntervalRat.mulFast base denominator)
  let first := IntervalRat.add
    (IntervalRat.add (IntervalRat.add (IntervalRat.add
      (subtract (IntervalRat.mulFast numerator (subtract cosineTheta cosinePhi))
        (IntervalRat.mulFast (scale 2 numeratorB) sinePhi))
      (IntervalRat.mulFast (IntervalRat.mulFast (subtract delta one) cosineTheta) denominator))
      (IntervalRat.neg (IntervalRat.mulFast sineTheta denominator)))
      (IntervalRat.mulFast cosinePhi denominator)) (IntervalRat.mulFast sinePhi denominator)
  let second := IntervalRat.add
    (IntervalRat.add (IntervalRat.add (IntervalRat.add
      (subtract (IntervalRat.mulFast numerator (IntervalRat.add (scale 3 sineTheta) sinePhi))
        (IntervalRat.mulFast (scale 2 numeratorB) cosinePhi))
      (IntervalRat.mulFast
        (IntervalRat.mulFast (scale 3 (subtract delta one)) sineTheta) denominator))
      (IntervalRat.mulFast (scale 3 cosineTheta) denominator))
      (IntervalRat.neg (IntervalRat.mulFast sinePhi denominator)))
    (IntervalRat.mulFast cosinePhi denominator)
  (first, second)

/-- The faster residual calculation returns exactly the same rational intervals. -/
theorem fastResidualIntervals_eq (phi theta : IntervalRat) (configuration : EvalConfig)
    (cosinePhi sinePhi : IntervalRat) :
    fastResidualIntervals phi theta configuration cosinePhi sinePhi =
      CachedIntervals.residualIntervals phi theta configuration cosinePhi sinePhi := by
  simp only [fastResidualIntervals, CachedIntervals.residualIntervals,
    IntervalRat.mulFast_eq_mul, fastCosine_eq, fastSine_eq]

/-- Apply the existing zero-exclusion tests to the faster residual calculation. -/
def fastRejectionWithTrig (cell : AngleCell) (configuration : EvalConfig)
    (cosinePhi sinePhi : IntervalRat) : Bool :=
  let residuals := fastResidualIntervals cell.phiI cell.thetaI configuration cosinePhi sinePhi
  intervalExcludesZero residuals.1 || intervalExcludesZero residuals.2

private theorem fastRejectionWithTrig_eq (cell : AngleCell) (configuration : EvalConfig)
    (cosinePhi sinePhi : IntervalRat) :
    fastRejectionWithTrig cell configuration cosinePhi sinePhi =
      CachedIntervals.rejected cell configuration cosinePhi sinePhi := by
  simp only [fastRejectionWithTrig, CachedIntervals.rejected, fastResidualIntervals_eq]

/-- Compute the first-angle enclosures when the input has no cached entry. -/
def fastRejectionCheck (cell : AngleCell) (configuration : EvalConfig) : Bool :=
  fastRejectionWithTrig cell configuration
    (fastCosine cell.phiI configuration.taylorDepth)
    (fastSine cell.phiI configuration.taylorDepth)

/-- The result of the fast computation proves the original rejection statement. -/
theorem rejected_of_fastCheck (cell : AngleCell) (configuration : EvalConfig)
    (certificate : fastRejectionCheck cell configuration = true) :
    cell.rejected configuration = true := by
  simpa only [fastRejectionCheck, fastRejectionWithTrig_eq, fastCosine_eq, fastSine_eq,
    CachedIntervals.rejected_eq] using certificate

/-- Transfer a fast check that reuses the exact first-angle cache. -/
theorem rejected_of_fastCached (cell : AngleCell) (configuration : EvalConfig)
    (cosinePhi sinePhi : IntervalRat)
    (cosineEquality :
      IntervalRat.cosComputable cell.phiI configuration.taylorDepth = cosinePhi)
    (sineEquality :
      IntervalRat.sinComputable cell.phiI configuration.taylorDepth = sinePhi)
    (certificate : fastRejectionWithTrig cell configuration cosinePhi sinePhi = true) :
    cell.rejected configuration = true :=
  CachedIntervals.rejected_of_cached cell configuration cosinePhi sinePhi cosineEquality
    sineEquality ((fastRejectionWithTrig_eq cell configuration cosinePhi sinePhi) ▸ certificate)

end GerverSofa.PartE

open Lean Meta Elab Tactic in
/-- Kernel-check the fast computation while retaining the original auxiliary proposition. -/
elab (name := gerverFastRejection) "gerver_fast_rejection" index:(ppSpace num)? : tactic =>
  closeMainGoalUsing `gerver_fast_rejection fun expectedType _ => do
    let expectedType ← instantiateMVars expectedType
    unless expectedType.isAppOfArity ``Eq 3 do throwError "expected a rejection equality"
    let expression := expectedType.appFn!.appArg!
    unless expression.isAppOfArity ``GerverSofa.PartE.AngleCell.rejected 2 do
      throwError "expected an AngleCell rejection test"
    let arguments := expression.getAppArgs
    let cell := arguments[0]!
    let configuration := arguments[1]!
    let reflexivity := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let proof := match index with
      | none =>
        mkAppN (mkConst ``GerverSofa.PartE.rejected_of_fastCheck)
          #[cell, configuration, reflexivity]
      | some number =>
        let cacheEntry (field suffix : String) :=
          mkConst (`GerverSofa.PartE.CachedIntervals ++
            Name.mkSimple (field ++ toString number.getNat ++ suffix))
        mkAppN (mkConst ``GerverSofa.PartE.rejected_of_fastCached)
          #[cell, configuration, cacheEntry "cosine" "", cacheEntry "sine" "",
            cacheEntry "cosine" "_eq", cacheEntry "sine" "_eq", reflexivity]
    let name ← mkAuxLemma [] expectedType proof
    pure (mkConst name)
