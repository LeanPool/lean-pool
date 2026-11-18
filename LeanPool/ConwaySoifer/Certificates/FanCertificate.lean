/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module
public meta import Lean.Elab.Command  -- shake: keep
public meta import Lean.Elab.Tactic.Basic  -- shake: keep
public meta import Lean.Meta.Tactic.AuxLemma  -- shake: keep
public import LeanPool.ConwaySoifer.Certificates.Witness

/-!
# Shared kernel-checked orientation fan certificates

A support bound depends on three selected points, rather than the complete
checkpoint. Reuse that smaller arithmetic certificate across repeated fan queries,
and check long fan proofs in chunks to bound the kernel's working set.
-/

@[expose] public section

namespace ConwaySoifer.Certificates.FanProof

open ConwaySoifer.Certificates

theorem cachedSupport (Ps : List IPoint) (den : Int) (u : IPoint) (T : Triple)
    (a b d : Int) (fuel : Nat) (P₀ P₁ P₂ : IPoint)
    (h₀ : nth Ps T.1 = some P₀) (h₁ : nth Ps T.2.1 = some P₁)
    (h₂ : nth Ps T.2.2 = some P₂)
    (h : supportOK [P₀, P₁, P₂] den u (0, 1, 2) a b d fuel = true) :
    supportOK Ps den u T a b d fuel = true := by
  simpa only [supportOK, nth, h₀, h₁, h₂] using h

theorem cachedNode (Ps : List IPoint) (den : Int) (caps : List Cap) (T : Triple)
    (u : IPoint) (a b d : Int) (fuel : Nat)
    (h : supportOK Ps den u T a b d fuel = true) :
    nodeWitnessCheck Ps den caps (some T) u a b d fuel = true := h

theorem cachedCone (Ps : List IPoint) (den : Int) (caps : List Cap) (T : Triple)
    (u v : IPoint) (a b d : Int) (fuel : Nat)
    (hu : supportOK Ps den u T a b d fuel = true)
    (hv : supportOK Ps den v T a b d fuel = true) :
    coneWitnessCheck Ps den caps (some T) u v a b d fuel = true :=
  Bool.and_eq_true_iff.mpr ⟨hu, hv⟩

theorem cachedNext (Ps : List IPoint) (den : Int) (caps : List Cap)
    (a b d : Int) (fuel : Nat) (v : IPoint) (node cone : BoundWitness)
    (rest : FanWitness) (u : IPoint)
    (hn : nodeWitnessCheck Ps den caps node u a b d fuel = true)
    (hc : coneWitnessCheck Ps den caps cone u v a b d fuel = true)
    (hd : nonnegOn (detP u v) a b d fuel = true)
    (hv : nodeCond v a b d fuel = true)
    (ht : rest.check Ps den caps a b d fuel v = true) :
    (FanWitness.next v node cone rest).check Ps den caps a b d fuel u = true :=
  Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨hn, hc⟩, hd⟩, hv⟩, ht⟩

theorem cachedTerminal (Ps : List IPoint) (den : Int) (caps : List Cap)
    (a b d : Int) (fuel : Nat) (left right cone : BoundWitness) (u : IPoint)
    (hl : nodeWitnessCheck Ps den caps left u a b d fuel = true)
    (hc : coneWitnessCheck Ps den caps cone u rotEastP a b d fuel = true)
    (hd : nonnegOn (detP u rotEastP) a b d fuel = true)
    (hr : nodeWitnessCheck Ps den caps right rotEastP a b d fuel = true) :
    (FanWitness.terminal left right cone).check Ps den caps a b d fuel u = true :=
  Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hl, hc⟩, hd⟩, hr⟩

end ConwaySoifer.Certificates.FanProof

namespace ConwaySoifer.Certificates.FanProof

meta section
open Lean Meta Elab Tactic Command
open ConwaySoifer.Certificates

/-- Imported checkpoint used to share support certificates across elaboration branches. -/
initialize fanCacheAnchor : EnvExtension Name ←
  registerEnvExtension (pure Name.anonymous) (asyncMode := .local)

/-- Select the imported checkpoint that anchors shared support certificates. -/
elab (name := prepareFanCache) "prepare_fan_cache " anchor:ident : command => do
  let anchor ← resolveGlobalConstNoOverload anchor
  modifyEnv fun env => fanCacheAnchor.setState env anchor

/-- Form the proposition that a Boolean arithmetic certificate returns true. -/
def booleanType (value : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) value (mkConst ``Bool.true)

/-- Construct a closed arithmetic proof term whose reductions are checked by the kernel. -/
def closedArithmeticProof (type : Expr) : MetaM Expr := withoutModifyingMCtx do
  let proof ← if type.isAppOfArity ``Eq 3 then mkEqRefl type.appArg! else mkDecideProof type
  instantiateMVars proof

/-- Reuse a support certificate keyed by its three selected points and direction. -/
def cachedSupportProof (arguments : Array Expr) : MetaM Expr := withoutModifyingMCtx do
  let #[points, denominator, direction, triple, lower, upper, scale, fuel] := arguments
    | throwError "invalid support arguments"
  let triple ← whnf triple
  let tripleArgs := triple.getAppArgs
  let pair ← whnf tripleArgs[3]!
  let pairArgs := pair.getAppArgs
  let indices := #[tripleArgs[2]!, pairArgs[2]!, pairArgs[3]!]
  let mut selected : Array Expr := #[]
  let mut equalities : Array Expr := #[]
  for index in indices do
    let lookup := mkApp3 (mkConst ``nth) (mkConst ``IPoint) points index
    let result ← whnf lookup
    unless result.isAppOfArity ``Option.some 2 do throwError "invalid support index"
    selected := selected.push (← whnf result.appArg!)
    equalities := equalities.push (← mkEqRefl result)
  let selectedPoints ← mkListLit (mkConst ``IPoint) selected.toList
  let selectedTriple := toExpr ((0, 1, 2) : Nat × Nat × Nat)
  let direction ← whnf direction
  let query := mkAppN (mkConst ``supportOK)
    #[selectedPoints, denominator, direction, selectedTriple, lower, upper, scale, fuel]
  let type := booleanType query
  let env ← getEnv
  let anchor := fanCacheAnchor.getState env
  let cacheName := mkPrivateName env (Name.str `ConwaySoifer.SupportCache (toString type.hash))
  realizeConst anchor cacheName do
    let value ← closedArithmeticProof type
    addDecl (.thmDecl { name := cacheName, levelParams := [], type, value })
  instantiateMVars (mkAppN (mkConst ``cachedSupport)
    (arguments ++ selected ++ equalities ++ #[mkConst cacheName]))

/-- Prove a fan node check, sharing a supplied support triple when present. -/
def cachedNodeProof (arguments : Array Expr) : MetaM Expr := do
  let #[points, denominator, caps, witness, direction, lower, upper, scale, fuel] := arguments
    | throwError "invalid node arguments"
  let witness ← whnf witness
  if witness.isAppOfArity ``Option.some 2 then
    let triple := witness.appArg!
    let proof ← cachedSupportProof
      #[points, denominator, direction, triple, lower, upper, scale, fuel]
    return mkAppN (mkConst ``cachedNode)
      #[points, denominator, caps, triple, direction, lower, upper, scale, fuel, proof]
  closedArithmeticProof (booleanType (mkAppN (mkConst ``nodeWitnessCheck) arguments))

/-- Prove a fan cone check from shared support certificates at both endpoints. -/
def cachedConeProof (arguments : Array Expr) : MetaM Expr := do
  let #[points, denominator, caps, witness, left, right, lower, upper, scale, fuel] := arguments
    | throwError "invalid cone arguments"
  let witness ← whnf witness
  if witness.isAppOfArity ``Option.some 2 then
    let triple := witness.appArg!
    let first ← cachedSupportProof
      #[points, denominator, left, triple, lower, upper, scale, fuel]
    let second ← cachedSupportProof
      #[points, denominator, right, triple, lower, upper, scale, fuel]
    return mkAppN (mkConst ``cachedCone)
      #[points, denominator, caps, triple, left, right, lower, upper, scale, fuel, first, second]
  closedArithmeticProof (booleanType (mkAppN (mkConst ``coneWitnessCheck) arguments))

/-- Prove the terminal fan sector, including the fixed east-facing endpoint. -/
def cachedTerminalProof (common args : Array Expr) (direction : Expr) : MetaM Expr := do
  let #[points, denominator, caps, lower, upper, scale, fuel] := common
    | throwError "invalid terminal context"
  let #[left, right, cone] := args | throwError "invalid fan terminal"
  let east := mkConst ``rotEastP
  let leftProof ← cachedNodeProof
    #[points, denominator, caps, left, direction, lower, upper, scale, fuel]
  let coneProof ← cachedConeProof
    #[points, denominator, caps, cone, direction, east, lower, upper, scale, fuel]
  let determinant := mkApp2 (mkConst ``detP) direction east
  let determinantProof ← closedArithmeticProof (booleanType
    (mkAppN (mkConst ``nonnegOn) #[determinant, lower, upper, scale, fuel]))
  let rightProof ← cachedNodeProof
    #[points, denominator, caps, right, east, lower, upper, scale, fuel]
  return mkAppN (mkConst ``cachedTerminal)
    (common ++ #[left, right, cone, direction,
      leftProof, coneProof, determinantProof, rightProof])

/-- Assemble sector proofs into small separately checked kernel certificates. -/
def closeFanFrames (frames : Array (Array Expr)) (lastProof : Expr) : MetaM Expr := do
  let mut proof := lastProof
  for i in [:frames.size] do
    let frame := frames[frames.size - i - 1]!
    proof := mkAppN (mkConst ``cachedNext) (frame.push proof)
    -- Small checked chunks keep large fan tails out of one kernel check.
    if i % 8 == 7 then
      let type ← inferType proof
      let name ← mkAuxLemma [] type proof (kind? := some `_fanChunk)
      proof := mkConst name
  return proof

/-- Traverse a closed fan witness and construct its sector-by-sector certificate. -/
def cachedFanProof (arguments : Array Expr) : MetaM Expr := do
  let #[points, denominator, caps, lower, upper, scale, fuel, witness, direction] := arguments
    | throwError "invalid fan arguments"
  let common := #[points, denominator, caps, lower, upper, scale, fuel]
  let mut witness := witness
  let mut direction := direction
  let mut frames : Array (Array Expr) := #[]
  let mut proof? : Option Expr := none
  for _ in [:4096] do
    let value ← whnf witness
    let args := value.getAppArgs
    if value.isAppOfArity ``FanWitness.next 4 then
      let #[next, node, cone, rest] := args | throwError "invalid fan next"
      let nodeProof ← cachedNodeProof
        #[points, denominator, caps, node, direction, lower, upper, scale, fuel]
      let coneProof ← cachedConeProof
        #[points, denominator, caps, cone, direction, next, lower, upper, scale, fuel]
      let determinant := mkApp2 (mkConst ``detP) direction next
      let determinantProof ← closedArithmeticProof (booleanType
        (mkAppN (mkConst ``nonnegOn) #[determinant, lower, upper, scale, fuel]))
      let directionProof ← closedArithmeticProof (booleanType
        (mkAppN (mkConst ``nodeCond) #[next, lower, upper, scale, fuel]))
      frames := frames.push (common ++ #[next, node, cone, rest, direction,
        nodeProof, coneProof, determinantProof, directionProof])
      witness := rest
      direction := next
    else if value.isAppOfArity ``FanWitness.terminal 3 then
      proof? := some (← cachedTerminalProof common args direction)
      break
    else
      throwError "invalid fan witness"
  let some proof := proof? | throwError "fan traversal limit exceeded"
  closeFanFrames frames proof

/-- Prove a closed witnessed-fan check by sharing three-point support bounds and
checking the assembled fan in small kernel-checked chunks. -/
elab (name := tacticCertifyFan) "certify_fan" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    unless type.isAppOfArity ``Eq 3 do throwError "expected a boolean certificate equality"
    let value := type.appFn!.appArg!
    let args := value.getAppArgs
    unless value.isAppOfArity ``ExclusionHint.check 9 do
      throwError "expected an exclusion hint"
    let hint ← whnf args[5]!
    unless hint.isAppOfArity ``ExclusionHint.witnessedFan 1 do
      throwError "expected an orientation fan"
    -- Added certificates must not consume the caller's auxiliary names.
    let auxiliaryPrefix := (← getDeclNGen).namePrefix ++ `supportQueries
    let proof ← withDeclNameForAuxNaming auxiliaryPrefix do
      cachedFanProof #[args[0]!, args[1]!, args[2]!, args[6]!, args[7]!, args[8]!,
        args[4]!, hint.appArg!, mkConst ``eastP]
    let name ← mkAuxLemma [] type proof
    goal.assign (mkConst name)
  replaceMainGoal []

end

end ConwaySoifer.Certificates.FanProof
