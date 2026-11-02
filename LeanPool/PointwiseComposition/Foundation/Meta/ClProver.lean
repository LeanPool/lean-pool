/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Meta.ClProverTheorems
public meta import LeanPool.PointwiseComposition.Foundation.Meta.ClProverTheorems
public import Mathlib.Util.AtomM

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Proof automation based on the proof search on $\mathbf{LK}$
-/

public meta section

namespace FFL
namespace Meta

open _root_.Lean Mathlib _root_.Qq Qq Lean Elab Meta Tactic

namespace ClProver

initialize
  registerTraceClass `cl_prover

/-- The cl prover construction in `FFL.Meta.ClProver`. -/
structure Context where
  /-- The level F construction in `FFL.Meta.ClProver.Context`. -/
  levelF : Level
  /-- The level S construction in `FFL.Meta.ClProver.Context`. -/
  levelS : Level
  /-- The level E construction in `FFL.Meta.ClProver.Context`. -/
  levelE : Level
  /-- The F construction in `FFL.Meta.ClProver.Context`. -/
  F : Q(Type levelF)
  /-- The LC construction in `FFL.Meta.ClProver.Context`. -/
  LC : Q(LogicalConnective $F)
  /-- The LN construction in `FFL.Meta.ClProver.Context`. -/
  LN : Q(LogicalNeutral $F)
  /-- The S construction in `FFL.Meta.ClProver.Context`. -/
  S : Q(Type levelS)
  /-- The E construction in `FFL.Meta.ClProver.Context`. -/
  E : Q(Entailment.{_, _, levelE} $S $F)
  /-- The 𝓢 construction in `FFL.Meta.ClProver.Context`. -/
  𝓢 : Q($S)
  /-- The CL construction in `FFL.Meta.ClProver.Context`. -/
  CL : Q(Entailment.Cl $𝓢)

/-- The monad for `cl_prover` contains. -/
abbrev M :=
  ReaderT Context AtomM

/-- Apply the function
  `n : ∀ {F} [LogicalConnective F] [LogicalNeutral F] {S} [Entailment S F] {𝓢} [Entailment.Cl
  𝓢], _` to the
implicit parameters in the context, and the given list of arguments. -/
def Context.app (c : Context) (n : Name) : Array Expr → Expr :=
  mkAppN <|
    mkAppN (Expr.const n [c.levelF, c.levelS, c.levelE]) #[c.F, c.LC, c.LN, c.S, c.E, c.𝓢, c.CL]

/-- The iapp construction in `FFL.Meta.ClProver`. -/
def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app n xs

/-- The get Goal Two Sided construction in `FFL.Meta.ClProver`. -/
def getGoalTwoSided (e : Q(Prop)) : MetaM ((c : Context) × List Q($c.F) × List Q($c.F)) := do
  let ~q(@Entailment.TwoSided $F $LC $LN $S $E $𝓢 $p $q) := e | throwError
      m!"(getGoal) error: {e} not a form of _ ⊢ _"
  let .some CL ← trySynthInstanceQ q(Entailment.Cl $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  let Γ ← Qq.ofQList p
  let Δ ← Qq.ofQList q
  return ⟨⟨_, _, _, F, LC, LN, S, E, 𝓢, CL⟩, Γ, Δ⟩







/-- The get Goal Provable construction in `FFL.Meta.ClProver`. -/
def getGoalProvable (e : Q(Prop)) : MetaM ((c : Context) × Q($c.F)) := do
  let ~q(@Entailment.Provable $F $S $E $𝓢 $p) := e | throwError
      m!"(getGoal) error: {e} not a form of _ ⊢ _"
  let .some LC ← trySynthInstanceQ q(LogicalConnective $F)
    | throwError m! "error: failed to find instance LogicalConnective {F}"
  let .some LN ← trySynthInstanceQ q(LogicalNeutral $F)
    | throwError m! "error: failed to find instance LogicalNeutral {F}"
  let .some CL ← trySynthInstanceQ q(Entailment.Cl $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  return ⟨⟨_, _, _, F, LC, LN, S, E, 𝓢, CL⟩, p⟩







/-- The Sequent construction in `FFL.Meta.ClProver`. -/
abbrev Sequent :=
  List Lit

/-- The lit To Expr construction in `FFL.Meta.ClProver`. -/
def litToExpr (φ : Lit) : M Expr := do
  let c ← read
  return Litform.toExpr c.LC c.LN φ

/-- The expr To Lit construction in `FFL.Meta.ClProver`. -/
def exprToLit (e : Expr) : M Lit := do
  let c ← read
  Litform.denote c.LC c.LN e

/-- The to Expr List construction in `FFL.Meta.ClProver.Sequent`. -/
def Sequent.toExprList (Γ : Sequent) : M (List Expr) := do
  let c ← read
  return Γ.map (Litform.toExpr c.LC c.LN)

/-- The expr List To Lit List construction in `FFL.Meta.ClProver`. -/
def exprListToLitList (l : List Expr) : M (List Lit) := do
  let c ← read
  l.mapM (m := MetaM) (Litform.denote c.LC c.LN)

/-- The to Expr construction in `FFL.Meta.ClProver.Sequent`. -/
def Sequent.toExpr (Γ : Sequent) : M Expr := do
  let c ← read
  return toQList <| Γ.map (Litform.toExpr c.LC c.LN)

/-- The try Right Close construction in `FFL.Meta.ClProver`. -/
def tryRightClose (φ : Lit) (Γ Δ : Sequent) : M (Option Expr) := do
  match ← memQListOptional' (← litToExpr φ) (← Γ.toExprList) with
  | .none =>
    return none
  | .some e =>
    do
      let eΓ ← Sequent.toExpr Γ
      let eΔ ← Sequent.toExpr Δ
      let eφ ← litToExpr φ
      return some (← iapp ``FFL.Meta.ClProver.Theorems.right_closed #[eΓ, eΔ, eφ, e])

/-- The try Left Close construction in `FFL.Meta.ClProver`. -/
def tryLeftClose (φ : Lit) (Γ Δ : Sequent) : M (Option Expr) := do
  match ← memQListOptional' (← litToExpr φ) (← Δ.toExprList) with
  | .none =>
    return none
  | .some e =>
    do
      let eΓ ← Sequent.toExpr Γ
      let eΔ ← Sequent.toExpr Δ
      let eφ ← litToExpr φ
      return some (← iapp ``FFL.Meta.ClProver.Theorems.left_closed #[eΓ, eΔ, eφ, e])

/-- The rotate Right construction in `FFL.Meta.ClProver`. -/
def rotateRight (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``FFL.Meta.ClProver.Theorems.rotate_right #[eΓ, eΔ, eφ, e]

/-- The rotate Left construction in `FFL.Meta.ClProver`. -/
def rotateLeft (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``FFL.Meta.ClProver.Theorems.rotate_left #[eΓ, eΔ, eφ, e]

/-- The verum Right construction in `FFL.Meta.ClProver`. -/
def verumRight (Γ Δ : Sequent) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.ClProver.Theorems.verum_right #[eΓ, eΔ]

/-- The falsum Right construction in `FFL.Meta.ClProver`. -/
def falsumRight (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.ClProver.Theorems.falsum_right #[eΓ, eΔ, e]

/-- The and Right construction in `FFL.Meta.ClProver`. -/
def andRight (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``FFL.Meta.ClProver.Theorems.and_right #[eΓ, eΔ, eφ, eψ, e₁, e₂]

/-- The or Right construction in `FFL.Meta.ClProver`. -/
def orRight (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``FFL.Meta.ClProver.Theorems.or_right #[eΓ, eΔ, eφ, eψ, e]

/-- The neg Right construction in `FFL.Meta.ClProver`. -/
def negRight (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``FFL.Meta.ClProver.Theorems.neg_right #[eΓ, eΔ, eφ, e]

/-- The imply Right construction in `FFL.Meta.ClProver`. -/
def implyRight (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``FFL.Meta.ClProver.Theorems.imply_right #[eΓ, eΔ, eφ, eψ, e]

/-- The iff Right construction in `FFL.Meta.ClProver`. -/
def iffRight (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``FFL.Meta.ClProver.Theorems.iff_right #[eΓ, eΔ, eφ, eψ, e₁, e₂]

/-- The verum Left construction in `FFL.Meta.ClProver`. -/
def verumLeft (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.ClProver.Theorems.verum_left #[eΓ, eΔ, e]

/-- The falsum Left construction in `FFL.Meta.ClProver`. -/
def falsumLeft (Γ Δ : Sequent) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``FFL.Meta.ClProver.Theorems.falsum_left #[eΓ, eΔ]

/-- The and Left construction in `FFL.Meta.ClProver`. -/
def andLeft (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``FFL.Meta.ClProver.Theorems.and_left #[eΓ, eΔ, eφ, eψ, e]

/-- The or Left construction in `FFL.Meta.ClProver`. -/
def orLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``FFL.Meta.ClProver.Theorems.or_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

/-- The neg Left construction in `FFL.Meta.ClProver`. -/
def negLeft (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``FFL.Meta.ClProver.Theorems.neg_left #[eΓ, eΔ, eφ, e]

/-- The imply Left construction in `FFL.Meta.ClProver`. -/
def implyLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``FFL.Meta.ClProver.Theorems.imply_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

/-- The iff Left construction in `FFL.Meta.ClProver`. -/
def iffLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``FFL.Meta.ClProver.Theorems.iff_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

/-- The to Provable construction in `FFL.Meta.ClProver`. -/
def toProvable (φ : Expr) (e : Expr) : M Expr := do
  iapp ``FFL.Meta.ClProver.Theorems.to_provable #[φ, e]

/-- The prover construction in `FFL.Meta.ClProver`. -/
def prover (k : ℕ) (b : Bool) (Γ Δ : Sequent) : M Expr := do
  --logInfo m!"step: {k}, case: {b}, {← Sequent.toExpr Γ} ⟹ {← Sequent.toExpr Δ}"
  match k, b with
  |     0,      _ => throwError m!"Proof search failed: {← Sequent.toExpr Γ} ⟹ {← Sequent.toExpr Δ}"
  | k + 1,  false =>
    match Δ with
    |     [] => prover k true Γ []
    | φ :: Δ => do
      let e ← tryRightClose φ Γ Δ
      match e with
      | some h => return h
      |   none =>
        match φ with
        | .atom a =>
          let e ← prover k true Γ (Δ ++ [.atom a])
          rotateRight Γ Δ (.atom a) e
        | ⊤ => verumRight Γ Δ
        | ⊥ => do
          let e ← prover k true Γ Δ
          falsumRight Γ Δ e
        | φ ⋏ ψ => do
          let e₁ ← prover k true Γ (Δ ++ [φ])
          let e₂ ← prover k true Γ (Δ ++ [ψ])
          andRight Γ Δ φ ψ e₁ e₂
        | φ ⋎ ψ => do
          let e ← prover k true Γ (Δ ++ [φ, ψ])
          orRight Γ Δ φ ψ e
        | ∼φ => do
          let e ← prover k true (Γ ++ [φ]) Δ
          negRight Γ Δ φ e
        | φ ⇒ₗ ψ => do
          let e ← prover k true (Γ ++ [φ]) (Δ ++ [ψ])
          implyRight Γ Δ φ ψ e
        | .iff φ ψ => do
          let e₁ ← prover k true (Γ ++ [φ]) (Δ ++ [ψ])
          let e₂ ← prover k true (Γ ++ [ψ]) (Δ ++ [φ])
          iffRight Γ Δ φ ψ e₁ e₂
  | k + 1, true =>
    match Γ with
    |     [] => prover k false [] Δ
    | φ :: Γ => do
      let e ← tryLeftClose φ Γ Δ
      match e with
      | some h => return h
      |   none =>
        match φ with
        | .atom a =>
          let e ← prover k false (Γ ++ [.atom a]) Δ
          rotateLeft Γ Δ (.atom a) e
        | ⊤ => do
          let e ← prover k false Γ Δ
          verumLeft Γ Δ e
        | ⊥ => do
          falsumLeft Γ Δ
        | φ ⋏ ψ => do
          let e ← prover k false (Γ ++ [φ, ψ]) Δ
          andLeft Γ Δ φ ψ e
        | φ ⋎ ψ => do
          let e₁ ← prover k false (Γ ++ [φ]) Δ
          let e₂ ← prover k false (Γ ++ [ψ]) Δ
          orLeft Γ Δ φ ψ e₁ e₂
        | ∼φ => do
          let e ← prover k false Γ (Δ ++ [φ])
          negLeft Γ Δ φ e
        | φ ⇒ₗ ψ => do
          let e₁ ← prover k false Γ (Δ ++ [φ])
          let e₂ ← prover k false (Γ ++ [ψ]) Δ
          implyLeft Γ Δ φ ψ e₁ e₂
        | .iff φ ψ => do
          let e₁ ← prover k false Γ (Δ ++ [φ, ψ])
          let e₂ ← prover k false (Γ ++ [φ, ψ]) Δ
          iffLeft Γ Δ φ ψ e₁ e₂



/-- Data and laws for Hyp Info in `FFL.Meta.ClProver`. -/
structure HypInfo where
  /-- The level F construction in `FFL.Meta.ClProver.HypInfo`. -/
  levelF : Level
  /-- The level S construction in `FFL.Meta.ClProver.HypInfo`. -/
  levelS : Level
  /-- The level E construction in `FFL.Meta.ClProver.HypInfo`. -/
  levelE : Level
  /-- The F construction in `FFL.Meta.ClProver.HypInfo`. -/
  F : Q(Type levelF)
  /-- The S construction in `FFL.Meta.ClProver.HypInfo`. -/
  S : Q(Type levelS)
  /-- The E construction in `FFL.Meta.ClProver.HypInfo`. -/
  E : Q(Entailment.{_, _, levelE} $S $F)
  /-- The 𝓢 construction in `FFL.Meta.ClProver.HypInfo`. -/
  𝓢 : Q($S)
  /-- The φ construction in `FFL.Meta.ClProver.HypInfo`. -/
  φ : Q($F)
  /-- The proof construction in `FFL.Meta.ClProver.HypInfo`. -/
  proof : Q($𝓢 ⊢ $φ)







/-- The synth Provable construction in `FFL.Meta.ClProver`. -/
def synthProvable (e : Expr) : MetaM HypInfo := do
  let (ty : Q(Prop)) ← inferType e
  let ~q(@Entailment.Provable $F $S $E $𝓢 $φ) := ty | throwError
      m!"(getGoal) error: {e} not a form of _ ⊢ _"
  return ⟨_, _, _, F, S, E, 𝓢, φ, e⟩







/-- Data and laws for Compatible Hyp Info in `FFL.Meta.ClProver`. -/
structure CompatibleHypInfo where
  /-- The 𝓢 construction in `FFL.Meta.ClProver.CompatibleHypInfo`. -/
  𝓢 : Expr
  /-- The WT construction in `FFL.Meta.ClProver.CompatibleHypInfo`. -/
  WT : Expr
  /-- The φ construction in `FFL.Meta.ClProver.CompatibleHypInfo`. -/
  φ : Lit
  /-- The proof construction in `FFL.Meta.ClProver.CompatibleHypInfo`. -/
  proof : Expr

/-- The to Compatible construction in `FFL.Meta.ClProver.HypInfo`. -/
def HypInfo.toCompatible (h : HypInfo) : M CompatibleHypInfo := do
  let c ← read
  if (← isDefEq (← whnf h.F) (← whnf c.F)) && (← isDefEq (← whnf h.S) (← whnf c.S)) && (←
      isDefEq (← whnf h.E) (← whnf c.E)) then
    let e := @Expr.const ``FFL.Entailment.WeakerThan [c.levelF, c.levelS, c.levelS, c.levelE,
        c.levelE]
      |>.app c.F |>.app c.S |>.app c.S |>.app c.E |>.app c.E |>.app h.𝓢 |>.app c.𝓢
    let .some wt ← trySynthInstance e
      | throwError m! "error: failed to find instance {e}"
    return ⟨h.𝓢, wt, ← exprToLit h.φ, h.proof⟩
  else throwError m! "error: proof not compatible: {h.proof}"







/-- The add Hyp construction in `FFL.Meta.ClProver`. -/
def addHyp (𝓣 wt : Expr) (Γ Δ : Sequent) (φ : Lit) (E e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``FFL.Meta.ClProver.Theorems.add_hyp #[𝓣, wt, eΓ, eΔ, eφ, E, e]

/-- The add Hyps construction in `FFL.Meta.ClProver`. -/
def addHyps (prover : (Γ Δ : Sequent) → M Expr) (Γ Δ : Sequent) : List HypInfo → M Expr
  | [] => prover Γ Δ
  | h :: hyps => do
    let H ← h.toCompatible
    addHyp H.𝓢 H.WT Γ Δ H.φ H.proof <| ← addHyps prover (H.φ :: Γ) Δ hyps

/-- The main construction in `FFL.Meta.ClProver`. -/
def main (n : ℕ) (hyps : Array HypInfo) (L R : List Expr) : M Expr := do
  let Γ ← exprListToLitList L
  let Δ ← exprListToLitList R
  addHyps (prover n false) Γ Δ hyps.toList

/-- The term Seq construction in `FFL.Meta.ClProver`. -/
syntax termSeq := "["(term,*)"]"

/-- Prove a two-sided classical sequent, optionally supplying a search depth and hypotheses. -/
elab "cl_prover_2s" n:(num)? seq:(termSeq)? : tactic => withMainContext do
  let ⟨c, L, R⟩ ← getGoalTwoSided <| ← whnfR <| ← getMainTarget
  let n : ℕ :=
    match n with
    | some n => n.getNat
    |   none => 32
  let hyps ← (match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do
        ss.getElems.mapM fun s ↦ do synthProvable (← Term.elabTerm s none true)
      | _                      =>
        return #[]
    | _        =>
      return #[])
  closeMainGoal `cl_prover <| ← AtomM.run .reducible <| ReaderT.run (main n hyps L R) c







/-- Prove a classical entailment, optionally supplying a search depth and hypotheses. -/
elab "cl_prover" n:(num)? seq:(termSeq)? : tactic => withMainContext do
  let ⟨c, φ⟩ ← getGoalProvable <| ← whnfR <| ← getMainTarget
  let n : ℕ :=
    match n with
    | some n => n.getNat
    |   none => 32
  let hyps ← (match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do
        ss.getElems.mapM fun s ↦ do synthProvable (← Term.elabTerm s none true)
      | _                      =>
        return #[]
    | _        =>
      return #[])
  closeMainGoal `cl_prover <| ← AtomM.run .reducible <| ReaderT.run (r := c) do
    let e ← main n hyps [] [φ]
    toProvable φ e







end ClProver

end Meta
end FFL

end

end PointwiseComposition
