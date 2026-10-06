/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ExactLiteralTrial.NFChoiceExactLiteral

/-! NF weak partition development: NominalCertificate. -/


public section

namespace NFChoice.DirectCertificate.Nominal

variable {Var Atom : Type}

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial

/-! A direct Flypitch executor for named-variable Metamath certificates.  Proofs
are polymorphic in the assignment of source names to free de Bruijn indices.
Consequently `ax-gen` can bind one source name without choosing a global
variable numbering or copying a proof term.

The exact repaired-source trace sidecar has SHA-256
`89E80799B18269313FED986238AAEEEB1BE0DBAD2D7F28C3469521701A837E80`.
-/


/-- Proof-translation construction identified upstream as `sourceMmSha256`. -/
@[expose]
def sourceMmSha256 : String :=
  "868DF831E63E28AA924CC099510CD9E5D3BE18CD8416A20B335F5BBF3B42ED3F"

/-- Proof-translation construction identified upstream as `exactSliceSha256`. -/
@[expose]
def exactSliceSha256 : String :=
  "89E80799B18269313FED986238AAEEEB1BE0DBAD2D7F28C3469521701A837E80"

/-- A small nominal source AST sufficient for the exact quantified slice. -/
inductive Code (Var Atom : Type) where
  | atom : Atom → Code Var Atom
  | falsum : Code Var Atom
  | equal : Var → Var → Code Var Atom
  | imp : Code Var Atom → Code Var Atom → Code Var Atom
  | all : Var → Code Var Atom → Code Var Atom
  deriving DecidableEq, Repr

/-- Assignment used below a binder: the bound name becomes index zero. -/
@[expose]
def bindRho [DecidableEq Var] (rho : Var → Nat) (bound : Var) : Var → Nat := fun name =>
  if name = bound then 0 else rho name + 1

namespace Code

/-- Compile named source syntax to Flypitch's de Bruijn formula syntax. -/
@[expose]
def lower {L : Fol.Language} [DecidableEq Var]
    (atomFormula : (Var → Nat) → Atom → Fol.formula L) :
    (Var → Nat) → Code Var Atom → Fol.formula L
  | rho, .atom a => atomFormula rho a
  | _, .falsum => Fol.preformula.falsum
  | rho, .equal x y => Fol.preformula.equal (&(rho x)) (&(rho y))
  | rho, .imp p q =>
    Fol.preformula.imp (lower atomFormula rho p) (lower atomFormula rho q)
  | rho, .all x p => Fol.preformula.all (lower atomFormula (bindRho rho x) p)

end Code

/-- A proof-valued nominal judgment over a closed sentence theory. -/
@[expose]
def NPrf {L : Fol.Language} [DecidableEq Var] (theory : Fol.SentTheory L)
    (atomFormula : (Var → Nat) → Atom → Fol.formula L) (code : Code Var Atom) : Type :=
  ∀ rho : Var → Nat, Fol.prf theory.fst (Code.lower atomFormula rho code)

/-- One shared, dependently typed proof-table entry. -/
abbrev Packed {L : Fol.Language} [DecidableEq Var] (theory : Fol.SentTheory L)
    (atomFormula : (Var → Nat) → Atom → Fol.formula L) :=
  Σ code : Code Var Atom, NPrf theory atomFormula code

/-- Proof-translation construction identified upstream as `Step`. -/
inductive Step (Var Atom : Type) where
  | input : Nat → Step Var Atom
  | ref : Var → Step Var Atom
  | ax1 : Code Var Atom → Code Var Atom → Step Var Atom
  | mp : Nat → Nat → Step Var Atom
  | gen : Var → Nat → Step Var Atom
  deriving DecidableEq, Repr

/-- Proof-translation construction identified upstream as `castNPrf`. -/
@[expose]
def castNPrf {L : Fol.Language} [DecidableEq Var] {theory : Fol.SentTheory L}
    {atomFormula : (Var → Nat) → Atom → Fol.formula L} {p q : Code Var Atom} (h : p = q)
    (proof : NPrf theory atomFormula p) : NPrf theory atomFormula q :=
  by
  cases h
  exact proof

/-- Proof-translation construction identified upstream as `execStep`. -/
@[expose]
def execStep {L : Fol.Language} [DecidableEq Var] [DecidableEq Atom]
    (theory : Fol.SentTheory L) (atomFormula : (Var → Nat) → Atom → Fol.formula L)
    (inputs : Array (Packed theory atomFormula))
    (state : Array (Packed theory atomFormula)) :
    Step Var Atom → Option (Packed theory atomFormula)
  | .input index => inputs[index]?
  | .ref x => some ⟨.equal x x, fun rho => Fol.prf.ref theory.fst (&(rho x))⟩
  | .ax1 p q =>
    some
      ⟨.imp p (.imp q p), fun rho => by
        apply Fol.prf.impI
        apply Fol.prf.impI
        apply Fol.prf.axm
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)⟩
  | .mp implication argument =>
    match state[implication]?, state[argument]? with
    | some ⟨.imp antecedent consequent, hImp⟩, some ⟨actual, hActual⟩ =>
      if h : actual = antecedent then
        let hAntecedent := castNPrf h hActual
        some
          ⟨consequent, fun rho =>
            Fol.prf.impE (Code.lower atomFormula rho antecedent) (hImp rho)
              (hAntecedent rho)⟩
      else none
    | _, _ => none
  | .gen bound input =>
    match state[input]? with
    | some ⟨body, hBody⟩ =>
      some
        ⟨.all bound body, fun rho => by
          apply Fol.prf.allI
          rw [Fol.SentTheory.lift_irrel theory]
          exact hBody (bindRho rho bound)⟩
    | none => none

/-- Execute a topologically ordered proof DAG with actual node sharing. -/
@[expose]
def run {L : Fol.Language} [DecidableEq Var] [DecidableEq Atom]
    (theory : Fol.SentTheory L) (atomFormula : (Var → Nat) → Atom → Fol.formula L)
    (inputs : Array (Packed theory atomFormula)) :
    List (Step Var Atom) →
      Array (Packed theory atomFormula) → Option (Array (Packed theory atomFormula))
  | [], state => some state
  | step :: rest, state =>
    match execStep theory atomFormula inputs state step with
    | none => none
    | some proof => run theory atomFormula inputs rest (state.push proof)

/-- Proof-translation construction identified upstream as `extract`. -/
@[expose]
def extract {L : Fol.Language} [DecidableEq Var] [DecidableEq Atom]
    (theory : Fol.SentTheory L) (atomFormula : (Var → Nat) → Atom → Fol.formula L)
    (state : Array (Packed theory atomFormula)) (index : Nat) (goal : Code Var Atom) :
    Option (NPrf theory atomFormula goal) :=
  match state[index]? with
  | none => none
  | some ⟨actual, proof⟩ => if h : actual = goal then some (castNPrf h proof) else none

/-! ### Exact real-source slices -/


/-- Proof-translation construction identified upstream as `SourceVar`. -/
inductive SourceVar
  | x
  | y
  deriving DecidableEq, Repr

/-- Proof-translation construction identified upstream as `NoAtom`. -/
inductive NoAtom
  deriving DecidableEq, Repr

/-- Proof-translation construction identified upstream as `noAtomFormula`. -/
@[expose]
def noAtomFormula (_ : SourceVar → Nat) (atom : NoAtom) : Fol.formula LNF :=
  nomatch atom

/-- Proof-translation construction identified upstream as `eqxx`. -/
abbrev eqxx : Code SourceVar NoAtom :=
  .equal .x .x
/-- Proof-translation construction identified upstream as `allEqxx`. -/
abbrev allEqxx : Code SourceVar NoAtom :=
  .all .x eqxx

/-- Exact proof-bearing `stdpc6` trace: `equid`, then `ax-gen`. -/
@[expose]
def stdpc6Certificate : List (Step SourceVar NoAtom) :=
  [.ref .x, .gen .x 0]

/-- Proof-translation construction identified upstream as `stdpc6Result`. -/
@[expose]
def stdpc6Result : Option (NPrf LiteralHailperinNF noAtomFormula allEqxx) := do
  let state ← run LiteralHailperinNF noAtomFormula #[] stdpc6Certificate #[]
  extract LiteralHailperinNF noAtomFormula state 1 allEqxx

/-- Proof-translation construction identified upstream as `stdpc6Proof`. -/
@[expose]
def stdpc6Proof : NPrf LiteralHailperinNF noAtomFormula allEqxx :=
  stdpc6Result.get (by rfl)

/-- Proof-translation construction identified upstream as `SchematicAtom`. -/
inductive SchematicAtom
  | ph
  deriving DecidableEq, Repr

/-- Proof-translation construction identified upstream as `ph`. -/
abbrev ph : Code SourceVar SchematicAtom :=
  .atom .ph
/-- Proof-translation construction identified upstream as `allYPh`. -/
abbrev allYPh : Code SourceVar SchematicAtom :=
  .all .y ph
/-- Proof-translation construction identified upstream as `allXAllYPh`. -/
abbrev allXAllYPh : Code SourceVar SchematicAtom :=
  .all .x allYPh

/-- Exact proof-bearing `gen2` trace: input hypothesis and two `ax-gen`s. -/
@[expose]
def gen2Certificate : List (Step SourceVar SchematicAtom) :=
  [.input 0, .gen .y 0, .gen .x 1]

/-- Proof-translation construction identified upstream as `gen2Result`. -/
@[expose]
def gen2Result (atomFormula : (SourceVar → Nat) → SchematicAtom → Fol.formula LNF)
    (hypothesis : NPrf LiteralHailperinNF atomFormula ph) :
    Option (NPrf LiteralHailperinNF atomFormula allXAllYPh) := do
  let inputs : Array (Packed LiteralHailperinNF atomFormula) := #[⟨ph, hypothesis⟩]
  let state ← run LiteralHailperinNF atomFormula inputs gen2Certificate #[]
  extract LiteralHailperinNF atomFormula state 2 allXAllYPh

/-- Proof-translation construction identified upstream as `gen2Proof`. -/
@[expose]
def gen2Proof (atomFormula : (SourceVar → Nat) → SchematicAtom → Fol.formula LNF)
    (hypothesis : NPrf LiteralHailperinNF atomFormula ph) :
    NPrf LiteralHailperinNF atomFormula allXAllYPh :=
  (gen2Result atomFormula hypothesis).get (by rfl)


end NFChoice.DirectCertificate.Nominal
