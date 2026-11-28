/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import Init

/-!
  Multiple Context-Free Grammars / Linear Context-Free Rewriting Systems
  (Seki, Matsumura, Fujii & Kasami 1991; Vijay-Shanker, Weir & Joshi 1987)

  A linear, non-erasing MCFG (LCFRS) over nonterminals `N` and terminals `T`
  assigns each nonterminal `A : N` a positive dimension `dim A ≥ 1` (with `dim start = 1`),
  and each rule builds a `dim A`-tuple of strings linearly and non-erasingly from
  the string tuples of its RHS nonterminals plus literal terminals.
-/

@[expose] public section

namespace FormalLinguistics

/-- An atom inside an MCFG yield component: either a literal terminal or
    a variable `(argIdx, compIdx)` referencing component `compIdx` of RHS nonterminal `argIdx`. -/
inductive MCFGAtom (T : Type) where
  | tm : T → MCFGAtom T
  | var : Nat → Nat → MCFGAtom T
  deriving DecidableEq, Repr

/-- An MCFG production rule:
    `lhs` derives `rhs` via the tuple of component templates `yield`. -/
structure MCFGRule (N T : Type) where
  /-- Nonterminal produced by the rule. -/
  lhs : N
  /-- Ordered argument nonterminals whose yields feed the rule. -/
  rhs : List N
  /-- Output component templates, referring to argument components by position. -/
  yield : List (List (MCFGAtom T))
  deriving DecidableEq, Repr

namespace MCFGRule

variable {N T : Type}

/-- All variable occurrences `(argIdx, compIdx)` appearing across all components of `r.yield`. -/
def varOccurrences (r : MCFGRule N T) : List (Nat × Nat) :=
  r.yield.flatMap fun comp =>
    comp.filterMap fun
      | MCFGAtom.tm _ => none
      | MCFGAtom.var i j => some (i, j)

/-- Expected list of all input variable coordinates `(i, j)` for `r.rhs` under `dim`. -/
def expectedVars (dim : N → Nat) (rhs : List N) : List (Nat × Nat) :=
  (List.range rhs.length).flatMap fun i =>
    match rhs[i]? with
    | none => []
    | some B => (List.range (dim B)).map fun j => (i, j)

/-- A rule is **linear** if no variable coordinate `(i, j)` appears more than once. -/
def isLinear (r : MCFGRule N T) : Prop :=
  r.varOccurrences.Nodup

/-- A rule is **non-erasing** (and well-scoped) if every input coordinate `(i, j)`
    with `i < r.rhs.length` and `j < dim (r.rhs[i])` appears in `r.yield`, and vice versa. -/
def isNonErasing (dim : N → Nat) (r : MCFGRule N T) : Prop :=
  ∀ i j, (i, j) ∈ r.varOccurrences ↔
    ∃ B, r.rhs[i]? = some B ∧ j < dim B

/-- Full well-formedness of an LCFRS / linear non-erasing MCFG rule:
    correct output arity, linearity, and non-erasing variable bijection. -/
def WellFormed (dim : N → Nat) (r : MCFGRule N T) : Prop :=
  r.yield.length = dim r.lhs ∧ r.isLinear ∧ r.isNonErasing dim

end MCFGRule

/-- A finite Linear Non-Erasing Multiple Context-Free Grammar (LCFRS / MCFG). -/
structure MCFG (N T : Type) where
  /-- Arity-one start nonterminal. -/
  start : N
  /-- Number of string components yielded by each nonterminal. -/
  dim : N → Nat
  dim_pos : ∀ A, 1 ≤ dim A
  dim_start : dim start = 1
  /-- List of linear, non-erasing productions. -/
  rules : List (MCFGRule N T)
  rules_wf : ∀ r, r ∈ rules → r.WellFormed dim

namespace MCFG

variable {N T : Type}

/-- Evaluate a single component template `comp` given the list of RHS string tuples `args`. -/
def evalComp (args : List (List (List T))) : List (MCFGAtom T) → List T
  | [] => []
  | MCFGAtom.tm a :: rest => a :: evalComp args rest
  | MCFGAtom.var i j :: rest =>
      let piece :=
        match args[i]? with
        | some tup =>
            match tup[j]? with
            | some s => s
            | none => []
        | none => []
      piece ++ evalComp args rest

/-- Evaluate all output components of an MCFG rule on `args`. -/
def evalYield (args : List (List (List T))) (yield : List (List (MCFGAtom T))) : List (List T) :=
  yield.map (evalComp args)

theorem evalComp_append (args : List (List (List T))) (c1 c2 : List (MCFGAtom T)) :
    evalComp args (c1 ++ c2) = evalComp args c1 ++ evalComp args c2 := by
  induction c1 with
  | nil => simp [evalComp]
  | cons a t ih =>
    cases a with
    | tm x => simp [evalComp, ih]
    | var i j => simp [evalComp, ih, List.append_assoc]

theorem evalYield_length (args : List (List (List T))) (yield : List (List (MCFGAtom T))) :
    (evalYield args yield).length = yield.length := by
  simp [evalYield]

/- Structural tuple derivations for an MCFG (mutually inductive for single nonterminals and RHS lists). -/
mutual
  /-- A derivation of a tuple of words from one nonterminal. -/
  inductive Yield (G : MCFG N T) : N → List (List T) → Prop where
    | rule {r : MCFGRule N T} {args : List (List (List T))} :
        r ∈ G.rules →
        YieldList G r.rhs args →
        Yield G r.lhs (evalYield args r.yield)

  /-- Simultaneous derivations of the tuples for a rule’s argument nonterminals. -/
  inductive YieldList (G : MCFG N T) : List N → List (List (List T)) → Prop where
    | nil : YieldList G [] []
    | cons {B : N} {Bs : List N} {tup : List (List T)} {tups : List (List (List T))} :
        Yield G B tup →
        YieldList G Bs tups →
        YieldList G (B :: Bs) (tup :: tups)
end

/-- Every tuple yielded by nonterminal `A` has length `G.dim A`. -/
theorem Yield.length_eq {G : MCFG N T} {A : N} {tup : List (List T)}
    (h : Yield G A tup) : tup.length = G.dim A := by
  cases h with
  | rule hr _ =>
    rw [evalYield_length]
    exact (G.rules_wf _ hr).1

/-- The string language generated by an MCFG (`start` has dimension 1). -/
def Lang (G : MCFG N T) (w : List T) : Prop :=
  Yield G G.start [w]

theorem YieldList.length_eq {G : MCFG N T} {Bs : List N} {args : List (List (List T))} :
    YieldList G Bs args → args.length = Bs.length
  | YieldList.nil => rfl
  | YieldList.cons _ rest => by simp [YieldList.length_eq rest]

theorem YieldList.getElem?_some {G : MCFG N T} {Bs : List N} {args : List (List (List T))} :
    YieldList G Bs args →
    ∀ (i : Nat) (B : N), Bs[i]? = some B → ∃ tup, args[i]? = some tup ∧ Yield G B tup
  | YieldList.nil, _, _, h => by simp at h
  | YieldList.cons hy hrest, 0, B, h => by
      simp at h; subst h
      exact ⟨_, rfl, hy⟩
  | YieldList.cons _ hrest, i + 1, B, h =>
      YieldList.getElem?_some hrest i B (by simpa using h)

theorem YieldList.append {G : MCFG N T} {Bs1 Bs2 : List N}
    {args1 args2 : List (List (List T))} :
    YieldList G Bs1 args1 → YieldList G Bs2 args2 →
    YieldList G (Bs1 ++ Bs2) (args1 ++ args2)
  | YieldList.nil, h2 => by simpa using h2
  | YieldList.cons hy h1, h2 => YieldList.cons hy (YieldList.append h1 h2)

end MCFG
end FormalLinguistics
