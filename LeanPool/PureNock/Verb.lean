/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Tree
public import LeanPool.PureNock.Reference

/-!
# Verbs and local transitions

`Def:verb`–selection (`main.tex:1034–1112`); `D`/OP (`1055–1076`);
`Def:NockProgram` (`1090–1098`); operators (`1514–1626`); `Nock` (`1639–1661`).
-/

@[expose] public section

namespace Nock

-- main.tex:1034–1040  (Def:verb — alphabet)
/-- **`Def:verb`** (`main.tex:1034–1040`).
    Alphabet `X := ⟨?,=,/,#,−⟩`; actions from `X ∪ {*,⊥}`. -/
inductive Action where
  | null    -- ⊥
  | star    -- *
  | wut     -- ?
  | equal   -- =
  | slot    -- /
  | edit    -- #
  | minus   -- -
deriving Repr, DecidableEq, Inhabited

/-- Is an action the null element `⊥`? -/
def Action.isNull : Action → Bool
  | .null => true
  | _     => false

/-- Is an action one of the operators in `X` (as opposed to `⊥` or `*`)? -/
def Action.isOperator : Action → Bool
  | .null => false
  | .star => false
  | _     => true

-- main.tex:1034–1040  (Def:verb)
/-- **`Def:verb`** (`main.tex:1034–1040`).
    `verb := (actions, noun) ∈ (X ∪ {*,⊥})^{λ−1} × N^λ(F)`; terminal iff actions all `⊥`. -/
inductive Verb where
  | leaf : Nat → Verb
  | node : Action → Verb → Verb → Verb
deriving Repr, DecidableEq, Inhabited

namespace Verb

/-- The underlying noun (`snd` of the verb pair): forget the action labels. -/
def noun : Verb → Noun
  | .leaf n     => .atom n
  | .node _ l r => .cell l.noun r.noun

/-- Number of leaves `λ` of the verb's noun. -/
def leaves : Verb → Nat
  | .leaf _     => 1
  | .node _ l r => l.leaves + r.leaves

/-- `type` (main.tex:1045): is the underlying noun a cell? -/
def isCell : Verb → Bool
  | .node _ _ _ => true
  | .leaf _     => false

/-- Root action, if the verb is a cell (`none` at a leaf — leaves carry no action). -/
def rootAction : Verb → Option Action
  | .node a _ _ => some a
  | .leaf _     => none

/-- Is the root action a pending `*`? -/
def isStar : Verb → Bool
  | .node .star _ _ => true
  | _               => false

/-- Does the root node carry a *pending* (non-`⊥`) action?  `*` or any operator counts;
    a leaf or a `⊥`-node does not. -/
def isPending : Verb → Bool
  | .node a _ _ => !a.isNull
  | .leaf _     => false

-- main.tex:1039  (Def:verb — terminal clause)
/-- **`Def:verb`** (`main.tex:1039`).
    `verb` is (fully) executed or in terminal state if its `actions` array consists only of `⊥`. -/
def isTerminal : Verb → Bool
  | .leaf _     => true
  | .node a l r => a.isNull && isTerminal l && isTerminal r

/-! ### Selection (`main.tex:1103–1112`) -/

-- main.tex:1103  (DFS enumeration of internal nodes)
/-- **Selection** (`main.tex:1103–1112`).
    `map := DFS`; index of each internal node is the order a DFS from the root first explores
    it, excluding leaves. -/
def enum : Verb → Nat → Nat × List (Nat × Verb)
  | .leaf _,     c => (c, [])
  | .node a l r, c =>
      let e1 := enum l (c + 1)
      let e2 := enum r e1.1
      (e2.1, (c, .node a l r) :: (e1.2 ++ e2.2))

/-- All `(index, subverb)` pairs of internal nodes, in DFS pre-order. -/
def nodes (v : Verb) : List (Nat × Verb) := (enum v 0).2

/-- Find the verb at an index in a list of enumerated internal nodes. -/
def findAt : Nat → List (Nat × Verb) → Option Verb
  | _, []          => none
  | i, (j, v) :: t => if i = j then some v else findAt i t

-- main.tex:1103  (`map := DFS`)
/-- **Selection** (`main.tex:1103–1112`).
    `map := DFS`: returns the verb at internal-node index `i ∈ [λ−1]`. -/
def map (i : Nat) (v : Verb) : Option Verb := findAt i (nodes v)

/-- Greatest index of a pending verb in an enumerated list of internal nodes. -/
def maximumPendingIndex : List (Nat × Verb) → Option Nat
  | []          => none
  | (i, v) :: t =>
      let rest := maximumPendingIndex t
      if v.isPending then
        some (match rest with | none => i | some j => Nat.max i j)
      else rest

-- main.tex:1109–1112  (`getIndex^Λ(F) = argmax …`; `F₁ >_F F₂ ⇔ i₁ > i₂`)
/-- **Selection** (`main.tex:1103–1112`).
    `getIndex^Λ(F) = argmax_{map(i,F) ∈ NockProgram^Λ}(map(i,F))`; `F₁ >_F F₂ ⇔ i₁ > i₂`. -/
def getIndex (v : Verb) : Option Nat := maximumPendingIndex (nodes v)

/-- Rebuild `v`, replacing the internal node at DFS index `i` by `new`. -/
def replaceAux (i : Nat) (new : Verb) : Verb → Nat → Nat × Verb
  | .leaf n,     c => (c, .leaf n)
  | .node a l r, c =>
      let e1 := replaceAux i new l (c + 1)
      let e2 := replaceAux i new r e1.1
      (e2.1, if c = i then new else .node a e1.2 e2.2)

/-- Splice: replace the subverb at DFS index `i` with `new`. -/
def replaceAt (i : Nat) (v new : Verb) : Verb := (replaceAux i new v 0).2

/-! ### Computable opcode domain `D` (`main.tex:1055–1083`) -/

/-- `type(i) = atom ∧ i ∈ [11]`, or `type(i) = cell` (⇒ the `cons` opcode). -/
def opHeadOk : Verb → Bool
  | .leaf k     => k < 11
  | .node _ _ _ => true

-- main.tex:1055–1058, 1078–1083  (computable opcode domain `D`)
/-- **`Algorithm:Opcode_Updates_verb`** domain `D` (`main.tex:1055–1058`, `1078–1083`).
    `D := {v := (a,n) | n := [n₁,[i,n₂]], (i∈[11]) ∪ (type(i)=cell), a₁=⟨*⟩, ∀j≠1 aⱼ=⟨⊥⟩}`;
    (1) `v := *[n₁,[i,n₂]]`; (2) `n₁,[i,n₂]` terminal; (3) `i` atom in `[11]` or cell. -/
def inOpcodeDomain : Verb → Bool
  | .node .star n1 (.node ra i n2) =>
      isTerminal n1
        && ra.isNull
        && isTerminal i && isTerminal n2 && opHeadOk i
  | _ => false

/-- A node ready for an **operator-application step**: it carries an operator from `X`
    and both of its argument subtrees are already in terminal state (note 2b).  These are
    the operator redexes that the paper's App A transition algorithm elides. -/
def opReady : Verb → Bool
  | .node a l r => a.isOperator && isTerminal l && isTerminal r
  | .leaf _     => false

/-- The full domain of the transition function `next`: opcode redexes (`inOpcodeDomain`,
    = the paper's `D`) together with ready operator nodes (`opReady`).  See note 2c;
    `Trace.domain` (`Lem:domain`) concludes membership here. -/
def inDomain (v : Verb) : Bool := inOpcodeDomain v || opReady v

/-! ### Opcode local rewrite (`main.tex:1060–1076`) -/
-- main.tex:1060–1076  (Algorithm:Opcode_Updates_verb)
/-- **`Algorithm:Opcode_Updates_verb`** (`main.tex:1060–1076`).
    `OP₀: *[n₁,[0,n₂]] → /(n₂,n₁)`; `OP₁ → n₂`; `OP₂ → *[*[n₁,h],*[n₁,t]]`;
    `OP₃ → -[3,*[n₁,n₂]]`; `OP₄ → -[4,*[n₁,n₂]]`; `OP₅ → =(*[n₁,h],*[n₁,t])`;
    `OP₆ → *[n₁,*[t,[0,*[[2,3],[0,*[n₁,[4,[4,h]]]]]]]]`; `OP₇ → *[*[n₁,h],t]`;
    `OP₈ → *[[*[n₁,h],n₁],t]`; `OP₉ → *[*[n₁,t],2,[[0,1],0,h]]`;
    `OP₁₀ → #[hh,*[n₁,th],*[n₁,t]]`; `cons: *[n₁,[i,n₂]] → [*[n₁,i],*[n₁,n₂]]`. -/
def redex : Verb → Option Verb
  | .node .star n1 (.node _ i n2) =>
      match i with
      | .node _ _ _ =>                                  -- main.tex:1075  cons (type(i)=cell)
          some (.node .null (.node .star n1 i) (.node .star n1 n2))
      | .leaf op =>
          match op with
          | 0 =>                                        -- main.tex:1061  OP₀ : → /(n₂,n₁)
              some (.node .slot n2 n1)
          | 1 => some n2                                -- main.tex:1062  OP₁ : → n₂
          | 2 => match n2 with                          -- main.tex:1063  OP₂ : → *[*[n₁,h],*[n₁,t]]
                 | .node _ b c =>
                     some (.node .star (.node .star n1 b) (.node .star n1 c))
                 | _ => none
          | 3 =>                                        -- main.tex:1064  OP₃ : → -[3, *[n₁,n₂]] =
            -- ?(*[n₁,n₂])
              some (.node .minus (.leaf 3) (.node .star n1 n2))
          | 4 =>                                        -- main.tex:1065  OP₄ : → -[4, *[n₁,n₂]] =
            -- +(*[n₁,n₂])
              some (.node .minus (.leaf 4) (.node .star n1 n2))
          | 5 => match n2 with                          -- main.tex:1066  OP₅ : → =(*[n₁,h],*[n₁,t])
                 | .node _ b c =>
                     some (.node .equal (.node .star n1 b) (.node .star n1 c))
                 | _ => none
          | 6 => match n2 with                          -- main.tex:1067  OP₆ (if-then-else macro)
                 | .node _ b c =>
                     -- b = head(n₂), c = tail(n₂);
                     -- → *[n₁, *[c, [0, *[[2,3], [0, *[n₁,[4,[4,b]]]]]]]]
                     let inner := Verb.node .star n1
                                    (.node .null (.leaf 4) (.node .null (.leaf 4) b))
                     let d0    := Verb.node .null (.leaf 0) inner
                     let c0    := Verb.node .star (.node .null (.leaf 2) (.leaf 3)) d0
                     let b0    := Verb.node .null (.leaf 0) c0
                     let a0    := Verb.node .star c b0
                     some (.node .star n1 a0)
                 | _ => none
          | 7 => match n2 with                          -- main.tex:1068  OP₇ : → *[*[n₁,h],t]
                 | .node _ b c => some (.node .star (.node .star n1 b) c)
                 | _ => none
          | 8 => match n2 with                          -- main.tex:1069  OP₈ : → *[[*[n₁,h],n₁],t]
                 | .node _ b c =>
                     some (.node .star (.node .null (.node .star n1 b) n1) c)
                 | _ => none
          | 9 => match n2 with                          -- main.tex:1070  OP₉ : → *[*[n₁,t], 2,
            -- [[0,1],0,h]]
                 | .node _ b c =>
                     -- b = head(n₂), c = tail(n₂)
                     let core := Verb.node .star n1 c
                     let f01  := Verb.node .null (.leaf 0) (.leaf 1)
                     let f0h  := Verb.node .null (.leaf 0) b
                     let form := Verb.node .null (.leaf 2) (.node .null f01 f0h)
                     some (.node .star core form)
                 | _ => none
          | 10 => match n2 with                         -- main.tex:1071  OP₁₀ : → #[hh(n₂),
            -- *[n₁,th(n₂)], *[n₁,t(n₂)]]
                  | .node _ hd d =>
                      match hd with
                      | .node _ ax c =>
                          some (.node .edit ax
                                  (.node .null (.node .star n1 c) (.node .star n1 d)))
                      | _ => none
                  | _ => none
          | _ => none                                   -- i ∉ [11] ⇒ crash
  | _ => none

/-! ### Operator-application steps (`Algorithm:Noun_Operators` / `Unroll_Operator`) -/

/-- Convert a plain noun into a *terminal* verb (all actions `⊥`). -/
def ofNoun : Noun → Verb
  | .atom k   => .leaf k
  | .cell l r => .node .null (ofNoun l) (ofNoun r)

/-! ### Local rewrite (`main.tex:1060–1076`, `1514–1626`) -/

-- main.tex:1514–1626  (Algorithm:Noun_Operators / Unroll_Operator; opcodes via redex)
/-- **`Algorithm:Noun_Operators`** / **`Unroll_Operator`** (`main.tex:1514–1626`).
    Local rewrite: `*` via opcodes, or `=`, `/`, `#`, `-` (`-[3,·]=?`, `-[4,·]=+`) on terminal
    args. -/
def reduce : Verb → Option Verb
  | .node .star n1 t     => redex (.node .star n1 t)                    -- opcode step
  | .node .equal l r     => some (ofNoun (Noun.tis l.noun r.noun))      -- main.tex:1525  =
  | .node .slot l r      =>                                             -- main.tex:1537  /
      match l.noun with
      | .atom ax => (Noun.slot ax r.noun).map ofNoun
      | _        => none
  | .node .edit l r      =>                                             -- main.tex:1587  #
      match l.noun, r with
      | .atom ax, .node _ nw od => (Noun.edit ax nw.noun od.noun).map ofNoun
      | _,        _             => none
  | .node .minus l r     =>                                             -- main.tex:1618  -
      match l.noun with
      | .atom 3 => some (ofNoun (Noun.wut r.noun))                      --   -[3,·] = ?(·)
      | .atom 4 => (Noun.lus r.noun).map ofNoun                         --   -[4,·] = +(·)
      | _       => none
  | .node .wut _ _       => none                                        -- unreachable, see note 2a
  | .node .null _ _      => none
  | .leaf _              => none

-- main.tex:1052, 1109  (`* : V → V ∪ {⊥}`, driving the next redex chosen by `getIndex`)
/-- One Nock step.  Locate the pending redex of largest DFS index via `getIndex`/`map`; if it
    lies in the transition domain `D` (opcode redex or ready operator), apply the local
    rewrite (`reduce`) and splice the result back; otherwise crash (`none`).
    `next v = none` also when `v` is terminal (no pending action).  Being a Lean function,
    `next` is deterministic — the concrete realization of the paper's "`*` is a
    deterministic mapping between program states". -/
def next (v : Verb) : Option Verb :=
  match getIndex v with
  | none   => none
  | some i =>
      match map i v with
      | none     => none
      | some sub =>
          if inDomain sub then
            match reduce sub with
            | some r => some (replaceAt i v r)
            | none   => none
          else none

/-! ### Executable paper interpreter — iterate `next` to a result (note 2, PLAN §2) -/

-- main.tex:1090–1098  (Def:NockProgram)
/-- **`Def:NockProgram`** (`main.tex:1090–1098`).
    `F = *[subject, formula]` with subject, formula terminal; `NockProgram^Λ := {F | λ ≤ Λ}`. -/
def program (subject formula : Noun) : Verb :=
  .node .star (ofNoun subject) (ofNoun formula)

/-- Extract the observable output of a stuck verb: its underlying noun if it is in terminal
    state (a *valid* completion, main.tex:1123), else `none` (a crash / *invalid*
    completion, main.tex:1124). -/
def result (v : Verb) : Option Noun :=
  if v.isTerminal then some v.noun else none

/-- Fuel-indexed iteration of `next` from `v` to a terminal/⊥ state, returning the result
    noun (`none` on crash or fuel exhaustion).  Nock is Turing-complete, so fuel is
    required for totality; `none` conflates a genuine crash with fuel exhaustion, exactly
    as `evalN` does. -/
def run : Nat → Verb → Option Noun
  | 0,        _ => none
  | fuel + 1, v =>
      match next v with
      | some v' => run fuel v'
      | none    => result v

/-- Run a Nock program `*[subject, formula]` through the paper's small-step interpreter. -/
def runProgram (fuel : Nat) (subject formula : Noun) : Option Noun :=
  run fuel (program subject formula)

/-! ### Strictness of the DFS order (main.tex:1107) -/

/-- The DFS counter never decreases: `(enum v c).1 ≥ c`. -/
theorem enum_ge_start (v : Verb) (c : Nat) : c ≤ (enum v c).1 := by
  induction v generalizing c with
  | leaf n => simp [enum]
  | node a l r ihl ihr =>
      simp only [enum]
      have h1 : c + 1 ≤ (enum l (c + 1)).1 := ihl (c + 1)
      have h2 : (enum l (c + 1)).1 ≤ (enum r (enum l (c + 1)).1).1 := ihr _
      omega

/-- Every internal-node index produced by `enum v c` lies in the half-open counter range
    `[c, (enum v c).1)`.  Distinct nodes therefore receive distinct indices: the DFS
    `map` enforces a *strict* ordering on subtrees (main.tex:1107). -/
theorem enum_index_range (v : Verb) (c : Nat) :
    ∀ p ∈ (enum v c).2, c ≤ p.1 ∧ p.1 < (enum v c).1 := by
  induction v generalizing c with
  | leaf n => intro p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro p hp
      simp only [enum, List.mem_cons, List.mem_append] at hp
      have hlge : c + 1 ≤ (enum l (c + 1)).1 := enum_ge_start l (c + 1)
      have hrge : (enum l (c + 1)).1 ≤ (enum r (enum l (c + 1)).1).1 := enum_ge_start r _
      rcases hp with hroot | hleft | hright
      · subst hroot; simp only [enum]; omega
      · have := ihl (c + 1) p hleft
        simp only [enum]; omega
      · have := ihr (enum l (c + 1)).1 p hright
        simp only [enum]; omega

/-! ### DFS indices are distinct (main.tex:1107) -/

/-- `findAt` over an append: the left list wins if it has a match. -/
theorem findAt_append (i : Nat) :
    ∀ (L1 L2 : List (Nat × Verb)),
      findAt i (L1 ++ L2) = match findAt i L1 with
                            | some v => some v
                            | none   => findAt i L2
  | [],            L2 => by simp [findAt]
  | (j, w) :: t, L2 => by
      simp only [List.cons_append, findAt]
      by_cases h : i = j
      · simp [h]
      · simp only [ite_eq_right h]; exact findAt_append i t L2

/-- If no pair in `L` carries index `i`, then `findAt i L = none`. -/
theorem findAt_eq_none {i : Nat} :
    ∀ {L : List (Nat × Verb)}, (∀ p ∈ L, p.1 ≠ i) → findAt i L = none
  | [],            _ => rfl
  | (j, w) :: t, h => by
      have hj : ¬ (i = j) := fun heq => (h (j, w) (by simp)) heq.symm
      simp only [findAt, ite_eq_right hj]
      exact findAt_eq_none (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- `findAt i L = some v` witnesses membership `(i, v) ∈ L`. -/
theorem findAt_some_mem {i : Nat} {v : Verb} :
    ∀ {L : List (Nat × Verb)}, findAt i L = some v → (i, v) ∈ L
  | [],            h => by simp [findAt] at h
  | (j, w) :: t, h => by
      simp only [findAt] at h
      split at h
      · rename_i hij
        subst hij
        obtain rfl := Option.some.inj h
        simp
      · exact List.mem_cons_of_mem _ (findAt_some_mem h)

/-- **DFS distinctness (core).**  Every pair produced by `enum` is recovered by `findAt` on
    its own index: the index ranges of the two subtrees (`enum_index_range`) are disjoint
    from each other and from the root counter, so no two pairs share an index. -/
private theorem enum_findAt (v : Verb) (c : Nat) :
    ∀ p ∈ (enum v c).2, findAt p.1 (enum v c).2 = some p.2 := by
  induction v generalizing c with
  | leaf n => intro p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro p hp
      simp only [enum, List.mem_cons, List.mem_append] at hp
      have hlge : c + 1 ≤ (enum l (c + 1)).1 := enum_ge_start l (c + 1)
      simp only [enum, findAt]
      rcases hp with hroot | hleft | hright
      · subst hroot; simp
      · have hb := enum_index_range l (c + 1) p hleft
        have hpc : p.1 ≠ c := by omega
        rw [ite_eq_right hpc, findAt_append]
        rw [ihl (c + 1) p hleft]
      · have hb := enum_index_range r (enum l (c + 1)).1 p hright
        have hpc : p.1 ≠ c := by omega
        rw [ite_eq_right hpc, findAt_append]
        have hnone : findAt p.1 (enum l (c + 1)).2 = none := by
          apply findAt_eq_none
          intro q hq
          have := enum_index_range l (c + 1) q hq
          omega
        rw [hnone]
        exact ihr (enum l (c + 1)).1 p hright

/-- **`map` retrieves the unique node at an index.**  If `(i, v)` is one of the DFS
    internal-node pairs of `a`, then `map i a = some v`.  (Uses DFS distinctness,
    `enum_findAt`.) -/
theorem map_of_mem_nodes {a : Verb} {i : Nat} {v : Verb}
    (h : (i, v) ∈ nodes a) : map i a = some v :=
  enum_findAt a 0 (i, v) h

/-- Membership of the retrieved node: `map i a = some v ⇒ (i, v) ∈ nodes a`. -/
theorem mem_nodes_of_map {a : Verb} {i : Nat} {v : Verb}
    (h : map i a = some v) : (i, v) ∈ nodes a :=
  findAt_some_mem h

/-! ### `getIndex` = numeric argmax of pending indices (spec of `maximumPendingIndex`) -/

/-- `maximumPendingIndex L = none` iff no pair in `L` has a pending action. -/
private theorem maximumPendingIndex_eq_none :
    ∀ {L : List (Nat × Verb)},
      maximumPendingIndex L = none ↔ ∀ p ∈ L, p.2.isPending = false
  | [] => by simp [maximumPendingIndex]
  | (i, w) :: t => by
      simp only [maximumPendingIndex]
      by_cases hw : w.isPending = true
      · rw [ite_eq_left hw]
        constructor
        · intro h; cases maximumPendingIndex t <;> simp at h
        · intro h; exact absurd (h (i, w) (by simp)) (by simp [hw])
      · rw [ite_eq_right hw]
        rw [maximumPendingIndex_eq_none]
        constructor
        · intro h p hp
          rcases List.mem_cons.1 hp with heq | hmem
          · subst heq; simpa using hw
          · exact h p hmem
        · intro h p hp; exact h p (List.mem_cons_of_mem _ hp)

/-- The numeric argmax is achieved: `maximumPendingIndex L = some i` names a pending pair at `i`. -/
private theorem maximumPendingIndex_mem :
    ∀ {L : List (Nat × Verb)} {i : Nat},
      maximumPendingIndex L = some i → ∃ v, (i, v) ∈ L ∧ v.isPending = true
  | [], i, h => by simp [maximumPendingIndex] at h
  | (j, w) :: t, i, h => by
      simp only [maximumPendingIndex] at h
      by_cases hw : w.isPending = true
      · rw [ite_eq_left hw] at h
        cases hr : maximumPendingIndex t with
        | none => rw [hr] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨w, by simp, hw⟩
        | some k =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : Nat.max j k = i
            rcases Nat.le_total j k with hjk | hkj
            · have hmx : Nat.max j k = k := Nat.max_eq_right hjk
              have hik : i = k := hmx ▸ h.symm
              subst hik
              obtain ⟨v, hv, hvp⟩ := maximumPendingIndex_mem hr
              exact ⟨v, List.mem_cons_of_mem _ hv, hvp⟩
            · have hmx : Nat.max j k = j := Nat.max_eq_left hkj
              have hij : i = j := hmx ▸ h.symm
              subst hij
              exact ⟨w, by simp, hw⟩
      · rw [ite_eq_right hw] at h
        obtain ⟨v, hv, hvp⟩ := maximumPendingIndex_mem h
        exact ⟨v, List.mem_cons_of_mem _ hv, hvp⟩

/-- Every pending index is `≤` the numeric argmax. -/
private theorem maximumPendingIndex_ge :
    ∀ {L : List (Nat × Verb)} {i : Nat},
      maximumPendingIndex L = some i → ∀ j v, (j, v) ∈ L → v.isPending = true → j ≤ i
  | [], i, h => by simp [maximumPendingIndex] at h
  | (p, w) :: t, i, h => by
      intro j v hmem hvp
      simp only [maximumPendingIndex] at h
      by_cases hw : w.isPending = true
      · rw [ite_eq_left hw] at h
        cases hr : maximumPendingIndex t with
        | none =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : p = i
            rcases List.mem_cons.1 hmem with heq | hmem'
            · simp only [Prod.mk.injEq] at heq; have hjp := heq.1; omega
            · have hnone := (maximumPendingIndex_eq_none).1 hr
              exact absurd (hnone (j, v) hmem') (by simp [hvp])
        | some k =>
            rw [hr] at h; simp only [Option.some.injEq] at h
            -- h : Nat.max p k = i  (kept as an opaque atom for omega)
            rcases List.mem_cons.1 hmem with heq | hmem'
            · simp only [Prod.mk.injEq] at heq
              have hjp : j = p := heq.1
              have hle : p ≤ Nat.max p k := Nat.le_max_left p k; omega
            · have hjk := maximumPendingIndex_ge hr j v hmem' hvp
              have hle : k ≤ Nat.max p k := Nat.le_max_right p k; omega
      · rw [ite_eq_right hw] at h
        rcases List.mem_cons.1 hmem with heq | hmem'
        · simp only [Prod.mk.injEq] at heq
          obtain ⟨_, rfl⟩ := heq; simp [hvp] at hw
        · exact maximumPendingIndex_ge h j v hmem' hvp

/-- Characterization of the numeric argmax: if `(i, v)` is pending and no pending index
    exceeds `i`, then `maximumPendingIndex L = some i`. -/
private theorem maximumPendingIndex_of {L : List (Nat × Verb)} {i : Nat}
    (hmem : ∃ v, (i, v) ∈ L ∧ v.isPending = true)
    (hmax : ∀ j v, (j, v) ∈ L → v.isPending = true → j ≤ i) :
    maximumPendingIndex L = some i := by
  obtain ⟨v, hv, hvp⟩ := hmem
  cases hm : maximumPendingIndex L with
  | none =>
      have hnone := (maximumPendingIndex_eq_none).1 hm
      exact absurd (hnone (i, v) hv) (by simp [hvp])
  | some m =>
      obtain ⟨w, hw, hwp⟩ := maximumPendingIndex_mem hm
      have h1 : m ≤ i := hmax m w hw hwp
      have h2 : i ≤ m := maximumPendingIndex_ge hm i v hv hvp
      have : m = i := by omega
      rw [this]

/-! ### Strict redex-selection order (main.tex:1105-1109, 1156) -/

-- main.tex:1105-1107  (`>_F` a strict ordering on subtrees)
/-- A **strict selection order** on internal-node indices: a strict total order (the paper's
    "strict ordering", main.tex:1107).  Irreflexive + transitive ⇒ asymmetric; `total`
    (connectedness) is what forbids ties, hence forces a *unique* maximum. -/
structure StrictSelect (lt : Nat → Nat → Prop) : Prop where
  irrefl : ∀ i, ¬ lt i i
  trans  : ∀ {i j k}, lt i j → lt j k → lt i k
  total  : ∀ {i j}, i ≠ j → lt i j ∨ lt j i

/-- `i` is a *pending* internal-node index of `a`: `map i a` is a node with a pending
    (non-⊥) action. -/
def IsPendingIdx (a : Verb) (i : Nat) : Prop :=
  ∃ v, map i a = some v ∧ v.isPending = true

-- main.tex:1109,1111  (`getIndex = argmax`)
/-- `i` is a **maximal** pending index of `a` under the order `lt`: a pending index that no
    other pending index exceeds.  This is the paper's `argmax` characterization of
    `getIndex`. -/
def IsMaxPending (lt : Nat → Nat → Prop) (a : Verb) (i : Nat) : Prop :=
  IsPendingIdx a i ∧ ∀ j, IsPendingIdx a j → ¬ lt i j

-- main.tex:1052,1109  (one `*`-step: rewrite the redex chosen by the order)
/-- An **abstract redex-selection step**: pick a maximal pending index `i` under `lt`, and
    if the selected subverb is in the transition domain, apply the local rewrite and splice
    it back.  With no strictness assumption this relation can be multi-valued (several
    maximal redexes); `SelStep.det` shows a *strict* order collapses it to a function. -/
def SelStep (lt : Nat → Nat → Prop) (a b : Verb) : Prop :=
  ∃ i sub r, IsMaxPending lt a i ∧ map i a = some sub ∧ inDomain sub = true
             ∧ reduce sub = some r ∧ b = replaceAt i a r

-- main.tex:2325  (uniqueness of the argmax from strictness)
/-- **Determinism from strictness.**  If `lt` is a strict total order, a redex-selection
    step is deterministic: `hs.total` forces the two selected indices to coincide; the rest
    is functionality of `map`/`reduce`/`replaceAt`. -/
theorem SelStep.det {lt : Nat → Nat → Prop} (hs : StrictSelect lt) {a b b' : Verb}
    (h : SelStep lt a b) (h' : SelStep lt a b') : b = b' := by
  obtain ⟨i, sub, r, ⟨hip, hmax⟩, hmap, _, hred, hb⟩ := h
  obtain ⟨i', sub', r', ⟨hip', hmax'⟩, hmap', _, hred', hb'⟩ := h'
  have hii : i = i' := by
    rcases Classical.em (i = i') with heq | hne
    · exact heq
    · rcases hs.total hne with hlt | hlt
      · exact absurd hlt (hmax i' hip')
      · exact absurd hlt (hmax' i hip)
  subst hii
  have hsub : sub = sub' := Option.some.inj (hmap.symm.trans hmap')
  subst hsub
  have hr : r = r' := Option.some.inj (hred.symm.trans hred')
  subst hr
  exact hb.trans hb'.symm

/-! ### DFS instantiation: the concrete order is strict, and `next` realizes `SelStep` -/

/-- The concrete DFS order on pre-order indices is the usual strict order on `Nat`. -/
abbrev dfsLt : Nat → Nat → Prop := (· < ·)

-- main.tex:1103,1107  (DFS enforces a strict ordering)
/-- The DFS index order is a strict total order.  This is *why* `map = DFS` "enforces a
    strict ordering on subtrees" (main.tex:1107): distinct internal nodes get distinct `Nat`
    indices (`enum_index_range`/`map_of_mem_nodes`), and `Nat.lt` is a strict total order. -/
theorem strictSelect_dfs : StrictSelect dfsLt where
  irrefl i := Nat.lt_irrefl i
  trans h h' := Nat.lt_trans h h'
  total hne := Nat.lt_or_gt_of_ne hne

/-- Pending-index membership, in list form.  The `←` direction uses DFS distinctness
    (`map_of_mem_nodes`): a pending node in the `nodes` list is retrieved by `map` on its
    (unique) index. -/
theorem isPendingIdx_iff_mem {a : Verb} {i : Nat} :
    IsPendingIdx a i ↔ ∃ v, (i, v) ∈ nodes a ∧ v.isPending = true := by
  constructor
  · rintro ⟨v, hmap, hp⟩; exact ⟨v, mem_nodes_of_map hmap, hp⟩
  · rintro ⟨v, hmem, hp⟩; exact ⟨v, map_of_mem_nodes hmem, hp⟩

/-- `getIndex` is exactly the DFS argmax: `getIndex a = some i ↔ i` is the maximal pending
    index under `dfsLt`.  (Combines the `maximumPendingIndex` spec with DFS distinctness.) -/
theorem getIndex_eq_some_iff {a : Verb} {i : Nat} :
    getIndex a = some i ↔ IsMaxPending dfsLt a i := by
  unfold getIndex IsMaxPending dfsLt
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨v, hv, hvp⟩ := maximumPendingIndex_mem h
      exact isPendingIdx_iff_mem.2 ⟨v, hv, hvp⟩
    · intro j hj
      rw [Nat.not_lt]
      obtain ⟨w, hw, hwp⟩ := isPendingIdx_iff_mem.1 hj
      exact maximumPendingIndex_ge h j w hw hwp
  · rintro ⟨hip, hmax⟩
    obtain ⟨v, hv, hvp⟩ := isPendingIdx_iff_mem.1 hip
    apply maximumPendingIndex_of ⟨v, hv, hvp⟩
    intro j w hjw hwp
    have hj : IsPendingIdx a j := isPendingIdx_iff_mem.2 ⟨w, hjw, hwp⟩
    have := hmax j hj
    omega

-- main.tex:1052,1156  (`next` = the DFS-ordered selection step)
/-- **`next` faithfully realizes the strict DFS selection step.**  This is the bridge that
    makes `deterministic_Trace` an instance of the paper's conditional theorem: the concrete
    interpreter's step is `SelStep` for the (strict) DFS order. -/
theorem next_eq_some_iff {a b : Verb} : next a = some b ↔ SelStep dfsLt a b := by
  constructor
  · intro h
    unfold next at h
    split at h
    · simp at h
    · rename_i i hgi
      split at h
      · simp at h
      · rename_i sub hmap
        split at h
        · rename_i hdom
          split at h
          · rename_i r hred
            exact ⟨i, sub, r, getIndex_eq_some_iff.1 hgi, hmap, hdom, hred, (Option.some.inj
              h).symm⟩
          · simp at h
        · simp at h
  · rintro ⟨i, sub, r, hmax, hmap, hdom, hred, hb⟩
    have hgi : getIndex a = some i := getIndex_eq_some_iff.2 hmax
    unfold next
    simp only [hgi, hmap, hdom, hred, ite_true]
    rw [hb]

/-! ### Non-strict selection witness (main.tex:2325) -/

/-- The empty order — *not* total, hence not a `StrictSelect`.  Every index is vacuously
    maximal under it. -/
def emptyLt : Nat → Nat → Prop := fun _ _ => False

/-- A verb with two independent, equally-maximal redexes: two copies of `*[0, [1, 5]]`
    (each an `OP₁` redex reducing to `5`), spliced under a `⊥` root. -/
def twoRedex : Verb :=
  .node .null
    (.node .star (.leaf 0) (.node .null (.leaf 1) (.leaf 5)))
    (.node .star (.leaf 0) (.node .null (.leaf 1) (.leaf 5)))

-- main.tex:2325  (strictness essential: no ties ⇒ unique max)
/-- **Non-vacuity of strictness.**  Under a non-strict order, `SelStep` is not a function:
    it relates `twoRedex` to two distinct successors.  Contrast `SelStep.det`, which uses
    `StrictSelect.total` to collapse exactly this ambiguity. -/
theorem selStep_multivalued_without_strictness :
    ∃ (a b b' : Verb), b ≠ b' ∧ SelStep emptyLt a b ∧ SelStep emptyLt a b' := by
  refine ⟨twoRedex, replaceAt 1 twoRedex (.leaf 5), replaceAt 3 twoRedex (.leaf 5), by decide,
    ⟨1, _, .leaf 5, ⟨⟨_, rfl, rfl⟩, fun _ _ hf => hf⟩, rfl, by decide, rfl, rfl⟩,
    ⟨3, _, .leaf 5, ⟨⟨_, rfl, rfl⟩, fun _ _ hf => hf⟩, rfl, by decide, rfl, rfl⟩⟩

/-! ### Terminal verbs cannot step (main.tex:1039, 1122) -/

/-- Every internal node produced by `enum` of a *terminal* verb is non-pending. -/
theorem enum_nonpending_of_terminal : ∀ (v : Verb), isTerminal v = true →
    ∀ (c : Nat), ∀ p ∈ (enum v c).2, p.2.isPending = false := by
  intro v
  induction v with
  | leaf n => intro _ c p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro h c p hp
      simp only [isTerminal, Bool.and_eq_true] at h
      obtain ⟨⟨ha, hl⟩, hr⟩ := h
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; simp [isPending, ha]
      · exact ihl hl (c + 1) p hleft
      · exact ihr hr _ p hright

-- main.tex:1039,1122  (a terminal verb has no pending redex to select)
/-- `getIndex` of a terminal verb is `none`: no internal node carries a pending action. -/
theorem getIndex_none_of_terminal {v : Verb} (h : isTerminal v = true) : getIndex v = none := by
  unfold getIndex nodes
  rw [maximumPendingIndex_eq_none]
  exact enum_nonpending_of_terminal v h 0

-- main.tex:1122  (`tₙ` terminal ⇒ the trace is complete: `next` bottoms out)
/-- A terminal verb cannot take a Nock step. -/
theorem next_none_of_terminal {v : Verb} (h : isTerminal v = true) : next v = none := by
  unfold next; rw [getIndex_none_of_terminal h]

/-! ### Converses: no pending redex ⇒ terminal (main.tex:1122) -/

/-- **Converse of `enum_nonpending_of_terminal`.**  If every internal node enumerated from `v`
    is non-pending, then `v` is terminal. -/
theorem terminal_of_enum_nonpending :
    ∀ (v : Verb) (c : Nat),
      (∀ p ∈ (enum v c).2, p.2.isPending = false) → isTerminal v = true := by
  intro v
  induction v with
  | leaf k => intro c _; rfl
  | node a l r ihl ihr =>
      intro c h
      have hroot : ((c, Verb.node a l r) : Nat × Verb) ∈ (enum (Verb.node a l r) c).2 := by
        simp [enum]
      have hpc := h _ hroot
      have ha : a.isNull = true := by
        simp only [isPending] at hpc
        cases hh : a.isNull with
        | true => rfl
        | false => rw [hh] at hpc; simp at hpc
      have hl : isTerminal l = true := by
        apply ihl (c + 1)
        intro p hp
        apply h
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl hp)
      have hr : isTerminal r = true := by
        apply ihr (enum l (c + 1)).1
        intro p hp
        apply h
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hp)
      simp only [isTerminal, ha, hl, hr, Bool.and_self]

-- main.tex:1039,1122  (halting condition: `getIndex F = ⊥ ⇔ F` terminal)
/-- **`getIndex` is `none` iff terminal.**  The `←` is `getIndex_none_of_terminal`; the `→`
    is `terminal_of_enum_nonpending` fed the `maximumPendingIndex` emptiness spec. -/
theorem getIndex_none_iff_terminal {v : Verb} : getIndex v = none ↔ isTerminal v = true := by
  constructor
  · intro h
    apply terminal_of_enum_nonpending v 0
    unfold getIndex nodes at h
    exact maximumPendingIndex_eq_none.1 h
  · exact getIndex_none_of_terminal

/-- **Subtree enumeration embeds.**  If `sub` is enumerated at index `i` within `v` (counter
    `c`), then every internal node of `sub`'s own enumeration (counter `i`) also appears in
    `v`'s enumeration.  This is what lets a pending node *inside* the selected redex be seen as
    a pending index of the whole verb. -/
theorem enum_subtree_mem :
    ∀ (v : Verb) (c i : Nat) (sub : Verb),
      (i, sub) ∈ (enum v c).2 → ∀ p ∈ (enum sub i).2, p ∈ (enum v c).2 := by
  intro v
  induction v with
  | leaf k => intro c i sub hmem; simp [enum] at hmem
  | node a l r ihl ihr =>
      intro c i sub hmem p hp
      simp only [enum, List.mem_cons, List.mem_append] at hmem
      rcases hmem with hroot | hleft | hright
      · simp only [Prod.mk.injEq] at hroot
        obtain ⟨rfl, rfl⟩ := hroot
        simpa only [enum] using hp
      · have := ihl (c + 1) i sub hleft p hp
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl this)
      · have := ihr (enum l (c + 1)).1 i sub hright p hp
        simp only [enum, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr this)

-- main.tex:1109  (the argmax redex has no pending descendant ⇒ its arguments are terminal)
/-- **The selected redex has terminal children.**  If `getIndex v = some i` picks the argmax
    pending node `map i v = node a l r`, then `l` and `r` are terminal: any pending node below
    them would have a strictly larger DFS index (`enum_index_range` + `enum_subtree_mem`),
    contradicting maximality (`getIndex_eq_some_iff`).  This is the shape `inDomain`/`reduce`
    need at the redex. -/
theorem children_terminal_of_getIndex {v : Verb} {i : Nat} {a : Action} {l r : Verb}
    (hidx : getIndex v = some i) (hmap : map i v = some (Verb.node a l r)) :
    isTerminal l = true ∧ isTerminal r = true := by
  have hmax : IsMaxPending dfsLt v i := getIndex_eq_some_iff.1 hidx
  have hmem : (i, Verb.node a l r) ∈ nodes v := mem_nodes_of_map hmap
  have hsub : ∀ p ∈ (enum (Verb.node a l r) i).2, p ∈ nodes v := by
    intro p hp; exact enum_subtree_mem v 0 i (Verb.node a l r) hmem p hp
  have hnopend : ∀ p ∈ (enum (Verb.node a l r) i).2, i < p.1 → p.2.isPending = false := by
    intro p hp hlt
    obtain ⟨j, w⟩ := p
    simp only at hlt ⊢
    cases hw : w.isPending with
    | false => rfl
    | true =>
        have hpid : IsPendingIdx v j := isPendingIdx_iff_mem.2 ⟨w, hsub (j, w) hp, hw⟩
        exact absurd hlt (hmax.2 j hpid)
  refine ⟨?_, ?_⟩
  · apply terminal_of_enum_nonpending l (i + 1)
    intro p hp
    apply hnopend p
    · simp only [enum, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hp)
    · have := enum_index_range l (i + 1) p hp; omega
  · apply terminal_of_enum_nonpending r (enum l (i + 1)).1
    intro p hp
    apply hnopend p
    · simp only [enum, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hp)
    · have hge : i + 1 ≤ (enum l (i + 1)).1 := enum_ge_start l (i + 1)
      have := enum_index_range r (enum l (i + 1)).1 p hp; omega

/-! ### `NockVMROM` without OP₁₀ (main.tex:1160) -/

-- main.tex:1160  (the local rewrite with `OP₁₀` excluded)
/-- The ROM local rewrite: identical to `reduce` except every part of `OP₁₀` (edit, `#` —
    main.tex:1071,1587) is *rejected* (`none` = crash), removing the ability to write to memory.
    Two things are excluded, exactly the two halves of `OP₁₀` in our two-step encoding
    (note 2b): (i) the `OP₁₀` opcode redex `*[n₁,[10,n₂]]` (`i = 10`), and (ii) the `edit`
    operator node it produces (`#`, the actual memory write).  No other opcode produces `edit`,
    so this removes `OP₁₀` and nothing else. -/
def reduceROM : Verb → Option Verb
  | .node .star _ (.node _ (.leaf 10) _) => none   -- (i) OP₁₀ opcode excluded (main.tex:1160)
  | .node .edit _ _                      => none   -- (ii) the `#`/edit write step excluded
  | v => reduce v

-- main.tex:1160  (the transition function of `NockVMROM`)
/-- One `NockVMROM` step: exactly `next`, but using `reduceROM` for the local rewrite, so a
    selected `OP₁₀` redex (or a stray `edit` node) crashes.  Every non-crashing ROM step is a
    genuine Nock step (`next_of_nextROM`). -/
def nextROM (v : Verb) : Option Verb :=
  match getIndex v with
  | none   => none
  | some i =>
      match map i v with
      | none     => none
      | some sub =>
          if inDomain sub then
            match reduceROM sub with
            | some r => some (replaceAt i v r)
            | none   => none
          else none

/-- A terminal verb cannot take a ROM step either. -/
theorem nextROM_none_of_terminal {v : Verb} (h : isTerminal v = true) : nextROM v = none := by
  unfold nextROM; rw [getIndex_none_of_terminal h]

/-- `reduceROM` refines `reduce`: whenever the ROM rewrite succeeds, the full Nock rewrite agrees
    (they differ only on `OP₁₀`, where `reduceROM` returns `none`). -/
theorem reduce_of_reduceROM {v r : Verb} (h : reduceROM v = some r) : reduce v = some r := by
  unfold reduceROM at h
  split at h <;> first | exact h | simp at h

-- main.tex:1160  (NockVMROM ⊆ NockVM at the transition level: ROM steps are Nock steps)
/-- **Every ROM transition is a Nock transition.**  `nextROM` is a *restriction* of `next`
    (`OP₁₀` removed): if `nextROM v = some w` then `next v = some w`.  This is the verb-level
    sense in which `NockVMROM` is `NockVM` without `OP₁₀`. -/
theorem next_of_nextROM {v w : Verb} (h : nextROM v = some w) : next v = some w := by
  unfold nextROM at h
  unfold next
  cases hg : getIndex v with
  | none => simp only [hg] at h ⊢; exact h
  | some i =>
      simp only [hg] at h ⊢
      cases hm : map i v with
      | none => simp only [hm] at h ⊢; exact h
      | some sub =>
          simp only [hm] at h ⊢
          by_cases hd : inDomain sub = true
          · simp only [ite_eq_left hd] at h ⊢
            cases hr : reduceROM sub with
            | none => simp only [hr] at h; simp at h
            | some r =>
                simp only [hr] at h
                simp only [reduce_of_reduceROM hr]
                exact h
          · simp only [ite_eq_right hd] at h ⊢; exact h

/-! ### Two-verb transition checker `Nock` (`main.tex:1639–1661`) -/
-- main.tex:1639–1661  (Algorithm:Transition_Function)
/-- **`Algorithm:Transition_Function`** (`main.tex:1639–1661`).
    `Nock(Tᵢ,Tᵢ₊₁)`: `Fᵢ ← map(Tᵢ,getIndex(Tᵢ))`; frame `Tᵢ\Fᵢ = Tᵢ₊₁\Fᵢ₊₁`;
    accept (`0`) iff `Fᵢ₊₁ = OP:Fᵢ` / `cons:Fᵢ`, or `Fᵢ₊₁=⊥` when out of domain. -/
def NockCheck (Ti : Verb) (Tnext : Option Verb) : Bool :=
  match getIndex Ti with
  | none   => false                                        -- terminal `Ti`: no transition
  | some i =>
      match map i Ti with
      | none    => false                                   -- (unreachable: `getIndex ⇒ node`)
      | some Fi =>
          match inDomain Fi, reduce Fi with
          -- main.tex:1642,1653,1657  genuine step: frame-preserving splice of the rewrite
          | true,  some Fnext => decide (Tnext = some (replaceAt i Ti Fnext))
          -- main.tex:1644,1650    crash: selected redex reduces to ⊥
          | true,  none       => decide (Tnext = none)
          -- main.tex:1643,1649    crash: selected `Fᵢ` is a non-redex / out of domain
          | false, _          => decide (Tnext = none)

-- main.tex:1643-1659  (the crash branches: selected redex has no consistent non-⊥ successor)
/-- **`Ti` crashes.**  `Ti` selects a pending redex (`getIndex Ti ≠ none`, so `Ti` is not
    terminal, main.tex:1039) but that redex is out of the transition domain / does not reduce,
    so its only consistent successor is `⊥` (main.tex:1644,1650).  Equivalently `next Ti = none`
    together with a pending redex. -/
def Crashes (Ti : Verb) : Prop := getIndex Ti ≠ none ∧ next Ti = none

/-- `getIndex a = some i` names an actual internal node: `map i a` succeeds.  (The argmax is
    achieved at a pending node, which `map` retrieves by DFS distinctness.) -/
theorem map_some_of_getIndex {a : Verb} {i : Nat} (h : getIndex a = some i) :
    ∃ sub, map i a = some sub := by
  obtain ⟨⟨v, hmap, _⟩, _⟩ := getIndex_eq_some_iff.1 h
  exact ⟨v, hmap⟩

-- main.tex:1639  (the checker is 1-1 with the forward semantics `next` plus the crash branch)
/-- **`NockCheck` ↔ forward semantics + crash.**  The two-verb checker accepts `(a, b)`
    (returns `true` = the paper's `0`) iff `b` is a genuine one-step successor of `a`
    (`next a = some v`, i.e. `Step a v`) OR `a` crashes and `b = ⊥` (`b = none`).  This is a
    genuine biconditional: `NockCheck` is 1-1 with `next` (on non-⊥ successors) together with
    the crash branch — the checker `Nock(Tᵢ,Tᵢ₊₁)=0` and the forward map coincide exactly. -/
theorem nockCheck_eq_true_iff {a : Verb} {b : Option Verb} :
    NockCheck a b = true ↔
      (∃ v, b = some v ∧ next a = some v) ∨ (b = none ∧ Crashes a) := by
  unfold NockCheck Crashes
  cases hgi : getIndex a with
  | none =>
      have hn : next a = none := by unfold next; rw [hgi]
      rw [hn]; simp
  | some i =>
      obtain ⟨Fi, hmap⟩ := map_some_of_getIndex hgi
      simp only [hmap]
      by_cases hd : inDomain Fi = true
      · cases hr : reduce Fi with
        | some Fnext =>
            have hnext : next a = some (replaceAt i a Fnext) := by
              unfold next; simp only [hgi, hmap, ite_eq_left hd, hr]
            simp only [hd]
            constructor
            · intro h
              have hb : b = some (replaceAt i a Fnext) := by simpa using h
              exact Or.inl ⟨_, hb, hnext⟩
            · rintro (⟨v, hb, hv⟩ | ⟨_, _, hcr⟩)
              · rw [hnext] at hv
                have : v = replaceAt i a Fnext := (Option.some.inj hv).symm
                subst this; simp [hb]
              · rw [hnext] at hcr; simp at hcr
        | none =>
            have hnext : next a = none := by
              unfold next; simp only [hgi, hmap, ite_eq_left hd, hr]
            simp only [hd]
            constructor
            · intro h
              have hb : b = none := by simpa using h
              exact Or.inr ⟨hb, by simp, hnext⟩
            · rintro (⟨v, hb, hv⟩ | ⟨hb, _, _⟩)
              · rw [hnext] at hv; simp at hv
              · simp [hb]
      · have hd' : inDomain Fi = false := by simpa using hd
        have hnext : next a = none := by
          unfold next; simp only [hgi, hmap, ite_eq_right hd]
        simp only [hd']
        constructor
        · intro h
          have hb : b = none := by simpa using h
          exact Or.inr ⟨hb, by simp, hnext⟩
        · rintro (⟨v, hb, hv⟩ | ⟨hb, _, _⟩)
          · rw [hnext] at hv; simp at hv
          · simp [hb]

/-! ### Frame-invariance gate (main.tex:1642) -/

-- main.tex:1642  (`Tᵢ \ Fᵢ = Tᵢ₊₁ \ Fᵢ₊₁`: equal contexts outside the selected index)
/-- **Frame agreement at index `i`**: `Tj` is `Ti` with the subverb at DFS index `i` replaced
    by some `Fj` — so `Ti` and `Tj` share the same frame (context) outside `i`.  This is the
    map-complement equality `Ti \ Fᵢ = Tj \ Fⱼ` (main.tex:1642). -/
def FrameAgree (i : Nat) (Ti Tj : Verb) : Prop := ∃ Fj, Tj = replaceAt i Ti Fj

-- main.tex:1642  (an accepted non-⊥ transition satisfies the frame gate)
/-- **Accepted steps pass the frame gate (main.tex:1642).**  If `NockCheck` accepts a non-⊥
    successor `b` of `a`, then `b` agrees with `a` outside the selected index: `FrameAgree`.
    (The genuine-step branch of `NockCheck` is exactly the frame-preserving splice.) -/
theorem nockCheck_frameAgree {a b : Verb} (h : NockCheck a (some b) = true) :
    ∃ i, getIndex a = some i ∧ FrameAgree i a b := by
  rcases nockCheck_eq_true_iff.1 h with ⟨v, hbv, hnext⟩ | ⟨hb, _⟩
  · have hvb : v = b := (Option.some.inj hbv).symm
    subst hvb
    obtain ⟨i, sub, r, hmax, _, _, _, hb⟩ := next_eq_some_iff.1 hnext
    exact ⟨i, getIndex_eq_some_iff.2 hmax, r, hb⟩
  · exact absurd hb (by simp)

/-! ### Verifiable crash — a three-way outcome (value / crash / timeout)

`run`/`runProgram` return `Option Noun`, collapsing a genuine crash (a stuck, non-terminal ⊥ state,
`main.tex:1124`) and fuel exhaustion into the same `none`.  `eval` refines that: it mirrors `run`'s
fuel structure exactly, but at a halt (`next v = none`) it reports `value` (a terminal completion)
or
`crash` (a *checked* ⊥) instead of `some`/`none`; only a genuinely-steppable state can `timeout`.  A
crash thus becomes a positive, kernel-checkable outcome, not merely the absence of a value. -/

/-- Result of running a verb to a normal form. -/
inductive Outcome
  | value (n : Noun)   -- terminal reached: the paper's `*[s f] = n`
  | crash              -- stuck, non-terminal reached: the paper's `*[s f] = ⊥` (main.tex:1124)
  | timeout            -- fuel exhausted while the state was still steppable
  deriving Repr, DecidableEq, Inhabited

/-- The halting outcome of a stopped verb (`next v = none`): its noun if terminal (a *valid*
    completion), else a `crash` (an *invalid* completion, main.tex:1124). -/
def haltOutcome (v : Verb) : Outcome :=
  if v.isTerminal then .value v.noun else .crash

/-- A non-terminal halt is a `crash`. -/
theorem haltOutcome_crash {v : Verb} (h : v.isTerminal = false) : haltOutcome v = .crash := by
  simp [haltOutcome, h]

/-- Fuel-indexed evaluation distinguishing a crash from fuel exhaustion.  Structurally identical to
    `run`, so `eval` and `run` agree on values at the *same* fuel (`eval_value_iff_run`); the crash
    branch turns `run`'s conflated `none` into a positive `crash`. -/
def eval : Nat → Verb → Outcome
  | 0,        _ => .timeout
  | fuel + 1, v =>
      match next v with
      | some v' => eval fuel v'
      | none    => haltOutcome v

/-- Run a Nock program `*[subject, formula]`, reporting value / crash / timeout. -/
def evalProgram (fuel : Nat) (subject formula : Noun) : Outcome :=
  eval fuel (program subject formula)

/-- One-step unfolding of `eval` (definitional), to avoid over-unfolding nested `eval` calls. -/
theorem eval_succ (n : Nat) (v : Verb) :
    eval (n + 1) v = match next v with | some v' => eval n v' | none => haltOutcome v := rfl

/-- **Values are preserved exactly.**  `eval` yields `value r` at fuel `n` iff the `Option`-valued
    `run` yields `some r` at the same fuel — successful evaluation is unchanged. -/
theorem eval_value_iff_run {n : Nat} {v : Verb} {r : Noun} :
    eval n v = .value r ↔ run n v = some r := by
  induction n generalizing v with
  | zero => simp [eval, run]
  | succ n ih =>
      rw [eval_succ, run]
      cases hnv : next v with
      | some v' => exact ih
      | none =>
          simp only [haltOutcome, result]
          by_cases ht : v.isTerminal
          · simp [ht]
          · simp [ht]

/-- **Crash is stable one step on**: if `eval` reports `crash` at fuel `n`, it reports `crash` at
    `n + 1`.  (The general "any larger fuel" form is `eval_crash_mono_le`.) -/
theorem eval_crash_mono {n : Nat} {v : Verb} (h : eval n v = .crash) :
    eval (n + 1) v = .crash := by
  induction n generalizing v with
  | zero => simp [eval] at h
  | succ n ih =>
      rw [eval_succ] at h ⊢
      cases hnv : next v with
      | some v' => simp only [hnv] at h; exact ih h
      | none    => simp only [hnv] at h; exact h

/-- **Crash is permanent** (so a single successful `eval` certifies it *at every fuel*): once `eval`
    reports `crash` at fuel `n`, it reports `crash` at every `m ≥ n`. -/
theorem eval_crash_mono_le {n m : Nat} {v : Verb} (hnm : n ≤ m) (h : eval n v = .crash) :
    eval m v = .crash := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact eval_crash_mono ih

end Verb
end Nock
