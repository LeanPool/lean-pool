/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Net

/-!
# Nets as graphs

The rest of the development presents a net as a text: a multiset of equations between trees.
This file gives the other presentation, the one of Lafont's pictures (Lafont 1997, Section 1.1,
page 71): a net is a finite set of cells, each with a symbol and its ports, some free ports, and
wires that join the ports two by two.

* `End` — an end of a wire: a port of a cell, or a name.
* `Graph` — cells, wires between ends, and a number of cyclic wires.
* `Graph.WF` — every port of every cell is the end of exactly one wire, and a name ends at most
  one wire. Then the names are the free ports.
* `Graph.Iso` — the same graph up to the identity of the cells.
* `Graph.raw` — the graph read off a text without thinking: one cell for each cell of the trees,
  one wire for each equation and for each auxiliary port. In it a name may end two wires.
* `Graph.Contract` — erasing such a name by joining its two wires.
* `Net.HasGraph` — `G` is the graph of the net `N`: contract the raw graph of a text of `N`
  until no name ends two wires.

This file contains definitions only. The statements about them are in
`InteractionCombinators/Graphs/`: every linear net has a graph, it is unique up to `Iso`, two
linear nets are `Equiv` if and only if their graphs are `Iso`, every well-formed graph is the
graph of a net, and an interaction of texts is an interaction of graphs.

Contents, in the order of the file:

1. Graphs: `End`, `End.mapCell`, `Graph`, `Graph.ends`, `Graph.WF`, `Graph.free`, `Graph.Iso`.
2. The raw graph of a text: `Term.size`, `Term.rootEnd`, `Term.childBase`, `Term.rawCells`,
   `Term.rawWires`, `Graph.raw`.
3. The graph of a net: `Graph.Contract`, `Net.ofList`, `Net.HasGraph`.
-/

@[expose] public section

namespace INet

-- the signature and the type of names, for the whole file
variable {S : Signature} {ν : Type}

-- ============================================================================================
-- 1. Graphs
-- ============================================================================================

/-- An end of a wire. `port c 0` is the principal port of the cell `c`, and `port c (i + 1)` is
its `i`-th auxiliary port. `name x` is the free port called `x`. -/
inductive End (ν : Type) : Type
  -- the port number `i` of the cell number `c`
  | port (c i : ℕ)
  -- the name `x`
  | name (x : ν)
  deriving DecidableEq

namespace End

/-- Renaming the cells. -/
def mapCell
    -- the renaming of the cells
    (σ : ℕ → ℕ) :
    End ν → End ν
  -- a port keeps its number and moves to the renamed cell
  | port c i => port (σ c) i
  -- a name is kept
  | name x => name x

end End

/-- A net as a graph (Lafont 1997, page 71). Cells are identified by numbers. A wire is an
unordered pair of ends. `loops` counts the wires that have no end at all: closed loops. -/
structure Graph (S : Signature) (ν : Type) where
  /-- The cells, with their symbols. -/
  cells : Multiset (ℕ × S.Sym)
  /-- The wires that have ends. -/
  wires : Multiset (Sym2 (End ν))
  /-- The number of cyclic wires. -/
  loops : ℕ

namespace Graph

/-- The ends of the wires, with multiplicity: a wire from an end to itself counts it twice. -/
def ends
    (G : Graph S ν) :
    Multiset (End ν) :=
  -- each wire gives its two ends
  G.wires.bind fun e => e.lift ⟨fun p q => {p, q}, fun p q => Multiset.pair_comm p q⟩

/-- A well-formed graph: cells have distinct identities, each port of each cell ends exactly one
wire, nothing else is a port, and a name ends at most one wire. -/
structure WF [DecidableEq ν] (G : Graph S ν) : Prop where
  /-- Two cells do not share an identity. -/
  nodup : (G.cells.map Prod.fst).Nodup
  /-- The principal port and every auxiliary port of a cell end exactly one wire. -/
  port : ∀ c α, (c, α) ∈ G.cells → ∀ i ≤ S.arity α, G.ends.count (.port c i) = 1
  /-- An end that is a port is a port of a cell of the graph. -/
  cell : ∀ c i, End.port c i ∈ G.ends → ∃ α, (c, α) ∈ G.cells ∧ i ≤ S.arity α
  /-- A name is a free port: it ends at most one wire. -/
  name : ∀ x, G.ends.count (.name x) ≤ 1

/-- The free ports of a graph. -/
def free
    (G : Graph S ν) :
    Multiset ν :=
  -- the ends that are names
  G.ends.filterMap fun
    | .name x => some x
    | .port _ _ => none

/-- The same graph: a renaming of the cells, injective on the cells of `G`, carries the cells and
the wires of `G` to those of `H`. Symbols, ports and free ports are kept, and so is the number of
cyclic wires. -/
def Iso
    (G H : Graph S ν) :
    Prop :=
  -- there is a renaming `σ` of the cells such that
  ∃ σ : ℕ → ℕ,
    -- `σ` is injective on the cells of `G`,
    Set.InjOn σ {c | c ∈ G.cells.map Prod.fst} ∧
    -- the cells of `H` are those of `G` renamed, with the same symbols,
    H.cells = G.cells.map (Prod.map σ id) ∧
    -- the wires of `H` are those of `G`, with the cells of their ends renamed,
    H.wires = G.wires.map (Sym2.map (End.mapCell σ)) ∧
    -- and the two graphs have the same number of cyclic wires
    H.loops = G.loops

end Graph

-- ============================================================================================
-- 2. The raw graph of a text
-- ============================================================================================

namespace Term

/-- The number of cells of a tree. -/
def size : Term S ν → ℕ
  | var _ => 0
  | app _ ts => 1 + ∑ i, (ts i).size

/-- The end at the root of a tree whose cells are numbered from `k`: the name itself, or the
principal port of the root cell, which gets the number `k`. -/
def rootEnd
    -- the number of the first cell of the tree
    (k : ℕ) :
    Term S ν → End ν
  | var x => .name x
  | app _ _ => .port k 0

/-- The number given to the first cell of the `i`-th subtree, when the cell above it has the
number `k`: the subtrees are numbered one after the other, from `k + 1`. -/
def childBase
    {n : ℕ}
    -- the number of the cell above
    (k : ℕ)
    -- the subtrees on its auxiliary ports
    (ts : Fin n → Term S ν)
    -- the subtree whose first number is asked
    (i : Fin n) :
    ℕ :=
  -- after `k`, and after the cells of the subtrees before the `i`-th
  k + 1 + ∑ j : Fin n, if j < i then (ts j).size else 0

/-- The cells of a tree, numbered from `k` in prefix order. -/
def rawCells
    -- the number of the first cell of the tree
    (k : ℕ) :
    Term S ν → Multiset (ℕ × S.Sym)
  -- a leaf has no cell
  | var _ => 0
  -- the root cell has the number `k`; then the cells of the subtrees
  | app α ts => (k, α) ::ₘ ∑ i, (ts i).rawCells (childBase k ts i)

/-- The wires inside a tree: each auxiliary port of each cell is joined to the root of the subtree
plugged into it. -/
def rawWires
    -- the number of the first cell of the tree
    (k : ℕ) :
    Term S ν → Multiset (Sym2 (End ν))
  -- a leaf has no wire inside
  | var _ => 0
  -- for each auxiliary port `i` of the root cell: the wire from that port (port `i + 1` of the
  -- cell `k`) to the root of the `i`-th subtree, and the wires inside that subtree
  | app α ts => ∑ i : Fin (S.arity α),
      (s(End.port k ((i : ℕ) + 1), (ts i).rootEnd (childBase k ts i)) ::ₘ
        (ts i).rawWires (childBase k ts i))

end Term

namespace Graph

/-- The graph read off a list of equations, with cells numbered from `k`: the cells and inner
wires of every tree, and for each equation a wire between the roots of its two sides. Here a name
is not yet a free port: it ends one wire for each of its occurrences. -/
def raw : ℕ → List (Term S ν × Term S ν) → Graph S ν
  -- no equation: the empty graph
  | _, [] => ⟨0, 0, 0⟩
  -- an equation `a = b` and the rest `L`: the cells of `a` are numbered from `k`, those of `b`
  -- after them, those of `L` after them
  | k, (a, b) :: L =>
    let G := raw (k + a.size + b.size) L
    -- the cells of `a`, of `b` and of the rest
    ⟨a.rawCells k + b.rawCells (k + a.size) + G.cells,
      -- the wire between the roots of `a` and `b`, the wires inside `a`, inside `b`, and those
      -- of the rest
      s(a.rootEnd k, b.rootEnd (k + a.size)) ::ₘ
        (a.rawWires k + b.rawWires (k + a.size) + G.wires),
      -- no cyclic wire is created here
      G.loops⟩

-- ============================================================================================
-- 3. The graph of a net
-- ============================================================================================

/-- Erasing a name that ends two wires. If the two wires are different, they are joined into
one. If it is one wire from the name to itself, it becomes a cyclic wire. -/
inductive Contract : Graph S ν → Graph S ν → Prop
  -- two different wires that end at the name `x` are joined into one
  | join
      -- the name, and the other ends of its two wires
      (x : ν)
      (p q : End ν)
      -- the cells, the other wires, and the number of cyclic wires
      (C : Multiset (ℕ × S.Sym))
      (W : Multiset (Sym2 (End ν)))
      (n : ℕ) :
      Contract ⟨C, s(.name x, p) ::ₘ s(.name x, q) ::ₘ W, n⟩ ⟨C, s(p, q) ::ₘ W, n⟩
  -- a wire from the name `x` to itself becomes a cyclic wire
  | loop
      -- the name
      (x : ν)
      -- the cells, the other wires, and the number of cyclic wires
      (C : Multiset (ℕ × S.Sym))
      (W : Multiset (Sym2 (End ν)))
      (n : ℕ) :
      Contract ⟨C, s(.name x, .name x) ::ₘ W, n⟩ ⟨C, W, n + 1⟩

end Graph

/-- The text of a net given as a list of equations. -/
def Net.ofList
    (L : List (Term S ν × Term S ν)) :
    Net S ν :=
  (L.map fun e => s(e.1, e.2) : List (Sym2 (Term S ν)))

/-- **`G` is the graph of the net `N`.** Take a text of `N` as a list of equations, read off its
raw graph, and erase names that end two wires until each name ends at most one. -/
def Net.HasGraph
    [DecidableEq ν]
    -- the net
    (N : Net S ν)
    -- the graph
    (G : Graph S ν) :
    Prop :=
  -- there are a list of equations `L` and a first cell number `k` such that
  ∃ (L : List (Term S ν × Term S ν)) (k : ℕ),
    -- `L` is a text of `N`,
    N = Net.ofList L ∧
    -- the raw graph of `L`, with cells numbered from `k`, contracts to `G`,
    Relation.ReflTransGen Graph.Contract (Graph.raw k L) G ∧
    -- and in `G` every name ends at most one wire
    ∀ x, G.ends.count (.name x) ≤ 1

end INet
