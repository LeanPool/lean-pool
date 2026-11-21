/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.System
public import Mathlib.Order.Lattice.Nat

/-!
# Principal nets and translations

Lafont, "Interaction Combinators" (1997), Section 1.7.

* `PNet S n` — a principal net of arity `n`: a tree whose leaves are its `n` auxiliary ports, each
  once, and the two ends of some internal wires. It behaves like a cell with `n` auxiliary ports.
* `Translation S S'` — a principal net over `S'` for each symbol of `S`.
* `Translation.NetTr` — a net over `S'` is a translation of a net over `S`: every cell is replaced
  by an instance of the principal net of its symbol, with new names for its internal wires.
* `Translation.Compatible` — a translation of interaction systems: it is compatible with
  reduction.
* `Universal` — every interaction system can be translated into the given one.

Contents, in the order of the file:

1. Principal nets: `PNet`, `PNet.inst`, `PNet.Strict`, `PNet.cell`, `PNet.inst_cell`.
2. Translations of nets: `Translation`, `Translation.Strict`, `Translation.TermTr`,
   `Translation.EqTr`, `Translation.NetTr`.
3. Translations of interaction systems: `Translation.Compatible`.
4. The identity translation, a sanity check of the definitions: `Translation.id`,
   `Translation.termTr_id`, `Translation.eqTr_id`, `Translation.id_compatible`.
5. Universality: `Universal`, `StrictlyUniversal`, `StrictlyUniversal.universal`.
-/

@[expose] public section

namespace INet

-- the source signature `S` and the target signature `S'`, for the whole file
variable {S S' : Signature}

-- ============================================================================================
-- 1. Principal nets
-- ============================================================================================

/-- A principal net of arity `n`: a tree over the `n` auxiliary ports and some internal wires.
The root of the tree is the root of the net. -/
structure PNet (S : Signature) (n : ℕ) where
  /-- The number of internal wires. -/
  internal : ℕ
  /-- The tree: its leaves are auxiliary ports or ends of internal wires. -/
  tree : Term S (Fin n ⊕ Fin internal)
  /-- Every auxiliary port occurs exactly once. -/
  port_count : ∀ i, tree.vars.count (.inl i) = 1
  /-- Every internal wire has exactly two ends. -/
  internal_count : ∀ w, tree.vars.count (.inr w) = 2

namespace PNet

-- the arity of the principal net
variable {n : ℕ}

/-- An instance of a principal net: trees plugged into the auxiliary ports, and the internal wires
named by `f`. -/
def inst
    -- the principal net
    (p : PNet S n)
    -- the trees plugged into its auxiliary ports
    (args : Fin n → Term S ℕ)
    -- the names given to its internal wires
    (f : Fin p.internal → ℕ) :
    Term S ℕ :=
  p.tree.bind (Sum.elim args fun w => Term.var (f w))

/-- A principal net is strict when it is not a single wire: its root is the principal port of a
cell. -/
def Strict
    (p : PNet S n) :
    Prop :=
  -- the tree is not a leaf
  ∀ x, p.tree ≠ Term.var x

/-- A single cell, as a principal net. -/
def cell
    (α : S.Sym) :
    PNet S (S.arity α) where
  -- no internal wire
  internal := 0
  -- the cell, with its auxiliary ports in order
  tree := .app α fun i => .var (.inl i)
  port_count i := by
    simp [Multiset.count_sum', Multiset.count_singleton]
  internal_count w := w.elim0

/-- An instance of a single cell is the cell with the trees on its auxiliary ports. -/
@[simp] theorem inst_cell
    -- the symbol of the cell
    (α : S.Sym)
    -- the trees plugged into its auxiliary ports
    (args : Fin (S.arity α) → Term S ℕ)
    -- the names of its internal wires: there is none
    (f : Fin (cell α).internal → ℕ) :
    (cell α).inst args f = .app α args :=
  rfl

end PNet

-- ============================================================================================
-- 2. Translations of nets
-- ============================================================================================

/-- A translation of the symbols of `S` into principal nets over `S'`. -/
structure Translation (S S' : Signature) where
  /-- The principal net that stands for a symbol. -/
  net : (α : S.Sym) → PNet S' (S.arity α)

namespace Translation

/-- A translation is strict when no symbol is translated to a single wire. -/
def Strict
    (Φ : Translation S S') :
    Prop :=
  -- the principal net of every symbol has a cell at its root
  ∀ α, (Φ.net α).Strict

/-- `t'` is a translation of the tree `t`: names are kept, and every cell is replaced by an
instance of the principal net of its symbol. -/
inductive TermTr (Φ : Translation S S') : Term S ℕ → Term S' ℕ → Prop
  -- a leaf is translated to itself
  | var
      (x : ℕ) :
      TermTr Φ (.var x) (.var x)
  -- a cell is translated to an instance of the principal net of its symbol
  | app
      -- the symbol of the cell
      (α : S.Sym)
      -- the trees on its auxiliary ports
      (ts : Fin (S.arity α) → Term S ℕ)
      -- their translations
      (ts' : Fin (S.arity α) → Term S' ℕ)
      -- the names given to the internal wires of this instance: any names
      (f : Fin (Φ.net α).internal → ℕ)
      -- each `ts' i` is a translation of `ts i`
      (h : ∀ i, TermTr Φ (ts i) (ts' i)) :
      -- the instance has the translated trees plugged into its auxiliary ports
      TermTr Φ (.app α ts) ((Φ.net α).inst ts' f)

/-- `e'` is a translation of the equation `e`. -/
def EqTr
    -- the translation
    (Φ : Translation S S')
    -- the equation over `S`
    (e : Sym2 (Term S ℕ))
    -- the equation over `S'`
    (e' : Sym2 (Term S' ℕ)) :
    Prop :=
  -- there are trees `a`, `b` over `S` and `a'`, `b'` over `S'` such that
  ∃ a b a' b',
    -- `e` is the equation `a = b`,
    e = s(a, b) ∧
    -- `e'` is the equation `a' = b'`,
    e' = s(a', b') ∧
    -- `a'` is a translation of `a`,
    Φ.TermTr a a' ∧
    -- and `b'` is a translation of `b`
    Φ.TermTr b b'

/-- `N'` is a translation of the net `N`: equation by equation, and linear. Linearity forces the
internal wires of the instances to have names that are new and pairwise distinct. -/
structure NetTr (Φ : Translation S S') (N : Net S ℕ) (N' : Net S' ℕ) : Prop where
  /-- The equations of `N'` are translations of those of `N`. -/
  rel : Multiset.Rel Φ.EqTr N N'
  /-- The translated net is linear. -/
  linear : N'.Linear

-- ============================================================================================
-- 3. Translations of interaction systems
-- ============================================================================================

/-- A translation of interaction systems (Lafont, Section 1.7): for every rule, the translations of
the two cells, plugged by their roots, reduce to a translation of the right-hand side. The
auxiliary ports of the two cells are the names `xs` and `ys`. Reduction is up to wires
(`StepsE`): cells whose principal ports are joined by a named wire may interact. -/
def Compatible
    -- the translation: a principal net over `S'` for each symbol of `S`
    (Φ : Translation S S')
    -- the system that is translated, over `S`
    (I : System S)
    -- the system it is translated into, over `S'`
    (I' : System S') :
    Prop :=
  -- for all symbols `α`, `β` of `S` and every net `r` such that
  ∀ (α β : S.Sym) (r : Rule S (S.arity α) (S.arity β)),
    -- `r` is the right-hand side of the rule of `I` for an `α` cell against a `β` cell,
    I.rule α β = some r →
    ∀
      -- for all names `xs` of the auxiliary ports of the `α` cell,
      (xs : Fin (S.arity α) → ℕ)
      -- all names `ys` of the auxiliary ports of the `β` cell,
      (ys : Fin (S.arity β) → ℕ)
      -- all names `f` of the internal wires of the translation of `α`,
      (f : Fin (Φ.net α).internal → ℕ)
      -- and all names `g` of the internal wires of the translation of `β`,
      (g : Fin (Φ.net β).internal → ℕ),
      -- if the translation of `α` plugged by its root into the root of the translation of `β`
      -- is a linear net, that is, if no name among `xs`, `ys`, `f`, `g` occurs more than twice,
      Net.Linear ({s((Φ.net α).inst (fun i => .var (xs i)) f,
        (Φ.net β).inst (fun j => .var (ys j)) g)} : Net S' ℕ) →
      -- then there are two nets `M`, `N'` over `S'`, and names `h` for the wires created by the
      -- rule, such that
      ∃ (M N' : Net S' ℕ) (h : Fin r.internal → ℕ),
        -- in `I'`, the two translations plugged by their roots reduce, up to wires, to `M`,
        StepsE I' {s((Φ.net α).inst (fun i => .var (xs i)) f,
          (Φ.net β).inst (fun j => .var (ys j)) g)} M ∧
        -- `M` is the same graph as `N'`,
        Equiv M N' ∧
        -- and `N'` is a translation of the right-hand side of the rule, taken with the same
        -- names `xs` and `ys` on the auxiliary ports of the two cells and with `h` on its wires
        Φ.NetTr (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) h) N'

-- ============================================================================================
-- 4. The identity translation
-- ============================================================================================

/-- Every symbol is translated to itself. -/
protected def id
    (S : Signature) :
    Translation S S :=
  ⟨PNet.cell⟩

/-- Under the identity translation, every tree is a translation of itself. -/
theorem termTr_id
    (t : Term S ℕ) :
    (Translation.id S).TermTr t t := by
  induction t with
  | var x => exact .var x
  | app α ts ih => exact TermTr.app (Φ := Translation.id S) α ts ts Fin.elim0 ih

/-- Under the identity translation, every equation is a translation of itself. -/
theorem eqTr_id
    (e : Sym2 (Term S ℕ)) :
    (Translation.id S).EqTr e e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, a, b, rfl, rfl, termTr_id a, termTr_id b⟩

/-- A sanity check of the definitions: the identity translation of a well-formed system into
itself is a translation of interaction systems. -/
theorem id_compatible
    -- a well-formed interaction system
    (I : System S)
    (hI : I.WellFormed) :
    (Translation.id S).Compatible I I := by
  intro α β r hr xs ys f g hlin
  let L : Sym2 (Term S ℕ) := s(.app α fun i => .var (xs i), .app β fun j => .var (ys j))
  let k : ℕ := (Net.vars ({L} : Net S ℕ)).sup + 1
  have hstep : Step I (L ::ₘ 0)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w) + 0) :=
    Step.mk α β r hr _ _ 0 (fun w => k + w)
      (fun a b hab => Fin.ext (by simpa using hab))
      (fun w hw => by
        have hle : k + w ≤ (Net.vars ({L} : Net S ℕ)).sup :=
          Multiset.le_sup (show k + (w : ℕ) ∈ Net.vars ({L} : Net S ℕ) from hw)
        omega)
  have hstep' : Step I ({L} : Net S ℕ)
      (r.inst (fun i => .var (xs i)) (fun j => .var (ys j)) (fun w => k + w)) := by
    simpa using hstep
  refine ⟨_, _, fun w => k + w, (Steps.single hstep').stepsE, Equiv.refl _, ?_, ?_⟩
  · exact Multiset.rel_refl_of_refl_on fun e _ => eqTr_id e
  · exact hstep'.linear hI.linear hlin

end Translation

-- ============================================================================================
-- 5. Universality
-- ============================================================================================

/-- A universal interaction system: every interaction system over a finite alphabet can be
translated into it. -/
def Universal
    -- the system, over the signature `S'`
    (I' : System S') :
    Prop :=
  ∀
    -- for every signature `S`
    (S : Signature)
    -- with finitely many symbols,
    [Finite S.Sym]
    -- and every system `I` over `S`
    (I : System S),
    -- that is an interaction system in the sense of Lafont,
    I.WellFormed →
    -- there is a translation `Φ` of the symbols of `S` into principal nets over `S'`
    ∃ Φ : Translation S S',
      -- that is a translation of the interaction system `I` into `I'`
      Φ.Compatible I I'

/-- A strictly universal interaction system: every interaction system over a finite alphabet has a
strict translation into it. Strictness excludes translations that erase cells by turning them into
wires, so every interaction of the source costs at least one interaction of the target. -/
def StrictlyUniversal
    -- the system, over the signature `S'`
    (I' : System S') :
    Prop :=
  ∀
    -- for every signature `S`
    (S : Signature)
    -- with finitely many symbols,
    [Finite S.Sym]
    -- and every system `I` over `S`
    (I : System S),
    -- that is an interaction system in the sense of Lafont,
    I.WellFormed →
    -- there is a translation `Φ` of the symbols of `S` into principal nets over `S'`
    ∃ Φ : Translation S S',
      -- that translates no symbol to a single wire,
      Φ.Strict ∧
      -- and that is a translation of the interaction system `I` into `I'`
      Φ.Compatible I I'

/-- A strictly universal interaction system is universal. -/
theorem StrictlyUniversal.universal
    {I' : System S'}
    (h : StrictlyUniversal I') :
    Universal I' :=
  fun S _ I hI => (h S I hI).imp fun _ hΦ => hΦ.2

end INet
