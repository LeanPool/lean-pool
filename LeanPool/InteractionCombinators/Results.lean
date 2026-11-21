/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduction.NormalFormE
public import LeanPool.InteractionCombinators.Reduced.ReducedDecompUnique
public import LeanPool.InteractionCombinators.Reduced.ViciousReflect
public import LeanPool.InteractionCombinators.Translations.SimulationE
public import LeanPool.InteractionCombinators.Translations.SimulationUniform
public import LeanPool.InteractionCombinators.Translations.PairStepEReduced
public import LeanPool.InteractionCombinators.Translations.TranslationRenPerm
public import LeanPool.InteractionCombinators.Graphs.GraphStepEConverse
public import LeanPool.InteractionCombinators.Universality.Multiplexors.TranspositorConverse
public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFreeCompatible
public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFreeTerminates
public import LeanPool.InteractionCombinators.Universality.General.CodeCompatibleSides
public import LeanPool.InteractionCombinators.Universality.Theorem1
public import LeanPool.InteractionCombinators.Reduced.ReducedClosed

/-!
# Lafont, "Interaction Combinators" (1997): the results

This is the front page of a formalization in Lean 4 of Yves Lafont, *Interaction Combinators*
(Information and Computation 137, 1997, pages 69-101). The project proves Theorem 1 of the paper,
"any interaction system can be translated into the system of interaction combinators", together
with the propositions and lemmas of Sections 1 and 2 that lead to it.

This file proves nothing new. It restates the main results in the order and with the numbering of
the paper, each as a theorem proved in one line from the theorem of the library that its
docstring names. Lean checks that each statement written here follows from the library.

Names. The code uses the following names for the three combinators:

* `con` (`mkCon a b`) is Lafont's `γ`, the constructor, of arity 2;
* `dup` (`mkDup a b`) is Lafont's `δ`, the duplicator, of arity 2;
* `era` (`mkEra`) is Lafont's `ε`, the eraser, of arity 0.

The system is Lafont's: `con`-`con` exchanges the auxiliary ports, `dup`-`dup` does not.

Nets are text. A tree (`Term S ν`) is a name or a cell whose root is its principal port, with a
tree on each auxiliary port. A net (`Net S ν`) is a multiset of unordered equations `s(t, u)`
between trees. A name is a wire: a name that occurs twice is an internal wire, a name that occurs
once is a free port, and a net is linear (`Net.Linear`) when no name occurs more than twice.

* `Equiv N M`: the two texts are the same graph (they differ by wire substitutions). Section 4
  below proves that this is isomorphism of graphs.
* `Step I N M`, `Steps I N M` (`Red` for the combinators): one interaction, several interactions,
  on the text as it is written: the active pair is an equation between two cells.
* `StepE I N M`, `StepsE I N M`, `StepsEN I n N M`: one interaction, several, exactly `n`, of the
  graph: the text may be rewritten into an equivalent one before each interaction.
* `Φ.NetTr N N'`: `N'` is a translation `Φ(N)` of `N`; a relation, because the new internal wires
  can be named freely.
* Every statement about a net carries the rest of the net as a variable `Δ`.

Contents, in the order of the file:

1. Reduction (Section 1.2, pages 73-74): `proposition_1`, `normal_form_unique`,
   `normal_form_reached`.
2. Reduced nets (Section 1.6, pages 77-80): `proposition_2_exists`, `proposition_2_unique`,
   `reduced_iff_trees_on_wiring`, `reduced_closed_empty`.
3. Translations (Section 1.7, pages 80-81): `proposition_3`, `proposition_3_converse`,
   `invertible_iff_renaming`, the abbreviation `LinearRules`, `proposition_4`,
   `proposition_4_bounds`, `bounds_exist`, `bounds_pos_of_strict`, `bounds_one_of_invertible`.
4. Nets as graphs (Section 1.1, page 71): `graph_exists`, `graph_unique`, `equiv_iff_graph_iso`,
   `graph_of_net`, `step_is_interaction`, `interaction_is_step`.
5. The combinators (Sections 2.1-2.3, pages 81-85): `combinators_wellFormed`,
   the abbreviation `Wires`, `multiplexor_property`, `autodual_multiplexor_property`,
   `transpositor_property`, `transpositor_involutive`, `lemma_2_erase_package`,
   `menu_selector_property`.
6. Recursion-free systems (Section 2.4, pages 85-87): `recursion_free_compatible`,
   `recursion_free_strict`, `recursion_free_terminates`.
7. Duplication and codes (Sections 2.5-2.6, pages 87-89): the abbreviation `CopyOf`,
   `lemma_3_dup_package`, `copier_property`, `decoder_property`.
8. Theorem 1 (Section 2.7, pages 82 and 90): `theorem_1`, `theorem_1_strict`,
   `theorem_1_explicit`, `theorem_1_bounds`.
-/

@[expose] public section

namespace INet.Results

open Term Comb

-- the signatures of the source and of the target of a translation, for the whole file
variable {S S' : Signature}

-- ============================================================================================
-- 1. Reduction (Section 1.2, pages 73-74)
-- ============================================================================================

/-- **Proposition 1** (Lafont 1997, page 73): "If a net `N` reduces in one step to `P` and to
`P'`, with `P ≠ P'`, then `P` and `P'` reduce in one step to a common `Q`." Nets are graphs: one
step is `StepE` and equality is `Equiv`. The net is linear and the system is an interaction system
in the sense of Lafont (`System.WellFormed`).

Library: `INet.StepE.strong_confluence` in
`InteractionCombinators/Reduction/StrongConfluenceE.lean`. -/
theorem proposition_1
    -- an interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a linear net `N` that reduces in one step to `P` and to `P'`
    {N P P' : Net S ℕ}
    (hN : N.Linear)
    (h : StepE I N P)
    (h' : StepE I N P') :
    -- `P` and `P'` are the same graph,
    Equiv P P' ∨
    -- or they reduce in one step to nets `Q` and `Q'`
    ∃ Q Q', StepE I P Q ∧ StepE I P' Q' ∧
      -- that are the same graph
      Equiv Q Q' :=
  StepE.strong_confluence hI hN h h'

/-- **One normal form, one length** (Lafont 1997, pages 73-74, the consequence of Proposition 1).
If a linear net `N` reduces in `n` steps to an irreducible net `P` and in `m` steps to an
irreducible net `Q`, then `m = n` and `P`, `Q` are the same graph.

Library: `INet.StepsEN.normal_unique` in `InteractionCombinators/Reduction/NormalFormE.lean`. -/
theorem normal_form_unique
    -- an interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a linear net `N`
    {N P Q : Net S ℕ}
    (hN : N.Linear)
    -- that reduces in `n` steps to the irreducible net `P`
    {n m : ℕ}
    (hP : StepE.Normal I P)
    (hs : StepsEN I n N P)
    -- and in `m` steps to the irreducible net `Q`
    (hQ : StepE.Normal I Q)
    (ht : StepsEN I m N Q) :
    -- the two reductions have the same length,
    m = n ∧
    -- and the two normal forms are the same graph
    Equiv P Q :=
  StepsEN.normal_unique hI hN hP hQ hs ht

/-- **Every reduction reaches the normal form, in the same number of steps** (Lafont 1997,
pages 73-74: "if a net `N` reduces to an irreducible net `P` in `n` steps, then any reduction
starting from `N` eventually reaches `P` in `n` steps"). If `N` reduces in `n` steps to an
irreducible `P` and in `k` steps to any `Q`, then `k ≤ n` and `Q` reduces to `P` in the `n - k`
remaining steps.

Library: `INet.StepsEN.normal_of_stepsEN` in `InteractionCombinators/Reduction/NormalFormE.lean`. -/
theorem normal_form_reached
    -- an interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a linear net `N`
    {N P Q : Net S ℕ}
    (hN : N.Linear)
    -- that reduces in `n` steps to the irreducible net `P`
    {n k : ℕ}
    (hP : StepE.Normal I P)
    (hs : StepsEN I n N P)
    -- and in `k` steps to some net `Q`
    (hk : StepsEN I k N Q) :
    -- the reduction to `Q` is not longer,
    k ≤ n ∧
    -- and `Q` reduces in `n - k` steps to a net `P'`
    ∃ P', StepsEN I (n - k) Q P' ∧
      -- that is the same graph as `P`
      Equiv P' P :=
  StepsEN.normal_of_stepsEN hI hN hP hs hk

-- ============================================================================================
-- 2. Reduced nets (Section 1.6, pages 77-80)
-- ============================================================================================

/-- **Proposition 2, existence** (Lafont 1997, page 79): "Any reduced net with `n` free ports can
be uniquely decomposed as follows": trees hanging from the free ports, their leaves joined by a
wiring. A linear net with no cut and no vicious circle (`Net.IsReduced`) is the same graph as a
net in the normal form `Net.IsTreesOnWiringN`: every equation is `x = t` with `x` a free port, and
an equation between two names joins two free ports.

Library: `INet.Net.IsReduced.exists_treesOnWiringN` in
`InteractionCombinators/Reduced/ReducedDecompUnique.lean`. -/
theorem proposition_2_exists
    -- a linear net with no cut and no vicious circle
    {N : Net S ℕ}
    (hN : N.Linear)
    (hR : N.IsReduced) :
    -- some net `M` is the same graph as `N`
    ∃ M, Equiv N M ∧
      -- and is made of trees hanging from its free ports
      M.IsTreesOnWiringN :=
  Net.IsReduced.exists_treesOnWiringN hN hR

/-- **Proposition 2, uniqueness** (Lafont 1997, page 79: "uniquely decomposed"). Two nets in the
normal form `Net.IsTreesOnWiringN` that are the same graph differ only by the names of the wires
of the wiring: one is the other renamed by a function that keeps the free ports and is injective
on the names. Linearity is not assumed.

Library: `INet.Net.IsTreesOnWiringN.unique` in
`InteractionCombinators/Reduced/ReducedDecompUnique.lean`. -/
theorem proposition_2_unique
    -- two nets
    {N M : Net S ℕ}
    -- both made of trees hanging from their free ports
    (hn : N.IsTreesOnWiringN)
    (hm : M.IsTreesOnWiringN)
    -- that are the same graph
    (h : Equiv N M) :
    -- there is a renaming `ρ` of the names
    ∃ ρ : ℕ → ℕ,
      -- that keeps the free ports of `N`,
      (∀ x, N.vars.count x = 1 → ρ x = x) ∧
      -- is injective on the names of `N`,
      Set.InjOn ρ {x | x ∈ N.vars} ∧
      -- and carries the text of `N` to the text of `M`
      M = N.bind (fun x => var (ρ x)) :=
  Net.IsTreesOnWiringN.unique hn hm h

/-- **Reduced is "trees on a wiring"** (Lafont 1997, Proposition 2, page 79, with its converse). A
linear net is reduced if and only if it is the same graph as a net each of whose equations is
`x = t` with `x` a free port (`Net.IsTreesOnWiring`).

Library: `INet.Net.isReduced_iff_exists_treesOnWiring` in
`InteractionCombinators/Reduced/ReducedDecomp.lean`. -/
theorem reduced_iff_trees_on_wiring
    -- a linear net
    {N : Net S ℕ}
    (hN : N.Linear) :
    -- it has no cut and no vicious circle exactly when it is the same graph as a net made of
    -- trees hanging from its free ports
    N.IsReduced ↔ ∃ M, Equiv N M ∧ M.IsTreesOnWiring :=
  Net.isReduced_iff_exists_treesOnWiring hN

/-- **A reduced net with no free port is empty** (Lafont 1997, page 80: "a reduced net with no
free port is necessarily empty").

Library: `INet.Net.IsReduced.eq_zero_of_closed` in
`InteractionCombinators/Reduced/ReducedClosed.lean`. -/
theorem reduced_closed_empty
    -- a linear net with no cut and no vicious circle
    {N : Net S ℕ}
    (hN : N.Linear)
    (hR : N.IsReduced)
    -- and no free port: no name occurs exactly once
    (hfree : ∀ x, N.vars.count x ≠ 1) :
    -- it has no equation
    N = 0 :=
  Net.IsReduced.eq_zero_of_closed hN hR hfree

-- ============================================================================================
-- 3. Translations (Section 1.7, pages 80-81)
-- ============================================================================================

/-- **Proposition 3** (Lafont 1997, page 80): "If `ν` is a reduced net, then `Φ(ν)` is a reduced
net." A cut of `Φ(ν)` comes from a cut of `ν`, and a vicious circle of `Φ(ν)` from a vicious
circle or a cut of `ν`.

Library: `INet.Translation.NetTr.isReduced` in
`InteractionCombinators/Reduced/ViciousReflect.lean`. -/
theorem proposition_3
    -- a translation `Φ`, a net `N` and a translation `N'` of `N`
    {Φ : Translation S S'}
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Φ.NetTr N N')
    -- `N` is reduced
    (hN : N.IsReduced) :
    -- then `Φ(N)` is reduced
    N'.IsReduced :=
  h.isReduced hN

/-- **Proposition 3, the converse** (Lafont 1997, page 80): "The converse holds if `Φ` is strict."

Library: `INet.Translation.NetTr.isReduced_of_strict` in
`InteractionCombinators/Reduced/ViciousReflect.lean`. -/
theorem proposition_3_converse
    -- a strict translation `Φ`, a net `N` and a translation `N'` of `N`
    {Φ : Translation S S'}
    (hΦ : Φ.Strict)
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Φ.NetTr N N')
    -- `Φ(N)` is reduced
    (hN' : N'.IsReduced) :
    -- then `N` is reduced
    N.IsReduced :=
  h.isReduced_of_strict hΦ hN'

/-- **The invertible translations** (Lafont 1997, page 81, top): "`Φ` is given by a renaming of
the symbols and a permutation of the auxiliary ports of each symbol". `Φ` is invertible if and
only if there are a bijection `e` of the symbols and, for each symbol `α`, a bijection `ρ α` of
the auxiliary ports of `e α` onto those of `α`, such that `Φ(α)` is the cell `e α` with its
port `j` plugged into the port `ρ α j` (`Translation.renPermTr e ρ`).

Library: `INet.Translation.invertible_iff_renPermTr` in
`InteractionCombinators/Translations/TranslationRenPerm.lean`. -/
theorem invertible_iff_renaming
    -- a translation
    (Φ : Translation S S') :
    -- it is invertible exactly when there are a bijection `e` of the symbols and bijections `ρ`
    -- of the ports
    Φ.Invertible ↔
      ∃ (e : S.Sym ≃ S'.Sym) (ρ : ∀ α, Fin (S'.arity (e α)) ≃ Fin (S.arity α)),
        -- such that every `Φ(α)` is the same graph as the cell `e α` with its ports permuted
        ∀ α, (Φ.net α).Iso ((Translation.renPermTr e ρ).net α) :=
  Translation.invertible_iff_renPermTr Φ

/-- The right member of every rule of the system `I` is a linear net: each port of the two cells
occurs once and each new wire twice (Lafont 1997, page 73). It is the first condition of
`System.WellFormed`, and the only one Proposition 4 uses. -/
abbrev LinearRules
    -- the system
    (I : System S) :
    Prop :=
  ∀ α β r, I.rule α β = some r → r.Linear

/-- **Proposition 4** (Lafont 1997, page 81): if `Φ` is a translation of interaction systems from
`I` to `I'` and `N` reduces to `M`, then `Φ(N)` reduces to `Φ(M)`. Reduction is reduction of
graphs on both sides, and `Φ(M)` is reached up to `Equiv`. Only the linearity of the rules of the
two systems is used.

Library: `INet.Translation.Compatible.stepsE` in
`InteractionCombinators/Translations/SimulationE.lean`. -/
theorem proposition_4
    -- two systems whose rules are linear
    {I : System S}
    {I' : System S'}
    (hI : LinearRules I)
    (hI' : LinearRules I')
    -- a translation of interaction systems from `I` to `I'`
    {Φ : Translation S S'}
    (hΦ : Φ.Compatible I I')
    -- a net `N` that reduces to `M`, and a translation `N'` of `N`
    {N M : Net S ℕ}
    {N' : Net S' ℕ}
    (h : StepsE I N M)
    (hT : Φ.NetTr N N') :
    -- `Φ(N)` reduces to a net `M₁`
    ∃ M₁ M', StepsE I' N' M₁ ∧
      -- that is the same graph as `M'`,
      Equiv M₁ M' ∧
      -- a translation of `M`
      Φ.NetTr M M' :=
  hΦ.stepsE hI hI' h hT

/-- **Proposition 4, with the lengths** (Lafont 1997, page 81): "If `N` reduces in `n` steps to
`M`, then `Φ(N)` reduces in `n'` steps to `Φ(M)`, with `L n ≤ n' ≤ M n`", where every rule is
simulated in at least `L` and at most `M` steps (`Translation.CompatibleWithin`). Here the upper
bound is called `U`, because `M` is a net.

Library: `INet.Translation.CompatibleWithin.stepsEN` in
`InteractionCombinators/Translations/SimulationE.lean`. -/
theorem proposition_4_bounds
    -- two systems whose rules are linear
    {I : System S}
    {I' : System S'}
    (hI : LinearRules I)
    (hI' : LinearRules I')
    -- a translation that simulates every rule in at least `L` and at most `U` steps
    {Φ : Translation S S'}
    {L U : ℕ}
    (hΦ : Φ.CompatibleWithin I I' L U)
    -- a net `N` that reduces in `n` steps to `M`, and a translation `N'` of `N`
    {n : ℕ}
    {N M : Net S ℕ}
    {N' : Net S' ℕ}
    (h : StepsEN I n N M)
    (hT : Φ.NetTr N N') :
    -- `Φ(N)` reduces in `n'` steps to a net `M₁`,
    ∃ n' M₁ M', StepsEN I' n' N' M₁ ∧
      -- with `L n ≤ n'`
      L * n ≤ n' ∧
      -- and `n' ≤ U n`,
      n' ≤ U * n ∧
      -- and `M₁` is the same graph as `M'`,
      Equiv M₁ M' ∧
      -- a translation of `M`
      Φ.NetTr M M' :=
  hΦ.stepsEN hI hI' h hT

/-- **The bounds `L` and `M` exist** (Lafont 1997, page 81: "let `L` (resp. `M`) be the minimal
(resp. maximal) length of all those reductions"). A translation of interaction systems from a
system with finitely many symbols simulates every rule in a number of steps between two bounds.

Library: `INet.Translation.Compatible.exists_compatibleWithin` in
`InteractionCombinators/Translations/SimulationUniform.lean`. -/
theorem bounds_exist
    -- an interaction system with finitely many symbols
    [Finite S.Sym]
    {I : System S}
    (hI : I.WellFormed)
    -- a system whose rules are linear
    {I' : System S'}
    (hI' : LinearRules I')
    -- a translation of interaction systems from `I` to `I'`
    {Φ : Translation S S'}
    (hΦ : Φ.Compatible I I') :
    -- every rule is simulated in at least `L` and at most `U` steps
    ∃ L U, Φ.CompatibleWithin I I' L U :=
  hΦ.exists_compatibleWithin hI hI'

/-- **`L > 0` if `Φ` is strict** (Lafont 1997, page 81).

Library: `INet.Translation.Compatible.exists_compatibleWithin_pos` in
`InteractionCombinators/Translations/SimulationUniform.lean`. -/
theorem bounds_pos_of_strict
    -- an interaction system with finitely many symbols
    [Finite S.Sym]
    {I : System S}
    (hI : I.WellFormed)
    -- a system whose rules are linear
    {I' : System S'}
    (hI' : LinearRules I')
    -- a strict translation of interaction systems from `I` to `I'`
    {Φ : Translation S S'}
    (hs : Φ.Strict)
    (hΦ : Φ.Compatible I I') :
    -- every rule is simulated in at least `L > 0` and at most `U` steps
    ∃ L U, 0 < L ∧ Φ.CompatibleWithin I I' L U :=
  hΦ.exists_compatibleWithin_pos hI hI' hs

/-- **`L = M = 1` if `Φ` is invertible** (Lafont 1997, page 81). The rules of the two systems are
linear and in reduced form (`Rule.Reduced`); the two other conditions of `System.WellFormed` are
not used.

Library: `INet.Translation.Invertible.compatibleWithin_one_of_linear_reduced` in
`InteractionCombinators/Translations/PairStepEReduced.lean`. -/
theorem bounds_one_of_invertible
    -- a system whose rules are linear and reduced
    {I : System S}
    (hIl : LinearRules I)
    (hIr : ∀ α β r, I.rule α β = some r → r.Reduced)
    -- another one
    {I' : System S'}
    (hIl' : LinearRules I')
    (hIr' : ∀ α β r, I'.rule α β = some r → r.Reduced)
    -- an invertible translation of interaction systems from `I` to `I'`
    {Φ : Translation S S'}
    (hi : Φ.Invertible)
    (hΦ : Φ.Compatible I I') :
    -- every rule is simulated in exactly one step
    Φ.CompatibleWithin I I' 1 1 :=
  hi.compatibleWithin_one_of_linear_reduced hIl hIr hIl' hIr' hΦ

-- ============================================================================================
-- 4. Nets as graphs (Section 1.1, page 71)
-- ============================================================================================

/-- **Every net has a graph** (Lafont 1997, page 71: a net is a finite set of cells and free
ports, joined two by two by wires). The graph is well formed (`Graph.WF`): every port of every
cell ends exactly one wire, and a name ends at most one. No linearity is needed here.

Library: `INet.Net.exists_graph` in `InteractionCombinators/Graphs/GraphContract.lean`. -/
theorem graph_exists
    -- a net, over any type of names
    {ν : Type}
    [DecidableEq ν]
    (N : Net S ν) :
    -- it has a graph `G`, and `G` is well formed
    ∃ G, N.HasGraph G ∧ G.WF :=
  Net.exists_graph N

/-- **The graph of a linear net is unique** (Lafont 1997, page 71), up to the identity of the
cells (`Graph.Iso`).

Library: `INet.Net.Linear.hasGraph_iso` in `InteractionCombinators/Graphs/GraphIso.lean`. -/
theorem graph_unique
    -- a linear net, over any type of names
    {ν : Type}
    [DecidableEq ν]
    {N : Net S ν}
    (hN : N.Linear)
    -- two graphs of it
    {G G' : Graph S ν}
    (h : N.HasGraph G)
    (h' : N.HasGraph G') :
    -- they are isomorphic
    G.Iso G' :=
  hN.hasGraph_iso h h'

/-- **`Equiv` is equality of graphs** (Lafont 1997, Section 1.1, page 71). Two linear nets are
`Equiv` if and only if their graphs are isomorphic. This is what justifies reading "the same net"
of the paper as `Equiv` everywhere in this development.

Library: `INet.Net.Linear.equiv_iff_hasGraph_iso` in
`InteractionCombinators/Graphs/GraphIsoEquiv.lean`. -/
theorem equiv_iff_graph_iso
    -- two linear nets
    {N M : Net S ℕ}
    (hN : N.Linear)
    (hM : M.Linear)
    -- with their graphs
    {G G' : Graph S ℕ}
    (hG : N.HasGraph G)
    (hG' : M.HasGraph G') :
    -- the texts differ by wire substitutions exactly when the graphs are isomorphic
    Equiv N M ↔ G.Iso G' :=
  hN.equiv_iff_hasGraph_iso hM hG hG'

/-- **Every well-formed graph is the graph of a linear net, with the same free ports** (Lafont
1997, Section 1.1, page 71). So the text loses nothing: every picture can be written. The graph
of the net is isomorphic to `G`, not equal, because the cells of the graph of a net are numbered
in the order of its text. Without its last part this is `INet.Graph.WF.exists_net`.

Library: `INet.Graph.WF.exists_net_free` in `InteractionCombinators/Graphs/GraphRealize.lean`. -/
theorem graph_of_net
    -- a well-formed graph
    {G : Graph S ℕ}
    (h : G.WF) :
    -- there are a linear net `N`
    ∃ (N : Net S ℕ) (G' : Graph S ℕ), N.Linear ∧
      -- with a graph `G'`
      N.HasGraph G' ∧
      -- isomorphic to `G`,
      G'.Iso G ∧
      -- and the names that occur once in `N` are the free ports of `G`
      ∀ x, N.vars.count x = 1 ↔ x ∈ G.free :=
  h.exists_net_free

/-- **An interaction of texts is an interaction of graphs** (Lafont 1997, Section 1.2, page 73).
If a linear net `N` with graph `G` reduces by one `StepE` to `M`, then `G` has an interaction
(`Graph.Interact`: remove two cells joined by their principal ports, put the right member of
their rule in their place) whose result is a graph of `M`, up to isomorphism.

Library: `INet.Net.Linear.stepE_interact` in `InteractionCombinators/Graphs/GraphStepE.lean`. -/
theorem step_is_interaction
    -- a system whose rules are linear
    {I : System S}
    (hI : LinearRules I)
    -- a linear net `N` that reduces in one step to `M`
    {N M : Net S ℕ}
    (hN : N.Linear)
    (h : StepE I N M)
    -- the graph of `N`
    {G : Graph S ℕ}
    (hG : N.HasGraph G) :
    -- `G` has an interaction, to a graph `H`,
    ∃ H H', Graph.Interact I G H ∧
      -- `M` has a graph `H'`,
      M.HasGraph H' ∧
      -- and `H` is isomorphic to `H'`
      H.Iso H' :=
  hN.stepE_interact hI h hG

/-- **An interaction of graphs is an interaction of texts** (Lafont 1997, Section 1.2, page 73).
If the graph `G` of a linear net `N` has an interaction to `H`, then `N` reduces by one `StepE`
to a net whose graph is `H`, up to isomorphism. With `step_is_interaction`: `StepE` is the
reduction of the paper.

Library: `INet.Net.Linear.interact_stepE` in
`InteractionCombinators/Graphs/GraphStepEConverse.lean`. -/
theorem interaction_is_step
    -- a system whose rules are linear
    {I : System S}
    (hI : LinearRules I)
    -- a linear net `N` and its graph `G`
    {N : Net S ℕ}
    (hN : N.Linear)
    {G H : Graph S ℕ}
    (hG : N.HasGraph G)
    -- an interaction of `G`, to `H`
    (h : Graph.Interact I G H) :
    -- `N` reduces in one step to a net `M`
    ∃ M H', StepE I N M ∧
      -- that has a graph `H'`,
      M.HasGraph H' ∧
      -- and `H` is isomorphic to `H'`
      H.Iso H' :=
  hN.interact_stepE hI hG h

-- ============================================================================================
-- 5. The combinators (Sections 2.1-2.3, pages 81-85)
-- ============================================================================================

/-- **The combinators form an interaction system** (Lafont 1997, pages 81-82, Fig. 2): the six
rules of `con`, `dup` and `era` have linear, reduced right members, there is one rule for each
pair of symbols, and "the symmetry condition is satisfied".

Library: `INet.Comb.system_wellFormed` in `InteractionCombinators/Core/Combinators.lean`. -/
theorem combinators_wellFormed :
    Comb.system.WellFormed :=
  Comb.system_wellFormed

/-- The `n` wires that join the trees `ts` to the trees `us`, in order: the equations
`ts[i] = us[i]` (Lafont 1997, pages 82-83, the right members of the pictures of `M_n` and
`T_n`). -/
abbrev Wires
    -- the trees on the two ends of the wires
    (ts us : List (Term sig ℕ)) :
    CNet :=
  (List.zipWith (fun t u => s(t, u)) ts us : CNet)

/-- **The property of the multiplexors** (Lafont 1997, pages 82-83, Fig. 4): `M_n` plugged into
`M_n*` by the roots reduces to `n` wires. Here `mux ts` is `M_n` with the trees `ts` on its `n`
auxiliary ports, and the reduction is literal (`Red`), which is stronger than up to wires.

Library: `INet.Comb.mux_muxStar` in
`InteractionCombinators/Universality/Multiplexors/Multiplexor.lean`. -/
theorem multiplexor_property
    -- the trees `ts` on the auxiliary ports of `M_n`, `us` on those of `M_n*`
    (ts us : List (Term sig ℕ))
    -- the rest of the net
    (Δ : CNet)
    -- both multiplexors have the same arity `n`
    (hlen : ts.length = us.length) :
    -- `M_n` against `M_n*`, with `Δ`, reduces to the `n` wires, with `Δ`
    Red (s(mux ts, muxStar us) ::ₘ Δ) (Wires ts us + Δ) :=
  Comb.mux_muxStar ts us Δ hlen

/-- **The property of the autodual multiplexor `T_n`** (Lafont 1997, page 83, Fig. 5): two copies
of `T_n` plugged by their roots reduce to `n` wires. The reduction is literal (`Red`).

Library: `INet.Comb.autoMux_autoMux` in
`InteractionCombinators/Universality/Multiplexors/AutoMux.lean`. -/
theorem autodual_multiplexor_property
    -- the trees `ts` on the auxiliary ports of one `T_n`, `us` on those of the other
    (ts us : List (Term sig ℕ))
    -- the rest of the net
    (Δ : CNet)
    -- both have the same arity `n`
    (hlen : ts.length = us.length) :
    -- `T_n` against `T_n`, with `Δ`, reduces to the `n` wires, with `Δ`
    Red (s(autoMux ts, autoMux us) ::ₘ Δ) (Wires ts us + Δ) :=
  Comb.autoMux_autoMux ts us Δ hlen

/-- **The property of the transpositor `T_σ`** (Lafont 1997, page 84): for an involutive
permutation σ of `n` ports, two copies of `T_σ` plugged by their roots reduce to the wiring σ: the
port `i` of one copy is joined to the port `σ i` of the other. The reduction is literal (`Red`).

Library: `INet.Comb.transpositorPerm_transpositorPerm` in
`InteractionCombinators/Universality/Multiplexors/TranspositorPerm.lean`. -/
theorem transpositor_property
    -- an involutive permutation of the `n` ports
    {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (hσ : Function.Involutive σ)
    -- the trees plugged into the ports of the two copies
    (ts us : Fin n → Term sig ℕ)
    -- the rest of the net
    (Δ : CNet) :
    -- `T_σ` against `T_σ`, with `Δ`, reduces to the wires `ts i = us (σ i)`, with `Δ`
    Red (s(transpositorPerm σ hσ ts, transpositorPerm σ hσ us) ::ₘ Δ)
      ((Finset.univ.val.map fun i => s(ts i, us (σ i))) + Δ) :=
  Comb.transpositorPerm_transpositorPerm σ hσ ts us Δ

/-- **Conversely, σ is involutive** (Lafont 1997, page 84: "if such a `T_σ` exists, the
permutation σ is necessarily involutive. This is a consequence of the symmetry condition"). In
any interaction system: if two copies of a principal net `p`, plugged by their roots, with ports
named `0, …, n - 1` and `n, …, 2n - 1`, reduce to the wiring that joins the port `i` of the first
to the port `σ i` of the second, then σ is involutive.

Library: `INet.involutive_of_transpositor` in
`InteractionCombinators/Universality/Multiplexors/TranspositorConverse.lean`. -/
theorem transpositor_involutive
    -- an interaction system
    {I : System S}
    (hI : I.WellFormed)
    -- a principal net `p` with `n` ports, and a permutation σ
    {n : ℕ}
    (p : PNet S n)
    (σ : Equiv.Perm (Fin n))
    -- the names of the internal wires of the first copy (`f`) and of the second (`g`)
    (f g : Fin p.internal → ℕ)
    -- the two copies plugged by their roots form a linear net
    (hlin : Net.Linear
      (s(p.inst (fun i => var (i : ℕ)) f, p.inst (fun i => var (n + (i : ℕ))) g) ::ₘ 0))
    -- they reduce to a net `M` that is the same graph as the wiring σ
    (h : ∃ M, StepsE I
        (s(p.inst (fun i => var (i : ℕ)) f, p.inst (fun i => var (n + (i : ℕ))) g) ::ₘ 0) M ∧
      Equiv M (Finset.univ.val.map fun i : Fin n => s(var (i : ℕ), var (n + (σ i : ℕ))))) :
    -- σ is involutive
    Function.Involutive σ :=
  involutive_of_transpositor hI p σ f g hlin h

/-- **Lemma 2, corollary: a package is erased** (Lafont 1997, page 84). A package is a tree in
which every name occurs twice: a principal net with no free port but its root. Plugged into an
`era`, it reduces to the empty net: by Lemma 2 (i) the tree is erased and leaves an `era` on each
leaf, by Lemma 2 (ii) the wiring between the leaves is erased.

Library: `INet.Comb.erase_package` in `InteractionCombinators/Universality/Menus/Package.lean`. -/
theorem lemma_2_erase_package
    -- the package
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the package plugged into an `era`, and `Δ`
    (hlin : Net.Linear (s(mkEra, π) ::ₘ Δ)) :
    -- the package is erased, and `Δ` is left
    StepsE system (s(mkEra, π) ::ₘ Δ) Δ :=
  Comb.erase_package π hπ Δ hlin

/-- **The property of menus and selectors** (Lafont 1997, page 84): the menu `π₁ & ⋯ & πₙ`
plugged into the selector `Sⁱₙ` reduces to `πᵢ`; the other packages are erased. The index `i`
counts from 0, and `x` is the free port of the selector.

Library: `INet.Comb.menu_selector` in `InteractionCombinators/Universality/Menus/Menu.lean`. -/
theorem menu_selector_property
    -- the packages of the menu
    (πs : List (Term sig ℕ))
    (hπ : ∀ π ∈ πs, π.IsPackage)
    -- the selected index, within the list
    (i : ℕ)
    (hi : i < πs.length)
    -- the free port of the selector
    (x : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the menu against the selector, and `Δ`
    (hlin : Net.Linear (s(menu πs, selector πs.length i x) ::ₘ Δ)) :
    -- it reduces to `πᵢ` on the free port `x`, and `Δ`
    StepsE system (s(menu πs, selector πs.length i x) ::ₘ Δ) (s(πs[i], var x) ::ₘ Δ) :=
  Comb.menu_selector πs i hi x hπ Δ hlin

-- ============================================================================================
-- 6. Recursion-free systems (Section 2.4, pages 85-87)
-- ============================================================================================

/-- **The translation of Fig. 6 is a translation of interaction systems** (Lafont 1997,
Section 2.4, pages 85-86: "In that way, one gets a translation of interaction systems", Fig. 7).
`D` is the data that make `I` recursion-free: an order on the symbols and a decomposition of each
rule; `D.translation` is the translation of Fig. 6 built from it.

Library: `INet.System.RecursionFreeData.translation_compatible` in
`InteractionCombinators/Universality/RecursionFree/RecursionFreeCompatible.lean`. -/
theorem recursion_free_compatible
    -- an interaction system with finitely many symbols
    [Finite S.Sym]
    {I : System S}
    (hI : I.WellFormed)
    -- an order and decompositions that make it recursion-free
    (D : I.RecursionFreeData) :
    -- the translation of Fig. 6 simulates every rule of `I` in the combinators
    D.translation.Compatible I system :=
  D.translation_compatible hI

/-- **Theorem 1 for recursion-free systems** (Lafont 1997, Section 2.4, pages 85-87): a
recursion-free interaction system has a strict translation into the interaction combinators.

Library: `INet.Comb.recursionFree_strict` in
`InteractionCombinators/Universality/RecursionFree/RecursionFreeCompatible.lean`. -/
theorem recursion_free_strict
    -- a recursion-free interaction system with finitely many symbols
    [Finite S.Sym]
    (I : System S)
    (hI : I.WellFormed)
    (hR : I.RecursionFree) :
    -- some translation into the combinators is strict
    ∃ Φ : Translation S sig, Φ.Strict ∧
      -- and simulates every rule of `I`
      Φ.Compatible I system :=
  Comb.recursionFree_strict I hI hR

/-- **Reduction terminates in a recursion-free system** (Lafont 1997, page 86: "It is easy to see
that the process of reduction always terminates in such a system"). There is no infinite sequence
of nets each of which reduces in one step to the next.

Library: `INet.System.RecursionFree.not_stepE_seq` in
`InteractionCombinators/Universality/RecursionFree/RecursionFreeTerminates.lean`. -/
theorem recursion_free_terminates
    -- a recursion-free system
    {I : System S}
    (hR : I.RecursionFree)
    -- a sequence of nets
    (N : ℕ → Net S ℕ) :
    -- it is not a reduction: some net does not reduce in one step to the next
    ¬ ∀ n, StepE I (N n) (N (n + 1)) :=
  hR.not_stepE_seq N

-- ============================================================================================
-- 7. Duplication and codes (Sections 2.5-2.6, pages 87-89)
-- ============================================================================================

/-- The package `π` with its wires renamed by `f`. When `f` is injective on the names of `π`,
this is another text of the same package: "a copy of `π`" (Lafont 1997, page 87). -/
abbrev CopyOf
    -- the package
    (π : Term sig ℕ)
    -- the renaming of its wires
    (f : ℕ → ℕ) :
    Term sig ℕ :=
  π.bind fun x => var (f x)

/-- **Lemma 3, corollary: a package without `dup` is duplicated** (Lafont 1997, page 87). A
package `π` built from `con` and `era` only, plugged into the principal port of a `dup`, reduces
to two copies of `π`, one on each auxiliary port. By Lemma 3 (i) the tree is duplicated and
leaves a `dup` on each leaf, by Lemma 3 (ii) these annihilate two by two along the wiring.

Library: `INet.Comb.dup_package` in
`InteractionCombinators/Universality/Duplication/DupPackage.lean`. -/
theorem lemma_3_dup_package
    -- the package, without `dup`
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    (hd : DupFree π)
    -- the trees plugged into the two auxiliary ports of the `dup`
    (u v : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the package on the principal port of the `dup`, and `Δ`
    (hlin : Net.Linear (s(mkDup u v, π) ::ₘ Δ)) :
    -- there are two renamings `f`, `g` and a net `N` such that
    ∃ (f g : ℕ → ℕ) (N : CNet),
      -- `f` is injective on the names of the package,
      Set.InjOn f {x | x ∈ π.vars} ∧
      -- so is `g`,
      Set.InjOn g {x | x ∈ π.vars} ∧
      -- the net reduces to `N`,
      StepsE system (s(mkDup u v, π) ::ₘ Δ) N ∧
      -- and `N` is the same graph as: a copy of `π` on `u`, a copy of `π` on `v`, and `Δ`
      Equiv N (s(u, CopyOf π f) ::ₘ s(v, CopyOf π g) ::ₘ Δ) :=
  Comb.dup_package π hπ hd u v Δ hlin

/-- **The property of the copier `C_n`** (Lafont 1997, page 88): a package without `dup`,
plugged into the root of `C_n`, reduces to `n` copies of the package, one on each auxiliary port.
`copier us` is `C_n` with the trees `us` on its auxiliary ports; it is the autodual multiplexor
`T_n`, as in the paper.

Library: `INet.Comb.copier_package` in `InteractionCombinators/Universality/Codes/Copier.lean`. -/
theorem copier_property
    -- the package, without `dup`
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    (hd : DupFree π)
    -- the trees plugged into the `n` auxiliary ports of the copier
    (us : List (Term sig ℕ))
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the package on the root of the copier, and `Δ`
    (hlin : Net.Linear (s(copier us, π) ::ₘ Δ)) :
    -- there are renamings `fs` and a net `N` such that
    ∃ (fs : List (ℕ → ℕ)) (N : CNet),
      -- there is one renaming for each auxiliary port,
      fs.length = us.length ∧
      -- each injective on the names of the package,
      (∀ f ∈ fs, Set.InjOn f {x | x ∈ π.vars}) ∧
      -- the net reduces to `N`,
      StepsE system (s(copier us, π) ::ₘ Δ) N ∧
      -- and `N` is the same graph as: a copy of `π` on each tree of `us`, and `Δ`
      Equiv N ((List.zipWith (fun u f => s(u, CopyOf π f)) us fs : CNet) + Δ) :=
  Comb.copier_package π hπ hd us Δ hlin

/-- **The decoder extracts a package from its code** (Lafont 1997, pages 88-89, Fig. 8 and
Fig. 9: "`!π` is a code for `π`, which can be extracted with the decoder `D`"). The code
`code k π` is `!π`, a package without `dup` even when `π` has some; its new wires are named from
`k`. The decoder `decoder w k₀` is `D` with free port `w` and its loop named `k₀`, `k₀ + 1`. The
code plugged into the decoder reduces to `π` on the port `w`. The library theorem also takes the
hypothesis that `π` is a package, which it does not use; it is kept here.

Library: `INet.Comb.code_decoder_package` in
`InteractionCombinators/Universality/Codes/Decode.lean`. -/
theorem decoder_property
    -- the package
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    -- the first new name `k` of the code, the free port `w` of the decoder, and the first name
    -- `k₀` of the loop of the decoder
    (k w k₀ : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net `π` on `w`, with `Δ`, is linear and its names are below `k`
    (hlin : Net.Linear (s(var w, π) ::ₘ Δ))
    (hb : Net.Below k (s(var w, π) ::ₘ Δ))
    -- the loop of the decoder is at or above the names of the code
    (hk₀ : (decomp k π).k ≤ k₀) :
    -- the code `!π` against the decoder, with `Δ`, reduces to a net `M`
    ∃ M, StepsE system (s(code k π, decoder w k₀) ::ₘ Δ) M ∧
      -- that is the same graph as `π` on `w`, with `Δ`
      Equiv M (s(var w, π) ::ₘ Δ) :=
  Comb.code_decoder_package π hπ k w k₀ Δ hlin hb hk₀

-- ============================================================================================
-- 8. Theorem 1 (Section 2.7, pages 82 and 90)
-- ============================================================================================

/-- **Theorem 1** (Lafont 1997, stated on page 82, proof ended on page 90): "Any interaction
system can be translated into the system of interaction combinators." An interaction system is a
`System` that is `WellFormed`, over finitely many symbols; a translation `Φ` gives a principal
net of combinators for each symbol; `Φ.Compatible I system` says that for every rule of `I`, the
translations of the two cells, plugged by their roots, reduce to a translation of the right
member of the rule. This is `Universal system` unfolded.

Library: `INet.Comb.universal` in `InteractionCombinators/Universality/Theorem1.lean`. -/
theorem theorem_1
    -- an interaction system with finitely many symbols
    (S : Signature)
    [Finite S.Sym]
    (I : System S)
    (hI : I.WellFormed) :
    -- some translation into the combinators simulates every rule of `I`
    ∃ Φ : Translation S sig, Φ.Compatible I system :=
  Comb.universal S I hI

/-- **Theorem 1, with a strict translation**: no symbol is translated into a single wire. This is
the target of the project, `StrictlyUniversal system`, unfolded. Lafont's translation (Fig. 10,
page 89) has a cell at the root of the translation of every symbol, so it is strict; by
Proposition 4 every step of `I` then costs at least one step of the combinators.

Library: `INet.Comb.universal_strict` in `InteractionCombinators/Universality/Theorem1.lean`. -/
theorem theorem_1_strict
    -- an interaction system with finitely many symbols
    (S : Signature)
    [Finite S.Sym]
    (I : System S)
    (hI : I.WellFormed) :
    -- some translation into the combinators is strict
    ∃ Φ : Translation S sig, Φ.Strict ∧
      -- and simulates every rule of `I`
      Φ.Compatible I system :=
  Comb.universal_strict S I hI

/-- **Theorem 1 for a translation given by data** (Lafont 1997, Section 2.7, Fig. 10,
pages 89-90). The translation of Fig. 10 is `codeTranslationE e side`, built from a numbering `e`
of the symbols and, for each pair of symbols, one side of a decomposition of their rule (page 85).
If the sides plug back into the rules (`System.SidesPlug`), the translation is strict and
simulates every rule. Nothing is chosen: `e` and `side` are arguments, and the system is not
asked to be well formed.

Library: `INet.Comb.codeTranslationE_strict` and `INet.Comb.codeTranslationE_compatible_of_sides`
in `InteractionCombinators/Universality/General/CodeCompatibleSides.lean`. -/
theorem theorem_1_explicit
    -- a system whose `n` symbols are numbered by `e`
    {I : System S}
    {n : ℕ}
    (e : S.Sym ≃ Fin n)
    -- for each pair of symbols, a side of a decomposition of their rule, and the two sides of
    -- each rule plug back into the rule
    {side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))}
    (hside : I.SidesPlug side) :
    -- the translation of Fig. 10 is strict
    (codeTranslationE e side).Strict ∧
    -- and simulates every rule of `I`
    (codeTranslationE e side).Compatible I system :=
  ⟨Comb.codeTranslationE_strict e side, Comb.codeTranslationE_compatible_of_sides e hside⟩

/-- **Theorem 1 with the number of steps** (Lafont 1997, page 81 and Theorem 1, page 82). For
any decomposition data `D` of an interaction system (they exist: `System.exists_decData`), the
translation of Fig. 10 simulates every rule in at least `L > 0` and at most `U` steps of the
combinators. By `proposition_4_bounds`, `n` steps of `I` then cost between `L n` and `U n` steps.
The bounds are shown to exist; they are not computed.

Library: `INet.Comb.codeTranslation_compatibleWithin` in
`InteractionCombinators/Translations/SimulationUniform.lean`. -/
theorem theorem_1_bounds
    -- an interaction system with finitely many symbols
    [Finite S.Sym]
    {I : System S}
    (hI : I.WellFormed)
    -- decompositions of its rules
    (D : I.DecData) :
    -- the translation of Fig. 10 simulates every rule in at least `L > 0` and at most `U` steps
    ∃ L U, 0 < L ∧ (codeTranslation D.side).CompatibleWithin I system L U :=
  Comb.codeTranslation_compatibleWithin hI D

end INet.Results
