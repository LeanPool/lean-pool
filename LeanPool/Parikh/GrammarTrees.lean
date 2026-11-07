/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Counting
public import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Set.Finite.List

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Parse trees, unfinished derivations, and their meaning

To decompose a derivation, we need to retain its production nodes and child
order. `ParseTree` provides this syntax. A hole represents an unexpanded
nonterminal; `Valid` checks the grammar rules, and `Complete` rules out holes.
An empty production is still a production node, even though its frontier is empty.

The first part defines tree statistics and contexts. Later results show that
complete trees describe exactly Mathlib's derivations (`derives_iff_tree`) and
that trees of bounded height form a finite family when their labels are
restricted appropriately (`bounded_open_finite`). These are the semantic and
finiteness foundations for decomposition.

Source: `def:tree`, `def:statistics`, `prop:tree-word`, `lem:finite`.
-/
namespace Parikh

/-- Concrete parse-tree syntax (`def:tree`), including open trees with holes.
Grammar validity and completeness are checked separately by `Valid` and `Complete`. -/
inductive ParseTree (T N : Type*) where
  | terminal (a : T)
  | hole (A : N)
  | node (rule : ContextFreeRule T N) (children : List (ParseTree T N))

namespace ParseTree
variable {T N : Type*}

/-- Terminal or nonterminal symbol at the tree root. -/
@[expose] def root : ParseTree T N → Symbol T N
  | .terminal a => .terminal a
  | .hole A => .nonterminal A
  | .node r _ => .nonterminal r.input

/-- Read the leaves from left to right, retaining holes as nonterminals.
At a production node we concatenate the children's frontiers. In particular,
an empty production has no children and contributes the empty list: its root
label records a rule application, not a remaining symbol in the frontier. -/
@[expose] def frontier : ParseTree T N → List (Symbol T N)
  | .terminal a => [.terminal a]
  | .hole A => [.nonterminal A]
  | .node _ children => (children.map frontier).flatten

/-- Terminal leaves in order; for a complete tree this is its yield. -/
@[expose] def yield : ParseTree T N → List T
  | .terminal a => [a]
  | .hole _ => []
  | .node _ children => (children.map yield).flatten

/-- Unexpanded nonterminal leaves in frontier order. -/
@[expose] def holes : ParseTree T N → List N
  | .terminal _ => []
  | .hole A => [A]
  | .node _ children => (children.map holes).flatten

/-- The termination measure counts productions, including silent/unit nodes. -/
@[expose] def productionSize : ParseTree T N → ℕ
  | .terminal _ | .hole _ => 0
  | .node _ children => 1 + (children.map productionSize).sum

/-- The maximum number of production nodes on a downward path.
Terminal leaves and holes have height zero. A production node adds one to its
largest child height; with no children, the maximum is zero, so an empty
production has height one. -/
@[expose] def height : ParseTree T N → ℕ
  | .terminal _ | .hole _ => 0
  | .node _ children => 1 + (children.map height).foldl max 0

/-- Nonterminal labels at production nodes, including empty productions. -/
@[expose] def productionLabels : ParseTree T N → List N
  | .terminal _ | .hole _ => []
  | .node r children => r.input :: (children.map productionLabels).flatten

/-- Holes contribute no nonterminal to support (`def:statistics`). -/
@[expose] def support (t : ParseTree T N) : Set N := {A | A ∈ t.productionLabels}

/-- Letter-count vector of the terminal yield. -/
@[expose] def weight [DecidableEq T] (t : ParseTree T N) : Vector T := counts t.yield

/-- Production labels along downward paths, including nonempty prefixes at nodes.
A terminal or hole contributes the empty label path. At a node, `[r.input]`
records the path stopping there, and prepending `r.input` to each child path
records paths continuing below it. The explicit singleton also handles an
empty production. Labels repeated in different sibling branches are allowed;
`Simple` excludes repetitions only within a single path. -/
@[expose] def labelPaths : ParseTree T N → List (List N)
  | .terminal _ | .hole _ => [[]]
  | .node r children => [r.input] ::
      ((children.map labelPaths).flatten.map (r.input :: ·))

/-- No production label repeats along any downward path. -/
@[expose] def Simple (t : ParseTree T N) : Prop := ∀ path ∈ t.labelPaths, path.Nodup

/-- Plug all holes. The one-hole contract below makes this a single replacement. -/
@[expose] def plug : ParseTree T N → ParseTree T N → ParseTree T N
  | .terminal a, _ => .terminal a
  | .hole _, t => t
  | .node r children, t => .node r (children.map (fun c => plug c t))

/-- Positions use zero-based child indices; invalid positions return `none`. -/
@[expose] def subtree : ParseTree T N → List ℕ → Option (ParseTree T N)
  | t, [] => some t
  | .node _ children, i :: q => children[i]?.bind (fun t => subtree t q)
  | _, _ :: _ => none

/-- Replace the subtree at a child-index path, rejecting invalid positions. -/
@[expose] def replaceAt : ParseTree T N → List ℕ → ParseTree T N → Option (ParseTree T N)
  | _, [], replacement => some replacement
  | .node r children, i :: q, replacement => do
      let child ← children[i]?
      let newChild ← replaceAt child q replacement
      return .node r (children.set i newChild)
  | _, _ :: _, _ => none

end ParseTree

variable {T : Type*}

/-- A tree follows the grammar, although it may still contain holes.
Terminal leaves and holes are valid on their own. A production node is valid
when its rule belongs to the grammar, all children are valid, and their roots
match the rule's right-hand side in order. For an empty right-hand side, this
last condition forces the child list to be empty. -/
inductive Valid (g : ContextFreeGrammar T) : ParseTree T g.NT → Prop where
  | terminal (a) : Valid g (.terminal a)
  | hole (A) : Valid g (.hole A)
  | node (r children) (rule_mem : r ∈ g.rules)
      (children_valid : ∀ t ∈ children, Valid g t)
      (roots_match : children.map ParseTree.root = r.output) : Valid g (.node r children)

/-- A valid tree with no unexpanded nonterminal leaves.
Its terminal yield is therefore a fully derived word. The root condition for
a grammar's start symbol is imposed separately where needed. -/
@[expose] def Complete (g : ContextFreeGrammar T) (t : ParseTree T g.NT) : Prop :=
  Valid g t ∧ t.holes = []

/-- A valid context with exactly one hole, labelled `A`.
A matching complete tree can be placed in that hole to finish the context. -/
@[expose] def OneHole (g : ContextFreeGrammar T) (E : ParseTree T g.NT) (A : g.NT) : Prop :=
  Valid g E ∧ E.holes = [A]

/-- A derivation context that returns to its starting nonterminal (`def:cycle`).
The unique hole and the root both have label `A`, so the context can wrap a
subtree rooted at `A` and can be inserted repeatedly. Positive production size
excludes the bare hole. A cycle may nevertheless produce no terminal letters;
then insertion enlarges the tree without changing its Parikh vector. -/
@[expose] def Cycle (g : ContextFreeGrammar T) (C : ParseTree T g.NT) (A : g.NT) : Prop :=
  OneHole g C A ∧ C.root = .nonterminal A ∧ 0 < C.productionSize

/-- The start and every nonterminal mentioned in a production: finite even if `g.NT` is infinite. -/
@[expose] noncomputable def activeNonterminals (g : ContextFreeGrammar T) : Finset g.NT := by
  classical
  exact {g.initial} ∪ g.rules.biUnion (fun r =>
    {r.input} ∪ (r.output.filterMap fun s => match s with
      | .terminal _ => none
      | .nonterminal A => some A).toFinset)

/-- Arbitrary holes outside the active alphabet must be excluded from bounded enumeration. -/
@[expose] def ActiveOpen (g : ContextFreeGrammar T) (t : ParseTree T g.NT) : Prop :=
  Valid g t ∧ ∀ A ∈ t.holes, A ∈ activeNonterminals g

/-- Production-node labels are active even in a valid open tree (`def:statistics`).
Holes contribute no label to support. -/
theorem Valid.support_active {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) : t.support ⊆ (activeNonterminals g : Set g.NT) := by
  classical
  induction ht with
  | terminal a =>
    intro A hA
    change A ∈ (ParseTree.terminal a : ParseTree T g.NT).productionLabels at hA
    rw [ParseTree.productionLabels.eq_1] at hA
    exact False.elim (List.not_mem_nil hA)
  | hole A =>
    intro B hB
    change B ∈ (ParseTree.hole A : ParseTree T g.NT).productionLabels at hB
    rw [ParseTree.productionLabels.eq_2] at hB
    exact False.elim (List.not_mem_nil hB)
  | node r children hr hc roots ih =>
    intro A hA
    change A ∈ (ParseTree.node r children).productionLabels at hA
    rw [ParseTree.productionLabels.eq_3] at hA
    rcases List.mem_cons.mp hA with rfl | hA
    · unfold activeNonterminals
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨r, hr, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
    · obtain ⟨labels, hlabels, hA⟩ := List.mem_flatten.mp hA
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hlabels
      exact ih c hc hA

/-- Every production node in a complete tree belongs to the finite active alphabet. -/
theorem complete_support_active (g : ContextFreeGrammar T) (t : ParseTree T g.NT)
    (ht : Complete g t) : t.support ⊆ (activeNonterminals g : Set g.NT) := by
  exact ht.1.support_active

/-- Finite terminals and finite productions suffice; no `Fintype g.NT` (`lem:finite`). -/
theorem bounded_open_finite [Finite T] (g : ContextFreeGrammar T) (H : ℕ) :
    {t : ParseTree T g.NT | ActiveOpen g t ∧ t.height ≤ H}.Finite := by
  classical
  have nodeHeight (r : ContextFreeRule T g.NT) (cs : List (ParseTree T g.NT)) :
      (ParseTree.node r cs).height = 1 + (cs.map ParseTree.height).foldl max 0 := by
    exact ParseTree.height.eq_3 r cs
  -- Fixed-length lists over a finite subtype cover every possible child list.
  have finiteLists {s : Set (ParseTree T g.NT)} (hs : s.Finite) (n : ℕ) :
      {cs : List (ParseTree T g.NT) | cs.length = n ∧ ∀ c ∈ cs, c ∈ s}.Finite := by
    let : Finite s := hs
    apply ((List.finite_length_eq s n).image (List.map Subtype.val)).subset
    intro cs hcs
    refine ⟨cs.attachWith (· ∈ s) hcs.2, ?_, ?_⟩
    · simpa using hcs.1
    · exact List.attachWith_map_subtype_val hcs.2
  -- At height zero, only finite terminals and active holes are available.
  have leaves :
      (Set.range (ParseTree.terminal (N := g.NT)) ∪
        ParseTree.hole '' (activeNonterminals g : Set g.NT)).Finite :=
    (Set.finite_range (ParseTree.terminal (T := T) (N := g.NT))).union
      ((activeNonterminals g).finite_toSet.image _)
  induction H with
  | zero =>
    apply leaves.subset
    rintro t ⟨⟨hv, ha⟩, hh⟩
    cases hv with
    | terminal a => exact Or.inl ⟨a, rfl⟩
    | hole A =>
      apply Or.inr
      refine ⟨A, ?_, rfl⟩
      apply ha A
      simp [ParseTree.holes]
    | node r cs hr hv roots =>
      rw [nodeHeight] at hh
      omega
  | succ H ih =>
    let family : Set (ParseTree T g.NT) :=
      {t | ActiveOpen g t ∧ t.height ≤ H}
    -- Each finite production fixes its arity; validity filters this finite superset.
    have nodes : (⋃ r ∈ (g.rules : Set (ContextFreeRule T g.NT)),
        ParseTree.node r '' {cs : List (ParseTree T g.NT) |
          cs.length = r.output.length ∧ ∀ c ∈ cs, c ∈ family}).Finite :=
      g.rules.finite_toSet.biUnion fun r _ => (finiteLists ih r.output.length).image _
    apply (leaves.union nodes).subset
    rintro t ⟨⟨hv, ha⟩, hh⟩
    cases hv with
    | terminal a => exact Or.inl (Or.inl ⟨a, rfl⟩)
    | hole A =>
      apply Or.inl ∘ Or.inr
      refine ⟨A, ?_, rfl⟩
      apply ha A
      simp [ParseTree.holes]
    | node r cs hr hv roots =>
      apply Or.inr
      apply Set.mem_iUnion₂.mpr
      refine ⟨r, hr, cs, ⟨?_, ?_⟩, rfl⟩
      · simpa using congrArg List.length roots
      · intro c hc
        refine ⟨⟨hv c hc, ?_⟩, ?_⟩
        · intro A hA
          apply ha A
          simp only [ParseTree.holes, ← List.flatMap_def, List.mem_flatMap]
          exact ⟨c, hc, hA⟩
        · have hm : c.height ∈ cs.map ParseTree.height := List.mem_map_of_mem hc
          have hmax := List.le_max_of_mem hm
          have hne := List.ne_nil_of_mem hm
          rw [nodeHeight, List.foldl_max_eq_max hne, Nat.zero_max] at hh
          omega


variable {N : Type*}

/-- A context-free rewrite in a concatenation occurs in one of its two parts. -/
theorem rewrites_append_cases (r : ContextFreeRule T N)
    (u v w : List (Symbol T N)) (h : r.Rewrites (u ++ v) w) :
    (∃ u', r.Rewrites u u' ∧ w = u' ++ v) ∨
      (∃ v', r.Rewrites v v' ∧ w = u ++ v') := by
  induction u generalizing w with
  | nil => exact Or.inr ⟨w, h, rfl⟩
  | cons x u ih =>
    cases h with
    | head =>
      exact Or.inl ⟨r.output ++ u, .head u, (List.append_assoc _ _ _).symm⟩
    | cons _ h =>
      rcases ih _ h with ⟨u', hu', rfl⟩ | ⟨v', hv', rfl⟩
      · exact Or.inl ⟨x :: u', .cons x hu', rfl⟩
      · exact Or.inr ⟨v', hv', rfl⟩

namespace ParseTree
/-- The nonterminals on the frontier are exactly the holes. -/
theorem frontier_holes (t : ParseTree T N) :
    (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal _ => none | .nonterminal A => some A) = t.holes := by
  induction t using ParseTree.rec (motive_2 := fun (ts : List (ParseTree T N)) =>
    ∀ t ∈ ts, (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal _ => none | .nonterminal A => some A) = t.holes) with
  | terminal a => simp [frontier, holes]
  | hole A => simp [frontier, holes]
  | node r children ih =>
    simp only [frontier, holes, List.filterMap_flatten, List.map_map]
    congr 1
    exact List.map_congr_left ih
  | nil c hc => simp at hc
  | cons t ts ht hts c hc =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ht
    · exact hts c hc

/-- The terminals on the frontier are exactly the yield. -/
theorem frontier_yield (t : ParseTree T N) :
    (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal a => some a | .nonterminal _ => none) = t.yield := by
  induction t using ParseTree.rec (motive_2 := fun (ts : List (ParseTree T N)) =>
    ∀ t ∈ ts, (t.frontier.filterMap fun (s : Symbol T N) => match s with
      | .terminal a => some a | .nonterminal _ => none) = t.yield) with
  | terminal a => simp [frontier, yield]
  | hole A => simp [frontier, yield]
  | node r children ih =>
    simp only [frontier, yield, List.filterMap_flatten, List.map_map]
    congr 1
    exact List.map_congr_left ih
  | nil c hc => simp at hc
  | cons t ts ht hts c hc =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ht
    · exact hts c hc

/-- A tree with no holes has a wholly terminal frontier. -/
theorem frontier_of_holes_eq_nil (t : ParseTree T N) (h : t.holes = []) :
    t.frontier = t.yield.map Symbol.terminal := by
  have onlyTerminals : ∀ l : List (Symbol T N),
      (l.filterMap fun s => match s with
        | .terminal _ => none | .nonterminal A => some A) = [] →
      l = (l.filterMap fun s => match s with
        | .terminal a => some a | .nonterminal _ => none).map Symbol.terminal := by
    intro l
    induction l with
    | nil => simp
    | cons s l ih =>
      cases s with
      | terminal a =>
        intro h
        simp only [List.filterMap_cons_none] at h
        simpa only [List.filterMap_cons, List.map_cons]
          using congrArg (Symbol.terminal a :: ·) (ih h)
      | nonterminal A => simp
  rw [← frontier_yield]
  exact onlyTerminals t.frontier (t.frontier_holes.trans h)

end ParseTree

/-- A valid tree gives a Mathlib derivation from its root to its frontier. -/
theorem Valid.derives_frontier {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) : g.Derives [t.root] t.frontier := by
  induction ht with
  | terminal a => simpa only [ParseTree.root, ParseTree.frontier] using
      (ContextFreeGrammar.Derives.refl (g := g) [.terminal a])
  | hole A => simpa only [ParseTree.root, ParseTree.frontier] using
      (ContextFreeGrammar.Derives.refl (g := g) [.nonterminal A])
  | node r children hr hc roots ih =>
    have forest : g.Derives (children.map ParseTree.root)
        (children.map ParseTree.frontier).flatten := by
      clear hc roots
      induction children with
      | nil => exact .refl _
      | cons c cs hcs =>
        have hhead := ih c (by simp)
        have htail := hcs (fun t ht => ih t (by simp [ht]))
        exact (hhead.append_right (cs.map ParseTree.root)).trans
          (htail.append_left c.frontier)
    simpa only [ParseTree.root, ParseTree.frontier] using
      (ContextFreeGrammar.Produces.single (g := g) ⟨r, hr,
        ContextFreeRule.Rewrites.input_output⟩).trans (roots ▸ forest)

/-- A rewrite expands one frontier hole, preserving validity and the tree root. -/
theorem Valid.frontier_step {g : ContextFreeGrammar T} {t : ParseTree T g.NT}
    (ht : Valid g t) {v : List (Symbol T g.NT)} (h : g.Produces t.frontier v) :
    ∃ t', Valid g t' ∧ t'.root = t.root ∧ t'.frontier = v := by
  induction ht generalizing v with
  | terminal a =>
    obtain ⟨r, hr, hs⟩ := h
    have hm := hs.nonterminal_input_mem
    simp [ParseTree.frontier] at hm
  | hole A =>
    obtain ⟨r, hr, hs⟩ := h
    have hm := hs.nonterminal_input_mem
    simp only [ParseTree.frontier, List.mem_singleton, Symbol.nonterminal.injEq] at hm
    have hv : v = r.output := by
      simp only [ParseTree.frontier] at hs
      cases hs with
      | head => simp
      | cons _ hs => exact False.elim (by simpa using hs.nonterminal_input_mem)
    let leaf : Symbol T g.NT → ParseTree T g.NT := fun s => match s with
      | .terminal a => .terminal a
      | .nonterminal B => .hole B
    have hroot : ∀ s, (leaf s).root = s := by intro s; cases s <;> rfl
    refine ⟨.node r (r.output.map leaf), .node _ _ hr ?_ ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      cases s with
      | terminal a => exact .terminal a
      | nonterminal B => exact .hole B
    · simp only [List.map_map]
      simp only [Function.comp_def, hroot, List.map_id']
    · simpa only [ParseTree.root] using congrArg Symbol.nonterminal hm
    · have hf : ∀ s, (leaf s).frontier = [s] := by
        intro s; cases s <;> simp [leaf, ParseTree.frontier]
      simp only [ParseTree.frontier, List.map_map, Function.comp_def, hf]
      simpa only [← List.flatMap_def, List.flatMap_singleton'] using hv.symm
  | node r children hr hc roots ih =>
    have forest : ∀ v, g.Produces (children.map ParseTree.frontier).flatten v →
        ∃ children' : List (ParseTree T g.NT), (∀ c ∈ children', Valid g c) ∧
          children'.map ParseTree.root = children.map ParseTree.root ∧
          (children'.map ParseTree.frontier).flatten = v := by
      clear hr roots h
      induction children with
      | nil =>
        intro v hv
        obtain ⟨s, hs, hrewrite⟩ := hv
        exact False.elim (by simpa using hrewrite.nonterminal_input_mem)
      | cons c cs hcs =>
        intro v hv
        obtain ⟨s, hs, hrewrite⟩ := hv
        simp only [List.map_cons, List.flatten_cons] at hrewrite
        rcases rewrites_append_cases s c.frontier (cs.map ParseTree.frontier).flatten v
          hrewrite with ⟨u, hu, hv⟩ | ⟨u, hu, hv⟩
        · obtain ⟨c', hc', hroot, hf⟩ := ih c (by simp) ⟨s, hs, hu⟩
          refine ⟨c' :: cs, ?_, ?_, ?_⟩
          · intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hc'
            · exact hc d (by simp [hd])
          · simp only [List.map_cons, hroot]
          · simp only [List.map_cons, List.flatten_cons, hf, hv]
        · obtain ⟨cs', hvalid, hroot, hf⟩ := hcs
            (fun d hd => hc d (by simp [hd]))
            (fun d hd => ih d (by simp [hd])) u ⟨s, hs, hu⟩
          refine ⟨c :: cs', ?_, ?_, ?_⟩
          · intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hc d (by simp)
            · exact hvalid d hd
          · simp only [List.map_cons, hroot]
          · simp only [List.map_cons, List.flatten_cons, hf, hv]
    obtain ⟨children', hvalid, hroots, hf⟩ := forest v (by
      simpa only [ParseTree.frontier] using h)
    exact ⟨.node r children', .node _ _ hr hvalid (hroots.trans roots),
      rfl, by simpa only [ParseTree.frontier] using hf⟩

/-- Any derivation from a nonterminal is the frontier of a valid open tree. -/
theorem derives_tree_frontier (g : ContextFreeGrammar T) (A : g.NT)
    {v : List (Symbol T g.NT)} (h : g.Derives [.nonterminal A] v) :
    ∃ t, Valid g t ∧ t.root = .nonterminal A ∧ t.frontier = v := by
  induction h with
  | refl => exact ⟨.hole A, .hole A, rfl, by simp [ParseTree.frontier]⟩
  | tail h step ih =>
    obtain ⟨t, ht, hr, hf⟩ := ih
    obtain ⟨t', ht', hr', hf'⟩ := ht.frontier_step (hf.symm ▸ step)
    exact ⟨t', ht', hr'.trans hr, hf'⟩

/-- Concrete bridge to Mathlib's derivation relation, for every root (`prop:tree-word`,
appendix A). -/
theorem derives_iff_tree (g : ContextFreeGrammar T) (A : g.NT) (w : List T) :
    g.Derives [.nonterminal A] (w.map Symbol.terminal) ↔
      ∃ t : ParseTree T g.NT,
        Complete g t ∧ t.root = .nonterminal A ∧ t.yield = w := by
  constructor
  · intro h
    obtain ⟨t, ht, hr, hf⟩ := derives_tree_frontier g A h
    refine ⟨t, ⟨ht, ?_⟩, hr, ?_⟩
    · rw [← t.frontier_holes, hf]
      simp
    · rw [← t.frontier_yield, hf]
      simp
  · rintro ⟨t, ⟨ht, hh⟩, hr, hw⟩
    simpa only [hr, t.frontier_of_holes_eq_nil hh, hw] using ht.derives_frontier


end Parikh
