/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.FiniteRamsey.RamseyNumber
import Mathlib.Data.Finset.Sort

/-!
# Ordered Ramsey numbers

An **ordered** Ramsey statement strengthens the classical Ramsey arrow by requiring the copy of
the target inside a coloured host to be found by an *order-preserving* embedding, rather than an
arbitrary one. Host and target vertex types here are both `Fin`-types, carrying the ambient linear
order; `OrderedCopy`/`OrderedIsContained` play the order-preserving role that `SimpleGraph.Copy`/
`SimpleGraph.IsContained` (`⊑`) play for ordinary containment, and `OrderedArrow` is the resulting
arrow relation. Since order-preserving copies are harder to find than arbitrary ones, ordered
Ramsey numbers are always at least as large as their classical counterparts.

## Main declarations

* `SimpleGraph.OrderedCopy`, `SimpleGraph.OrderedIsContained`: an order-preserving copy, and
  containment via one; `OrderedIsContained.isContained` forgets order-preservation to recover the
  ordinary `⊑`.
* `SimpleGraph.OrderedArrow`: the ordered Ramsey arrow relation, and its transport calculus
  `OrderedArrow.mono_target`/`mono_host_le`/`mono_completeHost`.
* `SimpleGraph.completeGraph_isContained_iff_orderedIsContained` and its arrow-level
  generalisation `SimpleGraph.orderedArrow_completeGraph_iff`: ordering never matters when every
  colour's target is a complete graph, for an arbitrary colour palette.
* `SimpleGraph.orderedArrowNumber`: the ordered Ramsey number, defined by `sInf` (junk value `0`
  when no complete host works), with its least-number API under an existence hypothesis.
* `SimpleGraph.orderedArrowNumber_completeGraph_eq_ramseyNumber`: for clique targets the ordered
  Ramsey number is the ordinary Ramsey number `ramseyNumber`.
* `SimpleGraph.IsOrderedCopyWitness`, `SimpleGraph.decidableOrderedIsContained`,
  `SimpleGraph.decidableOrderedArrow`, `SimpleGraph.orderedArrowB`: executable decidability, by a
  finite search over strictly monotone adjacency-preserving functions.
-/

@[expose] public section

namespace SimpleGraph

universe w

/-! ### Ordered copies and ordered containment -/

/-- **An order-preserving copy** of `A : SimpleGraph (Fin m)` inside `B : SimpleGraph (Fin n)`: an
`OrderEmbedding` `Fin m ↪o Fin n` that is additionally adjacency-preserving. The order-preserving
analogue of `SimpleGraph.Copy`. -/
def OrderedCopy {m n : Nat} (A : SimpleGraph (Fin m)) (B : SimpleGraph (Fin n)) : Type :=
  {f : Fin m ↪o Fin n // ∀ a b, A.Adj a b → B.Adj (f a) (f b)}

/-- **Ordered containment.** Some order-preserving copy of `A` exists inside `B`. The
order-preserving analogue of `SimpleGraph.IsContained` (`⊑`). -/
def OrderedIsContained {m n : Nat} (A : SimpleGraph (Fin m)) (B : SimpleGraph (Fin n)) : Prop :=
  Nonempty (OrderedCopy A B)

/-- **Forgetting order-preservation.** An ordered copy is in particular an ordinary copy, so
ordered containment implies ordinary containment (`⊑`). The converse fails in general — not every
ordinary copy can be reordered to be order-preserving, which is exactly why ordered Ramsey numbers
can exceed ordinary ones. -/
theorem OrderedIsContained.isContained {m n : Nat} {A : SimpleGraph (Fin m)}
    {B : SimpleGraph (Fin n)} (h : OrderedIsContained A B) : A ⊑ B := by
  obtain ⟨f, hf⟩ := h
  exact ⟨⟨⟨f, hf _ _⟩, f.injective⟩⟩

/-- **Ordered containment composes.** An order-preserving copy of `A` in `B`, composed with one of
`B` in `C`, gives one of `A` in `C`. -/
theorem OrderedIsContained.trans {l m n : Nat} {A : SimpleGraph (Fin l)} {B : SimpleGraph (Fin m)}
    {C : SimpleGraph (Fin n)} (hAB : OrderedIsContained A B) (hBC : OrderedIsContained B C) :
    OrderedIsContained A C := by
  obtain ⟨f, hf⟩ := hAB
  obtain ⟨g, hg⟩ := hBC
  exact ⟨f.trans g, fun a b hab => hg _ _ (hf a b hab)⟩

/-- Ordered containment is monotone in the host graph. -/
theorem OrderedIsContained.mono_right {m n : Nat} {A : SimpleGraph (Fin m)}
    {B B' : SimpleGraph (Fin n)} (h : OrderedIsContained A B) (hle : B ≤ B') :
    OrderedIsContained A B' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun a b hab => hle (hf a b hab)⟩

/-! ### The ordered arrow relation and its transport calculus -/

/-- **The ordered Ramsey arrow relation.** Every edge-labelling `C` of the host
`G : SimpleGraph (Fin n)` by colours `ι` contains, in some colour `c`, an order-preserving copy of
the colour-`c` target `H c : SimpleGraph (Fin (sz c))`. -/
def OrderedArrow {n : Nat} (G : SimpleGraph (Fin n)) {ι : Type w} {sz : ι → Nat}
    (H : (c : ι) → SimpleGraph (Fin (sz c))) : Prop :=
  ∀ C : G.EdgeLabeling ι, ∃ c : ι, OrderedIsContained (H c) (C.labelGraph c)

variable {n : Nat} {G : SimpleGraph (Fin n)} {ι : Type w} {sz sz' : ι → Nat}

/-- **Target antitonicity.** An ordered arrow relation persists if every colour's target is
replaced by one it already ordered-contains — an easier target to find. -/
theorem OrderedArrow.mono_target {H : (c : ι) → SimpleGraph (Fin (sz c))}
    {H' : (c : ι) → SimpleGraph (Fin (sz' c))} (hsub : ∀ c, OrderedIsContained (H' c) (H c))
    (h : OrderedArrow G H) : OrderedArrow G H' :=
  fun C => (h C).imp fun c => (hsub c).trans

/-- **Host monotonicity under plain subgraph inclusion**, on the same `Fin n`: adding edges to the
host can only help find an order-preserving copy of the target (the copy's order embedding is
untouched — only the adjacency-preservation proof needs to be transported through the larger edge
set). -/
theorem OrderedArrow.mono_host_le {G G' : SimpleGraph (Fin n)}
    {H : (c : ι) → SimpleGraph (Fin (sz c))} (hle : G ≤ G') (h : OrderedArrow G H) :
    OrderedArrow G' H :=
  fun C' => (h _).imp fun c hc => hc.mono_right (C'.labelGraph_pullback_ofLE hle c)

/-- **Host-size monotonicity for complete hosts.** If `⊤ : SimpleGraph (Fin n)` ordered-arrows
`H`, so does `⊤ : SimpleGraph (Fin m)` for any `m ≥ n`, transported along `Fin.castLEOrderEmb`.
Restricted to complete hosts deliberately: any order embedding `Fin n ↪o Fin m` is automatically a
graph embedding `⊤ ↪g ⊤`, which is not available for a non-complete host of a strictly larger
`Fin m` in general (nothing forces the larger host's extra edges to align with the order-preserving
image of the smaller one). -/
theorem OrderedArrow.mono_completeHost {m : Nat} (hnm : n ≤ m)
    {H : (c : ι) → SimpleGraph (Fin (sz c))}
    (h : OrderedArrow (⊤ : SimpleGraph (Fin n)) H) :
    OrderedArrow (⊤ : SimpleGraph (Fin m)) H := by
  intro C'
  obtain ⟨c, f, hf⟩ :=
    h (C'.pullback (Embedding.completeGraph (Fin.castLEOrderEmb hnm).toEmbedding).toHom)
  refine ⟨c, f.trans (Fin.castLEOrderEmb hnm), fun a b hab => ?_⟩
  obtain ⟨hadj, hcol⟩ := (EdgeLabeling.labelGraph_adj _ _).mp (hf a b hab)
  exact (EdgeLabeling.labelGraph_adj _ _).mpr ⟨by simpa using hadj, hcol⟩

/-! ### Ordering never matters for complete-graph targets -/

/-- **Ordered containment of a complete-graph target coincides with ordinary containment**, in any
host `B`. Forward direction: re-sort an arbitrary copy's image via `Finset.orderEmbOfFin`, using
that the source being complete means every pair of distinct sorted-image elements is still
guaranteed `B`-adjacent (the image finset is a clique in `B`, independent of enumeration order).
Backward direction: an ordered copy is a fortiori an ordinary one. A non-complete target's edges
would generally not survive an arbitrary re-enumeration of the same image, which is what makes
this special to complete-graph targets. -/
theorem completeGraph_isContained_iff_orderedIsContained {s n : Nat} {B : SimpleGraph (Fin n)} :
    completeGraph (Fin s) ⊑ B ↔ OrderedIsContained (completeGraph (Fin s)) B := by
  refine ⟨fun ⟨f⟩ => ?_, (·.isContained)⟩
  let S := Finset.univ.map f.toEmbedding
  have hcard : S.card = s := by simp [S]
  refine ⟨⟨S.orderEmbOfFin hcard, fun a b hab => ?_⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_map.mp (S.orderEmbOfFin_mem hcard a)
  obtain ⟨j, -, hj⟩ := Finset.mem_map.mp (S.orderEmbOfFin_mem hcard b)
  rw [← hi, ← hj]
  exact f.toHom.map_adj ((top_adj _ _).mpr fun hij =>
    hab.ne ((S.orderEmbOfFin hcard).injective (by rw [← hi, ← hj, hij])))

/-- **Ordering never matters when every colour's target is a complete graph**, for an arbitrary
(not necessarily two-colour) palette `ι`: `OrderedArrow` and the order-forgetting
containment-based arrow statement coincide exactly. The precise general fact behind
`orderedArrowNumber_completeGraph_eq_ramseyNumber` below. -/
theorem orderedArrow_completeGraph_iff {sz : ι → Nat} :
    OrderedArrow G (fun c => completeGraph (Fin (sz c))) ↔
      ∀ C : G.EdgeLabeling ι, ∃ c : ι, completeGraph (Fin (sz c)) ⊑ C.labelGraph c :=
  forall_congr' fun _ => exists_congr fun _ => completeGraph_isContained_iff_orderedIsContained.symm

/-! ### Executable decidability -/

section OrderedIsContainedDecidable

variable {m n : Nat} {A : SimpleGraph (Fin m)} {B : SimpleGraph (Fin n)}
  [DecidableRel A.Adj] [DecidableRel B.Adj]

/-- **An ordered copy witness.** A function `Fin m → Fin n` is an "ordered copy witness" of `A` in
`B` when it is strictly monotone (the raw content of `OrderEmbedding`, using explicit binders so
decidable-search instances apply directly) and adjacency-preserving. Unlike `OrderedCopy A B`
itself, this is a `Prop` about a plain function, so it is the right shape to run a
`Fintype`-indexed decidable search over. -/
def IsOrderedCopyWitness (A : SimpleGraph (Fin m)) (B : SimpleGraph (Fin n))
    (f : Fin m → Fin n) : Prop :=
  (∀ a b : Fin m, a < b → f a < f b) ∧ ∀ a b : Fin m, A.Adj a b → B.Adj (f a) (f b)

instance : DecidablePred (IsOrderedCopyWitness A B) := fun f => by
  unfold IsOrderedCopyWitness
  infer_instance

omit [DecidableRel A.Adj] [DecidableRel B.Adj] in
/-- `OrderedCopy A B` unpacks exactly to an ordered copy witness: its order-embedding component is
the strict-monotonicity side, its subtype proof is the adjacency-preserving side. -/
theorem nonempty_orderedCopy_iff_exists_isOrderedCopyWitness :
    Nonempty (OrderedCopy A B) ↔ ∃ f : Fin m → Fin n, IsOrderedCopyWitness A B f :=
  ⟨fun ⟨f, hf⟩ => ⟨f, fun _ _ h => f.strictMono h, hf⟩,
    fun ⟨f, hmono, hpres⟩ => ⟨⟨.ofStrictMono f fun _ _ => hmono _ _, hpres⟩⟩⟩

/-- **Decidability of ordered containment**, for finite `A`, `B` with decidable adjacency: a finite
search over ordered copy witnesses `Fin m → Fin n`, which mathlib's `Fintype` instance for
`Fin m → Fin n` together with the decidable `IsOrderedCopyWitness` predicate above already make
into a decidable finite existential. -/
instance decidableOrderedIsContained : Decidable (OrderedIsContained A B) :=
  decidable_of_iff _ nonempty_orderedCopy_iff_exists_isOrderedCopyWitness.symm

end OrderedIsContainedDecidable

section OrderedArrowDecidable

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {sz : ι → Nat} {H : (c : ι) → SimpleGraph (Fin (sz c))}
  [∀ c, DecidableRel (H c).Adj]

/-- **Decidability of the ordered arrow**, for a finite host `G`, a finite colour type `ι`, and
targets `H c` with decidable adjacency throughout, by exactly the same finite-search argument as
`decidableOrderedIsContained`. -/
instance decidableOrderedArrow : Decidable (OrderedArrow G H) := by
  unfold OrderedArrow; infer_instance

/-- **The executable ordered arrow.** A `Bool` computed by the decision procedure above, runnable
with `#eval` or `decide`. -/
def orderedArrowB (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : (c : ι) → SimpleGraph (Fin (sz c))) [∀ c, DecidableRel (H c).Adj] : Bool :=
  decide (OrderedArrow G H)

/-- The semantic/executable equivalence for the ordered arrow. -/
theorem orderedArrow_iff_orderedArrowB_eq_true : OrderedArrow G H ↔ orderedArrowB G H = true :=
  decide_eq_true_iff.symm

end OrderedArrowDecidable

/-! ### The ordered Ramsey number -/

section OrderedArrowNumber

/-- **The ordered Ramsey number**: the least `n` such that the complete host `Fin n` ordered-arrows
`H`. Defined by `sInf`, so it is `0` when no such `n` exists; general existence for ordered targets
is a separate theorem not developed here. -/
noncomputable def orderedArrowNumber (H : (c : ι) → SimpleGraph (Fin (sz c))) : ℕ :=
  sInf {n | OrderedArrow (⊤ : SimpleGraph (Fin n)) H}

variable {H : (c : ι) → SimpleGraph (Fin (sz c))} {n : ℕ}

/-- Any proved ordered arrow gives an upper bound on `orderedArrowNumber`. -/
theorem orderedArrowNumber_le_of_arrow (h : OrderedArrow (⊤ : SimpleGraph (Fin n)) H) :
    orderedArrowNumber H ≤ n :=
  Nat.sInf_le h

/-- If some complete host ordered-arrows `H`, so does the one of size `orderedArrowNumber H`. -/
theorem orderedArrow_orderedArrowNumber (hex : ∃ n, OrderedArrow (⊤ : SimpleGraph (Fin n)) H) :
    OrderedArrow (⊤ : SimpleGraph (Fin (orderedArrowNumber H))) H :=
  Nat.sInf_mem (s := {n | OrderedArrow (⊤ : SimpleGraph (Fin n)) H}) hex

/-- **The least-number characterisation**, given existence. Monotone in the host size via
`OrderedArrow.mono_completeHost`. -/
theorem orderedArrow_iff_orderedArrowNumber_le
    (hex : ∃ n, OrderedArrow (⊤ : SimpleGraph (Fin n)) H) :
    OrderedArrow (⊤ : SimpleGraph (Fin n)) H ↔ orderedArrowNumber H ≤ n :=
  ⟨orderedArrowNumber_le_of_arrow,
    fun hle => OrderedArrow.mono_completeHost hle (orderedArrow_orderedArrowNumber hex)⟩

/-- Below the ordered Ramsey number the complete host does not ordered-arrow `H`. -/
theorem not_orderedArrow_of_lt_orderedArrowNumber (h : n < orderedArrowNumber H) :
    ¬ OrderedArrow (⊤ : SimpleGraph (Fin n)) H :=
  fun ha => (orderedArrowNumber_le_of_arrow ha).not_gt h

end OrderedArrowNumber

/-! ### Clique targets: ordered and ordinary Ramsey numbers agree -/

/-- For clique targets the ordered arrow is the ordinary `Arrow`. -/
theorem orderedArrow_completeGraph_iff_arrow {sz : ι → ℕ} :
    OrderedArrow G (fun c => completeGraph (Fin (sz c))) ↔
      G.Arrow (fun c => completeGraph (Fin (sz c))) :=
  orderedArrow_completeGraph_iff

/-- **Ordering does not change clique Ramsey numbers.** The ordered Ramsey number of clique
targets is the Ramsey number `ramseyNumber sz`. -/
theorem orderedArrowNumber_completeGraph_eq_ramseyNumber (sz : ι → ℕ) :
    orderedArrowNumber (fun c => completeGraph (Fin (sz c))) = ramseyNumber sz :=
  congrArg sInf (Set.ext fun _ => orderedArrow_completeGraph_iff_arrow)

end SimpleGraph
