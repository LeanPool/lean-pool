/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Decomposition
import LeanPool.Parikh.InsertionSequences
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Algebra.Order.Group.Nat

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# When can a family of cycles be used together?

A context can be inserted only if its root label is already present. One
insertion may introduce labels needed by another, so first uses require an
order. Once a context is enabled, growing support keeps it enabled.

We first study this without grammar syntax: each operation requires a label
and adds a set of labels. `first_occurrences` reduces a valid sequence to an
activation order, and `positive_multiplicities` permits arbitrary additional
copies. The later results realize these operations by tree insertions.

`one_linear` is the payoff: a chosen activatable family describes one linear
set. Its base includes one copy of every chosen context; its periods describe
extra copies. Context identities are retained throughout, because equal weights
do not imply equal root requirements or equal added support.

Source: `def:activation`, `lem:first-occurrence`, `lem:multiplicities`, `prop:one-linear`.
-/
namespace Parikh

/-- Execute operations in an order that makes each required label available.
Starting with support `U`, operation `c` requires `required c ∈ U` and enlarges
support to `U ∪ added c` before the rest of the list is considered. Nothing is
removed, so a label that has become available stays available (`eq:activation`). -/
@[expose] def ActivationOrder {N C : Type*} (required : C → N) (added : C → Set N) :
    Set N → List C → Prop
  | _, [] => True
  | U, c :: cs => required c ∈ U ∧ ActivationOrder required added (U ∪ added c) cs

/-- A finite family admits an enabled order using each member exactly once.
This describes the first-use phase. For cycle contexts, later repetitions are
possible because support only grows; `positive_multiplicities` makes that
consequence precise under its additional self-enabling hypothesis. -/
@[expose] def Activatable {N C : Type*} (required : C → N) (added : C → Set N)
    (U : Set N) (D : Finset C) : Prop :=
  ∃ order : List C, order.Nodup ∧ (∀ c, c ∈ order ↔ c ∈ D) ∧
    ActivationOrder required added U order

namespace ActivationOrder
variable {N C : Type*} {required : C → N} {added : C → Set N}

/-- An operation may be omitted when everything it adds is already present. -/
theorem filter_of_covered {U : Set N} {cs : List C}
    (h : ActivationOrder required added U cs) (p : C → Bool)
    (hcovered : ∀ c ∈ cs, p c = false → added c ⊆ U) :
    ActivationOrder required added U (cs.filter p) := by
  induction cs generalizing U with
  | nil => simp [ActivationOrder]
  | cons c cs ih =>
    cases hp : p c with
    | false =>
      have hU : U ∪ added c = U :=
        Set.union_eq_left.mpr (hcovered c (by simp) hp)
      have htail : ActivationOrder required added U cs := by
        simpa only [hU] using h.2
      simpa only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte] using
        ih htail (fun d hd hpd => hcovered d (List.mem_cons_of_mem c hd) hpd)
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, ActivationOrder]
      refine ⟨h.1, ih h.2 ?_⟩
      intro d hd hpd x hx
      exact Or.inl (hcovered d (List.mem_cons_of_mem c hd) hpd hx)

/-- If every requested root is already present, any finite order is enabled. -/
theorem of_forall_mem {U : Set N} {cs : List C}
    (h : ∀ c ∈ cs, required c ∈ U) : ActivationOrder required added U cs := by
  induction cs generalizing U with
  | nil => simp [ActivationOrder]
  | cons c cs ih =>
    refine ⟨h c (by simp), ih ?_⟩
    intro d hd
    exact Or.inl (h d (List.mem_cons_of_mem c hd))

/-- After an activation pass, append any operations whose roots it supplies. -/
theorem append_of_covered {U : Set N} {cs ds : List C}
    (h : ActivationOrder required added U cs)
    (hcovered : ∀ d ∈ ds, required d ∈ U ∨ ∃ c ∈ cs, required d ∈ added c) :
    ActivationOrder required added U (cs ++ ds) := by
  induction cs generalizing U with
  | nil =>
    apply of_forall_mem
    intro d hd
    simpa using hcovered d hd
  | cons c cs ih =>
    refine ⟨h.1, ih h.2 ?_⟩
    intro d hd
    rcases hcovered d hd with hU | ⟨b, hb, hadded⟩
    · exact Or.inl (Or.inl hU)
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl (Or.inr hadded)
      · exact Or.inr ⟨b, hb, hadded⟩
end ActivationOrder

/-- A valid sequence's distinct first occurrences activate the same set (`lem:first-occurrence`). -/
theorem first_occurrences {N C : Type*} [DecidableEq C]
    (required : C → N) (added : C → Set N) (U : Set N) (cs : List C)
    (h : ActivationOrder required added U cs) :
    Activatable required added U cs.toFinset := by
  induction cs generalizing U with
  | nil => exact ⟨[], by simp, by simp, by simp [ActivationOrder]⟩
  | cons c cs ih =>
    obtain ⟨order, hnd, hmem, horder⟩ := ih (U ∪ added c) h.2
    have hfiltered := horder.filter_of_covered (fun d => decide (d ≠ c)) (by
      intro d hd hp
      have heq : d = c := by simpa using hp
      subst d
      exact Set.subset_union_right)
    refine ⟨c :: order.filter (fun d => decide (d ≠ c)), ?_, ?_, h.1, hfiltered⟩
    · exact List.nodup_cons.mpr ⟨by simp, List.Nodup.filter _ hnd⟩
    · intro d
      simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq, hmem,
        List.mem_toFinset]
      tauto

/-- After activation, every positive multiplicity is possible (`lem:multiplicities`). -/
theorem positive_multiplicities {N C : Type*} [DecidableEq C]
    (required : C → N) (added : C → Set N) (U : Set N) (D : Finset C)
    (hself : ∀ c ∈ D, required c ∈ added c) (h : Activatable required added U D)
    (m : C → ℕ) (hm : ∀ c ∈ D, 0 < m c) :
    ∃ cs : List C, ActivationOrder required added U cs ∧
      (∀ c, c ∈ cs ↔ c ∈ D) ∧ (∀ c ∈ D, cs.count c = m c) := by
  obtain ⟨order, hnd, hmem, horder⟩ := h
  -- Pay for every operation once, then append the requested extra copies.
  let extra := order.flatMap (fun c => List.replicate (m c - 1) c)
  have hextra : ∀ c ∈ extra, c ∈ D := by
    intro c hc
    obtain ⟨d, hd, hrep⟩ := List.mem_flatMap.mp hc
    have hcd := List.eq_of_mem_replicate hrep
    exact hcd ▸ (hmem d).mp hd
  have hact : ActivationOrder required added U (order ++ extra) :=
    horder.append_of_covered (by
      intro c hc
      have hD := hextra c hc
      exact Or.inr ⟨c, (hmem c).mpr hD, hself c hD⟩)
  refine ⟨order ++ extra, hact, ?_, ?_⟩
  · intro c
    constructor
    · intro hc
      rcases List.mem_append.mp hc with hc | hc
      · exact (hmem c).mp hc
      · exact hextra c hc
    · intro hc
      exact List.mem_append_left _ ((hmem c).mpr hc)
  · intro c hc
    have hone : order.count c = 1 := List.count_eq_one_of_mem hnd ((hmem c).mpr hc)
    have hcount : extra.count c = m c - 1 := by
      dsimp only [extra]
      rw [List.count_flatMap]
      have hzero : ∀ d, d ≠ c → d ∈ order →
          (List.count c ∘ fun b => List.replicate (m b - 1) b) d = 0 := by
        intro d hdc hd
        simp [List.count_replicate, hdc]
      rw [List.sum_map_eq_nsmul_single c _ hzero, hone]
      simp
    rw [List.count_append, hone, hcount]
    have hpositive := hm c hc
    omega

/-- With matching cycles, enabled support transitions are exactly realizable
tree insertion sequences (`lem:activation-realize`). Repeated cycles are allowed. -/
theorem activationOrder_iff_insertionSequence {T : Type*} {g : ContextFreeGrammar T}
    (roots : ParseTree T g.NT → g.NT) (B : ParseTree T g.NT)
    (Cs : List (ParseTree T g.NT)) (hB : Complete g B)
    (hCs : ∀ C ∈ Cs, Cycle g C (roots C)) :
    ActivationOrder roots ParseTree.support B.support Cs ↔
      ∃ t, InsertionSequence g B Cs t := by
  classical
  induction Cs generalizing B with
  | nil => exact ⟨fun _ => ⟨B, .nil B⟩, fun _ => True.intro⟩
  | cons C Cs ih =>
    have hC := hCs C (by simp)
    have htail : ∀ D ∈ Cs, Cycle g D (roots D) :=
      fun D hD => hCs D (List.mem_cons_of_mem C hD)
    constructor
    · intro horder
      obtain ⟨next, hstep⟩ := (insertion_enabled g B C (roots C) hB hC).mpr horder.1
      have hsupport := (insertion_accounting g B C next hstep).2.2.2
      have hnext : ActivationOrder roots ParseTree.support next.support Cs := by
        simpa only [hsupport] using horder.2
      obtain ⟨t, hseq⟩ := (ih next hstep.2.1 htail).mp hnext
      exact ⟨t, .cons hstep hseq⟩
    · rintro ⟨t, hseq⟩
      cases hseq with
      | @cons _ _ next _ _ hstep hrest =>
        refine ⟨(insertion_enabled g B C (roots C) hB hC).mp ⟨next, hstep⟩, ?_⟩
        have hsupport := (insertion_accounting g B C next hstep).2.2.2
        rw [← hsupport]
        exact (ih next hstep.2.1 htail).mpr ⟨t, hrest⟩

/-- Exact finite-search interface, implemented by `activationTest` in `ActivationAlgorithm`.
`lem:activation-test`: no choice of an enabled operation can cause a false rejection.
-/
structure ActivationTest (N C : Type*) [DecidableEq N] [DecidableEq C] where
  /-- Decide whether all operations can be activated from the initial support. -/
  run : (C → N) → (C → Finset N) → Finset N → Finset C → Bool
  correct : ∀ required added U D,
    run required added U D = true ↔
      Activatable required (fun c => (added c : Set N)) (U : Set N) D

/-- Concrete context subsets do not need a `DecidableEq g.NT` public hypothesis. -/
@[expose] def ContextsActivatable {T : Type*} (g : ContextFreeGrammar T)
    (B : ParseTree T g.NT) (D : Finset (ParseTree T g.NT)) : Prop :=
  ∃ order : List (ParseTree T g.NT), order.Nodup ∧
    (∀ C, C ∈ order ↔ C ∈ D) ∧
    ∃ roots : ParseTree T g.NT → g.NT,
      (∀ C ∈ D, Cycle g C (roots C)) ∧
      ActivationOrder roots ParseTree.support B.support order

/-- Introduce each selected context once, with exact accounting and every
selected context enabled afterwards (`lem:activation-realize`, `eq:activated-wt/supp`). -/
theorem ContextsActivatable.realize {T : Type*} [DecidableEq T]
    {g : ContextFreeGrammar T} {B : ParseTree T g.NT} {D : Finset (ParseTree T g.NT)}
    (hD : ContextsActivatable g B D) (hB : Complete g B) :
    ∃ order t, order.Nodup ∧ (∀ C, C ∈ order ↔ C ∈ D) ∧
      InsertionSequence g B order t ∧ Complete g t ∧ t.root = B.root ∧
      t.weight = B.weight + ∑ C ∈ D, C.weight ∧
      t.support = B.support ∪ ⋃ C ∈ D, C.support ∧
      ∀ C ∈ D, ∃ t', Inserts g t C t' := by
  classical
  obtain ⟨order, hnd, hmem, roots, hcycles, horder⟩ := hD
  obtain ⟨t, hseq⟩ := (activationOrder_iff_insertionSequence roots B order hB
    (fun C hC => hcycles C ((hmem C).mp hC))).mp horder
  obtain ⟨ht, hroot, hweight, _, hsupport⟩ := hseq.accounting hB
  have hset : order.toFinset = D := by
    ext C
    simpa only [List.mem_toFinset] using hmem C
  have hsum : (order.map ParseTree.weight).sum = ∑ C ∈ D, C.weight := by
    rw [← hset]
    exact (List.sum_toFinset ParseTree.weight hnd).symm
  have hsupportD : t.support = B.support ∪ ⋃ C ∈ D, C.support := by
    simpa only [hmem] using hsupport
  refine ⟨order, t, hnd, hmem, hseq, ht, hroot, ?_, hsupportD, ?_⟩
  · simpa only [hsum] using hweight
  · intro C hC
    apply (insertion_enabled g t C (roots C) ht (hcycles C hC)).mpr
    rw [hsupportD]
    apply Or.inr
    simp only [Set.mem_iUnion]
    exact ⟨C, hC, (hcycles C hC).root_mem_support⟩

/-- Every selected context is paid once in the base (`eq:component-base`). -/
@[expose] noncomputable def contextComponent {T : Type*} [DecidableEq T]
    (B : ParseTree T N) (D : Finset (ParseTree T N)) : Component T := by
  classical
  exact ⟨B.weight + ∑ C ∈ D, C.weight, D.toList.map ParseTree.weight⟩

/-- Reindex the period list by its context identities (`eq:component`).
Equal or zero weights retain independent natural coefficients. -/
theorem contextComponent.mem_denotation_iff {T N : Type*} [DecidableEq T]
    (B : ParseTree T N) (D : Finset (ParseTree T N)) (v : Vector T) :
    v ∈ (contextComponent B D).denotation ↔
      ∃ k : ParseTree T N → ℕ,
        v = (B.weight + ∑ C ∈ D, C.weight) + ∑ C ∈ D, k C • C.weight := by
  classical
  have hrange : Set.range (contextComponent B D).periods.get =
      Set.range (fun C : D => C.val.weight) := by
    ext w
    simp [contextComponent]
  rw [Component.denotation_eq_vadd_closure, hrange]
  simp only [Set.mem_vadd_set, SetLike.mem_coe, vadd_eq_add,
    AddSubmonoid.mem_closure_range_iff_of_fintype]
  constructor
  · rintro ⟨w, ⟨k, rfl⟩, rfl⟩
    let coeff : ParseTree T N → ℕ := fun C => if hC : C ∈ D then k ⟨C, hC⟩ else 0
    refine ⟨coeff, ?_⟩
    change (B.weight + ∑ C ∈ D, C.weight) + (∑ C : D, k C • C.val.weight) = _
    congr 1
    rw [← Finset.sum_coe_sort D]
    apply Finset.sum_congr rfl
    intro C _
    simp [coeff, C.property]
  · rintro ⟨k, rfl⟩
    refine ⟨∑ C : D, k C.val • C.val.weight, ⟨fun C => k C.val, rfl⟩, ?_⟩
    change (B.weight + ∑ C ∈ D, C.weight) + (∑ C : D, k C.val • C.val.weight) = _
    rw [Finset.sum_coe_sort D (fun C => k C • C.weight)]

/-- The explicit finite-union formula, retaining context identities (`eq:main`). -/
@[expose] def treeRepresentation {T : Type*} [DecidableEq T] (g : ContextFreeGrammar T) :
    Set (Vector T) :=
  {v | ∃ B D, IsBase g B ∧ (∀ C ∈ D, IsBoundedCycle g C) ∧
    ContextsActivatable g B D ∧ v ∈ (contextComponent B D).denotation}

/-- The weights obtained using exactly an activatable family of contexts form
one linear component (`prop:one-linear`).
Every selected context must occur at least once. These first copies are included
in the component's base; its period coefficients count additional copies.
The equality proves both that insertion yields only these vectors and that
every choice of coefficients can be realized by an insertion sequence. -/
theorem one_linear {T : Type*} [DecidableEq T] (g : ContextFreeGrammar T)
    (B : ParseTree T g.NT) (D : Finset (ParseTree T g.NT))
    (hB : Complete g B) (hD : ContextsActivatable g B D) :
    {v | ∃ t Cs, InsertionSequence g B Cs t ∧
      (∀ C, C ∈ Cs ↔ C ∈ D) ∧ t.weight = v} =
      (contextComponent B D).denotation := by
  classical
  have sum_counts : ∀ (Cs : List (ParseTree T g.NT))
      (hmem : ∀ C, C ∈ Cs ↔ C ∈ D),
      (Cs.map ParseTree.weight).sum = ∑ C ∈ D, Cs.count C • C.weight := by
    intro Cs hmem
    have hset : Cs.toFinset = D := by
      ext C
      simpa only [List.mem_toFinset] using hmem C
    rw [Finset.sum_list_map_count, hset]
  ext v
  rw [contextComponent.mem_denotation_iff]
  constructor
  · rintro ⟨t, Cs, hseq, hmem, rfl⟩
    refine ⟨fun C => Cs.count C - 1, ?_⟩
    rw [(hseq.accounting hB).2.2.1, sum_counts Cs hmem]
    have hsplit : ∑ C ∈ D, Cs.count C • C.weight =
        (∑ C ∈ D, C.weight) + ∑ C ∈ D, (Cs.count C - 1) • C.weight := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro C hC
      have hpositive : 0 < Cs.count C := List.count_pos_iff.mpr ((hmem C).mpr hC)
      have hcount : Cs.count C = 1 + (Cs.count C - 1) := by omega
      conv_lhs => rw [hcount]
      rw [add_nsmul, one_nsmul]
    rw [hsplit, add_assoc]
  · rintro ⟨k, rfl⟩
    obtain ⟨order, hnd, hmem, roots, hcycles, horder⟩ := hD
    have hact : Activatable roots ParseTree.support B.support D := ⟨order, hnd, hmem, horder⟩
    obtain ⟨Cs, hCs, hCs_mem, hcount⟩ := positive_multiplicities roots ParseTree.support
      B.support D (fun C hC => (hcycles C hC).root_mem_support) hact
      (fun C => k C + 1) (by simp)
    obtain ⟨t, hseq⟩ := (activationOrder_iff_insertionSequence roots B Cs hB
      (fun C hC => hcycles C ((hCs_mem C).mp hC))).mp hCs
    refine ⟨t, Cs, hseq, hCs_mem, ?_⟩
    rw [(hseq.accounting hB).2.2.1, sum_counts Cs hCs_mem]
    have hsplit : ∑ C ∈ D, Cs.count C • C.weight =
        (∑ C ∈ D, C.weight) + ∑ C ∈ D, k C • C.weight := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro C hC
      rw [hcount C hC, add_nsmul, one_nsmul, add_comm]
    rw [hsplit, add_assoc]

/-- The distinct contexts used by an insertion sequence are activatable from
its complete base (`lem:first-occurrence`, `thm:main`). Context identities are retained. -/
theorem InsertionSequence.contextsActivatable {T : Type*} {g : ContextFreeGrammar T}
    {B t : ParseTree T g.NT} {Cs : List (ParseTree T g.NT)}
    [DecidableEq (ParseTree T g.NT)]
    (h : InsertionSequence g B Cs t) (hB : Complete g B) :
    ContextsActivatable g B Cs.toFinset := by
  classical
  have hcycles : ∀ C ∈ Cs, ∃ A, Cycle g C A := by
    clear hB
    induction h with
    | nil _ => simp
    | cons step _ ih =>
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC
      · obtain ⟨_, _, A, hcycle, _⟩ := step
        exact ⟨A, hcycle⟩
      · exact ih C hC
  let roots : ParseTree T g.NT → g.NT := fun C =>
    if hC : C ∈ Cs then Classical.choose (hcycles C hC) else g.initial
  have hrootcycles : ∀ C ∈ Cs, Cycle g C (roots C) := by
    intro C hC
    simpa only [roots, dite_eq_left hC] using Classical.choose_spec (hcycles C hC)
  have horder := (activationOrder_iff_insertionSequence roots B Cs hB hrootcycles).mpr ⟨t, h⟩
  obtain ⟨order, hnodup, hmem, hfirst⟩ :=
    first_occurrences roots ParseTree.support B.support Cs horder
  exact ⟨order, hnodup, hmem, roots,
    fun C hC => hrootcycles C (List.mem_toFinset.mp hC), hfirst⟩

end Parikh
