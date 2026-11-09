/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColorDegreeBounds

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.ColoredVertexSetStronglyClosed
public import LeanPool.GoldbergSeymour.DensityLowerBound
public import LeanPool.GoldbergSeymour.Elementary
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.MaximumDegree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Strongly Closed Witness Elementary

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_missingPairs_le_67.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (phi : PartialEdgeColoring E k) (X : Finset V), ColoredVertexSetElementary G phi X →
    let allVC : Finset (V × Fin k) := X.product Finset.univ;
    let missingPairs : Finset (V × Fin k) := ({p ∈ allVC | p.2 ∈ MissingColors G phi p.1} : Finset
        (V × Fin k));
    let missingUnion : Finset (Fin k) := ({c : Fin k |
    ∃ v ∈ X, c ∈ MissingColors G phi v} : Finset (Fin k)); missingPairs.card ≤ missingUnion.card
  := by
  classical
  intro V E _ _ G k phi X helementary allVC missingPairs missingUnion
  let _ := Fintype.ofFinite V
  apply Finset.card_le_card_of_injOn (fun p : V × Fin k => p.2)
  · intro p hp
    have hpm := (Finset.mem_filter.mp hp).2
    have hpall := (Finset.mem_filter.mp hp).1
    have hpX := (Finset.mem_product.mp hpall).1
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, missingUnion]
    exact ⟨p.1, hpX, hpm⟩
  · intro a ha b hb hab
    have haall := (Finset.mem_filter.mp ha).1
    have hball := (Finset.mem_filter.mp hb).1
    have haX := (Finset.mem_product.mp haall).1
    have hbX := (Finset.mem_product.mp hball).1
    have ham := (Finset.mem_filter.mp ha).2
    have hbm := (Finset.mem_filter.mp hb).2
    have hv : a.1 = b.1 := by
      by_contra hv
      have hd := helementary haX hbX hv
      have hab' : a.2 = b.2 := hab
      rw [← hab'] at hbm
      exact (Finset.disjoint_left.mp hd) ham hbm
    apply Prod.ext
    · exact hv
    · exact hab

private theorem helper_incidences_le_present_158.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] [DecidableEq V] (G : LooplessMultigraph
        V E) (k : ℕ) (phi : PartialEdgeColoring E k) (X : Finset V), IsProperEdgeColoring G phi →
    ∀ (alpha : Fin k),
    let allVC : Finset (V × Fin k) := X.product Finset.univ;
    let presentPairs : Finset (V × Fin k) := ({p ∈ allVC | p.2 ∈ PresentColors G phi p.1} : Finset
        (V × Fin k));
    let incidences : Finset (E × V) := ({p ∈ Finset.univ.product X | Incident G p.2 p.1 ∧
    ∃ (c : Fin k), phi p.1 = some c} : Finset (E × V));
    ∀ (incidence_witness :
    ∀ p ∈ incidences,
    ∃ (c : Fin k), phi p.1 = some c),
    let incidenceColor : E × V → Fin k := fun (p : E × V) ↦ if hp : p ∈ incidences then
        Classical.choose (incidence_witness p hp) else alpha; (
    ∀ p ∈ incidences, phi p.1 = some (incidenceColor p)) → incidences.card ≤ presentPairs.card := by
  classical
  intro V E _ _ _ G k phi X hproper alpha allVC presentPairs incidences incidence_witness
      incidenceColor incidenceColor_spec
  let _ := Fintype.ofFinite V
  apply Finset.card_le_card_of_injOn
    (fun p : E × V => (p.2, incidenceColor p))
  · intro p hp
    have hpbase := (Finset.mem_filter.mp hp).1
    have hpX := (Finset.mem_product.mp hpbase).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hpX, Finset.mem_univ _⟩, ?_⟩
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p.1, (Finset.mem_filter.mp hp).2.1, incidenceColor_spec p hp⟩
  · intro a ha b hb hab
    have hv : a.2 = b.2 := congrArg Prod.fst hab
    have hc : incidenceColor a = incidenceColor b := congrArg Prod.snd hab
    have he : a.1 = b.1 := by
      by_contra he
      have hadj : AdjacentEdges G a.1 b.1 :=
        ⟨a.2, (Finset.mem_filter.mp ha).2.1,
          hv ▸ (Finset.mem_filter.mp hb).2.1⟩
      have hh := hproper he hadj (incidenceColor_spec a ha)
      exact hh (by rw [incidenceColor_spec b hb, hc])
    exact Prod.ext he hv

private theorem helper_incidences_split_223.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V),
        IsOneEdgeUncolored phi e0 →
    let incidences : Finset (E × V) := ({p ∈ Finset.univ.product X | Incident G p.2 p.1 ∧
    ∃ (c : Fin k), phi p.1 = some c} : Finset (E × V));
    let internalColored : Finset E := (InternalEdges G X).erase e0;
    let boundary : Finset E := BoundaryEdges G X;
    let internalInc : Finset (E × V) := ({p ∈ incidences | p.1 ∈ internalColored} : Finset (E ×
        V));
    let boundaryInc : Finset (E × V) := ({p ∈ incidences | p.1 ∈ boundary} : Finset (E × V)); (
    ∀ {e : E} {v : V}, v ∈ X → Incident G v e → e ∈ InternalEdges G X ∨ e ∈ BoundaryEdges G X) →
        internalInc ∪ boundaryInc = incidences := by
  classical
  intro V E _ _ _ G k e0 phi X hone incidences internalColored boundary internalInc boundaryInc
      edge_classification
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · exact (Finset.mem_filter.mp hp).1
  · intro hp
    have hpbase := (Finset.mem_filter.mp hp).1
    have hpX := (Finset.mem_product.mp hpbase).2
    have hpinc := (Finset.mem_filter.mp hp).2.1
    rcases edge_classification hpX hpinc with hi | hb
    · have hne : p.1 ≠ e0 := by
        intro heq
        obtain ⟨c, hc⟩ := (Finset.mem_filter.mp hp).2.2
        have hc0 : phi p.1 = none := by rw [heq]; exact hone.1
        rw [hc0] at hc
        cases hc
      exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hp, Finset.mem_erase.mpr ⟨hne, hi⟩⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp, hb⟩))

private theorem helper_edgeInc_insert_256.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [DecidableEq V] (G : LooplessMultigraph V E)
      (X : Finset V),
    let edgeInc : Finset E → Finset (E × V) := fun (s : Finset E) ↦
      ({p ∈ s.product X | Incident G p.2 p.1} : Finset (E × V));
    ∀ (e : E) (s : Finset E),
    edgeInc (insert e s : Finset E) = edgeInc ({ e } : Finset E) ∪ edgeInc s := by
  classical
  intro V E _ G X edgeInc e s
  ext p
  constructor
  · intro hp
    have hpProd := (Finset.mem_filter.mp hp).1
    have hpInc := (Finset.mem_filter.mp hp).2
    have hpe := (Finset.mem_product.mp hpProd).1
    have hpX := (Finset.mem_product.mp hpProd).2
    rcases Finset.mem_insert.mp hpe with he | hs
    · apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr he, hpX⟩, hpInc⟩)
    · apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs, hpX⟩, hpInc⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have hpProd := (Finset.mem_filter.mp hp).1
      have hpInc := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_insert.mpr (Or.inl
            (Finset.mem_singleton.mp (Finset.mem_product.mp hpProd).1)),
          (Finset.mem_product.mp hpProd).2⟩, hpInc⟩
    · have hpProd := (Finset.mem_filter.mp hp).1
      have hpInc := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_product.mp hpProd).1,
          (Finset.mem_product.mp hpProd).2⟩, hpInc⟩

private theorem helper_edgeInc_single_internal_286.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq V] (G : LooplessMultigraph V E) (X : Finset V),
    let edgeInc : Finset E → Finset (E × V) := fun (s : Finset E) ↦
      ({p ∈ s.product X | Incident G p.2 p.1} : Finset (E × V));
    ∀ e ∈ InternalEdges G X,
    edgeInc ({ e } : Finset E) = ({ e } : Finset E).product (G.ends e).toFinset := by
  classical
  intro V E _ _ _ G X edgeInc e he
  unfold InternalEdges at he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  ext p
  constructor
  · intro hp
    have hpProd := (Finset.mem_filter.mp hp).1
    have hpinc := (Finset.mem_filter.mp hp).2
    have hpe := Finset.mem_singleton.mp (Finset.mem_product.mp hpProd).1
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_singleton.mpr hpe,
      Sym2.mem_toFinset.mpr (hpe ▸ hpinc)⟩
  · intro hp
    have hpe := Finset.mem_singleton.mp (Finset.mem_product.mp hp).1
    have hpend := (Finset.mem_product.mp hp).2
    have hpinc : Incident G p.2 p.1 := by
      rw [hpe]
      exact Sym2.mem_toFinset.mp hpend
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hpe, ?_⟩, hpinc⟩
    exact he p.2 (Sym2.mem_toFinset.mp hpend)

private theorem helper_internal_edgeInc_card_309.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] (G :
        LooplessMultigraph V E) (k : ℕ) (_ : E) (_ : PartialEdgeColoring E k) (X : Finset V), (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) →
    ∀ (_ : V),
    let edgeInc : Finset E → Finset (E × V) := fun (s : Finset E) ↦
        ({p ∈ s.product X | Incident G p.2 p.1} : Finset (E × V)); (
    ∀ (e : E) (s : Finset E), edgeInc (insert e s : Finset E) = edgeInc ({ e } : Finset E) ∪
        edgeInc s) → (
    ∀ e ∈ InternalEdges G X, edgeInc ({ e } : Finset E) = ({ e } : Finset E).product (G.ends
        e).toFinset) →
    ∀ s ⊆ InternalEdges G X, (edgeInc s).card = (2 : ℕ) * s.card := by
  classical
  intro V E _ _ _ G k e0 phi X endpoint_card x edgeInc edgeInc_insert edgeInc_single_internal s hs
  induction s using Finset.induction_on with
  | empty => simp [edgeInc]
  | @insert e s hes ih =>
    rw [edgeInc_insert]
    have hd : Disjoint (edgeInc {e}) (edgeInc s) := by
      rw [Finset.disjoint_left]
      intro p hpe hps
      have hpe' := (Finset.mem_filter.mp hpe).1
      have hps' := (Finset.mem_filter.mp hps).1
      have heq : p.1 = e := Finset.mem_singleton.mp (Finset.mem_product.mp hpe').1
      have hmem : p.1 ∈ s := (Finset.mem_product.mp hps').1
      exact hes (heq ▸ hmem)
    rw [Finset.card_union_of_disjoint hd]
    have heI : e ∈ InternalEdges G X := hs (Finset.mem_insert_self e s)
    rw [edgeInc_single_internal e heI]
    have hprod : (({e} : Finset E).product (G.ends e).toFinset).card = 2 := by
      calc
        _ = ({e} : Finset E).card * (G.ends e).toFinset.card :=
          Finset.card_product _ _
        _ = 2 := by rw [endpoint_card]; simp
    rw [hprod]
    rw [ih (fun z hz => hs (Finset.mem_insert_of_mem hz)),
      Finset.card_insert_of_notMem hes]
    omega

private theorem helper_boundary_edgeInc_card_399.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] (G :
        LooplessMultigraph V E) (k : ℕ) (_ : E) (_ : PartialEdgeColoring E k) (X : Finset V) (_ :
        V),
    let boundary : Finset E := BoundaryEdges G X;
    let edgeInc : Finset E → Finset (E × V) := fun (s : Finset E) ↦
        ({p ∈ s.product X | Incident G p.2 p.1} : Finset (E × V)); (
    ∀ (e : E) (s : Finset E), edgeInc (insert e s : Finset E) = edgeInc ({ e } : Finset E) ∪
        edgeInc s) → (
    ∀ e ∈ boundary, ({v ∈ X | Incident G v e} : Finset V).card = (1 : ℕ)) → (
    ∀ (e : E), edgeInc ({ e } : Finset E) = ({ e } : Finset E).product ({v ∈ X | Incident G v e} :
        Finset V)) →
    ∀ s ⊆ boundary, (edgeInc s).card = s.card := by
  classical
  intro V E _ _ _ G k e0 phi X x boundary edgeInc edgeInc_insert boundary_fiber_card
      edgeInc_single_boundary s hs
  induction s using Finset.induction_on with
  | empty => simp [edgeInc]
  | @insert e s hes ih =>
    rw [edgeInc_insert]
    have hd : Disjoint (edgeInc {e}) (edgeInc s) := by
      rw [Finset.disjoint_left]
      intro p hpe hps
      have hpe' := (Finset.mem_filter.mp hpe).1
      have hps' := (Finset.mem_filter.mp hps).1
      have heq : p.1 = e := Finset.mem_singleton.mp (Finset.mem_product.mp hpe').1
      have hmem : p.1 ∈ s := (Finset.mem_product.mp hps').1
      exact hes (heq ▸ hmem)
    rw [Finset.card_union_of_disjoint hd]
    have heB : e ∈ boundary := hs (Finset.mem_insert_self e s)
    rw [edgeInc_single_boundary e]
    have hprod : (({e} : Finset E).product
        (X.filter (fun v => Incident G v e))).card = 1 := by
      calc
        _ = ({e} : Finset E).card *
            (X.filter (fun v => Incident G v e)).card := Finset.card_product _ _
        _ = 1 := by rw [boundary_fiber_card e heB]; simp
    rw [hprod]
    rw [ih (fun z hz => hs (Finset.mem_insert_of_mem hz)),
      Finset.card_insert_of_notMem hes]
    omega

private theorem helper_presentPairs_le_inc_363.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] [DecidableEq V] (G : LooplessMultigraph
        V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V),
    let allVC : Finset (V × Fin k) := X.product Finset.univ;
    let presentPairs : Finset (V × Fin k) := ({p ∈ allVC | p.2 ∈ PresentColors G phi p.1} : Finset
        (V × Fin k));
    let incidences : Finset (E × V) := ({p ∈ Finset.univ.product X | Incident G p.2 p.1 ∧
    ∃ (c : Fin k), phi p.1 = some c} : Finset (E × V));
    ∀ (present_witness :
    ∀ p ∈ presentPairs,
    ∃ (e : E), Incident G p.1 e ∧ phi e = some p.2),
    let presentEdge : V × Fin k → E := fun (p : V × Fin k) ↦ if hp : p ∈ presentPairs then
        Classical.choose (present_witness p hp) else e0; (
    ∀ p ∈ presentPairs, Incident G p.1 (presentEdge p) ∧ phi (presentEdge p) = some p.2) →
        presentPairs.card ≤ incidences.card := by
  classical
  intro V E _ _ _ G k e0 phi X allVC presentPairs incidences present_witness presentEdge
      presentEdge_spec
  let _ := Fintype.ofFinite V
  apply Finset.card_le_card_of_injOn
    (fun p : V × Fin k => (presentEdge p, p.1))
  · intro p hp
    have hpall := (Finset.mem_filter.mp hp).1
    have hpX := (Finset.mem_product.mp hpall).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hpX⟩,
      (presentEdge_spec p hp).1, p.2, (presentEdge_spec p hp).2⟩
  · intro a ha b hb hab
    have hv : a.1 = b.1 := congrArg (fun p : E × V => p.2) hab
    have he : presentEdge a = presentEdge b := congrArg Prod.fst hab
    have hc : a.2 = b.2 := by
      apply Option.some.inj
      calc
        some a.2 = phi (presentEdge a) := (presentEdge_spec a ha).2.symm
        _ = phi (presentEdge b) := by rw [he]
        _ = some b.2 := (presentEdge_spec b hb).2
    exact Prod.ext hv hc

private theorem helper_edge_classification_411.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (X :
        Finset V) {e : E} {v : V}, v ∈ X → Incident G v e → e ∈ InternalEdges G X ∨ e ∈
        BoundaryEdges G X := by
  classical
  intro V E _ _ G X e v hvX hve
  by_cases hall : ∀ z, Incident G z e → z ∈ X
  · left
    unfold InternalEdges
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hall
  · right
    push Not at hall
    obtain ⟨z, hze, hzX⟩ := hall
    obtain ⟨w, heq⟩ := Sym2.mem_iff_exists.mp hze
    have hvpair : v = z ∨ v = w := by
      have : v ∈ s(z, w) := by rw [← heq]; exact hve
      simpa using this
    have hvw : v = w := hvpair.resolve_left (fun hvz => hzX (hvz ▸ hvX))
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, hvX, z, hzX, by simpa [hvw] using heq.trans Sym2.eq_swap⟩

private theorem helper_internalInc_eq_461.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V), IsOneEdgeUncolored phi e0 →
    let incidences : Finset (E × V) := ({p ∈ Finset.univ.product X | Incident G p.2 p.1 ∧
    ∃ (c : Fin k), phi p.1 = some c} : Finset (E × V));
    let internalColored : Finset E := (InternalEdges G X).erase e0;
    let internalInc : Finset (E × V) := ({p ∈ incidences | p.1 ∈ internalColored} : Finset (E ×
        V));
    let edgeInc : Finset E → Finset (E × V) := fun (s : Finset E) ↦
        ({p ∈ s.product X | Incident G p.2 p.1} : Finset (E × V)); internalInc = edgeInc
        internalColored := by
  classical
  intro V E _ _ G k e0 phi X hone incidences internalColored internalInc edgeInc
  ext p
  constructor
  · intro hp
    have hpi := (Finset.mem_filter.mp hp).1
    have hpe := (Finset.mem_filter.mp hp).2
    have hpbase := (Finset.mem_filter.mp hpi).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hpe, (Finset.mem_product.mp hpbase).2⟩,
        (Finset.mem_filter.mp hpi).2.1⟩
  · intro hp
    have hpbase := (Finset.mem_filter.mp hp).1
    have hpe := (Finset.mem_product.mp hpbase).1
    have hpX := (Finset.mem_product.mp hpbase).2
    have hpinc := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ e0 := (Finset.mem_erase.mp hpe).1
    obtain ⟨c, hc⟩ := hone.2 p.1 hne
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hpX⟩, hpinc, c, hc⟩, hpe⟩

private theorem helper_boundary_fiber_card_489.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      (G : LooplessMultigraph V E) (X : Finset V),
    let boundary : Finset E := BoundaryEdges G X;
    ∀ e ∈ boundary,
    ({v ∈ X | Incident G v e} : Finset V).card = (1 : ℕ) := by
  classical
  intro V E _ _ G X boundary e he
  obtain ⟨u, hu, v, hv, huv⟩ := by
    simpa [boundary, BoundaryEdges] using he
  have hs : X.filter (fun z => Incident G z e) = {u} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton, Incident,
      huv, Sym2.mem_iff]
    constructor
    · rintro ⟨hz, rfl | hzu⟩
      · exact rfl
      · exact False.elim (hv (hzu ▸ hz))
    · intro hzu
      subst z
      exact ⟨hu, Or.inl rfl⟩
  rw [hs]
  simp

private theorem helper_edgeInc_single_boundary_507.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (X : Finset V),
    let edgeInc : Finset E → Finset (E × V) := fun (s : Finset E) ↦
      ({p ∈ s.product X | Incident G p.2 p.1} : Finset (E × V));
    ∀ (e : E),
    edgeInc ({ e } : Finset E) =
      ({ e } : Finset E).product ({v ∈ X | Incident G v e} : Finset V) := by
  classical
  intro V E G X edgeInc e
  ext p
  constructor
  · intro hp
    have hpProd := (Finset.mem_filter.mp hp).1
    have hpinc := (Finset.mem_filter.mp hp).2
    have hpe := Finset.mem_singleton.mp (Finset.mem_product.mp hpProd).1
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hpe,
      Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hpProd).2, hpe ▸ hpinc⟩⟩
  · intro hp
    have hpe := Finset.mem_singleton.mp (Finset.mem_product.mp hp).1
    have hpv := Finset.mem_filter.mp (Finset.mem_product.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_singleton.mpr hpe, hpv.1⟩, hpe.symm ▸ hpv.2⟩

private theorem helper_boundaryInc_eq_527.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V), IsOneEdgeUncolored phi e0 →
    let incidences : Finset (E × V) := ({p ∈ Finset.univ.product X | Incident G p.2 p.1 ∧
    ∃ (c : Fin k), phi p.1 = some c} : Finset (E × V)); (
    ∀ e ∈ BoundaryEdges G X, e ≠ e0) →
    let boundary : Finset E := BoundaryEdges G X;
    let boundaryInc : Finset (E × V) := ({p ∈ incidences | p.1 ∈ boundary} : Finset (E × V));
    let edgeInc : Finset E → Finset (E × V) := fun (s : Finset E) ↦
        ({p ∈ s.product X | Incident G p.2 p.1} : Finset (E × V)); boundaryInc = edgeInc boundary
  := by
  classical
  intro V E _ _ G k e0 phi X hone incidences boundary_ne_e0 boundary boundaryInc edgeInc
  ext p
  constructor
  · intro hp
    have hpi := (Finset.mem_filter.mp hp).1
    have hpe := (Finset.mem_filter.mp hp).2
    have hpbase := (Finset.mem_filter.mp hpi).1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hpe, (Finset.mem_product.mp hpbase).2⟩,
        (Finset.mem_filter.mp hpi).2.1⟩
  · intro hp
    have hpbase := (Finset.mem_filter.mp hp).1
    have hpe := (Finset.mem_product.mp hpbase).1
    have hpX := (Finset.mem_product.mp hpbase).2
    have hpinc := (Finset.mem_filter.mp hp).2
    have hne : p.1 ≠ e0 := boundary_ne_e0 p.1 (by simpa [boundary] using hpe)
    obtain ⟨c, hc⟩ := hone.2 p.1 hne
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hpX⟩, hpinc, c, hc⟩, hpe⟩

private theorem helper_continuation_596.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] (G :
        LooplessMultigraph V E) (k : ℕ), ChromaticIndex G = k + (1 : ℕ) →
    ∀ (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V), IsOneEdgeUncolored phi e0 →
        ColoredVertexSetStronglyClosed G phi X → (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) →
    ∀ (x : V) (_ : Fin k),
    let Y : Finset V := X.erase x; X.card = Y.card + (1 : ℕ) → Odd X.card → (3 : ℕ) ≤ X.card →
    let allVC : Finset (V × Fin k) := X.product Finset.univ;
    let missingPairs : Finset (V × Fin k) := ({p ∈ allVC | p.2 ∈ MissingColors G phi p.1} : Finset
        (V × Fin k));
    let presentPairs : Finset (V × Fin k) := ({p ∈ allVC | p.2 ∈ PresentColors G phi p.1} : Finset
        (V × Fin k));
    let missingUnion : Finset (Fin k) := ({c : Fin k |
    ∃ v ∈ X, c ∈ MissingColors G phi v} : Finset (Fin k)); missingPairs.card ≤ missingUnion.card →
        missingUnion.card ≤ missingPairs.card → missingUnion.card + presentPairs.card = X.card * k
        →
    let incidences : Finset (E × V) := ({p ∈ Finset.univ.product X | Incident G p.2 p.1 ∧
    ∃ (c : Fin k), phi p.1 = some c} : Finset (E × V)); presentPairs.card ≤ incidences.card →
        incidences.card ≤ presentPairs.card → missingUnion.card + incidences.card = X.card * k →
        e0 ∈ InternalEdges G X → (
    ∀ e ∈ BoundaryEdges G X, e ≠ e0) →
    let internalColored : Finset E := (InternalEdges G X).erase e0;
    let boundary : Finset E := BoundaryEdges G X;
    let internalInc : Finset (E × V) := ({p ∈ incidences | p.1 ∈ internalColored} : Finset (E ×
        V));
    let boundaryInc : Finset (E × V) := ({p ∈ incidences | p.1 ∈ boundary} : Finset (E × V));
        incidences.card = internalInc.card + boundaryInc.card →
    let _ : Finset E → Finset (E × V) := fun (s : Finset E) ↦
        ({p ∈ s.product X | Incident G p.2 p.1} : Finset (E × V)); Elementary G := by
  classical
  intro V E _ _ _ G k hindex e0 phi X hone hstrong endpoint_card x alpha Y hXcard hXodd hXthree
      allVC missingPairs presentPairs missingUnion missingPairs_le missingUnion_le
      pairs_card_identity incidences presentPairs_le_inc incidences_le_present
      incidence_color_identity e0_internal boundary_ne_e0 internalColored boundary internalInc
      boundaryInc incidence_edge_identity edgeInc
  have edgeInc_insert : ∀ (e : E) (s : Finset E),
      edgeInc (insert e s) = edgeInc {e} ∪ edgeInc s := by
    exact @helper_edgeInc_insert_256 (@V) (@E) inferInstance (@G) (@X)
  have edgeInc_single_internal : ∀ e, e ∈ InternalEdges G X →
      edgeInc {e} = ({e} : Finset E).product (G.ends e).toFinset := by
    exact @helper_edgeInc_single_internal_286 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@X)
  have internal_edgeInc_card : ∀ s : Finset E, s ⊆ InternalEdges G X →
      (edgeInc s).card = 2 * s.card := by
    exact @helper_internal_edgeInc_card_309 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@X) (@endpoint_card) (@x) (@edgeInc_insert)
        (@edgeInc_single_internal)
  have internalInc_eq : internalInc = edgeInc internalColored := by
    exact @helper_internalInc_eq_461 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi)
        (@X) (@hone)
  have internalInc_card : internalInc.card =
      2 * ((InternalEdges G X).card - 1) := by
    rw [internalInc_eq, internal_edgeInc_card internalColored]
    · have hc := Finset.card_erase_of_mem e0_internal
      dsimp [internalColored]
      omega
    · intro e he
      exact (Finset.mem_erase.mp he).2
  have boundary_fiber_card : ∀ e, e ∈ boundary →
      (X.filter (fun v => Incident G v e)).card = 1 := by
    exact @helper_boundary_fiber_card_489 (@V) (@E) inferInstance inferInstance (@G) (@X)
  have edgeInc_single_boundary :
    ∀ e, edgeInc {e} = ({e} : Finset E).product (X.filter (fun v => Incident G v e)) := by
    exact @helper_edgeInc_single_boundary_507 (@V) (@E) (@G) (@X)
  have boundary_edgeInc_card : ∀ s : Finset E, s ⊆ boundary →
      (edgeInc s).card = s.card := by
    exact @helper_boundary_edgeInc_card_399 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@X) (@x) (@edgeInc_insert) (@boundary_fiber_card)
        (@edgeInc_single_boundary)
  have boundaryInc_eq : boundaryInc = edgeInc boundary := by
    exact @helper_boundaryInc_eq_527 (@V) (@E) inferInstance inferInstance (@G) (@k) (@e0) (@phi)
        (@X) (@hone) (@boundary_ne_e0)
  have boundaryInc_card : boundaryInc.card = boundary.card := by
    rw [boundaryInc_eq, boundary_edgeInc_card boundary (by intro e he; exact he)]
  have edge_incidence_count : incidences.card =
      2 * ((InternalEdges G X).card - 1) + boundary.card := by
    rw [incidence_edge_identity, internalInc_card, boundaryInc_card]
  have boundary_color_witness : ∀ e, e ∈ boundary → ∃ c, phi e = some c := by
    intro e he
    exact hone.2 e (boundary_ne_e0 e (by simpa [boundary] using he))
  let boundaryColor (e : E) : Fin k :=
    if he : e ∈ boundary then Classical.choose (boundary_color_witness e he) else alpha
  have boundaryColor_spec : ∀ e, e ∈ boundary → phi e = some (boundaryColor e) := by
    intro e he
    simp only [boundaryColor, dite_eq_left he]
    exact Classical.choose_spec (boundary_color_witness e he)
  let availableColors := (Finset.univ : Finset (Fin k)) \ missingUnion
  have boundary_maps_available : ∀ e, e ∈ boundary →
      boundaryColor e ∈ availableColors := by
    intro e he
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hm
    obtain ⟨v, hvX, hvm⟩ := by simpa [missingUnion] using hm
    exact (hstrong.1 (by simpa [boundary] using he) hvX
      (boundaryColor_spec e he)) hvm
  have boundaryColor_inj : Set.InjOn boundaryColor (boundary : Set E) := by
    intro e he f hf hef
    by_contra hne
    have hh := hstrong.2 (by simpa [boundary] using he)
      (by simpa [boundary] using hf) hne (boundaryColor_spec e he)
    exact hh (by rw [boundaryColor_spec f hf, hef])
  have boundary_le_available : boundary.card ≤ availableColors.card :=
    Finset.card_le_card_of_injOn boundaryColor boundary_maps_available boundaryColor_inj
  have available_card : availableColors.card = k - missingUnion.card := by
    simp [availableColors, Finset.card_sdiff]
  have boundary_missing_bound : boundary.card + missingUnion.card ≤ k := by
    rw [available_card] at boundary_le_available
    have hmle : missingUnion.card ≤ k := by
      simpa using Finset.card_le_card (Finset.subset_univ missingUnion)
    omega
  have full_count : missingUnion.card +
      (2 * ((InternalEdges G X).card - 1) + boundary.card) = X.card * k := by
    rw [← edge_incidence_count]
    exact incidence_color_identity
  have hXsplit : X.card = (X.card - 1) + 1 := by omega
  have hmul : X.card * k = (X.card - 1) * k + k := by
    calc
      X.card * k = ((X.card - 1) + 1) * k := by rw [← hXsplit]
      _ = (X.card - 1) * k + k := by simp [Nat.add_mul]
  have density_nat_le : (X.card - 1) * k ≤
      2 * ((InternalEdges G X).card - 1) := by
    omega
  have internal_pos : 1 ≤ (InternalEdges G X).card :=
    Finset.card_pos.mpr ⟨e0, e0_internal⟩
  have density_nat_strict : k * (X.card - 1) <
      2 * (InternalEdges G X).card := by
    rw [Nat.mul_comm]
    omega
  have denominator_pos : (0 : ℚ) < (X.card - 1 : ℚ) := by
    have hx : (1 : ℚ) < (X.card : ℚ) := by exact_mod_cast (show 1 < X.card by omega)
    exact sub_pos.mpr hx
  have sub_cast : (X.card - 1 : ℚ) = (↑(X.card - 1) : ℚ) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have witness_density : (k : ℚ) < DensityValue G X := by
    unfold DensityValue
    apply (lt_div_iff₀ denominator_pos).2
    rw [sub_cast]
    exact_mod_cast density_nat_strict
  have X_eligible : EligibleOddSet X := ⟨hXthree, hXodd⟩
  have density_ge_witness : DensityValue G X ≤ Density G := by
    unfold Density
    dsimp
    apply Finset.le_max'
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨X, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ X),
      X_eligible⟩
  have density_gt : (k : ℚ) < Density G := witness_density.trans_le density_ge_witness
  have ceil_ge : k + 1 ≤ DensityCeil G := by
    unfold DensityCeil
    have hceilQ : (k : ℚ) < (⌈Density G⌉₊ : ℚ) :=
      density_gt.trans_le (Nat.le_ceil (Density G))
    have hceilN : k < ⌈Density G⌉₊ := by exact_mod_cast hceilQ
    omega
  have ceil_le : DensityCeil G ≤ k + 1 := by
    rw [← hindex]
    exact DensityLowerBound G
  unfold Elementary
  omega

private theorem helper_continuation_170.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] (G :
        LooplessMultigraph V E) (k : ℕ), ChromaticIndex G = k + (1 : ℕ) →
    ∀ (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V), IsProperEdgeColoring G phi →
        IsOneEdgeUncolored phi e0 → (
    ∀ v ∈ G.ends e0, v ∈ X) → ColoredVertexSetElementary G phi X → ColoredVertexSetStronglyClosed
        G phi X → (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) →
    ∀ (x : V) (_ : Fin k),
    let Y : Finset V := X.erase x; X.card = Y.card + (1 : ℕ) → Odd X.card → (3 : ℕ) ≤ X.card →
    let allVC : Finset (V × Fin k) := X.product Finset.univ;
    let missingPairs : Finset (V × Fin k) := ({p ∈ allVC | p.2 ∈ MissingColors G phi p.1} : Finset
        (V × Fin k));
    let presentPairs : Finset (V × Fin k) := ({p ∈ allVC | p.2 ∈ PresentColors G phi p.1} : Finset
        (V × Fin k));
    let _ : Finset (Fin k) := ({c : Fin k |
    ∃ v ∈ X, c ∈ MissingColors G phi v} : Finset (Fin k)); missingPairs ∪ presentPairs = allVC →
        Disjoint missingPairs presentPairs → Elementary G := by
  classical
  intro V E _ _ _ G k hindex e0 phi X hproper hone hends helementary hstrong endpoint_card x
      alpha Y hXcard hXodd hXthree allVC missingPairs presentPairs missingUnion allVC_split
      allVC_disjoint
  have allVC_card : allVC.card = X.card * k := by
    simp [allVC, Finset.card_product]
  have missingPairs_le : missingPairs.card ≤ missingUnion.card := by
    exact @helper_missingPairs_le_67 (@V) (@E) inferInstance inferInstance (@G) (@k) (@phi) (@X)
        (@helementary)
  have missing_witness : ∀ c, c ∈ missingUnion →
      ∃ v, v ∈ X ∧ c ∈ MissingColors G phi v := by
    intro c hc
    simpa [missingUnion] using hc
  let missingVertex (c : Fin k) : V :=
    if hc : c ∈ missingUnion then Classical.choose (missing_witness c hc) else x
  have missingVertex_spec : ∀ c, c ∈ missingUnion →
      missingVertex c ∈ X ∧ c ∈ MissingColors G phi (missingVertex c) := by
    intro c hc
    simp only [missingVertex, dite_eq_left hc]
    exact Classical.choose_spec (missing_witness c hc)
  have missingUnion_le : missingUnion.card ≤ missingPairs.card := by
    apply Finset.card_le_card_of_injOn (fun c : Fin k => (missingVertex c, c))
    · intro c hc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨(missingVertex_spec c hc).1, Finset.mem_univ _⟩,
        (missingVertex_spec c hc).2⟩
    · intro a ha b hb hab
      exact congrArg Prod.snd hab
  have missingPairs_card : missingPairs.card = missingUnion.card :=
    Nat.le_antisymm missingPairs_le missingUnion_le
  have pairs_card_identity : missingUnion.card + presentPairs.card = X.card * k := by
    rw [← missingPairs_card, ← Finset.card_union_of_disjoint allVC_disjoint,
      allVC_split, allVC_card]
  let incidences := ((Finset.univ : Finset E).product X).filter
    (fun p => Incident G p.2 p.1 ∧ ∃ c, phi p.1 = some c)
  have present_witness : ∀ p, p ∈ presentPairs →
      ∃ e, Incident G p.1 e ∧ phi e = some p.2 := by
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    simpa [PresentColors] using hc
  let presentEdge (p : V × Fin k) : E :=
    if hp : p ∈ presentPairs then Classical.choose (present_witness p hp) else e0
  have presentEdge_spec : ∀ p, p ∈ presentPairs →
      Incident G p.1 (presentEdge p) ∧ phi (presentEdge p) = some p.2 := by
    intro p hp
    simp only [presentEdge, dite_eq_left hp]
    exact Classical.choose_spec (present_witness p hp)
  have presentPairs_le_inc : presentPairs.card ≤ incidences.card := by
    exact @helper_presentPairs_le_inc_363 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@X) (@present_witness) (@presentEdge_spec)
  have incidence_witness : ∀ p, p ∈ incidences → ∃ c, phi p.1 = some c := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.2
  let incidenceColor (p : E × V) : Fin k :=
    if hp : p ∈ incidences then Classical.choose (incidence_witness p hp) else alpha
  have incidenceColor_spec : ∀ p, p ∈ incidences →
      phi p.1 = some (incidenceColor p) := by
    intro p hp
    simp only [incidenceColor, dite_eq_left hp]
    exact Classical.choose_spec (incidence_witness p hp)
  have incidences_le_present : incidences.card ≤ presentPairs.card := by
    exact @helper_incidences_le_present_158 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@phi) (@X) (@hproper) (@alpha) (@incidence_witness) (@incidenceColor_spec)
  have presentPairs_card : presentPairs.card = incidences.card :=
    Nat.le_antisymm presentPairs_le_inc incidences_le_present
  have incidence_color_identity : missingUnion.card + incidences.card = X.card * k := by
    simpa [presentPairs_card] using pairs_card_identity
  have e0_internal : e0 ∈ InternalEdges G X := by
    simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hends
  have boundary_ne_e0 : ∀ e, e ∈ BoundaryEdges G X → e ≠ e0 := by
    intro e he heq
    subst e
    obtain ⟨u, huX, v, hvX, huv⟩ := by
      simpa [BoundaryEdges] using he
    exact hvX (hends v (by rw [huv]; simp))
  let internalColored := (InternalEdges G X).erase e0
  let boundary := BoundaryEdges G X
  let internalInc := incidences.filter (fun p => p.1 ∈ internalColored)
  let boundaryInc := incidences.filter (fun p => p.1 ∈ boundary)
  have edge_classification : ∀ {e v}, v ∈ X → Incident G v e →
      e ∈ InternalEdges G X ∨ e ∈ BoundaryEdges G X := by
    exact @helper_edge_classification_411 (@V) (@E) inferInstance inferInstance (@G) (@X)
  have internal_boundary_disjoint :
      Disjoint (InternalEdges G X) (BoundaryEdges G X) := by
    rw [Finset.disjoint_left]
    intro e hi hb
    obtain ⟨u, huX, v, hvX, huv⟩ := by
      simpa [BoundaryEdges] using hb
    unfold InternalEdges at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hvX (hi v (by change v ∈ G.ends e; rw [huv]; simp))
  have incidences_split : internalInc ∪ boundaryInc = incidences := by
    exact @helper_incidences_split_223 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@X) (@hone) (@edge_classification)
  have incidences_disjoint : Disjoint internalInc boundaryInc := by
    rw [Finset.disjoint_left]
    intro p hi hb
    have hei : p.1 ∈ InternalEdges G X :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp hi).2).2
    have heb : p.1 ∈ BoundaryEdges G X := (Finset.mem_filter.mp hb).2
    exact (Finset.disjoint_left.mp internal_boundary_disjoint) hei heb
  have incidence_edge_identity :
      incidences.card = internalInc.card + boundaryInc.card := by
    rw [← Finset.card_union_of_disjoint incidences_disjoint, incidences_split]
  let edgeInc (s : Finset E) := (s.product X).filter
    (fun p => Incident G p.2 p.1)
  exact @helper_continuation_596 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@hindex) (@e0) (@phi) (@X) (@hone) (@hstrong) (@endpoint_card) (@x) (@alpha) (@hXcard)
      (@hXodd) (@hXthree) (@missingPairs_le) (@missingUnion_le) (@pairs_card_identity)
      (@presentPairs_le_inc) (@incidences_le_present) (@incidence_color_identity) (@e0_internal)
      (@boundary_ne_e0) (@incidence_edge_identity)
private theorem helper_continuation_156.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] (G :
        LooplessMultigraph V E) (k : ℕ), ChromaticIndex G = k + (1 : ℕ) →
    ∀ (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V), IsProperEdgeColoring G phi →
        IsOneEdgeUncolored phi e0 → (
    ∀ v ∈ G.ends e0, v ∈ X) → ColoredVertexSetElementary G phi X → ColoredVertexSetStronglyClosed
        G phi X → (
    ∀ (e : E), (G.ends e).toFinset.card = (2 : ℕ)) →
    ∀ (x y : V), x ≠ y → (G.ends e0).toFinset = { x, y } → Incident G x e0 → Incident G y e0 → x ∈
        X → y ∈ X →
    ∀ alpha ∈ MissingColors G phi x,
    let Y : Finset V := X.erase x;
    let alphaEdges : Finset E := {e : E | phi e = some alpha}; (
    ∀ v ∈ Y, alpha ∈ PresentColors G phi v) → (
    ∀ v ∈ Y,
    ∃! e : E, e ∈ alphaEdges ∧ Incident G v e) → (
    ∀ e ∈ alphaEdges, ¬Incident G x e) → (
    ∀ e ∈ alphaEdges,
    ∀ v ∈ X, Incident G v e →
    ∀ (z : V), Incident G z e → z ∈ X) → Elementary G := by
  classical
  intro V E _ _ _ G k hindex e0 phi X hproper hone hends helementary hstrong endpoint_card x y
      hxy hxyends hxend hyend hxX hyX alpha halpha Y alphaEdges y_present alpha_inc no_alpha_at_x
      alpha_internal
  let goodAlpha := alphaEdges.filter (fun e => ∀ v, Incident G v e → v ∈ X)
  have goodAlpha_spec : ∀ e, e ∈ goodAlpha ↔
      e ∈ alphaEdges ∧ ∀ v, Incident G v e → v ∈ X := by
    intro e
    simp [goodAlpha]
  have goodAlpha_disjoint : ∀ {e}, e ∈ goodAlpha → ∀ {f}, f ∈ goodAlpha →
      e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro v hev hvf
    have hce := (goodAlpha_spec e).mp he |>.1
    have hcf := (goodAlpha_spec f).mp hf |>.1
    exact (hproper hef ⟨v, Sym2.mem_toFinset.mp hev, Sym2.mem_toFinset.mp hvf⟩
      (Finset.mem_filter.mp hce).2) (Finset.mem_filter.mp hcf).2
  have goodAlpha_union_card :
      (goodAlpha.biUnion fun edge => (G.ends edge).toFinset).card = 2 * goodAlpha.card := by
    rw [Finset.card_biUnion @goodAlpha_disjoint]
    exact (Finset.sum_const_nat (fun edge _ => endpoint_card edge)).trans (Nat.mul_comm _ _)
  have goodAlpha_union_eq : goodAlpha.biUnion (fun e => (G.ends e).toFinset) = Y := by
    ext v
    constructor
    · intro hv
      obtain ⟨e, he, hev⟩ := Finset.mem_biUnion.mp hv
      have hvX := (goodAlpha_spec e |>.mp he).2 v (Sym2.mem_toFinset.mp hev)
      have hvx : v ≠ x := by
        intro hvx
        exact no_alpha_at_x e (goodAlpha_spec e |>.mp he).1
          (hvx ▸ Sym2.mem_toFinset.mp hev)
      exact Finset.mem_erase.mpr ⟨hvx, hvX⟩
    · intro hv
      obtain ⟨e, he, hve⟩ := alpha_inc v hv
      have hg : e ∈ goodAlpha := goodAlpha_spec e |>.mpr ⟨he.1,
        alpha_internal e he.1 v (Finset.mem_erase.mp hv).2 he.2⟩
      exact Finset.mem_biUnion.mpr ⟨e, hg, Sym2.mem_toFinset.mpr he.2⟩
  have hYeven : Even Y.card := by
    refine ⟨goodAlpha.card, ?_⟩
    rw [← goodAlpha_union_eq, goodAlpha_union_card]
    omega
  have hXcard : X.card = Y.card + 1 := by
    have hh := Finset.card_erase_of_mem hxX
    simp [Y] at hh ⊢
    have hpos : 0 < X.card := Finset.card_pos.mpr ⟨x, hxX⟩
    omega
  have hXodd : Odd X.card := by
    rw [hXcard]
    rcases hYeven with ⟨q, hq⟩
    exact ⟨q, by omega⟩
  have hXthree : 3 ≤ X.card := by
    have htwo : 2 ≤ X.card := by
      have hsub : ({x, y} : Finset V) ⊆ X := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hxX
        · exact hyX
      have hc := Finset.card_le_card hsub
      simpa [hxy] using hc
    rcases hXodd with ⟨q, hq⟩
    omega
  let allVC : Finset (V × Fin k) := X.product Finset.univ
  let missingPairs := allVC.filter (fun p => p.2 ∈ MissingColors G phi p.1)
  let presentPairs := allVC.filter (fun p => p.2 ∈ PresentColors G phi p.1)
  let missingUnion := (Finset.univ : Finset (Fin k)).filter
    (fun c => ∃ v ∈ X, c ∈ MissingColors G phi v)
  have allVC_split : missingPairs ∪ presentPairs = allVC := by
    ext p
    simp only [missingPairs, presentPairs, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      by_cases hc : p.2 ∈ PresentColors G phi p.1
      · exact Or.inr ⟨hp, hc⟩
      · exact Or.inl ⟨hp, by simp [MissingColors, hc]⟩
  have allVC_disjoint : Disjoint missingPairs presentPairs := by
    rw [Finset.disjoint_left]
    intro p hm hp
    have hm' := (Finset.mem_filter.mp hm).2
    have hp' := (Finset.mem_filter.mp hp).2
    exact (Finset.mem_sdiff.mp hm').2 hp'
  exact @helper_continuation_170 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@hindex) (@e0) (@phi) (@X) (@hproper) (@hone) (@hends) (@helementary) (@hstrong)
      (@endpoint_card) (@x) (@alpha) (@hXcard) (@hXodd) (@hXthree) (@allVC_split) (@allVC_disjoint)
theorem StronglyClosedWitnessElementary {V E : Type*} [Fintype V] [Fintype E]
      (G : LooplessMultigraph V E) (k : ℕ)
    (hindex : ChromaticIndex G = k + 1)
    (hdegree : MaximumDegree G + 1 ≤ k)
    (e0 : E) (phi : PartialEdgeColoring E k) (X : Finset V)
    (hproper : IsProperEdgeColoring G phi)
    (hone : IsOneEdgeUncolored phi e0)
    (hends : ∀ v, v ∈ G.ends e0 → v ∈ X)
    (helementary : ColoredVertexSetElementary G phi X)
    (hstrong : ColoredVertexSetStronglyClosed G phi X) :
    Elementary G := by
  classical
  have endpoint_card : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd) (Sym2.diag_diagElem hd).symm
  obtain ⟨x, y, hxy, hxyends⟩ := Finset.card_eq_two.mp (endpoint_card e0)
  have hxend : Incident G x e0 := by
    change x ∈ G.ends e0
    apply Sym2.mem_toFinset.mp
    rw [hxyends]
    simp
  have hyend : Incident G y e0 := by
    change y ∈ G.ends e0
    apply Sym2.mem_toFinset.mp
    rw [hxyends]
    simp
  have hxX : x ∈ X := hends x hxend
  have hyX : y ∈ X := hends y hyend
  have hdeg : ∀ v : V, Degree G v ≤ MaximumDegree G := by
    intro v
    unfold MaximumDegree
    exact Finset.le_max' _ _ (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_image.mpr ⟨v, by simp⟩)))
  have missing_exists (v : V) : (MissingColors G phi v).Nonempty := by
    apply MissingColors.nonempty_of_degree_lt G phi v
    have degree := hdeg v
    omega
  obtain ⟨alpha, halpha⟩ := missing_exists x
  let Y := X.erase x
  let alphaEdges := (Finset.univ : Finset E).filter (fun e => phi e = some alpha)
  have y_present : ∀ v, v ∈ Y → alpha ∈ PresentColors G phi v := by
    intro v hv
    have hvX : v ∈ X := (Finset.mem_erase.mp hv).2
    have hvne : v ≠ x := (Finset.mem_erase.mp hv).1
    have hdis := helementary hxX hvX hvne.symm
    have : alpha ∉ MissingColors G phi v := by
      intro hm
      exact (Finset.disjoint_left.mp hdis) halpha hm
    simpa [MissingColors] using this
  have alpha_inc : ∀ v, v ∈ Y → ∃! e, e ∈ alphaEdges ∧ Incident G v e := by
    intro v hv
    obtain ⟨e, he, hve⟩ := by simpa [PresentColors] using y_present v hv
    refine ⟨e, ?_, ?_⟩
    · exact ⟨by simpa [alphaEdges] using hve, he⟩
    · intro f hf
      by_contra hef
      exact (hproper (fun h => hef h.symm) ⟨v, he, hf.2⟩ hve)
        (Finset.mem_filter.mp hf.1).2
  have no_alpha_at_x : ∀ e, e ∈ alphaEdges → ¬ Incident G x e := by
    intro e he hxe
    have hp : alpha ∈ PresentColors G phi x := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, hxe, (Finset.mem_filter.mp he).2⟩
    exact (Finset.mem_sdiff.mp halpha).2 hp
  have alpha_internal : ∀ e, e ∈ alphaEdges → ∀ v, v ∈ X → Incident G v e →
      ∀ z, Incident G z e → z ∈ X := by
    intro e he v hvX hve z hze
    by_contra hz
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hze
    have hzw : G.ends e = s(z, w) := hw
    have hvpair : v = z ∨ v = w := by
      have : v ∈ s(z, w) := by rw [← hzw]; exact hve
      simpa using this
    have hwX : w ∈ X := by
      rcases hvpair with hvz | hvw
      · exact False.elim (hz (hvz ▸ hvX))
      · exact hvw ▸ hvX
    have hb : e ∈ BoundaryEdges G X := by
      simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨w, hwX, z, hz, hzw.trans Sym2.eq_swap⟩
    exact (hstrong.1 hb hxX (Finset.mem_filter.mp he).2) halpha
  exact @helper_continuation_156 V E inferInstance inferInstance inferInstance G k
      hindex e0 phi X hproper hone hends helementary hstrong endpoint_card x y hxy hxyends hxend
      hyend hxX hyX alpha halpha y_present alpha_inc no_alpha_at_x alpha_internal
end GoldbergSeymour

end
