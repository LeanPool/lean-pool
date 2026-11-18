/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeControlledInterchange
public import LeanPool.GoldbergSeymour.TashTreeFourUnusedColors
public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TreeFreeColors
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TwoColorMissingVertexNeighbors

/-!
# Tash Tree Early Beta Normalization

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hnone_387.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [ Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hbefore : TashTreePathIndex G T < T.length), (¬
    ∃ (alpha : Fin k) (i : Fin (T.length + (1 : ℕ))), TashTreePathIndex G T ≤ (↑i : ℕ) ∧ (↑i : ℕ)
        < T.length ∧ alpha ∈ MissingColors G phi (T.vertex i) ∧ alpha ∈ MissingColors G phi
        (T.vertex (Fin.last T.length))) →
    ∀ (beta : Fin k) (j : Fin (T.length + (1 : ℕ))), T.vertex j ∈ TreeSequenceVertexSet T →
    ∀ (i : Fin (T.length + (1 : ℕ))) (hiBefore : (↑i : ℕ) < TashTreePathIndex G T) (hiearly : ¬(↑i
        : ℕ) + (2 : ℕ) ≤ TashTreePathIndex G T) (hiEq : (↑i : ℕ) = TashTreePathIndex G T - (1 :
        ℕ)),
    let rnew : Fin T.length := (⟨TashTreePathIndex G T - (2 : ℕ), Decidable.byContradiction fun (a
        : ¬TashTreePathIndex G T - (2 : ℕ) < T.length) =>
    by omega
    ⟩ : Fin T.length);
    let d : Fin k := (phi (T.edge rnew)).getD beta;
    ∀ (alpha : Fin k), alpha ≠ beta → alpha ≠ d →
    ∀ (m : Fin (T.length + (1 : ℕ))), (↑m : ℕ) ≤ TashTreePathIndex G T - (2 : ℕ) →
    let pen : Fin (T.length + (1 : ℕ)) := (⟨TashTreePathIndex G T - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (1 : ℕ) < T.length + (1 : ℕ))
        =>
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let B : TreeSequence G e0 := TreeSequencePrefix T (TashTreePathIndex G T - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ TashTreePathIndex G T - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (1 : ℕ) ≤ T.length) =>
    by omega
    ); B.length = TashTreePathIndex G T - (1 : ℕ) →
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl
        (T.vertex pen));
    let C : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen));
    ∀ (a b : V ⊕ E), (
    ∀ {x : V ⊕ E}, x ∈ C → ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x).Subsingleton
        → x = a ∨ x = b) → (
    ∀ {x : V ⊕ E}, x = a ∨ x = b → x = Sum.inl (T.vertex m) ∨ x = Sum.inl (T.vertex pen)) →
        Sum.inl (T.vertex (Fin.last T.length)) ∉ C → ((
    ∀ (v : V), Sum.inl v ∉ TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen)) →
        MissingColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex pen))) v =
        MissingColors G phi v) ∧ (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen)) → alpha ∈
        MissingColors G phi v → beta ∈ MissingColors G (TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex pen))) v) ∧ (
    ∀ (v : V), Sum.inl v ∈ TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen)) → beta ∈
        MissingColors G phi v → alpha ∈ MissingColors G (TwoColorComponentSwap G phi alpha beta
        (Sum.inl (T.vertex pen))) v) ∧
    ∀ (v : V) (c : Fin k), c ≠ alpha → c ≠ beta → (c ∈ MissingColors G (TwoColorComponentSwap G
        phi alpha beta (Sum.inl (T.vertex pen))) v ↔ c ∈ MissingColors G phi v)) →
        TwoColorIncidenceGraph G phi' alpha beta = TwoColorIncidenceGraph G phi alpha beta →
        IsProperEdgeColoring G phi' → ¬
    ∃ (c : Fin k) (s : Fin (T.length + (1 : ℕ))), TashTreePathIndex G T ≤ (↑s : ℕ) ∧ (↑s : ℕ) <
        T.length ∧ c ∈ MissingColors G phi' (T.vertex s) ∧ c ∈ MissingColors G phi' (T.vertex
        (Fin.last T.length)) := by
  classical
  intro V E _ _ G k e0 phi T hq hbefore hnone beta j hv i hiBefore hiearly hiEq rnew d alpha hab had
      m hm pen B hBlength phi' C a b endpoint_of_subsingleton endpoint_is_m_or_pen hlastOutside
      hbehavior hgraph hproper'
  let _ := Fintype.ofFinite V
  rintro ⟨c, s, hqs, hsLength, hcs, hcLast⟩
  have hcLastOld : c ∈
      MissingColors G phi (T.vertex (Fin.last T.length)) := by
    rw [← hbehavior.1 _ hlastOutside]
    exact hcLast
  by_cases hsOutside : Sum.inl (T.vertex s) ∉ C
  · have hcsOld : c ∈ MissingColors G phi (T.vertex s) := by
      rw [← hbehavior.1 _ hsOutside]
      exact hcs
    exact hnone ⟨c, s, hqs, hsLength, hcsOld, hcLastOld⟩
  · have hsComponent : Sum.inl (T.vertex s) ∈ C :=
      not_not.mp hsOutside
    by_cases hca : c = alpha
    · subst c
      have hsSubNew : Set.Subsingleton
          ((TwoColorIncidenceGraph G phi' alpha beta).neighborSet
            (Sum.inl (T.vertex s))) := by
        exact TwoColorMissingVertexNeighborsSubsingleton G phi' hproper' alpha beta
          (T.vertex s) (Or.inl hcs)
      have hsSubOld : Set.Subsingleton
          ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
            (Sum.inl (T.vertex s))) := by
        rw [← hgraph]
        exact hsSubNew
      rcases endpoint_is_m_or_pen
          (endpoint_of_subsingleton hsComponent hsSubOld) with hsM | hsPen
      · have hv : T.vertex s = T.vertex m := by simpa using hsM
        have hindices := congrArg Fin.val (T.vertex_injective hv)
        omega
      · have hv : T.vertex s = T.vertex pen := by simpa using hsPen
        have hindices := congrArg Fin.val (T.vertex_injective hv)
        dsimp [pen] at hindices
        omega
    · by_cases hcb : c = beta
      · subst c
        have hsSubNew : Set.Subsingleton
            ((TwoColorIncidenceGraph G phi' alpha beta).neighborSet
              (Sum.inl (T.vertex s))) := by
          exact TwoColorMissingVertexNeighborsSubsingleton G phi' hproper' alpha beta
            (T.vertex s) (Or.inr hcs)
        have hsSubOld : Set.Subsingleton
            ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
              (Sum.inl (T.vertex s))) := by
          rw [← hgraph]
          exact hsSubNew
        rcases endpoint_is_m_or_pen
            (endpoint_of_subsingleton hsComponent hsSubOld) with hsM | hsPen
        · have hv : T.vertex s = T.vertex m := by simpa using hsM
          have hindices := congrArg Fin.val (T.vertex_injective hv)
          omega
        · have hv : T.vertex s = T.vertex pen := by simpa using hsPen
          have hindices := congrArg Fin.val (T.vertex_injective hv)
          dsimp [pen] at hindices
          omega
      · have hcsOld : c ∈ MissingColors G phi (T.vertex s) :=
          (hbehavior.2.2.2 (T.vertex s) c hca hcb).mp hcs
        exact hnone ⟨c, s, hqs, hsLength, hcsOld, hcLastOld⟩

private theorem helper_halphaUnused_358.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hbefore : TashTreePathIndex G T < T.length) (beta : Fin k) (i :
        Fin (T.length + (1 : ℕ))) (hiBefore : (↑i : ℕ) < TashTreePathIndex G T) (hiearly : ¬(↑i :
        ℕ) + (2 : ℕ) ≤ TashTreePathIndex G T) (hiEq : (↑i : ℕ) = TashTreePathIndex G T - (1 : ℕ)),
    let A : TreeSequence G e0 := TreeSequencePrefix T (TashTreePathIndex G T - (2 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ TashTreePathIndex G T - (2 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (2 : ℕ) ≤ T.length) =>
    by omega
    ); A.length = TashTreePathIndex G T - (2 : ℕ) →
    let rnew : Fin T.length := (⟨TashTreePathIndex G T - (2 : ℕ), Decidable.byContradiction fun (a
        : ¬TashTreePathIndex G T - (2 : ℕ) < T.length) =>
    by omega
    ⟩ : Fin T.length);
    let d : Fin k := (phi (T.edge rnew)).getD beta;
    ∀ alpha ∈ TreeFreeColors phi A, alpha ≠ beta → alpha ≠ d →
    ∀ (_ : Fin (T.length + (1 : ℕ))),
    let pen : Fin (T.length + (1 : ℕ)) := (⟨TashTreePathIndex G T - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (1 : ℕ) < T.length + (1 : ℕ))
        =>
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); TreeColorUnusedThrough phi T alpha pen := by
  classical
  intro V E _ _ G k e0 phi T hq hbefore beta i hiBefore hiearly hiEq A hAlength rnew d alpha
      halphaFree hab had m pen r hrPositive hrBefore hrAlpha
  let _ := Fintype.ofFinite V
  by_cases hrnew : r.val = TashTreePathIndex G T - 2
  · have hre : r = rnew := by
      apply Fin.ext
      simpa [rnew] using hrnew
    rw [hre] at hrAlpha
    apply had
    simp [d, hrAlpha]
  · have hrlt : r.val < TashTreePathIndex G T - 2 := by
      dsimp [pen] at hrBefore
      omega
    have hnotUsed : alpha ∉ TreeUsedColors phi A :=
      (Finset.mem_sdiff.mp (by simpa [TreeFreeColors] using halphaFree)).2
    apply hnotUsed
    rw [TreeUsedColors]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨⟨r.val, by rw [hAlength]; omega⟩,
      hrPositive, ?_⟩⟩
    change phi (T.edge r) = some alpha
    exact hrAlpha

private theorem helper_hbetaUnused_395.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hbefore : TashTreePathIndex G T < T.length), TashkinovTree G e0
        phi T →
    ∀ (beta : Fin k) (j : Fin (T.length + (1 : ℕ))), T.vertex j ∈ TreeSequenceVertexSet T →
    ∀ (i : Fin (T.length + (1 : ℕ))) (hiBefore : (↑i : ℕ) < TashTreePathIndex G T) (hiearly : ¬(↑i
        : ℕ) + (2 : ℕ) ≤ TashTreePathIndex G T) (hiEq : (↑i : ℕ) = TashTreePathIndex G T - (1 :
        ℕ)) (_ : Fin (T.length + (1 : ℕ))),
    let pen : Fin (T.length + (1 : ℕ)) := (⟨TashTreePathIndex G T - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (1 : ℕ) < T.length + (1 : ℕ))
        =>
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); beta ∈ MissingColors G phi (T.vertex pen) →
    let B : TreeSequence G e0 := TreeSequencePrefix T (TashTreePathIndex G T - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ TashTreePathIndex G T - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (1 : ℕ) ≤ T.length) =>
    by omega
    ); B.length = TashTreePathIndex G T - (1 : ℕ) → ColoredVertexSetElementary G phi
        (TreeSequenceVertexSet B) → T.vertex pen ∈ TreeSequenceVertexSet B →
        TreeColorUnusedThrough phi T beta pen := by
  classical
  intro V E _ _ G k e0 phi T hq hbefore hTash beta j hv i hiBefore hiearly hiEq m pen hbetaPen B
      hBlength hBelem hpenB r hrPositive hrBefore hrBeta
  let _ := Fintype.ofFinite V
  rcases hTash r hrPositive with ⟨w, c, hc, hw⟩
  have hcbeta : c = beta := Option.some.inj (hc.symm.trans hrBeta)
  subst c
  let wt : Fin (T.length + 1) :=
    Fin.castLT w (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt))
  have hwB : T.vertex wt ∈ TreeSequenceVertexSet B := by
    rw [TreeSequenceVertexSet]
    let wp : Fin (B.length + 1) := ⟨w.val, by
      rw [hBlength]
      dsimp [pen] at hrBefore
      omega⟩
    refine Finset.mem_image.mpr ⟨wp, Finset.mem_univ _, ?_⟩
    apply congrArg T.vertex
    apply Fin.ext
    rfl
  have hwne : T.vertex wt ≠ T.vertex pen := by
    intro hv
    have hindices := congrArg Fin.val (T.vertex_injective hv)
    dsimp [wt, pen] at hindices
    dsimp [pen] at hrBefore
    omega
  have hd := hBelem hwB hpenB hwne
  exact (Finset.disjoint_left.mp hd) hw hbetaPen

private theorem helper_hgraph_526.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) (k : ℕ) (e0
        : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (_ : (2 : ℕ) <
        TashTreePathIndex G T) (hbefore : TashTreePathIndex G T < T.length) (beta : Fin k) (i :
        Fin (T.length + (1 : ℕ))) (hiBefore : (↑i : ℕ) < TashTreePathIndex G T) (hiearly : ¬(↑i :
        ℕ) + (2 : ℕ) ≤ TashTreePathIndex G T) (hiEq : (↑i : ℕ) = TashTreePathIndex G T - (1 : ℕ))
        (alpha : Fin k), alpha ≠ beta →
    ∀ (_ : Fin (T.length + (1 : ℕ))),
    let pen : Fin (T.length + (1 : ℕ)) := (⟨TashTreePathIndex G T - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (1 : ℕ) < T.length + (1 : ℕ))
        =>
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi alpha beta (Sum.inl
        (T.vertex pen));
    let _ : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen));
        TwoColorIncidenceGraph G phi' alpha beta = TwoColorIncidenceGraph G phi alpha beta := by
  classical
  intro V E _ _ G k e0 phi T hq hbefore beta i hiBefore hiearly hiEq alpha hab m pen phi' C
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  apply SimpleGraph.ext
  funext x y
  cases x with
  | inl v =>
      cases y with
      | inl w => simp [TwoColorIncidenceGraph]
      | inr e =>
          simp only [TwoColorIncidenceGraph]
          by_cases he : Sum.inr e ∈ C
          · by_cases ha : phi e = some alpha
            · simp [phi', TwoColorComponentSwap, C, he, ha, hab]
            · by_cases hb : phi e = some beta
              · simp [phi', TwoColorComponentSwap, C, he, hb, hab]
              · simp [phi', TwoColorComponentSwap, C, he, ha, hb]
          · simp [phi', TwoColorComponentSwap, C, he]
  | inr e =>
      cases y with
      | inl v =>
          simp only [TwoColorIncidenceGraph]
          by_cases he : Sum.inr e ∈ C
          · by_cases ha : phi e = some alpha
            · simp [phi', TwoColorComponentSwap, C, he, ha, hab]
            · by_cases hb : phi e = some beta
              · simp [phi', TwoColorComponentSwap, C, he, hb, hab]
              · simp [phi', TwoColorComponentSwap, C, he, ha, hb]
          · simp [phi', TwoColorComponentSwap, C, he]
      | inr f => simp [TwoColorIncidenceGraph]

private theorem helper_hbetaLast_454.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hbefore : TashTreePathIndex G T < T.length),
    let P : TreeSequence G e0 := TreeSequencePrefix T (T.length - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ T.length - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬T.length - (1 : ℕ) ≤ T.length) =>
    by omega
    ); P.length = T.length - (1 : ℕ) → ColoredVertexSetElementary G phi (TreeSequenceVertexSet P)
        →
    ∀ (beta : Fin k) (i : Fin (T.length + (1 : ℕ))), beta ∈ MissingColors G phi (T.vertex i) →
    ∀ (j : Fin (T.length + (1 : ℕ))), beta ∈ MissingColors G phi (T.vertex j) → T.vertex i ≠
        T.vertex j → beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)) := by
  classical
  intro V E _ _ G k e0 phi T hq hbefore P hPlength hPelem beta i hbu j hbv huv
  let _ := Fintype.ofFinite V
  have hil : i.val ≤ T.length := Nat.le_of_lt_succ i.isLt
  have hjl : j.val ≤ T.length := Nat.le_of_lt_succ j.isLt
  by_cases hi : i.val = T.length
  · have hi' : i = Fin.last T.length := Fin.ext (by simpa using hi)
    simpa [hi'] using hbu
  · by_cases hj : j.val = T.length
    · have hj' : j = Fin.last T.length := Fin.ext (by simpa using hj)
      simpa [hj'] using hbv
    · exfalso
      have hiP : T.vertex i ∈ TreeSequenceVertexSet P := by
        rw [TreeSequenceVertexSet]
        let ip : Fin (P.length + 1) := ⟨i.val, by rw [hPlength]; omega⟩
        exact Finset.mem_image.mpr ⟨ip, Finset.mem_univ _, rfl⟩
      have hjP : T.vertex j ∈ TreeSequenceVertexSet P := by
        rw [TreeSequenceVertexSet]
        let jp : Fin (P.length + 1) := ⟨j.val, by rw [hPlength]; omega⟩
        exact Finset.mem_image.mpr ⟨jp, Finset.mem_univ _, rfl⟩
      have hd := hPelem hiP hjP huv
      exact (Finset.disjoint_left.mp hd) hbu hbv

private theorem helper_halphaMissing_519.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Finite V] [ Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hbefore : TashTreePathIndex G T < T.length) (beta : Fin k) (i :
        Fin (T.length + (1 : ℕ))) (hiBefore : (↑i : ℕ) < TashTreePathIndex G T) (hiearly : ¬(↑i :
        ℕ) + (2 : ℕ) ≤ TashTreePathIndex G T) (hiEq : (↑i : ℕ) = TashTreePathIndex G T - (1 : ℕ)),
    let A : TreeSequence G e0 := TreeSequencePrefix T (TashTreePathIndex G T - (2 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ TashTreePathIndex G T - (2 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (2 : ℕ) ≤ T.length) => (
    by first  | omega
    )); A.length = TashTreePathIndex G T - (2 : ℕ) →
    let rnew : Fin T.length := (⟨TashTreePathIndex G T - (2 : ℕ), Decidable.byContradiction fun (a
        : ¬TashTreePathIndex G T - (2 : ℕ) < T.length) =>
    by omega
    ⟩ : Fin T.length);
    let d : Fin k := (phi (T.edge rnew)).getD beta;
    ∀ alpha ∈ TreeFreeColors phi A, alpha ≠ beta → alpha ≠ d →
    ∃ (m : Fin (T.length + (1 : ℕ))), (↑m : ℕ) ≤ TashTreePathIndex G T - (2 : ℕ) ∧ alpha ∈
        MissingColors G phi (T.vertex m) := by
  classical
  intro V E _ _ G k e0 phi T hq hbefore beta i hiBefore hiearly hiEq A hAlength rnew d alpha
      halphaFree hab had
  let _ := Fintype.ofFinite V
  have hm : alpha ∈ TreeMissingColors phi A :=
    (Finset.mem_sdiff.mp (by simpa [TreeFreeColors] using halphaFree)).1
  rw [TreeMissingColors] at hm
  rcases Finset.mem_biUnion.mp hm with ⟨x, hx, hxm⟩
  rw [TreeSequenceVertexSet] at hx
  rcases Finset.mem_image.mp hx with ⟨m, -, rfl⟩
  let mt : Fin (T.length + 1) :=
    Fin.castLE (by rw [hAlength]; omega) m
  refine ⟨mt, ?_, ?_⟩
  · dsimp [mt]
    rw [hAlength] at m
    omega
  · simpa [mt, A, TreeSequencePrefix] using hxm

private theorem helper_hlastOutside_622.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Finite E] (G : LooplessMultigraph V E) (k : ℕ) (e0
        : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (hq : (2 : ℕ) <
        TashTreePathIndex G T) (hbefore : TashTreePathIndex G T < T.length) (beta : Fin k) (j :
        Fin (T.length + (1 : ℕ))), T.vertex j ∈ TreeSequenceVertexSet T →
    ∀ (i : Fin (T.length + (1 : ℕ))) (hiBefore : (↑i : ℕ) < TashTreePathIndex G T) (hiearly : ¬(↑i
        : ℕ) + (2 : ℕ) ≤ TashTreePathIndex G T) (hiEq : (↑i : ℕ) = TashTreePathIndex G T - (1 :
        ℕ)) (alpha : Fin k) (m : Fin (T.length + (1 : ℕ))),
    let pen : Fin (T.length + (1 : ℕ)) := (⟨TashTreePathIndex G T - (1 : ℕ),
        Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (1 : ℕ) < T.length + (1 : ℕ))
        =>
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let B : TreeSequence G e0 := TreeSequencePrefix T (TashTreePathIndex G T - (1 : ℕ))
        (Decidable.byContradiction fun (a : ¬(1 : ℕ) ≤ TashTreePathIndex G T - (1 : ℕ)) =>
    by omega
    ) (Decidable.byContradiction fun (a : ¬TashTreePathIndex G T - (1 : ℕ) ≤ T.length) =>
    by omega
    ); B.length = TashTreePathIndex G T - (1 : ℕ) → (↑m : ℕ) < (↑pen : ℕ) → (↑pen : ℕ) < T.length
        →
    let C : Set (V ⊕ E) := TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen));
    ∀ (a b : V ⊕ E), (
    ∀ {x : V ⊕ E}, x ∈ C → ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x).Subsingleton
        → x = a ∨ x = b) → (
    ∀ {x : V ⊕ E}, x = a ∨ x = b → x = Sum.inl (T.vertex m) ∨ x = Sum.inl (T.vertex pen)) →
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet (Sum.inl (T.vertex (Fin.last
        T.length)))).Subsingleton → Sum.inl (T.vertex (Fin.last T.length)) ∉ C := by
  classical
  intro V E _ _ G k e0 phi T hq hbefore beta j hv i hiBefore hiearly hiEq alpha m pen B hBlength
      hmpen hpenLength C a b endpoint_of_subsingleton endpoint_is_m_or_pen hlastSub hlastComponent
  let := Fintype.ofFinite V
  let := Fintype.ofFinite E
  have hlastEnd := endpoint_of_subsingleton hlastComponent hlastSub
  rcases endpoint_is_m_or_pen hlastEnd with hlastM | hlastPen
  · have hv : T.vertex m = T.vertex (Fin.last T.length) := by
      simpa using hlastM.symm
    have hindices := congrArg Fin.val (T.vertex_injective hv)
    dsimp at hindices
    omega
  · have hv : T.vertex pen = T.vertex (Fin.last T.length) := by
      simpa using hlastPen.symm
    have hindices := congrArg Fin.val (T.vertex_injective hv)
    dsimp [pen] at hindices
    omega

private theorem helper_continuation_699.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), TashTreeMinimumBadPair G k e0 phi T →
    ∀ (hq : (2 : ℕ) < TashTreePathIndex G T) (hbefore : TashTreePathIndex G T < T.length), (¬
    ∃ (alpha : Fin k) (i : Fin (T.length + (1 : ℕ))), TashTreePathIndex G T ≤ (↑i : ℕ) ∧ (↑i : ℕ)
        < T.length ∧ alpha ∈ MissingColors G phi (T.vertex i) ∧ alpha ∈ MissingColors G phi
        (T.vertex (Fin.last T.length))) → IsProperEdgeColoring G phi → TashkinovTree G e0 phi T →
    ∀ (beta : Fin k) (j : Fin (T.length + (1 : ℕ))), T.vertex j ∈ TreeSequenceVertexSet T → beta ∈
        MissingColors G phi (T.vertex (Fin.last T.length)) →
    ∀ (i : Fin (T.length + (1 : ℕ))) (hiBefore : (↑i : ℕ) < TashTreePathIndex G T) (hiearly : ¬(↑i
        : ℕ) + (2 : ℕ) ≤ TashTreePathIndex G T) (hiEq : (↑i : ℕ) = TashTreePathIndex G T - (1 :
        ℕ)),
    let rnew : Fin T.length := (⟨TashTreePathIndex G T - (2 : ℕ),
    by omega
    ⟩ : Fin T.length);
    let d : Fin k := (phi (T.edge rnew)).getD beta;
    ∀ (alpha : Fin k), alpha ≠ beta → alpha ≠ d →
    ∀ (m : Fin (T.length + (1 : ℕ))), (↑m : ℕ) ≤ TashTreePathIndex G T - (2 : ℕ) → alpha ∈
        MissingColors G phi (T.vertex m) →
    let pen : Fin (T.length + (1 : ℕ)) := (⟨TashTreePathIndex G T - (1 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); beta ∈ MissingColors G phi (T.vertex pen) →
        TreeColorUnusedThrough phi T alpha pen →
    let _ : TreeSequence G e0 := TreeSequencePrefix T (TashTreePathIndex G T - (1 : ℕ)) (
    by omega
    ) (
    by omega
    );
    ∃ (phi' : PartialEdgeColoring E k) (beta : Fin k) (i : Fin (T.length + (1 : ℕ))),
        TashTreeMinimumBadPair G k e0 phi' T ∧ (↑i : ℕ) + (2 : ℕ) ≤ TashTreePathIndex G T ∧ beta ∈
        MissingColors G phi' (T.vertex i) ∧ beta ∈ MissingColors G phi' (T.vertex (Fin.last
        T.length)) ∧ ¬
    ∃ (alpha : Fin k) (s : Fin (T.length + (1 : ℕ))), TashTreePathIndex G T ≤ (↑s : ℕ) ∧ (↑s : ℕ)
        < T.length ∧ alpha ∈ MissingColors G phi' (T.vertex s) ∧ alpha ∈ MissingColors G phi'
        (T.vertex (Fin.last T.length)) := by
  classical
  intro V E _ _ _ G k e0 phi T hmin hq hbefore hnone hproper hTash beta j hv hbetaLast i hiBefore
      hiearly hiEq rnew d alpha hab had m hm halphaM pen hbetaPen halphaUnused B
  have hBlength : B.length = TashTreePathIndex G T - 1 := rfl
  have hBelem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet B) := by
    apply TashTreeProperPrefixElementary G k e0 phi T B hmin
    · refine ⟨by rw [hBlength]; omega, ?_, ?_⟩
      · intro r
        rfl
      · intro r
        rfl
    · rw [hBlength]
      omega
  have hpenB : T.vertex pen ∈ TreeSequenceVertexSet B := by
    rw [TreeSequenceVertexSet]
    let p : Fin (B.length + 1) := ⟨pen.val, by rw [hBlength]; simp [pen]⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
  have hbetaUnused := @helper_hbetaUnused_395 V E inferInstance inferInstance G k e0 phi T hq
      hbefore hTash beta j hv i hiBefore hiearly hiEq m hbetaPen hBlength hBelem hpenB
  have hmpen : m.val < pen.val := by
    dsimp [pen]
    omega
  have hpenLength : pen.val < T.length := by
    dsimp [pen]
    omega
  have hswap := TashTreeControlledInterchange G k e0 phi T hmin
    m pen hmpen hpenLength alpha beta hab halphaM hbetaPen
    halphaUnused hbetaUnused
  dsimp only at hswap
  let phi' := TwoColorComponentSwap G phi alpha beta
    (Sum.inl (T.vertex pen))
  rcases hswap with
    ⟨_hcomponentPath, hmComponent, hmSub, hpenSub, hbetaM,
      _halphaPen, _hearly, _hlater, hmin'⟩
  let C := TwoColorComponent G phi alpha beta (Sum.inl (T.vertex pen))
  obtain ⟨a, b, path, hpathSimple, hsupport⟩ :=
    TwoColorComponentSpanningPath G phi alpha beta hproper
      (Sum.inl (T.vertex pen))
  have support_of_component {x : Sum V E} (hx : x ∈ C) :
      x ∈ path.support := by
    change x ∈ {y | y ∈ path.support}
    rw [hsupport]
    exact hx
  have endpoint_of_subsingleton {x : Sum V E} (hx : x ∈ C)
      (hxSub : Set.Subsingleton
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet x)) :
      x = a ∨ x = b := by
    by_contra hend
    push Not at hend
    exact (hpathSimple.isTrail.notMem_support_of_subsingleton_neighborSet
      hend.1 hend.2 hxSub) (support_of_component hx)
  have hpenComponent : Sum.inl (T.vertex pen) ∈ C := by
    change Sum.inl (T.vertex pen) ∈
      ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
        (Sum.inl (T.vertex pen))).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hmEnd := endpoint_of_subsingleton hmComponent hmSub
  have hpenEnd := endpoint_of_subsingleton hpenComponent hpenSub
  have hm_ne_pen : (Sum.inl (T.vertex m) : Sum V E) ≠
      Sum.inl (T.vertex pen) := by
    intro heq
    have hv : T.vertex m = T.vertex pen := by simpa using heq
    exact (Fin.ne_of_lt (by exact hmpen)) (T.vertex_injective hv)
  have endpoint_is_m_or_pen {x : Sum V E} (hx : x = a ∨ x = b) :
      x = Sum.inl (T.vertex m) ∨ x = Sum.inl (T.vertex pen) := by
    rcases hmEnd with hmA | hmB <;> rcases hpenEnd with hpA | hpB
    · exact False.elim (hm_ne_pen (hmA.trans hpA.symm))
    · rcases hx with hxA | hxB
      · exact Or.inl (hxA.trans hmA.symm)
      · exact Or.inr (hxB.trans hpB.symm)
    · rcases hx with hxA | hxB
      · exact Or.inr (hxA.trans hpA.symm)
      · exact Or.inl (hxB.trans hmB.symm)
    · exact False.elim (hm_ne_pen (hmB.trans hpB.symm))
  have hlastSub := TwoColorMissingVertexNeighborsSubsingleton G phi hproper alpha beta
    (T.vertex (Fin.last T.length)) (Or.inr hbetaLast)
  have hlastOutside := @helper_hlastOutside_622 V E inferInstance inferInstance G k e0 phi T hq
      hbefore beta j hv i hiBefore hiearly hiEq alpha m hBlength hmpen hpenLength a b
      endpoint_of_subsingleton endpoint_is_m_or_pen hlastSub
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi alpha beta hab
    hproper (Sum.inl (T.vertex pen))
  dsimp only at hbehavior
  have hbetaLast' : beta ∈
      MissingColors G phi' (T.vertex (Fin.last T.length)) := by
    rw [hbehavior.1 _ hlastOutside]
    exact hbetaLast
  have hgraph := @helper_hgraph_526 V E inferInstance inferInstance G k e0 phi T hq hbefore beta i
      hiBefore hiearly hiEq alpha hab m
  have hproper' : IsProperEdgeColoring G phi' := hmin'.1.1.2.2.2.1
  have hnone' : ¬ ∃ c : Fin k, ∃ s : Fin (T.length + 1),
      TashTreePathIndex G T ≤ s.val ∧ s.val < T.length ∧
      c ∈ MissingColors G phi' (T.vertex s) ∧
      c ∈ MissingColors G phi'
        (T.vertex (Fin.last T.length)) := by
    exact @helper_hnone_387 V E inferInstance inferInstance G k e0 phi T hq hbefore
        hnone beta j hv i hiBefore hiearly hiEq alpha hab had m hm hBlength a b
        endpoint_of_subsingleton endpoint_is_m_or_pen hlastOutside hbehavior hgraph hproper'
  refine ⟨phi', beta, m, hmin', ?_, hbetaM, hbetaLast', hnone'⟩
  omega

theorem TashTreeEarlyBetaNormalization {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hbefore : TashTreePathIndex G T < T.length)
    (hnone : ¬ ∃ alpha : Fin k, ∃ i : Fin (T.length + 1),
      TashTreePathIndex G T ≤ i.val ∧ i.val < T.length ∧
      alpha ∈ MissingColors G phi (T.vertex i) ∧
      alpha ∈ MissingColors G phi (T.vertex (Fin.last T.length))) :
    ∃ (phi' : PartialEdgeColoring E k) (beta : Fin k) (i : Fin (T.length + 1)),
    TashTreeMinimumBadPair G k e0 phi' T ∧
      i.val + 2 ≤ TashTreePathIndex G T ∧
        beta ∈ MissingColors G phi' (T.vertex i) ∧
          beta ∈ MissingColors G phi' (T.vertex (Fin.last T.length)) ∧
            ¬∃ alpha : Fin k,
                ∃ s : Fin (T.length + 1),
                  TashTreePathIndex G T ≤ s.val ∧
                    s.val < T.length ∧
                      alpha ∈ MissingColors G phi' (T.vertex s) ∧
                        alpha ∈ MissingColors G phi' (T.vertex (Fin.last T.length)) := by
  classical
  have hproper : IsProperEdgeColoring G phi := hmin.1.1.2.2.2.1
  have hTash : TashkinovTree G e0 phi T := hmin.1.2.1
  have hnotElementary :
      ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    hmin.1.2.2
  let P : TreeSequence G e0 :=
    TreeSequencePrefix T (T.length - 1) (by omega) (by omega)
  have hPlength : P.length = T.length - 1 := rfl
  have hPelem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet P) := by
    apply TashTreeProperPrefixElementary G k e0 phi T P hmin
    · refine ⟨by rw [hPlength]; omega, ?_, ?_⟩
      · intro r
        rfl
      · intro r
        rfl
    · rw [hPlength]
      omega
  have hcommon : ∃ u ∈ TreeSequenceVertexSet T,
      ∃ v ∈ TreeSequenceVertexSet T, u ≠ v ∧
        ∃ beta, beta ∈ MissingColors G phi u ∧
          beta ∈ MissingColors G phi v := by
    by_contra hneg
    push Not at hneg
    apply hnotElementary
    intro u hu v hv huv
    rw [Finset.disjoint_left]
    intro beta hbu hbv
    exact hneg u hu v hv huv beta hbu hbv
  rcases hcommon with ⟨u, hu, v, hv, huv, beta, hbu, hbv⟩
  have huindex : ∃ i : Fin (T.length + 1), T.vertex i = u := by
    simpa [TreeSequenceVertexSet] using hu
  have hvindex : ∃ i : Fin (T.length + 1), T.vertex i = v := by
    simpa [TreeSequenceVertexSet] using hv
  rcases huindex with ⟨i, rfl⟩
  rcases hvindex with ⟨j, rfl⟩
  have hbetaLast := @helper_hbetaLast_454 V E inferInstance inferInstance G k e0 phi T hq hbefore
      hPlength hPelem beta i hbu j hbv huv
  have hbetaIndex : ∃ i : Fin (T.length + 1), i.val < T.length ∧
      beta ∈ MissingColors G phi (T.vertex i) := by
    by_cases hi : i.val < T.length
    · exact ⟨i, hi, hbu⟩
    · have hjlt : j.val < T.length := by
        have hjle : j.val ≤ T.length := Nat.le_of_lt_succ j.isLt
        have hjne : j.val ≠ T.length := by
          intro hjlast
          have hiLast : i.val = T.length := by omega
          have hij : i = j := Fin.ext (by simp [hiLast, hjlast])
          exact huv (congrArg T.vertex hij)
        exact Nat.lt_of_le_of_ne hjle hjne
      exact ⟨j, hjlt, hbv⟩
  rcases hbetaIndex with ⟨i, hiLength, hbetaI⟩
  have hiBefore : i.val < TashTreePathIndex G T := by
    by_contra hi
    have hqi : TashTreePathIndex G T ≤ i.val := Nat.le_of_not_gt hi
    exact hnone ⟨beta, i, hqi, hiLength, hbetaI, hbetaLast⟩
  by_cases hiearly : i.val + 2 ≤ TashTreePathIndex G T
  · exact ⟨phi, beta, i, hmin, hiearly, hbetaI, hbetaLast, hnone⟩
  have hiEq : i.val = TashTreePathIndex G T - 1 := by omega
  let A : TreeSequence G e0 :=
    TreeSequencePrefix T (TashTreePathIndex G T - 2) (by omega) (by omega)
  have hAlength : A.length = TashTreePathIndex G T - 2 := rfl
  have hfour : 4 ≤ (TreeFreeColors phi A).card := by
    simpa [A] using TashTreeFourUnusedColors G k e0 phi T hmin
      (TashTreePathIndex G T - 2) (by omega) (by omega)
  let rnew : Fin T.length :=
    ⟨TashTreePathIndex G T - 2, by omega⟩
  let d : Fin k := (phi (T.edge rnew)).getD beta
  have hfree : ∃ alpha : Fin k, alpha ∈ TreeFreeColors phi A ∧
      alpha ≠ beta ∧ alpha ≠ d := by
    by_contra! hn
    have hs : TreeFreeColors phi A ⊆ ({beta, d} : Finset (Fin k)) := by
      intro c hc
      by_cases hcb : c = beta
      · simp [hcb]
      · simp [hn c hc hcb]
    have hc := Finset.card_le_card hs
    have hpair : ({beta, d} : Finset (Fin k)).card ≤ 2 :=
      Finset.card_insert_le _ _
    omega
  rcases hfree with ⟨alpha, halphaFree, hab, had⟩
  have halphaMissing := @helper_halphaMissing_519 V E inferInstance inferInstance G k e0 phi T hq
      hbefore beta i hiBefore hiearly hiEq hAlength alpha halphaFree hab had
  rcases halphaMissing with ⟨m, hm, halphaM⟩
  let pen : Fin (T.length + 1) :=
    ⟨TashTreePathIndex G T - 1, by omega⟩
  have hbetaPen : beta ∈ MissingColors G phi (T.vertex pen) := by
    have hip : i = pen := by
      apply Fin.ext
      simpa [pen] using hiEq
    simpa [hip] using hbetaI
  have halphaUnused := @helper_halphaUnused_358 V E inferInstance inferInstance G k e0 phi T hq
      hbefore beta i hiBefore hiearly hiEq hAlength alpha halphaFree hab had m
  let B : TreeSequence G e0 :=
    TreeSequencePrefix T (TashTreePathIndex G T - 1) (by omega) (by omega)
  exact @helper_continuation_699 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@hmin) (@hq) (@hbefore) (@hnone) (@hproper) (@hTash) (@beta) (@j) (@hv)
      (@hbetaLast) (@i) (@hiBefore) (@hiearly) (@hiEq) (@alpha) (@hab) (@had) (@m) (@hm)
      (@halphaM) (@hbetaPen) (@halphaUnused)
end GoldbergSeymour

end
