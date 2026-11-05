/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BoundaryEdges
public import LeanPool.GoldbergSeymour.InternalEdges
public import LeanPool.GoldbergSeymour.RevisitingExtensionCertificate
public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStep
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TwoColorCycle
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Earlier PECycle First Nonrevisiting Internal

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private abbrev helperContinuation1518Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k),
        series.data.kind r.succ = some TashkinovExtensionKind.PE → series.data.gamma r.succ = some
        gamma → series.data.delta r.succ = some delta →
    ∀ (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (
    ∃ v ∈ TreeSequenceVertexSet (series.data.tree r.succ.castSucc), Sum.inl v ∈
        cycle.walk.support) → (↑r : ℕ) + (1 : ℕ) < rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty; (↑r : ℕ) < (↑p : ℕ) → (
    ∀ (j : Fin rounds), (↑r : ℕ) < (↑j : ℕ) → (↑j : ℕ) < (↑p : ℕ) → series.data.kind j.succ = some
        TashkinovExtensionKind.RE) →
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
        cycleP.walk.support = cycle.walk.support → TreeSequenceVertexSet (series.data.tree
        r.succ.castSucc) ⊆ TreeSequenceVertexSet (series.data.tree p.succ.castSucc) → ¬Nonempty
        (RevisitingExtensionCertificate series.data p.castSucc) →
    ∀ f ∉ InternalEdges G (TreeSequenceVertexSet (series.data.tree p.succ.castSucc)),
    ∀ (hfCycleP : Sum.inr f ∈ cycleP.walk.support), (
    ∀ {z : Sym2 V} {a b : V}, a ∈ z → b ∈ z → a ≠ b → z = s(a, b)) →
    let edgeCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Walk
        (Sum.inr f) (Sum.inr f) := cycleP.walk.rotate (Sum.inr f) hfCycleP;
    ∀ (a : V), edgeCycle.getVert (1 : ℕ) = Sum.inl a → Incident G a f →
    ∀ (b : V), edgeCycle.getVert (edgeCycle.length - (1 : ℕ)) = Sum.inl b → Incident G b f → a ≠ b
        → G.ends f = s(a, b) → False

private theorem helper_reColoring_116.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (_ : (↑r : ℕ) + (1 : ℕ) < rounds),
    let candidates : Finset (Fin rounds) := {q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE};
    ∀ (_ : candidates.Nonempty) (j : Fin rounds) (_ : series.data.kind j.succ = some
        TashkinovExtensionKind.RE), series.data.coloring j.succ = series.data.coloring j.castSucc
  := by
  classical
  intro V E _ _ _ G k rounds e0 input series r hrTerminalLt candidates candidatesNonempty j hjKind
  generalize hjSlot : j.succ = slot at hjKind ⊢
  cases series.certified slot with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    exact (Fin.succ_ne_zero j hjSlot).elim
  | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    have : some TashkinovExtensionKind.SE = some TashkinovExtensionKind.RE :=
      currentKind.symm.trans (by simpa [hjSlot] using hjKind)
    cases this
  | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
    have : some TashkinovExtensionKind.PE = some TashkinovExtensionKind.RE :=
      currentKind.symm.trans (by simpa [hjSlot] using hjKind)
    cases this
  | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
    have hi : i = j := by
      apply Fin.ext
      have := congrArg Fin.val hjSlot
      simp only [Fin.val_succ] at this
      omega
    subst i
    simpa [hjSlot] using currentColoring

private theorem helper_stepVertexSubset_192.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (_ : (↑r : ℕ) + (1 : ℕ) < rounds),
    let candidates : Finset (Fin rounds) := {q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE};
    ∀ (_ : candidates.Nonempty) (j : Fin rounds), TreeSequenceVertexSet (series.data.tree
        j.succ.castSucc) ⊆ TreeSequenceVertexSet (series.data.tree j.succ.succ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series r hrTerminalLt candidates candidatesNonempty j
  generalize hjSlot : j.succ = slot
  cases series.certified slot with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    exact (Fin.succ_ne_zero j hjSlot).elim
  | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    have hi : i = j := by
      apply Fin.ext
      have := congrArg Fin.val hjSlot
      simp only [Fin.val_succ] at this
      omega
    subst i
    exact TreeSequenceInitialSegmentVertexSetSubset (by simpa [hjSlot] using orderedExtension)
  | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
    have hi : i = j := by
      apply Fin.ext
      have := congrArg Fin.val hjSlot
      simp only [Fin.val_succ] at this
      omega
    subst i
    exact TreeSequenceInitialSegmentVertexSetSubset (by simpa [hjSlot] using orderedExtension)
  | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
    have hi : i = j := by
      apply Fin.ext
      have := congrArg Fin.val hjSlot
      simp only [Fin.val_succ] at this
      omega
    subst i
    exact TreeSequenceInitialSegmentVertexSetSubset (by simpa [hjSlot] using orderedExtension)

private theorem helper_pNoRevisiting_258.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (_ : (↑r : ℕ) + (1 : ℕ) < rounds),
    let candidates : Finset (Fin rounds) := {q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE};
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (_ : series.data.kind p.succ ≠ some TashkinovExtensionKind.RE), ¬Nonempty
        (RevisitingExtensionCertificate series.data p.castSucc) := by
  classical
  intro V E _ _ _ G k rounds e0 input series r hrTerminalLt candidates candidatesNonempty p pNotRE
  generalize hpSlot : p.succ = slot
  cases series.certified slot with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    exact (Fin.succ_ne_zero p hpSlot).elim
  | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    have hi : i = p := by
      apply Fin.ext
      have := congrArg Fin.val hpSlot
      simp only [Fin.val_succ] at this
      omega
    subst i
    simpa using noRevisiting
  | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
    have hi : i = p := by
      apply Fin.ext
      have := congrArg Fin.val hpSlot
      simp only [Fin.val_succ] at this
      omega
    subst i
    simpa using noRevisiting
  | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
    have hRE : series.data.kind p.succ = some TashkinovExtensionKind.RE := by
      simpa [hpSlot] using currentKind
    exact False.elim (pNotRE hRE)

private theorem helper_hrTerminalLt_212 :
    open scoped Classical in
    ∀ (rounds : ℕ) (r : Fin rounds), r.succ ≠ Fin.last rounds → (↑r : ℕ) + (1 : ℕ) < rounds := by
  classical
  intro rounds r hrEarlier
  have hrle : r.val + 1 ≤ rounds := by omega
  have hrne : r.val + 1 ≠ rounds := by
    intro h
    apply hrEarlier
    apply Fin.ext
    simpa using h
  omega

private theorem helper_betweenRE_239.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (r : Fin rounds), (↑r : ℕ) + (1 : ℕ) < rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (j : Fin rounds), (↑r : ℕ) < (↑j : ℕ) → (↑j : ℕ) < (↑p : ℕ) → series.data.kind j.succ = some
        TashkinovExtensionKind.RE := by
  classical
  intro V E _ _ _ G k rounds e0 input series r hrTerminalLt candidates candidatesNonempty p j hrj
      hjp
  by_contra hjNot
  have hjMem : j ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hrj, hjNot⟩
  have hpj : p ≤ j := Finset.min'_le candidates j hjMem
  omega

private theorem helper_pKind_247.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (r : Fin rounds),
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty; series.data.kind p.succ ≠ some
        TashkinovExtensionKind.RE → series.data.kind p.succ = some TashkinovExtensionKind.SE ∨
        series.data.kind p.succ = some TashkinovExtensionKind.PE := by
  classical
  intro V E _ _ _ G k rounds e0 input series r candidates candidatesNonempty p pNotRE
  generalize hpSlot : p.succ = slot at pNotRE ⊢
  cases series.certified slot with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma initialClosure =>
    exact (Fin.succ_ne_zero p hpSlot).elim
  | SE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternative currentColoring currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma adjoined
      adjoinedExactly closedExtension orderedExtension strictExtension =>
    exact Or.inl (by simpa [hpSlot] using currentKind)
  | PE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      noRevisiting choice seriesAlternativeFails actualGamma gammaRule secondStable
      secondStableProper secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored currentEdges
      currentKind currentVertex currentOutside currentDelta currentGamma closedExtension
      orderedExtension strictExtension =>
    exact Or.inr (by simpa [hpSlot] using currentKind)
  | RE i previousProper previousOneUncolored previousClosed previousNotStronglyClosed
      available currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly closedExtension
      orderedExtension strictExtension =>
    exact False.elim (pNotRE (by simpa [hpSlot] using currentKind))

private theorem helper_coloringAlong_276.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (r : Fin rounds), (↑r : ℕ) + (1 : ℕ) < rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty; (
    ∀ (j : Fin rounds), (↑r : ℕ) < (↑j : ℕ) → (↑j : ℕ) < (↑p : ℕ) → series.data.kind j.succ = some
        TashkinovExtensionKind.RE) → (
    ∀ (j : Fin rounds), series.data.kind j.succ = some TashkinovExtensionKind.RE →
        series.data.coloring j.succ = series.data.coloring j.castSucc) →
    ∀ (n : ℕ), (↑r : ℕ) + (1 : ℕ) ≤ n → n ≤ (↑p : ℕ) →
    ∀ (q : Fin (rounds + (1 : ℕ))), (↑q : ℕ) = n → series.data.coloring q = series.data.coloring
        r.succ := by
  classical
  intro V E _ _ _ G k rounds e0 input series r hrTerminalLt candidates candidatesNonempty p
      betweenRE reColoring n hrn
  induction n, hrn using Nat.le_induction with
  | base =>
    intro hnp q hq
    have hqr : q = r.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    simp [hqr]
  | succ n hn ih =>
    intro hnp q hq
    have hnltp : n < p.val := by omega
    have hnr : r.val < n := by omega
    let j : Fin rounds := ⟨n, by omega⟩
    have hjKind := betweenRE j (by simpa [j]) (by simpa [j])
    have hjColor := reColoring j hjKind
    have hqSucc : q = j.succ := by
      apply Fin.ext
      simp [j, hq]
    have hjCast : j.castSucc.val = n := by simp [j]
    calc
      series.data.coloring q = series.data.coloring j.succ := by rw [hqSucc]
      _ = series.data.coloring j.castSucc := hjColor
      _ = series.data.coloring r.succ := ih (by omega) j.castSucc hjCast

private theorem helper_treeAlong_321.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k) (series
        : TashkinovSeries G k rounds e0 input) (r : Fin rounds), (↑r : ℕ) + (1 : ℕ) < rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty; (
    ∀ (j : Fin rounds), TreeSequenceVertexSet (series.data.tree j.succ.castSucc) ⊆
        TreeSequenceVertexSet (series.data.tree j.succ.succ)) →
    ∀ (n : ℕ), (↑r : ℕ) ≤ n → n ≤ (↑p : ℕ) →
    ∀ (q : Fin rounds), (↑q : ℕ) = n → TreeSequenceVertexSet (series.data.tree r.succ.castSucc) ⊆
        TreeSequenceVertexSet (series.data.tree q.succ.castSucc) := by
  classical
  intro V E _ _ _ G k rounds e0 input series r hrTerminalLt candidates candidatesNonempty p
      stepVertexSubset n hrn
  induction n, hrn using Nat.le_induction with
  | base =>
    intro hnp q hq
    have hqr : q = r := by apply Fin.ext; omega
    simp [hqr]
  | succ n hn ih =>
    intro hnp q hq
    let prev : Fin rounds := ⟨n, by omega⟩
    have hprev := ih (by omega) prev rfl
    have hstep := stepVertexSubset prev
    have htree : prev.succ.succ = q.succ.castSucc := by
      apply Fin.ext
      simp [prev, hq]
    simpa [htree] using Set.Subset.trans hprev hstep

private theorem helper_edgeIdentity_353.{u_1} :
    open scoped Classical in
    ∀ {V : Type u_1} {z : Sym2 V} {a b : V}, a ∈ z → b ∈ z → a ≠ b → z = s(a, b) := by
  classical
  intro V z a b ha hb hab
  induction z using Sym2.inductionOn with
  | _ c d =>
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

private theorem helper_firstVertex_365.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta),
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E) (hfCycleP : Sum.inr f ∈ cycleP.walk.support),
    let edgeCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Walk
        (Sum.inr f) (Sum.inr f) := cycleP.walk.rotate (Sum.inr f) hfCycleP;
        (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Adj
        (edgeCycle.getVert (0 : ℕ)) (edgeCycle.getVert ((0 : ℕ) + (1 : ℕ))) →
    ∃ (a : V), edgeCycle.getVert (1 : ℕ) = Sum.inl a := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle candidates candidatesNonempty p
      pColoring cycleP f hfCycleP edgeCycle firstAdj
  cases hfirst : edgeCycle.getVert 1 with
  | inl a => exact ⟨a, rfl⟩
  | inr e =>
    exfalso
    rw [edgeCycle.getVert_zero, hfirst] at firstAdj
    simp [TwoColorIncidenceGraph] at firstAdj

private theorem helper_lastVertex_378.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E) (hfCycleP : Sum.inr f ∈ cycleP.walk.support),
    let edgeCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Walk
        (Sum.inr f) (Sum.inr f) := cycleP.walk.rotate (Sum.inr f) hfCycleP; (3 : ℕ) ≤
        edgeCycle.length → (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Adj (edgeCycle.getVert (edgeCycle.length - (1 : ℕ))) (edgeCycle.getVert
        (edgeCycle.length - (1 : ℕ) + (1 : ℕ))) →
    ∃ (b : V), edgeCycle.getVert (edgeCycle.length - (1 : ℕ)) = Sum.inl b := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP edgeCycle edgeCycleLength lastAdj
  cases hlast : edgeCycle.getVert (edgeCycle.length - 1) with
  | inl b => exact ⟨b, rfl⟩
  | inr e =>
    exfalso
    have hidx : edgeCycle.length - 1 + 1 = edgeCycle.length := by omega
    rw [hidx, edgeCycle.getVert_length, hlast] at lastAdj
    simp [TwoColorIncidenceGraph] at lastAdj

private theorem helper_hab_392.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta),
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E) (hfCycleP : Sum.inr f ∈ cycleP.walk.support),
    let edgeCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Walk
        (Sum.inr f) (Sum.inr f) := cycleP.walk.rotate (Sum.inr f) hfCycleP; edgeCycle.IsCycle →
    ∀ (a : V), edgeCycle.getVert (1 : ℕ) = Sum.inl a →
    ∀ (b : V), edgeCycle.getVert (edgeCycle.length - (1 : ℕ)) = Sum.inl b → a ≠ b := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle candidates candidatesNonempty p
      pColoring cycleP f hfCycleP edgeCycle edgeCycleIsCycle a ha b hb habEq
  apply edgeCycleIsCycle.snd_ne_penultimate
  rw [show edgeCycle.snd = Sum.inl a by simpa using ha]
  rw [show edgeCycle.penultimate = Sum.inl b by simpa using hb]
  exact congrArg Sum.inl habEq

private theorem helper_outsideOnCycle_401.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta),
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ f ∉ InternalEdges G (TreeSequenceVertexSet (series.data.tree p.succ.castSucc)),
    ∀ (hfCycleP : Sum.inr f ∈ cycleP.walk.support),
    let edgeCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Walk
        (Sum.inr f) (Sum.inr f) := cycleP.walk.rotate (Sum.inr f) hfCycleP;
    ∀ (a : V), edgeCycle.getVert (1 : ℕ) = Sum.inl a → Incident G a f →
    ∀ (b : V), edgeCycle.getVert (edgeCycle.length - (1 : ℕ)) = Sum.inl b → Incident G b f → a ≠ b
        → G.ends f = s(a, b) →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∃ y ∉ currentTree, Sum.inl y ∈ cycleP.walk.support := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle candidates candidatesNonempty p
      pColoring cycleP f hfNotInternal hfCycleP edgeCycle a ha hfa b hb hfb hab hfEndsAB currentTree
  by_cases haCurrent : a ∈ currentTree
  · have hbOutside : b ∉ currentTree := by
      intro hbCurrent
      apply hfNotInternal
      simp only [InternalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      intro v hv
      have hvEnds : v ∈ G.ends f := by simpa [Incident] using hv
      rw [hfEndsAB] at hvEnds
      rcases (by simpa only [Sym2.mem_iff] using hvEnds) with rfl | rfl
      · exact haCurrent
      · exact hbCurrent
    refine ⟨b, hbOutside, ?_⟩
    apply (cycleP.walk.mem_support_rotate_iff (Sum.inr f) hfCycleP).mp
    change Sum.inl b ∈ edgeCycle.support
    rw [← hb]
    exact edgeCycle.getVert_mem_support (edgeCycle.length - 1)
  · refine ⟨a, haCurrent, ?_⟩
    apply (cycleP.walk.mem_support_rotate_iff (Sum.inr f) hfCycleP).mp
    change Sum.inl a ∈ edgeCycle.support
    rw [← ha]
    exact edgeCycle.getVert_mem_support 1

private theorem helper_outsideIndicesNonempty_437.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    ∀ outsideVertex ∉ currentTree,
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
        Sum.inl outsideVertex ∈ rootedCycle.support →
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ)))); outsideIndices.Nonempty := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP outsideVertex
      outsideVertexNotCurrent rootedCycle outsideVertexRooted outsideIndices
  obtain ⟨n, hn, hnle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp outsideVertexRooted
  let i : Fin (rootedCycle.length + 1) := ⟨n, by omega⟩
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact ⟨outsideVertex, by simpa [i] using hn, outsideVertexNotCurrent⟩

private theorem helper_beforeFirstOutside_450.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (i : Fin (rootedCycle.length + (1 : ℕ))), (↑i : ℕ) < (↑firstOutside : ℕ) →
    ∀ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v → v ∈ currentTree := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP rootedCycle
      outsideIndices outsideIndicesNonempty firstOutside i hi v hv
  by_contra hvOutside
  have hiMem : i ∈ outsideIndices := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨v, hv, hvOutside⟩⟩
  have hmin := Finset.min'_le outsideIndices i hiMem
  omega

private theorem helper_firstOutsidePositive_459.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support), v0 ∈ currentTree →
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (y : V), rootedCycle.getVert (↑firstOutside : ℕ) = Sum.inl y → y ∉ currentTree → (0 : ℕ) <
        (↑firstOutside : ℕ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP hv0Current
      rootedCycle outsideIndices outsideIndicesNonempty firstOutside y hyAt hyOutside
  by_contra hnot
  have hiZero : firstOutside.val = 0 := by omega
  have hyv0 : y = v0 := by
    apply Sum.inl.inj
    calc
      Sum.inl y = rootedCycle.getVert firstOutside.val := hyAt.symm
      _ = rootedCycle.getVert 0 := by rw [hiZero]
      _ = Sum.inl v0 := rootedCycle.getVert_zero
  exact hyOutside (hyv0.symm ▸ hv0Current)

private theorem helper_firstOutsideLt_469.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support), v0 ∈ currentTree →
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (y : V), rootedCycle.getVert (↑firstOutside : ℕ) = Sum.inl y → y ∉ currentTree →
        (↑firstOutside : ℕ) < rootedCycle.length := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP hv0Current
      rootedCycle outsideIndices outsideIndicesNonempty firstOutside y hyAt hyOutside
  by_contra hnot
  have hiLast : firstOutside.val = rootedCycle.length := by
    have := firstOutside.isLt
    omega
  have hyv0 : y = v0 := by
    apply Sum.inl.inj
    calc
      Sum.inl y = rootedCycle.getVert firstOutside.val := hyAt.symm
      _ = rootedCycle.getVert rootedCycle.length := by rw [hiLast]
      _ = Sum.inl v0 := rootedCycle.getVert_length
  exact hyOutside (hyv0.symm ▸ hv0Current)

private theorem helper_firstOutsideNotOne_481.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (y : V), rootedCycle.getVert (↑firstOutside : ℕ) = Sum.inl y → (↑firstOutside : ℕ) <
        rootedCycle.length → (↑firstOutside : ℕ) ≠ (1 : ℕ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP rootedCycle
      outsideIndices outsideIndicesNonempty firstOutside y hyAt firstOutsideLt hiOne
  have hAdj := rootedCycle.adj_getVert_succ (i := 0) (by omega)
  have hyOne : rootedCycle.getVert 1 = Sum.inl y := by
    simpa [hiOne] using hyAt
  rw [rootedCycle.getVert_zero, hyOne] at hAdj
  simp [TwoColorIncidenceGraph] at hAdj

private theorem helper_crossingEdge_492.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta),
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (y : V), rootedCycle.getVert (↑firstOutside : ℕ) = Sum.inl y → (TwoColorIncidenceGraph G
        (series.data.coloring p.castSucc) gamma delta).Adj (rootedCycle.getVert ((↑firstOutside :
        ℕ) - (1 : ℕ))) (rootedCycle.getVert ((↑firstOutside : ℕ) - (1 : ℕ) + (1 : ℕ))) →
        (↑firstOutside : ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) →
    ∃ (g : E), rootedCycle.getVert ((↑firstOutside : ℕ) - (1 : ℕ)) = Sum.inr g := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle candidates candidatesNonempty p
      pColoring cycleP currentTree v0 hv0CycleP rootedCycle outsideIndices outsideIndicesNonempty
      firstOutside y hyAt crossingAdj crossingIndex
  cases hnode : rootedCycle.getVert (firstOutside.val - 1) with
  | inl v =>
    exfalso
    rw [crossingIndex, hyAt, hnode] at crossingAdj
    simp [TwoColorIncidenceGraph] at crossingAdj
  | inr g => exact ⟨g, rfl⟩

private theorem helper_insideVertex_508.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta),
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty;
    ∀ (g : E), rootedCycle.getVert ((↑firstOutside : ℕ) - (1 : ℕ)) = Sum.inr g →
        (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Adj
        (rootedCycle.getVert ((↑firstOutside : ℕ) - (2 : ℕ))) (rootedCycle.getVert ((↑firstOutside
        : ℕ) - (2 : ℕ) + (1 : ℕ))) → (↑firstOutside : ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ)
        - (1 : ℕ) →
    ∃ (x : V), rootedCycle.getVert ((↑firstOutside : ℕ) - (2 : ℕ)) = Sum.inl x := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle candidates candidatesNonempty p
      pColoring cycleP currentTree v0 hv0CycleP rootedCycle outsideIndices outsideIndicesNonempty
      firstOutside g hgAt beforeCrossingAdj beforeCrossingIndex
  cases hnode : rootedCycle.getVert (firstOutside.val - 2) with
  | inl x => exact ⟨x, rfl⟩
  | inr e =>
    exfalso
    rw [beforeCrossingIndex, hgAt, hnode] at beforeCrossingAdj
    simp [TwoColorIncidenceGraph] at beforeCrossingAdj

private theorem helper_hxCurrent_517.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty; (
    ∀ (i : Fin (rootedCycle.length + (1 : ℕ))), (↑i : ℕ) < (↑firstOutside : ℕ) →
    ∀ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v → v ∈ currentTree) → (↑firstOutside : ℕ) <
        rootedCycle.length → (↑firstOutside : ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) →
        (↑firstOutside : ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) - (1 : ℕ) →
    ∀ (x : V), rootedCycle.getVert ((↑firstOutside : ℕ) - (2 : ℕ)) = Sum.inl x → x ∈ currentTree
  := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP rootedCycle
      outsideIndices outsideIndicesNonempty firstOutside beforeFirstOutside firstOutsideLt
      crossingIndex beforeCrossingIndex x hxAt
  apply beforeFirstOutside
    (⟨firstOutside.val - 2, Nat.lt_succ_of_le
      ((Nat.sub_le _ _).trans (Nat.le_of_lt firstOutsideLt))⟩ :
        Fin (rootedCycle.length + 1))
    (show firstOutside.val - 2 < firstOutside.val by omega) x
  simpa using hxAt

private theorem helper_returnPrefixPositive_550.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ)))); outsideIndices.Nonempty →
    ∀ (g : E) (hgRooted : Sum.inr g ∈ rootedCycle.support),
    let returnPrefix : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inr g) := rootedCycle.takeUntil (Sum.inr g) hgRooted; (0 :
        ℕ) < returnPrefix.length := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP rootedCycle
      outsideIndices outsideIndicesNonempty g hgRooted returnPrefix
  by_contra hnot
  have hzero : returnPrefix.length = 0 := by omega
  have hget := rootedCycle.getVert_length_takeUntil hgRooted
  rw [hzero, rootedCycle.getVert_zero] at hget
  cases hget

private theorem helper_returnPrefixLength_556.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
        rootedCycle.IsCycle →
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty; (↑firstOutside : ℕ) < rootedCycle.length → (2 : ℕ) ≤
        (↑firstOutside : ℕ) → (↑firstOutside : ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) →
    ∀ (g : E), rootedCycle.getVert ((↑firstOutside : ℕ) - (1 : ℕ)) = Sum.inr g → (↑firstOutside :
        ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) - (1 : ℕ) →
    ∀ (hgRooted : Sum.inr g ∈ rootedCycle.support),
    let returnPrefix : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inr g) := rootedCycle.takeUntil (Sum.inr g) hgRooted; (0 :
        ℕ) < returnPrefix.length → returnPrefix.length = (↑firstOutside : ℕ) - (1 : ℕ) := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP rootedCycle
      rootedIsCycle outsideIndices outsideIndicesNonempty firstOutside firstOutsideLt
      firstOutsideAtLeastTwo crossingIndex g hgAt beforeCrossingIndex hgRooted returnPrefix
      returnPrefixPositive
  have hprefixLe := rootedCycle.length_takeUntil_le_length hgRooted
  apply rootedIsCycle.getVert_injOn
    (by simp only [Set.mem_ofPred_eq]; exact ⟨returnPrefixPositive, hprefixLe⟩)
    (by simp only [Set.mem_ofPred_eq]; constructor <;> omega)
  calc
    rootedCycle.getVert returnPrefix.length = Sum.inr g :=
      rootedCycle.getVert_length_takeUntil hgRooted
    _ = rootedCycle.getVert (firstOutside.val - 1) := hgAt.symm

private theorem helper_returnPathOnCycle_565.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta),
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    ∀ (g : E) (hgRooted : Sum.inr g ∈ rootedCycle.support),
    let returnPrefix : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inr g) := rootedCycle.takeUntil (Sum.inr g) hgRooted;
    let returnPath : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Walk
        (Sum.inr g) (Sum.inl v0) := returnPrefix.reverse;
    ∀ z ∈ returnPath.support, z ∈ cycleP.walk.support := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle candidates candidatesNonempty p
      pColoring cycleP v0 hv0CycleP rootedCycle g hgRooted returnPrefix returnPath z hz
  have hzPrefix : z ∈ returnPrefix.support := by
    simpa [returnPath, SimpleGraph.Walk.support_reverse] using hz
  have hzRooted := rootedCycle.support_takeUntil_subset_support hgRooted hzPrefix
  exact (cycleP.walk.mem_support_rotate_iff (Sum.inl v0) hv0CycleP).mp hzRooted

private theorem helper_returnPathInternal_572.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty;
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ))));
    ∀ (outsideIndicesNonempty : outsideIndices.Nonempty),
    let firstOutside : Fin (rootedCycle.length + (1 : ℕ)) := outsideIndices.min'
        outsideIndicesNonempty; (
    ∀ (i : Fin (rootedCycle.length + (1 : ℕ))), (↑i : ℕ) < (↑firstOutside : ℕ) →
    ∀ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v → v ∈ currentTree) → (↑firstOutside : ℕ) <
        rootedCycle.length → (↑firstOutside : ℕ) - (1 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) →
    ∀ (g : E), (↑firstOutside : ℕ) - (2 : ℕ) + (1 : ℕ) = (↑firstOutside : ℕ) - (1 : ℕ) →
    ∀ (hgRooted : Sum.inr g ∈ rootedCycle.support),
    let returnPrefix : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inr g) := rootedCycle.takeUntil (Sum.inr g) hgRooted;
    let returnPath : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma delta).Walk
        (Sum.inr g) (Sum.inl v0) := returnPrefix.reverse; returnPrefix.length = (↑firstOutside :
        ℕ) - (1 : ℕ) →
    ∀ (v : V), Sum.inl v ∈ returnPath.support → v ∈ currentTree := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p pColoring cycleP f hfCycleP currentTree v0 hv0CycleP rootedCycle
      outsideIndices outsideIndicesNonempty firstOutside beforeFirstOutside firstOutsideLt
      crossingIndex g beforeCrossingIndex hgRooted returnPrefix returnPath returnPrefixLength v hv
  have hvPrefix : Sum.inl v ∈ returnPrefix.support := by
    simpa [returnPath, SimpleGraph.Walk.support_reverse] using hv
  obtain ⟨m, hm, hmle⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvPrefix
  have hmRooted : rootedCycle.getVert m = Sum.inl v := by
    rw [← rootedCycle.getVert_takeUntil hgRooted hmle]
    exact hm
  have hmFirst : m < firstOutside.val := by
    rw [returnPrefixLength] at hmle
    omega
  apply beforeFirstOutside
    (⟨m, by omega⟩ : Fin (rootedCycle.length + 1)) hmFirst v hmRooted

private theorem helper_interveningForCertificate_587.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [inst : Fintype V] [inst_1 : Fintype E] [inst_2 : DecidableEq
        E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E) (input : PartialEdgeColoring E k)
        (series : TashkinovSeries G k rounds e0 input) (r : Fin rounds) (gamma delta : Fin k)
        (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta), (↑r : ℕ) + (1 : ℕ) <
        rounds →
    let candidates : Finset (Fin rounds) := ({q : Fin rounds | (↑r : ℕ) < (↑q : ℕ) ∧
        series.data.kind q.succ ≠ some TashkinovExtensionKind.RE} : Finset (Fin rounds));
    ∀ (candidatesNonempty : candidates.Nonempty),
    let p : Fin rounds := candidates.min' candidatesNonempty; (
    ∀ (j : Fin rounds), (↑r : ℕ) < (↑j : ℕ) → (↑j : ℕ) < (↑p : ℕ) → series.data.kind j.succ = some
        TashkinovExtensionKind.RE) →
    ∀ (pColoring : series.data.coloring p.castSucc = series.data.coloring r.succ),
    let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta := @Eq.rec
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ
        rounds r)) (fun (x : PartialEdgeColoring E k) (_ : @Eq (PartialEdgeColoring E k)
        (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E inst inst_1
        inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) x) ↦ @TwoColorCycle V E G k x
        gamma delta) cycle (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data
        V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc rounds p)) (@Eq.symm
        (PartialEdgeColoring E k) (@TashkinovSeriesData.coloring V E G k rounds e0
        (@TashkinovSeries.data V E inst inst_1 inst_2 G k rounds e0 input series) (@Fin.castSucc
        rounds p)) (@TashkinovSeriesData.coloring V E G k rounds e0 (@TashkinovSeries.data V E
        inst inst_1 inst_2 G k rounds e0 input series) (@Fin.succ rounds r)) pColoring);
    ∀ (f : E), Sum.inr f ∈ cycleP.walk.support →
    let currentTree : Finset V := TreeSequenceVertexSet (series.data.tree p.succ.castSucc);
    ∀ (v0 : V) (hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support),
    let rootedCycle : (TwoColorIncidenceGraph G (series.data.coloring p.castSucc) gamma
        delta).Walk (Sum.inl v0) (Sum.inl v0) := cycleP.walk.rotate (Sum.inl v0) hv0CycleP;
    let outsideIndices : Finset (Fin (rootedCycle.length + (1 : ℕ))) := ({i : Fin
        (rootedCycle.length + (1 : ℕ)) |
    ∃ (v : V), rootedCycle.getVert (↑i : ℕ) = Sum.inl v ∧ v ∉ currentTree} : Finset (Fin
        (rootedCycle.length + (1 : ℕ)))); outsideIndices.Nonempty →
    ∀ (g : E), Sum.inr g ∈ rootedCycle.support →
    ∀ (j : Fin (rounds + (1 : ℕ))), (0 : ℕ) < (↑j : ℕ) → (↑r.succ : ℕ) < (↑j : ℕ) → (↑j : ℕ) ≤
        (↑p.castSucc : ℕ) → series.data.kind j = some TashkinovExtensionKind.RE := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta cycle hrTerminalLt candidates
      candidatesNonempty p betweenRE pColoring cycleP f hfCycleP currentTree v0 hv0CycleP
      rootedCycle outsideIndices outsideIndicesNonempty g hgRooted j hjPositive hrj hjp
  simp only [Fin.val_succ, Fin.val_castSucc] at hrj hjp
  let q : Fin rounds := ⟨j.val - 1, by omega⟩
  have hqSucc : q.succ = j := by
    apply Fin.ext
    simp [q]
    omega
  rw [← hqSucc]
  apply betweenRE q
  · simp [q]
    omega
  · simp [q]
    omega

private theorem helper_continuation_1518.{u_1, u_2} :
    helperContinuation1518Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k rounds e0 input series r gamma delta hkindr hgammar hdeltar cycle hmeets
      hrTerminalLt candidates candidatesNonempty p hrp betweenRE pColoring cycleP cyclePSupport
      treeSubset pNoRevisiting f hfNotInternal hfCycleP edgeIdentity edgeCycle a ha hfa b hb hfb
      hab hfEndsAB
  let currentTree := TreeSequenceVertexSet (series.data.tree p.succ.castSucc)
  have outsideOnCycle : ∃ y : V, y ∉ currentTree ∧ Sum.inl y ∈ cycleP.walk.support := by
    exact @helper_outsideOnCycle_401 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle)
        (@candidatesNonempty) (@pColoring) (@f) (@hfNotInternal) (@hfCycleP) (@a) (@ha) (@hfa)
        (@b) (@hb) (@hfb) (@hab) (@hfEndsAB)
  obtain ⟨v0, hv0Earlier, hv0Cycle⟩ := hmeets
  have hv0CycleP : Sum.inl v0 ∈ cycleP.walk.support := by
    rw [cyclePSupport]
    exact hv0Cycle
  have hv0Current : v0 ∈ currentTree := treeSubset hv0Earlier
  obtain ⟨outsideVertex, outsideVertexNotCurrent, outsideVertexCycle⟩ := outsideOnCycle
  let rootedCycle := cycleP.walk.rotate (Sum.inl v0) hv0CycleP
  have rootedIsCycle : rootedCycle.IsCycle := cycleP.isCycle.rotate hv0CycleP
  have outsideVertexRooted : Sum.inl outsideVertex ∈ rootedCycle.support := by
    apply (cycleP.walk.mem_support_rotate_iff (Sum.inl v0) hv0CycleP).mpr
    exact outsideVertexCycle
  let outsideIndices : Finset (Fin (rootedCycle.length + 1)) :=
    Finset.univ.filter fun i => ∃ v : V,
      rootedCycle.getVert i.val = Sum.inl v ∧ v ∉ currentTree
  have outsideIndicesNonempty : outsideIndices.Nonempty := by
    exact @helper_outsideIndicesNonempty_437 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle)
        (@hrTerminalLt) (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP)
        (@outsideVertex) (@outsideVertexNotCurrent) (@outsideVertexRooted)
  let firstOutside : Fin (rootedCycle.length + 1) :=
    outsideIndices.min' outsideIndicesNonempty
  have firstOutsideSpec : ∃ y : V,
      rootedCycle.getVert firstOutside.val = Sum.inl y ∧ y ∉ currentTree :=
    (Finset.mem_filter.mp
      (Finset.min'_mem outsideIndices outsideIndicesNonempty)).2
  obtain ⟨y, hyAt, hyOutside⟩ := firstOutsideSpec
  have beforeFirstOutside : ∀ i : Fin (rootedCycle.length + 1),
      i.val < firstOutside.val → ∀ v : V,
        rootedCycle.getVert i.val = Sum.inl v → v ∈ currentTree := by
    exact @helper_beforeFirstOutside_450 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@hrTerminalLt)
        (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP)
        (@outsideIndicesNonempty)
  have firstOutsidePositive : 0 < firstOutside.val := by
    exact @helper_firstOutsidePositive_459 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle)
        (@hrTerminalLt) (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP)
        (@hv0Current) (@outsideIndicesNonempty) (@y) (@hyAt) (@hyOutside)
  have firstOutsideLt : firstOutside.val < rootedCycle.length := by
    exact @helper_firstOutsideLt_469 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@hrTerminalLt)
        (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP) (@hv0Current)
        (@outsideIndicesNonempty) (@y) (@hyAt) (@hyOutside)
  have firstOutsideNotOne : firstOutside.val ≠ 1 := by
    exact @helper_firstOutsideNotOne_481 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@hrTerminalLt)
        (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP)
        (@outsideIndicesNonempty) (@y) (@hyAt) (@firstOutsideLt)
  have firstOutsideAtLeastTwo : 2 ≤ firstOutside.val := by omega
  have crossingAdj := rootedCycle.adj_getVert_succ
    (i := firstOutside.val - 1) (by omega)
  have crossingIndex : firstOutside.val - 1 + 1 = firstOutside.val := by omega
  have crossingEdge : ∃ g : E,
      rootedCycle.getVert (firstOutside.val - 1) = Sum.inr g := by
    exact @helper_crossingEdge_492 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@candidatesNonempty)
        (@pColoring) (@v0) (@hv0CycleP) (@outsideIndicesNonempty) (@y) (@hyAt) (@crossingAdj)
        (@crossingIndex)
  obtain ⟨g, hgAt⟩ := crossingEdge
  have hgy : Incident G y g := by
    rw [crossingIndex, hyAt, hgAt] at crossingAdj
    simpa [TwoColorIncidenceGraph] using crossingAdj.1
  have beforeCrossingAdj := rootedCycle.adj_getVert_succ
    (i := firstOutside.val - 2) (by omega)
  have beforeCrossingIndex : firstOutside.val - 2 + 1 =
      firstOutside.val - 1 := by omega
  have insideVertex : ∃ x : V,
      rootedCycle.getVert (firstOutside.val - 2) = Sum.inl x := by
    exact @helper_insideVertex_508 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@candidatesNonempty)
        (@pColoring) (@v0) (@hv0CycleP) (@outsideIndicesNonempty) (@g) (@hgAt)
        (@beforeCrossingAdj) (@beforeCrossingIndex)
  obtain ⟨x, hxAt⟩ := insideVertex
  have hxCurrent : x ∈ currentTree := by
    exact @helper_hxCurrent_517 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@hrTerminalLt)
        (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP)
        (@outsideIndicesNonempty) (@beforeFirstOutside) (@firstOutsideLt) (@crossingIndex)
        (@beforeCrossingIndex) (@x) (@hxAt)
  have hxg : Incident G x g := by
    rw [beforeCrossingIndex, hgAt, hxAt] at beforeCrossingAdj
    simpa [TwoColorIncidenceGraph] using beforeCrossingAdj.1
  have hxy : x ≠ y := by
    intro h
    exact hyOutside (h ▸ hxCurrent)
  have hgEnds : G.ends g = s(x, y) :=
    edgeIdentity (by simpa [Incident] using hxg) (by simpa [Incident] using hgy) hxy
  have hgBoundary : g ∈ BoundaryEdges G currentTree := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hxCurrent, y, hyOutside, hgEnds⟩
  have hgRooted : Sum.inr g ∈ rootedCycle.support := by
    rw [← hgAt]
    exact rootedCycle.getVert_mem_support (firstOutside.val - 1)
  have hgCycleP : Sum.inr g ∈ cycleP.walk.support := by
    apply (cycleP.walk.mem_support_rotate_iff (Sum.inl v0) hv0CycleP).mp
    exact hgRooted
  have hyCycleP : Sum.inl y ∈ cycleP.walk.support := by
    apply (cycleP.walk.mem_support_rotate_iff (Sum.inl v0) hv0CycleP).mp
    rw [← hyAt]
    exact rootedCycle.getVert_mem_support firstOutside.val
  let returnPrefix := rootedCycle.takeUntil (Sum.inr g) hgRooted
  let returnPath := returnPrefix.reverse
  have returnPrefixPath : returnPrefix.IsPath :=
    rootedIsCycle.isPath_takeUntil hgRooted
  have returnPathIsPath : returnPath.IsPath := returnPrefixPath.reverse
  have returnPrefixPositive : 0 < returnPrefix.length := by
    exact @helper_returnPrefixPositive_550 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle)
        (@hrTerminalLt) (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP)
        (@outsideIndicesNonempty) (@g) (@hgRooted)
  have returnPrefixLength : returnPrefix.length = firstOutside.val - 1 := by
    exact @helper_returnPrefixLength_556 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@hrTerminalLt)
        (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP) (@rootedIsCycle)
        (@outsideIndicesNonempty) (@firstOutsideLt) (@firstOutsideAtLeastTwo) (@crossingIndex)
        (@g) (@hgAt) (@beforeCrossingIndex) (@hgRooted) (@returnPrefixPositive)
  have returnPathOnCycle : ∀ z ∈ returnPath.support,
      z ∈ cycleP.walk.support := by
    exact @helper_returnPathOnCycle_565 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle)
        (@candidatesNonempty) (@pColoring) (@v0) (@hv0CycleP) (@g) (@hgRooted)
  have returnPathInternal : ∀ v, Sum.inl v ∈ returnPath.support →
      v ∈ currentTree := by
    exact @helper_returnPathInternal_572 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@hrTerminalLt)
        (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@v0) (@hv0CycleP)
        (@outsideIndicesNonempty) (@beforeFirstOutside) (@firstOutsideLt) (@crossingIndex) (@g)
        (@beforeCrossingIndex) (@hgRooted) (@returnPrefixLength)
  have interveningForCertificate : ∀ j : Fin (rounds + 1),
      0 < j.val → r.succ.val < j.val → j.val ≤ p.castSucc.val →
        series.data.kind j = some TashkinovExtensionKind.RE := by
    exact @helper_interveningForCertificate_587 (@V) (@E) inferInstance inferInstance
        inferInstance (@G) (@k) (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta)
        (@cycle) (@hrTerminalLt) (@candidatesNonempty) (@betweenRE) (@pColoring) (@f) (@hfCycleP)
        (@v0) (@hv0CycleP) (@outsideIndicesNonempty) (@g) (@hgRooted)
  have cert : RevisitingExtensionCertificate series.data p.castSucc := {
    earlier := r.succ
    earlierPositive := by simp
    earlierAtMost := by simp; omega
    earlierPE := hkindr
    interveningRevisiting := interveningForCertificate
    gamma := gamma
    delta := delta
    earlierGamma := hgammar
    earlierDelta := hdeltar
    cycle := cycleP
    meetsEarlier := by
      exact ⟨v0, hv0Earlier, hv0CycleP⟩
    leavesCurrent := by
      exact ⟨y, by simpa [currentTree] using hyOutside,
        hyCycleP⟩
    edge := g
    edgeOnCycle := hgCycleP
    edgeBoundary := by simpa [currentTree] using hgBoundary
    insideEndpoint := x
    outsideEndpoint := y
    insideInCurrent := by simpa [currentTree] using hxCurrent
    outsideNotCurrent := by simpa [currentTree] using hyOutside
    edgeEnds := hgEnds
    returnVertex := v0
    returnInEarlier := hv0Earlier
    returnPath := returnPath
    returnPathIsPath := returnPathIsPath
    returnPathOnCycle := returnPathOnCycle
    returnPathInternal := by
      intro v hv
      simpa [currentTree] using returnPathInternal v hv
  }
  exact pNoRevisiting ⟨cert⟩

theorem EarlierPECycleFirstNonrevisitingInternal {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (r : Fin rounds) (hrEarlier : r.succ ≠ Fin.last rounds)
    (gamma delta : Fin k)
    (hkindr : series.data.kind r.succ = some TashkinovExtensionKind.PE)
    (hgammar : series.data.gamma r.succ = some gamma)
    (hdeltar : series.data.delta r.succ = some delta)
    (cycle : TwoColorCycle G (series.data.coloring r.succ) gamma delta)
    (hmeets : ∃ v ∈ TreeSequenceVertexSet
        (series.data.tree r.succ.castSucc),
      Sum.inl v ∈ cycle.walk.support)
    (hterminal : series.data.kind (Fin.last rounds) =
      some TashkinovExtensionKind.PE) :
    ∃ p : Fin rounds,
    r.val < p.val ∧
    (series.data.kind p.succ = some TashkinovExtensionKind.SE ∨
      series.data.kind p.succ = some TashkinovExtensionKind.PE) ∧
    (∀ j : Fin rounds,
      r.val < j.val →
        j.val < p.val → series.data.kind j.succ = some TashkinovExtensionKind.RE) ∧
    series.data.coloring p.castSucc = series.data.coloring r.succ ∧
    ∀ f : E,
    Sum.inr f ∈ cycle.walk.support →
    f ∈ InternalEdges G (TreeSequenceVertexSet (series.data.tree p.succ.castSucc)) := by
  classical
  have hrTerminalLt : r.val + 1 < rounds := by
    exact @helper_hrTerminalLt_212 (@rounds) (@r) (@hrEarlier)
  let terminalIndex : Fin rounds := ⟨rounds - 1, by omega⟩
  have terminalIndexSucc : terminalIndex.succ = Fin.last rounds := by
    apply Fin.ext
    simp [terminalIndex]
    omega
  let candidates : Finset (Fin rounds) := Finset.univ.filter fun q =>
    r.val < q.val ∧
      series.data.kind q.succ ≠ some TashkinovExtensionKind.RE
  have terminalMem : terminalIndex ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, by simp [terminalIndex]; omega, ?_⟩
    rw [terminalIndexSucc, hterminal]
    simp
  have candidatesNonempty : candidates.Nonempty := ⟨terminalIndex, terminalMem⟩
  let p : Fin rounds := candidates.min' candidatesNonempty
  have pMem : p ∈ candidates := Finset.min'_mem candidates candidatesNonempty
  have hrp : r.val < p.val := (Finset.mem_filter.mp pMem).2.1
  have pNotRE : series.data.kind p.succ ≠
      some TashkinovExtensionKind.RE := (Finset.mem_filter.mp pMem).2.2
  have betweenRE : ∀ j : Fin rounds, r.val < j.val → j.val < p.val →
      series.data.kind j.succ = some TashkinovExtensionKind.RE := by
    exact @helper_betweenRE_239 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@hrTerminalLt) (@candidatesNonempty)
  have pKind : series.data.kind p.succ = some TashkinovExtensionKind.SE ∨
      series.data.kind p.succ = some TashkinovExtensionKind.PE := by
    exact @helper_pKind_247 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@candidatesNonempty) (@pNotRE)
  have reColoring : ∀ j : Fin rounds,
      series.data.kind j.succ = some TashkinovExtensionKind.RE →
      series.data.coloring j.succ = series.data.coloring j.castSucc := by
    exact @helper_reColoring_116 V E inferInstance inferInstance inferInstance G k rounds e0
        input series r hrTerminalLt candidatesNonempty
  have coloringAlong : ∀ n : ℕ, r.val + 1 ≤ n → n ≤ p.val →
      ∀ q : Fin (rounds + 1), q.val = n →
        series.data.coloring q = series.data.coloring r.succ := by
    exact @helper_coloringAlong_276 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@hrTerminalLt) (@candidatesNonempty)
        (@betweenRE) (@reColoring)
  have pColoring : series.data.coloring p.castSucc =
      series.data.coloring r.succ := by
    exact coloringAlong p.val (by omega) (by omega) p.castSucc rfl
  let cycleP : TwoColorCycle G (series.data.coloring p.castSucc) gamma delta :=
    pColoring.symm ▸ cycle
  have transportedCycleSupport : ∀ (phi psi : PartialEdgeColoring E k)
      (h : phi = psi) (c : TwoColorCycle G psi gamma delta),
      (h.symm ▸ c).walk.support = c.walk.support := by
    intro phi psi h c
    cases h
    rfl
  have cyclePSupport : cycleP.walk.support = cycle.walk.support := by
    exact transportedCycleSupport _ _ pColoring cycle
  have stepVertexSubset : ∀ j : Fin rounds,
      TreeSequenceVertexSet (series.data.tree j.succ.castSucc) ⊆
        TreeSequenceVertexSet (series.data.tree j.succ.succ) := by
    exact @helper_stepVertexSubset_192 V E inferInstance inferInstance
        inferInstance G k rounds e0 input series r hrTerminalLt candidatesNonempty
  have treeAlong : ∀ n : ℕ, r.val ≤ n → n ≤ p.val →
      ∀ q : Fin rounds, q.val = n →
        TreeSequenceVertexSet (series.data.tree r.succ.castSucc) ⊆
          TreeSequenceVertexSet (series.data.tree q.succ.castSucc) := by
    exact @helper_treeAlong_321 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@hrTerminalLt) (@candidatesNonempty)
        (@stepVertexSubset)
  have treeSubset : TreeSequenceVertexSet (series.data.tree r.succ.castSucc) ⊆
      TreeSequenceVertexSet (series.data.tree p.succ.castSucc) :=
    treeAlong p.val (by omega) (by omega) p rfl
  have pNoRevisiting : ¬ Nonempty
      (RevisitingExtensionCertificate series.data p.castSucc) := by
    exact @helper_pNoRevisiting_258 V E inferInstance inferInstance inferInstance G k rounds e0
        input series r hrTerminalLt candidatesNonempty pNotRE
  refine ⟨p, hrp, pKind, betweenRE, pColoring, ?_⟩
  intro f hfCycle
  by_contra hfNotInternal
  have hfCycleP : Sum.inr f ∈ cycleP.walk.support := by
    rw [cyclePSupport]
    exact hfCycle
  have edgeIdentity : ∀ {z : Sym2 V} {a b : V}, a ∈ z → b ∈ z → a ≠ b →
      z = s(a, b) := by
    exact @helper_edgeIdentity_353 (@V)
  let edgeCycle := cycleP.walk.rotate (Sum.inr f) hfCycleP
  have edgeCycleIsCycle : edgeCycle.IsCycle := by
    exact cycleP.isCycle.rotate hfCycleP
  have edgeCycleLength : 3 ≤ edgeCycle.length := edgeCycleIsCycle.three_le_length
  have firstAdj := edgeCycle.adj_getVert_succ (i := 0) (by omega)
  have firstVertex : ∃ a : V, edgeCycle.getVert 1 = Sum.inl a := by
    exact @helper_firstVertex_365 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@candidatesNonempty)
        (@pColoring) (@f) (@hfCycleP) (@firstAdj)
  obtain ⟨a, ha⟩ := firstVertex
  have hfa : Incident G a f := by
    rw [edgeCycle.getVert_zero, ha] at firstAdj
    simpa [edgeCycle, TwoColorIncidenceGraph] using firstAdj.1
  have lastAdj := edgeCycle.adj_getVert_succ
    (i := edgeCycle.length - 1) (by omega)
  have lastVertex : ∃ b : V,
      edgeCycle.getVert (edgeCycle.length - 1) = Sum.inl b := by
    exact @helper_lastVertex_378 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@hrTerminalLt)
        (@candidatesNonempty) (@pColoring) (@f) (@hfCycleP) (@edgeCycleLength) (@lastAdj)
  obtain ⟨b, hb⟩ := lastVertex
  have hfb : Incident G b f := by
    have hidx : edgeCycle.length - 1 + 1 = edgeCycle.length := by omega
    rw [hidx, edgeCycle.getVert_length, hb] at lastAdj
    simpa [edgeCycle, TwoColorIncidenceGraph] using lastAdj.1
  have hab : a ≠ b := by
    exact @helper_hab_392 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@rounds)
        (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@cycle) (@candidatesNonempty)
        (@pColoring) (@f) (@hfCycleP) (@edgeCycleIsCycle) (@a) (@ha) (@b) (@hb)
  have hfEndsAB : G.ends f = s(a, b) :=
    edgeIdentity (by simpa [Incident] using hfa) (by simpa [Incident] using hfb) hab
  exact @helper_continuation_1518 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@rounds) (@e0) (@input) (@series) (@r) (@gamma) (@delta) (@hkindr) (@hgammar) (@hdeltar)
      (@cycle) (@hmeets) (@hrTerminalLt) (@candidatesNonempty) (@hrp) (@betweenRE) (@pColoring)
      (@cyclePSupport) (@treeSubset) (@pNoRevisiting) (@f) (@hfNotInternal) (@hfCycleP)
      (@edgeIdentity) (@a) (@ha) (@hfa) (@b) (@hb) (@hfb) (@hab) (@hfEndsAB)
end GoldbergSeymour

end
