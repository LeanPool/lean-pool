/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseRestorationInvariant

public import LeanPool.GoldbergSeymour.InternalEdges

/-!
# Extension Base Claim43Edge Effects

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem ExtensionBaseClaim43EdgeEffects_transitionFact_62.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] {G
    : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k} {T :
    TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett : ExtendedTashkinovTree G k
    e0 input T generating) (terminalSupport : V) (hterminalSupport : terminalSupport ∈
    TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport hterminalSupport sigmaN),
    ExtensionBaseRestorationInvariant ett terminalSupport hterminalSupport jSlot q sigmaN
    trace → ∀ (f : E), let colors := (ExtensionBaseRestorationIndices ett terminalSupport
    hterminalSupport).biUnion fun (t : Fin ett.rounds) => ett.series.data.stored t.succ; ∀ (b
    : Fin trace.steps), trace.coloring b.succ f ≠ trace.coloring b.castSucc f → ∃ (c : Fin k)
    (d : Fin k), trace.coloring b.castSucc f = some c ∧ trace.coloring b.succ f = some d ∧ c ∈
    colors ∧ d ∈ colors := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN
      trace hinvariant f colors b hdiff
  have hb := hinvariant.2.1 b
  have hslot : trace.slot b ∈ ExtensionBaseRestorationIndices ett
      terminalSupport hterminalSupport := hb.1
  have hactive : trace.slot b ∈ ExtensionBaseActiveIndices ett
      terminalSupport hterminalSupport := by
    have hsplit : trace.slot b ∈ ExtensionBaseActiveIndices ett
        terminalSupport hterminalSupport \
        ExtensionBaseSupportClass ett terminalSupport hterminalSupport
          terminalSupport := by
      simpa [ExtensionBaseRestorationIndices] using hslot
    exact (Finset.mem_sdiff.mp hsplit).1
  have hkind : ett.series.data.kind (trace.slot b).succ =
      some TashkinovExtensionKind.PE := by
    have hh := hactive
    simp only [ExtensionBaseActiveIndices, exists_and_left, Finset.mem_filter, Finset.mem_univ,
        true_and] at hh
    exact hh.2.1
  generalize targetEq : (trace.slot b).succ = target
  have cert := ett.series.certified target
  cases cert with
  | initial triple seedLength initialColoring initialStored initialEdges
      initialKind initialVertex initialOutside initialDelta initialGamma
      initialClosure =>
    have : (trace.slot b).val + 1 = 0 := by simpa using congrArg Fin.val targetEq
    omega
  | SE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternative
      currentColoring currentStored currentEdges currentKind currentVertex
      currentOutside currentDelta currentGamma adjoined adjoinedExactly
      closedExtension orderedExtension strictExtension =>
    have tv := congrArg Fin.val targetEq
    have ciEq : ci = trace.slot b := by
      apply Fin.ext
      simp at tv ⊢
      omega
    subst ci
    rw [currentKind] at hkind
    simp at hkind
  | RE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed available currentColoring currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma adjoined adjoinedExactly closedExtension orderedExtension
      strictExtension =>
    have tv := congrArg Fin.val targetEq
    have ciEq : ci = trace.slot b := by
      apply Fin.ext
      simp at tv ⊢
      omega
    subst ci
    rw [currentKind] at hkind
    simp at hkind
  | PE ci previousProper previousOneUncolored previousClosed
      previousNotStronglyClosed noRevisiting choice seriesAlternativeFails
      gamma gammaRule secondStable secondStableProper
      secondStableOneUncolored secondStableRelation exitWitness
      currentColoring currentProper currentOneUncolored currentStored
      currentEdges currentKind currentVertex currentOutside currentDelta
      currentGamma closedExtension orderedExtension strictExtension =>
    have tv := congrArg Fin.val targetEq
    have ciEq : ci = trace.slot b := by
      apply Fin.ext
      simp at tv ⊢
      omega
    subst ci
    have hstored : ett.series.data.stored (trace.slot b).succ =
        {choice.color, gamma} := currentStored
    have hgamma : trace.gamma b = gamma := by
      apply Option.some.inj
      exact (trace.gammaField b).symm.trans currentGamma
    have hdelta : trace.delta b = choice.color := by
      apply Option.some.inj
      exact (trace.deltaField b).symm.trans currentDelta
    have hcolorMem : ∀ x : Fin k, x ∈
        ett.series.data.stored (trace.slot b).succ → x ∈ colors := by
      intro x hx
      apply Finset.mem_biUnion.mpr
      exact ⟨trace.slot b, hslot, hx⟩
    have hgammaMem : trace.gamma b ∈ colors := by
      apply hcolorMem
      rw [hgamma, hstored]
      simp
    have hdeltaMem : trace.delta b ∈ colors := by
      apply hcolorMem
      rw [hdelta, hstored]
      simp
    have hmem : Sum.inr f ∈ TwoColorComponent G
        (trace.coloring b.castSucc) (trace.gamma b) (trace.delta b)
        (Sum.inl (trace.support b)) := by
      by_contra hn
      have heq : trace.coloring b.succ f = trace.coloring b.castSucc f := by
        rw [trace.transition b]
        simp [TwoColorComponentSwap, hn]
      exact hdiff heq
    have hpre : trace.coloring b.castSucc f = some (trace.gamma b) ∨
        trace.coloring b.castSucc f = some (trace.delta b) := by
      by_cases hg : trace.coloring b.castSucc f = some (trace.gamma b)
      · exact Or.inl hg
      by_cases hd : trace.coloring b.castSucc f = some (trace.delta b)
      · exact Or.inr hd
      have heq : trace.coloring b.succ f = trace.coloring b.castSucc f := by
        rw [trace.transition b]
        simp [TwoColorComponentSwap, hmem, hg, hd]
      exact (hdiff heq).elim
    have hpost : trace.coloring b.succ f = some (trace.delta b) ∨
        trace.coloring b.succ f = some (trace.gamma b) := by
      rcases hpre with hg | hd
      · left
        rw [trace.transition b]
        simp [TwoColorComponentSwap, hmem, hg]
      · right
        rw [trace.transition b]
        simp [TwoColorComponentSwap, hmem, hd]
    rcases hpre with hg | hd <;> rcases hpost with hp | hp
    · exact ⟨trace.gamma b, trace.delta b, hg, hp, hgammaMem, hdeltaMem⟩
    · exact ⟨trace.gamma b, trace.gamma b, hg, hp, hgammaMem, hgammaMem⟩
    · exact ⟨trace.delta b, trace.delta b, hd, hp, hdeltaMem, hdeltaMem⟩
    · exact ⟨trace.delta b, trace.gamma b, hd, hp, hdeltaMem, hgammaMem⟩

private theorem helper_continuation_306.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (hterminalSupport :
        terminalSupport ∈ TreeSequenceVertexSet T) (jSlot q : Fin ett.rounds) (sigmaN :
        PartialEdgeColoring E k) (trace : ExtensionBaseRestorationTrace ett terminalSupport
        hterminalSupport sigmaN), ExtensionBaseRestorationInvariant ett terminalSupport
        hterminalSupport jSlot q sigmaN trace →
    ∀ (f : E),
    let colors : Finset (Fin k) := (ExtensionBaseRestorationIndices ett terminalSupport
        hterminalSupport).biUnion fun (t : Fin ett.rounds) => ett.series.data.stored t.succ; (
    ∀ (b : Fin trace.steps), trace.coloring b.succ f ≠ trace.coloring b.castSucc f →
    ∃ (c : Fin k) (d : Fin k), trace.coloring b.castSucc f = some c ∧ trace.coloring b.succ f =
        some d ∧ c ∈ colors ∧ d ∈ colors) →
    let changes : Finset (Fin trace.steps) :=
        {b : Fin trace.steps | trace.coloring b.succ f ≠ trace.coloring b.castSucc f}; (
    ∀ (b : Fin trace.steps), b ∈ changes ↔ trace.coloring b.succ f ≠ trace.coloring b.castSucc f)
        →
    ∀ (changesNonempty : changes.Nonempty),
    let first : Fin trace.steps := changes.min' changesNonempty;
    let last : Fin trace.steps := changes.max' changesNonempty; first ∈ changes → last ∈ changes →
        (
    ∀ (b : Fin trace.steps), (↑last : ℕ) < (↑b : ℕ) → b ∉ changes) → trace.coloring first.castSucc
        f = sigmaN f → (
    ∀ (n : ℕ) (hn : n ≤ trace.steps), (
    ∀ (b : Fin trace.steps), n ≤ (↑b : ℕ) → b ∉ changes) → trace.coloring (Fin.last trace.steps) f
        = trace.coloring (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (trace.steps + (1 : ℕ))) f) → f ∉
        InternalEdges G (TreeSequenceVertexSet (ett.series.data.tree jSlot.castSucc.succ)) ∧
    ∃ (c : Fin k) (d : Fin k), sigmaN f = some c ∧ trace.coloring (Fin.last trace.steps) f = some
        d ∧ (c ∈ (ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport).biUnion
        fun (t : Fin ett.rounds) => ett.series.data.stored t.succ) ∧ d ∈
        (ExtensionBaseRestorationIndices ett terminalSupport hterminalSupport).biUnion fun (t :
        Fin ett.rounds) => ett.series.data.stored t.succ
                                           := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN
      trace hinvariant f colors transitionFact changes changesSpec changesNonempty first last
      firstMem lastMem afterLast firstValue finalFrom
  have firstData := transitionFact first
    ((changesSpec first).1 firstMem)
  have lastData := transitionFact last
    ((changesSpec last).1 lastMem)
  have lastValue : trace.coloring last.succ f =
      trace.coloring (Fin.last trace.steps) f := by
    have htail := finalFrom (last.val + 1) (by omega)
      (fun b hb => afterLast b (by omega))
    have hi : (⟨last.val + 1, by omega⟩ : Fin (trace.steps + 1)) = last.succ := by
      apply Fin.ext
      simp
    rw [hi] at htail
    exact htail.symm
  rcases firstData with ⟨c, c', hc, hc', hcMem, hc'Mem⟩
  rcases lastData with ⟨d', d, hd', hd, hd'Mem, hdMem⟩
  have initialColor : sigmaN f = some c := firstValue ▸ hc
  have finalColor : trace.coloring (Fin.last trace.steps) f = some d := by
    rw [← lastValue]
    exact hd
  refine ⟨?_, c, d, initialColor, finalColor, hcMem, hdMem⟩
  intro hf
  have internal : ∀ v : V, Incident G v f →
      v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) := by
    simpa [InternalEdges] using hf
  have hb := hinvariant.2.1 first
  have segment := hb.2.2.1
  have exactIntersection := hb.2.2.2.2.2.2.1
  clear hb
  rcases segment with ⟨hlen, vertexEntries, edgeEntries⟩
  let currentTree := ett.series.data.tree (trace.slot first).succ.castSucc
  have vertexTransfer : ∀ v : V,
      v ∈ TreeSequenceVertexSet (ett.series.data.tree jSlot.succ.castSucc) →
      v ∈ TreeSequenceVertexSet currentTree := by
    intro v hv
    simp only [TreeSequenceVertexSet, Fin.castSucc_succ, Finset.mem_image, Finset.mem_univ,
        true_and] at hv ⊢
    rcases hv with ⟨i, hi⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
    exact (vertexEntries i).trans hi
  have edgeMem : Sum.inr f ∈ TwoColorComponent G
      (trace.coloring first.castSucc)
      (trace.gamma first) (trace.delta first)
      (Sum.inl (trace.support first)) := by
    by_contra hn
    have heq : trace.coloring first.succ f = trace.coloring first.castSucc f := by
      rw [trace.transition first]
      simp [TwoColorComponentSwap, hn]
    exact (changesSpec first).1 firstMem heq
  have preKinds : trace.coloring first.castSucc f = some (trace.gamma first) ∨
      trace.coloring first.castSucc f = some (trace.delta first) := by
    by_cases hg : trace.coloring first.castSucc f = some (trace.gamma first)
    · exact Or.inl hg
    by_cases hdg : trace.coloring first.castSucc f = some (trace.delta first)
    · exact Or.inr hdg
    have heq : trace.coloring first.succ f = trace.coloring first.castSucc f := by
      rw [trace.transition first]
      simp [TwoColorComponentSwap, edgeMem, hg, hdg]
    exact ((changesSpec first).1 firstMem heq).elim
  have endpointComponent :
    ∀ v : V, Incident G v f → Sum.inl v ∈ TwoColorComponent G (trace.coloring first.castSucc)
        (trace.gamma first) (trace.delta first) (Sum.inl (trace.support first)) := by
    intro v hv
    let H := TwoColorIncidenceGraph G (trace.coloring first.castSucc)
      (trace.gamma first) (trace.delta first)
    have hadj : H.Adj (Sum.inl v) (Sum.inr f) := by
      simp [H, TwoColorIncidenceGraph, hv, preKinds]
    have hcc : H.connectedComponentMk (Sum.inl v) =
        H.connectedComponentMk (Sum.inr f) :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    have hedge : H.connectedComponentMk (Sum.inr f) =
        H.connectedComponentMk (Sum.inl (trace.support first)) := by
      change H.connectedComponentMk (Sum.inr f) =
        H.connectedComponentMk (Sum.inl (trace.support first)) at edgeMem
      exact edgeMem
    change H.connectedComponentMk (Sum.inl v) =
      H.connectedComponentMk (Sum.inl (trace.support first))
    exact hcc.trans hedge
  have contradiction : ∀ z : Sym2 V, z = G.ends f → False := by
    intro z hz
    induction z using Sym2.inductionOn with
    | _ x y =>
      have hends : G.ends f = s(x, y) := hz.symm
      have hxj : x ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) := by
        exact internal x (by change x ∈ G.ends f; rw [hends]; exact Sym2.mem_mk_left _ _)
      have hyj : y ∈ TreeSequenceVertexSet
          (ett.series.data.tree jSlot.succ.castSucc) := by
        exact internal y (by change y ∈ G.ends f; rw [hends]; exact Sym2.mem_mk_right _ _)
      have hxcur := vertexTransfer x hxj
      have hycur := vertexTransfer y hyj
      have hx : x = trace.support first :=
        (exactIntersection x hxcur).mp (endpointComponent x (by
          change x ∈ G.ends f; rw [hends]; exact Sym2.mem_mk_left _ _))
      have hy : y = trace.support first :=
        (exactIntersection y hycur).mp (endpointComponent y (by
          change y ∈ G.ends f; rw [hends]; exact Sym2.mem_mk_right _ _))
      apply G.loopless f x
      simpa [hx, hy] using hends
  exact contradiction (G.ends f) rfl

theorem ExtensionBaseClaim43EdgeEffects {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (sigmaN : PartialEdgeColoring E k)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace) :
    let rho1 := trace.coloring (Fin.last trace.steps)
    let restorationColors :=
      (ExtensionBaseRestorationIndices ett terminalSupport
        hterminalSupport).biUnion fun t => ett.series.data.stored t.succ
    ∀ f : E, rho1 f ≠ sigmaN f →
      f ∉ InternalEdges G
          (TreeSequenceVertexSet
            (ett.series.data.tree jSlot.succ.castSucc)) ∧
        ∃ c d : Fin k, sigmaN f = some c ∧ rho1 f = some d ∧
          c ∈ restorationColors ∧ d ∈ restorationColors := by
  classical
  dsimp
  intro f hchange
  let colors := (ExtensionBaseRestorationIndices ett terminalSupport
    hterminalSupport).biUnion fun t => ett.series.data.stored t.succ
  have transitionFact : ∀ b : Fin trace.steps,
      trace.coloring b.succ f ≠ trace.coloring b.castSucc f →
      ∃ c d : Fin k, trace.coloring b.castSucc f = some c ∧
        trace.coloring b.succ f = some d ∧ c ∈ colors ∧ d ∈ colors := by
    exact @ExtensionBaseClaim43EdgeEffects_transitionFact_62 V E inferInstance inferInstance
         inferInstance G k e0 input T generating ett terminalSupport
        hterminalSupport jSlot q sigmaN trace hinvariant f
  let changes : Finset (Fin trace.steps) := Finset.univ.filter fun b =>
    trace.coloring b.succ f ≠ trace.coloring b.castSucc f
  have changesSpec (b : Fin trace.steps) : b ∈ changes ↔
      trace.coloring b.succ f ≠ trace.coloring b.castSucc f := by
    simp [changes]
  have changesNonempty : changes.Nonempty := by
    by_contra hn
    have noChange : ∀ b : Fin trace.steps,
        trace.coloring b.succ f = trace.coloring b.castSucc f := by
      intro b
      by_contra hd
      exact hn ⟨b, (changesSpec b).2 hd⟩
    have walk : ∀ n (hn : n ≤ trace.steps),
        trace.coloring ⟨n, Nat.lt_succ_of_le hn⟩ f = sigmaN f := by
      intro n hn
      induction n with
      | zero => simpa using congrFun trace.initialColoring f
      | succ n ih =>
        let b : Fin trace.steps := ⟨n, Nat.lt_of_succ_le hn⟩
        have he := congrFun (trace.transition b) f
        have hp := ih (Nat.le_of_succ_le hn)
        have hq : trace.coloring b.succ f = trace.coloring b.castSucc f := noChange b
        have hprev : b.castSucc = (⟨n, Nat.lt_succ_of_le (Nat.le_of_succ_le hn)⟩ :
            Fin (trace.steps + 1)) := by apply Fin.ext; simp [b]
        rw [hprev, hp] at hq
        have hi : (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (trace.steps + 1)) = b.succ := by
          apply Fin.ext
          simp [b]
        rw [hi, he]
        exact he.symm.trans hq
    have hi : (⟨trace.steps, Nat.lt_succ_of_le le_rfl⟩ : Fin (trace.steps + 1)) =
        Fin.last trace.steps := by apply Fin.ext; simp
    exact hchange (hi ▸ walk trace.steps le_rfl)
  let first := changes.min' changesNonempty
  let last := changes.max' changesNonempty
  have firstMem : first ∈ changes := Finset.min'_mem changes changesNonempty
  have lastMem : last ∈ changes := Finset.max'_mem changes changesNonempty
  have beforeFirst (b : Fin trace.steps) (hlt : b.val < first.val) : b ∉ changes := by
    intro hb
    exact (Nat.not_lt_of_ge (Finset.min'_le changes b hb)) hlt
  have afterLast (b : Fin trace.steps) (hlt : last.val < b.val) : b ∉ changes := by
    intro hb
    exact (Nat.not_lt_of_ge (Finset.le_max' changes b hb)) hlt
  have firstValue : trace.coloring first.castSucc f = sigmaN f := by
    have walk : ∀ n (hn : n ≤ trace.steps),
        (∀ b : Fin trace.steps, b.val < n → b ∉ changes) →
        trace.coloring ⟨n, Nat.lt_succ_of_le hn⟩ f = sigmaN f := by
      intro n hn
      induction n with
      | zero => intro h; simpa using congrFun trace.initialColoring f
      | succ n ih =>
        intro hbefore
        let b : Fin trace.steps := ⟨n, Nat.lt_of_succ_le hn⟩
        have he := congrFun (trace.transition b) f
        have hb : b ∉ changes := hbefore b (by simp [b])
        have hsame : trace.coloring b.succ f = trace.coloring b.castSucc f := by
          apply Classical.byContradiction
          intro hd
          exact hb ((changesSpec b).2 hd)
        have hp := ih (Nat.le_of_succ_le hn) (fun c hc => hbefore c (by omega))
        have hi : (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (trace.steps + 1)) = b.succ := by
          apply Fin.ext
          simp [b]
        have hprev : b.castSucc = (⟨n, Nat.lt_succ_of_le (Nat.le_of_succ_le hn)⟩ :
            Fin (trace.steps + 1)) := by apply Fin.ext; simp [b]
        rw [hi]
        calc
          trace.coloring b.succ f = trace.coloring b.castSucc f := hsame
          _ = sigmaN f := by rw [hprev, hp]
    have hi : (⟨first.val, Nat.lt_succ_of_le first.isLt.le⟩ : Fin (trace.steps + 1)) =
        first.castSucc := by apply Fin.ext; simp
    rw [← hi]
    exact walk first.val first.isLt.le (fun b hb => beforeFirst b hb)
  have finalFrom : ∀ n (hn : n ≤ trace.steps),
      (∀ b : Fin trace.steps, n ≤ b.val → b ∉ changes) →
      trace.coloring (Fin.last trace.steps) f =
        trace.coloring ⟨n, Nat.lt_succ_of_le hn⟩ f := by
    intro n hn
    induction hrem : trace.steps - n using Nat.strong_induction_on generalizing n with
    | h rem ih =>
      intro hafter
      by_cases heq : n = trace.steps
      · subst n
        rfl
      · have hnlt : n < trace.steps := Nat.lt_of_le_of_ne hn heq
        let b : Fin trace.steps := ⟨n, hnlt⟩
        have hsame : trace.coloring b.succ f = trace.coloring b.castSucc f := by
          apply Classical.byContradiction
          intro hd
          exact hafter b (by simp [b]) ((changesSpec b).2 hd)
        have htail := ih (trace.steps - (n + 1)) (by omega) (n + 1)
          (by omega) rfl (fun c hc => hafter c (by omega))
        have he := congrFun (trace.transition b) f
        have hprev : b.castSucc = (⟨n, Nat.lt_succ_of_le (Nat.le_of_lt hnlt)⟩ :
            Fin (trace.steps + 1)) := by apply Fin.ext; simp [b]
        have hnext : (⟨n + 1, by omega⟩ :
            Fin (trace.steps + 1)) = b.succ := by apply Fin.ext; simp [b]
        rw [hnext] at htail
        calc
          trace.coloring (Fin.last trace.steps) f = trace.coloring b.succ f := htail
          _ = trace.coloring b.castSucc f := hsame
          _ = trace.coloring ⟨n, Nat.lt_succ_of_le (Nat.le_of_lt hnlt)⟩ f := by rw [hprev]
  exact @helper_continuation_306 V E inferInstance inferInstance  inferInstance G k
      e0 input T generating ett terminalSupport hterminalSupport jSlot q sigmaN trace hinvariant
      f transitionFact changesSpec changesNonempty firstMem lastMem afterLast firstValue finalFrom
end GoldbergSeymour

end
