/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponentSwapPresentColors

public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBSingleStep
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBTrace
public import LeanPool.GoldbergSeymour.StrongInterchangeabilityKempePreserved

/-!
# Extension Base Algorithm BInduction

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_root_swap_exchange_230.{u_1, u_2} :
    open scoped Classical in ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] {G :
    LooplessMultigraph V E} {k : ℕ} {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin
    k}, alpha ≠ beta → beta ∈ MissingColors G phi v → alpha ∈ PresentColors G phi v → alpha ∈
    MissingColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ∧ beta ∈
    PresentColors G (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v := by
  classical
  intro V E _ _ G k phi v alpha beta hne hbeta halpha
  let _ := Fintype.ofFinite V
  have hbetaNotPresent : beta ∉ PresentColors G phi v := by
    simpa [MissingColors] using hbeta
  obtain ⟨eAlpha, heAlphaIncident, heAlphaColor⟩ := by
    simpa only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] using halpha
  have heAlphaComponent : Sum.inr eAlpha ∈
      TwoColorComponent G phi alpha beta (Sum.inl v) := by
    let H := TwoColorIncidenceGraph G phi alpha beta
    have hadj : H.Adj (Sum.inl v) (Sum.inr eAlpha) := by
      simpa [H, TwoColorIncidenceGraph] using
        And.intro heAlphaIncident (Or.inl heAlphaColor)
    change H.connectedComponentMk (Sum.inr eAlpha) =
      H.connectedComponentMk (Sum.inl v)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      hadj).symm
  constructor
  · unfold MissingColors
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hp
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    rcases hp with ⟨e, hev, heColor⟩
    by_cases heK :
        Sum.inr e ∈ TwoColorComponent G phi alpha beta (Sum.inl v)
    · have heBeta : phi e = some beta := by
        unfold TwoColorComponentSwap at heColor
        rw [ite_eq_left heK] at heColor
        by_cases heAlpha : phi e = some alpha
        · rw [ite_eq_left heAlpha] at heColor
          exact False.elim (hne (Option.some.inj heColor).symm)
        · by_cases heBeta : phi e = some beta
          · exact heBeta
          · rw [ite_eq_right heAlpha, ite_eq_right heBeta] at heColor
            exact False.elim (heAlpha heColor)
      apply hbetaNotPresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨e, hev, heBeta⟩
    · have heOldAlpha : phi e = some alpha := by
        simpa [TwoColorComponentSwap, heK] using heColor
      have heAdj : (TwoColorIncidenceGraph G phi alpha beta).Adj
          (Sum.inl v) (Sum.inr e) := by
        simpa [TwoColorIncidenceGraph] using
          And.intro hev (Or.inl heOldAlpha)
      apply heK
      change (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
          (Sum.inr e) =
        (TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
          (Sum.inl v)
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        heAdj).symm
  · simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨eAlpha, heAlphaIncident, by
      simp [TwoColorComponentSwap, heAlphaComponent, heAlphaColor]⟩

private theorem helper_branch_318.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_
        _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b),
    let L : Finset (Fin ett.rounds) := ExtensionBaseCaseOneIndices ett p indices b;
    let U : Finset (Fin k) := L.biUnion fun (t : Fin ett.rounds) ↦ ett.series.data.stored t.succ;
        (
    ∀ (a : Fin trace.steps), trace.gamma a ≠ trace.delta a) → (
    ∀ (a c : Fin trace.steps), (↑a : ℕ) < (↑c : ℕ) → trace.gamma c ≠ trace.gamma a ∧ trace.gamma c
        ≠ trace.delta a) → (
    ∀ (a c : Fin trace.steps), (↑c : ℕ) = (↑a : ℕ) + (1 : ℕ) → trace.delta c = trace.gamma a) → (
    ∀ (a : Fin trace.steps), trace.slot a ∈ L) → (
    ∀ (a : Fin trace.steps), trace.gamma a ∈ U) → (
    ∀ (a : Fin trace.steps), trace.delta a ∈ U) → (
    ∀ {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {z : V ⊕ E}, IsOneEdgeUncolored phi e0
        → IsOneEdgeUncolored (TwoColorComponentSwap G phi alpha beta z) e0) → (
    ∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta c : Fin k} {z : V ⊕ E}, c ∈
        PresentColors G phi v → c ≠ alpha → c ≠ beta → c ∈ PresentColors G (TwoColorComponentSwap
        G phi alpha beta z) v) → (
    ∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k}, alpha ≠ beta → beta ∈
        MissingColors G phi v → alpha ∈ PresentColors G phi v → alpha ∈ MissingColors G
        (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ∧ beta ∈ PresentColors G
        (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v) → (
    ∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k} {z : V ⊕ E}, alpha ≠ beta →
        alpha ∈ PresentColors G phi v → beta ∈ PresentColors G phi v →
    ∀ c ∈ PresentColors G phi v, c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v)
        →
    ∀ (a : Fin trace.steps), ((IsProperEdgeColoring G (trace.coloring a.castSucc) ∧
        IsOneEdgeUncolored (trace.coloring a.castSucc) e0) ∧ (
    ∀ c ∈ U, c ∈ PresentColors G (trace.coloring a.castSucc) terminalSupport) ∧ (
    ∀ (a_1 : Fin trace.steps), (↑a.castSucc : ℕ) ≤ (↑a_1 : ℕ) → trace.gamma a_1 ∈ PresentColors G
        (trace.coloring a.castSucc) u) ∧ (
    ∀ (a_1 : Fin trace.steps), (↑a_1 : ℕ) = (↑a.castSucc : ℕ) → trace.delta a_1 ∈ MissingColors G
        (trace.coloring a.castSucc) u) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ L → (
    ∀ (a_2 : Fin trace.steps), (↑a_2 : ℕ) < (↑a.castSucc : ℕ) → trace.slot a_2 ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring a.castSucc) gammaS deltaS) → (IsProperEdgeColoring G
        (trace.coloring a.succ) ∧ IsOneEdgeUncolored (trace.coloring a.succ) e0) ∧ (
    ∀ c ∈ U, c ∈ PresentColors G (trace.coloring a.succ) terminalSupport) ∧ (
    ∀ (a_1 : Fin trace.steps), (↑a.succ : ℕ) ≤ (↑a_1 : ℕ) → trace.gamma a_1 ∈ PresentColors G
        (trace.coloring a.succ) u) ∧ (
    ∀ (a_1 : Fin trace.steps), (↑a_1 : ℕ) = (↑a.succ : ℕ) → trace.delta a_1 ∈ MissingColors G
        (trace.coloring a.succ) u) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ L → (
    ∀ (a_2 : Fin trace.steps), (↑a_2 : ℕ) < (↑a.succ : ℕ) → trace.slot a_2 ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring a.succ) gammaS deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace L U trace_colors_ne future_gamma_ne next_delta_eq_gamma slot_mem gamma_mem_U
      delta_mem_U swap_preserves_one swap_present_other root_swap_exchange swap_preserves_present
      a ih
  rcases ih with ⟨hgood, hterminal, hfuture, hnext, hsurvivor⟩
  have hgammaPresent : trace.gamma a ∈
      PresentColors G (trace.coloring a.castSucc) u :=
    hfuture a (by rfl)
  have hdeltaMissing : trace.delta a ∈
      MissingColors G (trace.coloring a.castSucc) u :=
    hnext a rfl
  have hcurrentSI : ETTStrongInterchangeable ett (trace.slot a)
      terminalSupport (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a) := by
    apply hsurvivor (trace.slot a) (trace.gamma a) (trace.delta a)
        (slot_mem a)
    · intro c hc hca
      have hdesc := trace.strictlyDescending c a hc
      rw [hca] at hdesc
      exact (Nat.lt_irrefl _ hdesc)
    · exact trace.chosenSupport a
    · exact trace.gammaField a
    · exact trace.deltaField a
  have hterminalGamma : trace.gamma a ∈
      PresentColors G (trace.coloring a.castSucc) terminalSupport :=
    hterminal (trace.gamma a) (gamma_mem_U a)
  have hterminalDelta : trace.delta a ∈
      PresentColors G (trace.coloring a.castSucc) terminalSupport :=
    hterminal (trace.delta a) (delta_mem_U a)
  have hstep := ExtensionBaseAlgorithmBSingleStep ett (trace.slot a)
    terminalSupport (trace.coloring a.castSucc) u (trace.gamma a)
    (trace.delta a) hgood.1 hcurrentSI hdeltaMissing hgammaPresent
    hterminalGamma hterminalDelta
  have hproperNext : IsProperEdgeColoring G (trace.coloring a.succ) := by
    rw [trace.transition a]
    exact TwoColorComponentSwapProper G (trace.coloring a.castSucc)
      (trace.gamma a) (trace.delta a) (trace_colors_ne a) hgood.1
      (Sum.inl u)
  have honeNext : IsOneEdgeUncolored (trace.coloring a.succ) e0 := by
    rw [trace.transition a]
    exact swap_preserves_one hgood.2
  have hexchange := root_swap_exchange (trace_colors_ne a)
    hdeltaMissing hgammaPresent
  rw [← trace.transition a] at hexchange
  refine ⟨⟨hproperNext, honeNext⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hp := swap_preserves_present (z := Sum.inl u)
      (trace_colors_ne a)
      hterminalGamma hterminalDelta c (hterminal c hc)
    rw [← trace.transition a] at hp
    exact hp
  · intro c hac
    have hac' : a.val < c.val := by
      change a.val + 1 ≤ c.val at hac
      omega
    have hne := future_gamma_ne a c hac'
    have hp := swap_present_other (z := Sum.inl u)
      (hfuture c (Nat.le_of_lt hac'))
      hne.1 hne.2
    rw [← trace.transition a] at hp
    exact hp
  · intro c hca
    rw [next_delta_eq_gamma a c (by simpa using hca)]
    exact hexchange.1
  · intro s gammaS deltaS hs hnot hsupport hgammaS hdeltaS
    have hsOld : ETTStrongInterchangeable ett s terminalSupport
        (trace.coloring a.castSucc) gammaS deltaS := by
      apply hsurvivor s gammaS deltaS hs
      · intro c hc
        apply hnot c
        change c.val < a.val at hc
        change c.val < a.val + 1
        omega
      · exact hsupport
      · exact hgammaS
      · exact hdeltaS
    have hsImage : s ∈ Finset.univ.image trace.slot := by
      rw [trace.enumerates]
      exact hs
    rcases Finset.mem_image.mp hsImage with ⟨c, -, hc⟩
    have hac : a.val < c.val := by
      by_contra hle
      have hca : c.val < a.succ.val := by
        simp
        omega
      exact hnot c hca hc
    have hslt : s.val < (trace.slot a).val := by
      have hdesc := trace.strictlyDescending a c hac
      simpa [hc] using hdesc
    have hpreserved := StrongInterchangeabilityKempePreserved ett s
      (trace.slot a) terminalSupport terminalSupport gammaS deltaS
      (trace.gamma a) (trace.delta a) (trace.coloring a.castSucc)
      (Sum.inl u) hgood.1 hgood.2 hgammaS hdeltaS
      (trace.gammaField a) (trace.deltaField a) (Or.inr hslt)
      (by intro hneSupport; exact (hneSupport rfl).elim) hstep.1
      hcurrentSI hsOld
    rw [trace.transition a]
    exact hpreserved.2.2

private theorem helper_invariant_383.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds)
        (gamma delta : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b), (
    ∀ (a : Fin trace.steps), (↑(trace.position a) : ℕ) + (↑a : ℕ) + (1 : ℕ) = (↑b : ℕ)) → (
    ∀ (a : Fin trace.steps), trace.delta a = delta (trace.position a)) → IsProperEdgeColoring G
        rho1 → IsOneEdgeUncolored rho1 e0 → (
    ∀ (a : Fin p), gamma a.succ = delta a.castSucc) → gamma b ∈ MissingColors G rho1 u →
    let L : Finset (Fin ett.rounds) := ExtensionBaseCaseOneIndices ett p indices b;
    let U : Finset (Fin k) := L.biUnion fun (t : Fin ett.rounds) => ett.series.data.stored t.succ;
        (
    ∀ (a : Fin trace.steps), trace.gamma a ≠ trace.delta a) → (
    ∀ (a c : Fin trace.steps), (↑a : ℕ) < (↑c : ℕ) → trace.gamma c ≠ trace.gamma a ∧ trace.gamma c
        ≠ trace.delta a) → (
    ∀ (a c : Fin trace.steps), (↑c : ℕ) = (↑a : ℕ) + (1 : ℕ) → trace.delta c = trace.gamma a) → (
    ∀ (a : Fin trace.steps), trace.slot a ∈ L) → (
    ∀ (a : Fin trace.steps), trace.gamma a ∈ U) → (
    ∀ (a : Fin trace.steps), trace.delta a ∈ U) → (
    ∀ c ∈ U, c ∈ PresentColors G rho1 terminalSupport) → (
    ∀ (a : Fin trace.steps), trace.gamma a ∈ PresentColors G rho1 u) → (
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ L → ett.series.data.gamma s.succ = some
        gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett s
        terminalSupport rho1 gammaS deltaS) → (
    ∀ {phi : PartialEdgeColoring E k} {alpha beta : Fin k} {z : V ⊕ E}, IsOneEdgeUncolored phi e0
        → IsOneEdgeUncolored (TwoColorComponentSwap G phi alpha beta z) e0) → (
    ∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta c : Fin k} {z : V ⊕ E}, c ∈
        PresentColors G phi v → c ≠ alpha → c ≠ beta → c ∈ PresentColors G (TwoColorComponentSwap
        G phi alpha beta z) v) → (
    ∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k}, alpha ≠ beta → beta ∈
        MissingColors G phi v → alpha ∈ PresentColors G phi v → alpha ∈ MissingColors G
        (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v ∧ beta ∈ PresentColors G
        (TwoColorComponentSwap G phi alpha beta (Sum.inl v)) v) → (
    ∀ {phi : PartialEdgeColoring E k} {v : V} {alpha beta : Fin k} {z : V ⊕ E}, alpha ≠ beta →
        alpha ∈ PresentColors G phi v → beta ∈ PresentColors G phi v →
    ∀ c ∈ PresentColors G phi v, c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v)
        →
    ∀ (n : Fin (trace.steps + (1 : ℕ))), (IsProperEdgeColoring G (trace.coloring n) ∧
        IsOneEdgeUncolored (trace.coloring n) e0) ∧ (
    ∀ c ∈ U, c ∈ PresentColors G (trace.coloring n) terminalSupport) ∧ (
    ∀ (a : Fin trace.steps), (↑n : ℕ) ≤ (↑a : ℕ) → trace.gamma a ∈ PresentColors G (trace.coloring
        n) u) ∧ (
    ∀ (a : Fin trace.steps), (↑a : ℕ) = (↑n : ℕ) → trace.delta a ∈ MissingColors G (trace.coloring
        n) u) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ L → (
    ∀ (a : Fin trace.steps), (↑a : ℕ) < (↑n : ℕ) → trace.slot a ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring n) gammaS deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace hposition htraceDelta hproper hone hchain hselected L U trace_colors_ne
      future_gamma_ne next_delta_eq_gamma slot_mem gamma_mem_U delta_mem_U
      initial_terminal_present initial_gamma_present initial_survivor swap_preserves_one
      swap_present_other root_swap_exchange swap_preserves_present n
  induction n using Fin.induction with
  | zero =>
      rw [trace.initialColoring]
      refine ⟨⟨hproper, hone⟩, initial_terminal_present,
        (fun a _ => initial_gamma_present a), ?_, ?_⟩
      · intro a ha
        have hpa := hposition a
        have hq : (trace.position a).val < p := by
          have hb := b.isLt
          omega
        let q : Fin p := ⟨(trace.position a).val, hq⟩
        have hpos : trace.position a = q.castSucc := by
          apply Fin.ext
          rfl
        have hbq : b = q.succ := by
          apply Fin.ext
          change b.val = (trace.position a).val + 1
          have ha0 : a.val = 0 := ha
          omega
        rw [htraceDelta a, hpos, ← hchain q, ← hbq]
        exact hselected
      · intro s gammaS deltaS hs _ _ hgs hds
        exact initial_survivor s gammaS deltaS hs hgs hds
  | succ a ih =>
      exact @helper_branch_318 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
          (@e0) (@input) (@T) (@generating) (@ett) (@terminalSupport) (@rho1) (@u) (@p)
          (@indices) (@gamma) (@delta) (@b) (@trace) (@trace_colors_ne) (@future_gamma_ne)
          (@next_delta_eq_gamma) (@slot_mem) (@gamma_mem_U) (@delta_mem_U) (@swap_preserves_one)
          (@swap_present_other) (@root_swap_exchange) (@swap_preserves_present) (@a) (@ih)
private theorem helper_branch_626.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E]
        {G : LooplessMultigraph V E} {k : ℕ} {e0 : E} {input : PartialEdgeColoring E k}
        {T : TreeSequence G e0} {generating : PartialEdgeColoring E k} (ett :
        ExtendedTashkinovTree G k e0 input T generating) (terminalSupport : V) (rho1 :
        PartialEdgeColoring E k) (u : V) (p : ℕ) (indices : Fin (p + (1 : ℕ)) → Fin ett.rounds) (_
        _ : Fin (p + (1 : ℕ)) → Fin k) (b : Fin (p + (1 : ℕ))) (trace :
        ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u p indices b),
    let L : Finset (Fin ett.rounds) := ExtensionBaseCaseOneIndices ett p indices b;
    let U : Finset (Fin k) := L.biUnion fun (t : Fin ett.rounds) => ett.series.data.stored t.succ;
        (
    ∀ (a : Fin trace.steps), trace.slot a ∈ L) → (
    ∀ (a : Fin trace.steps), trace.gamma a ∈ U) → (
    ∀ (a : Fin trace.steps), trace.delta a ∈ U) → (
    ∀ (n : Fin (trace.steps + (1 : ℕ))), (IsProperEdgeColoring G (trace.coloring n) ∧
        IsOneEdgeUncolored (trace.coloring n) e0) ∧ (
    ∀ c ∈ U, c ∈ PresentColors G (trace.coloring n) terminalSupport) ∧ (
    ∀ (a : Fin trace.steps), (↑n : ℕ) ≤ (↑a : ℕ) → trace.gamma a ∈ PresentColors G (trace.coloring
        n) u) ∧ (
    ∀ (a : Fin trace.steps), (↑a : ℕ) = (↑n : ℕ) → trace.delta a ∈ MissingColors G (trace.coloring
        n) u) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ L → (
    ∀ (a : Fin trace.steps), (↑a : ℕ) < (↑n : ℕ) → trace.slot a ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring n) gammaS deltaS) →
    ∀ (a : Fin trace.steps), trace.delta a ∈ MissingColors G (trace.coloring a.castSucc) u ∧
        trace.gamma a ∈ PresentColors G (trace.coloring a.castSucc) u ∧ trace.gamma a ∈
        PresentColors G (trace.coloring a.castSucc) terminalSupport ∧ trace.delta a ∈
        PresentColors G (trace.coloring a.castSucc) terminalSupport ∧ ETTStrongInterchangeable ett
        (trace.slot a) terminalSupport (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a)
        ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k), s ∈ ExtensionBaseCaseOneIndices ett p indices
        b → (
    ∀ (c : Fin trace.steps), (↑c : ℕ) ≤ (↑a : ℕ) → trace.slot c ≠ s) →
        ett.series.data.chosenVertex s.succ = some terminalSupport → ett.series.data.gamma s.succ
        = some gammaS → ett.series.data.delta s.succ = some deltaS → ETTStrongInterchangeable ett
        s terminalSupport (trace.coloring a.succ) gammaS deltaS := by
  classical
  intro V E _ _ _ G k e0 input T generating ett terminalSupport rho1 u p indices gamma delta b
      trace L U slot_mem gamma_mem_U delta_mem_U invariant a
  rcases invariant a.castSucc with
    ⟨hgood, hterminal, hfuture, hnext, hsurvivor⟩
  have hmissing := hnext a rfl
  have hpresent := hfuture a (by rfl)
  have hterminalGamma := hterminal (trace.gamma a) (gamma_mem_U a)
  have hterminalDelta := hterminal (trace.delta a) (delta_mem_U a)
  have hsi : ETTStrongInterchangeable ett (trace.slot a) terminalSupport
      (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) := by
    apply hsurvivor (trace.slot a) (trace.gamma a) (trace.delta a)
        (slot_mem a)
    · intro c hc hca
      have hdesc := trace.strictlyDescending c a hc
      rw [hca] at hdesc
      exact (Nat.lt_irrefl _ hdesc)
    · exact trace.chosenSupport a
    · exact trace.gammaField a
    · exact trace.deltaField a
  refine ⟨hmissing, hpresent, hterminalGamma, hterminalDelta, hsi, ?_⟩
  intro s gammaS deltaS hs hnot hsupport hgammaS hdeltaS
  have hnextInvariant := invariant a.succ
  exact hnextInvariant.2.2.2.2 s gammaS deltaS hs (by
    intro c hc
    apply hnot c
    change c.val < a.val + 1 at hc
    omega) hsupport hgammaS hdeltaS

theorem ExtensionBaseAlgorithmBInduction {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V) (rho1 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
    (trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
      p indices b)
    (_ : trace.steps = b.val)
    (hposition : ∀ a : Fin trace.steps,
      (trace.position a).val + a.val + 1 = b.val)
    (htraceGamma : ∀ a : Fin trace.steps,
      trace.gamma a = gamma (trace.position a))
    (htraceDelta : ∀ a : Fin trace.steps,
      trace.delta a = delta (trace.position a))
    (hproper : IsProperEdgeColoring G rho1)
    (hone : IsOneEdgeUncolored rho1 e0)
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hselected : gamma b ∈ MissingColors G rho1 u)
    (hminimal : ∀ a : Fin (p + 1), a.val < b.val →
      gamma a ∉ MissingColors G rho1 u)
    (hinitialSI : ∀ a : Fin (p + 1), a.val < b.val →
      ETTStrongInterchangeable ett (indices a) terminalSupport rho1
        (gamma a) (delta a))
    (hterminalNoMissing :
      MissingColors G rho1 terminalSupport ∩
        ((ExtensionBaseCaseOneIndices ett p indices b).biUnion
          fun t => ett.series.data.stored t.succ) = ∅)
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a}) :
    (∀ a : Fin (trace.steps + 1),
      IsProperEdgeColoring G (trace.coloring a) ∧
        IsOneEdgeUncolored (trace.coloring a) e0) ∧
    (∀ a : Fin trace.steps,
      trace.delta a ∈ MissingColors G (trace.coloring a.castSucc) u ∧
        trace.gamma a ∈ PresentColors G (trace.coloring a.castSucc) u ∧
        trace.gamma a ∈
          PresentColors G (trace.coloring a.castSucc) terminalSupport ∧
        trace.delta a ∈
          PresentColors G (trace.coloring a.castSucc) terminalSupport ∧
        ETTStrongInterchangeable ett (trace.slot a) terminalSupport
          (trace.coloring a.castSucc) (trace.gamma a) (trace.delta a) ∧
        ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
          s ∈ ExtensionBaseCaseOneIndices ett p indices b →
          (∀ c : Fin trace.steps, c.val ≤ a.val → trace.slot c ≠ s) →
          ett.series.data.chosenVertex s.succ = some terminalSupport →
          ett.series.data.gamma s.succ = some gammaS →
          ett.series.data.delta s.succ = some deltaS →
          ETTStrongInterchangeable ett s terminalSupport
            (trace.coloring a.succ) gammaS deltaS) ∧
    ∀ (s : Fin ett.rounds) (gammaS deltaS : Fin k),
      s ∈ ExtensionBaseCaseOneIndices ett p indices b →
      (∀ a : Fin trace.steps, trace.slot a ≠ s) →
      ett.series.data.chosenVertex s.succ = some terminalSupport →
      ett.series.data.gamma s.succ = some gammaS →
      ett.series.data.delta s.succ = some deltaS →
      ETTStrongInterchangeable ett s terminalSupport
        (trace.coloring (Fin.last trace.steps)) gammaS deltaS := by
  classical
  let L := ExtensionBaseCaseOneIndices ett p indices b
  let U := L.biUnion fun t => ett.series.data.stored t.succ
  let colorChain : Fin (p + 2) → Fin k := Fin.cons (gamma 0) delta
  have gamma_eq_chain (r : Fin (p + 1)) :
      gamma r = colorChain r.castSucc := by
    cases r using Fin.cases with
    | zero => simp [colorChain]
    | succ q => simpa [colorChain] using hchain q
  have delta_eq_chain (r : Fin (p + 1)) :
      delta r = colorChain r.succ := by
    simp [colorChain]
  have trace_colors_ne (a : Fin trace.steps) :
      trace.gamma a ≠ trace.delta a := by
    rw [htraceGamma a, htraceDelta a, gamma_eq_chain, delta_eq_chain]
    intro h
    have hi := hdistinct h
    have hv := congrArg Fin.val hi
    simp at hv
  have future_gamma_ne (a c : Fin trace.steps) (hac : a.val < c.val) :
      trace.gamma c ≠ trace.gamma a ∧ trace.gamma c ≠ trace.delta a := by
    rw [htraceGamma c, htraceGamma a, htraceDelta a,
      gamma_eq_chain, gamma_eq_chain, delta_eq_chain]
    constructor <;> intro h
    · have hi := hdistinct h
      have hv := congrArg Fin.val hi
      have ha := hposition a
      have hc := hposition c
      simp at hv
      omega
    · have hi := hdistinct h
      have hv := congrArg Fin.val hi
      have ha := hposition a
      have hc := hposition c
      simp at hv
      omega
  have next_delta_eq_gamma (a c : Fin trace.steps)
      (hca : c.val = a.val + 1) : trace.delta c = trace.gamma a := by
    have ha := hposition a
    have hc := hposition c
    have hq : (trace.position c).val < p := by
      have hpos := (trace.position a).isLt
      omega
    let q : Fin p := ⟨(trace.position c).val, hq⟩
    have hpc : trace.position c = q.castSucc := by
      apply Fin.ext
      rfl
    have hpa : trace.position a = q.succ := by
      apply Fin.ext
      simp [q]
      omega
    rw [htraceDelta c, htraceGamma a, hpc, hpa]
    exact (hchain q).symm
  have slot_mem (a : Fin trace.steps) : trace.slot a ∈ L := by
    change trace.slot a ∈ ExtensionBaseCaseOneIndices ett p indices b
    rw [← trace.enumerates]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have gamma_mem_U (a : Fin trace.steps) : trace.gamma a ∈ U := by
    apply Finset.mem_biUnion.mpr
    refine ⟨trace.slot a, slot_mem a, ?_⟩
    rw [trace.slotIdentity a, hstored (trace.position a),
      ← htraceGamma a]
    simp
  have delta_mem_U (a : Fin trace.steps) : trace.delta a ∈ U := by
    apply Finset.mem_biUnion.mpr
    refine ⟨trace.slot a, slot_mem a, ?_⟩
    rw [trace.slotIdentity a, hstored (trace.position a),
      ← htraceDelta a]
    simp
  have initial_terminal_present (c : Fin k) (hc : c ∈ U) :
      c ∈ PresentColors G rho1 terminalSupport := by
    have hn : c ∉ MissingColors G rho1 terminalSupport := by
      intro hm
      have hi : c ∈ MissingColors G rho1 terminalSupport ∩ U :=
        Finset.mem_inter.mpr ⟨hm, hc⟩
      change c ∈ MissingColors G rho1 terminalSupport ∩
        ((ExtensionBaseCaseOneIndices ett p indices b).biUnion
          fun t => ett.series.data.stored t.succ) at hi
      rw [hterminalNoMissing] at hi
      simp at hi
    simpa [MissingColors] using hn
  have initial_gamma_present (a : Fin trace.steps) :
      trace.gamma a ∈ PresentColors G rho1 u := by
    have hn := hminimal (trace.position a) (trace.positionBefore a)
    rw [← htraceGamma a] at hn
    simpa [MissingColors] using hn
  have initial_survivor (s : Fin ett.rounds) (gammaS deltaS : Fin k)
      (hs : s ∈ L)
      (hgs : ett.series.data.gamma s.succ = some gammaS)
      (hds : ett.series.data.delta s.succ = some deltaS) :
      ETTStrongInterchangeable ett s terminalSupport rho1 gammaS deltaS := by
    change s ∈ ExtensionBaseCaseOneIndices ett p indices b at hs
    rw [← trace.enumerates] at hs
    rcases Finset.mem_image.mp hs with ⟨a, -, ha⟩
    have hgammaS : gammaS = trace.gamma a := by
      apply Option.some.inj
      rw [← hgs, ← ha]
      exact trace.gammaField a
    have hdeltaS : deltaS = trace.delta a := by
      apply Option.some.inj
      rw [← hds, ← ha]
      exact trace.deltaField a
    have hsi := hinitialSI (trace.position a) (trace.positionBefore a)
    rw [← trace.slotIdentity a, ← htraceGamma a, ← htraceDelta a] at hsi
    rw [ha] at hsi
    simpa [hgammaS, hdeltaS] using hsi
  have swap_preserves_one {phi : PartialEdgeColoring E k}
      {alpha beta : Fin k} {z : Sum V E}
      (h : IsOneEdgeUncolored phi e0) :
      IsOneEdgeUncolored (TwoColorComponentSwap G phi alpha beta z) e0 := by
    constructor
    · simp [TwoColorComponentSwap, h.1]
    · intro e he0
      obtain ⟨c, hc⟩ := h.2 e he0
      by_cases heK :
          Sum.inr e ∈ TwoColorComponent G phi alpha beta z
      · by_cases heAlpha : phi e = some alpha
        · exact ⟨beta, by
            simp [TwoColorComponentSwap, heK, heAlpha]⟩
        · by_cases heBeta : phi e = some beta
          · exact ⟨alpha, by
              simp [TwoColorComponentSwap, heK, heBeta]⟩
          · exact ⟨c, by
              simpa [TwoColorComponentSwap, heK, heAlpha, heBeta] using hc⟩
      · exact ⟨c, by
          simpa [TwoColorComponentSwap, heK] using hc⟩
  have swap_present_other {phi : PartialEdgeColoring E k} {v : V}
      {alpha beta c : Fin k} {z : Sum V E}
      (hc : c ∈ PresentColors G phi v) (hca : c ≠ alpha)
      (hcb : c ≠ beta) :
      c ∈ PresentColors G (TwoColorComponentSwap G phi alpha beta z) v := by
    exact TwoColorComponentSwapPreservesOther hc hca hcb
  have root_swap_exchange := @helper_root_swap_exchange_230 V E inferInstance inferInstance G k
  have swap_preserves_present {phi : PartialEdgeColoring E k} {v : V}
      {alpha beta : Fin k} {z : Sum V E}
      (hne : alpha ≠ beta)
      (halpha : alpha ∈ PresentColors G phi v)
      (hbeta : beta ∈ PresentColors G phi v) :
      ∀ c : Fin k, c ∈ PresentColors G phi v →
        c ∈ PresentColors G
          (TwoColorComponentSwap G phi alpha beta z) v := by
    exact TwoColorComponentSwapPreservesPresent halpha hbeta
  have invariant := @helper_invariant_383 V E inferInstance inferInstance inferInstance G k e0 input
      T generating ett terminalSupport rho1 u p indices gamma delta b trace hposition htraceDelta
      hproper hone hchain hselected trace_colors_ne future_gamma_ne next_delta_eq_gamma slot_mem
      gamma_mem_U delta_mem_U initial_terminal_present initial_gamma_present initial_survivor
      swap_preserves_one swap_present_other root_swap_exchange swap_preserves_present
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (invariant a).1
  · exact @helper_branch_626 V E inferInstance inferInstance inferInstance G k e0 input T
      generating ett terminalSupport rho1 u p indices gamma delta b trace slot_mem gamma_mem_U
      delta_mem_U invariant
  · intro s gammaS deltaS hs hnot _ _ _
    change s ∈ L at hs
    have hsImage : s ∈ Finset.univ.image trace.slot := by
      rw [trace.enumerates]
      exact hs
    rcases Finset.mem_image.mp hsImage with ⟨a, -, ha⟩
    exact False.elim (hnot a ha)

end GoldbergSeymour

end
