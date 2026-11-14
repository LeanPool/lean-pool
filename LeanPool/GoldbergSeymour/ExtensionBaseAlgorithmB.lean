/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBInduction
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBInvariant
public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBTraceExists

/-!
# Extension Base Algorithm B

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseAlgorithmB {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V) (jSlot : Fin ett.rounds)
    (rho1 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
    (hproper : IsProperEdgeColoring G rho1)
    (hone : IsOneEdgeUncolored rho1 e0)
    (hincreasing : ∀ a c, a.val < c.val →
      (indices a).val < (indices c).val)
    (hsupport : ∀ a,
      ett.series.data.chosenVertex (indices a).succ = some terminalSupport)
    (hkind : ∀ a,
      ett.series.data.kind (indices a).succ =
        some TashkinovExtensionKind.PE)
    (hgamma : ∀ a,
      ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a,
      ett.series.data.delta (indices a).succ = some (delta a))
    (hchain : ∀ a : Fin p, gamma a.succ = delta a.castSucc)
    (hdistinct : Function.Injective (Fin.cons (gamma 0) delta))
    (hselected : gamma b ∈ MissingColors G rho1 u)
    (hminimal : ∀ a : Fin (p + 1), a.val < b.val →
      gamma a ∉ MissingColors G rho1 u)
    (hinitialSI : ∀ a : Fin (p + 1), a.val < b.val →
      ETTStrongInterchangeable ett (indices a) terminalSupport rho1
        (gamma a) (delta a))
    (hTjInitial : ∀ a : Fin (p + 1), a.val < b.val →
      TreeSequenceInitialSegment
        (ett.series.data.tree jSlot.succ.castSucc)
        (ett.series.data.tree (indices a).succ.castSucc))
    (hterminalNoMissing :
      MissingColors G rho1 terminalSupport ∩
        ((ExtensionBaseCaseOneIndices ett p indices b).biUnion
          fun t => ett.series.data.stored t.succ) = ∅)
    (hstored : ∀ a,
      ett.series.data.stored (indices a).succ = {gamma a, delta a}) :
    ∃ trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
        p indices b,
      ExtensionBaseAlgorithmBInvariant ett terminalSupport jSlot rho1 u
        p indices b trace := by
  classical
  obtain ⟨trace, hsteps, hposition, htraceGamma, htraceDelta⟩ :=
    ExtensionBaseAlgorithmBTraceExists ett terminalSupport rho1 u p indices
      gamma delta b hincreasing hsupport hkind hgamma hdelta
  refine ⟨trace, ?_⟩
  obtain ⟨hcoloring, hstate, hfinal⟩ :=
    ExtensionBaseAlgorithmBInduction ett terminalSupport rho1 u p indices
      gamma delta b trace hsteps hposition htraceGamma htraceDelta hproper
      hone hchain hdistinct hselected hminimal hinitialSI hterminalNoMissing
      hstored
  unfold ExtensionBaseAlgorithmBInvariant
  refine ⟨hcoloring, ?_, hfinal⟩
  intro a
  obtain ⟨hmissing, hpresent, hterminalGamma, hterminalDelta, hsi,
      hsurvivors⟩ := hstate a
  have hstep := ExtensionBaseAlgorithmBSingleStep ett (trace.slot a)
    terminalSupport (trace.coloring a.castSucc) u (trace.gamma a)
    (trace.delta a) (hcoloring a.castSucc).1 hsi hmissing hpresent
    hterminalGamma hterminalDelta
  refine ⟨?_, hmissing, hstep.1, hstep.2.1, hstep.2.2, hsurvivors⟩
  rw [trace.slotIdentity a]
  exact hTjInitial (trace.position a) (trace.positionBefore a)

end GoldbergSeymour

end
