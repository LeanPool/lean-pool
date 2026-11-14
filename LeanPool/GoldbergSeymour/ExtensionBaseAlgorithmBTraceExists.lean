/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseAlgorithmBTrace

/-!
# Extension Base Algorithm BTrace Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseAlgorithmBTraceExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V) (rho1 : PartialEdgeColoring E k) (u : V)
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (gamma delta : Fin (p + 1) → Fin k) (b : Fin (p + 1))
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
      ett.series.data.delta (indices a).succ = some (delta a)) :
    ∃ trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
        p indices b,
      trace.steps = b.val ∧
        (∀ a : Fin trace.steps,
          (trace.position a).val + a.val + 1 = b.val) ∧
        (∀ a : Fin trace.steps,
          trace.gamma a = gamma (trace.position a)) ∧
        ∀ a : Fin trace.steps,
          trace.delta a = delta (trace.position a) := by
  classical
  let positionNat : ℕ → Fin (p + 1) := fun a =>
    ⟨b.val - 1 - a, by
      have hb := b.isLt
      omega⟩
  let coloringNat : ℕ → PartialEdgeColoring E k := fun n =>
    Nat.rec rho1 (fun a phi =>
      TwoColorComponentSwap G phi (gamma (positionNat a))
        (delta (positionNat a)) (Sum.inl u)) n
  let trace : ExtensionBaseAlgorithmBTrace ett terminalSupport rho1 u
      p indices b := {
    steps := b.val
    position := fun a => positionNat a.val
    slot := fun a => indices (positionNat a.val)
    gamma := fun a => gamma (positionNat a.val)
    delta := fun a => delta (positionNat a.val)
    coloring := fun a => coloringNat a.val
    initialColoring := by simp [coloringNat]
    positionBefore := by
      intro a
      simp only [positionNat]
      omega
    slotIdentity := by intro a; rfl
    enumerates := by
      ext s
      simp only [Finset.mem_image, Finset.mem_univ, true_and,
        ExtensionBaseCaseOneIndices, Finset.mem_filter]
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨positionNat a.val, ?_, ha⟩
        simp only [positionNat]
        omega
      · rintro ⟨q, hq, hqs⟩
        let a : Fin b.val := ⟨b.val - 1 - q.val, by omega⟩
        have hpos : positionNat a.val = q := by
          apply Fin.ext
          simp only [positionNat, a]
          omega
        exact ⟨a, by simpa [hpos] using hqs⟩
    strictlyDescending := by
      intro a c hac
      apply hincreasing
      simp only [positionNat]
      omega
    chosenSupport := by
      intro a
      exact hsupport (positionNat a.val)
    extensionKind := by
      intro a
      exact hkind (positionNat a.val)
    gammaField := by
      intro a
      exact hgamma (positionNat a.val)
    deltaField := by
      intro a
      exact hdelta (positionNat a.val)
    transition := by
      intro a
      simp only [coloringNat, Fin.val_succ, Fin.val_castSucc]
  }
  refine ⟨trace, rfl, ?_, ?_, ?_⟩
  · intro a
    simp only [trace, positionNat]
    omega
  · intro a
    rfl
  · intro a
    rfl

end GoldbergSeymour

end
