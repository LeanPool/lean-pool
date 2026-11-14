/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveSetup
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Shared facts for ScheideDeletedMissingReplacementInternal

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ScheideDeletedMissingReplacementInternal

open scoped Sym2

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev phiDAlpha0Statement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
          G e0) (C : ScheideReducedConfiguration G k e0 phi T) (D : ScheideDefectiveSetup G k e0 phi
          T C) (d : ↥(DefectiveColors G phi (TreeSequenceVertexSet T))),
      let gamma : Fin k := C.gamma (D.gammaIndex d);
      let phiD : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma (↑d : Fin k) (Sum.inl
          (D.v0 d)); gamma ≠ (↑d : Fin k) → D.alpha0 ≠ gamma → D.alpha0 ≠ (↑d : Fin k) →
      ∀ (f : E), phiD f = some D.alpha0 ↔ phi f = some D.alpha0

/-- A common proof used by the branches of this transport or construction argument. -/
theorem phiDAlpha0.{u_1, u_2} : phiDAlpha0Statement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T C D d gamma phiD hGammaDelta hAlpha0Gamma hAlpha0Delta f
  simp only [phiD, TwoColorComponentSwap]
  by_cases hf : Sum.inr f ∈
      TwoColorComponent G phi gamma d.1 (Sum.inl (D.v0 d))
  · by_cases hfg : phi f = some gamma
    · simp only [hf, ite_eq_left, hfg, Option.some.injEq]
      constructor
      · intro h
        exact False.elim (hAlpha0Delta h.symm)
      · intro h
        exact False.elim (hAlpha0Gamma h.symm)
    · by_cases hfd : phi f = some d.1
      · simp [hf, hfd, hGammaDelta.symm, hAlpha0Gamma.symm, hAlpha0Delta.symm]
      · simp [hf, hfg, hfd]
  · simp [hf]

end GoldbergSeymour.SharedFacts.ScheideDeletedMissingReplacementInternal

end
