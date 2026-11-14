/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Two Color Component Swap Disjoint Pair Graph

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TwoColorComponentSwapDisjointPairGraph {V E : Type*}
      (G : LooplessMultigraph V E) {k : ℕ}
    (phi : PartialEdgeColoring E k) (alpha beta gamma delta : Fin k)
    (z : Sum V E)
    (hdisjoint : Disjoint ({alpha, beta} : Finset (Fin k)) {gamma, delta}) :
    TwoColorIncidenceGraph G (TwoColorComponentSwap G phi gamma delta z) alpha beta =
      TwoColorIncidenceGraph G phi alpha beta := by
  classical
  have hag : alpha ≠ gamma := by
    intro h
    subst gamma
    have := Finset.disjoint_left.mp hdisjoint (Finset.mem_insert_self alpha {beta})
      (Finset.mem_insert_self alpha {delta})
    exact this
  have had : alpha ≠ delta := by
    intro h
    subst delta
    have := Finset.disjoint_left.mp hdisjoint (Finset.mem_insert_self alpha {beta})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self alpha))
    exact this
  have hbg : beta ≠ gamma := by
    intro h
    subst gamma
    have := Finset.disjoint_left.mp hdisjoint
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self beta))
      (Finset.mem_insert_self beta {delta})
    exact this
  have hbd : beta ≠ delta := by
    intro h
    subst delta
    have := Finset.disjoint_left.mp hdisjoint
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self beta))
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self beta))
    exact this
  have hga : gamma ≠ alpha := Ne.symm hag
  have hgb : gamma ≠ beta := Ne.symm hbg
  have hda : delta ≠ alpha := Ne.symm had
  have hdb : delta ≠ beta := Ne.symm hbd
  ext x y
  cases x with
  | inl v =>
      cases y with
      | inl w => simp [TwoColorIncidenceGraph]
      | inr e =>
          simp only [TwoColorIncidenceGraph, and_congr_right_iff]
          intro hinc
          simp only [TwoColorComponentSwap]
          by_cases he : Sum.inr e ∈ TwoColorComponent G phi gamma delta z
          · simp only [ite_eq_left he]
            by_cases heg : phi e = some gamma
            · simp [heg, hga, hgb, hda, hdb]
            · by_cases hed : phi e = some delta
              · have hgd : gamma ≠ delta := by
                  intro hgd
                  apply heg
                  simpa [hgd] using hed
                simp [hed, hgd.symm, hga, hgb, hda, hdb]
              · simp [heg, hed]
          · simp [he]
  | inr e =>
      cases y with
      | inl v =>
          simp only [TwoColorIncidenceGraph, and_congr_right_iff]
          intro hinc
          simp only [TwoColorComponentSwap]
          by_cases he : Sum.inr e ∈ TwoColorComponent G phi gamma delta z
          · simp only [ite_eq_left he]
            by_cases heg : phi e = some gamma
            · simp [heg, hga, hgb, hda, hdb]
            · by_cases hed : phi e = some delta
              · have hgd : gamma ≠ delta := by
                  intro hgd
                  apply heg
                  simpa [hgd] using hed
                simp [hed, hgd.symm, hga, hgb, hda, hdb]
              · simp [heg, hed]
          · simp [he]
      | inr f => simp [TwoColorIncidenceGraph]

end GoldbergSeymour

end
