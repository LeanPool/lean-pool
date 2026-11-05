/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovSeries
public import LeanPool.GoldbergSeymour.TashkinovSeriesStepPrefix

/-!
# Tashkinov Series Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovSeriesPrefix {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq E] (G : LooplessMultigraph V E) (k rounds : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k)
    (series : TashkinovSeries G k rounds e0 input)
    (m : ℕ) (hm : m ≤ rounds) :
    ∃ restricted : TashkinovSeries G k m e0 input,
      restricted.data = TashkinovSeriesDataPrefix m hm series.data ∧
      ∀ i : Fin (m + 1), HEq (restricted.certified i)
        (series.certified (Fin.castLE (by omega) i)) := by
  let restricted : TashkinovSeries G k m e0 input := {
    data := TashkinovSeriesDataPrefix m hm series.data
    certified := fun i =>
      (TashkinovSeriesStepPrefix input series.data m hm i
        (series.certified (Fin.castLE (by omega) i))).choose
  }
  refine ⟨restricted, rfl, ?_⟩
  intro i
  exact (TashkinovSeriesStepPrefix input series.data m hm i
    (series.certified (Fin.castLE (by omega) i))).choose_spec

end GoldbergSeymour

end
