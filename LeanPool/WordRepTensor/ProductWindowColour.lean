/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.ProductWindow

/-! The ordinary window colouring works on the extended window too. -/

@[expose] public section

namespace WordRepTensor

theorem commonWindowStep :
  ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V) (w : List V) (ι : Fin 7 → V),
      Represents G w → Function.Injective ι →
      ((∀ x y, G.Adj (ι x) (ι y) ↔ wadjOf winMuEdges x y = true) ∨
       (∀ x y, G.Adj (ι x) (ι y) ↔ wadjOf winExtEdges x y = true)) →
      colOf winMuCol (stateOf (orient w ι winMuEdges) winMuS1) =
        !colOf winMuCol (stateOf (orient w ι winMuEdges) winMuS0) := by
  intro V _ G w ι hw hi hwin
  rcases hwin with hmu | hext
  · exact flip_of_flipOK winMu_flip _ (orient_out w ι winMuEdges)
      (cond3_of_word hw ι hi winMuEdges hmu winMuPats winMu_valid)
  · exact extended_window_colour_flip hw ι hi hext

theorem productStateShift :
  ∀ (k K : ℕ) [NeZero K] (hk : 3 ≤ k)
      (w : List ((Fin k ⊕ Fin k ⊕ Unit) × (Fin K ⊕ Fin K ⊕ Unit))) (i : Fin K),
      stateOf (orient w (productWinMap hk i) winMuEdges) winMuS1 =
        stateOf (orient w (productWinMap hk (i + 1)) winMuEdges) winMuS0 := by
  intro k K _ hk w i
  rfl

end WordRepTensor
