/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.AffineH54

/-! Four matching classes in each of the three bipartite layers of the local graph. -/

@[expose] public section
namespace GapExtremal.R434.H54

/-- Values on missing pairs are immaterial. The layers are ordered 01, 12, 02. -/
def edgeColour (k : Fin 3) (a b : Fin 5) : Fin 4 :=
  ![![![0, 1, 2, 0, 0],
      ![1, 0, 0, 2, 3],
      ![2, 3, 0, 0, 0],
      ![3, 0, 0, 1, 2],
      ![0, 2, 3, 0, 1]],
    ![![0, 1, 2, 0, 3],
      ![1, 0, 3, 2, 0],
      ![2, 0, 0, 0, 1],
      ![0, 0, 0, 1, 2],
      ![0, 2, 1, 3, 0]],
    ![![0, 0, 0, 1, 2],
      ![0, 0, 1, 2, 3],
      ![0, 0, 0, 3, 1],
      ![1, 2, 3, 0, 0],
      ![3, 1, 2, 0, 0]]] k a b

theorem edgeColour_left :
    ∀ (k : Fin 3) (a b b' : Fin 5), (k,a,b) ∈ edges → (k,a,b') ∈ edges →
      edgeColour k a b = edgeColour k a b' → b = b' := by
  decide +kernel

theorem edgeColour_right :
    ∀ (k : Fin 3) (a a' b : Fin 5), (k,a,b) ∈ edges → (k,a',b) ∈ edges →
      edgeColour k a b = edgeColour k a' b → a = a' := by
  decide +kernel

end GapExtremal.R434.H54
