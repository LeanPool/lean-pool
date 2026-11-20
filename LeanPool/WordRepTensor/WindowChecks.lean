/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.WindowOrientation

/-! # Kernel-checked orientation certificates for the three local graphs -/

@[expose] public section

namespace WordRepTensor

/-! ## Kernel-checked facts about the data -/

-- Kernel reduction checks the edge indices and chord condition of each listed path.
theorem winMu_valid : winMuPats.all (patValid winMuEdges) = true := by decide +kernel
/-- The ordinary window's forbidden paths are still forbidden after adding the cross-edges. -/
theorem winMu_valid_extended : winMuPats.all (patValid winExtEdges) = true := by
  -- Check the sixteen recorded paths in the extended seven-vertex graph.
  decide +kernel

theorem mu3_valid : mu3Pats.all (patValid mu3Edges) = true := by decide +kernel

-- Kernel reduction checks the colouring on all orientations of the nine edges.
theorem winMu_flip : flipOK 9 winMuPats winMuS0 winMuS1 winMuCol = true := by decide +kernel
-- Kernel reduction rules out the orientations of the seven-vertex base graph.
theorem mu3_none : noneOK 12 mu3Pats = true := by decide +kernel

section
variable {V : Type} [DecidableEq V]

/-- On a common edge, extending the window does not change its orientation. -/
private theorem orient_extended_eq (w : List V) (ι : Fin 7 → V) {edge : ℕ}
    (hedge : edge < winMuEdges.length) :
    orient w ι winExtEdges edge = orient w ι winMuEdges edge := by
  have hlength : edge < winExtEdges.length := by
    rw [winExtEdges, List.length_append]
    omega
  unfold orient
  rw [ite_eq_left hlength, ite_eq_left hedge]
  simp only [winExtEdges, List.getD_eq_getElem?_getD, List.getElem?_append_left hedge]

/-- The ordinary colouring flips on the extended window as well. -/
theorem extended_window_colour_flip {G : SimpleGraph V} {w : List V} (hw : Represents G w)
    (ι : Fin 7 → V) (hinj : Function.Injective ι)
    (hadj : ∀ x y, G.Adj (ι x) (ι y) ↔ wadjOf winExtEdges x y = true) :
    colOf winMuCol (stateOf (orient w ι winMuEdges) winMuS1) =
      !colOf winMuCol (stateOf (orient w ι winMuEdges) winMuS0) := by
  have hext := cond3_of_word hw ι hinj winExtEdges hadj winMuPats winMu_valid_extended
  refine flip_of_flipOK winMu_flip _ (orient_out w ι winMuEdges) ?_
  unfold cond3B at hext ⊢
  rw [List.all_eq_true] at hext ⊢
  intro path hpath
  have bounds : winMuPats.all (fun path => decide
      (path.e1 < winMuEdges.length ∧ path.e2 < winMuEdges.length ∧
        path.e3 < winMuEdges.length)) = true := by
    -- All three indices in each of the sixteen paths refer to ordinary edges.
    decide +kernel
  obtain ⟨h₁, h₂, h₃⟩ := of_decide_eq_true (List.all_eq_true.mp bounds path hpath)
  simpa only [arc, orient_extended_eq w ι h₁, orient_extended_eq w ι h₂,
    orient_extended_eq w ι h₃] using hext path hpath

end

end WordRepTensor
