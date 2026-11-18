/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeVertexIncidentCell
public import Mathlib.Init


/-!
# LatticeFootprintIncidence

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace LatticeFootprintIncidence

/-- Shared incidentCell fact. -/
theorem incidentCell :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (y : GaussianInt), (W.cells.Nonempty) → ((y ∈ FootprintVertices W) →
            (∃ j : Fin 4, LatticeVertexIncidentCell y j ∈ W.cells)) ) := by
  classical
  intro W y hne hy
  simp only [FootprintVertices, hne, ite_true, Set.mem_ofPred_eq] at hy
  rcases hy with ⟨c, hc, h | h | h | h⟩
  · exact ⟨0, by simpa [LatticeVertexIncidentCell] using h ▸ hc⟩
  · refine ⟨1, ?_⟩
    rw [h]
    simpa [LatticeVertexIncidentCell] using hc
  · refine ⟨3, ?_⟩
    rw [h]
    simpa [LatticeVertexIncidentCell] using hc
  · refine ⟨2, ?_⟩
    change y - 1 - ⟨0, 1⟩ ∈ W.cells
    rw [h]
    convert hc using 1
    ext <;> simp


end LatticeFootprintIncidence
end ApollonianSuperharmonic

end
