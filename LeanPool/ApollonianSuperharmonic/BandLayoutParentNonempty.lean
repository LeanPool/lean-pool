/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import Mathlib.Init


/-!
# BandLayoutParentNonempty

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace BandLayoutParentNonempty

/-- Every parent tile in a general layout has a cell. -/
theorem cells (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T₀ : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T₀) (j : Fin 3) (hs : Bool) :
    (cert.P j hs).cells.Nonempty := by
  classical
  rcases cert.parent_lattice j hs with ⟨e⟩
  have hball : (0 : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    simp
  have hreal : (e ⟨(0 : ℝ × ℝ), hball⟩ : ℝ × ℝ) ∈
      TileRealization (cert.P j hs) := (e ⟨0, hball⟩).property
  simp only [TileRealization, Set.mem_iUnion] at hreal
  rcases hreal with ⟨x, hx, _⟩
  exact ⟨x, hx⟩

end BandLayoutParentNonempty
end ApollonianSuperharmonic

end
