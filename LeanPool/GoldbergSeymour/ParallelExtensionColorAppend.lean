/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ParallelExtensionColor
public import LeanPool.GoldbergSeymour.TashkinovSeriesDataAppend
public import Mathlib.Data.Fintype.EquivFin

/-!
# Parallel Extension Color Append

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ParallelExtensionColorAppend {V E : Type*} [Finite V] [Fintype E]
    {G : LooplessMultigraph V E} {k rounds : ℕ} {e0 : E}
    (data : TashkinovSeriesData G k rounds e0)
    (newTree : TreeSequence G e0)
    (newColoring : PartialEdgeColoring E k)
    (newStored : Finset (Fin k))
    (newConnectingEdges : Finset E)
    (newKind : Option TashkinovExtensionKind)
    (newChosenVertex newOutsideVertex : Option V)
    (newDelta newGamma : Option (Fin k))
    (i : Fin (rounds + 1)) (selected : PartialEdgeColoring E k)
    (v : V) (gamma : Fin k) :
    ParallelExtensionColor
      (TashkinovSeriesDataAppend data newTree newColoring newStored
        newConnectingEdges newKind newChosenVertex newOutsideVertex newDelta newGamma)
      i.castSucc selected v gamma ↔
      ParallelExtensionColor data i selected v gamma := by
  classical
  let _ := Fintype.ofFinite V
  let appended := TashkinovSeriesDataAppend data newTree newColoring
    newStored newConnectingEdges newKind newChosenVertex newOutsideVertex
    newDelta newGamma
  unfold ParallelExtensionColor
  constructor
  · rintro ⟨hmissing, history | noHistory⟩
    · rcases history with ⟨h, hpos, hle, hPE, hv, hdelta, hmax⟩
      let oldH : Fin (rounds + 1) := ⟨h.val, lt_of_le_of_lt hle i.isLt⟩
      have hEq : h = oldH.castSucc := by ext; rfl
      refine ⟨hmissing, Or.inl ⟨oldH, hpos, hle, ?_, ?_, ?_, ?_⟩⟩
      · simpa [appended, TashkinovSeriesDataAppend, hEq] using hPE
      · simpa [appended, TashkinovSeriesDataAppend, hEq] using hv
      · simpa [appended, TashkinovSeriesDataAppend, hEq] using hdelta
      · intro j hjpos hjle hjPE hjv
        exact hmax j.castSucc hjpos hjle
          (by simpa [appended, TashkinovSeriesDataAppend] using hjPE)
          (by simpa [appended, TashkinovSeriesDataAppend] using hjv)
    · refine ⟨hmissing, Or.inr ?_⟩
      intro h hpos hle hPE
      have newNe := noHistory h.castSucc hpos hle
        (by simpa [appended, TashkinovSeriesDataAppend] using hPE)
      simpa [appended, TashkinovSeriesDataAppend] using newNe
  · rintro ⟨hmissing, history | noHistory⟩
    · rcases history with ⟨h, hpos, hle, hPE, hv, hdelta, hmax⟩
      refine ⟨hmissing, Or.inl ⟨h.castSucc, hpos, hle, ?_, ?_, ?_, ?_⟩⟩
      · simpa [appended, TashkinovSeriesDataAppend] using hPE
      · simpa [appended, TashkinovSeriesDataAppend] using hv
      · simpa [appended, TashkinovSeriesDataAppend] using hdelta
      · intro j hjpos hjle hjPE hjv
        let oldJ : Fin (rounds + 1) := ⟨j.val, lt_of_le_of_lt hjle i.isLt⟩
        have jEq : j = oldJ.castSucc := by ext; rfl
        exact hmax oldJ hjpos hjle
          (by simpa [appended, TashkinovSeriesDataAppend, jEq] using hjPE)
          (by simpa [appended, TashkinovSeriesDataAppend, jEq] using hjv)
    · refine ⟨hmissing, Or.inr ?_⟩
      intro h hpos hle hPE
      let oldH : Fin (rounds + 1) := ⟨h.val, lt_of_le_of_lt hle i.isLt⟩
      have hEq : h = oldH.castSucc := by ext; rfl
      have oldNe := noHistory oldH hpos hle
        (by simpa [appended, TashkinovSeriesDataAppend, hEq] using hPE)
      simpa [appended, TashkinovSeriesDataAppend, hEq] using oldNe

end GoldbergSeymour

end
