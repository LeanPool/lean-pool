/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionData

/-!
# RandomHsepWaveEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The wave envelope at the random separation scale

`measureReal_exists_cubeSupBound_gt_le` prices the wave-envelope failure for a
deterministic Whitney scale profile.  The profile used in Section 3 is instead
selected from the same cutoff sample through `hsep`.  This file performs that
selection by a finite-cutoff decomposition.  No independence or measurability
of the random index is used.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## A set-valued random-index decomposition -/

/-- A finite-cutoff decomposition for a set selected by a random natural
index.  The pieces with index at most `H` are bounded separately, while all
remaining samples are charged to `{omega | H < N omega}`.  This requires no
measurability of `N` and no independence between `N` and the family `B`. -/
theorem measureReal_mem_randomIndex_le {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] (B : ℕ → Set Omega)
    (N : Omega → ℕ) (H : ℕ) :
    mu.real {omega | omega ∈ B (N omega)} ≤
      (∑ h ∈ Finset.range (H + 1), mu.real (B h)) +
        mu.real {omega | H < N omega} := by
  classical
  have hsub : {omega | omega ∈ B (N omega)} ⊆
      (⋃ h ∈ Finset.range (H + 1), B h) ∪ {omega | H < N omega} := by
    intro omega homega
    by_cases hN : H < N omega
    · exact Or.inr hN
    · have hle : N omega < H + 1 := by omega
      exact Or.inl (Set.mem_biUnion (Finset.mem_range.2 hle) homega)
  calc
    mu.real {omega | omega ∈ B (N omega)}
        ≤ mu.real ((⋃ h ∈ Finset.range (H + 1), B h) ∪
            {omega | H < N omega}) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ mu.real (⋃ h ∈ Finset.range (H + 1), B h) +
          mu.real {omega | H < N omega} := measureReal_union_le _ _
    _ ≤ (∑ h ∈ Finset.range (H + 1), mu.real (B h)) +
          mu.real {omega | H < N omega} :=
        add_le_add (measureReal_biUnion_finset_le _ _) le_rfl

/-! ## The random-`hsep` wave event -/


end

end Algsuperdiff.Section3.Provider.Multiscale
