/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.Polydisc

/-!
Geometric domain conditions for boundary layers and slabs. These conditions concern the
initial frequency domain and are proved for the polydiscs used in localization.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- The complex-linear pairing with a real coordinate covector. -/
def realCovectorPairing {n : ℕ} (ℓ : RealSpace n) (z : ComplexSpace n) : ℂ :=
  ∑ j, (ℓ j : ℂ) * z j

/-- The sum of absolute covector coordinates controlling its pairing norm. -/
def covectorLength {n : ℕ} (ℓ : RealSpace n) : ℝ := ∑ j, |ℓ j|

/-- The open complex slab cut out by a real covector and scalar center. -/
def complexSlab {n : ℕ} (ℓ : RealSpace n) (c a : ℝ) : Set (ComplexSpace n) :=
  {z | ‖realCovectorPairing ℓ z - (c : ℂ)‖ < a}

/-- Compact positive-volume frequency domains with quantitative boundary and slab-loss bounds. -/
structure TypeD {n : ℕ} (Ω : Set (ComplexSpace n)) (D : ℝ) : Prop where
  constant_pos : 0 < D
  compact : IsCompact Ω
  volume_pos : 0 < realVolume Ω
  boundary : ∀ d₁ d₂ : ℝ≥0, d₁ ≤ d₂ →
    realVolume (erosion Ω d₁ \ erosion Ω d₂) ≤
      ENNReal.ofReal (D * ((d₂ : ℝ) - d₁)) * realVolume Ω
  slab : ∀ (ℓ : RealSpace n) (c a : ℝ), 0 < covectorLength ℓ → 0 ≤ a →
    realVolume (Ω ∩ complexSlab ℓ c a) ≤
      ENNReal.ofReal (D * n * (2 * a / covectorLength ℓ)) * realVolume Ω

theorem realVolume_biUnion_finset_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Set (ComplexSpace n)) :
    realVolume (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, realVolume (f i) := by
  unfold realVolume realSlice
  simp only [preimage_iUnion]
  exact measure_biUnion_finset_le s _

end KamProject.Arnold1963
