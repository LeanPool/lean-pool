/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.WholePlaneH1L4Embedding
public import LeanPool.FastDynamo.Global.TransverseCoefficientMultipliers
public import LeanPool.FastDynamo.Global.TorusChartWeakTransfer
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Measurability of the placed local cores on the torus

The torus image `P.torusLocalCoreDisk n` of the local core disc of a placed cell is detected by
the canonical measurable chart representative `transverseIocRepresentative`, just as buffer
membership is (`mem_torusLocalCoreDisk_iff_transverseIocRepresentative`); hence it is measurable
(`measurableSet_torusLocalCoreDisk`).  `Global/TorusBackgroundVelocity.lean` uses this for the
union of the local cores.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

/-! ## Measurability of the local cores -/

namespace ScaleFamily

variable {p : LocalSeedParameters} {r : ScaleRatios p}

namespace TorusCellPlacement

variable {supportRadius : ℝ}

/-- Core membership is detected by the canonical measurable chart
representative, just as buffer membership is. -/
theorem mem_torusLocalCoreDisk_iff_transverseIocRepresentative
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (q : TransverseTorus) :
    q ∈ P.torusLocalCoreDisk n ↔
      transverseIocRepresentative q ∈
        P.scaleFamily.localCoreDisk supportRadius n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxbuffer : x ∈ P.scaleFamily.bufferDisk n :=
      P.localCoreDisk_subset_bufferDisk n hx
    simpa [transverseIocRepresentative_transverseTorusPoint_of_mem_placementChart
      (P.bufferDisk_subset_chart n hxbuffer)] using hx
  · intro hq
    exact ⟨transverseIocRepresentative q, hq,
      transverseTorusPoint_transverseIocRepresentative q⟩

/-- The torus image of a placed local core disc is measurable: it is the preimage of the Euclidean
core disc under the canonical measurable chart representative.
-/
theorem measurableSet_torusLocalCoreDisk
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ) :
    MeasurableSet (P.torusLocalCoreDisk n) := by
  have heq : P.torusLocalCoreDisk n =
      transverseIocRepresentative ⁻¹'
        P.scaleFamily.localCoreDisk supportRadius n := by
    ext q
    exact P.mem_torusLocalCoreDisk_iff_transverseIocRepresentative n q
  rw [heq]
  exact measurableSet_ball.preimage measurable_transverseIocRepresentative

end TorusCellPlacement

end ScaleFamily

end

end FastDynamo
