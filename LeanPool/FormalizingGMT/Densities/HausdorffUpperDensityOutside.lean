/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import LeanPool.FormalizingGMT.Densities.HausdorffUpperDensityOutsideLemmas


/-!
# Density bound for Hausdorff measure restricted to a set for points not in the set

Let X be a locally compact, second countable metric space (equipped with its Borel σ-algebra),
let s ≥ 0, and let E ⊆ X be measurable in the sense of Carathéodory with respect to the
s-dimensional Hausdorff outer measure H^s, with H^s(E) < ∞. Then for H^s-almost every x ∈ X \ E:

  lim sup_{r → 0⁺} H^s(E ∩ B(x, r)) / (2r)^s = 0

where B(x, r) denotes the closed metric ball with center x and radius r.
-/

@[expose] public section

open MeasureTheory Measure Metric Set Filter ENNReal
open scoped NNReal Topology

variable {X : Type*} [MetricSpace X]
  [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-! ## Step (n): Main theorem -/

/-- **Theorem 2.6** (Density at points not in E).
Let `X` be a locally compact, second countable metric space with its Borel σ-algebra, let
`s ≥ 0`, and let `E ⊆ X` be measurable in the sense of Carathéodory with respect to the
`s`-dimensional Hausdorff outer measure `H^s` (`hsOuter s`), with `H^s(E) < ∞`.
Then the set of points `x ∉ E` at which the `s`-dimensional upper density of `H^s ⌞ E`
(`hsRestrict s E`) is nonzero is `μH[s]`-null; that is, for `H^s`-almost every `x ∈ X \ E`,

  `limsup_{r → 0⁺} H^s(E ∩ B(x, r)) / (2r)^s = 0`,

where `B(x, r)` is the closed ball. (σ-compactness of `X` is not assumed separately: it follows
from local compactness and second countability.) -/
theorem hausdorffMeasure_upperDensity_eq_zero_ae_notMem
    {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hE_meas : MeasurableSet[(hsOuter (X := X) s).caratheodory] E)
    (hE_fin : (hsOuter (X := X) s) E < ⊤) :
    μH[s] {x | x ∉ E ∧
      dimensionalUpperDensity (hsRestrict s E) s x ≠ 0} = 0 := by
  apply MeasureTheory.measure_mono_null
      (t := ⋃ n : ℕ, aSet s E (1 / (n + 1)))
  · intro x hx
    simp only [Set.mem_iUnion]
    rcases ENNReal.exists_inv_nat_lt hx.2 with ⟨n, hn⟩
    have hle : 1 / ((n : ℝ≥0∞) + 1) ≤ 1 / (n : ℝ≥0∞) := by
      gcongr
      exact le_add_of_nonneg_right zero_le
    exact ⟨n, hx.1, hle.trans_lt (by simpa only [one_div] using hn)⟩
  · exact MeasureTheory.measure_iUnion_null fun n =>
      A_t_null s hs hE_meas hE_fin
        (ENNReal.div_pos_iff.mpr ⟨by norm_num, by norm_num⟩) (by simp)
