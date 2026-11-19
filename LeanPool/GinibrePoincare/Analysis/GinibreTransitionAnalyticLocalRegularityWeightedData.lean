/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityWeightedData.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityInteriorCutoff
public import LeanPool.GinibrePoincare.Analysis.GinibreLocalSobolev
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Ginibre transition analytic local regularity weighted data

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_density_resolvent_data_memLp`.
-/

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_weighted_multiplier_restrict_memLp
    (n : ℕ) (hn : 0 < n) (u q : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hq : Continuous q)
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z}) :
    MemLp (fun z => q z*u z) 2 ((volume : Measure (Configuration n)).restrict K) := by
  obtain ⟨χ, hχ, hχc, hχs, hχone⟩ := ginibreLocalRegularity_exists_compact_interior_cutoff n hn K hK
      hs
  have hcq : HasCompactSupport (χ*q) := hχc.mul_right
  have htop : MemLp (χ*q) ⊤ ((volume : Measure (Configuration n)).restrict K) :=
    (hχ.continuous.mul hq).memLp_top_of_hasCompactSupport hcq _
  have hi := htop.fun_mul (r := 2)
    (ginibre_memLp_restrict_volume_compact_collisionFree hn u hu K hK hs)
  apply MemLp.ae_eq (hf_Lp := hi)
  apply ae_restrict_of_forall_mem hK.measurableSet
  intro z hz
  dsimp only [Pi.mul_apply]
  rw [(hχone z hz).eq_of_nhds]
  simp

/-- The three concrete divergence-form data are locally ordinary L² solely
from the actual weighted L² resolvent data and smooth density. -/
theorem ginibreLocalRegularity_density_resolvent_data_memLp
    (n : ℕ) (hn : 0 < n) (ℓ : ℝ) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z}) :
    MemLp (fun z => ginibreLebesgueDensityReal n z*u z) 2 (volume.restrict K) ∧
    MemLp (fun z => (n : ℝ)*ginibreLebesgueDensityReal n z*(ℓ*u z-f z)) 2 (volume.restrict K) ∧
    ∀ v : Configuration n, MemLp (fun z => fderiv ℝ (ginibreLebesgueDensityReal n) z v*u z)
      2 (volume.restrict K) := by
  refine ⟨ginibreLocalRegularity_weighted_multiplier_restrict_memLp n hn u _ hu
    (contDiff_ginibreLebesgueDensityReal n).continuous K hK hs,?_,?_⟩
  · have hm := ginibreLocalRegularity_weighted_multiplier_restrict_memLp n hn
      (fun z => ℓ*u z-f z) (fun z => (n : ℝ)*ginibreLebesgueDensityReal n z)
      ((hu.const_mul ℓ).sub hf) (continuous_const.mul (contDiff_ginibreLebesgueDensityReal
          n).continuous) K hK hs
    exact hm
  · intro v
    have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ (ginibreLebesgueDensityReal n) z v) :=
      ((contDiff_ginibreLebesgueDensityReal n).fderiv_right (by simp)).clm_apply contDiff_const
    exact ginibreLocalRegularity_weighted_multiplier_restrict_memLp n hn u _ hu hd.continuous K hK
        hs

end
end GinibrePoincare
