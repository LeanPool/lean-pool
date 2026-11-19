/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathCompactClippedFlow.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathClippedLocalFlow
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathCompactLocalFlow

/-!
# Ginibre driven path compact clipped flow

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreDrivenPath_compact_clipped_measurable_local_flow`.
-/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenPath_compact_clipped_measurable_local_flow (n : ℕ) (α : ℝ) (z : Configuration
    n)
    (hz : CollisionFree z) :
    ∃ δ : ℝ, ∃ hδ : δ > 0, ∃ τ : ℝ, ∃ hτ : τ > 0,
    ∃ K : Set (Configuration n), IsCompact K ∧ (∀ x ∈ K, CollisionFree x) ∧
    ∃ Φ : C(Icc (-1 : ℝ) 1, Configuration n) → C(Icc 0 τ, Configuration n),
      @Measurable _ _ (borel C(Icc (-1 : ℝ) 1, Configuration n))
        (borel C(Icc 0 τ, Configuration n)) Φ ∧
      (∀ N, Φ N ⟨0, ⟨le_rfl, hτ.le⟩⟩ = z) ∧
      (∀ N (t : Icc 0 τ), Φ N t ∈ K) ∧
      (∀ N (t : Icc 0 τ), Φ N t = z+
        drivenBoundedNoiseExtension (Configuration n) (drivenNoiseClipSmall δ hδ N).val t+
        ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (Φ N (Set.projIcc 0 τ hτ.le s))) ∧
      ∀ N Q (t : Icc 0 τ),
        (∀ s ∈ Icc 0 (t : ℝ), N (Set.projIcc (-1 : ℝ) 1 (by norm_num) s) =
          Q (Set.projIcc (-1 : ℝ) 1 (by norm_num) s)) → Φ N t = Φ Q t := by
  obtain ⟨δ, hδ, τ, hτ, K, hK, hKCF, Ψ, hMeas, hZero, hCF, hEq, hCausal⟩ :=
      ginibreDrivenPath_compact_measurable_local_flow n α z hz
  let Φ := fun N => Ψ (drivenNoiseClipSmall δ hδ N)
  have hΦ : @Measurable _ _ (borel C(Icc (-1 : ℝ) 1, Configuration n))
      (borel C(Icc 0 τ, Configuration n)) Φ :=
    hMeas.comp (drivenNoiseClipSmall_continuous δ hδ).borel_measurable
  refine ⟨δ, hδ, τ, hτ, K, hK, hKCF, Φ, hΦ, fun N => hZero _, fun N t => hCF _ t, fun N t => hEq _
      t,?_⟩
  intro N Q t hPast
  apply hCausal
  intro s hs
  have h0 := hPast 0 ⟨le_rfl, t.property.1⟩
  simp only [Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ)
                                                                   1)] at h0
  change drivenNoiseClip (drivenNoiseClipRadius δ) (N _-N _) = drivenNoiseClip
      (drivenNoiseClipRadius δ) (Q _-Q _)
  rw [hPast s hs, h0]

end
end GinibrePoincare
