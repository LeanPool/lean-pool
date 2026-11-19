/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FullRadialLSIReduction.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BlockMagnitudeLift
public import LeanPool.GinibrePoincare.Analysis.GaussianBlockLSI

/-!
# Full radial LSI reduction

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `gaussian_smooth_lsi`, `radial_core_lsi`, `radial_sobolev_lsi`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- A Lipschitz Gaussian bound supplies the smooth Gaussian bound. -/
theorem gaussian_smooth_lsi_of_lipschitz (n : ℕ)
    (hG : GaussianBlockLipschitzLSIStatement n) : GaussianBlockLSIStatement n := by
  intro H hH hc
  exact hG H (ContDiff.lipschitzWith_of_hasCompactSupport hc hH (by simp)) hc

/-- The full original smooth radial core satisfies the paper's inequality once
the standard Lipschitz Gaussian LSI is supplied. The radial witness is arbitrary;
its regularity is not assumed. -/
theorem radial_core_lsi_of_gaussian (n : ℕ) (hn : 0 < n)
    (hG : GaussianBlockLipschitzLSIStatement n)
    (f : Configuration n → ℝ) (hf : IsRadialSobolevCore f) :
    ginibreSquareEntropy n f ≤ smoothGinibreEnergy n f := by
  let F := magnitudeProfile f
  have hF := contDiff_magnitudeProfile f hf.1.1
  have hc := compactSupport_magnitudeProfile f hf.1.2.1
  have hs := magnitudeProfile_symmetric f hf.1.2.2
  have he : f = fun z => F (magnitudeVector z) :=
    funext (radial_eq_magnitudeProfile f hf.2)
  rw [he]
  change squareEntropy (ginibreMeasure n) (fun z => magnitudeProfile f (magnitudeVector z)) ≤ _
  rw [ginibre_magnitude_entropy_eq_block n hn _ hF.continuous hc hs,
    ginibre_magnitude_energy_eq_block n hn _ hF hc hs]
  exact hG _ (lipschitz_block_magnitude_lift n _ hF hc)
    (compactSupport_block_magnitude_lift n _ hc)

/-- The full radial symmetric Sobolev closure theorem with only the standard
Gaussian LSI left as a hypothesis. All radial and limiting arguments are proved. -/
theorem radial_sobolev_lsi_of_gaussian (n : ℕ) (hn : 0 < n)
    (hG : GaussianBlockLipschitzLSIStatement n) :
    ∀ p ∈ radialSobolevClosure n,
      Integrable (fun z => p.1 z ^ 2 * Real.log (p.1 z ^ 2)) (ginibreMeasure n) ∧
        squareEntropy (ginibreMeasure n) p.1 ≤ (1 / (n : ℝ)) * ‖p.2‖ ^ 2 := by
  exact radialSobolevClosure_lsi_of_core n hn (radial_core_lsi_of_gaussian n hn hG)

/-- The sharp smooth block Gaussian LSI, with its input discharged. -/
theorem gaussian_smooth_lsi (n : ℕ) (hn : 0 < n) : GaussianBlockLSIStatement n :=
  gaussian_smooth_lsi_of_lipschitz n (gaussianBlock_lsi n hn)

/-- Unconditional sharp LSI on the full smooth symmetric radial core.
No regularity is assumed of the existential radial witness. -/
theorem radial_core_lsi (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsRadialSobolevCore f) :
    ginibreSquareEntropy n f ≤ smoothGinibreEnergy n f :=
  radial_core_lsi_of_gaussian n hn (gaussianBlock_lsi n hn) f hf

/-- Unconditional sharp radial LSI on the actual value-gradient L² completion,
including finiteness of the logarithmic entropy moment. -/
theorem radial_sobolev_lsi (n : ℕ) (hn : 0 < n) :
    ∀ p ∈ radialSobolevClosure n,
      Integrable (fun z => p.1 z ^ 2 * Real.log (p.1 z ^ 2)) (ginibreMeasure n) ∧
        squareEntropy (ginibreMeasure n) p.1 ≤ (1 / (n : ℝ)) * ‖p.2‖ ^ 2 :=
  radial_sobolev_lsi_of_gaussian n hn (gaussianBlock_lsi n hn)

end
end GinibrePoincare
