/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialCompactLift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialCompactGap

/-!
# General potential compact lift

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialVandermonde_compact_graph_value`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem potentialVandermonde_compact_graph_value {d : ℕ}
    (hn : 0 < d + 1) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hfin : potentialPartition (d + 1) V < ⊤)
    (f : Configuration (d + 1) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let hmem := potentialSmoothCompact_memLp (d + 1) hn hV.continuous hfin f hf.continuous hc
    let g := potentialVandermondeCoefficient (d + 1) V (fun z => (f z : ℂ))
    let hg := potentialVandermondeCoefficient_contDiff V _ (Complex.ofRealCLM.contDiff.comp hf)
    let hgc := potentialVandermondeCoefficient_hasCompactSupport V _
      (hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero)
    (piCompactWeightedDbarGraph (d + 1) V hV.continuous g hg hgc).1 =
      potentialVandermondeL2 (d + 1) hn hV.continuous hfin
        (hmem.ofReal.toLp (fun z => (f z : ℂ))) := by
  dsimp only
  apply Lp.ext
  have ha := potentialVandermondeL2_coeFn_public (d+1) hn hV.continuous hfin
    ((potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc).ofReal.toLp
      (fun z => (f z : ℂ)))
  have hm : MemLp (fun z => (f z : ℂ)) 2 (potentialMeasure (d+1) V) :=
    (potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc).ofReal
  have hb := (configurationVolume_absolutelyContinuous_potentialMeasure (d+1) hn hV.continuous
    hfin).ae_eq hm.coeFn_toLp
  have hg : ContDiff ℝ 1 (potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ))) :=
    potentialVandermondeCoefficient_contDiff V _ (Complex.ofRealCLM.contDiff.comp hf)
  have hgc : HasCompactSupport (potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ))) :=
    potentialVandermondeCoefficient_hasCompactSupport V _
    (hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero)
  have hx : MemLp (fun z => potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ)) z *
      piPotentialHalfWeight (d+1) (d+1) V z) 2 (volume : Measure (Configuration (d+1))) :=
    (hg.continuous.mul (piPotentialHalfWeight_continuous (d+1) (d+1) V
      hV.continuous)).memLp_of_hasCompactSupport hgc.mul_right
  filter_upwards [ha, hb, hx.coeFn_toLp] with z hz hb hx
  refine Eq.trans ?_ (hz.trans (congrArg (potentialVandermondeMultiplier (d+1) V z * ·) hb)).symm
  change ((hg.continuous.mul (piPotentialHalfWeight_continuous (d+1) (d+1) V
    hV.continuous)).memLp_of_hasCompactSupport hgc.mul_right).toLp _ z = _
  convert hx.trans (potentialVandermondeCoefficient_weighted (d+1) V _ z) using 1

end
end GinibrePoincare
