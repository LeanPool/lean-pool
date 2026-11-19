/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianFamilyCrossBracket.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticGaussianPiCrossMoments

/-! Distinct actual Brownian coordinates have zero cross bracket in the whole family filtration. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianFamilyFiltration_cross_conditional {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i j : ι) (hij : i ≠ j)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω => B i t ω*B j t ω) | ginibreBrownianFamilyFiltration B P hB s] =ᵐ[P]
      (fun ω => B i s ω*B j s ω) := by
  have := Fintype.ofFinite ι
  let := (hB i).isGaussianProcess.isProbabilityMeasure
  let Past := fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω
  let Z := fun ω k => B k t ω-B k s ω
  let ν := Measure.pi (fun _ : ι => gaussianReal 0 (t-s))
  have hPast : Measurable Past := by
    apply Measurable.of_eval
    intro p
    exact aemeasurable_iff_measurable.mp ((hB p.1).aemeasurable p.2)
  have hZ : HasLaw Z ν P := by
    simpa only [Z, add_tsub_cancel_of_le hst] using ginibreBrownian_family_increment_hasLaw B P hB
        hind s (t-s)
  have hInd : IndepFun Z Past P := by
    simpa only [Z, Past, add_tsub_cancel_of_le hst] using
      ginibreBrownian_family_increment_independent_past B P hB hind s (t-s)
  let G : ((ι × Set.Iic s) → ℝ) × (ι → ℝ) → ℝ := fun p =>
    (p.1 (i, ⟨s, by change s ≤ s; exact le_rfl⟩)+p.2 i)*
      (p.1 (j, ⟨s, by change s ≤ s; exact le_rfl⟩)+p.2 j)
  have hG : Measurable G := by fun_prop
  have hEq : (fun ω => G (Past ω, Z ω)) =ᵐ[P] (fun ω => B i t ω*B j t ω) :=
    Filter.Eventually.of_forall fun ω => by dsimp [G, Past, Z]; ring
  have hProd : Integrable (fun ω => B i t ω*B j t ω) P :=
    ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_mul
      ((hB j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hGi := hProd.congr hEq.symm
  have hCondω := ae_of_ae_map hPast.aemeasurable
    (ginibreIndependent_condDistrib_general P Past Z hPast ν hZ hInd)
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hZ.aemeasurable hG.stronglyMeasurable
      hGi
  have h := ((condExp_congr_ae (m := MeasurableSpace.comap Past inferInstance) hEq).symm.trans hCE)
  change P[(fun ω => B i t ω*B j t ω) | MeasurableSpace.comap Past inferInstance] =ᵐ[P] _
  apply h.trans
  filter_upwards [hCondω] with ω hκ
  change (∫ u, (B i s ω+u i)*(B j s ω+u j) ∂condDistrib Z Past P (Past ω)) = _
  rw [hκ]
  exact ginibreGaussianPi_shifted_crossMoment (t-s) i j hij (B i s ω) (B j s ω)

theorem ginibreBrownianFamilyFiltration_cross_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i j : ι) (hij : i ≠ j) :
    Martingale (fun t ω => B i t ω*B j t ω) (ginibreBrownianFamilyFiltration B P hB) P := by
  have := Fintype.ofFinite ι
  refine ⟨fun s => (ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hB i s).mul
    (ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hB j s), ?_⟩
  intro s t hst
  exact ginibreBrownianFamilyFiltration_cross_conditional B P hB hind i j hij s t hst

end
end GinibrePoincare
