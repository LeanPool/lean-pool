/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianFamilyBracket.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyMartingale
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCIRMoments

/-! Actual Brownian square brackets in the full family filtration. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianFamilyFiltration_square_conditional {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i : ι) (s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω => (B i t ω)^2) | ginibreBrownianFamilyFiltration B P hB s] =ᵐ[P]
      (fun ω => (B i s ω)^2+(t-s : ℝ≥0)) := by
  have := Fintype.ofFinite ι
  let := (hB i).isGaussianProcess.isProbabilityMeasure
  let Past := fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω
  let Z := fun ω => B i t ω-B i s ω
  let ν := gaussianReal 0 (t-s)
  have hPast : Measurable Past := by
    apply Measurable.of_eval
    intro p
    exact aemeasurable_iff_measurable.mp ((hB p.1).aemeasurable p.2)
  have hZ : HasLaw Z ν P := ginibreBrownian_increment_hasLaw (B i) P (hB i) s t hst
  have hInd := (ginibreBrownian_family_increment_independent_past B P hB hind s (t-s)).comp
    (measurable_pi_apply i) measurable_id
  have hInd' : IndepFun Z Past P := by
    simpa only [Z, Past, Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using hInd
  let G : ((ι × Set.Iic s) → ℝ) × ℝ → ℝ :=
    fun p => (p.1 (i, ⟨s, by change s ≤ s; exact le_rfl⟩)+p.2)^2
  have hG : Measurable G := by fun_prop
  have hEq : (fun ω => G (Past ω, Z ω)) =ᵐ[P] (fun ω => (B i t ω)^2) :=
    Filter.Eventually.of_forall fun ω => by dsimp [G, Past, Z]; ring
  have hGi : Integrable (fun ω => G (Past ω, Z ω)) P :=
    ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_sq.congr hEq.symm
  have hCondω := ae_of_ae_map hPast.aemeasurable (ginibreIndependent_condDistrib P Past Z hPast ν hZ
      hInd')
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hZ.aemeasurable hG.stronglyMeasurable
      hGi
  have h := ((condExp_congr_ae (m := MeasurableSpace.comap Past inferInstance) hEq).symm.trans hCE)
  change P[(fun ω => (B i t ω)^2) | MeasurableSpace.comap Past inferInstance] =ᵐ[P] _
  apply h.trans
  filter_upwards [hCondω] with ω hκ
  change (∫ u, (B i s ω+u)^2 ∂condDistrib Z Past P (Past ω)) = _
  rw [hκ]
  change (∫ u, (B i s ω+u)^2 ∂gaussianReal 0 (t-s)) = _
  rw [ginibreGaussian_shifted_secondMoment]
  ring

theorem ginibreBrownianFamilyFiltration_square_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i : ι) :
    Martingale (fun t ω => (B i t ω)^2-(t : ℝ)) (ginibreBrownianFamilyFiltration B P hB) P := by
  have := Fintype.ofFinite ι
  let := (hB i).isGaussianProcess.isProbabilityMeasure
  have hAdapt := ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hB i
  refine ⟨fun s => (hAdapt s).pow 2 |>.sub stronglyMeasurable_const, ?_⟩
  intro s t hst
  have hSq := ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_sq
  have hSub := condExp_sub hSq (integrable_const (t : ℝ)) (ginibreBrownianFamilyFiltration B P hB s)
  rw [condExp_const (ginibreBrownianFamilyFiltration B P hB |>.le s)] at hSub
  simp only [Pi.sub_def] at hSub
  have hCE := ginibreBrownianFamilyFiltration_square_conditional B P hB hind i s t hst
  filter_upwards [hSub, hCE] with ω hω he
  rw [NNReal.coe_sub hst] at he
  linarith

end
end GinibrePoincare
