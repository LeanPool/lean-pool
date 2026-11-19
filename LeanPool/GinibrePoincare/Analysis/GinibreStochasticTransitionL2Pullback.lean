/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionL2Pullback.lean.
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

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Probability.IdentDistrib

/-!
# Ginibre stochastic transition L 2 pullback

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `stationaryEndpointL2Operator_norm_le`,
`stationaryEndpointL2Operator_symmetric_pairing`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- Actual L² pullback along a measure-preserving endpoint. -/
def stationaryEndpointL2Pullback {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure E) (X : Ω → E) (hX : MeasurePreserving X P μ) :
    Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 P where
  toFun := Lp.compMeasurePreserving X hX
  map_add' := (Lp.compMeasurePreserving X hX).map_add
  map_smul' := by
    intro c f
    apply Lp.ext
    have hsm := hX.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c f)
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • f) hX,
      Lp.coeFn_compMeasurePreserving f hX, Lp.coeFn_smul c (Lp.compMeasurePreserving X hX f), hsm]
          with ω hleft hright hscalar hsrc
    simp only [RingHom.id_apply]
    rw [hleft, hscalar]
    simp only [Pi.smul_apply, Function.comp_apply] at hsrc hright ⊢
    rw [hright]
    exact hsrc
  norm_map' := fun f => Lp.norm_compMeasurePreserving f hX

/-- The stochastic L² endpoint operator obtained by the genuine Hilbert
adjoint of the initial endpoint pullback and the terminal endpoint pullback.
This generic construction becomes a transition operator after the actual
stationary endpoint identities are proved. -/
def stationaryEndpointL2Operator {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure E) (X Y : Ω → E)
    (hX : MeasurePreserving X P μ) (hY : MeasurePreserving Y P μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (stationaryEndpointL2Pullback P μ X hX).toContinuousLinearMap.adjoint.comp
    (stationaryEndpointL2Pullback P μ Y hY).toContinuousLinearMap

theorem stationaryEndpointL2Operator_pairing {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) (μ : Measure E)
    (X Y : Ω → E) (hX : MeasurePreserving X P μ) (hY : MeasurePreserving Y P μ)
    (f g : Lp ℝ 2 μ) :
    inner ℝ f (stationaryEndpointL2Operator P μ X Y hX hY g)=
      ∫ ω, f (X ω)*g (Y ω) ∂P := by
  rw [stationaryEndpointL2Operator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f hX, Lp.coeFn_compMeasurePreserving g hY] with ω
      hf hg
  change (Lp.compMeasurePreserving Y hY g) ω*(Lp.compMeasurePreserving X hX f) ω=_
  rw [hf, hg]
  exact mul_comm _ _

theorem stationaryEndpointL2Operator_norm_le {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) (μ : Measure E)
    (X Y : Ω → E) (hX : MeasurePreserving X P μ) (hY : MeasurePreserving Y P μ)
    (f : Lp ℝ 2 μ) : ‖stationaryEndpointL2Operator P μ X Y hX hY f‖≤‖f‖ := by
  let A := (stationaryEndpointL2Pullback P μ X hX).toContinuousLinearMap
  let B := (stationaryEndpointL2Pullback P μ Y hY).toContinuousLinearMap
  have hA : ‖A‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    change ‖Lp.compMeasurePreserving X hX g‖≤1*‖g‖
    simp only [Lp.norm_compMeasurePreserving, one_mul, le_refl]
  have hB : ‖B f‖=‖f‖ := Lp.norm_compMeasurePreserving f hY
  change ‖A.adjoint (B f)‖≤‖f‖
  calc
    ‖A.adjoint (B f)‖≤‖A.adjoint‖*‖B f‖ := A.adjoint.le_opNorm _
    _=‖A‖*‖f‖ := by rw [ContinuousLinearMap.adjoint.norm_map, hB]
    _≤1*‖f‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _=‖f‖ := one_mul _

theorem stationaryEndpointL2Operator_symmetric_pairing {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) (μ : Measure E)
    (X Y : Ω → E) (hX : MeasurePreserving X P μ) (hY : MeasurePreserving Y P μ)
    (hSym : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (Y ω, X ω)) P P)
    (f g : Lp ℝ 2 μ) :
    inner ℝ f (stationaryEndpointL2Operator P μ X Y hX hY g)=
      inner ℝ g (stationaryEndpointL2Operator P μ X Y hX hY f) := by
  rw [stationaryEndpointL2Operator_pairing, stationaryEndpointL2Operator_pairing]
  have hm : Measurable (fun p : E × E => f p.1*g p.2) :=
    ((Lp.stronglyMeasurable f).measurable.comp measurable_fst).mul
      ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)
  have he := (hSym.comp hm).integral_eq
  exact he.trans (integral_congr_ae (ae_of_all P (fun ω => mul_comm _ _)))

end
end GinibrePoincare
