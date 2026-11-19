/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianScalarOUPairFunction.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianContinuousPathIndependence
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUProductReversal

/-!
# Ginibre Hamiltonian scalar OU pair function

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreScalarOUHorizon_independent_coordinates`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous real paths `C(ℝ≥0, ℝ)`. -/
local instance ginibreScalarOUPairNoiseMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance ginibreScalarOUPairNoiseBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous real paths over the horizon `[0, T]` in `ℝ≥0`. -/
local instance ginibreScalarOUPairHorizonMeasurable (T : ℝ≥0) : MeasurableSpace C(Icc (0 : ℝ≥0) T,
    ℝ) := borel _
local instance ginibreScalarOUPairHorizonBorel (T : ℝ≥0) : BorelSpace C(Icc (0 : ℝ≥0) T, ℝ) := ⟨rfl⟩

/-- The scalar Ornstein–Uhlenbeck path with rate `rate`, started at `p.1` and driven by
`√rate * p.2`, restricted to `[0, T]`. -/
def ginibreScalarOUPairHorizon (rate T : ℝ≥0) (p : ℝ × C(ℝ≥0, ℝ)) :
    C(Icc (0 : ℝ≥0) T, ℝ) :=
  ⟨fun t => drivenOUPath rate p.1 (fun s => Real.sqrt (rate : ℝ) * p.2 s.toNNReal) t.val,
    (drivenOUPath_continuous _ p.1 _
      (continuous_const.mul (p.2.continuous.comp continuous_real_toNNReal))).comp
      (NNReal.continuous_coe.comp continuous_subtype_val)⟩

theorem ginibreScalarOUPairHorizon_measurable (rate T : ℝ≥0) :
    Measurable (ginibreScalarOUPairHorizon rate T) := by
  let : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, ⟨le_rfl, zero_le⟩⟩⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  have hj : Continuous (fun p : (ℝ × C(ℝ≥0, ℝ)) × ℝ =>
      Real.exp ((rate : ℝ)*p.2) * (Real.sqrt (rate : ℝ) * p.1.2 p.2.toNNReal)) := by
    fun_prop
  have hInt : Measurable (fun p : ℝ × C(ℝ≥0, ℝ) => ∫ s in (0 : ℝ)..(t.val : ℝ),
      Real.exp ((rate : ℝ)*s) * (Real.sqrt (rate : ℝ)*p.2 s.toNNReal)) := by
    have hi := hj.measurable.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (t.val : ℝ)))
    simpa only [intervalIntegral.integral_of_le t.val.coe_nonneg] using hi.measurable
  have hEval : Measurable (fun p : ℝ × C(ℝ≥0, ℝ) => Real.sqrt (rate : ℝ)*p.2 t.val) :=
    measurable_const.mul ((continuous_eval_const t.val).measurable.comp measurable_snd)
  change Measurable (fun p : ℝ × C(ℝ≥0, ℝ) =>
    drivenOUPath rate p.1 (fun s => Real.sqrt (rate : ℝ)*p.2 s.toNNReal) t.val)
  convert hEval.add ((measurable_fst.sub (hInt.const_mul (rate : ℝ))).const_mul
    (Real.exp (-(rate : ℝ)*(t.val : ℝ)))) using 1
  funext p
  simp [drivenOUPath, drivenOUCorrection, smul_eq_mul]

theorem ginibreScalarOUPairHorizon_actual {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (Z : Ω → ℝ) (rate T : ℝ≥0) :
    ∀ᵐ ω ∂P, ginibreScalarOUPairHorizon rate T
      (Z ω, ginibreScalarBrownianNormalize (fun t => B t ω)) =
      ginibreBrownianOUHorizonPath B Z rate T ω := by
  filter_upwards [hB.cont, ginibreBrownianOUHorizonPath_ae B P hB Z rate T] with ω hc hω
  have he := ginibreScalarBrownianNormalize_continuous (fun t => B t ω) hc
  ext t
  rw [hω t]
  simp only [ginibreScalarOUPairHorizon, ContinuousMap.coe_mk, ginibreBrownianOU]
  congr 1
  funext s
  rw [he]
  rfl

theorem ginibreScalarOUHorizon_independent_coordinates {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (Z : ι → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hiZ : iIndepFun Z P) (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (hind : IndepFun (fun ω i => Z i ω) (fun ω i t => B i t ω) P)
    (rate T : ℝ≥0) :
    iIndepFun (fun i => ginibreBrownianOUHorizonPath (B i) (Z i) rate T) P := by
  have := Fintype.ofFinite ι
  have hmB : ∀ i, Measurable (fun ω t => B i t ω) := fun i =>
    Measurable.of_eval (fun t => aemeasurable_iff_measurable.mp ((hB i).aemeasurable t))
  have hp := independent_coordinate_pairs_of_independent_families P Z
    (fun i ω t => B i t ω) hZ hmB hiZ hiB hind
  let f : ℝ × (ℝ≥0 → ℝ) → C(Icc (0 : ℝ≥0) T, ℝ) :=
    fun p => ginibreScalarOUPairHorizon rate T (p.1, ginibreScalarBrownianNormalize p.2)
  have hf : Measurable f := (ginibreScalarOUPairHorizon_measurable rate T).comp
    (measurable_fst.prodMk (ginibreScalarBrownianNormalize_measurable.comp measurable_snd))
  have hi := hp.comp (fun _ => f) (fun _ => hf)
  apply hi.congr
  intro i
  exact ginibreScalarOUPairHorizon_actual (B i) P (hB i) (Z i) rate T

end
end GinibrePoincare
