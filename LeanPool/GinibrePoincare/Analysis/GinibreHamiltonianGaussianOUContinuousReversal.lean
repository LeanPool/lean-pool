/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGaussianOUContinuousReversal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUWholeReversal
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousNoisePath

/-!
# Ginibre Hamiltonian Gaussian OU continuous reversal

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownianOU_stationary_continuous_horizon_law_reversal`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem continuousMap_law_eq_of_whole_domain_path_law_eq {Ω D E : Type*}
    [MeasurableSpace Ω] [TopologicalSpace D] [TopologicalSpace.SeparableSpace D] [Nonempty D]
    [TopologicalSpace E] [SecondCountableTopology E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(D, E)] [BorelSpace C(D, E)] [PolishSpace C(D, E)]
    (P : Measure Ω) (X Y : Ω → C(D, E)) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : P.map (fun ω t => X ω t) = P.map (fun ω t => Y ω t)) :
    P.map X = P.map Y := by
  let d := TopologicalSpace.denseSeq D
  let f : C(D, E) → ℕ → E := fun x k => x (d k)
  have hf : MeasurableEmbedding f :=
    (continuous_pi (fun k => continuous_eval_const (d k))).measurableEmbedding (by
      intro x y h
      apply DFunLike.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq D).equalizer x.continuous y.continuous h)
  have hXm : Measurable (fun ω t => X ω t) :=
    Measurable.of_eval (fun t => (continuous_eval_const t).measurable.comp hX)
  have hYm : Measurable (fun ω t => Y ω t) :=
    Measurable.of_eval (fun t => (continuous_eval_const t).measurable.comp hY)
  let R : (D → E) → ℕ → E := fun x k => x (d k)
  have hR : Measurable R := Measurable.of_eval (fun k => measurable_pi_apply (d k))
  apply hf.map_injective
  rw [Measure.map_map hf.measurable hX, Measure.map_map hf.measurable hY]
  have hh := congrArg (Measure.map R) hlaw
  rw [Measure.map_map hR hXm, Measure.map_map hR hYm] at hh
  exact hh

/-- The scalar Brownian Ornstein–Uhlenbeck path with rate `rate`, noise scale `√rate` and
initial value `Z ω`, restricted to `[0, T]` (the zero path if it is not continuous). -/
def ginibreBrownianOUHorizonPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (Z : Ω → ℝ) (rate T : ℝ≥0) (ω : Ω) : C(Icc (0 : ℝ≥0) T, ℝ) :=
  ContinuousMap.mkD (fun t => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t.val ω) 0

theorem ginibreBrownianOUHorizonPath_ae {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (Z : Ω → ℝ) (rate T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ≥0) T,
      ginibreBrownianOUHorizonPath B Z rate T ω t =
        ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t.val ω := by
  filter_upwards [hB.cont] with ω hω
  have hN : Continuous (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) :=
    continuous_const.mul (hω.comp continuous_real_toNNReal)
  have hc : Continuous (fun t : Icc (0 : ℝ≥0) T =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t.val ω) :=
    (drivenOUPath_continuous rate (Z ω) _ hN).comp
      (NNReal.continuous_coe.comp continuous_subtype_val)
  intro t
  simp [ginibreBrownianOUHorizonPath, ContinuousMap.mkD, hc]

/-- The Borel σ-algebra on continuous real paths over the horizon `[0, T]` in `ℝ≥0`. -/
local instance instBorelGinibreHamiltonianGaussianOUContinuousReversal104 (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ≥0) T, ℝ) := borel _
local instance (T : ℝ≥0) : BorelSpace C(Icc (0 : ℝ≥0) T, ℝ) := ⟨rfl⟩
local instance (T : ℝ≥0) : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, ⟨le_rfl, zero_le⟩⟩⟩

/-- The time reversal `t ↦ T - t` of the interval `[0, T]` in `ℝ≥0`. -/
def ginibreOUHorizonReverseTime (T : ℝ≥0) : C(Icc (0 : ℝ≥0) T, Icc (0 : ℝ≥0) T) :=
  ⟨fun t => ⟨T-t.val, ⟨zero_le, tsub_le_self⟩⟩, by fun_prop⟩

theorem ginibreBrownianOUHorizonPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasGaussianLaw Z P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate T : ℝ≥0) :
    Measurable (ginibreBrownianOUHorizonPath B Z rate T) := by
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply (aemeasurable_iff_measurable (μ := P)).mp
  exact ((ginibreBrownianOU_gaussian_initial_isGaussianProcess P B hB Z hZ hind rate).aemeasurable
      t.val).congr
    (by filter_upwards [ginibreBrownianOUHorizonPath_ae B P hB Z rate T] with ω hω; exact (hω
          t).symm)

theorem ginibreBrownianOU_stationary_continuous_horizon_law_reversal
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1 / 2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate T : ℝ≥0) :
    P.map (ginibreBrownianOUHorizonPath B Z rate T) =
      P.map (fun ω => (ginibreBrownianOUHorizonPath B Z rate T ω).comp (ginibreOUHorizonReverseTime
          T)) := by
  have hm := ginibreBrownianOUHorizonPath_measurable B P hB Z hZ.hasGaussianLaw hind rate T
  have hr : Measurable (fun ω => (ginibreBrownianOUHorizonPath B Z rate T ω).comp
      (ginibreOUHorizonReverseTime T)) := by
    apply ginibre_measurable_continuousMap_of_evaluations
    intro t
    exact (continuous_eval_const (ginibreOUHorizonReverseTime T t)).measurable.comp hm
  apply continuousMap_law_eq_of_whole_domain_path_law_eq P _ _ hm hr
  have hx : (fun ω t => ginibreBrownianOUHorizonPath B Z rate T ω t) =ᵐ[P]
      (fun ω => fun t : Icc (0 : ℝ≥0) T => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω)
          t.val ω) := by
    filter_upwards [ginibreBrownianOUHorizonPath_ae B P hB Z rate T] with ω hω
    exact funext hω
  have hy : (fun ω t => ((ginibreBrownianOUHorizonPath B Z rate T ω).comp
      (ginibreOUHorizonReverseTime T)) t) =ᵐ[P]
      (fun ω => fun t : Icc (0 : ℝ≥0) T => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω)
        ((T-t.val : ℝ≥0) : ℝ) ω) := by
    filter_upwards [ginibreBrownianOUHorizonPath_ae B P hB Z rate T] with ω hω
    funext t
    exact hω (ginibreOUHorizonReverseTime T t)
  rw [Measure.map_congr hx, Measure.map_congr hy]
  exact ginibreBrownianOU_stationary_whole_horizon_law_reversal B P hB Z hZ hind rate T

end
end GinibrePoincare
