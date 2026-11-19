/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianConfigurationOUReference.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCompactPathWeight
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUProductReversal

/-! The genuine independent stationary scalar OU product, assembled into a
configuration-valued continuous path. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The Borel σ-algebra on continuous real paths over the horizon `[0, T]` in `ℝ≥0`. -/
local instance instBorelGinibreHamiltonianConfigurationOUReference1 (T : ℝ≥0) : MeasurableSpace
    C(Icc (0 : ℝ≥0) T, ℝ) := borel _
local instance instBorelGinibreHamiltonianConfigurationOUReference2 (T : ℝ≥0) : BorelSpace C(Icc (0
    : ℝ≥0) T, ℝ) := ⟨rfl⟩
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance instBorelGinibreHamiltonianConfigurationOUReference3 (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance instBorelGinibreHamiltonianConfigurationOUReference4 (n : ℕ) (T : ℝ≥0) : BorelSpace
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
local instance instBorelGinibreHamiltonianConfigurationOUReference5 (T : ℝ≥0) : Nonempty (Icc (0 :
    ℝ) (T : ℝ)) := ⟨⟨0, ⟨le_rfl, T.property⟩⟩⟩

/-- The continuous map from the real interval `[0, T]` to the interval `[0, T]` in `ℝ≥0`,
`t ↦ t.toNNReal`. -/
def ginibreOURealHorizonToNNReal (T : ℝ≥0) :
    C(Icc (0 : ℝ) (T : ℝ), Icc (0 : ℝ≥0) T) :=
  ⟨fun t => ⟨t.val.toNNReal, ⟨zero_le, by
    simpa using (Real.toNNReal_le_toNNReal t.property.2)⟩⟩,
    by fun_prop⟩

/-- Assembles `2n` real paths on `[0, T]` into a configuration path whose coordinate `j` at
time `t` is `(x (j, 0) t + I * x (j, 1) t) / √n`. -/
def ginibreConfigurationOUAssemble (n : ℕ) (T : ℝ≥0)
    (x : (Fin n × Fin 2) → C(Icc (0 : ℝ≥0) T, ℝ)) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ⟨fun t j => ((x (j, 0) (ginibreOURealHorizonToNNReal T t) : ℂ) +
      Complex.I * (x (j, 1) (ginibreOURealHorizonToNNReal T t) : ℂ)) / Real.sqrt n,
    by apply continuous_pi; intro j; fun_prop⟩

theorem ginibreConfigurationOUAssemble_measurable (n : ℕ) (T : ℝ≥0) :
    Measurable (ginibreConfigurationOUAssemble n T) := by
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply Measurable.of_eval
  intro j
  unfold ginibreConfigurationOUAssemble
  exact ((((continuous_eval_const (ginibreOURealHorizonToNNReal T t)).measurable.comp
    (measurable_pi_apply (j, 0))).complex_ofReal).add
    (measurable_const.mul (((continuous_eval_const (ginibreOURealHorizonToNNReal T
        t)).measurable.comp
      (measurable_pi_apply (j, 1))).complex_ofReal))).div_const _

theorem ginibreOURealHorizonToNNReal_reverse (T : ℝ≥0)
    (t : Icc (0 : ℝ) (T : ℝ)) :
    ginibreOURealHorizonToNNReal T
      (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property t) =
    ginibreOUHorizonReverseTime T (ginibreOURealHorizonToNNReal T t) := by
  apply Subtype.ext
  apply NNReal.eq
  change (((T : ℝ) - t.val).toNNReal : ℝ) = ((T - t.val.toNNReal : ℝ≥0) : ℝ)
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr t.property.2),
    NNReal.coe_sub (by simpa using Real.toNNReal_le_toNNReal t.property.2),
    Real.coe_toNNReal _ t.property.1]

theorem ginibreConfigurationOUAssemble_reverse (n : ℕ) (T : ℝ≥0)
    (x : (Fin n × Fin 2) → C(Icc (0 : ℝ≥0) T, ℝ)) :
    ginibreConfigurationOUAssemble n T
      (fun i => (x i).comp (ginibreOUHorizonReverseTime T)) =
    (ginibreConfigurationOUAssemble n T x).comp
      (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property) := by
  ext t j
  simp only [ginibreConfigurationOUAssemble, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
    ginibreOURealHorizonToNNReal_reverse]

/-- Independent copies of the actual stationary scalar Brownian-convolution OU
law, scaled to the `n`-particle Gaussian reference equilibrium. -/
def ginibreConfigurationOUReferenceLaw {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (Z : Ω → ℝ) (rate T : ℝ≥0) :
    Measure C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  (Measure.pi (fun _ : Fin n × Fin 2 =>
    P.map (ginibreBrownianOUHorizonPath B Z rate T))).map (ginibreConfigurationOUAssemble n T)

theorem ginibreConfigurationOUReferenceLaw_reverse {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1 / 2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate T : ℝ≥0) :
    (ginibreConfigurationOUReferenceLaw n B P Z rate T).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    ginibreConfigurationOUReferenceLaw n B P Z rate T := by
  let μ := P.map (ginibreBrownianOUHorizonPath B Z rate T)
  let R : C(Icc (0 : ℝ≥0) T, ℝ) → C(Icc (0 : ℝ≥0) T, ℝ) :=
    fun x => x.comp (ginibreOUHorizonReverseTime T)
  have hm := ginibreBrownianOUHorizonPath_measurable B P hB Z hZ.hasGaussianLaw hind rate T
  have hR : Measurable R := (ContinuousMap.continuous_precomp (ginibreOUHorizonReverseTime
      T)).measurable
  have hμ : μ.map R = μ := by
    rw [Measure.map_map hR hm]
    exact (ginibreBrownianOU_stationary_continuous_horizon_law_reversal B P hB Z hZ hind rate
        T).symm
  have : IsProbabilityMeasure μ := (by infer_instance)
  have : IsProbabilityMeasure (μ.map R) := (by infer_instance)
  have hpi : (Measure.pi (fun _ : Fin n × Fin 2 => μ)).map (fun x i => R (x i)) =
      Measure.pi (fun _ : Fin n × Fin 2 => μ) := by
    rw [Measure.pi_map_pi (fun _ => hR.aemeasurable)]
    simp_rw [hμ]
  have ha := ginibreConfigurationOUAssemble_measurable n T
  have hr : Measurable (fun x : C(Icc (0 : ℝ) (T : ℝ), Configuration n) =>
      x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime (T : ℝ)
        T.property)).measurable
  unfold ginibreConfigurationOUReferenceLaw
  rw [Measure.map_map hr ha]
  have he : (fun x => (ginibreConfigurationOUAssemble n T x).comp
      (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
      (ginibreConfigurationOUAssemble n T) ∘ (fun x i => R (x i)) := by
    funext x
    exact (ginibreConfigurationOUAssemble_reverse n T x).symm
  change (Measure.pi (fun _ : Fin n × Fin 2 => μ)).map (fun x =>
    (ginibreConfigurationOUAssemble n T x).comp (ginibreHamiltonianCompactReverseTime (T : ℝ)
        T.property)) =
    (Measure.pi (fun _ : Fin n × Fin 2 => μ)).map (ginibreConfigurationOUAssemble n T)
  rw [he]
  have hh : Measurable (fun x : (Fin n × Fin 2) → C(Icc (0 : ℝ≥0) T, ℝ) => fun i => R (x i)) :=
    Measurable.of_eval (fun i => hR.comp (measurable_pi_apply i))
  exact (Measure.map_map ha hh).symm.trans (congrArg (Measure.map (ginibreConfigurationOUAssemble n
      T)) hpi)

end
end GinibrePoincare
