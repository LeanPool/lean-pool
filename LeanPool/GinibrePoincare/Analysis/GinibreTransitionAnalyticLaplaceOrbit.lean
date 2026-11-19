/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLaplaceOrbit.lean.
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

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Ginibre transition analytic Laplace orbit

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `actualContractionLaplace_orbit_derivative`, `actualContractionLaplace_commutes`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Literal translation of a Bochner tail integral. -/
theorem actualBochnerTail_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (t : ℝ) :
    (∫ s in Ioi (0 : ℝ), f (s+t))=∫ s in Ioi t, f s := by
  have hm := measurePreserving_add_right (volume : Measure ℝ) t
  have he : MeasurableEmbedding (fun s : ℝ => s+t) :=
    (Homeomorph.addRight t).measurableEmbedding
  have hi : (fun s : ℝ => s+t) '' Ioi 0=Ioi t := by
    ext s
    constructor
    · rintro ⟨a, ha, rfl⟩
      change 0<a at ha
      change t<a+t
      linarith
    · intro hs
      refine ⟨s-t,?_, by ring⟩
      change t<s at hs
      change 0<s-t
      linarith
  have h := hm.setIntegral_image_emb he f (Ioi 0)
  rw [hi] at h
  exact h.symm

/-- The genuine normalized Laplace transform of a strongly continuous
contraction family is Bochner integrable. -/
theorem actualContractionLaplace_integrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖) (c : ℝ) (hc : 0 < c) (u : E) :
    IntegrableOn (fun s : ℝ => (c*Real.exp (-c*s)) • A s.toNNReal u) (Ioi 0) := by
  have hs : Continuous (fun s : ℝ => (c*Real.exp (-c*s)) • A s.toNNReal u) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).smul
      ((hcont u).comp continuous_real_toNNReal)
  apply ((integrableOn_exp_mul_Ioi (show -c<0 by linarith) 0).const_mul (c*‖u‖)).mono'
    hs.aestronglyMeasurable
  filter_upwards [] with s
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le (Real.exp_pos _).le)]
  calc
    _ ≤ (c*Real.exp (-c*s))*‖u‖ := mul_le_mul_of_nonneg_left (hbound _ _)
      (mul_nonneg hc.le (Real.exp_pos _).le)
    _ = (c*‖u‖)*Real.exp (-c*s) := by ring

/-- Genuine semigroup and normalized Bochner Laplace integral give the exact
resolvent orbit formula, before any generator-domain identification. -/
theorem actualContractionLaplace_orbit_formula {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖)
    (hadd : ∀ s t u, A (s + t) u = A s (A t u))
    (c : ℝ) (hc : 0 < c) (u : E) (t : ℝ≥0) :
    A t (∫ s in Ioi (0 : ℝ), (c*Real.exp (-c*s)) • A s.toNNReal u) =
      Real.exp (c*(t : ℝ)) •
        ((∫ s in Ioi (0 : ℝ), (c*Real.exp (-c*s)) • A s.toNNReal u)-
          ∫ s in (0 : ℝ)..(t : ℝ), (c*Real.exp (-c*s)) • A s.toNNReal u) := by
  let F := fun s : ℝ => (c*Real.exp (-c*s)) • A s.toNNReal u
  have hi : IntegrableOn F (Ioi 0) := actualContractionLaplace_integrable A hcont hbound c hc u
  have hit : IntegrableOn F (Ioi (t : ℝ)) := hi.mono_set (Ioi_subset_Ioi t.property)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hit
  have htail : (∫ s in Ioi (t : ℝ), F s)=
      (∫ s in Ioi (0 : ℝ), F s)-(∫ s in (0 : ℝ)..(t : ℝ), F s) := by
    exact eq_sub_of_add_eq' hsplit
  have hexp (s : ℝ) : Real.exp (c*(t : ℝ))*(c*Real.exp (-c*(s+(t : ℝ))))=
      c*Real.exp (-c*s) := by
    calc
      _ = c*(Real.exp (c*(t : ℝ))*Real.exp (-c*(s+(t : ℝ)))) := by ring
      _ = c*Real.exp (c*(t : ℝ)+(-c*(s+(t : ℝ)))) := by rw [Real.exp_add]
      _ = c*Real.exp (-c*s) := by congr 2; ring
  have hpoint : (fun s => A t (F s)) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun s => Real.exp (c*(t : ℝ)) • F (s+(t : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := hs.le
    have hn : (s+(t : ℝ)).toNNReal=t+s.toNNReal := by
      apply NNReal.eq
      simp only [NNReal.coe_add, Real.coe_toNNReal (s+(t : ℝ)) (add_nonneg hs0 t.property),
          Real.coe_toNNReal s hs0]
      ring
    dsimp only [F]
    rw [map_smul, smul_smul, hexp, hn, hadd]
  change A t (∫ s in Ioi (0 : ℝ), F s)=_
  rw [← (A t).integral_comp_comm hi, integral_congr_ae hpoint, integral_smul,
    actualBochnerTail_translate F (t : ℝ), htail]

/-- Actual semigroup orbits through the genuine normalized Laplace range are
differentiable; their derivative follows from the literal integral formula. -/
theorem actualContractionLaplace_orbit_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖)
    (hadd : ∀ s t u, A (s + t) u = A s (A t u))
    (c : ℝ) (hc : 0 < c) (u : E) (t : ℝ) (ht : 0 < t) :
    let r := ∫ s in Ioi (0 : ℝ), (c*Real.exp (-c*s)) • A s.toNNReal u
    HasDerivAt (fun s : ℝ => A s.toNNReal r)
      (c • (A t.toNNReal r-A t.toNNReal u)) t := by
  dsimp only
  let F := fun s : ℝ => (c*Real.exp (-c*s)) • A s.toNNReal u
  let r := ∫ s in Ioi (0 : ℝ), F s
  let J := fun s : ℝ => ∫ q in (0 : ℝ)..s, F q
  have hFc : Continuous F :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).smul
      ((hcont u).comp continuous_real_toNNReal)
  have hJ : HasDerivAt J (F t) t :=
    intervalIntegral.integral_hasDerivAt_right (hFc.intervalIntegrable 0 t)
      hFc.aestronglyMeasurable.stronglyMeasurableAtFilter hFc.continuousAt
  have hExp : HasDerivAt (fun s : ℝ => Real.exp (c*s)) (c*Real.exp (c*t)) t :=
    (((hasDerivAt_id t).const_mul c).exp).congr_deriv (by simp only [id_eq]; ring)
  have hder := hExp.smul ((hasDerivAt_const t r).sub hJ)
  have hEq : (fun s : ℝ => A s.toNNReal r) =ᶠ[𝓝 t]
      (fun s => Real.exp (c*s) • (r-J s)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    have hh := actualContractionLaplace_orbit_formula A hcont hbound hadd c hc u s.toNNReal
    simpa only [Real.coe_toNNReal s hs.le] using hh
  have hOrbit : A t.toNNReal r=Real.exp (c*t) • (r-J t) := by
    have hh := actualContractionLaplace_orbit_formula A hcont hbound hadd c hc u t.toNNReal
    simpa only [Real.coe_toNNReal t ht.le] using hh
  have hCancel : Real.exp (c*t)*(c*Real.exp (-c*t))=c := by
    calc
      _ = c*(Real.exp (c*t)*Real.exp (-c*t)) := by ring
      _ = c*Real.exp (c*t+(-c*t)) := by rw [Real.exp_add]
      _ = c := by simp
  have hDerivative : (c*Real.exp (c*t)) • (r-J t)+Real.exp (c*t) • (0-F t)=
      c • (A t.toNNReal r-A t.toNNReal u) := by
    rw [mul_smul,← hOrbit, zero_sub, smul_neg]
    dsimp only [F]
    rw [smul_smul, hCancel, smul_sub, sub_eq_add_neg]
  apply (hder.congr_deriv ?_).congr_of_eventuallyEq hEq
  change Real.exp (c*t) • (0-F t)+(c*Real.exp (c*t)) • (r-J t)=_
  rw [add_comm]
  exact hDerivative

/-- The genuine semigroup commutes with its actual normalized Laplace integral. -/
theorem actualContractionLaplace_commutes {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖ ≤ ‖u‖)
    (hadd : ∀ s t u, A (s + t) u = A s (A t u))
    (c : ℝ) (hc : 0 < c) (u : E) (t : ℝ≥0) :
    A t (∫ s in Ioi (0 : ℝ), (c*Real.exp (-c*s)) • A s.toNNReal u) =
      ∫ s in Ioi (0 : ℝ), (c*Real.exp (-c*s)) • A s.toNNReal (A t u) := by
  rw [← (A t).integral_comp_comm (actualContractionLaplace_integrable A hcont hbound c hc u)]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    dsimp only
    rw [map_smul]
    congr 1
    rw [← hadd, add_comm, hadd]

end
end GinibrePoincare
