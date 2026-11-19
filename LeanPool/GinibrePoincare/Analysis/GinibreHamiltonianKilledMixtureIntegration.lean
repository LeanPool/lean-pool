/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianKilledMixtureIntegration.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInitialMeasureIdentification
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Ginibre Hamiltonian killed mixture integration

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibre_killed_product_mixture`.
-/

@[expose] public section

open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Tonelli integration of actual fixed-initial killed identities, with exact
initial likelihood cancellation. This lemma is instantiated with the proved
Brownian/Girsanov identity, never with a desired stationary conclusion. -/
theorem ginibre_killed_product_mixture {A Ω E : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω] [MeasurableSpace E]
    (γ : Measure A) (P : Measure Ω) [SFinite P]
    (C O : A × Ω → E) (hC : Measurable C) (hO : Measurable O)
    (S : Set E) (hS : MeasurableSet S) (a : E → ENNReal) (ha : Measurable a)
    (w e : A → ENNReal) (hw : Measurable w) (_ : Measurable e)
    (hCancel : ∀ᵐ z ∂γ, w z * e z = 1)
    (hFiber : ∀ᵐ z ∂γ,
      (P.map (fun ω => C (z, ω))).restrict S =
      (P.withDensity (fun ω => e z * S.indicator a (O (z, ω)))).map (fun ω => O (z, ω))) :
    (((γ.prod P).withDensity (fun x => w x.1)).map C).restrict S =
      ((γ.prod P).map O).withDensity (S.indicator a) := by
  classical
  ext s hs
  have hCS : MeasurableSet (C ⁻¹' (s ∩ S)) := hC (hs.inter hS)
  rw [Measure.restrict_apply hs, Measure.map_apply hC (hs.inter hS), withDensity_apply _ hCS]
  rw [← lintegral_indicator hCS]
  rw [withDensity_apply _ hs,← lintegral_indicator hs]
  rw [lintegral_map ((ha.indicator hS).indicator hs) hO]
  have hL : Measurable ((C ⁻¹' (s ∩ S)).indicator (fun x : A × Ω => w x.1)) :=
    (hw.comp measurable_fst).indicator hCS
  have hR : Measurable (fun x : A × Ω => s.indicator (S.indicator a) (O x)) :=
    ((ha.indicator hS).indicator hs).comp hO
  rw [lintegral_prod _ hL.aemeasurable, lintegral_prod _ hR.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hFiber, hCancel] with z hf hc
  have hCz : Measurable (fun ω => C (z, ω)) := hC.comp measurable_prodMk_left
  have hOz : Measurable (fun ω => O (z, ω)) := hO.comp measurable_prodMk_left
  have hh := congrArg (fun μ : Measure E => μ s) hf
  rw [Measure.restrict_apply hs, Measure.map_apply hCz (hs.inter hS), Measure.map_apply hOz hs,
    withDensity_apply _ (hOz hs)] at hh
  have hLeft : (∫⁻ ω, (C ⁻¹' (s ∩ S)).indicator (fun x : A × Ω => w x.1) (z, ω) ∂P) =
      w z * P ((fun ω => C (z, ω)) ⁻¹' (s ∩ S)) := by
    have hi : (fun ω => (C ⁻¹' (s ∩ S)).indicator (fun x : A × Ω => w x.1) (z, ω)) =
        ((fun ω => C (z, ω)) ⁻¹' (s ∩ S)).indicator (fun _ => w z) := by
      funext ω
      rfl
    rw [hi, lintegral_indicator (hCz (hs.inter hS)), lintegral_const]
    rw [Measure.restrict_apply_univ]
  rw [hLeft, hh]
  have hfm : Measurable (fun ω => e z * S.indicator a (O (z, ω))) :=
    ((ha.indicator hS).comp hOz).const_mul (e z)
  rw [← lintegral_const_mul (μ := P.restrict ((fun ω => O (z, ω)) ⁻¹' s)) (w z) hfm]
  rw [← lintegral_indicator (hOz hs)]
  apply lintegral_congr
  intro ω
  by_cases hx : O (z, ω) ∈ s
  · simp only [Set.indicator_of_mem (show ω ∈ (fun ω => O (z, ω)) ⁻¹' s from hx),
      Set.indicator_of_mem hx,← mul_assoc, hc, one_mul]
  · simp [hx]

end
end GinibrePoincare
