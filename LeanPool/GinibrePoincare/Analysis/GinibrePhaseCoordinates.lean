/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePhaseCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevMultipliers
public import LeanPool.GinibrePoincare.Analysis.GinibreDirectionalCoordinates
public import LeanPool.GinibrePoincare.Analysis.RadialConvolutionInvariance
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure

/-! # Real-linear phase coordinates and local Lebesgue transport -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

/-- Independent coordinate multiplication as an actual real-linear map. -/
def coordinatePhaseCLM (n : ℕ) (a : Fin n → ℂ) : Configuration n →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun i => a i • ContinuousLinearMap.proj i

@[simp] theorem coordinatePhaseCLM_apply (n : ℕ) (a : Fin n → ℂ) (z : Configuration n) :
    coordinatePhaseCLM n a z = coordinatePhase a z := by
  rfl

/-- Unit phases give a continuous real-linear equivalence. -/
def coordinatePhaseCLE (n : ℕ) (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    Configuration n ≃L[ℝ] Configuration n :=
  ContinuousLinearEquiv.equivOfInverse (coordinatePhaseCLM n a)
    (coordinatePhaseCLM n (fun i => (a i)⁻¹))
    (by
      intro z
      ext i
      have hne : a i ≠ 0 := by intro he; simpa [he] using ha i
      simp [coordinatePhaseCLM, hne])
    (by
      intro z
      ext i
      have hne : a i ≠ 0 := by intro he; simpa [he] using ha i
      simp [coordinatePhaseCLM, hne])

@[simp] theorem coordinatePhaseCLE_apply (n : ℕ) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ = 1) (z : Configuration n) :
    coordinatePhaseCLE n a ha z = coordinatePhase a z := rfl

theorem measurePreserving_coordinatePhaseCLE_volume (n : ℕ) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ = 1) :
    MeasurePreserving (coordinatePhaseCLE n a ha)
      (volume : Measure (Configuration n)) volume :=
  measurePreserving_coordinatePhase_volume n a ha

/-- Local Lebesgue integrability is transported through an actual volume-preserving
real-linear equivalence onto the preimage open set. -/
theorem locallyIntegrableOn_comp_volume_equiv (n : ℕ)
    {V : Type*} [NormedAddCommGroup V]
    (e : Configuration n ≃L[ℝ] Configuration n)
    (he : MeasurePreserving e (volume : Measure (Configuration n)) volume)
    (U : Set (Configuration n)) (hU : IsOpen U) (f : Configuration n → V)
    (hf : LocallyIntegrableOn f U volume) :
    LocallyIntegrableOn (f ∘ e) (e ⁻¹' U) volume := by
  apply (locallyIntegrableOn_iff (hU.preimage e.continuous).isLocallyClosed).mpr
  intro K hK hc
  have hi : IntegrableOn f (e '' K) volume := hf.integrableOn_compact_subset
    (by rintro _ ⟨x, hx, rfl⟩; exact hK hx) (hc.image e.continuous)
  exact (he.integrableOn_image e.toHomeomorph.toMeasurableEquiv.measurableEmbedding).mp hi

/-- A radial L² value is invariant a.e. under every fixed unit phase rotation,
with Lebesgue a.e. equality independent of the weighted density. -/
theorem ginibre_radial_L2_phase_ae (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    ∀ᵐ z ∂(volume : Measure (Configuration n)), u (coordinatePhase a z) = u z := by
  have hf' := (ginibre_ae_eq_iff_volume n hn _ _).mp hf
  have he := (measurePreserving_coordinatePhaseCLE_volume n a ha).quasiMeasurePreserving.ae_eq_comp
      hf'
  filter_upwards [hf', he] with z hz hz'
  exact hz'.trans ((radial_coordinatePhase hr a ha z).trans hz.symm)

end
end GinibrePoincare
