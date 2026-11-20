/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryRadialProductAssembly.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryEntropyPiTensorization
public import LeanPool.GinibrePoincare.Analysis.StrongConvexRadialProductLSI
public import Mathlib.Analysis.Calculus.Deriv.Pi
/-!
# Alternative Bakry Emery radial product assembly

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmery_radiusProduct_lsi_of_factor_lsi`.
-/

@[expose] public section
open MeasureTheory Set
open scoped NNReal ContDiff
namespace GinibrePoincare
noncomputable section

theorem bakryRadius_update_lipschitz {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (i : ι) : LipschitzWith 1 (Function.update x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist a b)).mpr
  intro j
  by_cases hj : j = i
  · subst j; simp
  · simp [Function.update_of_ne hj, dist_nonneg]

theorem bakryRadius_section_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (x : ι → ℝ) (i : ι) (y : ℝ) :
    deriv (fun t => f (Function.update x i t)) y =
      fderiv ℝ f (Function.update x i y) (Pi.single i 1) := by
  exact ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt y
    (hasDerivAt_update x i y)).deriv

theorem bakryRadius_coordinate_energy_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (f : (ι → ℝ) → ℝ)
    (_ : ContDiff ℝ 1 f) {K : ℝ≥0} (hLip : LipschitzWith K f) (i : ι) :
    Integrable (fun x => (fderiv ℝ f x (Pi.single i 1))^2) μ := by
  have hm := (measurable_fderiv_apply_const ℝ f (Pi.single i 1)).pow_const 2
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound hm.aestronglyMeasurable ((K : ℝ)^2)
  filter_upwards [] with x
  have hb := (fderiv ℝ f x).le_opNorm (Pi.single i 1)
  have hK := norm_fderiv_le_of_lipschitz ℝ hLip (x₀ := x)
  have hdir : ‖(Pi.single i 1 : ι → ℝ)‖ = 1 := by rw [Pi.norm_single]; norm_num
  rw [hdir, mul_one, Real.norm_eq_abs] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [abs_nonneg (fderiv ℝ f x (Pi.single i 1)), sq_abs (fderiv ℝ f x (Pi.single i 1))]

/-- A tensorization reduction. The single-radius inequalities are explicit inputs;
actual confinement-specific inputs are discharged in the final application. -/
theorem bakryRadiusPi_lsi_of_factor_lsi (n : ℕ) (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (κ : ℝ) (_ : 0 ≤ κ)
    (hLSI : ∀ (i : Fin (n + 1)) (g : ℝ → ℝ), ContDiff ℝ 1 g →
      ∀ {K : ℝ≥0}, LipschitzWith K g → ∀ C : ℝ, 0 ≤ C → (∀ r, |g r| ≤ C) →
      squareEntropy (μ i) g ≤ κ * ∫ r, (deriv g r)^2 ∂μ i)
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ≥0}
    (hLip : LipschitzWith K f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    squareEntropy (Measure.pi μ) f ≤ κ * ∫ x,
      directionalEnergy (fun i : Fin (n+1) => Pi.single i 1) f x ∂Measure.pi μ := by
  have ht := bakryEntropyPi_tensorization_bounded (fun _ : Fin (n+1) => ℝ)
    μ f hf.continuous.measurable C hC hb
  have hcoord (i : Fin (n+1)) : (∫ x, bakryEntropyPiCoordinate μ f i x ∂Measure.pi μ) ≤
      κ * ∫ x, (fderiv ℝ f x (Pi.single i 1))^2 ∂Measure.pi μ := by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
    let ν := Measure.pi (fun j : Fin n => μ (i.succAbove j))
    have hp := (measurePreserving_piFinSuccAbove μ i).symm e
    have hg := hf.continuous.measurable.comp e.symm.measurable
    have hE : Integrable (fun x => squareEntropy (μ i) (fun a => f (i.insertNth a x))) ν := by
      have hh := bakryEntropy_fiber_integrable_bounded ν (μ i)
        (fun p => f (i.insertNth p.2 p.1)) (hg.comp measurable_swap) C hC (fun p => hb _)
      exact hh
    have hG := hp.integrable_comp_of_integrable
      (bakryRadius_coordinate_energy_integrable (Measure.pi μ) f hf hLip i)
    have hGi : Integrable (fun x => ∫ a, (fderiv ℝ f (i.insertNth a x) (Pi.single i 1))^2 ∂μ i) ν :=
      hG.integral_prod_right
    have hs (x : Fin n → ℝ) : squareEntropy (μ i) (fun a => f (i.insertNth a x)) ≤
        κ * ∫ a, (fderiv ℝ f (i.insertNth a x) (Pi.single i 1))^2 ∂μ i := by
      let b : Fin (n+1) → ℝ := i.insertNth 0 x
      have hh := hLSI i (fun a => f (Function.update b i a))
        (hf.comp (contDiff_update 1 b i)) (hLip.comp (bakryRadius_update_lipschitz b i)) C hC
        (fun a => hb _)
      simp_rw [bakryRadius_section_deriv f hf b i] at hh
      simpa only [b, Fin.update_insertNth] using hh
    rw [bakryEntropyFin_coordinate_integral n (fun _ => ℝ) μ f hf.continuous.measurable C hC hb i]
    have hle := integral_mono hE (hGi.const_mul κ) hs
    rw [integral_const_mul] at hle
    have hid : (∫ x, (fderiv ℝ f x (Pi.single i 1))^2 ∂Measure.pi μ) =
        ∫ x, (∫ a, (fderiv ℝ f (i.insertNth a x) (Pi.single i 1))^2 ∂μ i) ∂ν := by
      rw [← hp.integral_comp e.symm.measurableEmbedding (fun x => (fderiv ℝ f x (Pi.single i 1))^2)]
      exact integral_prod_symm _ hG
    rw [hid]
    exact hle
  calc
    _ ≤ ∑ i, κ * ∫ x, (fderiv ℝ f x (Pi.single i 1))^2 ∂Measure.pi μ :=
      ht.trans (Finset.sum_le_sum (fun i _ => hcoord i))
    _ = _ := by
      unfold directionalEnergy
      rw [integral_finsetSum Finset.univ (fun i _ =>
        bakryRadius_coordinate_energy_integrable (Measure.pi μ) f hf hLip i), Finset.mul_sum]

/-- Product-radius assembly from single-radius inequalities; this is a reduction
whose factor inputs are discharged by the independent Langevin proof. -/
theorem bakryEmery_radiusProduct_lsi_of_factor_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (hFactors : ∀ (i : Fin n) (g : ℝ → ℝ), ContDiff ℝ 1 g →
      ∀ {K : ℝ≥0}, LipschitzWith K g → ∀ C : ℝ, 0 ≤ C → (∀ r, |g r| ≤ C) →
      squareEntropy ((potentialSquaredRadiusLaw n i.val V).map Real.sqrt) g ≤
        (2/((n : ℝ)*ρ)) * ∫ r, (deriv g r)^2
          ∂((potentialSquaredRadiusLaw n i.val V).map Real.sqrt))
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ≥0}
    (hLip : LipschitzWith K f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    squareEntropy (potentialRadiusProduct n V) f ≤ (2/((n : ℝ)*ρ)) * ∫ x,
      directionalEnergy (fun i : Fin n => Pi.single i 1) f x ∂potentialRadiusProduct n V := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let μ := fun i : Fin (m+1) => (potentialSquaredRadiusLaw (m+1) i.val V).map Real.sqrt
  let (i : Fin (m+1)) : IsProbabilityMeasure (μ i) := by
    have hi := rhoConvexPotential_radial_density_integrable (m+1) i.val hn ρ hρ hV hrot hc
    change IsProbabilityMeasure ((potentialSquaredRadiusLaw (m+1) i.val V).map Real.sqrt)
    rw [← radialConfinementProbabilityDensity_eq_sqrt_map (m+1) i.val V hV.continuous hi]
    exact radialConfinementProbabilityDensity_isProbability (m+1) i.val _
      (hV.continuous.comp Complex.continuous_ofReal) hi
  exact bakryRadiusPi_lsi_of_factor_lsi m μ (2/(((m+1 : ℕ) : ℝ)*ρ))
    (by positivity) hFactors f hf hLip C hC hb

end
end GinibrePoincare
