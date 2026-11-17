/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreWeakGradient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreRadialSobolevCore
public import LeanPool.GinibrePoincare.Analysis.GinibreIntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2Inverse

/-! # Weak gradients and closability for the Ginibre radial completion

Write `ρ` for the concrete, unnormalised real Lebesgue density. Testing with
`ρ ψ` avoids division by the density at collisions. The adjoint test is
`ρ ∂ψ + 2 (∂ρ) ψ`. These identities describe the distributional derivative of
`ρ² u`, and determine the gradient uniquely because `ρ > 0` almost everywhere
for the Ginibre measure. They do not assert the reverse approximation theorem
from an independently defined weak Sobolev space to the radial core.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- The real coordinate direction indexed by a particle and its real or imaginary component. -/
def ginibreCoordinateDirection {n : ℕ} (k : Fin n × Fin 2) : Configuration n :=
  if k.2 = 0 then realCoordinateDirection k.1 else imaginaryCoordinateDirection k.1

/-- A test function multiplied by the real density factor used in the weak-gradient
identities. -/
def ginibreWeakTest {n : ℕ} (ψ : Configuration n → ℝ) : Configuration n → ℝ :=
  fun z => ginibreLebesgueDensityReal n z * ψ z

/-- Density-weighted adjoint test encoding weak derivatives without division at collisions. -/
def ginibreWeakAdjointTest {n : ℕ} (k : Fin n × Fin 2)
    (ψ : Configuration n → ℝ) : Configuration n → ℝ :=
  fun z => ginibreLebesgueDensityReal n z * fderiv ℝ ψ z (ginibreCoordinateDirection k) +
    2 * fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k) * ψ z

theorem ginibreEuclideanGradient_coordinate {n : ℕ} (f : Configuration n → ℝ)
    (z : Configuration n) (k : Fin n × Fin 2) :
    ginibreEuclideanGradient f z k = fderiv ℝ f z (ginibreCoordinateDirection k) := by
  simp only [ginibreEuclideanGradient, ginibreCoordinateDirection]
  split_ifs <;> rfl

theorem ginibreLebesgueDensityReal_ne_zero_ae {n : ℕ} (hn : 0 < n) :
    ∀ᵐ z ∂ginibreMeasure n, ginibreLebesgueDensityReal n z ≠ 0 := by
  have hv := (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n).ae_le
    (vandermondeDensity_ne_zero_ae n)
  filter_upwards [hv] with z hz
  have hw : vandermondeWeight z ≠ 0 := by
    intro h
    exact hz (by simp [vandermondeDensity, h])
  unfold ginibreLebesgueDensityReal gaussianWeight
  exact mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (div_ne_zero (Nat.cast_ne_zero.mpr hn.ne') Real.pi_ne_zero)) hw)
    (Real.exp_ne_zero _)

theorem continuous_ginibreWeakTest {n : ℕ} {ψ : Configuration n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : Continuous (ginibreWeakTest ψ) :=
  (contDiff_ginibreLebesgueDensityReal n).continuous.mul hψ.continuous

theorem compactSupport_ginibreWeakTest {n : ℕ} {ψ : Configuration n → ℝ}
    (hc : HasCompactSupport ψ) : HasCompactSupport (ginibreWeakTest ψ) :=
  hc.mul_left

theorem continuous_ginibreWeakAdjointTest {n : ℕ} (k : Fin n × Fin 2)
    {ψ : Configuration n → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (ginibreWeakAdjointTest k ψ) := by
  exact ((contDiff_ginibreLebesgueDensityReal n).continuous.mul
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).add
    ((continuous_const.mul
      (((contDiff_ginibreLebesgueDensityReal n).continuous_fderiv (by simp)).clm_apply
        continuous_const)).mul hψ.continuous)

theorem compactSupport_ginibreWeakAdjointTest {n : ℕ} (k : Fin n × Fin 2)
    {ψ : Configuration n → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (ginibreWeakAdjointTest k ψ) :=
  ((hc.fderiv_apply (𝕜 := ℝ) _).mul_left).add hc.mul_left

/-- Integration by parts with density-multiplied tests, valid across collisions. -/
theorem ginibre_weak_integration_by_parts {n : ℕ} (hn : 0 < n)
    (f ψ : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (k : Fin n × Fin 2) :
    (∫ z, fderiv ℝ f z (ginibreCoordinateDirection k) * ginibreWeakTest ψ z
      ∂ginibreMeasure n) =
      -(∫ z, f z * ginibreWeakAdjointTest k ψ z ∂ginibreMeasure n) := by
  let ρ := ginibreLebesgueDensityReal n
  let Φ : Configuration n → ℝ := fun z => ρ z * ρ z * f z * ψ z
  have hρ := contDiff_ginibreLebesgueDensityReal n
  have hΦ : ContDiff ℝ ∞ Φ := ((hρ.mul hρ).mul hf).mul hψ
  have hΦc : HasCompactSupport Φ := hc.mul_left
  have hzero : (∫ z, fderiv ℝ Φ z (ginibreCoordinateDirection k)) = 0 := by
    unfold ginibreCoordinateDirection
    split_ifs
    · exact integral_fderiv_configuration_real_eq_zero Φ (hΦ.of_le (by simp)) hΦc k.1
    · exact integral_fderiv_configuration_imag_eq_zero Φ (hΦ.of_le (by simp)) hΦc k.1
  have hprod (z : Configuration n) :
      fderiv ℝ Φ z (ginibreCoordinateDirection k) =
        ρ z * (fderiv ℝ f z (ginibreCoordinateDirection k) * ginibreWeakTest ψ z) +
        ρ z * (f z * ginibreWeakAdjointTest k ψ z) := by
    have hdρ := (hρ.differentiable (by simp)).differentiableAt (x := z)
    have hdf := (hf.differentiable (by simp)).differentiableAt (x := z)
    have hdψ := (hψ.differentiable (by simp)).differentiableAt (x := z)
    change fderiv ℝ (((ρ * ρ) * f) * ψ) z _ = _
    rw [fderiv_mul ((hdρ.mul hdρ).mul hdf) hdψ,
      fderiv_mul (hdρ.mul hdρ) hdf, fderiv_mul hdρ hdρ]
    simp only [add_apply, smul_apply, smul_eq_mul]
    dsimp [ginibreWeakTest, ginibreWeakAdjointTest, ρ]
    ring
  have hi₁ : Integrable (fun z => ρ z *
      (fderiv ℝ f z (ginibreCoordinateDirection k) * ginibreWeakTest ψ z)) :=
    (hρ.continuous.mul (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      (continuous_ginibreWeakTest hψ))).integrable_of_hasCompactSupport
      ((compactSupport_ginibreWeakTest hc).mul_left.mul_left)
  have hi₂ : Integrable (fun z => ρ z * (f z * ginibreWeakAdjointTest k ψ z)) :=
    (hρ.continuous.mul (hf.continuous.mul (continuous_ginibreWeakAdjointTest k
      hψ))).integrable_of_hasCompactSupport
        ((compactSupport_ginibreWeakAdjointTest k hc).mul_left.mul_left)
  simp_rw [hprod] at hzero
  rw [integral_add hi₁ hi₂] at hzero
  rw [integral_ginibreMeasure_eq_density_volume hn,
    integral_ginibreMeasure_eq_density_volume hn]
  change _ * (∫ z, ρ z * _) = -(_ * (∫ z, ρ z * _))
  rw [show (∫ z, ρ z * (fderiv ℝ f z (ginibreCoordinateDirection k) *
    ginibreWeakTest ψ z)) = -(∫ z, ρ z * (f z * ginibreWeakAdjointTest k ψ z)) by
      linarith]
  ring

/-- A concrete weak-gradient identity using all smooth compact tests. -/
def IsGinibreWeakGradient (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) : Prop :=
  ∀ (k : Fin n × Fin 2) (ψ : Configuration n → ℝ),
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ z, g z k * ginibreWeakTest ψ z ∂ginibreMeasure n) =
        -(∫ z, u z * ginibreWeakAdjointTest k ψ z ∂ginibreMeasure n)

/-- Pairing with an L² test is continuous in the actual L² norm. -/
theorem continuous_L2_integral_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ) (hw : MemLp w 2 μ) :
    Continuous (fun u : Lp ℝ 2 μ => ∫ x, u x * w x ∂μ) := by
  have he : (fun u : Lp ℝ 2 μ => ∫ x, u x * w x ∂μ) =
      (fun u => inner ℝ u (hw.toLp w)) := by
    funext u
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  rw [he]
  exact continuous_id.inner continuous_const

/-- Coordinate pairing with an L² test is continuous for vector-valued gradients. -/
theorem continuous_ginibre_gradient_pairing (n : ℕ) (k : Fin n × Fin 2)
    (w : Configuration n → ℝ) (hw : MemLp w 2 (ginibreMeasure n)) :
    Continuous (fun g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) =>
      ∫ z, g z k * w z ∂ginibreMeasure n) := by
  let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
  have he : (fun g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) =>
      ∫ z, g z k * w z ∂ginibreMeasure n) =
      (fun g => ∫ z, (P.compLpL 2 (ginibreMeasure n) g) z * w z ∂ginibreMeasure n) := by
    funext g
    apply integral_congr_ae
    filter_upwards [P.coeFn_compLpL g] with z hz
    rw [hz]
    rfl
  rw [he]
  exact (continuous_L2_integral_mul _ w hw).comp (P.compLpL 2 _).continuous

/-- The concrete weak-gradient identities are closed under strong value-gradient convergence. -/
theorem isClosed_ginibre_weak_gradient_pairs (n : ℕ) (hn : 0 < n) :
    IsClosed {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      IsGinibreWeakGradient n p.1 p.2} := by
  let := ginibreMeasure_isProbabilityMeasure hn
  simp only [IsGinibreWeakGradient, Set.ofPred_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro ψ
  apply isClosed_iInter
  intro hψ
  apply isClosed_iInter
  intro hc
  exact isClosed_eq
    ((continuous_ginibre_gradient_pairing n k (ginibreWeakTest ψ)
      ((continuous_ginibreWeakTest hψ).memLp_of_hasCompactSupport
        (compactSupport_ginibreWeakTest hc))).comp continuous_snd)
    (((continuous_L2_integral_mul (ginibreMeasure n) (ginibreWeakAdjointTest k ψ)
      ((continuous_ginibreWeakAdjointTest k hψ).memLp_of_hasCompactSupport
        (compactSupport_ginibreWeakAdjointTest k hc))).comp continuous_fst).neg)

/-- Every actual radial core pair satisfies the concrete weak-gradient identities. -/
theorem radialSobolevCorePairs_weak_gradient (n : ℕ) (hn : 0 < n)
    (p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hp : p ∈ radialSobolevCorePairs n) : IsGinibreWeakGradient n p.1 p.2 := by
  obtain ⟨f, hf, hv, hg⟩ := hp
  intro k ψ hψ hc
  have hl : (∫ z, p.2 z k * ginibreWeakTest ψ z ∂ginibreMeasure n) =
      ∫ z, fderiv ℝ f z (ginibreCoordinateDirection k) * ginibreWeakTest ψ z
        ∂ginibreMeasure n := by
    apply integral_congr_ae
    filter_upwards [hg] with z hz
    rw [hz, ginibreEuclideanGradient_coordinate]
  have hr : (∫ z, p.1 z * ginibreWeakAdjointTest k ψ z ∂ginibreMeasure n) =
      ∫ z, f z * ginibreWeakAdjointTest k ψ z ∂ginibreMeasure n := by
    apply integral_congr_ae
    filter_upwards [hv] with z hz
    rw [hz]
  rw [hl, hr]
  exact ginibre_weak_integration_by_parts hn f ψ hf.1.1 hψ hc k

/-- Every pair in the radial completion has a concrete weak gradient. -/
theorem radialSobolevClosure_weak_gradient (n : ℕ) (hn : 0 < n)
    (p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hp : p ∈ radialSobolevClosure n) : IsGinibreWeakGradient n p.1 p.2 := by
  exact closure_minimal (fun q hq => radialSobolevCorePairs_weak_gradient n hn q hq)
    (isClosed_ginibre_weak_gradient_pairs n hn) hp

/-- The weak gradient is unique, despite the zeros of the Ginibre density at collisions. -/
theorem ginibre_weak_gradient_unique (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g h : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreWeakGradient n u g) (hh : IsGinibreWeakGradient n u h) : g = h := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have he (k : Fin n × Fin 2) : ∀ᵐ z ∂ginibreMeasure n, g z k = h z k := by
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
    have hglp : MemLp (fun z => g z k) 2 (ginibreMeasure n) := P.comp_memLp g
    have hhlp : MemLp (fun z => h z k) 2 (ginibreMeasure n) := P.comp_memLp h
    have hl : LocallyIntegrable (fun z => ginibreLebesgueDensityReal n z *
        (g z k - h z k)) (ginibreMeasure n) :=
      ((hglp.integrable (by norm_num)).sub (hhlp.integrable (by
        norm_num))).locallyIntegrable.continuous_mul (contDiff_ginibreLebesgueDensityReal
        n).continuous
    have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hl (fun ψ hψ hc => by
      have hw : MemLp (ginibreWeakTest ψ) 2 (ginibreMeasure n) :=
        (continuous_ginibreWeakTest hψ).memLp_of_hasCompactSupport
          (compactSupport_ginibreWeakTest hc)
      have hgint : Integrable (fun z => g z k * ginibreWeakTest ψ z) (ginibreMeasure n) :=
        hglp.integrable_mul hw
      have hhint : Integrable (fun z => h z k * ginibreWeakTest ψ z) (ginibreMeasure n) :=
        hhlp.integrable_mul hw
      have htest : (∫ z, ψ z • (ginibreLebesgueDensityReal n z * (g z k - h z k))
          ∂ginibreMeasure n) =
          (∫ z, g z k * ginibreWeakTest ψ z ∂ginibreMeasure n) -
            ∫ z, h z k * ginibreWeakTest ψ z ∂ginibreMeasure n := by
        rw [← integral_sub hgint hhint]
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by simp only [smul_eq_mul, ginibreWeakTest]; ring)
      rw [htest, hg k ψ hψ hc, hh k ψ hψ hc, sub_self])
    filter_upwards [hz, ginibreLebesgueDensityReal_ne_zero_ae hn] with z hz hρ
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hρ)
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr he] with z hz
  exact PiLp.ext hz

/-- The completion is the graph of a single-valued closed gradient operator. -/
theorem radialSobolevClosure_gradient_unique (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g h : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : (u, g) ∈ radialSobolevClosure n) (hh : (u, h) ∈ radialSobolevClosure n) :
    g = h :=
  ginibre_weak_gradient_unique n hn u g h
    (radialSobolevClosure_weak_gradient n hn _ hg)
    (radialSobolevClosure_weak_gradient n hn _ hh)

/-- The density-weighted identities are genuine distributional identities
against Lebesgue volume, rather than just identities between abstract L² pairings. -/
theorem ginibre_weak_gradient_distribution_identity (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreWeakGradient n u g) (k : Fin n × Fin 2)
    (ψ : Configuration n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ z, ginibreLebesgueDensityReal n z ^ 2 * g z k * ψ z) =
      -(∫ z, u z * (ginibreLebesgueDensityReal n z ^ 2 *
        fderiv ℝ ψ z (ginibreCoordinateDirection k) +
        2 * ginibreLebesgueDensityReal n z *
          fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k) * ψ z)) := by
  have he := hg k ψ hψ hc
  rw [integral_ginibreMeasure_eq_density_volume hn,
    integral_ginibreMeasure_eq_density_volume hn] at he
  have hm : (ginibreNormalizingMass n).toReal⁻¹ ≠ 0 :=
    inv_ne_zero (ENNReal.toReal_ne_zero.mpr
      ⟨(ginibreMassEvaluation n hn).1.ne', (ginibreMassEvaluation n hn).2.ne⟩)
  have hl : (fun z => ginibreLebesgueDensityReal n z * (g z k * ginibreWeakTest ψ z)) =
      (fun z => ginibreLebesgueDensityReal n z ^ 2 * g z k * ψ z) := by
    funext z
    dsimp [ginibreWeakTest]
    ring
  have hr : (fun z => ginibreLebesgueDensityReal n z * (u z * ginibreWeakAdjointTest k ψ z)) =
      (fun z => u z * (ginibreLebesgueDensityReal n z ^ 2 *
        fderiv ℝ ψ z (ginibreCoordinateDirection k) +
        2 * ginibreLebesgueDensityReal n z *
          fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k) * ψ z)) := by
    funext z
    dsimp [ginibreWeakAdjointTest]
    ring
  rw [hl, hr, ← mul_neg] at he
  exact mul_left_cancel₀ hm he

theorem ginibre_zero_weak_gradient (n : ℕ) :
    IsGinibreWeakGradient n (0 : Lp ℝ 2 (ginibreMeasure n))
      (0 : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) := by
  intro k ψ hψ hc
  have hl : (∫ z, (0 : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) z k *
      ginibreWeakTest ψ z ∂ginibreMeasure n) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin n × Fin 2)) (p := 2)
      (μ := ginibreMeasure n)] with z hz
    simp only [Pi.zero_apply] at hz
    rw [hz]
    simp
  have hr : (∫ z, (0 : Lp ℝ 2 (ginibreMeasure n)) z *
      ginibreWeakAdjointTest k ψ z ∂ginibreMeasure n) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ginibreMeasure n)] with z hz
    simp only [Pi.zero_apply] at hz
    rw [hz, zero_mul]
    rfl
  rw [hl, hr, neg_zero]

/-- A zero value in the completion has zero gradient. -/
theorem radialSobolevClosure_zero_gradient (n : ℕ) (hn : 0 < n)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : (0, g) ∈ radialSobolevClosure n) : g = 0 :=
  ginibre_weak_gradient_unique n hn 0 g 0
    (radialSobolevClosure_weak_gradient n hn _ hg) (ginibre_zero_weak_gradient n)

/-- Closability of the actual radial core gradient: values tending to zero
cannot have gradients tending to a nonzero vector in L². -/
theorem radialSobolevCorePairs_closable (n : ℕ) (hn : 0 < n)
    (p : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hp : ∀ m, p m ∈ radialSobolevCorePairs n)
    (hv : Tendsto (fun m => (p m).1) atTop (𝓝 0))
    (hg : Tendsto (fun m => (p m).2) atTop (𝓝 g)) : g = 0 := by
  apply radialSobolevClosure_zero_gradient n hn g
  exact isClosed_closure.mem_of_tendsto (hv.prodMk_nhds hg)
    (Eventually.of_forall (fun m => subset_closure (hp m)))

end
end GinibrePoincare
