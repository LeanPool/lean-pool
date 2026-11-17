/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreGeneratorL2.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreIntegrationByParts
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges

/-!
# Ginibre Generator L2
-/


@[expose] public section

open MeasureTheory
open Filter Topology

namespace GinibrePoincare

noncomputable section

/-- The concrete pregenerator vanishes away from the topological support of
the observable. -/
theorem ginibrePregenerator_eq_zero_of_notMem_tsupport {n : ℕ}
    (f : Configuration n → ℝ) {z : Configuration n}
    (hz : z ∉ tsupport f) : ginibrePregenerator n f z = 0 := by
  have hdf : fderiv ℝ f z = 0 := fderiv_of_notMem_tsupport ℝ hz
  have hsecond (v : Configuration n) :
      secondDirectionalDerivative f v z = 0 := by
    unfold secondDirectionalDerivative
    have hsub : tsupport (fun x => fderiv ℝ f x v) ⊆ tsupport f :=
      tsupport_fderiv_apply_subset ℝ v
    have hz' : z ∉ tsupport (fun x => fderiv ℝ f x v) :=
      fun h => hz (hsub h)
    rw [fderiv_of_notMem_tsupport ℝ hz']
    rfl
  simp [ginibrePregenerator, configurationLaplacian, hdf, hsecond]

/-- The pregenerator of a compactly supported observable remains compactly
supported. -/
theorem hasCompactSupport_ginibrePregenerator {n : ℕ}
    {f : Configuration n → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (ginibrePregenerator n f) := by
  apply HasCompactSupport.intro hf
  intro z hz
  exact ginibrePregenerator_eq_zero_of_notMem_tsupport f hz

theorem continuousAt_ginibrePregenerator_of_collisionFree {n : ℕ}
    {f : Configuration n → ℝ} (hf : ContDiff ℝ 2 f)
    {z : Configuration n} (hz : CollisionFree z) :
    ContinuousAt (ginibrePregenerator n f) z := by
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hsecond (v : Configuration n) :
      Continuous (fun x => secondDirectionalDerivative f v x) := by
    unfold secondDirectionalDerivative
    have hfirst : ContDiff ℝ 1 (fun x => fderiv ℝ f x v) := by
      have hp : ContDiff ℝ 1 (fun x : Configuration n => (x, v)) :=
        contDiff_id.prodMk contDiff_const
      exact (hf.contDiff_fderiv_apply (m := 1) (by norm_num)).comp hp
    exact (hfirst.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcoul (j k : Fin n) (hjk : j < k) :
      ContinuousAt (fun x => fderiv ℝ f x (coulombPairDirection j k x)) z := by
    have hne : z j - z k ≠ 0 := sub_ne_zero.mpr (fun h => hjk.ne (hz h))
    apply hdf.continuousAt.clm_apply
    have hsub : Continuous (fun x : Configuration n => x j - x k) :=
      (continuous_apply j).sub (continuous_apply k)
    have hfrac : ContinuousAt
        (fun x : Configuration n => (x j - x k) /
          (Complex.normSq (x j - x k) : ℂ)) z := by
      apply hsub.continuousAt.div₀
        (Complex.continuous_ofReal.comp (Complex.continuous_normSq.comp hsub)).continuousAt
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Complex.normSq_pos.mpr hne))
    unfold coulombPairDirection
    apply ContinuousAt.sub <;> unfold coordinateDirection <;>
      rw [continuousAt_pi] <;> intro i
    · by_cases hi : i = j
      · subst i
        simp only [ite_eq_left]
        exact hfrac
      · simp only [hi]
        exact continuousAt_const
    · by_cases hi : i = k
      · subst i
        simp only [ite_eq_left]
        exact hfrac
      · simp only [hi]
        exact continuousAt_const
  unfold ginibrePregenerator configurationLaplacian
  apply ContinuousAt.add
  · apply ContinuousAt.sub
    · exact ((continuous_finsetSum _ fun j _ =>
        (hsecond _).add (hsecond _)).continuousAt).const_mul _
    · apply ContinuousAt.const_mul
      apply (continuous_finsetSum _ fun j _ => ?_).continuousAt
      apply hdf.clm_apply
      unfold coordinateDirection
      apply continuous_pi
      intro i
      by_cases hi : i = j
      · subst i; simpa using continuous_apply j
      · simpa [hi] using (continuous_const : Continuous (fun _ : Configuration n => (0 : ℂ)))
  · apply ContinuousAt.const_mul
    have hsum {ι : Type} (s : Finset ι) (g : ι → Configuration n → ℝ)
        (hg : ∀ i ∈ s, ContinuousAt (g i) z) :
        ContinuousAt (fun x => ∑ i ∈ s, g i x) z := by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : Configuration n => (0 :
        ℝ)) z)
      | @insert a s ha ih =>
          simp only [Finset.sum_insert ha]
          exact (hg a (Finset.mem_insert_self _ _)).add
            (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
    apply hsum Finset.univ
    intro j hj
    apply hsum (Finset.Ioi j)
    intro k hk
    exact hcoul j k (Finset.mem_Ioi.mp hk)

/-- On the theorem core the apparent Coulomb singularity never meets the
support, so the concrete pregenerator has a continuous representative. -/
theorem continuous_ginibrePregenerator_of_core {n : ℕ}
    {f : Configuration n → ℝ} (hf : IsTheoremOneNineCore f) :
    Continuous (ginibrePregenerator n f) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · have h2 : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr le_top
    exact continuousAt_ginibrePregenerator_of_collisionFree (hf.1.of_le h2)
      ((collisionFree_iff_not_mem_collisionSet z).mpr (hf.2.2.1 hz))
  · have heq : ginibrePregenerator n f =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [((isClosed_tsupport f).isOpen_compl.mem_nhds hz)] with y hy
      exact ginibrePregenerator_eq_zero_of_notMem_tsupport f hy
    exact continuousAt_const.congr_of_eventuallyEq heq

/-- The complex-valued concrete pregenerator belongs to Ginibre `L²`. -/
theorem memLp_ginibrePregenerator_of_core {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    MemLp (fun z => (ginibrePregenerator n f z : ℂ)) 2 (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  apply (Complex.continuous_ofReal.comp
    (continuous_ginibrePregenerator_of_core hf)).memLp_of_hasCompactSupport
  apply (hasCompactSupport_ginibrePregenerator hf.2.1).mono
  intro z hz hzero
  apply hz
  simp [hzero]

/-- The Ginibre `L²` class represented by the concrete pregenerator. -/
def ginibrePregeneratorL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Lp ℂ 2 (ginibreMeasure n) :=
  (memLp_ginibrePregenerator_of_core hn f hf).toLp _

theorem ginibrePregeneratorL2_coeFn {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibrePregeneratorL2 hn f hf =ᵐ[ginibreMeasure n]
      fun z => (ginibrePregenerator n f z : ℂ) :=
  (memLp_ginibrePregenerator_of_core hn f hf).coeFn_toLp

theorem norm_sq_ginibrePregeneratorL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ‖ginibrePregeneratorL2 hn f hf‖ ^ 2 = ginibreGeneratorNormSq n f := by
  exact L2_norm_sq_eq_integral_sq_of_ae_ofReal (ginibreMeasure n)
    (ginibrePregeneratorL2 hn f hf) (ginibrePregenerator n f)
    (ginibrePregeneratorL2_coeFn hn f hf)

theorem memLp_shiftedGinibrePregenerator_of_core {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    MemLp (fun z => ((ginibrePregenerator n f z + 2 * f z : ℝ) : ℂ)) 2
      (ginibreMeasure n) := by
  have hgen := memLp_ginibrePregenerator_of_core hn f hf
  let := ginibreMeasure_isProbabilityMeasure hn
  have hfun : MemLp (fun z => (f z : ℂ)) 2 (ginibreMeasure n) :=
    (Complex.continuous_ofReal.comp hf.1.continuous).memLp_of_hasCompactSupport
      (by
        apply hf.2.1.mono
        intro z hz hzero
        apply hz
        simp [hzero])
  convert hgen.add (hfun.const_mul 2) using 1; ext z; simp

/-- The `L²` class represented by `(Aₙ + 2)f`. -/
def shiftedGinibrePregeneratorL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Lp ℂ 2 (ginibreMeasure n) :=
  (memLp_shiftedGinibrePregenerator_of_core hn f hf).toLp _

theorem shiftedGinibrePregeneratorL2_coeFn {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    shiftedGinibrePregeneratorL2 hn f hf =ᵐ[ginibreMeasure n]
      fun z => ((ginibrePregenerator n f z + 2 * f z : ℝ) : ℂ) :=
  (memLp_shiftedGinibrePregenerator_of_core hn f hf).coeFn_toLp

theorem norm_sq_shiftedGinibrePregeneratorL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ‖shiftedGinibrePregeneratorL2 hn f hf‖ ^ 2 =
      shiftedGinibreGeneratorNormSq n f := by
  exact L2_norm_sq_eq_integral_sq_of_ae_ofReal (ginibreMeasure n)
    (shiftedGinibrePregeneratorL2 hn f hf) (fun z ↦ ginibrePregenerator n f z + 2 * f z)
    (shiftedGinibrePregeneratorL2_coeFn hn f hf)

/-- The Hilbert inner product of the centered observable with its concrete
pregenerator is exactly minus the Dirichlet energy. -/
theorem inner_centeredObservableL2_ginibrePregeneratorL2 {n : ℕ}
    (hn : 0 < n) (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    inner ℂ (centeredObservableL2 hn f hf) (ginibrePregeneratorL2 hn f hf) =
      (-smoothGinibreEnergy n f : ℂ) := by
  rw [MeasureTheory.L2.inner_def]
  have hc := centeredObservableL2_coeFn hn f hf
  have hA := ginibrePregeneratorL2_coeFn hn f hf
  rw [integral_congr_ae (by
    filter_upwards [hc, hA] with z hcz hAz
    rw [hcz, hAz])]
  have hi : (fun z => inner ℂ (centeredObservable n f z : ℂ)
      (ginibrePregenerator n f z : ℂ)) =
      fun z => ((ginibrePregenerator n f z * centeredObservable n f z : ℝ) : ℂ) := by
    funext z
    simp only [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [hi]
  rw [integral_complex_ofReal]
  let := ginibreMeasure_isProbabilityMeasure hn
  have hgen : Integrable (ginibrePregenerator n f) (ginibreMeasure n) := by
    exact (continuous_ginibrePregenerator_of_core hf).integrable_of_hasCompactSupport
      (hasCompactSupport_ginibrePregenerator hf.2.1)
  have hprod : Integrable (fun z => ginibrePregenerator n f z * f z)
      (ginibreMeasure n) := by
    have hpcont : Continuous (fun z => ginibrePregenerator n f z * f z) :=
      (continuous_ginibrePregenerator_of_core hf).mul hf.1.continuous
    exact hpcont.integrable_of_hasCompactSupport
      ((hasCompactSupport_ginibrePregenerator hf.2.1).mul_right)
  rw [show (fun z => ginibrePregenerator n f z * centeredObservable n f z) =
      fun z => ginibrePregenerator n f z * f z -
        smoothGinibreMean n f * ginibrePregenerator n f z by
    funext z
    simp [centeredObservable]
    ring]
  rw [integral_sub hprod (hgen.const_mul _), integral_const_mul,
    integral_ginibrePregenerator_eq_zero hn hf,
    ginibrePregenerator_integrationByParts hn hf]
  simp

theorem inner_ginibrePregeneratorL2_centeredObservableL2 {n : ℕ}
    (hn : 0 < n) (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    inner ℂ (ginibrePregeneratorL2 hn f hf) (centeredObservableL2 hn f hf) =
      (-smoothGinibreEnergy n f : ℂ) := by
  rw [← inner_conj_symm]
  rw [inner_centeredObservableL2_ginibrePregeneratorL2 hn f hf]
  simp

/-- The centered realization of `(Aₙ + 2)f` in Ginibre `L²`. -/
def centeredShiftedGinibreGeneratorL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Lp ℂ 2 (ginibreMeasure n) :=
  ginibrePregeneratorL2 hn f hf +
    (2 : ℂ) • centeredObservableL2 hn f hf

theorem centeredShiftedGinibreGeneratorL2_coeFn {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    centeredShiftedGinibreGeneratorL2 hn f hf =ᵐ[ginibreMeasure n]
      fun z => ((ginibrePregenerator n f z +
        2 * centeredObservable n f z : ℝ) : ℂ) := by
  change (ginibrePregeneratorL2 hn f hf +
      (2 : ℂ) • centeredObservableL2 hn f hf) =ᵐ[ginibreMeasure n] _
  filter_upwards [ginibrePregeneratorL2_coeFn hn f hf,
    centeredObservableL2_coeFn hn f hf,
    Lp.coeFn_add (ginibrePregeneratorL2 hn f hf)
      ((2 : ℂ) • centeredObservableL2 hn f hf),
    Lp.coeFn_smul (2 : ℂ) (centeredObservableL2 hn f hf)] with z hA hc hadd hsmul
  rw [hadd]
  change (ginibrePregeneratorL2 hn f hf) z +
      ((2 : ℂ) • centeredObservableL2 hn f hf) z = _
  rw [hsmul, hA]
  change (ginibrePregenerator n f z : ℂ) +
      (2 : ℂ) * (centeredObservableL2 hn f hf) z = _
  rw [hc]
  norm_num

theorem norm_sq_centeredShiftedGinibreGeneratorL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ‖centeredShiftedGinibreGeneratorL2 hn f hf‖ ^ 2 =
      shiftedGinibreGeneratorNormSq n (centeredObservable n f) := by
  rw [L2_norm_sq_eq_integral_sq_of_ae_ofReal (ginibreMeasure n)
    (centeredShiftedGinibreGeneratorL2 hn f hf) _
    (centeredShiftedGinibreGeneratorL2_coeFn hn f hf)]
  unfold shiftedGinibreGeneratorNormSq
  apply integral_congr_ae
  exact Eventually.of_forall fun z =>
    congrArg (fun a : ℝ => (a + 2 * centeredObservable n f z) ^ 2)
      (ginibrePregenerator_sub_const n f (smoothGinibreMean n f) z).symm

/-- Concrete square completion, with the shifted square applied to the
centered observable as in Theorem 1.9. -/
theorem ginibreGenerator_squareCompletion {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreGeneratorNormSq n f - 2 * smoothGinibreEnergy n f =
      shiftedGinibreGeneratorNormSq n (centeredObservable n f) +
        2 * (smoothGinibreEnergy n f - 2 * smoothGinibreVariance n f) := by
  have h := norm_add_sq (𝕜 := ℂ) (ginibrePregeneratorL2 hn f hf)
    ((2 : ℂ) • centeredObservableL2 hn f hf)
  rw [← centeredShiftedGinibreGeneratorL2] at h
  have hcross : RCLike.re (inner ℂ (ginibrePregeneratorL2 hn f hf)
      ((2 : ℂ) • centeredObservableL2 hn f hf)) =
      -2 * smoothGinibreEnergy n f := by
    rw [inner_smul_right,
      inner_ginibrePregeneratorL2_centeredObservableL2 hn f hf]
    norm_num
  have hscaled : ‖(2 : ℂ) • centeredObservableL2 hn f hf‖ ^ 2 =
      4 * smoothGinibreVariance n f := by
    calc
      _ = 4 * ‖centeredObservableL2 hn f hf‖ ^ 2 := by
        rw [norm_smul, Complex.norm_ofNat]
        ring
      _ = 4 * smoothGinibreVariance n f := by
        rw [norm_sq_centeredObservableL2 hn f hf]
  rw [norm_sq_centeredShiftedGinibreGeneratorL2 hn f hf,
    norm_sq_ginibrePregeneratorL2 hn f hf,
    hcross, hscaled] at h
  linarith

/-- Any concrete first deficit identity immediately yields the second
Theorem 1.9 identity by square completion. -/
theorem ginibre_second_deficit_identity_of_first {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f)
    (deficit : ℝ) (hfirst :
      smoothGinibreEnergy n f - 2 * smoothGinibreVariance n f = deficit) :
    ginibreGeneratorNormSq n f - 2 * smoothGinibreEnergy n f =
      shiftedGinibreGeneratorNormSq n (centeredObservable n f) + 2 * deficit := by
  rw [ginibreGenerator_squareCompletion hn f hf, hfirst]

end
end GinibrePoincare
