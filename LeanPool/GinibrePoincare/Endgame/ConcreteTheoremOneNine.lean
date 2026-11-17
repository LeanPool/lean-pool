/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Endgame/ConcreteTheoremOneNine.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreGeneratorL2
public import LeanPool.GinibrePoincare.Analysis.GinibreConjugationGeometry
public import LeanPool.GinibrePoincare.Analysis.HermiteWeightedEnergy
public import LeanPool.GinibrePoincare.Analysis.WeightedSeriesTruncation
public import LeanPool.GinibrePoincare.Analysis.VandermondeGroundStateZeroMode
public import LeanPool.GinibrePoincare.Endgame.SeriesDeficit
public import LeanPool.GinibrePoincare.Endgame.FiniteTheoremOneNine

/-! # Concrete assembly of the two identities in Theorem 1.9 -/


@[expose] public section


namespace GinibrePoincare

noncomputable section
open scoped Topology
open MeasureTheory
open ComplexHermite
open Filter

local instance concrete_completeSpace_gaussianAlternatingL2 (n : ℕ) :
    CompleteSpace (gaussianAlternatingL2 n) :=
  (isClosed_gaussianAlternatingL2 n).completeSpace_coe

local instance concrete_completeSpace_ginibreSymmetricL2 (n : ℕ) :
    CompleteSpace (ginibreSymmetricL2 n) :=
  (isClosed_ginibreSymmetricL2 n).completeSpace_coe

/-- Positive antiholomorphic masses of the transformed centered observable,
indexed so that entry `k` is the mode of degree `k + 1`. -/
def concretePositiveHermiteModeMass {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) : ℕ → ℝ :=
  positiveHermiteModeMass hn (transformedCenteredObservableL2 hn f hf)

/-- Normalized Vandermonde transform of an observable before subtracting its Ginibre mean. -/
def uncenteredGroundStateTransform {n : ℕ} (f : Configuration n → ℝ) :
    Configuration n → ℂ :=
  normalizedVandermondeTransform n (fun z => (f z : ℂ))

/-- The Gaussian L² class of the uncentered normalized Vandermonde transform of a core
observable. -/
def uncenteredGroundStateL2 {n : ℕ} (_hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Lp ℂ 2 (complexGaussianMeasure n) := by
  have hF : ContDiff ℝ 1 (uncenteredGroundStateTransform f) :=
    (contDiff_normalizedVandermonde_ofReal hf.1).of_le (by simp)
  exact smoothCompactL2 (uncenteredGroundStateTransform f) hF
    (hasCompactSupport_normalizedVandermonde_ofReal hf.2.1)

theorem uncenteredGroundStateL2_coeFn {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    uncenteredGroundStateL2 hn f hf =ᵐ[complexGaussianMeasure n]
      uncenteredGroundStateTransform f := by
  unfold uncenteredGroundStateL2 smoothCompactL2
  exact MemLp.coeFn_toLp _

theorem uncenteredGroundStateL2_eq_centered_add_groundState
    {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    uncenteredGroundStateL2 hn f hf =
      transformedCenteredObservableL2 hn f hf +
        (smoothGinibreMean n f : ℂ) • normalizedVandermondeGroundStateL2 n hn := by
  apply Lp.ext
  filter_upwards [uncenteredGroundStateL2_coeFn hn f hf,
    transformedCenteredObservableL2_coeFn hn f hf,
    normalizedVandermondeGroundStateL2_coeFn n hn,
    Lp.coeFn_add (transformedCenteredObservableL2 hn f hf)
      ((smoothGinibreMean n f : ℂ) • normalizedVandermondeGroundStateL2 n hn),
    Lp.coeFn_smul (smoothGinibreMean n f : ℂ)
      (normalizedVandermondeGroundStateL2 n hn)] with z hunc hcent hground hadd hsmul
  rw [hunc, hadd, Pi.add_apply, hsmul, hcent, Pi.smul_apply, hground]
  unfold uncenteredGroundStateTransform centeredObservable
  rw [normalizedVandermondeTransform_apply,
    normalizedVandermondeTransform_apply]
  unfold normalizedVandermondeMultiplier
  simp only [smul_eq_mul]
  push_cast
  ring

theorem positiveHermiteMode_uncentered_eq_centered {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) (k : ℕ) :
    gaussianHermiteMode hn (k + 1) (uncenteredGroundStateL2 hn f hf) =
      gaussianHermiteMode hn (k + 1)
        (transformedCenteredObservableL2 hn f hf) := by
  let v := normalizedVandermondeGroundStateL2 n hn
  have hv0 : gaussianHermiteMode hn 0 v = v := by
    rw [gaussianHermiteMode_eq_antiDegreeProjection]
    exact Submodule.starProjection_eq_self_iff.mpr
      (normalizedVandermondeGroundStateL2_mem_hermiteAntiDegreeClosedSpan n hn)
  have hvpos : gaussianHermiteMode hn (k + 1) v = 0 := by
    rw [← hv0]
    exact gaussianHermiteMode_cross_eq_zero hn (by omega) v
  rw [uncenteredGroundStateL2_eq_centered_add_groundState hn f hf,
    gaussianHermiteMode_eq_antiDegreeProjection, map_add, map_smul,
    ← gaussianHermiteMode_eq_antiDegreeProjection,
    ← gaussianHermiteMode_eq_antiDegreeProjection, hvpos, smul_zero, add_zero]

theorem positiveHermiteModeMass_uncentered_eq_concrete {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) (k : ℕ) :
    positiveHermiteModeMass hn (uncenteredGroundStateL2 hn f hf) k =
      concretePositiveHermiteModeMass hn f hf k := by
  unfold positiveHermiteModeMass concretePositiveHermiteModeMass
  change ‖gaussianHermiteMode hn (k + 1) (uncenteredGroundStateL2 hn f hf)‖ ^ 2 =
    ‖gaussianHermiteMode hn (k + 1) (transformedCenteredObservableL2 hn f hf)‖ ^ 2
  rw [positiveHermiteMode_uncentered_eq_centered hn f hf k]

theorem uncenteredGroundState_weightedModeEnergy {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    HasSum (fun k : ℕ => (k + 1) * positiveHermiteModeMass hn
      (uncenteredGroundStateL2 hn f hf) k)
      (smoothGinibreEnergy n f / 4) := by
  have hF : ContDiff ℝ 1 (uncenteredGroundStateTransform f) :=
    (contDiff_normalizedVandermonde_ofReal hf.1).of_le (by simp)
  let hFc : HasCompactSupport (uncenteredGroundStateTransform f) :=
    hasCompactSupport_normalizedVandermonde_ofReal hf.2.1
  have hs := hasSum_weighted_positiveHermiteModeMass_smoothCompact hn
    (uncenteredGroundStateTransform f) hF hFc
  change HasSum _ (gaussianDbarEnergy n (uncenteredGroundStateTransform f)) at hs
  have hcenter := gaussianDbarEnergy_normalizedVandermonde_centered_eq_uncentered
    (hf.1.differentiable (by simp))
  have hground := groundStateEnergyIdentity n hn
    (ginibreMeasure_isProbabilityMeasure hn) f hf.isSmoothCompactSymmetric
  change smoothGinibreEnergy n f = 4 * gaussianDbarEnergy n
    (normalizedVandermondeTransform n
      (fun z => (centeredObservable n f z : ℂ))) at hground
  convert hs using 1
  · simp only [uncenteredGroundStateL2]
  · change smoothGinibreEnergy n f / 4 = gaussianDbarEnergy n
      (normalizedVandermondeTransform n (fun z => (f z : ℂ)))
    rw [← hcenter, hground]
    ring

theorem concrete_weightedModeEnergy {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      concretePositiveHermiteModeMass hn f hf k)
      (smoothGinibreEnergy n f / 4) := by
  apply (uncenteredGroundState_weightedModeEnergy hn f hf).congr_fun
  intro k
  rw [positiveHermiteModeMass_uncentered_eq_concrete hn f hf k]
  push_cast
  rfl

theorem transformedCenteredObservable_mem_hermiteWeightedDomain
    {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    transformedCenteredObservableL2 hn f hf ∈ HermiteWeightedDomain hn := by
  change Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
    positiveHermiteModeMass hn (transformedCenteredObservableL2 hn f hf) k)
  exact (concrete_weightedModeEnergy hn f hf).summable

/-- Concrete form-domain approximation by finite antiholomorphic Hermite
modes, including both `L²` convergence and convergence of the weighted
energy tails. -/
theorem transformedCenteredObservable_finiteMode_formCore
    {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    Tendsto (fun N ↦ gaussianHermiteModePartialSum hn N
        (transformedCenteredObservableL2 hn f hf)) atTop
        (𝓝 (transformedCenteredObservableL2 hn f hf)) ∧
      Tendsto
        (fun N ↦
          (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) *
              concretePositiveHermiteModeMass hn f hf k) -
            ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) *
              concretePositiveHermiteModeMass hn f hf k)
        atTop (𝓝 0) := by
  exact HermiteWeightedDomain.finiteMode_formCore
    (transformedCenteredObservable_mem_hermiteWeightedDomain hn f hf)

/-- The centered observable as a class in the particle-symmetric Ginibre L² subspace. -/
def centeredObservableSymmetricL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreSymmetricL2 n := by
  refine ⟨centeredObservableL2 hn f hf, ?_⟩
  intro σ
  apply Lp.ext
  have hc := centeredObservableL2_coeFn hn f hf
  filter_upwards [Lp.coeFn_compMeasurePreserving (centeredObservableL2 hn f hf)
      (ginibre_measurePreserving_permute σ),
    (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hc,
    hc] with z hperm hcomp hz
  change (Lp.compMeasurePreserving (permute σ)
    (ginibre_measurePreserving_permute σ) (centeredObservableL2 hn f hf)) z = _
  rw [hperm, hcomp, hz]
  simp only [Function.comp_apply, Complex.ofReal_inj]
  unfold centeredObservable
  rw [hf.2.2.2 σ z]

theorem coe_starProjection_centeredObservableSymmetricL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (ComplexHermite.ginibreSymmetricHolomorphicProjection n hn
      (centeredObservableSymmetricL2 hn f hf)).1 =
      (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
        (centeredObservableL2 hn f hf) := by
  let u := centeredObservableSymmetricL2 hn f hf
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨ComplexHermite.ginibreSymmetricHolomorphicProjection n hn u,
      Submodule.starProjection_apply_mem
        (ComplexHermite.ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule u,
      rfl⟩
  · intro w hw
    rcases hw with ⟨v, hv, rfl⟩
    change inner ℂ (u.1 - (ComplexHermite.ginibreSymmetricHolomorphicProjection n hn u).1) v.1 = 0
    exact Submodule.starProjection_inner_eq_zero u v hv

theorem coe_gaussianAlternatingZeroModeProjection {n : ℕ} (hn : 0 < n)
    (v : gaussianAlternatingL2 n) :
    (ComplexHermite.gaussianAlternatingZeroModeProjection n hn v).1 =
      ComplexHermite.hermiteAntiDegreeProjection n hn 0 v.1 := by
  let p : gaussianAlternatingL2 n :=
    ⟨ComplexHermite.hermiteAntiDegreeProjection n hn 0 v.1, by
      intro σ
      rw [gaussianPermutationL2_comm_antiDegreeProjection hn,
        v.2 σ, map_smul]⟩
  have hp : p ∈ ComplexHermite.gaussianAlternatingZeroModeClosedSpan n hn := by
    change p ∈ (ComplexHermite.gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
    rw [ComplexHermite.gaussianAlternatingZeroModeClosedSpan_eq_hermiteZeroMode_comap]
    exact Submodule.starProjection_apply_mem
      (ComplexHermite.hermiteAntiDegreeClosedSpan n hn 0).toSubmodule v.1
  have hort : ∀ w ∈ ComplexHermite.gaussianAlternatingZeroModeClosedSpan n hn,
      inner ℂ (v - p) w = 0 := by
    intro w hw
    change inner ℂ (v.1 - ComplexHermite.hermiteAntiDegreeProjection n hn 0 v.1) w.1 = 0
    apply Submodule.starProjection_inner_eq_zero
    have heq := ComplexHermite.gaussianAlternatingZeroModeClosedSpan_eq_hermiteZeroMode_comap n hn
    have hw' : w ∈ (ComplexHermite.gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule := hw
    rw [heq] at hw'
    exact hw'
  change (ComplexHermite.gaussianAlternatingZeroModeProjection n hn v).1 = p.1
  apply congrArg Subtype.val
  unfold ComplexHermite.gaussianAlternatingZeroModeProjection
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [ComplexHermite.map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
    exact hp
  · intro w hw
    apply hort w
    have hmap := ComplexHermite.map_ginibreSymmetricHolomorphicPolynomialClosedSpan n hn
    have hw' := hw
    rw [hmap] at hw'
    exact hw'

theorem concreteZeroMode_norm_sq_eq_holomorphicProjection {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ‖gaussianHermiteMode hn 0 (transformedCenteredObservableL2 hn f hf)‖ ^ 2 =
      ‖(ginibreHolomorphicAmbientClosedSpan n hn).starProjection
        (centeredObservableL2 hn f hf)‖ ^ 2 := by
  let u := centeredObservableSymmetricL2 hn f hf
  let v := vandermondeSymmetricAlternatingEquiv n hn u
  have hv : v.1 = transformedCenteredObservableL2 hn f hf := rfl
  have hproj := ComplexHermite.transform_ginibreSymmetricHolomorphicPart_eq_gaussianZeroMode
    n hn u
  have hambient := coe_starProjection_centeredObservableSymmetricL2 hn f hf
  rw [gaussianHermiteMode_eq_antiDegreeProjection]
  rw [← hv, ← coe_gaussianAlternatingZeroModeProjection hn v]
  change ‖ComplexHermite.gaussianZeroModeOfGinibre n hn u‖ ^ 2 = _
  rw [← hproj]
  rw [(vandermondeSymmetricAlternatingEquiv n hn).norm_map]
  change ‖(ComplexHermite.ginibreSymmetricHolomorphicPart n hn u).1‖ ^ 2 = _
  dsimp [u, ComplexHermite.ginibreSymmetricHolomorphicPart]
  rw [hambient]

/-- Internal concrete assembly lemma. Its sole analytic hypothesis is the
weighted mode-energy series identity, stated as `HasSum` so convergence is
part of the identity rather than a separate assumption. -/
theorem concrete_theoremOneNine_of_modeEnergy {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f)
    (henergy : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      concretePositiveHermiteModeMass hn f hf k)
        (smoothGinibreEnergy n f / 4)) :
    let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (centeredObservableL2 hn f hf)
    let r := centeredObservableL2 hn f hf - h - star h
    (smoothGinibreEnergy n f - 2 * smoothGinibreVariance n f =
      2 * ‖r‖ ^ 2 +
        4 * modeTail (concretePositiveHermiteModeMass hn f hf)) ∧
    (ginibreGeneratorNormSq n f - 2 * smoothGinibreEnergy n f =
      shiftedGinibreGeneratorNormSq n (centeredObservable n f) +
        4 * ‖r‖ ^ 2 +
        8 * modeTail (concretePositiveHermiteModeMass hn f hf)) := by
  dsimp only
  let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
    (centeredObservableL2 hn f hf)
  let r := centeredObservableL2 hn f hf - h - star h
  let a := concretePositiveHermiteModeMass hn f hf
  have ha : Summable a := summable_transformedCentered_positiveModeMass hn f hf
  have ht : Summable fun k : ℕ => (k : ℝ) * a k := by
    have hs := henergy.summable.sub ha
    apply hs.congr
    intro k
    dsimp [a]
    push_cast
    ring
  have henergy' : smoothGinibreEnergy n f = 4 * modeEnergy a := by
    unfold modeEnergy
    rw [henergy.tsum_eq]
    ring
  have hparseval : smoothGinibreVariance n f = ‖h‖ ^ 2 + modeMass a := by
    rw [smoothGinibreVariance_eq_zeroMode_add_positiveModeMass hn f hf,
      concreteZeroMode_norm_sq_eq_holomorphicProjection hn f hf]
    rfl
  have hgeometry : smoothGinibreVariance n f = 2 * ‖h‖ ^ 2 + ‖r‖ ^ 2 := by
    exact (centeredHolomorphicRemainderGeometry hn f hf).2.2.2
  have hfirst : smoothGinibreEnergy n f - 2 * smoothGinibreVariance n f =
      2 * ‖r‖ ^ 2 + 4 * modeTail a :=
    infinite_deficit_identity a ha ht _ _ _ _ hparseval hgeometry henergy'
  constructor
  · exact hfirst
  · rw [ginibreGenerator_squareCompletion hn f hf, hfirst]
    ring

/-- The two exact sum-of-squares identities of Theorem 1.9 for the concrete
Ginibre measure and generator, with all Hermite-series convergence included. -/
theorem concrete_theoremOneNine {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (centeredObservableL2 hn f hf)
    let r := centeredObservableL2 hn f hf - h - star h
    (smoothGinibreEnergy n f - 2 * smoothGinibreVariance n f =
      2 * ‖r‖ ^ 2 +
        4 * modeTail (concretePositiveHermiteModeMass hn f hf)) ∧
    (ginibreGeneratorNormSq n f - 2 * smoothGinibreEnergy n f =
      shiftedGinibreGeneratorNormSq n (centeredObservable n f) +
        4 * ‖r‖ ^ 2 +
        8 * modeTail (concretePositiveHermiteModeMass hn f hf)) :=
  concrete_theoremOneNine_of_modeEnergy hn f hf
    (concrete_weightedModeEnergy hn f hf)

end

end GinibrePoincare
