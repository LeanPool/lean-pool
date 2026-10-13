/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ComparatorUniformBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedTranslation
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RenormalizationAtRandomScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SigmaBarBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionScaling
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepOneMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.FlowArithmetic

/-!
# ErrorMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A renormalization amplitude for the localized error

The generator-renormalization estimate is uniform over the normalized forcing
class.  This module compares its constant-coefficient solution with the
canonical comparator used in `localizedError`.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-- The relative diffusivity error can be made uniformly small by shrinking the
disorder threshold. -/
private theorem exists_sqrt_mul_abs_log_small {K : ℝ} (hK : 0 < K) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
      K * (Real.sqrt gamma * |Real.log gamma|) ≤ 1 / 4 := by
  let A : ℝ := max 1 (16 * K)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hAone : 1 ≤ A := le_max_left _ _
  have hAK : 16 * K ≤ A := le_max_right _ _
  refine ⟨A⁻¹ ^ (4 : ℕ), by positivity, ?_⟩
  intro gamma hgamma hgamma0
  have hinv : 0 ≤ A⁻¹ := (inv_pos.2 hA).le
  have hgamma1 : gamma ≤ 1 := by
    have hpow : A⁻¹ ^ (4 : ℕ) ≤ 1 := by
      have hi : A⁻¹ ≤ 1 := (inv_le_one₀ hA).2 hAone
      exact pow_le_one₀ hinv hi
    exact hgamma0.trans hpow
  have hsqrt : Real.sqrt gamma ≤ A⁻¹ ^ (2 : ℕ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨pow_nonneg hinv 2, ?_⟩
    nlinarith only [hgamma0]
  have hsqrtsqrt : Real.sqrt (Real.sqrt gamma) ≤ A⁻¹ := by
    rw [Real.sqrt_le_iff]
    exact ⟨hinv, hsqrt⟩
  have hlog := Algsuperdiff.Section3.Provider.Diffusivity.sqrt_mul_abs_log_le
    hgamma hgamma1
  have hKA : K * 4 * A⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hA]
    linarith only [hAK]
  calc
    K * (Real.sqrt gamma * |Real.log gamma|) ≤
        K * (4 * Real.sqrt (Real.sqrt gamma)) :=
      mul_le_mul_of_nonneg_left hlog hK.le
    _ ≤ K * (4 * A⁻¹) := by gcongr
    _ = K * 4 * A⁻¹ := by ring
    _ ≤ 1 / 4 := hKA

/-- A symmetric relative error smaller than one quarter gives a one-sided
ratio bound and an absolute ratio defect bound. -/
private theorem ratio_bounds_of_symmetric_error {a s q : ℝ} (ha : 0 < a)
    (hs : 0 < s) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4)
    (h : |s - a| ≤ q * (s + a)) :
    a / s ≤ 2 ∧ |a / s - 1| ≤ 4 * q := by
  have habs : |a - s| ≤ q * (s + a) := by simpa only [abs_sub_comm] using h
  have heq : |a / s - 1| = |a - s| / s := by
    rw [show a / s - 1 = (a - s) / s by field_simp, abs_div, abs_of_pos hs]
  have hratio : |a / s - 1| ≤ q * (1 + a / s) := by
    rw [heq]
    apply (div_le_iff₀ hs).2
    calc
      |a - s| ≤ q * (s + a) := habs
      _ = q * (1 + a / s) * s := by field_simp
  have haratio : 0 ≤ a / s := (div_pos ha hs).le
  have htwo : a / s ≤ 2 := by
    have hlin := (le_abs_self (a / s - 1)).trans hratio
    nlinarith only [hlin, hq]
  constructor
  · exact htwo
  · nlinarith only [hratio, hq0, haratio, htwo]

private theorem hasGradientOn_zero {d : ℕ} {U : Set (Vec d)} :
    HasGradientOn U (0 : H1Function U).toFun (0 : H1Function U).grad := by
  intro x _hx
  have hz : slopeCLM ((0 : H1Function U).grad x) = (0 : Vec d →L[ℝ] ℝ) := by
    ext v
    simp [vecDot]
  rw [hz]
  exact hasFDerivWithinAt_const (0 : ℝ) x U

/-! ## Comparator rescaling -/

/-- A solution for `sigma • 1` rescales to a solution with the same forcing for
`tau • 1`. -/
theorem isDirichletSolutionAt_rescale_constant {d : ℕ} {y : Vec d} {n : ℤ}
    {sigma tau : ℝ} (htau : 0 < tau) {v : H1Function (cubeSetAt y n)}
    {g : Vec d → Vec d}
    (hv : IsDirichletSolutionAt (fun _ => sigma • (1 : Mat d)) y n v g) :
    IsDirichletSolutionAt (fun _ => tau • (1 : Mat d)) y n
      ((sigma / tau) • v) g := by
  obtain ⟨⟨w, hwf, hwg⟩, hweak⟩ := hv
  refine ⟨⟨(sigma / tau) • w, fun x => ?_, fun x => ?_⟩, fun phi => ?_⟩
  · change ((sigma / tau) • v).toFun x = ((sigma / tau) • w.toH1Function).toFun x
    simp only [H1Function.smul_toFun, hwf x]
  · change ((sigma / tau) • v).grad x = ((sigma / tau) • w.toH1Function).grad x
    simp only [H1Function.smul_grad, hwg x]
  · have hpoint : ∀ x : Vec d,
        vecDot
            (matVecMul (tau • (1 : Mat d)) (((sigma / tau) • v).grad x))
            (phi.toH1Function.grad x) =
          vecDot (matVecMul (sigma • (1 : Mat d)) (v.grad x))
            (phi.toH1Function.grad x) := by
      intro x
      simp only [H1Function.smul_grad, Section4.Provider.Schauder.matVecMul_smul_one,
        smul_smul]
      congr 2
      field_simp
    simpa only [hpoint] using hweak phi

/-! ## Reading a pointwise estimate as an essential-supremum estimate -/

private theorem normalized_eLpNorm_top_le_of_ae {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} {sigma scale E : ℝ} (hsigma : 0 < sigma)
    (hscale : 0 < scale) (hf : AEStronglyMeasurable f (volume.restrict U))
    (h : ∀ᵐ x ∂(volume.restrict U), scale * |f x| ≤ E * sigma⁻¹) :
    ENNReal.ofReal (sigma * scale) * eLpNorm f ⊤ (volume.restrict U) ≤
      ENNReal.ofReal E := by
  have hae : ∀ᵐ x ∂(volume.restrict U), ‖f x‖ ≤ E * sigma⁻¹ * scale⁻¹ := by
    filter_upwards [h] with x hx
    rw [Real.norm_eq_abs]
    calc
      |f x| ≤ (E * sigma⁻¹) / scale :=
        (le_div_iff₀ hscale).2 (by simpa only [mul_comm] using hx)
      _ = E * sigma⁻¹ * scale⁻¹ := by rw [div_eq_mul_inv]
  have hlp : eLpNorm f ⊤ (volume.restrict U) ≤
      ENNReal.ofReal (E * sigma⁻¹ * scale⁻¹) := by
    simpa using (eLpNorm_le_of_ae_bound (p := (⊤ : ℝ≥0∞)) hf hae)
  calc
    ENNReal.ofReal (sigma * scale) * eLpNorm f ⊤ (volume.restrict U) ≤
        ENNReal.ofReal (sigma * scale) * ENNReal.ofReal (E * sigma⁻¹ * scale⁻¹) :=
      mul_le_mul_right hlp _
    _ = ENNReal.ofReal E := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hsigma.le hscale.le)]
      congr 1
      field_simp

/-! ## The comparator swap -/

/-- The normalized error for the canonical comparator is controlled by the
renormalization error and the explicit cost of changing the scalar. -/
theorem localizedError_origin_le_of_renormalization {d : ℕ} (M : ABKModel d)
    (n : ℤ) (omega : Cutoff.CutoffSample d) {sigma E B : ℝ}
    (hsigma : 0 < sigma) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hren : ∀ (g : Vec d → Vec d), NormalizedForceAt 0 n g →
      ∀ u : H1Function (cubeSetAt 0 n),
        IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
          0 n u g →
      ∀ w : H1Function (cubeSetAt 0 n),
        IsDirichletSolutionAt (fun _ => sigma • (1 : Mat d)) 0 n w g →
        ENNReal.ofReal (sigma * Real.rpow 3 (-(n : ℝ))) *
          eLpNorm (fun x => u.toFun x - w.toFun x) ⊤
            (volume.restrict (cubeSetAt 0 n)) ≤ ENNReal.ofReal E)
    (hcomp : ∀ (g : Vec d → Vec d), NormalizedForceAt 0 n g →
      ∀ v : H1Function (cubeSetAt 0 n),
        IsDirichletSolutionAt
          (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) 0 n v g →
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
          eLpNorm v.toFun ⊤ (volume.restrict (cubeSetAt 0 n)) ≤ ENNReal.ofReal B) :
    localizedError M n 0 omega ≤
      ENNReal.ofReal (((Annealed.sigmaBar M n : ℝ) / sigma) * E +
        |(Annealed.sigmaBar M n : ℝ) / sigma - 1| * B) := by
  rw [localizedError_le_iff]
  intro g hg u hu v hv
  let t : ℝ := (Annealed.sigmaBar M n : ℝ) / sigma
  let w : H1Function (cubeSetAt 0 n) := t • v
  have hw : IsDirichletSolutionAt (fun _ => sigma • (1 : Mat d)) 0 n w g := by
    exact isDirichletSolutionAt_rescale_constant hsigma hv
  have hrough := hren g hg u hu w hw
  have htriangle : eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
      (volume.restrict (cubeSetAt 0 n)) ≤
      eLpNorm (fun x => u.toFun x - w.toFun x) ⊤
          (volume.restrict (cubeSetAt 0 n)) +
        eLpNorm (fun x => w.toFun x - v.toFun x) ⊤
          (volume.restrict (cubeSetAt 0 n)) := by
    have hadd := eLpNorm_add_le (f := u.toFun - w.toFun) (g := w.toFun - v.toFun)
      (μ := volume.restrict (cubeSetAt 0 n)) (show (1 : ℝ≥0∞) ≤ ⊤ by simp)
    have heq : (fun x => u.toFun x - v.toFun x) =
        (u.toFun - w.toFun) + (w.toFun - v.toFun) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [heq]
    exact hadd
  have hscale : eLpNorm (fun x => w.toFun x - v.toFun x) ⊤
      (volume.restrict (cubeSetAt 0 n)) =
      ENNReal.ofReal |t - 1| * eLpNorm v.toFun ⊤
        (volume.restrict (cubeSetAt 0 n)) := by
    have hfun : (fun x => w.toFun x - v.toFun x) = fun x => (t - 1) * v.toFun x := by
      funext x
      simp only [w, H1Function.smul_toFun]
      ring
    rw [hfun]
    change eLpNorm ((t - 1) • v.toFun) ⊤ (volume.restrict (cubeSetAt 0 n)) = _
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs]
  have hcanon := hcomp g hg v hv
  have hsigCanon : 0 < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have ht : 0 < t := div_pos hsigCanon hsigma
  have hcoeff :
      ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) =
        ENNReal.ofReal t * ENNReal.ofReal (sigma * Real.rpow 3 (-(n : ℝ))) := by
    rw [← ENNReal.ofReal_mul ht.le]
    congr 1
    simp only [t]
    field_simp
  calc
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
          (volume.restrict (cubeSetAt 0 n))
        ≤ ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            (eLpNorm (fun x => u.toFun x - w.toFun x) ⊤
                (volume.restrict (cubeSetAt 0 n)) +
              eLpNorm (fun x => w.toFun x - v.toFun x) ⊤
                (volume.restrict (cubeSetAt 0 n))) := mul_le_mul_right htriangle _
    _ = ENNReal.ofReal t *
          (ENNReal.ofReal (sigma * Real.rpow 3 (-(n : ℝ))) *
            eLpNorm (fun x => u.toFun x - w.toFun x) ⊤
              (volume.restrict (cubeSetAt 0 n))) +
        ENNReal.ofReal |t - 1| *
          (ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            eLpNorm v.toFun ⊤ (volume.restrict (cubeSetAt 0 n))) := by
      rw [hscale, hcoeff]
      ring
    _ ≤ ENNReal.ofReal t * ENNReal.ofReal E + ENNReal.ofReal |t - 1| * ENNReal.ofReal B :=
      add_le_add (mul_le_mul_right hrough _) (mul_le_mul_right hcanon _)
    _ = ENNReal.ofReal (t * E + |t - 1| * B) := by
      rw [← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul (abs_nonneg _),
        ← ENNReal.ofReal_add (mul_nonneg ht.le hE)]
      positivity
    _ = _ := rfl

/-- Every canonical comparator has the explicit normalized essential-supremum
bound supplied by the cube Schauder estimate. -/
theorem exists_comparator_eLpNorm_bound (d : ℕ) (hdim : 2 ≤ d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (M : ABKModel d) (n : ℤ) (g : Vec d → Vec d),
        NormalizedForceAt 0 n g →
        ∀ v : H1Function (cubeSetAt 0 n),
          IsDirichletSolutionAt
            (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) 0 n v g →
          ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            eLpNorm v.toFun ⊤ (volume.restrict (cubeSetAt 0 n)) ≤ ENNReal.ofReal B := by
  obtain ⟨C, hC, hbound⟩ := localizedError_comparator_term_le d hdim
  obtain ⟨_Crep, _hCrep, hrep⟩ := exists_lipschitzRepresentative_comparator d hdim
  refine ⟨(d : ℝ) * C / 2, by positivity, ?_⟩
  intro M n g hg v hv
  obtain ⟨v0, vRep, Ksup, KHol, hv0, _hKsup, _hKHol, _hgrad, _hhol, _hest,
      hv0Rep, hvRepLip, _hsup, _hhasRep⟩ :=
    hrep M n 0 g (Real.rpow 3 (-(n : ℝ) / 2)) hg
  have hv0v := (isDirichletSolutionAt_ae_unique_comparator M n 0 hv0 hv).2
  have hvRep : IsCubeRepresentative 0 n v vRep :=
    ⟨hv0Rep.symm.trans hv0v, hvRepLip.continuous.continuousOn⟩
  have hs := hbound M n 0 g hg v hv vRep hvRep
  rw [eLpNorm_top_restrict_eq_supNormOn_of_ae (isOpen_cubeSetAt 0 n)
    hvRep.1 hvRep.2]
  exact hs

/-- The generator-renormalization estimate, specialized at zero boundary datum and the
normalized forcing scale, bounds the localized error at the origin after the
canonical-comparator swap. -/
theorem exists_localizedError_origin_bound (d : ℕ) (cstar : ℝ)
    (hdim : 2 ≤ d) (hcstar : 0 < cstar) :
    ∃ gamma0 C K B : ℝ,
      0 < gamma0 ∧ 0 < C ∧ 0 < K ∧ 0 < B ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ n : ℤ, ∃ sigma : ℝ, ∃ EB : Cutoff.CutoffSample d → ℝ,
          0 < sigma ∧ (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
          (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
            (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
          (Annealed.sigmaBar M n : ℝ) / sigma ≤ 2 ∧
          |(Annealed.sigmaBar M n : ℝ) / sigma - 1| ≤
            4 * K * Real.sqrt M.gamma * |Real.log M.gamma| ∧
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            localizedError M n 0 omega ≤
              ENNReal.ofReal (((Annealed.sigmaBar M n : ℝ) / sigma) * EB omega +
                |(Annealed.sigmaBar M n : ℝ) / sigma - 1| * B) := by
  obtain ⟨gammaGen, C, hgammaGen, hC, hgen⟩ :=
    Algsuperdiff.Frozen.Section4.generator_renormalization d cstar hcstar
  obtain ⟨gammaInd, Cind, hgammaInd, hCind, hbridge⟩ :=
    generatorSigmaBar_close_to_sigmaBar_of_approx d cstar hcstar
  let K : ℝ := max C (Cind * cstar⁻¹ ^ (2 : ℕ))
  have hK : 0 < K := hC.trans_le (le_max_left _ _)
  obtain ⟨gammaSmall, hgammaSmall, hsmall⟩ := exists_sqrt_mul_abs_log_small hK
  obtain ⟨B, hB, hcomp⟩ := exists_comparator_eLpNorm_bound d hdim
  refine ⟨min gammaGen (min gammaInd gammaSmall), C, K, B,
    lt_min hgammaGen (lt_min hgammaInd hgammaSmall), hC, hK, hB, ?_⟩
  intro M hcs hgamma n
  have hgGen := hgamma.trans (min_le_left _ _)
  have hgInd := hgamma.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hgSmall := hgamma.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨sigma, hsigma, hsigmaApprox, EB, hEBnn, hEBmeas, hEBmom, hdir⟩ :=
    hgen M hcs hgGen n
  have hclose := hbridge M hcs hgInd n C sigma hC hsigma hsigmaApprox
  have hq0 : 0 ≤ K * (Real.sqrt M.gamma * |Real.log M.gamma|) := by positivity
  have hq := hsmall M.gamma M.shellPrefix.gamma_pos hgSmall
  obtain ⟨hratio, hratioDefect⟩ := ratio_bounds_of_symmetric_error
    (Annealed.sigmaBar M n).2 hsigma hq0 hq (by simpa only [K, mul_assoc] using hclose)
  refine ⟨sigma, EB, hsigma, hEBnn, hEBmeas, hEBmom, hratio,
    by simpa only [mul_assoc] using hratioDefect, ?_⟩
  filter_upwards [hdir] with omega homega
  apply localizedError_origin_le_of_renormalization M n omega hsigma (hEBnn omega) hB.le
  · intro g hg u hu w hw
    have huO := (isDirichletSolutionAt_iff_origin _ 0 n u g).1 hu
    have hwO := (isDirichletSolutionAt_iff_origin _ 0 n w g).1 hw
    have hraw := (homega n le_rfl (originPullback 0 n u) (originPullback 0 n w) 0 g
      (Real.rpow 3 (-(n : ℝ) / 2)) 0 0 (by simpa only [zero_add] using huO)
      (by simpa only [zero_add] using hwO)
      (by simpa only [NormalizedForceAt, cubeSetAt_zero_eq_openCubeSet] using hg)
      (holderSeminormBoundOn_zero _ _ le_rfl) (by simp) hasGradientOn_zero).1
    have hcancel : Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 (-(n : ℝ) / 2) = 1 := by
      calc
        Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 (-(n : ℝ) / 2) =
            Real.rpow 3 ((n : ℝ) / 2 + -(n : ℝ) / 2) :=
          (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
        _ = 1 := by rw [show (n : ℝ) / 2 + -(n : ℝ) / 2 = 0 by ring]; norm_num
    have hae : ∀ᵐ x ∂(volume.restrict (cubeSetAt 0 n)),
        Real.rpow 3 (-(n : ℝ)) * |u.toFun x - w.toFun x| ≤ EB omega * sigma⁻¹ := by
      have hmeasure : volume.restrict (cubeSetAt (0 : Vec d) n) =
          volume.restrict (openCubeSet (originCube d n)) := by
        rw [cubeSetAt_zero_eq_openCubeSet]
      rw [hmeasure]
      filter_upwards [hraw] with x hx
      simp only [originPullback_toFun, add_zero, mul_zero] at hx
      calc
        Real.rpow 3 (-(n : ℝ)) * |u.toFun x - w.toFun x| ≤
            EB omega * (sigma⁻¹ * Real.rpow 3 ((n : ℝ) / 2) *
              Real.rpow 3 (-(n : ℝ) / 2)) := hx
        _ = EB omega * sigma⁻¹ := by rw [mul_assoc sigma⁻¹, hcancel, mul_one]
    exact normalized_eLpNorm_top_le_of_ae hsigma (Real.rpow_pos_of_pos (by norm_num) _)
      (u.memL2.aestronglyMeasurable.sub w.memL2.aestronglyMeasurable) hae
  · exact hcomp M n

/-! ## Moment packaging -/

/-- A uniform almost-everywhere bound by a rescaled random amplitude plus a
deterministic comparator cost gives the corresponding two-term moment bound. -/
theorem lintegral_localizedError_rpow_le_of_rescaled_bound {d : ℕ}
    (M : ABKModel d) (n : ℤ) {EB : Cutoff.CutoffSample d → ℝ}
    {t D R p : ℝ} (hp : 1 ≤ p) (ht : 0 ≤ t) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hEB : Measurable EB) (hEBnn : ∀ omega, 0 ≤ EB omega)
    (hpoint : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      localizedError M n 0 omega ≤ ENNReal.ofReal (t * EB omega + D))
    (hmom : (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ ENNReal.ofReal R ^ p) :
    (∫⁻ omega, localizedError M n 0 omega ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (t * R + D) ^ p := by
  let F : Cutoff.CutoffSample d → ℝ≥0∞ := fun omega => ENNReal.ofReal (t * EB omega)
  let G : Cutoff.CutoffSample d → ℝ≥0∞ := fun _ => ENNReal.ofReal D
  have hFmeas : AEMeasurable F (Cutoff.cutoffSampleLaw M).toMeasure :=
    ((hEB.const_mul t).ennreal_ofReal).aemeasurable
  have hGmeas : AEMeasurable G (Cutoff.cutoffSampleLaw M).toMeasure :=
    measurable_const.aemeasurable
  have hFmom : (∫⁻ omega, F omega ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (t * R) ^ p := by
    have hpow : ∀ omega, F omega ^ p = ENNReal.ofReal t ^ p *
        ENNReal.ofReal (EB omega) ^ p := by
      intro omega
      rw [show F omega = ENNReal.ofReal t * ENNReal.ofReal (EB omega) by
        simp only [F, ← ENNReal.ofReal_mul ht]]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    calc
      (∫⁻ omega, F omega ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
          ∫⁻ omega, ENNReal.ofReal t ^ p * ENNReal.ofReal (EB omega) ^ p
            ∂(Cutoff.cutoffSampleLaw M).toMeasure := lintegral_congr hpow
      _ = ENNReal.ofReal t ^ p *
          ∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
            ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
        lintegral_const_mul _
          (ENNReal.continuous_rpow_const.measurable.comp hEB.ennreal_ofReal)
      _ ≤ ENNReal.ofReal t ^ p * ENNReal.ofReal R ^ p := mul_le_mul_right hmom _
      _ = ENNReal.ofReal (t * R) ^ p := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.ofReal_mul ht]
  have hGmom : (∫⁻ omega, G omega ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal D ^ p := by
    simpa only [G, lintegral_const, measure_univ, mul_one] using
      (le_refl (ENNReal.ofReal D ^ p))
  have hadd :=
    Algsuperdiff.Section4.Provider.Homogenization.lintegral_rpow_add_le_of_moments
      hp hFmeas hGmeas (mul_nonneg ht hR) hD hFmom hGmom
  calc
    (∫⁻ omega, localizedError M n 0 omega ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ∫⁻ omega, (F omega + G omega) ^ p
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      refine lintegral_mono_ae (hpoint.mono fun omega homega => ?_)
      refine ENNReal.rpow_le_rpow ?_ (by positivity)
      rw [ENNReal.ofReal_add (mul_nonneg ht (hEBnn omega))] at homega
      exact homega
      exact hD
    _ ≤ ENNReal.ofReal (t * R + D) ^ p := hadd

/-- The localized error has the generator-renormalization moment profile, with
a new constant absorbing the canonical-comparator swap. -/
theorem localizedError_moment_bound (d : ℕ) (cstar : ℝ) (hdim : 2 ≤ d)
    (hcstar : 0 < cstar) :
    ∃ gamma0 C' : ℝ, 0 < gamma0 ∧ 0 < C' ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ (p : ℝ) (n : ℤ) (y : Vec d), 1 ≤ p →
          p ≤ C'⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
          (∫⁻ omega, localizedError M n y omega ^ p
              ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
            ENNReal.ofReal (C' * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
              Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p := by
  obtain ⟨gamma0, C, K, B, hgamma0, hC, hK, hB, hmain⟩ :=
    exists_localizedError_origin_bound d cstar hdim hcstar
  let C' : ℝ := max C (2 * C + 4 * K * B)
  have hC' : 0 < C' := hC.trans_le (le_max_left _ _)
  refine ⟨gamma0, C', hgamma0, hC', ?_⟩
  intro M hcs hgamma p n y hp hrange
  obtain ⟨sigma, EB, hsigma, hEBnn, hEBmeas, hEBmom, hratio, hdefect, hpoint⟩ :=
    hmain M hcs hgamma n
  let S : ℝ := Real.sqrt p + Real.sqrt |Real.log M.gamma|
  let R : ℝ := C * S * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)
  let D : ℝ := |(Annealed.sigmaBar M n : ℝ) / sigma - 1| * B
  have hCC' : C ≤ C' := le_max_left _ _
  have hrangeC : p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ := by
    have hinv : C'⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hC' hC).2 hCC'
    exact hrange.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hinv (inv_nonneg.mpr M.shellPrefix.gamma_pos.le))
      (inv_nonneg.mpr (abs_nonneg _)))
  have hR : 0 ≤ R := by unfold R S; positivity
  have hD : 0 ≤ D := by unfold D; positivity
  have ht : 0 ≤ (Annealed.sigmaBar M n : ℝ) / sigma :=
    (div_pos (Annealed.sigmaBar M n).2 hsigma).le
  have horigin := lintegral_localizedError_rpow_le_of_rescaled_bound M n hp ht hD hR
    hEBmeas hEBnn hpoint (hEBmom p hp hrangeC)
  rw [lintegral_localizedError_rpow_eq_origin M n y p]
  refine horigin.trans (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_)
    (by linarith only [hp]))
  have hlog : 1 ≤ |Real.log M.gamma| :=
    one_le_abs_log M.shellPrefix.gamma_pos M.shellPrefix.gamma_le_quarter
  have hsqrtp : 1 ≤ Real.sqrt p := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt p := Real.sqrt_le_sqrt hp
  have hS : 1 ≤ S := by unfold S; linarith only [hsqrtp, Real.sqrt_nonneg |Real.log M.gamma|]
  have hlog3 : |Real.log M.gamma| ≤ |Real.log M.gamma| ^ (3 : ℕ) := by
    nlinarith only [hlog, sq_nonneg (|Real.log M.gamma| - 1)]
  have hcommon0 : 0 ≤ S * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by positivity
  have hDle : D ≤ 4 * K * B *
      (S * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) := by
    unfold D
    have h1 := mul_le_mul_of_nonneg_right hdefect hB.le
    have h2 : Real.sqrt M.gamma * |Real.log M.gamma| ≤
        S * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by
      have hbase := mul_le_mul_of_nonneg_left hlog3 (Real.sqrt_nonneg M.gamma)
      calc
        Real.sqrt M.gamma * |Real.log M.gamma| ≤
            Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := hbase
        _ = 1 * (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) := by ring
        _ ≤ S * (Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_right hS (mul_nonneg (Real.sqrt_nonneg _)
            (pow_nonneg (abs_nonneg _) 3))
        _ = S * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ) := by ring
    calc
      |(Annealed.sigmaBar M n : ℝ) / sigma - 1| * B ≤
          4 * K * Real.sqrt M.gamma * |Real.log M.gamma| * B := h1
      _ = (4 * K * B) * (Real.sqrt M.gamma * |Real.log M.gamma|) := by ring
      _ ≤ (4 * K * B) *
          (S * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 * K * B *
          (S * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) := by ring
  have hbase : (Annealed.sigmaBar M n : ℝ) / sigma * R + D ≤
      (2 * C + 4 * K * B) *
        (S * Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) := by
    unfold R
    have hRpart := mul_le_mul_of_nonneg_right hratio
      (mul_nonneg hC.le hcommon0)
    nlinarith only [hRpart, hDle]
  have hcoef : 2 * C + 4 * K * B ≤ C' := le_max_right _ _
  simpa only [S, mul_assoc] using
    hbase.trans (mul_le_mul_of_nonneg_right hcoef hcommon0)

end


end Algsuperdiff.Section5.Provider
