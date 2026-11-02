/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedInteriorSkew

/-!
# LocalizedInteriorEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Localized split-skew energy for bounded interior solutions

The localization is supported inside the domain, so the solution may have
nonzero trace.  Both split-skew constants are read on an active set containing
the topological support of the localization.
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ}

/-- The split-skew weighted energy inequality for a bounded `H¹` solution.
The smooth skew term is transferred using the compact support of the weight,
not a zero-trace property of the solution. -/
theorem weightedEnergy_split_interior_le {Om : Set (Vec d)}
    (hOm : IsOpenBoundedConvexDomain Om)
    {a : CoeffField d} {ks kl : Vec d → Mat d} {u : H1Function Om}
    {g zeta : Vec d → ℝ} {L : Set (Vec d)} {nu LamS Ks M : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hM : 0 ≤ M)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om g u)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |u.toFun y| ≤ M)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (hzetaCompact : HasCompactSupport zeta) (hzetaOm : tsupport zeta ⊆ Om)
    (hzetaL : tsupport zeta ⊆ L)
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v) :
    nu / 2 * ∫ y in Om, zeta y ^ 2 * vecNormSq (u.grad y) ∂volume +
        1 / 2 * ∫ y in Om, u.toFun y ^ 2 *
          vecDot (skewFieldDiv kl y)
            (fun i => (fderiv ℝ (fun z => zeta z ^ 2) y) (basisVec i)) ∂volume ≤
      (∫ y in Om, g y * (zeta y ^ 2 * u.toFun y) ∂volume) +
        2 * (nu + Ks) ^ 2 / nu *
          ∫ y in Om, u.toFun y ^ 2 *
            vecNormSq (fun i => (fderiv ℝ zeta y) (basisVec i)) ∂volume := by
  classical
  let measureOm := volumeMeasureOn Om
  let S : CoeffField d := fun y => nu • (1 : Mat d) + ks y
  let dz : Vec d → Vec d := fun y i => (fderiv ℝ zeta y) (basisVec i)
  let qf : Vec d → Vec d := fun y => (zeta y ^ 2) • u.grad y
  let rf : Vec d → Vec d := fun y => (2 * zeta y * u.toFun y) • dz y
  obtain ⟨hweight, hweightCompact⟩ := sq_weight_smooth hzeta hzetaCompact
  have hadm := isAdmissibleMultiplier_sq_of_tsupport_subset hOm u hzeta
    hzetaCompact hzetaOm
  obtain ⟨test, htestVal, htestGrad⟩ := hadm
  have hweightTop : MemLp (fun y => zeta y ^ 2) ∞ measureOm :=
    (hweight.continuous.memLp_of_hasCompactSupport hweightCompact).restrict Om
  have hdzTop : ∀ i : Fin d, MemLp (fun y => dz y i) ∞ measureOm := by
    intro i
    have hcont : Continuous (fun y => dz y i) := by
      simpa only [dz] using
        (hzeta.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcomp : HasCompactSupport (fun y => dz y i) := by
      simpa only [dz] using hzetaCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hcont.memLp_of_hasCompactSupport hcomp).restrict Om
  have hqf : MemVectorL2 Om qf := by
    simpa only [MemVectorL2, volumeMeasureOn, qf, Pi.smul_apply, smul_eq_mul,
      mul_comm] using!
      (MemLp.of_eval fun i : Fin d =>
        (memScalarL2_coord_of_memVectorL2 u.grad_memVectorL2 i).fun_mul hweightTop)
  have hudZ : MemVectorL2 Om (fun y => u.toFun y • dz y) := by
    simpa only [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul,
      mul_comm] using!
      (MemLp.of_eval fun i : Fin d => u.memL2.fun_mul (hdzTop i))
  have hrf : MemVectorL2 Om rf := by
    have hbase : MemVectorL2 Om (fun y => test.toH1Function.grad y - qf y) :=
      test.toH1Function.grad_memVectorL2.sub hqf
    apply hbase.ae_eq
    filter_upwards [htestGrad] with y hy
    rw [hy]
    funext i
    simp only [qf, rf, dz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [fderiv_sq_apply hzeta y i]
    ring
  have hfluxS : MemVectorL2 Om (fun y => matVecMul (S y) (u.grad y)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllS u.grad_memVectorL2
  have hfluxL : MemVectorL2 Om (fun y => matVecMul (kl y) (u.grad y)) :=
    MemLp.of_eval fun i =>
      memScalarL2_matVecMul_coord hOm.isOpen.measurableSet hOm.isBoundedDomain
        hklC1 u.gradMemL2 i
  have htargetInt : Integrable
      (fun y => zeta y ^ 2 * vecNormSq (u.grad y)) measureOm := by
    apply (integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hqf).congr
    filter_upwards with y
    simp only [vecNormSq, vecDot, qf, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcutInt : Integrable
      (fun y => u.toFun y ^ 2 * vecNormSq (dz y)) measureOm := by
    apply (integrableOn_vecDot_of_memVectorL2 hudZ hudZ).congr
    filter_upwards with y
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcrossSInt : Integrable
      (fun y => vecDot (matVecMul (S y) (u.grad y)) (rf y)) measureOm :=
    integrableOn_vecDot_of_memVectorL2 hfluxS hrf
  have hcrossLInt : Integrable
      (fun y => vecDot (matVecMul (kl y) (u.grad y)) (rf y)) measureOm :=
    integrableOn_vecDot_of_memVectorL2 hfluxL hrf
  have henergy := weightedEnergy_identity hsol hzeta ⟨test, htestVal, htestGrad⟩
  have hdecomp :
      nu * (∫ y in Om, zeta y ^ 2 * vecNormSq (u.grad y) ∂volume) +
          (∫ y in Om, vecDot (matVecMul (S y) (u.grad y)) (rf y) ∂volume) +
          (∫ y in Om, vecDot (matVecMul (kl y) (u.grad y)) (rf y) ∂volume) =
        ∫ y in Om, g y * (zeta y ^ 2 * u.toFun y) ∂volume := by
    have hsumInt : Integrable (fun y =>
        nu * (zeta y ^ 2 * vecNormSq (u.grad y)) +
          vecDot (matVecMul (S y) (u.grad y)) (rf y)) measureOm :=
      (htargetInt.const_mul nu).add hcrossSInt
    calc
      _ = ∫ y, (nu * (zeta y ^ 2 * vecNormSq (u.grad y)) +
          vecDot (matVecMul (S y) (u.grad y)) (rf y)) +
          vecDot (matVecMul (kl y) (u.grad y)) (rf y) ∂measureOm := by
        rw [integral_add hsumInt hcrossLInt,
          integral_add (htargetInt.const_mul nu) hcrossSInt,
          integral_const_mul]
      _ = ∫ y in Om,
          zeta y ^ 2 * vecDot (matVecMul (a y) (u.grad y)) (u.grad y) +
            2 * zeta y * u.toFun y *
              vecDot (matVecMul (a y) (u.grad y))
                (fun i => (fderiv ℝ zeta y) (basisVec i)) ∂volume := by
        apply integral_congr_ae
        filter_upwards with y
        have hskewSum : matTranspose (ks y + kl y) = -(ks y + kl y) := by
          rw [show matTranspose (ks y + kl y) =
              matTranspose (ks y) + matTranspose (kl y) from
            Matrix.transpose_add (ks y) (kl y), hksSkew y, hklSkew y]
          exact (neg_add _ _).symm
        have hquad : vecDot (matVecMul (a y) (u.grad y)) (u.grad y) =
            nu * vecNormSq (u.grad y) :=
          vecDot_matVecMul_eq_of_scalar_add_skew
            (by rw [hsplit y, add_assoc]) hskewSum (u.grad y)
        have hmv : matVecMul (a y) (u.grad y) =
            fun i => matVecMul (S y) (u.grad y) i +
              matVecMul (kl y) (u.grad y) i := by
          funext i
          simp only [S]
          rw [hsplit y]
          simp only [matVecMul, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
        have hsumS :
            (∑ i : Fin d, matVecMul (S y) (u.grad y) i *
              (2 * zeta y * u.toFun y * (fderiv ℝ zeta y) (basisVec i))) =
              2 * zeta y * u.toFun y * (∑ i : Fin d,
                matVecMul (S y) (u.grad y) i *
                  (fderiv ℝ zeta y) (basisVec i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        have hsumL :
            (∑ i : Fin d, matVecMul (kl y) (u.grad y) i *
              (2 * zeta y * u.toFun y * (fderiv ℝ zeta y) (basisVec i))) =
              2 * zeta y * u.toFun y * (∑ i : Fin d,
                matVecMul (kl y) (u.grad y) i *
                  (fderiv ℝ zeta y) (basisVec i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hquad, show vecDot (matVecMul (a y) (u.grad y))
            (fun i => (fderiv ℝ zeta y) (basisVec i)) =
            vecDot (matVecMul (S y) (u.grad y))
                (fun i => (fderiv ℝ zeta y) (basisVec i)) +
              vecDot (matVecMul (kl y) (u.grad y))
                (fun i => (fderiv ℝ zeta y) (basisVec i)) by
          rw [hmv]
          simp only [vecDot, add_mul, Finset.sum_add_distrib]]
        simp only [vecDot, rf, dz, Pi.smul_apply, smul_eq_mul]
        rw [hsumS, hsumL]
        ring
      _ = _ := henergy
  have hsmooth :
      (∫ y in Om, vecDot (matVecMul (kl y) (u.grad y)) (rf y) ∂volume) =
        1 / 2 * ∫ y in Om, u.toFun y ^ 2 *
          vecDot (skewFieldDiv kl y)
            (fun i => (fderiv ℝ (fun z => zeta z ^ 2) y) (basisVec i)) ∂volume := by
    have htransfer := integral_mul_vecDot_matVecMul_eq_half_interior hOm hklC1
      hklSkew u hweight hweightCompact (tsupport_sq_weight_subset hzetaOm)
      hM hMbound
    rw [← htransfer]
    apply integral_congr_ae
    filter_upwards with y
    simp only [rf, dz, vecDot_smul_right]
    rw [show (fun i => (fderiv ℝ (fun z => zeta z ^ 2) y) (basisVec i)) =
        fun i => 2 * zeta y * (fderiv ℝ zeta y) (basisVec i) by
      funext i; exact fderiv_sq_apply hzeta y i]
    simp only [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hCpos : (0 : ℝ) < nu + Ks := by linarith only [hnu, hKs]
  have hmem : ∀ᵐ y ∂measureOm, y ∈ Om :=
    (ae_restrict_iff' hOm.isOpen.measurableSet).2
      (Filter.Eventually.of_forall fun _ hy => hy)
  have hyoung :
      ∫ y, |vecDot (matVecMul (S y) (u.grad y)) (rf y)| ∂measureOm ≤
        nu / 2 * (∫ y, zeta y ^ 2 * vecNormSq (u.grad y) ∂measureOm) +
          2 * (nu + Ks) ^ 2 / nu *
            ∫ y, u.toFun y ^ 2 * vecNormSq (dz y) ∂measureOm := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (htargetInt.const_mul _) (hcutInt.const_mul _)]
    apply integral_mono_ae hcrossSInt.abs
      ((htargetInt.const_mul _).add (hcutInt.const_mul _))
    filter_upwards [hmem] with y hy
    simp only [rf, vecDot_smul_right]
    by_cases hzero : fderiv ℝ zeta y = 0
    · have hdz : dz y = fun _ : Fin d => (0 : ℝ) := by
        funext i
        simp only [dz, hzero, zero_apply]
      rw [hdz]
      simp only [vecDot, mul_zero, Finset.sum_const_zero, abs_zero]
      exact add_nonneg
        (mul_nonneg (div_nonneg hnu.le (by norm_num))
          (mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)))
        (mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hnu.le)
          (mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)))
    · have hyL : y ∈ L := by
        apply hzetaL
        by_contra hn
        exact hzero (fderiv_of_notMem_tsupport ℝ hn)
      have hsize : ∀ v : Vec d,
          vecNormSq (matVecMul (S y) v) ≤ (nu + Ks) ^ 2 * vecNormSq v := by
        intro v
        exact vecNormSq_matVecMul_le_add_of_scalar_add_skew hnu.le hKs rfl
          (hksSkew y) (hksSize y hyL v)
      exact localizedFlux_young hnu hCpos hsize (u.grad y) (dz y)
  have habs :
      -(∫ y in Om, vecDot (matVecMul (S y) (u.grad y)) (rf y) ∂volume) ≤
        ∫ y in Om, |vecDot (matVecMul (S y) (u.grad y)) (rf y)| ∂volume :=
    (neg_le_abs _).trans abs_integral_le_integral_abs
  rw [hsmooth] at hdecomp
  change nu / 2 * (∫ y, zeta y ^ 2 * vecNormSq (u.grad y) ∂measureOm) + _ ≤ _
  linarith only [hdecomp, hyoung, habs]

end DivergenceFormProcess.Decay
