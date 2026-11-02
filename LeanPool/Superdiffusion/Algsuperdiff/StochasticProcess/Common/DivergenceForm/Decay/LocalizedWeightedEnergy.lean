/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.ExponentialWeight
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedSkewAlgebra

/-!
# LocalizedWeightedEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The weighted energy inequality with layer constants

The weighted energy estimate is restated so that the size of the coefficient
enters only on the transition layer of the weight.  Two structural facts make
this possible.

* The symmetric part of the coefficient is the fixed scalar `nu • I`, so the
  elliptic energy is *exactly* `nu` times the squared gradient at every point
  of the domain.  No upper size constant is used there.
* The coefficient enters everywhere else only through the flux cross term
  `⟨a grad u, grad zeta⟩`, whose second factor is supported on the layer
  `{grad zeta ≠ 0}`.  The Young inequality is therefore applied with a size
  constant that the caller supplies on that layer alone.

The resulting statements take exactly the form of the uniformly elliptic ones
with lower constant `nu` and with the upper constant replaced by the layer
size `C`; the ellipticity hypothesis on the whole domain survives only
qualitatively, to know that the flux is square integrable, and its upper
constant never enters a conclusion.

## Main results

- `DivergenceFormProcess.Decay.weightedEnergy_localized_le`
- `DivergenceFormProcess.Decay.weightedMass_le_of_energy`
- `DivergenceFormProcess.Decay.integral_sq_mul_gradSq_product_le`
- `DivergenceFormProcess.Decay.localizedMass_absorb`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-! ### The layer form of the weighted energy inequality -/

/-- **The weighted energy inequality with a layer size constant.**  The
coefficient has scalar symmetric part `nu • I`, so the elliptic energy is
exactly `nu` times the squared gradient; the size constant `C` is required
only where the weight gradient does not vanish. -/
theorem weightedEnergy_localized_le {a : CoeffField d} {g zeta : Vec d → ℝ}
    {u : H1Function U} {kk : Vec d → Mat d} {nu Lam C : ℝ}
    (hnu : 0 < nu) (hC : 0 < C)
    (hEll : IsEllipticFieldOn nu Lam U a)
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + kk y)
    (hskew : ∀ y, matTranspose (kk y) = -kk y)
    (hsol : IsScalarForcedWeakSolution a U g u)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hzetaCompact : HasCompactSupport zeta)
    (hadm : IsAdmissibleMultiplier U u (fun x => zeta x ^ 2))
    (hlayer : ∀ y ∈ U, fderiv ℝ zeta y ≠ 0 → ∀ v : Vec d,
      vecNormSq (matVecMul (a y) v) ≤ C ^ 2 * vecNormSq v) :
    nu / 2 * ∫ x in U, zeta x ^ 2 * vecNormSq (u.grad x) ∂volume ≤
      (∫ x in U, g x * (zeta x ^ 2 * u.toFun x) ∂volume) +
        2 * C ^ 2 / nu *
          ∫ x in U, u.toFun x ^ 2 *
            vecNormSq (fun i => (fderiv ℝ zeta x) (basisVec i)) ∂volume := by
  let mu := volumeMeasureOn U
  let dz : Vec d → Vec d := fun x i => (fderiv ℝ zeta x) (basisVec i)
  let qf : Vec d → Vec d := fun x => (zeta x ^ 2) • u.grad x
  let rf : Vec d → Vec d := fun x => (2 * zeta x * u.toFun x) • dz x
  obtain ⟨hphi, hphiCompact⟩ := sq_weight_smooth hzeta hzetaCompact
  obtain ⟨w, hwval, hwgrad⟩ := hadm
  have hphiTop : MemLp (fun x => zeta x ^ 2) ∞ mu :=
    (hphi.continuous.memLp_of_hasCompactSupport hphiCompact).restrict U
  have hdzTop : ∀ i : Fin d, MemLp (fun x => dz x i) ∞ mu := by
    intro i
    have hcont : Continuous (fun x => dz x i) := by
      simpa only [dz] using
        (hzeta.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcomp : HasCompactSupport (fun x => dz x i) := by
      simpa only [dz] using hzetaCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hcont.memLp_of_hasCompactSupport hcomp).restrict U
  have hq : MemVectorL2 U qf := by
    simpa only [MemVectorL2, volumeMeasureOn, qf, Pi.smul_apply, smul_eq_mul,
      mul_comm] using!
      (MemLp.of_eval fun i : Fin d =>
        (memScalarL2_coord_of_memVectorL2 u.grad_memVectorL2 i).fun_mul hphiTop)
  have hudz : MemVectorL2 U (fun x => u.toFun x • dz x) := by
    simpa only [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul,
      mul_comm] using!
      (MemLp.of_eval fun i : Fin d => u.memL2.fun_mul (hdzTop i))
  have hr : MemVectorL2 U rf := by
    have hbase : MemVectorL2 U (fun x => w.toH1Function.grad x - qf x) :=
      w.toH1Function.grad_memVectorL2.sub hq
    apply hbase.ae_eq
    filter_upwards [hwgrad] with x hx
    rw [hx]
    funext i
    simp only [qf, rf, dz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hfd : (fderiv ℝ (fun y => zeta y ^ 2) x) (basisVec i) =
        2 * zeta x * (fderiv ℝ zeta x) (basisVec i) := by
      have hdiff : DifferentiableAt ℝ zeta x := hzeta.differentiable (by simp) x
      rw [show (fun y => zeta y ^ 2) = zeta * zeta by
        funext y; simp only [pow_two, Pi.mul_apply]]
      rw [fderiv_mul hdiff hdiff]
      simp only [add_apply, smul_apply,
        smul_eq_mul]
      ring
    rw [hfd]
    ring
  have hflux : MemVectorL2 U (fun x => matVecMul (a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have henergyInt : Integrable (fun x =>
      vecDot (matVecMul (a x) (u.grad x)) (qf x)) mu :=
    integrableOn_vecDot_of_memVectorL2 hflux hq
  have hcrossInt : Integrable (fun x =>
      vecDot (matVecMul (a x) (u.grad x)) (rf x)) mu :=
    integrableOn_vecDot_of_memVectorL2 hflux hr
  have htargetInt : Integrable (fun x =>
      zeta x ^ 2 * vecNormSq (u.grad x)) mu := by
    apply (integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hq).congr
    filter_upwards with x
    simp only [vecNormSq, vecDot, qf, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcutInt : Integrable (fun x =>
      u.toFun x ^ 2 * vecNormSq (dz x)) mu := by
    apply (integrableOn_vecDot_of_memVectorL2 hudz hudz).congr
    filter_upwards with x
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmem : ∀ᵐ x ∂mu, x ∈ U :=
    (ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
      (Filter.Eventually.of_forall fun _ hx => hx)
  have hlower : nu * ∫ x, zeta x ^ 2 * vecNormSq (u.grad x) ∂mu ≤
      ∫ x, vecDot (matVecMul (a x) (u.grad x)) (qf x) ∂mu := by
    rw [← integral_const_mul]
    apply integral_mono_ae (htargetInt.const_mul nu) henergyInt
    filter_upwards with x
    have hquad : vecDot (matVecMul (a x) (u.grad x)) (u.grad x) =
        nu * vecNormSq (u.grad x) :=
      vecDot_matVecMul_eq_of_scalar_add_skew (hsplit x) (hskew x) (u.grad x)
    have hexp : vecDot (matVecMul (a x) (u.grad x)) (qf x) =
        zeta x ^ 2 * vecDot (matVecMul (a x) (u.grad x)) (u.grad x) := by
      simp only [qf, vecDot_smul_right]
    rw [hexp, hquad]
    ring_nf
    exact le_rfl
  have hid := weightedEnergy_identity hsol hzeta ⟨w, hwval, hwgrad⟩
  have hsplitInt : (∫ x, vecDot (matVecMul (a x) (u.grad x)) (qf x) ∂mu) +
      ∫ x, vecDot (matVecMul (a x) (u.grad x)) (rf x) ∂mu =
        ∫ x, g x * (zeta x ^ 2 * u.toFun x) ∂mu := by
    rw [← integral_add henergyInt hcrossInt]
    refine Eq.trans (integral_congr_ae ?_) hid
    filter_upwards with x
    simp only [qf, rf, dz, vecDot_smul_right]
  have hyoung : ∫ x, |vecDot (matVecMul (a x) (u.grad x)) (rf x)| ∂mu ≤
      nu / 2 * (∫ x, zeta x ^ 2 * vecNormSq (u.grad x) ∂mu) +
        2 * C ^ 2 / nu * ∫ x, u.toFun x ^ 2 * vecNormSq (dz x) ∂mu := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (htargetInt.const_mul _) (hcutInt.const_mul _)]
    apply integral_mono_ae hcrossInt.abs
      ((htargetInt.const_mul _).add (hcutInt.const_mul _))
    filter_upwards [hmem] with x hx
    have hexp : vecDot (matVecMul (a x) (u.grad x)) (rf x) =
        2 * zeta x * u.toFun x *
          vecDot (matVecMul (a x) (u.grad x)) (dz x) := by
      simp only [rf, vecDot_smul_right]
    rw [hexp]
    simp only [Pi.add_apply]
    by_cases hzero : fderiv ℝ zeta x = 0
    · have hdz : dz x = fun _ : Fin d => (0 : ℝ) := by
        funext i
        simp only [dz, hzero, zero_apply]
      have hdotzero : vecDot (matVecMul (a x) (u.grad x)) (dz x) = 0 := by
        rw [hdz]
        simp only [vecDot, mul_zero, Finset.sum_const_zero]
      have hnormzero : vecNormSq (dz x) = 0 := by
        rw [hdz]
        simp only [vecNormSq, vecDot, mul_zero, Finset.sum_const_zero]
      rw [hdotzero, hnormzero, mul_zero, abs_zero, mul_zero]
      have h1 : (0 : ℝ) ≤ nu / 2 * (zeta x ^ 2 * vecNormSq (u.grad x)) := by
        have := vecNormSq_nonneg (u.grad x)
        positivity
      linarith only [h1]
    · exact localizedFlux_young hnu hC (hlayer x hx hzero) (u.grad x) (dz x)
  have habs : -(∫ x, vecDot (matVecMul (a x) (u.grad x)) (rf x) ∂mu) ≤
      ∫ x, |vecDot (matVecMul (a x) (u.grad x)) (rf x)| ∂mu :=
    (neg_le_abs _).trans abs_integral_le_integral_abs
  change nu / 2 * ∫ x, zeta x ^ 2 * vecNormSq (u.grad x) ∂mu ≤
    (∫ x, g x * (zeta x ^ 2 * u.toFun x) ∂mu) +
      2 * C ^ 2 / nu * ∫ x, u.toFun x ^ 2 * vecNormSq (dz x) ∂mu
  linarith only [hlower, hsplitInt, hyoung, habs]

/-! ### The mass form -/

/-- **The mass form of an energy inequality.**  When the forcing has the
dissipative sign, the localized mass is bounded by whatever bounds the layer
term of the energy inequality.  The coefficient enters only through that
inequality. -/
theorem weightedMass_le_of_energy {a : CoeffField d} {g zeta : Vec d → ℝ}
    {u : H1Function U} {lam mass T : ℝ} (hlam : 0 < lam)
    (hsol : IsScalarForcedWeakSolution a U g u)
    (hadm : IsAdmissibleMultiplier U u (fun x => zeta x ^ 2))
    (hg : ∀ᵐ x ∂volumeMeasureOn U,
      zeta x ≠ 0 → g x * u.toFun x ≤ -(mass * u.toFun x ^ 2))
    (henergy : lam / 2 * ∫ x in U, zeta x ^ 2 * vecNormSq (u.grad x) ∂volume ≤
      (∫ x in U, g x * (zeta x ^ 2 * u.toFun x) ∂volume) + T) :
    mass * ∫ x in U, zeta x ^ 2 * u.toFun x ^ 2 ∂volume ≤ T := by
  let mu := volumeMeasureOn U
  obtain ⟨w, hwval, hwgrad⟩ := hadm
  have hprodL2 : MemScalarL2 U (fun x => zeta x ^ 2 * u.toFun x) := by
    have hw := w.toH1Function.memL2
    rwa [hwval] at hw
  have hforcingInt : Integrable (fun x => g x * (zeta x ^ 2 * u.toFun x)) mu :=
    hsol.1.integrable_mul hprodL2
  have hmassInt : Integrable (fun x => zeta x ^ 2 * u.toFun x ^ 2) mu := by
    apply (hprodL2.integrable_mul u.memL2).congr
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  have hforcing : (∫ x, g x * (zeta x ^ 2 * u.toFun x) ∂mu) ≤
      -(mass * ∫ x, zeta x ^ 2 * u.toFun x ^ 2 ∂mu) := by
    rw [← integral_const_mul, ← integral_neg]
    apply integral_mono_ae hforcingInt ((hmassInt.const_mul mass).neg)
    filter_upwards [hg] with x hx
    have hsq : (0 : ℝ) ≤ zeta x ^ 2 := sq_nonneg _
    by_cases hzero : zeta x = 0
    · simp only [Pi.neg_apply, hzero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, mul_zero, neg_zero, le_refl]
    · calc
        g x * (zeta x ^ 2 * u.toFun x) = zeta x ^ 2 * (g x * u.toFun x) := by
          ring
        _ ≤ zeta x ^ 2 * -(mass * u.toFun x ^ 2) :=
          mul_le_mul_of_nonneg_left (hx hzero) hsq
        _ = -(mass * (zeta x ^ 2 * u.toFun x ^ 2)) := by ring
  have hgrad : 0 ≤ lam / 2 * ∫ x, zeta x ^ 2 * vecNormSq (u.grad x) ∂mu := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg_of_ae
    filter_upwards with x
    exact mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
  change lam / 2 * ∫ x, zeta x ^ 2 * vecNormSq (u.grad x) ∂mu ≤
    (∫ x, g x * (zeta x ^ 2 * u.toFun x) ∂mu) + T at henergy
  change mass * ∫ x, zeta x ^ 2 * u.toFun x ^ 2 ∂mu ≤ T
  linarith only [hgrad, henergy, hforcing]


/-! ### Absorbing the exponential factor -/

/-- The squared gradient of a product weight is controlled by the squared
gradient of the localization and the logarithmic rate of the second factor. -/
theorem integral_sq_mul_gradSq_product_le {u : H1Function U}
    {eta chi : Vec d → ℝ} {kappa : ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiGrad : ∀ᵐ x ∂volumeMeasureOn U,
      vecNormSq (fun i => (fderiv ℝ chi x) (basisVec i)) ≤
        kappa ^ 2 * chi x ^ 2) :
    (∫ x in U, u.toFun x ^ 2 *
        vecNormSq (fun i =>
          (fderiv ℝ (fun y => eta y * chi y) x) (basisVec i)) ∂volume) ≤
      2 * (∫ x in U, u.toFun x ^ 2 *
          (chi x ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta x) (basisVec i))) ∂volume) +
        2 * kappa ^ 2 *
          ∫ x in U, u.toFun x ^ 2 * (eta x ^ 2 * chi x ^ 2) ∂volume := by
  classical
  let mu := volumeMeasureOn U
  let zeta : Vec d → ℝ := fun x => eta x * chi x
  have hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta := heta.mul hchi
  have hzetaCompact : HasCompactSupport zeta := hetaCompact.mul_right
  have hetaSq : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two] using! hetaCompact.mul_left (f := eta)
  have hmassTop : MemLp (fun x => eta x ^ 2 * chi x ^ 2) ∞ mu := by
    refine (Continuous.memLp_of_hasCompactSupport ?_ ?_).restrict U
    · exact (heta.continuous.pow 2).mul (hchi.continuous.pow 2)
    · exact hetaSq.mul_right
  have hcutTop : MemLp (fun x => chi x ^ 2 *
      vecNormSq (fun i => (fderiv ℝ eta x) (basisVec i))) ∞ mu := by
    refine (Continuous.memLp_of_hasCompactSupport ?_ ?_).restrict U
    · exact (hchi.continuous.pow 2).mul (continuous_gradSq heta)
    · exact (hasCompactSupport_gradSq hetaCompact).mul_left
  have hzetaTop : MemLp
      (fun x => vecNormSq (fun i => (fderiv ℝ zeta x) (basisVec i))) ∞ mu := by
    refine (Continuous.memLp_of_hasCompactSupport ?_ ?_).restrict U
    · exact continuous_gradSq hzeta
    · exact hasCompactSupport_gradSq hzetaCompact
  have hmassInt := integrable_sq_mul_memLpTop (u := u) hmassTop
  have hcutInt := integrable_sq_mul_memLpTop (u := u) hcutTop
  have hzetaInt := integrable_sq_mul_memLpTop (u := u) hzetaTop
  have hgradPt : ∀ᵐ x ∂volumeMeasureOn U,
      vecNormSq (fun i => (fderiv ℝ zeta x) (basisVec i)) ≤
        2 * (chi x ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta x) (basisVec i))) +
          2 * kappa ^ 2 * (eta x ^ 2 * chi x ^ 2) := by
    filter_upwards [hchiGrad] with x hchix
    have hsplitG : (fun i => (fderiv ℝ zeta x) (basisVec i)) =
        fun i => chi x * (fderiv ℝ eta x) (basisVec i) +
          eta x * (fderiv ℝ chi x) (basisVec i) := by
      funext i
      have hfd : DifferentiableAt ℝ eta x := heta.differentiable (by simp) x
      have hhd : DifferentiableAt ℝ chi x := hchi.differentiable (by simp) x
      change (fderiv ℝ (fun y => eta y * chi y) x) (basisVec i) = _
      rw [show (fun y => eta y * chi y) = eta * chi by
        funext y; simp only [Pi.mul_apply]]
      rw [fderiv_mul hfd hhd]
      simp only [add_apply, smul_apply,
        smul_eq_mul]
      ring
    rw [hsplitG]
    have hscale : ∀ (c : ℝ) (v : Vec d),
        vecNormSq (fun i => c * v i) = c ^ 2 * vecNormSq v := by
      intro c v
      simp only [vecNormSq, vecDot, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hbound : vecNormSq (fun i => chi x * (fderiv ℝ eta x) (basisVec i) +
        eta x * (fderiv ℝ chi x) (basisVec i)) ≤
        2 * (vecNormSq (fun i => chi x * (fderiv ℝ eta x) (basisVec i)) +
          vecNormSq (fun i => eta x * (fderiv ℝ chi x) (basisVec i))) :=
      vecNormSq_add_le (fun i => chi x * (fderiv ℝ eta x) (basisVec i))
        (fun i => eta x * (fderiv ℝ chi x) (basisVec i))
    rw [hscale, hscale] at hbound
    have hsq : (0 : ℝ) ≤ eta x ^ 2 := sq_nonneg _
    nlinarith only [hbound, hchix, hsq]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hcutInt.const_mul _) (hmassInt.const_mul _)]
  refine integral_mono_ae hzetaInt
    ((hcutInt.const_mul _).add (hmassInt.const_mul _)) ?_
  filter_upwards [hgradPt] with x hgx
  have hsq : (0 : ℝ) ≤ u.toFun x ^ 2 := sq_nonneg _
  calc
    u.toFun x ^ 2 * vecNormSq (fun i => (fderiv ℝ zeta x) (basisVec i)) ≤
        u.toFun x ^ 2 * (2 * (chi x ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta x) (basisVec i))) +
          2 * kappa ^ 2 * (eta x ^ 2 * chi x ^ 2)) :=
      mul_le_mul_of_nonneg_left hgx hsq
    _ = 2 * (u.toFun x ^ 2 * (chi x ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta x) (basisVec i)))) +
          2 * kappa ^ 2 *
            (u.toFun x ^ 2 * (eta x ^ 2 * chi x ^ 2)) := by ring

/-- Absorb a logarithmic weight while paying an explicit remainder from the mass budget. -/
theorem localizedMass_absorb_remainder {u : H1Function U} {eta chi : Vec d → ℝ}
    {mass kappa Cbase remainder : ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hCbase : 0 ≤ Cbase)
    (hchiGrad : ∀ᵐ x ∂volumeMeasureOn U,
      vecNormSq (fun i => (fderiv ℝ chi x) (basisVec i)) ≤ kappa ^ 2 * chi x ^ 2)
    (habs : remainder + 2 * Cbase * kappa ^ 2 ≤ mass / 2)
    (hbase : mass * ∫ x in U, (eta x * chi x) ^ 2 * u.toFun x ^ 2 ∂volume ≤
      Cbase * ∫ x in U, u.toFun x ^ 2 *
        vecNormSq (fun i =>
          (fderiv ℝ (fun y => eta y * chi y) x) (basisVec i)) ∂volume +
        remainder * ∫ x in U, u.toFun x ^ 2 * (eta x ^ 2 * chi x ^ 2) ∂volume) :
    mass / 2 * ∫ x in U, u.toFun x ^ 2 * (eta x ^ 2 * chi x ^ 2) ∂volume ≤
      2 * Cbase * ∫ x in U, u.toFun x ^ 2 *
        (chi x ^ 2 * vecNormSq (fun i => (fderiv ℝ eta x) (basisVec i))) ∂volume := by
  let A := ∫ x in U, u.toFun x ^ 2 * (eta x ^ 2 * chi x ^ 2) ∂volume
  let B := ∫ x in U, u.toFun x ^ 2 *
    (chi x ^ 2 * vecNormSq (fun i => (fderiv ℝ eta x) (basisVec i))) ∂volume
  let Z := ∫ x in U, u.toFun x ^ 2 *
    vecNormSq (fun i => (fderiv ℝ (fun y => eta y * chi y) x) (basisVec i)) ∂volume
  have hA0 : 0 ≤ A := integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => by
    dsimp only
    positivity)
  have hrewrite : (∫ x in U, (eta x * chi x) ^ 2 * u.toFun x ^ 2 ∂volume) = A := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hrewrite] at hbase
  change mass * A ≤ Cbase * Z + remainder * A at hbase
  have hcompare : Z ≤ 2 * B + 2 * kappa ^ 2 * A :=
    integral_sq_mul_gradSq_product_le heta hetaCompact hchi hchiGrad
  have hscaled := mul_le_mul_of_nonneg_left hcompare hCbase
  have habsorb : (remainder + 2 * Cbase * kappa ^ 2) * A ≤ mass / 2 * A :=
    mul_le_mul_of_nonneg_right habs hA0
  change mass / 2 * A ≤ 2 * Cbase * B
  nlinarith only [hbase, hscaled, habsorb]

/-- **Absorption of a logarithmic weight.**  Given a mass bound whose layer
term is the squared gradient of the product weight, and a factor obeying the
logarithmic gradient bound at rate `kappa`, half of the mass is absorbed and
only the gradient of the localization survives. -/
theorem localizedMass_absorb {u : H1Function U} {eta chi : Vec d → ℝ}
    {mass kappa Cbase : ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hCbase : 0 ≤ Cbase)
    (hchiGrad : ∀ᵐ x ∂volumeMeasureOn U,
      vecNormSq (fun i => (fderiv ℝ chi x) (basisVec i)) ≤ kappa ^ 2 * chi x ^ 2)
    (habs : 2 * Cbase * kappa ^ 2 ≤ mass / 2)
    (hbase : mass * ∫ x in U, (eta x * chi x) ^ 2 * u.toFun x ^ 2 ∂volume ≤
      Cbase * ∫ x in U, u.toFun x ^ 2 *
        vecNormSq (fun i =>
          (fderiv ℝ (fun y => eta y * chi y) x) (basisVec i)) ∂volume) :
    mass / 2 * ∫ x in U, u.toFun x ^ 2 * (eta x ^ 2 * chi x ^ 2) ∂volume ≤
      2 * Cbase * ∫ x in U, u.toFun x ^ 2 *
        (chi x ^ 2 *
          vecNormSq (fun i => (fderiv ℝ eta x) (basisVec i))) ∂volume := by
  exact localizedMass_absorb_remainder (remainder := 0) heta hetaCompact hchi hCbase
    hchiGrad (by simpa only [zero_add] using habs)
    (by simpa only [zero_mul, add_zero] using hbase)

/-! ### The localized Agmon mass estimate -/

end DivergenceFormProcess.Decay
