/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedSplitSkew

/-!
# LocalizedSplitMass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Agmon mass estimate with a split antisymmetric part

The drift term produced by the smooth antisymmetric part carries the
divergence of that part and the gradient of the exponential weight.  Both
contributions are paid for here: the part carried by the gradient of the
localization is absorbed by half of the mass, and the part carried by the
gradient of the phase is proportional to the rate, so it is absorbed by the
same budget that fixes the rate.

## Main results

- `DivergenceFormProcess.Decay.integral_sq_mul_vecDot_skewFieldDiv_le`
- `DivergenceFormProcess.Decay.agmonMass_split_le`
- `DivergenceFormProcess.Decay.localizedAgmonUpper`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-! ### The drift term -/

/-- The coordinate gradient of a squared weight. -/
theorem fderiv_sq_apply {zeta : Vec d → ℝ} (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y => zeta y ^ 2) x) (basisVec i) =
      2 * zeta x * (fderiv ℝ zeta x) (basisVec i) := by
  have hdiff : DifferentiableAt ℝ zeta x := hzeta.differentiable (by simp) x
  rw [show (fun y => zeta y ^ 2) = zeta * zeta by
    funext y; simp only [pow_two, Pi.mul_apply]]
  rw [fderiv_mul hdiff hdiff]
  simp only [add_apply, smul_apply,
    smul_eq_mul]
  ring

/-- A scalar Young inequality at the mass budget `mass / 8`. -/
private theorem abs_mul_le_mass_young {mass e c : ℝ} (hmass : 0 < mass) :
    |e| * |c| ≤ mass / 8 * e ^ 2 + 2 / mass * c ^ 2 := by
  set alpha : ℝ := Real.sqrt (mass / 4) with halpha_def
  have halpha : 0 < alpha := Real.sqrt_pos.2 (by positivity)
  have halpha2 : alpha ^ 2 = mass / 4 := Real.sq_sqrt (by positivity)
  have hbase := two_mul_le_add_sq (alpha * |e|) (|c| / alpha)
  have hprod : alpha * |e| * (|c| / alpha) = |e| * |c| := by
    field_simp
  have hsq1 : (alpha * |e|) ^ 2 = mass / 4 * e ^ 2 := by
    rw [mul_pow, halpha2, sq_abs]
  have hsq2 : (|c| / alpha) ^ 2 = c ^ 2 / (mass / 4) := by
    rw [div_pow, halpha2, sq_abs]
  rw [mul_assoc, hprod, hsq1, hsq2] at hbase
  have hval : c ^ 2 / (mass / 4) = 4 / mass * c ^ 2 := by
    field_simp
  rw [hval] at hbase
  have hhalf : mass / 8 * e ^ 2 + 2 / mass * c ^ 2 =
      (mass / 4 * e ^ 2 + 4 / mass * c ^ 2) / 2 := by ring
  rw [hhalf]
  linarith only [hbase]

/-- **The drift term of the smooth antisymmetric part.**  The drift produced by
integrating the smooth part by parts carries no gradient of the solution: it is
split between a part absorbed by an eighth of the mass and a layer part
proportional to the squared divergence bound and to the squared gradient of the
weight.  The size of the divergence is needed only on the layer that carries
the weight. -/
theorem integral_sq_mul_vecDot_skewFieldDiv_le {Om : Set (Vec d)}
    {u : H1Function Om} {kl : Vec d → Mat d} {zeta : Vec d → ℝ}
    {L : Set (Vec d)} {Kl mass : ℝ} (hmass : 0 < mass)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hzetaCompact : HasCompactSupport zeta)
    (hzetaL : tsupport zeta ⊆ L)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2) :
    -(1 / 2) * ∫ y in Om, u.toFun y ^ 2 *
        vecDot (skewFieldDiv kl y)
          (fun i => (fderiv ℝ (fun w => zeta w ^ 2) y) (basisVec i)) ∂volume ≤
      mass / 8 * (∫ y in Om, u.toFun y ^ 2 * zeta y ^ 2 ∂volume) +
        2 * Kl ^ 2 / mass *
          ∫ y in Om, u.toFun y ^ 2 *
            vecNormSq (fun i => (fderiv ℝ zeta y) (basisVec i)) ∂volume := by
  classical
  obtain ⟨hWsmooth, hWcompact⟩ := sq_weight_smooth hzeta hzetaCompact
  have hDwCont : ∀ i : Fin d, Continuous fun y =>
      (fderiv ℝ (fun w => zeta w ^ 2) y) (basisVec i) := by
    intro i
    exact (hWsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hbDwTop : MemLp (fun y => vecDot (skewFieldDiv kl y)
      (fun i => (fderiv ℝ (fun w => zeta w ^ 2) y) (basisVec i))) ∞
        (volumeMeasureOn Om) := by
    refine (Continuous.memLp_of_hasCompactSupport ?_ ?_).restrict Om
    · exact continuous_finsetSum _ fun i _ =>
        (continuous_skewFieldDiv_apply hklC1 i).mul (hDwCont i)
    · refine HasCompactSupport.intro hWcompact.isCompact ?_
      intro y hy
      have hzero : fderiv ℝ (fun w => zeta w ^ 2) y = 0 :=
        fderiv_of_notMem_tsupport ℝ hy
      simp only [hzero, zero_apply, vecDot, mul_zero,
        Finset.sum_const_zero]
  have hmassTop : MemLp (fun x => zeta x ^ 2) ∞ (volumeMeasureOn Om) :=
    (hWsmooth.continuous.memLp_of_hasCompactSupport hWcompact).restrict Om
  have hcutTop : MemLp
      (fun x => vecNormSq (fun i => (fderiv ℝ zeta x) (basisVec i))) ∞
        (volumeMeasureOn Om) :=
    ((continuous_gradSq hzeta).memLp_of_hasCompactSupport
      (hasCompactSupport_gradSq hzetaCompact)).restrict Om
  have hbDwInt := integrable_sq_mul_memLpTop (u := u) hbDwTop
  have hmassInt := integrable_sq_mul_memLpTop (u := u) hmassTop
  have hcutInt := integrable_sq_mul_memLpTop (u := u) hcutTop
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hmassInt.const_mul _) (hcutInt.const_mul _)]
  refine integral_mono_ae (hbDwInt.const_mul _)
    ((hmassInt.const_mul _).add (hcutInt.const_mul _)) ?_
  filter_upwards with y
  set b : Vec d := skewFieldDiv kl y with hb_def
  set Dz : Vec d := fun i => (fderiv ℝ zeta y) (basisVec i) with hDz_def
  have hdot : vecDot b
        (fun i => (fderiv ℝ (fun w => zeta w ^ 2) y) (basisVec i)) =
      2 * zeta y * vecDot b Dz := by
    simp only [vecDot, hDz_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_sq_apply hzeta y i]
    ring
  have hunn : (0 : ℝ) ≤ u.toFun y ^ 2 := sq_nonneg _
  by_cases hyL : y ∈ L
  · have hbSize := hklDiv y hyL
    have hcSq : vecDot b Dz ^ 2 ≤ Kl ^ 2 * vecNormSq Dz := by
      refine (sq_vecDot_le_vecNormSq_mul_vecNormSq b Dz).trans ?_
      exact mul_le_mul_of_nonneg_right hbSize (vecNormSq_nonneg _)
    have hyoung := abs_mul_le_mass_young (mass := mass) (e := zeta y)
      (c := vecDot b Dz) hmass
    have hcbound : 2 / mass * vecDot b Dz ^ 2 ≤
        2 * Kl ^ 2 / mass * vecNormSq Dz := by
      have hcoef : (0 : ℝ) ≤ 2 / mass := by positivity
      have hstep := mul_le_mul_of_nonneg_left hcSq hcoef
      calc
        2 / mass * vecDot b Dz ^ 2 ≤ 2 / mass * (Kl ^ 2 * vecNormSq Dz) := hstep
        _ = 2 * Kl ^ 2 / mass * vecNormSq Dz := by ring
    have habs : -(zeta y * vecDot b Dz) ≤ |zeta y| * |vecDot b Dz| := by
      calc
        -(zeta y * vecDot b Dz) ≤ |zeta y * vecDot b Dz| := neg_le_abs _
        _ = |zeta y| * |vecDot b Dz| := abs_mul _ _
    have hstep : -(zeta y * vecDot b Dz) ≤
        mass / 8 * zeta y ^ 2 + 2 * Kl ^ 2 / mass * vecNormSq Dz := by
      linarith only [habs, hyoung, hcbound]
    have hscaled := mul_le_mul_of_nonneg_left hstep hunn
    change -(1 / 2) * (u.toFun y ^ 2 *
      vecDot b (fun i =>
        (fderiv ℝ (fun w => zeta w ^ 2) y) (basisVec i))) ≤ _
    rw [hdot]
    nlinarith only [hscaled]
  · have hnotsupp : y ∉ tsupport zeta := fun hy => hyL (hzetaL hy)
    have hzetaZero : zeta y = 0 := image_eq_zero_of_notMem_tsupport hnotsupp
    have hDzZero : Dz = fun _ : Fin d => (0 : ℝ) := by
      funext i
      rw [hDz_def]
      simp only [fderiv_of_notMem_tsupport ℝ hnotsupp,
        zero_apply]
    have hnormZero : vecNormSq (fun _ : Fin d => (0 : ℝ)) = 0 := by
      simp only [vecNormSq, vecDot, mul_zero, Finset.sum_const_zero]
    change -(1 / 2) * (u.toFun y ^ 2 *
      vecDot b (fun i =>
        (fderiv ℝ (fun w => zeta w ^ 2) y) (basisVec i))) ≤ _
    rw [hdot, hzetaZero, hDzZero, hnormZero]
    ring_nf
    exact le_rfl



/-! ### The Agmon mass estimate with a split antisymmetric part -/

/-- **The Agmon weighted mass estimate with a split antisymmetric part.**  The
rough part contributes its size on the layer and the smooth part its
divergence on the layer; the admissibility of the rate is the single budget
inequality `hadmiss`. -/
theorem agmonMass_split_le {Om : Set (Vec d)} (hOmOpen : IsOpen Om)
    (hOmBdd : IsBoundedDomain Om) {a : CoeffField d} {ks kl : Vec d → Mat d}
    {z : H10Function Om} {g eta psi : Vec d → ℝ} {L : Set (Vec d)}
    {nu LamS Ks Kl mass kappa : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hmass : 0 < mass)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om g z.toH1Function)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaL : tsupport eta ⊆ L) (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
      vecNormSq (fun i => (fderiv ℝ psi y) (basisVec i)) ≤ 1)
    (hg : ∀ᵐ y ∂volumeMeasureOn Om,
      eta y ≠ 0 → g y * z.toH1Function.toFun y ≤
        -(mass * z.toH1Function.toFun y ^ 2))
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    (hadmiss : (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) * kappa ^ 2 ≤
      3 * mass / 8) :
    mass / 2 * ∫ y in Om, z.toH1Function.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume ≤
      (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) *
        ∫ y in Om, z.toH1Function.toFun y ^ 2 *
          (Real.exp (kappa * psi y) ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume := by
  classical
  have hchiSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => Real.exp (kappa * psi y)) :=
    contDiff_exponentialWeight hpsi kappa
  have hzetaSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => eta y * Real.exp (kappa * psi y)) := heta.mul hchiSmooth
  have hzetaCompact : HasCompactSupport
      (fun y => eta y * Real.exp (kappa * psi y)) := hetaCompact.mul_right
  have hzetaL : tsupport (fun y => eta y * Real.exp (kappa * psi y)) ⊆ L :=
    tsupport_mul_subset hetaL
  have hadm := isAdmissibleMultiplier_sq_of_zeroTrace z hzetaSmooth hzetaCompact
  have hgzeta : ∀ᵐ y ∂volumeMeasureOn Om,
      eta y * Real.exp (kappa * psi y) ≠ 0 →
        g y * z.toH1Function.toFun y ≤
          -(mass * z.toH1Function.toFun y ^ 2) := by
    filter_upwards [hg] with y hy hzy
    refine hy ?_
    intro hzero
    exact hzy (by rw [hzero, zero_mul])
  have hchiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
      vecNormSq (fun i =>
          (fderiv ℝ (fun w => Real.exp (kappa * psi w)) y) (basisVec i)) ≤
        kappa ^ 2 * Real.exp (kappa * psi y) ^ 2 := by
    filter_upwards [hpsiGrad] with y hy
    exact exponentialWeight_gradient_le hpsi hy kappa
  have hsplitEnergy := weightedEnergy_split_le hOmOpen hOmBdd hnu hKs hEllS
    hsplit hksSkew hklSkew hklC1 hsol hzetaSmooth hzetaCompact hzetaL hksSize
  have hZle := integral_sq_mul_gradSq_product_le (u := z.toH1Function)
    (kappa := kappa) heta hetaCompact hchiSmooth hchiGrad
  have hDle := integral_sq_mul_vecDot_skewFieldDiv_le (u := z.toH1Function)
    (kl := kl) (L := L) (mass := mass) hmass hzetaSmooth hzetaCompact hzetaL
    hklC1 hklDiv
  set A := ∫ y in Om, z.toH1Function.toFun y ^ 2 *
    (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume with hA_def
  set B := ∫ y in Om, z.toH1Function.toFun y ^ 2 *
    (Real.exp (kappa * psi y) ^ 2 *
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume with hB_def
  set Zg := ∫ y in Om, z.toH1Function.toFun y ^ 2 *
    vecNormSq (fun i =>
      (fderiv ℝ (fun w => eta w * Real.exp (kappa * psi w)) y)
        (basisVec i)) ∂volume with hZ_def
  set D := ∫ y in Om, z.toH1Function.toFun y ^ 2 *
    vecDot (skewFieldDiv kl y)
      (fun i => (fderiv ℝ
        (fun w => (eta w * Real.exp (kappa * psi w)) ^ 2) y) (basisVec i))
    ∂volume with hD_def
  have henergy : nu / 2 * (∫ x in Om,
      (eta x * Real.exp (kappa * psi x)) ^ 2 *
        vecNormSq (z.toH1Function.grad x) ∂volume) ≤
      (∫ x in Om, g x * ((eta x * Real.exp (kappa * psi x)) ^ 2 *
        z.toH1Function.toFun x) ∂volume) +
        (2 * (nu + Ks) ^ 2 / nu * Zg - 1 / 2 * D) := by
    linarith only [hsplitEnergy]
  have hmassRaw := weightedMass_le_of_energy hnu hsol hadm hgzeta henergy
  have hArw : (∫ x in Om, (eta x * Real.exp (kappa * psi x)) ^ 2 *
      z.toH1Function.toFun x ^ 2 ∂volume) = A := by
    rw [hA_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hDArw : (∫ y in Om, z.toH1Function.toFun y ^ 2 *
      (eta y * Real.exp (kappa * psi y)) ^ 2 ∂volume) = A := by
    rw [hA_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hArw] at hmassRaw
  rw [hDArw] at hDle
  have hA0 : 0 ≤ A := by
    rw [hA_def]
    refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => ?_)
    positivity
  have hCnn : (0 : ℝ) ≤ 2 * (nu + Ks) ^ 2 / nu + 2 * Kl ^ 2 / mass := by
    positivity
  set C : ℝ := 2 * (nu + Ks) ^ 2 / nu + 2 * Kl ^ 2 / mass with hC_def
  have hcombine : mass * A ≤ C * Zg + mass / 8 * A := by
    rw [hC_def]
    linarith only [hmassRaw, hDle]
  have hZmul : C * Zg ≤ C * (2 * B + 2 * kappa ^ 2 * A) :=
    mul_le_mul_of_nonneg_left hZle hCnn
  have hadmiss' : 2 * C * kappa ^ 2 ≤ 3 * mass / 8 := by
    rw [hC_def]
    calc 2 * (2 * (nu + Ks) ^ 2 / nu + 2 * Kl ^ 2 / mass) * kappa ^ 2
        = (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) * kappa ^ 2 := by ring
      _ ≤ 3 * mass / 8 := hadmiss
  have hadmA : 2 * C * kappa ^ 2 * A ≤ 3 * mass / 8 * A :=
    mul_le_mul_of_nonneg_right hadmiss' hA0
  have hgoal : (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) = 2 * C := by
    rw [hC_def]
    ring
  rw [hgoal]
  nlinarith only [hcombine, hZmul, hadmA]

/-! ### The effective upper constant -/

/-- The effective upper ellipticity constant of the localized estimate: the
size of the rough part on the layer, together with the divergence of the
smooth part measured against the mass. -/
def localizedAgmonUpper (nu mass Ks Kl : ℝ) : ℝ :=
  Real.sqrt 2 * (nu + Ks + 2 * Kl * Real.sqrt (nu / mass))

theorem localizedAgmonUpper_pos {nu mass Ks Kl : ℝ} (hnu : 0 < nu)
    (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) :
    0 < localizedAgmonUpper nu mass Ks Kl := by
  unfold localizedAgmonUpper
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hterm : (0 : ℝ) ≤ 2 * Kl * Real.sqrt (nu / mass) := by positivity
  have hsum : (0 : ℝ) < nu + Ks + 2 * Kl * Real.sqrt (nu / mass) := by
    linarith only [hnu, hKs, hterm]
  exact mul_pos h2 hsum

/-- The effective constant dominates the size of the rough part. -/
theorem two_mul_sq_le_localizedAgmonUpper_sq {nu mass Ks Kl : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) :
    2 * (nu + Ks) ^ 2 ≤ localizedAgmonUpper nu mass Ks Kl ^ 2 := by
  unfold localizedAgmonUpper
  have hterm : (0 : ℝ) ≤ 2 * Kl * Real.sqrt (nu / mass) := by positivity
  have hS : (0 : ℝ) ≤ nu + Ks := by linarith only [hnu, hKs]
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [mul_pow, hsq2]
  have hmono : (nu + Ks) ^ 2 ≤
      (nu + Ks + 2 * Kl * Real.sqrt (nu / mass)) ^ 2 :=
    pow_le_pow_left₀ hS (by linarith only [hterm]) 2
  linarith only [hmono]

/-- The effective constant dominates the divergence of the smooth part
measured against the mass. -/
theorem eight_mul_div_le_localizedAgmonUpper_sq {nu mass Ks Kl : ℝ}
    (hnu : 0 < nu) (hmass : 0 < mass) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) :
    8 * nu * Kl ^ 2 / mass ≤ localizedAgmonUpper nu mass Ks Kl ^ 2 := by
  unfold localizedAgmonUpper
  have hterm : (0 : ℝ) ≤ 2 * Kl * Real.sqrt (nu / mass) := by positivity
  have hS : (0 : ℝ) ≤ nu + Ks := by linarith only [hnu, hKs]
  have hsq2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hroot : Real.sqrt (nu / mass) ^ 2 = nu / mass :=
    Real.sq_sqrt (by positivity)
  rw [mul_pow, hsq2]
  have hmono : (2 * Kl * Real.sqrt (nu / mass)) ^ 2 ≤
      (nu + Ks + 2 * Kl * Real.sqrt (nu / mass)) ^ 2 :=
    pow_le_pow_left₀ hterm (by linarith only [hS]) 2
  have hval : (2 * Kl * Real.sqrt (nu / mass)) ^ 2 = 4 * Kl ^ 2 * (nu / mass) := by
    rw [mul_pow, mul_pow, hroot]
    ring
  rw [hval] at hmono
  have hid : 8 * nu * Kl ^ 2 / mass = 2 * (4 * Kl ^ 2 * (nu / mass)) := by
    field_simp
    ring
  rw [hid]
  linarith only [hmono]

/-! ### The uniformly elliptic shape at the effective constant -/

/-- **The localized Agmon mass estimate at the effective constant.**  With the
effective upper constant the estimate takes exactly the form of the uniformly
elliptic one, at lower constant `nu`, and so does its admissibility
hypothesis. -/
theorem agmonMass_localizedSplit_le {Om : Set (Vec d)} (hOmOpen : IsOpen Om)
    (hOmBdd : IsBoundedDomain Om) {a : CoeffField d} {ks kl : Vec d → Mat d}
    {z : H10Function Om} {g eta psi : Vec d → ℝ} {L : Set (Vec d)}
    {nu LamS Ks Kl mass kappa : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) (hmass : 0 < mass)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om g z.toH1Function)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaL : tsupport eta ⊆ L) (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
      vecNormSq (fun i => (fderiv ℝ psi y) (basisVec i)) ≤ 1)
    (hg : ∀ᵐ y ∂volumeMeasureOn Om,
      eta y ≠ 0 → g y * z.toH1Function.toFun y ≤
        -(mass * z.toH1Function.toFun y ^ 2))
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    (hkappa : 8 * localizedAgmonUpper nu mass Ks Kl ^ 2 * kappa ^ 2 ≤
      nu * mass) :
    mass / 2 * ∫ y in Om, z.toH1Function.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume ≤
      4 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu *
        ∫ y in Om, z.toH1Function.toFun y ^ 2 *
          (Real.exp (kappa * psi y) ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume := by
  have hL1 := two_mul_sq_le_localizedAgmonUpper_sq (mass := mass) hnu hKs hKl
  have hL2 := eight_mul_div_le_localizedAgmonUpper_sq hnu hmass hKs hKl
  have hcoef : 4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass ≤
      3 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu := by
    rw [le_div_iff₀ hnu]
    have hexp : (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) * nu =
        4 * (nu + Ks) ^ 2 + 4 * nu * Kl ^ 2 / mass := by
      field_simp
    rw [hexp]
    have hLsq0 : (0 : ℝ) ≤ localizedAgmonUpper nu mass Ks Kl ^ 2 := sq_nonneg _
    have hnn : (0 : ℝ) ≤ nu * Kl ^ 2 := by positivity
    have hinv : (0 : ℝ) ≤ mass⁻¹ := (inv_pos.2 hmass).le
    have hL2' : 4 * nu * Kl ^ 2 / mass ≤
        localizedAgmonUpper nu mass Ks Kl ^ 2 := by
      refine le_trans ?_ hL2
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith only [hnn]) hinv
    linarith only [hL1, hL2', hLsq0]
  have hkappaSq : (0 : ℝ) ≤ kappa ^ 2 := sq_nonneg _
  have hLsqk : localizedAgmonUpper nu mass Ks Kl ^ 2 * kappa ^ 2 ≤
      nu * mass / 8 := by linarith only [hkappa]
  have hadmiss : (4 * (nu + Ks) ^ 2 / nu + 4 * Kl ^ 2 / mass) * kappa ^ 2 ≤
      3 * mass / 8 := by
    have hstep := mul_le_mul_of_nonneg_right hcoef hkappaSq
    have hval : 3 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu * kappa ^ 2 ≤
        3 * mass / 8 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hnu]
      nlinarith only [hLsqk, hnu]
    linarith only [hstep, hval]
  have hbase := agmonMass_split_le hOmOpen hOmBdd hnu hKs hmass hEllS hsplit
    hksSkew hklSkew hklC1 hsol heta hetaCompact hetaL hpsi hpsiGrad hg
    hksSize hklDiv hadmiss
  refine hbase.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · have hLsq : (0 : ℝ) ≤ localizedAgmonUpper nu mass Ks Kl ^ 2 := sq_nonneg _
    have hquarter : 3 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu ≤
        4 * localizedAgmonUpper nu mass Ks Kl ^ 2 / nu := by
      have hinv : (0 : ℝ) < nu⁻¹ := inv_pos.2 hnu
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith only [hLsq]) hinv.le
    linarith only [hcoef, hquarter]
  · refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => ?_)
    have := vecNormSq_nonneg (fun i => (fderiv ℝ eta x) (basisVec i))
    positivity

/-! ### The Caccioppoli gradient bound with a split antisymmetric part -/

/-- **The Caccioppoli gradient bound with a split antisymmetric part.**  The
mass term is retained and absorbs the part of the drift carried by the
gradient of the localization, so the constant depends only on the size of the
rough part and the divergence of the smooth part on the layer. -/
theorem setIntegral_gradSq_split_le {Om : Set (Vec d)} (hOmOpen : IsOpen Om)
    (hOmBdd : IsBoundedDomain Om) {a : CoeffField d} {ks kl : Vec d → Mat d}
    {z : H10Function Om} {g eta : Vec d → ℝ} {L : Set (Vec d)}
    {nu LamS Ks Kl mu M Ceta volLayer : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hmu : 0 < mu)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om
      (fun y => g y - mu * z.toH1Function.toFun y) z.toH1Function)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaL : tsupport eta ⊆ L)
    (hzero : ∀ᵐ y ∂volumeMeasureOn Om, eta y ≠ 0 → g y = 0)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |z.toH1Function.toFun y| ≤ M)
    (hCeta : 0 ≤ Ceta)
    (hetaGrad : ∀ y ∈ Om,
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ≤ Ceta)
    (hvolLayer : (volume {y ∈ Om | fderiv ℝ eta y ≠ 0}).toReal ≤ volLayer)
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    {W : Set (Vec d)} (hW : MeasurableSet W) (hWOm : W ⊆ Om)
    (hWeta : ∀ y ∈ W, eta y = 1) :
    (∫ y in W, vecNormSq (z.toH1Function.grad y) ∂volume) ≤
      (4 * (nu + Ks) ^ 2 / nu ^ 2 + Kl ^ 2 / (nu * mu)) * M ^ 2 *
        (Ceta * volLayer) := by
  classical
  have hsplitEnergy := weightedEnergy_split_le hOmOpen hOmBdd hnu hKs hEllS
    hsplit hksSkew hklSkew hklC1 hsol heta hetaCompact hetaL hksSize
  have hDle := integral_sq_mul_vecDot_skewFieldDiv_le (u := z.toH1Function)
    (kl := kl) (L := L) (mass := 4 * mu) (by linarith only [hmu]) heta
    hetaCompact hetaL hklC1 hklDiv
  have hmassInt : Integrable
      (fun x => z.toH1Function.toFun x ^ 2 * eta x ^ 2)
      (volumeMeasureOn Om) := by
    have hetaSq : HasCompactSupport (fun x => eta x ^ 2) := by
      simpa only [pow_two] using! hetaCompact.mul_left (f := eta)
    have htop : MemLp (fun x => eta x ^ 2) ∞ (volumeMeasureOn Om) :=
      ((heta.continuous.pow 2).memLp_of_hasCompactSupport hetaSq).restrict Om
    exact integrable_sq_mul_memLpTop (u := z.toH1Function) htop
  have hforce : (∫ x in Om, (g x - mu * z.toH1Function.toFun x) *
      (eta x ^ 2 * z.toH1Function.toFun x) ∂volume) ≤
      -(mu * ∫ x in Om,
        z.toH1Function.toFun x ^ 2 * eta x ^ 2 ∂volume) := by
    rw [← integral_const_mul, ← integral_neg]
    refine integral_mono_ae ?_ ((hmassInt.const_mul mu).neg) ?_
    · obtain ⟨w, hwval, -⟩ := isAdmissibleMultiplier_sq_of_zeroTrace z heta
        hetaCompact
      have hprodL2 : MemScalarL2 Om
          (fun x => eta x ^ 2 * z.toH1Function.toFun x) := by
        have hw := w.toH1Function.memL2
        rwa [hwval] at hw
      exact hsol.1.integrable_mul hprodL2
    · filter_upwards [hzero] with x hx
      by_cases hetax : eta x = 0
      · simp [hetax]
      · rw [hx hetax]
        have hid : (0 - mu * z.toH1Function.toFun x) *
            (eta x ^ 2 * z.toH1Function.toFun x) =
            -(mu * (z.toH1Function.toFun x ^ 2 * eta x ^ 2)) := by ring
        rw [hid]
  have hlayerBound := setIntegral_sq_mul_gradSq_layer_le (u := z.toH1Function)
    hOmOpen hOmBdd hMbound heta hetaCompact hCeta hetaGrad hvolLayer
  have hcoef : 4 * mu / 8 = mu / 2 := by ring
  rw [hcoef] at hDle
  have hval : 2 * Kl ^ 2 / (4 * mu) = Kl ^ 2 / (2 * mu) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hval] at hDle
  set X := ∫ x in Om, z.toH1Function.toFun x ^ 2 * eta x ^ 2 ∂volume
    with hX_def
  set Y := ∫ y in Om, z.toH1Function.toFun y ^ 2 *
    vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ∂volume with hY_def
  set G := ∫ x in Om, eta x ^ 2 *
    vecNormSq (z.toH1Function.grad x) ∂volume with hG_def
  have hX0 : 0 ≤ X := by
    rw [hX_def]
    refine integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => ?_)
    positivity
  have hmuX : (0 : ℝ) ≤ mu / 2 * X := by positivity
  have hgrad : nu / 2 * G ≤
      (2 * (nu + Ks) ^ 2 / nu + Kl ^ 2 / (2 * mu)) * Y := by
    linarith only [hsplitEnergy, hforce, hDle, hmuX]
  have hnu2 : (0 : ℝ) < nu / 2 := by linarith only [hnu]
  have hcoefnn : (0 : ℝ) ≤ 2 * (nu + Ks) ^ 2 / nu + Kl ^ 2 / (2 * mu) := by
    positivity
  have hstep : G ≤ (2 * (nu + Ks) ^ 2 / nu + Kl ^ 2 / (2 * mu)) *
      (M ^ 2 * Ceta * volLayer) / (nu / 2) := by
    rw [le_div_iff₀ hnu2]
    have hmono := mul_le_mul_of_nonneg_left hlayerBound hcoefnn
    linarith only [hgrad, hmono]
  have hvalue : (2 * (nu + Ks) ^ 2 / nu + Kl ^ 2 / (2 * mu)) *
      (M ^ 2 * Ceta * volLayer) / (nu / 2) =
      (4 * (nu + Ks) ^ 2 / nu ^ 2 + Kl ^ 2 / (nu * mu)) * M ^ 2 *
        (Ceta * volLayer) := by
    field_simp
    ring
  rw [hvalue] at hstep
  exact setIntegral_gradSq_le_of_localizedBound heta hetaCompact hstep hW hWOm
    hWeta

/-- **The Caccioppoli gradient bound at the effective constant.**  With the
effective upper constant the bound takes exactly the form of the uniformly
elliptic one, at lower constant `nu`. -/
theorem setIntegral_gradSq_localizedSplit_le {Om : Set (Vec d)}
    (hOmOpen : IsOpen Om) (hOmBdd : IsBoundedDomain Om) {a : CoeffField d}
    {ks kl : Vec d → Mat d} {z : H10Function Om} {g eta : Vec d → ℝ}
    {L : Set (Vec d)} {nu LamS Ks Kl mu M Ceta volLayer : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) (hmu : 0 < mu)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om
      (fun y => g y - mu * z.toH1Function.toFun y) z.toH1Function)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaL : tsupport eta ⊆ L)
    (hzero : ∀ᵐ y ∂volumeMeasureOn Om, eta y ≠ 0 → g y = 0)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |z.toH1Function.toFun y| ≤ M)
    (hCeta : 0 ≤ Ceta)
    (hetaGrad : ∀ y ∈ Om,
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ≤ Ceta)
    (hvolLayer : (volume {y ∈ Om | fderiv ℝ eta y ≠ 0}).toReal ≤ volLayer)
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    {W : Set (Vec d)} (hW : MeasurableSet W) (hWOm : W ⊆ Om)
    (hWeta : ∀ y ∈ W, eta y = 1) :
    (∫ y in W, vecNormSq (z.toH1Function.grad y) ∂volume) ≤
      4 * localizedAgmonUpper nu mu Ks Kl ^ 2 / nu ^ 2 * M ^ 2 *
        (Ceta * volLayer) := by
  have hbase := setIntegral_gradSq_split_le hOmOpen hOmBdd hnu hKs hmu hEllS
    hsplit hksSkew hklSkew hklC1 hsol heta hetaCompact hetaL hzero hMbound
    hCeta hetaGrad hvolLayer hksSize hklDiv hW hWOm hWeta
  refine hbase.trans ?_
  have hvol0 : (0 : ℝ) ≤ volLayer := le_trans ENNReal.toReal_nonneg hvolLayer
  have hdata : (0 : ℝ) ≤ M ^ 2 * (Ceta * volLayer) := by positivity
  have hL1 := two_mul_sq_le_localizedAgmonUpper_sq (mass := mu) hnu hKs hKl
  have hL2 := eight_mul_div_le_localizedAgmonUpper_sq hnu hmu hKs hKl
  have hLsq0 : (0 : ℝ) ≤ localizedAgmonUpper nu mu Ks Kl ^ 2 := sq_nonneg _
  have hcoef : 4 * (nu + Ks) ^ 2 / nu ^ 2 + Kl ^ 2 / (nu * mu) ≤
      4 * localizedAgmonUpper nu mu Ks Kl ^ 2 / nu ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < nu ^ 2)]
    have hexp : (4 * (nu + Ks) ^ 2 / nu ^ 2 + Kl ^ 2 / (nu * mu)) * nu ^ 2 =
        4 * (nu + Ks) ^ 2 + nu * Kl ^ 2 / mu := by
      field_simp
    rw [hexp]
    have hnn : (0 : ℝ) ≤ nu * Kl ^ 2 := by positivity
    have hinv : (0 : ℝ) ≤ mu⁻¹ := (inv_pos.2 hmu).le
    have hL2' : nu * Kl ^ 2 / mu ≤ localizedAgmonUpper nu mu Ks Kl ^ 2 := by
      refine le_trans ?_ hL2
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith only [hnn]) hinv
    linarith only [hL1, hL2', hLsq0]
  have hstep := mul_le_mul_of_nonneg_right hcoef hdata
  calc
    (4 * (nu + Ks) ^ 2 / nu ^ 2 + Kl ^ 2 / (nu * mu)) * M ^ 2 *
        (Ceta * volLayer) =
        (4 * (nu + Ks) ^ 2 / nu ^ 2 + Kl ^ 2 / (nu * mu)) *
          (M ^ 2 * (Ceta * volLayer)) := by ring
    _ ≤ 4 * localizedAgmonUpper nu mu Ks Kl ^ 2 / nu ^ 2 *
          (M ^ 2 * (Ceta * volLayer)) := hstep
    _ = 4 * localizedAgmonUpper nu mu Ks Kl ^ 2 / nu ^ 2 * M ^ 2 *
          (Ceta * volLayer) := by ring

end DivergenceFormProcess.Decay
