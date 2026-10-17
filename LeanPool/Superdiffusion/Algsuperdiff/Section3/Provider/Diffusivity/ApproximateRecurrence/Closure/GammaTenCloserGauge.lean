/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenAssemblyCell
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenAssemblyMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenLoad
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.SplitFoldIntegrability
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.VecGauge

/-!
# GammaTenCloserGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-2 cell bound at the closure's own corrector families

ABK26, Step 2 of `l.approximate.recurrence.formula`, target
`e.lower.bound.localization.terms`.

## The gap this module fills

`Closure.GammaTenAssemblyCell.meshFluctuationCellIntegrand_le_ancestor_fold_shape`
bounds the Step-2 cell integrand by `c1 H + c2 H` at a *free* Besov exponent
`s`, a *free* gauge `sigma_0`, and with the load leg read as `blockVecNormSum
(blockGaugeUp sigma_0 P_z)`.  The two proved moment producers read their legs
at fixed data:

* `LocalizationFluctuationSplitFoldArithmetic.exists_regime_gaugedEllipticitySum_pow_four_le`
  gauges the ellipticity sum by `shom_{n+h-1}`;
* `Closure.GammaTenLoad.exists_gammaTenLoadConst_root` reads the load as
  `sqrt (annealedSqrtNormSq shom_n (meshCellLoad ...))`.

## What is proved

* `gammaTenBesovExponent`, `gammaTenCellFactor`, `gammaTenDualityConst`,
  `gammaTenGaugeConst`, `gammaTenCrossConst`, `gammaTenQuadConst` --- the
  absolute constants of the fold at the fixed exponent, with their signs.  The
  duality constant is cube-independent by
  `Closure.GammaTenAssemblyCell.besovDualityConst_eq`, so `c1` and `c2` depend
  only on the dimension.
* `blockVecNormSum_blockGaugeUp_le_gaugeRatio` --- **the load-leg
  identification**:
  ```
    | bfA_0^{1/2} P |_1 + | bfA_0^{1/2} P |_2
      <=  sqrt ( 2 gaugeRatio(shom_low, shom_top) ) * sqrt ( annealedSqrtNormSq shom_low P ) .
  ```
  Both sides are gauge readings of the same load; the two constants are the
  `sqrt 2` of `(a + b)^2 <= 2 (a^2 + b^2)` and the gauge ratio of
  `PrincipalResponseMomentsFourth.gaugeRatio`.
* `blockVecNormSum_blockGaugeUp_le_gammaTenGaugeConst` --- the same at the
  closure's own pair of scales, where
  `PrincipalResponseComposeDisplayTwo.gaugeRatio_sigmaBar_le_readingConst` caps
  the ratio by the absolute `4 . 3^9`.
* `meshFluctuationCellIntegrand_le_closureFold` --- the Step-2 cell bound at
  the closure's own corrector families, in the exact `c1 H + c2 H` shape the
  grid fold consumes, with `F` the gauged ellipticity sum at the cell's
  scale-`(n+h)` ancestor, `G` the load in the producer's own spelling and `H`
  the pathwise Besov envelope.

## Binders

The large-cube gate, the depth/scale identity of the closure mesh, the two
`e.recurrence.params` facts `hcover`, `hshell`, the gauge-ratio cap `hgauge`,
the cell membership and the envelope.  No measurability, no moment and no
smallness proposition occurs.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2, `e.Pz.def`, `e.Fz.def`, the
  load display.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.CoarseEllipticity
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The absolute constants of the fold at the fixed exponent -/

/-- **The Besov exponent the closure fixes**, `s = 1/2`.  The ancestor route of
`Closure.GammaTenAssemblyCell.meshFluctuationCellIntegrand_le_ancestor_fold_shape`
forces `cgamma < s`, the annealed depth fold of
`LocalizationFluctuationAnnealedFold` asks for `s <= 1/2`, and the per-cube bound
asks for `0 < s < 1`; `1/2` is the unique value meeting all three uniformly in
the model. -/
def gammaTenBesovExponent : ℝ := 1 / 2

/-- **The absolute Poincare/ancestor factor `32 c_{s,2}^{-2} 3^{22}`** of the
cell bound at the fixed exponent. -/
def gammaTenCellFactor : ℝ :=
  32 * (Ch03.poincareDiscountFactor gammaTenBesovExponent (.finite 2) *
    Ch03.poincareDiscountFactor gammaTenBesovExponent (.finite 2)) * Real.rpow (3 : ℝ) 22

theorem gammaTenCellFactor_nonneg : 0 ≤ gammaTenCellFactor := by
  have hc : (0 : ℝ) ≤ Ch03.poincareDiscountFactor gammaTenBesovExponent (.finite 2) := by
    unfold Ch03.poincareDiscountFactor
    refine Real.rpow_nonneg ?_ _
    have h := HCPolySupport.geometricDiscount_pos
      (mul_pos (by norm_num [gammaTenBesovExponent] : (0 : ℝ) < gammaTenBesovExponent)
        (by norm_num : (0 : ℝ) < 2))
    have hpos : 0 < Ch02.geometricDiscount gammaTenBesovExponent 2 := by
      simpa [Ch02.geometricDiscount, HCPolySupport.geometricDiscount] using h
    exact hpos.le
  have h3 : (0 : ℝ) ≤ Real.rpow (3 : ℝ) 22 := Real.rpow_nonneg (by norm_num) _
  unfold gammaTenCellFactor
  positivity

/-- **The cube-independent duality constant `2 d 3^{d+s}`** at the fixed exponent
(`Closure.GammaTenAssemblyCell.besovDualityConst_eq`). -/
def gammaTenDualityConst (d : ℕ) : ℝ :=
  2 * (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + gammaTenBesovExponent)

theorem gammaTenDualityConst_nonneg (d : ℕ) : 0 ≤ gammaTenDualityConst d := by
  unfold gammaTenDualityConst; positivity

/-- **The gauge-transport factor** between the load's own gauge `shom_n` and the
ellipticity leg's gauge `shom_{n+h-1}`: the `sqrt 2` of
`(a + b)^2 <= 2 (a^2 + b^2)` times the absolute cap `4 . 3^9` of
`PrincipalResponseComposeDisplayTwo.gaugeRatio_sigmaBar_le_readingConst`. -/
def gammaTenGaugeConst : ℝ := Real.sqrt (2 * (4 * (3 : ℝ) ^ (9 : ℕ)))

theorem gammaTenGaugeConst_nonneg : 0 ≤ gammaTenGaugeConst := Real.sqrt_nonneg _

/-- **`c1`**, the coefficient of the cross term `F G H` of the Step-2 fold. -/
def gammaTenCrossConst (d : ℕ) : ℝ :=
  2 * gammaTenDualityConst d * gammaTenCellFactor * gammaTenGaugeConst

/-- **`c2`**, the coefficient of the quadratic term `F H H` of the Step-2 fold. -/
def gammaTenQuadConst (d : ℕ) : ℝ :=
  gammaTenDualityConst d * gammaTenDualityConst d * gammaTenCellFactor

theorem gammaTenCrossConst_nonneg (d : ℕ) : 0 ≤ gammaTenCrossConst d := by
  unfold gammaTenCrossConst
  have := gammaTenDualityConst_nonneg d
  have := gammaTenCellFactor_nonneg
  have := gammaTenGaugeConst_nonneg
  positivity

theorem gammaTenQuadConst_nonneg (d : ℕ) : 0 ≤ gammaTenQuadConst d := by
  unfold gammaTenQuadConst
  have := gammaTenDualityConst_nonneg d
  have := gammaTenCellFactor_nonneg
  positivity

/-! ## The load-leg identification -/

/-- The Euclidean vector norm of a nonnegative scalar multiple. -/
theorem vecNorm_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (v : Vec d) :
    vecNorm (c • v) = c * vecNorm v := by
  rw [Algsuperdiff.Section5.Support.vecNorm_smul, abs_of_nonneg hc]

/-- **The two gauge readings of one load.**

```
  | bfA_0^{1/2} P |_1 + | bfA_0^{1/2} P |_2
    <=  sqrt ( 2 rho ) * sqrt ( shom |P_1|^2 + shom^{-1} |P_2|^2 ) ,
```
with `rho = gaugeRatio shom_low shom_top` and `bfA_0` the gauge at `shom_top`.
The `2` is `(a + b)^2 <= 2 (a^2 + b^2)`, the `rho` is the change of gauge.
Unconditional. -/
theorem blockVecNormSum_blockGaugeUp_le_gaugeRatio (sigmaLow sigmaTop : PositiveScalar)
    (P : BlockVec d) :
    blockVecNormSum (blockGaugeUp (sigmaTop : ℝ) P) ≤
      Real.sqrt (2 * gaugeRatio sigmaLow sigmaTop) *
        Real.sqrt (annealedSqrtNormSq sigmaLow P) := by
  have hLow : (0 : ℝ) < (sigmaLow : ℝ) := sigmaLow.2
  have hTop : (0 : ℝ) < (sigmaTop : ℝ) := sigmaTop.2
  set a : ℝ := vecNorm P.1 with ha
  set b : ℝ := vecNorm P.2 with hb
  have ha0 : 0 ≤ a := vecNorm_nonneg _
  have hb0 : 0 ≤ b := vecNorm_nonneg _
  set t : ℝ := Real.sqrt (sigmaTop : ℝ) with ht
  have htpos : (0 : ℝ) < t := Real.sqrt_pos.2 hTop
  have htsq : t ^ 2 = (sigmaTop : ℝ) := Real.sq_sqrt hTop.le
  have hLHS : blockVecNormSum (blockGaugeUp (sigmaTop : ℝ) P) = t * a + t⁻¹ * b := by
    rw [blockVecNormSum, blockGaugeUp_fst, blockGaugeUp_snd,
      vecNorm_smul_of_nonneg (Real.sqrt_nonneg _),
      vecNorm_smul_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  have hA : annealedSqrtNormSq sigmaLow P =
      (sigmaLow : ℝ) * a ^ 2 + ((sigmaLow : ℝ))⁻¹ * b ^ 2 := by
    rw [annealedSqrtNormSq, ha, hb, vecNorm_sq_eq_vecNormSq, vecNorm_sq_eq_vecNormSq]
  set rho : ℝ := gaugeRatio sigmaLow sigmaTop with hrho
  have hrho1 : (sigmaTop : ℝ) / (sigmaLow : ℝ) ≤ rho := le_max_left _ _
  have hrho2 : (sigmaLow : ℝ) / (sigmaTop : ℝ) ≤ rho := le_max_right _ _
  have hrho0 : (0 : ℝ) < rho := gaugeRatio_pos _ _
  have hcmp1 : (sigmaTop : ℝ) ≤ rho * (sigmaLow : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hrho1 hLow.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hLow)] at h
  have hcmp2 : ((sigmaTop : ℝ))⁻¹ ≤ rho * ((sigmaLow : ℝ))⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hrho2 (inv_pos.2 hLow).le
    rwa [div_mul_eq_mul_div, mul_inv_cancel₀ (ne_of_gt hLow), one_div] at h
  have hkey : (t * a + t⁻¹ * b) ^ 2 ≤ 2 * rho * annealedSqrtNormSq sigmaLow P := by
    have hsplit : (t * a + t⁻¹ * b) ^ 2 ≤ 2 * ((t * a) ^ 2 + (t⁻¹ * b) ^ 2) := by
      nlinarith [sq_nonneg (t * a - t⁻¹ * b)]
    have hta : (t * a) ^ 2 = (sigmaTop : ℝ) * a ^ 2 := by rw [mul_pow, htsq]
    have htb : (t⁻¹ * b) ^ 2 = ((sigmaTop : ℝ))⁻¹ * b ^ 2 := by
      rw [mul_pow, inv_pow, htsq]
    have h1 : (sigmaTop : ℝ) * a ^ 2 ≤ rho * ((sigmaLow : ℝ) * a ^ 2) := by
      have := mul_le_mul_of_nonneg_right hcmp1 (sq_nonneg a); linarith [this]
    have h2 : ((sigmaTop : ℝ))⁻¹ * b ^ 2 ≤ rho * (((sigmaLow : ℝ))⁻¹ * b ^ 2) := by
      have := mul_le_mul_of_nonneg_right hcmp2 (sq_nonneg b); linarith [this]
    rw [hA]
    rw [hta, htb] at hsplit
    linarith [hsplit, h1, h2]
  rw [hLHS]
  have hnn : (0 : ℝ) ≤ t * a + t⁻¹ * b := by positivity
  calc t * a + t⁻¹ * b = Real.sqrt ((t * a + t⁻¹ * b) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (2 * rho * annealedSqrtNormSq sigmaLow P) := Real.sqrt_le_sqrt hkey
    _ = Real.sqrt (2 * rho) * Real.sqrt (annealedSqrtNormSq sigmaLow P) :=
        Real.sqrt_mul (by positivity) _

/-- The load-leg identification at the closure's two gauges. -/
theorem blockVecNormSum_blockGaugeUp_le_gammaTenGaugeConst (M : ABKModel d)
    (n : ℤ) (h : ℕ)
    (hgauge : gaugeRatio (Annealed.sigmaBar M n) (Annealed.sigmaBar M (n + (h : ℤ) - 1)) ≤
      4 * (3 : ℝ) ^ (9 : ℕ))
    (P : BlockVec d) :
    blockVecNormSum (blockGaugeUp (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ) P) ≤
      gammaTenGaugeConst * Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M n) P) := by
  refine (blockVecNormSum_blockGaugeUp_le_gaugeRatio (Annealed.sigmaBar M n)
    (Annealed.sigmaBar M (n + (h : ℤ) - 1)) P).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  unfold gammaTenGaugeConst
  exact Real.sqrt_le_sqrt (by linarith [hgauge])

/-! ## The cell bound at the closure's own families -/

theorem meshFluctuationCellIntegrand_le_closureFold [NeZero d] (M : ABKModel d)
    (n : ℤ) (h K : ℕ)
    (hK10 : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (((K : ℤ)) : ℝ) - ((n + (h : ℤ) : ℤ) : ℝ))
    (hscale : ((originCube d (K : ℤ)).scale : ℤ) - ((closureMeshDepth M n h K : ℕ) : ℤ) =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ))
    (hcover : (((recurrenceGapMultiplier : ℕ) : ℝ) + 1) ^ 2 ≤ M.gamma⁻¹)
    (hshell : (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹)
    (hgauge : gaugeRatio (Annealed.sigmaBar M n) (Annealed.sigmaBar M (n + (h : ℤ) - 1)) ≤
      4 * (3 : ℝ) ^ (9 : ℕ))
    (e e' : Vec d) (omega : CutoffSample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (K : ℤ)) (closureMeshDepth M n h K))
    {Bg : ℝ} (hBg : 0 ≤ Bg)
    (hpos1 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N
      (fun x => (blockGaugeUp (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
        ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
          (closureDirichletAlong M n h K e omega.val)
          (closureNeumannAlong M n h K e' omega.val)).eval x)).1) ≤ Bg)
    (hpos2 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo R gammaTenBesovExponent N
      (fun x => (blockGaugeUp (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
        ((localizationFz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e' R
          (closureDirichletAlong M n h K e omega.val)
          (closureNeumannAlong M n h K e' omega.val)).eval x)).2) ≤ Bg) :
    meshFluctuationCellIntegrand M n h (K : ℤ) e e'
        (closureDirichletAlong M n h K e) (closureNeumannAlong M n h K e') R omega ≤
      gammaTenCrossConst d *
          (gaugedEllipticitySum (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
              (ancestorAtScale R (n + (h : ℤ))) M.gamma
              (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) *
            Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M n)
              (meshCellLoad M n h (K : ℤ) e e' (closureDirichletAlong M n h K e)
                (closureNeumannAlong M n h K e') R omega)) * Bg) +
        gammaTenQuadConst d *
          (gaugedEllipticitySum (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
              (ancestorAtScale R (n + (h : ℤ))) M.gamma
              (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) * Bg * Bg) := by
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgquarter : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hgs : M.gamma < gammaTenBesovExponent := by
    unfold gammaTenBesovExponent; linarith
  have hs1 : gammaTenBesovExponent < 1 := by unfold gammaTenBesovExponent; norm_num
  have hsig0 : (0 : ℝ) < (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ) :=
    (Annealed.sigmaBar M (n + (h : ℤ) - 1)).2
  have hsc : R.scale =
      recurrenceMesoScale recurrenceGapMultiplier M.gamma (n + (h : ℤ)) (h : ℤ) := by
    have := scale_eq_sub_of_mem_descendantsAtDepth hR
    rw [this]; exact hscale
  have hbase := meshFluctuationCellIntegrand_le_ancestor_fold_shape M n (K : ℤ) h hK10
    e e' (closureMeshDepth M n h K) hscale (closureDirichletAlong M n h K e)
    (closureNeumannAlong M n h K e') omega
    (isZeroTraceDirichletRhsWeakSolution_closureDirichletAlong M n h K e omega.val)
    (isMeanZeroNeumannRhsWeakSolution_closureNeumannAlong M n h K e' omega.val)
    hR hsc hcover hshell (s := gammaTenBesovExponent)
    (sig0 := (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)) hgs hs1 hsig0 hBg hpos1 hpos2
  refine hbase.trans ?_
  set gES : ℝ := gaugedEllipticitySum (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
    (ancestorAtScale R (n + (h : ℤ))) M.gamma
    (coefficientCutoffTriadicCoeffFamily M (n + (h : ℤ)) omega) with hgES
  set V : ℝ := blockVecNormSum (blockGaugeUp (Annealed.sigmaBar M (n + (h : ℤ) - 1) : ℝ)
    (principalPz (Annealed.sigmaBar M n) omega.val n (n + (h : ℤ)) e e' R
      (closureDirichletAlong M n h K e omega.val)
      (closureNeumannAlong M n h K e' omega.val))) with hV
  set G : ℝ := Real.sqrt (annealedSqrtNormSq (Annealed.sigmaBar M n)
    (meshCellLoad M n h (K : ℤ) e e' (closureDirichletAlong M n h K e)
      (closureNeumannAlong M n h K e') R omega)) with hG
  have hgES0 : 0 ≤ gES :=
    gaugedEllipticitySum_nonneg _ _ hsig0.le hgamma0
  have hVG : V ≤ gammaTenGaugeConst * G :=
    blockVecNormSum_blockGaugeUp_le_gammaTenGaugeConst M n h hgauge _
  have hkap : besovDualityConst R gammaTenBesovExponent = gammaTenDualityConst d := by
    rw [besovDualityConst_eq, gammaTenDualityConst]
  have hkap0 : (0 : ℝ) ≤ gammaTenDualityConst d := gammaTenDualityConst_nonneg d
  have hcc0 : (0 : ℝ) ≤ gammaTenCellFactor := gammaTenCellFactor_nonneg
  rw [hkap]
  have hcross : 2 * gammaTenDualityConst d * gammaTenCellFactor * (gES * V * Bg) ≤
      gammaTenCrossConst d * (gES * G * Bg) := by
    have hfac : (0 : ℝ) ≤ 2 * gammaTenDualityConst d * gammaTenCellFactor * (gES * Bg) := by
      have : (0 : ℝ) ≤ gES * Bg := mul_nonneg hgES0 hBg
      positivity
    have hstep : 2 * gammaTenDualityConst d * gammaTenCellFactor * (gES * Bg) * V ≤
        2 * gammaTenDualityConst d * gammaTenCellFactor * (gES * Bg) *
          (gammaTenGaugeConst * G) := mul_le_mul_of_nonneg_left hVG hfac
    unfold gammaTenCrossConst
    nlinarith [hstep]
  have hquad : gammaTenDualityConst d * gammaTenDualityConst d * gammaTenCellFactor *
      (gES * Bg * Bg) = gammaTenQuadConst d * (gES * Bg * Bg) := by
    unfold gammaTenQuadConst; ring
  have hgoal : 2 * gammaTenDualityConst d * gammaTenCellFactor * (gES * V * Bg) +
      gammaTenDualityConst d * gammaTenDualityConst d * gammaTenCellFactor *
        (gES * Bg * Bg) ≤
      gammaTenCrossConst d * (gES * G * Bg) + gammaTenQuadConst d * (gES * Bg * Bg) := by
    rw [hquad] at *
    linarith [hcross]
  exact hgoal

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
