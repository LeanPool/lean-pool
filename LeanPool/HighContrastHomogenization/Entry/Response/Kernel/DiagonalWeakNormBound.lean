/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AffineSobolevPullback
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.AdjointRecentHeadEstimate
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.CentredVarianceTailRoute
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalWeakNormAssembly
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.PrimalBranchSelector
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentredCarrierHypotheses

/-!
# High-contrast homogenization: Entry.Response.Kernel.DiagonalWeakNormBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The diagonal weak-norm primal bound (Lemma 2.16)

This file proves the two tail branches of the cell-average estimate for the recentred coefficient
`a_- = a - g`: it bounds the normalized scale-average seminorm of the recentred,
metric-transported subcell averages of the doubled optimizer field, in two branches according to
the size of the all-scale maximum `M`. It then states and proves the diagonal weak-norm primal
bound itself, `diagonalWeakNorm_primal_le` - HC bridge II, paper `p.response.transfer`,
Lemma 2.16 - assembled from the recent head estimate and the older-scale tail bound.
-/

section
/-!
## The two tail branches of the cell-average estimate at the carriers

The cell-average estimate `e.response.weak.estimate` bounds the normalized scale-average seminorm
of the recentred, metric-transported subcell averages of the doubled optimizer field of the parent
adapted cell, `3 ^ (-(t / 2)) * besovSeminorm t`, in two branches according to the size of the
all-scale maximum `M = respAllScaleMax P γ jStar F t a`.  Every input of the older-scale branch is
already proved at the estimate's own carriers: the per-cell bound `tailCell_of_bridge`, the
per-scale assembly `scaleTail_carrier`, the summability `summable_centred`, and the
integrability and nonnegativity inputs.  This module composes them once with the abstract branch
splitting `primal_branches`.

The per-scale family is
`avg n w = M_0^{1/2} · ((X)_{z + U_{t-n}} − (X)_{U_t})`, the transported recentring of the parent
optimizer field `X = (∇v, b ∇v)`.  On `1 < M` the whole series is absorbed by the older-scale
term; on `M ≤ 1` only the scales beyond a window `H` are absorbed and the first `H + 1` scales
remain as an explicit head sum.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The two older-scale branches of the cell-average estimate at the carriers.**  For an
invertible selected grid, a generation `t`, a parent harmonic optimizer attached to the recentred
response coefficient, and the pointwise elliptic data of the parent and normalized blocks, the
normalized seminorm of the recentred transported optimizer field obeys the bad-branch bound
`16 / (1 - Quenched.contrastRho γ) · K · √M · ℰ` when `1 < M` and the good-branch bound
`∑_{n ≤ H} 3 ^ (-(n / 2)) S n + 16 / (1 - Quenched.contrastRho γ) · K · 3 ^
(-(Quenched.contrastAlpha γ H)) · ℰ` when
`M ≤ 1`, where `K = √(‖(Ehat_t^-)_+‖)`, `ℰ` is the weak optimizer energy, and `S n` is the
depth-`n` scale average. -/
theorem tailBranches_minus (P : Measure (CoeffSpace d)) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    (1 < respAllScaleMax P γ jStar F t a →
        (3 : ℝ) ^ (-((t : ℝ) / 2)) *
            besovSeminorm t (fun n w =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverageFamily (respGrid jStar F) t
                    (optimizerField (respCoeffMinus F a) u) n w -
                  cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
          ≤ 16 / (1 - Quenched.contrastRho γ) *
              Real.sqrt
                (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
              Real.sqrt (respAllScaleMax P γ jStar F t a) *
              weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u) ∧
    (respAllScaleMax P γ jStar F t a ≤ 1 →
        (3 : ℝ) ^ (-((t : ℝ) / 2)) *
            besovSeminorm t (fun n w =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverageFamily (respGrid jStar F) t
                    (optimizerField (respCoeffMinus F a) u) n w -
                  cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
          ≤ (∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) *
                Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                  ∑ w ∈ triadicIndexBox d n,
                    blockVecDot
                      (blockMatVecMul (blockSqrt (respM0 F))
                        (cellAverageFamily (respGrid jStar F) t
                            (optimizerField (respCoeffMinus F a) u) n w -
                          cellAverage (respCell jStar F t)
                            (optimizerField (respCoeffMinus F a) u)))
                      (blockMatVecMul (blockSqrt (respM0 F))
                        (cellAverageFamily (respGrid jStar F) t
                            (optimizerField (respCoeffMinus F a) u) n w -
                          cellAverage (respCell jStar F t)
                            (optimizerField (respCoeffMinus F a) u)))))
            + 16 / (1 - Quenched.contrastRho γ) *
                Real.sqrt
                  (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
                (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) *
                weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u) := by
  classical
  obtain ⟨hmem1, hmem2⟩ :=
    memVectorL2_optimizerField_respCoeffMinus_cell (respGrid jStar F) hgrid t F a u
  have hK : 0 ≤ Real.sqrt
      (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) :=
    Real.sqrt_nonneg _
  have hEn : 0 ≤ weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u :=
    Real.sqrt_nonneg _
  have hM : 0 ≤ respAllScaleMax P γ jStar F t a := by
    have hSpecBound_nonneg : ∀ Hb : BlockMat d, 0 ≤ blockSpecBound Hb :=
      fun Hb => Real.sInf_nonneg fun _ hx => hx.1
    refine Real.sSup_nonneg ?_
    rintro y ⟨n, z, _hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hSpecBound_nonneg _)
  have hsum := summable_centred (respGrid jStar F) hgrid t (blockSqrt (respM0 F))
    (optimizerField (respCoeffMinus F a) u) hmem1 hmem2
  have hscale : ∀ n : ℕ,
      Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u := by
    intro n
    have hcell := tailCell_of_bridge P γ jStar F t hgrid a n u hm hEmean hEhat hM0 hbdd
    have h1 : ∀ j : Fin d, IntegrableOn
        (fun x => (optimizerField (respCoeffMinus F a) u x).1 j) (respCell jStar F t) :=
      fun j => (integrableOn_optimizerField_respCoeffMinus_cell
        (respGrid jStar F) hgrid t F a u j).1
    have h2 : ∀ j : Fin d, IntegrableOn
        (fun x => (optimizerField (respCoeffMinus F a) u x).2 j) (respCell jStar F t) :=
      fun j => (integrableOn_optimizerField_respCoeffMinus_cell
        (respGrid jStar F) hgrid t F a u j).2
    have hnn := energyDensity_average_nonneg (respGrid jStar F) hgrid t F a u
    have hintE := integrableOn_energyDensity_respCoeffMinus (respGrid jStar F) hgrid t F a u
    exact scaleTail_carrier P γ jStar F t hgrid a n u hcell h1 h2 hnn hintE
  exact primal_branches hγ t H
    (fun n w => blockMatVecMul (blockSqrt (respM0 F))
      (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
        cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
    hK hEn hM hsum hscale

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## HC bridge II: the diagonal weak-norm primal bound (Lemma 2.16)

The scale-average seminorm and the positive-definiteness facts the bound rests on are developed
in `ScaleAverageSeminorm.lean`; the supporting defect, energy-map and head estimates are in
`DiagonalDefectCarriers.lean`, `RecentEnergyMapSupport.lean` and `RecentHeadDefectHalves.lean`.
Paper `p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockSub coarseBlock
  normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## AK.HC Lemma 2.16 on the selected grid, pathwise (the weak-norm kernel).
The carriers of the weak-norm kernel are the defect carriers and closed helpers of
`DiagonalDefectCarriers.lean`.  Paper `p.response.transfer`.

The right-hand side below is the explicit printed bound: the finite recent-scale defect sums
`16 * K * L * (weakCellSum + weakAverageSum)` together with the older-scale energy term
`16 / (1 - rho) * K * (if 1 < M then sqrt M else 3 ^ (-(alpha * H))) * E`, where
`K = sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))`,
`L = sqrt (respLsqMinus P jStar F t e)`, `E = weakOptimizerEnergy (respCell jStar F t)
(respCoeffMinus F a) u` and `M = respAllScaleMax P γ jStar F t a`.  The constants are explicit,
and the bound carries the two finite sums rather than a single unspecified universal constant.

SPECIALIZATION.  The general `(rho, s, delta)` bound is specialised here to AK.HC Lemma 2.16
"with exponent 1/2, decay exponent rho, cutoff delta = 1, and window H"
(`p.response.transfer`), i.e. `s = 1/2`, `rho = Quenched.contrastRho γ = (1+γ)/2`, `delta = 1`.
The side conditions under `_hγ : γ ∈ Set.Ico 0 1` hold:
* `0 < rho`   : `rho = (1+γ)/2 ≥ 1/2 > 0`                              ✓
* `rho < 2`   : `γ < 1` gives `rho < 1 < 2`                            ✓
* `rho/2 < s` : `(1+γ)/4 < 1/2 ⇔ γ < 1`                                ✓ (it is exactly `γ < 1`)
* `s ≤ 1`     : `1/2 ≤ 1`                                              ✓
* `0 < delta`, `delta ≤ 1` : `delta = 1`                               ✓
Two consequent simplifications are performed in the printed constants:
`(Real.sqrt delta)⁻¹ = (Real.sqrt 1)⁻¹ = 1`, and `2*s - rho = 1 - Quenched.contrastRho γ` (`=
(1-γ)/2
= 2 * Quenched.contrastAlpha γ > 0`).  Also `s - rho/2 = 1/2 - (1+γ)/4 = (1-γ)/4 =
Quenched.contrastAlpha γ`, which is why
the tail weight is printed as `3^{-(Quenched.contrastAlpha γ * H)}`.

CARRIER MAP (paper ↦ current):
* `adaptedWeakSeminorm q t (1/2) F ↦ besovSeminorm t (cellAverageFamily q t F)` — real-valued;
  the statement is therefore an inequality in `ℝ`, not in `ℝ≥0∞`, and the outer
  `ENNReal.ofReal` on both sides disappears.
* `diagonalWeakMaximum rho q t E a ↦ respAllScaleMax P γ jStar F t a`
(`ResponseBlockObjects.lean`) —
  REAL-valued, so the `if … = ⊤ then ⊤ else …` case distinction is unnecessary: there is no `⊤`
  branch to state, and `respAllScaleMax …` is the real cutoff value.
* `diagonalWeakMetricFactor m E ↦ Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P
  jStar F t) (respM0 F)))` — the `K₀` of `p.response.transfer`.  The paper's `(S, m)` binders
  (`S*S = m`, `S` symmetric) are absorbed into `respM0 F` and `blockSqrt`, so no `S`/`m` binders
  are added.
* `diagonalWeakLoadMinus E p r ↦ Real.sqrt (respLsqMinus P jStar F t e)`
(`ResponseBlockObjects.lean`) —
  the loads `(p, r)` are the response coordinates of `e`, so no `p r` binders are added.
* `diagonalWeakCellDefect q (t-n) t ↦ weakCellDefect q t n`, `diagonalWeakAverageDefect ↦
  weakAverageDefect`, `diagonalWeakCellSum ↦ weakCellSum`, `diagonalWeakAverageSum ↦
  weakAverageSum`, `diagonalWeakEnergy ↦ weakOptimizerEnergy` — the five carriers above
  (`blockSize ↦ blockSpecBound ∘ normalizedBlock`, `avsum` spelled out, `variationEnergyValue`
  on `optimizerField`).
* `diagonalWeakState hq t a p r - blockCellAverage (adaptedCell q t) … ↦` the LEFT-hand side
  (`cellAverageFamily … - cellAverage (respCell jStar F t) …`).
The right-hand side carries the explicit constants `16` and `16 * (√delta)⁻¹ / (2s - rho)`,
printed here. -/

/-- AK.HC Lemma 2.16 on the selected grid, pathwise: the scale-average seminorm of
the recentred doubled optimizer state is bounded by the two finite recent-scale sums plus the
older-scale energy term, at `s = 1/2`, `rho = Quenched.contrastRho γ` and `delta = 1`; see the
section docstring for the carrier map.

The binder `hgrid : IsUnit (respGrid jStar F)` supplies the invertibility that
`cellAverage_optimizerField_eq_blockResponseMean` needs, and the two defect sums take the
recentred field `respCoeffMinus F a` so that numerator and denominator are congruenced alike; the
two defect carriers use the two-sided norm, the one-sided version being false (see their
docstrings). -/
theorem diagonalWeakNorm_primal_le (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t))
    (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        besovSeminorm t (fun n w =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))) ≤
      16 * Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          Real.sqrt (respLsqMinus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
              (respCoeffMinus F a) +
            weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatMinus P jStar F t)
              (respCoeffMinus F a)) +
        (16 / (1 - Quenched.contrastRho γ) *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))) *
          (if 1 < respAllScaleMax P γ jStar F t a then
              Real.sqrt (respAllScaleMax P γ jStar F t a)
            else
              (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ)))) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u := by
  classical
  have hrho : Quenched.contrastRho γ < 1 := by
    have := _hγ.2
    rw [Quenched.contrastRho]
    linarith only [this]
  have hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
    respEhatMinus_posDef_of_integrable hgrid t hint
  have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
    respM0_posDef_of_isUnit_respGrid hgrid
  have hm : (explicitCanonicalMetric F).PosDef :=
    explicitCanonicalMetric_posDef_of_isUnit_respGrid hgrid
  have hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    respMean_posDef_of_integrable hgrid t hint
  obtain ⟨hbad, hgood⟩ :=
    tailBranches_minus P γ _hγ jStar H F t hgrid a u hm hEmean hE hM0 hbdd
  set K : ℝ :=
    Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) with hKdef
  set L : ℝ := Real.sqrt (respLsqMinus P jStar F t e) with hLdef
  set Ene : ℝ := weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u with hEnedef
  set Sums : ℝ := 16 * K * L *
    (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t) (respCoeffMinus F a) +
      weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatMinus P jStar F t)
        (respCoeffMinus F a)) with hSumsdef
  set c : ℝ := 16 / (1 - Quenched.contrastRho γ) * K with hcdef
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hEne0 : 0 ≤ Ene := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - Quenched.contrastRho γ := by linarith only [hrho]
    rw [hcdef]
    positivity
  have hSums0 : 0 ≤ Sums := by
    have h1 : 0 ≤ weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
        (respCoeffMinus F a) := weakCellSum_nonneg _ _ _ _ _
    have h2 : 0 ≤ weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ)
        (respEhatMinus P jStar F t) (respCoeffMinus F a) := weakAverageSum_nonneg _ _ _ _ _ _
    rw [hSumsdef]
    have : 0 ≤ 16 * K * L := by positivity
    exact mul_nonneg this (by linarith only [h1, h2])
  have hMnn : 0 ≤ respAllScaleMax P γ jStar F t a := by
    have hSpecBound_nonneg : ∀ Hb : BlockMat d, 0 ≤ blockSpecBound Hb :=
      fun _ => Real.sInf_nonneg fun _ hx => hx.1
    refine Real.sSup_nonneg ?_
    rintro y ⟨m, z, _hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hSpecBound_nonneg _)
  have hgood' : respAllScaleMax P γ jStar F t a ≤ 1 →
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n w =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
        ≤ Sums + c * (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) * Ene := by
    intro hMle
    have hhead := recentHead_carrier_minus P γ _hγ jStar H F t e hgrid hint a hbdd u hu hMle
    have hhead' : (∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverageFamily (respGrid jStar F) t
                      (optimizerField (respCoeffMinus F a) u) n w -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffMinus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverageFamily (respGrid jStar F) t
                      (optimizerField (respCoeffMinus F a) u) n w -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffMinus F a) u))))) ≤ Sums := hhead
    have := hgood hMle
    linarith only [this, hhead']
  have hbad' : 1 < respAllScaleMax P γ jStar F t a →
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n w =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
        ≤ c * Real.sqrt (respAllScaleMax P γ jStar F t a) * Ene := by
    intro hMgt
    have := hbad hMgt
    linarith only [this]
  have hkey := head_le_add_max_mul_ite _hγ H hMnn
    ((3 : ℝ) ^ (-((t : ℝ) / 2)) *
      besovSeminorm t (fun n w =>
        blockMatVecMul (blockSqrt (respM0 F))
          (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
            cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
    Sums Ene c c hc0 hc0 hSums0 hEne0 hgood' hbad'
  rwa [max_self] at hkey
end

end HCPolySupport.HighContrast.Multiscale
end
