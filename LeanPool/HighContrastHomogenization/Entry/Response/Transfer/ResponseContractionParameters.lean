/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedMeanDrift
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseImbalanceComparison

/-!
# High-contrast homogenization: Entry.Response.Transfer.ResponseContractionParameters

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Closing the multiscale contraction

The source load bound `L_s^± ≤ C κ_s^{3/2}` of `p.response.transfer` is proved by removing the
translation dependence through integer stationarity, bounding the weighted sum of the coarse-block
norms by a constant multiple of the finest one via the determinant-drift telescope, and treating
the scales below the selection threshold with the source estimate and the smallness hypothesis on
the source term. Turning the resulting one-step inequality `κ_t - 1 ≤ ω κ_t` into the target bound
`κ_t ≤ 1 + δ_ad` is pure real arithmetic, valid once `ω ≤ δ_ad/(1+δ_ad)`. The parameter choice
closes the argument by fixing, in order, a scale `H` large enough that `3^{-H}` and `3^{-αH}` are
small, a tolerance `η` small enough that the resulting quadratic term is small, and a base scale
`σ₀` small enough that the eccentricity `r` stays close to `1`, so that the printed contraction
constant `ω` obeys the bound the arithmetic step needs.
-/

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}
/-! ## The source load bound -/

private def responseSourceLoadCoefficient (γ κ Cc Csc A : ℝ) (N n : ℕ) : ℝ :=
  if n ≤ N then 3 / 2 * ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n * (Cc * Real.sqrt κ)
  else Csc * A * ((3 : ℝ) ^ γ) ^ (n - N) * (Cc * Real.sqrt κ)

/-- The two geometric regimes for the source load have a summable weighted majorant.
The coefficient in the coarse regime is controlled by the source smallness at the crossover. -/
private theorem responseSourceLoadGeometricSum (γ κ Cc Cs Cl Csc A : ℝ) (N : ℕ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (hκ : 0 ≤ κ) (hCc : 0 < Cc) (hCs : 0 < Cs)
    (hCl : 0 ≤ Cl) (hCsc : 0 ≤ Csc) (hA : 0 ≤ A)
    (hsmall : A * ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ N ≤ Cs⁻¹) :
    Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      (4 * (responseSourceLoadCoefficient γ κ Cc Csc A N n * (Cl * κ)))) ∧
      ∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        (4 * (responseSourceLoadCoefficient γ κ Cc Csc A N n * (Cl * κ))) ≤
        Cc * Cl * (6 * (1 - (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2))⁻¹ +
          4 * Csc * Cs⁻¹ * (1 - (3 : ℝ) ^ (γ - 3 / 2))⁻¹) * Real.sqrt κ ^ 3 := by
  have hrho0 : (0 : ℝ) ≤ Quenched.contrastRho γ := by
    have : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    rw [this]; linarith only [hγ.1]
  have hr1lt : (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    have : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    rw [this]; linarith only [hγ.2]
  have hr2lt : (3 : ℝ) ^ (γ - 3 / 2) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    linarith only [hγ.2]
  have hr1pos : (0 : ℝ) < (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr2pos : (0 : ℝ) < (3 : ℝ) ^ (γ - 3 / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hden1 : (0 : ℝ) < 1 - (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2) := by
    linarith only [hr1lt]
  have hden2 : (0 : ℝ) < 1 - (3 : ℝ) ^ (γ - 3 / 2) := by linarith only [hr2lt]
  have hi1 : (0 : ℝ) < (1 - (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2))⁻¹ := inv_pos.mpr hden1
  have hi2 : (0 : ℝ) < (1 - (3 : ℝ) ^ (γ - 3 / 2))⁻¹ := inv_pos.mpr hden2
  have hCsinv : (0 : ℝ) < Cs⁻¹ := inv_pos.mpr hCs
  set Msc : ℝ := Cl * κ
  have hMsc0 : (0 : ℝ) ≤ Msc := mul_nonneg hCl hκ
  set u : ℕ → ℝ := fun n => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
    (4 * (responseSourceLoadCoefficient γ κ Cc Csc A N n * Msc))
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (by norm_num) (mul_nonneg (by
        unfold responseSourceLoadCoefficient
        split_ifs <;> positivity) hMsc0))
  have hmulpow : ∀ n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) =
      ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ n := weight_eq
  have hr1eq : ((3 : ℝ) ^ (-((3 : ℝ) / 2))) * ((3 : ℝ) ^ Quenched.contrastRho γ) =
      (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have hr2eq : ((3 : ℝ) ^ (-((3 : ℝ) / 2))) * ((3 : ℝ) ^ γ) =
      (3 : ℝ) ^ (γ - 3 / 2) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  have hreg1 : ∀ n : ℕ, n ≤ N →
      u n ≤ (6 * (Cc * Real.sqrt κ) * Msc) *
        ((3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2)) ^ n := by
    intro n hn
    have : u n = (6 * (Cc * Real.sqrt κ) * Msc) *
        (((3 : ℝ) ^ (-((3 : ℝ) / 2))) * ((3 : ℝ) ^ Quenched.contrastRho γ)) ^ n := by
      simp [u, responseSourceLoadCoefficient, hn, hmulpow n]
      ring
    rw [this, hr1eq]
  have hreg2 : ∀ n : ℕ, N < n →
      u n ≤ (4 * Csc * Cs⁻¹ * (Cc * Real.sqrt κ) * Msc) *
        ((3 : ℝ) ^ (γ - 3 / 2)) ^ (n - N) := by
    intro n hn
    have hpowsplit : ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ n =
        ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ N *
          ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ (n - N) := by
      rw [← pow_add]
      congr 1
      omega
    have hue : u n = (4 * Csc * (Cc * Real.sqrt κ) * Msc) *
        (A * ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ N) *
          (((3 : ℝ) ^ (-((3 : ℝ) / 2))) * ((3 : ℝ) ^ γ)) ^ (n - N) := by
      simp [u, responseSourceLoadCoefficient, hn, mul_pow, hmulpow n, hpowsplit]
      ring
    rw [hue, hr2eq]
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (pow_pos hr2pos _))
    have hrhs : 4 * Csc * Cs⁻¹ * (Cc * Real.sqrt κ) * Msc =
        (4 * Csc * (Cc * Real.sqrt κ) * Msc) * Cs⁻¹ := by ring
    rw [hrhs]
    refine mul_le_mul_of_nonneg_left hsmall ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCsc)
      (mul_nonneg hCc.le (Real.sqrt_nonneg _))) hMsc0
  have ha0 : (0 : ℝ) ≤ 6 * (Cc * Real.sqrt κ) * Msc :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hCc.le (Real.sqrt_nonneg _))) hMsc0
  have hb0 : (0 : ℝ) ≤ 4 * Csc * Cs⁻¹ * (Cc * Real.sqrt κ) * Msc :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCsc) hCsinv.le)
      (mul_nonneg hCc.le (Real.sqrt_nonneg _))) hMsc0
  obtain ⟨husum, hubound⟩ := tsum_two_regime (u := u) (N := N)
    (a := 6 * (Cc * Real.sqrt κ) * Msc)
    (b := 4 * Csc * Cs⁻¹ * (Cc * Real.sqrt κ) * Msc)
    (r₁ := (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2)) (r₂ := (3 : ℝ) ^ (γ - 3 / 2))
    hu0 ha0 hb0 hr1pos.le hr1lt hr2pos hr2lt hreg1 hreg2
  refine ⟨husum, le_trans hubound (le_of_eq ?_)⟩
  have hcube : Real.sqrt κ ^ 3 = κ * Real.sqrt κ := by
    rw [pow_succ, Real.sq_sqrt hκ]
  rw [Msc, hcube]
  ring

private theorem responseSourceBoundConstantPos (γ Cc Cs Cl Csc : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (hCc : 0 < Cc) (hCs : 0 < Cs)
    (hCl : 0 < Cl) (hCsc : 0 < Csc) :
    0 < Cc * Cl * (6 * (1 - (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2))⁻¹ +
      4 * Csc * Cs⁻¹ * (1 - (3 : ℝ) ^ (γ - 3 / 2))⁻¹) := by
  have hr1lt : (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    have : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    rw [this]; linarith only [hγ.2]
  have hr2lt : (3 : ℝ) ^ (γ - 3 / 2) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    linarith only [hγ.2]
  have hi1 : (0 : ℝ) < (1 - (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2))⁻¹ :=
    inv_pos.mpr (by linarith only [hr1lt])
  have hi2 : (0 : ℝ) < (1 - (3 : ℝ) ^ (γ - 3 / 2))⁻¹ :=
    inv_pos.mpr (by linarith only [hr2lt])
  have hCsinv : (0 : ℝ) < Cs⁻¹ := inv_pos.mpr hCs
  have hp1 : (0 : ℝ) < 6 * (1 - (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2))⁻¹ := by
    linarith only [hi1]
  have hp2 : (0 : ℝ) < 4 * Csc * Cs⁻¹ * (1 - (3 : ℝ) ^ (γ - 3 / 2))⁻¹ :=
    mul_pos (mul_pos (by linarith only [hCsc] : (0 : ℝ) < 4 * Csc) hCsinv) hi2
  exact mul_pos (mul_pos hCc hCl) (add_pos hp1 hp2)

private theorem responseSourceThreshold
    {d : ℕ} {γ : ℝ} {S : SelectionData} {ε σ Cglob Cprof Csrc0 : ℝ} {H : ℕ}
    {Bresp : ℝ} {P : Measure (CoeffSpace d)} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {Kg : ℝ} {Src : CoeffSpace d → ℝ} {B : ℝ} {jStar : ℕ} {F : BlockMat d} {s t : ℤ}
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc0 H Bresp P E Ψ Kg Src B jStar F s t)
    (hCglob : 0 ≤ Cglob) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) :
    ⌈Csrc0 * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) := by
  have hB1 : (1 : ℝ) ≤ B :=
    le_trans (S.one_le_B0 ε σ hε hσ) (le_trans (le_max_left _ _) raw.hB)
  have hPi := Annealed.aspectRatio_pos_and_three_le raw.ell
  have hlogPi : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    refine (Real.le_logb_iff_rpow_le (by norm_num) (by linarith only [hPi.2])).mpr ?_
    rw [Real.rpow_one]; linarith only [hPi.2]
  have h0 : (0 : ℝ) ≤ Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E) :=
    mul_nonneg (mul_nonneg hCglob (by linarith only [hB1])) (by linarith only [hlogPi])
  refine le_trans (Int.ceil_le_ceil ?_) raw.hsrc
  linarith only [h0]

private theorem responseSourceDistance (jStar : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s) :
    ∃ N : ℕ, (N : ℤ) = s - (jStar : ℤ) ∧
      (N : ℝ) = (s : ℝ) - (jStar : ℝ) := by
  let N := (s - (jStar : ℤ)).toNat
  have hNZ : (N : ℤ) = s - (jStar : ℤ) := Int.toNat_of_nonneg (by omega)
  refine ⟨N, hNZ, ?_⟩
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hNZ

private theorem responseProfileControlsSourceDrift
    {d : ℕ} {γ : ℝ} {S : SelectionData} {ε σ Cglob Cprof Csrc : ℝ} {H : ℕ}
    {Bresp : ℝ} {P : Measure (CoeffSpace d)} {E : BlockMat d} {Ψ : ℝ → ℝ}
    {Kg : ℝ} {Src : CoeffSpace d → ℝ} {B : ℝ} {jStar : ℕ} {F : BlockMat d} {s t : ℤ}
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (hd : 2 ≤ d) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (hjs : (jStar : ℤ) ≤ s)
    (η Cprof σ : ℝ) (hprof : Cprof * σ ^ ((1 - γ) / 8) ≤ η) :
    determinantDrift P γ (respGrid jStar F) jStar s ≤ η := by
  have hDt0 : 0 ≤ determinantDrift P γ (respGrid jStar F) jStar t :=
    determinantDrift_nonneg d hd γ E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F)
      (Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos) t
  have hpr0 : 0 ≤ profile P γ (respGrid jStar F) jStar s s :=
    profile_nonneg d hd γ hγ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F)
      (Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos) s s hjs le_rfl
  have hmax : profile P γ (respGrid jStar F) jStar s s ≤
      max (max (profile P γ (respGrid jStar F) jStar s s)
        (profile P γ (respGrid jStar F) jStar s t))
        (profile P γ (respGrid jStar F) jStar t t) :=
    le_max_of_le_left (le_max_left _ _)
  have hraw : max
      (max (profile P γ (respGrid jStar F) jStar s s)
        (profile P γ (respGrid jStar F) jStar s t))
      (profile P γ (respGrid jStar F) jStar t t) +
      determinantDrift P γ (respGrid jStar F) jStar s +
      determinantDrift P γ (respGrid jStar F) jStar t ≤
      Cprof * σ ^ ((1 - γ) / 8) := raw.prof
  linarith only [hmax, hpr0, hDt0, hraw, hprof]

private theorem responseSourceCoefficientIdentities (d : ℕ) (γ : ℝ) (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d))
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ)
    (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (hqU : IsUnit (respGrid jStar F)) (hFfull : (toFullBlockMat F).PosDef)
    (hmF : (explicitCanonicalMetric F).PosDef)
    (hint : ∀ (k : ℤ) (y : Vec d),
      HasIntegrableCoarseBlock P (HighContrast.adaptedCellTranslate (respGrid jStar F) k y)) :
    ∃ Gplus : BlockMat d,
      (∀ (k : ℤ) (z : Fin d → ℤ),
        annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffMinus F) =
          blockCongr (respG F) (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z))) ∧
      (∀ (k : ℤ) (z : Fin d → ℤ),
        annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffPlus F) =
          blockCongr Gplus (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z))) := by
  have hbMinus : ∀ (k : ℤ) (z : Fin d → ℤ),
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffMinus F) =
        blockCongr (respG F) (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z)) :=
    fun k z => annealedBlockOf_respCoeffMinus_adapted (respGrid jStar F) hqU k
      (adaptedCellCenter (respGrid jStar F) k z) F hFfull (hint k _)
  let Gplus : BlockMat d :=
    ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d))
  have hbPlus : ∀ (k : ℤ) (z : Fin d → ℤ),
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffPlus F) =
        blockCongr Gplus (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z)) := by
    intro k z
    have h : annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffPlus F) =
        blockAdjoint (blockCongr (respG F)
          (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z))) :=
      annealedBlockOf_respCoeffPlus_adapted (respGrid jStar F) hqU k
        (adaptedCellCenter (respGrid jStar F) k z) F hFfull (hint k _)
    rw [h, blockAdjoint, blockCongr_blockCongr]
    rfl
  exact ⟨Gplus, hbMinus, hbPlus⟩

/-- **The source load bound** `response_source_load_bound` (`p.response.transfer`):
`L_s^± <= C kappa_s^{3/2}`.

Route: for `k >= j_*` integer stationarity removes `z`
(`Annealed.annealedBlock_adaptedCellAtCenter`), and the weighted sum of the `E_k` is bounded by
`C(1 + D_{q,j_*}(s))E_s` -- telescope the mean increments of `determinantDrift` and use
`3/2 > (1-gamma)/8`.  For `k < j_*` the source estimate and the **second** inequality of
`e.response.source.smallness` bound the rest by `C E_s`.  Apply the resulting matrix bounds to
the two coordinate projections of `Y^±` and finish with `response_calibrated_blocks`
and `response_load_and_mean`; the series converges
because `gamma < 3/2`.

Premises `_hε`, `_hσ`: without them `1 ≤ B` and `jStar ≤ s` are unavailable.  The binder
*names* are underscore-prefixed because they do not occur in the statement's own type; the
proof uses them. -/
theorem response_source_load_bound (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ)
    (Cc Cs Cl : ℝ) (_hCc : 0 < Cc) (_hCs : 0 < Cs) (_hCl : 0 < Cl) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ : ℝ) (_hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (_hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
        (Cglob Cprof Bresp : ℝ) (_hCglob : 0 ≤ Cglob) (H : ℕ) (P : Measure (CoeffSpace d))
        (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ)
        (F : BlockMat d) (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
          Cprof * σ ^ ((1 - γ) / 8) ≤ η →
          RespSourceSmall d γ Cs η E F jStar s t →
          ∀ e : Vec d, vecDot e e = 1 →
            RespLoadMean Cl P jStar F s t e → RespLoadBound C P jStar F s t e := by
  obtain ⟨Csrc0, Csc, hCsrc0, hCsc, hcell⟩ := annealedBlock_le_adaptedMean d _hd γ _hγ
  have hrho0 : (0 : ℝ) ≤ Quenched.contrastRho γ := by
    have : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    rw [this]; linarith only [_hγ.1]
  have hboundPos := responseSourceBoundConstantPos γ Cc Cs Cl Csc _hγ _hCc _hCs _hCl hCsc
  refine ⟨Csrc0, hCsrc0,
    Cc * Cl * (6 * (1 - (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2))⁻¹ +
      4 * Csc * Cs⁻¹ * (1 - (3 : ℝ) ^ (γ - 3 / 2))⁻¹), hboundPos, ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw hcal η hη hprof
    hsmall e he hload
  have := raw.prob
  let : NeZero d := ⟨by omega⟩
  have hmF : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    raw.symm raw.pos
  have hFfull : (toFullBlockMat F).PosDef :=
    posDef_toFullBlockMat raw.symm raw.pos
  have hM0pd : Book.Ch02.BlockPosDef (respM0 F) := respM0_blockPosDef_of_canonicalMetric_posDef hmF
  have hM0full : (toFullBlockMat (respM0 F)).PosDef :=
    posDef_toFullBlockMat (respM0_isSymm_of_canonicalMetric_posDef hmF) hM0pd
  have hqU : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hmF
  have hjs : (jStar : ℤ) ≤ s :=
    le_of_lt (jStar_lt_s_of_raw d _hd γ _hγ S ε σ Cglob Cprof Csrc0 Bresp hε hσ H P E Ψ Kg
      Src B jStar F s t raw)
  have hwin : HighContrast.adaptedCell (respGrid jStar F) s ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)) :=
    subset_trans (adaptedCell_subset (respGrid jStar F) (le_of_lt raw.hst)) raw.cube
  have hPi := Annealed.aspectRatio_pos_and_three_le raw.ell
  have hKg : (1 : ℝ) < Kg := raw.ell.one_lt_growthWitness
  have hlogK : (0 : ℝ) ≤ Real.logb 3 (2 * Kg) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hKg])
  have hthr := responseSourceThreshold raw hCglob hε hσ
  have hD := responseProfileControlsSourceDrift raw _hd _hγ hjs η Cprof σ hprof
  set κ : ℝ := respKappa P jStar F s with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    unfold respKappa canonicalImbalance blockOpNorm
    exact norm_nonneg _
  have hsqκ : (0 : ℝ) ≤ Real.sqrt κ := Real.sqrt_nonneg _
  obtain ⟨N, hNZ, hNR⟩ := responseSourceDistance jStar s hjs
  set A : ℝ := aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖)
  have hA0 : 0 ≤ A := mul_nonneg (le_of_lt hPi.1) (by positivity)
  have h3rho : (1 : ℝ) ≤ (3 : ℝ) ^ Quenched.contrastRho γ := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hrho0
  have hkey : ∀ (G' : BlockMat d) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d),
      (∀ (k : ℤ) (z : Fin d → ℤ),
          annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) b
            = blockCongr G' (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z))) →
      BlockMatLoewnerLE (blockCongr G' (adaptedMean P (respGrid jStar F) s))
        (blockScale (Cc * Real.sqrt κ) (respM0 F)) →
      blockVecDot Y (blockMatVecMul (respM0 F) Y) ≤ Cl * κ →
      Summable (respSourceLoadSummand P jStar F s b Y) ∧
        respSourceLoad P jStar F s b Y ≤
          Cc * Cl * (6 * (1 - (3 : ℝ) ^ (Quenched.contrastRho γ - 3 / 2))⁻¹ +
            4 * Csc * Cs⁻¹ * (1 - (3 : ℝ) ^ (γ - 3 / 2))⁻¹) * Real.sqrt κ ^ 3 := by
    intro G' b Y hb hEs hY
    set cfun : ℕ → ℝ := fun n => responseSourceLoadCoefficient γ κ Cc Csc A N n with hcfun
    have hpow1 : ∀ n : ℕ, (0 : ℝ) ≤ ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n := fun n =>
      le_of_lt (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) n)
    have hpow2 : ∀ k : ℕ, (0 : ℝ) ≤ ((3 : ℝ) ^ γ) ^ k := fun k =>
      le_of_lt (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) k)
    have hcfun0 : ∀ n, 0 ≤ cfun n := by
      intro n
      by_cases h : n ≤ N
      · simp only [hcfun, responseSourceLoadCoefficient, h, ite_true]
        exact mul_nonneg (mul_nonneg (by norm_num) (hpow1 n)) (mul_nonneg _hCc.le hsqκ)
      · simp only [hcfun, responseSourceLoadCoefficient, h, ite_false]
        exact mul_nonneg (mul_nonneg (mul_nonneg hCsc.le hA0) (hpow2 (n - N)))
          (mul_nonneg _hCc.le hsqκ)
    -- the per-cell Loewner bound, in both regimes
    have hcellb : ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
        BlockMatLoewnerLE
          (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b)
          (blockScale (cfun n) (respM0 F)) := by
      intro n z _
      rw [hb]
      rcases le_or_gt n N with hn | hn
      · have hnZ : ((n : ℕ) : ℤ) ≤ ((N : ℕ) : ℤ) := by exact_mod_cast hn
        have hk : (jStar : ℤ) ≤ s - (n : ℤ) := by omega
        have h1 : annealedBlock P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
            = adaptedMean P (respGrid jStar F) (s - (n : ℤ)) :=
          Annealed.annealedBlock_adaptedCellAtCenter P raw.stat jStar raw.hj
            (explicitCanonicalMetric F)
            hmF (s - (n : ℤ)) hk z
        rw [h1]
        have h2 := adaptedMean_le_of_drift d _hd γ _hγ P E Ψ Kg Src raw.stat raw.ell
          jStar raw.hj (explicitCanonicalMetric F) hmF (s - (n : ℤ)) s hk (by omega)
        have hexp : ((s : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) = (n : ℝ) := by push_cast; ring
        rw [hexp, pow_eq (Quenched.contrastRho γ) n] at h2
        set D : ℝ := determinantDrift P γ (respGrid jStar F) jStar s with hDdef
        have hXge : (1 : ℝ) ≤ ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n := one_le_pow₀ h3rho
        have hDle : D ≤ 1 / 2 := le_trans hD (le_of_lt hη.2)
        have hD0' : 0 ≤ D :=
          determinantDrift_nonneg d _hd γ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
            jStar raw.hj (explicitCanonicalMetric F) hmF s
        have hX0 : (0 : ℝ) ≤ ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n := le_trans zero_le_one hXge
        have hXD : ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n * D ≤ ((3 : ℝ) ^ Quenched.contrastRho
          γ) ^ n * (1 / 2) :=
          mul_le_mul_of_nonneg_left hDle hX0
        have hXD0 : (0 : ℝ) ≤ ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n * D := mul_nonneg hX0 hD0'
        have hscal : 1 + ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n * D ≤
            3 / 2 * ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n := by linarith only [hXD, hXge]
        have hfac0 : (0 : ℝ) ≤ 1 + ((3 : ℝ) ^ Quenched.contrastRho γ) ^ n * D := by linarith
          only [hXD0]
        have step1 := blockCongr_mono G' h2
        rw [blockCongr_blockScale] at step1
        have step2 := blockScale_mono_of_loewnerLE hEs hfac0
        refine fun V => le_trans (le_trans (step1 V) (step2 V)) ?_
        rw [blockScale_blockScale]
        refine Source.blockScale_le_blockScale_of_pos hM0pd ?_ V
        simp only [hcfun, responseSourceLoadCoefficient, hn, ite_true]
        exact mul_le_mul_of_nonneg_right hscal (mul_nonneg _hCc.le hsqκ)
      · have h1 := hcell P E Ψ Kg Src raw.stat raw.ell jStar raw.hj hthr (explicitCanonicalMetric F)
          hmF s hjs hwin (s - (n : ℤ)) z
        have hnR : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hmaxe : max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0
            = ((n : ℕ) : ℝ) - ((N : ℕ) : ℝ) := by
          have hval : (jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)
              = ((n : ℕ) : ℝ) - ((N : ℕ) : ℝ) := by
            rw [hNR]; push_cast; ring
          rw [hval, max_eq_left (by linarith only [hnR])]
        have hsubcast : (((n - N : ℕ)) : ℝ) = ((n : ℕ) : ℝ) - ((N : ℕ) : ℝ) := by
          exact_mod_cast Nat.cast_sub (le_of_lt hn)
        rw [hmaxe, ← hsubcast, pow_eq γ (n - N)] at h1
        have step1 := blockCongr_mono G' h1
        rw [blockCongr_blockScale] at step1
        have hfac0 : (0 : ℝ) ≤ Csc * A * ((3 : ℝ) ^ γ) ^ (n - N) :=
          mul_nonneg (mul_nonneg hCsc.le hA0) (hpow2 (n - N))
        have step2 := blockScale_mono_of_loewnerLE hEs hfac0
        refine fun V => le_trans (le_trans (step1 V) (step2 V)) ?_
        rw [blockScale_blockScale]
        refine Source.blockScale_le_blockScale_of_pos hM0pd ?_ V
        simp only [hcfun, responseSourceLoadCoefficient, Nat.not_le.mpr hn, ite_false]
        exact le_rfl
    -- the two-regime summation is independent of the response construction
    set Msc : ℝ := Cl * κ with hMsc
    have hMsc0 : (0 : ℝ) ≤ Msc := mul_nonneg _hCl.le hκ0
    have hsmall2 : A * ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ N ≤ Cs⁻¹ := by
      have h := hsmall.2
      have hw : (3 : ℝ) ^ (-((3 : ℝ) / 2 * ((s : ℝ) - (jStar : ℝ))))
          = ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ N := by
        rw [← hNR, ← weight_eq]
        ring_nf
      rw [hw] at h
      have hmul : A * ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ N * Cs ≤ 1 := by
        dsimp [A]
        calc aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
                ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ N * Cs
            = Cs * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
                ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ N := by ring
          _ ≤ 1 := h
      have h2 := (le_div_iff₀ _hCs).mpr hmul
      rwa [one_div] at h2
    have hseries := responseSourceLoadGeometricSum γ κ Cc Cs Cl Csc A N _hγ hκ0
      _hCc _hCs _hCl.le hCsc.le hA0 hsmall2
    have husum : Summable fun n : ℕ =>
        (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * (cfun n * Msc)) := by
      simpa only [hcfun, responseSourceLoadCoefficient, hMsc] using hseries.1
    have hfinal := respSourceLoad_le_of_loewner_scalewise P jStar F s b Y cfun Msc
      hcfun0 hMsc0 hmF hY husum hcellb
    refine ⟨hfinal.1, le_trans hfinal.2 ?_⟩
    simpa only [hcfun, responseSourceLoadCoefficient, hMsc] using hseries.2
  -- integrability of the coarse block at every adapted cell
  have hint : ∀ (k : ℤ) (y : Vec d),
      HasIntegrableCoarseBlock P (HighContrast.adaptedCellTranslate (respGrid jStar F) k y) :=
    fun k y => Annealed.hasIntegrableCoarseBlock_adapted d _hd P γ E Ψ Kg Src raw.stat raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hmF k y
  obtain ⟨Gplus, hbMinus, hbPlus⟩ := responseSourceCoefficientIdentities d γ S ε σ Cglob Cprof
    Csrc0 H Bresp P E Ψ Kg Src B jStar F s t raw hqU hFfull hmF hint
  have hEsPlus : BlockMatLoewnerLE (blockCongr Gplus (adaptedMean P (respGrid jStar F) s))
      (blockScale (Cc * Real.sqrt κ) (respM0 F)) := by
    have h := hcal.2.2.2.2.2
    rw [respEhatPlus, blockAdjoint, respEhatMinus, blockCongr_blockCongr] at h
    exact h
  have hYm : blockVecDot (respYMinus P jStar F t e)
      (blockMatVecMul (respM0 F) (respYMinus P jStar F t e)) ≤ Cl * κ := by
    rw [← blockSqrt_qform_blockVecDot hM0full.posSemidef]
    exact hload.2.2.1
  have hYp : blockVecDot (respYPlus P jStar F t e)
      (blockMatVecMul (respM0 F) (respYPlus P jStar F t e)) ≤ Cl * κ := by
    rw [← blockSqrt_qform_blockVecDot hM0full.posSemidef]
    exact hload.2.2.2
  have hkm := hkey (respG F) (respCoeffMinus F) (respYMinus P jStar F t e) hbMinus
    hcal.2.2.2.2.1 hYm
  have hkp := hkey Gplus (respCoeffPlus F) (respYPlus P jStar F t e) hbPlus hEsPlus hYp
  exact ⟨zero_le_respSourceLoad _ _ _ _ _ _, zero_le_respSourceLoad _ _ _ _ _ _,
    hkm.2, hkp.2, hkm.1, hkp.1⟩

/-! ## The contraction arithmetic -/

/-- **The contraction arithmetic** `response_contraction_arith`: rearranging `kappa_t - 1 <= omega
kappa_t`
(`p.response.transfer`).  Pure real arithmetic.

From `omega <= delta/(1+delta) < 1` one gets `(1-omega) kappa_t <= 1`, hence
`kappa_t <= 1/(1-omega) <= 1 + delta`. -/
theorem response_contraction_arith (d : ℕ) (_hd : 2 ≤ d) (σ δad κt κs r ω : ℝ)
    (hκt : 1 ≤ κt) (_hts : κt ≤ κs) (_hsr : κs ≤ r ^ 2 * κt)
    (_hr : r < Real.exp ((d : ℝ) * σ)) (hδad : δad ∈ Set.Ioc (0 : ℝ) 1)
    (hω : κt - 1 ≤ ω * κt) (hωδ : ω ≤ δad / (1 + δad)) :
    κt ≤ 1 + δad := by
  have h1 : 0 < 1 + δad := by linarith only [hδad.1]
  have ne1 : (1 + δad : ℝ) ≠ 0 := ne_of_gt h1
  have h2 : ω * (1 + δad) ≤ δad := by
    field_simp [ne1] at hωδ
    exact hωδ
  have hA : κt * (1 - ω) ≤ 1 := by linarith only [hω]
  have hB : 1 ≤ (1 - ω) * (1 + δad) := by nlinarith only [h2]
  have hκt0 : (0 : ℝ) ≤ κt := le_trans zero_le_one hκt
  calc κt = κt * 1 := by ring
    _ ≤ κt * ((1 - ω) * (1 + δad)) := mul_le_mul_of_nonneg_left hB hκt0
    _ = (κt * (1 - ω)) * (1 + δad) := by ring
    _ ≤ 1 * (1 + δad) := mul_le_mul_of_nonneg_right hA h1.le
    _ = 1 + δad := by ring

/-! ## The parameter choice -/

/-- Arithmetic core of **the parameter choice**: four nonnegative terms, each at most `τ`, scaled by
`C r^2` with `1 ≤ r ≤ 2`, stay below `16 C τ`. -/
private theorem response_parameter_choice_arith {C r a1 a2 a3 a4 τ T : ℝ} (hC : 0 < C)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) (h4 : 0 ≤ a4)
    (hb1 : a1 ≤ τ) (hb2 : a2 ≤ τ) (hb3 : a3 ≤ τ) (hb4 : a4 ≤ τ)
    (hT : 16 * C * τ = T) :
    C * r ^ 2 * (a1 + a2 + a3 + a4) ≤ T := by
  have hsum : a1 + a2 + a3 + a4 ≤ 4 * τ := by linarith only [hb1, hb2, hb3, hb4]
  have hsum0 : (0 : ℝ) ≤ a1 + a2 + a3 + a4 := by linarith only [h1, h2, h3, h4]
  have hrsq : r ^ 2 ≤ 4 := by nlinarith only [hr1, hr2]
  have hrsq0 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have step1 : C * r ^ 2 * (a1 + a2 + a3 + a4) ≤ C * 4 * (a1 + a2 + a3 + a4) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrsq hC.le) hsum0
  have step2 : C * 4 * (a1 + a2 + a3 + a4) ≤ C * 4 * (4 * τ) :=
    mul_le_mul_of_nonneg_left hsum (by linarith only [hC])
  calc C * r ^ 2 * (a1 + a2 + a3 + a4) ≤ C * 4 * (a1 + a2 + a3 + a4) := step1
    _ ≤ C * 4 * (4 * τ) := step2
    _ = 16 * C * τ := by ring
    _ = T := hT

/-- **The parameter choice** `response_parameter_choice` (`p.response.transfer`): choose `H` large,
then `eta` small, then `sigma_0` small enough that `r < e^{d sigma_0}`, so that the printed
`omega` obeys `omega <= delta_ad/(1+delta_ad)`.  The `omega` formula matches the printed display
symbol for symbol.

Route: `3^{-H}` and `3^{-alpha H}` tend to `0`, so fix `H` with
`C' (3^{-H} + 4 * 3^{-2 alpha H}) <= delta_ad/(4(1+delta_ad))`, where `C'` absorbs the `r^2`
factor (bounded once `sigma_0 <= 1`); then `eta` with `C' * 4 * (C_H eta^{1/(2Q)})^2` small;
then `sigma_0` so small that `r - 1 <= e^{d sigma_0} - 1` and `sqrt(r-1)` are small. -/
theorem response_parameter_choice (d : ℕ) (_hd : 2 ≤ d) (h Q : ℕ) (ε δad α C : ℝ)
    (CH : ℕ → ℝ) (_hε : 0 < ε) (_hδad : δad ∈ Set.Ioc (0 : ℝ) 1)
    (_hα : α ∈ Set.Ioo (0 : ℝ) 1) (_hC : 0 < C) (_hQ : 2 ≤ Q) (_hCH : ∀ n : ℕ, 0 < CH n) :
    ∃ H : ℕ, max 4 h ≤ H ∧ ∃ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
      ∃ σ₀ : ℝ, σ₀ ∈ Set.Ioc (0 : ℝ) ε ∧
        ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) σ₀ → ∀ r : ℝ, 1 ≤ r → r < Real.exp ((d : ℝ) * σ) →
          C * r ^ 2 * ((r - 1) + Real.sqrt (r - 1) + (3 : ℝ) ^ (-(H : ℝ)) +
              ((3 : ℝ) ^ (-(α * (H : ℝ))) + CH H * η ^ ((1 : ℝ) / (2 * (Q : ℝ)))) ^ 2) ≤
            δad / (1 + δad) := by
  obtain ⟨hδ0, hδ1⟩ := _hδad
  obtain ⟨hα0, hα1⟩ := _hα
  -- the target `T` and the per-term tolerance `τ`
  have hTpos : 0 < δad / (1 + δad) := div_pos hδ0 (by linarith only [hδ0])
  set τ : ℝ := δad / (1 + δad) / (16 * C) with hτdef
  have hτpos : 0 < τ := div_pos hTpos (by linarith only [_hC])
  have hsqτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτpos
  -- rewriting rules for the two `rpow` decays
  have key3 : ∀ n : ℕ, (3 : ℝ) ^ (-(n : ℝ)) = (1 / 3 : ℝ) ^ n := by
    intro n
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
  have keyα : ∀ n : ℕ, (3 : ℝ) ^ (-(α * (n : ℝ))) = ((3 : ℝ) ^ (-α)) ^ n := by
    intro n
    rw [show -(α * (n : ℝ)) = (-α) * (n : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]
  have hbase0 : (0 : ℝ) < (3 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : (3 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα0])
  -- choose `H`
  obtain ⟨N₂, hN₂⟩ := exists_pow_lt_of_lt_one hτpos (show (1:ℝ)/3 < 1 by norm_num)
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt_of_lt_one (half_pos hsqτ) hbase1
  refine ⟨max (max 4 h) (max N₁ N₂), le_max_left _ _, ?_⟩
  set H : ℕ := max (max 4 h) (max N₁ N₂) with hHdef
  have hA3 : (3 : ℝ) ^ (-(H : ℝ)) ≤ τ := by
    rw [key3]
    refine le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_) hN₂.le
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hAα : (3 : ℝ) ^ (-(α * (H : ℝ))) ≤ Real.sqrt τ / 2 := by
    rw [keyα]
    refine le_trans (pow_le_pow_of_le_one hbase0.le hbase1.le ?_) hN₁.le
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  -- choose `η`
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by
    have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast _hQ
    linarith only [this]
  have hQne : (2 * (Q : ℝ)) ≠ 0 := by positivity
  have hCHpos : 0 < CH H := _hCH H
  have hBvpos : 0 < Real.sqrt τ / 2 / CH H := by positivity
  refine ⟨min (1/4) ((Real.sqrt τ / 2 / CH H) ^ (2 * (Q : ℝ))), ?_, ?_⟩
  · exact ⟨lt_min (by norm_num) (Real.rpow_pos_of_pos hBvpos _),
      lt_of_le_of_lt (min_le_left _ _) (by norm_num)⟩
  set η : ℝ := min (1/4) ((Real.sqrt τ / 2 / CH H) ^ (2 * (Q : ℝ))) with hηdef
  have hηpos : 0 < η := lt_min (by norm_num) (Real.rpow_pos_of_pos hBvpos _)
  have hηp : η ^ ((1 : ℝ) / (2 * (Q : ℝ))) ≤ Real.sqrt τ / 2 / CH H := by
    have h1 : η ^ ((1 : ℝ) / (2 * (Q : ℝ))) ≤
        ((Real.sqrt τ / 2 / CH H) ^ (2 * (Q : ℝ))) ^ ((1 : ℝ) / (2 * (Q : ℝ))) :=
      Real.rpow_le_rpow hηpos.le (min_le_right _ _) (by positivity)
    rwa [← Real.rpow_mul hBvpos.le, mul_one_div_cancel hQne, Real.rpow_one] at h1
  have hA4 : ((3 : ℝ) ^ (-(α * (H : ℝ))) + CH H * η ^ ((1 : ℝ) / (2 * (Q : ℝ)))) ^ 2 ≤ τ := by
    have hterm : CH H * η ^ ((1 : ℝ) / (2 * (Q : ℝ))) ≤ Real.sqrt τ / 2 := by
      have := mul_le_mul_of_nonneg_left hηp hCHpos.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hCHpos)] at this
    have hsum : (3 : ℝ) ^ (-(α * (H : ℝ))) + CH H * η ^ ((1 : ℝ) / (2 * (Q : ℝ)))
        ≤ Real.sqrt τ := by linarith only [hAα, hterm]
    have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(α * (H : ℝ))) + CH H * η ^ ((1 : ℝ) / (2 * (Q : ℝ))) := by
      have h1 : (0:ℝ) < (3 : ℝ) ^ (-(α * (H : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
      have h2 : (0:ℝ) ≤ η ^ ((1 : ℝ) / (2 * (Q : ℝ))) :=
        (Real.rpow_pos_of_pos hηpos _).le
      exact add_nonneg h1.le (mul_nonneg hCHpos.le h2)
    calc ((3 : ℝ) ^ (-(α * (H : ℝ))) + CH H * η ^ ((1 : ℝ) / (2 * (Q : ℝ)))) ^ 2
        ≤ (Real.sqrt τ) ^ 2 := pow_le_pow_left₀ hnn hsum 2
      _ = τ := Real.sq_sqrt hτpos.le
  -- choose `σ₀`
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast _hd
    linarith only [this]
  have hmpos : 0 < min τ (min (τ ^ 2) 1) := lt_min hτpos (lt_min (by positivity) (by norm_num))
  have hlogpos : 0 < Real.log (1 + min τ (min (τ ^ 2) 1)) := Real.log_pos (by linarith only [hmpos])
  refine ⟨min ε (Real.log (1 + min τ (min (τ ^ 2) 1)) / (d : ℝ)),
    ⟨lt_min _hε (div_pos hlogpos hdpos), min_le_left _ _⟩, ?_⟩
  intro σ hσ r hr1 hrlt
  obtain ⟨hσpos, hσle⟩ := hσ
  set m : ℝ := min τ (min (τ ^ 2) 1) with hmdef
  have hdσ : (d : ℝ) * σ ≤ Real.log (1 + m) := by
    have h1 : σ ≤ Real.log (1 + m) / (d : ℝ) := le_trans hσle (min_le_right _ _)
    have h2 : (d : ℝ) * σ ≤ (d : ℝ) * (Real.log (1 + m) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 hdpos.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hdpos)] at h2
  have hrle : r ≤ 1 + m := by
    calc r ≤ Real.exp ((d : ℝ) * σ) := hrlt.le
      _ ≤ Real.exp (Real.log (1 + m)) := Real.exp_le_exp.mpr hdσ
      _ = 1 + m := Real.exp_log (by linarith only [hmpos, hmdef])
  have hm_le_τ : m ≤ τ := min_le_left _ _
  have hm_le_τ2 : m ≤ τ ^ 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm_le_1 : m ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hA1 : r - 1 ≤ τ := by linarith only [hrle, hm_le_τ]
  have hA1nn : (0 : ℝ) ≤ r - 1 := by linarith only [hr1]
  have hA2 : Real.sqrt (r - 1) ≤ τ := by
    have : Real.sqrt (r - 1) ≤ Real.sqrt (τ ^ 2) := Real.sqrt_le_sqrt (by linarith only [hrle,
      hm_le_τ2])
    rwa [Real.sqrt_sq hτpos.le] at this
  have hA2nn : (0 : ℝ) ≤ Real.sqrt (r - 1) := Real.sqrt_nonneg _
  have hA3nn : (0 : ℝ) < (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hA4nn : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(α * (H : ℝ))) +
      CH H * η ^ ((1 : ℝ) / (2 * (Q : ℝ)))) ^ 2 := sq_nonneg _
  have hrle2 : r ≤ 2 := by linarith only [hrle, hm_le_1]
  have hCne : C ≠ 0 := ne_of_gt _hC
  have hdne : (1 : ℝ) + δad ≠ 0 := by positivity
  refine response_parameter_choice_arith _hC hr1 hrle2 hA1nn hA2nn hA3nn.le hA4nn
    hA1 hA2 hA3 hA4 ?_
  rw [hτdef]
  field_simp

end HCPolySupport.HighContrast.Multiscale
end
