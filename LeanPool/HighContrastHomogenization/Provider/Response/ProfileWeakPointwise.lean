/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakSplit
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjoint

/-!
# High-contrast homogenization: Provider.Response.ProfileWeakPointwise

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Pointwise weak-profile estimates

The diagonal weak estimate is separated into its recent, bad-energy, and
good-energy terms.  The maximum is assumed finite only at the sample under
consideration; the probabilistic argument supplies this almost everywhere.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem weakRoot_le_recent_add_energy
    {root : ℝ≥0∞} {K L U V En alpha R : ℝ} {M : ℝ≥0∞}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hEn : 0 ≤ En) (halpha : 0 < alpha) (hR : 0 ≤ R)
    (hfinite : M ≠ ⊤)
    (hroot : root ≤ ENNReal.ofReal
      (16 * K * L * (U + V) +
        (16 * K / (2 * alpha)) *
          (if (1 : ℝ) < M.toReal then Real.sqrt M.toReal else R) * En)) :
    root ≤
      ENNReal.ofReal (16 * K * L) *
          (ENNReal.ofReal U + ENNReal.ofReal V) +
        ENNReal.ofReal (16 * K / (2 * alpha)) *
          (if (1 : ℝ≥0∞) < M then
              M ^ (1 / 2 : ℝ) * ENNReal.ofReal En
            else ENNReal.ofReal R * ENNReal.ofReal En) := by
  have hA : 0 ≤ 16 * K * L := by positivity
  have hB : 0 ≤ 16 * K / (2 * alpha) := by positivity
  have hbranch :
      ENNReal.ofReal
          ((if (1 : ℝ) < M.toReal then Real.sqrt M.toReal else R) * En) =
        if (1 : ℝ≥0∞) < M then
            M ^ (1 / 2 : ℝ) * ENNReal.ofReal En
          else ENNReal.ofReal R * ENNReal.ofReal En := by
    have hiff : (1 : ℝ) < M.toReal ↔ (1 : ℝ≥0∞) < M := by
      simpa using
        (ENNReal.toReal_lt_toReal
          (a := (1 : ℝ≥0∞)) (b := M) (by norm_num) hfinite)
    by_cases hbad : (1 : ℝ≥0∞) < M
    · have hbadReal : (1 : ℝ) < M.toReal := hiff.mpr hbad
      rw [ite_eq_left hbad, ite_eq_left hbadReal]
      have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
      have hMrpow : M ^ (1 / 2 : ℝ) =
          ENNReal.ofReal (Real.sqrt M.toReal) := by
        calc
          M ^ (1 / 2 : ℝ) =
              (ENNReal.ofReal M.toReal) ^ (1 / 2 : ℝ) := by
            rw [ENNReal.ofReal_toReal hfinite]
          _ = ENNReal.ofReal (M.toReal ^ (1 / 2 : ℝ)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hM0 (by norm_num)]
          _ = ENNReal.ofReal (Real.sqrt M.toReal) := by
            rw [Real.sqrt_eq_rpow]
      rw [hMrpow, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    · have hbadReal : ¬(1 : ℝ) < M.toReal := fun h ↦ hbad (hiff.mp h)
      rw [ite_eq_right hbad, ite_eq_right hbadReal,
        ← ENNReal.ofReal_mul hR]
  have hrecent : 0 ≤ 16 * K * L * (U + V) := by positivity
  have hfactor : 0 ≤
      if (1 : ℝ) < M.toReal then Real.sqrt M.toReal else R := by
    split <;> positivity
  have henergy : 0 ≤ (16 * K / (2 * alpha)) *
      (if (1 : ℝ) < M.toReal then Real.sqrt M.toReal else R) * En := by
    positivity
  calc
    root ≤ ENNReal.ofReal
        (16 * K * L * (U + V) +
          (16 * K / (2 * alpha)) *
            (if (1 : ℝ) < M.toReal then Real.sqrt M.toReal else R) * En) :=
      hroot
    _ = ENNReal.ofReal (16 * K * L) *
          (ENNReal.ofReal U + ENNReal.ofReal V) +
        ENNReal.ofReal (16 * K / (2 * alpha)) *
          ENNReal.ofReal
            ((if (1 : ℝ) < M.toReal then Real.sqrt M.toReal else R) * En) := by
      rw [ENNReal.ofReal_add hrecent henergy,
        ENNReal.ofReal_mul hA, ENNReal.ofReal_add hU hV]
      congr 1
      rw [show (16 * K / (2 * alpha) *
          (if (1 : ℝ) < M.toReal then Real.sqrt M.toReal else R)) * En =
          (16 * K / (2 * alpha)) *
            ((if (1 : ℝ) < M.toReal then Real.sqrt M.toReal else R) * En) by
        ring, ENNReal.ofReal_mul hB]
    _ = _ := by rw [hbranch]

/-- The primal random-centered weak root splits pointwise into the recent
terms and the two optimizer-energy events. -/
theorem profilePrimalWeakRoot_randomCentered_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {m : Mat d}
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho alpha : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (halpha : alpha = (1 - rho) / 2) (a : CoeffSpace d) (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    profilePrimalWeakRoot m hq t id p r
        (blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r)) a ≤
      ENNReal.ofReal
          (16 * diagonalWeakMetricFactor m E *
            diagonalWeakLoadMinus E p r) *
        (ENNReal.ofReal (diagonalWeakCellSum q t H (1 / 2) E a) +
          ENNReal.ofReal
            (diagonalWeakAverageSum q t H (1 / 2) rho E a)) +
      ENNReal.ofReal
          (16 * diagonalWeakMetricFactor m E / (2 * alpha)) *
        (if (1 : ℝ≥0∞) < diagonalWeakMaximum rho q t E a then
            diagonalWeakMaximum rho q t E a ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (diagonalWeakEnergy hq t a p r)
          else
            ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (diagonalWeakEnergy hq t a p r)) := by
  have hrootSpec := matSqrt_spec hm.posSemidef
  have hsymm : matTranspose (matSqrt m) = matSqrt m := by
    show (matSqrt m).transpose = matSqrt m
    rw [← conjTranspose_eq_transpose']
    exact hrootSpec.1.isHermitian
  have hraw := diagonalWeakNorm_primal_le hq t H hsymm hrootSpec.2 hm
    hE hEpd (rho := rho) (s := (1 / 2 : ℝ)) (delta := 1)
    hrho (by linarith only [hrho1])
    (by linarith only [hrho1]) (by norm_num) (by norm_num) (by norm_num)
    (a := a) p r
  rw [ite_eq_right hfinite] at hraw
  norm_num only [Real.sqrt_one, inv_one] at hraw
  have halphaPos : 0 < alpha := by
    rw [halpha]
    linarith only [hrho1]
  have hden : 1 - rho = 2 * alpha := by
    rw [halpha]
    ring
  have hexpAlpha : 1 / 2 - rho / 2 = alpha := by
    rw [halpha]
    ring
  have hcoef : 16 / (1 - rho) * diagonalWeakMetricFactor m E =
      16 * diagonalWeakMetricFactor m E / (2 * alpha) := by
    rw [hden]
    ring
  have hroot : profilePrimalWeakRoot m hq t id p r
        (blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r)) a ≤
      ENNReal.ofReal
        (16 * diagonalWeakMetricFactor m E *
            diagonalWeakLoadMinus E p r *
              (diagonalWeakCellSum q t H (1 / 2) E a +
                diagonalWeakAverageSum q t H (1 / 2) rho E a) +
          (16 * diagonalWeakMetricFactor m E / (2 * alpha)) *
            (if (1 : ℝ) <
                (diagonalWeakMaximum rho q t E a).toReal then
                Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
              else (3 : ℝ) ^ (-alpha * (H : ℝ))) *
            diagonalWeakEnergy hq t a p r) := by
    simp only [profilePrimalWeakRoot, id_eq]
    have hexp : (-(1 / 2 : ℝ)) * (t : ℝ) =
        -((1 / 2 : ℝ) * (t : ℝ)) := by ring
    rw [hexp]
    calc
      _ ≤ ENNReal.ofReal
          (16 * diagonalWeakMetricFactor m E *
              diagonalWeakLoadMinus E p r *
                (diagonalWeakCellSum q t H (1 / 2) E a +
                  diagonalWeakAverageSum q t H (1 / 2) rho E a) +
            (16 / (1 - rho) * diagonalWeakMetricFactor m E) *
              (if (1 : ℝ) <
                  (diagonalWeakMaximum rho q t E a).toReal then
                  Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
                else (3 : ℝ) ^ (-((1 / 2 - rho / 2) * (H : ℝ)))) *
              diagonalWeakEnergy hq t a p r) := hraw
      _ = _ := by
        congr 1
        rw [hcoef, hexpAlpha]
        ring_nf
  exact weakRoot_le_recent_add_energy
    (diagonalWeakMetricFactor_nonneg m E)
    (diagonalWeakLoadMinus_nonneg E p r)
    (diagonalWeakCellSum_nonneg q t H (1 / 2) E a)
    (diagonalWeakAverageSum_nonneg q t H (1 / 2) rho E a)
    (diagonalWeakEnergy_nonneg hq t a p r) halphaPos
    (Real.rpow_nonneg (by norm_num) _) hfinite hroot

/-- The coefficient-transpose optimizer has the same pointwise split with
its independent plus load and adjoint energy. -/
theorem profileAdjointWeakRoot_randomCentered_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {m : Mat d}
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho alpha : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (halpha : alpha = (1 - rho) / 2) (a : CoeffSpace d) (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    profileAdjointWeakRoot m hq t id p r
        (blockCellAverage (adaptedCell q t)
          (diagonalWeakAdjointState hq t a p r)) a ≤
      ENNReal.ofReal
          (16 * diagonalWeakMetricFactor m E *
            diagonalWeakLoadPlus E p r) *
        (ENNReal.ofReal (diagonalWeakCellSum q t H (1 / 2) E a) +
          ENNReal.ofReal
            (diagonalWeakAverageSum q t H (1 / 2) rho E a)) +
      ENNReal.ofReal
          (16 * diagonalWeakMetricFactor m E / (2 * alpha)) *
        (if (1 : ℝ≥0∞) < diagonalWeakMaximum rho q t E a then
            diagonalWeakMaximum rho q t E a ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (diagonalWeakAdjointEnergy hq t a p r)
          else
            ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (diagonalWeakAdjointEnergy hq t a p r)) := by
  have hrootSpec := matSqrt_spec hm.posSemidef
  have hsymm : matTranspose (matSqrt m) = matSqrt m := by
    show (matSqrt m).transpose = matSqrt m
    rw [← conjTranspose_eq_transpose']
    exact hrootSpec.1.isHermitian
  have hraw := diagonalWeakNorm_adjoint_le hq t H hsymm hrootSpec.2 hm
    hE hEpd (rho := rho) (s := (1 / 2 : ℝ)) (delta := 1)
    hrho (by linarith only [hrho1])
    (by linarith only [hrho1]) (by norm_num) (by norm_num) (by norm_num)
    a p r
  rw [ite_eq_right hfinite] at hraw
  norm_num only [Real.sqrt_one, inv_one] at hraw
  have halphaPos : 0 < alpha := by
    rw [halpha]
    linarith only [hrho1]
  have hden : 1 - rho = 2 * alpha := by
    rw [halpha]
    ring
  have hexpAlpha : 1 / 2 - rho / 2 = alpha := by
    rw [halpha]
    ring
  have hcoef : 16 / (1 - rho) * diagonalWeakMetricFactor m E =
      16 * diagonalWeakMetricFactor m E / (2 * alpha) := by
    rw [hden]
    ring
  have hroot : profileAdjointWeakRoot m hq t id p r
        (blockCellAverage (adaptedCell q t)
          (diagonalWeakAdjointState hq t a p r)) a ≤
      ENNReal.ofReal
        (16 * diagonalWeakMetricFactor m E *
            diagonalWeakLoadPlus E p r *
              (diagonalWeakCellSum q t H (1 / 2) E a +
                diagonalWeakAverageSum q t H (1 / 2) rho E a) +
          (16 * diagonalWeakMetricFactor m E / (2 * alpha)) *
            (if (1 : ℝ) <
                (diagonalWeakMaximum rho q t E a).toReal then
                Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
              else (3 : ℝ) ^ (-alpha * (H : ℝ))) *
            diagonalWeakAdjointEnergy hq t a p r) := by
    simp only [profileAdjointWeakRoot, id_eq]
    have hexp : (-(1 / 2 : ℝ)) * (t : ℝ) =
        -((1 / 2 : ℝ) * (t : ℝ)) := by ring
    rw [hexp]
    calc
      _ ≤ ENNReal.ofReal
          (16 * diagonalWeakMetricFactor m E *
              diagonalWeakLoadPlus E p r *
                (diagonalWeakCellSum q t H (1 / 2) E a +
                  diagonalWeakAverageSum q t H (1 / 2) rho E a) +
            (16 / (1 - rho) * diagonalWeakMetricFactor m E) *
              (if (1 : ℝ) <
                  (diagonalWeakMaximum rho q t E a).toReal then
                  Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
                else (3 : ℝ) ^ (-((1 / 2 - rho / 2) * (H : ℝ)))) *
              diagonalWeakAdjointEnergy hq t a p r) := hraw
      _ = _ := by
        congr 1
        rw [hcoef, hexpAlpha]
        ring_nf
  exact weakRoot_le_recent_add_energy
    (diagonalWeakMetricFactor_nonneg m E)
    (diagonalWeakLoadPlus_nonneg E p r)
    (diagonalWeakCellSum_nonneg q t H (1 / 2) E a)
    (diagonalWeakAverageSum_nonneg q t H (1 / 2) rho E a)
    (by
      simpa only [diagonalWeakAdjointEnergy_eq] using
        diagonalWeakEnergy_nonneg hq t a.transpose p r) halphaPos
    (Real.rpow_nonneg (by norm_num) _) hfinite hroot

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

private theorem weakRoot_le_recent_add_energy_at_level
    {root : ℝ≥0∞} {crec cmax K L U V En alpha R lev : ℝ} {M : ℝ≥0∞}
    (hcrec : 0 ≤ crec) (hcmax : 0 ≤ cmax)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hEn : 0 ≤ En) (halpha : 0 < alpha) (hR : 0 ≤ R) (hlev : 0 ≤ lev)
    (hfinite : M ≠ ⊤)
    (hroot : root ≤ ENNReal.ofReal
      (crec * K * L * (U + V) +
        (cmax * K / (2 * alpha)) *
          (if lev < M.toReal then Real.sqrt M.toReal else R) * En)) :
    root ≤
      ENNReal.ofReal (crec * K * L) *
          (ENNReal.ofReal U + ENNReal.ofReal V) +
        ENNReal.ofReal (cmax * K / (2 * alpha)) *
          (if ENNReal.ofReal lev < M then
              M ^ (1 / 2 : ℝ) * ENNReal.ofReal En
            else ENNReal.ofReal R * ENNReal.ofReal En) := by
  have hA : 0 ≤ crec * K * L := by positivity
  have hB : 0 ≤ cmax * K / (2 * alpha) := by positivity
  have hiff : lev < M.toReal ↔ ENNReal.ofReal lev < M := by
    have h := ENNReal.toReal_lt_toReal
      (a := ENNReal.ofReal lev) (b := M) ENNReal.ofReal_ne_top hfinite
    rwa [ENNReal.toReal_ofReal hlev] at h
  have hbranch :
      ENNReal.ofReal
          ((if lev < M.toReal then Real.sqrt M.toReal else R) * En) =
        if ENNReal.ofReal lev < M then
            M ^ (1 / 2 : ℝ) * ENNReal.ofReal En
          else ENNReal.ofReal R * ENNReal.ofReal En := by
    by_cases hbad : ENNReal.ofReal lev < M
    · have hbadReal : lev < M.toReal := hiff.mpr hbad
      rw [ite_eq_left hbad, ite_eq_left hbadReal]
      have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
      have hMrpow : M ^ (1 / 2 : ℝ) =
          ENNReal.ofReal (Real.sqrt M.toReal) := by
        calc
          M ^ (1 / 2 : ℝ) =
              (ENNReal.ofReal M.toReal) ^ (1 / 2 : ℝ) := by
            rw [ENNReal.ofReal_toReal hfinite]
          _ = ENNReal.ofReal (M.toReal ^ (1 / 2 : ℝ)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hM0 (by norm_num)]
          _ = ENNReal.ofReal (Real.sqrt M.toReal) := by
            rw [Real.sqrt_eq_rpow]
      rw [hMrpow, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    · have hbadReal : ¬lev < M.toReal := fun h ↦ hbad (hiff.mp h)
      rw [ite_eq_right hbad, ite_eq_right hbadReal, ← ENNReal.ofReal_mul hR]
  have hrecent : 0 ≤ crec * K * L * (U + V) := by positivity
  have hfactor : 0 ≤
      if lev < M.toReal then Real.sqrt M.toReal else R := by
    split <;> positivity
  have henergy : 0 ≤ (cmax * K / (2 * alpha)) *
      (if lev < M.toReal then Real.sqrt M.toReal else R) * En := by
    positivity
  calc
    root ≤ ENNReal.ofReal
        (crec * K * L * (U + V) +
          (cmax * K / (2 * alpha)) *
            (if lev < M.toReal then Real.sqrt M.toReal else R) * En) :=
      hroot
    _ = ENNReal.ofReal (crec * K * L) *
          (ENNReal.ofReal U + ENNReal.ofReal V) +
        ENNReal.ofReal (cmax * K / (2 * alpha)) *
          ENNReal.ofReal
            ((if lev < M.toReal then Real.sqrt M.toReal else R) * En) := by
      rw [ENNReal.ofReal_add hrecent henergy,
        ENNReal.ofReal_mul hA, ENNReal.ofReal_add hU hV]
      congr 1
      rw [show (cmax * K / (2 * alpha) *
          (if lev < M.toReal then Real.sqrt M.toReal else R)) * En =
          (cmax * K / (2 * alpha)) *
            ((if lev < M.toReal then Real.sqrt M.toReal else R) * En) by
        ring, ENNReal.ofReal_mul hB]
    _ = _ := by rw [hbranch]

/-- The primal random-centered weak root at a released split level. -/
theorem profilePrimalWeakRoot_randomCentered_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {m : Mat d}
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho alpha lev : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hlev : 0 < lev)
    (halpha : alpha = (1 - rho) / 2) (a : CoeffSpace d) (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    profilePrimalWeakRoot m hq t id p r
        (blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r)) a ≤
      ENNReal.ofReal
          (recentConstantAtLevel lev * diagonalWeakMetricFactor m E *
            diagonalWeakLoadMinus E p r) *
        (ENNReal.ofReal (diagonalWeakCellSum q t H (1 / 2) E a) +
          ENNReal.ofReal
            (diagonalWeakAverageSum q t H (1 / 2) rho E a)) +
      ENNReal.ofReal
          (maxGroupConstantAtLevel lev * diagonalWeakMetricFactor m E /
            (2 * alpha)) *
        (if ENNReal.ofReal lev < diagonalWeakMaximum rho q t E a then
            diagonalWeakMaximum rho q t E a ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (diagonalWeakEnergy hq t a p r)
          else
            ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (diagonalWeakEnergy hq t a p r)) := by
  have hrootSpec := matSqrt_spec hm.posSemidef
  have hsymm : matTranspose (matSqrt m) = matSqrt m := by
    show (matSqrt m).transpose = matSqrt m
    rw [← conjTranspose_eq_transpose']
    exact hrootSpec.1.isHermitian
  have hraw := diagonalWeakNorm_primal_at_level_le hq t H hsymm hrootSpec.2 hm
    hE hEpd (rho := rho) (s := (1 / 2 : ℝ)) (delta := lev)
    hrho (by linarith only [hrho1]) (by norm_num) hlev
    (a := a) p r
  rw [ite_eq_right hfinite] at hraw
  have halphaPos : 0 < alpha := by
    rw [halpha]
    linarith only [hrho1]
  have hden : 2 * (1 / 2 : ℝ) - rho = 2 * alpha := by
    rw [halpha]
    ring
  have hexpAlpha : (1 / 2 : ℝ) - rho / 2 = alpha := by
    rw [halpha]
    ring
  have hcoef : maxGroupConstantAtLevel lev / (2 * (1 / 2 : ℝ) - rho) *
      diagonalWeakMetricFactor m E =
      maxGroupConstantAtLevel lev * diagonalWeakMetricFactor m E /
        (2 * alpha) := by
    rw [hden]
    ring
  have hroot : profilePrimalWeakRoot m hq t id p r
        (blockCellAverage (adaptedCell q t)
          (diagonalWeakState hq t a p r)) a ≤
      ENNReal.ofReal
        (recentConstantAtLevel lev * diagonalWeakMetricFactor m E *
            diagonalWeakLoadMinus E p r *
              (diagonalWeakCellSum q t H (1 / 2) E a +
                diagonalWeakAverageSum q t H (1 / 2) rho E a) +
          (maxGroupConstantAtLevel lev * diagonalWeakMetricFactor m E /
              (2 * alpha)) *
            (if lev < (diagonalWeakMaximum rho q t E a).toReal then
                Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
              else (3 : ℝ) ^ (-alpha * (H : ℝ))) *
            diagonalWeakEnergy hq t a p r) := by
    simp only [profilePrimalWeakRoot, id_eq]
    have hexp : (-(1 / 2 : ℝ)) * (t : ℝ) =
        -((1 / 2 : ℝ) * (t : ℝ)) := by ring
    rw [hexp]
    calc
      _ ≤ ENNReal.ofReal
          (recentConstantAtLevel lev * diagonalWeakMetricFactor m E *
              diagonalWeakLoadMinus E p r *
                (diagonalWeakCellSum q t H (1 / 2) E a +
                  diagonalWeakAverageSum q t H (1 / 2) rho E a) +
            (maxGroupConstantAtLevel lev / (2 * (1 / 2 : ℝ) - rho) *
                diagonalWeakMetricFactor m E) *
              (if lev < (diagonalWeakMaximum rho q t E a).toReal then
                  Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
                else (3 : ℝ) ^ (-(((1 / 2 : ℝ) - rho / 2) * (H : ℝ)))) *
              diagonalWeakEnergy hq t a p r) := hraw
      _ = _ := by
        congr 1
        rw [hcoef, hexpAlpha]
        ring_nf
  exact weakRoot_le_recent_add_energy_at_level
    (zero_le_recentConstantAtLevel lev)
    (zero_le_maxGroupConstantAtLevel lev)
    (diagonalWeakMetricFactor_nonneg m E)
    (diagonalWeakLoadMinus_nonneg E p r)
    (diagonalWeakCellSum_nonneg q t H (1 / 2) E a)
    (diagonalWeakAverageSum_nonneg q t H (1 / 2) rho E a)
    (diagonalWeakEnergy_nonneg hq t a p r) halphaPos
    (Real.rpow_nonneg (by norm_num) _) hlev.le hfinite hroot

/-- The adjoint random-centered weak root at a released split level. -/
theorem profileAdjointWeakRoot_randomCentered_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) (H : ℕ) {m : Mat d}
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho alpha lev : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hlev : 0 < lev)
    (halpha : alpha = (1 - rho) / 2) (a : CoeffSpace d) (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    profileAdjointWeakRoot m hq t id p r
        (blockCellAverage (adaptedCell q t)
          (diagonalWeakAdjointState hq t a p r)) a ≤
      ENNReal.ofReal
          (recentConstantAtLevel lev * diagonalWeakMetricFactor m E *
            diagonalWeakLoadPlus E p r) *
        (ENNReal.ofReal (diagonalWeakCellSum q t H (1 / 2) E a) +
          ENNReal.ofReal
            (diagonalWeakAverageSum q t H (1 / 2) rho E a)) +
      ENNReal.ofReal
          (maxGroupConstantAtLevel lev * diagonalWeakMetricFactor m E /
            (2 * alpha)) *
        (if ENNReal.ofReal lev < diagonalWeakMaximum rho q t E a then
            diagonalWeakMaximum rho q t E a ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (diagonalWeakAdjointEnergy hq t a p r)
          else
            ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (diagonalWeakAdjointEnergy hq t a p r)) := by
  have hrootSpec := matSqrt_spec hm.posSemidef
  have hsymm : matTranspose (matSqrt m) = matSqrt m := by
    show (matSqrt m).transpose = matSqrt m
    rw [← conjTranspose_eq_transpose']
    exact hrootSpec.1.isHermitian
  have hraw := diagonalWeakNorm_adjoint_at_level_le hq t H hsymm hrootSpec.2 hm
    hE hEpd (rho := rho) (s := (1 / 2 : ℝ)) (delta := lev)
    hrho (by linarith only [hrho1]) (by norm_num) hlev
    a p r
  rw [ite_eq_right hfinite] at hraw
  have halphaPos : 0 < alpha := by
    rw [halpha]
    linarith only [hrho1]
  have hden : 2 * (1 / 2 : ℝ) - rho = 2 * alpha := by
    rw [halpha]
    ring
  have hexpAlpha : (1 / 2 : ℝ) - rho / 2 = alpha := by
    rw [halpha]
    ring
  have hcoef : maxGroupConstantAtLevel lev / (2 * (1 / 2 : ℝ) - rho) *
      diagonalWeakMetricFactor m E =
      maxGroupConstantAtLevel lev * diagonalWeakMetricFactor m E /
        (2 * alpha) := by
    rw [hden]
    ring
  have hroot : profileAdjointWeakRoot m hq t id p r
        (blockCellAverage (adaptedCell q t)
          (diagonalWeakAdjointState hq t a p r)) a ≤
      ENNReal.ofReal
        (recentConstantAtLevel lev * diagonalWeakMetricFactor m E *
            diagonalWeakLoadPlus E p r *
              (diagonalWeakCellSum q t H (1 / 2) E a +
                diagonalWeakAverageSum q t H (1 / 2) rho E a) +
          (maxGroupConstantAtLevel lev * diagonalWeakMetricFactor m E /
              (2 * alpha)) *
            (if lev < (diagonalWeakMaximum rho q t E a).toReal then
                Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
              else (3 : ℝ) ^ (-alpha * (H : ℝ))) *
            diagonalWeakAdjointEnergy hq t a p r) := by
    simp only [profileAdjointWeakRoot, id_eq]
    have hexp : (-(1 / 2 : ℝ)) * (t : ℝ) =
        -((1 / 2 : ℝ) * (t : ℝ)) := by ring
    rw [hexp]
    calc
      _ ≤ ENNReal.ofReal
          (recentConstantAtLevel lev * diagonalWeakMetricFactor m E *
              diagonalWeakLoadPlus E p r *
                (diagonalWeakCellSum q t H (1 / 2) E a +
                  diagonalWeakAverageSum q t H (1 / 2) rho E a) +
            (maxGroupConstantAtLevel lev / (2 * (1 / 2 : ℝ) - rho) *
                diagonalWeakMetricFactor m E) *
              (if lev < (diagonalWeakMaximum rho q t E a).toReal then
                  Real.sqrt (diagonalWeakMaximum rho q t E a).toReal
                else (3 : ℝ) ^ (-(((1 / 2 : ℝ) - rho / 2) * (H : ℝ)))) *
              diagonalWeakAdjointEnergy hq t a p r) := hraw
      _ = _ := by
        congr 1
        rw [hcoef, hexpAlpha]
        ring_nf
  exact weakRoot_le_recent_add_energy_at_level
    (zero_le_recentConstantAtLevel lev)
    (zero_le_maxGroupConstantAtLevel lev)
    (diagonalWeakMetricFactor_nonneg m E)
    (diagonalWeakLoadPlus_nonneg E p r)
    (diagonalWeakCellSum_nonneg q t H (1 / 2) E a)
    (diagonalWeakAverageSum_nonneg q t H (1 / 2) rho E a)
    (by
      simpa only [diagonalWeakAdjointEnergy_eq] using
        diagonalWeakEnergy_nonneg hq t a.transpose p r) halphaPos
    (Real.rpow_nonneg (by norm_num) _) hlev.le hfinite hroot

end

end HCPolySupport.HighContrast.Response
