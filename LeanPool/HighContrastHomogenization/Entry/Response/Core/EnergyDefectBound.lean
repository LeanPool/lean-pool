/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.LoadQuadraticSchur
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ScalarMaximizerExistence
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.PositiveGapClosure

/-!
# High-contrast homogenization: Entry.Response.Core.EnergyDefectBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The response energy-and-defect estimate

This file proves the response energy-and-defect estimate `response_energy_and_defect`
(`e.response.energy.and.defect`) and the all-scale spectral bound of the recentred block
(`p.response.transfer`) it rests on, the latter by splitting the bound across scales and comparing
each piece to the Loewner order. It proves the block spectral bound is nonnegative and controlled
by the Loewner order and by the block trace, bounds the mean part of the estimate by the
determinant drift, telescopes the resulting bound over an interval of scales, and shows the
maximal scale ratio `rhoMax` stays below the response's own scale ratio `respRho`.
-/

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean aspectRatio blockScale blockSub blockTrace coarseBlock matSqrt normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}
private theorem respTau_le [NeZero d] (hd : 2 ≤ d) (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (s t : ℤ) (e : Vec d)
    (he : vecDot e e = 1) (hq : IsUnit (respGrid jStar F))
    (hg : matTranspose (respg F) = -(respg F))
    (hsymm : IsSymmetricBlockMat (respMean P jStar F t))
    (hposd : Book.Ch02.BlockPosDef (respMean P jStar F t))
    (hintT : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hintS : HasIntegrableCoarseBlock P (respCell jStar F s))
    (hkts : respKappa P jStar F t ≤ respKappa P jStar F s)
    (hk1 : 1 ≤ respKappa P jStar F s)
    (hr1 : 1 ≤ respRatio P jStar F s t)
    (hcmp : ∀ Y : BlockVec d, blockVecDot Y (blockMatVecMul (respMean P jStar F s) Y)
      ≤ respRatio P jStar F s t * blockVecDot Y (blockMatVecMul (respMean P jStar F t) Y)) :
    respTauMinus P jStar F s t e
        ≤ 3 * (respRatio P jStar F s t - 1) * Real.sqrt (respKappa P jStar F s) ∧
      respTauPlus P jStar F s t e
        ≤ 3 * (respRatio P jStar F s t - 1) * Real.sqrt (respKappa P jStar F s) := by
  have hM : (respM (respMean P jStar F t)).PosDef := response_by_centered_energies_respM_posDef
    hsymm hposd
  have hsqk : 1 ≤ Real.sqrt (respKappa P jStar F s) := by
    have h := Real.sqrt_le_sqrt hk1
    rwa [Real.sqrt_one] at h
  obtain ⟨hE5, hE6⟩ := respEJ_le hd P jStar F s t e he hq hg hsymm hposd hintT hkts
  have hrnn : (0 : ℝ) ≤ respRatio P jStar F s t - 1 := by linarith only [hr1]
  constructor
  · have hEJm := respEJMinus_eq_final P jStar F t e he hq hg hM hintT
    have htau := respTauMinus_eq P jStar F s t e
      (fun a => respJ_eq_respCoeffMinus (respGrid jStar F) hq s F hg a _ _)
      (integrable_respCoeffMinus P jStar F s hq hg hintS)
      (annealedBlockOf_respCoeffMinus P jStar F s hq hg hintS) hEJm
      (vecDot_respP_respqMinus_eq_one P jStar F t e he hM hg)
    have hcmp2 := ehatMinus_scale_cmp P jStar F s t (respxMinus P jStar F t e)
      (respRatio P jStar F s t) hcmp
    have hlsq : blockVecDot (respxMinus P jStar F t e)
        (blockMatVecMul (respEhatMinus P jStar F t) (respxMinus P jStar F t e))
        = respLsqMinus P jStar F t e := rfl
    rw [hlsq] at hcmp2
    have hL : respLsqMinus P jStar F t e = 2 * (respEJMinus P jStar F t e + 1) := by
      linarith only [hEJm]
    rw [hL] at hcmp2
    have hb : respEJMinus P jStar F t e + 1 ≤ 3 * Real.sqrt (respKappa P jStar F s) := by
      linarith only [hE5, hsqk]
    have hmul := mul_le_mul_of_nonneg_left hb hrnn
    rw [htau, hL]
    nlinarith only [hcmp2, hmul]
  · have hEJp := respEJPlus_eq_final P jStar F t e he hq hg hM hintT
    have htau := respTauPlus_eq P jStar F s t e
      (fun a => respJ_eq_respCoeffPlus (respGrid jStar F) hq s F hg a _ _)
      (integrable_respCoeffPlus P jStar F s hq hg hintS)
      (annealedBlockOf_respCoeffPlus P jStar F s hq hg hintS) hEJp
      (vecDot_respP_respqPlus_eq_one P jStar F t e he hM hg)
    have hcmp2 := ehatPlus_scale_cmp P jStar F s t (respxPlus P jStar F t e)
      (respRatio P jStar F s t) hcmp
    have hlsq : blockVecDot (respxPlus P jStar F t e)
        (blockMatVecMul (respEhatPlus P jStar F t) (respxPlus P jStar F t e))
        = respLsqPlus P jStar F t e := rfl
    rw [hlsq] at hcmp2
    have hL : respLsqPlus P jStar F t e = 2 * (respEJPlus P jStar F t e + 1) := by
      linarith only [hEJp]
    rw [hL] at hcmp2
    have hb : respEJPlus P jStar F t e + 1 ≤ 3 * Real.sqrt (respKappa P jStar F s) := by
      linarith only [hE6, hsqk]
    have hmul := mul_le_mul_of_nonneg_left hb hrnn
    rw [htau, hL]
    nlinarith only [hcmp2, hmul]

/-! ## The response energy and defect estimate -/

/-- **The response energy and defect estimate** `e.response.energy.and.defect`:
`0 <= E[J_t^±] = (L^±)^2/2 - 1 <= C kappa_s^{1/2}` and
`0 <= tau^± <= C(r-1) kappa_s^{1/2}`.

Route: `Annealed.responseJ_eq_coarseBlock_adapted` is AK.HC (2.15) at an adapted cell, so
`E[J_t^±] = (L^±)^2/2 - p.q^± = (L^±)^2/2 - 1` (the loads satisfy `p.q^± = 1`,
`p.response.transfer`);
`(L^-)^2 + (L^+)^2 = 4 e.m_t^{1/2}S_*^{-1}m_t^{1/2}e <= 4 sqrt(theta)` (`p.response.transfer`) and
the
calibrated blocks give the upper bound.  The defect bound is `0 <= E_s - E_t <= (r-1)E_t`
 applied to the same loads, with `Annealed.adaptedMean_antitone` for `E_t <= E_s`.

The premises `_hε`, `_hσ` are carried: without them `1 ≤ B` and `jStar ≤ s`
are unavailable.  The binder *names* are underscore-prefixed because they do not occur in
the statement's own type; the hypotheses are unchanged and the proof uses them, with no
linter suppression. -/
theorem response_energy_and_defect (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) (Cc : ℝ) (_hCc : 0 < Cc) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ : ℝ) (_hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (_hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
        (Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
        (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
        (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ e : Vec d, vecDot e e = 1 → RespEnergyDefect C P jStar F s t e := by
  refine ⟨3, by norm_num, ?_⟩
  intro ε σ hε hσ Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw hcal e he
  have := raw.prob
  let : NeZero d := ⟨by omega⟩
  have hFpd : (toFullBlockMat F).PosDef := posDef_toFullBlockMat raw.symm raw.pos
  have hg : matTranspose (respg F) = -(respg F) := respCalib_respg_isSkew hFpd
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
  have hintT : HasIntegrableCoarseBlock P (respCell jStar F t) :=
    hasIntegrableCoarseBlock_respCell_of_raw d _hd γ P E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      F hm t
  have hintS : HasIntegrableCoarseBlock P (respCell jStar F s) :=
    hasIntegrableCoarseBlock_respCell_of_raw d _hd γ P E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      F hm s
  have hEtpd : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      (explicitCanonicalMetric F) hm t
  have hEspd : (toFullBlockMat (respMean P jStar F s)).PosDef :=
    Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
      (explicitCanonicalMetric F) hm s
  have hsymm : IsSymmetricBlockMat (respMean P jStar F t) :=
    isSymmetricBlockMat_annealedBlock P _
  have hposd : Book.Ch02.BlockPosDef (respMean P jStar F t) := blockPosDef_of_full hEtpd
  have hM : (respM (respMean P jStar F t)).PosDef := response_by_centered_energies_respM_posDef
    hsymm hposd
  have hord : BlockMatLoewnerLE (respMean P jStar F t) (respMean P jStar F s) :=
    respMean_order_of_raw d _hd γ _hγ S ε σ Cglob Cprof Csrc Bresp hε hσ H P E Ψ Kg Src B
      jStar F s t raw
  obtain ⟨hk1, hkts, -, hr1, -⟩ := response_imbalance_comparison d _hd γ _hγ S _hS ε σ hε hσ
    Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw
  have hts : toFullBlockMat (respMean P jStar F t) ≤ toFullBlockMat (respMean P jStar F s) :=
    Analysis.matrixOrder_of_blockMatLoewnerLE hEtpd.isHermitian hEspd.isHermitian hord
  obtain ⟨-, hEsr⟩ := le_detRatio_smul_of_le hEtpd hEspd hts
  have hcmp : ∀ Y : BlockVec d, blockVecDot Y (blockMatVecMul (respMean P jStar F s) Y)
      ≤ respRatio P jStar F s t * blockVecDot Y (blockMatVecMul (respMean P jStar F t) Y) :=
    respMean_scale_cmp P jStar F s t (respRatio P jStar F s t) hEsr
  have hk1s : 1 ≤ respKappa P jStar F s := le_trans hk1 hkts
  have hsqnn : (0 : ℝ) ≤ Real.sqrt (respKappa P jStar F s) := Real.sqrt_nonneg _
  obtain ⟨hE5, hE6⟩ := respEJ_le _hd P jStar F s t e he hq hg hsymm hposd hintT hkts
  obtain ⟨hE9, hE10⟩ := respTau_le _hd P jStar F s t e he hq hg hsymm hposd hintT hintS
    hkts hk1s hr1 hcmp
  exact ⟨respEJMinus_nonneg P jStar F t e hq hg,
    respEJPlus_nonneg P jStar F t e hq hg,
    respEJMinus_eq_final P jStar F t e he hq hg hM hintT,
    respEJPlus_eq_final P jStar F t e he hq hg hM hintT,
    by linarith only [hE5, hsqnn],
    by linarith only [hE6, hsqnn],
    zero_le_respTauMinus_final P jStar F s t e he hq hg hM hord hintT hintS,
    zero_le_respTauPlus_final P jStar F s t e he hq hg hM hord hintT hintS,
    hE9, hE10⟩

/-! ## Helpers for the Step 5 split

Eleven lemmas used in the Step 5 split, kept `private` so that later steps can cite
them without re-deriving them. -/

/-- The flat representation of a scalar multiple of `I_{2d}`
(`p.response.transfer`, the definition of the spectral positive part). -/
theorem toFullBlockMat_blockScale_identity (c : ℝ) :
    toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d)) = c • (1 : FullBlockMat d) := by
  ext (i | i) (j | j) <;>
    simp [toFullBlockMat, blockScale, Book.Ch02.blockIdentity, Book.Ch02.blockDiag,
      Matrix.one_apply]

/-- Quadratic forms add along an additive decomposition of the flat representations.  This is
the form in which the Step 5 split is fed to `BlockMatLoewnerLE`
(`p.response.transfer`). -/
theorem qform_add_of_full (C A B : BlockMat d)
    (h : toFullBlockMat C = toFullBlockMat A + toFullBlockMat B) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul C X) =
      blockVecDot X (blockMatVecMul A X) + blockVecDot X (blockMatVecMul B X) := by
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
    h, Matrix.add_mulVec, dotProduct_add]

/-- **The Step 5 split** (`p.response.transfer`, "decompose the normalized block into
`V^q_{k,t}(z)` and `P^q_{k,t}`"): for any reference `Ak`,
`E_t^{-1/2} A_k(z) E_t^{-1/2} - I = V + (P - I)` with
`V = E_t^{-1/2}(A_k(z) - Ak)E_t^{-1/2}` and `P = E_t^{-1/2} Ak E_t^{-1/2}`, as flat
matrices.  Purely algebraic: no positivity or measurability is used. -/
private theorem allScale_full_split (A Ak At : BlockMat d) :
    toFullBlockMat (blockSub (normalizedBlock A At) (Book.Ch02.blockIdentity d)) =
      toFullBlockMat (normalizedBlock (blockSub A Ak) At) +
        toFullBlockMat (blockSub (normalizedBlock Ak At) (Book.Ch02.blockIdentity d)) := by
  simp only [Recurrence.toFullBlockMat_blockSub, normalizedBlock, toFullBlockMat_ofFullBlockMat,
    Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- The flat representation of `(c_V + c_P) I_{2d}` splits additively
(`p.response.transfer`). -/
private theorem full_scale_add (cv cm : ℝ) :
    toFullBlockMat (blockScale (cv + cm) (Book.Ch02.blockIdentity d)) =
      toFullBlockMat (blockScale cv (Book.Ch02.blockIdentity d)) +
        toFullBlockMat (blockScale cm (Book.Ch02.blockIdentity d)) := by
  simp only [toFullBlockMat_blockScale_identity, add_smul]

/-- `|H_+| >= 0` (`p.response.transfer`).  The defining set of `blockSpecBound`
consists of nonnegative reals, so its `sInf` is nonnegative -- including the junk value `0`
on the empty set, i.e. on a block with no Loewner upper bound of the form `c I_{2d}`. -/
theorem blockSpecBound_nonneg (Hb : BlockMat d) : 0 ≤ blockSpecBound Hb :=
  Real.sInf_nonneg fun _ hx => hx.1

/-- **The attained-infimum lemma for `blockSpecBound`** (`p.response.transfer`): any
nonnegative `c` with `H <= c I_{2d}` bounds `|H_+|`.  The defining set is bounded below by `0`,
so `csInf_le` applies with no further hypothesis. -/
theorem blockSpecBound_le_of_loewner (Hb : BlockMat d) (c : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE Hb (blockScale c (Book.Ch02.blockIdentity d))) :
    blockSpecBound Hb ≤ c :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hc, h⟩

/-- **The subadditive Step 5 bound** (`p.response.transfer`): if the fluctuation part
`V^q_{k,t}(z) = E_t^{-1/2}(A_k(z) - Ak)E_t^{-1/2}` is at most `cv I_{2d}` and the mean part
`P^q_{k,t} - I_{2d}` is at most `cm I_{2d}`, then the spectral positive part of the
normalized difference is at most `cv + cm`.  This is the only place the two parts are
recombined. -/
theorem allScale_specBound_split_le (A Ak At : BlockMat d) (cv cm : ℝ)
    (hcv : 0 ≤ cv) (hcm : 0 ≤ cm)
    (hV : BlockMatLoewnerLE (normalizedBlock (blockSub A Ak) At)
      (blockScale cv (Book.Ch02.blockIdentity d)))
    (hM : BlockMatLoewnerLE (blockSub (normalizedBlock Ak At) (Book.Ch02.blockIdentity d))
      (blockScale cm (Book.Ch02.blockIdentity d))) :
    blockSpecBound (blockSub (normalizedBlock A At) (Book.Ch02.blockIdentity d)) ≤ cv + cm := by
  refine blockSpecBound_le_of_loewner _ _ (by linarith only [hcv, hcm]) ?_
  intro X
  have hv := hV X
  have hm := hM X
  rw [qform_add_of_full _ _ _ (allScale_full_split A Ak At) X,
    qform_add_of_full _ _ _ (full_scale_add cv cm) X]
  linarith only [hv, hm]

/-- **The bounded-supremum lemma for the all-scale maximum**
(`p.response.transfer`).  `respAllScaleMax` is a real `sSup` over the pairs
`(n, z)` with `n : ℕ` -- the scale `k = t - n` -- and `z` in the *finite* index box
`triadicIndexBox d n` of the scale-`k` cells inside `U_t`.  The scale index is **not**
bounded, so the family need not be bounded above; `Real.sSup_le` covers both cases, since on
an unbounded family the real `sSup` takes the junk value `0`.  Consequently a single
nonnegative bound valid at every scale and index bounds `M` pathwise. -/
theorem respAllScaleMax_le_of_forall (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) ≤ M) :
    respAllScaleMax P γ jStar F t a ≤ M := by
  refine Real.sSup_le ?_ hM
  rintro y ⟨n, z, hz, rfl⟩
  exact h n z hz

/-- **The response window lies above `j_*`** (`p.response.transfer`): the raw
output places `s` at least `B log_3(2 + Pi)` generations above `j_*`, and `B >= B_0 >= 1`
while `2 + Pi >= 3`, so `j_* < s < t`.

This is the premise every OneGrid history/profile lemma needs (`(j_* : Z) <= n`), and it
is **not** derivable from `RawOutput` alone: `SelectionData.one_le_B0` is stated only for
`eps in (0, eps_0]` and `sigma in (0, eps]`, so the two range hypotheses `hε`, `hσ` must be
carried. -/
theorem respAllScale_window (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t) :
    (jStar : ℤ) < s ∧ (jStar : ℤ) < t := by
  have : NeZero d := ⟨by omega⟩
  have := raw.prob
  have hB0 : (1 : ℝ) ≤ S.B0 ε σ := S.one_le_B0 ε σ hε hσ
  have hB : (1 : ℝ) ≤ B := hB0.trans ((le_max_left _ _).trans raw.hB)
  have hA : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger raw.ell
  have h3 : (3 : ℝ) ≤ 2 + aspectRatio E := by linarith only [hA]
  have hlog : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h2 : Real.log 3 ≤ Real.log (2 + aspectRatio E) := Real.log_le_log (by norm_num) h3
    rw [Real.logb, le_div_iff₀ hl3]
    linarith only [h2]
  have hpos : (0 : ℝ) < B * Real.logb 3 (2 + aspectRatio E) :=
    mul_pos (zero_lt_one.trans_le hB) (zero_lt_one.trans_le hlog)
  have hceil : (0 : ℤ) < ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ :=
    Int.lt_ceil.mpr (by exact_mod_cast hpos)
  have h1 := raw.hs_lo
  have h2 := raw.hst
  omega

/-! ## Further helpers for the Step 5 split

Eleven additional lemmas used in the Step 5 split.  They close the mean-part estimate
(`mean_part_le_determinantDrift`) and supply the two ingredients needed for the fluctuation half
(the
index-box inclusion `triadicIndexBox_center_mem` and the weight trade
`rhoMax_lt_respRho`).

Every lemma cited by name is either from Mathlib, an exported declaration of this library,
or one of the
`private` helpers above. -/

/-- **The operator-norm Loewner envelope of a positive semidefinite doubled block**
(`p.response.transfer`).  For `N >= 0` the quadratic form is dominated by `|N|` times the
Euclidean square, so `N <= |N| I_{2d}` in the Loewner order.  This is the step that turns a norm
bound into the `blockScale c I` witness that `blockSpecBound` is an infimum over. -/
theorem loewner_le_blockOpNorm_of_posSemidef (N : BlockMat d)
    (hN : (toFullBlockMat N).PosSemidef) :
    BlockMatLoewnerLE N (blockScale (blockOpNorm N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := psd_dot_le_opNorm hN (toFullBlockVec X)
  have hL : blockVecDot X (blockMatVecMul N X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hR : blockVecDot X (blockMatVecMul (blockScale (blockOpNorm N)
      (Book.Ch02.blockIdentity d)) X) =
      blockOpNorm N * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_blockScale_identity]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [hL, hR]
  unfold blockOpNorm at h ⊢
  linarith only [h]

/-- **`|N_+| <= tr N` for a positive semidefinite doubled block**
(`p.response.transfer`, "the mean part telescopes into the nonnegative increments in
`D_{q,j_*}(t)`"; the same fact is printed at `p.response.transfer` as
`|P - I_{2d}| <= tr(P - I_{2d})`).  This is the lemma the mean-part estimate needs:
`Annealed.blockOpNorm_le_one_add_trace` is about `blockOpNorm` and carries a spurious `1 +`,
whereas the printed step needs the clean spectral bound.  The proof is
`blockSpecBound N <= blockOpNorm N <= absSchattenNorm 1 N <= blockTrace N`. -/
private theorem blockSpecBound_le_blockTrace (N : BlockMat d)
    (hN : (toFullBlockMat N).PosSemidef) :
    blockSpecBound N ≤ blockTrace N := by
  have hop : blockOpNorm N ≤ blockTrace N :=
    (Analysis.blockOpNorm_le_absSchattenNorm hN.isHermitian le_rfl).trans
      (Analysis.absSchattenNorm_le_blockTrace hN le_rfl)
  exact (blockSpecBound_le_of_loewner N _ (norm_nonneg _)
    (loewner_le_blockOpNorm_of_posSemidef N hN)).trans hop

/-- `blockTrace` is additive on `blockSub`.  Auxiliary to the telescoping of
`determinantDrift` (`p.response.transfer`). -/
theorem blockTrace_blockSub (A B : BlockMat d) :
    blockTrace (blockSub A B) = blockTrace A - blockTrace B := by
  simp only [blockTrace, Recurrence.toFullBlockMat_blockSub, Matrix.trace_sub]

/-- The integer telescoping identity behind `D_{q,j_*}(t)`
(`p.response.transfer`):
`sum_{j=k+1}^{t} (g(j-1) - g(j)) = g(k) - g(t)` for `k <= t`. -/
theorem telescope_Icc (g : ℤ → ℝ) (k t : ℤ) (hkt : k ≤ t) :
    ∑ j ∈ Finset.Icc (k + 1) t, (g (j - 1) - g j) = g k - g t := by
  induction t, hkt using Int.leInduction with
  | base => simp
  | succ n hn ih =>
      have hset : Finset.Icc (k + 1) (n + 1) = insert (n + 1) (Finset.Icc (k + 1) n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hset, Finset.sum_insert (by simp), ih]
      simp

/-- **Congruence preserves the Loewner gap** (`p.response.transfer`): if `B <= A` and
`R > 0`, then `R^{-1/2} A R^{-1/2} - R^{-1/2} B R^{-1/2} >= 0`.  This is the pathwise sign that
makes every increment of `determinantDrift` nonnegative and makes `P^q_{k,t} - I_{2d}` positive
semidefinite. -/
theorem normalizedBlock_gap_posSemidef (A B R : BlockMat d)
    (hR : (toFullBlockMat R).PosDef)
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hBA : BlockMatLoewnerLE B A) :
    (toFullBlockMat (blockSub (normalizedBlock A R) (normalizedBlock B R))).PosSemidef := by
  have hle : toFullBlockMat B ≤ toFullBlockMat A := (Annealed.fullBlock_le_iff hB hA).2 hBA
  have hgap : (toFullBlockMat A - toFullBlockMat B).PosSemidef := Matrix.le_iff.mp hle
  have hS := (matSqrt_inv_posDef_full hR).isHermitian
  have h := hgap.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat R)⁻¹)
  rw [hS.eq] at h
  rw [Recurrence.toFullBlockMat_blockSub]
  simpa only [normalizedBlock, toFullBlockMat_ofFullBlockMat, Matrix.mul_sub,
    Matrix.sub_mul] using h

/-- **The mean part of the all-scale maximum**
(`p.response.transfer`): "The mean part telescopes into the nonnegative increments in
`D_{q,j_*}(t)`; its weight is bounded by the drift weight because `rho > (1-gamma)/8`."

For `j_* <= k <= t`,
`3^{-rho(t-k)} |(P^q_{k,t} - I_{2d})_+| <= D_{q,j_*}(t)`.

Route, in order: `Annealed.adaptedMean_antitone` gives `A_t <= A_k`, hence `P^q_{k,t} >= I_{2d}`
(`normalizedBlock_gap_posSemidef`); `blockSpecBound_le_blockTrace` replaces the spectral
bound by `tr(P^q_{k,t} - I_{2d})`; `Annealed.normalizedMean_self` gives `P^q_{t,t} = I_{2d}`, so
`telescope_Icc` writes that trace as `sum_{j=k+1}^{t} tr(P^q_{j-1,t} - P^q_{j,t})`; every
summand is nonnegative, so the range extends from `Icc (k+1) t` to `Icc (j_*+1) t`; and the
weight comparison is `rho_gamma = (1+gamma)/2 >= 1/2 > 1/8 >= (1-gamma)/8` together with
`0 <= t - j <= t - k`. -/
theorem mean_part_le_determinantDrift (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (mt : Mat d) (hm : mt.PosDef)
    (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (hkt : k ≤ t) :
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) *
        blockSpecBound (blockSub (relMean P (Geometry.explicitRoundedGrid jStar mt) k t)
          (Book.Ch02.blockIdentity d))
      ≤ determinantDrift P γ (Geometry.explicitRoundedGrid jStar mt) jStar t := by
  have hγ := hdag.g_mem
  set q := Geometry.explicitRoundedGrid jStar mt with hqdef
  have hpd : ∀ j : ℤ, (toFullBlockMat (adaptedMean P q j)).PosDef := fun j =>
    Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm j
  have hgap : ∀ i j : ℤ, (jStar : ℤ) ≤ i → i ≤ j →
      (toFullBlockMat (blockSub (relMean P q i t)
        (relMean P q j t))).PosSemidef := by
    intro i j hi hij
    simpa only [relMean] using
      normalizedBlock_gap_posSemidef (adaptedMean P q i) (adaptedMean P q j)
        (adaptedMean P q t) (hpd t) (hpd i).isHermitian (hpd j).isHermitian
        (Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm i j
          hi hij)
  set T : ℤ → ℝ := fun j =>
    blockTrace (blockSub (relMean P q (j - 1) t) (relMean P q j t)) with hTdef
  have hT0 : ∀ j : ℤ, (jStar : ℤ) + 1 ≤ j → 0 ≤ T j := by
    intro j hj
    exact Analysis.blockTrace_nonneg (hgap (j - 1) j (by omega) (by omega))
  have hI : relMean P q t t = Book.Ch02.blockIdentity d :=
    Annealed.normalizedMean_self d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm t
  -- Step 1: the spectral bound is at most the trace excess
  have hstep1 : blockSpecBound (blockSub (relMean P q k t) (Book.Ch02.blockIdentity d))
      ≤ ∑ j ∈ Finset.Icc (k + 1) t, T j := by
    have hpsd : (toFullBlockMat (blockSub (relMean P q k t)
        (Book.Ch02.blockIdentity d))).PosSemidef := by
      rw [← hI]; exact hgap k t hk hkt
    refine (blockSpecBound_le_blockTrace _ hpsd).trans_eq ?_
    have hsum : ∑ j ∈ Finset.Icc (k + 1) t, T j =
        ∑ j ∈ Finset.Icc (k + 1) t,
          (blockTrace (relMean P q (j - 1) t) - blockTrace (relMean P q j t)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hTdef, blockTrace_blockSub]
    rw [hsum, telescope_Icc (fun j => blockTrace (relMean P q j t)) k t hkt,
      ← hI, blockTrace_blockSub]
  -- Step 2: the weight comparison
  have hrho : (1 : ℝ) / 2 ≤ Quenched.contrastRho γ := by
    unfold Quenched.contrastRho; linarith only [hγ.1]
  have hw : ∀ j ∈ Finset.Icc (k + 1) t,
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) ≤
        (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - (j : ℝ))) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h1 : (j : ℝ) ≤ (t : ℝ) := by exact_mod_cast hj.2
    have h2 : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hu : (0 : ℝ) ≤ (t : ℝ) - (j : ℝ) := by linarith only [h1]
    have hv : (0 : ℝ) ≤ (t : ℝ) - (k : ℝ) := by linarith only [h1, h2]
    have s1 : ((1 - γ) / 8) * ((t : ℝ) - (j : ℝ)) ≤ (1 / 8 : ℝ) * ((t : ℝ) - (j : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hγ.1]) hu
    have s2 : (1 / 8 : ℝ) * ((t : ℝ) - (j : ℝ)) ≤ (1 / 8 : ℝ) * ((t : ℝ) - (k : ℝ)) := by
      linarith only [h2]
    have s3 : (1 / 8 : ℝ) * ((t : ℝ) - (k : ℝ)) ≤ Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hrho]) hv
    linarith only [s1, s2, s3]
  -- Step 3: assemble
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) *
        blockSpecBound (blockSub (relMean P q k t) (Book.Ch02.blockIdentity d))
        ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) * ∑ j ∈ Finset.Icc (k + 1)
          t, T j :=
      mul_le_mul_of_nonneg_left hstep1 hc0
    _ = ∑ j ∈ Finset.Icc (k + 1) t,
          (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) * T j := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.Icc (k + 1) t,
          (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - (j : ℝ))) * T j := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm := Finset.mem_Icc.mp hj
      exact mul_le_mul_of_nonneg_right (hw j hj) (hT0 j (by omega))
    _ ≤ ∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) t,
          (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - (j : ℝ))) * T j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        omega
      · intro j hj _
        have hjm := Finset.mem_Icc.mp hj
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hT0 j (by omega))
    _ = determinantDrift P γ q jStar t := rfl

/-! ### Geometry and exponents for the fluctuation half -/

/-- Every index of the depth-`n` triadic box places its standard cell inside the generation-`t`
centred cube (`p.response.transfer`, "`max_{z in 3^k q Z^d cap U_t}`").  Re-derived here;
the same statement is proved for the weak-seminorm route in
`HCPoly/Entry/Response/Kernel/ScaleAverageSeminorm.lean`, which this file does not
import. -/
private theorem standardCell_subset_centeredCube (t : ℤ) (n : ℕ)
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    HighContrast.standardCell d (t - (n : ℤ)) w ⊆ HighContrast.centeredCube d t := by
  intro x hx
  rw [Recurrence.mem_standardCell_iff] at hx
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have hwi : w i ∈ Finset.Icc (-(((3 ^ n - 1) / 2 : ℕ) : ℤ)) (((3 ^ n - 1) / 2 : ℕ) : ℤ) :=
    (Fintype.mem_piFinset.mp hw) i
  rw [Finset.mem_Icc] at hwi
  set m : ℕ := (3 ^ n - 1) / 2 with hm
  have hone : 1 ≤ (3 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hdvd : 2 ∣ (3 : ℕ) ^ n - 1 := by
    have hodd : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
    exact (Nat.Odd.sub_odd hodd odd_one).two_dvd
  have hm2 : 2 * m = (3 : ℕ) ^ n - 1 := by
    rw [hm, Nat.mul_div_cancel' hdvd]
  have hmR : 2 * (m : ℝ) = (3 : ℝ) ^ n - 1 := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hm2
    push_cast [Nat.cast_sub hone] at h
    linarith only [h]
  set c : ℝ := (3 : ℝ) ^ (t - (n : ℤ)) with hcdef
  have hc : 0 < c := by positivity
  have h3n : ((3 : ℝ) ^ (n : ℤ)) * c = (3 : ℝ) ^ t := by
    rw [hcdef, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring_nf
  have h3nn : ((3 : ℝ) ^ (n : ℤ)) = (3 : ℝ) ^ n := zpow_natCast (3 : ℝ) n
  have hkey : ((m : ℝ) + 1 / 2) * c = 1 / 2 * (3 : ℝ) ^ t := by
    have hmhalf : (m : ℝ) + 1 / 2 = 1 / 2 * (3 : ℝ) ^ n := by linarith only [hmR]
    rw [hmhalf, ← h3nn, mul_assoc, h3n]
  have hwloR : -((m : ℝ)) ≤ (w i : ℝ) := by exact_mod_cast hwi.1
  have hwhiR : (w i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hwi.2
  have hup : ((w i : ℝ) + 1 / 2) * c ≤ ((m : ℝ) + 1 / 2) * c :=
    mul_le_mul_of_nonneg_right (by linarith only [hwhiR]) hc.le
  have hlo : (-((m : ℝ)) - 1 / 2) * c ≤ ((w i : ℝ) - 1 / 2) * c :=
    mul_le_mul_of_nonneg_right (by linarith only [hwloR]) hc.le
  have hlokey : (-((m : ℝ)) - 1 / 2) * c = -(1 / 2) * (3 : ℝ) ^ t := by
    have h : (-((m : ℝ)) - 1 / 2) * c = -(((m : ℝ) + 1 / 2) * c) := by ring
    rw [h, hkey]; ring
  constructor
  · calc -(1 / 2 : ℝ) * (3 : ℝ) ^ t = (-((m : ℝ)) - 1 / 2) * c := hlokey.symm
      _ ≤ ((w i : ℝ) - 1 / 2) * c := hlo
      _ < x i := h1
  · calc x i < ((w i : ℝ) + 1 / 2) * c := h2
      _ ≤ ((m : ℝ) + 1 / 2) * c := hup
      _ = 1 / 2 * (3 : ℝ) ^ t := hkey

/-- The centre of an aligned adapted cell lies in that cell (the cell is an open cube around
its centre).  `p.response.transfer`. -/
private theorem adaptedCellCenter_mem_adaptedCellAtCenter (q : Mat d) (j : ℤ) (w : Fin d → ℤ) :
    adaptedCellCenter q j w ∈ adaptedCellAtCenter q j w := by
  refine ⟨0, ?_, by simp⟩
  refine ⟨0, ?_, by funext i; simp [matVecMul]⟩
  rw [Recurrence.mem_centeredCube_iff]
  intro i
  have h : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hz : (0 : Vec d) i = 0 := rfl
  rw [hz]
  constructor <;> linarith only [h]

/-- **The index-box inclusion needed for the fluctuation half** (`p.response.transfer` versus
`e.scale.selection.fluctuation.history`): the centre indexed by `z in triadicIndexBox d n` at
scale `k = t - n` is a point of the aligned lattice `3^k q Z^d` that lies in `U_t`.  This is
exactly the hypothesis needed to re-index the inner supremum of `respAllScaleMax` from
`triadicIndexBox d n` onto the index set `adaptedLatticeAtScale q k cap U_t` of
`fluctuationHistory`. -/
private theorem triadicIndexBox_center_mem (q : Mat d) (t : ℤ) (n : ℕ)
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    adaptedCellCenter q (t - (n : ℤ)) w ∈
      adaptedLatticeAtScale q (t - (n : ℤ)) ∩ HighContrast.adaptedCell q t :=
  ⟨⟨w, rfl⟩, adaptedCellAtCenter_subset_adaptedCell q t n hw
    (adaptedCellCenter_mem_adaptedCellAtCenter q (t - (n : ℤ)) w)⟩

/-- **`rho_max < rho`** (`p.response.transfer`, "because `rho > rho_max`"): with
`rho_gamma = (1+gamma)/2` and `rho_max = gamma + Q^{-1}(d + (1-gamma)/4)`, the selection bound
`4(d+1) <= Q(1-gamma)` gives `Q^{-1}(d + (1-gamma)/4) < (1-gamma)/2`.  This is the weight trade
of the fluctuation half of the all-scale maximum. -/
theorem rhoMax_lt_respRho (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : rhoMax d γ < Quenched.contrastRho γ := by
  have hq : 0 < (bigQ d γ : ℝ) := bigQ_real_pos d γ hγ
  have hden : 0 < 1 - γ := sub_pos.mpr hγ.2
  have hd1 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hbound := bigQ_mul_one_sub_ge d hd γ hγ
  have hnum : (0 : ℝ) < (d : ℝ) + (1 - γ) / 4 := by linarith only [hd1, hden]
  have hkey : (bigQ d γ : ℝ)⁻¹ * ((d : ℝ) + (1 - γ) / 4) < (1 - γ) / 2 := by
    rw [inv_mul_eq_div, div_lt_iff₀ hq]
    have hre : (1 - γ) / 2 * (bigQ d γ : ℝ) = (bigQ d γ : ℝ) * (1 - γ) / 2 := by ring
    rw [hre]
    linarith only [hbound, hγ.1, hγ.2, hd1]
  unfold rhoMax Quenched.contrastRho
  linarith only [hkey]

/-! ## Helpers for the fluctuation half

Four further lemmas for the fluctuation half of the all-scale maximum
(`p.response.transfer`).  They are stated against the OneGrid history layer, so they require
the import `HCPoly.Entry.Multiscale.OneGrid.HistoryMajorization`.

They cite the `private` helpers `triadicIndexBox_center_mem` and
`rhoMax_lt_respRho`. -/

/-! ### The fluctuation half of the all-scale maximum -/

/-- Auxiliary to the fluctuation half: the summand of `respAllScaleMax`'s fluctuation part at one
scale index
`n'` and one triadic index `z` is dominated by the integrand of `fluctuationHistory`
(`p.response.transfer`, "the fluctuation part is bounded by the maximum defining
`ℋ^fluc_q(t)`, because `rho > rho_max`").

The scale `j = t - n'` lies in `[j_*, t]` because `n' ≤ (t - j_*)⁺`; the centre
`3^j q z` lies in `3^j q Z^d ∩ U_t` by `triadicIndexBox_center_mem`; and the weight is traded
by `rhoMax_lt_respRho`. -/
theorem scale_index_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (mt : Mat d) (hm : mt.PosDef) (t : ℤ)
    (ht : (jStar : ℤ) ≤ t) (a : CoeffSpace d) (n' : ℕ)
    (hn' : n' ∈ Set.Icc 0 (t - (jStar : ℤ)).toNat) (z : Fin d → ℤ)
    (hz : z ∈ triadicIndexBox d n') :
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * Quenched.contrastRho γ * (n' : ℝ)) *
        blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar mt)
          (t - (n' : ℤ)) t
          (adaptedCellCenter (Geometry.explicitRoundedGrid jStar mt) (t - (n' : ℤ)) z) a) ^ bigQ
            d γ ≤
      ⨆ j ∈ Set.Icc (jStar : ℤ) t,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
          ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar mt) j ∩
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mt) t,
            blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar mt) j t y a) ^
              bigQ d γ := by
  have hγ := hdag.g_mem
  have hdom := (oneGrid_fluctuation_integrable_dominate d hd γ P E Ψ K Src hstat hdag
    jStar hjStar mt hm t).2
  obtain ⟨-, hn2⟩ := Set.mem_Icc.mp hn'
  have hnle : (n' : ℤ) ≤ t - (jStar : ℤ) := by omega
  have hj1 : (jStar : ℤ) ≤ t - (n' : ℤ) := by omega
  have hj2 : t - (n' : ℤ) ≤ t := by omega
  have hmem := triadicIndexBox_center_mem (Geometry.explicitRoundedGrid jStar mt) t n' hz
  have hd0 := hdom a (t - (n' : ℤ)) (Set.mem_Icc.mpr ⟨hj1, hj2⟩) _ hmem
  refine le_trans ?_ hd0
  have hcast : (t : ℝ) - ((t - (n' : ℤ) : ℤ) : ℝ) = (n' : ℝ) := by push_cast; ring
  rw [hcast]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) _)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hQ : (0 : ℝ) < (bigQ d γ : ℝ) := bigQ_real_pos d γ hγ
  have hn0 : (0 : ℝ) ≤ (n' : ℝ) := Nat.cast_nonneg n'
  have hrho := rhoMax_lt_respRho d hd γ hγ
  nlinarith only [hrho, hQ, hn0, mul_nonneg hQ.le hn0]

end HCPolySupport.HighContrast.Multiscale
end
