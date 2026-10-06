/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDefectComposition
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastResponseUpper
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridDischarge
public import LeanPool.HighContrastHomogenization.Provider.Response.RandomAdaptedResponseCarrierBridge
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileDefectHistory

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastOneStepHub

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The conditional one-step hatted contraction on the fixed grid

This is the composition hub for the native form of Lemma 4.5 of HC: the
fixed-grid pre-Young response families, the carrier bridges at the calibrated
Schur loads, the hatted-drop profile-defect cap, the reabsorbed compact
response upper bound, and the hatted response lower bound compose into a
one-step estimate for the hatted carrier at the terminal generation.

The estimate is conditional on exactly the still-open row (`L`), weak (`W`),
and centering (`Z`) caps at the calibrated loads: these three uniform caps are
the only analytic inputs not derived from stationarity, unit range,
Dagger, and the two smallness clauses.  Once the cap theorem exists, this hub
discharges it into
`hat(t) - 1 ≤ 4·Cpre·((3/2 + 1/(4η))·16d·(hat(s)-hat(t)) + L + W) + 2·Z`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory Set

open scoped ENNReal Matrix

noncomputable section


private theorem calibrated_response_energy_bounds (d : ℕ) [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {t : ℤ} {q S SStar K : Mat d}
    (hintt : HasFiniteAdaptedMean P q t) (hq : q.PosDef)
    (hh0 : IsSkewMat (Response.responseSkew K))
    : (∀ e : Vec d, e ⬝ᵥ e = 1 →
      (fun e ↦
    ∫ a, responseJ (Response.adaptedDomain hq t) (((fun a ↦ a.subSkew (Response.responseSkew K)
      hh0) a).coeffOn (Response.adaptedDomain hq t)) ((Response.centeredResponseLoadP S SStar K) e)
      ((Response.centeredResponseLoadQ S SStar K) e) ∂P) e ≤
        |Response.centeredResponse P (Response.adaptedDomain hq t) ((Response.centeredResponseLoadP
          S SStar K) e)
          ((Response.centeredResponseLoadQ S SStar K) e - (Response.responseSkew K) *ᵥ
            (Response.centeredResponseLoadP S SStar K) e)| + (fun e ↦
    (1 / 2 : ℝ) *
      |vecDot
        (fun i ↦ ∫ a, averageGradient (Response.adaptedDomain hq t) (((fun a ↦ a.subSkew
          (Response.responseSkew K) hh0) a).coeffOn (Response.adaptedDomain hq t))
          (Response.centeredResponseOptimizer (Response.adaptedDomain hq t) ((fun a ↦ a.subSkew
            (Response.responseSkew K) hh0) a) ((Response.centeredResponseLoadP S SStar K) e)
            ((Response.centeredResponseLoadQ S SStar K) e))
            i ∂P)
        (fun i ↦ ∫ a, averageFlux (Response.adaptedDomain hq t) (((fun a ↦ a.subSkew
          (Response.responseSkew K) hh0) a).coeffOn (Response.adaptedDomain hq t))
          (Response.centeredResponseOptimizer (Response.adaptedDomain hq t) ((fun a ↦ a.subSkew
            (Response.responseSkew K) hh0) a) ((Response.centeredResponseLoadP S SStar K) e)
            ((Response.centeredResponseLoadQ S SStar K) e))
            i ∂P)|) e) ∧
    (∀ e : Vec d, e ⬝ᵥ e = 1 →
      (fun e ↦
    ∫ a, responseJ (Response.adaptedDomain hq t) (((fun a ↦ a.subSkew (Response.responseSkew K)
      hh0) a).transpose.coeffOn (Response.adaptedDomain hq t))
      ((Response.centeredResponseLoadP S SStar K) e) ((Response.centeredResponseLoadQ S SStar K) e)
        ∂P) e ≤
        |Response.centeredAdjointResponse P (Response.adaptedDomain hq t)
          ((Response.centeredResponseLoadP S SStar K) e)
          ((Response.centeredResponseLoadQ S SStar K) e + (Response.responseSkew K) *ᵥ
            (Response.centeredResponseLoadP S SStar K) e)| + (fun e ↦
    (1 / 2 : ℝ) *
      |vecDot
        (fun i ↦ ∫ a, averageGradient (Response.adaptedDomain hq t) (((fun a ↦ a.subSkew
          (Response.responseSkew K) hh0) a).transpose.coeffOn (Response.adaptedDomain hq t))
          (Response.centeredAdjointOptimizer (Response.adaptedDomain hq t) ((fun a ↦ a.subSkew
            (Response.responseSkew K) hh0) a) ((Response.centeredResponseLoadP S SStar K) e)
            ((Response.centeredResponseLoadQ S SStar K) e))
            i ∂P)
        (fun i ↦ ∫ a, averageFlux (Response.adaptedDomain hq t) (((fun a ↦ a.subSkew
          (Response.responseSkew K) hh0) a).transpose.coeffOn (Response.adaptedDomain hq t))
          (Response.centeredAdjointOptimizer (Response.adaptedDomain hq t) ((fun a ↦ a.subSkew
            (Response.responseSkew K) hh0) a) ((Response.centeredResponseLoadP S SStar K) e)
            ((Response.centeredResponseLoadQ S SStar K) e))
            i ∂P)|) e) := by
  classical
  let U : Domain d := Response.adaptedDomain hq t
  let h0 : Mat d := Response.responseSkew K
  let loadP : Vec d → Vec d := Response.centeredResponseLoadP S SStar K
  let loadQ : Vec d → Vec d := Response.centeredResponseLoadQ S SStar K
  let sample : CoeffSpace d → CoeffSpace d := fun a ↦ a.subSkew h0 hh0
  let EJMinus : Vec d → ℝ := fun e ↦
    ∫ a, responseJ U ((sample a).coeffOn U) (loadP e) (loadQ e) ∂P
  let EJPlus : Vec d → ℝ := fun e ↦
    ∫ a, responseJ U ((sample a).transpose.coeffOn U)
      (loadP e) (loadQ e) ∂P
  let centerMinus : Vec d → ℝ := fun e ↦
    (1 / 2 : ℝ) *
      |vecDot
        (fun i ↦ ∫ a, averageGradient U ((sample a).coeffOn U)
          (Response.centeredResponseOptimizer U (sample a) (loadP e) (loadQ e))
            i ∂P)
        (fun i ↦ ∫ a, averageFlux U ((sample a).coeffOn U)
          (Response.centeredResponseOptimizer U (sample a) (loadP e) (loadQ e))
            i ∂P)|
  let centerPlus : Vec d → ℝ := fun e ↦
    (1 / 2 : ℝ) *
      |vecDot
        (fun i ↦ ∫ a, averageGradient U ((sample a).transpose.coeffOn U)
          (Response.centeredAdjointOptimizer U (sample a) (loadP e) (loadQ e))
            i ∂P)
        (fun i ↦ ∫ a, averageFlux U ((sample a).transpose.coeffOn U)
          (Response.centeredAdjointOptimizer U (sample a) (loadP e) (loadQ e))
            i ∂P)|
  have henergyMinus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      EJMinus e ≤
        |Response.centeredResponse P U (loadP e)
          (loadQ e - h0 *ᵥ loadP e)| + centerMinus e := by
    intro e _he
    have hid := Response.true_load_centered_response_eq hq t hintt
      (S := S) (SStar := SStar) (K := K) e
    dsimp only at hid
    have hEJ : EJMinus e =
        Response.centeredResponse P U (loadP e) (loadQ e - h0 *ᵥ loadP e) +
          (1 / 2 : ℝ) *
            vecDot
              (fun i ↦ ∫ a, averageGradient U ((sample a).coeffOn U)
                (Response.centeredResponseOptimizer U (sample a)
                  (loadP e) (loadQ e)) i ∂P)
              (fun i ↦ ∫ a, averageFlux U ((sample a).coeffOn U)
                (Response.centeredResponseOptimizer U (sample a)
                  (loadP e) (loadQ e)) i ∂P) :=
      sub_eq_iff_eq_add.mp hid
    have habs : |(1 / 2 : ℝ) *
        vecDot
          (fun i ↦ ∫ a, averageGradient U ((sample a).coeffOn U)
            (Response.centeredResponseOptimizer U (sample a) (loadP e) (loadQ e))
              i ∂P)
          (fun i ↦ ∫ a, averageFlux U ((sample a).coeffOn U)
            (Response.centeredResponseOptimizer U (sample a) (loadP e) (loadQ e))
              i ∂P)| = centerMinus e := by
      dsimp only [centerMinus]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [hEJ, ← habs]
    exact add_le_add (le_abs_self _) (le_abs_self _)
  have henergyPlus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      EJPlus e ≤
        |Response.centeredAdjointResponse P U (loadP e)
          (loadQ e + h0 *ᵥ loadP e)| + centerPlus e := by
    intro e _he
    have hid := Response.true_load_centered_adjoint_response_eq hq t hintt
      (S := S) (SStar := SStar) (K := K) e
    dsimp only at hid
    have hEJ : EJPlus e =
        Response.centeredAdjointResponse P U (loadP e)
            (loadQ e + h0 *ᵥ loadP e) +
          (1 / 2 : ℝ) *
            vecDot
              (fun i ↦ ∫ a, averageGradient U
                ((sample a).transpose.coeffOn U)
                (Response.centeredAdjointOptimizer U (sample a)
                  (loadP e) (loadQ e)) i ∂P)
              (fun i ↦ ∫ a, averageFlux U
                ((sample a).transpose.coeffOn U)
                (Response.centeredAdjointOptimizer U (sample a)
                  (loadP e) (loadQ e)) i ∂P) :=
      sub_eq_iff_eq_add.mp hid
    have habs : |(1 / 2 : ℝ) *
        vecDot
          (fun i ↦ ∫ a, averageGradient U ((sample a).transpose.coeffOn U)
            (Response.centeredAdjointOptimizer U (sample a) (loadP e) (loadQ e))
              i ∂P)
          (fun i ↦ ∫ a, averageFlux U ((sample a).transpose.coeffOn U)
            (Response.centeredAdjointOptimizer U (sample a) (loadP e) (loadQ e))
              i ∂P)| = centerPlus e := by
      dsimp only [centerPlus]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [hEJ, ← habs]
    exact add_le_add (le_abs_self _) (le_abs_self _)
  -- the reabsorbed compact response upper bound
  exact ⟨henergyMinus, henergyPlus⟩
/-- **The conditional one-step hatted contraction.**  The constant `Cpre` is
selected before the law.  All hypotheses except the three caps (`hcaps`) are
either hcore data, grid/window geometry, or the two smallness clauses; the
caps are the exact remaining analytic obligations of the small-contrast
iteration. -/
theorem exists_hatted_one_step_of_profile_caps (d : ℕ) [NeZero d] :
    ∃ Cpre : ℝ, 1 ≤ Cpre ∧
      ∀ {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P],
      ∀ (_hstat : HCPoly.Frozen.IsStationaryLaw P),
      ∀ {gdag : ℝ} {Edag : BlockMat d} {Psidag : ℝ → ℝ} {Kdag : ℝ}
        {Sdag : CoeffSpace d → ℝ},
      ∀ (_hdag : HCPoly.Frozen.CoarseEllipticityDagger
          P gdag Edag Psidag Kdag Sdag),
      ∀ {l : ℤ} {m0 q : Mat d},
      ∀ (_hm0 : m0.PosDef) (_hqeq : q = roundedGrid l m0)
        (hgrid : IsRoundedGrid l q),
      ∀ {s t : ℤ},
      ∀ (_hls : l ≤ s) (H : ℕ) (_ht : t = s + (H : ℤ)),
      ∀ (_hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
        HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k)),
      ∀ {S SStar K : Mat d},
      ∀ (_hS : S.PosDef) (_hStar : SStar.PosDef),
      ∀ (_hform : toFullBlockMat (adaptedMean P q t) =
        schurBlock S SStar K),
      ∀ (_hsmall : 6 * (blockContrast (adaptedMean P q t) - 1) ≤ 1),
      ∀ (_hdrop : (d : ℝ) *
        (adaptedHattedContrast P q s - adaptedHattedContrast P q t) ≤ 1),
      ∀ {eta L W Z : ℝ},
      ∀ (_heta : 0 < eta) (_hL : 0 ≤ L) (_hW : 0 ≤ W),
      ∀ (_habsorb :
        Cpre * eta + (3 / 2 : ℝ) * Cpre * (3 : ℝ) ^ (-(H : ℝ)) ≤ 1 / 2),
      ∀ (_hcaps : ∀ e : Vec d, e ⬝ᵥ e = 1 →
        let h0 := Response.responseSkew K
        let hh0 := Response.is_skew_mat_response_skew K
        let p := Response.centeredResponseLoadP S SStar K e
        let r := Response.centeredResponseLoadQ S SStar K e
        let hq := Recurrence.posDef_of_isRoundedGrid hgrid
        let Xm := Response.profilePrimalCenter P hq t
          (fun a ↦ a.subSkew h0 hh0) p r
        let Xp := Response.profileAdjointCenter P hq t
          (fun a ↦ a.subSkew h0 hh0) p r
        Response.profilePrimalHattedEarlierRow P q h0 s Xm.1 Xm.2 ≤
            ENNReal.ofReal L ∧
          Response.profileAdjointHattedEarlierRow P q h0 s Xp.1 Xp.2 ≤
            ENNReal.ofReal L ∧
          Response.profilePrimalWeakQuantity P m0 hq t
              (fun a ↦ a.subSkew h0 hh0) p r ≤ ENNReal.ofReal W ∧
          Response.profileAdjointWeakQuantity P m0 hq t
              (fun a ↦ a.subSkew h0 hh0) p r ≤ ENNReal.ofReal W ∧
          (1 / 2 : ℝ) *
              |vecDot
                (fun i ↦ ∫ a, averageGradient (Response.adaptedDomain hq t)
                  ((a.subSkew h0 hh0).coeffOn (Response.adaptedDomain hq t))
                  (Response.centeredResponseOptimizer (Response.adaptedDomain hq t)
                    (a.subSkew h0 hh0) p r) i ∂P)
                (fun i ↦ ∫ a, averageFlux (Response.adaptedDomain hq t)
                  ((a.subSkew h0 hh0).coeffOn (Response.adaptedDomain hq t))
                  (Response.centeredResponseOptimizer (Response.adaptedDomain hq t)
                    (a.subSkew h0 hh0) p r) i ∂P)| ≤ Z ∧
          (1 / 2 : ℝ) *
              |vecDot
                (fun i ↦ ∫ a, averageGradient (Response.adaptedDomain hq t)
                  ((a.subSkew h0 hh0).transpose.coeffOn
                    (Response.adaptedDomain hq t))
                  (Response.centeredAdjointOptimizer (Response.adaptedDomain hq t)
                    (a.subSkew h0 hh0) p r) i ∂P)
                (fun i ↦ ∫ a, averageFlux (Response.adaptedDomain hq t)
                  ((a.subSkew h0 hh0).transpose.coeffOn
                    (Response.adaptedDomain hq t))
                  (Response.centeredAdjointOptimizer (Response.adaptedDomain hq t)
                    (a.subSkew h0 hh0) p r) i ∂P)| ≤ Z),
      adaptedHattedContrast P q t - 1 ≤
        4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
            (16 * (d : ℝ) *
              (adaptedHattedContrast P q s -
                adaptedHattedContrast P q t)) + L + W) + 2 * Z := by
  classical
  obtain ⟨Cpre, hCpre, hfamilies⟩ :=
    Response.FixedGrid.exists_pre_young_response_families_of_dagger_fixed_grid d
  refine ⟨Cpre, hCpre, ?_⟩
  intro P _ hstat gdag Edag Psidag Kdag Sdag hdag l m0 q hm0 hqeq hgrid
    s t hls H ht hblocks S SStar K hS hStar hform hsmall hdrop
    eta L W Z heta hL hW habsorb hcaps
  have hst : s ≤ t := by omega
  have hlt : l ≤ t := hls.trans hst
  have hints := (hblocks s hls hst).1
  have hintt := (hblocks t hlt le_rfl).1
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let U : Domain d := Response.adaptedDomain hq t
  let h0 : Mat d := Response.responseSkew K
  have hh0 : IsSkewMat h0 := Response.is_skew_mat_response_skew K
  let h0S : {h : Mat d // IsSkewMat h} := ⟨h0, hh0⟩
  let loadP : Vec d → Vec d := Response.centeredResponseLoadP S SStar K
  let loadQ : Vec d → Vec d := Response.centeredResponseLoadQ S SStar K
  let sample : CoeffSpace d → CoeffSpace d := fun a ↦ a.subSkew h0 hh0
  let expo : ℝ := (3 : ℝ) ^ (-(H : ℝ))
  let drop : ℝ :=
    adaptedHattedContrast P q s - adaptedHattedContrast P q t
  let D : ℝ := 16 * (d : ℝ) * drop
  -- the eight carrier functions of the reabsorbed compact estimate
  let tauMinus : Vec d → ℝ := fun e ↦
    Response.profilePrimalResponseDefect P hq h0 hh0 s t (loadP e) (loadQ e)
  let tauPlus : Vec d → ℝ := fun e ↦
    Response.profileAdjointResponseDefect P hq h0 hh0 s t (loadP e) (loadQ e)
  let EJMinus : Vec d → ℝ := fun e ↦
    ∫ a, responseJ U ((sample a).coeffOn U) (loadP e) (loadQ e) ∂P
  let EJPlus : Vec d → ℝ := fun e ↦
    ∫ a, responseJ U ((sample a).transpose.coeffOn U)
      (loadP e) (loadQ e) ∂P
  let centerMinus : Vec d → ℝ := fun e ↦
    (1 / 2 : ℝ) *
      |vecDot
        (fun i ↦ ∫ a, averageGradient U ((sample a).coeffOn U)
          (Response.centeredResponseOptimizer U (sample a) (loadP e) (loadQ e))
            i ∂P)
        (fun i ↦ ∫ a, averageFlux U ((sample a).coeffOn U)
          (Response.centeredResponseOptimizer U (sample a) (loadP e) (loadQ e))
            i ∂P)|
  let centerPlus : Vec d → ℝ := fun e ↦
    (1 / 2 : ℝ) *
      |vecDot
        (fun i ↦ ∫ a, averageGradient U ((sample a).transpose.coeffOn U)
          (Response.centeredAdjointOptimizer U (sample a) (loadP e) (loadQ e))
            i ∂P)
        (fun i ↦ ∫ a, averageFlux U ((sample a).transpose.coeffOn U)
          (Response.centeredAdjointOptimizer U (sample a) (loadP e) (loadQ e))
            i ∂P)|
  let rowMinus : Vec d → ℝ≥0∞ := fun e ↦
    Response.profilePrimalHattedEarlierRow P q h0 s
      (Response.profilePrimalCenter P hq t sample (loadP e) (loadQ e)).1
      (Response.profilePrimalCenter P hq t sample (loadP e) (loadQ e)).2
  let rowPlus : Vec d → ℝ≥0∞ := fun e ↦
    Response.profileAdjointHattedEarlierRow P q h0 s
      (Response.profileAdjointCenter P hq t sample (loadP e) (loadQ e)).1
      (Response.profileAdjointCenter P hq t sample (loadP e) (loadQ e)).2
  let weakMinus : Vec d → ℝ≥0∞ := fun e ↦
    Response.profilePrimalWeakQuantity P m0 hq t sample (loadP e) (loadQ e)
  let weakPlus : Vec d → ℝ≥0∞ := fun e ↦
    Response.profileAdjointWeakQuantity P m0 hq t sample (loadP e) (loadQ e)
  -- the fixed-grid families at this configuration
  have hfam := hfamilies hstat hdag hm0 hqeq hgrid hls H ht hblocks
  -- the pre-Young premises at the calibrated loads, via the carrier bridges
  have hpreYoungMinus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      ENNReal.ofReal
          |Response.centeredResponse P U (loadP e)
            (loadQ e - h0 *ᵥ loadP e)| ≤
        ENNReal.ofReal Cpre * ENNReal.ofReal (Real.sqrt (tauMinus e)) *
            (ENNReal.ofReal (Real.sqrt (tauMinus e)) +
              ENNReal.ofReal (Real.sqrt (EJMinus e)) +
                rowMinus e ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal Cpre * ENNReal.ofReal expo *
            ENNReal.ofReal (Real.sqrt (EJMinus e)) *
              (ENNReal.ofReal (Real.sqrt (EJMinus e)) +
                rowMinus e ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal Cpre * weakMinus e := by
    intro e _he
    exact Response.true_carrier_compact_minus hq hintt e
      (hfam.1 Cpre le_rfl h0S (loadP e) (loadQ e))
  have hpreYoungPlus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      ENNReal.ofReal
          |Response.centeredAdjointResponse P U (loadP e)
            (loadQ e + h0 *ᵥ loadP e)| ≤
        ENNReal.ofReal Cpre * ENNReal.ofReal (Real.sqrt (tauPlus e)) *
            (ENNReal.ofReal (Real.sqrt (tauPlus e)) +
              ENNReal.ofReal (Real.sqrt (EJPlus e)) +
                rowPlus e ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal Cpre * ENNReal.ofReal expo *
            ENNReal.ofReal (Real.sqrt (EJPlus e)) *
              (ENNReal.ofReal (Real.sqrt (EJPlus e)) +
                rowPlus e ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal Cpre * weakPlus e := by
    intro e _he
    exact Response.true_carrier_compact_plus hq hintt e
      (hfam.2 Cpre le_rfl h0S (loadP e) (loadQ e))
  -- the defect caps from the hatted drop
  have hdefects : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      tauMinus e ≤ D ∧ tauPlus e ≤ D := by
    intro e he
    exact calibratedProfileDefects_le_of_smallDrop hstat hgrid hls hst
      hints hintt hS hStar hform hsmall hdrop e he
  -- the energy identities at the calibrated loads
  obtain ⟨henergyMinus, henergyPlus⟩ :=
    calibrated_response_energy_bounds
      d hintt hq hh0
  have hupper := centered_response_sup_le_of_reabsorbed_compact_preYoung
    (P := P) U (S := S) (SStar := SStar) (K := K)
    (C := Cpre) (expo := expo) (eta := eta) (D := D) (L := L) (W := W)
    (Z := Z)
    (le_trans zero_le_one hCpre)
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (Nat.cast_nonneg H)))
    heta hL hW habsorb
    tauMinus tauPlus EJMinus EJPlus centerMinus centerPlus
    rowMinus rowPlus weakMinus weakPlus
    (fun e _he ↦ Response.profilePrimalResponseDefect_nonneg_of_stationary
      hh0 hstat hgrid hls hst hints hintt (loadP e) (loadQ e))
    (fun e _he ↦ Response.profileAdjointResponseDefect_nonneg_of_stationary
      hh0 hstat hgrid hls hst hints hintt (loadP e) (loadQ e))
    (fun e _he ↦ integral_nonneg fun a ↦
      Book.Ch02.responseJ_nonneg U ((sample a).coeffOn U) (loadP e) (loadQ e))
    (fun e _he ↦ integral_nonneg fun a ↦
      Book.Ch02.responseJ_nonneg U ((sample a).transpose.coeffOn U)
        (loadP e) (loadQ e))
    (fun _e _he ↦ mul_nonneg (by norm_num) (abs_nonneg _))
    (fun _e _he ↦ mul_nonneg (by norm_num) (abs_nonneg _))
    henergyMinus henergyPlus hpreYoungMinus hpreYoungPlus
    (fun e he ↦ (hdefects e he).1)
    (fun e he ↦ (hdefects e he).2)
    (fun e he ↦ ((hcaps e he).1))
    (fun e he ↦ ((hcaps e he).2.1))
    (fun e he ↦ ((hcaps e he).2.2.1))
    (fun e he ↦ ((hcaps e he).2.2.2.1))
    (fun e he ↦ ((hcaps e he).2.2.2.2.1))
    (fun e he ↦ ((hcaps e he).2.2.2.2.2))
  -- the hatted response lower bound at the same domain and loads
  have hintU : HasIntegrableCoarseBlock P (U : Set (Vec d)) := by
    simpa only [U, Response.adaptedDomain_carrier] using! hintt
  have hEU : toFullBlockMat (annealedBlock P (U : Set (Vec d))) =
      schurBlock S SStar K := by
    simpa only [U, Response.adaptedDomain_carrier] using! hform
  have hlower :=
    hattedContrast_annealedBlock_sub_one_le_absoluteCenteredResponseSup
      U hintU hS hStar hEU
  have hhat : hattedContrast (annealedBlock P (U : Set (Vec d))) =
      adaptedHattedContrast P q t := rfl
  rw [hhat] at hlower
  calc
    adaptedHattedContrast P q t - 1 ≤ _ := hlower
    _ ≤ 4 * Cpre * ((3 / 2 + 1 / (4 * eta)) * D + L + W) + 2 * Z :=
      hupper
    _ = 4 * Cpre * ((3 / 2 + 1 / (4 * eta)) *
          (16 * (d : ℝ) *
            (adaptedHattedContrast P q s -
              adaptedHattedContrast P q t)) + L + W) + 2 * Z := by
      dsimp only [D, drop]

end

end HCPolySupport.HighContrast.Quenched
