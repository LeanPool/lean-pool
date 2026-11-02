/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.GoodLocalEventAt
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.BadEventCoarseAssemblyFloor

/-!
# BadEventEstimate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The bad event estimate — [ABK] `l.bad.event.lemma`

Under the induction state at scale `m0 - 1`, the probability that the local
good event at scales `n <= m` around a base point `z` fails is at most the sum
of two terms: a stretched-exponential term `exp(-c cstar gamma^{-1} 3^{...})`
carrying the triadic scale gap, and a doubly exponential rare term
`exp(-exp(c E^{-2} gamma^{-1}))`.  The coarse constant `Ccg` is at least `d^6`.

Proved; reduces to the standard axioms.
-/

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.Section3.bad_event_estimate
    (d : ℕ) :
    ∃ Ccg c : ℝ, (d : ℝ) ^ 6 ≤ Ccg ∧ 1 ≤ Ccg ∧ 0 < c ∧
      ∀ (M : Algsuperdiff.Section3.ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        c⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)) →
        ∀ (m n : ℤ), n ≤ m0 - 1 →
          (n < m →
            (3 : ℝ) ^ (5 *
                Algsuperdiff.Section3.Provider.BadEvents.scaleGapPos n m) ≤
              c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) →
          (n < m →
            (d : ℝ) * ((m : ℝ) - (n : ℝ)) * Real.log 3 +
                  Real.exp ((1 / 8 : ℝ) *
                    (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
                Real.exp ((1 / 4 : ℝ) *
                  (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) →
          ∀ z : HCPolySupport.Vec d,
            (Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure.real
                (Algsuperdiff.Frozen.Section3.goodLocalEventAt
                  M (2 * Ccg) m n z)ᶜ ≤
              Real.exp
                  (-(c * Algsuperdiff.Section3.Disorder.cstar M *
                    M.gamma⁻¹ *
                    (3 : ℝ) ^ (-5 *
                      Algsuperdiff.Section3.Provider.BadEvents.scaleGapPos n m) *
                    (3 : ℝ) ^
                      Algsuperdiff.Section3.Provider.BadEvents.scaleGapPos m n)) +
                Real.exp (-Real.exp
                  (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))
-- FROZEN-STATEMENT-END
:= by
  open MeasureTheory HCPolySupport HCPolySupport.Book
    Algsuperdiff.Frozen.Section3 Algsuperdiff.Section3
    Algsuperdiff.Section3.Cutoff
    Algsuperdiff.Section3.Provider.BadEvents in
  obtain ⟨Ccg, hCcg, hCcgFloor, hcentered⟩ :=
    exists_measureReal_compl_goodLocalEvent_originCube_le_of_frozenCoarse_dimFloor d
  have hCcg0 : 0 < Ccg := lt_of_lt_of_le zero_lt_one hCcg
  let c : ℝ :=
    min (badEventOscLowConst d (2 * Ccg))
      (min ((1 / 8 : ℝ) * Ccg⁻¹)
        (badEventCoarseAdmissibleConstFloor d Ccg)⁻¹)
  have hOscPos : 0 < badEventOscLowConst d (2 * Ccg) :=
    badEventOscLowConst_pos (by linarith) d
  have hCoeffPos : 0 < (1 / 8 : ℝ) * Ccg⁻¹ := by positivity
  have hAdmPos : 0 < badEventCoarseAdmissibleConstFloor d Ccg :=
    badEventCoarseAdmissibleConstFloor_pos d hCcg0
  have hcPos : 0 < c := by
    dsimp only [c]
    exact lt_min hOscPos (lt_min hCoeffPos (inv_pos.mpr hAdmPos))
  have hcOsc : c ≤ badEventOscLowConst d (2 * Ccg) := by
    dsimp only [c]
    exact min_le_left _ _
  have hcCoeff : c ≤ (1 / 8 : ℝ) * Ccg⁻¹ := by
    dsimp only [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcAdmInv : c ≤ (badEventCoarseAdmissibleConstFloor d Ccg)⁻¹ := by
    dsimp only [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Ccg, c, hCcgFloor, hCcg, hcPos, ?_⟩
  intro M m0 E hS hadmSource hEgamma m n hn hNLTM hELLIPGATE z
  have hcstarPos : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hAdmLeCInv : badEventCoarseAdmissibleConstFloor d Ccg ≤ c⁻¹ := by
    rw [le_inv_comm₀ hAdmPos hcPos]
    exact hcAdmInv
  have hCInvLe : c⁻¹ ≤
      (E : ℝ) * Algsuperdiff.Section3.Disorder.cstar M := by
    have hmul := mul_le_mul_of_nonneg_right hadmSource hcstarPos.le
    calc
      c⁻¹ =
          (c⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹) *
            Algsuperdiff.Section3.Disorder.cstar M := by field_simp
      _ ≤ (E : ℝ) * Algsuperdiff.Section3.Disorder.cstar M := hmul
  have hadm : badEventCoarseAdmissibleConstFloor d Ccg ≤
      (E : ℝ) * Algsuperdiff.Section3.Disorder.cstar M :=
    hAdmLeCInv.trans hCInvLe
  have hgammaZ : M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.gamma_le_zpow_neg_five_of_frozenGate
      E.property M.shellPrefix.gamma_pos hEgamma
  have hpower :
      (3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) *
          (3 : ℝ) ^ (scaleGapPos m n) =
        (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hNLTMRate : n < m →
      1 ≤ c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        ((3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) *
          (3 : ℝ) ^ (scaleGapPos m n)) := by
    intro hnm
    have hneg0 : 0 ≤ (3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hmul := mul_le_mul_of_nonneg_right (hNLTM hnm) hneg0
    have hcancel :
        (3 : ℝ) ^ (5 * scaleGapPos n m) *
            (3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show 5 * scaleGapPos n m + -(5 : ℝ) * scaleGapPos n m = 0 by ring]
      exact Real.rpow_zero 3
    calc
      1 = (3 : ℝ) ^ (5 * scaleGapPos n m) *
          (3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) := hcancel.symm
      _ ≤ (c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹) *
          (3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) := hmul
      _ = c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
          ((3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) *
            (3 : ℝ) ^ (scaleGapPos m n)) := by
        rw [scaleGapPos_of_lt hnm, Real.rpow_zero, mul_one]
  have hNLTMCentered : n < m →
      1 ≤ badEventOscFullRate M (2 * Ccg) (originCube d m) n := by
    intro hnm
    have hpow0 : 0 ≤
        (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hrest0 : 0 ≤ Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m) :=
      mul_nonneg
        (mul_nonneg hcstarPos.le (inv_pos.mpr M.shellPrefix.gamma_pos).le) hpow0
    have hcoef := mul_le_mul_of_nonneg_right hcOsc hrest0
    calc
      1 ≤ c * (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m)) := by
        simpa only [hpower, mul_assoc] using hNLTMRate hnm
      _ ≤ badEventOscLowConst d (2 * Ccg) *
          (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m)) := hcoef
      _ = badEventOscFullRate M (2 * Ccg) (originCube d m) n := by
        simp only [badEventOscFullRate, originCube, mul_assoc]
  have hcenter := hcentered M m n m0 E hS hn hadm hgammaZ
    hNLTMCentered hELLIPGATE
  have htransport :
      (cutoffSampleLaw M).toMeasure.real
          (goodLocalEventAt M (2 * Ccg) m n z)ᶜ =
        (cutoffSampleLaw M).toMeasure.real
          (goodLocalEvent M (2 * Ccg) (originCube d m) n)ᶜ := by
    rw [show (goodLocalEventAt M (2 * Ccg) m n z)ᶜ =
        translateCutoffSample z ⁻¹'
          (goodLocalEvent M (2 * Ccg) (originCube d m) n)ᶜ by
      ext omega
      rfl]
    exact
      Algsuperdiff.Section3.Provider.Stream.measureReal_preimage_translateCutoffSample M z
        (measurableSet_goodLocalEvent M (2 * Ccg) (originCube d m) n).compl
  rw [htransport]
  refine hcenter.trans (add_le_add ?_ ?_)
  · have hpow0 : 0 ≤
        (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hrest0 : 0 ≤ Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m) :=
      mul_nonneg
        (mul_nonneg hcstarPos.le (inv_pos.mpr M.shellPrefix.gamma_pos).le) hpow0
    have hcoef := mul_le_mul_of_nonneg_right hcOsc hrest0
    have hrate :
        c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) *
            (3 : ℝ) ^ (scaleGapPos m n) ≤
          badEventOscFullRate M (2 * Ccg) (originCube d m) n := by
      calc
        c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
              (3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) *
              (3 : ℝ) ^ (scaleGapPos m n) =
            c * (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
              ((3 : ℝ) ^ (-(5 : ℝ) * scaleGapPos n m) *
                (3 : ℝ) ^ (scaleGapPos m n))) := by ring
        _ = c * (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
              (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m)) := by
            rw [hpower]
        _ ≤ badEventOscLowConst d (2 * Ccg) *
              (Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
                (3 : ℝ) ^ (scaleGapPos m n - 5 * scaleGapPos n m)) := hcoef
        _ = badEventOscFullRate M (2 * Ccg) (originCube d m) n := by
          simp only [badEventOscFullRate, originCube, mul_assoc]
    exact Real.exp_le_exp.2 (neg_le_neg hrate)
  · have hrare0 : 0 ≤ ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ :=
      mul_nonneg (sq_nonneg _) (inv_pos.mpr M.shellPrefix.gamma_pos).le
    have hcoef := mul_le_mul_of_nonneg_right hcCoeff hrare0
    have hrate :
        c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹ ≤
          (1 / 8 : ℝ) *
            (Ccg⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹) := by
      simpa only [mul_assoc] using hcoef
    exact Real.exp_le_exp.2 (neg_le_neg (Real.exp_le_exp.2 hrate))
