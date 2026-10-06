/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.RunSteps
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellMeasurability

/-!
# High-contrast homogenization: Entry.Multiscale.Global.RunStepsChange

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The change-of-geometry steps of the run

`R3b` (Alternative 2, `𝔪₊ ≠ 𝔪⋆`) and `R3c` (Alternative 2, `𝔪₊ = 𝔪⋆` with a failed
determinant test) are the two clauses of `SelectionData.Selects` that move the metric. Each
produces a successor run state on the updated metric and a strict decrease of the run gauge by
`c`, the charge and the `2aC(h+2)log(1+δ)` jump of the metric being paid out of the
determinant reserve by the shared bookkeeping `run_gauge_step`. These are the
change-of-geometry alternatives of `p.global.selection`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockLogDet blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Rewriting the left endpoint of a projective distance along an equality of metrics. -/
private theorem pd_rw {d : ℕ} (m m' X : Mat d) (R : ℝ) (heq : m = m')
    (hh : projectiveDistance m' X ≤ R) : projectiveDistance m X ≤ R := by
  rw [heq]; exact hh

/-- The reserve/gauge bookkeeping shared by the two Alt-2 continuing branches: a potential
decrease with a `-2aC(h+2)log(1+δ)` slack and an `aC/d · charge` charge is turned into a
`runGauge` drop of `c`, the charge being paid out of the determinant reserve
(`run_reserve_change` + `run_energy_transfer` at `J = 2d(h+2)log(1+δ)`). -/
private theorem run_gauge_step {d : ℕ} (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hstat : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m mP : Mat d) (hm : m.PosDef) (hmP : mP.PosDef)
    (η a w δ C c charge : ℝ) (h : ℕ) (k n u s t : ℤ)
    (hwdef : w = a * C / d) (hw0 : 0 ≤ w) (hδ : 0 ≤ δ)
    (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) (hwindow : k + (h : ℤ) ≤ n + 1)
    (hnu : n ≤ u) (hks : k ≤ s) (hsht : s + (h : ℤ) ≤ t)
    (hjump : BlockMatLoewnerLE (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) s)
      (blockScale (1 + δ) (adaptedMean P (Geometry.explicitRoundedGrid jStar m) u)))
    (hstep : potential P γ jStar η a mP s t - potential P γ jStar η a m k n ≤
      -c - 2 * a * C * ((h : ℝ) + 2) * Real.log (1 + δ) + a * C / d * charge)
    (hcharge : charge ≤ detIncrement P (Geometry.explicitRoundedGrid jStar m) k u +
      detIncrement P (Geometry.explicitRoundedGrid jStar mP) s t) :
    runGauge P γ jStar η a w h mP s t - runGauge P γ jStar η a w h m k n ≤ -c := by
  let := hP
  have _hur := hur
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hmonoD : ∀ r r' : ℤ, k ≤ r → r ≤ r' →
      blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar m) r') ≤
        blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar m) r) := by
    intro r r' hr hrr'
    have hnn := Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hstat hce jStar hjStar m hm
      r r' (hk.trans hr) hrr'
    unfold detIncrement at hnn
    linarith only [hnn]
  have hmonoD' : ∀ r r' : ℤ, k ≤ r → r ≤ r' →
      blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) r') ≤
        blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) r) := by
    intro r r' hr hrr'
    have hnn := Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hstat hce jStar hjStar mP hmP
      r r' (hk.trans hr) hrr'
    unfold detIncrement at hnn
    linarith only [hnn]
  have hjump' : blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) s) ≤
      blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar m) u) +
        2 * (d : ℝ) * Real.log (1 + δ) :=
    blockLogDet_le_of_sandwich _ _ δ hδ (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _)
      (run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hstat hce jStar hjStar m hm u)
      (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _)
      (run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hstat hce jStar hjStar mP hmP s)
      hjump
  have hres := run_reserve_change
    (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar m) r))
    (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) r))
    h k k n u s t (2 * (d : ℝ) * Real.log (1 + δ)) hmonoD hmonoD' hkn hwindow hnu hks hsht
    hjump'
  have hJ : ((h : ℝ) + 2) * (2 * (d : ℝ) * Real.log (1 + δ)) =
      2 * (d : ℝ) * ((h : ℝ) + 2) * Real.log (1 + δ) := by ring
  rw [hJ] at hres
  have hwJ : w * (2 * (d : ℝ) * ((h : ℝ) + 2) * Real.log (1 + δ)) =
      2 * a * C * ((h : ℝ) + 2) * Real.log (1 + δ) := by
    rw [hwdef]
    field_simp
  have hwc : w * charge = a * C / d * charge := by rw [hwdef]
  have hfinal := run_energy_transfer
    (potential P γ jStar η a m k n) (potential P γ jStar η a mP s t)
    (run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar m) r))
      h k n)
    (run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar mP)
      r)) h s t)
    c w charge (2 * (d : ℝ) * ((h : ℝ) + 2) * Real.log (1 + δ)) hw0
    (by rw [hwJ, hwc]; exact hstep)
    (by unfold detIncrement at hcharge; linarith only [hcharge, hres])
  unfold runGauge
  exact hfinal

/-- **(R3b) Alternative 2, change of geometry with `𝔪₊ ≠ 𝔪⋆`** (`SelectionData.lean`,
`p.global.selection`). One counted step contains the change and the following
length-`h` start-up step, so the target is `partial_change_decrease`
(`PotentialDecreases.lean`). Its premises: `hcomp` is the first branch of
`comparison_choice`'s `min (ε/2) (Cσ/4)` at `δ = √ε σ` (supplied by the `ε` chosen in
`global_run_of_gap`, passed here as `hcomp`); `hw` is `weight_choice_ge_d`; `hmet` is
`partial_change_metric` (`PartialChangeMetric.lean`), whose `hsym`/`hpos`/`hsymP`/
`hposP` are `Recurrence.isSymmetricBlockMat_adaptedMean` + `run_adaptedMean_blockPosDef`, whose
`hmono` is the
annealed order, whose `hbr₁`/`hbr₂` are the bridge sandwich at `δ = √ε σ`
(`Entry.successful_short_bridge`; passed here as `hbr₁`/`hbr₂`), and whose `hfar` is the
case hypothesis `hne`; `hxP1` is the tail clause `honeP`; `hspan` is the Alt-1 start-up
clause of `Selects` applied at the new state `(𝔪₊, n+L, n+L)`, weakened from
`C(x + e^{QΔ} − 1)` to `C·h·(x + e^{QΔ} − 1)` using `1 ≤ S.h`; the nonnegativities are tree
facts. `run_reserve_change` pays the charge and the `2aC(h+2)log(1+δ)` jump out of the
reserve (`run_energy_transfer` with `J = 2d(h+2)log(1+δ)`).
The step carries one hypothesis beyond the printed statement:
`haQ : 4 * bigQ d γ * max 1 C ≤ a * C / d`, the third conjunct of `weight_choice_ge_d`.
The proof uses it to apply `partial_change_decrease`. -/
theorem run_step_change {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (H jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (n₀ : ℤ)
    (a c C w : ℝ) (hC : 1 ≤ C) (hCd : (d : ℝ) ≤ C) (ha1 : 1 ≤ a) (ha : (d : ℝ) ≤ a)
    (hw : w = a * C / d) (hc : c = 1 / 2 * S.eta ε σ * Real.log (16 / 9))
    (hh1 : 1 ≤ S.h) (hL1 : 1 ≤ S.L ε σ)
    (hweight : Real.log (1 + C * (S.h : ℝ)) + c ≤ a * ε / 2)
    (hcomp : 1 / 2 * Real.log ((1 + Real.sqrt ε * σ) / (1 - Real.sqrt ε * σ)) +
        2 * C * ((S.h : ℝ) + 2) * Real.log (1 + Real.sqrt ε * σ) ≤ ε / 2)
    (st : RunState P γ S ε σ B E H jStar n₀)
    (hlt : st.k < st.n)
    (hsmall : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n ≤ S.eta ε σ)
    (hne : geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))) ≠
      explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))))
    (hfar : ε < projectiveDistance st.m
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ)))))
    (hbr₁ : BlockMatLoewnerLE
      (blockScale (1 - Real.sqrt ε * σ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))))
    (hbr₂ : BlockMatLoewnerLE
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)))
      (blockScale (1 + Real.sqrt ε * σ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))))
    (hmono : BlockMatLoewnerLE
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) st.k))
    (honeP : profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar
          (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ)) ≤ 1)
    (heccP : 1 / 2 * Real.log (‖geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ))))‖ *
        ‖(geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))⁻¹‖) ≤
      ε / (S.L ε σ : ℝ) *
        (((st.n : ℝ) + (S.L ε σ : ℝ)) - (jStar : ℝ) -
          (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)))
    (hspan : profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ))
          (st.n + (S.L ε σ : ℤ) + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ) + (S.h : ℤ)) ≤
      C * (S.h : ℝ) *
        (profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
            (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
              (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ))
            (st.n + (S.L ε σ : ℤ)) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
            (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
              (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ)) +
          (Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
              (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
                (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))
              (st.n + (S.L ε σ : ℤ) + (S.h : ℤ))) - 1)))
    (haQ : 4 * (bigQ d γ : ℝ) * max 1 C ≤ a * C / d) :
    ∃ st' : RunState P γ S ε σ B E H jStar n₀,
      st'.m = geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))) ∧
        st'.k = st.n + (S.L ε σ : ℤ) ∧ st'.n = st.n + (S.L ε σ : ℤ) + (S.h : ℤ) ∧
        st'.i = st.i + 1 ∧
        runGauge P γ jStar (S.eta ε σ) a w S.h st'.m st'.k st'.n -
            runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c := by
  classical
  let := hP
  have : NeZero d := ⟨by omega⟩
  have _hγ := hγ
  have _ := ha
  have _ := hc
  have _ := hsmall
  have _ := hne
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨hε0, hεle⟩ := hε
  obtain ⟨hσ0, hσle⟩ := hσ
  obtain ⟨_, heps01⟩ := S.eps0_mem
  obtain ⟨hcpos, _⟩ := S.c_mem
  have hε1 : ε < 1 := lt_of_le_of_lt hεle heps01
  have hσ1 : σ < 1 := lt_of_le_of_lt hσle hε1
  have hsq0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hsq1 : Real.sqrt ε < 1 := by
    have h := Real.sqrt_lt_sqrt hε0.le hε1
    rwa [Real.sqrt_one] at h
  have hδ0 : 0 ≤ Real.sqrt ε * σ := mul_nonneg hsq0 hσ0.le
  have hδ1 : Real.sqrt ε * σ < 1 := by
    calc Real.sqrt ε * σ < 1 * σ := mul_lt_mul_of_pos_right hsq1 hσ0
      _ = σ := one_mul σ
      _ < 1 := hσ1
  have hη0 : 0 < S.eta ε σ := by
    unfold SelectionData.eta
    exact mul_pos (mul_pos hcpos hε0) hσ0
  have hη1 : S.eta ε σ ≤ 1 := selectionData_eta_le_one S ε σ ⟨hε0, hεle⟩ ⟨hσ0, hσle⟩
  have hstk := st.hk
  have hstkn := st.hkn
  have hstgap := st.hgap hlt
  have hstpr := st.hpr
  have hstgen := st.hgen
  have hFsym : IsSymmetricBlockMat
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))) :=
    Recurrence.isSymmetricBlockMat_adaptedMean _ _ _
  have hFpos := run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce jStar hjStar
    st.m st.hm (st.n + 2 * (S.L ε σ : ℤ))
  have hmStar : (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ :
        ℤ)))).PosDef :=
    explicitCanonicalMetric_posDef _ hFsym hFpos
  have hmP : (geometryUpdate ε st.m (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))))).PosDef :=
    Geometry.geometryUpdate_posDef st.hm hmStar ε
  have hmet := partial_change_metric P jStar ε (Real.sqrt ε * σ) st.m st.k st.n (S.L ε σ)
    st.hm hε0 ⟨hδ0, hδ1⟩
    (fun j => Recurrence.isSymmetricBlockMat_adaptedMean _ _ _)
    (fun j => run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce jStar hjStar
      st.m st.hm j)
    (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _)
    (run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce jStar hjStar _ hmP _)
    hmono hfar hbr₁ hbr₂
  have hx0 := profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
    st.m st.hm st.k st.n st.hk st.hkn
  have hxP0 := profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
    _ hmP (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) (by omega) le_rfl
  have hx'0 := profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
    _ hmP (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ) + (S.h : ℤ)) (by omega) (by omega)
  have hΔ := Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
    st.k (st.n + 2 * (S.L ε σ : ℤ)) st.hk (by omega)
  have hΔ' := Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar _ hmP
    (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ) + (S.h : ℤ)) (by omega) (by omega)
  have hpd := partial_change_decrease P γ jStar (S.eta ε σ) a c C (bigQ d γ : ℝ) ε
    (Real.sqrt ε * σ) st.m _ st.k st.n (S.L ε σ) S.h hd0 ⟨hη0, hη1⟩ hC hCd
    (Nat.cast_nonneg _) hh1 ha1 haQ hδ0 hε0 hcomp hweight hmet hx0 hxP0 honeP hx'0 hΔ hΔ'
    hspan
  refine ⟨⟨geometryUpdate ε st.m (explicitCanonicalMetric
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))),
      st.n + (S.L ε σ : ℤ), st.n + (S.L ε σ : ℤ) + (S.h : ℤ), st.i + 1, hmP,
      by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, ?_⟩
  · have h := heccP
    push_cast at h ⊢
    linarith only [h]
  · intro hcon
    exact absurd hcon (by omega)
  · intro _
    exact le_rfl
  · have htri := projectiveDistance_triangle (1 : Mat d) st.m
      (geometryUpdate ε st.m (explicitCanonicalMetric
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))))
      Matrix.PosDef.one st.hm hmP
    have hmv := Geometry.projectiveDistance_geometryUpdate_le st.hm hmStar hε0
    push_cast at hstpr ⊢
    linarith only [htri, hmv, hstpr]
  · have key : (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * (((st.i + 1 : ℕ) : ℤ) + 1)
        = (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((st.i : ℤ) + 1)
          + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) := by push_cast; ring
    have hLnn : (0 : ℤ) ≤ (S.L ε σ : ℤ) := by omega
    have hHnn : (0 : ℤ) ≤ (H : ℤ) := by omega
    linarith only [hstgen, key, hLnn, hHnn]
  · omega
  · exact run_gauge_step hd P γ E Ψ K Src hP hst hur hce jStar hjStar st.m _ st.hm hmP
      (S.eta ε σ) a w (Real.sqrt ε * σ) C c
      (detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.k (st.n + 2 * (S.L ε σ : ℤ)) +
        detIncrement P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))
          (st.n + (S.L ε σ : ℤ) + (S.h : ℤ)))
      S.h st.k st.n (st.n + 2 * (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ))
      (st.n + (S.L ε σ : ℤ) + (S.h : ℤ))
      hw
      (by rw [hw]
          exact div_nonneg (mul_nonneg (by linarith only [ha1] : (0 : ℝ) ≤ a) (by linarith only
            [hC] : (0 : ℝ) ≤ C))
            (Nat.cast_nonneg d))
      hδ0 hstk hstkn (by omega) (by omega) (by omega) le_rfl hbr₂ hpd le_rfl

/-- **(R3c) Alternative 2, `𝔪₊ = 𝔪⋆`, failed test** (`p.global.selection`). The
target is `failed_test_decrease` (`PotentialDecreases.lean`). `hcomp` is the second
branch of `comparison_choice` (`≤ Cσ/4`); `hmet` is the bridge half of
`partial_change_metric` at the reached target (`d_pr(𝔪₊, m(𝐀_{n+L,q₊})) ≤ ½log((1+δ)/(1−δ))`
from `explicitCanonicalMetric_projectiveDistance_le_of_deltaSandwich` and `hbr₁`/`hbr₂`); `hΔ'` is
the
negated stop test through `det_bridge_not_lt`; `hspan` is conjunct 8 of
`fixed_geometry_one_grid_propagation_full` at `h := 2 * bigQ d γ` (premise by `rfl`),
`L := (H : ℤ)`, guard branch `m = n` (here `k' = n'`), with `1 ≤ (H : ℤ)` from `4 ≤ H` —
this branch has **no** `S.h` dependence. `run_reserve_change` again pays the charge.
The step carries two hypotheses beyond the printed statement:
`haQ : 4 * bigQ d γ * max 1 C ≤ a * C / d` (the third conjunct of `weight_choice_ge_d`) and
`hspan`, the conjunct-8 instance of `fixed_geometry_one_grid_propagation_full` spelled at the
statement's own `C` — the theorem Skolemizes its own constant, so the instance cannot be built
from `hsrc`/`hC`. -/
theorem run_step_failed_test {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (H jStar : ℕ) (hH : max 4 S.h ≤ H)
    (hjStar : 2 * d ≤ 3 ^ jStar) (n₀ : ℤ)
    (Csrc : ℝ) (hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
    (a c C w : ℝ) (hC : 1 ≤ C) (ha1 : 1 ≤ a) (ha : (d : ℝ) ≤ a) (hw : w = a * C / d)
    (hc : c = 1 / 2 * S.eta ε σ * Real.log (16 / 9)) (hL1 : 1 ≤ S.L ε σ)
    (hweight : 4 * (Real.log (1 + 2 * C * (S.L ε σ : ℝ)) + Real.log (1 + C * (H : ℝ)) + c) ≤
      a * C * ε * σ)
    (hcomp : 1 / 2 * Real.log ((1 + Real.sqrt ε * σ) / (1 - Real.sqrt ε * σ)) +
        2 * C * ((S.h : ℝ) + 2) * Real.log (1 + Real.sqrt ε * σ) ≤ C * σ / 4)
    (st : RunState P γ S ε σ B E H jStar n₀)
    (hlt : st.k < st.n)
    (hsmall : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n ≤ S.eta ε σ)
    (heq : geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))) =
      explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))))
    (hbr₁ : BlockMatLoewnerLE
      (blockScale (1 - Real.sqrt ε * σ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))))
    (hbr₂ : BlockMatLoewnerLE
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)))
      (blockScale (1 + Real.sqrt ε * σ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))))
    (honeP : profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar
          (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ)) ≤ 1)
    (heccP : 1 / 2 * Real.log (‖geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ))))‖ *
        ‖(geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))⁻¹‖) ≤
      ε / (S.L ε σ : ℝ) *
        (((st.n : ℝ) + (S.L ε σ : ℝ)) - (jStar : ℝ) -
          (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)))
    (htest : ¬ ((d : ℝ)⁻¹ *
      detIncrement P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))
        (st.n + (S.L ε σ : ℤ) + (H : ℤ)) < σ))
    (haQ : 4 * (bigQ d γ : ℝ) * max 1 C ≤ a * C / d)
    (hspan : profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ))
          (st.n + (S.L ε σ : ℤ) + (H : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ) + (H : ℤ)) ≤
      C * (H : ℝ) *
        (profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
            (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
              (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ))
            (st.n + (S.L ε σ : ℤ)) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
            (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
              (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ)) +
          (Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
              (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
                (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))
              (st.n + (S.L ε σ : ℤ) + (H : ℤ))) - 1))) :
    ∃ st' : RunState P γ S ε σ B E H jStar n₀,
      st'.m = geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))) ∧
        st'.k = st.n + (S.L ε σ : ℤ) ∧ st'.n = st.n + (S.L ε σ : ℤ) + (H : ℤ) ∧
        st'.i = st.i + 1 ∧
        runGauge P γ jStar (S.eta ε σ) a w S.h st'.m st'.k st'.n -
            runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c := by
  classical
  let := hP
  have : NeZero d := ⟨by omega⟩
  have _hγ := hγ
  have _ := hsrc
  have _ := ha
  have _ := hsmall
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨hε0, hεle⟩ := hε
  obtain ⟨hσ0, hσle⟩ := hσ
  obtain ⟨_, heps01⟩ := S.eps0_mem
  obtain ⟨hcpos, _⟩ := S.c_mem
  have hε1 : ε < 1 := lt_of_le_of_lt hεle heps01
  have hσ1 : σ < 1 := lt_of_le_of_lt hσle hε1
  have hsq0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hsq1 : Real.sqrt ε < 1 := by
    have h := Real.sqrt_lt_sqrt hε0.le hε1
    rwa [Real.sqrt_one] at h
  have hδ0 : 0 ≤ Real.sqrt ε * σ := mul_nonneg hsq0 hσ0.le
  have hδ1 : Real.sqrt ε * σ < 1 := by
    have h1 := mul_lt_mul_of_pos_right hsq1 hσ0
    rw [one_mul] at h1
    exact h1.trans hσ1
  have hη0 : 0 < S.eta ε σ := by
    unfold SelectionData.eta
    exact mul_pos (mul_pos hcpos hε0) hσ0
  have hη1 : S.eta ε σ ≤ 1 := selectionData_eta_le_one S ε σ ⟨hε0, hεle⟩ ⟨hσ0, hσle⟩
  have hH4 : 4 ≤ H := le_trans (le_max_left 4 S.h) hH
  have hHh : S.h ≤ H := le_trans (le_max_right 4 S.h) hH
  have hstk := st.hk
  have hstkn := st.hkn
  have hstgap := st.hgap hlt
  have hstpr := st.hpr
  have hstgen := st.hgen
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (mul_nonneg (by norm_num) hη0.le)
      (Real.log_nonneg (by norm_num))
  have hlogL : 0 ≤ Real.log (1 + 2 * C * (S.L ε σ : ℝ)) := by
    have hprod : (0 : ℝ) ≤ 2 * C * (S.L ε σ : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hC)) (Nat.cast_nonneg _)
    exact Real.log_nonneg (le_add_of_nonneg_right hprod)
  have hFsym : IsSymmetricBlockMat
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))) :=
    Recurrence.isSymmetricBlockMat_adaptedMean _ _ _
  have hFpos := run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce jStar hjStar
    st.m st.hm (st.n + 2 * (S.L ε σ : ℤ))
  have hmStar : (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ :
        ℤ)))).PosDef :=
    explicitCanonicalMetric_posDef _ hFsym hFpos
  have hmP : (geometryUpdate ε st.m (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))))).PosDef :=
    Geometry.geometryUpdate_posDef st.hm hmStar ε
  have hGpos := run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce jStar hjStar
    _ hmP (st.n + (S.L ε σ : ℤ))
  have hsand := explicitCanonicalMetric_projectiveDistance_le_of_deltaSandwich
    (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))
    (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)))
    (Real.sqrt ε * σ) ⟨hδ0, hδ1⟩ hFsym hFpos (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _)
      hGpos hbr₁ hbr₂
  have hmet := pd_rw _ _ _ _ heq hsand
  have hold : 0 ≤ projectiveDistance st.m
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) st.k)) :=
    Geometry.projectiveDistance_nonneg st.hm
      (explicitCanonicalMetric_posDef _ (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _)
        (run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce jStar hjStar
          st.m st.hm st.k))
  have hx0 := profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
    st.m st.hm st.k st.n st.hk st.hkn
  have hxP0 := profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
    _ hmP (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) (by omega) le_rfl
  have hx'0 := profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
    _ hmP (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ) + (H : ℤ)) (by omega) (by omega)
  have hΔ := Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
    st.k (st.n + 2 * (S.L ε σ : ℤ)) st.hk (by omega)
  have hΔ' := det_bridge_not_lt d hd0 σ _ htest
  have hft := failed_test_decrease P γ jStar (S.eta ε σ) a c C (bigQ d γ : ℝ) ε σ
    (Real.sqrt ε * σ) st.m _ st.k st.n (S.L ε σ) H S.h hd0 ⟨hη0, hη1⟩ hC
    (Nat.cast_nonneg _) (by omega) ha1 haQ hδ0 ⟨hε0, hε1.le⟩ hσ0 hc0 hlogL hcomp hweight
    hmet hold hx0 hxP0 honeP hx'0 hΔ' hspan
  refine ⟨⟨geometryUpdate ε st.m (explicitCanonicalMetric
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))),
      st.n + (S.L ε σ : ℤ), st.n + (S.L ε σ : ℤ) + (H : ℤ), st.i + 1, hmP,
      by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, ?_⟩
  · have h := heccP
    push_cast at h ⊢
    linarith only [h]
  · intro hcon
    exact absurd hcon (by omega)
  · intro _
    omega
  · have htri := projectiveDistance_triangle (1 : Mat d) st.m
      (geometryUpdate ε st.m (explicitCanonicalMetric
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))))
      Matrix.PosDef.one st.hm hmP
    have hmv := Geometry.projectiveDistance_geometryUpdate_le st.hm hmStar hε0
    push_cast at hstpr ⊢
    linarith only [htri, hmv, hstpr]
  · have key : (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * (((st.i + 1 : ℕ) : ℤ) + 1)
        = (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((st.i : ℤ) + 1)
          + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) := by push_cast; ring
    have hLnn : (0 : ℤ) ≤ (S.L ε σ : ℤ) := by omega
    have hhnn : (0 : ℤ) ≤ (S.h : ℤ) := by omega
    linarith only [hstgen, key, hLnn, hhnn]
  · omega
  · exact run_gauge_step hd P γ E Ψ K Src hP hst hur hce jStar hjStar st.m _ st.hm hmP
      (S.eta ε σ) a w (Real.sqrt ε * σ) C c
      (detIncrement P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))
        (st.n + (S.L ε σ : ℤ) + (H : ℤ)))
      S.h st.k st.n (st.n + 2 * (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ))
      (st.n + (S.L ε σ : ℤ) + (H : ℤ))
      hw
      (by rw [hw]
          exact div_nonneg (mul_nonneg (by linarith only [ha1] : (0 : ℝ) ≤ a) (by linarith only
            [hC] : (0 : ℝ) ≤ C))
            (Nat.cast_nonneg d))
      hδ0 hstk hstkn (by omega) (by omega) (by omega) (by omega) hbr₂ hft (by linarith only [hΔ])
end

end HCPolySupport.HighContrast.Multiscale
