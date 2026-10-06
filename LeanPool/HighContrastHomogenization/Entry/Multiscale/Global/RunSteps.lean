/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.RunState

/-!
# High-contrast homogenization: Entry.Multiscale.Global.RunSteps

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The fixed-geometry steps of the run

The three fixed-geometry clauses of `SelectionData.Selects` that keep the metric and the
retained generation `(𝔪, k)` and advance only `n`: `R3a` (Alternative 1, service), `R3e`
(Alternative 3, synchronized) and `R3f` (Alternative 3, long). Each turns its propagation
guard into the potential decrease of the matching one-grid estimate and transfers that
decrease, through the determinant reserve, into a drop of `c` in the run gauge, carrying the
run-state invariants to the successor state. These are the continuing moves of the run whose
stopping output is Proposition `p.global.selection`, and through that proposition they enter
the assembly of Theorem `t.polynomial.entry`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockLogDet)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **(R3a) Alternative 1, service step** (`SelectionData.lean`). The guard supplies
`x > η` and the quarter propagation `x'@(n+h) ≤ x/4 + C Δ̂`;
`potential_step_sub_le_of_quarter_bound`
(`Run.lean`) converts it into the potential decrease with the charge
`a C / d · Δ̂_h(n)`, and `run_reserve_sync` pays that charge out of the reserve, so the
transferred gauge drops by `c`. The nonnegativities `hx'` and `hΔ` are tree facts
(`Annealed.logDetLoss_nonneg`, `profile_add_determinantDrift_nonneg`,
`logDetLoss_le_synchronizedLogDetLoss`). The new state keeps `(m, k)`, so `hecc`, `hm`,
`hpr` transport; `hone`/`hgap` are the tail clauses `hone'`/`hgap'`; `hgen` uses
`S.h ≤ 2L+H+h`. -/
theorem run_step_service {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (H jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (n₀ : ℤ)
    (a c C w : ℝ) (hC : 1 ≤ C) (ha : (d : ℝ) ≤ a) (hw : w = a * C / d)
    (hc : c = 1 / 2 * S.eta ε σ * Real.log (16 / 9))
    (st : RunState P γ S ε σ B E H jStar n₀)
    (hlt : st.k < st.n)
    (hbig : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n > S.eta ε σ)
    (hprop : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k (st.n + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + (S.h : ℤ)) ≤
      1 / 4 * (profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n) +
        C * synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n)
    (hone' : st.k = st.n + (S.h : ℤ) →
      profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + (S.h : ℤ))
          (st.n + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + (S.h : ℤ)) ≤ 1)
    (hgap' : st.k < st.n + (S.h : ℤ) → st.k + (S.h : ℤ) ≤ st.n + (S.h : ℤ)) :
    ∃ st' : RunState P γ S ε σ B E H jStar n₀,
      st'.m = st.m ∧ st'.k = st.k ∧ st'.n = st.n + (S.h : ℤ) ∧ st'.i = st.i + 1 ∧
        runGauge P γ jStar (S.eta ε σ) a w S.h st'.m st'.k st'.n -
            runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c := by
  have _ := hur
  have _ := hγ
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have haR : 0 < a := lt_of_lt_of_le hdR ha
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hwnn : 0 ≤ w := by rw [hw]; positivity
  have hSh_nonneg : (0 : ℤ) ≤ (S.h : ℤ) := Nat.cast_nonneg _
  have hkh : st.k + (S.h : ℤ) ≤ st.n := st.hgap hlt
  have hjn : (jStar : ℤ) ≤ st.n := le_trans st.hk st.hkn
  have hηpos : 0 < S.eta ε σ := by
    unfold SelectionData.eta
    exact mul_pos (mul_pos S.c_mem.1 hε.1) hσ.1
  -- nonnegativity of the synchronized loss
  have hΔ0 : 0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n :=
    synchronizedLogDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      (S.h : ℤ) st.n hSh_nonneg (by linarith only [st.hk, hkh])
  -- nonnegativity of profile + drift at the successor generation
  have hx'0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k
      (st.n + (S.h : ℤ)) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + (S.h : ℤ)) :=
    profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      st.k (st.n + (S.h : ℤ)) st.hk (by linarith only [st.hkn, hSh_nonneg])
  have hstep_raw := potential_step_sub_le_of_quarter_bound P γ jStar (S.eta ε σ) a c C st.m st.k st.n S.h
    hd0 hηpos hC ha hc hbig hx'0 hΔ0 hprop
  -- the transferred-gauge decrease
  have hwArg : 0 ≤ w := hwnn
  have hstepArg : potential P γ jStar (S.eta ε σ) a st.m st.k (st.n + (S.h : ℤ)) -
      potential P γ jStar (S.eta ε σ) a st.m st.k st.n ≤
      -c - w * 0 + w *
        synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n := by
    rw [hw, mul_zero, sub_zero]
    exact hstep_raw
  have hlogDetLoss_nonneg :
      0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n (st.n + (S.h : ℤ)) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      st.n (st.n + (S.h : ℤ)) hjn (by linarith only [hSh_nonneg])
  have hsync := run_reserve_sync P (Geometry.explicitRoundedGrid jStar st.m) S.h st.k st.n
  have hreserveArg : synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n
      - 0 ≤
      run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
          S.h st.k st.n -
        run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
          S.h st.k (st.n + (S.h : ℤ)) := by
    linarith only [hsync, hlogDetLoss_nonneg]
  have hgauge : runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k (st.n + (S.h : ℤ)) -
      runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c := by
    unfold runGauge
    exact run_energy_transfer
      (potential P γ jStar (S.eta ε σ) a st.m st.k st.n)
      (potential P γ jStar (S.eta ε σ) a st.m st.k (st.n + (S.h : ℤ)))
      (run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
        S.h st.k st.n)
      (run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
        S.h st.k (st.n + (S.h : ℤ)))
      c w (synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n) 0
      hwArg hstepArg hreserveArg
  have hkn' : st.k ≤ st.n + (S.h : ℤ) := by linarith only [st.hkn, hSh_nonneg]
  have hpr' : projectiveDistance (1 : Mat d) st.m ≤ ε * (((st.i + 1 : ℕ) : ℝ) + 1) := by
    have h1 := st.hpr
    have hmono : ε * ((st.i : ℝ) + 1) ≤ ε * (((st.i + 1 : ℕ) : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ hε.1.le
      push_cast; linarith only []
    linarith only [h1, hmono]
  have hgen' : st.n + (S.h : ℤ) ≤
      n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * (((st.i + 1 : ℕ) : ℤ) + 1) := by
    have hgen1 := st.hgen
    have hcoef : (0 : ℤ) ≤ 2 * (S.L ε σ : ℤ) + (H : ℤ) := by positivity
    have hcast : (((st.i + 1 : ℕ) : ℤ) + 1) = ((st.i : ℤ) + 1) + 1 := by push_cast; ring
    rw [hcast, mul_add, mul_one]
    linarith only [hgen1, hcoef]
  refine ⟨⟨st.m, st.k, st.n + (S.h : ℤ), st.i + 1, st.hm, st.hk, hkn', st.hecc, hone', hgap',
      hpr', hgen', by omega⟩, rfl, rfl, rfl, rfl, hgauge⟩

/-- **(R3e) Alternative 3, synchronized** (`SelectionData.lean`). `Selects` supplies
only the three guards and no propagation clause; the propagation is conjunct 6 of
`Entry.fixed_geometry_one_grid_propagation_full` instantiated at `h := S.h`, which needs
`hh : 2 * bigQ d γ ≤ S.h` (**conjunct C1 of `Selects`**), `L := 1`, `n := st.k`, `m := st.n`, with
`st.k + S.h ≤ st.n` from `st.hgap` and the source threshold
`⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ)`. Its
shape `1/8·e^{QΔ̂}·x + C(e^{QΔ̂} − 1)` is exactly `potential_step_sub_le_of_exp_bound.hprop`, so
the target here
is `potential_step_sub_le_of_exp_bound` (`Containment.lean`), not the quarter variant. The charge
`aC/d·Δ̂` is paid by `run_reserve_sync`. The state transition is as in `R3a`. -/
theorem run_step_sync {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (H jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (n₀ : ℤ)
    (hh : 2 * bigQ d γ ≤ S.h)
    (Csrc : ℝ) (hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
    (Cone : ℝ) (hCone : 0 < Cone)
    (hprop1 : ∀ (metric : Mat d), metric.PosDef → ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
      n + (S.h : ℤ) ≤ m →
        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (S.h : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar (m + (S.h : ℤ)) ≤
          1 / 8 * Real.exp ((bigQ d γ : ℝ) *
                synchCharge P (Geometry.explicitRoundedGrid jStar metric) (S.h : ℤ) m) *
              (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m) +
            Cone * (Real.exp ((bigQ d γ : ℝ) *
              synchCharge P (Geometry.explicitRoundedGrid jStar metric) (S.h : ℤ) m) - 1))
    (a c C w : ℝ) (hC : 1 ≤ C) (hCone' : Cone ≤ C) (ha : (d : ℝ) ≤ a) (hw : w = a * C / d)
    (hweight : 4 * (bigQ d γ : ℝ) * max 1 C ≤ a * C / d)
    (hc : c = 1 / 2 * S.eta ε σ * Real.log (16 / 9))
    (st : RunState P γ S ε σ B E H jStar n₀)
    (hlt : st.k < st.n)
    (hbig : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n > S.eta ε σ)
    (hobst : (d : ℝ)⁻¹ *
      synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n > σ)
    (hone' : st.k = st.n + (S.h : ℤ) →
      profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + (S.h : ℤ))
          (st.n + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + (S.h : ℤ)) ≤ 1)
    (hgap' : st.k < st.n + (S.h : ℤ) → st.k + (S.h : ℤ) ≤ st.n + (S.h : ℤ)) :
    ∃ st' : RunState P γ S ε σ B E H jStar n₀,
      st'.m = st.m ∧ st'.k = st.k ∧ st'.n = st.n + (S.h : ℤ) ∧ st'.i = st.i + 1 ∧
        runGauge P γ jStar (S.eta ε σ) a w S.h st'.m st'.k st'.n -
            runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c := by
  have _ := hur
  have _ := hh
  have _ := hsrc
  have _ := hCone
  have _ := hobst
  have _ := hγ
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have haR : 0 < a := lt_of_lt_of_le hdR ha
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hwnn : 0 ≤ w := by rw [hw]; positivity
  have hSh_nonneg : (0 : ℤ) ≤ (S.h : ℤ) := Nat.cast_nonneg _
  have hkh : st.k + (S.h : ℤ) ≤ st.n := st.hgap hlt
  have hjn : (jStar : ℤ) ≤ st.n := le_trans st.hk st.hkn
  have hQnonneg : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  have hηpos : 0 < S.eta ε σ := by
    unfold SelectionData.eta
    exact mul_pos (mul_pos S.c_mem.1 hε.1) hσ.1
  have hΔ0 : 0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n :=
    synchronizedLogDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      (S.h : ℤ) st.n hSh_nonneg (by linarith only [st.hk, hkh])
  have hx'0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k
      (st.n + (S.h : ℤ)) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + (S.h : ℤ)) :=
    profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      st.k (st.n + (S.h : ℤ)) st.hk (by linarith only [st.hkn, hSh_nonneg])
  have hexpnn : 0 ≤ Real.exp ((bigQ d γ : ℝ) *
      synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n) - 1 := by
    have := Real.one_le_exp (mul_nonneg hQnonneg hΔ0)
    linarith only [this]
  have hprop1' := hprop1 st.m st.hm st.k st.n st.hk st.hkn hkh
  have hpropC : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k (st.n + (S.h : ℤ)) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + (S.h : ℤ)) ≤
      1 / 8 * Real.exp ((bigQ d γ : ℝ) *
            synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n) *
          (profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n) +
        C * (Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n) - 1) := by
    have h2 : Cone * (Real.exp ((bigQ d γ : ℝ) *
        synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n) - 1) ≤
        C * (Real.exp ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n) - 1) :=
      mul_le_mul_of_nonneg_right hCone' hexpnn
    linarith only [hprop1', h2]
  have hstep_raw := potential_step_sub_le_of_exp_bound P γ jStar (S.eta ε σ) a c C (bigQ d γ : ℝ) st.m st.k st.n
    S.h hd0 ⟨hηpos, selectionData_eta_le_one S ε σ hε hσ⟩ hC hQnonneg hweight hc hbig hx'0
    hΔ0 hpropC
  have hstepArg : potential P γ jStar (S.eta ε σ) a st.m st.k (st.n + (S.h : ℤ)) -
      potential P γ jStar (S.eta ε σ) a st.m st.k st.n ≤
      -c - w * 0 + w *
        synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n := by
    rw [hw, mul_zero, sub_zero]
    exact hstep_raw
  have hlogDetLoss_nonneg :
      0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n (st.n + (S.h : ℤ)) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      st.n (st.n + (S.h : ℤ)) hjn (by linarith only [hSh_nonneg])
  have hsync := run_reserve_sync P (Geometry.explicitRoundedGrid jStar st.m) S.h st.k st.n
  have hreserveArg : synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n
      - 0 ≤
      run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
          S.h st.k st.n -
        run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
          S.h st.k (st.n + (S.h : ℤ)) := by
    linarith only [hsync, hlogDetLoss_nonneg]
  have hgauge : runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k (st.n + (S.h : ℤ)) -
      runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c := by
    unfold runGauge
    exact run_energy_transfer
      (potential P γ jStar (S.eta ε σ) a st.m st.k st.n)
      (potential P γ jStar (S.eta ε σ) a st.m st.k (st.n + (S.h : ℤ)))
      (run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
        S.h st.k st.n)
      (run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
        S.h st.k (st.n + (S.h : ℤ)))
      c w (synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n) 0
      hwnn hstepArg hreserveArg
  have hkn' : st.k ≤ st.n + (S.h : ℤ) := by linarith only [st.hkn, hSh_nonneg]
  have hpr' : projectiveDistance (1 : Mat d) st.m ≤ ε * (((st.i + 1 : ℕ) : ℝ) + 1) := by
    have h1 := st.hpr
    have hmono : ε * ((st.i : ℝ) + 1) ≤ ε * (((st.i + 1 : ℕ) : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ hε.1.le
      push_cast; linarith only []
    linarith only [h1, hmono]
  have hgen' : st.n + (S.h : ℤ) ≤
      n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * (((st.i + 1 : ℕ) : ℤ) + 1) := by
    have hgen1 := st.hgen
    have hcoef : (0 : ℤ) ≤ 2 * (S.L ε σ : ℤ) + (H : ℤ) := by positivity
    have hcast : (((st.i + 1 : ℕ) : ℤ) + 1) = ((st.i : ℤ) + 1) + 1 := by push_cast; ring
    rw [hcast, mul_add, mul_one]
    linarith only [hgen1, hcoef]
  refine ⟨⟨st.m, st.k, st.n + (S.h : ℤ), st.i + 1, st.hm, st.hk, hkn', st.hecc, hone', hgap',
      hpr', hgen', by omega⟩, rfl, rfl, rfl, rfl, hgauge⟩

/-- **(R3f) Alternative 3, long** (`SelectionData.lean`). Target:
`long_step_decrease` (`Containment.lean`). `hΔ` is the guard through
`det_bridge_gt`; `hx1 : x ≤ 1` is the guard `x ≤ S.eta ε σ` through
`selectionData_eta_le_one`; `hL : 1 ≤ L` is conjunct C2a of `Selects`, the binder `hL1`; `hw`, `ha`,
`hlogH` are `weight_choice_ge_d`; `hspan` is conjunct 3 (or 8) of
`fixed_geometry_one_grid_propagation_full` at `h := S.h` — which needs `hh : 2 * bigQ d γ ≤ S.h`
(**conjunct C1 of `Selects`**: the alternatives only give `k + S.h ≤ n`, while the supplier's
guard is `k + 2 * bigQ d γ ≤ n`) — with `L := 2 * (S.L ε σ : ℤ)`. The charge
`aC/d·Δ_{n,n+2L}` is paid by `run_reserve_advance`. The state keeps `(m, k)` and advances
`n` by `2L`.
The binder `haQ : 4 * bigQ d γ * max 1 C ≤ a * C / d` is the third conjunct of
`weight_choice_ge_d`. -/
theorem run_step_long {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (H jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (n₀ : ℤ)
    (hh : 2 * bigQ d γ ≤ S.h) (hL1 : 1 ≤ S.L ε σ)
    (a c C w : ℝ) (hC : 1 ≤ C) (ha1 : 1 ≤ a) (ha : (d : ℝ) ≤ a) (hw : w = a * C / d)
    (hc : c = 1 / 2 * S.eta ε σ * Real.log (16 / 9))
    (haQ : 4 * (bigQ d γ : ℝ) * max 1 C ≤ a * C / d)
    (hweight : 4 * (Real.log (1 + 2 * C * (S.L ε σ : ℝ)) + Real.log (1 + C * (H : ℝ)) + c) ≤
      a * C * ε * σ)
    (hlogH : 0 ≤ Real.log (1 + C * (H : ℝ)))
    (st : RunState P γ S ε σ B E H jStar n₀)
    (hlt : st.k < st.n)
    (hsmall : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n ≤ S.eta ε σ)
    (hobst : (d : ℝ)⁻¹ * detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n
      (st.n + 2 * (S.L ε σ : ℤ)) > ε * σ)
    (hspan : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k
          (st.n + 2 * (S.L ε σ : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar
          (st.n + 2 * (S.L ε σ : ℤ)) ≤
      C * (2 * (S.L ε σ : ℝ)) *
        (profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n +
          (Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n
              (st.n + 2 * (S.L ε σ : ℤ))) - 1)))
    (hone' : st.k = st.n + 2 * (S.L ε σ : ℤ) →
      profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar (st.n + 2 * (S.L ε σ : ℤ))
          (st.n + 2 * (S.L ε σ : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar
          (st.n + 2 * (S.L ε σ : ℤ)) ≤ 1)
    (hgap' : st.k < st.n + 2 * (S.L ε σ : ℤ) →
      st.k + (S.h : ℤ) ≤ st.n + 2 * (S.L ε σ : ℤ)) :
    ∃ st' : RunState P γ S ε σ B E H jStar n₀,
      st'.m = st.m ∧ st'.k = st.k ∧ st'.n = st.n + 2 * (S.L ε σ : ℤ) ∧ st'.i = st.i + 1 ∧
        runGauge P γ jStar (S.eta ε σ) a w S.h st'.m st'.k st'.n -
            runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c := by
  have _ := hur
  have _ := hh
  have _ := hγ
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have haR : 0 < a := lt_of_lt_of_le hdR ha
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hwnn : 0 ≤ w := by rw [hw]; positivity
  have hηpos : 0 < S.eta ε σ := by
    unfold SelectionData.eta
    exact mul_pos (mul_pos S.c_mem.1 hε.1) hσ.1
  have hetale1 : S.eta ε σ ≤ 1 := selectionData_eta_le_one S ε σ hε hσ
  have hlog169 : 0 < Real.log (16 / 9 : ℝ) := Real.log_pos (by norm_num)
  have hcnonneg : 0 ≤ c := by rw [hc]; positivity
  have hQnonneg : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℤ) ≤ 2 * (S.L ε σ : ℤ) := by positivity
  have hjn : (jStar : ℤ) ≤ st.n := le_trans st.hk st.hkn
  have hkh : st.k + (S.h : ℤ) ≤ st.n := st.hgap hlt
  -- entry nonnegativities/bounds for `long_step_decrease`
  have hx0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n :=
    profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      st.k st.n st.hk st.hkn
  have hx1 : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n ≤ 1 :=
    le_trans hsmall hetale1
  have hkn2 : st.k ≤ st.n + 2 * (S.L ε σ : ℤ) := by linarith only [st.hkn, hL0]
  have hx'0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k
      (st.n + 2 * (S.L ε σ : ℤ)) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar
        (st.n + 2 * (S.L ε σ : ℤ)) :=
    profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      st.k (st.n + 2 * (S.L ε σ : ℤ)) st.hk hkn2
  have hΔlt : (d : ℝ) * ε * σ <
      detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n (st.n + 2 * (S.L ε σ : ℤ)) :=
    det_bridge_gt d hd0 ε σ _ hobst
  have hstep_raw := long_step_decrease P γ jStar (S.eta ε σ) a c C (bigQ d γ : ℝ) ε σ
    (H : ℝ) st.m st.k st.n (S.L ε σ) hd0 ⟨hηpos, hetale1⟩ hC hQnonneg hL1 hcnonneg hε.1 hσ.1
    ha1 haQ hweight hlogH hx0 hx1 hx'0 hΔlt hspan
  -- transferred-gauge decrease via the reserve
  have hstepArg : potential P γ jStar (S.eta ε σ) a st.m st.k (st.n + 2 * (S.L ε σ : ℤ)) -
      potential P γ jStar (S.eta ε σ) a st.m st.k st.n ≤
      -c - w * 0 + w *
        detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n
          (st.n + 2 * (S.L ε σ : ℤ)) := by
    rw [hw, mul_zero, sub_zero]
    exact hstep_raw
  have hmono : ∀ r s : ℤ, (jStar : ℤ) ≤ r → r ≤ s →
      blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) s) ≤
        blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r) := by
    intro r s hr hrs
    have hnn := Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar st.m st.hm
      r s hr hrs
    unfold detIncrement at hnn
    linarith only [hnn]
  have hadv := run_reserve_advance
    (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r)) S.h
    (jStar : ℤ) st.k st.n (st.n + 2 * (S.L ε σ : ℤ)) hmono hjn (by linarith only [hkh, st.hk])
    (by linarith only [hL0])
  have hreserveArg : detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n
      (st.n + 2 * (S.L ε σ : ℤ)) - 0 ≤
      run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
          S.h st.k st.n -
        run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
          S.h st.k (st.n + 2 * (S.L ε σ : ℤ)) := by
    have heq : detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n
        (st.n + 2 * (S.L ε σ : ℤ)) =
        blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) st.n) -
          blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ))) := rfl
    rw [heq]
    simpa using hadv
  have hgauge : runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k
      (st.n + 2 * (S.L ε σ : ℤ)) -
      runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c := by
    unfold runGauge
    exact run_energy_transfer
      (potential P γ jStar (S.eta ε σ) a st.m st.k st.n)
      (potential P γ jStar (S.eta ε σ) a st.m st.k (st.n + 2 * (S.L ε σ : ℤ)))
      (run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
        S.h st.k st.n)
      (run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) r))
        S.h st.k (st.n + 2 * (S.L ε σ : ℤ)))
      c w (detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n
        (st.n + 2 * (S.L ε σ : ℤ))) 0
      hwnn hstepArg hreserveArg
  have hpr' : projectiveDistance (1 : Mat d) st.m ≤ ε * (((st.i + 1 : ℕ) : ℝ) + 1) := by
    have h1 := st.hpr
    have hmono2 : ε * ((st.i : ℝ) + 1) ≤ ε * (((st.i + 1 : ℕ) : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ hε.1.le
      push_cast; linarith only []
    linarith only [h1, hmono2]
  have hgen' : st.n + 2 * (S.L ε σ : ℤ) ≤
      n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * (((st.i + 1 : ℕ) : ℤ) + 1) := by
    have hgen1 := st.hgen
    have hcoef : (0 : ℤ) ≤ (H : ℤ) + (S.h : ℤ) := by positivity
    have hcast : (((st.i + 1 : ℕ) : ℤ) + 1) = ((st.i : ℤ) + 1) + 1 := by push_cast; ring
    rw [hcast, mul_add, mul_one]
    linarith only [hgen1, hcoef]
  refine ⟨⟨st.m, st.k, st.n + 2 * (S.L ε σ : ℤ), st.i + 1, st.hm, st.hk, hkn2, st.hecc, hone',
      hgap', hpr', hgen', by omega⟩, rfl, rfl, rfl, rfl, hgauge⟩
end

end HCPolySupport.HighContrast.Multiscale
