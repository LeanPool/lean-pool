/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.PartialChangeMetric

/-!
# High-contrast homogenization: Entry.Multiscale.Global.PotentialDecreases

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The partial-change and failed-test potential decreases

The remaining two of the four potential decreases of the printed proof — the partial geometry
change and the failed comparison test — together with the initial value of the potential.  They
serve `e.global.selection.partial.change` and `e.global.selection.failed.test`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- `e.global.selection.partial.change`, scalar assembly: metric part as in
`partial_change_metric` (premise `hmet`), profile part by `scalar_span` with `ℓ = h`, constants
by `comparison_choice` (first branch) and `weight_choice`. -/
theorem partial_change_decrease {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (η a c C Q ε δ : ℝ) (m mP : Mat d) (k n : ℤ) (L h : ℕ) (hd : 0 < d)
    (hη : η ∈ Set.Ioc (0 : ℝ) 1) (hC : 1 ≤ C) (hCd : (d : ℝ) ≤ C) (hQ : 0 ≤ Q) (hh : 1 ≤ h)
    (ha1 : 1 ≤ a) (ha : 4 * Q * max 1 C ≤ a * C / d) (_hδ : 0 ≤ δ) (_hε : 0 < ε)
    (hcomp : 1 / 2 * Real.log ((1 + δ) / (1 - δ)) + 2 * C * ((h : ℝ) + 2) * Real.log (1 + δ) ≤ ε
      / 2)
    (hw : Real.log (1 + C * h) + c ≤ a * ε / 2)
    (hmet : projectiveDistance mP
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) (n + L))) -
      projectiveDistance m (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid
        jStar m) k)) ≤
      -ε + 1 / 2 * detIncrement P (Geometry.explicitRoundedGrid jStar m) k (n + 2 * (L : ℤ)) +
        1 / 2 * Real.log ((1 + δ) / (1 - δ)))
    (hx0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n)
    (hxP0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L))
    (hxP1 : profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) ≤ 1)
    (hx'0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L + h) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L + h))
    (hΔ : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar m) k (n + 2 * (L : ℤ)))
    (hΔ' : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar mP) (n + L) (n + L + h))
    (hspan : profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L + h) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L + h) ≤
      C * h *
        (profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) +
          (Real.exp (Q * detIncrement P (Geometry.explicitRoundedGrid jStar mP) (n + L) (n + L +
            h)) - 1))) :
    potential P γ jStar η a mP (n + L) (n + L + h) - potential P γ jStar η a m k n ≤
      -c - 2 * a * C * ((h : ℝ) + 2) * Real.log (1 + δ) +
        a * C / d * (detIncrement P (Geometry.explicitRoundedGrid jStar m) k (n + 2 * (L : ℤ)) +
          detIncrement P (Geometry.explicitRoundedGrid jStar mP) (n + L) (n + L + h)) := by
  unfold potential
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have ha0 : 0 ≤ a := le_trans zero_le_one ha1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set x := profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n with hxdef
  set x0 := profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) with hx0def
  set x' := profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L + h) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L + h) with hx'def
  set Δ := detIncrement P (Geometry.explicitRoundedGrid jStar m) k (n + 2 * (L : ℤ)) with hΔdef
  set Δ' := detIncrement P (Geometry.explicitRoundedGrid jStar mP) (n + L) (n + L + h) with hΔ'def
  set oldDist := projectiveDistance m
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) k)) with
        holdDistdef
  set newDist := projectiveDistance mP
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) (n + L)))
        with hnewDistdef
  set compLog := Real.log ((1 + δ) / (1 - δ)) with hcompLogdef
  set deltaLog := Real.log (1 + δ) with hdeltaLogdef
  have hx0x : 0 ≤ x := by simpa [hxdef] using hx0
  have hx0_nonneg : 0 ≤ x0 := by simpa [hx0def] using hxP0
  have hx0_le_one : x0 ≤ 1 := by simpa [hx0def] using hxP1
  have hx'_nonneg : 0 ≤ x' := by simpa [hx'def] using hx'0
  have hΔ0 : 0 ≤ Δ := by simpa [hΔdef] using hΔ
  have hΔ'0 : 0 ≤ Δ' := by simpa [hΔ'def] using hΔ'
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hspan_x : x' ≤ C * (h : ℝ) *
      (x0 + (Real.exp (Q * Δ') - 1)) := by
    simpa [hx0def, hx'def, hΔ'def, mul_comm, mul_left_comm, mul_assoc] using hspan
  have hscalar :
      η * Real.log (1 + x' / η) ≤ Real.log (1 + C * (h : ℝ)) + Q * Δ' := by
    obtain ⟨hη0, hη1⟩ := hη
    have hℓ0 : (0 : ℝ) ≤ (h : ℝ) := le_trans zero_le_one hhR
    have hCℓ0 : 0 ≤ C * (h : ℝ) := mul_nonneg hC0 hℓ0
    have hηne : η ≠ 0 := hη0.ne'
    have h1 : x' ≤ C * (h : ℝ) * Real.exp (Q * Δ') := by
      calc
        x' ≤ C * (h : ℝ) * (x0 + (Real.exp (Q * Δ') - 1)) := hspan_x
        _ ≤ C * (h : ℝ) * (1 + (Real.exp (Q * Δ') - 1)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hx0_le_one]) hCℓ0
        _ = C * (h : ℝ) * Real.exp (Q * Δ') := by ring
    have h2 : x' / η ≤ C * (h : ℝ) / η * Real.exp (Q * Δ') := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hu0 : (0 : ℝ) ≤ η⁻¹ := inv_nonneg.mpr hη0.le
      calc
        x' * η⁻¹ ≤ (C * (h : ℝ) * Real.exp (Q * Δ')) * η⁻¹ :=
          mul_le_mul_of_nonneg_right h1 hu0
        _ = C * (h : ℝ) * η⁻¹ * Real.exp (Q * Δ') := by ring
    have hexp1 : (1 : ℝ) ≤ Real.exp (Q * Δ') := by
      calc
        (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
        _ ≤ Real.exp (Q * Δ') := Real.exp_le_exp.mpr (mul_nonneg hQ hΔ'0)
    have h3 : 1 + x' / η ≤ (1 + C * (h : ℝ) / η) * Real.exp (Q * Δ') := by
      have expand : (1 + C * (h : ℝ) / η) * Real.exp (Q * Δ')
          = Real.exp (Q * Δ') + C * (h : ℝ) / η * Real.exp (Q * Δ') := by ring
      rw [expand]
      linarith only [h2, hexp1]
    have hpos1 : (0 : ℝ) < 1 + x' / η := by
      have hdiv : 0 ≤ x' / η := div_nonneg hx'_nonneg hη0.le
      linarith only [hdiv]
    have hCℓη0 : (0 : ℝ) ≤ C * (h : ℝ) / η := div_nonneg hCℓ0 hη0.le
    have hpos2 : (0 : ℝ) < 1 + C * (h : ℝ) / η := by linarith only [hCℓη0]
    have h4 : Real.log (1 + x' / η) ≤
        Real.log ((1 + C * (h : ℝ) / η) * Real.exp (Q * Δ')) :=
      Real.log_le_log hpos1 h3
    have hlogmul : Real.log ((1 + C * (h : ℝ) / η) * Real.exp (Q * Δ'))
        = Real.log (1 + C * (h : ℝ) / η) + Q * Δ' := by
      rw [Real.log_mul hpos2.ne' (Real.exp_ne_zero _), Real.log_exp]
    rw [hlogmul] at h4
    have h5 : η * Real.log (1 + x' / η) ≤
        η * (Real.log (1 + C * (h : ℝ) / η) + Q * Δ') :=
      mul_le_mul_of_nonneg_left h4 hη0.le
    have hs : (-1 : ℝ) ≤ C * (h : ℝ) / η := by linarith only [hCℓη0]
    have hbernoulli : (1 + C * (h : ℝ) / η) ^ η ≤
        1 + η * (C * (h : ℝ) / η) :=
      rpow_one_add_le_one_add_mul_self hs hη0.le hη1
    have heq : η * (C * (h : ℝ) / η) = C * (h : ℝ) := by
      field_simp [hηne]
    rw [heq] at hbernoulli
    have h6 : Real.log ((1 + C * (h : ℝ) / η) ^ η) ≤ Real.log (1 + C * (h : ℝ)) :=
      Real.log_le_log (Real.rpow_pos_of_pos hpos2 η) hbernoulli
    have hrpowlog : Real.log ((1 + C * (h : ℝ) / η) ^ η) =
        η * Real.log (1 + C * (h : ℝ) / η) :=
      Real.log_rpow hpos2 η
    rw [hrpowlog] at h6
    have h7 : η * (Q * Δ') ≤ Q * Δ' := by
      exact mul_le_of_le_one_left (mul_nonneg hQ hΔ'0) hη1
    have hexpand5 : η * (Real.log (1 + C * (h : ℝ) / η) + Q * Δ') =
        η * Real.log (1 + C * (h : ℝ) / η) + η * (Q * Δ') := by ring
    rw [hexpand5] at h5
    linarith only [h5, h6, h7]
  have hηpos : 0 < η := hη.1
  have holdScalar_nonneg : 0 ≤ η * Real.log (1 + x / η) := by
    have hxdiv : 0 ≤ x / η := div_nonneg hx0x (le_of_lt hηpos)
    have hlog : 0 ≤ Real.log (1 + x / η) := Real.log_nonneg (by linarith only [hxdiv])
    exact mul_nonneg (le_of_lt hηpos) hlog
  have hmet_named : newDist - oldDist ≤ -ε + 1 / 2 * Δ + 1 / 2 * compLog := by
    simpa [newDist, oldDist, Δ, compLog, hnewDistdef, holdDistdef, hΔdef, hcompLogdef] using hmet
  have hmet_a : a * (newDist - oldDist) ≤ a * (-ε + 1 / 2 * Δ + 1 / 2 * compLog) :=
    mul_le_mul_of_nonneg_left hmet_named ha0
  have hcomp_bound :
      a * (1 / 2 * compLog) ≤ a * (ε / 2 - 2 * C * ((h : ℝ) + 2) * deltaLog) := by
    have hcomp' : 1 / 2 * compLog ≤ ε / 2 - 2 * C * ((h : ℝ) + 2) * deltaLog := by
      have hc : 1 / 2 * compLog + 2 * C * ((h : ℝ) + 2) * deltaLog ≤ ε / 2 := by
        simpa [compLog, deltaLog, hcompLogdef, hdeltaLogdef] using hcomp
      linarith only [hc]
    exact mul_le_mul_of_nonneg_left hcomp' ha0
  have hlog_bound : Real.log (1 + C * (h : ℝ)) ≤ a * ε / 2 - c := by
    linarith only [hw]
  have hQcoef : Q ≤ a * C / d := by
    have hmax : (1 : ℝ) ≤ max 1 C := le_max_left _ _
    have hQle : Q ≤ 4 * Q * max 1 C := by
      calc
        Q = Q * 1 := by ring
        _ ≤ Q * max 1 C := mul_le_mul_of_nonneg_left hmax hQ
        _ ≤ 4 * (Q * max 1 C) :=
          le_mul_of_one_le_left (mul_nonneg hQ (le_trans zero_le_one hmax)) (by norm_num)
        _ = 4 * Q * max 1 C := by ring
    linarith only [hQle, ha]
  have hQΔ' : Q * Δ' ≤ a * C / d * Δ' :=
    mul_le_mul_of_nonneg_right hQcoef hΔ'0
  have hhalfcoef : a * (1 / 2 * Δ) ≤ a * C / d * Δ := by
    have hCd_div : (1 : ℝ) ≤ C / d := by
      rw [le_div_iff₀ hdR]
      simpa using hCd
    have hhalf : (1 / 2 : ℝ) ≤ C / d := by linarith only [hCd_div]
    have hcoef : a * (1 / 2) ≤ a * (C / d) :=
      mul_le_mul_of_nonneg_left hhalf ha0
    calc
      a * (1 / 2 * Δ) = (a * (1 / 2)) * Δ := by ring
      _ ≤ (a * (C / d)) * Δ := mul_le_mul_of_nonneg_right hcoef hΔ0
      _ = a * C / d * Δ := by ring
  change
    η * Real.log (1 + x' / η) + a * newDist -
        (η * Real.log (1 + x / η) + a * oldDist) ≤
      -c - 2 * a * C * ((h : ℝ) + 2) * deltaLog + a * C / d * (Δ + Δ')
  calc
    η * Real.log (1 + x' / η) + a * newDist -
        (η * Real.log (1 + x / η) + a * oldDist)
        = η * Real.log (1 + x' / η) - η * Real.log (1 + x / η) +
            a * (newDist - oldDist) := by ring
    _ ≤ η * Real.log (1 + x' / η) + a * (newDist - oldDist) := by
      linarith only [holdScalar_nonneg]
    _ ≤ (Real.log (1 + C * (h : ℝ)) + Q * Δ') + a * (newDist - oldDist) := by
      linarith only [hscalar]
    _ ≤ (Real.log (1 + C * (h : ℝ)) + Q * Δ') +
        a * (-ε + 1 / 2 * Δ + 1 / 2 * compLog) := by
      exact add_le_add (le_refl _) hmet_a
    _ = Real.log (1 + C * (h : ℝ)) + Q * Δ' +
        (a * (-ε) + a * (1 / 2 * Δ) + a * (1 / 2 * compLog)) := by ring
    _ ≤ Real.log (1 + C * (h : ℝ)) + Q * Δ' +
        (a * (-ε) + a * (1 / 2 * Δ) +
          a * (ε / 2 - 2 * C * ((h : ℝ) + 2) * deltaLog)) := by
      linarith only [hcomp_bound]
    _ ≤ (a * ε / 2 - c) + Q * Δ' +
        (a * (-ε) + a * (1 / 2 * Δ) +
          a * (ε / 2 - 2 * C * ((h : ℝ) + 2) * deltaLog)) := by
      linarith only [hlog_bound]
    _ ≤ (a * ε / 2 - c) + a * C / d * Δ' +
        (a * (-ε) + a * C / d * Δ +
          a * (ε / 2 - 2 * C * ((h : ℝ) + 2) * deltaLog)) := by
      linarith only [hQΔ', hhalfcoef]
    _ = -c - 2 * a * C * ((h : ℝ) + 2) * deltaLog + a * C / d * (Δ + Δ') := by ring

/-- `e.global.selection.failed.test`, scalar assembly: the candidate was reached
(`m₊ = m⋆`), so the new metric term is `≤ ½ log((1+δ)/(1-δ))` by the bridge sandwich; profile
by `scalar_span` with `ℓ = H`; the failed test `Δ' ≥ dσ` absorbs the constants in quarters. -/
theorem failed_test_decrease {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (η a c C Q ε σ δ : ℝ) (m mP : Mat d) (k n : ℤ) (L H h : ℕ) (hd : 0 < d)
    (hη : η ∈ Set.Ioc (0 : ℝ) 1) (hC : 1 ≤ C) (hQ : 0 ≤ Q) (hH : 1 ≤ H) (ha1 : 1 ≤ a)
    (ha : 4 * Q * max 1 C ≤ a * C / d) (hδ : 0 ≤ δ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hσ : 0 < σ)
    (hc : 0 ≤ c) (hlogL : 0 ≤ Real.log (1 + 2 * C * L))
    (hcomp : 1 / 2 * Real.log ((1 + δ) / (1 - δ)) + 2 * C * ((h : ℝ) + 2) * Real.log (1 + δ) ≤
      C * σ / 4)
    (hw : 4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) ≤ a * C * ε * σ)
    (hmet : projectiveDistance mP
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) (n + L))) ≤
      1 / 2 * Real.log ((1 + δ) / (1 - δ)))
    (hold : 0 ≤ projectiveDistance m (explicitCanonicalMetric (adaptedMean P
      (Geometry.explicitRoundedGrid jStar m) k)))
    (hx0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n)
    (hxP0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L))
    (hxP1 : profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) ≤ 1)
    (hx'0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L + H) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L + H))
    (hΔ' : (d : ℝ) * σ ≤ detIncrement P (Geometry.explicitRoundedGrid jStar mP) (n + L) (n + L + H))
    (hspan : profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L + H) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L + H) ≤
      C * H *
        (profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) +
          (Real.exp (Q * detIncrement P (Geometry.explicitRoundedGrid jStar mP) (n + L) (n + L +
            H)) - 1))) :
    potential P γ jStar η a mP (n + L) (n + L + H) - potential P γ jStar η a m k n ≤
      -c - 2 * a * C * ((h : ℝ) + 2) * Real.log (1 + δ) +
        a * C / d * detIncrement P (Geometry.explicitRoundedGrid jStar mP) (n + L) (n + L + H) := by
  unfold potential
  have _hcδUsed := And.intro hc hδ
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have ha0 : 0 ≤ a := le_trans zero_le_one ha1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ0 : 0 ≤ σ := le_of_lt hσ
  set x := profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n with hxdef
  set x0 := profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) with hx0def
  set x' := profile P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L) (n + L + H) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar mP) jStar (n + L + H) with hx'def
  set Δ := detIncrement P (Geometry.explicitRoundedGrid jStar mP) (n + L) (n + L + H) with hΔdef
  set oldDist := projectiveDistance m
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m) k)) with
        holdDistdef
  set newDist := projectiveDistance mP
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar mP) (n + L)))
        with hnewDistdef
  set compLog := Real.log ((1 + δ) / (1 - δ)) with hcompLogdef
  set deltaLog := Real.log (1 + δ) with hdeltaLogdef
  set B := a * C / (d : ℝ) * Δ with hBdef
  have hηpos : 0 < η := hη.1
  have hx_nonneg : 0 ≤ x := by rw [hxdef]; exact hx0
  have hx0_nonneg : 0 ≤ x0 := by rw [hx0def]; exact hxP0
  have hx0_le_one : x0 ≤ 1 := by rw [hx0def]; exact hxP1
  have hx'_nonneg : 0 ≤ x' := by rw [hx'def]; exact hx'0
  have hΔ0 : 0 ≤ Δ := by
    exact le_trans (mul_nonneg hdR.le hσ0) (by rw [hΔdef]; exact hΔ')
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hspan_x : x' ≤ C * (H : ℝ) *
      (x0 + (Real.exp (Q * Δ) - 1)) := by
    simpa [hx0def, hx'def, hΔdef, mul_comm, mul_left_comm, mul_assoc] using hspan
  have hscalar :
      η * Real.log (1 + x' / η) ≤ Real.log (1 + C * (H : ℝ)) + Q * Δ := by
    obtain ⟨hη0, hη1⟩ := hη
    have hH0 : (0 : ℝ) ≤ (H : ℝ) := le_trans zero_le_one hHR
    have hCH0 : 0 ≤ C * (H : ℝ) := mul_nonneg hC0 hH0
    have h1 : x' ≤ C * (H : ℝ) * Real.exp (Q * Δ) := by
      calc
        x' ≤ C * (H : ℝ) * (x0 + (Real.exp (Q * Δ) - 1)) := hspan_x
        _ ≤ C * (H : ℝ) * (1 + (Real.exp (Q * Δ) - 1)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hx0_le_one]) hCH0
        _ = C * (H : ℝ) * Real.exp (Q * Δ) := by ring
    have h2 : x' / η ≤ C * (H : ℝ) / η * Real.exp (Q * Δ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hinv : (0 : ℝ) ≤ η⁻¹ := inv_nonneg.mpr hη0.le
      calc
        x' * η⁻¹ ≤ (C * (H : ℝ) * Real.exp (Q * Δ)) * η⁻¹ :=
          mul_le_mul_of_nonneg_right h1 hinv
        _ = C * (H : ℝ) * η⁻¹ * Real.exp (Q * Δ) := by ring
    have hexp1 : (1 : ℝ) ≤ Real.exp (Q * Δ) := by
      calc
        (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
        _ ≤ Real.exp (Q * Δ) := Real.exp_le_exp.mpr (mul_nonneg hQ hΔ0)
    have h3 : 1 + x' / η ≤ (1 + C * (H : ℝ) / η) * Real.exp (Q * Δ) := by
      have expand : (1 + C * (H : ℝ) / η) * Real.exp (Q * Δ) =
          Real.exp (Q * Δ) + C * (H : ℝ) / η * Real.exp (Q * Δ) := by ring
      rw [expand]
      linarith only [h2, hexp1]
    have hpos1 : (0 : ℝ) < 1 + x' / η := by
      have hdiv : 0 ≤ x' / η := div_nonneg hx'_nonneg hη0.le
      linarith only [hdiv]
    have hCHη0 : (0 : ℝ) ≤ C * (H : ℝ) / η := div_nonneg hCH0 hη0.le
    have hpos2 : (0 : ℝ) < 1 + C * (H : ℝ) / η := by linarith only [hCHη0]
    have h4 : Real.log (1 + x' / η) ≤
        Real.log ((1 + C * (H : ℝ) / η) * Real.exp (Q * Δ)) :=
      Real.log_le_log hpos1 h3
    have hlogmul : Real.log ((1 + C * (H : ℝ) / η) * Real.exp (Q * Δ)) =
        Real.log (1 + C * (H : ℝ) / η) + Q * Δ := by
      rw [Real.log_mul hpos2.ne' (Real.exp_ne_zero _), Real.log_exp]
    rw [hlogmul] at h4
    have h5 : η * Real.log (1 + x' / η) ≤
        η * (Real.log (1 + C * (H : ℝ) / η) + Q * Δ) :=
      mul_le_mul_of_nonneg_left h4 hη0.le
    have hs : (-1 : ℝ) ≤ C * (H : ℝ) / η := by linarith only [hCHη0]
    have hbernoulli : (1 + C * (H : ℝ) / η) ^ η ≤
        1 + η * (C * (H : ℝ) / η) :=
      rpow_one_add_le_one_add_mul_self hs hη0.le hη1
    have heq : η * (C * (H : ℝ) / η) = C * (H : ℝ) := by
      field_simp [hη0.ne']
    rw [heq] at hbernoulli
    have h6 : Real.log ((1 + C * (H : ℝ) / η) ^ η) ≤
        Real.log (1 + C * (H : ℝ)) :=
      Real.log_le_log (Real.rpow_pos_of_pos hpos2 η) hbernoulli
    have hrpowlog : Real.log ((1 + C * (H : ℝ) / η) ^ η) =
        η * Real.log (1 + C * (H : ℝ) / η) :=
      Real.log_rpow hpos2 η
    rw [hrpowlog] at h6
    have h7 : η * (Q * Δ) ≤ Q * Δ :=
      mul_le_of_le_one_left (mul_nonneg hQ hΔ0) hη1
    have hexpand5 : η * (Real.log (1 + C * (H : ℝ) / η) + Q * Δ) =
        η * Real.log (1 + C * (H : ℝ) / η) + η * (Q * Δ) := by ring
    rw [hexpand5] at h5
    linarith only [h5, h6, h7]
  have holdScalar_nonneg : 0 ≤ η * Real.log (1 + x / η) := by
    have hxdiv : 0 ≤ x / η := div_nonneg hx_nonneg hηpos.le
    have hlog : 0 ≤ Real.log (1 + x / η) := Real.log_nonneg (by linarith only [hxdiv])
    exact mul_nonneg hηpos.le hlog
  have holdMetric_nonneg : 0 ≤ a * oldDist := by
    exact mul_nonneg ha0 (by rw [holdDistdef]; exact hold)
  have hmet_a :
      a * newDist ≤ a * (1 / 2 * compLog) := by
    exact mul_le_mul_of_nonneg_left (by rw [hnewDistdef, hcompLogdef]; exact hmet) ha0
  have hcomp_bound :
      a * (1 / 2 * compLog) ≤ a * (C * σ / 4) -
        2 * a * C * ((h : ℝ) + 2) * deltaLog := by
    have hcomp' : 1 / 2 * compLog ≤
        C * σ / 4 - 2 * C * ((h : ℝ) + 2) * deltaLog := by
      have hc' : 1 / 2 * compLog + 2 * C * ((h : ℝ) + 2) * deltaLog ≤ C * σ / 4 := by
        rw [hcompLogdef, hdeltaLogdef]; exact hcomp
      linarith only [hc']
    calc
      a * (1 / 2 * compLog) ≤
          a * (C * σ / 4 - 2 * C * ((h : ℝ) + 2) * deltaLog) :=
        mul_le_mul_of_nonneg_left hcomp' ha0
      _ = a * (C * σ / 4) - 2 * a * C * ((h : ℝ) + 2) * deltaLog := by ring
  have hlogH_bound :
      Real.log (1 + C * (H : ℝ)) ≤ a * C * σ / 4 - c := by
    have hlogH_eps : Real.log (1 + C * (H : ℝ)) ≤ a * C * ε * σ / 4 - c := by
      linarith only [hw, hlogL, hc]
    have hεmul : a * C * ε * σ ≤ a * C * σ := by
      have hcoef : 0 ≤ a * C * σ := mul_nonneg (mul_nonneg ha0 hC0) hσ0
      calc
        a * C * ε * σ = (a * C * σ) * ε := by ring
        _ ≤ (a * C * σ) * 1 := mul_le_mul_of_nonneg_left hε.2 hcoef
        _ = a * C * σ := by ring
    linarith only [hlogH_eps, hεmul]
  have haCσ_le_B : a * C * σ ≤ B := by
    have hcoef : 0 ≤ a * C / (d : ℝ) :=
      div_nonneg (mul_nonneg ha0 hC0) hdR.le
    have hmul : a * C / (d : ℝ) * ((d : ℝ) * σ) ≤ a * C / (d : ℝ) * Δ :=
      mul_le_mul_of_nonneg_left (by rw [hΔdef]; exact hΔ') hcoef
    calc
      a * C * σ = a * C / (d : ℝ) * ((d : ℝ) * σ) := by
        calc
          a * C * σ = (a * C / (d : ℝ) * (d : ℝ)) * σ := by rw [div_mul_cancel₀ (a * C) hdR.ne']
          _ = a * C / (d : ℝ) * ((d : ℝ) * σ) := by rw [mul_assoc]
      _ ≤ a * C / (d : ℝ) * Δ := hmul
      _ = B := by rw [hBdef]
  have hσhalf : a * (C * σ / 4) + a * C * σ / 4 ≤ B / 2 := by
    calc
      a * (C * σ / 4) + a * C * σ / 4 = (a * C * σ) / 2 := by ring
      _ ≤ B / 2 := div_le_div_of_nonneg_right haCσ_le_B (by norm_num)
  have hQpart : Q * Δ ≤ B / 4 := by
    have h4Qnonneg : 0 ≤ 4 * Q := mul_nonneg (by norm_num) hQ
    have htmp : 4 * Q ≤ 4 * Q * max (1 : ℝ) C := by
      calc
        4 * Q = (4 * Q) * 1 := by ring
        _ ≤ (4 * Q) * max (1 : ℝ) C :=
          mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) C) h4Qnonneg
    have h4Q : 4 * Q ≤ a * C / (d : ℝ) := le_trans htmp (by simpa using ha)
    have hmul : 4 * Q * Δ ≤ a * C / (d : ℝ) * Δ :=
      mul_le_mul_of_nonneg_right h4Q hΔ0
    calc
      Q * Δ = (4 * Q * Δ) / 4 := by ring
      _ ≤ (a * C / (d : ℝ) * Δ) / 4 :=
        div_le_div_of_nonneg_right hmul (by norm_num)
      _ = B / 4 := by rw [hBdef]
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (div_nonneg (mul_nonneg ha0 hC0) hdR.le) hΔ0
  change
    η * Real.log (1 + x' / η) + a * newDist -
        (η * Real.log (1 + x / η) + a * oldDist) ≤
      -c - 2 * a * C * ((h : ℝ) + 2) * deltaLog + B
  linarith only [holdScalar_nonneg, holdMetric_nonneg, hscalar, hmet_a, hcomp_bound,
    hlogH_bound, hσhalf, hQpart, hB0]

end

end HCPolySupport.HighContrast.Multiscale
