/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.KickArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Tail.TailSqrt

/-!
# KickSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The clamp split of a two-term `(Γ₂, Γ_{1/2})` display

This module supplies the decomposition that meets both demands at once.  Given a
nonnegative `X` with a two-term display `X ≤ 𝒪_{Γ₂}(A₁) + 𝒪_{Γ_{1/2}}(A₂)`, the
two legs are the **clamp** and the **overshoot** at the deterministic threshold

```
lam := 8 A₁ ρ ,      ρ := (A₁/A₂)^{1/3}  (equivalently ρ³A₂ = A₁) ,
min(X, lam) ≤ 𝒪_{Γ₂}(8A₁) ,      X − min(X, lam) ≤ 𝒪_{Γ_{1/2}}(8A₂) .
```

Both legs are measurable functions of `X` alone, so they inherit verbatim every
independence property of `X`: this is what makes provable rather than assumed.
A split built from the two `Γ`-witnesses of the display instead would lose it,
because the witnesses are supplied by the Section 3 anchor as bare existentials
with no locality.

## Why the threshold is at `(A₁/A₂)^{1/3}`

`ρ` is the crossover of the two tails, and the exponent `1/3` is forced.  The
`Γ₂` leg needs the `Γ_{1/2}` witness to be negligible on levels below `lam`,
which costs `√(A₁/A₂ · t) ≥ t²` for `t ≤ ρ`, i.e. `ρ³ ≥ ρ⁴/ρ`; the `Γ_{1/2}` leg
needs the `Γ₂` witness to be negligible on levels above `lam`, which costs
`(lam/A₁)² ≥ √t` for `t` up to `ρ⁴`.  The two demands meet exactly at
`ρ ≍ (A₁/A₂)^{1/3}`; the numerical factor `8` is what makes both hold with room
to spare, and the proof below exhibits that room (`15 t² ≥ log 2` and
`15 √t ≥ log 2`).

## Main results

* `isBigOWith_min_of_isTwoTermBigOWith` — the `Γ₂` leg.
* `isBigOWith_sub_min_of_isTwoTermBigOWith` — the `Γ_{1/2}` leg.

`ρ` is a free parameter constrained only by `ρ³A₂ = A₁`, so no root is ever
formed: the caller supplies `ρ` (in `KickTails.lean`, as `(A₁/A₂)^{1/3}`).

## Scope

Carrier-free: generic in the measure space.

## References

* ABK26, `l.minimal.scale.sep`, Step 1.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open MeasureTheory
open HCPolySupport HCPolySupport.IndependentSums
open Algsuperdiff.Section3

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## `rpow` bookkeeping at the two Orlicz indices -/

theorem rpow_two_eq (t : ℝ) : t ^ (2 : ℝ) = t ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

theorem rpow_half_eq (t : ℝ) : t ^ (1 / 2 : ℝ) = Real.sqrt t :=
  (Real.sqrt_eq_rpow t).symm

theorem one_le_sqrt_of_one_le {t : ℝ} (ht : 1 ≤ t) : 1 ≤ Real.sqrt t := by
  have h := Real.sqrt_le_sqrt ht
  rwa [Real.sqrt_one] at h

theorem sqrt_four_mul (t : ℝ) : Real.sqrt (4 * t) = 2 * Real.sqrt t := by
  rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-! ## The `Γ₂` leg: the clamp -/

/-- **The `Γ₂` leg `X^{(1)} = min(X, 8A₁ρ)`.**  Below the threshold the `Γ_{1/2}`
witness is negligible against a `Γ₂` tail, and above it the clamp makes the
tail event empty. -/
theorem isBigOWith_min_of_isTwoTermBigOWith {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → ℝ} {A1 A2 rho : ℝ} (hratio : rho ^ 3 * A2 = A1)
    (hX : Probability.IsTwoTermBigOWith mu (gammaSigma 2) (gammaSigma (1 / 2)) X A1 A2) :
    IsBigOWith mu (gammaSigma 2) (fun omega => min (X omega) (8 * A1 * rho)) (8 * A1) := by
  obtain ⟨Y, Z, -, -, hA1, hA2, -, -, -, hdom, hYt, hZt⟩ := hX
  rw [isBigOWith_gammaSigma_iff] at hYt hZt ⊢
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have ht2 : (1 : ℝ) ≤ t ^ 2 := one_le_pow₀ ht
  have hlog2 := log_two_le_one
  rw [rpow_two_eq]
  rcases le_or_gt (8 * A1 * rho) (8 * A1 * t) with hcase | hcase
  · have hempty :
        upperTailEvent (fun omega => min (X omega) (8 * A1 * rho)) (8 * A1 * t) = ∅ := by
      ext omega
      simp only [Set.mem_empty_iff_false, iff_false, mem_upperTailEvent, not_lt]
      exact le_trans (min_le_right _ _) hcase
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  · have hA10 : (0 : ℝ) < 8 * A1 := by linarith only [hA1]
    have hrt : t < rho := lt_of_mul_lt_mul_left hcase hA10.le
    have hrho1 : (1 : ℝ) ≤ rho := le_trans ht hrt.le
    -- the union bound
    have hsub :
        upperTailEvent (fun omega => min (X omega) (8 * A1 * rho)) (8 * A1 * t)
          ⊆ upperTailEvent Y (A1 * (4 * t))
            ∪ upperTailEvent Z (A2 * (4 * rho ^ 3 * t)) := by
      intro omega homega
      have hX8 : 8 * A1 * t < X omega := lt_of_lt_of_le homega (min_le_left _ _)
      have hYZ : 8 * A1 * t < Y omega + Z omega := lt_of_lt_of_le hX8 (hdom omega)
      rcases le_or_gt (Y omega) (A1 * (4 * t)) with hY | hY
      · refine Set.mem_union_right _ ?_
        change A2 * (4 * rho ^ 3 * t) < Z omega
        have heq : A2 * (4 * rho ^ 3 * t) = A1 * (4 * t) := by
          rw [← hratio]; ring
        rw [heq]
        linarith only [hYZ, hY]
      · exact Set.mem_union_left _ hY
    have hmeas :
        mu.real (upperTailEvent (fun omega => min (X omega) (8 * A1 * rho)) (8 * A1 * t))
          ≤ mu.real (upperTailEvent Y (A1 * (4 * t)))
            + mu.real (upperTailEvent Z (A2 * (4 * rho ^ 3 * t))) :=
      le_trans (measureReal_mono hsub (measure_ne_top _ _)) (measureReal_union_le _ _)
    -- the two tails
    have hYb := hYt (show (1 : ℝ) ≤ 4 * t from by linarith only [ht])
    have hZarg : (1 : ℝ) ≤ 4 * rho ^ 3 * t := by
      have h1 : (1 : ℝ) ≤ rho ^ 3 := one_le_pow₀ hrho1
      have h2 : (1 : ℝ) ≤ rho ^ 3 * t := one_le_mul_of_one_le_of_one_le h1 ht
      linarith only [h2]
    have hZb := hZt hZarg
    rw [rpow_two_eq] at hYb
    rw [rpow_half_eq] at hZb
    -- the crossover: `√(4ρ³t) ≥ 2t²` because `ρ ≥ t ≥ 1`
    have hbig : 2 * t ^ 2 ≤ Real.sqrt (4 * rho ^ 3 * t) := by
      have hp : t ^ 3 ≤ rho ^ 3 := pow_le_pow_left₀ ht0 hrt.le 3
      have hmul : t ^ 3 * t ≤ rho ^ 3 * t := mul_le_mul_of_nonneg_right hp ht0
      have h4 : (2 * t ^ 2) ^ 2 ≤ 4 * rho ^ 3 * t := by
        calc (2 * t ^ 2) ^ 2 = 4 * (t ^ 3 * t) := by ring
          _ ≤ 4 * (rho ^ 3 * t) := by linarith only [hmul]
          _ = 4 * rho ^ 3 * t := by ring
      have h5 := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq (by positivity)] at h5
    have hh1 : Real.exp (-((4 * t) ^ 2)) ≤ Real.exp (-(t ^ 2)) / 2 := by
      refine exp_neg_le_half_exp_neg ?_
      have hexp : (4 * t) ^ 2 = 16 * t ^ 2 := by ring
      rw [hexp]
      linarith only [ht2, hlog2]
    have hh2 : Real.exp (-Real.sqrt (4 * rho ^ 3 * t)) ≤ Real.exp (-(t ^ 2)) / 2 := by
      refine exp_neg_le_half_exp_neg ?_
      linarith only [hbig, ht2, hlog2]
    calc mu.real
          (upperTailEvent (fun omega => min (X omega) (8 * A1 * rho)) (8 * A1 * t))
        ≤ mu.real (upperTailEvent Y (A1 * (4 * t)))
            + mu.real (upperTailEvent Z (A2 * (4 * rho ^ 3 * t))) := hmeas
      _ ≤ Real.exp (-(t ^ 2)) / 2 + Real.exp (-(t ^ 2)) / 2 :=
          add_le_add (hYb.trans hh1) (hZb.trans hh2)
      _ = Real.exp (-(t ^ 2)) := by ring

/-! ## The `Γ_{1/2}` leg: the overshoot -/

/-- **The `Γ_{1/2}` leg `X^{(2)} = X − min(X, 8A₁ρ)`.**  Above the threshold the
`Γ₂` witness is negligible against a `Γ_{1/2}` tail: at levels below `ρ⁴` the
constant part `4ρ` of the normalized level already dominates `√t`, and above
`ρ⁴` the growing part `4t/ρ³` does. -/
theorem isBigOWith_sub_min_of_isTwoTermBigOWith {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → ℝ} {A1 A2 rho : ℝ} (hrho : 0 < rho) (hratio : rho ^ 3 * A2 = A1)
    (hX : Probability.IsTwoTermBigOWith mu (gammaSigma 2) (gammaSigma (1 / 2)) X A1 A2) :
    IsBigOWith mu (gammaSigma (1 / 2))
      (fun omega => X omega - min (X omega) (8 * A1 * rho)) (8 * A2) := by
  obtain ⟨Y, Z, -, -, hA1, hA2, -, -, -, hdom, hYt, hZt⟩ := hX
  rw [isBigOWith_gammaSigma_iff] at hYt hZt ⊢
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hrho3 : (0 : ℝ) < rho ^ 3 := pow_pos hrho 3
  have hrhone : rho ≠ 0 := ne_of_gt hrho
  have hsqt : (1 : ℝ) ≤ Real.sqrt t := one_le_sqrt_of_one_le ht
  have hlog2 := log_two_le_one
  rw [rpow_half_eq]
  -- the two normalized levels of the half-way point `4A₁ρ + 4A₂t`
  have hAY : A1 * (4 * t / rho ^ 3 + 4 * rho) = 4 * A1 * rho + 4 * A2 * t := by
    rw [← hratio]
    field_simp
    ring
  have hAZ : A2 * (4 * t + 4 * rho ^ 4) = 4 * A1 * rho + 4 * A2 * t := by
    rw [← hratio]
    ring
  have hsub :
      upperTailEvent (fun omega => X omega - min (X omega) (8 * A1 * rho)) (8 * A2 * t)
        ⊆ upperTailEvent Y (A1 * (4 * t / rho ^ 3 + 4 * rho))
          ∪ upperTailEvent Z (A2 * (4 * t + 4 * rho ^ 4)) := by
    intro omega homega
    have hc0 : (0 : ℝ) < 8 * A2 * t := by
      have h1 : (0 : ℝ) < 8 * A2 := by linarith only [hA2]
      have h2 : (0 : ℝ) < 8 * A2 * 1 := by linarith only [h1]
      calc (0 : ℝ) < 8 * A2 * 1 := h2
        _ ≤ 8 * A2 * t := mul_le_mul_of_nonneg_left ht h1.le
    have hlt : 8 * A2 * t < X omega - min (X omega) (8 * A1 * rho) := homega
    have hXbig : 8 * A1 * rho + 8 * A2 * t < X omega := by
      rcases le_total (X omega) (8 * A1 * rho) with hle | hle
      · rw [min_eq_left hle] at hlt
        exact absurd hlt (by linarith only [hc0])
      · rw [min_eq_right hle] at hlt
        linarith only [hlt]
    have hYZ : 8 * A1 * rho + 8 * A2 * t < Y omega + Z omega :=
      lt_of_lt_of_le hXbig (hdom omega)
    rcases le_or_gt (Y omega) (A1 * (4 * t / rho ^ 3 + 4 * rho)) with hY | hY
    · refine Set.mem_union_right _ ?_
      change A2 * (4 * t + 4 * rho ^ 4) < Z omega
      rw [hAY] at hY
      rw [hAZ]
      linarith only [hYZ, hY]
    · exact Set.mem_union_left _ hY
  have hmeas :
      mu.real
          (upperTailEvent (fun omega => X omega - min (X omega) (8 * A1 * rho)) (8 * A2 * t))
        ≤ mu.real (upperTailEvent Y (A1 * (4 * t / rho ^ 3 + 4 * rho)))
          + mu.real (upperTailEvent Z (A2 * (4 * t + 4 * rho ^ 4))) :=
    le_trans (measureReal_mono hsub (measure_ne_top _ _)) (measureReal_union_le _ _)
  -- the `Γ_{1/2}` witness: its own level is already `≥ 4t`
  have hZarg : (1 : ℝ) ≤ 4 * t + 4 * rho ^ 4 := by
    have h1 : (0 : ℝ) ≤ 4 * rho ^ 4 := by positivity
    linarith only [ht, h1]
  have hZb := hZt hZarg
  rw [rpow_half_eq] at hZb
  have hZest : Real.exp (-Real.sqrt (4 * t + 4 * rho ^ 4))
      ≤ Real.exp (-Real.sqrt t) / 2 := by
    refine exp_neg_le_half_exp_neg ?_
    have h1 : Real.sqrt (4 * t) ≤ Real.sqrt (4 * t + 4 * rho ^ 4) := by
      refine Real.sqrt_le_sqrt ?_
      have h2 : (0 : ℝ) ≤ 4 * rho ^ 4 := by positivity
      linarith only [h2]
    rw [sqrt_four_mul t] at h1
    linarith only [h1, hsqt, hlog2]
  -- the `Γ₂` witness: two regimes, meeting at `t = ρ⁴`
  have hnum : (0 : ℝ) ≤ 4 * t / rho ^ 3 := div_nonneg (by linarith only [ht0]) hrho3.le
  have hYarg : (1 : ℝ) ≤ 4 * t / rho ^ 3 + 4 * rho := by
    rcases le_total rho 1 with hr | hr
    · have h1 : rho ^ 3 ≤ 1 := pow_le_one₀ hrho.le hr
      have h2 : 4 * t ≤ 4 * t / rho ^ 3 := by
        rw [le_div_iff₀ hrho3]
        calc 4 * t * rho ^ 3 ≤ 4 * t * 1 :=
              mul_le_mul_of_nonneg_left h1 (by linarith only [ht0])
          _ = 4 * t := by ring
      have h3 : (0 : ℝ) ≤ 4 * rho := by linarith only [hrho]
      linarith only [h2, ht, h3]
    · have h1 : (4 : ℝ) ≤ 4 * rho := by linarith only [hr]
      linarith only [h1, hnum]
  have hYb := hYt hYarg
  rw [rpow_two_eq] at hYb
  have hYest : Real.exp (-((4 * t / rho ^ 3 + 4 * rho) ^ 2))
      ≤ Real.exp (-Real.sqrt t) / 2 := by
    refine exp_neg_le_half_exp_neg ?_
    have hsplit : (4 * t / rho ^ 3) ^ 2 + (4 * rho) ^ 2
        ≤ (4 * t / rho ^ 3 + 4 * rho) ^ 2 := by
      have hab : (0 : ℝ) ≤ (4 * t / rho ^ 3) * (4 * rho) :=
        mul_nonneg hnum (by linarith only [hrho])
      have hexp : (4 * t / rho ^ 3 + 4 * rho) ^ 2
          = (4 * t / rho ^ 3) ^ 2 + (4 * rho) ^ 2
            + 2 * ((4 * t / rho ^ 3) * (4 * rho)) := by ring
      linarith only [hab, hexp]
    rcases le_total t (rho ^ 4) with hcase | hcase
    · -- below the crossover: the constant part `4ρ` carries it
      have hrho2 : (1 : ℝ) ≤ rho ^ 2 := by
        refine le_of_sq_le_sq' (by norm_num) (by positivity) ?_
        have h4 : (rho ^ 2) ^ 2 = rho ^ 4 := by ring
        rw [h4]
        linarith only [hcase, ht]
      have hsq : Real.sqrt t ≤ rho ^ 2 := by
        have h1 : Real.sqrt t ≤ Real.sqrt ((rho ^ 2) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          have h4 : (rho ^ 2) ^ 2 = rho ^ 4 := by ring
          rw [h4]
          exact hcase
        rwa [Real.sqrt_sq (by positivity)] at h1
      have hb2 : (4 * rho) ^ 2 = 16 * rho ^ 2 := by ring
      have hnn : (0 : ℝ) ≤ (4 * t / rho ^ 3) ^ 2 := by positivity
      linarith only [hsplit, hsq, hrho2, hlog2, hb2, hnn]
    · -- above the crossover: the growing part `4t/ρ³` carries it
      have hcube : rho ^ 6 ≤ t * Real.sqrt t := by
        refine le_of_sq_le_sq' (by positivity) (by positivity) ?_
        have hL : (rho ^ 6) ^ 2 = (rho ^ 4) ^ 3 := by ring
        have hR : (t * Real.sqrt t) ^ 2 = t ^ 3 := by
          have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
          calc (t * Real.sqrt t) ^ 2 = t ^ 2 * Real.sqrt t ^ 2 := by ring
            _ = t ^ 2 * t := by rw [hs]
            _ = t ^ 3 := by ring
        rw [hL, hR]
        exact pow_le_pow_left₀ (by positivity) hcase 3
      have hrho6 : (0 : ℝ) < rho ^ 6 := by positivity
      have hts : (0 : ℝ) < t * Real.sqrt t := by
        have h1 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
        have h2 : (0 : ℝ) < Real.sqrt t := lt_of_lt_of_le zero_lt_one hsqt
        exact mul_pos h1 h2
      have hkey : Real.sqrt t ≤ t ^ 2 / rho ^ 6 := by
        have hstep : t ^ 2 / (t * Real.sqrt t) ≤ t ^ 2 / rho ^ 6 :=
          div_le_div_of_nonneg_left (by positivity) hrho6 hcube
        have heq : t ^ 2 / (t * Real.sqrt t) = Real.sqrt t := by
          have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0
          have hne : t * Real.sqrt t ≠ 0 := ne_of_gt hts
          rw [eq_comm, eq_div_iff hne]
          calc Real.sqrt t * (t * Real.sqrt t)
              = t * (Real.sqrt t * Real.sqrt t) := by ring
            _ = t * t := by rw [hs]
            _ = t ^ 2 := by ring
        rwa [heq] at hstep
      have ha2 : (4 * t / rho ^ 3) ^ 2 = 16 * (t ^ 2 / rho ^ 6) := by
        have h6 : rho ^ 6 = (rho ^ 3) ^ 2 := by ring
        rw [h6]
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ (4 * rho) ^ 2 := by positivity
      linarith only [hsplit, hkey, hlog2, hsqt, ha2, hnn]
  calc mu.real
        (upperTailEvent (fun omega => X omega - min (X omega) (8 * A1 * rho)) (8 * A2 * t))
      ≤ mu.real (upperTailEvent Y (A1 * (4 * t / rho ^ 3 + 4 * rho)))
          + mu.real (upperTailEvent Z (A2 * (4 * t + 4 * rho ^ 4))) := hmeas
    _ ≤ Real.exp (-Real.sqrt t) / 2 + Real.exp (-Real.sqrt t) / 2 :=
        add_le_add (hYb.trans hYest) (hZb.trans hZest)
    _ = Real.exp (-Real.sqrt t) := by ring

end

end Algsuperdiff.Section4.Provider.MinimalScale
