/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMaximumEnvelope

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnSplitTsum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn split at the level of the row series

The burn split is stated over finite partial sums;
`adapted_scaled_of_standard`'s accounting is a `tsum` over the Whitney rows, so
the bridge needs the split in that form.  This file supplies it, with the two
inputs the filling provides: the *total* row weight (at most one, by
the total relative volume being at most one) and the *deep* row bound (the paid eccentricity
against the volume decay, by `Transport.sum_relative_volume_row_le`).

The flat band is the rows `u ≤ D`, where the envelope
`3 ^ (g * max (u - D) 0)` is exactly one; those are paid for by the total alone,
which is why the fixed-level bridge's weakening of `1` to `Cd * 𝔢` at `u = 0` is
the whole defect.  The deep rows keep the eccentricity, but only against
`3 ^ (-D)`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

/-- **The burn split over the row series.**  `w` is the row weight and `D` the
burn depth; the geometric constant `B` survives only against `3 ^ (-D)`. -/
theorem tsum_burn_split_le {g : ℝ} (hg1 : g < 1) {B : ℝ} (hB : 0 ≤ B) (D : ℕ)
    {w : ℕ → ℝ} (hw0 : ∀ u, 0 ≤ w u) (hwS : Summable w)
    (hwsum : ∑' u : ℕ, w u ≤ 1)
    (hdeep : ∀ v : ℕ, w (v + (D + 1)) ≤
      B * (3 : ℝ) ^ (-((v : ℝ) + (D : ℝ) + 1)))
    (hprod : Summable fun u : ℕ =>
      w u * (3 : ℝ) ^ (g * max ((u : ℝ) - (D : ℝ)) 0)) :
    ∑' u : ℕ, w u * (3 : ℝ) ^ (g * max ((u : ℝ) - (D : ℝ)) 0) ≤
      1 + B * zetaG g * (3 : ℝ) ^ (-(D : ℤ)) := by
  set f : ℕ → ℝ := fun u => w u * (3 : ℝ) ^ (g * max ((u : ℝ) - (D : ℝ)) 0)
    with hf
  -- the flat band: the envelope is one there
  have hflatEnv : ∀ u : ℕ, u ≤ D → f u = w u := by
    intro u hu
    have hle : ((u : ℝ) - (D : ℝ)) ≤ 0 := by
      have : (u : ℝ) ≤ (D : ℝ) := by exact_mod_cast hu
      linarith only [this]
    rw [hf]
    simp only [max_eq_right hle, mul_zero, Real.rpow_zero, mul_one]
  have hflat : ∑ u ∈ Finset.range (D + 1), f u ≤ 1 := by
    have hcongr : ∑ u ∈ Finset.range (D + 1), f u =
        ∑ u ∈ Finset.range (D + 1), w u :=
      Finset.sum_congr rfl fun u hu =>
        hflatEnv u (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu))
    rw [hcongr]
    exact (hwS.sum_le_tsum (Finset.range (D + 1))
      (fun i _ => hw0 i)).trans hwsum
  -- the deep rows
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-(1 - g)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(1 - g)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg1])
  have hgeomS : Summable fun v : ℕ => ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) := by
    have := (summable_geometric_of_lt_one hr0.le hr1).mul_left
      ((3 : ℝ) ^ (-(1 - g)))
    refine this.congr fun v => ?_
    rw [pow_succ]
    ring
  have hgeomTsum : ∑' v : ℕ, ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) ≤ zetaG g := by
    have hval : ∑' v : ℕ, ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) =
        (3 : ℝ) ^ (-(1 - g)) *
          ∑' v : ℕ, ((3 : ℝ) ^ (-(1 - g))) ^ v := by
      rw [← tsum_mul_left]
      exact tsum_congr fun v => by rw [pow_succ]; ring
    have hinv0 : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-(1 - g)))⁻¹ := by
      have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 - g)) := by linarith only [hr1]
      positivity
    rw [hval, tsum_geometric_of_lt_one hr0.le hr1, zetaG]
    calc
      (3 : ℝ) ^ (-(1 - g)) * (1 - (3 : ℝ) ^ (-(1 - g)))⁻¹ ≤
          1 * (1 - (3 : ℝ) ^ (-(1 - g)))⁻¹ :=
        mul_le_mul_of_nonneg_right hr1.le hinv0
      _ = (1 - (3 : ℝ) ^ (-(1 - g)))⁻¹ := one_mul _
  have hD0 : (0 : ℝ) < (3 : ℝ) ^ (-(D : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have htailS : Summable fun v : ℕ => f (v + (D + 1)) :=
    (summable_nat_add_iff (D + 1)).mpr hprod
  have htailBound : ∀ v : ℕ, f (v + (D + 1)) ≤
      (B * (3 : ℝ) ^ (-(D : ℝ))) * ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) := by
    intro v
    have henv : (3 : ℝ) ^ (g * max (((v + (D + 1) : ℕ) : ℝ) - (D : ℝ)) 0) =
        (3 : ℝ) ^ (g * ((v : ℝ) + 1)) := by
      congr 1
      have hpos : (0 : ℝ) ≤ ((v + (D + 1) : ℕ) : ℝ) - (D : ℝ) := by
        push_cast
        linarith only [Nat.cast_nonneg (α := ℝ) v]
      rw [max_eq_left hpos]
      push_cast
      ring
    have hgrow : (0 : ℝ) ≤ (3 : ℝ) ^ (g * ((v : ℝ) + 1)) :=
      Real.rpow_nonneg (by norm_num) _
    have hsplit : (3 : ℝ) ^ (-((v : ℝ) + (D : ℝ) + 1)) =
        (3 : ℝ) ^ (-(D : ℝ)) * (3 : ℝ) ^ (-((v : ℝ) + 1)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hterm : ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) =
        (3 : ℝ) ^ (-((v : ℝ) + 1)) * (3 : ℝ) ^ (g * ((v : ℝ) + 1)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 - g))) (v + 1),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    have hbase := hdeep v
    rw [hsplit] at hbase
    calc
      f (v + (D + 1)) =
          w (v + (D + 1)) * (3 : ℝ) ^ (g * ((v : ℝ) + 1)) := by
        simp only [hf]
        rw [henv]
      _ ≤ (B * ((3 : ℝ) ^ (-(D : ℝ)) * (3 : ℝ) ^ (-((v : ℝ) + 1)))) *
          (3 : ℝ) ^ (g * ((v : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hbase hgrow
      _ = (B * (3 : ℝ) ^ (-(D : ℝ))) *
          ((3 : ℝ) ^ (-((v : ℝ) + 1)) * (3 : ℝ) ^ (g * ((v : ℝ) + 1))) := by
        ring
      _ = (B * (3 : ℝ) ^ (-(D : ℝ))) * ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) := by
        rw [hterm]
  have hcoef0 : (0 : ℝ) ≤ B * (3 : ℝ) ^ (-(D : ℝ)) := mul_nonneg hB hD0.le
  have htail : ∑' v : ℕ, f (v + (D + 1)) ≤
      (B * (3 : ℝ) ^ (-(D : ℝ))) * zetaG g := by
    calc
      ∑' v : ℕ, f (v + (D + 1)) ≤
          ∑' v : ℕ, (B * (3 : ℝ) ^ (-(D : ℝ))) *
            ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) :=
        htailS.tsum_le_tsum htailBound (hgeomS.mul_left _)
      _ = (B * (3 : ℝ) ^ (-(D : ℝ))) *
          ∑' v : ℕ, ((3 : ℝ) ^ (-(1 - g))) ^ (v + 1) := tsum_mul_left
      _ ≤ (B * (3 : ℝ) ^ (-(D : ℝ))) * zetaG g :=
        mul_le_mul_of_nonneg_left hgeomTsum hcoef0
  -- assemble
  have hdecomp : ∑ u ∈ Finset.range (D + 1), f u +
      ∑' v : ℕ, f (v + (D + 1)) = ∑' u : ℕ, f u :=
    hprod.sum_add_tsum_nat_add (D + 1)
  have hcast : (3 : ℝ) ^ (-(D : ℤ)) = (3 : ℝ) ^ (-(D : ℝ)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (-(D : ℤ))]
    congr 1
    push_cast
    ring
  have hfinal : (B * (3 : ℝ) ^ (-(D : ℝ))) * zetaG g =
      B * zetaG g * (3 : ℝ) ^ (-(D : ℝ)) := by ring
  rw [← hdecomp, hcast]
  linarith only [hflat, htail, hfinal]

end

end HCPolySupport.HighContrast.Quenched
