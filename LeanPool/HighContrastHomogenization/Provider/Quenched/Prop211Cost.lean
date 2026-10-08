/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.RebaseSourceHalf

/-!
# High-contrast homogenization: Provider.Quenched.Prop211Cost

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Polynomial cost of the one-time rebase
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- A fixed positive factor is absorbed by a power of any base at least
three. -/
theorem fixed_le_rpow_of_three_le {C base : ℝ} (hC : 1 ≤ C)
    (hbase : 3 ≤ base) : C ≤ base ^ Real.logb 3 C := by
  have hlog : 0 ≤ Real.logb 3 C := Real.logb_nonneg (by norm_num) hC
  have hmono : (3 : ℝ) ^ Real.logb 3 C ≤ base ^ Real.logb 3 C :=
    Real.rpow_le_rpow (by norm_num) hbase hlog
  rwa [Real.rpow_logb (by norm_num) (by norm_num) (zero_lt_one.trans_le hC)] at hmono

/-- The generation selected from an entry scale and a bracket index has a
law-independent polynomial cost. -/
theorem rebase_generation_cost {base Centry : ℝ} {mEnt q A D : ℕ}
    (hbase : 3 ≤ base)
    (hentry : (3 : ℝ) ^ mEnt ≤ 3 * base ^ Centry)
    (hq : (3 : ℝ) ^ (q : ℤ) ≤ base ^ (4 : ℕ)) :
    (3 : ℝ) ^ (mEnt + ((A + D + 1) * q)) ≤
      base ^ (1 + Centry + 4 * ((A + D + 1 : ℕ) : ℝ)) := by
  have hbase0 : 0 < base := lt_of_lt_of_le (by norm_num) hbase
  have hq' : (3 : ℝ) ^ q ≤ base ^ (4 : ℕ) := by
    simpa only [zpow_natCast] using hq
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ q) hq'
    (A + D + 1)
  have hsplit3 : (3 : ℝ) ^ (mEnt + ((A + D + 1) * q)) =
      (3 : ℝ) ^ mEnt * ((3 : ℝ) ^ q) ^ (A + D + 1) := by
    rw [pow_add, Nat.mul_comm (A + D + 1) q, pow_mul]
  have hsplitBase :
      (3 * base ^ Centry) * (base ^ (4 : ℕ)) ^ (A + D + 1) ≤
        base ^ (1 + Centry + 4 * ((A + D + 1 : ℕ) : ℝ)) := by
    have h3 : (3 : ℝ) ≤ base ^ (1 : ℝ) := by simpa using hbase
    have hpowNat : (base ^ (4 : ℕ)) ^ (A + D + 1) =
        base ^ ((4 * (A + D + 1) : ℕ) : ℝ) := by
      rw [← pow_mul, ← Real.rpow_natCast]
    rw [hpowNat]
    have hstep : 3 * base ^ Centry ≤ base ^ (1 : ℝ) * base ^ Centry :=
      mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hbase0.le _)
    calc
      (3 * base ^ Centry) * base ^ ((4 * (A + D + 1) : ℕ) : ℝ)
          ≤ (base ^ (1 : ℝ) * base ^ Centry) *
            base ^ ((4 * (A + D + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hbase0.le _)
      _ = base ^ (1 + Centry + 4 * ((A + D + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add hbase0, ← Real.rpow_add hbase0]
        congr 1
        push_cast
        ring
  rw [hsplit3]
  exact (mul_le_mul hentry hpow (by positivity)
    (by positivity)).trans hsplitBase

/-- The combined growth witness has polynomial size in the original
polynomial base. -/
theorem renormalizedCombinedGrowthWitness_le_rpow
    (d : ℕ) {mu base K : ℝ} {B q : ℕ}
    (hmu : 0 < mu) (hbase : 3 ≤ base) (hK : K ≤ base)
    (hq : (3 : ℝ) ^ (q : ℤ) ≤ base ^ (4 : ℕ)) :
    renormalizedCombinedGrowthWitness d (B * q) mu K ≤
      base ^ (2 * (1 + 4 * (B : ℝ) +
        Real.logb 3 (frPoweredGrowthWitness d mu))) := by
  let Kfix : ℝ := frPoweredGrowthWitness d mu
  let e : ℝ := 1 + 4 * (B : ℝ) + Real.logb 3 Kfix
  have hbase0 : 0 < base := lt_of_lt_of_le (by norm_num) hbase
  have hKfix : 3 ≤ Kfix := three_le_frPoweredGrowthWitness d hmu
  have hlog : 0 ≤ Real.logb 3 Kfix :=
    Real.logb_nonneg (by norm_num) (by linarith only [hKfix])
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have he1 : 1 ≤ e := by dsimp only [e]; linarith only [hB0, hlog]
  have hq' : (3 : ℝ) ^ q ≤ base ^ (4 : ℕ) := by
    simpa only [zpow_natCast] using hq
  have hqB := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ q)
    hq' B
  have hbuffer : (3 : ℝ) ^ (B * q + 1) ≤
      base ^ (1 + 4 * (B : ℝ)) := by
    rw [Nat.mul_comm B q, pow_add, pow_one, pow_mul]
    have h3 : (3 : ℝ) ≤ base ^ (1 : ℝ) := by simpa using hbase
    have hpowNat : (base ^ (4 : ℕ)) ^ B = base ^ ((4 * B : ℕ) : ℝ) := by
      rw [← pow_mul, ← Real.rpow_natCast]
    calc
      ((3 : ℝ) ^ q) ^ B * 3 = 3 * ((3 : ℝ) ^ q) ^ B := by ring
      _ ≤ base ^ (1 : ℝ) * (base ^ (4 : ℕ)) ^ B :=
        mul_le_mul h3 hqB (by positivity) (by positivity)
      _ = base ^ (1 + 4 * (B : ℝ)) := by
        rw [hpowNat, ← Real.rpow_add hbase0]
        congr 1
        push_cast
        ring
  have hfix : Kfix ≤ base ^ Real.logb 3 Kfix :=
    fixed_le_rpow_of_three_le (by linarith only [hKfix]) hbase
  have hradius : renormalizedRadiusGrowthWitness d mu (B * q) ≤ base ^ e := by
    rw [renormalizedRadiusGrowthWitness]
    have hmul := mul_le_mul hbuffer hfix (by positivity) (by positivity)
    rw [← Real.rpow_add hbase0] at hmul
    simpa only [e] using hmul
  have htwo : (2 : ℝ) ≤ base ^ e := by
    calc
      (2 : ℝ) ≤ base := by linarith only [hbase]
      _ = base ^ (1 : ℝ) := (Real.rpow_one base).symm
      _ ≤ base ^ e := Real.rpow_le_rpow_of_exponent_le (by linarith only [hbase]) he1
  have hbaseE : base ≤ base ^ e := by
    have hp := Real.rpow_le_rpow_of_exponent_le
      (by linarith only [hbase] : (1 : ℝ) ≤ base) he1
    simpa only [Real.rpow_one] using hp
  have hKE : K ≤ base ^ e := hK.trans hbaseE
  have hmax : max 2 (max K (renormalizedRadiusGrowthWitness d mu (B * q))) ≤
      base ^ e := max_le htwo (max_le hKE hradius)
  rw [renormalizedCombinedGrowthWitness]
  have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    max 2 (max K (renormalizedRadiusGrowthWitness d mu (B * q)))) hmax 2
  calc
    max 2 (max K (renormalizedRadiusGrowthWitness d mu (B * q))) ^ (2 : ℕ)
        ≤ (base ^ e) ^ (2 : ℕ) := hsquare
    _ = base ^ (2 * e) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0.le]
      congr 1
      ring
    _ = base ^ (2 * (1 + 4 * (B : ℝ) +
        Real.logb 3 (frPoweredGrowthWitness d mu))) := by
      simp only [e, Kfix]

/-- A fixed aspect-ratio loss and a polynomial growth witness combine into
one polynomial reference cost. -/
theorem rebase_reference_cost {base aspect aspectNew Knew Casp eK : ℝ}
    (hbase : 3 ≤ base) (haspectOne : 1 ≤ aspect) (haspect : aspect ≤ base)
    (hCasp : 1 ≤ Casp) (haspectNew : 1 ≤ aspectNew)
    (hKnew : 1 ≤ Knew) (haspectBound : aspectNew ≤ Casp * aspect)
    (hKcost : Knew ≤ base ^ eK) :
    2 + aspectNew * Knew ≤
      base ^ (2 + Real.logb 3 Casp + eK) := by
  have hbase0 : 0 < base := lt_of_lt_of_le (by norm_num) hbase
  have hCcost : Casp ≤ base ^ Real.logb 3 Casp :=
    fixed_le_rpow_of_three_le hCasp hbase
  have hprod : aspectNew * Knew ≤
      base ^ (Real.logb 3 Casp + 1 + eK) := by
    have haspectR : aspect ≤ base ^ (1 : ℝ) := by
      simpa only [Real.rpow_one] using haspect
    have haspectCost : Casp * aspect ≤
        base ^ Real.logb 3 Casp * base ^ (1 : ℝ) :=
      mul_le_mul hCcost haspectR
        (zero_le_one.trans haspectOne) (Real.rpow_nonneg hbase0.le _)
    have hfirst : aspectNew ≤ base ^ (Real.logb 3 Casp + 1) := by
      refine haspectBound.trans ?_
      simpa only [Real.rpow_add hbase0, Real.rpow_one] using haspectCost
    have hmul := mul_le_mul hfirst hKcost (by positivity) (by positivity)
    rwa [← Real.rpow_add hbase0] at hmul
  have honeProd : 1 ≤ aspectNew * Knew := by
    nlinarith only [haspectNew, hKnew]
  have hsum : 2 + aspectNew * Knew ≤ base * (aspectNew * Knew) := by
    have hgap : 2 ≤ (base - 1) * (aspectNew * Knew) := by
      nlinarith only [hbase, honeProd]
    nlinarith only [hgap]
  calc
    2 + aspectNew * Knew ≤ base * (aspectNew * Knew) := hsum
    _ ≤ base ^ (1 : ℝ) * base ^ (Real.logb 3 Casp + 1 + eK) := by
      simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left hprod hbase0.le
    _ = base ^ (2 + Real.logb 3 Casp + eK) := by
      rw [← Real.rpow_add hbase0]
      congr 1
      ring

end

end HCPolySupport.HighContrast.Quenched
