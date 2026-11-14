/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.UpperPolyProfile

/-!
# UpperSaturatedProfile

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Saturated finite-`q` upper-profile arithmetic

This module studies the concrete depth profile

`A * (n + 1) * min 1 (gamma * (n + 1)) * 3^(gamma n)`.

The saturation supplies the missing small-depth factor when `1 <= q <= 2`.
Splitting according to whether `2 * s - gamma` is below or above `gamma`
reduces the profile to a linear or quadratic polynomial times a geometric
factor.  Half of the positive gap absorbs that polynomial, and the exact
normalized `Book.Ch02.geometricWeight` is retained throughout.

This is an internal conditional arithmetic helper.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport

noncomputable section

/-- The saturated linear-times-geometric depth profile. -/
def upperSaturatedProfile (A gamma : ℝ) (n : ℕ) : ℝ :=
  A * ((n : ℝ) + 1) * min 1 (gamma * ((n : ℝ) + 1)) *
    (3 : ℝ) ^ (gamma * (n : ℝ))

theorem upperSaturatedProfile_nonneg {A gamma : ℝ}
    (hA : 0 ≤ A) (hgamma : 0 ≤ gamma) (n : ℕ) :
    0 ≤ upperSaturatedProfile A gamma n := by
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg hA (by positivity))
      (le_min (by norm_num) (mul_nonneg hgamma (by positivity))))
    (Real.rpow_nonneg (by norm_num) _)

/-- Half of a positive gap absorbs one linear depth factor.  The constant is
deliberately coarse and universal. -/
theorem natCast_succ_le_inv_mul_three_rpow {rho : ℝ}
    (hrho : 0 < rho) (hrho2 : rho ≤ 2) (n : ℕ) :
    (n : ℝ) + 1 ≤
      6 * rho⁻¹ * (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) := by
  let N : ℝ := (n : ℝ) + 1
  let x : ℝ := rho * Real.log 3 * N / 2
  have hlog : (1 : ℝ) < Real.log 3 := by
    have h3 : Real.exp 1 < (3 : ℝ) :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2 h3
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxexp : x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have hscaled : rho * N ≤ 2 * Real.exp x := by
    have hlogmul : rho * N ≤ rho * Real.log 3 * N := by
      calc
        rho * N = (rho * 1) * N := by ring
        _ ≤ (rho * Real.log 3) * N :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlog.le hrho.le) hN.le
        _ = rho * Real.log 3 * N := by ring
    have hxid : rho * Real.log 3 * N = 2 * x := by
      dsimp [x]
      ring
    rw [hxid] at hlogmul
    nlinarith
  have hNexp : N ≤ 2 * rho⁻¹ * Real.exp x := by
    have hmul := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hrho.le)
    have hcancel : rho⁻¹ * (rho * N) = N := by
      field_simp
    rw [hcancel] at hmul
    nlinarith
  have hxBound : x ≤
      Real.log 3 + (rho / 2) * (n : ℝ) * Real.log 3 := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hcoeff : rho * ((n : ℝ) + 1) / 2 ≤
        1 + (rho / 2) * (n : ℝ) := by
      nlinarith
    have hlog0 : (0 : ℝ) ≤ Real.log 3 :=
      le_trans zero_le_one hlog.le
    have := mul_le_mul_of_nonneg_right hcoeff hlog0
    dsimp [x, N]
    linarith
  have hexpBound : Real.exp x ≤
      3 * (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) := by
    calc
      Real.exp x ≤ Real.exp
          (Real.log 3 + (rho / 2) * (n : ℝ) * Real.log 3) :=
        Real.exp_le_exp.mpr hxBound
      _ = Real.exp (Real.log 3) *
          Real.exp ((rho / 2) * (n : ℝ) * Real.log 3) := by
        rw [Real.exp_add]
      _ = 3 * (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 3),
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
        congr 2
        ring
  have hfac : 0 ≤ 2 * rho⁻¹ := by positivity
  calc
    (n : ℝ) + 1 = N := rfl
    _ ≤ 2 * rho⁻¹ * Real.exp x := hNexp
    _ ≤ 2 * rho⁻¹ *
        (3 * (3 : ℝ) ^ ((rho / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hexpBound hfac
    _ = 6 * rho⁻¹ *
        (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) := by ring

private theorem upperSaturatedProfile_le_finiteQGeometricProfile_linear
    {A gamma rho : ℝ} (hA : 0 ≤ A) (hrho : 0 < rho)
    (hrho2 : rho ≤ 2) (n : ℕ) :
    upperSaturatedProfile A gamma n ≤
      finiteQGeometricProfile (6 * A * rho⁻¹) (gamma + rho / 2) n := by
  have hN : 0 ≤ (n : ℝ) + 1 := by positivity
  have hpow : 0 ≤ (3 : ℝ) ^ (gamma * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmin : min 1 (gamma * ((n : ℝ) + 1)) ≤ 1 := min_le_left _ _
  have hminStep :
      A * ((n : ℝ) + 1) * min 1 (gamma * ((n : ℝ) + 1)) ≤
        A * ((n : ℝ) + 1) := by
    simpa using mul_le_mul_of_nonneg_left hmin (mul_nonneg hA hN)
  have hlinear := natCast_succ_le_inv_mul_three_rpow hrho hrho2 n
  have hlinearA := mul_le_mul_of_nonneg_left hlinear hA
  rw [upperSaturatedProfile, finiteQGeometricProfile]
  calc
    A * ((n : ℝ) + 1) * min 1 (gamma * ((n : ℝ) + 1)) *
          (3 : ℝ) ^ (gamma * (n : ℝ)) ≤
        (A * ((n : ℝ) + 1)) *
          (3 : ℝ) ^ (gamma * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hminStep hpow
    _ ≤ (A * (6 * rho⁻¹ *
          (3 : ℝ) ^ ((rho / 2) * (n : ℝ)))) *
          (3 : ℝ) ^ (gamma * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hlinearA hpow
    _ = (6 * A * rho⁻¹) *
          (3 : ℝ) ^ ((gamma + rho / 2) * (n : ℝ)) := by
      rw [show (3 : ℝ) ^ ((gamma + rho / 2) * (n : ℝ)) =
          (3 : ℝ) ^ ((rho / 2) * (n : ℝ)) *
            (3 : ℝ) ^ (gamma * (n : ℝ)) by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring]
      ring

private theorem upperSaturatedProfile_le_upperPolyProfile
    {A gamma : ℝ} (hA : 0 ≤ A) (n : ℕ) :
    upperSaturatedProfile A gamma n ≤
      upperPolyProfile (A * gamma) gamma n := by
  have hN : 0 ≤ (n : ℝ) + 1 := by positivity
  have hpow : 0 ≤ (3 : ℝ) ^ (gamma * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmin : min 1 (gamma * ((n : ℝ) + 1)) ≤
      gamma * ((n : ℝ) + 1) := min_le_right _ _
  have hminStep := mul_le_mul_of_nonneg_left hmin (mul_nonneg hA hN)
  rw [upperSaturatedProfile, upperPolyProfile]
  calc
    A * ((n : ℝ) + 1) * min 1 (gamma * ((n : ℝ) + 1)) *
          (3 : ℝ) ^ (gamma * (n : ℝ)) ≤
        (A * ((n : ℝ) + 1) * (gamma * ((n : ℝ) + 1))) *
          (3 : ℝ) ^ (gamma * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hminStep hpow
    _ = A * gamma * (((n : ℝ) + 1) ^ 2) *
          (3 : ℝ) ^ (gamma * (n : ℝ)) := by ring

private theorem upperSaturatedProfile_le_finiteQGeometricProfile_quadratic
    {A gamma rho : ℝ} (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (hrho : 0 < rho) (hrho2 : rho ≤ 2) (n : ℕ) :
    upperSaturatedProfile A gamma n ≤
      finiteQGeometricProfile
        (96 * (A * gamma) * rho⁻¹ ^ 2) (gamma + rho / 2) n := by
  exact (upperSaturatedProfile_le_upperPolyProfile hA n).trans
    (upperPolyProfile_le_finiteQGeometricProfile
      (mul_nonneg hA hgamma) hrho hrho2 gamma n)

private theorem upperSaturatedProfile_aggregate_le_of_pointwise
    {P : ℕ → ℝ} {s q gamma C : ℝ}
    (hP : ∀ n, 0 ≤ P n) (hC : 0 ≤ C) (hgamma : 0 ≤ gamma)
    (hs : 0 < s) (hq : 0 < q) (hgap : 0 < 2 * s - gamma)
    (hle : ∀ n, P n ≤ finiteQGeometricProfile C gamma n) :
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n * P n ^ (q / 2)) ^
        (2 / q) ≤
      C * (2 * s / (2 * s - gamma)) ^ (2 / q) := by
  have hsq : 0 ≤ s * q := mul_nonneg hs.le hq.le
  have hleftNonneg : ∀ n : ℕ, 0 ≤
      Book.Ch02.geometricWeight s q n * P n ^ (q / 2) := fun n =>
    mul_nonneg (HCPolySupport.geometricWeight_nonneg n hsq)
      (Real.rpow_nonneg (hP n) _)
  have hrightSum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s q n *
        finiteQGeometricProfile C gamma n ^ (q / 2) :=
    summable_geometricWeight_mul_finiteQGeometricProfile_rpow hC hgap hq
  have hterm : ∀ n : ℕ,
      Book.Ch02.geometricWeight s q n * P n ^ (q / 2) ≤
        Book.Ch02.geometricWeight s q n *
          finiteQGeometricProfile C gamma n ^ (q / 2) := by
    intro n
    refine mul_le_mul_of_nonneg_left ?_
      (HCPolySupport.geometricWeight_nonneg n hsq)
    exact Real.rpow_le_rpow (hP n) (hle n) (by positivity)
  have hleftSum : Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s q n * P n ^ (q / 2) :=
    Summable.of_nonneg_of_le hleftNonneg hterm hrightSum
  have htsum :
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n * P n ^ (q / 2)) ≤
        ∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          finiteQGeometricProfile C gamma n ^ (q / 2) :=
    hleftSum.tsum_le_tsum hterm hrightSum
  calc
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n * P n ^ (q / 2)) ^
          (2 / q) ≤
        (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          finiteQGeometricProfile C gamma n ^ (q / 2)) ^ (2 / q) :=
      Real.rpow_le_rpow (tsum_nonneg hleftNonneg) htsum (by positivity)
    _ ≤ C * (2 * s / (2 * s - gamma)) ^ (2 / q) :=
      finiteQGeometricProfile_aggregate_le hC hgamma hs hq hgap

/-- The exact normalized finite-`q` aggregate of the saturated profile has the
cubic gap pole uniformly on `1 <= q <= 2`. -/
theorem upperSaturatedProfile_aggregate_le_of_one_le_of_le_two
    {A gamma s q : ℝ} (hA : 0 ≤ A) (hgamma : 0 ≤ gamma)
    (hs : 0 < s) (hs1 : s ≤ 1) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hgap : 0 < 2 * s - gamma) :
    (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        upperSaturatedProfile A gamma n ^ (q / 2)) ^ (2 / q) ≤
      3072 * A * s * gamma * (2 * s - gamma)⁻¹ ^ 3 := by
  let rho : ℝ := 2 * s - gamma
  let gamma' : ℝ := gamma + rho / 2
  have hrho : 0 < rho := by simpa [rho] using hgap
  have hrho2 : rho ≤ 2 := by
    dsimp [rho]
    linarith
  have hqRange : q ∈ Set.Icc (1 : ℝ) 2 := ⟨hq1, hq2⟩
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hqRange.1
  have hexponent : 2 / q ≤ 2 := by
    rw [div_le_iff₀ hq0]
    linarith
  have hrho_le_two_s : rho ≤ 2 * s := by
    dsimp [rho]
    linarith
  have hbase1 : 1 ≤ 4 * s / rho := by
    rw [le_div_iff₀ hrho]
    linarith
  have hgamma' : 0 ≤ gamma' := by
    dsimp [gamma']
    positivity
  have hgap' : 0 < 2 * s - gamma' := by
    have hid : 2 * s - gamma' = rho / 2 := by
      dsimp [gamma', rho]
      ring
    rw [hid]
    positivity
  have hbaseEq : 2 * s / (2 * s - gamma') = 4 * s / rho := by
    have hrhoNe : rho ≠ 0 := ne_of_gt hrho
    have hid : 2 * s - gamma' = rho / 2 := by
      dsimp [gamma', rho]
      ring
    rw [hid]
    field_simp
    norm_num
  have hrpowSq : (4 * s / rho) ^ (2 / q) ≤ (4 * s / rho) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hbase1 hexponent
    simpa only [Real.rpow_two] using this
  rcases le_total rho gamma with hrhoGamma | hgammaRho
  · let C : ℝ := 6 * A * rho⁻¹
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hdom : ∀ n : ℕ,
        upperSaturatedProfile A gamma n ≤
          finiteQGeometricProfile C gamma' n := by
      intro n
      simpa [C, gamma'] using
        upperSaturatedProfile_le_finiteQGeometricProfile_linear
          hA hrho hrho2 n
    have hagg := upperSaturatedProfile_aggregate_le_of_pointwise
      (P := upperSaturatedProfile A gamma)
      (fun n => upperSaturatedProfile_nonneg hA hgamma n)
      hC hgamma' hs hq0 hgap' hdom
    have hsGamma : s ≤ gamma := by
      dsimp [rho] at hrhoGamma
      linarith
    have hfactor : 0 ≤ 96 * A * s * rho⁻¹ ^ 3 := by positivity
    have hsg := mul_le_mul_of_nonneg_left hsGamma hfactor
    have h96 :
        96 * A * s ^ 2 * rho⁻¹ ^ 3 ≤
          96 * A * s * gamma * rho⁻¹ ^ 3 := by
      calc 96 * A * s ^ 2 * rho⁻¹ ^ 3
          = 96 * A * s * rho⁻¹ ^ 3 * s := by ring
        _ ≤ 96 * A * s * rho⁻¹ ^ 3 * gamma := hsg
        _ = 96 * A * s * gamma * rho⁻¹ ^ 3 := by ring
    have hnonneg : 0 ≤ A * s * gamma * rho⁻¹ ^ 3 := by positivity
    have hconst :
        96 * A * s * gamma * rho⁻¹ ^ 3 ≤
          3072 * A * s * gamma * rho⁻¹ ^ 3 := by
      have := mul_le_mul_of_nonneg_right
        (by norm_num : (96 : ℝ) ≤ 3072) hnonneg
      calc 96 * A * s * gamma * rho⁻¹ ^ 3
          = 96 * (A * s * gamma * rho⁻¹ ^ 3) := by ring
        _ ≤ 3072 * (A * s * gamma * rho⁻¹ ^ 3) := this
        _ = 3072 * A * s * gamma * rho⁻¹ ^ 3 := by ring
    calc
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          upperSaturatedProfile A gamma n ^ (q / 2)) ^ (2 / q) ≤
          C * (2 * s / (2 * s - gamma')) ^ (2 / q) := hagg
      _ = 6 * A * rho⁻¹ * (4 * s / rho) ^ (2 / q) := by
        rw [hbaseEq]
      _ ≤ 6 * A * rho⁻¹ * (4 * s / rho) ^ 2 :=
        mul_le_mul_of_nonneg_left hrpowSq hC
      _ = 96 * A * s ^ 2 * rho⁻¹ ^ 3 := by
        simp only [div_eq_mul_inv]
        ring
      _ ≤ 96 * A * s * gamma * rho⁻¹ ^ 3 := h96
      _ ≤ 3072 * A * s * gamma * rho⁻¹ ^ 3 := hconst
      _ = 3072 * A * s * gamma * (2 * s - gamma)⁻¹ ^ 3 := by
        rfl
  · let C : ℝ := 96 * (A * gamma) * rho⁻¹ ^ 2
    have hC : 0 ≤ C := by
      dsimp [C]
      positivity
    have hdom : ∀ n : ℕ,
        upperSaturatedProfile A gamma n ≤
          finiteQGeometricProfile C gamma' n := by
      intro n
      simpa [C, gamma'] using
        upperSaturatedProfile_le_finiteQGeometricProfile_quadratic
          hA hgamma hrho hrho2 n
    have hagg := upperSaturatedProfile_aggregate_le_of_pointwise
      (P := upperSaturatedProfile A gamma)
      (fun n => upperSaturatedProfile_nonneg hA hgamma n)
      hC hgamma' hs hq0 hgap' hdom
    have hsRho : s ≤ rho := by
      dsimp [rho] at hgammaRho ⊢
      linarith
    have hbase4 : 4 * s / rho ≤ 4 := by
      rw [div_le_iff₀ hrho]
      nlinarith
    have hbase0 : 0 ≤ 4 * s / rho := hbase1.trans' zero_le_one
    have hsq16 : (4 * s / rho) ^ 2 ≤ 16 := by nlinarith
    have hrpow16 : (4 * s / rho) ^ (2 / q) ≤ 16 :=
      hrpowSq.trans hsq16
    have hinvId : rho⁻¹ ^ 2 = rho * rho⁻¹ ^ 3 := by
      field_simp [ne_of_gt hrho]
    have hfactor : 0 ≤ 1536 * A * gamma * rho⁻¹ ^ 3 := by positivity
    have hrhoStep := mul_le_mul_of_nonneg_left hrho_le_two_s hfactor
    have hfinal :
        1536 * A * gamma * rho⁻¹ ^ 2 ≤
          3072 * A * s * gamma * rho⁻¹ ^ 3 := by
      rw [hinvId]
      calc 1536 * A * gamma * (rho * rho⁻¹ ^ 3)
          = 1536 * A * gamma * rho⁻¹ ^ 3 * rho := by ring
        _ ≤ 1536 * A * gamma * rho⁻¹ ^ 3 * (2 * s) := hrhoStep
        _ = 3072 * A * s * gamma * rho⁻¹ ^ 3 := by ring
    calc
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          upperSaturatedProfile A gamma n ^ (q / 2)) ^ (2 / q) ≤
          C * (2 * s / (2 * s - gamma')) ^ (2 / q) := hagg
      _ = (96 * (A * gamma) * rho⁻¹ ^ 2) *
          (4 * s / rho) ^ (2 / q) := by
        rw [hbaseEq]
      _ ≤ (96 * (A * gamma) * rho⁻¹ ^ 2) * 16 :=
        mul_le_mul_of_nonneg_left hrpow16 hC
      _ = 1536 * A * gamma * rho⁻¹ ^ 2 := by ring
      _ ≤ 3072 * A * s * gamma * rho⁻¹ ^ 3 := hfinal
      _ = 3072 * A * s * gamma * (2 * s - gamma)⁻¹ ^ 3 := by
        rfl

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
