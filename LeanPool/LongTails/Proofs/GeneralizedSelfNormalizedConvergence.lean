/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import LeanPool.LongTails.Proofs.GeneralizedLogCharging
public import LeanPool.LongTails.Proofs.GeneralizedConvergence

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

open Finset Set

namespace LongTails.OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

lemma high_root_simplify {a D : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D) :
    64 * ((512 / 3 * a ^ 2) * D ^ 2) ^ (1 / 3 : ℝ) ≤
      512 * (a * D) ^ (2 / 3 : ℝ) := by
  have hroot : (((512 / 3 * a ^ 2) * D ^ 2) ^ (1 / 3 : ℝ)) ^ 3 =
      (512 / 3 * a ^ 2) * D ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (512 / 3 * a ^ 2) * D ^ 2)]
    norm_num
  have hpow : ((a * D) ^ (2 / 3 : ℝ)) ^ 3 = (a * D) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg ha hD)]
    norm_num
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp
  rw [mul_pow, mul_pow, hroot, hpow]
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg D)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma run_count_self_normalized {f : E → ℝ} {g : E → E} {L0 L1 R : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1) (hR : 0 ≤ R)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (s : Iterate E) (u : E) (hmin : IsMinOn f univ u)
    (hA : 0 < s.A) (hG : 0 < s.guess) (hE : energy f u s ≤ R ^ 2)
    (hfirst : localCurvature L0 L1 (g (coupling s)) = s.guess) (n : ℕ) :
    (n : ℝ) ≤ 96 * Real.sqrt (L0 * (run L0 L1 g s (n + 1)).A) +
      4 * Real.log (2 * (run L0 L1 g s (n + 1)).A / s.A) +
      512 * (L1 * R * Real.log (2 * (run L0 L1 g s (n + 1)).A / s.A)) ^ (2 / 3 : ℝ) := by
  classical
  let Q := chargingSet (runUp L0 L1 g s) n
  let A := fun b : ℕ × ℕ => (run L0 L1 g s (b.1 + 1)).A
  let G := fun b : ℕ × ℕ => (run L0 L1 g s b.1).guess
  let M := fun b : ℕ × ℕ => localCurvature L0 L1 (g (coupling (run L0 L1 g s b.1)))
  let low := Q.filter (fun b => M b ≤ 8 * L0)
  let high := Q.filter (fun b => ¬M b ≤ 8 * L0)
  let Afinal := (run L0 L1 g s (n + 1)).A
  obtain ⟨hbase, hguess, hlow, henergy, hweights, hprefix, hinj, hsplit⟩ :=
    run_charging_geometry hL0 hL1 hc hg hgd hH s u hmin hA hG hE hfirst n
  have hAF : s.A ≤ Afinal := hbase _
  let D := Real.log (2 * Afinal / s.A)
  have hD : 0 ≤ D := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hA).mpr
    linarith
  have hh := high_count_self_normalized high Prod.fst A G Prod.snd hA hAF
    (fun b _ => hbase _) (fun b _ => hguess b.1) (by positivity)
    hinj henergy hweights hprefix
  have hr := high_root_simplify (mul_nonneg hL1.le hR) hD
  change (∑ b ∈ high, (b.2 : ℝ)) ≤ 4 * D +
    64 * ((512 / 3 * (L1 * R) ^ 2) * D ^ 2) ^ (1 / 3 : ℝ) at hh
  have hhigh : (∑ b ∈ high, (b.2 : ℝ)) ≤ 4 * D + 512 * (L1 * R * D) ^ (2 / 3 : ℝ) := by
    linarith only [hh, hr]
  change (n : ℝ) ≤ 96 * Real.sqrt (L0 * Afinal) + 4 * D + _
  linarith only [hlow, hhigh, hsplit]

lemma run_accuracy_self_normalized {f : E → ℝ} {g : E → E} {L0 L1 R Δ ε : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 < R) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (x0 u : E) (hmin : IsMinOn f univ u) (hdist : ‖x0 - u‖ ≤ R)
    (hgap : f x0 - f u ≤ Δ) (N : ℕ)
    (hN : 4096 * (1 + Real.sqrt (L0 * R ^ 2 / ε) +
      Real.log (4 + 4 * Δ / ε) + (L1 * R * Real.log (4 + 4 * Δ / ε)) ^ (2 / 3 : ℝ)) ≤ N) :
    f (run L0 L1 g (initialIterate L0 L1 R Δ x0 g) N).x - f u ≤ ε := by
  let s := initialIterate L0 L1 R Δ x0 g
  let S := Real.sqrt (L0 * R ^ 2 / ε)
  let D := Real.log (4 + 4 * Δ / ε)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hD : 0 ≤ D := by
    apply Real.log_nonneg
    have ht : 0 < 4 * Δ / ε := by positivity
    linarith
  let T := (L1 * R * D) ^ (2 / 3 : ℝ)
  have hT : 0 ≤ T := Real.rpow_nonneg (mul_nonneg (mul_nonneg hL1 hR.le) hD) _
  have hA : 0 < s.A := by dsimp [s, initialIterate]; positivity
  have hG : 0 < s.guess := localCurvature_pos hL0 hL1 _
  have hfirst : localCurvature L0 L1 (g (coupling s)) = s.guess :=
    initial_first_down hL0 hL1 hΔ x0
  have hE : energy f u s ≤ R ^ 2 := initial_energy hΔ x0 u hdist hgap
  have hNpos : 0 < N := by
    change 4096 * (1 + S + D + T) ≤ (N : ℝ) at hN
    have hn : (0 : ℝ) < N := by linarith only [hS, hD, hT, hN]
    exact_mod_cast hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hNpos)
  change f (run L0 L1 g s (n + 1)).x - f u ≤ ε
  by_contra hfail
  have hfail' : ε < f (run L0 L1 g s (n + 1)).x - f u := lt_of_not_ge hfail
  let Afinal := (run L0 L1 g s (n + 1)).A
  have hAF : s.A ≤ Afinal :=
    run_weight_mono (g := g) hL0 hL1 s hA.le hG (Nat.zero_le _)
  have hAFpos : 0 < Afinal := hA.trans_le hAF
  have hsmall : Afinal ≤ R ^ 2 / ε :=
    run_weight_le_of_inaccurate hL0 hL1 hc hg hgd hH s u hA.le hG hE hε (n + 1) hfail'
  have hsqrt : Real.sqrt (L0 * Afinal) ≤ S := by
    apply Real.sqrt_le_sqrt
    have hm := mul_le_mul_of_nonneg_left hsmall hL0.le
    simpa only [mul_div_assoc] using hm
  have hlog : Real.log (2 * Afinal / s.A) ≤ D := by
    apply Real.log_le_log (by positivity)
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 2)) hA.le
    have he : 2 * (R ^ 2 / ε) / s.A = 4 * Δ / ε := by
      dsimp [s, initialIterate]
      field_simp
      ring
    rw [he] at hm
    change 2 * Afinal / s.A ≤ 4 + 4 * Δ / ε
    linarith only [hm]
  have hcount : (n : ℝ) ≤ 96 * S + 4 * D + 512 * T := by
    by_cases hz : L1 = 0
    · subst L1
      have hb := run_count_smooth hL0 s hA.le hG hfirst n
      change (n : ℝ) ≤ 96 * Real.sqrt (L0 * Afinal) at hb
      linarith only [hb, hsqrt, hD, hT]
    · have hL1p : 0 < L1 := lt_of_le_of_ne hL1 (Ne.symm hz)
      have hb := run_count_self_normalized hL0 hL1p hR.le hc hg hgd hH s u hmin hA hG hE hfirst n
      have hlogpos : 0 ≤ Real.log (2 * Afinal / s.A) := by
        apply Real.log_nonneg
        apply (le_div_iff₀ hA).mpr
        linarith
      have hp := Real.rpow_le_rpow
        (mul_nonneg (mul_nonneg hL1 hR.le) hlogpos)
        (mul_le_mul_of_nonneg_left hlog (mul_nonneg hL1 hR.le)) (by norm_num : (0 : ℝ) ≤ 2 / 3)
      change (n : ℝ) ≤ 96 * Real.sqrt (L0 * Afinal) + 4 * Real.log (2 * Afinal / s.A) +
        512 * (L1 * R * Real.log (2 * Afinal / s.A)) ^ (2 / 3 : ℝ) at hb
      change (L1 * R * Real.log (2 * Afinal / s.A)) ^ (2 / 3 : ℝ) ≤ T at hp
      nlinarith only [hb, hsqrt, hlog, hp]
  change 4096 * (1 + S + D + T) ≤ ((n + 1 : ℕ) : ℝ) at hN
  push_cast at hN
  linarith only [hS, hD, hT, hN, hcount]

lemma run_accuracy_min {f : E → ℝ} {g : E → E} {L0 L1 R Δ ε : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 < R) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (x0 u : E) (hmin : IsMinOn f univ u) (hdist : ‖x0 - u‖ ≤ R)
    (hgap : f x0 - f u ≤ Δ) (N : ℕ)
    (hN : 4096 * (1 + Real.sqrt (L0 * R ^ 2 / ε) +
      min ((⌈(L1 * R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * Δ / ε))
        (Real.log (4 + 4 * Δ / ε) + (L1 * R * Real.log (4 + 4 * Δ / ε)) ^ (2 / 3 : ℝ))) ≤ N) :
    f (run L0 L1 g (initialIterate L0 L1 R Δ x0 g) N).x - f u ≤ ε := by
  rcases le_total ((⌈(L1 * R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * Δ / ε))
    (Real.log (4 + 4 * Δ / ε) + (L1 * R * Real.log (4 + 4 * Δ / ε)) ^ (2 / 3 : ℝ)) with h | h
  · rw [min_eq_left h] at hN
    exact run_accuracy hL0 hL1 hR hΔ hε hc hg hgd hH x0 u hmin hdist hgap N hN
  · rw [min_eq_right h] at hN
    apply run_accuracy_self_normalized hL0 hL1 hR hΔ hε hc hg hgd hH x0 u hmin hdist hgap N
    linarith

end LongTails.OracleTemplate.GeneralizedAccelerated
