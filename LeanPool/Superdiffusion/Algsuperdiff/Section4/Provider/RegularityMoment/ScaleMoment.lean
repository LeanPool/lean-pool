/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomMomentTail

/-!
# ScaleMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exponential moments of the minimal scale at a fixed Hölder exponent

The minimal scale of the local Hölder estimate enters the localized regularity
through the factor `3^{X/2}`, and the exponent at which that factor has to be
integrated is a fixed multiple of `gamma⁻¹`.  This module supplies the moment at
that exponent.

The layer decomposition of `3^{cX}` at a cut `N0` and the exponential tail
`mu{X ≥ N} ≤ B e^{-θ N}` give the value at the cut plus a geometric remainder.
Both pieces are then evaluated for the tail

`P{X ≥ N} ≤ C exp(-((1 - alpha)² (N - C)) / (C gamma))`   at   `alpha = 1/2`,

whose normal form is `B = C e^{1/(4 gamma)}` and `θ = 1/(4 C gamma)`.  At the
exponent `p = c gamma⁻¹` with

`c = (4 C log 3)⁻¹`,

the ratio of the geometric remainder is `e^{-1/(8 C gamma)}`, at most one half
once `gamma ≤ (8 C log 2)⁻¹`; and the cut `N0 = ⌈4C⌉` makes the remainder at
most `C`, because `e^{1/(4 gamma)} e^{-(N0+1)/(8 C gamma)} ≤ 1`.  The value at
the cut is `(3^{N0/2})^p`, so both pieces are `p`-th powers of constants and the
moment is a `p`-th power of a constant.

The exponent `c` depends only on the constant of the tail, hence only on the
data the local Hölder estimate depends on; it does not depend on `gamma`.

## Main results

* `lintegral_homMinimalScaleFactor_le_trunc` — the layer decomposition at a free
  cut, for a scale with a geometric tail.
* `exists_minimalScaleFactor_moment_bound` — `∫⁻ (3^{X/2})^{c gamma⁻¹} ≤ K^{c gamma⁻¹}`
  for the tail of the local Hölder estimate at `alpha = 1/2`.
-/

namespace Algsuperdiff.Section4.Provider.RegularityMoment

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The geometric series of a ratio at most one half, in `ℝ≥0∞`. -/
private theorem tsum_ofReal_geometric_le_two {rho : ℝ} (h : rho ≤ 1 / 2) :
    ∑' _N : ℕ, ENNReal.ofReal rho ^ _N ≤ 2 := by
  exact _root_.Algsuperdiff.Section4.Provider.Homogenization.tsum_ofReal_pow_le_two h

private theorem three_rpow_mul_exp_pow' (c theta : ℝ) (K : ℕ) :
    (3 : ℝ) ^ (c * (K : ℝ)) * Real.exp (-(theta * (K : ℝ))) =
      ((3 : ℝ) ^ c * Real.exp (-theta)) ^ K := by
  have h1 : ((3 : ℝ) ^ c) ^ K = (3 : ℝ) ^ (c * (K : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ c) K, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have h2 : (Real.exp (-theta)) ^ K = Real.exp (-(theta * (K : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, h1, h2]

/-- **The truncated exponential-moment engine at an arbitrary cut.**

The exponential moment of `3^{cX}` for a scale with the geometric tail
`mu{X ≥ N} ≤ B e^{-θ N}` splits into the value at the cut and a geometric
remainder.  Unlike the packaged form used by the Theorem-B web, the cut `N0` is
free: the constant of the conclusion is whatever the two pieces produce. -/
theorem lintegral_homMinimalScaleFactor_le_trunc {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {X : Omega → ℕ∞} (hX : Measurable X)
    {c B theta : ℝ} (N0 : ℕ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (htail : ∀ N : ℕ, mu {w : Omega | (N : ℕ∞) ≤ X w} ≤
      ENNReal.ofReal (B * Real.exp (-(theta * (N : ℝ)))))
    (hratio : (3 : ℝ) ^ c * Real.exp (-theta) ≤ 1 / 2) :
    (∫⁻ omega, homMinimalScaleFactor c X omega ∂mu) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (c * (N0 : ℝ))) +
        ENNReal.ofReal (2 * (B * ((3 : ℝ) ^ c * Real.exp (-theta)) ^ (N0 + 1))) := by
  set rho : ℝ := (3 : ℝ) ^ c * Real.exp (-theta) with hrho
  have hrho0 : (0 : ℝ) ≤ rho := by
    rw [hrho]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le
  have hterm : ∀ N : ℕ,
      ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))) *
          mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w} ≤
        ENNReal.ofReal (B * rho ^ (N0 + 1)) * ENNReal.ofReal rho ^ N := by
    intro N
    have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hstep : ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))) *
        mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w} ≤
        ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))) *
          ENNReal.ofReal (B * Real.exp (-(theta * ((N0 + 1 + N : ℕ) : ℝ)))) :=
      mul_le_mul_right (htail (N0 + 1 + N)) _
    refine hstep.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul hbase]
    have hid : (3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ)) *
        (B * Real.exp (-(theta * ((N0 + 1 + N : ℕ) : ℝ)))) =
        B * rho ^ (N0 + 1 + N) := by
      have h := three_rpow_mul_exp_pow' c theta (N0 + 1 + N)
      rw [← hrho] at h
      calc (3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ)) *
            (B * Real.exp (-(theta * ((N0 + 1 + N : ℕ) : ℝ))))
          = B * ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ)) *
              Real.exp (-(theta * ((N0 + 1 + N : ℕ) : ℝ)))) := by ring
        _ = B * rho ^ (N0 + 1 + N) := by rw [h]
    rw [hid, pow_add,
      show B * (rho ^ (N0 + 1) * rho ^ N) = B * rho ^ (N0 + 1) * rho ^ N by ring,
      ENNReal.ofReal_mul (mul_nonneg hB (pow_nonneg hrho0 _)),
      ENNReal.ofReal_pow hrho0]
  have hseries : (∑' N : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))) *
      mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}) ≤
      ENNReal.ofReal (2 * (B * rho ^ (N0 + 1))) := by
    have hbound : (∑' N : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (c * ((N0 + 1 + N : ℕ) : ℝ))) *
        mu {w : Omega | ((N0 + 1 + N : ℕ) : ℕ∞) ≤ X w}) ≤
        ENNReal.ofReal (B * rho ^ (N0 + 1)) * ∑' _N : ℕ, ENNReal.ofReal rho ^ _N := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum hterm
    refine hbound.trans ?_
    have hgeom := tsum_ofReal_geometric_le_two (rho := rho) hratio
    refine (mul_le_mul_right hgeom _).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    ring
  exact (lintegral_homMinimalScaleFactor_le (mu := mu) hc N0 hX).trans
    (add_le_add le_rfl hseries)

variable {d : ℕ}

/-- **The minimal-scale factor has a bounded moment at an exponent proportional
to `gamma⁻¹`.**  For a scale with the exponential tail of the local Hölder
estimate at `alpha = 1/2` and constant `Ctail`, there are a threshold, an
exponent constant `c` and a bound `K`, all depending only on `Ctail`, such that

`∫⁻ (3^{X/2})^{c gamma⁻¹} ≤ K^{c gamma⁻¹}`

for every model of disorder strength at most the threshold and every scale with
that tail.  Both `c` and `K` are chosen before `gamma`. -/
theorem exists_minimalScaleFactor_moment_bound (Ctail : ℝ) (hCtail : 0 < Ctail) :
    ∃ gamma0 c K : ℝ, 0 < gamma0 ∧ 0 < c ∧ 0 < K ∧
      ∀ (M : ABKModel d) (X : Cutoff.CutoffSample d → ℕ), Measurable X →
        M.gamma ≤ gamma0 →
        (∀ N : ℕ, (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ X omega} ≤
          ENNReal.ofReal (Ctail * Real.exp
            (-((1 - (1 : ℝ) / 2) ^ (2 : ℕ) * ((N : ℝ) - Ctail)) / (Ctail * M.gamma)))) →
        (∫⁻ omega, ENNReal.ofReal (Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) ^
              (c * M.gamma⁻¹) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          ENNReal.ofReal K ^ (c * M.gamma⁻¹) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨cc, hcc⟩ : ∃ x : ℝ, x = (4 * Ctail * Real.log 3)⁻¹ := ⟨_, rfl⟩
  obtain ⟨N0, hN0⟩ : ∃ k : ℕ, k = ⌈4 * Ctail⌉₊ := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ x : ℝ, x = (3 : ℝ) ^ ((N0 : ℝ) / 2) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ x : ℝ, x = max 1 (2 * Ctail) := ⟨_, rfl⟩
  have hccpos : 0 < cc := by rw [hcc]; positivity
  have hA1one : (1 : ℝ) ≤ A1 := by
    rw [hA1]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hA2one : (1 : ℝ) ≤ A2 := by rw [hA2]; exact le_max_left _ _
  have hmaxone : (1 : ℝ) ≤ max A1 A2 := le_trans hA1one (le_max_left _ _)
  refine ⟨min cc (8 * Ctail * Real.log 2)⁻¹, cc, 2 * max A1 A2,
    lt_min hccpos (by positivity), hccpos, by linarith only [hmaxone], ?_⟩
  intro M X hXmeas hgamma htail
  have hgam : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgcc : M.gamma ≤ cc := hgamma.trans (min_le_left _ _)
  have hglog : M.gamma ≤ (8 * Ctail * Real.log 2)⁻¹ := hgamma.trans (min_le_right _ _)
  -- the exponent
  have hp : (1 : ℝ) ≤ cc * M.gamma⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hgam]
    linarith only [hgcc]
  have hppos : (0 : ℝ) < cc * M.gamma⁻¹ := lt_of_lt_of_le zero_lt_one hp
  set p : ℝ := cc * M.gamma⁻¹ with hpdef
  set Xhat : Cutoff.CutoffSample d → ℕ∞ := fun w => (X w : ℕ∞) with hXhat
  have hXhatmeas : Measurable Xhat := Measurable.of_discrete.comp hXmeas
  have hintegrand : ∀ omega : Cutoff.CutoffSample d,
      ENNReal.ofReal (Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) ^ p =
        homMinimalScaleFactor ((1 / 2 : ℝ) * p) Xhat omega := by
    intro omega
    exact homMinimalScaleFactor_rpow hppos Xhat omega
  rw [lintegral_congr hintegrand]
  -- the tail in the `(B, theta)` normal form
  have hgne : M.gamma ≠ 0 := hgam.ne'
  have htail' : ∀ N : ℕ,
      (Cutoff.cutoffSampleLaw M).toMeasure {w : Cutoff.CutoffSample d | (N : ℕ∞) ≤ Xhat w} ≤
        ENNReal.ofReal ((Ctail * Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma)) *
          Real.exp (-(((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / (Ctail * M.gamma)) * (N : ℝ)))) := by
    intro N
    have hset : {w : Cutoff.CutoffSample d | (N : ℕ∞) ≤ Xhat w} =
        {w : Cutoff.CutoffSample d | N ≤ X w} := by
      ext w
      simp only [hXhat, Set.mem_ofPred_eq, Nat.cast_le]
    rw [hset]
    have hN := htail N
    rwa [homTailNormalForm hCtail.ne' hgne N] at hN
  -- the two exponent identities
  have hc'log : (1 / 2 : ℝ) * p * Real.log 3 = (8 * Ctail * M.gamma)⁻¹ := by
    rw [hpdef, hcc]
    field_simp
    ring
  have hthetaval : (1 - (1 : ℝ) / 2) ^ (2 : ℕ) / (Ctail * M.gamma) =
      (4 * Ctail * M.gamma)⁻¹ := by
    rw [show (1 - (1 : ℝ) / 2) ^ (2 : ℕ) = 1 / 4 by norm_num]
    field_simp
  have hrhoval : (3 : ℝ) ^ ((1 / 2 : ℝ) * p) *
      Real.exp (-((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / (Ctail * M.gamma))) =
      Real.exp (-(8 * Ctail * M.gamma)⁻¹) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add, hthetaval]
    congr 1
    rw [show Real.log 3 * ((1 / 2 : ℝ) * p) = (1 / 2 : ℝ) * p * Real.log 3 by ring, hc'log]
    field_simp
    ring
  -- the ratio gate
  have hpos8 : (0 : ℝ) < 8 * Ctail * M.gamma := by positivity
  have hkey : Real.log 2 ≤ (8 * Ctail * M.gamma)⁻¹ := by
    have hstep : 8 * Ctail * M.gamma ≤ (Real.log 2)⁻¹ := by
      calc 8 * Ctail * M.gamma = (8 * Ctail) * M.gamma := by ring
        _ ≤ (8 * Ctail) * (8 * Ctail * Real.log 2)⁻¹ :=
            mul_le_mul_of_nonneg_left hglog (by positivity)
        _ = (Real.log 2)⁻¹ := by field_simp
    have h := (inv_le_inv₀ (by positivity : (0 : ℝ) < (Real.log 2)⁻¹) hpos8).2 hstep
    rwa [inv_inv] at h
  have hratio : (3 : ℝ) ^ ((1 / 2 : ℝ) * p) *
      Real.exp (-((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / (Ctail * M.gamma))) ≤ 1 / 2 := by
    rw [hrhoval]
    calc Real.exp (-(8 * Ctail * M.gamma)⁻¹) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.2 (neg_le_neg hkey)
      _ = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num
  -- the engine
  have hc'nn : (0 : ℝ) ≤ (1 / 2 : ℝ) * p := by positivity
  have hBnn : (0 : ℝ) ≤ Ctail * Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma) := by
    positivity
  have hengine := lintegral_homMinimalScaleFactor_le_trunc
    (mu := (Cutoff.cutoffSampleLaw M).toMeasure) hXhatmeas N0 hc'nn hBnn htail' hratio
  refine hengine.trans ?_
  -- the cut term
  have hcuteq : (3 : ℝ) ^ ((1 / 2 : ℝ) * p * (N0 : ℝ)) = A1 ^ p := by
    rw [hA1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  -- the remainder term
  have hNge : 2 * Ctail ≤ ((N0 : ℝ) + 1) := by
    have h1 : 4 * Ctail ≤ (N0 : ℝ) := by
      rw [hN0]
      exact Nat.le_ceil _
    linarith only [h1, hCtail]
  have hE : (1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma +
      -(((N0 : ℝ) + 1) * (8 * Ctail * M.gamma)⁻¹) ≤ 0 := by
    have hginv : (0 : ℝ) ≤ M.gamma⁻¹ := (inv_pos.2 hgam).le
    have hfrac : (1 : ℝ) / 4 ≤ ((N0 : ℝ) + 1) / (8 * Ctail) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * Ctail)]
      linarith only [hNge]
    have hmul := mul_le_mul_of_nonneg_right hfrac hginv
    have hL : (1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma = (1 / 4 : ℝ) * M.gamma⁻¹ := by
      rw [show (1 - (1 : ℝ) / 2) ^ (2 : ℕ) = 1 / 4 by norm_num, div_eq_mul_inv]
    have hR : ((N0 : ℝ) + 1) * (8 * Ctail * M.gamma)⁻¹ =
        (((N0 : ℝ) + 1) / (8 * Ctail)) * M.gamma⁻¹ := by
      field_simp
    rw [hL, hR]
    linarith only [hmul]
  have hremreal : 2 * ((Ctail * Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma)) *
      ((3 : ℝ) ^ ((1 / 2 : ℝ) * p) *
        Real.exp (-((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / (Ctail * M.gamma)))) ^ (N0 + 1)) ≤
      A2 ^ p := by
    have hpow : (Real.exp (-(8 * Ctail * M.gamma)⁻¹)) ^ (N0 + 1) =
        Real.exp (-(((N0 : ℝ) + 1) * (8 * Ctail * M.gamma)⁻¹)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hexpone : Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma) *
        Real.exp (-(((N0 : ℝ) + 1) * (8 * Ctail * M.gamma)⁻¹)) ≤ 1 := by
      rw [← Real.exp_add]
      calc Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma +
            -(((N0 : ℝ) + 1) * (8 * Ctail * M.gamma)⁻¹)) ≤ Real.exp 0 :=
            Real.exp_le_exp.2 hE
        _ = 1 := Real.exp_zero
    have hstep : 2 * ((Ctail * Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma)) *
        ((3 : ℝ) ^ ((1 / 2 : ℝ) * p) *
          Real.exp (-((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / (Ctail * M.gamma)))) ^ (N0 + 1)) ≤
        2 * Ctail := by
      rw [hrhoval, hpow,
        show 2 * (Ctail * Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma) *
            Real.exp (-(((N0 : ℝ) + 1) * (8 * Ctail * M.gamma)⁻¹))) =
          2 * Ctail * (Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma) *
            Real.exp (-(((N0 : ℝ) + 1) * (8 * Ctail * M.gamma)⁻¹))) by ring]
      calc 2 * Ctail * (Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma) *
            Real.exp (-(((N0 : ℝ) + 1) * (8 * Ctail * M.gamma)⁻¹)))
          ≤ 2 * Ctail * 1 :=
            mul_le_mul_of_nonneg_left hexpone (by positivity)
        _ = 2 * Ctail := by ring
    refine hstep.trans ?_
    have hA2p : A2 ≤ A2 ^ p := by
      have h := Real.rpow_le_rpow_of_exponent_le hA2one hp
      rwa [Real.rpow_one] at h
    have h2C : 2 * Ctail ≤ A2 := by
      rw [hA2]
      exact le_max_right _ _
    linarith only [hA2p, h2C]
  -- assemble
  have hsum : A1 ^ p + A2 ^ p ≤ (2 * max A1 A2) ^ p := by
    have hm0 : (0 : ℝ) ≤ max A1 A2 := le_trans zero_le_one hmaxone
    have h1 : A1 ^ p ≤ (max A1 A2) ^ p :=
      Real.rpow_le_rpow (by linarith only [hA1one]) (le_max_left _ _) hppos.le
    have h2 : A2 ^ p ≤ (max A1 A2) ^ p :=
      Real.rpow_le_rpow (by linarith only [hA2one]) (le_max_right _ _) hppos.le
    have h3 : (2 : ℝ) ^ p * (max A1 A2) ^ p = (2 * max A1 A2) ^ p :=
      (Real.mul_rpow (by norm_num) hm0).symm
    have h4 : (2 : ℝ) ≤ (2 : ℝ) ^ p := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
      rwa [Real.rpow_one] at h
    have hmp : (0 : ℝ) ≤ (max A1 A2) ^ p := Real.rpow_nonneg hm0 p
    calc A1 ^ p + A2 ^ p ≤ (max A1 A2) ^ p + (max A1 A2) ^ p := add_le_add h1 h2
      _ = 2 * (max A1 A2) ^ p := by ring
      _ ≤ (2 : ℝ) ^ p * (max A1 A2) ^ p := mul_le_mul_of_nonneg_right h4 hmp
      _ = (2 * max A1 A2) ^ p := h3
  have hKpos : (0 : ℝ) < 2 * max A1 A2 := by linarith only [hmaxone]
  calc ENNReal.ofReal ((3 : ℝ) ^ ((1 / 2 : ℝ) * p * (N0 : ℝ))) +
        ENNReal.ofReal (2 * ((Ctail * Real.exp ((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / M.gamma)) *
          ((3 : ℝ) ^ ((1 / 2 : ℝ) * p) *
            Real.exp (-((1 - (1 : ℝ) / 2) ^ (2 : ℕ) / (Ctail * M.gamma)))) ^ (N0 + 1)))
      ≤ ENNReal.ofReal (A1 ^ p) + ENNReal.ofReal (A2 ^ p) := by
        exact add_le_add (le_of_eq (by rw [hcuteq])) (ENNReal.ofReal_le_ofReal hremreal)
    _ = ENNReal.ofReal (A1 ^ p + A2 ^ p) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg (by linarith only [hA1one]) p)
          (Real.rpow_nonneg (by linarith only [hA2one]) p)).symm
    _ ≤ ENNReal.ofReal ((2 * max A1 A2) ^ p) := ENNReal.ofReal_le_ofReal hsum
    _ = ENNReal.ofReal (2 * max A1 A2) ^ p := (ENNReal.ofReal_rpow_of_pos hKpos).symm

end

end Algsuperdiff.Section4.Provider.RegularityMoment
