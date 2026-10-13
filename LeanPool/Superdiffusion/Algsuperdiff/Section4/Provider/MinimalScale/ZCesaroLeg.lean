/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.KickingAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.ZAssembly

/-!
# ZCesaroLeg

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `Z^{(1)}` leg: Markov on the kicking lemma, the centre union, and the tail

ABK26, §4.2.  The chain is the one the manuscript performs:

1. **The centre transfer.**  The per-centre window average at a centre `y` has
   the mass of the origin one
   (`GoodEvents.measure_lt_mul_sum_indicator_goodEventAt`, a consequence of the
   two proved translation identities).
2. **The event inclusion** `𝒢(k; s, s√δ) ⊆ 𝒢(k; s, 1)` at `s√δ ≤ 1`
   (`goodEventBase_subset_one`), which is what lets the kicking lemma — stated at
   the tolerance `1` — bound the frozen score's own gated average.
3. **Markov on the `Γ₂` fluctuation** (`measure_center_cesaro_le`): the kicking
   lemma splits the average into `Xdet ≤ C c⋆^{−1}s^{−7/2}√γ` and a `Γ₂`
   fluctuation at scale `C c⋆^{−1}s^{−9/2}√γ j^{−1/2}`; at the level `t = √(A j)`
   the weak-Orlicz definition returns `exp(−A j)` with
   `A = c⋆² s⁹ δ² / (4 C_kick² γ)`.

4. **The centre union and the geometric closure** —
   `Algsuperdiff.Probability`'s `windowScale_tail_const_of_center_tails` at `D
   = 2d`, on the proved centre enumeration `centerFinset`
   (`card_centerFinset_le`, and `hcover` as the theorem
   `exists_center_finset_of_badCesaro`), followed by the `(N−1)`-shift
   absorption of `windowTailConst` into the frozen prefactor.

## The `δ`-floor is derived, not assumed — and the exponent closes exactly

The manuscript's Markov step needs `δ ≥ (2C + 2d log 3)
c⋆^{−1}s^{−7/2}γ^{1/2}`, i.e. at the corrected fluctuation exponent `δ ≥ 2C
c⋆^{−1}s^{−9/2}γ^{1/2}`.  Squaring, that is

`4 C_kick² γ ≤ c⋆² s⁹ δ²`,  equivalently  `1 ≤ A`,

and `minimal_scale_separation`'s regime clause supplies exactly `γ ≤
C^{−10}·δ²c⋆²s⁹`, so the floor holds as soon as `4 C_kick² ≤ C ≤ C^{10}`.
**The condition-exponent and the rate-exponent are both `s⁹`**: the kicking
envelope's `s^{−9/2}`, squared, is the frozen clause's `s⁹`.

## References

* ABK26, `p.minimal.scale.separation.sec4`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Proportion
open Algsuperdiff.Probability
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The kicking lemma's constant -/

/-- **The kicking lemma's constant** (`e.good.scale.kicking`, `d` only). -/
noncomputable def kickConst (d : ℕ) : ℝ := (exists_goodScaleKicking d).choose

theorem kickConst_pos (d : ℕ) : 0 < kickConst d := (exists_goodScaleKicking d).choose_spec.1

/-- **The kicking lemma at `kickConst d`.** -/
theorem kickConst_spec (d : ℕ) :
    ∀ M : ABKModel d, M.gamma ≤ (kickConst d)⁻¹ ^ 10 * Disorder.cstar M ^ 10 →
      ∀ s : {s : ℝ // 0 < s}, 8 * M.gamma ≤ (s : ℝ) → (s : ℝ) ≤ 1 / 4 →
        ∀ n m : ℤ, n < m →
          ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
            (∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
                    ∑ k ∈ Finset.Icc n m,
                      Set.indicator (goodEventBase M (cgEllipLowerConstant d) k s 1)
                        (fun omega' => fluxCorrectedErrorObservableSup M k s omega')
                        omega ≤
                  ENNReal.ofReal (Xdet omega + Xfluc omega)) ∧
            (∀ omega, Xdet omega ≤
              kickConst d * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (7 : ℕ))⁻¹ *
                Real.sqrt M.gamma)) ∧
            IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
              (kickConst d * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ (9 : ℕ))⁻¹ *
                  Real.sqrt M.gamma) *
                ((m - n : ℤ) : ℝ) ^ (-(1 : ℝ) / 2)) :=
  (exists_goodScaleKicking d).choose_spec.2

/-! ## 2. The event inclusion `𝒢(k; s, ep) ⊆ 𝒢(k; s, 1)` -/

/-- **`𝒢(k; s, ep) ⊆ 𝒢(k; s, 1)` for `0 ≤ ep ≤ 1`.**  `𝒢₀` is
untouched, `𝒢₁`'s threshold carries the factor `s·ep` and `𝒢₂`'s is `ep`, so both
are monotone in `ep`. -/
theorem goodEventBase_subset_one (M : ABKModel d) (Ccg : ℝ) (k : ℤ) (s : {s : ℝ // 0 < s})
    {ep : ℝ} (hep0 : 0 ≤ ep) (hep1 : ep ≤ 1) :
    goodEventBase M Ccg k s ep ⊆ goodEventBase M Ccg k s 1 := by
  have hfac : (0 : ℝ) ≤ Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
    mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _))
  intro omega homega
  refine ⟨⟨goodEventBase_subset_eventG0 M Ccg k s ep homega, ?_⟩,
    eventG2_subset_of_le M k s hep0 hep1 (goodEventBase_subset_eventG2 M Ccg k s ep homega)⟩
  refine eventG1_subset_of_le M k (s : ℝ) ?_ ?_
    (goodEventBase_subset_eventG1 M Ccg k s ep homega)
  · exact mul_nonneg (mul_nonneg (mul_nonneg s.2.le hep0) (Real.sqrt_nonneg _))
      (inv_nonneg.2 (Real.sqrt_nonneg _))
  · have hstep : (s : ℝ) * ep ≤ (s : ℝ) * 1 := mul_le_mul_of_nonneg_left hep1 s.2.le
    have hmul := mul_le_mul_of_nonneg_right hstep hfac
    calc (s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹
        = (s : ℝ) * ep * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := by ring
      _ ≤ (s : ℝ) * 1 * (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) := hmul
      _ = (s : ℝ) * 1 * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ := by ring

/-- The gated window average is monotone in the tolerance. -/
theorem sum_indicator_le_of_le_one (M : ABKModel d) (Ccg : ℝ) (s : {s : ℝ // 0 < s})
    {ep : ℝ} (hep0 : 0 ≤ ep) (hep1 : ep ≤ 1) (n m : ℤ) (c : ℝ≥0∞)
    (omega : Cutoff.CutoffSample d) :
    c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (goodEventBase M Ccg k s ep)
          (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega ≤
      c * ∑ k ∈ Finset.Icc n m,
        Set.indicator (goodEventBase M Ccg k s 1)
          (fun omega' => fluxCorrectedErrorObservableSup M k s omega') omega := by
  refine mul_le_mul_right (Finset.sum_le_sum fun k _ => ?_) _
  by_cases hmem : omega ∈ goodEventBase M Ccg k s ep
  · rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (goodEventBase_subset_one M Ccg k s hep0 hep1 hmem)]
  · rw [Set.indicator_of_notMem hmem]
    exact zero_le

/-! ## 3. The `√`-arithmetic of the Markov level -/

/-- The square of the envelope. -/
theorem envNine_sq (M : ABKModel d) {s : ℝ} (hs : 0 < s) :
    ((Disorder.cstar M)⁻¹ * ((Real.sqrt s) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) ^ (2 : ℕ) =
      M.gamma / (Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) := by
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hsq0 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsq9 : ((Real.sqrt s) ^ (9 : ℕ)) ^ (2 : ℕ) = s ^ (9 : ℕ) := by
    rw [← pow_mul, show (9 : ℕ) * 2 = 2 * 9 from by norm_num, pow_mul, Real.sq_sqrt hs.le]
  have hgsq : (Real.sqrt M.gamma) ^ (2 : ℕ) = M.gamma := Real.sq_sqrt hgam.le
  calc ((Disorder.cstar M)⁻¹ * ((Real.sqrt s) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) ^ (2 : ℕ)
      = ((Disorder.cstar M)⁻¹) ^ (2 : ℕ) * (((Real.sqrt s) ^ (9 : ℕ))⁻¹) ^ (2 : ℕ) *
          (Real.sqrt M.gamma) ^ (2 : ℕ) := by ring
    _ = (Disorder.cstar M ^ (2 : ℕ))⁻¹ * (s ^ (9 : ℕ))⁻¹ * M.gamma := by
        rw [inv_pow, inv_pow, hsq9, hgsq]
    _ = M.gamma / (Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) := by
        rw [div_eq_mul_inv, mul_inv]
        ring

/-- The reciprocal square root, in `√` form. -/
theorem rpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(1 : ℝ) / 2) = (Real.sqrt x)⁻¹ := by
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) from by ring, Real.rpow_neg hx, ← Real.sqrt_eq_rpow]

/-- `t ^ (2 : ℝ) = t ^ (2 : ℕ)`. -/
theorem rpow_two_eq_sq (t : ℝ) : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

/-! ## 4. The per-centre Markov bound -/

/-- `A = c⋆² s⁹ δ² / (4 C_kick² γ) ≥ 1`.

Route: the centre transfer, the tolerance inclusion `𝒢(k;s,s√δ) ⊆ 𝒢(k;s,1)`,
the kicking lemma, and Markov at the weak-Orlicz level `t = √(A j)`.  The
δ-floor `δ ≥ 2 C_kick c⋆^{−1}s^{−9/2}γ^{1/2}` is **derived** from the regime
clause — squared, it is exactly `1 ≤ A` — and no power of `s` is absorbed. -/
theorem measure_center_cesaro_le (C : ℝ) (hC1 : 1 ≤ C) (hCa : kickConst d ≤ C)
    (hCb : 4 * kickConst d ^ (2 : ℕ) ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hd0 : 0 < delta) (hd2 : delta ≤ 1 / 2)
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (y : Vec d) (m : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    ((Cutoff.cutoffSampleLaw M).toMeasure).real
        {omega | ENNReal.ofReal delta <
          centerCesaroScore M s delta hs y (m - (j : ℤ)) m omega} ≤
      Real.exp
        (-(delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) /
            ((4 * kickConst d ^ (2 : ℕ)) * M.gamma)) * (j : ℝ)) := by
  have hCk0 : (0 : ℝ) < kickConst d := kickConst_pos d
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hs1 : s ≤ 1 := by linarith only [hs4]
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le zero_lt_one hjR
  have hsqj0 : (0 : ℝ) < Real.sqrt (j : ℝ) := Real.sqrt_pos.2 hjpos
  -- the rate `A`, and the δ-floor `1 ≤ A`
  have hnum0 : (0 : ℝ) < delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) :=
    mul_pos (mul_pos (pow_pos hd0 2) (pow_pos hcs0 2)) (pow_pos hs 9)
  have hK0 : (0 : ℝ) < 4 * kickConst d ^ (2 : ℕ) := by positivity
  have hKgam : (0 : ℝ) < (4 * kickConst d ^ (2 : ℕ)) * M.gamma := mul_pos hK0 hgam0
  have hgam9 : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) :=
    le_trans hgam
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg (inv_nonneg.2 hC0.le) 10))
  have hKC : 4 * kickConst d ^ (2 : ℕ) ≤ C ^ (10 : ℕ) := by
    refine le_trans hCb ?_
    calc C = C ^ (1 : ℕ) := (pow_one C).symm
      _ ≤ C ^ (10 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
  have hpowinv : (4 * kickConst d ^ (2 : ℕ)) * C⁻¹ ^ (10 : ℕ) ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hC0 10)]
    exact hKC
  have hfloor : (4 * kickConst d ^ (2 : ℕ)) * M.gamma ≤
      delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) := by
    calc (4 * kickConst d ^ (2 : ℕ)) * M.gamma
        ≤ (4 * kickConst d ^ (2 : ℕ)) *
            (C⁻¹ ^ (10 : ℕ) *
              (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ))) :=
          mul_le_mul_of_nonneg_left hgam9 hK0.le
      _ = ((4 * kickConst d ^ (2 : ℕ)) * C⁻¹ ^ (10 : ℕ)) *
            (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) := by ring
      _ ≤ 1 * (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) :=
          mul_le_mul_of_nonneg_right hpowinv hnum0.le
      _ = delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) := one_mul _
  set A : ℝ := delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) /
    ((4 * kickConst d ^ (2 : ℕ)) * M.gamma) with hAdef
  have hA1 : 1 ≤ A := by
    rw [hAdef, le_div_iff₀ hKgam, one_mul]
    exact hfloor
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  have hsqA1 : (1 : ℝ) ≤ Real.sqrt A := by
    have h := Real.sqrt_le_sqrt hA1
    rwa [Real.sqrt_one] at h
  -- the kicking lemma at the window `[m − j, m]`
  have hregK : M.gamma ≤ (kickConst d)⁻¹ ^ 10 * Disorder.cstar M ^ 10 := by
    refine le_trans hgam ?_
    refine le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _)
      (pow_nonneg (inv_nonneg.2 hC0.le) 10)) ?_
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (inv_nonneg.2 hC0.le) (inv_anti₀ hCk0 hCa) 10) (pow_nonneg hcs0.le 10)
  have hjlt : m - (j : ℤ) < m := by omega
  obtain ⟨Xdet, Xfluc, hdom, hdet, hfluc⟩ :=
    kickConst_spec d M hregK ⟨s, hs⟩ hwin hs4 (m - (j : ℤ)) m hjlt
  -- the envelope quantities and the Markov level
  have hE90 : (0 : ℝ) < (Disorder.cstar M)⁻¹ * ((Real.sqrt s) ^ (9 : ℕ))⁻¹ *
      Real.sqrt M.gamma := by
    have hsq0 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 hs
    have hgsq0 : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 hgam0
    positivity
  set G : ℝ := kickConst d *
    ((Disorder.cstar M)⁻¹ * ((Real.sqrt s) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) with hGdef
  have hG0 : (0 : ℝ) < G := by
    rw [hGdef]
    exact mul_pos hCk0 hE90
  set t : ℝ := Real.sqrt (A * (j : ℝ)) with htdef
  have hAj0 : (0 : ℝ) ≤ A * (j : ℝ) := mul_nonneg hA0 hjpos.le
  have hAj1 : (1 : ℝ) ≤ A * (j : ℝ) := by
    have h := mul_le_mul hA1 hjR zero_le_one hA0
    rwa [one_mul] at h
  have ht1 : (1 : ℝ) ≤ t := by
    rw [htdef]
    have h := Real.sqrt_le_sqrt hAj1
    rwa [Real.sqrt_one] at h
  -- the level identity: `G·j^{−1/2}·t = G√A ≤ δ/2`
  have hGut : G * (Real.sqrt (j : ℝ))⁻¹ * t = G * Real.sqrt A := by
    rw [htdef, Real.sqrt_mul hA0]
    field_simp
  have hid : 4 * G ^ (2 : ℕ) * A = delta ^ (2 : ℕ) := by
    rw [hGdef, hAdef, mul_pow, envNine_sq M hs]
    field_simp
  have hGsqA : G * Real.sqrt A ≤ delta / 2 := by
    have hsq : (2 * (G * Real.sqrt A)) ^ (2 : ℕ) = 4 * G ^ (2 : ℕ) * A := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hA0]
      ring
    have hle : 2 * (G * Real.sqrt A) ≤ delta :=
      le_of_pow_le_pow_left₀ (by norm_num) hd0.le (le_of_eq (hsq.trans hid))
    linarith only [hle]
  -- the deterministic slot is below `δ/2`
  have hXdet : ∀ omega, Xdet omega ≤ delta / 2 := by
    intro omega
    have h1 := hdet omega
    have h2 : kickConst d * ((Disorder.cstar M)⁻¹ * ((Real.sqrt s) ^ (7 : ℕ))⁻¹ *
        Real.sqrt M.gamma) ≤ G := by
      rw [hGdef]
      exact mul_le_mul_of_nonneg_left (envSeven_le_envNine M ⟨s, hs⟩ hs1) hCk0.le
    have h3 : G ≤ G * Real.sqrt A := by
      have h := mul_le_mul_of_nonneg_left hsqA1 hG0.le
      rwa [mul_one] at h
    linarith only [h1, h2, h3, hGsqA]
  -- the `Γ₂` scale, in `√` form
  have hcast : ((m - (m - (j : ℤ)) : ℤ) : ℝ) = (j : ℝ) := by
    push_cast
    ring
  have hscale : kickConst d *
        ((Disorder.cstar M)⁻¹ * ((Real.sqrt s) ^ (9 : ℕ))⁻¹ * Real.sqrt M.gamma) *
        ((m - (m - (j : ℤ)) : ℤ) : ℝ) ^ (-(1 : ℝ) / 2) =
      G * (Real.sqrt (j : ℝ))⁻¹ := by
    rw [hcast, rpow_neg_half_eq_inv_sqrt hjpos.le, hGdef]
  rw [hscale] at hfluc
  -- the three measure steps
  have hep0 : (0 : ℝ) ≤ s * Real.sqrt delta :=
    mul_nonneg hs.le (Real.sqrt_nonneg _)
  have hep1 : s * Real.sqrt delta ≤ 1 := by
    have hsqd : Real.sqrt delta ≤ 1 := Real.sqrt_le_one.2 (by linarith only [hd2])
    have h := mul_le_mul_of_nonneg_left hsqd hs.le
    rw [mul_one] at h
    linarith only [h, hs4]
  have hstep1 : ((Cutoff.cutoffSampleLaw M).toMeasure).real
        {omega | ENNReal.ofReal delta <
          centerCesaroScore M s delta hs y (m - (j : ℤ)) m omega} =
      ((Cutoff.cutoffSampleLaw M).toMeasure).real
        {omega | ENNReal.ofReal delta <
          (((m - (m - (j : ℤ))).toNat : ℝ≥0∞) + 1)⁻¹ *
            ∑ k ∈ Finset.Icc (m - (j : ℤ)) m,
              Set.indicator
                (goodEventBase M (cgEllipLowerConstant d) k ⟨s, hs⟩ (s * Real.sqrt delta))
                (fun omega' => fluxCorrectedErrorObservableSup M k ⟨s, hs⟩ omega')
                omega} := by
    rw [measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal
      (GoodEvents.measure_lt_mul_sum_indicator_goodEventAt M (cgEllipLowerConstant d) y
        ⟨s, hs⟩ (s * Real.sqrt delta) (m - (j : ℤ)) m
        ((((m - (m - (j : ℤ))).toNat : ℝ≥0∞) + 1)⁻¹) (ENNReal.ofReal delta))
  have hstep2 : ((Cutoff.cutoffSampleLaw M).toMeasure).real
        {omega | ENNReal.ofReal delta <
          (((m - (m - (j : ℤ))).toNat : ℝ≥0∞) + 1)⁻¹ *
            ∑ k ∈ Finset.Icc (m - (j : ℤ)) m,
              Set.indicator
                (goodEventBase M (cgEllipLowerConstant d) k ⟨s, hs⟩ (s * Real.sqrt delta))
                (fun omega' => fluxCorrectedErrorObservableSup M k ⟨s, hs⟩ omega')
                omega} ≤
      ((Cutoff.cutoffSampleLaw M).toMeasure).real
        {omega | ENNReal.ofReal delta <
          (((m - (m - (j : ℤ))).toNat : ℝ≥0∞) + 1)⁻¹ *
            ∑ k ∈ Finset.Icc (m - (j : ℤ)) m,
              Set.indicator (goodEventBase M (cgEllipLowerConstant d) k ⟨s, hs⟩ 1)
                (fun omega' => fluxCorrectedErrorObservableSup M k ⟨s, hs⟩ omega')
                omega} := by
    refine measureReal_mono (fun omega homega => ?_) (measure_ne_top _ _)
    exact lt_of_lt_of_le homega
      (sum_indicator_le_of_le_one M (cgEllipLowerConstant d) ⟨s, hs⟩ hep0 hep1
        (m - (j : ℤ)) m ((((m - (m - (j : ℤ))).toNat : ℝ≥0∞) + 1)⁻¹) omega)
  have hstep3 : ((Cutoff.cutoffSampleLaw M).toMeasure).real
        {omega | ENNReal.ofReal delta <
          (((m - (m - (j : ℤ))).toNat : ℝ≥0∞) + 1)⁻¹ *
            ∑ k ∈ Finset.Icc (m - (j : ℤ)) m,
              Set.indicator (goodEventBase M (cgEllipLowerConstant d) k ⟨s, hs⟩ 1)
                (fun omega' => fluxCorrectedErrorObservableSup M k ⟨s, hs⟩ omega')
                omega} ≤
      ((Cutoff.cutoffSampleLaw M).toMeasure).real
        (absTailEvent Xfluc (G * (Real.sqrt (j : ℝ))⁻¹ * t)) := by
    rw [measureReal_def, measureReal_def]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [hdom] with omega homega hmem
    have h1 : ENNReal.ofReal delta < ENNReal.ofReal (Xdet omega + Xfluc omega) :=
      lt_of_lt_of_le hmem homega
    have h2 : delta < Xdet omega + Xfluc omega :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd0.le).1 h1
    have h3 : Xfluc omega ≤ |Xfluc omega| := le_abs_self _
    change G * (Real.sqrt (j : ℝ))⁻¹ * t < |Xfluc omega|
    rw [hGut]
    linarith only [h2, hXdet omega, h3, hGsqA]
  -- Markov at the level `t`
  have hmarkov := (isBigO_gammaSigma_iff.1 hfluc) ht1
  have htsq : t ^ (2 : ℝ) = A * (j : ℝ) := by
    rw [rpow_two_eq_sq, htdef, Real.sq_sqrt hAj0]
  rw [htsq] at hmarkov
  refine le_trans (le_trans (le_of_eq hstep1) (le_trans hstep2 hstep3)) ?_
  refine le_trans hmarkov (le_of_eq ?_)
  rw [hAdef]
  congr 1
  ring

/-! ## 5. `hcover` for the Cesàro leg, as a theorem -/

/-- **`hcover`, as a theorem** (the Cesàro leg).  A bad Cesàro window is witnessed
by a centre of the proved explicit enumeration; the mechanism is `lt_iSup_iff`
in `ℝ≥0∞`, so no finiteness and no positivity of `δ` is used. -/
theorem exists_center_finset_of_badCesaro (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    (m : ℤ) (j : ℕ) (omega : Cutoff.CutoffSample d)
    (h : badCesaro M s delta hs m j omega) :
    ∃ z ∈ centerFinset d m j,
      ENNReal.ofReal delta <
        centerCesaroScore M s delta hs (triadicLatticePoint (m - (j : ℤ) - 1) z)
          (m - (j : ℤ)) m omega := by
  obtain ⟨z, hzmem, hz⟩ := exists_center_of_badCesaro M s delta hs m j h
  refine ⟨z, ?_, hz⟩
  exact (Proportion.mem_latticeCubeFinset_iff (by omega : m - (j : ℤ) - 1 ≤ m)).2 hzmem

/-! ## 6. The assembled constant of the `Z^{(1)}` leg -/

/-- **The `Z^{(1)}` leg's constant.**  Four floor duties, all functions of `d`
alone: `kickConst d` (the kicking lemma's own regime clause), `8·kickConst d²`
(the δ-floor **and** the halving `2c₀ ≤ A` that pays for the centre count),
`2·3^{2d}` (the union-bound prefactor against the geometric-summation constant
`(1 − e^{−c₀})⁻¹`), and `4 d log 3` (the absorption `2d log 3 + c₀ ≤ A`). -/
noncomputable def zOneConst (d : ℕ) : ℝ :=
  max (max (kickConst d) (8 * kickConst d ^ (2 : ℕ)))
    (max (2 * (3 : ℝ) ^ (2 * d)) (4 * (d : ℝ) * Real.log 3))

theorem kickConst_le_zOneConst (d : ℕ) : kickConst d ≤ zOneConst d :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem eight_mul_kickConst_sq_le_zOneConst (d : ℕ) :
    8 * kickConst d ^ (2 : ℕ) ≤ zOneConst d :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem two_mul_three_pow_le_zOneConst (d : ℕ) : 2 * (3 : ℝ) ^ (2 * d) ≤ zOneConst d :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem four_mul_log_three_le_zOneConst (d : ℕ) :
    4 * (d : ℝ) * Real.log 3 ≤ zOneConst d :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem one_le_zOneConst (d : ℕ) : 1 ≤ zOneConst d := by
  refine le_trans ?_ (two_mul_three_pow_le_zOneConst d)
  have h : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * d) := one_le_pow₀ (by norm_num)
  linarith only [h]

/-! ## 7. The geometric tail of the Cesàro random scale -/

/-- **The geometric tail of the Cesàro-`𝓔` random scale, at the frozen
prefactor-tail shape**

`P[N ≤ Z¹] ≤ C exp(−(N−1) s⁹ c⋆² δ² /(C γ))`.

The route: the per-centre Markov bound `measure_center_cesaro_le`, the proved
centre count `card_centerFinset_le` and cover
`exists_center_finset_of_badCesaro` (both theorems — neither is a binder), then
`Algsuperdiff.Probability.windowScale_tail_const_of_center_tails` at `D = 2d`,
whose `windowTailConst (2d) c₀` prefactor is absorbed by the `(N−1)` shift of
the frozen display.  The regime clause is `minimal_scale_separation`'s own, at
`s⁹`. -/
theorem measure_tail_badCesaro_le (C : ℝ) (hC : zOneConst d ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hd0 : 0 < delta) (hd2 : delta ≤ 1 / 2)
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (m : ℤ) (N : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN (badCesaro M s delta hs m) omega} ≤
      ENNReal.ofReal
        (C *
          Real.exp
            (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
              (C * M.gamma))) := by
  classical
  have hCk0 : (0 : ℝ) < kickConst d := kickConst_pos d
  have hC1 : (1 : ℝ) ≤ C := le_trans (one_le_zOneConst d) hC
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hCa : kickConst d ≤ C := le_trans (kickConst_le_zOneConst d) hC
  have h8Ck : 8 * kickConst d ^ (2 : ℕ) ≤ C :=
    le_trans (eight_mul_kickConst_sq_le_zOneConst d) hC
  have hCb : 4 * kickConst d ^ (2 : ℕ) ≤ C := by
    have h : (0 : ℝ) ≤ kickConst d ^ (2 : ℕ) := pow_nonneg hCk0.le 2
    linarith only [h8Ck, h]
  have h3dC : 2 * (3 : ℝ) ^ (2 * d) ≤ C := le_trans (two_mul_three_pow_le_zOneConst d) hC
  have hlogC : 4 * (d : ℝ) * Real.log 3 ≤ C := le_trans (four_mul_log_three_le_zOneConst d) hC
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hnumpos : (0 : ℝ) < delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) :=
    mul_pos (mul_pos (pow_pos hd0 2) (pow_pos hcs0 2)) (pow_pos hs 9)
  have hK0 : (0 : ℝ) < 4 * kickConst d ^ (2 : ℕ) := by positivity
  have hKgam : (0 : ℝ) < (4 * kickConst d ^ (2 : ℕ)) * M.gamma := mul_pos hK0 hgam0
  have hCgam : (0 : ℝ) < C * M.gamma := mul_pos hC0 hgam0
  set A : ℝ := delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) /
    ((4 * kickConst d ^ (2 : ℕ)) * M.gamma) with hAdef
  set c0 : ℝ := delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) /
    (C * M.gamma) with hc0def
  -- the regime clause in product form, and the two rate lower bounds
  have hgam9 : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) :=
    le_trans hgam
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg (inv_nonneg.2 hC0.le) 10))
  have hcancelC : (C : ℝ) ^ (10 : ℕ) * C⁻¹ ^ (10 : ℕ) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hC0), one_pow]
  have hX : C ^ (10 : ℕ) * M.gamma ≤
      delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) := by
    calc C ^ (10 : ℕ) * M.gamma
        ≤ C ^ (10 : ℕ) *
            (C⁻¹ ^ (10 : ℕ) *
              (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ))) :=
          mul_le_mul_of_nonneg_left hgam9 (pow_nonneg hC0.le 10)
      _ = (C ^ (10 : ℕ) * C⁻¹ ^ (10 : ℕ)) *
            (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) := by ring
      _ = delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ) := by
          rw [hcancelC, one_mul]
  have hAlow : C ≤ A := by
    rw [hAdef, le_div_iff₀ hKgam]
    refine le_trans ?_ hX
    have h1 : C * (4 * kickConst d ^ (2 : ℕ)) ≤ C ^ (10 : ℕ) := by
      calc C * (4 * kickConst d ^ (2 : ℕ)) ≤ C * C :=
            mul_le_mul_of_nonneg_left hCb hC0.le
        _ = C ^ (2 : ℕ) := by ring
        _ ≤ C ^ (10 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
    calc C * ((4 * kickConst d ^ (2 : ℕ)) * M.gamma)
        = (C * (4 * kickConst d ^ (2 : ℕ))) * M.gamma := by ring
      _ ≤ C ^ (10 : ℕ) * M.gamma := mul_le_mul_of_nonneg_right h1 hgam0.le
  have hc0low : 1 ≤ c0 := by
    rw [hc0def, le_div_iff₀ hCgam]
    refine le_trans ?_ hX
    have h1 : C ≤ C ^ (10 : ℕ) := by
      calc C = C ^ (1 : ℕ) := (pow_one C).symm
        _ ≤ C ^ (10 : ℕ) := pow_le_pow_right₀ hC1 (by norm_num)
    calc (1 : ℝ) * (C * M.gamma) = C * M.gamma := one_mul _
      _ ≤ C ^ (10 : ℕ) * M.gamma := mul_le_mul_of_nonneg_right h1 hgam0.le
  have hc0pos : (0 : ℝ) < c0 := lt_of_lt_of_le zero_lt_one hc0low
  have h2c0A : 2 * c0 ≤ A := by
    have hstep : 2 * c0 =
        (2 * (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ))) /
          (C * M.gamma) := by
      rw [hc0def]; ring
    rw [hstep, hAdef, div_le_div_iff₀ hCgam hKgam]
    have h := mul_le_mul_of_nonneg_left h8Ck (mul_nonneg hnumpos.le hgam0.le)
    linarith only [h]
  have h4d : 4 * (d : ℝ) * Real.log 3 ≤ A := le_trans hlogC hAlow
  have hcast2d : ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
  have habsorb : ((2 * d : ℕ) : ℝ) * Real.log 3 + c0 ≤ A := by
    rw [hcast2d]
    linarith only [h4d, h2c0A]
  -- the per-centre tails
  have hcenter : ∀ j : ℕ, 1 ≤ j → ∀ z ∈ centerFinset d m j,
      ((Cutoff.cutoffSampleLaw M).toMeasure).real
          {omega | ENNReal.ofReal delta <
            centerCesaroScore M s delta hs
              (triadicLatticePoint (m - (j : ℤ) - 1) z) (m - (j : ℤ)) m omega} ≤
        Real.exp (-A * (j : ℝ)) := by
    intro j hj z _
    have hb := measure_center_cesaro_le C hC1 hCa hCb M s delta hs hs4 hd0 hd2 hgam hwin
      (triadicLatticePoint (m - (j : ℤ) - 1) z) m j hj
    rw [← hAdef] at hb
    exact hb
  -- the geometric closure
  have htail := Probability.windowScale_tail_const_of_center_tails
    ((Cutoff.cutoffSampleLaw M).toMeasure) (D := 2 * d) (badCesaro M s delta hs m)
    (centerFinset d m)
    (fun z j omega => ENNReal.ofReal delta <
      centerCesaroScore M s delta hs (triadicLatticePoint (m - (j : ℤ) - 1) z)
        (m - (j : ℤ)) m omega)
    hc0pos (fun j => card_centerFinset_le d m j) habsorb
    (fun j omega h => exists_center_finset_of_badCesaro M s delta hs m j omega h)
    hcenter N
  -- the prefactor, absorbed by the `(N − 1)` shift
  have hexpneg : Real.exp (-c0) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hc : Real.exp (-1 : ℝ) * Real.exp 1 = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h3 : Real.exp (-c0) ≤ Real.exp (-1 : ℝ) :=
      Real.exp_le_exp.2 (by linarith only [hc0low])
    have h4 : Real.exp (-1 : ℝ) * 2 ≤ Real.exp (-1 : ℝ) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    linarith only [h3, h4, hc]
  have hg : (0 : ℝ) < 1 - Real.exp (-c0) := by linarith only [hexpneg]
  have hfrac : (3 : ℝ) ^ (2 * d) / (1 - Real.exp (-c0)) ≤ C := by
    rw [div_le_iff₀ hg]
    have h1 : (1 / 2 : ℝ) ≤ 1 - Real.exp (-c0) := by linarith only [hexpneg]
    have h2 : C * (1 / 2 : ℝ) ≤ C * (1 - Real.exp (-c0)) :=
      mul_le_mul_of_nonneg_left h1 hC0.le
    linarith only [h2, h3dC]
  have hfrozen : -c0 * ((N : ℝ) - 1)
      = -(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
        (C * M.gamma) := by
    rw [hc0def]; ring
  have hpref : Probability.windowTailConst (2 * d) c0 * Real.exp (-c0 * (N : ℝ))
      ≤ C *
        Real.exp
          (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
            (C * M.gamma)) := by
    have hcomb : Real.exp c0 * Real.exp (-c0 * (N : ℝ)) = Real.exp (-c0 * ((N : ℝ) - 1)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Probability.windowTailConst (2 * d) c0 * Real.exp (-c0 * (N : ℝ))
        = ((3 : ℝ) ^ (2 * d) / (1 - Real.exp (-c0))) *
            (Real.exp c0 * Real.exp (-c0 * (N : ℝ))) := by
          rw [Probability.windowTailConst_eq]; ring
      _ = ((3 : ℝ) ^ (2 * d) / (1 - Real.exp (-c0))) * Real.exp (-c0 * ((N : ℝ) - 1)) := by
          rw [hcomb]
      _ ≤ C * Real.exp (-c0 * ((N : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
      _ = C *
            Real.exp
              (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
                    delta ^ (2 : ℕ)) /
                (C * M.gamma)) := by rw [hfrozen]
  have hmeas : (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN (badCesaro M s delta hs m) omega}
      = ENNReal.ofReal (((Cutoff.cutoffSampleLaw M).toMeasure).real
          {omega | (N : ℕ∞) ≤
            Probability.minimalScaleEN (badCesaro M s delta hs m) omega}) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hmeas]
  exact ENNReal.ofReal_le_ofReal (le_trans htail hpref)

/-! ## 8. The `hZ1tail` slot in its exact shape -/

/-- **The `hZ1tail` slot, discharged.**  The `Z¹` tail at half the prefactor and
the un-halved rate — the verbatim shape `ZAssembly.frozen_body_of_cesaro_tail`
consumes.

Length-`0` windows are free (`measure ≤ 1 ≤ C/2`), and for `N ≥ 1` the rate
`num/((C/2)γ)` delivered by `measure_tail_badCesaro_le` at `C/2` dominates the
displayed `num/(Cγ)`.  This is `ZAssembly.measure_tail_badDensity_le_half`'s
two-line rate-weakening pattern, applied to the Cesàro leg. -/
theorem measure_tail_badCesaro_le_half (C : ℝ) (hC : 2 * zOneConst d ≤ C)
    (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hd0 : 0 < delta) (hd2 : delta ≤ 1 / 2)
    (hgam : M.gamma ≤ C⁻¹ ^ (10 : ℕ) *
      min (Disorder.cstar M ^ (10 : ℕ))
        (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)))
    (hwin : 8 * M.gamma ≤ s) (m : ℤ) (N : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | (N : ℕ∞) ≤ Probability.minimalScaleEN (badCesaro M s delta hs m) omega} ≤
      ENNReal.ofReal
        (C / 2 *
          Real.exp
            (-(((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) /
              (C * M.gamma))) := by
  have hz1 : (1 : ℝ) ≤ zOneConst d := one_le_zOneConst d
  have hhalf : zOneConst d ≤ C / 2 := by linarith only [hC]
  have hC1 : (1 : ℝ) ≤ C / 2 := le_trans hz1 hhalf
  have hC0 : (0 : ℝ) < C := by linarith only [hC1]
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hnum0 : (0 : ℝ) ≤ s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg (pow_nonneg hs.le 9) (pow_nonneg hcs0.le 2)) (pow_nonneg hd0.le 2)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- the length-`0` window is free
    have huniv : {omega : Cutoff.CutoffSample d |
        (((0 : ℕ) : ℕ∞)) ≤ Probability.minimalScaleEN (badCesaro M s delta hs m) omega}
        = Set.univ :=
      Set.eq_univ_of_forall fun omega => by
        simp only [Set.mem_ofPred_eq, Nat.cast_zero]
        exact zero_le
    rw [huniv, measure_univ,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexpnn : (0 : ℝ) ≤
        -((((0 : ℕ) : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
            delta ^ (2 : ℕ)) / (C * M.gamma) := by
      rw [Nat.cast_zero,
        show -(((0 : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ))
            = s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ) from by ring]
      exact div_nonneg hnum0 (mul_pos hC0 hgam0).le
    have hexp1 : (1 : ℝ) ≤
        Real.exp
          (-((((0 : ℕ) : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
              delta ^ (2 : ℕ)) / (C * M.gamma)) := Real.one_le_exp hexpnn
    have hmul := mul_le_mul_of_nonneg_left hexp1 (by linarith only [hC1] : (0 : ℝ) ≤ C / 2)
    rw [mul_one] at hmul
    linarith only [hmul, hC1]
  · -- the substantive window lengths
    have hgamhalf : M.gamma ≤ (C / 2)⁻¹ ^ (10 : ℕ) *
        min (Disorder.cstar M ^ (10 : ℕ))
          (delta ^ (2 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * s ^ (9 : ℕ)) := by
      refine le_trans hgam (mul_le_mul_of_nonneg_right ?_ ?_)
      · exact pow_le_pow_left₀ (inv_nonneg.2 hC0.le)
          (inv_anti₀ (by linarith only [hC1]) (by linarith only [hC1])) 10
      · exact le_min (pow_nonneg hcs0.le 10)
          (mul_nonneg (mul_nonneg (pow_nonneg hd0.le 2) (pow_nonneg hcs0.le 2))
            (pow_nonneg hs.le 9))
    refine le_trans
      (measure_tail_badCesaro_le (C / 2) hhalf M s delta hs hs4 hd0 hd2 hgamhalf hwin m N) ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (by linarith only [hC1] : (0 : ℝ) ≤ C / 2))
    have hNge : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.one_le_cast.2 hN
    have hfac : (0 : ℝ) ≤ ((N : ℝ) - 1) * (s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
        delta ^ (2 : ℕ)) := mul_nonneg (by linarith only [hNge]) hnum0
    have hd1 : (0 : ℝ) < C / 2 * M.gamma := mul_pos (by linarith only [hC1]) hgam0
    have hd2' : C / 2 * M.gamma ≤ C * M.gamma :=
      mul_le_mul_of_nonneg_right (by linarith only [hC1]) hgam0.le
    have hkey : ((N : ℝ) - 1) * (s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
          delta ^ (2 : ℕ)) / (C * M.gamma)
        ≤ ((N : ℝ) - 1) * (s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) *
          delta ^ (2 : ℕ)) / (C / 2 * M.gamma) :=
      div_le_div_of_nonneg_left hfac hd1 hd2'
    rw [neg_div, neg_div]
    have hrw1 : ((N : ℝ) - 1) * s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)
        = ((N : ℝ) - 1) * (s ^ (9 : ℕ) * Disorder.cstar M ^ (2 : ℕ) * delta ^ (2 : ℕ)) := by
      ring
    rw [hrw1]
    linarith only [hkey]

end

end Algsuperdiff.Section4.Provider.MinimalScale
