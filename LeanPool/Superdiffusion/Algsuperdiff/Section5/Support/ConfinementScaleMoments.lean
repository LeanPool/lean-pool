/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ConfinementScale

/-!
# ConfinementScaleMoments

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The moments of the widened scale, and the existence of the confinement scale

Widening the displacement scales costs a constant factor in the moments: since

`S_n^p = sup_{k ≥ n} (S_k 3^{-2(k-n)})^p ≤ Σ_{k ≥ n} S_k^p 3^{-2p(k-n)}`,

a bound `E[S_k^p] ≤ C^p` valid at every scale gives

`E[S_n^p] ≤ C^p Σ_{j ≥ 0} 3^{-2pj} ≤ (9/8) C^p ≤ ((9/8) C)^p`  for `p ≥ 1`,

uniformly in `n`.  The geometric series is what the exponent `-2(k-n)` of the
widening is there for: at `p ≥ 1` its ratio is at most `1/9`.

That uniform bound is also what makes the confinement scale exist.  Its defining
set is empty only if `L (1 + S_n) > 3^n` at *every* scale `n`, and the
probability of that is at most the probability of the single event at one scale,
which Chebyshev's inequality bounds by `(C'/λ_n)^p` with `λ_n = 3^n/L - 1`.
Taking `n` large makes this arbitrarily small, so the set is almost surely
nonempty and, being bounded below, has a least element.

## Main results

* `measurable_widenedScale` — the widened scale is a measurable function of the
  sample, being a countable supremum.
* `lintegral_widenedScale_rpow_le` — the moment bound, uniform in the scale.
* `ae_nonempty_confinementSet`, `ae_exists_isConfinementScale` — the defining set
  is almost surely nonempty, so the confinement scale almost surely exists.

## References

* ABK26, the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Support

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## 1. Three arithmetic steps -/

/-- A supremum commutes with a positive power. -/
private theorem iSup_rpow_of_pos {iota : Sort*} (f : iota → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p := by
  refine le_antisymm ?_ (iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) hp.le)
  set s : ℝ≥0∞ := ⨆ i, f i ^ p with hs
  have hle : ∀ i, f i ≤ s ^ p⁻¹ := by
    intro i
    have h1 : f i ^ p ≤ s := le_iSup (fun i => f i ^ p) i
    have h2 : (f i ^ p) ^ p⁻¹ ≤ s ^ p⁻¹ := ENNReal.rpow_le_rpow h1 (by positivity)
    rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one] at h2
  calc (⨆ i, f i) ^ p ≤ (s ^ p⁻¹) ^ p := ENNReal.rpow_le_rpow (iSup_le hle) hp.le
    _ = s := by rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- The weight of the widening is a geometric factor of ratio `1/9`. -/
private theorem three_zpow_neg_two_mul (j : ℕ) :
    (3 : ℝ) ^ (-2 * (j : ℤ)) = ((9 : ℝ)⁻¹) ^ j := by
  rw [zpow_mul]
  norm_num

private theorem pow_rpow_comm (x : ℝ≥0∞) (j : ℕ) (p : ℝ) : (x ^ j) ^ p = (x ^ p) ^ j := by
  rw [← ENNReal.rpow_natCast x j, ← ENNReal.rpow_natCast (x ^ p) j, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  ring_nf

/-- The sum of the geometric series of the widening, at every exponent `p ≥ 1`. -/
private theorem geometric_widening_le {p : ℝ} (hp : 1 ≤ p) :
    (1 - ENNReal.ofReal ((9 : ℝ)⁻¹) ^ p)⁻¹ ≤ ENNReal.ofReal (9 / 8) := by
  have hle : ENNReal.ofReal ((9 : ℝ)⁻¹) ^ p ≤ ENNReal.ofReal ((9 : ℝ)⁻¹) := by
    calc ENNReal.ofReal ((9 : ℝ)⁻¹) ^ p ≤ ENNReal.ofReal ((9 : ℝ)⁻¹) ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_ge
            (by rw [ENNReal.ofReal_le_one]; norm_num) hp
      _ = ENNReal.ofReal ((9 : ℝ)⁻¹) := ENNReal.rpow_one _
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal ((9 : ℝ)⁻¹) ≤ 1 - ENNReal.ofReal ((9 : ℝ)⁻¹) ^ p :=
    tsub_le_tsub_left hle 1
  refine (ENNReal.inv_le_inv.mpr hsub).trans (le_of_eq ?_)
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-! ## 2. Measurability and the moments of the widened scale -/

/-- The widened scale is measurable: reindexed by `ℕ` it is a countable
supremum. -/
theorem measurable_widenedScale {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k)) (n : ℤ) :
    Measurable fun omega => widenedScale (fun k => S k omega) n := by
  have hrw : (fun omega => widenedScale (fun k => S k omega) n) =
      fun omega => ⨆ j : ℕ, ENNReal.ofReal (S (n + j) omega * (3 : ℝ) ^ (-2 * (j : ℤ))) := by
    funext omega
    exact widenedScale_eq_iSup_nat (fun k => S k omega) n
  rw [hrw]
  exact Measurable.iSup fun j =>
    ENNReal.measurable_ofReal.comp ((hmeas (n + j)).mul measurable_const)

/-- **The moments of the widened scale.**  A moment bound valid at every scale is
inherited by the widened scale, uniformly in the scale, at the cost of the factor
`9/8` coming from the geometric series of the widening. -/
theorem lintegral_widenedScale_rpow_le (mu : Measure Omega) {S : ℤ → Omega → ℝ}
    (hmeas : ∀ k, Measurable (S k)) {C p : ℝ} (hp : 1 ≤ p) (n : ℤ)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ p ∂mu) ≤ ENNReal.ofReal C ^ p) :
    (∫⁻ omega, widenedScale (fun k => S k omega) n ^ p ∂mu) ≤
      ENNReal.ofReal (C * (9 / 8)) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set r : ℝ≥0∞ := ENNReal.ofReal ((9 : ℝ)⁻¹) ^ p with hr
  have hrne : r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have hterm : ∀ (j : ℕ) (omega : Omega),
      ENNReal.ofReal (S (n + j) omega * (3 : ℝ) ^ (-2 * (j : ℤ))) ^ p =
        r ^ j * ENNReal.ofReal (S (n + j) omega) ^ p := by
    intro j omega
    rw [three_zpow_neg_two_mul, ENNReal.ofReal_mul' (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.ofReal_pow (by norm_num),
      pow_rpow_comm, hr, mul_comm]
  calc (∫⁻ omega, widenedScale (fun k => S k omega) n ^ p ∂mu)
      ≤ ∫⁻ omega, ∑' j : ℕ, r ^ j * ENNReal.ofReal (S (n + j) omega) ^ p ∂mu := by
        refine lintegral_mono fun omega => ?_
        rw [widenedScale_eq_iSup_nat, iSup_rpow_of_pos _ hp0]
        refine iSup_le fun j => ?_
        rw [hterm j omega]
        exact ENNReal.le_tsum (f := fun j : ℕ => r ^ j * ENNReal.ofReal (S (n + j) omega) ^ p) j
    _ = ∑' j : ℕ, ∫⁻ omega, r ^ j * ENNReal.ofReal (S (n + j) omega) ^ p ∂mu := by
        refine lintegral_tsum fun j => ?_
        exact (((ENNReal.measurable_ofReal.comp (hmeas (n + j))).pow_const
          p).const_mul (r ^ j)).aemeasurable
    _ = ∑' j : ℕ, r ^ j * ∫⁻ omega, ENNReal.ofReal (S (n + j) omega) ^ p ∂mu := by
        refine tsum_congr fun j => ?_
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top hrne)
    _ ≤ ∑' j : ℕ, r ^ j * ENNReal.ofReal C ^ p :=
        ENNReal.tsum_le_tsum fun j => by gcongr; exact hmom (n + j)
    _ = (∑' j : ℕ, r ^ j) * ENNReal.ofReal C ^ p := ENNReal.tsum_mul_right
    _ = (1 - r)⁻¹ * ENNReal.ofReal C ^ p := by rw [ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (9 / 8) * ENNReal.ofReal C ^ p := by
        gcongr
        exact geometric_widening_le hp
    _ ≤ ENNReal.ofReal (9 / 8) ^ p * ENNReal.ofReal C ^ p := by
        gcongr
        calc ENNReal.ofReal (9 / 8) = ENNReal.ofReal (9 / 8) ^ (1 : ℝ) :=
              (ENNReal.rpow_one _).symm
          _ ≤ ENNReal.ofReal (9 / 8) ^ p :=
              ENNReal.rpow_le_rpow_of_exponent_le
                (by rw [ENNReal.one_le_ofReal]; norm_num) hp
    _ = ENNReal.ofReal (C * (9 / 8)) ^ p := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9 / 8), mul_comm (9 / 8 : ℝ) C]

/-! ## 3. The confinement scale exists almost surely -/

/-- One scale of the defining set, read as a bound on the widened scale: if a
scale `n` with `L ≤ 3^n` is not admissible, the widened scale there is at least
`3^n / L - 1`. -/
private theorem le_widenedScale_of_not_mem {Stilde : ℤ → ℝ≥0∞} {L : ℝ} (hL : 0 < L) {n : ℤ}
    (hLn : L ≤ (3 : ℝ) ^ n) (hn : n ∉ confinementSet Stilde L) :
    ENNReal.ofReal ((3 : ℝ) ^ n / L - 1) ≤ Stilde n := by
  by_contra hlt
  push Not at hlt
  have hnn : (0 : ℝ) ≤ (3 : ℝ) ^ n / L - 1 := by
    rw [sub_nonneg, le_div_iff₀ hL, one_mul]
    exact hLn
  have hstep : ENNReal.ofReal L * (1 + Stilde n) <
      ENNReal.ofReal L * (1 + ENNReal.ofReal ((3 : ℝ) ^ n / L - 1)) :=
    ENNReal.mul_lt_mul_right (by simpa using hL) ENNReal.ofReal_ne_top
      (ENNReal.add_lt_add_left ENNReal.one_ne_top hlt)
  have hval : ENNReal.ofReal L * (1 + ENNReal.ofReal ((3 : ℝ) ^ n / L - 1)) =
      ENNReal.ofReal ((3 : ℝ) ^ n) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
      ← ENNReal.ofReal_add zero_le_one hnn, ← ENNReal.ofReal_mul hL.le]
    congr 1
    field_simp
    ring
  rw [hval] at hstep
  exact hn (le_of_lt hstep)

/-- The Chebyshev bound at one scale: the probability that no scale is
admissible is at most the probability that the widened scale at `n` exceeds
`3^n / L - 1`. -/
private theorem measure_not_nonempty_le (mu : Measure Omega) {S : ℤ → Omega → ℝ}
    (hmeas : ∀ k, Measurable (S k)) {C p L : ℝ} (hC : 0 ≤ C) (hp : 1 ≤ p) (hL : 0 < L)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ p ∂mu) ≤ ENNReal.ofReal C ^ p)
    {n : ℤ} (hLn : L ≤ (3 : ℝ) ^ n) (hlam : 0 < (3 : ℝ) ^ n / L - 1) :
    mu {omega | ¬ (confinementSet (fun n => widenedScale (fun k => S k omega) n) L).Nonempty} ≤
      ENNReal.ofReal ((C * (9 / 8) / ((3 : ℝ) ^ n / L - 1)) ^ p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hB : (0 : ℝ) ≤ C * (9 / 8) := by positivity
  set lam : ℝ := (3 : ℝ) ^ n / L - 1 with hlamdef
  have hepsne : ENNReal.ofReal lam ^ p ≠ 0 := by
    refine (ENNReal.rpow_pos (by simpa using hlam) ENNReal.ofReal_ne_top).ne'
  have hepstop : ENNReal.ofReal lam ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have hsub : {omega | ¬ (confinementSet
        (fun n => widenedScale (fun k => S k omega) n) L).Nonempty} ⊆
      {omega | ENNReal.ofReal lam ^ p ≤ widenedScale (fun k => S k omega) n ^ p} := by
    intro omega homega
    have hnot : n ∉ confinementSet (fun n => widenedScale (fun k => S k omega) n) L :=
      fun h => homega ⟨n, h⟩
    exact ENNReal.rpow_le_rpow (le_widenedScale_of_not_mem hL hLn hnot) hp0.le
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div
    (((measurable_widenedScale hmeas n).pow_const p).aemeasurable) hepsne hepstop).trans ?_
  have hnum : (∫⁻ omega, widenedScale (fun k => S k omega) n ^ p ∂mu) ≤
      ENNReal.ofReal (C * (9 / 8)) ^ p :=
    lintegral_widenedScale_rpow_le mu hmeas hp n hmom
  refine (ENNReal.div_le_div_right hnum _).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hB hp0.le,
    ENNReal.ofReal_rpow_of_nonneg hlam.le hp0.le,
    ← ENNReal.ofReal_div_of_pos (by positivity),
    Real.div_rpow hB hlam.le]

/-- **The defining set of the confinement scale is almost surely nonempty.**  At
one scale the failure probability is bounded by Chebyshev's inequality through
the uniform moment bound of the widened scale, and it tends to zero as the scale
grows. -/
theorem ae_nonempty_confinementSet (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k)) {C p L : ℝ}
    (hC : 0 ≤ C) (hp : 1 ≤ p) (hL : 0 < L)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ p ∂mu) ≤ ENNReal.ofReal C ^ p) :
    ∀ᵐ omega ∂mu,
      (confinementSet (fun n => widenedScale (fun k => S k omega) n) L).Nonempty := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hB : (0 : ℝ) ≤ C * (9 / 8) := by positivity
  rw [ae_iff]
  set E : Set Omega := {omega | ¬ (confinementSet
    (fun n => widenedScale (fun k => S k omega) n) L).Nonempty} with hE
  by_contra hne
  have hfin : mu E ≠ ⊤ := measure_ne_top mu E
  have heta : 0 < (mu E).toReal := ENNReal.toReal_pos hne hfin
  set eta : ℝ := (mu E).toReal with hetadef
  have hroot : 0 < eta ^ p⁻¹ := Real.rpow_pos_of_pos heta _
  set M0 : ℝ := C * (9 / 8) / eta ^ p⁻¹ with hM0
  have hM0nn : 0 ≤ M0 := by positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (L * (2 + M0)) (by norm_num : (1 : ℝ) < 3)
  have h3n : L * (2 + M0) < (3 : ℝ) ^ (k : ℤ) := by rw [zpow_natCast]; exact hk
  have hLn : L ≤ (3 : ℝ) ^ (k : ℤ) := by nlinarith only [h3n, hL, hM0nn]
  have hlam : 0 < (3 : ℝ) ^ (k : ℤ) / L - 1 := by
    rw [sub_pos, lt_div_iff₀ hL, one_mul]
    nlinarith only [h3n, hL, hM0nn]
  have hM0lt : M0 < (3 : ℝ) ^ (k : ℤ) / L - 1 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hL]
    nlinarith only [h3n, hL, hM0nn]
  -- the bound at that scale is strictly below the measure of the bad set
  have hbound := measure_not_nonempty_le mu hmeas hC hp hL hmom hLn hlam
  have hquot : C * (9 / 8) / ((3 : ℝ) ^ (k : ℤ) / L - 1) < eta ^ p⁻¹ := by
    rw [div_lt_iff₀ hlam]
    have hmul : M0 * eta ^ p⁻¹ < ((3 : ℝ) ^ (k : ℤ) / L - 1) * eta ^ p⁻¹ :=
      mul_lt_mul_of_pos_right hM0lt hroot
    rw [hM0, div_mul_cancel₀ _ hroot.ne'] at hmul
    linarith only [hmul]
  have hlt : (C * (9 / 8) / ((3 : ℝ) ^ (k : ℤ) / L - 1)) ^ p < eta := by
    have hpow : (C * (9 / 8) / ((3 : ℝ) ^ (k : ℤ) / L - 1)) ^ p < (eta ^ p⁻¹) ^ p :=
      Real.rpow_lt_rpow (by positivity) hquot hp0
    rwa [← Real.rpow_mul heta.le, inv_mul_cancel₀ hp0.ne', Real.rpow_one] at hpow
  have hfinal : mu E < mu E := by
    calc mu E ≤ ENNReal.ofReal ((C * (9 / 8) / ((3 : ℝ) ^ (k : ℤ) / L - 1)) ^ p) := hbound
      _ < ENNReal.ofReal eta := by
          refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr hlt
      _ = mu E := ENNReal.ofReal_toReal hfin
  exact lt_irrefl _ hfinal

/-- **The confinement scale almost surely exists.**  Combining the almost-sure
nonemptiness with the attainment of the infimum. -/
theorem ae_exists_isConfinementScale (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : ℤ → Omega → ℝ} (hmeas : ∀ k, Measurable (S k)) {C p L : ℝ}
    (hC : 0 ≤ C) (hp : 1 ≤ p) (hL : 0 < L)
    (hmom : ∀ k : ℤ, (∫⁻ omega, ENNReal.ofReal (S k omega) ^ p ∂mu) ≤ ENNReal.ofReal C ^ p) :
    ∀ᵐ omega ∂mu, ∃ m : ℤ,
      IsConfinementScale (fun n => widenedScale (fun k => S k omega) n) L m := by
  filter_upwards [ae_nonempty_confinementSet mu hmeas hC hp hL hmom] with omega homega
  exact exists_isConfinementScale hL homega

end

end Algsuperdiff.Section5.Support
