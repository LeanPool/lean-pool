/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ProportionArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Api
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# ProportionAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `§4.1` proportion assembly, in the printed display

ABK26, §4.1, `p.independence.between.scales`.
`ShiftedInterface.exists_ratioTail_goodEventBase_shift` composes the two proved
lanes with the `𝒢₂` slot and delivers, at every base `m₀` and every window `n`,
a tail `exp(−c₁n)` for the clause `avsum 𝟙{𝒢} ≤ 1 − θ`.  This module turns that
lane package into the printed display itself:

```
ℙ[ (M_w+1)⁻¹ ∑_{k ≤ M_w} 𝟙{𝒢(m₀+k, 0; s, ε)} ≤ 1 − θ ] ≤ 6 exp(−A(M_w+1)) ,
```

with `A` read off the model.  Three things separate the two shapes and all three
are discharged here.

* **The level ceiling.**  The two proved lanes need `θ(r+1) < 1`, which the
  printed `θ ≤ ½` does not give once `r ≥ 2`.  The lanes are run at `θ/(8L)`,
  `L = r+1`, and the conclusion is read back at `θ` by `measure_mono`; the factor
  `L` is absorbed into the assembly's own constant (`ProportionArith`).
* **The rate.**  With `c₁ = 2A` one has `exp(−2A·M_w) ≤ 6 exp(−A(M_w+1))` for
  every `M_w ≥ 1`.  The printed prefactor `6` is exactly what pays for the
  `(M_w+1)`-versus-`M_w` offset.
* **The single-scale window.**  At `M_w = 0` the composed tail is `1` and the
  printed right-hand side is `6exp(−A)`, so the lane package must be read at a
  *different* window: `{ω ∉ 𝒢(m₀)}` carries bad-density `½` over `{m₀, m₀+1}`,
  so the window-`1` endpoint bounds it.

## The form delivered, and what blocks the printed one

`exists_proportionTail_of_honestG1` is the assembly proper: the display, at an
abstract rate `A`, from the honest `𝒢₁` condition `C(1+2A)γ ≤ θ c⋆ s⁶ ε²`.  The
frozen theorem's **printed** clauses (`s⁻⁴`, `s⁵`) do not imply that condition on
a nonempty parameter region: the minimal sufficient strengthening is the level
clause at `s⁻⁶` and the rate at `s⁷`, proved in `LaneCertificates`
(`couplingG1_of_anchor`).  The honest `𝒢₁`
condition is therefore an interface obligation of the consumer, not a source
premise.

## References

* ABK26, `p.independence.between.scales`; `d.good.event.for.lambda`,
  (`e.lambda.good.events`); `e.theta.cond.two`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {d : ℕ}

/-! ## 1. The common dependence range -/

/-- **The dependence range of the assembly.**  The three lanes are run at one
range: the one the composed two-lane interface fixes, enlarged so that the
count `3 + (2/3)√d ≤ 3^r` also holds at it.  The `𝒢₂` endpoint is stated at
*every* admissible range, so this choice costs nothing. -/
def laneRange (d : ℕ) : ℕ :=
  max (exists_ratioTail_goodEventBase_shift d).choose (exists_dependence_range d).choose

theorem one_le_laneRange (d : ℕ) : 1 ≤ laneRange d :=
  le_trans (exists_ratioTail_goodEventBase_shift d).choose_spec.1 (le_max_left _ _)

/-- The assembly's range is admissible for the count, so the shifted `𝒢₂`
endpoint can be read at it. -/
theorem laneRange_gap (d : ℕ) :
    3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (laneRange d) :=
  le_trans (exists_dependence_range d).choose_spec.2
    (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))

private theorem base_le_laneRange (d : ℕ) :
    (exists_ratioTail_goodEventBase_shift d).choose ≤ laneRange d := le_max_left _ _

/-! ## 2. The display from the lane package -/

/-- **The printed display from the two output forms of the lane package.**

The good-proportion endpoint at the split level `θ_L` covers every window
`M_w ≥ 1`; the bad-density endpoint at window `1` covers `M_w = 0`, where the
printed clause is the single bad event `𝒢(m₀)ᶜ`.  Running the lanes at the rate
`2A` is what makes both branches land under `6exp(−A(M_w+1))`. -/
theorem measure_scalePropFrom_le_of_lanes (M : ABKModel d) (Ccg : ℝ)
    (s : {s : ℝ // 0 < s}) (ep theta thetaL A : ℝ)
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hLle : thetaL ≤ theta) (hLhalf : thetaL < 1 / 2)
    (hA0 : 0 ≤ A)
    (hbad : ∀ (m0 : ℤ) (n : ℕ),
      (Cutoff.cutoffSampleLaw M).toMeasure
          {omega | thetaL < scaleProp
            (fun k => (Support.goodEventBase M Ccg (m0 + k) s ep)ᶜ) n omega}
        ≤ ENNReal.ofReal (Real.exp (-(2 * A) * (n : ℝ))))
    (hgood : ∀ (m0 : ℤ) (n : ℕ),
      (Cutoff.cutoffSampleLaw M).toMeasure
          {omega | scaleProp (fun k => Support.goodEventBase M Ccg (m0 + k) s ep) n omega
            ≤ 1 - thetaL}
        ≤ ENNReal.ofReal (Real.exp (-(2 * A) * (n : ℝ))))
    (m0 : ℤ) (Mw : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure
        {omega | scalePropFrom (fun m => Support.goodEventBase M Ccg m s ep) m0 Mw omega
          ≤ 1 - theta}
      ≤ ENNReal.ofReal (6 * Real.exp (-(A * ((Mw : ℝ) + 1)))) := by
  rcases Nat.eq_zero_or_pos Mw with hMw | hMw
  · subst hMw
    rw [setOf_scalePropFrom_zero_eq_compl _ m0 htheta0 htheta1]
    have hsub : (Support.goodEventBase M Ccg m0 s ep)ᶜ
        ⊆ {omega | thetaL < scaleProp
            (fun k => (Support.goodEventBase M Ccg (m0 + k) s ep)ᶜ) 1 omega} := by
      intro omega homega
      have hhalf := half_le_scaleProp_one_of_mem
        (fun k => (Support.goodEventBase M Ccg (m0 + k) s ep)ᶜ) omega
        (by
          show omega ∈ (Support.goodEventBase M Ccg (m0 + 0) s ep)ᶜ
          rwa [add_zero])
      exact lt_of_lt_of_le hLhalf hhalf
    refine le_trans (measure_mono hsub) ?_
    exact le_trans (hbad m0 1) (ENNReal.ofReal_le_ofReal (exp_le_six_exp_of_zero hA0))
  · have hsub : {omega |
          scalePropFrom (fun m => Support.goodEventBase M Ccg m s ep) m0 Mw omega ≤ 1 - theta}
        ⊆ {omega |
          scaleProp (fun k => Support.goodEventBase M Ccg (m0 + k) s ep) Mw omega
            ≤ 1 - thetaL} := by
      intro omega homega
      simp only [Set.mem_ofPred_eq] at homega ⊢
      simp only [scalePropFrom_eq_scaleProp] at homega
      linarith only [homega, hLle]
    refine le_trans (measure_mono hsub) ?_
    exact le_trans (hgood m0 Mw)
      (ENNReal.ofReal_le_ofReal (exp_le_six_exp_of_one_le hA0 hMw))

/-! ## 3. The assembly at the honest `𝒢₁` condition -/

/-- **The `§4.1` proportion display, at an abstract rate, from the honest `𝒢₁`
condition.**

One constant `C(d) ≥ 1`, fixed before the model and before every parameter.  For
every model, every `s, ε ∈ (0, ½]`, every level `θ ∈ (0, ½]` and every rate
`A ≥ 0` subject to

* the printed regime `γ ≤ C⁻¹c⋆¹⁰`,
* the printed level clause `C c⋆⁻²s⁻⁴ε⁻²γ ≤ θ`,
* the **honest `𝒢₁` condition** `C(1+2A)γ ≤ θ c⋆ s⁶ ε²`,

the printed display holds at every base `m₀` and every window length `M_w`,
including `M_w = 0`, with right-hand side `6exp(−A(M_w+1))`.

The `𝒢₂` lane enters as the named hypothesis `hG2`, in the `LaneTailFrom` shape,
at exactly the one level `θ/(32(r+1))` and the one rate `2A` the assembly
consumes — the shape the shifted `𝒢₂` lane produces at
`r = laneRange d` (admissible by `laneRange_gap`), for every `ε` above its own
threshold `ε₀`.  It is a caller-supplied interface obligation, not a source
premise. -/
theorem exists_proportionTail_of_honestG1 (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (M : ABKModel d) (s ep theta A : ℝ),
        0 < s → s ≤ 1 / 2 → 0 < ep → ep ≤ 1 / 2 → 0 < theta → theta ≤ 1 / 2 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        C * (Disorder.cstar M)⁻¹ ^ (2 : ℕ) * s⁻¹ ^ (4 : ℕ) * ep⁻¹ ^ (2 : ℕ) *
            M.gamma ≤ theta →
        0 ≤ A → 2 * A * M.gamma ≤ 1 →
        C * (1 + 2 * A) * M.gamma
            ≤ theta * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ) →
        ∀ (m0 : ℤ) (Mw : ℕ) (hs : 0 < s),
          LaneTailFrom M (fun k => Support.eventG2 M k ⟨s, hs⟩ ep)
              (theta / (32 * ((laneRange d : ℝ) + 1))) (2 * A) →
          (Cutoff.cutoffSampleLaw M).toMeasure
              {omega |
                (1 / ((Mw : ℝ) + 1)) *
                    ∑ k ∈ Finset.range (Mw + 1),
                      (Algsuperdiff.Frozen.Section4.goodEventAt M
                            (Algsuperdiff.Section4.Support.cgEllipLowerConstant d)
                            (m0 + (k : ℤ)) 0 ⟨s, hs⟩ ep).indicator
                        (fun _ => (1 : ℝ)) omega ≤
                  1 - theta } ≤
            ENNReal.ofReal (6 * Real.exp (-(A * ((Mw : ℝ) + 1)))) := by
  obtain ⟨C1, hC16, hmain⟩ := (exists_ratioTail_goodEventBase_shift d).choose_spec.2
  have hC10 : (0 : ℝ) < C1 := by linarith only [hC16]
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = ((laneRange d : ℕ) : ℝ) + 1 := ⟨_, rfl⟩
  have hL2 : (2 : ℝ) ≤ L := by
    have hcast : (1 : ℝ) ≤ ((laneRange d : ℕ) : ℝ) := by exact_mod_cast one_le_laneRange d
    rw [hLdef]
    linarith only [hcast]
  have hL0 : (0 : ℝ) < L := by linarith only [hL2]
  have h8L0 : (0 : ℝ) < 8 * L := by linarith only [hL2]
  have h8L1 : (1 : ℝ) ≤ 8 * L := by linarith only [hL2]
  obtain ⟨C, hCdef⟩ : ∃ x : ℝ,
      x = (8 * L * C1) ^ (5 : ℕ) + C1 ^ (10 : ℕ) + 8 * L * C1 + 1 := ⟨_, rfl⟩
  have hfl1 : (8 * L * C1) ^ (5 : ℕ) ≤ C := by
    rw [hCdef]
    have h2 : (0 : ℝ) ≤ C1 ^ (10 : ℕ) := by positivity
    have h3 : (0 : ℝ) ≤ 8 * L * C1 := by positivity
    linarith only [h2, h3]
  have hfl2 : C1 ^ (10 : ℕ) ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ (8 * L * C1) ^ (5 : ℕ) := by positivity
    have h3 : (0 : ℝ) ≤ 8 * L * C1 := by positivity
    linarith only [h1, h3]
  have hfl3 : 8 * L * C1 ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ (8 * L * C1) ^ (5 : ℕ) := by positivity
    have h2 : (0 : ℝ) ≤ C1 ^ (10 : ℕ) := by positivity
    linarith only [h1, h2]
  refine ⟨C, ?_, ?_⟩
  · rw [hCdef]
    have h1 : (0 : ℝ) ≤ (8 * L * C1) ^ (5 : ℕ) := by positivity
    have h2 : (0 : ℝ) ≤ C1 ^ (10 : ℕ) := by positivity
    have h3 : (0 : ℝ) ≤ 8 * L * C1 := by positivity
    linarith only [h1, h2, h3]
  intro M s ep theta A hs0 hs12 hep0 hep12 htheta0 htheta12 hreg hlevel4 hA0 hAceil hG1
    m0 Mw hs hG2
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs32 : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  -- the split level
  obtain ⟨thetaL, hthetaLdef⟩ : ∃ x : ℝ, x = theta / (8 * L) := ⟨_, rfl⟩
  have hthetaL0 : 0 < thetaL := by
    rw [hthetaLdef]; positivity
  have hthetaLle : thetaL ≤ theta := by
    rw [hthetaLdef, div_le_iff₀ h8L0]
    have h := mul_le_mul_of_nonneg_left h8L1 htheta0.le
    rw [mul_one] at h
    linarith only [h]
  have hthetaLhalf : thetaL < 1 / 2 := by
    rw [hthetaLdef, div_lt_iff₀ h8L0]
    have h : (8 : ℝ) ≤ 1 / 2 * (8 * L) := by linarith only [hL2]
    linarith only [h, htheta12]
  have hthetaLL : thetaL * L = theta / 8 := by
    rw [hthetaLdef]
    field_simp
  -- the level ceiling at the interface range
  have hceil : thetaL * (((exists_ratioTail_goodEventBase_shift d).choose : ℝ) + 1) < 1 := by
    have hle : (((exists_ratioTail_goodEventBase_shift d).choose : ℕ) : ℝ) + 1 ≤ L := by
      have hcast : (((exists_ratioTail_goodEventBase_shift d).choose : ℕ) : ℝ)
          ≤ ((laneRange d : ℕ) : ℝ) := by exact_mod_cast base_le_laneRange d
      rw [hLdef]
      linarith only [hcast]
    have hprod := mul_le_mul_of_nonneg_left hle hthetaL0.le
    rw [hthetaLL] at hprod
    linarith only [hprod, htheta12]
  -- the two couplings at the split level
  have hcoup0 : C1 ^ (10 : ℕ) * M.gamma ^ (2 : ℕ)
      ≤ thetaL * Disorder.cstar M ^ (8 : ℕ) := by
    rw [hthetaLdef]
    exact couplingG0_at_split hC16 hL2 hcs0 hcs32 hs0 hs12 hep0 hep12 hg0 hfl1 hreg hlevel4
  have hcoup1 : C1 * (1 + 2 * A) * M.gamma
      ≤ thetaL * Disorder.cstar M * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := by
    rw [hthetaLdef]
    exact honestG1_at_split hL2 hfl3 hA0 hg0 hG1
  -- the `𝒢₂` slot at the split level and the assembly's rate
  have hG2inst : LaneTailFrom M (fun k => Support.eventG2 M k ⟨s, hs⟩ ep)
      (thetaL / 4) (2 * A) := by
    have hrw : thetaL / 4 = theta / (32 * ((laneRange d : ℝ) + 1)) := by
      rw [hthetaLdef, ← hLdef]
      ring
    rw [hrw]
    exact hG2
  obtain ⟨hbad, hgood⟩ := hmain M ⟨s, hs⟩ ep thetaL (2 * A) (by linarith only [hs12]) hep0
    hthetaL0 hceil (by linarith only [hA0]) hAceil (regime_of_anchor hC10 hfl2 hreg)
    hcoup0 hcoup1 hG2inst
  have hcore := measure_scalePropFrom_le_of_lanes M
    (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) ⟨s, hs⟩ ep theta thetaL A
    htheta0 (by linarith only [htheta12]) hthetaLle hthetaLhalf hA0 hbad hgood m0 Mw
  have hset : {omega |
        (1 / ((Mw : ℝ) + 1)) *
            ∑ k ∈ Finset.range (Mw + 1),
              (Algsuperdiff.Frozen.Section4.goodEventAt M
                    (Algsuperdiff.Section4.Support.cgEllipLowerConstant d)
                    (m0 + (k : ℤ)) 0 ⟨s, hs⟩ ep).indicator
                (fun _ => (1 : ℝ)) omega ≤ 1 - theta}
      = {omega |
        scalePropFrom
            (fun m => Support.goodEventBase M
              (Algsuperdiff.Section4.Support.cgEllipLowerConstant d) m ⟨s, hs⟩ ep)
            m0 Mw omega ≤ 1 - theta} := by
    simp only [scalePropFrom, GoodEvents.goodEventAt_zero]
  rw [hset]
  exact hcore

end

end Algsuperdiff.Section4.Provider.Proportion
