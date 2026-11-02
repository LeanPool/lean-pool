/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLegsHolder
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Chebyshev

/-!
# PrincipalResponseLegsBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Provider: sub-step (iv) of the principal response, the `(1/2) gamma^6` budget

Source display in ABK26:

```
avsum_{z in 3^n Zd cap cu_K} E[ P_z . bfA_m(z+cu_n) P_z 1_{not Q_z} ]
  <= C gamma^{-2} exp(-gamma^{-1})
  <= (1/2) gamma^6 .
```

The companion module `PrincipalResponseLegsHolder` supplies the two Hoelder
splits behind the first inequality.  This module supplies

* the elementary exponential-beats-polynomial estimate closing the second
  inequality,
* the two-lane envelope that turns the two atomic tails of `l.bad.event.lemma`
  (`l.bad.event.lemma`, label; its display `e.bad.event.Q.estimate`, label)
  into the single `exp(-gamma^{-1})` the display quotes,
* the per-cube composition, and
* the grid step, which is needed because bounds only the *averaged* fourth
  moment while the Hoelder split is applied cube by cube.

## Main results

* `exp_add_exp_le_exp_neg` -- the two-lane envelope.
* `badEventEnergy_budget_le` -- `Emom . tail^{3/8} <= (1/2) gamma^6`.
* `gridAverage_badEventEnergy_le` -- the grid step.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-! ## Exponential beats polynomial -/

/-- `exp(-a/gamma) <= (9/a)^9 gamma^9` for positive `a` and `gamma`.

Nine powers are exactly what the budget needs: the envelope `Cm gamma^{-2}`
leaves `gamma^7`, one spare power of `gamma` to absorb the constant against the
target `(1/2) gamma^6`.  The proof uses only `t <= exp t`, so no numerical
tactic is applied to an exponential. -/
private theorem exp_neg_div_le_pow_nine {a gamma : ℝ} (ha : 0 < a)
    (hgamma : 0 < gamma) :
    Real.exp (-(a / gamma)) ≤ (9 / a) ^ (9 : ℕ) * gamma ^ (9 : ℕ) := by
  set t : ℝ := a / (9 * gamma) with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have hexp : t ≤ Real.exp t := by
    have := Real.add_one_le_exp t
    linarith
  have hmul : ((9 : ℕ) : ℝ) * t = a / gamma := by
    rw [htdef]; push_cast; field_simp
  have hnine : Real.exp (a / gamma) = Real.exp t ^ (9 : ℕ) := by
    rw [← hmul, Real.exp_nat_mul]
  have hpow : t ^ (9 : ℕ) ≤ Real.exp (a / gamma) := by
    rw [hnine]
    exact pow_le_pow_left₀ ht.le hexp 9
  have htpow : (0 : ℝ) < t ^ (9 : ℕ) := by positivity
  have hinv : (Real.exp (a / gamma))⁻¹ ≤ (t ^ (9 : ℕ))⁻¹ := inv_anti₀ htpow hpow
  have hrewrite : (t ^ (9 : ℕ))⁻¹ = (9 / a) ^ (9 : ℕ) * gamma ^ (9 : ℕ) := by
    rw [htdef]; field_simp
  calc Real.exp (-(a / gamma)) = (Real.exp (a / gamma))⁻¹ := by rw [Real.exp_neg]
    _ ≤ (t ^ (9 : ℕ))⁻¹ := hinv
    _ = (9 / a) ^ (9 : ℕ) * gamma ^ (9 : ℕ) := hrewrite

/-! ## The two-lane envelope -/

/-- **The envelope.**  `l.bad.event.lemma` delivers the probability of the bad
event as a sum of two exponentials; if each rate exceeds the target rate by
`log 2`, their sum is at most the single exponential the display quotes. -/
theorem exp_add_exp_le_exp_neg {x y r : ℝ}
    (hx : r + Real.log 2 ≤ -x) (hy : r + Real.log 2 ≤ -y) :
    Real.exp x + Real.exp y ≤ Real.exp (-r) := by
  have hhalf : ∀ {u : ℝ}, r + Real.log 2 ≤ -u → Real.exp u ≤ Real.exp (-r) / 2 := by
    intro u hu
    have h1 : Real.exp u ≤ Real.exp (-r - Real.log 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-r - Real.log 2) = Real.exp (-r) / 2 := by
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rwa [h2] at h1
  have h1 := hhalf hx
  have h2 := hhalf hy
  linarith

/-! ## The budget -/

/-- **The closing inequality.**  With the energy moment inside the manuscript's
envelope `Cm gamma^{-2}` and the tail inside `exp(-gamma^{-1})`, the Hoelder
product is within the half budget `(1/2) gamma^6` as soon as `gamma` is small,
which is the manuscript's "for a sufficiently large choice of `M` in
`e.cgamma.constraints`". -/
theorem badEventEnergy_budget_le {Emom tail gamma Cm : ℝ} (hgamma : 0 < gamma)
    (hCm : 0 < Cm) (htail0 : 0 ≤ tail)
    (hEmom : Emom ≤ Cm * (gamma ^ (2 : ℕ))⁻¹)
    (htail : tail ≤ Real.exp (-gamma⁻¹))
    (hsmall : gamma ≤ (2 * Cm * 24 ^ (9 : ℕ))⁻¹) :
    Emom * tail ^ ((3 : ℝ) / 8) ≤ gamma ^ (6 : ℕ) / 2 := by
  have hpow : tail ^ ((3 : ℝ) / 8) ≤ Real.exp (-((3 / 8 : ℝ) / gamma)) := by
    refine (Real.rpow_le_rpow htail0 htail (by norm_num)).trans (le_of_eq ?_)
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    field_simp
  have hexp : Real.exp (-((3 / 8 : ℝ) / gamma)) ≤ 24 ^ (9 : ℕ) * gamma ^ (9 : ℕ) := by
    have h := exp_neg_div_le_pow_nine (a := (3 / 8 : ℝ)) (gamma := gamma)
      (by norm_num) hgamma
    have hc : (9 : ℝ) / (3 / 8 : ℝ) = 24 := by norm_num
    rwa [hc] at h
  have hpow' : tail ^ ((3 : ℝ) / 8) ≤ 24 ^ (9 : ℕ) * gamma ^ (9 : ℕ) := hpow.trans hexp
  have hprod : Emom * tail ^ ((3 : ℝ) / 8) ≤
      Cm * (gamma ^ (2 : ℕ))⁻¹ * (24 ^ (9 : ℕ) * gamma ^ (9 : ℕ)) := by
    refine mul_le_mul hEmom hpow' (Real.rpow_nonneg htail0 _) ?_
    positivity
  have hcollapse : Cm * (gamma ^ (2 : ℕ))⁻¹ * (24 ^ (9 : ℕ) * gamma ^ (9 : ℕ)) =
      gamma ^ (6 : ℕ) * (Cm * 24 ^ (9 : ℕ) * gamma) := by
    field_simp
  have hgate : Cm * 24 ^ (9 : ℕ) * gamma ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hsmall
      (le_of_lt (by positivity : (0 : ℝ) < Cm * 24 ^ (9 : ℕ)))
    refine h.trans (le_of_eq ?_)
    field_simp
  have hgamma6 : (0 : ℝ) ≤ gamma ^ (6 : ℕ) := by positivity
  calc Emom * tail ^ ((3 : ℝ) / 8)
      ≤ Cm * (gamma ^ (2 : ℕ))⁻¹ * (24 ^ (9 : ℕ) * gamma ^ (9 : ℕ)) := hprod
    _ = gamma ^ (6 : ℕ) * (Cm * 24 ^ (9 : ℕ) * gamma) := hcollapse
    _ ≤ gamma ^ (6 : ℕ) * (1 / 2) := mul_le_mul_of_nonneg_left hgate hgamma6
    _ = gamma ^ (6 : ℕ) / 2 := by ring

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

/-! ## The grid step -/

/-- Discrete Cauchy--Schwarz on a nonempty grid: the average of the square roots
is at most the square root of the average. -/
private theorem finsetAverage_sqrt_le {iota : Type*} {s : Finset iota}
    (hs : s.Nonempty) (a : iota → ℝ) (ha : ∀ z ∈ s, 0 ≤ a z) :
    (∑ z ∈ s, Real.sqrt (a z)) / s.card ≤
      Real.sqrt ((∑ z ∈ s, a z) / s.card) := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hsq : (∑ z ∈ s, Real.sqrt (a z)) ^ 2 ≤ (s.card : ℝ) * ∑ z ∈ s, a z := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun z => Real.sqrt (a z))
    have hcongr : ∑ z ∈ s, Real.sqrt (a z) ^ 2 = ∑ z ∈ s, a z :=
      Finset.sum_congr rfl fun z hz => Real.sq_sqrt (ha z hz)
    rwa [hcongr] at h
  have hnn : 0 ≤ (∑ z ∈ s, Real.sqrt (a z)) / (s.card : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun z _ => Real.sqrt_nonneg _) hcard.le
  have hdiv : ((∑ z ∈ s, Real.sqrt (a z)) / (s.card : ℝ)) ^ 2 ≤
      (∑ z ∈ s, a z) / (s.card : ℝ) := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hcard]
    nlinarith [hsq, hcard]
  calc (∑ z ∈ s, Real.sqrt (a z)) / (s.card : ℝ)
      = Real.sqrt (((∑ z ∈ s, Real.sqrt (a z)) / (s.card : ℝ)) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((∑ z ∈ s, a z) / (s.card : ℝ)) := Real.sqrt_le_sqrt hdiv

/-- **The grid step.**  ABK26 bounds only the grid average of the fourth moment
`m4 z = E[|bfAhom_{m-1}^{1/2} P_z|^4]`, while the Hoelder split is applied cube
by cube and produces `sqrt (m4 z)`.  Discrete Cauchy--Schwarz closes the gap and
returns the manuscript's grid form. -/
theorem gridAverage_badEventEnergy_le {iota : Type*} {s : Finset iota}
    (hs : s.Nonempty) (pbad m4 : iota → ℝ) {Cb Cv t : ℝ}
    (hm4 : ∀ z ∈ s, 0 ≤ m4 z) (hCb0 : 0 ≤ Cb) (ht0 : 0 ≤ t)
    (hpbad : ∀ z ∈ s, pbad z ≤ Cb * Real.sqrt (m4 z) * t)
    (havg : (∑ z ∈ s, m4 z) / s.card ≤ Cv ^ (4 : ℕ)) :
    (∑ z ∈ s, pbad z) / s.card ≤ Cb * Cv ^ (2 : ℕ) * t := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hstep : (∑ z ∈ s, pbad z) / (s.card : ℝ) ≤
      (∑ z ∈ s, Cb * Real.sqrt (m4 z) * t) / (s.card : ℝ) := by
    gcongr with z hz
    exact hpbad z hz
  have hpull : (∑ z ∈ s, Cb * Real.sqrt (m4 z) * t) / (s.card : ℝ) =
      Cb * t * ((∑ z ∈ s, Real.sqrt (m4 z)) / (s.card : ℝ)) := by
    have hs' : ∑ z ∈ s, Cb * Real.sqrt (m4 z) * t =
        Cb * t * ∑ z ∈ s, Real.sqrt (m4 z) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hs', mul_div_assoc]
  have hcs : (∑ z ∈ s, Real.sqrt (m4 z)) / (s.card : ℝ) ≤
      Real.sqrt ((∑ z ∈ s, m4 z) / (s.card : ℝ)) := finsetAverage_sqrt_le hs m4 hm4
  have hsq : Real.sqrt ((∑ z ∈ s, m4 z) / (s.card : ℝ)) ≤ Cv ^ (2 : ℕ) := by
    have h1 : Real.sqrt ((∑ z ∈ s, m4 z) / (s.card : ℝ)) ≤
        Real.sqrt (Cv ^ (4 : ℕ)) := Real.sqrt_le_sqrt havg
    have h2 : Real.sqrt (Cv ^ (4 : ℕ)) = Cv ^ (2 : ℕ) := by
      have hfour : (Cv : ℝ) ^ (4 : ℕ) = (Cv ^ (2 : ℕ)) ^ 2 := by ring
      rw [hfour, Real.sqrt_sq (by positivity)]
    rwa [h2] at h1
  have hfin : Cb * t * ((∑ z ∈ s, Real.sqrt (m4 z)) / (s.card : ℝ)) ≤
      Cb * t * Cv ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left (hcs.trans hsq) (by positivity)
  calc (∑ z ∈ s, pbad z) / (s.card : ℝ)
      ≤ (∑ z ∈ s, Cb * Real.sqrt (m4 z) * t) / (s.card : ℝ) := hstep
    _ = Cb * t * ((∑ z ∈ s, Real.sqrt (m4 z)) / (s.card : ℝ)) := hpull
    _ ≤ Cb * t * Cv ^ (2 : ℕ) := hfin
    _ = Cb * Cv ^ (2 : ℕ) * t := by ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
