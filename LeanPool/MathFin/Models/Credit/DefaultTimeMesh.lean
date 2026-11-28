/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Credit.DefaultTime

/-!
# The CDS on a payment grid converges to the continuous legs

`Models/Credit/DefaultTime.lean` prices the CDS on a payment grid against a default time: the
legs are the grid annuity `∑ D(tᵢ₊₁)(tᵢ₊₁ − tᵢ) S(tᵢ₊₁)` and the grid losses
`∑ D(tᵢ₊₁)(S tᵢ − S tᵢ₊₁)`. Here the grid is refined. For a continuous positive hazard rate `h`
(survival `S = hazardSurvival h`) and a flat rate `r`, `D u = e^{−ru}`, the grid legs converge to
the continuous legs of `Models/Credit/Cox.lean` as the mesh `max (tᵢ₊₁ − tᵢ)` goes to zero:

  `cdsAnnuityGrid D S t n → Cox.cdsAnnuity r h T`,   `cdsLossesGrid D S t n → Cox.cdsLosses r h T`,

and so the protection buyer's CDS contract converges to `Cox.protectionLeg − Cox.premiumLeg`, and
the grid par spread to `Cox.cdsFairSpreadTV`.

The limit is taken in the numbers the grid contract is worth (`value_cdsBuyer_coxDefaultTime`).
The grid protection leg also converges to the *contract* that pays at the default time: its values
tend to the value of `cdsProtectionAtDefault` (`Contract.payAtHit`), which is `Cox.protectionLeg`
(`tendsto_value_cdsProtectionLeg_coxDefaultTime`). The premium leg has no such contract, since the
tower has no continuous payment stream.

The core is deterministic: a right-endpoint Riemann–Stieltjes sum of a continuous `g` against a
continuous density `f` differs from `∫ g f` by at most `ε ∫ |f|` once `g` oscillates by at most
`ε` on each cell (`abs_sum_mul_integral_sub_integral_le`).

## Main definitions

* `IsGridOfMesh` — a grid of `[0, T]` with steps at most `δ`.

## Main results

* `abs_sum_mul_integral_sub_integral_le` — the Riemann–Stieltjes error bound.
* `exists_cdsLossesGrid_close`, `exists_cdsAnnuityGrid_close` — the ε–δ form: for every `ε` there is
  a mesh bound `δ` under which every grid is within `ε` of the continuous leg.
* `tendsto_cdsLossesGrid`, `tendsto_cdsAnnuityGrid`, `tendsto_cdsParSpreadGrid`,
  `tendsto_value_cdsBuyer_coxDefaultTime`, `tendsto_value_cdsProtectionLeg_coxDefaultTime` — the
  limits along grids whose mesh tends to zero.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 16
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Lando, *Credit Risk Modeling*][Lando2004], ch. 5
* [S. Peyton Jones, J. M. Eber and J. Seward, *Composing contracts*][PeytonJonesEberSeward2000]

## Tags

CDS discretization, Riemann–Stieltjes sum, hazard rate, par spread limit, continuous-time CDS,
MSC 91G40, JEL G12
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace MathFin.Contracts

/-! ### Riemann–Stieltjes sums -/

/-- **The Riemann–Stieltjes error bound.** Let `g` and `f` be continuous and `t` a monotone grid.
If `g` moves by at most `ε` between the right end of each cell `[tᵢ, tᵢ₊₁]` and any point of it,
then `∑ g(tᵢ₊₁) ∫_{tᵢ}^{tᵢ₊₁} f` is within `ε ∫ |f|` of `∫_{t₀}^{tₙ} g f`. -/
lemma abs_sum_mul_integral_sub_integral_le {g f : ℝ → ℝ} (hg : Continuous g) (hf : Continuous f)
    {t : ℕ → ℝ} (ht : Monotone t) (n : ℕ) {ε : ℝ}
    (hε : ∀ i < n, ∀ s ∈ Set.Icc (t i) (t (i + 1)), |g (t (i + 1)) - g s| ≤ ε) :
    |∑ i ∈ Finset.range n, g (t (i + 1)) * (∫ s in t i..t (i + 1), f s)
        - ∫ s in t 0..t n, g s * f s|
      ≤ ε * ∫ s in t 0..t n, |f s| := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals (a := t) (n := n)
      (f := fun s ↦ g s * f s) fun i _ ↦ (hg.mul hf).intervalIntegrable _ _,
    ← intervalIntegral.sum_integral_adjacent_intervals (a := t) (n := n)
      (f := fun s ↦ |f s|) fun i _ ↦ hf.abs.intervalIntegrable _ _,
    Finset.mul_sum]
  simp only [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  have hle := ht (Nat.le_succ i)
  have h1 : IntervalIntegrable (fun x ↦ g (t (i + 1)) * f x) volume (t i) (t (i + 1)) :=
    (hf.const_mul _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x ↦ g x * f x) volume (t i) (t (i + 1)) :=
    (hg.mul hf).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub h1 h2,
    ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs hle).trans
    (intervalIntegral.integral_mono_on hle (h1.sub h2).abs
      ((hf.abs.const_mul _).intervalIntegrable _ _) fun s hs ↦ ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (hε i (Finset.mem_range.1 hi) s hs) (abs_nonneg _)

/-! ### Grids -/

/-- `t` is a **grid of `[0, T]` of mesh at most `δ`** with `n` cells: monotone, from `0` to `T`,
with every step at most `δ`. -/
def IsGridOfMesh (t : ℕ → ℝ≥0) (n : ℕ) (T δ : ℝ) : Prop :=
  Monotone t ∧ t 0 = 0 ∧ (t n : ℝ) = T ∧ ∀ i < n, (t (i + 1) : ℝ) - t i ≤ δ

lemma IsGridOfMesh.mono {t : ℕ → ℝ≥0} {n : ℕ} {T δ δ' : ℝ} (h : IsGridOfMesh t n T δ)
    (hδ : δ ≤ δ') : IsGridOfMesh t n T δ' :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi ↦ (h.2.2.2 i hi).trans hδ⟩

/-- On a grid of mesh `≤ δ`, a function `g` uniformly continuous at scale `δ` on `[0, T]` moves by
at most `ε` between the right end of each cell and any point of it. -/
private lemma IsGridOfMesh.oscillation {t : ℕ → ℝ≥0} {n : ℕ} {T δ : ℝ} (h : IsGridOfMesh t n T δ)
    {g : ℝ → ℝ} {ε : ℝ} (hg : ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T, |x - y| ≤ δ →
      |g x - g y| ≤ ε) {i : ℕ} (hi : i < n) (s : ℝ) (hs : s ∈ Set.Icc (t i : ℝ) (t (i + 1))) :
    |g (t (i + 1)) - g s| ≤ ε := by
  have hT : (t (i + 1) : ℝ) ≤ T :=
    h.2.2.1 ▸ NNReal.coe_le_coe.2 (h.1 (Nat.succ_le_of_lt hi))
  refine hg (t (i + 1) : ℝ) ⟨NNReal.coe_nonneg _, hT⟩ s
    ⟨(NNReal.coe_nonneg _).trans hs.1, hs.2.trans hT⟩ ?_
  exact (abs_of_nonneg (sub_nonneg.2 hs.2)).trans_le (by linarith [h.2.2.2 i hi, hs.1])

/-- A continuous `g` oscillates by at most `ε` at some scale `δ > 0` on `[0, T]`: uniform continuity
on the compact interval. -/
lemma exists_oscillation_le {g : ℝ → ℝ} (hg : Continuous g) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T, |x - y| ≤ δ → |g x - g y| ≤ ε := by
  obtain ⟨δ, hδ, H⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn) ε hε
  exact ⟨δ / 2, half_pos hδ, fun x hx y hy hxy ↦ (H x hx y hy (by
    rw [Real.dist_eq]; linarith)).le⟩

/-- Convergence along grids of vanishing mesh from the ε–δ closeness: if every grid of mesh at most
`δ` is within `ε` of `L`, then along grids `t k` of mesh at most `δ k → 0` the values tend to
`L`. -/
private lemma tendsto_of_close (Φ : (ℕ → ℝ≥0) → ℕ → ℝ) (L T : ℝ)
    (hclose : ∀ ε > 0, ∃ δ > 0, ∀ t n, IsGridOfMesh t n T δ → |Φ t n - L| ≤ ε)
    {t : ℕ → ℕ → ℝ≥0} {n : ℕ → ℕ} {δ : ℕ → ℝ} (hgrid : ∀ k, IsGridOfMesh (t k) (n k) T (δ k))
    (hδ : Tendsto δ atTop (𝓝 0)) : Tendsto (fun k ↦ Φ (t k) (n k)) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ₀, hδ₀, H⟩ := hclose (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hδ.eventually (gt_mem_nhds hδ₀))
  exact ⟨N, fun k hk ↦ lt_of_le_of_lt (H _ _ ((hgrid k).mono (hN k hk).le))
    (half_lt_self hε)⟩

/-! ### The legs -/

section Legs

variable {h : ℝ → ℝ}

/-- **The grid losses are close to the continuous losses.** For a continuous positive hazard `h`, a
rate `r` and a horizon `T`, every `ε > 0` has a mesh bound `δ > 0` such that every grid of `[0, T]`
of mesh at most `δ` has `|cdsLossesGrid D S t n − Cox.cdsLosses r h T| ≤ ε`, with `D u = e^{−ru}`
and `S = hazardSurvival h`. The error is at most `ε` times the default probability
`1 − S(T) ≤ 1`. -/
theorem exists_cdsLossesGrid_close (hh : Continuous h) (hpos : ∀ s, 0 < h s) (r T : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (t : ℕ → ℝ≥0) (n : ℕ), IsGridOfMesh t n T δ →
      |cdsLossesGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h) t n
        - Cox.cdsLosses r h T| ≤ ε := by
  obtain ⟨δ, hδ, hosc⟩ := exists_oscillation_le (g := fun s ↦ Real.exp (-(r * s)))
    (by fun_prop) T hε
  refine ⟨δ, hδ, fun t n hgrid ↦ ?_⟩
  have key := abs_sum_mul_integral_sub_integral_le (g := fun s ↦ Real.exp (-(r * s)))
    (f := DefaultDensity.defaultDensity h) (by fun_prop)
        (DefaultDensity.continuous_defaultDensity hh)
    (t := fun i ↦ (t i : ℝ)) (fun i j hij ↦ NNReal.coe_le_coe.2 (hgrid.1 hij)) n
    (fun i hi s hs ↦ hgrid.oscillation hosc hi s hs)
  beta_reduce at key
  rw [hgrid.2.1, hgrid.2.2.1, NNReal.coe_zero] at key
  have hsum : ∑ i ∈ Finset.range n, Real.exp (-(r * (t (i + 1) : ℝ)))
      * ∫ s in (t i : ℝ)..(t (i + 1) : ℝ), DefaultDensity.defaultDensity h s
      = cdsLossesGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h) t n := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [DefaultDensity.integral_defaultDensity hh]
  have hint : ∫ s in (0 : ℝ)..T, Real.exp (-(r * s)) * DefaultDensity.defaultDensity h s
      = Cox.cdsLosses r h T := by
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    simp only [DefaultDensity.defaultDensity]
    ring
  have hbound : ∫ s in (0 : ℝ)..T, |DefaultDensity.defaultDensity h s| ≤ 1 := by
    rw [intervalIntegral.integral_congr (g := DefaultDensity.defaultDensity h) fun s _ ↦
        abs_of_nonneg (DefaultDensity.defaultDensity_nonneg (fun s ↦ (hpos s).le) s),
      DefaultDensity.integral_defaultDensity_zero hh]
    linarith [hazardSurvival_pos h T]
  refine (le_of_eq_of_le ?_ key).trans
      ((mul_le_mul_of_nonneg_left hbound hε.le).trans_eq (mul_one ε))
  exact congrArg abs (congrArg₂ (· - ·) hsum.symm hint.symm)

/-- **The grid annuity is close to the continuous annuity**, as `exists_cdsLossesGrid_close`:
every grid of `[0, T]` of mesh at most `δ` has
`|cdsAnnuityGrid D S t n − Cox.cdsAnnuity r h T| ≤ ε`. The error is at most `ε/(T + 1)` times
`T`. -/
theorem exists_cdsAnnuityGrid_close (hh : Continuous h) (r : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (t : ℕ → ℝ≥0) (n : ℕ), IsGridOfMesh t n T δ →
      |cdsAnnuityGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h) t n
        - Cox.cdsAnnuity r h T| ≤ ε := by
  have hgc : Continuous fun s ↦ Real.exp (-(r * s)) * hazardSurvival h s :=
    (by fun_prop : Continuous fun s : ℝ ↦ Real.exp (-(r * s))).mul
      (continuous_iff_continuousAt.2 fun _ ↦
        (DefaultDensity.hasDerivAt_hazardSurvival hh.locallyIntegrable
            hh.continuousAt).continuousAt)
  obtain ⟨δ, hδ, hosc⟩ := exists_oscillation_le hgc T (div_pos hε (by linarith : 0 < T + 1))
  refine ⟨δ, hδ, fun t n hgrid ↦ ?_⟩
  have key := abs_sum_mul_integral_sub_integral_le hgc (f := fun _ ↦ (1 : ℝ)) continuous_const
    (t := fun i ↦ (t i : ℝ)) (fun i j hij ↦ NNReal.coe_le_coe.2 (hgrid.1 hij)) n
    (fun i hi s hs ↦ hgrid.oscillation hosc hi s hs)
  beta_reduce at key
  rw [hgrid.2.1, hgrid.2.2.1, NNReal.coe_zero] at key
  have hsum : ∑ i ∈ Finset.range n, Real.exp (-(r * (t (i + 1) : ℝ))) * hazardSurvival h (t (i + 1))
      * ∫ s in (t i : ℝ)..(t (i + 1) : ℝ), (1 : ℝ)
      = cdsAnnuityGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h) t n := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  have hint : ∫ s in (0 : ℝ)..T, Real.exp (-(r * s)) * hazardSurvival h s * (1 : ℝ)
      = Cox.cdsAnnuity r h T := by
    simp only [mul_one, Cox.cdsAnnuity]
  have hone : ∫ s in (0 : ℝ)..T, |(1 : ℝ)| = T := by simp
  have hε' : 0 ≤ ε / (T + 1) := (div_pos hε (by linarith)).le
  refine (le_of_eq_of_le ?_ key).trans
    ((mul_le_mul_of_nonneg_left hone.le hε').trans ?_)
  · exact congrArg abs (congrArg₂ (· - ·) hsum.symm hint.symm)
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith

/-- **The grid losses converge to the continuous losses** along grids of `[0, T]` whose mesh
tends to zero: `cdsLossesGrid D S (t k) (n k) → Cox.cdsLosses r h T`, `D u = e^{−ru}`. -/
theorem tendsto_cdsLossesGrid (hh : Continuous h) (hpos : ∀ s, 0 < h s) (r T : ℝ)
    {t : ℕ → ℕ → ℝ≥0} {n : ℕ → ℕ} {δ : ℕ → ℝ} (hgrid : ∀ k, IsGridOfMesh (t k) (n k) T (δ k))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k ↦ cdsLossesGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h)
      (t k) (n k)) atTop (𝓝 (Cox.cdsLosses r h T)) :=
  tendsto_of_close
      (fun t n ↦ cdsLossesGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h) t n)
    _ T (fun _ hε ↦ exists_cdsLossesGrid_close hh hpos r T hε) hgrid hδ

/-- **The grid annuity converges to the continuous annuity** along grids of `[0, T]` whose mesh
tends to zero: `cdsAnnuityGrid D S (t k) (n k) → Cox.cdsAnnuity r h T`. -/
theorem tendsto_cdsAnnuityGrid (hh : Continuous h) (r : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {t : ℕ → ℕ → ℝ≥0} {n : ℕ → ℕ} {δ : ℕ → ℝ} (hgrid : ∀ k, IsGridOfMesh (t k) (n k) T (δ k))
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k ↦ cdsAnnuityGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h)
      (t k) (n k)) atTop (𝓝 (Cox.cdsAnnuity r h T)) :=
  tendsto_of_close
      (fun t n ↦ cdsAnnuityGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h) t n)
    _ T (fun _ hε ↦ exists_cdsAnnuityGrid_close hh r hT hε) hgrid hδ

/-- **The grid par spread converges to the continuous fair spread** `Cox.cdsFairSpreadTV` along
grids of `(0, T]` whose mesh tends to zero: the ratio of the two limits, whose denominator
`Cox.cdsAnnuity` is positive. -/
theorem tendsto_cdsParSpreadGrid (hh : Continuous h) (hpos : ∀ s, 0 < h s) (r R : ℝ) {T : ℝ}
    (hT : 0 < T) {t : ℕ → ℕ → ℝ≥0} {n : ℕ → ℕ} {δ : ℕ → ℝ}
    (hgrid : ∀ k, IsGridOfMesh (t k) (n k) T (δ k)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k ↦ cdsParSpreadGrid (fun u : ℝ≥0 ↦ Real.exp (-(r * u))) (hazardSurvival h)
      (t k) R (n k)) atTop (𝓝 (Cox.cdsFairSpreadTV r h R T)) :=
  (((tendsto_cdsLossesGrid hh hpos r T hgrid hδ).const_mul (1 - R)).div
    (tendsto_cdsAnnuityGrid hh r hT.le hgrid hδ) (Cox.cdsAnnuity_pos hh hT).ne')

end Legs

/-! ### The contract -/

section Contract

open Cox

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {h : ℝ → ℝ}

/-- **The CDS contract converges to the continuous legs.** Under the Cox default time of a
continuous positive intensity `h` (`hdiv`: the cumulative hazard diverges), the protection buyer's
CDS on the grids `t k` of `[0, T]`, discounted at the flat rate `r` (`D u = e^{−ru}`), is worth
`(1 − R)·cdsLossesGrid − s·cdsAnnuityGrid` (`value_cdsBuyer_coxDefaultTime`), which tends to
`Cox.protectionLeg R r h T − Cox.premiumLeg s r h T` as the mesh tends to zero. The limit is a
statement about the values, `Cox.protectionLeg` and `Cox.premiumLeg`: the first is the value of
`cdsProtectionAtDefault` (`tendsto_value_cdsProtectionLeg_coxDefaultTime`). -/
theorem tendsto_value_cdsBuyer_coxDefaultTime (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1) (r s R : ℝ) {T : ℝ}
    (hT : 0 ≤ T) {t : ℕ → ℕ → ℝ≥0} {n : ℕ → ℕ} {δ : ℕ → ℝ}
    (hgrid : ∀ k, IsGridOfMesh (t k) (n k) T (δ k)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k ↦ (cdsBuyer (t k) s R (n k)).value μ (fun (u : ℝ≥0) _ ↦ Real.exp (-(r * u)))
      (defaultIndicator (coxDefaultTime h ξ))) atTop
      (𝓝 (protectionLeg R r h T - premiumLeg s r h T)) := by
  simp only [value_cdsBuyer_coxDefaultTime hh hpos hdiv hξmeas hξlaw, protectionLeg, premiumLeg]
  exact ((tendsto_cdsLossesGrid hh hpos r T hgrid hδ).const_mul (1 - R)).sub
    ((tendsto_cdsAnnuityGrid hh r hT hgrid hδ).const_mul s)

/-- **The grid protection leg converges to the protection leg paid at the default time.** Under the
Cox default time, the values of the grid contracts `cdsProtectionLeg (t k) R (n k)`, each paying
`(1 − R)` at the end of the period in which default happens, tend to the value of the contract
`cdsProtectionAtDefault T R`, which pays `(1 − R)` at the default time itself, as the mesh of the
grids of `[0, T]` goes to zero. -/
theorem tendsto_value_cdsProtectionLeg_coxDefaultTime (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1) (r R : ℝ) {T : ℝ≥0}
    {t : ℕ → ℕ → ℝ≥0} {n : ℕ → ℕ} {δ : ℕ → ℝ}
    (hgrid : ∀ k, IsGridOfMesh (t k) (n k) T (δ k)) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k ↦ (cdsProtectionLeg (t k) R (n k)).value μ
      (fun (u : ℝ≥0) _ ↦ Real.exp (-(r * u)))
      (defaultIndicator (coxDefaultTime h ξ))) atTop
      (𝓝 ((cdsProtectionAtDefault T R).value μ (fun (u : ℝ≥0) _ ↦ Real.exp (-(r * u)))
        (defaultIndicator (coxDefaultTime h ξ)))) := by
  rw [value_cdsProtectionAtDefault_coxDefaultTime hh hpos hdiv hξmeas hξlaw, protectionLeg]
  simp only [value_cdsProtectionLeg (measurable_coxDefaultTime hh hpos hξmeas)
    (measureReal_coxDefaultTime_le hh hpos hdiv hξmeas hξlaw)]
  exact (tendsto_cdsLossesGrid hh hpos r T hgrid hδ).const_mul (1 - R)

end Contract

end MathFin.Contracts
