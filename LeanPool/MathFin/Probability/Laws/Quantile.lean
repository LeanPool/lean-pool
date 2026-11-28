/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw

/-!
# The quantile function of a law on `ℝ`

The **quantile function** of a probability measure `μ` on `ℝ` is the generalized inverse of its
CDF `F = cdf μ`:

  `quantile μ p = inf {x | p ≤ F x}`,   `p ∈ (0, 1)`.

Mathlib has the CDF (`ProbabilityTheory.cdf`) but no inverse. This file supplies it, together
with the facts that make it the right object.

* **The Galois connection.** For `p ∈ (0, 1)`, `quantile μ p ≤ x ↔ p ≤ F x` (`quantile_le_iff`).
  Everything below is read off this one equivalence. It needs neither continuity nor strict
  monotonicity of `F`, so atoms and flat stretches of `F` are handled without case analysis. Its
  contrapositive `x < quantile μ p ↔ F x < p` (`lt_quantile_iff`) is the threshold form that the
  bisection method (`Probability/Analysis/Bisection.lean`) converges under.
* **The quantile transform.** Under the uniform law on `(0, 1)`, `quantile μ` has law `μ`
  (`hasLaw_quantile`). So every law on `ℝ` is the image of the uniform law under a monotone map,
  and expectations are integrals over `(0, 1)`: `∫ f dμ = ∫₀¹ f (quantile μ p) dp`
  (`integral_eq_setIntegral_quantile`).
* **The probability integral transform.** If `F` is continuous, `F ∘ quantile μ` is the identity
  on `(0, 1)` (`cdf_quantile`), so `F(X)` is uniform whenever `X` has law `μ` (`hasLaw_cdf`).
* **Equivariance.** Quantiles commute with monotone lower-semicontinuous maps, in particular with
  continuous increasing ones: `quantile (μ.map h) p = h (quantile μ p)` (`quantile_map`).

In risk management `quantile μ α` is the value-at-risk at level `α` of a loss with law `μ`
(`Risk/ValueAtRisk.lean`).

## Main definitions

* `quantile`: the generalized inverse `quantile μ p = inf {x | p ≤ cdf μ x}` of the CDF of a law
  `μ` on `ℝ`, meaningful for `p ∈ (0, 1)`.

## Main results

* `quantile_le_iff`, `lt_quantile_iff`: the Galois connection with the CDF.
* `le_cdf_quantile`: `p ≤ F (quantile μ p)`, from right-continuity of `F`.
* `monotoneOn_quantile`, `aemeasurable_quantile`: monotone, hence measurable, on `(0, 1)`.
* `quantile_dirac`: a point mass is its own quantile.
* `quantile_eq_iff`: a quantile is characterized by the CDF on both sides of it.
* `quantile_expMeasure`: the exponential quantile `−log(1 − p)/r`.
* `uniformIoo_Iic`: the uniform law on `(0, 1)` gives `(-∞, c]` mass `c`.
* `hasLaw_quantile`: the quantile transform.
* `integral_eq_setIntegral_quantile`: expectations as integrals of the quantile function.
* `continuous_cdf`: a law without atoms has a continuous CDF.
* `cdf_quantile`, `hasLaw_cdf`: the probability integral transform.
* `quantile_cdf`: `quantile μ (F x) = x` when `F` is strictly increasing.
* `quantile_map`: equivariance under monotone lower-semicontinuous maps.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Appendix A.1.2; Proposition 7.2; Proposition 7.2 / Appendix A.1.2;
  Proposition A.3
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 2.21; Ex. 2.6; Ex. 7.2

## Tags

generalized inverse CDF, quantile function, probability integral transform, quantile transform,
value-at-risk, Galois connection, MSC 62G30, MSC 60E05, MSC 91G70
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The **quantile function** of a law `μ` on `ℝ`: the generalized inverse of its CDF,
`quantile μ p = inf {x | p ≤ cdf μ x}`. Its values are meaningful for `p ∈ (0, 1)`, where the set
is nonempty and bounded below. -/
noncomputable def quantile (μ : Measure ℝ) (p : ℝ) : ℝ :=
  sInf {x | p ≤ cdf μ x}

/-- The uniform law on `(0, 1)` is a probability measure. -/
instance isProbabilityMeasure_volume_restrict_Ioo_zero_one :
    IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ⟨by simp⟩

variable {μ : Measure ℝ} {p x : ℝ}

/-! ### The Galois connection with the CDF -/

/-- For `p < 1` some `x` has `p ≤ F x`, because `F → 1` at `+∞`. -/
lemma nonempty_setOf_le_cdf (hp : p < 1) : {x | p ≤ cdf μ x}.Nonempty :=
  (tendsto_cdf_atTop μ |>.eventually_const_lt hp).exists.imp fun _ ↦ le_of_lt

/-- For `0 < p` the set `{x | p ≤ F x}` is bounded below, because `F → 0` at `-∞`. -/
lemma bddBelow_setOf_le_cdf (hp : 0 < p) : BddBelow {x | p ≤ cdf μ x} := by
  obtain ⟨b, hb⟩ := (tendsto_cdf_atBot μ |>.eventually_lt_const hp).exists
  exact ⟨b, fun x hx ↦ le_of_not_gt fun hxb ↦ (hx.trans (monotone_cdf μ hxb.le)).not_gt hb⟩

/-- Right-continuity of `F` keeps the infimum inside the set: `p ≤ F (quantile μ p)`. -/
lemma le_cdf_quantile (hp : p ∈ Ioo 0 1) : p ≤ cdf μ (quantile μ p) := by
  refine ge_of_tendsto (((cdf μ).right_continuous _).mono Ioi_subset_Ici_self) ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  obtain ⟨x, hx, hxy⟩ := exists_lt_of_csInf_lt (nonempty_setOf_le_cdf hp.2) hy
  exact hx.trans (monotone_cdf μ hxy.le)

/-- **The Galois connection** between the quantile function and the CDF: for `p ∈ (0, 1)`,
`quantile μ p ≤ x ↔ p ≤ F x`. -/
theorem quantile_le_iff (hp : p ∈ Ioo 0 1) : quantile μ p ≤ x ↔ p ≤ cdf μ x :=
  ⟨fun h ↦ (le_cdf_quantile hp).trans (monotone_cdf μ h),
    fun h ↦ csInf_le (bddBelow_setOf_le_cdf hp.1) h⟩

/-- The Galois connection read contrapositively: `x < quantile μ p ↔ F x < p`. The quantile is
the threshold of the CDF against `p`. -/
theorem lt_quantile_iff (hp : p ∈ Ioo 0 1) : x < quantile μ p ↔ cdf μ x < p := by
  simpa only [not_le] using (quantile_le_iff hp).not

/-- The quantile function is monotone on `(0, 1)`. -/
lemma monotoneOn_quantile : MonotoneOn (quantile μ) (Ioo 0 1) := fun _ hp _ hq hpq ↦
  (quantile_le_iff hp).2 (hpq.trans (le_cdf_quantile hq))

/-- Monotone on `(0, 1)`, hence measurable for the uniform law there. -/
lemma aemeasurable_quantile : AEMeasurable (quantile μ) (volume.restrict (Ioo 0 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo monotoneOn_quantile

/-- A point mass sits at its own quantile at every level. -/
theorem quantile_dirac (a : ℝ) (hp : p ∈ Ioo 0 1) : quantile (Measure.dirac a) p = a := by
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [quantile_le_iff hp, cdf_eq_real]
  by_cases hax : a ≤ x
  · rw [measureReal_def, Measure.dirac_apply_of_mem (mem_Iic.2 hax)]
    simpa [hax] using hp.2.le
  · rw [measureReal_def, Measure.dirac_apply' a measurableSet_Iic,
      indicator_of_notMem (by simpa using hax)]
    simpa [hax] using hp.1

/-- A level's quantile is pinned down by the CDF: `quantile μ p = a` exactly when `p ≤ F(a)` and
`F(x) < p` for every `x < a`. -/
theorem quantile_eq_iff (hp : p ∈ Ioo 0 1) {a : ℝ} :
    quantile μ p = a ↔ p ≤ cdf μ a ∧ ∀ x < a, cdf μ x < p := by
  refine ⟨?_, fun ⟨ha, hlt⟩ ↦ le_antisymm ((quantile_le_iff hp).2 ha)
    (le_of_forall_lt fun x hx ↦ (lt_quantile_iff hp).2 (hlt x hx))⟩
  rintro rfl
  exact ⟨le_cdf_quantile hp, fun _ hx ↦ (lt_quantile_iff hp).1 hx⟩

/-- The quantile of the exponential law with rate `r`: `quantile (Exp r) p = −log(1 − p)/r`. -/
theorem quantile_expMeasure {r : ℝ} (hr : 0 < r) (hp : p ∈ Ioo 0 1) :
    quantile (expMeasure r) p = -Real.log (1 - p) / r := by
  have h1p : 0 < 1 - p := sub_pos.2 hp.2
  have hlog : Real.log (1 - p) < 0 := Real.log_neg h1p (by linarith [hp.1])
  refine eq_of_forall_ge_iff fun y ↦ ?_
  rw [quantile_le_iff hp, cdf_expMeasure_eq hr]
  split_ifs with hy
  · rw [le_sub_comm, ← Real.le_log_iff_exp_le h1p, neg_le, div_le_iff₀ hr, mul_comm]
  · exact iff_of_false (not_le.2 hp.1)
      (not_le.2 ((not_le.1 hy).trans_le (div_nonneg (by linarith) hr.le)))

/-! ### The quantile transform -/

/-- The uniform law on `(0, 1)` gives `(-∞, c]` mass `c` for `c ∈ [0, 1]`. -/
theorem uniformIoo_Iic {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    volume.restrict (Ioo (0 : ℝ) 1) (Iic c) = ENNReal.ofReal c := by
  rw [Measure.restrict_apply measurableSet_Iic]
  rcases h1.lt_or_eq with h1 | rfl
  · rw [show Iic c ∩ Ioo 0 1 = Ioc 0 c by
      ext p; exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans_lt h1⟩⟩]
    simp
  · rw [inter_eq_right.2 (Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self)]
    simp

/-- **The quantile transform.** Under the uniform law on `(0, 1)`, the quantile function of a
probability measure `μ` has law `μ`: every law on `ℝ` is the image of the uniform law under its
own quantile function. -/
theorem hasLaw_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    HasLaw (quantile μ) μ (volume.restrict (Ioo 0 1)) where
  aemeasurable := aemeasurable_quantile
  map_eq := by
    refine Measure.ext_of_Iic _ _ fun a ↦ ?_
    have hset : quantile μ ⁻¹' Iic a ∩ Ioo 0 1 = Iic (cdf μ a) ∩ Ioo 0 1 := by
      ext p
      exact ⟨fun h ↦ ⟨(quantile_le_iff h.2).1 h.1, h.2⟩,
        fun h ↦ ⟨(quantile_le_iff h.2).2 h.1, h.2⟩⟩
    rw [Measure.map_apply_of_aemeasurable aemeasurable_quantile measurableSet_Iic,
      Measure.restrict_apply' measurableSet_Ioo, hset, ← Measure.restrict_apply measurableSet_Iic,
      uniformIoo_Iic (cdf_nonneg μ a) (cdf_le_one μ a), ofReal_cdf]

/-- **Expectations as integrals of the quantile function**: `∫ f dμ = ∫₀¹ f (quantile μ p) dp`. -/
theorem integral_eq_setIntegral_quantile [IsProbabilityMeasure μ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} (hf : AEStronglyMeasurable f μ) :
    ∫ x, f x ∂μ = ∫ p in Ioo 0 1, f (quantile μ p) :=
  ((hasLaw_quantile μ).integral_comp hf).symm

/-- Integrability transfers along the quantile transform. -/
theorem integrableOn_comp_quantile_iff [IsProbabilityMeasure μ] {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} (hf : AEStronglyMeasurable f μ) :
    IntegrableOn (fun p ↦ f (quantile μ p)) (Ioo 0 1) ↔ Integrable f μ := by
  have h := integrable_map_measure (by rwa [(hasLaw_quantile μ).map_eq]) aemeasurable_quantile
  rw [(hasLaw_quantile μ).map_eq] at h
  exact h.symm

/-! ### Continuous CDFs and the probability integral transform -/

/-- A law without atoms has a continuous CDF: the jump of `F` at `x` is the mass of `{x}`. -/
theorem continuous_cdf [IsProbabilityMeasure μ] [NullSingletonClass μ] : Continuous (cdf μ) := by
  refine continuous_iff_continuousAt.2 fun x ↦ continuousAt_iff_continuous_left_right.2
    ⟨?_, (cdf μ).right_continuous x⟩
  rw [continuousWithinAt_Iio_iff_Iic.symm,
    (monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq]
  have hjump := (cdf μ).measure_singleton x
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at hjump
  exact le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) hjump

/-- If `F` is continuous, `F ∘ quantile μ` is the identity on `(0, 1)`. -/
theorem cdf_quantile (hF : Continuous (cdf μ)) (hp : p ∈ Ioo 0 1) :
    cdf μ (quantile μ p) = p := by
  refine le_antisymm (le_of_tendsto ((hF.tendsto _).mono_left
    (nhdsWithin_le_nhds (s := Iio (quantile μ p)))) ?_) (le_cdf_quantile hp)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact ((lt_quantile_iff hp).1 hy).le

/-- **The probability integral transform**: if `X` has law `μ` and `F` is continuous, then `F(X)`
is uniform on `(0, 1)`. -/
theorem hasLaw_cdf {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    [IsProbabilityMeasure μ] (hX : HasLaw X μ P) (hF : Continuous (cdf μ)) :
    HasLaw (fun ω ↦ cdf μ (X ω)) (volume.restrict (Ioo 0 1)) P :=
  (hasLaw_quantile μ).comp_of_hasLaw_comp (monotone_cdf μ).measurable.aemeasurable hX <|
    HasLaw.id.congr <| (ae_restrict_mem measurableSet_Ioo).mono fun _ hp ↦ cdf_quantile hF hp

/-- If `F` is strictly increasing, `quantile μ ∘ F` is the identity where `F ∈ (0, 1)`. -/
theorem quantile_cdf (hF : StrictMono (cdf μ)) (hx : cdf μ x ∈ Ioo 0 1) :
    quantile μ (cdf μ x) = x :=
  eq_of_forall_ge_iff fun _ ↦ (quantile_le_iff hx).trans hF.le_iff_le

/-! ### Equivariance -/

/-- **Quantiles commute with monotone lower-semicontinuous maps**:
`quantile (μ.map h) p = h (quantile μ p)`. Lower semicontinuity makes `{h ≤ y}` closed, which is
what keeps the lower sets of `h ∘ quantile` and of the image quantile aligned; continuous
increasing maps are the main instance (`quantile_map_of_strictMono`). -/
theorem quantile_map [IsProbabilityMeasure μ] {h : ℝ → ℝ} (hmono : Monotone h)
    (hlsc : LowerSemicontinuous h) (hp : p ∈ Ioo 0 1) :
    quantile (μ.map h) p = h (quantile μ p) := by
  have hmeas : Measurable h := hmono.measurable
  refine eq_of_forall_ge_iff fun y ↦ ?_
  rw [quantile_le_iff hp, cdf_eq_real, map_measureReal_apply hmeas measurableSet_Iic]
  constructor
  · intro hpy
    by_contra! hlt
    -- the sublevel set `{h ≤ y}` is closed and lies strictly below `quantile μ p`
    set S := h ⁻¹' Iic y
    have hS : S ⊆ Iio (quantile μ p) := fun z hz ↦
      lt_of_not_ge fun hqz ↦ (hlt.trans_le (hmono hqz)).not_ge hz
    rcases S.eq_empty_or_nonempty with hS0 | hSne
    · rw [hS0, measureReal_empty] at hpy
      exact hp.1.not_ge hpy
    have hbdd : BddAbove S := ⟨quantile μ p, fun z hz ↦ (hS hz).le⟩
    have hmem : sSup S ∈ S := (hlsc.isClosed_preimage y).csSup_mem hSne hbdd
    have hcdf : cdf μ (sSup S) < p := (lt_quantile_iff hp).1 (hS hmem)
    rw [cdf_eq_real] at hcdf
    exact (hpy.trans (measureReal_mono fun z hz ↦ le_csSup hbdd hz)).not_gt hcdf
  · intro hqy
    calc p ≤ cdf μ (quantile μ p) := le_cdf_quantile hp
      _ = μ.real (Iic (quantile μ p)) := cdf_eq_real μ _
      _ ≤ μ.real (h ⁻¹' Iic y) := measureReal_mono fun z hz ↦ (hmono hz).trans hqy

/-- Quantiles commute with continuous strictly increasing maps (MFE Exercise 2.21). -/
theorem quantile_map_of_strictMono [IsProbabilityMeasure μ] {h : ℝ → ℝ} (hmono : StrictMono h)
    (hcont : Continuous h) (hp : p ∈ Ioo 0 1) :
    quantile (μ.map h) p = h (quantile μ p) :=
  quantile_map hmono.monotone hcont.lowerSemicontinuous hp

/-- Quantiles are affine-equivariant: `quantile (μ.map (a · + b)) p = a · quantile μ p + b` for
`a > 0`. -/
theorem quantile_map_affine [IsProbabilityMeasure μ] {a b : ℝ} (ha : 0 < a) (hp : p ∈ Ioo 0 1) :
    quantile (μ.map fun x ↦ a * x + b) p = a * quantile μ p + b :=
  quantile_map_of_strictMono (fun _ _ hxy ↦ by gcongr) (by fun_prop) hp

end MathFin
