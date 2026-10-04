/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Analysis.Dilation
public import LeanPool.EllipticPDE.Embedding.H01Sobolev
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.Basic


/-!
# Sharpness of the Sobolev embedding

The embedding of `H₀¹(Ω)` into `L^q(Ω)` is compact below the Sobolev conjugate and at the
conjugate itself is bounded. It is not compact there, and the obstruction is scaling: the
dilates of a fixed test function, renormalised to keep their `L^{2⋆}` norm, keep their gradient
norm as well and lose their `L²` norm.

Writing `φ_λ(x) = φ(x/λ)` and `v_λ = λ^{1 - d/2} φ_λ`, the three identities are

`‖v_λ‖_{L^{2⋆}} = ‖φ‖_{L^{2⋆}}`, `‖v_λ‖_{L²} = λ‖φ‖_{L²}`, `‖∂ᵢ v_λ‖_{L²} = ‖∂ᵢφ‖_{L²}`,

and the reason is `d/2⋆ = d/2 - 1`, the Sobolev relation itself. A family bounded in
`H₀¹(Ω)` whose images keep a fixed positive `L^{2⋆}` norm and tend to zero in `L²` has no
`L^{2⋆}`-convergent subsequence.

## Main declarations

* `EllipticPdes.Embedding.eLpNorm_dilate`: the `Lᵖ` seminorm of a dilate on the unit ball.
* `EllipticPdes.Embedding.eLpNorm_partialD_dilate`: the same for its partial derivatives.
* `EllipticPdes.Embedding.isTestFn_dilate`: a dilate of a test function is a test function.

## References

James Guo, *Partial Differential Equations*, Example IV.2.11.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev EllipticPdes.Analysis

variable {d : ℕ}

/-- The dilate `x ↦ φ(x/lam)` of a test function supported in the closed unit ball is a test
function on the unit ball, for `0 < lam ≤ 1/2`. -/
theorem isTestFn_dilate {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) φ)
    (hsupp : tsupport φ ⊆ closedBall 0 1) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / 2) :
    IsTestFn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) (fun x => φ (lam⁻¹ • x)) := by
  have hsub : tsupport (fun x => φ (lam⁻¹ • x)) ⊆ closedBall 0 lam := by
    have := tsupport_comp_smul_subset (f := φ) (r := lam⁻¹) (by positivity) hsupp
    rwa [inv_inv] at this
  refine ⟨h.1.comp (contDiff_const_smul _), ?_, hsub.trans ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) lam)
      ((subset_tsupport _).trans hsub)
  · intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_ball, dist_zero_right]
    linarith

/-- **`Lᵖ` seminorm of a dilate**, over the unit ball, where both sides see the whole space
since the supports lie inside. -/
theorem eLpNorm_dilate {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Measurable φ)
    {lam : ℝ} (hlam0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (fun x => φ (lam⁻¹ • x)) p volume
      = ENNReal.ofReal (lam ^ d) ^ (1 / p.toReal) * eLpNorm φ p volume := by
  rw [eLpNorm_comp_smul hφ (by positivity) hp0 hpt]
  congr 2
  rw [inv_pow, inv_inv, abs_of_nonneg (by positivity)]

/-- **Partial derivatives of a dilate**, in `Lᵖ`. -/
theorem eLpNorm_partialD_dilate {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (i : Fin d) (hmeas : Measurable (partialD i φ))
    {lam : ℝ} (hlam0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (partialD i (fun x => φ (lam⁻¹ • x))) p volume
      = ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal (lam ^ d) ^ (1 / p.toReal)
          * eLpNorm (partialD i φ) p volume) := by
  rw [partialD_comp_smul (hφ.differentiable one_ne_zero) _ i]
  rw [show (fun x => lam⁻¹ * partialD i φ (lam⁻¹ • x))
      = lam⁻¹ • (fun y => partialD i φ (lam⁻¹ • y)) from rfl,
    eLpNorm_const_smul, eLpNorm_comp_smul hmeas (by positivity) hp0 hpt]
  congr 2
  · simp [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hlam0)]
  · rw [inv_pow, inv_inv, abs_of_nonneg (by positivity)]


/-! ### The test function the argument dilates -/

/-- A bump on the unit ball: one on `closedBall 0 (1/4)` and supported in `closedBall 0 (1/2)`. -/
def sharpBump (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

@[simp] lemma tsupport_sharpBump :
    tsupport (⇑(sharpBump d)) = closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) :=
  (sharpBump d).tsupport_eq

lemma tsupport_sharpBump_subset :
    tsupport (⇑(sharpBump d)) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  rw [tsupport_sharpBump]
  exact closedBall_subset_closedBall (by norm_num)

lemma isTestFn_sharpBump : IsTestFn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) (⇑(sharpBump d)) := by
  refine ⟨(sharpBump d).contDiff, (sharpBump d).hasCompactSupport, ?_⟩
  rw [tsupport_sharpBump]
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  rw [mem_ball, dist_zero_right]
  linarith

lemma sharpBump_zero : (sharpBump d) 0 = 1 :=
  (sharpBump d).one_of_mem_closedBall (mem_closedBall_self (sharpBump d).rIn_pos.le)

/-- The bump has positive `Lᵖ` seminorm, being continuous and nonzero at the origin. -/
lemma eLpNorm_sharpBump_ne_zero {p : ℝ≥0∞} (hp0 : p ≠ 0) :
    eLpNorm (⇑(sharpBump d)) p volume ≠ 0 := by
  rw [Ne, eLpNorm_eq_zero_iff hp0]
  intro hae
  have hzero : (⇑(sharpBump d) : EuclideanSpace ℝ (Fin d) → ℝ) = 0 :=
    (sharpBump d).continuous.ae_eq_iff_eq volume continuous_const |>.mp hae
  have := sharpBump_zero (d := d)
  rw [hzero] at this
  simp at this

/-! ### The graph coordinates of a test function -/

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The function coordinate of a test graph, in `Lᵖ` over the whole space. -/
lemma eLpNorm_testGraph_zero_eq (hΩm : MeasurableSet Ω) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω ψ) (p : ℝ≥0∞) :
    eLpNorm (h.testGraph 0 : L2D Ω) p (volume.restrict Ω) = eLpNorm ψ p volume := by
  rw [eLpNorm_testGraph_zero p h, eLpNorm_restrict_eq_of_tsupport_subset hΩm h.2.2 p]

/-- A gradient coordinate of a test graph, in `Lᵖ` over the whole space. -/
lemma eLpNorm_testGraph_succ_eq (hΩm : MeasurableSet Ω) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω ψ) (p : ℝ≥0∞) (i : Fin d) :
    eLpNorm (h.testGraph i.succ : L2D Ω) p (volume.restrict Ω)
      = eLpNorm (partialD i ψ) p volume := by
  rw [IsTestFn.testGraph_succ, IsTestFn.partialCls,
    eLpNorm_congr_ae (h.memLp_partialD i).coeFn_toLp,
    eLpNorm_restrict_eq_of_tsupport_subset hΩm ((tsupport_partialD_subset i ψ).trans h.2.2) p]


/-! ### The renormalised dilates -/

/-- `lam^{1 - d/2} φ(·/lam)`, the dilate renormalised to keep its `L^{2⋆}` norm. -/
def sharpFamily (d : ℕ) (lam : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (lam ^ (1 - (d : ℝ) / 2)) • fun x => (sharpBump d) (lam⁻¹ • x)

lemma isTestFn_sharpFamily {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) :
    IsTestFn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) (sharpFamily d lam) :=
  (isTestFn_dilate isTestFn_sharpBump tsupport_sharpBump_subset h0 h1).const_smul _

private lemma rpow_pow_mul {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (t : ℝ) :
    (lam ^ n) ^ t = lam ^ ((n : ℝ) * t) := by
  rw [← Real.rpow_natCast lam n, ← Real.rpow_mul hlam.le]

/-- The `Lᵖ` seminorm of a renormalised dilate, with the two powers of `lam` collected. -/
lemma eLpNorm_sharpFamily {lam : ℝ} (h0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (sharpFamily d lam) p volume
      = ENNReal.ofReal (lam ^ (1 - (d : ℝ) / 2 + (d : ℝ) * (1 / p.toReal)))
        * eLpNorm (⇑(sharpBump d)) p volume := by
  rw [sharpFamily, eLpNorm_const_smul,
    eLpNorm_dilate (sharpBump d).continuous.measurable h0 hp0 hpt,
    ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.rpow_pos_of_pos h0 _),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_nonneg.mpr ENNReal.toReal_nonneg),
    rpow_pow_mul h0, ← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos h0 _)),
    ← Real.rpow_add h0]

/-- The same for a gradient coordinate, which picks up one further power of the dilation. -/
lemma eLpNorm_partialD_sharpFamily {lam : ℝ} (h0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) (i : Fin d) :
    eLpNorm (partialD i (sharpFamily d lam)) p volume
      = ENNReal.ofReal (lam ^ (1 - (d : ℝ) / 2 - 1 + (d : ℝ) * (1 / p.toReal)))
        * eLpNorm (partialD i (⇑(sharpBump d))) p volume := by
  have hdiff : Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin d) => (sharpBump d) (lam⁻¹ • x)) :=
    ((sharpBump d).contDiff (n := 1)).differentiable (by norm_num) |>.comp
      ((differentiable_id).const_smul lam⁻¹)
  have hmeas : Measurable (partialD i (⇑(sharpBump d))) :=
    ((isTestFn_sharpBump (d := d)).continuous_partialD i).measurable
  rw [sharpFamily, partialD_const_smul hdiff _ i, eLpNorm_const_smul,
    eLpNorm_partialD_dilate ((sharpBump d).contDiff (n := 1)) i hmeas h0 hp0 hpt,
    ← mul_assoc, ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.rpow_pos_of_pos h0 _),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_nonneg.mpr ENNReal.toReal_nonneg),
    rpow_pow_mul h0, ← Real.rpow_neg_one lam,
    ← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos h0 _)),
    ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_add h0, ← Real.rpow_add h0]
  ring_nf


/-! ### The family in `H₀¹` of the unit ball -/

/-- The renormalised dilate, as an element of `H₀¹` of the unit ball. -/
def sharpElt (d : ℕ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) :
    H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  ⟨(isTestFn_sharpFamily h0 h1).testGraph,
    (Submodule.le_topologicalClosure _)
      (Submodule.subset_span ⟨sharpFamily d lam, isTestFn_sharpFamily h0 h1, rfl⟩)⟩

variable {lam : ℝ}

lemma eLpNorm_sharpElt_zero (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) {p : ℝ≥0∞} :
    eLpNorm (((sharpElt d h0 h1 : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
        H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) 0) p
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = eLpNorm (sharpFamily d lam) p volume :=
  eLpNorm_testGraph_zero_eq measurableSet_ball (isTestFn_sharpFamily h0 h1) p

lemma eLpNorm_sharpElt_succ (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) {p : ℝ≥0∞} (i : Fin d) :
    eLpNorm (((sharpElt d h0 h1 : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
        H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) i.succ) p
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = eLpNorm (partialD i (sharpFamily d lam)) p volume :=
  eLpNorm_testGraph_succ_eq measurableSet_ball (isTestFn_sharpFamily h0 h1) p i

/-- At the critical exponent the two powers of `lam` cancel: the renormalised dilates all have
the seminorm of the bump itself. -/
lemma eLpNorm_sharpFamily_crit {p' : ℝ≥0} (hp'0 : p' ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hd : 0 < d) (h0 : 0 < lam) :
    eLpNorm (sharpFamily d lam) (p' : ℝ≥0∞) volume
      = eLpNorm (⇑(sharpBump d)) (p' : ℝ≥0∞) volume := by
  rw [eLpNorm_sharpFamily h0 (by simpa using hp'0) (by simp)]
  have hp'R : ((p' : ℝ≥0∞)).toReal = (p' : ℝ) := by simp
  have hexp : 1 - (d : ℝ) / 2 + (d : ℝ) * (1 / ((p' : ℝ≥0∞)).toReal) = 0 := by
    have hp'' : (p' : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
      simpa using hp'
    rw [hp'R, one_div, hp'']
    have hdne : (d : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hexp, Real.rpow_zero, ENNReal.ofReal_one, one_mul]

/-- At the exponent `2` the renormalised dilates lose their norm linearly in `lam`. -/
lemma eLpNorm_sharpFamily_two (h0 : 0 < lam) :
    eLpNorm (sharpFamily d lam) 2 volume
      = ENNReal.ofReal lam * eLpNorm (⇑(sharpBump d)) 2 volume := by
  rw [eLpNorm_sharpFamily h0 two_ne_zero (by simp)]
  congr 2
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by simp
  rw [h2, show 1 - (d : ℝ) / 2 + (d : ℝ) * (1 / 2) = 1 by ring, Real.rpow_one]

/-- The gradient coordinates keep their norm. -/
lemma eLpNorm_partialD_sharpFamily_two (h0 : 0 < lam) (i : Fin d) :
    eLpNorm (partialD i (sharpFamily d lam)) 2 volume
      = eLpNorm (partialD i (⇑(sharpBump d))) 2 volume := by
  rw [eLpNorm_partialD_sharpFamily h0 two_ne_zero (by simp) i]
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by simp
  rw [h2, show 1 - (d : ℝ) / 2 - 1 + (d : ℝ) * (1 / 2) = 0 by ring, Real.rpow_zero,
    ENNReal.ofReal_one, one_mul]


/-! ### Sharpness -/

section Crit

variable {p' : ℝ≥0} [Fact (1 ≤ (p' : ℝ≥0∞))]

/-- The Sobolev embedding of `H₀¹` of the unit ball at the critical exponent. -/
def critEmb (d : ℕ) (hd : 0 < d) (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1) →L[ℝ]
      Lp ℝ (p' : ℝ≥0∞) (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  sobolevEmbL (fun _U hU => eLpNorm_le_of_mem_H01 measurableSet_ball hd hp' hU)

lemma eLpNorm_critEmb (hd : 0 < d) (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹)
    (U : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) (q : ℝ≥0∞) :
    eLpNorm (⇑(critEmb d hd hp' U)) q (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = eLpNorm (((U : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1))) 0) q
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  eLpNorm_congr_ae (coeFn_sobolevEmbL _ U)

lemma norm_critEmb (hd : 0 < d) (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹)
    (U : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    ‖critEmb d hd hp' U‖
      = (eLpNorm (((U : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1))) 0) (p' : ℝ≥0∞)
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))).toReal := by
  rw [Lp.norm_def, eLpNorm_critEmb]

end Crit

/-- **Failure of compactness at the critical exponent.** The renormalised dilates
stay in the unit ball of `H₀¹`, keep the `L^{2⋆}` norm of the bump, and lose their `L²` norm, so
their images have no convergent subsequence.

Compactness below the critical exponent is `rellichEmbL_isCompact_of_lt`. This is where that
range stops. -/
theorem not_isCompactOperator_critEmb (hd : 2 < d) (hdpos : 0 < d) {p' : ℝ≥0}
    [Fact (1 ≤ (p' : ℝ≥0∞))] (hp'0 : p' ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ¬ IsCompactOperator (critEmb d hdpos hp') := by
  intro hcpt
  -- The bump's two seminorms, both positive and finite.
  have hfin : ∀ q : ℝ≥0∞, eLpNorm (⇑(sharpBump d)) q volume ≠ ⊤ := fun q =>
    ((sharpBump d).continuous.memLp_of_hasCompactSupport
      (μ := volume) (p := q) (sharpBump d).hasCompactSupport).eLpNorm_ne_top
  set a : ℝ := (eLpNorm (⇑(sharpBump d)) 2 volume).toReal with hadef
  set c : ℝ := (eLpNorm (⇑(sharpBump d)) (p' : ℝ≥0∞) volume).toReal with hcdef
  have ha0 : 0 < a := by
    rw [hadef, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr (eLpNorm_sharpBump_ne_zero two_ne_zero),
      lt_top_iff_ne_top.mpr (hfin 2)⟩
  have hc0 : 0 < c := by
    rw [hcdef, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr (eLpNorm_sharpBump_ne_zero (by simpa using hp'0)),
      lt_top_iff_ne_top.mpr (hfin _)⟩
  -- The dilation parameters.
  have hl0 : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 2) := fun n => by positivity
  have hl1 : ∀ n : ℕ, (1 : ℝ) / (n + 2) ≤ 1 / 2 := fun n => by
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hltend : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
    have hto : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [Pi.inv_def, one_div] using hto.inv_tendsto_atTop
  -- The family and its coordinates.
  set U : ℕ → H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    fun n => sharpElt d (hl0 n) (hl1 n) with hUdef
  set b : Fin d → ℝ := fun i => (eLpNorm (partialD i (⇑(sharpBump d))) 2 volume).toReal with hbdef
  have hzero : ∀ n, ‖((U n : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
      H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) 0‖ = 1 / ((n : ℝ) + 2) * a := by
    intro n
    rw [Lp.norm_def, hUdef, eLpNorm_sharpElt_zero, eLpNorm_sharpFamily_two (hl0 n),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (hl0 n).le]
  have hsucc : ∀ n i, ‖((U n : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
      H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) i.succ‖ = b i := by
    intro n i
    rw [Lp.norm_def, hUdef, eLpNorm_sharpElt_succ, eLpNorm_partialD_sharpFamily_two (hl0 n)]
  -- A bound on the family, uniform in `n`.
  set B : ℝ := Real.sqrt (a ^ 2 + ∑ i, (b i) ^ 2) with hBdef
  have hB0 : 0 < B := by
    rw [hBdef]
    refine Real.sqrt_pos.mpr ?_
    have hnn : 0 ≤ ∑ i, (b i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have ha2 : 0 < a ^ 2 := by positivity
    linarith
  have hUbound : ∀ n, ‖U n‖ ≤ B := by
    intro n
    have hsq : ‖(U n : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1))‖ ^ 2
        ≤ a ^ 2 + ∑ i, (b i) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin (d + 1) => L2D (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
        (U n : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)), Fin.sum_univ_succ]
      have h0' : ‖((U n : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
          H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) 0‖ ^ 2 ≤ a ^ 2 := by
        rw [hzero n]
        have hla : 1 / ((n : ℝ) + 2) * a ≤ a := by
          have := hl1 n
          nlinarith [ha0.le, (hl0 n).le]
        have hla0 : 0 ≤ 1 / ((n : ℝ) + 2) * a := mul_nonneg (hl0 n).le ha0.le
        nlinarith [hla, hla0]
      have hi' : ∀ i : Fin d, ‖((U n : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
          H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) i.succ‖ ^ 2 = (b i) ^ 2 := fun i => by
        rw [hsucc n i]
      rw [Finset.sum_congr rfl (fun i _ => hi' i)]
      linarith
    have hsr := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), ← hBdef] at hsr
  -- The renormalised family sits in the closed unit ball.
  set W : ℕ → H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := fun n => B⁻¹ • U n with hWdef
  have hWball : ∀ n, W n ∈ closedBall (0 : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) 1 := by
    intro n
    rw [mem_closedBall, dist_zero_right, hWdef, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hB0)]
    calc B⁻¹ * ‖U n‖
        ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hUbound n) (inv_pos.mpr hB0).le
      _ = 1 := inv_mul_cancel₀ hB0.ne'
  -- The images keep a fixed positive norm and lose their `L²` seminorm.
  have himg : ∀ n, ‖critEmb d hdpos hp' (W n)‖ = B⁻¹ * c := by
    intro n
    rw [hWdef, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB0)]
    congr 1
    rw [norm_critEmb, hUdef, eLpNorm_sharpElt_zero,
      eLpNorm_sharpFamily_crit hp'0 hp' hdpos (hl0 n)]
  have hL2 : ∀ n, eLpNorm (⇑(critEmb d hdpos hp' (W n))) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = ENNReal.ofReal (B⁻¹ * (1 / ((n : ℝ) + 2) * a)) := by
    intro n
    rw [hWdef, map_smul, eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul,
      eLpNorm_critEmb, hUdef, eLpNorm_sharpElt_zero, eLpNorm_sharpFamily_two (hl0 n),
      Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hB0),
      show eLpNorm (⇑(sharpBump d)) 2 volume = ENNReal.ofReal a from
        (ENNReal.ofReal_toReal (hfin 2)).symm,
      ← ENNReal.ofReal_mul (hl0 n).le, ← ENNReal.ofReal_mul (inv_pos.mpr hB0).le]
  -- Compactness would give a convergent subsequence.
  have hcptL : IsCompactOperator ((critEmb d hdpos hp').toLinearMap) := hcpt
  have hcptC := (isCompactOperator_iff_isCompact_closure_image_closedBall
    (critEmb d hdpos hp').toLinearMap one_pos).mp hcptL
  have hmemcl : ∀ n, critEmb d hdpos hp' (W n) ∈ closure (⇑(critEmb d hdpos hp').toLinearMap ''
      closedBall (0 : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) 1) :=
    fun n => subset_closure ⟨W n, hWball n, rfl⟩
  obtain ⟨v, -, ψ, hψ, hψtend⟩ := hcptC.tendsto_subseq hmemcl
  have hvnorm : ‖v‖ = B⁻¹ * c := by
    refine tendsto_nhds_unique ((continuous_norm.tendsto v).comp hψtend) ?_
    simp [Function.comp_def, himg]
  -- The limit has vanishing `L²` seminorm, hence is zero.
  have hp'2R : (2 : ℝ) ≤ (p' : ℝ) := by
    have hp2 : (p' : ℝ)⁻¹ = 2⁻¹ - (d : ℝ)⁻¹ := by simpa using hp'
    have hdR : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hdinv : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
    have hdlt : (d : ℝ)⁻¹ < (2 : ℝ)⁻¹ := by
      rw [inv_lt_inv₀ (by linarith) (by norm_num)]
      exact hdR
    have hppos : (0 : ℝ) < (p' : ℝ)⁻¹ := by rw [hp2]; linarith
    have hp'pos : (0 : ℝ) < (p' : ℝ) := by
      rcases (NNReal.coe_nonneg p').lt_or_eq with h | h
      · exact h
      · rw [← h] at hppos; simp at hppos
    have h1 : (p' : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by rw [hp2]; linarith
    exact (inv_le_inv₀ hp'pos (by norm_num)).mp h1
  have h2p' : (2 : ℝ≥0∞) ≤ (p' : ℝ≥0∞) := by exact_mod_cast hp'2R
  set e : ℝ := 1 / (2 : ℝ≥0∞).toReal - 1 / ((p' : ℝ≥0∞)).toReal with hedef
  set mv : ℝ≥0∞ := (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) Set.univ with hmvdef
  have hbnd : ∀ k, eLpNorm (⇑v) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      ≤ ‖v - critEmb d hdpos hp' (W (ψ k))‖ₑ * mv ^ e
        + ENNReal.ofReal (B⁻¹ * (1 / ((ψ k : ℝ) + 2) * a)) := by
    intro k
    have hfirst : eLpNorm (⇑v - ⇑(critEmb d hdpos hp' (W (ψ k)))) 2
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
        ≤ ‖v - critEmb d hdpos hp' (W (ψ k))‖ₑ * mv ^ e := by
      refine le_trans (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h2p'
        ((Lp.aestronglyMeasurable v).sub (Lp.aestronglyMeasurable _))) ?_
      refine mul_le_mul' (le_of_eq ?_) le_rfl
      rw [Lp.enorm_def]
      exact eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
    have hsplit : eLpNorm (⇑v) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
        ≤ eLpNorm (⇑v - ⇑(critEmb d hdpos hp' (W (ψ k)))) 2
            (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
          + eLpNorm (⇑(critEmb d hdpos hp' (W (ψ k)))) 2
            (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
      have hfun : (⇑v : EuclideanSpace ℝ (Fin d) → ℝ)
          = (⇑v - ⇑(critEmb d hdpos hp' (W (ψ k)))) + ⇑(critEmb d hdpos hp' (W (ψ k))) := by
        funext x; simp
      conv_lhs => rw [hfun]
      exact eLpNorm_add_le one_le_two
    refine hsplit.trans ?_
    rw [hL2 (ψ k)]
    exact add_le_add hfirst le_rfl
  have htend0 : Filter.Tendsto
      (fun k => ‖v - critEmb d hdpos hp' (W (ψ k))‖ₑ * mv ^ e
        + ENNReal.ofReal (B⁻¹ * (1 / ((ψ k : ℝ) + 2) * a))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k => ‖v - critEmb d hdpos hp' (W (ψ k))‖ₑ)
        Filter.atTop (nhds 0) := by
      have hreal : Filter.Tendsto (fun k => ‖v - critEmb d hdpos hp' (W (ψ k))‖)
          Filter.atTop (nhds 0) := by
        have hsub := (hψtend.const_sub v).norm
        simpa [Function.comp_def] using hsub
      have := ENNReal.tendsto_ofReal hreal
      simpa [ofReal_norm] using this
    have h2 : Filter.Tendsto (fun k => ENNReal.ofReal (B⁻¹ * (1 / ((ψ k : ℝ) + 2) * a)))
        Filter.atTop (nhds 0) := by
      have hreal : Filter.Tendsto (fun k => B⁻¹ * (1 / ((ψ k : ℝ) + 2) * a))
          Filter.atTop (nhds 0) := by
        have hcomp := (hltend.comp hψ.tendsto_atTop).mul_const a
        have := hcomp.const_mul B⁻¹
        simpa [Function.comp_def] using this
      simpa using ENNReal.tendsto_ofReal hreal
    have hmvne : mv ^ e ≠ ⊤ := by
      rw [hmvdef, Measure.restrict_apply_univ]
      refine ENNReal.rpow_ne_top_of_nonneg ?_ measure_ball_lt_top.ne
      rw [hedef]
      have h2R : (2 : ℝ≥0∞).toReal = 2 := by simp
      have hp'R : ((p' : ℝ≥0∞)).toReal = (p' : ℝ) := by simp
      rw [h2R, hp'R, sub_nonneg]
      exact one_div_le_one_div_of_le (by norm_num) hp'2R
    have hsum := (ENNReal.Tendsto.mul_const h1 (Or.inr hmvne)).add h2
    simpa using hsum
  have hzeroL2 : eLpNorm (⇑v) 2
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) = 0 :=
    le_antisymm (ge_of_tendsto htend0 (Filter.Eventually.of_forall hbnd)) (by simp)
  have hvzero : ‖v‖ = 0 := by
    rw [Lp.norm_def, eLpNorm_congr_ae
      ((eLpNorm_eq_zero_iff two_ne_zero).mp hzeroL2)]
    simp
  rw [hvnorm] at hvzero
  have hpos : (0 : ℝ) < B⁻¹ * c := mul_pos (inv_pos.mpr hB0) hc0
  linarith

end EllipticPdes.Embedding
