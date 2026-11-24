/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.FunctionalCalculusSemigroup
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Continuity and differentiability of the `cfc` semigroup

For `R` as in `FunctionalCalculusSemigroup` (with `R` injective):
* `‖T_s R - R‖ ≤ s` in operator norm, hence `T_s u → u` for all `u` (density of `ran R`);
  `t ↦ T_t u` is continuous on `ℝ≥0` for every `u`;
* for `t > 0`, `s ↦ T_s R` is differentiable in operator norm with derivative `-T_t (1 - R)`;
  in particular `HasDerivAt (s ↦ T_s (R g)) (-(T_t (g - R g))) t`;
* the integral form `T_t (R g) - R g = - ∫₀ᵗ T_s (g - R g) ds`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped NNReal InnerProductSpace

namespace CutoffRigidity.Riemann.Diff


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma abs_exp_neg_sub_le (y : ℝ) :
    |Real.exp (-y) - 1 + y| ≤ 3 * y ^ 2 * Real.exp |y| := by
  have he1 : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg y)
  by_cases hy : |y| ≤ 1
  · have h := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rwa [abs_neg])
    have : Real.exp (-y) - 1 + y = Real.exp (-y) - 1 - (-y) := by ring
    rw [this]
    refine h.trans ?_
    have : (-y) ^ 2 = y ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg y]
  · rw [not_le] at hy
    have h1 : Real.exp (-y) ≤ Real.exp |y| := Real.exp_le_exp.mpr (neg_le_abs y)
    have h2 : 1 ≤ y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    have h3 : |y| ≤ y ^ 2 := by nlinarith [sq_abs y]
    have h4 : y ^ 2 ≤ y ^ 2 * Real.exp |y| := by nlinarith [sq_nonneg y]
    have h5 : Real.exp |y| ≤ y ^ 2 * Real.exp |y| := by nlinarith [Real.exp_pos |y|]
    have h6 : |Real.exp (-y) - 1 + y| ≤ Real.exp (-y) + 1 + |y| := by
      calc |Real.exp (-y) - 1 + y| ≤ |Real.exp (-y) - 1| + |y| := abs_add_le _ _
        _ ≤ (|Real.exp (-y)| + |1|) + |y| := by gcongr; exact abs_sub _ _
        _ = Real.exp (-y) + 1 + |y| := by rw [abs_of_pos (Real.exp_pos _), abs_one]
    linarith

/-- Semigroup parameter as a real number. -/
noncomputable def hfunR (s : ℝ) (r : ℝ) : ℝ := hfun s.toNNReal r

lemma hfunR_of_pos {s : ℝ} (hs : 0 < s) {r : ℝ} (hr : 0 < r) :
    hfunR s r = Real.exp (-s * (r⁻¹ - 1)) := by
  have h1 : s.toNNReal ≠ 0 := by simpa using hs
  unfold hfunR
  rw [hfun_of_pos h1 hr, Real.coe_toNNReal _ hs.le]

lemma hfunR_zero {s : ℝ} (hs : 0 < s) : hfunR s 0 = 0 := by
  have h1 : s.toNNReal ≠ 0 := by simpa using hs
  unfold hfunR
  exact hfun_of_nonpos h1 le_rfl

lemma quad_exp_bound {α w : ℝ} (hα : 0 < α) (hw : 0 ≤ w) :
    w ^ 2 * Real.exp (-(α * w)) ≤ 2 / α ^ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := α * w) (by positivity)
  have h2 : (α * w) ^ 2 / 2 ≤ Real.exp (α * w) := by nlinarith [mul_nonneg hα.le hw]
  have hpos := Real.exp_pos (-(α * w))
  have h3 : Real.exp (α * w) * Real.exp (-(α * w)) = 1 := by rw [← Real.exp_add]; simp
  have h4 : w ^ 2 * Real.exp (-(α * w)) ≤ 2 / α ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc w ^ 2 * Real.exp (-(α * w)) * α ^ 2 = (α * w) ^ 2 * Real.exp (-(α * w)) := by ring
      _ ≤ (2 * Real.exp (α * w)) * Real.exp (-(α * w)) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le; linarith
      _ = 2 := by rw [mul_assoc, h3, mul_one]
  exact h4

lemma scalar_remainder {t s : ℝ} (ht : 0 < t) (hs : |s - t| ≤ t / 2) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    |hfunR s r * r - hfunR t r * r + (s - t) * ((1 - r) * hfunR t r)| ≤
      24 * (s - t) ^ 2 / t ^ 2 := by
  have hs0 : 0 < s := by
    have := (abs_le.mp hs).1
    linarith
  have hb : 0 ≤ 24 * (s - t) ^ 2 / t ^ 2 := by positivity
  rcases hr.1.eq_or_lt with h | h
  · rw [← h, hfunR_zero hs0, hfunR_zero ht]; simpa using hb
  · set w : ℝ := r⁻¹ - 1 with hw
    have hw0 : 0 ≤ w := by
      have := (one_le_inv₀ h).mpr hr.2
      rw [hw]; linarith
    have hrw : 1 - r = r * w := by rw [hw]; field_simp
    set δ : ℝ := s - t with hδ
    rw [hfunR_of_pos hs0 h, hfunR_of_pos ht h, hrw]
    have e1 : Real.exp (-s * w) = Real.exp (-t * w) * Real.exp (-(δ * w)) := by
      rw [← Real.exp_add]; congr 1; rw [hδ]; ring
    have e2 : r * Real.exp (-s * w) - r * Real.exp (-t * w) + δ * (r * w * Real.exp (-t * w)) =
        r * Real.exp (-t * w) * (Real.exp (-(δ * w)) - 1 + δ * w) := by
      rw [e1]; ring
    have e3 : Real.exp (-s * (r⁻¹ - 1)) * r - Real.exp (-t * (r⁻¹ - 1)) * r +
        (s - t) * (r * w * Real.exp (-t * (r⁻¹ - 1))) =
        r * Real.exp (-s * w) - r * Real.exp (-t * w) + δ * (r * w * Real.exp (-t * w)) := by
      rw [← hw]; ring
    rw [e3, e2, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r * Real.exp (-t * w))]
    have h1 := abs_exp_neg_sub_le (δ * w)
    have h2 : |δ * w| ≤ (t / 2) * w := by
      rw [abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul_of_nonneg_right hs hw0
    have h3 : Real.exp (-t * w) * Real.exp |δ * w| ≤ Real.exp (-((t / 2) * w)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    have h4 := quad_exp_bound (α := t / 2) (by positivity) hw0
    have hr1 : r ≤ 1 := hr.2
    calc r * Real.exp (-t * w) * |Real.exp (-(δ * w)) - 1 + δ * w|
        ≤ 1 * Real.exp (-t * w) * (3 * (δ * w) ^ 2 * Real.exp |δ * w|) := by
          apply mul_le_mul _ h1 (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right hr1 (Real.exp_pos _).le
      _ = 3 * δ ^ 2 * (w ^ 2 * (Real.exp (-t * w) * Real.exp |δ * w|)) := by ring
      _ ≤ 3 * δ ^ 2 * (w ^ 2 * Real.exp (-((t / 2) * w))) := by
          gcongr
      _ ≤ 3 * δ ^ 2 * (2 / (t / 2) ^ 2) := by gcongr
      _ = 24 * δ ^ 2 / t ^ 2 := by field_simp; ring

variable {R : H →L[ℝ] H} (hR : UnitOp R)
include hR

/-- `T_s R` as a function of `R`. -/
lemma cfcSemigroup_mul_R (s : ℝ≥0) :
    cfcSemigroup R s * R = cfc (fun r => hfun s r * r) R := by
  unfold cfcSemigroup
  have h := hR.rcfc_mul (continuousOn_hfun s) (f := hfun s) (g := id) continuousOn_id
  rw [hR.rcfc_id] at h
  exact h.symm

omit hR in
lemma abs_hfun_mul_sub_le (s : ℝ≥0) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    |hfun s r * r - r| ≤ s := by
  by_cases hs : s = 0
  · simp [hs, hfun_zero]
  rcases hr.1.eq_or_lt with h | h
  · rw [← h]; simp
  · have hw : 0 ≤ r⁻¹ - 1 := by
      have := (one_le_inv₀ h).mpr hr.2
      linarith
    rw [hfun_of_pos hs h]
    have h1 : 0 ≤ Real.exp (-(s : ℝ) * (r⁻¹ - 1)) := (Real.exp_pos _).le
    have h2 : Real.exp (-(s : ℝ) * (r⁻¹ - 1)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ (s : ℝ) := s.2
      nlinarith
    have h3 : 1 - (s : ℝ) * (r⁻¹ - 1) ≤ Real.exp (-(s : ℝ) * (r⁻¹ - 1)) := by
      have := Real.add_one_le_exp (-(s : ℝ) * (r⁻¹ - 1))
      linarith
    rw [abs_le]
    have hrs : r * (r⁻¹ - 1) = 1 - r := by field_simp
    have hs0 : (0 : ℝ) ≤ s := s.2
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left h3 h.le]
    · nlinarith

lemma norm_cfcSemigroup_mul_sub_le (s : ℝ≥0) : ‖cfcSemigroup R s * R - R‖ ≤ s := by
  have h1 : cfcSemigroup R s * R - R = cfc (fun r => hfun s r * r - r) R := by
    have := hR.rcfc_sub (f := fun r => hfun s r * r) (g := id)
      ((continuousOn_hfun s).mul continuousOn_id) continuousOn_id
    rw [cfcSemigroup_mul_R hR]
    simp only [id] at this
    rw [this, hR.rcfc_id']
  rw [h1]
  exact hR.norm_rcfc_le s.2 (fun r hr => abs_hfun_mul_sub_le s hr)

/-- `ran R` is dense when `R` is injective. -/
lemma denseRange_of_injective (hinj : Function.Injective R) : Dense (Set.range R) := by
  have hsa := hR.selfAdjoint
  have h : (LinearMap.range R.toLinearMap)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have h1 : ∀ x, inner ℝ (R x) u = 0 := fun x =>
      (Submodule.mem_orthogonal _ _).mp hu _ ⟨x, rfl⟩
    have h2 : R u = 0 := by
      apply ext_inner_right ℝ
      intro x
      have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
      have := hsym u x
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, real_inner_comm, h1]; simp
    exact hinj (by rw [h2, map_zero])
  have h' : (LinearMap.range R.toLinearMap).topologicalClosure = ⊤ :=
    Submodule.topologicalClosure_eq_top_iff.mpr h
  have := (Submodule.dense_iff_topologicalClosure_eq_top
    (s := LinearMap.range R.toLinearMap)).mpr h'
  rwa [show ((LinearMap.range R.toLinearMap : Submodule ℝ H) : Set H) = Set.range R from
    LinearMap.coe_range _] at this

/-- Strong continuity at `0`. -/
lemma tendsto_cfcSemigroup_zero (hinj : Function.Injective R) (u : H) :
    ∀ ε > 0, ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s : ℝ≥0, s < δ → ‖cfcSemigroup R s u - u‖ < ε := by
  intro ε hε
  have hd := denseRange_of_injective hR hinj
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := Metric.mem_closure_iff.mp (hd u) (ε / 3) (by positivity)
  rw [dist_eq_norm] at hg
  -- hg : ‖u - R g‖ < ε / 3
  set δ0 : ℝ := ε / (3 * (‖g‖ + 1)) with hδ0
  have hδpos : 0 < δ0 := by positivity
  refine ⟨⟨δ0, hδpos.le⟩, by exact_mod_cast hδpos, fun s hs => ?_⟩
  have hs' : (s : ℝ) < δ0 := by exact_mod_cast hs
  have h1 : ‖cfcSemigroup R s (u - R g)‖ ≤ ‖u - R g‖ := norm_cfcSemigroup_apply_le hR s _
  have h2 : ‖cfcSemigroup R s (R g) - R g‖ ≤ s * ‖g‖ := by
    have := (cfcSemigroup R s * R - R).le_opNorm g
    have h3 := norm_cfcSemigroup_mul_sub_le hR s
    simp only [sub_apply, mul_apply_eq_comp] at this
    calc ‖cfcSemigroup R s (R g) - R g‖ ≤ ‖cfcSemigroup R s * R - R‖ * ‖g‖ := this
      _ ≤ s * ‖g‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  have h4 : (s : ℝ) * ‖g‖ < ε / 3 := by
    have : (s : ℝ) * ‖g‖ ≤ (s : ℝ) * (‖g‖ + 1) := by
      rw [mul_add, mul_one]; linarith [NNReal.coe_nonneg s]
    have h5 : (s : ℝ) * (‖g‖ + 1) < δ0 * (‖g‖ + 1) :=
      mul_lt_mul_of_pos_right hs' (by positivity)
    have h6 : δ0 * (‖g‖ + 1) = ε / 3 := by rw [hδ0]; field_simp
    linarith
  have h7 : cfcSemigroup R s u - u = cfcSemigroup R s (u - R g) +
      (cfcSemigroup R s (R g) - R g) + (R g - u) := by
    rw [map_sub]; abel
  rw [h7]
  calc ‖cfcSemigroup R s (u - R g) + (cfcSemigroup R s (R g) - R g) + (R g - u)‖
      ≤ ‖cfcSemigroup R s (u - R g)‖ + ‖cfcSemigroup R s (R g) - R g‖ + ‖R g - u‖ :=
        norm_add₃_le
    _ < ε := by rw [norm_sub_rev (R g) u]; linarith

/-- For all `u`, `t ↦ T_t u` is continuous on `ℝ≥0`. -/
theorem continuous_cfcSemigroup_apply (hinj : Function.Injective R) (u : H) :
    Continuous fun t : ℝ≥0 => cfcSemigroup R t u := by
  have key : ∀ s t : ℝ≥0, s ≤ t →
      ‖cfcSemigroup R t u - cfcSemigroup R s u‖ ≤ ‖cfcSemigroup R (t - s) u - u‖ := by
    intro s t hst
    have : cfcSemigroup R t = cfcSemigroup R s * cfcSemigroup R (t - s) := by
      rw [← cfcSemigroup_add hR, add_tsub_cancel_of_le hst]
    have h1 : cfcSemigroup R t u - cfcSemigroup R s u =
        cfcSemigroup R s (cfcSemigroup R (t - s) u - u) := by
      rw [this, mul_apply_eq_comp, map_sub]
    rw [h1]
    exact norm_cfcSemigroup_apply_le hR s _
  rw [Metric.continuous_iff]
  intro t ε hε
  obtain ⟨δ, hδ, hδε⟩ := tendsto_cfcSemigroup_zero hR hinj u ε hε
  refine ⟨δ, by exact_mod_cast hδ, fun s hs => ?_⟩
  rw [dist_eq_norm]
  rw [NNReal.dist_eq] at hs
  rcases le_total s t with h | h
  · rw [norm_sub_rev]
    refine lt_of_le_of_lt (key s t h) (hδε _ ?_)
    have : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - s := NNReal.coe_sub h
    have h2 : ((t - s : ℝ≥0) : ℝ) < δ := by
      rw [this]; rw [abs_sub_comm, abs_of_nonneg (by simpa using h)] at hs; simpa using hs
    exact_mod_cast h2
  · refine lt_of_le_of_lt (key t s h) (hδε _ ?_)
    have : ((s - t : ℝ≥0) : ℝ) = (s : ℝ) - t := NNReal.coe_sub h
    have h2 : ((s - t : ℝ≥0) : ℝ) < δ := by
      rw [this]; rw [abs_of_nonneg (by simpa using h)] at hs; simpa using hs
    exact_mod_cast h2

/-- Linear combinations. -/
lemma rcfc_comb {f g k : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hk : ContinuousOn k (Icc 0 1)) (a b c : ℝ) :
    cfc (fun r => a * f r + b * g r + c * k r) R = a • cfc f R + b • cfc g R + c • cfc k R := by
  have h1 := hR.rcfc_add (f := fun r => a * f r + b * g r) (g := fun r => c * k r)
    ((continuousOn_const.mul hf).add (continuousOn_const.mul hg)) (continuousOn_const.mul hk)
  have h2 := hR.rcfc_add (f := fun r => a * f r) (g := fun r => b * g r)
    (continuousOn_const.mul hf) (continuousOn_const.mul hg)
  have h3 := hR.rcfc_smul a hf
  have h4 := hR.rcfc_smul b hg
  have h5 := hR.rcfc_smul c hk
  rw [h1, h2, h3, h4, h5]

lemma cfcSemigroup_mul_one_sub (s : ℝ≥0) :
    cfcSemigroup R s * (1 - R) = cfc (fun r => hfun s r * (1 - r)) R := by
  have hc : ContinuousOn (fun r : ℝ => 1 - r) (Icc 0 1) := by fun_prop
  have h1 : cfc (fun r : ℝ => 1 - r) R = 1 - R := by
    have := hR.rcfc_sub (f := fun _ => (1 : ℝ)) (g := id) continuousOn_const continuousOn_id
    simp only [id] at this
    rw [this, hR.rcfc_one, hR.rcfc_id']
  have h2 := hR.rcfc_mul (continuousOn_hfun s) hc
  rw [h1] at h2
  exact h2.symm

/-- The operator-norm derivative of `s ↦ T_s R` at `t > 0`. -/
theorem hasDerivAt_cfcSemigroup_mul {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => cfcSemigroup R s.toNNReal * R)
      (-(cfcSemigroup R t.toNNReal * (1 - R))) t := by
  rw [hasDerivAt_iff_isLittleO]
  have hbound : ∀ s : ℝ, |s - t| ≤ t / 2 →
      ‖cfcSemigroup R s.toNNReal * R - cfcSemigroup R t.toNNReal * R -
        (s - t) • (-(cfcSemigroup R t.toNNReal * (1 - R)))‖ ≤ 24 / t ^ 2 * (s - t) ^ 2 := by
    intro s hs
    have hf : ContinuousOn (fun r => hfunR s r * r) (Icc 0 1) :=
      (continuousOn_hfun _).mul continuousOn_id
    have hg : ContinuousOn (fun r => hfunR t r * r) (Icc 0 1) :=
      (continuousOn_hfun _).mul continuousOn_id
    have hk : ContinuousOn (fun r => (1 - r) * hfunR t r) (Icc 0 1) :=
      (by fun_prop : ContinuousOn (fun r : ℝ => 1 - r) (Icc 0 1)).mul (continuousOn_hfun _)
    have hcomb := rcfc_comb hR hf hg hk 1 (-1) (s - t)
    have e1 : cfc (fun r => hfunR s r * r) R = cfcSemigroup R s.toNNReal * R :=
      (cfcSemigroup_mul_R hR _).symm
    have e2 : cfc (fun r => hfunR t r * r) R = cfcSemigroup R t.toNNReal * R :=
      (cfcSemigroup_mul_R hR _).symm
    have e3 : cfc (fun r => (1 - r) * hfunR t r) R = cfcSemigroup R t.toNNReal * (1 - R) := by
      rw [cfcSemigroup_mul_one_sub hR]
      apply hR.rcfc_congr; intro r _; unfold hfunR; ring
    rw [e1, e2, e3] at hcomb
    have hrem : cfcSemigroup R s.toNNReal * R - cfcSemigroup R t.toNNReal * R -
        (s - t) • (-(cfcSemigroup R t.toNNReal * (1 - R))) =
        cfc (fun r => 1 * (hfunR s r * r) + (-1) * (hfunR t r * r) +
          (s - t) * ((1 - r) * hfunR t r)) R := by
      rw [hcomb]; simp only [one_smul, neg_smul, smul_neg]; abel
    rw [hrem]
    refine hR.norm_rcfc_le (by positivity) (fun r hr => ?_)
    have := scalar_remainder ht hs hr
    have e : 1 * (hfunR s r * r) + (-1) * (hfunR t r * r) + (s - t) * ((1 - r) * hfunR t r) =
        hfunR s r * r - hfunR t r * r + (s - t) * ((1 - r) * hfunR t r) := by ring
    rw [e]
    calc _ ≤ 24 * (s - t) ^ 2 / t ^ 2 := this
      _ = 24 / t ^ 2 * (s - t) ^ 2 := by ring
  have hbig : (fun s : ℝ => cfcSemigroup R s.toNNReal * R - cfcSemigroup R t.toNNReal * R -
      (s - t) • (-(cfcSemigroup R t.toNNReal * (1 - R)))) =O[𝓝 t] (fun s : ℝ => (s - t) ^ 2) := by
    apply Asymptotics.IsBigO.of_bound (24 / t ^ 2)
    have : ∀ᶠ s in 𝓝 t, |s - t| ≤ t / 2 := by
      have h1 : Tendsto (fun s : ℝ => |s - t|) (𝓝 t) (𝓝 0) := by
        have hc : Continuous fun s : ℝ => |s - t| := by fun_prop
        simpa using hc.tendsto t
      exact h1.eventually (ge_mem_nhds (by positivity))
    filter_upwards [this] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound s hs
  have hlo : (fun s : ℝ => (s - t) ^ 2) =o[𝓝 t] (fun s : ℝ => s - t) := by
    have h1 : (fun x : ℝ => x ^ 2) =o[𝓝 0] (fun x : ℝ => x) :=
      Asymptotics.isLittleO_pow_id (by norm_num)
    have h2 : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
      have hc : Continuous fun s : ℝ => s - t := by fun_prop
      simpa using hc.tendsto t
    exact h1.comp_tendsto h2
  exact hbig.trans_isLittleO hlo

/-- Derivative of the orbit of `R g`: `d/ds T_s (R g) = -T_s (g - R g)` for `s > 0`. -/
theorem hasDerivAt_cfcSemigroup_apply {t : ℝ} (ht : 0 < t) (g : H) :
    HasDerivAt (fun s : ℝ => cfcSemigroup R s.toNNReal (R g))
      (-(cfcSemigroup R t.toNNReal (g - R g))) t := by
  have h := (hasDerivAt_cfcSemigroup_mul hR ht).clm_apply (hasDerivAt_const t g)
  have e : (-(cfcSemigroup R t.toNNReal * (1 - R))) g =
      -(cfcSemigroup R t.toNNReal (g - R g)) := rfl
  have e0 : (cfcSemigroup R t.toNNReal * R) 0 = 0 := map_zero _
  rw [e, e0, add_zero] at h
  exact h

/-- `s ↦ T_s u` as a continuous function on `ℝ` (extended by `T_0 u` for `s < 0`). -/
lemma continuous_cfcSemigroup_apply_real (hinj : Function.Injective R) (u : H) :
    Continuous fun s : ℝ => cfcSemigroup R s.toNNReal u :=
  (continuous_cfcSemigroup_apply hR hinj u).comp continuous_real_toNNReal

/-- **Duhamel/Dynkin formula**: `T_t (R g) - R g = - ∫₀ᵗ T_s (g - R g) ds`. -/
theorem cfcSemigroup_integral (hinj : Function.Injective R) (g : H) (t : ℝ≥0) :
    cfcSemigroup R t (R g) - R g =
      -∫ s in (0 : ℝ)..t, cfcSemigroup R s.toNNReal (g - R g) := by
  have hcont := continuous_cfcSemigroup_apply_real hR hinj (R g)
  have hcont' := continuous_cfcSemigroup_apply_real hR hinj (g - R g)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := 0) (b := (t : ℝ))
    (f := fun s : ℝ => cfcSemigroup R s.toNNReal (R g))
    (f' := fun s : ℝ => -(cfcSemigroup R s.toNNReal (g - R g))) t.2 hcont.continuousOn
    (fun x hx => hasDerivAt_cfcSemigroup_apply hR hx.1 g) (hcont'.neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at h
  have h0 : cfcSemigroup R (0 : ℝ).toNNReal (R g) = R g := by
    simp [cfcSemigroup_zero hR]
  have ht : cfcSemigroup R (t : ℝ).toNNReal (R g) = cfcSemigroup R t (R g) := by
    rw [Real.toNNReal_coe]
  rw [h0, ht] at h
  rw [← h]

end CutoffRigidity.Riemann.Diff
