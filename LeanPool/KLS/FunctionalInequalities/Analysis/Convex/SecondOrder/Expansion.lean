/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Existence
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Taylor
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Proximal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import LeanPool.KLS.FunctionalInequalities.Analysis.Sard.Equidimensional
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Second-order differentiability of convex functions (Alexandrov's theorem)

First-order expansions of the subgradient through the resolvent of the subdifferential, integrated
second
differences, and Alexandrov's theorem that a convex function has a second-order Taylor expansion
almost everywhere
.

* `subgradient_expansion_of_hasFDerivAt_resolvent`;
* `tendsto_integral_secondDifference_mul`, `integral_mul_le_integral_mul_sum_iteratedFDeriv`;
* `ae_exists_secondOrder_expansion`.
-/

@[expose] public section

section

open Set Filter
open scoped RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma resolvent_subgradient_monotone {f : E → ℝ} {u v p q : E}
    (hp : ∀ w, f u + ⟪p, w - u⟫ ≤ f w)
    (hq : ∀ w, f v + ⟪q, w - v⟫ ≤ f w) :
    0 ≤ ⟪p - q, u - v⟫ := by
  have h₁ := hp v
  have h₂ := hq u
  have he : ⟪p, v - u⟫ + ⟪q, u - v⟫ = -⟪p - q, u - v⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  linarith

private lemma resolvent_firm_monotone {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (a b : E) :
    ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫ := by
  have h := resolvent_subgradient_monotone (hP a) (hP b)
  have he :
      ⟪(a - P a) - (b - P b), P a - P b⟫ =
        ⟪P a - P b, a - b⟫ - ‖P a - P b‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm a (P a), real_inner_comm a (P b),
      real_inner_comm b (P a), real_inner_comm b (P b)]
    ring
  rw [he] at h
  linarith

private lemma resolvent_subgradient_inverse {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y)
    {y q : E} (hq : ∀ w, f y + ⟪q, w - y⟫ ≤ f w) :
    P (y + q) = y := by
  have h := resolvent_subgradient_monotone (hP (y + q)) hq
  have he : (y + q - P (y + q)) - q = -(P (y + q) - y) := by
    abel
  rw [he, inner_neg_left, real_inner_self_eq_norm_sq] at h
  have hn : ‖P (y + q) - y‖ = 0 := by
    nlinarith [norm_nonneg (P (y + q) - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

-- A local lower bound, together with firm monotonicity, controls every preimage.
private lemma resolvent_preimage_near {P : E → E} {z : E}
    (hm : ∀ a b, ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hl : ∀ w, ‖w - z‖ < δ → c * ‖w - z‖ ≤ ‖P w - P z‖)
    (a : E) (ha : ‖P a - P z‖ < c ^ 2 * δ / 2) :
    ‖a - z‖ < δ := by
  by_contra hn
  have hN : 0 < ‖a - z‖ := lt_of_lt_of_le hδ (le_of_not_gt hn)
  let s : ℝ := δ / (2 * ‖a - z‖)
  have hs : 0 < s := div_pos hδ (by positivity)
  have hs1 : s < 1 :=
    (div_lt_one (by positivity)).2 (by linarith [le_of_not_gt hn])
  have hsN : s * ‖a - z‖ = δ / 2 := by
    dsimp [s]
    field_simp
  let w := z + s • (a - z)
  have hw : w - z = s • (a - z) := by
    dsimp [w]
    abel
  have hwn : ‖w - z‖ = s * ‖a - z‖ := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hwl : ‖w - z‖ < δ := by
    rw [hwn, hsN]
    linarith
  have hlow := hl w hwl
  have hsq :=
    (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg (w - z)))
      (norm_nonneg (P w - P z))).2 hlow
  have hm1 := hm w z
  rw [hw, real_inner_smul_right] at hm1
  have haw : a - w = (1 - s) • (a - z) := by
    dsimp [w]
    module
  have hm2 := hm a w
  rw [haw, real_inner_smul_right] at hm2
  have hip :
      ⟪P a - P w, a - z⟫ =
        ⟪P a - P z, a - z⟫ - ⟪P w - P z, a - z⟫ := by
    simp only [inner_sub_left]
    ring
  rw [hip] at hm2
  have hmon : ⟪P w - P z, a - z⟫ ≤ ⟪P a - P z, a - z⟫ := by
    nlinarith [sq_nonneg ‖P a - P w‖]
  have hupper := real_inner_le_norm (P a - P z) (a - z)
  have hb := hsq.trans
    (hm1.trans (mul_le_mul_of_nonneg_left (hmon.trans hupper) hs.le))
  rw [hwn] at hb
  have hcancel : c ^ 2 * (s * ‖a - z‖) ≤ ‖P a - P z‖ :=
    le_of_mul_le_mul_right (by nlinarith only [hb]) (mul_pos hs hN)
  rw [hsN] at hcancel
  nlinarith only [hcancel, ha]

private lemma resolvent_absorb_remainder (T : E ≃L[ℝ] E) {K c : ℝ}
    (hK : 0 < K) (hnorm : ‖(T.symm : E →L[ℝ] E)‖ ≤ K)
    (hc : K * c = 1 / 2) (d u : E)
    (hr : ‖u - T d‖ ≤ c * ‖d‖) :
    ‖d‖ ≤ 2 * K * ‖u‖ := by
  have hop := (T.symm : E →L[ℝ] E).le_opNorm (T d)
  simp only [ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] at hop
  have ht := norm_sub_norm_le (T d) u
  rw [norm_sub_rev] at ht
  have hb : ‖d‖ ≤ K * (‖u‖ + ‖u - T d‖) :=
    hop.trans
      ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg (T d))).trans
        (mul_le_mul_of_nonneg_left (by linarith only [ht]) hK.le))
  have hm := mul_le_mul_of_nonneg_left hr hK.le
  have he : K * (c * ‖d‖) = ‖d‖ / 2 := by
    rw [← mul_assoc, hc]
    ring
  rw [he] at hm
  nlinarith only [hb, hm]

/--
**Inverting the resolvent at a point of invertible differentiability** (Alexandrov's theorem):
let `P` be the resolvent of `f` (`z − P z` is a subgradient of `f` at
`P z` for every `z`). If `P` is differentiable at `z` with invertible derivative `T`, then `p₀ := z
− P z` is
the only subgradient of `f` at `x := P z`, and every subgradient `q` of `f` at `y` near `x`
satisfies
`‖q − p₀ − (T⁻¹ (y − x) − (y − x))‖ ≤ ε ‖y − x‖`. -/
theorem subgradient_expansion_of_hasFDerivAt_resolvent {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E} {T : E ≃L[ℝ] E}
    (hT : HasFDerivAt P (T : E →L[ℝ] E) z) :
    (∀ q : E, (∀ y, f (P z) + ⟪q, y - P z⟫ ≤ f y) → q = z - P z) ∧
      ∀ ε > 0,
        ∀ᶠ y in 𝓝 (P z),
          ∀ q : E,
            (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
              ‖q - (z - P z) - (T.symm (y - P z) - (y - P z))‖ ≤ ε * ‖y - P z‖ := by
  -- Adding one also covers the zero-dimensional case without a case split.
  let K : ℝ := ‖(T.symm : E →L[ℝ] E)‖ + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hnorm : ‖(T.symm : E →L[ℝ] E)‖ ≤ K := by
    dsimp [K]
    linarith
  let c : ℝ := 1 / (2 * K)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hKc : K * c = 1 / 2 := by
    dsimp [c]
    field_simp
  have hexp :
    ∀ ε > 0,
      ∀ᶠ y in 𝓝 (P z),
        ∀ q : E,
          (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
            ‖q - (z - P z) - (T.symm (y - P z) - (y - P z))‖ ≤ ε * ‖y - P z‖ := by
    intro ε hε
    let η : ℝ := min c (ε / (2 * K ^ 2))
    have hη : 0 < η := lt_min hc (by positivity)
    have hηc : η ≤ c := min_le_left _ _
    have hηε : 2 * K ^ 2 * η ≤ ε := by
      have h :=
        (le_div_iff₀ (by positivity : 0 < 2 * K ^ 2)).mp (min_le_right c (ε / (2 * K ^ 2)))
      nlinarith only [h]
    obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp (hT.isLittleO.def hη)
    have hr (w : E) (hw : ‖w - z‖ < δ) : ‖P w - P z - T (w - z)‖ ≤ η * ‖w - z‖ :=
      hd
        (by
          rw [dist_eq_norm]
          exact hw)
    have hlocal (w : E) (hw : ‖w - z‖ < δ) : ‖w - z‖ ≤ 2 * K * ‖P w - P z‖ :=
      resolvent_absorb_remainder T hK hnorm hKc (w - z) (P w - P z)
        ((hr w hw).trans (mul_le_mul_of_nonneg_right hηc (norm_nonneg _)))
    have hl (w : E) (hw : ‖w - z‖ < δ) : c * ‖w - z‖ ≤ ‖P w - P z‖ := by
      have hm := mul_le_mul_of_nonneg_left (hlocal w hw) hc.le
      have he : c * (2 * K * ‖P w - P z‖) = ‖P w - P z‖ := by
        calc
          c * (2 * K * ‖P w - P z‖) = (2 * (K * c)) * ‖P w - P z‖ := by ring
          _ = ‖P w - P z‖ := by rw [hKc]; ring
      rw [he] at hm
      exact hm
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨c ^ 2 * δ / 2, by positivity, ?_⟩
    intro y hy q hq
    rw [dist_eq_norm] at hy
    have hinv : P (y + q) = y := resolvent_subgradient_inverse hP hq
    have hnear : ‖y + q - z‖ < δ :=
      resolvent_preimage_near (resolvent_firm_monotone hP) hc hδ hl (y + q)
        (by simpa only [hinv] using hy)
    have hR : ‖y - P z - T (y + q - z)‖ ≤ η * ‖y + q - z‖ := by
      simpa only [hinv] using hr (y + q) hnear
    have hD : ‖y + q - z‖ ≤ 2 * K * ‖y - P z‖ := by simpa only [hinv] using hlocal (y + q) hnear
    have he : T.symm (y - P z - T (y + q - z)) = T.symm (y - P z) - (y + q - z) := by
      rw [map_sub, T.symm_apply_apply]
    have hA : ‖(y + q - z) - T.symm (y - P z)‖ ≤ K * ‖y - P z - T (y + q - z)‖ := by
      rw [norm_sub_rev, ← he]
      exact
        ((T.symm : E →L[ℝ] E).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have h₁ := mul_le_mul_of_nonneg_left hR hK.le
    have h₂ := mul_le_mul_of_nonneg_left hD (mul_nonneg hK.le hη.le)
    have h₃ := mul_le_mul_of_nonneg_right hηε (norm_nonneg (y - P z))
    have hfinal : ‖(y + q - z) - T.symm (y - P z)‖ ≤ ε * ‖y - P z‖ := by
      nlinarith only [hA, h₁, h₂, h₃]
    have halg :
      q - (z - P z) - (T.symm (y - P z) - (y - P z)) = (y + q - z) - T.symm (y - P z) := by abel
    rw [halg]
    exact hfinal
  refine ⟨?_, hexp⟩
  intro q hq
  have hh := (hexp 1 zero_lt_one).self_of_nhds q hq
  simp only [sub_self, map_zero, sub_zero, norm_zero, mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

end InnerProduct

end FunctionalInequalities.Analysis

section FatouSecondDifference

open MeasureTheory Set Filter
open scoped Topology

/-! Second differences against smooth tests and their limit. -/

namespace FunctionalInequalities.Analysis

private lemma secondDifference_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Tendsto (fun t : ℝ => (f t + f (-t) - 2 * f 0) / t ^ 2)
      (𝓝[>] 0) (𝓝 (iteratedDeriv 2 f 0)) := by
  have h := (taylor_isLittleO_univ (x₀ := 0) (n := 2) hf).tendsto_div_nhds_zero
  have hn := h.comp (show Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) by
    simpa using continuous_neg.tendsto (0 : ℝ))
  have H := ((h.add hn).add_const (iteratedDeriv 2 f 0)).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [zero_add] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  dsimp
  simp only [show (2 : ℕ) = 1 + 1 from rfl, taylorWithinEval_succ,
    taylor_within_zero_eval, iteratedDerivWithin_univ, sub_zero]
  norm_num
  field_simp
  ring

section StructuredSpace

variable {E : Type*}
  [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E]

private lemma directional_second_derivative {ψ : E → ℝ} (hψ : ContDiff ℝ 2 ψ) (v x : E) :
    fderiv ℝ (fun y => fderiv ℝ ψ y v) x v =
      iteratedFDeriv ℝ 2 ψ x (fun _ => v) := by
  rw [fderiv_clm_apply
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
    (differentiableAt_const v)]
  simp [iteratedFDeriv_two_apply]

private lemma second_derivative_continuous_compact {χ : E → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (v : E) :
    Continuous (fun x => iteratedFDeriv ℝ 2 χ x (fun _ => v)) ∧
      HasCompactSupport (fun x => iteratedFDeriv ℝ 2 χ x (fun _ => v)) := by
  simp only [iteratedFDeriv_two_apply]
  constructor
  · have hd := (hχ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    exact (hd.clm_apply continuous_const).clm_apply continuous_const
  · exact ((hχc.fderiv ℝ).fderiv_apply ℝ v).comp_left
      (g := fun L : E →L[ℝ] ℝ => L v) (by simp)

end NormedSpace

section InnerProduct

variable [InnerProductSpace ℝ E]

section FiniteDimensional

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma reflected_convolution_eq (u ψ : E → ℝ) (z : E) :
    convolution (fun y => u (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume z =
      ∫ x, u (x - z) * ψ x := by
  have h := integral_sub_left_eq_self
    (fun y => u (-y) * ψ (z - y)) (volume : Measure E) z
  simpa only [convolution_def, ContinuousLinearMap.mul_apply',
    neg_sub, sub_sub_cancel] using h.symm

private lemma reflected_convolution_hasDerivAt {u ψ : E → ℝ}
    (hu : Continuous u) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (v : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        convolution (fun y => u (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume (s • v))
      (convolution (fun y => u (-y)) (fun x => fderiv ℝ ψ x v)
        (ContinuousLinearMap.mul ℝ ℝ) volume (t • v)) t := by
  have hi : LocallyIntegrable (fun y => u (-y)) (volume : Measure E) :=
    (hu.comp continuous_neg).locallyIntegrable
  have h :=
    (hψc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hi hψ (t • v)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
  simp only [one_smul] at h
  exact h.congr_deriv
    (convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hi
      (hψc.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) (t • v) v)

private lemma secondDifference_integrable {u χ : E → ℝ}
    (hu : Continuous u) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (v : E) (t : ℝ) :
    Integrable
      (fun x => (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x)
      (volume : Measure E) := by
  have hcont :
      Continuous
        (fun x => (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x) :=
    ((((hu.comp (continuous_id.add continuous_const)).add
      (hu.comp (continuous_id.sub continuous_const))).sub
        (continuous_const.mul hu)).div_const (t ^ 2)).mul hχ
  exact hcont.integrable_of_hasCompactSupport hχc.mul_left

private lemma integral_secondDifference_eq {u χ : E → ℝ}
    (hu : Continuous u) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (v : E) (t : ℝ) :
    (∫ x, (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x) =
      ((∫ x, u (x + t • v) * χ x) + (∫ x, u (x - t • v) * χ x) -
        2 * (∫ x, u x * χ x)) / t ^ 2 := by
  have hpc : Continuous (fun x => u (x + t • v) * χ x) :=
    (hu.comp (continuous_id.add continuous_const)).mul hχ
  have hmc : Continuous (fun x => u (x - t • v) * χ x) :=
    (hu.comp (continuous_id.sub continuous_const)).mul hχ
  have hp : Integrable (fun x => u (x + t • v) * χ x) (volume : Measure E) :=
    hpc.integrable_of_hasCompactSupport hχc.mul_left
  have hm : Integrable (fun x => u (x - t • v) * χ x) (volume : Measure E) :=
    hmc.integrable_of_hasCompactSupport hχc.mul_left
  have hz : Integrable (fun x => u x * χ x) (volume : Measure E) :=
    (hu.mul hχ).integrable_of_hasCompactSupport hχc.mul_left
  have hsum :
      Integrable (fun x => u (x + t • v) * χ x + u (x - t • v) * χ x)
        (volume : Measure E) := hp.add hm
  have htwo : Integrable (fun x => 2 * (u x * χ x)) (volume : Measure E) :=
    hz.const_mul 2
  calc
    _ = ∫ x, ((u (x + t • v) * χ x + u (x - t • v) * χ x) -
        2 * (u x * χ x)) / t ^ 2 := by
      apply integral_congr_ae
      exact .of_forall (fun x => by ring)
    _ = _ := by
      rw [integral_div, integral_sub hsum htwo,
        integral_add hp hm, integral_const_mul]

/-- **Second difference quotients converge to the distributional second derivative**: for continuous
`u` and `χ ∈ C²` with compact support,
`∫ (u(x + t v) + u(x − t v) − 2 u(x)) / t² · χ(x) dx → ∫ u(x) ∂²_v χ(x) dx` as `t → 0⁺`. -/
theorem tendsto_integral_secondDifference_mul
    {u : E → ℝ} (hu : Continuous u) {χ : E → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (v : E) :
    Tendsto (fun t : ℝ => ∫ x, (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x)
      (𝓝[>] 0) (𝓝 (∫ x, u x * iteratedFDeriv ℝ 2 χ x (fun _ => v))) := by
  let F : ℝ → ℝ := fun t =>
    convolution (fun y => u (-y)) χ (ContinuousLinearMap.mul ℝ ℝ) volume (t • v)
  let ψ : E → ℝ := fun x => fderiv ℝ χ x v
  have hi : LocallyIntegrable (fun y => u (-y)) (volume : Measure E) :=
    (hu.comp continuous_neg).locallyIntegrable
  have hF : ContDiff ℝ 2 F :=
    (hχc.contDiff_convolution_right (n := 2)
      (ContinuousLinearMap.mul ℝ ℝ) hi hχ).comp (contDiff_id.smul contDiff_const)
  have hψ : ContDiff ℝ 1 ψ :=
    (hχ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hψc : HasCompactSupport ψ := hχc.fderiv_apply ℝ v
  have hd : deriv F = fun t =>
      convolution (fun y => u (-y)) ψ (ContinuousLinearMap.mul ℝ ℝ) volume (t • v) := by
    funext t
    exact (reflected_convolution_hasDerivAt hu (hχ.of_le (by norm_num))
      hχc v t).deriv
  have hdd : iteratedDeriv 2 F 0 =
      ∫ x, u x * iteratedFDeriv ℝ 2 χ x (fun _ => v) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd,
      (reflected_convolution_hasDerivAt hu hψ hψc v 0).deriv]
    simp only [zero_smul, convolution_def, ContinuousLinearMap.mul_apply', zero_sub]
    change (∫ x, u (-x) * fderiv ℝ (fun y => fderiv ℝ χ y v) (-x) v) = _
    simp_rw [directional_second_derivative hχ]
    exact integral_neg_eq_self
      (fun x => u x * iteratedFDeriv ℝ 2 χ x (fun _ => v)) volume
  have heq (t : ℝ) :
      (∫ x, (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x) =
        (F t + F (-t) - 2 * F 0) / t ^ 2 := by
    rw [integral_secondDifference_eq hu hχ.continuous hχc]
    dsimp only [F]
    simp only [reflected_convolution_eq, neg_smul, sub_neg_eq_add,
      zero_smul, sub_zero]
    ring
  have H := secondDifference_tendsto hF
  rw [hdd] at H
  exact H.congr' (.of_forall fun t => (heq t).symm)

end FiniteDimensional

private lemma convex_secondDifference_nonneg {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (x w : E) :
    0 ≤ u (x + w) + u (x - w) - 2 * u x := by
  have hm : (1 / 2 : ℝ) • (x + w) + (1 / 2 : ℝ) • (x - w) = x := by
    module
  have H := hconv.2 (mem_univ (x + w)) (mem_univ (x - w))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [hm] at H
  dsimp at H
  linarith

private lemma ofReal_mul_le_of_sub (a k : ℝ) (B : ENNReal)
    (h : ∀ ε > 0, ENNReal.ofReal ((a - ε) * k) ≤ B) :
    ENNReal.ofReal (a * k) ≤ B := by
  have hz : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal ((a - ε) * k))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (a * k))) := by
    simpa only [sub_zero] using
      ENNReal.tendsto_ofReal ((tendsto_const_nhds.sub hz).mul_const k)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact h ε hε

/-- **Fatou bound for the distributional second derivatives of a convex function** (input of the
distributional log-det inequality): if `g` is below the lower limit of a
nonnegative combination of second difference quotients of the convex `u` almost everywhere, then
`∫ g χ ≤ ∫ u ∑ᵢ cᵢ ∂²_{vᵢ} χ` for every nonnegative `χ ∈ C²` with compact support. -/
theorem integral_mul_le_integral_mul_sum_iteratedFDeriv [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {ι : Type*}
    [Fintype ι] (v : ι → E) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) {χ : E → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) {g : E → ℝ}
    (hgm : AEStronglyMeasurable g (volume : Measure E))
    (hg :
      ∀ᵐ x ∂(volume : Measure E),
        ∀ ε > 0,
          ∃ δ > 0,
            ∀ t : ℝ,
              0 < t →
                t < δ →
                  g x - ε ≤
                    ∑ i, c i * ((u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2)) :
    ∫ x, g x * χ x ≤ ∫ x, u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i) := by
  classical
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  let A : ℝ → ι → E → ℝ := fun t i x =>
    (u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2 * χ x
  let F : ℝ → E → ℝ := fun t x => ∑ i, c i * A t i x
  let R : ℝ := ∫ x, u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i)
  have hAi (t : ℝ) (i : ι) : Integrable (A t i) (volume : Measure E) :=
    secondDifference_integrable hu hχ.continuous hχc (v i) t
  have hFi (t : ℝ) : Integrable (F t) (volume : Measure E) :=
    integrable_finsetSum Finset.univ fun i _ => (hAi t i).const_mul (c i)
  have hF0 (t : ℝ) (x : E) : 0 ≤ F t x := by
    apply Finset.sum_nonneg
    intro i _
    exact
      mul_nonneg (hc i)
        (mul_nonneg
          (div_nonneg (convex_secondDifference_nonneg hconv x (t • v i)) (sq_nonneg t)) (hχ0 x))
  have hDi (i : ι) :
    Integrable (fun x => u x * iteratedFDeriv ℝ 2 χ x (fun _ => v i)) (volume : Measure E) := by
    obtain ⟨hdc, hds⟩ := second_derivative_continuous_compact hχ hχc (v i)
    exact (hu.mul hdc).integrable_of_hasCompactSupport hds.mul_left
  have hR : R = ∑ i, c i * (∫ x, u x * iteratedFDeriv ℝ 2 χ x (fun _ => v i)) := by
    have heq :
      (fun x => u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i)) =
        (fun x => ∑ i, c i * (u x * iteratedFDeriv ℝ 2 χ x (fun _ => v i))) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    dsimp only [R]
    rw [heq, integral_finsetSum Finset.univ (fun i _ => (hDi i).const_mul (c i))]
    simp_rw [integral_const_mul]
  have hI (t : ℝ) : (∫ x, F t x) = ∑ i, c i * (∫ x, A t i x) := by
    dsimp only [F]
    rw [integral_finsetSum Finset.univ (fun i _ => (hAi t i).const_mul (c i))]
    simp_rw [integral_const_mul]
  have hlim : Tendsto (fun t : ℝ => ∫ x, F t x) (𝓝[>] 0) (𝓝 R) := by
    rw [hR]
    have H :=
      tendsto_finsetSum Finset.univ
        (fun i _ => (tendsto_integral_secondDifference_mul hu hχ hχc (v i)).const_mul (c i))
    exact H.congr' (.of_forall fun t => (hI t).symm)
  have hR0 : 0 ≤ R :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (.of_forall fun t => integral_nonneg (hF0 t))
  by_cases hgi : Integrable (fun x => g x * χ x) (volume : Measure E)
  · have hgi' : Integrable (fun x => g x * χ x) (volume : Measure E) :=
      ⟨hgm.mul hχ.continuous.aestronglyMeasurable, hgi.2⟩
    have hpoint :
      ∀ᵐ x ∂(volume : Measure E),
        ENNReal.ofReal (g x * χ x) ≤ liminf (fun t : ℝ => ENNReal.ofReal (F t x)) (𝓝[>] 0) := by
      filter_upwards [hg] with x hx
      apply ofReal_mul_le_of_sub
      intro ε hε
      obtain ⟨δ, hδ, hbound⟩ := hx ε hε
      have hev :
        ∀ᶠ t : ℝ in 𝓝[>] 0, ENNReal.ofReal ((g x - ε) * χ x) ≤ ENNReal.ofReal (F t x) := by
        have hδevent : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 δ :=
          (nhdsGT_basis (0 : ℝ)).mem_iff.mpr ⟨δ, hδ, subset_rfl⟩
        filter_upwards [hδevent] with t ht
        apply ENNReal.ofReal_le_ofReal
        calc
          (g x - ε) * χ x ≤
              (∑ i, c i * ((u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2)) * χ x :=
            mul_le_mul_of_nonneg_right (hbound t ht.1 ht.2) (hχ0 x)
          _ = F t x := by
            dsimp only [F, A]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
      exact le_liminf_of_le (h := hev)
    have hL :
      Tendsto (fun t : ℝ => ∫⁻ x, ENNReal.ofReal (F t x)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal R)) := by
      exact
        (ENNReal.tendsto_ofReal hlim).congr'
          (.of_forall fun t => ofReal_integral_eq_lintegral_ofReal (hFi t) (.of_forall (hF0 t)))
    have hfatou : (∫⁻ x, ENNReal.ofReal (g x * χ x)) ≤ ENNReal.ofReal R := by
      calc
        _ ≤ ∫⁻ x, liminf (fun t : ℝ => ENNReal.ofReal (F t x)) (𝓝[>] 0) :=
          lintegral_mono_ae hpoint
        _ ≤ liminf (fun t : ℝ => ∫⁻ x, ENNReal.ofReal (F t x)) (𝓝[>] 0) :=
          lintegral_liminf_le'
            (fun t =>
              ENNReal.continuous_ofReal.measurable.comp_aemeasurable
                (hFi t).aestronglyMeasurable.aemeasurable)
        _ = ENNReal.ofReal R := hL.liminf_eq
    have hp : ENNReal.ofReal (∫ x, max (g x * χ x) 0) ≤ ENNReal.ofReal R := by
      calc
        _ = ∫⁻ x, ENNReal.ofReal (g x * χ x) := by
          rw [ofReal_integral_eq_lintegral_ofReal hgi'.pos_part
              (.of_forall fun x => le_max_right (g x * χ x) 0)]
          apply lintegral_congr
          intro x
          simp
        _ ≤ ENNReal.ofReal R := hfatou
    exact
      (integral_mono hgi' hgi'.pos_part (fun x => le_max_left (g x * χ x) 0)).trans
        ((ENNReal.ofReal_le_ofReal_iff hR0).mp hp)
  · rw [integral_undef hgi]
    exact hR0

end InnerProduct

end StructuredSpace

end FunctionalInequalities.Analysis

end FatouSecondDifference

section AlexandrovTheorem

open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology

/-! **Alexandrov's theorem**: a convex function on a finite-dimensional space has a second-order
Taylor expansion at almost every point. -/

namespace FunctionalInequalities.Analysis

/-- **Alexandrov expansion with retained subgradient expansion**.

This is the shared producer for the value expansion and the first-order expansion of all
subgradients, with the same symmetric operator `B`. -/
theorem ae_exists_subgradient_secondOrder_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂(volume : Measure E), ∃ p : E, ∃ B : E →L[ℝ] E,
      (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
      (∀ q : E, (∀ y, f x + ⟪q, y - x⟫ ≤ f y) → q = p) ∧
      (∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ q : E,
        (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
          ‖q - p - B (y - x)‖ ≤ ε * ‖y - x‖) ∧
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |f y - f x - ⟪p, y - x⟫ -
            (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
  classical
  let P : E → E := proximalPoint f
  have hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y :=
    proximalPoint_spec hconv
  have hLip : LipschitzWith 1 P := lipschitzWith_proximalPoint hconv
  let N₁ : Set E := {z | ¬ DifferentiableAt ℝ P z}
  let N₂ : Set E :=
    {z | DifferentiableAt ℝ P z ∧ (fderiv ℝ P z).det = 0}
  have hN₁ : (volume : Measure E) N₁ = 0 :=
    ae_iff.mp (hLip.ae_differentiableAt (μ := (volume : Measure E)))
  have hImage₁ : (volume : Measure E) (P '' N₁) = 0 :=
    volume_image_eq_zero_of_lipschitzOnWith hLip.lipschitzOnWith hN₁
  have hImage₂ : (volume : Measure E) (P '' N₂) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (volume : Measure E) (f' := fun z => fderiv ℝ P z)
    · intro z hz
      exact hz.1.hasFDerivAt.hasFDerivWithinAt
    · intro z hz
      exact hz.2
  let Bad : Set E := P '' N₁ ∪ P '' N₂
  have hBad : (volume : Measure E) Bad = 0 :=
    measure_union_null hImage₁ hImage₂
  have hGood : ∀ᵐ x ∂(volume : Measure E), x ∉ Bad := by
    rw [ae_iff]
    exact measure_mono_null (fun a ha => not_not.mp ha) hBad
  filter_upwards [hGood] with x hx
  have hx₁ : x ∉ P '' N₁ := fun h => hx (Or.inl h)
  have hx₂ : x ∉ P '' N₂ := fun h => hx (Or.inr h)
  obtain ⟨p₁, hp₁, _⟩ := exists_subgradient_slope_le_inner_add hconv x 0
  let z : E := x + p₁
  have hzsub : z - x = p₁ := by
    simp only [z, add_sub_cancel_left]
  have hPz : P z = x := by
    apply proximalPoint_eq_of_subgradient hconv
    simpa only [hzsub] using hp₁
  have hDiff : DifferentiableAt ℝ P z := by
    by_contra h
    exact hx₁ ⟨z, h, hPz⟩
  have hDet : (fderiv ℝ P z).det ≠ 0 := by
    intro h
    exact hx₂ ⟨z, ⟨hDiff, h⟩, hPz⟩
  let T : E ≃L[ℝ] E :=
    (LinearMap.equivOfDetNeZero (fderiv ℝ P z : E →ₗ[ℝ] E) hDet).toContinuousLinearEquiv
  have hTcoe : (T : E →L[ℝ] E) = fderiv ℝ P z := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have hT : HasFDerivAt P (T : E →L[ℝ] E) z := by
    rw [hTcoe]
    exact hDiff.hasFDerivAt
  have hInvSymm : ∀ v w, ⟪T.symm v, w⟫ = ⟪v, T.symm w⟫ := by
    intro v w
    have h :=
      (inner_hasFDerivAt_resolvent_symm hP hT
        (T.symm v) (T.symm w)).1
    change ⟪T (T.symm v), T.symm w⟫ =
      ⟪T.symm v, T (T.symm w)⟫ at h
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm
  let B : E →L[ℝ] E :=
    (T.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E
  have hBsymm : ∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫ := by
    intro v w
    change ⟪T.symm v - v, w⟫ = ⟪v, T.symm w - w⟫
    rw [inner_sub_left, inner_sub_right, hInvSymm v w]
  have hExpansion :=
    subgradient_expansion_of_hasFDerivAt_resolvent hP hT
  rw [hPz] at hExpansion
  have hTaylor :
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |f y - f x - ⟪z - x, y - x⟫ -
            (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
    apply eventually_abs_sub_quadratic_le_of_subgradient_expansion hconv
    intro ε hε
    filter_upwards [hExpansion.2 ε hε] with y hy
    intro q hq
    change
      ‖q - (z - x) - (T.symm (y - x) - (y - x))‖ ≤
        ε * ‖y - x‖
    exact hy q hq
  exact ⟨z - x, B, hBsymm, hExpansion.1, hExpansion.2, hTaylor⟩

/--
**Alexandrov's theorem** (A. D. Alexandrov 1939; Evans–Gariepy, *Measure theory and fine properties
of
functions*, Thm 6.9): a convex function on a finite-dimensional real inner
product space has, at almost every point, a unique subgradient `p` and a second-order expansion
`f y = f x + ⟪p, y − x⟫ + ½ ⟪B (y − x), y − x⟫ + o(‖y − x‖²)` with a symmetric `B`. -/
theorem ae_exists_secondOrder_expansion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂(volume : Measure E),
      ∃ p : E,
        ∃ B : E →L[ℝ] E,
          (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
            (∀ q : E, (∀ y, f x + ⟪q, y - x⟫ ≤ f y) → q = p) ∧
              ∀ ε > 0,
                ∀ᶠ y in 𝓝 x,
                  |f y - f x - ⟪p, y - x⟫ - (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_subgradient_secondOrder_expansion hconv] with x hx
  rcases hx with ⟨p, B, hBsymm, huniq, _hfirst, hTaylor⟩
  exact ⟨p, B, hBsymm, huniq, hTaylor⟩

/-- **Almost-everywhere differentiability of the gradient with the Alexandrov expansion**.

For a globally finite convex function differentiable only on an open domain, the derivative
of `gradient u` and the quadratic Taylor expansion use the SAME symmetric operator a.e. there.
No global differentiability, smooth extension, C11 or W2p is an input. -/
theorem ae_exists_gradient_secondOrder_expansion_on_open
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} (hconv : ConvexOn ℝ Set.univ u) {Omega : Set E}
    (hOmega : IsOpen Omega) (hdiff : DifferentiableOn ℝ u Omega) :
    ∀ᵐ x ∂(volume : Measure E).restrict Omega, ∃ B : E →L[ℝ] E,
      (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
      HasFDerivAt (gradient u) B x ∧
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |u y - u x - ⟪gradient u x, y - x⟫ -
            (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
  have hgradsub (y : E) (hy : y ∈ Omega) :
      ∀ w, u y + ⟪gradient u y, w - y⟫ ≤ u w := by
    intro w
    have hdy : DifferentiableAt ℝ u y :=
      (hdiff y hy).differentiableAt (hOmega.mem_nhds hy)
    have h :=
      gradient_le_increment hconv y (w - y) hdy
    have harg : y + (w - y) = w := by
      abel
    rw [harg] at h
    linarith
  have hsub :=
    ae_exists_subgradient_secondOrder_expansion (E := E) hconv
  have hsub' :=
    ae_restrict_of_ae (s := Omega) hsub
  have hmem :
      ∀ᵐ x ∂(volume : Measure E).restrict Omega, x ∈ Omega :=
    ae_restrict_mem hOmega.measurableSet
  filter_upwards [hsub', hmem] with x hx hxOmega
  rcases hx with ⟨p, B, hBsymm, huniq, hfirst, hTaylor⟩
  have hpx : p = gradient u x :=
    (huniq (gradient u x) (hgradsub x hxOmega)).symm
  have hfirstGrad (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ y in 𝓝 x,
        ‖gradient u y - gradient u x - B (y - x)‖ ≤
          ε * ‖y - x‖ := by
    filter_upwards [hfirst ε hε, hOmega.mem_nhds hxOmega] with y hy hyOmega
    have hy' := hy (gradient u y) (hgradsub y hyOmega)
    simpa only [hpx] using hy'
  have hlittle :
      (fun h : E =>
        gradient u (x + h) - gradient u x - B h) =o[𝓝 (0 : E)]
          (fun h : E => h) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have ht :
        Tendsto (fun h : E => x + h) (𝓝 (0 : E)) (𝓝 x) := by
      simpa only [id_eq, add_zero] using
        (tendsto_const_nhds.add
          (tendsto_id :
            Tendsto id (𝓝 (0 : E)) (𝓝 (0 : E))))
    have hev := ht.eventually (hfirstGrad ε hε)
    filter_upwards [hev] with h hh
    simpa only [add_sub_cancel_left] using hh
  have hgrad :
      HasFDerivAt (gradient u) B x := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simpa only using hlittle
  have hTaylor' :
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |u y - u x - ⟪gradient u x, y - x⟫ -
            (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
    simpa only [hpx] using hTaylor
  exact ⟨B, hBsymm, hgrad, hTaylor'⟩


/-- The global differentiable theorem is the actual univ specialization of the
local gradient/second-order producer, retaining the same symmetric operator. -/
theorem ae_exists_gradient_secondOrder_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (hdiff : Differentiable ℝ u) :
    ∀ᵐ x ∂(volume : Measure E), ∃ B : E →L[ℝ] E,
      (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
      HasFDerivAt (gradient u) B x ∧
      ∀ ε > 0, ∀ᶠ y in 𝓝 x,
        |u y - u x - ⟪gradient u x, y - x⟫ -
            (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
  simpa only [Measure.restrict_univ] using
    ae_exists_gradient_secondOrder_expansion_on_open hconv isOpen_univ hdiff.differentiableOn


end FunctionalInequalities.Analysis

end AlexandrovTheorem
