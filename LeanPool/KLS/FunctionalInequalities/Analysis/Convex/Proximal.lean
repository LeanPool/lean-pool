/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Existence
public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Subgradient.Regularity

/-!
# Proximal points, Moreau derivatives and resolvent symmetry

Actual positive-parameter Moreau values now generate global convex C1 functions
with Lipschitz gradients and attained quadratic minima. The scaled source uses
the existing proximal point directly. Generic quadratic bounds are shared with
the original dimension-free resolvent derivative proof. This supports the
local MA route of Letwin2607.24164v1 Lemma2.2 / BB1207.6128v1 Thm2.24(ii);
no MA equation, reference existence or regularity of the unknown source is assumed.
-/

@[expose] public section

noncomputable section
open Set
open scoped RealInnerProductSpace

section ProximalPoint

open Set
open scoped RealInnerProductSpace

/-! The proximal point of a convex function and its Lipschitz dependence. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem proximal_subgradient_monotonicity
    {f : E → ℝ} {x x' z w : E}
    (hx : ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y)
    (hx' : ∀ y, f x' + ⟪w - x', y - x'⟫ ≤ f y) :
    ‖x - x'‖ ^ 2 ≤ ⟪x - x', z - w⟫ := by
  have h₁ : f x - ⟪z - x, x - x'⟫ ≤ f x' := by
    simpa only [← neg_sub x x', inner_neg_right, sub_eq_add_neg] using hx x'
  have h₂ := hx' x
  have hm : 0 ≤ ⟪(z - x) - (w - x'), x - x'⟫ := by
    rw [inner_sub_left]
    linarith
  have he : (z - x) - (w - x') = (z - w) - (x - x') := by
    abel
  rw [he, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hc := real_inner_comm (x - x') (z - w)
  linarith

private theorem exists_proximal_minimizer
    [FiniteDimensional ℝ E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) (z : E) :
    ∃ x, ∀ y,
      f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤
        f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2 := by
  let φ : E → ℝ := fun x => f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2
  have hf : Continuous f :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hφ : Continuous φ :=
    hf.add (((continuous_id.sub continuous_const).norm.pow 2).const_mul (1 / 2 : ℝ))
  obtain ⟨g, hg, _⟩ := exists_subgradient_slope_le_inner_add hconv z (0 : E)
  let R : ℝ := 2 * ‖g‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  obtain ⟨x, _, hx⟩ :=
    (isCompact_closedBall z R).exists_isMinOn
      ⟨z, Metric.mem_closedBall_self hR⟩ hφ.continuousOn
  refine ⟨x, ?_⟩
  intro y
  by_cases hy : y ∈ Metric.closedBall z R
  · exact (isMinOn_iff.mp hx) y hy
  · have hr : 2 * ‖g‖ + 1 < ‖y - z‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, not_le, R] using hy
    have hr0 : 0 < ‖y - z‖ := by
      linarith [norm_nonneg g]
    have hprod :=
      mul_pos hr0 (show 0 < ‖y - z‖ - 2 * ‖g‖ by linarith)
    have hi := neg_le_of_abs_le (abs_real_inner_le_norm g (y - z))
    have ha := hg y
    have hxz := (isMinOn_iff.mp hx) z (Metric.mem_closedBall_self hR)
    dsimp [φ] at hxz ⊢
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] at hxz
    nlinarith

private theorem subgradient_of_proximal_minimizer
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) {x z : E}
    (hx : ∀ y,
      f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤
        f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2) :
    ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y := by
  intro y
  have ht : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2 := by
    intro t ht ht1
    have he : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    have hf := hconv.2 (mem_univ x) (mem_univ y)
      (sub_nonneg.mpr ht1) ht.le (show 1 - t + t = 1 by ring)
    rw [he] at hf
    simp only [smul_eq_mul] at hf
    have hm := hx (x + t • (y - x))
    have he' : x + t • (y - x) - z = (x - z) + t • (y - x) := by
      abel
    rw [he', norm_add_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht] at hm
    have hmul :
        0 ≤ t * (f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right hmul ht
  have hcont : Continuous
      (fun t : ℝ => f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2) :=
    continuous_const.add ((continuous_id.div_const 2).mul continuous_const)
  have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      0 ≤ f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2 := by
    have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 < t :=
      self_mem_nhdsWithin
    have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
    exact (hpos.and hsmall).mono (fun t h => ht t h.1 h.2.le)
  have hlim : 0 ≤ f y - f x + ⟪x - z, y - x⟫ := by
    simpa only [zero_div, zero_mul, add_zero] using
      ge_of_tendsto ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds) hev
  have hi : ⟪z - x, y - x⟫ = -⟪x - z, y - x⟫ := by
    rw [← neg_sub x z, inner_neg_left]
  rw [hi]
  linarith

/--
The **proximal point** (resolvent of the subdifferential) of `f` at `z`: a point `x` such that
`z − x` is a subgradient of `f` at `x`, i.e. the minimiser of `x ↦ f x + ½‖x − z‖²` (Alexandrov's
theorem). For convex `f` on a finite-dimensional space it exists and is unique. -/
def proximalPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → ℝ)
    (z : E) : E :=
  Classical.epsilon fun x => ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- `z − proximalPoint f z` is a subgradient of the convex `f` at `proximalPoint f z`. -/
theorem proximalPoint_spec {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (z : E) :
    ∀ y, f (proximalPoint f z) + ⟪z - proximalPoint f z, y - proximalPoint f z⟫ ≤ f y := by
  obtain ⟨x, hx⟩ := exists_proximal_minimizer hconv z
  exact Classical.epsilon_spec
    (p := fun x : E => ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y)
    ⟨x, subgradient_of_proximal_minimizer hconv hx⟩

/-- Uniqueness: if `z − x` is a subgradient of `f` at `x`, then `x` is the proximal point of `z`. -/
theorem proximalPoint_eq_of_subgradient {f : E → ℝ} (hconv : ConvexOn ℝ univ f) {x z : E}
    (hx : ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y) : proximalPoint f z = x := by
  have h := proximal_subgradient_monotonicity (proximalPoint_spec hconv z) hx
  simp only [sub_self, inner_zero_right] at h
  have hn : ‖proximalPoint f z - x‖ = 0 := by
    nlinarith [norm_nonneg (proximalPoint f z - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Firm nonexpansiveness of the proximal map. -/
theorem sq_norm_proximalPoint_sub_le_inner {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (z w : E) :
    ‖proximalPoint f z - proximalPoint f w‖ ^ 2 ≤
      ⟪proximalPoint f z - proximalPoint f w, z - w⟫ := by
  exact proximal_subgradient_monotonicity
    (proximalPoint_spec hconv z) (proximalPoint_spec hconv w)

/-- The proximal map is `1`-Lipschitz. -/
theorem lipschitzWith_proximalPoint {f : E → ℝ} (hconv : ConvexOn ℝ univ f) :
    LipschitzWith 1 (proximalPoint f) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h := sq_norm_proximalPoint_sub_le_inner hconv z w
  have hi := real_inner_le_norm (proximalPoint f z - proximalPoint f w) (z - w)
  have hb : ‖proximalPoint f z - proximalPoint f w‖ ^ 2 ≤
      ‖proximalPoint f z - proximalPoint f w‖ * ‖z - w‖ :=
    h.trans hi
  by_contra hn
  have hlt : ‖z - w‖ < ‖proximalPoint f z - proximalPoint f w‖ :=
    lt_of_not_ge hn
  have hp : 0 < ‖proximalPoint f z - proximalPoint f w‖ :=
    lt_of_le_of_lt (norm_nonneg _) hlt
  have hm := mul_pos hp (sub_pos.mpr hlt)
  nlinarith

end FiniteDimensional

end InnerProduct

end FunctionalInequalities.Analysis

end ProximalPoint

section MoreauSymmetricDerivative

open Set Filter
open scoped RealInnerProductSpace Topology

/-! Derivative of `½‖x‖² − (Moreau envelope)` and symmetry of the derivative of the resolvent. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Moreau envelope evaluated at the proximal point of the scaled function. -/
def moreauEnvelope (f : E → ℝ) (ε : ℝ) (x : E) : ℝ :=
  ε⁻¹ *
    (ε * f ((proximalPoint (fun z => ε * f z)) x) +
      (1 / 2 : ℝ) * ‖(proximalPoint (fun z => ε * f z)) x - x‖ ^ 2)

/-- Actual quadratic minimum and dual-value bounds, shared by the old
resolvent derivative and the scaled Moreau source. No dimension or completeness. -/
private lemma proximal_quadratic_bounds {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (z : E) :
    let g : E → ℝ := fun w => (1 / 2 : ℝ) * ‖w‖ ^ 2 - (f (P w) + (1 / 2 : ℝ) * ‖P w - w‖ ^ 2)
    (∀ y, f (P z) + (1 / 2 : ℝ) * ‖P z - z‖ ^ 2 ≤ f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2) ∧
      (∀ w,
        0 ≤ g w - g z - ⟪P z, w - z⟫ ∧ g w - g z - ⟪P z, w - z⟫ ≤ (1 / 2 : ℝ) * ‖w - z‖ ^ 2) := by
  let g : E → ℝ := fun w => (1 / 2 : ℝ) * ‖w‖ ^ 2 - (f (P w) + (1 / 2 : ℝ) * ‖P w - w‖ ^ 2)
  refine ⟨?_, ?_⟩
  · intro y
    have hp := hP z y
    have hs := sq_nonneg ‖y - P z‖
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right] at hp hs ⊢
    simp only [real_inner_comm] at hp hs ⊢
    linarith only [hp, hs]
  · intro w
    change 0 ≤ g w - g z - ⟪P z, w - z⟫ ∧ g w - g z - ⟪P z, w - z⟫ ≤ (1 / 2 : ℝ) * ‖w - z‖ ^ 2
    have hpw := hP w (P z)
    have hpz := hP z (P w)
    have hsq := sq_nonneg ‖(w - z) - (P w - P z)‖
    have hsq' := sq_nonneg ‖P w - P z‖
    dsimp only [g]
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left,
      inner_sub_right] at hpw hpz hsq hsq' ⊢
    simp only [real_inner_comm] at hpw hpz hsq hsq' ⊢
    constructor
    · linarith only [hpw, hsq']
    · linarith only [hpz, hsq]

/--
**The resolvent of a convex function is a gradient** (Alexandrov's theorem): if `P z` is a point
at which `z − P z` is a subgradient of the convex `f` (the proximal map), then
`w ↦ ½‖w‖² − (f (P w) + ½‖P w − w‖²)` (½‖·‖² minus the Moreau envelope) has derivative `⟪P z, ·⟫` at
every `z`. -/
theorem hasFDerivAt_half_sq_sub_moreau {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (z : E) :
    HasFDerivAt (fun w => (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2))
      (innerSL ℝ (P z)) z := by
  let g : E → ℝ := fun w => (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2)
  have hbound (w : E) :
    0 ≤ g w - g z - ⟪P z, w - z⟫ ∧ g w - g z - ⟪P z, w - z⟫ ≤ (1 / 2) * ‖w - z‖ ^ 2 := by
    exact (proximal_quadratic_bounds hP z).2 w
  change HasFDerivAt g (innerSL ℝ (P z)) z
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hn : ContinuousAt (fun w : E => ‖w - z‖) z :=
    (continuousAt_id.sub continuousAt_const).norm
  have he : ∀ᶠ w in 𝓝 z, ‖w - z‖ < c :=
    hn.eventually_lt continuousAt_const (by simpa only [sub_self, norm_zero] using hc)
  filter_upwards [he] with w hw
  change ‖g w - g z - ⟪P z, w - z⟫‖ ≤ c * ‖w - z‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hbound w).1]
  calc
    g w - g z - ⟪P z, w - z⟫ ≤ (1 / 2) * ‖w - z‖ ^ 2 := (hbound w).2
    _ ≤ c * ‖w - z‖ := by
      have hm := mul_le_mul_of_nonneg_right hw.le (norm_nonneg (w - z))
      nlinarith only [hm, sq_nonneg ‖w - z‖]

/-- **The derivative of the resolvent is symmetric and firmly nonexpansive**: at a point
where the proximal map `P` is differentiable with derivative `T`, `⟪T v, w⟫ = ⟪v, T w⟫` and
`‖T v‖² ≤ ⟪T v, v⟫`. -/
theorem inner_hasFDerivAt_resolvent_symm
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E}
    {T : E →L[ℝ] E} (hT : HasFDerivAt P T z) (v w : E) :
    ⟪T v, w⟫ = ⟪v, T w⟫ ∧ ‖T v‖ ^ 2 ≤ ⟪T v, v⟫ := by
  constructor
  · have hs := second_derivative_symmetric
      (fun y => hasFDerivAt_half_sq_sub_moreau hP y)
      ((innerSL ℝ : E →L[ℝ] (E →L[ℝ] ℝ)).hasFDerivAt.comp z hT) v w
    change ⟪T v, w⟫ = ⟪T w, v⟫ at hs
    exact hs.trans (real_inner_comm (T w) v).symm
  · have hfirm (a b : E) :
        ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫ := by
      have hab := hP a (P b)
      have hba := hP b (P a)
      simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
        at hab hba ⊢
      simp only [real_inner_comm] at hab hba ⊢
      linarith only [hab, hba]
    have hline : HasDerivAt (fun t : ℝ => P (z + t • v)) (T v) 0 := by
      have hp : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
        simpa only [id_eq, one_smul] using
          ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
      have ht : HasFDerivAt P T (z + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using hT
      exact ht.comp_hasDerivAt 0 hp
    have hlim :
        Tendsto (fun t : ℝ => t⁻¹ • (P (z + t • v) - P z))
          (𝓝[≠] 0) (𝓝 (T v)) := by
      simpa only [zero_add, zero_smul, add_zero] using hline.tendsto_slope_zero
    have hquot (t : ℝ) :
        ‖t⁻¹ • (P (z + t • v) - P z)‖ ^ 2 ≤
          ⟪t⁻¹ • (P (z + t • v) - P z), v⟫ := by
      by_cases ht : t = 0
      · simp [ht]
      · have hp := hfirm (z + t • v) z
        simp only [add_sub_cancel_left, real_inner_smul_right] at hp
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_left]
        calc
          (t⁻¹) ^ 2 * ‖P (z + t • v) - P z‖ ^ 2 ≤
              (t⁻¹) ^ 2 * (t * ⟪P (z + t • v) - P z, v⟫) :=
            mul_le_mul_of_nonneg_left hp (sq_nonneg t⁻¹)
          _ = t⁻¹ * ⟪P (z + t • v) - P z, v⟫ := by
            field_simp [ht]
    exact le_of_tendsto_of_tendsto (hlim.norm.pow 2)
      (hlim.inner tendsto_const_nhds) (Filter.Eventually.of_forall hquot)

section MoreauRegularization
variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private lemma moreau_scaled_convex {f : E → ℝ} (hf : ConvexOn ℝ univ f) {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ univ (fun y => ε * f y) := by
  simpa only [smul_eq_mul] using ConvexOn.smul hε.le hf

private lemma moreau_support (f : E → ℝ) (hf : ConvexOn ℝ univ f) {ε : ℝ} (hε : 0 < ε)
    (x y : E) :
    moreauEnvelope f ε x + ⟪ε⁻¹ • (x - (proximalPoint (fun z => ε * f z)) x), y - x⟫ ≤
      moreauEnvelope f ε y := by
  have hb :=
    ((proximal_quadratic_bounds (proximalPoint_spec (moreau_scaled_convex hf hε)) x).2 y).2
  have he (z : E) :
    ε * moreauEnvelope f ε z =
      ε * f ((proximalPoint (fun z => ε * f z)) z) +
        (1 / 2 : ℝ) * ‖(proximalPoint (fun z => ε * f z)) z - z‖ ^ 2 := by
    dsimp [moreauEnvelope]
    rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
  apply (mul_le_mul_iff_right₀ hε).mp
  rw [mul_add, he, he]
  have hi :
    ε * ⟪ε⁻¹ • (x - (proximalPoint (fun z => ε * f z)) x), y - x⟫ =
      ⟪x - (proximalPoint (fun z => ε * f z)) x, y - x⟫ := by
    rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
  rw [hi]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right] at hb ⊢
  simp only [real_inner_comm] at hb ⊢
  linarith only [hb]

private lemma moreau_convex (f : E → ℝ) (hf : ConvexOn ℝ univ f) {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ univ (moreauEnvelope f ε) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  let g := ε⁻¹ • (z - (proximalPoint (fun z => ε * f z)) z)
  have hx := moreau_support f hf hε z x
  have hy := moreau_support f hf hε z y
  have hvec : a • (x - z) + b • (y - z) = 0 := by
    calc
      _ = a • x + b • y - (a + b) • z := by rw [add_smul, smul_sub, smul_sub]; abel
      _ = 0 := by rw [hab, one_smul]; dsimp [z]; abel
  have hi := congrArg (fun w => ⟪g, w⟫) hvec
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at hi
  have hax := mul_le_mul_of_nonneg_left hx ha
  have hby := mul_le_mul_of_nonneg_left hy hb
  change moreauEnvelope f ε z ≤ a * moreauEnvelope f ε x + b * moreauEnvelope f ε y
  change
    a * ⟪ε⁻¹ • (z - (proximalPoint (fun z => ε * f z)) z), x - z⟫ +
        b * ⟪ε⁻¹ • (z - (proximalPoint (fun z => ε * f z)) z), y - z⟫ =
      0 at hi
  have he : (a + b) * moreauEnvelope f ε z = moreauEnvelope f ε z := by rw [hab, one_mul]
  nlinarith only [hax, hby, hi, he]

private lemma moreau_derivative (f : E → ℝ) (hf : ConvexOn ℝ univ f) {ε : ℝ} (hε : 0 < ε)
    (x : E) :
    HasFDerivAt (moreauEnvelope f ε)
      (innerSL ℝ (ε⁻¹ • (x - (proximalPoint (fun z => ε * f z)) x))) x := by
  have hhalf : HasFDerivAt (fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2) (innerSL ℝ x) x := by
    convert! ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ)) using 1
    ext y
    simp
  have hd := hasFDerivAt_half_sq_sub_moreau (proximalPoint_spec (moreau_scaled_convex hf hε)) x
  have h := (hhalf.sub hd).const_mul ε⁻¹
  convert! h using 1
  · funext y
    dsimp [moreauEnvelope]
    ring
  · ext y
    simp

/-- Actual positive-parameter Moreau regularity: no C1 or gradient supplied. -/
theorem moreauEnvelope_regularization (f : E → ℝ) (hf : ConvexOn ℝ univ f) {ε : ℝ}
    (hε : 0 < ε) :
    ConvexOn ℝ univ (moreauEnvelope f ε) ∧
      ContDiff ℝ 1 (moreauEnvelope f ε) ∧
        (∀ x,
            gradient (moreauEnvelope f ε) x =
              ε⁻¹ • (x - (proximalPoint (fun z => ε * f z)) x)) ∧
          LipschitzWith (‖(ε⁻¹ : ℝ)‖₊ * 2) (gradient (moreauEnvelope f ε)) := by
  have hcv := moreau_convex f hf hε
  have hd := moreau_derivative f hf hε
  have hg (x : E) :
    gradient (moreauEnvelope f ε) x = ε⁻¹ • (x - (proximalPoint (fun z => ε * f z)) x) :=
    (subgradient_eq_gradient (hd x).differentiableAt (moreau_support f hf hε x)).symm
  refine
    ⟨hcv, contDiff_one_of_convexOn_of_differentiable hcv (fun x => (hd x).differentiableAt), hg,
      ?_⟩
  have hp : LipschitzWith 1 ((proximalPoint (fun z => ε * f z))) :=
    lipschitzWith_proximalPoint (moreau_scaled_convex hf hε)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hpn :
    ‖(proximalPoint (fun z => ε * f z)) x - (proximalPoint (fun z => ε * f z)) y‖ ≤ ‖x - y‖ := by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using hp.dist_le_mul x y
  have hr :
    ‖(x - (proximalPoint (fun z => ε * f z)) x) - (y - (proximalPoint (fun z => ε * f z)) y)‖ ≤
      2 * ‖x - y‖ := by
    rw [show
        (x - (proximalPoint (fun z => ε * f z)) x) -
            (y - (proximalPoint (fun z => ε * f z)) y) =
          (x - y) -
            ((proximalPoint (fun z => ε * f z)) x - (proximalPoint (fun z => ε * f z)) y)
        by abel]
    have hn :=
      norm_sub_le (x - y)
        ((proximalPoint (fun z => ε * f z)) x - (proximalPoint (fun z => ε * f z)) y)
    linarith
  simp only [hg, dist_eq_norm, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnNorm,
    NNReal.coe_ofNat]
  calc
    _ ≤ ‖ε⁻¹‖ * (2 * ‖x - y‖) := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
    _ = _ := by ring

/-- The value formula genuinely attains the infimal quadratic bound. -/
theorem moreauEnvelope_le_quadratic_cost (f : E → ℝ) (hf : ConvexOn ℝ univ f) {ε : ℝ}
    (hε : 0 < ε) (x w : E) : moreauEnvelope f ε x ≤ f w + (2 * ε)⁻¹ * ‖w - x‖ ^ 2 := by
  have hh := (proximal_quadratic_bounds (proximalPoint_spec (moreau_scaled_convex hf hε)) x).1 w
  calc
    _ ≤ ε⁻¹ * (ε * f w + (1 / 2 : ℝ) * ‖w - x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hh (inv_pos.mpr hε).le
    _ = _ := by field_simp

/-- Actual lower germs transfer to the SAME proximal point, with actual contact. -/
theorem lower_contact_moreauEnvelope (f : E → ℝ) (hf : ConvexOn ℝ univ f) {ε : ℝ} (hε : 0 < ε)
    {x : E} {ψ : E → ℝ} (hc : moreauEnvelope f ε x = ψ x)
    (ht : ∀ᶠ z in 𝓝 x, ψ z ≤ moreauEnvelope f ε z) :
    let y := (proximalPoint (fun z => ε * f z)) x
    let c := (2 * ε)⁻¹ * ‖y - x‖ ^ 2
    f y = ψ (y + (x - y)) - c ∧ ∀ᶠ w in 𝓝 y, ψ (w + (x - y)) - c ≤ f w := by
  let y := (proximalPoint (fun z => ε * f z)) x
  let c := (2 * ε)⁻¹ * ‖y - x‖ ^ 2
  have he : moreauEnvelope f ε x = f y + c := by dsimp [moreauEnvelope, y, c]; field_simp
  refine ⟨?_, ?_⟩
  · rw [show y + (x - y) = x by abel, ← hc, he]
    ring
  · have hh : Tendsto (fun w : E => w + (x - y)) (𝓝 y) (𝓝 x) := by
      have hc : Continuous (fun w : E => w + (x - y)) := by fun_prop
      have hh := hc.tendsto y
      rwa [show y + (x - y) = x by abel] at hh
    filter_upwards [hh.eventually ht] with w hw
    have hm := moreauEnvelope_le_quadratic_cost f hf hε (w + (x - y)) w
    have hnorm : ‖w - (w + (x - y))‖ ^ 2 = ‖y - x‖ ^ 2 := by congr 1; congr 1; abel
    rw [hnorm] at hm
    change ψ (w + (x - y)) - c ≤ f w
    change moreauEnvelope f ε (w + (x - y)) ≤ f w + c at hm
    linarith

/-- Lipschitz source generates the uniform error and actual proximal displacement. -/
theorem moreauEnvelope_approximation (f : E → ℝ) (hf : ConvexOn ℝ univ f) {L : NNReal}
    (hL : LipschitzWith L f) {ε : ℝ} (hε : 0 < ε) (x : E) :
    moreauEnvelope f ε x ≤ f x ∧
      |moreauEnvelope f ε x - f x| ≤ ε * (L : ℝ) ^ 2 / 2 ∧
        ‖(proximalPoint (fun z => ε * f z)) x - x‖ ≤ ε * (L : ℝ) := by
  have hu : moreauEnvelope f ε x ≤ f x := by
    simpa using moreauEnvelope_le_quadratic_cost f hf hε x x
  have hLip :
    f x - f ((proximalPoint (fun z => ε * f z)) x) ≤
      (L : ℝ) * ‖(proximalPoint (fun z => ε * f z)) x - x‖ := by
    have h := hL.dist_le_mul x ((proximalPoint (fun z => ε * f z)) x)
    rw [Real.dist_eq, dist_eq_norm, norm_sub_rev] at h
    exact (le_abs_self _).trans h
  have he :
    ε * moreauEnvelope f ε x =
      ε * f ((proximalPoint (fun z => ε * f z)) x) +
        (1 / 2 : ℝ) * ‖(proximalPoint (fun z => ε * f z)) x - x‖ ^ 2 := by
    dsimp [moreauEnvelope]; rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
  have herror : f x - moreauEnvelope f ε x ≤ ε * (L : ℝ) ^ 2 / 2 := by
    apply (mul_le_mul_iff_right₀ hε).mp
    have hh := mul_le_mul_of_nonneg_left hLip hε.le
    nlinarith only [he, hh,
      sq_nonneg (‖(proximalPoint (fun z => ε * f z)) x - x‖ - ε * (L : ℝ))]
  have hp := proximalPoint_spec (moreau_scaled_convex hf hε) x x
  change
    ε * f ((proximalPoint (fun z => ε * f z)) x) +
        ⟪x - (proximalPoint (fun z => ε * f z)) x, x - (proximalPoint (fun z => ε * f z)) x⟫ ≤
      ε * f x at hp
  rw [real_inner_self_eq_norm_sq, norm_sub_rev] at hp
  have hd :
    ‖(proximalPoint (fun z => ε * f z)) x - x‖ ^ 2 ≤
      ε * (L : ℝ) * ‖(proximalPoint (fun z => ε * f z)) x - x‖ := by
    have hh := mul_le_mul_of_nonneg_left hLip hε.le
    nlinarith only [hp, hh]
  have hdisp : ‖(proximalPoint (fun z => ε * f z)) x - x‖ ≤ ε * (L : ℝ) := by
    by_contra hbad
    have hh := lt_of_not_ge hbad
    have hn : 0 < ‖(proximalPoint (fun z => ε * f z)) x - x‖ :=
      lt_of_le_of_lt (by positivity) hh
    have hm := mul_pos hn (sub_pos.mpr hh)
    nlinarith only [hd, hm]
  refine ⟨hu, ?_, hdisp⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith

/-- The actual quantitative error produces uniform convergence, not an input. -/
theorem tendstoUniformlyOn_moreauEnvelope (f : E → ℝ) (hf : ConvexOn ℝ univ f) {L : NNReal}
    (hL : LipschitzWith L f) :
    TendstoUniformlyOn (fun ε : ℝ => moreauEnvelope f ε) f (𝓝[>] (0 : ℝ)) univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hs : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < δ / ((L : ℝ) ^ 2 + 1) :=
    (eventually_lt_nhds (div_pos hδ (by positivity))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hs] with ε hε he x _
  have hpos : 0 < ε := hε
  have hb := (moreauEnvelope_approximation f hf hL hpos x).2.1
  have hd : ε * ((L : ℝ) ^ 2 + 1) < δ := (lt_div_iff₀ (by positivity)).mp he
  rw [Real.dist_eq, abs_sub_comm]
  nlinarith only [hb, hd, hpos, sq_nonneg (L : ℝ)]

end MoreauRegularization

end InnerProduct

end FunctionalInequalities.Analysis

end MoreauSymmetricDerivative
