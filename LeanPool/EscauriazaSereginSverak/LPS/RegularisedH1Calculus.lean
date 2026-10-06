/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTransportPairing
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedScalarCurve

/-!
# Calculus facts for the regularized `H¹` energy

Elementary real-analysis inputs to the differentiated energy identity of
`lem:lps-regularized-Hk-start` and `prop:lps-local-strong`: differentiation of a
scalar function from a paired increment, `L²` continuity of products, and the
sup-norm bound of a convolution by `L²` norms.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A scalar function whose increments over `[a,c]` are the integrals of the pairing of a path `R`, continuous at `a`, against `Θ a + Θ c`, with `Θ` continuous at `a`, has derivative `2 ⟪R a, Θ a⟫` at `a` (`prop:lps-local-strong`). -/
theorem lps_hasDerivAt_of_pair_increment
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {φ : ℝ → ℝ} {R Θ : ι → ℝ → E} {a : ℝ}
    (hR : ∀ i, ContinuousAt (R i) a) (hΘ : ∀ i, ContinuousAt (Θ i) a)
    (hInc : ∀ᶠ c in 𝓝 a,
      IntervalIntegrable (fun r => ∑ i, inner ℝ (R i r) (Θ i a + Θ i c)) volume a c ∧
      φ c - φ a = ∫ r in a..c, ∑ i, inner ℝ (R i r) (Θ i a + Θ i c)) :
    HasDerivAt φ (2 * ∑ i, inner ℝ (R i a) (Θ i a)) a := by
  set g : ℝ → ℝ → ℝ := fun r c => ∑ i, inner ℝ (R i r) (Θ i a + Θ i c) with hg
  set L : ℝ := 2 * ∑ i, inner ℝ (R i a) (Θ i a) with hL
  have hgcont : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (a, a) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    refine ContinuousAt.inner ?_ ?_
    · exact (hR i).comp_of_eq continuousAt_fst rfl
    · exact continuousAt_const.add ((hΘ i).comp_of_eq continuousAt_snd rfl)
  have hgaa : g a a = L := by
    simp only [hg, hL, ← two_mul, inner_add_right, Finset.mul_sum]
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro η hη
  have hev : ∀ᶠ p in 𝓝 (a, a), |g p.1 p.2 - L| < η := by
    have := hgcont.eventually (Metric.ball_mem_nhds (g a a) hη)
    filter_upwards [this] with p hp
    rw [← hgaa]
    simpa [Real.dist_eq] using hp
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hsub⟩ := hev
  filter_upwards [Metric.ball_mem_nhds a hδ, hInc] with c hc ⟨hint, hφ⟩
  have hbound : ∀ r ∈ Ι a c, ‖g r c - L‖ ≤ η := by
    intro r hr
    have hr' : dist r a < δ := by
      have hr2 : r ∈ uIcc a c := uIoc_subset_uIcc hr
      rw [Set.mem_uIcc] at hr2
      have hc' : dist c a < δ := hc
      rw [Real.dist_eq] at hc' ⊢
      rw [abs_lt] at hc' ⊢
      rcases hr2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2, hc'.1, hc'.2, hδ]
    have := hsub (y := (r, c)) (by
      rw [Prod.dist_eq]
      exact max_lt (by simpa using hr') (by simpa using hc))
    simpa [Real.norm_eq_abs] using this.le
  have h1 : ‖∫ r in a..c, (g r c - L)‖ ≤ η * |c - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub hint (by simp), intervalIntegral.integral_const,
    ← hφ] at h1
  simpa [Real.norm_eq_abs, smul_eq_mul, mul_comm] using h1

/-- The squared `L²` norm of the class of a square-integrable function is its integral of squares. -/
theorem lps_lp_norm_sq_eq_integral {f : Vec3 → ℝ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, sq]

/-- The squared distance of two `L²` classes is the integral of the squared difference of representatives. -/
theorem lps_lp_dist_sq_eq_integral {f g : Vec3 → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 := by
  have h : hf.toLp f - hg.toLp g = (hf.sub hg).toLp (fun x => f x - g x) :=
    (MemLp.toLp_sub hf hg).symm
  have hfg : MemLp (fun x => f x - g x) 2 volume := hf.sub hg
  rw [h]
  exact lps_lp_norm_sq_eq_integral (f := fun x => f x - g x) hfg

/-- Convergence of squared `L²` distances is continuity of the induced `L²` path. -/
theorem lps_continuousAt_toLp_of_sq_tendsto {f : ℝ → Vec3 → ℝ}
    (hmem : ∀ r, MemLp (f r) 2 volume) {a : ℝ}
    (h : Tendsto (fun r => ∫ x, (f r x - f a x) ^ 2) (𝓝 a) (𝓝 0)) :
    ContinuousAt (fun r => (hmem r).toLp (f r)) a := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun r => ‖(hmem r).toLp (f r) - (hmem a).toLp (f a)‖ ^ 2) (𝓝 a) (𝓝 0) := by
    refine h.congr fun r => ?_
    exact (lps_lp_dist_sq_eq_integral (hmem r) (hmem a)).symm
  have h3 := h2.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

/-- Continuity of an `L²` path gives convergence of the squared `L²` distances of its representatives. -/
theorem lps_sq_tendsto_of_continuousAt_toLp {f : ℝ → Vec3 → ℝ}
    (hmem : ∀ r, MemLp (f r) 2 volume) {a : ℝ}
    (h : ContinuousAt (fun r => (hmem r).toLp (f r)) a) :
    Tendsto (fun r => ∫ x, (f r x - f a x) ^ 2) (𝓝 a) (𝓝 0) := by
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp h)
  have h2 := (h1.pow 2)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
  refine h2.congr fun r => ?_
  exact lps_lp_dist_sq_eq_integral (hmem r) (hmem a)


/-- The product of a uniformly bounded, uniformly convergent factor with an `L²`-convergent factor converges in `L²`. -/
theorem lps_sq_tendsto_mul {A B : ℝ → Vec3 → ℝ} {a M : ℝ} {ν : ℝ → ℝ}
    (hBa : MemLp (B a) 2 volume) (hB : ∀ᶠ r in 𝓝 a, MemLp (B r) 2 volume)
    (hBt : Tendsto (fun r => ∫ x, (B r x - B a x) ^ 2) (𝓝 a) (𝓝 0))
    (hM : ∀ᶠ r in 𝓝 a, ∀ x, |A r x| ≤ M)
    (hν : Tendsto ν (𝓝 a) (𝓝 0))
    (hAν : ∀ᶠ r in 𝓝 a, ∀ x, |A r x - A a x| ≤ ν r) :
    Tendsto (fun r => ∫ x, (A r x * B r x - A a x * B a x) ^ 2) (𝓝 a) (𝓝 0) := by
  have hbound : Tendsto (fun r => 2 * M ^ 2 * (∫ x, (B r x - B a x) ^ 2) +
      2 * ν r ^ 2 * (∫ x, B a x ^ 2)) (𝓝 a) (𝓝 0) := by
    have h1 := hBt.const_mul (2 * M ^ 2)
    have h2 := ((hν.pow 2).const_mul 2).mul_const (∫ x, B a x ^ 2)
    have := h1.add h2
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun r => integral_nonneg fun x => sq_nonneg _)
    ?_ hbound
  filter_upwards [hM, hB, hAν] with r hr hBr hAνr
  have hint1 : Integrable (fun x => (B r x - B a x) ^ 2) volume :=
    (hBr.sub hBa).integrable_sq
  have hint2 : Integrable (fun x => B a x ^ 2) volume := hBa.integrable_sq
  have hrhs : Integrable (fun x => 2 * M ^ 2 * (B r x - B a x) ^ 2 +
      2 * ν r ^ 2 * B a x ^ 2) volume :=
    (hint1.const_mul _).add (hint2.const_mul _)
  calc ∫ x, (A r x * B r x - A a x * B a x) ^ 2
      ≤ ∫ x, (2 * M ^ 2 * (B r x - B a x) ^ 2 + 2 * ν r ^ 2 * B a x ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hrhs
          (Eventually.of_forall fun x => ?_)
        beta_reduce
        have h1 : |A r x| ≤ M := hr x
        have h2 : |A r x - A a x| ≤ ν r := hAνr x
        have hM0 : 0 ≤ M := (abs_nonneg _).trans h1
        have e : A r x * B r x - A a x * B a x =
            A r x * (B r x - B a x) + (A r x - A a x) * B a x := by ring
        rw [e]
        have h3 : (A r x * (B r x - B a x)) ^ 2 ≤ M ^ 2 * (B r x - B a x) ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (by
            have := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
            simpa using this) (sq_nonneg _)
        have h4 : ((A r x - A a x) * B a x) ^ 2 ≤ ν r ^ 2 * B a x ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (by
            have hν0 : 0 ≤ ν r := (abs_nonneg _).trans h2
            have := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
            simpa using this) (sq_nonneg _)
        nlinarith only [h3, h4, sq_nonneg (A r x * (B r x - B a x) - (A r x - A a x) * B a x)]
    _ = 2 * M ^ 2 * (∫ x, (B r x - B a x) ^ 2) + 2 * ν r ^ 2 * (∫ x, B a x ^ 2) := by
        rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
          integral_const_mul]

/-- The pointwise difference of two convolutions with a fixed `L²` kernel is bounded by the kernel's `L²` norm times the `L²` distance of the two arguments. -/
theorem lps_convolution_diff_abs_le {κ f g : Vec3 → ℝ}
    (hκ : MemLp κ 2 volume) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x : Vec3) :
    |(convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x -
        (convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x| ≤
      Real.sqrt (∫ t, κ t ^ 2) * Real.sqrt (∫ t, (f t - g t) ^ 2) := by
  have hmp : MeasurePreserving (fun t : Vec3 => x - t) volume volume :=
    (volume : Measure Vec3).measurePreserving_sub_left x
  have hfx : MemLp (fun t => f (x - t)) 2 volume := hf.comp_measurePreserving hmp
  have hgx : MemLp (fun t => g (x - t)) 2 volume := hg.comp_measurePreserving hmp
  have hdx : MemLp (fun t => f (x - t) - g (x - t)) 2 volume := hfx.sub hgx
  have h1 : (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x -
        (convolution κ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x =
      ∫ t, κ t * (f (x - t) - g (x - t)) := by
    simp only [convolution_lsmul, smul_eq_mul]
    have := integral_sub (hκ.integrable_mul hfx) (hκ.integrable_mul hgx)
    simp only [Pi.mul_apply] at this
    rw [← this]
    congr 1
    funext t
    ring
  have h2 : (∫ t, (f (x - t) - g (x - t)) ^ 2) = ∫ t, (f t - g t) ^ 2 := by
    exact integral_sub_left_eq_self (fun t : Vec3 => (f t - g t) ^ 2) volume x
  rw [h1]
  have h3 : |∫ t, κ t * (f (x - t) - g (x - t))| ≤
      ∫ t, |κ t| * |f (x - t) - g (x - t)| := by
    refine (abs_integral_le_integral_abs).trans ?_
    simp only [abs_mul, le_refl]
  have h4 := lps_integral_pairing_le (fun t => |κ t|) (fun t => |f (x - t) - g (x - t)|)
    hκ.abs hdx.abs
  refine h3.trans (h4.trans ?_)
  simp only [sq_abs]
  rw [h2]


/-- The `L²` class of a time-dependent function, with time clamped to `[0, ∞)`. -/
@[expose] def lpsPath (f : ℝ → Vec3 → ℝ) (hf : ∀ s, 0 ≤ s → MemLp (f s) 2 volume) (s : ℝ) :
    Lp ℝ 2 (volume : Measure Vec3) :=
  (hf (max s 0) (le_max_right _ _)).toLp (f (max s 0))

/-- On nonnegative times the clamped `L²` path is the class of the function itself. -/
theorem lps_lpsPath_apply {f : ℝ → Vec3 → ℝ} {hf : ∀ s, 0 ≤ s → MemLp (f s) 2 volume}
    {r : ℝ} (hr : 0 ≤ r) :
    lpsPath f hf r = (hf r hr).toLp (f r) := by
  unfold lpsPath
  simp only [max_eq_left hr]

/-- On nonnegative times the clamped `L²` path is represented by the function itself. -/
theorem lps_lpsPath_coeFn {f : ℝ → Vec3 → ℝ} {hf : ∀ s, 0 ≤ s → MemLp (f s) 2 volume}
    {r : ℝ} (hr : 0 ≤ r) :
    (lpsPath f hf r : Vec3 → ℝ) =ᵐ[volume] f r := by
  rw [lps_lpsPath_apply hr]
  exact (hf r hr).coeFn_toLp

/-- A clamped `L²` path is continuous at a positive time where it agrees near that time with an `L²`-continuous path. -/
theorem lps_continuousAt_lpsPath_of_path {f : ℝ → Vec3 → ℝ}
    {hf : ∀ s, 0 ≤ s → MemLp (f s) 2 volume} {a : ℝ}
    {F : ℝ → Lp ℝ 2 (volume : Measure Vec3)} (ha : 0 < a) (hF : ContinuousAt F a)
    (hae : ∀ᶠ r in 𝓝 a, (F r : Vec3 → ℝ) =ᵐ[volume] f r) :
    ContinuousAt (lpsPath f hf) a := by
  refine hF.congr ?_
  filter_upwards [hae, lt_mem_nhds ha] with r hr hr0
  rw [lps_lpsPath_apply hr0.le]
  exact (Lp.ext (by
    filter_upwards [hr, (hf r hr0.le).coeFn_toLp] with x h1 h2
    rw [h1, h2]))

/-- Every value of the clamped `L²` path is represented by the function at the clamped time. -/
theorem lps_lpsPath_coeFn' {f : ℝ → Vec3 → ℝ} {hf : ∀ s, 0 ≤ s → MemLp (f s) 2 volume}
    (r : ℝ) :
    (lpsPath f hf r : Vec3 → ℝ) =ᵐ[volume] f (max r 0) :=
  (hf (max r 0) (le_max_right _ _)).coeFn_toLp

/-- The clamped `L²` path of a finite sum of functions is the sum of the paths. -/
theorem lps_lpsPath_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℝ → Vec3 → ℝ}
    {hf : ∀ i, ∀ t, 0 ≤ t → MemLp (f i t) 2 volume}
    {g : ℝ → Vec3 → ℝ} {hg : ∀ t, 0 ≤ t → MemLp (g t) 2 volume}
    (hsum : ∀ t x, g t x = ∑ i ∈ s, f i t x) (r : ℝ) :
    lpsPath g hg r = ∑ i ∈ s, lpsPath (f i) (hf i) r := by
  refine Lp.ext ?_
  have h1 := lps_lpsPath_coeFn' (hf := hg) r
  have h3 := Lp.coeFn_finsetSum s (fun i => lpsPath (f i) (hf i) r)
  have h4 : ∀ᵐ x ∂(volume : Measure Vec3), ∀ i ∈ s,
      ((lpsPath (f i) (hf i) r : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) x =
        f i (max r 0) x :=
    (Filter.eventually_all_finset s).2 fun i _ => lps_lpsPath_coeFn' (hf := hf i) r
  filter_upwards [h1, h3, h4] with x hx1 hx3 hx4
  rw [hx1, hx3, hsum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => (hx4 i hi).symm

/-- The clamped `L²` path of a difference is the difference of the paths. -/
theorem lps_lpsPath_sub {f g h : ℝ → Vec3 → ℝ}
    {hf : ∀ t, 0 ≤ t → MemLp (f t) 2 volume} {hg : ∀ t, 0 ≤ t → MemLp (g t) 2 volume}
    {hh : ∀ t, 0 ≤ t → MemLp (h t) 2 volume}
    (hsub : ∀ t x, h t x = f t x - g t x) (r : ℝ) :
    lpsPath h hh r = lpsPath f hf r - lpsPath g hg r := by
  refine Lp.ext ?_
  filter_upwards [lps_lpsPath_coeFn' (hf := hh) r, lps_lpsPath_coeFn' (hf := hf) r,
    lps_lpsPath_coeFn' (hf := hg) r, Lp.coeFn_sub (lpsPath f hf r) (lpsPath g hg r)] with
    x h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3, hsub]

/-- The clamped `L²` path of a negative is the negative of the path. -/
theorem lps_lpsPath_neg {f h : ℝ → Vec3 → ℝ}
    {hf : ∀ t, 0 ≤ t → MemLp (f t) 2 volume} {hh : ∀ t, 0 ≤ t → MemLp (h t) 2 volume}
    (hneg : ∀ t x, h t x = -f t x) (r : ℝ) :
    lpsPath h hh r = -lpsPath f hf r := by
  refine Lp.ext ?_
  filter_upwards [lps_lpsPath_coeFn' (hf := hh) r, lps_lpsPath_coeFn' (hf := hf) r,
    Lp.coeFn_neg (lpsPath f hf r)] with x h1 h2 h4
  rw [h1, h4, Pi.neg_apply, h2, hneg]

/-- The inner product of two clamped `L²` paths is the integral of the product of the functions at the clamped times. -/
theorem lps_inner_lpsPath {f g : ℝ → Vec3 → ℝ}
    {hf : ∀ t, 0 ≤ t → MemLp (f t) 2 volume} {hg : ∀ t, 0 ≤ t → MemLp (g t) 2 volume}
    (r c : ℝ) :
    inner ℝ (lpsPath f hf r) (lpsPath g hg c) = ∫ x, f (max r 0) x * g (max c 0) x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lps_lpsPath_coeFn' (hf := hf) r, lps_lpsPath_coeFn' (hf := hg) c] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]


/-- Continuity of a clamped `L²` path at a positive time gives convergence of the squared `L²`
distances of the underlying functions. -/
theorem lps_sq_tendsto_of_continuousAt_lpsPath {f : ℝ → Vec3 → ℝ}
    {hf : ∀ s, 0 ≤ s → MemLp (f s) 2 volume} {a : ℝ} (ha : 0 < a)
    (h : ContinuousAt (lpsPath f hf) a) :
    Tendsto (fun r => ∫ x, (f r x - f a x) ^ 2) (𝓝 a) (𝓝 0) := by
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.mp h)
  have h2 := h1.pow 2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h2
  refine h2.congr' ?_
  filter_upwards [lt_mem_nhds ha] with r hr
  rw [lps_lpsPath_apply hr.le, lps_lpsPath_apply ha.le]
  exact lps_lp_dist_sq_eq_integral (hf r hr.le) (hf a ha.le)

/-- Convergence of squared `L²` distances at a positive time gives continuity of the clamped `L²`
path. -/
theorem lps_continuousAt_lpsPath_of_sq_tendsto {f : ℝ → Vec3 → ℝ}
    {hf : ∀ s, 0 ≤ s → MemLp (f s) 2 volume} {a : ℝ} (ha : 0 < a)
    (h : Tendsto (fun r => ∫ x, (f r x - f a x) ^ 2) (𝓝 a) (𝓝 0)) :
    ContinuousAt (lpsPath f hf) a := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun r => ‖lpsPath f hf r - lpsPath f hf a‖ ^ 2) (𝓝 a) (𝓝 0) := by
    refine h.congr' ?_
    filter_upwards [lt_mem_nhds ha] with r hr
    rw [lps_lpsPath_apply hr.le, lps_lpsPath_apply ha.le]
    exact (lps_lp_dist_sq_eq_integral (hf r hr.le) (hf a ha.le)).symm
  have h3 := h2.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

end ESS.LPS

end
