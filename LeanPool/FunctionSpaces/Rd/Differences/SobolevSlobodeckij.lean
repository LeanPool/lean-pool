/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Differences.Differences
public import LeanPool.FunctionSpaces.Analysis.Maximal.HardyLittlewoodMaximal
public import LeanPool.FunctionSpaces.Rd.Differences.BesovDifferences

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sobolev–Slobodeckij norms by first differences

On a finite-dimensional real inner product space `V` of dimension `n` with Lebesgue measure, the
**Gagliardo form** of `f : V → ℂ` with smoothness `s` and exponent `p` is
`∫∫ |f(y) - f(x)|^p / |y - x|^(n + sp) dy dx` (`Rd.slobodeckijForm`), the `p`-th power of the
Gagliardo seminorm of the Sobolev–Slobodeckij space `W^{s,p}(V)` (Gagliardo 1957). The
substitution `y = x + h` and Tonelli's theorem turn it into
`∫ ‖Δ_h f‖_p^p / |h|^(n + sp) dh` (`Rd.slobodeckijForm_eq_lintegral_eLpNorm`).

For `1 ≤ p < ∞` and `s > 0` the form is equivalent to the first-difference Besov norm:
* `‖(2^(ks) ω_1(f, 2^(-k))_p)_k‖_{ℓ_p}^p ≤ C_1 ∫∫ …` (`Rd.lqNorm_modulus_rpow_le_slobodeckijForm`),
  since `‖Δ_h f‖_p^p ≤ 2^p |B(0,t)|⁻¹ ∫_{|z| < 2t} ‖Δ_z f‖_p^p dz` for `|h| ≤ t`
  (`Rd.eLpNorm_fwdDiff_rpow_le_average`), and Hardy's inequality sums the dyadic annuli;
* `∫∫ … ≤ C_2 (‖f‖_p^p + ‖(2^(ks) ω_1(f, 2^(-k))_p)_k‖_{ℓ_p}^p)` (`Rd.slobodeckijForm_le`),
  from the dyadic annuli inside the unit ball and the radial integral
  `∫_{|z| ≥ R} |z|^(-a) dz ≤ c R^(n-a)` for `a > n` (`Rd.lintegral_compl_ball_norm_rpow_neg_le`).

The constants are explicit (`Rd.slobodeckijConstUpper`, `Rd.slobodeckijConstLower`). For
`0 < s < 1` the form is finite exactly on the Besov space `B^s_{p,p}(V)`, so
`W^{s,p}(V) = B^s_{p,p}(V)` (`Rd.slobodeckijForm_lt_top_iff_memApprox`). The radial integral
over balls, `∫_{|z| < R} |z|^(-a) dz ≤ c R^(n-a)` for `a < n`, is
`Rd.lintegral_ball_norm_rpow_neg_le`. Together they bound `∫ u(z)^p / |z|^a dz` for
`u(z) ≤ min(L |z|, S)` (`Rd.lintegral_rpow_div_norm_rpow_le`), and the integral outside a ball
bounds, after translation, the tail `∫∫ u(x) 1_{|y - x| ≥ η} |y - x|^(-a) dy dx`
(`Rd.lintegral_lintegral_mul_indicator_le`). Double integrals split over sums and take out finite
constants (`Rd.lintegral_lintegral_add_right`, `Rd.lintegral_lintegral_le_add_two_mul`,
`Rd.lintegral_lintegral_const_mul'`).
-/

@[expose] public section

open MeasureTheory Metric Module Set
open scoped ENNReal

namespace ENNReal

/-! ### Powers in `[0, ∞]` -/

/-- A power of a number between `l` and `u` is at most `l^b + u^b`, whatever the sign of `b`. -/
theorem rpow_le_rpow_add_rpow_of_le_of_le {x l u : ℝ≥0∞} (hl : l ≤ x) (hu : x ≤ u) (b : ℝ) :
    x ^ b ≤ l ^ b + u ^ b := by
  rcases le_total b 0 with hb | hb
  · exact (ENNReal.rpow_le_rpow_of_nonpos hl hb).trans le_self_add
  · exact (ENNReal.rpow_le_rpow hu hb).trans le_add_self

end ENNReal

namespace Rd

open ENNReal (lqNorm dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The Gagliardo form -/

/-- The **Gagliardo form** `∫∫ |f(y) - f(x)|^p / |y - x|^(n + sp) dy dx` of `f : V → ℂ`, with
`n = dim V`: for `0 < p < ∞` the `p`-th power of the Gagliardo seminorm of the
Sobolev–Slobodeckij space `W^{s,p}(V)` (Gagliardo 1957). The exponent is the real number
`p.toReal`, which is `0` for `p = ∞`. For `p = 2`, `s = α/2` and measurable real-valued `f` it
agrees, by Tonelli's theorem, with the form `formHs univ α` of the Lean project
*quadratic-forms-sobolev-lean*, an integral for the product measure, with the same orientation
`f(y) - f(x)`. -/
noncomputable def slobodeckijForm (p : ℝ≥0∞) (s : ℝ) (f : V → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ‖f y - f x‖ₑ ^ p.toReal / ‖y - x‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)

/-- The Gagliardo form depends only on the class of `f` modulo null sets. -/
theorem slobodeckijForm_congr_ae {f g : V → ℂ} (hfg : f =ᵐ[volume] g) (p : ℝ≥0∞) (s : ℝ) :
    slobodeckijForm p s f = slobodeckijForm p s g :=
  lintegral_congr_ae (hfg.mono fun x hx => lintegral_congr_ae (hfg.mono fun y hy => by
    simp only [hx, hy]))

/-- On a space with one point the Gagliardo form vanishes for `0 < p < ∞`: every difference
`f(y) - f(x)` is `0`. -/
theorem slobodeckijForm_of_subsingleton [Subsingleton V] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (s : ℝ) (f : V → ℂ) : slobodeckijForm p s f = 0 := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have h : ∀ x y : V,
      ‖f y - f x‖ₑ ^ p.toReal / ‖y - x‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) = 0 :=
    fun x y => by
      rw [Subsingleton.elim y x, sub_self, eNorm_zero, ENNReal.zero_rpow_of_pos hP,
        ENNReal.zero_div]
  simp only [slobodeckijForm, h, lintegral_zero]

/-- First differences of functions that agree almost everywhere agree almost everywhere. -/
theorem fwdDiff_congr_ae {f g : V → ℂ} (hfg : f =ᵐ[volume] g) (h : V) :
    fwdDiff h f =ᵐ[volume] fwdDiff h g := by
  simpa using higherDiff_congr_ae hfg 1 h

/-- `‖Δ_h f‖_p^p = ∫ |f(x + h) - f(x)|^p dx` for `0 < p < ∞` and a.e. strongly measurable `f`
(Mathlib's `eLpNorm_eq_lintegral_rpow_eNorm_toReal`). -/
theorem eLpNorm_fwdDiff_rpow_eq {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) (h : V) :
    eLpNorm (fwdDiff h f) p volume ^ p.toReal = ∫⁻ x, ‖f (x + h) - f x‖ₑ ^ p.toReal := by
  have hm : AEStronglyMeasurable (fwdDiff h f) volume := by
    simpa using aestronglyMeasurable_higherDiff hf 1 h
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hm, one_div,
    ENNReal.rpow_inv_rpow (ENNReal.toReal_pos hp0 hp).ne']
  rfl

/-- `‖Δ_0 f‖_p^p = 0` for `0 < p < ∞`, since `Δ_0 f = 0`. -/
theorem eLpNorm_fwdDiff_zero_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (f : V → ℂ) :
    eLpNorm (fwdDiff 0 f) p volume ^ p.toReal = 0 := by
  have h0 : fwdDiff (0 : V) f = 0 := funext fun x => by simp [fwdDiff]
  rw [h0, eLpNorm_zero, ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp0 hp)]

/-- For `0 < p < ∞` and a.e. strongly measurable `f`, the step function `h ↦ ‖Δ_h f‖_p^p` is
measurable, as the integral of a jointly measurable function of `(x, h)` (Mathlib's
`Measurable.lintegral_prod_left'`). -/
theorem measurable_eLpNorm_fwdDiff_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) :
    Measurable fun h : V => eLpNorm (fwdDiff h f) p volume ^ p.toReal := by
  have hg : Measurable (hf.mk f) := hf.stronglyMeasurable_mk.measurable
  have heq : (fun h : V => eLpNorm (fwdDiff h f) p volume ^ p.toReal) =
      fun h => ∫⁻ x, ‖hf.mk f (x + h) - hf.mk f x‖ₑ ^ p.toReal := by
    funext h
    rw [eLpNorm_congr_ae (fwdDiff_congr_ae hf.ae_eq_mk h),
      eLpNorm_fwdDiff_rpow_eq hp0 hp hg.aestronglyMeasurable h]
  rw [heq]
  exact Measurable.lintegral_prod_left' (f := fun z : V × V =>
    ‖hf.mk f (z.1 + z.2) - hf.mk f z.1‖ₑ ^ p.toReal)
    (((hg.comp (measurable_fst.add measurable_snd)).sub (hg.comp measurable_fst)).eNorm.pow_const _)

/-- **The Gagliardo form by the step**, for measurable `f`: the substitution `y = x + h`
(Mathlib's `lintegral_add_left_eq_self`) and Tonelli's theorem (`lintegral_lintegral_swap`) give
`∫∫ |f(y) - f(x)|^p / |y - x|^(n + sp) dy dx = ∫ ‖Δ_h f‖_p^p / |h|^(n + sp) dh`. -/
theorem slobodeckijForm_eq_lintegral_of_measurable {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (s : ℝ) {f : V → ℂ} (hf : Measurable f) :
    slobodeckijForm p s f = ∫⁻ h, eLpNorm (fwdDiff h f) p volume ^ p.toReal /
      ‖h‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) := by
  have hshift : ∀ x : V, ∫⁻ y, ‖f y - f x‖ₑ ^ p.toReal /
      ‖y - x‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) =
      ∫⁻ h, ‖f (x + h) - f x‖ₑ ^ p.toReal / ‖h‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) := by
    intro x
    rw [← lintegral_add_left_eq_self _ x]
    simp only [add_sub_cancel_left]
  have hmeas : Measurable (Function.uncurry fun (x h : V) =>
      ‖f (x + h) - f x‖ₑ ^ p.toReal / ‖h‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)) :=
    (((hf.comp (measurable_fst.add measurable_snd)).sub (hf.comp measurable_fst)).eNorm.pow_const
      _).div (measurable_snd.eNorm.pow_const _)
  rw [slobodeckijForm]
  simp_rw [hshift]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun h => ?_
  rw [eLpNorm_fwdDiff_rpow_eq hp0 hp hf.aestronglyMeasurable h]
  simp_rw [div_eq_mul_inv]
  exact lintegral_mul_const _
    (((hf.comp (measurable_add_const h)).sub hf).eNorm.pow_const _)

/-- **The Gagliardo form by the step**: for `0 < p < ∞` and a.e. strongly measurable `f`,
`∫∫ |f(y) - f(x)|^p / |y - x|^(n + sp) dy dx = ∫ ‖Δ_h f‖_p^p / |h|^(n + sp) dh`. -/
theorem slobodeckijForm_eq_lintegral_eLpNorm {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (s : ℝ)
    {f : V → ℂ} (hf : AEStronglyMeasurable f volume) :
    slobodeckijForm p s f = ∫⁻ h, eLpNorm (fwdDiff h f) p volume ^ p.toReal /
      ‖h‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) := by
  rw [slobodeckijForm_congr_ae hf.ae_eq_mk,
    slobodeckijForm_eq_lintegral_of_measurable hp0 hp s hf.stronglyMeasurable_mk.measurable]
  refine lintegral_congr fun h => ?_
  rw [eLpNorm_congr_ae (fwdDiff_congr_ae hf.ae_eq_mk h)]

/-! ### Dyadic annuli -/

/-- The **dyadic annulus** `{z : ρ 2^(-(j+1)) < |z| ≤ ρ 2^(-j)}`. -/
def dyadicAnnulus (ρ : ℝ) (j : ℕ) : Set V :=
  {z | ρ / 2 ^ (j + 1) < ‖z‖ ∧ ‖z‖ ≤ ρ / 2 ^ j}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The dyadic annuli are measurable. -/
theorem measurableSet_dyadicAnnulus (ρ : ℝ) (j : ℕ) :
    MeasurableSet (dyadicAnnulus (V := V) ρ j) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For `ρ ≥ 0` the dyadic annuli are pairwise disjoint. -/
theorem pairwise_disjoint_dyadicAnnulus {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Pairwise (Function.onFun Disjoint (dyadicAnnulus (V := V) ρ)) := by
  rw [pairwise_disjoint_on]
  intro i j hij
  rw [Set.disjoint_left]
  rintro z ⟨hz1, -⟩ ⟨-, hz4⟩
  have hle : ρ / 2 ^ j ≤ ρ / 2 ^ (i + 1) :=
    div_le_div_of_nonneg_left hρ (by positivity) (pow_le_pow_right₀ one_le_two hij)
  linarith

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The annuli cover the punctured ball**: every `z ≠ 0` with `|z| ≤ ρ 2^(-k)` lies in an
annulus `ρ 2^(-(k+i+1)) < |z| ≤ ρ 2^(-(k+i))`, with `2^i ≤ ρ 2^(-k)/|z| < 2^(i+1)`. -/
theorem closedBall_subset_union_iUnion_dyadicAnnulus (ρ : ℝ) (k : ℕ) :
    closedBall (0 : V) (ρ / 2 ^ k) ⊆ {0} ∪ ⋃ i, dyadicAnnulus ρ (k + i) := by
  intro z hz
  rw [mem_closedBall_zero_iff] at hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact Or.inl rfl
  refine Or.inr (mem_iUnion.2 ?_)
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  obtain ⟨i, hi1, hi2⟩ := exists_nat_pow_near ((one_le_div hn).2 hz) one_lt_two
  rw [le_div_iff₀ hn] at hi1
  rw [div_lt_iff₀ hn] at hi2
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h2i : (0 : ℝ) < 2 ^ i := by positivity
  refine ⟨i, ?_, ?_⟩
  · rw [show k + i + 1 = k + (i + 1) by ring, pow_add, ← div_div, div_lt_iff₀ (by positivity)]
    linarith
  · rw [pow_add, ← div_div, le_div_iff₀ h2i]
    linarith

/-- **An integral over a ball by the annuli**: for every `G : V → [0, ∞]`,
`∫_{|z| ≤ ρ 2^(-k)} G ≤ G(0) |{0}| + ∑_i ∫_{annulus (k + i)} G`. -/
theorem setLIntegral_closedBall_le_tsum_dyadicAnnulus (G : V → ℝ≥0∞) (ρ : ℝ) (k : ℕ) :
    ∫⁻ z in closedBall (0 : V) (ρ / 2 ^ k), G z ≤
      G 0 * volume {(0 : V)} + ∑' i, ∫⁻ z in dyadicAnnulus ρ (k + i), G z := by
  calc ∫⁻ z in closedBall (0 : V) (ρ / 2 ^ k), G z
      ≤ ∫⁻ z in {0} ∪ ⋃ i, dyadicAnnulus ρ (k + i), G z :=
        lintegral_mono_set (closedBall_subset_union_iUnion_dyadicAnnulus ρ k)
    _ ≤ (∫⁻ z in {(0 : V)}, G z) + ∫⁻ z in ⋃ i, dyadicAnnulus ρ (k + i), G z :=
        lintegral_union_le _ _ _
    _ ≤ _ := by
        rw [lintegral_singleton]
        gcongr
        exact lintegral_iUnion_le _ _

/-- For `G(0) = 0`: `∫_{|z| ≤ ρ 2^(-k)} G ≤ ∑_i ∫_{annulus (k + i)} G`. -/
theorem setLIntegral_closedBall_le_tsum_dyadicAnnulus_of_zero {G : V → ℝ≥0∞} (hG : G 0 = 0)
    (ρ : ℝ) (k : ℕ) :
    ∫⁻ z in closedBall (0 : V) (ρ / 2 ^ k), G z ≤ ∑' i, ∫⁻ z in dyadicAnnulus ρ (k + i), G z := by
  simpa [hG] using setLIntegral_closedBall_le_tsum_dyadicAnnulus G ρ k

/-- The integrals over the disjoint annuli sum to at most the integral over `V`
(Mathlib's `lintegral_iUnion`). -/
theorem tsum_setLIntegral_dyadicAnnulus_le (G : V → ℝ≥0∞) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑' j, ∫⁻ z in dyadicAnnulus ρ j, G z ≤ ∫⁻ z, G z := by
  rw [← lintegral_iUnion (measurableSet_dyadicAnnulus ρ) (pairwise_disjoint_dyadicAnnulus hρ)]
  exact setLIntegral_le_lintegral _ _

/-- The annulus `j` has volume at most `ρ^n 2^(-jn) |B_1|`, the volume of the closed ball of
radius `ρ 2^(-j)` (`Rd.volume_closedBall_div_two_pow`). -/
theorem volume_dyadicAnnulus_le {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    volume (dyadicAnnulus (V := V) ρ j) ≤ ENNReal.ofReal ρ ^ (finrank ℝ V : ℝ) *
      dyadicWeight (-(finrank ℝ V : ℝ)) j * volume (ball (0 : V) 1) :=
  (measure_mono fun z (hz : z ∈ dyadicAnnulus (V := V) ρ j) =>
    mem_closedBall_zero_iff.2 hz.2).trans_eq <| by
    rw [volume_closedBall_div_two_pow hρ.le, ENNReal.ofReal_pow hρ.le, ← ENNReal.rpow_natCast]
    ring

/-! ### Radial integrals of powers -/

variable (V) in
/-- The constant `2^n |B_1| (1 - 2^(-(a-n)))⁻¹` of the radial integral
`∫_{|z| ≥ R} |z|^(-a) dz` for `a > n = dim V`. -/
noncomputable def complBallRpowConst (a : ℝ) : ℝ≥0∞ :=
  2 ^ (finrank ℝ V : ℝ) * volume (ball (0 : V) 1) * (1 - 2 ^ (-(a - finrank ℝ V)))⁻¹

/-- The constant of `∫_{|z| ≥ R} |z|^(-a) dz` is finite for `a > n`. -/
theorem complBallRpowConst_ne_top {a : ℝ} (ha : (finrank ℝ V : ℝ) < a) :
    complBallRpowConst V a ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.two_rpow_ne_top _)
    (volume_ball_ne_top 1)) (ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 ha))

/-- On the part of the dyadic shell `i` outside the ball of radius `R`, `|z|^(-a)` has the
integral at most `2^n |B_1| R^(n-a) 2^(-i(a-n))`, for `a ≥ 0`. -/
theorem setLIntegral_compl_ball_inter_dyadicShell_le {a : ℝ} (ha : 0 ≤ a) {R : ℝ}
    (hR : 0 < R) (i : ℕ) :
    ∫⁻ z in (ball (0 : V) R)ᶜ ∩ dyadicShell R i, ‖z‖ₑ ^ (-a) ≤
      2 ^ (finrank ℝ V : ℝ) * volume (ball (0 : V) 1) *
        ENNReal.ofReal R ^ ((finrank ℝ V : ℝ) - a) * dyadicWeight (-(a - finrank ℝ V)) i := by
  have hpt : ∀ z ∈ (ball (0 : V) R)ᶜ ∩ dyadicShell R i,
      ‖z‖ₑ ^ (-a) ≤ ENNReal.ofReal (2 ^ i * R) ^ (-a) := by
    rintro z ⟨hz1, hz2⟩
    have hle : 2 ^ i * R ≤ ‖z‖ := by
      rcases hz2.2 with rfl | hi
      · simpa [mem_ball_zero_iff] using hz1
      · exact hi
    rw [← ofReal_norm]
    exact ENNReal.rpow_le_rpow_of_nonpos (ENNReal.ofReal_le_ofReal hle) (neg_nonpos.2 ha)
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.2 hR).ne'
  calc ∫⁻ z in (ball (0 : V) R)ᶜ ∩ dyadicShell R i, ‖z‖ₑ ^ (-a)
      ≤ ∫⁻ _ in (ball (0 : V) R)ᶜ ∩ dyadicShell R i, ENNReal.ofReal (2 ^ i * R) ^ (-a) :=
        setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal (2 ^ i * R) ^ (-a) * volume ((ball (0 : V) R)ᶜ ∩ dyadicShell R i) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (2 ^ i * R) ^ (-a) * volume (ball (0 : V) (2 ^ (i + 1) * R)) := by
        gcongr
        exact fun z hz => mem_ball_zero_iff.2 hz.2.1
    _ = _ := by
        rw [Measure.addHaar_ball_of_pos _ _ (by positivity), ENNReal.ofReal_pow (by positivity),
          ← ENNReal.rpow_natCast, ENNReal.ofReal_two_pow_mul_rpow hR,
          ENNReal.ofReal_two_pow_mul_rpow hR,
          ENNReal.dyadicWeight_succ, show (finrank ℝ V : ℝ) - a = -a + finrank ℝ V by ring,
          ENNReal.rpow_add _ _ hR0 ENNReal.ofReal_ne_top,
          show -(a - (finrank ℝ V : ℝ)) = -a + finrank ℝ V by ring, ENNReal.dyadicWeight_add]
        ring

/-- **The radial integral outside a ball**: for `a > n = dim V` and `R > 0`,
`∫_{|z| ≥ R} |z|^(-a) dz ≤ 2^n |B_1| (1 - 2^(-(a-n)))⁻¹ R^(n-a)`, by the dyadic shells
`2^i R ≤ |z| < 2^(i+1) R` and a geometric series. -/
theorem lintegral_compl_ball_norm_rpow_neg_le {a : ℝ} (ha : (finrank ℝ V : ℝ) < a) {R : ℝ}
    (hR : 0 < R) :
    ∫⁻ z in (ball (0 : V) R)ᶜ, ‖z‖ₑ ^ (-a) ≤
      complBallRpowConst V a * ENNReal.ofReal R ^ ((finrank ℝ V : ℝ) - a) := by
  have ha0 : 0 ≤ a := (Nat.cast_nonneg _).trans ha.le
  have hcover : (ball (0 : V) R)ᶜ ⊆ ⋃ i, (ball (0 : V) R)ᶜ ∩ dyadicShell R i := by
    intro z hz
    have hz' : z ∈ ⋃ i, dyadicShell (V := V) R i := by
      rw [iUnion_dyadicShell hR]
      exact mem_univ z
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz'
    exact mem_iUnion.2 ⟨i, hz, hi⟩
  calc ∫⁻ z in (ball (0 : V) R)ᶜ, ‖z‖ₑ ^ (-a)
      ≤ ∫⁻ z in ⋃ i, (ball (0 : V) R)ᶜ ∩ dyadicShell R i, ‖z‖ₑ ^ (-a) := lintegral_mono_set hcover
    _ ≤ ∑' i, ∫⁻ z in (ball (0 : V) R)ᶜ ∩ dyadicShell R i, ‖z‖ₑ ^ (-a) :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' i, 2 ^ (finrank ℝ V : ℝ) * volume (ball (0 : V) 1) *
          ENNReal.ofReal R ^ ((finrank ℝ V : ℝ) - a) * dyadicWeight (-(a - finrank ℝ V)) i :=
        tsum_le_tsum fun i => setLIntegral_compl_ball_inter_dyadicShell_le ha0 hR i
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg, complBallRpowConst]
        ring

variable (V) in
/-- The constant `(1 + 2^a) |B_1| (1 - 2^(-(n-a)))⁻¹` of the radial integral
`∫_{|z| < R} |z|^(-a) dz` for `a < n = dim V`. -/
noncomputable def ballRpowConst (a : ℝ) : ℝ≥0∞ :=
  (1 + 2 ^ a) * volume (ball (0 : V) 1) * (1 - 2 ^ (-((finrank ℝ V : ℝ) - a)))⁻¹

/-- The constant of `∫_{|z| < R} |z|^(-a) dz` is finite for `a < n`. -/
theorem ballRpowConst_ne_top {a : ℝ} (ha : a < finrank ℝ V) : ballRpowConst V a ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.two_rpow_ne_top _⟩) (volume_ball_ne_top 1))
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 ha))

/-- On the annulus `R 2^(-(i+1)) < |z| ≤ R 2^(-i)`, `|z|^(-a)` has the integral at most
`(1 + 2^a) |B_1| R^(n-a) 2^(-i(n-a))`, for every real `a`. -/
theorem setLIntegral_dyadicAnnulus_norm_rpow_neg_le (a : ℝ) {R : ℝ} (hR : 0 < R) (i : ℕ) :
    ∫⁻ z in dyadicAnnulus (V := V) R i, ‖z‖ₑ ^ (-a) ≤ (1 + 2 ^ a) * volume (ball (0 : V) 1) *
      ENNReal.ofReal R ^ ((finrank ℝ V : ℝ) - a) * dyadicWeight (-((finrank ℝ V : ℝ) - a)) i := by
  have hpt : ∀ z ∈ dyadicAnnulus (V := V) R i, ‖z‖ₑ ^ (-a) ≤
      ENNReal.ofReal (R / 2 ^ (i + 1)) ^ (-a) + ENNReal.ofReal (R / 2 ^ i) ^ (-a) := by
    rintro z ⟨hz1, hz2⟩
    rw [← ofReal_norm]
    exact ENNReal.rpow_le_rpow_add_rpow_of_le_of_le (ENNReal.ofReal_le_ofReal hz1.le)
      (ENNReal.ofReal_le_ofReal hz2) _
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.2 hR).ne'
  calc ∫⁻ z in dyadicAnnulus (V := V) R i, ‖z‖ₑ ^ (-a)
      ≤ ∫⁻ _ in dyadicAnnulus (V := V) R i,
          (ENNReal.ofReal (R / 2 ^ (i + 1)) ^ (-a) + ENNReal.ofReal (R / 2 ^ i) ^ (-a)) :=
        setLIntegral_mono measurable_const hpt
    _ = (ENNReal.ofReal (R / 2 ^ (i + 1)) ^ (-a) + ENNReal.ofReal (R / 2 ^ i) ^ (-a)) *
          volume (dyadicAnnulus (V := V) R i) := setLIntegral_const _ _
    _ ≤ (ENNReal.ofReal (R / 2 ^ (i + 1)) ^ (-a) + ENNReal.ofReal (R / 2 ^ i) ^ (-a)) *
          (ENNReal.ofReal R ^ (finrank ℝ V : ℝ) * dyadicWeight (-(finrank ℝ V : ℝ)) i *
            volume (ball (0 : V) 1)) := by
        gcongr
        exact volume_dyadicAnnulus_le hR i
    _ = _ := by
        rw [ENNReal.ofReal_div_two_pow_rpow hR, ENNReal.ofReal_div_two_pow_rpow hR, neg_neg,
          ENNReal.dyadicWeight_succ, show (finrank ℝ V : ℝ) - a = -a + finrank ℝ V by ring,
          ENNReal.rpow_add _ _ hR0 ENNReal.ofReal_ne_top,
          show -(-a + (finrank ℝ V : ℝ)) = a + -(finrank ℝ V : ℝ) by ring,
          ENNReal.dyadicWeight_add]
        ring

/-- **The radial integral over a ball**: for `a < n = dim V` and `R > 0`,
`∫_{|z| < R} |z|^(-a) dz ≤ (1 + 2^a) |B_1| (1 - 2^(-(n-a)))⁻¹ R^(n-a)`, by the dyadic annuli
`R 2^(-(i+1)) < |z| ≤ R 2^(-i)` and a geometric series; the centre is a null set for `n ≥ 1`,
and for `n = 0` the integrand vanishes. -/
theorem lintegral_ball_norm_rpow_neg_le {a : ℝ} (ha : a < finrank ℝ V) {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in ball (0 : V) R, ‖z‖ₑ ^ (-a) ≤
      ballRpowConst V a * ENNReal.ofReal R ^ ((finrank ℝ V : ℝ) - a) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have ha' : 0 < -a := by
      rw [finrank_zero_of_subsingleton, Nat.cast_zero] at ha
      linarith
    have h0 : ∀ z : V, ‖z‖ₑ ^ (-a) = 0 := fun z => by
      rw [Subsingleton.elim z 0, eNorm_zero, ENNReal.zero_rpow_of_pos ha']
    simp only [h0, lintegral_zero, zero_le]
  calc ∫⁻ z in ball (0 : V) R, ‖z‖ₑ ^ (-a)
      ≤ ∫⁻ z in closedBall (0 : V) (R / 2 ^ 0), ‖z‖ₑ ^ (-a) := by
        rw [pow_zero, div_one]
        exact lintegral_mono_set ball_subset_closedBall
    _ ≤ ‖(0 : V)‖ₑ ^ (-a) * volume {(0 : V)} +
          ∑' i, ∫⁻ z in dyadicAnnulus R (0 + i), ‖z‖ₑ ^ (-a) :=
        setLIntegral_closedBall_le_tsum_dyadicAnnulus _ R 0
    _ ≤ ∑' i, (1 + 2 ^ a) * volume (ball (0 : V) 1) *
          ENNReal.ofReal R ^ ((finrank ℝ V : ℝ) - a) *
            dyadicWeight (-((finrank ℝ V : ℝ) - a)) i := by
        rw [measure_singleton, mul_zero, zero_add]
        exact tsum_le_tsum fun i => by
          simpa only [zero_add] using setLIntegral_dyadicAnnulus_norm_rpow_neg_le a hR i
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg, ballRpowConst]
        ring

/-- **A radial integral of Lipschitz differences**: if `u(z) ≤ L |z|` and `u(z) ≤ S` for all
`z ∈ V`, `dim V = n`, then `∫ u(z)^p / |z|^a dz ≤ L^p c_1 + S^p c_2` for `p > 0` and
`a - p < n < a`, with the constants `c_1 = Rd.ballRpowConst V (a - p)` of the unit ball, where
`u^p / |z|^a ≤ L^p |z|^(-(a-p))`, and `c_2 = Rd.complBallRpowConst V a` of its complement, where
`u^p / |z|^a ≤ S^p |z|^(-a)`. -/
theorem lintegral_rpow_div_norm_rpow_le {u : V → ℝ≥0∞} {L S : ℝ≥0∞}
    (huL : ∀ z, u z ≤ L * ‖z‖ₑ) (huS : ∀ z, u z ≤ S) {p a : ℝ} (hp : 0 < p)
    (ha : (finrank ℝ V : ℝ) < a) (hap : a - p < finrank ℝ V) :
    ∫⁻ z, u z ^ p / ‖z‖ₑ ^ a ≤
      L ^ p * ballRpowConst V (a - p) + S ^ p * complBallRpowConst V a := by
  have hin : ∀ z, u z ^ p / ‖z‖ₑ ^ a ≤ L ^ p * ‖z‖ₑ ^ (-(a - p)) := fun z => by
    rcases eq_or_ne z 0 with rfl | hz
    · have h0 : u 0 = 0 := le_antisymm ((huL 0).trans (by rw [eNorm_zero, mul_zero])) zero_le
      rw [h0, ENNReal.zero_rpow_of_pos hp, ENNReal.zero_div]
      exact zero_le
    · calc u z ^ p / ‖z‖ₑ ^ a ≤ (L * ‖z‖ₑ) ^ p / ‖z‖ₑ ^ a :=
            ENNReal.div_le_div_right (ENNReal.rpow_le_rpow (huL z) hp.le) _
        _ = L ^ p * ‖z‖ₑ ^ (-(a - p)) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, mul_div_assoc, neg_sub,
              ENNReal.rpow_sub _ _ (eNorm_ne_zero.2 hz) eNorm_ne_top]
  have hout : ∀ z, u z ^ p / ‖z‖ₑ ^ a ≤ S ^ p * ‖z‖ₑ ^ (-a) := fun z => by
    rw [ENNReal.rpow_neg, ← div_eq_mul_inv]
    exact ENNReal.div_le_div_right (ENNReal.rpow_le_rpow (huS z) hp.le) _
  calc ∫⁻ z, u z ^ p / ‖z‖ₑ ^ a
      = ∫⁻ z in ball (0 : V) 1 ∪ (ball (0 : V) 1)ᶜ, u z ^ p / ‖z‖ₑ ^ a := by
        rw [union_compl_self, Measure.restrict_univ]
    _ ≤ (∫⁻ z in ball (0 : V) 1, u z ^ p / ‖z‖ₑ ^ a) +
          ∫⁻ z in (ball (0 : V) 1)ᶜ, u z ^ p / ‖z‖ₑ ^ a := lintegral_union_le _ _ _
    _ ≤ (∫⁻ z in ball (0 : V) 1, L ^ p * ‖z‖ₑ ^ (-(a - p))) +
          ∫⁻ z in (ball (0 : V) 1)ᶜ, S ^ p * ‖z‖ₑ ^ (-a) :=
        add_le_add (lintegral_mono hin) (lintegral_mono hout)
    _ = L ^ p * (∫⁻ z in ball (0 : V) 1, ‖z‖ₑ ^ (-(a - p))) +
          S ^ p * ∫⁻ z in (ball (0 : V) 1)ᶜ, ‖z‖ₑ ^ (-a) := by
        rw [lintegral_const_mul _ (measurable_eNorm.pow_const _),
          lintegral_const_mul _ (measurable_eNorm.pow_const _)]
    _ ≤ L ^ p * ballRpowConst V (a - p) + S ^ p * complBallRpowConst V a := by
        gcongr
        · simpa using lintegral_ball_norm_rpow_neg_le hap one_pos
        · simpa using lintegral_compl_ball_norm_rpow_neg_le ha one_pos

/-- **The tail part of a Gagliardo form**: for `η > 0`, `a > n = dim V` and every
`u : V → [0, ∞]`, `∫∫ u(x) 1_{|y - x| ≥ η} |y - x|^(-a) dy dx ≤ c η^(n - a) ∫ u` with
`c = Rd.complBallRpowConst V a`: the inner integral is `∫_{|z| ≥ η} |z|^(-a) dz` by translation
(`Rd.lintegral_compl_ball_norm_rpow_neg_le`). -/
theorem lintegral_lintegral_mul_indicator_le (u : V → ℝ≥0∞) {η a : ℝ} (hη : 0 < η)
    (ha : (finrank ℝ V : ℝ) < a) :
    ∫⁻ x, ∫⁻ y, u x * (ball (0 : V) η)ᶜ.indicator (fun z => ‖z‖ₑ ^ (-a)) (y - x) ≤
      complBallRpowConst V a * ENNReal.ofReal η ^ ((finrank ℝ V : ℝ) - a) * ∫⁻ x, u x := by
  have hh : Measurable ((ball (0 : V) η)ᶜ.indicator fun z => ‖z‖ₑ ^ (-a)) :=
    (measurable_eNorm.pow_const _).indicator measurableSet_ball.compl
  have hI : complBallRpowConst V a * ENNReal.ofReal η ^ ((finrank ℝ V : ℝ) - a) ≠ ∞ :=
    ENNReal.mul_ne_top (complBallRpowConst_ne_top ha)
      (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.2 hη).ne' ENNReal.ofReal_ne_top)
  have hin : ∀ x, ∫⁻ y, u x * (ball (0 : V) η)ᶜ.indicator (fun z => ‖z‖ₑ ^ (-a)) (y - x) ≤
      u x * (complBallRpowConst V a * ENNReal.ofReal η ^ ((finrank ℝ V : ℝ) - a)) := fun x => by
    have hm : Measurable fun y : V => (ball (0 : V) η)ᶜ.indicator (fun z => ‖z‖ₑ ^ (-a)) (y - x) :=
      hh.comp (measurable_id.sub measurable_const)
    rw [lintegral_const_mul _ hm,
      lintegral_sub_right_eq_self (fun z => (ball (0 : V) η)ᶜ.indicator
        (fun z => ‖z‖ₑ ^ (-a)) z) x, lintegral_indicator measurableSet_ball.compl]
    exact mul_le_mul' le_rfl (lintegral_compl_ball_norm_rpow_neg_le ha hη)
  calc _ ≤ ∫⁻ x, u x * (complBallRpowConst V a * ENNReal.ofReal η ^ ((finrank ℝ V : ℝ) - a)) :=
        lintegral_mono hin
    _ = _ := by rw [lintegral_mul_const' _ _ hI, mul_comm]

/-- The integrand `(x, y) ↦ |f(y) - f(x)|^p / |y - x|^b` of a Gagliardo form is measurable for
measurable `f`. -/
theorem measurable_slobodeckijIntegrand {f : V → ℂ} (hf : Measurable f) (p b : ℝ) :
    Measurable (Function.uncurry fun x y : V => ‖f y - f x‖ₑ ^ p / ‖y - x‖ₑ ^ b) :=
  (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).eNorm.pow_const _).div
    ((measurable_snd.sub measurable_fst).eNorm.pow_const _)

/-- **Splitting a double integral**: `∫∫ (F + G) = ∫∫ F + ∫∫ G` for an s-finite measure and `G`
jointly measurable, whatever `F` (Mathlib's `lintegral_add_right'` for the inner and the outer
integral, with `Measurable.lintegral_prod_right'`). -/
theorem lintegral_lintegral_add_right {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    (F : α → α → ℝ≥0∞) {G : α → α → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    ∫⁻ x, ∫⁻ y, (F x y + G x y) ∂μ ∂μ = ∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ + ∫⁻ x, ∫⁻ y, G x y ∂μ ∂μ := by
  have hin : ∀ x, ∫⁻ y, (F x y + G x y) ∂μ = ∫⁻ y, F x y ∂μ + ∫⁻ y, G x y ∂μ := fun x =>
    lintegral_add_right' _ (hG.comp measurable_prodMk_left).aemeasurable
  simp_rw [hin]
  exact lintegral_add_right' _ hG.lintegral_prod_right'.aemeasurable

/-- **A double integral by a pointwise bound with one-variable parts**: if
`F(x, y) ≤ T(x, y) + a(x) + a(y)` for measurable `a`, then
`∫∫ F ≤ ∫∫ T + 2 μ(univ) ∫ a` (`Rd.lintegral_lintegral_add_right`). -/
theorem lintegral_lintegral_le_add_two_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {F T : α → α → ℝ≥0∞} {a : α → ℝ≥0∞} (ha : Measurable a)
    (hF : ∀ x y, F x y ≤ T x y + a x + a y) :
    ∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ ≤ ∫⁻ x, ∫⁻ y, T x y ∂μ ∂μ + 2 * μ univ * ∫⁻ x, a x ∂μ := by
  calc ∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ ≤ ∫⁻ x, ∫⁻ y, (T x y + a x + a y) ∂μ ∂μ :=
        lintegral_mono fun x => lintegral_mono fun y => hF x y
    _ = (∫⁻ x, ∫⁻ y, T x y ∂μ ∂μ) + (∫⁻ x, ∫⁻ _, a x ∂μ ∂μ) + ∫⁻ _, ∫⁻ y, a y ∂μ ∂μ := by
        rw [lintegral_lintegral_add_right (fun x y => T x y + a x) (G := fun _ y => a y)
            (ha.comp measurable_snd),
          lintegral_lintegral_add_right T (G := fun x _ => a x) (ha.comp measurable_fst)]
    _ = _ := by
        simp only [lintegral_const, lintegral_mul_const _ ha]
        ring

/-- `∫∫ c F = c ∫∫ F` for a finite constant `c`, measurable `F` or not (Mathlib's
`lintegral_const_mul'` twice). -/
theorem lintegral_lintegral_const_mul' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {c : ℝ≥0∞} (hc : c ≠ ∞) (F : α → α → ℝ≥0∞) :
    ∫⁻ x, ∫⁻ y, c * F x y ∂μ ∂μ = c * ∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ := by
  rw [lintegral_congr fun x => lintegral_const_mul' c (F x) hc, lintegral_const_mul' _ _ hc]

/-! ### Averaging the differences over a ball -/

/-- **Splitting a step**: `‖Δ_h f‖_p ≤ ‖Δ_{h-z} f‖_p + ‖Δ_z f‖_p`, from
`Δ_h f = (Δ_{h-z} f)(· + z) + Δ_z f` and the invariance of `L_p` norms under translations. -/
theorem eLpNorm_fwdDiff_le_add {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) (h z : V) :
    eLpNorm (fwdDiff h f) p volume ≤
      eLpNorm (fwdDiff (h - z) f) p volume + eLpNorm (fwdDiff z f) p volume := by
  have hm : AEStronglyMeasurable (fwdDiff (h - z) f) volume := by
    simpa using aestronglyMeasurable_higherDiff hf 1 (h - z)
  have heq : fwdDiff h f = (fun x => fwdDiff (h - z) f (x + z)) + fwdDiff z f := by
    funext x
    simp only [fwdDiff, Pi.add_apply]
    rw [show x + z + (h - z) = x + h by abel]
    ring
  rw [heq]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_comp_add_right hm p z]

/-- The `p`-th power of the splitting: `‖Δ_h f‖_p^p ≤ 2^(p-1) (‖Δ_{h-z} f‖_p^p + ‖Δ_z f‖_p^p)`
for `1 ≤ p < ∞` (Mathlib's `ENNReal.rpow_add_le_mul_rpow_add_rpow`). -/
theorem eLpNorm_fwdDiff_rpow_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) (h z : V) :
    eLpNorm (fwdDiff h f) p volume ^ p.toReal ≤ 2 ^ (p.toReal - 1) *
      (eLpNorm (fwdDiff (h - z) f) p volume ^ p.toReal +
        eLpNorm (fwdDiff z f) p volume ^ p.toReal) :=
  (ENNReal.rpow_le_rpow (eLpNorm_fwdDiff_le_add hp1 hf h z) ENNReal.toReal_nonneg).trans
    (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (ENNReal.one_le_toReal_of_one_le hp1 hp))

/-- `∫_{|z| < t} G(h - z) dz ≤ ∫_{|z| < 2t} G(z) dz` for `|h| ≤ t` and every `G : V → [0, ∞]`:
the reflection `z ↦ h - z` preserves Lebesgue measure (Mathlib's `lintegral_sub_left_eq_self`)
and maps the ball of radius `t` into the ball of radius `2t`. -/
theorem setLIntegral_ball_comp_sub_le (G : V → ℝ≥0∞) {h : V} {t : ℝ} (hh : ‖h‖ ≤ t) :
    ∫⁻ z in ball (0 : V) t, G (h - z) ≤ ∫⁻ z in ball (0 : V) (2 * t), G z := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  conv_lhs => rw [← lintegral_sub_left_eq_self _ h]
  refine lintegral_mono fun w => ?_
  by_cases hw : h - w ∈ ball (0 : V) t
  · have hw2 : w ∈ ball (0 : V) (2 * t) := by
      rw [mem_ball_zero_iff] at hw ⊢
      calc ‖w‖ = ‖h - (h - w)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖h‖ + ‖h - w‖ := norm_sub_le _ _
        _ < 2 * t := by linarith
    rw [indicator_of_mem hw, indicator_of_mem hw2, sub_sub_cancel]
  · rw [indicator_of_notMem hw]
    exact zero_le

/-- **Averaging over a ball**: for `1 ≤ p < ∞`, `|h| ≤ t` and `t > 0`,
`‖Δ_h f‖_p^p ≤ 2^p |B(0,t)|⁻¹ ∫_{|z| < 2t} ‖Δ_z f‖_p^p dz`. The splitting
`‖Δ_h f‖_p^p ≤ 2^(p-1) (‖Δ_{h-z} f‖_p^p + ‖Δ_z f‖_p^p)` is averaged over `|z| < t`. -/
theorem eLpNorm_fwdDiff_rpow_le_average {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : V → ℂ}
    (hf : AEStronglyMeasurable f volume) {h : V} {t : ℝ} (hh : ‖h‖ ≤ t) (ht : 0 < t) :
    eLpNorm (fwdDiff h f) p volume ^ p.toReal ≤ 2 ^ p.toReal * (volume (ball (0 : V) t))⁻¹ *
      ∫⁻ z in ball (0 : V) (2 * t), eLpNorm (fwdDiff z f) p volume ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hmeas := measurable_eLpNorm_fwdDiff_rpow hp0 hp hf
  have hv0 : volume (ball (0 : V) t) ≠ 0 := volume_ball_ne_zero ht
  have hvt : volume (ball (0 : V) t) ≠ ∞ := volume_ball_ne_top t
  have h2 : (2 : ℝ≥0∞) ^ (p.toReal - 1) * 2 = 2 ^ p.toReal := by
    have h := ENNReal.two_rpow_mul_two_rpow (p.toReal - 1) 1
    rwa [ENNReal.rpow_one, sub_add_cancel] at h
  have hkey : volume (ball (0 : V) t) * eLpNorm (fwdDiff h f) p volume ^ p.toReal ≤
      2 ^ p.toReal * ∫⁻ z in ball (0 : V) (2 * t), eLpNorm (fwdDiff z f) p volume ^ p.toReal := by
    calc volume (ball (0 : V) t) * eLpNorm (fwdDiff h f) p volume ^ p.toReal
        = ∫⁻ _ in ball (0 : V) t, eLpNorm (fwdDiff h f) p volume ^ p.toReal := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ z in ball (0 : V) t, 2 ^ (p.toReal - 1) *
            (eLpNorm (fwdDiff (h - z) f) p volume ^ p.toReal +
              eLpNorm (fwdDiff z f) p volume ^ p.toReal) :=
          lintegral_mono fun z => eLpNorm_fwdDiff_rpow_le hp1 hp hf h z
      _ = 2 ^ (p.toReal - 1) *
            ((∫⁻ z in ball (0 : V) t, eLpNorm (fwdDiff (h - z) f) p volume ^ p.toReal) +
              ∫⁻ z in ball (0 : V) t, eLpNorm (fwdDiff z f) p volume ^ p.toReal) := by
          rw [lintegral_const_mul' _ _ (ENNReal.two_rpow_ne_top _), lintegral_add_right _ hmeas]
      _ ≤ 2 ^ (p.toReal - 1) *
            ((∫⁻ z in ball (0 : V) (2 * t), eLpNorm (fwdDiff z f) p volume ^ p.toReal) +
              ∫⁻ z in ball (0 : V) (2 * t), eLpNorm (fwdDiff z f) p volume ^ p.toReal) := by
          exact mul_le_mul_right (add_le_add (setLIntegral_ball_comp_sub_le
            (fun w => eLpNorm (fwdDiff w f) p volume ^ p.toReal) hh)
            (lintegral_mono_set (ball_subset_ball (x := (0 : V)) (show t ≤ 2 * t by linarith)))) _
      _ = _ := by rw [← two_mul, ← mul_assoc, h2]
  calc eLpNorm (fwdDiff h f) p volume ^ p.toReal
      = (volume (ball (0 : V) t))⁻¹ *
          (volume (ball (0 : V) t) * eLpNorm (fwdDiff h f) p volume ^ p.toReal) :=
        (ENNReal.inv_mul_cancel_left hv0 hvt).symm
    _ ≤ (volume (ball (0 : V) t))⁻¹ * (2 ^ p.toReal *
          ∫⁻ z in ball (0 : V) (2 * t), eLpNorm (fwdDiff z f) p volume ^ p.toReal) := by
        gcongr
    _ = _ := by ring

/-! ### The modulus of smoothness by the Gagliardo form -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The dyadic modulus by an average**: for `1 ≤ p < ∞`,
`ω_1(f, 2^(-k))_p^p ≤ 2^p |B(0, 2^(-k))|⁻¹ ∫_{|z| < 2^(1-k)} ‖Δ_z f‖_p^p dz`
(`Rd.eLpNorm_fwdDiff_rpow_le_average` for every step of the supremum). -/
theorem lpModulus_rpow_le_average (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure V)) (k : ℕ) :
    lpModulus p 1 f k ^ p.toReal ≤ 2 ^ p.toReal * (volume (ball (0 : V) (1 / 2 ^ k)))⁻¹ *
      ∫⁻ z in ball (0 : V) (2 * (1 / 2 ^ k)),
        eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [← ENNReal.le_rpow_inv_iff hP]
  change modulus volume 1 p (f : V → ℂ) (1 / 2 ^ k) ≤ _
  refine iSup₂_le fun h hh => ?_
  rw [ENNReal.le_rpow_inv_iff hP]
  exact eLpNorm_fwdDiff_rpow_le_average Fact.out hp (Lp.aestronglyMeasurable f) hh
    (by positivity)

/-- `|B(0, 2^(-k))|⁻¹ = 2^(kn) |B_1|⁻¹`. -/
theorem inv_volume_ball_one_div_two_pow (k : ℕ) :
    (volume (ball (0 : V) (1 / 2 ^ k)))⁻¹ =
      dyadicWeight (finrank ℝ V : ℝ) k * (volume (ball (0 : V) 1))⁻¹ := by
  rw [volume_ball_div_two_pow one_pos k 0, one_pow, ENNReal.ofReal_one, one_mul,
    ENNReal.mul_inv (Or.inl (volume_ball_ne_zero one_pos)) (Or.inl (volume_ball_ne_top 1)),
    ENNReal.dyadicWeight_neg, inv_inv, mul_comm]

/-- **The weighted dyadic modulus by an integral over a ball**:
`(2^(ks) ω_1(f, 2^(-k))_p)^p ≤ 2^p |B_1|⁻¹ 2^(k(n+sp)) ∫_{|z| ≤ 2^(1-k)} ‖Δ_z f‖_p^p dz`. -/
theorem dyadicWeight_mul_lpModulus_rpow_le (hp : p ≠ ∞) (s : ℝ)
    (f : Lp ℂ p (volume : Measure V)) (k : ℕ) :
    (dyadicWeight s k * lpModulus p 1 f k) ^ p.toReal ≤
      2 ^ p.toReal * (volume (ball (0 : V) 1))⁻¹ *
        (dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) k *
          ∫⁻ z in closedBall (0 : V) (2 / 2 ^ k),
            eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal) := by
  have hsub : ball (0 : V) (2 * (1 / 2 ^ k)) ⊆ closedBall (0 : V) (2 / 2 ^ k) := by
    rw [show 2 * (1 / 2 ^ k : ℝ) = 2 / 2 ^ k by ring]
    exact ball_subset_closedBall
  rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ENNReal.dyadicWeight_rpow]
  calc dyadicWeight (s * p.toReal) k * lpModulus p 1 f k ^ p.toReal
      ≤ dyadicWeight (s * p.toReal) k * (2 ^ p.toReal *
          (volume (ball (0 : V) (1 / 2 ^ k)))⁻¹ * ∫⁻ z in closedBall (0 : V) (2 / 2 ^ k),
            eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal) :=
        mul_le_mul_right ((lpModulus_rpow_le_average hp f k).trans
          (mul_le_mul_right (lintegral_mono_set hsub) _)) _
    _ = _ := by
        rw [inv_volume_ball_one_div_two_pow, ENNReal.dyadicWeight_add]
        ring

/-- On the annulus `2^(-j) < |z| ≤ 2^(1-j)` the weight `2^(jb)` is at most `2^b |z|^(-b)`, so
`2^(jb) ∫_{annulus} G ≤ 2^b ∫_{annulus} G(z) / |z|^b` for `b ≥ 0`. -/
theorem dyadicWeight_mul_setLIntegral_dyadicAnnulus_le (G : V → ℝ≥0∞) {b : ℝ} (hb : 0 ≤ b)
    (j : ℕ) : dyadicWeight b j * ∫⁻ z in dyadicAnnulus 2 j, G z ≤
      2 ^ b * ∫⁻ z in dyadicAnnulus 2 j, G z / ‖z‖ₑ ^ b := by
  rw [← lintegral_const_mul' _ _ (ENNReal.dyadicWeight_ne_top b j),
    ← lintegral_const_mul' _ _ (ENNReal.two_rpow_ne_top _)]
  refine setLIntegral_mono' (measurableSet_dyadicAnnulus 2 j) fun z hz => ?_
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (by positivity) hz.1
  have hn0 : ‖z‖ₑ ^ b ≠ 0 :=
    (ENNReal.rpow_pos (eNorm_pos.2 (norm_pos_iff.1 hz0)) eNorm_ne_top).ne'
  have hnt : ‖z‖ₑ ^ b ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hb eNorm_ne_top
  have hle : dyadicWeight b j * ‖z‖ₑ ^ b ≤ 2 ^ b := by
    calc dyadicWeight b j * ‖z‖ₑ ^ b ≤ dyadicWeight b j * ENNReal.ofReal (2 / 2 ^ j) ^ b := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hz.2
      _ = 2 ^ b := by
          rw [ENNReal.ofReal_div_two_pow_rpow two_pos, ENNReal.ofReal_ofNat, mul_left_comm,
            ENNReal.dyadicWeight_mul_neg_self, mul_one]
  have hdiv : dyadicWeight b j ≤ 2 ^ b / ‖z‖ₑ ^ b :=
    (ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl hnt)).2 hle
  calc dyadicWeight b j * G z = G z * dyadicWeight b j := mul_comm _ _
    _ ≤ G z * (2 ^ b / ‖z‖ₑ ^ b) := by gcongr
    _ = 2 ^ b * (G z / ‖z‖ₑ ^ b) := by
        simp only [div_eq_mul_inv]
        ring

/-- **Hardy's inequality for the balls**: for `G : V → [0, ∞]` with `G(0) = 0` and `b > 0`,
`∑_k 2^(kb) ∫_{|z| ≤ 2^(1-k)} G ≤ (1 - 2^(-b))⁻¹ 2^b ∫ G(z) / |z|^b dz`: each ball is the union
of the annuli `2^(-j) < |z| ≤ 2^(1-j)`, `j ≥ k`, and `ENNReal.hardy_tail_le` sums the tails. -/
theorem tsum_dyadicWeight_mul_setLIntegral_closedBall_le {G : V → ℝ≥0∞} (hG : G 0 = 0) {b : ℝ}
    (hb : 0 < b) : ∑' k, dyadicWeight b k * ∫⁻ z in closedBall (0 : V) (2 / 2 ^ k), G z ≤
      (1 - 2 ^ (-b))⁻¹ * 2 ^ b * ∫⁻ z, G z / ‖z‖ₑ ^ b := by
  calc ∑' k, dyadicWeight b k * ∫⁻ z in closedBall (0 : V) (2 / 2 ^ k), G z
      ≤ ∑' k, dyadicWeight b k * ∑' i, ∫⁻ z in dyadicAnnulus 2 (k + i), G z :=
        tsum_le_tsum fun k =>
          mul_le_mul_right (setLIntegral_closedBall_le_tsum_dyadicAnnulus_of_zero hG 2 k) _
    _ = lqNorm 1 (fun k => dyadicWeight b k *
          ∑' i, (fun j => ∫⁻ z in dyadicAnnulus (V := V) 2 j, G z) (k + i)) :=
        (ENNReal.lqNorm_one _).symm
    _ ≤ (1 - 2 ^ (-b))⁻¹ * lqNorm 1 (fun k => dyadicWeight b k *
          ∫⁻ z in dyadicAnnulus (V := V) 2 k, G z) :=
        ENNReal.hardy_tail_le (q := 1) le_rfl b (fun j => ∫⁻ z in dyadicAnnulus (V := V) 2 j, G z)
    _ = (1 - 2 ^ (-b))⁻¹ * ∑' k, dyadicWeight b k * ∫⁻ z in dyadicAnnulus (V := V) 2 k, G z := by
        rw [ENNReal.lqNorm_one]
    _ ≤ (1 - 2 ^ (-b))⁻¹ * ∑' k, 2 ^ b * ∫⁻ z in dyadicAnnulus (V := V) 2 k, G z / ‖z‖ₑ ^ b := by
        exact mul_le_mul_right (tsum_le_tsum fun k =>
          dyadicWeight_mul_setLIntegral_dyadicAnnulus_le G hb.le k) _
    _ = (1 - 2 ^ (-b))⁻¹ * 2 ^ b *
          ∑' k, ∫⁻ z in dyadicAnnulus (V := V) 2 k, G z / ‖z‖ₑ ^ b := by
        rw [ENNReal.tsum_mul_left, mul_assoc]
    _ ≤ _ := by
        gcongr
        exact tsum_setLIntegral_dyadicAnnulus_le _ zero_le_two

variable (V) in
/-- The constant `2^p |B_1|⁻¹ (1 - 2^(-(n+sp)))⁻¹ 2^(n+sp)` of
`‖(2^(ks) ω_1(f, 2^(-k))_p)_k‖_{ℓ_p}^p ≤ C ∫∫ |f(y) - f(x)|^p / |y - x|^(n+sp) dy dx`. -/
noncomputable def slobodeckijConstUpper (p : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  2 ^ p.toReal * (volume (ball (0 : V) 1))⁻¹ *
    (1 - 2 ^ (-((finrank ℝ V : ℝ) + s * p.toReal)))⁻¹ * 2 ^ ((finrank ℝ V : ℝ) + s * p.toReal)

omit [Fact (1 ≤ p)] in
/-- The constant `Rd.slobodeckijConstUpper V p s` is finite for `0 < p < ∞` and `s > 0`. -/
theorem slobodeckijConstUpper_ne_top (hp0 : p ≠ 0) (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) :
    slobodeckijConstUpper V p s ≠ ∞ := by
  have hb : 0 < (finrank ℝ V : ℝ) + s * p.toReal :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos hs (ENNReal.toReal_pos hp0 hp))
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_)
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top hb)) ?_
  · exact ENNReal.two_rpow_ne_top _
  · exact ENNReal.inv_ne_top.2 (volume_ball_ne_zero one_pos)
  · exact ENNReal.two_rpow_ne_top _

/-- **The first-difference Besov norm by the Gagliardo form**: for `1 ≤ p < ∞`, `s > 0` and
`f ∈ L_p(V)`,
`‖(2^(ks) ω_1(f, 2^(-k))_p)_k‖_{ℓ_p}^p ≤ C ∫∫ |f(y) - f(x)|^p / |y - x|^(n+sp) dy dx`
with `C = Rd.slobodeckijConstUpper V p s`. -/
theorem lqNorm_modulus_rpow_le_slobodeckijForm (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    (f : Lp ℂ p (volume : Measure V)) :
    lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 f k) ^ p.toReal ≤
      slobodeckijConstUpper V p s * slobodeckijForm p s (f : V → ℂ) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hb : 0 < (finrank ℝ V : ℝ) + s * p.toReal :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos hs (ENNReal.toReal_pos hp0 hp))
  calc lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 f k) ^ p.toReal
      = ∑' k, (dyadicWeight s k * lpModulus p 1 f k) ^ p.toReal := ENNReal.lqNorm_rpow hp0 hp _
    _ ≤ ∑' k, 2 ^ p.toReal * (volume (ball (0 : V) 1))⁻¹ *
          (dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) k *
            ∫⁻ z in closedBall (0 : V) (2 / 2 ^ k),
              eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal) :=
        tsum_le_tsum fun k => dyadicWeight_mul_lpModulus_rpow_le hp s f k
    _ = 2 ^ p.toReal * (volume (ball (0 : V) 1))⁻¹ *
          ∑' k, dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) k *
            ∫⁻ z in closedBall (0 : V) (2 / 2 ^ k),
              eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal := ENNReal.tsum_mul_left
    _ ≤ 2 ^ p.toReal * (volume (ball (0 : V) 1))⁻¹ *
          ((1 - 2 ^ (-((finrank ℝ V : ℝ) + s * p.toReal)))⁻¹ *
            2 ^ ((finrank ℝ V : ℝ) + s * p.toReal) *
            ∫⁻ z, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
              ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)) := by
        gcongr
        exact tsum_dyadicWeight_mul_setLIntegral_closedBall_le
          (eLpNorm_fwdDiff_zero_rpow hp0 hp _) hb
    _ = _ := by
        rw [slobodeckijForm_eq_lintegral_eLpNorm hp0 hp s (Lp.aestronglyMeasurable f),
          slobodeckijConstUpper]
        ring

/-! ### The Gagliardo form by the modulus of smoothness -/

omit [Fact (1 ≤ p)] in
/-- **One annulus of the Gagliardo form**: for `s ≥ 0`, on `2^(-(i+1)) < |z| ≤ 2^(-i)`,
`∫ ‖Δ_z f‖_p^p / |z|^(n+sp) dz ≤ 2^(n+sp) |B_1| (2^(is) ω_1(f, 2^(-i))_p)^p`, since there
`‖Δ_z f‖_p ≤ ω_1(f, 2^(-i))_p` and `|z|^(-(n+sp)) ≤ 2^((i+1)(n+sp))`. -/
theorem setLIntegral_dyadicAnnulus_le_lpModulus {s : ℝ} (hs : 0 ≤ s)
    (f : Lp ℂ p (volume : Measure V)) (i : ℕ) :
    ∫⁻ z in dyadicAnnulus 1 i, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
      ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) ≤
        2 ^ ((finrank ℝ V : ℝ) + s * p.toReal) * volume (ball (0 : V) 1) *
          (dyadicWeight s i * lpModulus p 1 f i) ^ p.toReal := by
  have hP0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ (finrank ℝ V : ℝ) + s * p.toReal := by positivity
  have hpt : ∀ z ∈ dyadicAnnulus (V := V) 1 i,
      eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
        ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) ≤ lpModulus p 1 f i ^ p.toReal *
          dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) (i + 1) := by
    intro z hz
    have h1 : eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal ≤
        lpModulus p 1 f i ^ p.toReal :=
      ENNReal.rpow_le_rpow (eLpNorm_higherDiff_le_modulus (μ := volume) (r := 1) hz.2) hP0
    have h2 : (‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal))⁻¹ ≤
        dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) (i + 1) := by
      rw [← inv_inv (dyadicWeight _ (i + 1)), ← ENNReal.dyadicWeight_neg, ENNReal.inv_le_inv]
      calc dyadicWeight (-((finrank ℝ V : ℝ) + s * p.toReal)) (i + 1)
          = ENNReal.ofReal (1 / 2 ^ (i + 1)) ^ ((finrank ℝ V : ℝ) + s * p.toReal) := by
            rw [ENNReal.ofReal_div_two_pow_rpow one_pos, ENNReal.ofReal_one, ENNReal.one_rpow,
              one_mul]
        _ ≤ ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) := by
            rw [← ofReal_norm]
            exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hz.1.le) hb
    rw [div_eq_mul_inv]
    exact mul_le_mul' h1 h2
  calc ∫⁻ z in dyadicAnnulus 1 i, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
        ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)
      ≤ ∫⁻ _ in dyadicAnnulus (V := V) 1 i, lpModulus p 1 f i ^ p.toReal *
          dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) (i + 1) :=
        setLIntegral_mono' (measurableSet_dyadicAnnulus 1 i) hpt
    _ = lpModulus p 1 f i ^ p.toReal * dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) (i + 1) *
          volume (dyadicAnnulus (V := V) 1 i) := setLIntegral_const _ _
    _ ≤ lpModulus p 1 f i ^ p.toReal * dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) (i + 1) *
          (ENNReal.ofReal 1 ^ (finrank ℝ V : ℝ) * dyadicWeight (-(finrank ℝ V : ℝ)) i *
            volume (ball (0 : V) 1)) := by
        gcongr
        exact volume_dyadicAnnulus_le one_pos i
    _ = _ := by
        rw [ENNReal.ofReal_one, ENNReal.one_rpow, one_mul, ENNReal.dyadicWeight_succ,
          ENNReal.mul_rpow_of_nonneg _ _ hP0, ENNReal.dyadicWeight_rpow,
          show dyadicWeight (s * p.toReal) i = dyadicWeight ((finrank ℝ V : ℝ) + s * p.toReal) i *
            dyadicWeight (-(finrank ℝ V : ℝ)) i by
            rw [← ENNReal.dyadicWeight_add]
            congr 1
            ring]
        ring

/-- **The tail of the Gagliardo form**: for `1 ≤ p < ∞` and `s > 0`,
`∫_{|z| ≥ 1} ‖Δ_z f‖_p^p / |z|^(n+sp) dz ≤ 2^p C ‖f‖_p^p` with
`C = Rd.complBallRpowConst V (n + sp)`, since `‖Δ_z f‖_p ≤ 2 ‖f‖_p`. -/
theorem setLIntegral_compl_ball_le_enorm {s : ℝ} (hs : 0 < s) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure V)) :
    ∫⁻ z in (ball (0 : V) 1)ᶜ, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
      ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) ≤
        2 ^ p.toReal * complBallRpowConst V ((finrank ℝ V : ℝ) + s * p.toReal) *
          ‖f‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hpt : ∀ z : V, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
      ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) ≤
        (2 * ‖f‖ₑ) ^ p.toReal * ‖z‖ₑ ^ (-((finrank ℝ V : ℝ) + s * p.toReal)) := fun z => by
    rw [div_eq_mul_inv, ← ENNReal.rpow_neg]
    gcongr
    have h := eLpNorm_higherDiff_le (Lp.aestronglyMeasurable f) (Fact.out : 1 ≤ p) 1 z
    rw [pow_one, ← Lp.eNorm_def] at h
    exact h
  have hlt : (finrank ℝ V : ℝ) < (finrank ℝ V : ℝ) + s * p.toReal :=
    lt_add_of_pos_right _ (mul_pos hs (ENNReal.toReal_pos hp0 hp))
  calc ∫⁻ z in (ball (0 : V) 1)ᶜ, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
        ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)
      ≤ ∫⁻ z in (ball (0 : V) 1)ᶜ,
          (2 * ‖f‖ₑ) ^ p.toReal * ‖z‖ₑ ^ (-((finrank ℝ V : ℝ) + s * p.toReal)) :=
        lintegral_mono hpt
    _ = (2 * ‖f‖ₑ) ^ p.toReal *
          ∫⁻ z in (ball (0 : V) 1)ᶜ, ‖z‖ₑ ^ (-((finrank ℝ V : ℝ) + s * p.toReal)) :=
        lintegral_const_mul _ (measurable_eNorm.pow_const _)
    _ ≤ (2 * ‖f‖ₑ) ^ p.toReal * (complBallRpowConst V ((finrank ℝ V : ℝ) + s * p.toReal) *
          ENNReal.ofReal 1 ^ ((finrank ℝ V : ℝ) - ((finrank ℝ V : ℝ) + s * p.toReal))) := by
        gcongr
        exact lintegral_compl_ball_norm_rpow_neg_le hlt one_pos
    _ = _ := by
        rw [ENNReal.ofReal_one, ENNReal.one_rpow, mul_one, ENNReal.mul_rpow_of_nonneg _ _ hP0]
        ring

variable (V) in
/-- The constant `2^(n+sp) |B_1| + 2^p Rd.complBallRpowConst V (n + sp)` of the bound of the
Gagliardo form by `‖f‖_p^p + ‖(2^(ks) ω_1(f, 2^(-k))_p)_k‖_{ℓ_p}^p` (`Rd.slobodeckijForm_le`). -/
noncomputable def slobodeckijConstLower (p : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  2 ^ ((finrank ℝ V : ℝ) + s * p.toReal) * volume (ball (0 : V) 1) +
    2 ^ p.toReal * complBallRpowConst V ((finrank ℝ V : ℝ) + s * p.toReal)

omit [Fact (1 ≤ p)] in
/-- The constant `Rd.slobodeckijConstLower V p s` is finite for `0 < p < ∞` and `s > 0`. -/
theorem slobodeckijConstLower_ne_top (hp0 : p ≠ 0) (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) :
    slobodeckijConstLower V p s ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.two_rpow_ne_top _) (volume_ball_ne_top 1),
    ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top _)
      (complBallRpowConst_ne_top
        (lt_add_of_pos_right _ (mul_pos hs (ENNReal.toReal_pos hp0 hp))))⟩

/-- **The Gagliardo form by the first-difference Besov norm**: for `1 ≤ p < ∞`, `s > 0` and
`f ∈ L_p(V)`,
`∫∫ |f(y) - f(x)|^p / |y - x|^(n+sp) dy dx ≤ C (‖f‖_p^p + ‖(2^(ks) ω_1(f, 2^(-k))_p)_k‖_{ℓ_p}^p)`
with `C = Rd.slobodeckijConstLower V p s`: the steps `|z| ≤ 1` are sorted into the dyadic annuli,
and the steps `|z| ≥ 1` give the tail. -/
theorem slobodeckijForm_le (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (f : Lp ℂ p (volume : Measure V)) :
    slobodeckijForm p s (f : V → ℂ) ≤ slobodeckijConstLower V p s *
      (‖f‖ₑ ^ p.toReal + lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 f k) ^ p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hF0 : eLpNorm (fwdDiff (0 : V) (f : V → ℂ)) p volume ^ p.toReal /
      ‖(0 : V)‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) = 0 := by
    rw [eLpNorm_fwdDiff_zero_rpow hp0 hp, ENNReal.zero_div]
  have huniv : closedBall (0 : V) 1 ∪ (ball (0 : V) 1)ᶜ = univ :=
    eq_univ_of_forall fun z => by
      by_cases hz : z ∈ ball (0 : V) 1
      · exact Or.inl (ball_subset_closedBall hz)
      · exact Or.inr hz
  have hA : ∫⁻ z in closedBall (0 : V) 1, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
      ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) ≤
        2 ^ ((finrank ℝ V : ℝ) + s * p.toReal) * volume (ball (0 : V) 1) *
          lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 f k) ^ p.toReal := by
    calc ∫⁻ z in closedBall (0 : V) 1, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
          ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)
        ≤ ∑' i, ∫⁻ z in dyadicAnnulus 1 i, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
            ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) := by
          simpa only [pow_zero, div_one, zero_add] using
            setLIntegral_closedBall_le_tsum_dyadicAnnulus_of_zero (G := fun z =>
              eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
                ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)) hF0 1 0
      _ ≤ ∑' i, 2 ^ ((finrank ℝ V : ℝ) + s * p.toReal) * volume (ball (0 : V) 1) *
            (dyadicWeight s i * lpModulus p 1 f i) ^ p.toReal :=
          tsum_le_tsum fun i => setLIntegral_dyadicAnnulus_le_lpModulus hs.le f i
      _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.lqNorm_rpow hp0 hp]
  rw [slobodeckijForm_eq_lintegral_eLpNorm hp0 hp s (Lp.aestronglyMeasurable f)]
  calc ∫⁻ z, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
        ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)
      = ∫⁻ z in closedBall (0 : V) 1 ∪ (ball (0 : V) 1)ᶜ,
          eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
            ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) := by rw [huniv, Measure.restrict_univ]
    _ ≤ (∫⁻ z in closedBall (0 : V) 1, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
            ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal)) +
          ∫⁻ z in (ball (0 : V) 1)ᶜ, eLpNorm (fwdDiff z (f : V → ℂ)) p volume ^ p.toReal /
            ‖z‖ₑ ^ ((finrank ℝ V : ℝ) + s * p.toReal) := lintegral_union_le _ _ _
    _ ≤ 2 ^ ((finrank ℝ V : ℝ) + s * p.toReal) * volume (ball (0 : V) 1) *
          lqNorm p (fun k => dyadicWeight s k * lpModulus p 1 f k) ^ p.toReal +
        2 ^ p.toReal * complBallRpowConst V ((finrank ℝ V : ℝ) + s * p.toReal) *
          ‖f‖ₑ ^ p.toReal := add_le_add hA (setLIntegral_compl_ball_le_enorm hs hp f)
    _ ≤ _ := by
        rw [slobodeckijConstLower, add_mul, mul_add, mul_add]
        exact add_le_add le_add_self le_self_add

/-! ### Sobolev–Slobodeckij spaces are Besov spaces -/

/-- **`W^{s,p} = B^s_{p,p}` for `0 < s < 1`**: for `1 ≤ p < ∞` and `f ∈ L_p(V)`, the Gagliardo
form `∫∫ |f(y) - f(x)|^p / |y - x|^(n+sp) dy dx` is finite if and only if `f` lies in the
approximation space `A^s_p` of the band-limited scheme, that is, in `B^s_{p,p}(V)`
(`Rd.memApprox_bandScheme_iff_modulus` with differences of order `1`). -/
theorem slobodeckijForm_lt_top_iff_memApprox (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (f : Lp ℂ p (volume : Measure V)) :
    slobodeckijForm p s (f : V → ℂ) < ∞ ↔ (bandScheme hp).MemApprox s p f := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [memApprox_bandScheme_iff_modulus hp hs.le (r := 1) (by exact_mod_cast hs1) Fact.out f]
  constructor
  · intro h
    refine ENNReal.add_lt_top.2 ⟨eNorm_lt_top, ?_⟩
    rw [← ENNReal.rpow_lt_top_iff_of_pos hP]
    exact (lqNorm_modulus_rpow_le_slobodeckijForm hp hs f).trans_lt
      (ENNReal.mul_lt_top (slobodeckijConstUpper_ne_top hp0 hp hs).lt_top h)
  · intro h
    have hL := (ENNReal.add_lt_top.1 h).2
    refine (slobodeckijForm_le hp hs f).trans_lt (ENNReal.mul_lt_top
      (slobodeckijConstLower_ne_top hp0 hp hs).lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩))
    · exact ENNReal.rpow_lt_top_of_nonneg hP.le eNorm_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg hP.le hL.ne

end Rd
