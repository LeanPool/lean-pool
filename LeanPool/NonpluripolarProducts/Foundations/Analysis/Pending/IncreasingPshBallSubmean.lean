/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscSupremumRecovery
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PSHD.Measurability
public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Ball submeans for an increasing limit of disc-PSH potentials

The pointwise supremum `⨆ j, u j` of an increasing sequence of disc-PSH
potentials is in general not upper semicontinuous, so it is not itself a
plurisubharmonic function; only its upper semicontinuous regularization is
(`FirstPass.plurisubharmonicOn_uscRegularization_sSup`).  It does however
inherit the *ball submean inequality* of the members, in the nonnegative
deficit normalization the project uses (`DiscPshOn.ball_deficit_le`).

This is the first analytic step towards the Lebesgue-a.e. identity
`uscRegularization (⨆ j, u j) = ⨆ j, u j`, which is one of the inputs the
Guan--Zhou strong openness argument needs (see
`Pending/StrongOpennessRegularRoute.lean`).

The passage to the limit is on the *right* of the inequality: the integrand
only decreases when `u j` is replaced by the supremum, while the central value
`((C : EReal) - u j a).toENNReal` decreases to `((C : EReal) - ⨆ j, u j a).toENNReal`
along the sequence.  Continuity of `x ↦ ((C : EReal) - x).toENNReal`, which
holds at *every* extended real because the subtracted constant is finite, is
what makes the limit legitimate at poles and at `⊤` alike.
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Subtracting an extended real from a finite constant and truncating below
at `0` is continuous everywhere: the excluded pairs for extended addition are
`(⊥, ⊤)` and `(⊤, ⊥)`, and a real constant is neither. -/
theorem continuousAt_coe_sub_toENNReal (C : ℝ) (y : EReal) :
    ContinuousAt (fun x : EReal => ((C : EReal) - x).toENNReal) y := by
  have hsub : ContinuousAt (fun x : EReal => (C : EReal) - x) y := by
    have hcomp : (fun x : EReal => (C : EReal) - x) =
        (fun p : EReal × EReal => p.1 + p.2) ∘ (fun x : EReal => ((C : EReal), -x)) := by
      funext x
      rfl
    rw [hcomp]
    refine ContinuousAt.comp ?_ ?_
    · exact EReal.continuousAt_add (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))
    · exact continuousAt_const.prodMk (continuous_neg (G := EReal)).continuousAt
  exact hsub.ereal_toENNReal

/-- Along an increasing sequence the normalized deficit at a point converges
to the deficit of the supremum. -/
theorem tendsto_coe_sub_iSup_toENNReal {C : ℝ} {b : ℕ → EReal} (hb : Monotone b) :
    Tendsto (fun j => ((C : EReal) - b j).toENNReal) atTop
      (𝓝 (((C : EReal) - ⨆ j, b j).toENNReal)) :=
  (continuousAt_coe_sub_toENNReal C (⨆ j, b j)).tendsto.comp (tendsto_atTop_iSup hb)

/-- The pointwise supremum of an increasing sequence of disc-PSH potentials
satisfies the ball submean inequality in deficit form, with the same constant
as its members.  No upper semicontinuity of the supremum is used or needed. -/
theorem ball_deficit_le_of_monotone_iSup
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
    {u : ℕ → E → EReal} {U : Set E} (hu : ∀ j, DiscPshOn (u j) U)
    (μ : Measure E) [μ.IsAddHaarMeasure] (a : E) (R C : ℝ) (hBU : ball a R ⊆ U)
    (hC : ∀ j, ∀ y ∈ ball a R, u j y ≤ (C : EReal))
    (ha : Monotone fun j => u j a) :
    ∫⁻ x in ball a R, ((C : EReal) - ⨆ j, u j x).toENNReal ∂μ ≤
      μ (ball 0 R) * ((C : EReal) - ⨆ j, u j a).toENNReal := by
  have hstep : ∀ j : ℕ,
      (∫⁻ x in ball a R, ((C : EReal) - ⨆ k, u k x).toENNReal ∂μ) ≤
        μ (ball 0 R) * ((C : EReal) - u j a).toENNReal := by
    intro j
    refine le_trans (lintegral_mono fun x => ?_) ((hu j).ball_deficit_le μ a R C hBU (hC j))
    exact EReal.toENNReal_le_toENNReal
      (EReal.sub_le_sub le_rfl (le_iSup (fun k => u k x) j))
  have hlim : Tendsto (fun j : ℕ => μ (ball 0 R) * ((C : EReal) - u j a).toENNReal) atTop
      (𝓝 (μ (ball 0 R) * ((C : EReal) - ⨆ j, u j a).toENNReal)) :=
    ENNReal.Tendsto.const_mul (tendsto_coe_sub_iSup_toENNReal ha)
      (Or.inr measure_ball_lt_top.ne)
  exact ge_of_tendsto hlim (Eventually.of_forall hstep)

/-- Deficits of an increasing sequence: the deficit of the supremum is the
infimum of the deficits. -/
theorem coe_sub_iSup_toENNReal_eq_iInf {C : ℝ} {b : ℕ → EReal} (hb : Monotone b) :
    ((C : EReal) - ⨆ j, b j).toENNReal = ⨅ j, ((C : EReal) - b j).toENNReal :=
  tendsto_nhds_unique (tendsto_coe_sub_iSup_toENNReal hb)
    (tendsto_atTop_iInf fun _i _j hij =>
      EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (hb hij)))

/-- The zero extension of the deficit of an increasing supremum is measurable:
it is the pointwise infimum of the zero extensions of the members' deficits. -/
theorem measurable_indicator_deficit_iSup {u : ℕ → E → EReal} {U s : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (hmono : ∀ y ∈ s, Monotone fun j => u j y) (C : ℝ) :
    Measurable (s.indicator (fun x => ((C : EReal) - ⨆ j, u j x).toENNReal)) := by
  classical
  have heq : s.indicator (fun x => ((C : EReal) - ⨆ j, u j x).toENNReal) =
      fun x => ⨅ j, s.indicator (fun y => ((C : EReal) - u j y).toENNReal) x := by
    funext x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      exact coe_sub_iSup_toENNReal_eq_iInf (hmono x hx)
    · simp [Set.indicator_of_notMem hx]
  rw [heq]
  exact Measurable.iInf fun j => (hu j).measurable_indicator_deficit hs hsU C

section UscCentre

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- The ball submean inequality for the increasing supremum holds with the
**regularized** value at the centre, which is the sharp form: the centre value
`⨆ j, u j a` is in general strictly smaller than
`uscRegularization (⨆ j, u j) a`, so this is a genuine strengthening of
`ball_deficit_le_of_monotone_iSup`.

The proof is the moving-centre argument.  Truncating the deficit at a finite
height makes the moving-ball integral continuous in its centre
(`PSHD.continuousAt_lintegral_ball`), and every neighbourhood of `a` contains
points where the supremum already exceeds any value below the regularization
(`FirstPass.exists_mem_lt_of_lt_uscRegularization`).  Letting the truncation
and then the test value tend to their limits gives the inequality. -/
theorem ball_deficit_le_uscRegularization_of_monotone_iSup
    {u : ℕ → E → EReal} {U : Set E} (hu : ∀ j, DiscPshOn (u j) U)
    (hmono : ∀ y ∈ U, Monotone fun j => u j y)
    (μ : Measure E) [μ.IsAddHaarMeasure] (a : E) {R S C : ℝ}
    (hR : 0 < R) (hRS : R < S) (hBU : ball a S ⊆ U)
    (hC : ∀ j, ∀ y ∈ ball a S, u j y ≤ (C : EReal)) :
    ∫⁻ x in ball a R, ((C : EReal) - ⨆ j, u j x).toENNReal ∂μ ≤
      μ (ball 0 R) *
        ((C : EReal) - FirstPass.uscRegularization (fun x => ⨆ j, u j x) a).toENNReal := by
  classical
  have hS : 0 < S := hR.trans hRS
  set v : E → EReal := fun x => ⨆ j, u j x with hv
  set g : E → ℝ≥0∞ :=
    (ball a S).indicator (fun x => ((C : EReal) - v x).toENNReal) with hg
  have hgmeas : Measurable g :=
    measurable_indicator_deficit_iSup hu measurableSet_ball hBU
      (fun y hy => hmono y (hBU hy)) C
  -- the moving-centre bound
  have hkey : ∀ w : E, dist w a < S - R → ∀ N : ℝ≥0∞,
      (∫⁻ x in ball w R, min (g x) N ∂μ) ≤
        μ (ball 0 R) * ((C : EReal) - v w).toENNReal := by
    intro w hw N
    have hsub : ball w R ⊆ ball a S := by
      intro y hy
      have : dist y a ≤ dist y w + dist w a := dist_triangle y w a
      exact mem_ball.mpr (by
        have hyw : dist y w < R := mem_ball.mp hy
        linarith)
    refine le_trans (lintegral_mono_ae ?_)
      (ball_deficit_le_of_monotone_iSup hu μ w R C (hsub.trans hBU)
        (fun j y hy => hC j y (hsub hy))
        (hmono w (hBU (hsub (mem_ball_self hR)))))
    filter_upwards [ae_restrict_mem (measurableSet_ball (x := w) (ε := R))] with x hx
    simp only [hg, Set.indicator_of_mem (hsub hx)]
    exact min_le_left _ _
  -- continuity of the truncated moving-ball integral at `a`
  have hcont : ∀ N : ℝ≥0∞, N ≠ ⊤ →
      ContinuousAt (fun z => ∫⁻ x in ball z R, min (g x) N ∂μ) a := by
    intro N hN
    refine PSHD.continuousAt_lintegral_ball (hgmeas.min measurable_const) ?_
      (Measure.addHaar_sphere_of_ne_zero μ a hR.ne')
    have hdom : ∀ x, min (g x) N ≤ (ball a S).indicator (fun _ => N) x := by
      intro x
      by_cases hx : x ∈ ball a S
      · simp only [Set.indicator_of_mem hx]
        exact min_le_right (g x) N
      · simp [hg, Set.indicator_of_notMem hx]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hdom)
    rw [lintegral_indicator_const measurableSet_ball]
    exact ENNReal.mul_ne_top hN measure_ball_lt_top.ne
  -- the regularized value is below the uniform bound, in particular finite
  have hPle : FirstPass.uscRegularization v a ≤ (C : EReal) := by
    refine le_trans (FirstPass.uscRegularization_le_localSup v
      (ball_mem_nhds a hS)) ?_
    refine iSup_le fun y => iSup_le fun hy => ?_
    exact iSup_le fun j => hC j y hy
  -- the truncated bound at `a`
  have hat : ∀ N : ℝ≥0∞, N ≠ ⊤ →
      (∫⁻ x in ball a R, min (g x) N ∂μ) ≤
        μ (ball 0 R) * ((C : EReal) - FirstPass.uscRegularization v a).toENNReal := by
    intro N hN
    set P : EReal := FirstPass.uscRegularization v a with hP
    -- for every test value strictly below `P`
    have htest : ∀ b : EReal, b < P →
        (∫⁻ x in ball a R, min (g x) N ∂μ) ≤
          μ (ball 0 R) * ((C : EReal) - b).toENNReal := by
      intro b hb
      by_contra hcon
      rw [not_le] at hcon
      have hnbhd : {z : E | μ (ball 0 R) * ((C : EReal) - b).toENNReal <
          ∫⁻ x in ball z R, min (g x) N ∂μ} ∈ 𝓝 a :=
        (hcont N hN) (Ioi_mem_nhds hcon)
      obtain ⟨w, hwmem, hwb⟩ :=
        FirstPass.exists_mem_lt_of_lt_uscRegularization hb
          (Filter.inter_mem hnbhd (ball_mem_nhds a (by linarith : (0:ℝ) < S - R)))
      have h1 : (∫⁻ x in ball w R, min (g x) N ∂μ) ≤
          μ (ball 0 R) * ((C : EReal) - b).toENNReal := by
        refine le_trans (hkey w (mem_ball.mp hwmem.2) N) ?_
        gcongr
        exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hwb.le)
      exact absurd h1 (not_le.mpr hwmem.1)
    -- let the test value increase to `P`
    rcases eq_or_ne P ⊥ with hPbot | hPbot
    · have hpos : μ (ball (0 : E) R) ≠ 0 := (measure_ball_pos μ 0 hR).ne'
      rw [hPbot, EReal.coe_sub_bot, EReal.toENNReal_top, ENNReal.mul_top hpos]
      exact le_top
    · have hPtop : P ≠ ⊤ := fun h => by simp [h] at hPle
      have hPcoe : P = ((P.toReal : ℝ) : EReal) := (EReal.coe_toReal hPtop hPbot).symm
      have hlim : Tendsto
          (fun k : ℕ => μ (ball 0 R) *
            ((C : EReal) - ((P.toReal - 1 / (k + 1 : ℝ) : ℝ) : EReal)).toENNReal)
          atTop (𝓝 (μ (ball 0 R) * ((C : EReal) - P).toENNReal)) := by
        refine ENNReal.Tendsto.const_mul ?_ (Or.inr measure_ball_lt_top.ne)
        refine (continuousAt_coe_sub_toENNReal C P).tendsto.comp ?_
        rw [hPcoe]
        refine (continuous_coe_real_ereal.tendsto _).comp ?_
        have : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1 : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using tendsto_const_nhds.sub this
      refine ge_of_tendsto hlim (Eventually.of_forall fun k => htest _ ?_)
      have h1 : ((P.toReal - 1 / (k + 1 : ℝ) : ℝ) : EReal) < ((P.toReal : ℝ) : EReal) := by
        refine EReal.coe_lt_coe_iff.mpr ?_
        have hpos : (0:ℝ) < 1 / (k + 1 : ℝ) := by positivity
        linarith
      exact h1.trans_le hPcoe.ge
  -- monotone convergence in the truncation height
  have hsup : ∫⁻ x in ball a R, ((C : EReal) - v x).toENNReal ∂μ
      = ⨆ k : ℕ, ∫⁻ x in ball a R, min (g x) (k : ℝ≥0∞) ∂μ := by
    rw [← lintegral_iSup (fun k => hgmeas.min measurable_const)
      (fun i j hij x => min_le_min_left _ (by exact_mod_cast hij))]
    refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
    have hxS : x ∈ ball a S := ball_subset_ball hRS.le hx
    have hgx : g x = ((C : EReal) - v x).toENNReal := by
      simp [hg, Set.indicator_of_mem hxS]
    rw [hgx]
    refine le_antisymm ?_ (iSup_le fun k => min_le_left _ _)
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hc.ne_top
    exact lt_of_lt_of_le (lt_min hc hk)
      (le_iSup (fun k : ℕ => min (((C : EReal) - v x).toENNReal) (k : ℝ≥0∞)) k)
  rw [hsup]
  exact iSup_le fun k => hat _ (by simp)

/-- Lebesgue-a.e. on an interior ball, the increasing supremum already agrees
with its upper semicontinuous regularization.

This is the classical statement that an increasing sequence of plurisubharmonic
functions converges almost everywhere to the *regularized* limit, and it is
input (i) of the Guan--Zhou route of `Pending/StrongOpennessRegularRoute.lean`: the
strong openness hypothesis is stated for the regularization, which is the
larger function, and only this identity turns it into a hypothesis for the
pointwise limit.

The proof combines the sharp moving-centre submean
(`ball_deficit_le_uscRegularization_of_monotone_iSup`), which says that every
small ball average of the deficit of the limit is at most the deficit of the
regularization at the centre, with Lebesgue differentiation
(`IsUnifLocDoublingMeasure.ae_tendsto_average`), which says that almost every
point recovers its own value from those averages.  Truncating the deficit at
each natural number keeps the differentiated function bounded, hence locally
integrable; the untruncated inequality follows by taking the countable
supremum, and it forces equality because the deficit of the regularization is
the smaller one. -/
theorem ae_uscRegularization_iSup_eq_on_ball
    {u : ℕ → E → EReal} {U : Set E} (hu : ∀ j, DiscPshOn (u j) U)
    (hmono : ∀ y ∈ U, Monotone fun j => u j y)
    (μ : Measure E) [μ.IsAddHaarMeasure] (a : E) {S C : ℝ} (hS : 0 < S)
    (hBU : ball a S ⊆ U)
    (hC : ∀ j, ∀ y ∈ ball a S, u j y ≤ (C : EReal)) :
    ∀ᵐ x ∂μ, x ∈ ball a (S / 2) →
      FirstPass.uscRegularization (fun y => ⨆ j, u j y) x = ⨆ j, u j x := by
  classical
  set v : E → EReal := fun x => ⨆ j, u j x with hv
  set P : E → EReal := FirstPass.uscRegularization v with hP
  set d : E → ℝ≥0∞ := fun x => ((C : EReal) - v x).toENNReal with hd
  set d' : E → ℝ≥0∞ := fun x => ((C : EReal) - P x).toENNReal with hd'
  have hhalf : S / 2 < S := by linarith
  have hdmeas : Measurable ((ball a S).indicator d) :=
    measurable_indicator_deficit_iSup hu measurableSet_ball hBU
      (fun y hy => hmono y (hBU hy)) C
  have hvC : ∀ y ∈ ball a S, v y ≤ (C : EReal) := fun y hy =>
    iSup_le fun j => hC j y hy
  have hPC : ∀ x ∈ ball a (S / 2), P x ≤ (C : EReal) := by
    intro x hx
    have hxS : x ∈ ball a S := ball_subset_ball hhalf.le hx
    refine le_trans (FirstPass.uscRegularization_le_localSup v
      (isOpen_ball.mem_nhds hxS)) ?_
    exact iSup_le fun y => iSup_le fun hy => hvC y hy
  -- the sharp submean at every centre of the half ball
  have hkey : ∀ x ∈ ball a (S / 2), ∀ r : ℝ, 0 < r → r < S / 2 →
      ∫⁻ y in ball x r, d y ∂μ ≤ μ (ball 0 r) * d' x := by
    intro x hx r hr hrS
    have hsub : ball x (S / 2) ⊆ ball a S := by
      intro y hy
      have h1 : dist y x < S / 2 := mem_ball.mp hy
      have h2 : dist x a < S / 2 := mem_ball.mp hx
      have := dist_triangle y x a
      exact mem_ball.mpr (by linarith)
    exact ball_deficit_le_uscRegularization_of_monotone_iSup hu hmono μ x hr hrS
      (hsub.trans hBU) (fun j y hy => hC j y (hsub hy))
  -- the truncated statement, for each height
  have htrunc : ∀ N : ℕ, ∀ᵐ x ∂μ, x ∈ ball a (S / 2) → min (d x) (N : ℝ≥0∞) ≤ d' x := by
    intro N
    set f : E → ℝ := fun y => (min ((ball a S).indicator d y) (N : ℝ≥0∞)).toReal with hf
    have hfmeas : Measurable f := (hdmeas.min measurable_const).ennreal_toReal
    have hfle : ∀ y, ‖f y‖ ≤ ‖(N : ℝ)‖ := by
      intro y
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_nonneg (Nat.cast_nonneg N)]
      calc (min ((ball a S).indicator d y) (N : ℝ≥0∞)).toReal
          ≤ ((N : ℝ≥0∞)).toReal := ENNReal.toReal_mono (by simp) (min_le_right _ _)
        _ = (N : ℝ) := by simp
    have hLI : LocallyIntegrable f μ :=
      (locallyIntegrable_const (N : ℝ)).mono hfmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall hfle)
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hLI 1] with x hxdiff hxball
    by_cases hd'top : d' x = ⊤
    · simp [hd'top]
    have hxS : x ∈ ball a S := ball_subset_ball hhalf.le hxball
    -- every small average is below the regularized deficit at the centre
    have havg : ∀ r : ℝ, 0 < r → r < S / 2 →
        ⨍ y in closedBall x r, f y ∂μ ≤ (d' x).toReal := by
      intro r hr hrS
      have hsub : ball x r ⊆ ball a S := by
        intro y hy
        have h1 : dist y x < r := mem_ball.mp hy
        have h2 : dist x a < S / 2 := mem_ball.mp hxball
        have := dist_triangle y x a
        exact mem_ball.mpr (by linarith)
      have hballae : (closedBall x r : Set E) =ᵐ[μ] ball x r := by
        refine ae_eq_set.mpr ⟨?_, ?_⟩
        · rw [Metric.closedBall_sdiff_ball]
          exact Measure.addHaar_sphere_of_ne_zero μ x hr.ne'
        · simp [Set.sdiff_eq_empty.mpr Metric.ball_subset_closedBall]
      have hmasspos : 0 < (μ (ball x r)).toReal :=
        ENNReal.toReal_pos (measure_ball_pos μ x hr).ne' measure_ball_lt_top.ne
      have hlint : ∫⁻ y in ball x r, min ((ball a S).indicator d y) (N : ℝ≥0∞) ∂μ
          ≤ μ (ball x r) * d' x := by
        refine le_trans (lintegral_mono_ae ?_) ((hkey x hxball r hr hrS).trans_eq ?_)
        · filter_upwards [ae_restrict_mem (measurableSet_ball (x := x) (ε := r))] with y hy
          simp only [Set.indicator_of_mem (hsub hy)]
          exact min_le_left _ _
        · rw [Measure.addHaar_ball_center μ x r]
      have hreal : ∫ y in ball x r, f y ∂μ ≤ (μ (ball x r)).toReal * (d' x).toReal := by
        rw [hf, integral_toReal ((hdmeas.min measurable_const).aemeasurable)
          (ae_of_all _ fun y => lt_of_le_of_lt (min_le_right _ _) (by simp))]
        calc (∫⁻ y in ball x r, min ((ball a S).indicator d y) (N : ℝ≥0∞) ∂μ).toReal
            ≤ (μ (ball x r) * d' x).toReal :=
              ENNReal.toReal_mono (ENNReal.mul_ne_top measure_ball_lt_top.ne hd'top) hlint
          _ = (μ (ball x r)).toReal * (d' x).toReal := ENNReal.toReal_mul
      rw [setAverage_congr hballae, setAverage_eq, smul_eq_mul, measureReal_def,
        inv_mul_le_iff₀ hmasspos]
      exact hreal.trans_eq (by ring)
    -- differentiate along a shrinking sequence of radii
    have hpos : ∀ k : ℕ, 0 < S / ((k : ℝ) + 3) := fun k => by positivity
    have hsmall : ∀ k : ℕ, S / ((k : ℝ) + 3) < S / 2 := by
      intro k
      refine div_lt_div_of_pos_left hS (by norm_num) ?_
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hδ : Tendsto (fun k : ℕ => S / ((k : ℝ) + 3)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Filter.Eventually.of_forall fun k => Set.mem_Ioi.mpr (hpos k))
      have h := (tendsto_const_div_atTop_nhds_zero_nat S).comp (tendsto_add_atTop_nat 3)
      simpa [Function.comp_def] using h
    have hmemball : ∀ k : ℕ, x ∈ closedBall x (1 * (S / ((k : ℝ) + 3))) := by
      intro k
      rw [one_mul]
      exact mem_closedBall_self (hpos k).le
    have hlim := hxdiff (fun _ : ℕ => x) (fun k => S / ((k : ℝ) + 3)) hδ
      (Filter.Eventually.of_forall hmemball)
    have hbound : f x ≤ (d' x).toReal :=
      le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
        havg _ (hpos k) (hsmall k))
    have hfx : f x = (min (d x) (N : ℝ≥0∞)).toReal := by
      simp [hf, Set.indicator_of_mem hxS]
    have hne : min (d x) (N : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) (min_le_right _ _)
    rw [← ENNReal.toReal_le_toReal hne hd'top, ← hfx]
    exact hbound
  -- assemble over the truncation heights and convert back to the potentials
  filter_upwards [ae_all_iff.mpr htrunc] with x hx hxball
  change P x = v x
  have hle : d x ≤ d' x := by
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hc.ne_top
    exact lt_of_lt_of_le (lt_min hc hN) (hx N hxball)
  have hxS : x ∈ ball a S := ball_subset_ball hhalf.le hxball
  have hvP : v x ≤ P x := FirstPass.le_uscRegularization v x
  refine le_antisymm ?_ hvP
  rcases eq_or_ne (P x) ⊥ with hb | hb
  · rw [hb]; exact bot_le
  have hPtop : P x ≠ ⊤ := fun h => by
    have := hPC x hxball
    rw [h] at this
    exact absurd (top_le_iff.mp this) (EReal.coe_ne_top C)
  have hPreal : P x = ((P x).toReal : EReal) := (EReal.coe_toReal hPtop hb).symm
  have hd'eq : d' x = ENNReal.ofReal (C - (P x).toReal) := by
    rw [hd']
    simp only
    rw [hPreal, ← EReal.coe_sub, EReal.real_coe_toENNReal]
    simp
  have hvbot : v x ≠ ⊥ := by
    intro hvb
    have : d x = ⊤ := by
      rw [hd]; simp only; rw [hvb, EReal.coe_sub_bot, EReal.toENNReal_top]
    rw [this, hd'eq] at hle
    exact absurd (top_le_iff.mp hle) ENNReal.ofReal_ne_top
  have hvtop : v x ≠ ⊤ := fun h => by
    have := hvC x hxS
    rw [h] at this
    exact absurd (top_le_iff.mp this) (EReal.coe_ne_top C)
  have hvreal : v x = ((v x).toReal : EReal) := (EReal.coe_toReal hvtop hvbot).symm
  have hdeq : d x = ENNReal.ofReal (C - (v x).toReal) := by
    rw [hd]
    simp only
    rw [hvreal, ← EReal.coe_sub, EReal.real_coe_toENNReal]
    simp
  rw [hdeq, hd'eq] at hle
  have hnn : 0 ≤ C - (P x).toReal := by
    have := hPC x hxball
    rw [hPreal] at this
    have := EReal.coe_le_coe_iff.mp this
    linarith
  have := (ENNReal.ofReal_le_ofReal_iff hnn).mp hle
  rw [hPreal, hvreal]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

end UscCentre

end SGPT.Foundations.Analysis
