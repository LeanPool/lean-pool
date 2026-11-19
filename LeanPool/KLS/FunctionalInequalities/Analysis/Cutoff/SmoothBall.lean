/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.MetricSpace.Lipschitz
public import LeanPool.KLS.FunctionalInequalities.Analysis.Lipschitz.Gradient
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.Profile
public import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# Smooth norm-ball cutoffs and compact localization

`exists_smooth_concentric_cutoff_norm_fderiv_le` (namespace `FunctionalInequalities.Analysis`) adds
generic concentric
cutoffs in a finite-dimensional real inner product space: one constant `D > 0` serves every center
and every pair of
radii `0 ≤ r < R`, with `‖Dχ‖ ≤ D/(R − r)`. These are the cutoffs of a Moser-type iteration
(Gilbarg–Trudinger (2001) (8.48)–(8.49)); they are not the iteration itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Basic

/-- A fixed smooth bump: one on the closed unit ball, zero outside radius two. -/
def bump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump rescaled to be one on radius `R` and zero outside radius `2 * R`. -/
def scaled (R : ℝ) (x : E) : ℝ := (bump (E := E)) (R⁻¹ • x)

theorem scaled_nonneg (R : ℝ) (x : E) : 0 ≤ scaled R x := by
  unfold scaled; exact (bump (E := E)).nonneg

theorem scaled_le_one (R : ℝ) (x : E) : scaled R x ≤ 1 := by
  unfold scaled; exact (bump (E := E)).le_one

theorem scaled_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : scaled R x = 1 := by
  unfold scaled
  apply (bump (E := E)).one_of_mem_closedBall
  change R⁻¹ • x ∈ Metric.closedBall (0 : E) 1
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hR, inv_mul_le_iff₀ hR, mul_one]
  exact hx

theorem scaled_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) : scaled R x = 0 := by
  unfold scaled
  apply (bump (E := E)).zero_of_le_dist
  change (2 : ℝ) ≤ dist (R⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, le_inv_mul_iff₀ hR]
  linarith

theorem contDiff_scaled (R : ℝ) : ContDiff ℝ ∞ (scaled (E := E) R) := by
  unfold scaled
  exact ((bump (E := E)).contDiff (n := ⊤)).comp (contDiff_const_smul R⁻¹)

theorem continuous_scaled (R : ℝ) : Continuous (scaled (E := E) R) :=
  (contDiff_scaled R).continuous

theorem hasFDerivAt_scaled (R : ℝ) (x : E) :
    HasFDerivAt (scaled R) (R⁻¹ • fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)) x := by
  have h1 : HasFDerivAt (fun y : E => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have h2 : HasFDerivAt (⇑(bump (E := E))) (fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)) (R⁻¹ • x) :=
    (((bump (E := E)).contDiff (n := 1)).differentiable (by simp) (R⁻¹ • x)).hasFDerivAt
  have h3 : (fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ E) =
      R⁻¹ • fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x) := by
    ext v
    simp
  unfold scaled
  exact (h2.comp x h1).congr_fderiv h3

theorem fderiv_scaled_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ < R) :
    fderiv ℝ (scaled R) x = 0 := by
  have h : scaled (E := E) R =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : E) R by
      simpa [Metric.mem_ball, dist_zero_right] using hx)] with y hy
    exact scaled_eq_one hR (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy))
  rw [h.fderiv_eq]
  simp

theorem norm_fderiv_scaled_le {R : ℝ} (hR : 0 < R) {M : ℝ}
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M) (x : E) :
    ‖fderiv ℝ (scaled R) x‖ ≤ R⁻¹ * M := by
  rw [(hasFDerivAt_scaled R x).fderiv, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  gcongr
  exact hM _

theorem lipschitzWith_scaled {R : ℝ} (hR : 0 < R) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M) :
    LipschitzWith (R⁻¹ * M).toNNReal (scaled (E := E) R) := by
  apply lipschitzWith_of_nnNorm_fderiv_le ((contDiff_scaled R).differentiable (by simp))
  intro x
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal _ (by positivity)]
  exact norm_fderiv_scaled_le hR hM x

theorem gradient_scaled_mul [CompleteSpace E] {R : ℝ} {g : E → ℝ} {x : E}
    (hx : DifferentiableAt ℝ g x) :
    gradient (fun y => scaled R y * g y) x =
      scaled R x • gradient g x + g x • gradient (scaled R) x := by
  have h1 : HasFDerivAt (scaled R) (fderiv ℝ (scaled R) x) x :=
    (hasFDerivAt_scaled R x).differentiableAt.hasFDerivAt
  have h :
    HasFDerivAt (fun y => scaled R y * g y)
      (scaled R x • fderiv ℝ g x + g x • fderiv ℝ (scaled R) x) x :=
    h1.mul hx.hasFDerivAt
  rw [gradient_eq_of_hasFDerivAt h]
  simp only [map_add, map_smulₛₗ, starRingEnd_apply, star_trivial]
  rfl

end Basic

section FiniteDimensional

variable [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A locally Lipschitz real function is Lipschitz on every compact set. -/
theorem lipschitzOnWith_of_locallyLipschitz_of_isCompact {f : E → ℝ} (hf : LocallyLipschitz f)
    {s : Set E} (hs : IsCompact s) : ∃ K : NNReal, LipschitzOnWith K f s := by
  have key : ∀ x : E, ∃ r : ℝ, 0 < r ∧ ∃ K : NNReal, LipschitzOnWith K f (Metric.ball x r) := by
    intro x
    obtain ⟨K, t, ht, hK⟩ := hf x
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
    exact ⟨r, hr, K, hK.mono hrt⟩
  choose r hr K hK using key
  obtain ⟨T, -, hT⟩ := hs.elim_nhds_subcover (fun x => Metric.ball x (r x))
    (fun x _ => Metric.ball_mem_nhds x (hr x))
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric (ι := T)
    (c := fun i => Metric.ball (i : E) (r i)) hs (fun _ => Metric.isOpen_ball)
    (fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hT hx)
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf.continuous.continuousOn
  set K' : NNReal := T.sup K with hK'
  set C' : ℝ := max C 0 with hC'
  refine ⟨(max (K' : ℝ) (2 * C' / δ)).toNNReal, LipschitzOnWith.of_dist_le' ?_⟩
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · obtain ⟨i, hi⟩ := hcover x hx
    have hxi : x ∈ Metric.ball (i : E) (r i) := hi (Metric.mem_ball_self hδ)
    have hyi : y ∈ Metric.ball (i : E) (r i) := hi (by simpa [dist_comm] using hxy)
    have hKi : LipschitzOnWith (K i) f (Metric.ball (i : E) (r i)) := hK i
    calc dist (f x) (f y) ≤ K i * dist x y := hKi.dist_le_mul x hxi y hyi
      _ ≤ K' * dist x y := by
          gcongr
          exact_mod_cast Finset.le_sup (f := K) i.2
      _ ≤ max (K' : ℝ) (2 * C' / δ) * dist x y := by gcongr; exact le_max_left _ _
  · push Not at hxy
    have hCx : ‖f x‖ ≤ C' := (hC x hx).trans (le_max_left _ _)
    have hCy : ‖f y‖ ≤ C' := (hC y hy).trans (le_max_left _ _)
    have hC0 : 0 ≤ C' := le_max_right _ _
    calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * C' := by linarith
      _ = (2 * C' / δ) * δ := by field_simp
      _ ≤ (2 * C' / δ) * dist x y := by gcongr
      _ ≤ max (K' : ℝ) (2 * C' / δ) * dist x y := by gcongr; exact le_max_right _ _

theorem hasCompactSupport_scaled {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (scaled (E := E) R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx =>
    scaled_eq_zero hR (by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact le_of_lt (not_le.mp hx))

theorem exists_bound_fderiv_bump :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M := by
  have hc : Continuous (fderiv ℝ (⇑(bump (E := E)))) :=
    ((bump (E := E)).contDiff (n := 1)).continuous_fderiv (by simp)
  have hs : HasCompactSupport (fderiv ℝ (⇑(bump (E := E)))) :=
    (bump (E := E)).hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

end FiniteDimensional


end FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

section ConcentricCutoff

open Set Metric

namespace FunctionalInequalities.Analysis

/--
**Uniform concentric cutoffs.** In a finite-dimensional real inner product space (dimension zero
included) there is ONE
`D > 0` such that for every center `c` and radii `0 ≤ r < R` some `C^∞` cutoff `χ` with values in
`[0, 1]` equals one on
`closedBall c r`, vanishes for `‖x − c‖ ≥ R`, has `tsupport χ ⊆ closedBall c R` and `‖Dχ‖ ≤ D / (R −
r)`. The profile is
composed with the normalized squared distance, so it is smooth at the center. `D` depends on the
space only. -/
theorem exists_smooth_concentric_cutoff_norm_fderiv_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ D : ℝ,
      0 < D ∧
        ∀ (c : E) (r R : ℝ),
          0 ≤ r →
            r < R →
              ∃ χ : E → ℝ,
                ContDiff ℝ ∞ χ ∧
                  HasCompactSupport χ ∧
                    tsupport χ ⊆ closedBall c R ∧
                      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
                        (∀ x ∈ closedBall c r, χ x = 1) ∧
                          (∀ x, R ≤ ‖x - c‖ → χ x = 0) ∧ ∀ x, ‖fderiv ℝ χ x‖ ≤ D / (R - r) := by
  classical
  obtain ⟨hf, -, h01, hone, hzero, -, -, -, B, hB, hBd⟩ := smoothTransition_two_sub_cutoff
  let f := fun t : ℝ => Real.smoothTransition (2 - t)
  refine ⟨2 * B + 1, by positivity, ?_⟩
  intro c r R hr hR
  have hRp : 0 < R := lt_of_le_of_lt hr hR
  have hgap : 0 < R - r := sub_pos.mpr hR
  let d := R ^ 2 - r ^ 2
  have hd : 0 < d := by dsimp only [d]; nlinarith
  let g := fun x : E => d⁻¹ * (‖x - c‖ ^ 2 - r ^ 2) + 1
  let χ := fun x : E => f (g x)
  have hg : ContDiff ℝ ∞ g :=
    ((contDiff_const.mul
          (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const)).add
      contDiff_const)
  have hc : ContDiff ℝ ∞ χ := hf.comp hg
  have hzeroχ (x : E) (hx : R ≤ ‖x - c‖) : χ x = 0 := by
    apply hzero
    change 2 ≤ d⁻¹ * (‖x - c‖ ^ 2 - r ^ 2) + 1
    have hs : d ≤ ‖x - c‖ ^ 2 - r ^ 2 := by dsimp only [d]; nlinarith [norm_nonneg (x - c)]
    have hi : 1 ≤ d⁻¹ * (‖x - c‖ ^ 2 - r ^ 2) := by
      rw [le_inv_mul_iff₀ hd, mul_one]
      exact hs
    linarith
  have hχc : HasCompactSupport χ := by
    apply HasCompactSupport.intro (isCompact_closedBall c R)
    intro x hx
    apply hzeroχ
    have hn : R < ‖x - c‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
    exact hn.le
  have hχS : tsupport χ ⊆ closedBall c R := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    by_contra h
    exact hx (hzeroχ x (le_of_lt (lt_of_not_ge h)))
  refine ⟨χ, hc, hχc, hχS, fun x => h01 (g x), ?_, hzeroχ, ?_⟩
  · intro x hx
    apply hone
    change d⁻¹ * (‖x - c‖ ^ 2 - r ^ 2) + 1 ≤ 1
    have hn : ‖x - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hx
    have hs : ‖x - c‖ ^ 2 - r ^ 2 ≤ 0 := by nlinarith [norm_nonneg (x - c)]
    have hi := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hd.le) hs
    linarith
  · intro x
    by_cases hx : x ∈ closedBall c R
    · have hn : ‖x - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hx
      have hg' :=
        ((((hasFDerivAt_id x).sub_const c).norm_sq.sub_const (r ^ 2)).const_mul d⁻¹).add_const 1
      have hf' := (hf.differentiable (by simp) (g x)).hasDerivAt
      have hcomp := hf'.comp_hasFDerivAt x hg'
      have he : fderiv ℝ χ x = deriv f (g x) • (d⁻¹ • ((2 : ℝ) • innerSL ℝ (x - c))) := by
        simpa only [χ, f, Function.comp_def, id_eq, ContinuousLinearMap.comp_id, two_smul] using
          hcomp.fderiv
      rw [he, norm_smul, norm_smul, norm_smul, innerSL_apply_norm]
      simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hd,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb : |deriv f (g x)| ≤ B := (hBd (g x)).1
      calc
        |deriv f (g x)| * (d⁻¹ * (2 * ‖x - c‖)) ≤ B * (d⁻¹ * (2 * R)) := by gcongr
        _ = (2 * B * R) / d := by ring
        _ ≤ (2 * B + 1) / (R - r) := by
          apply (div_le_div_iff₀ hd hgap).mpr
          have hpos : 0 ≤ 2 * B * r * (R - r) :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB) hr) hgap.le
          dsimp only [d] at hd ⊢
          nlinarith [hpos]
    · have hxt : x ∉ tsupport χ := fun h => hx (hχS h)
      rw [fderiv_of_notMem_tsupport ℝ hxt, norm_zero]
      positivity

end FunctionalInequalities.Analysis

end ConcentricCutoff

namespace FunctionalInequalities.Analysis
open Set Filter Topology
open scoped ContDiff
/-- A compact set admits a compact C1 cutoff equal to one near each of its points. -/
theorem exists_compact_contDiff_eq_one_near {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) :
    ∃ χ : E → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : E)
  let φ : ContDiffBump (0 : E) :=
    ⟨max r 0 + 1, max r 0 + 2, by positivity, by linarith⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, ?_⟩
  intro x hx
  apply φ.eventuallyEq_one_of_mem_ball
  have h := hr hx
  change dist x 0 ≤ r at h
  change dist x 0 < max r 0 + 1
  linarith [le_max_left r 0]


end FunctionalInequalities.Analysis
