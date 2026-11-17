/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Transport
public import LeanPool.KLS.FunctionalInequalities.Probability.Domination.Averages
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Small-ball bounds for log-concave laws

The proof uses ball averages, convex superlevel sets, separation, Tonelli, and the
Besicovitch covering theorem to derive intrinsic absolute continuity from compact-set
log-concavity. It includes singular ambient laws and zero-dimensional affine supports.
It proves the absolute-continuity and null-boundary portions of the representation
theorem; it does not construct the log-concave density representative or prove moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set Topology

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- A convex set meeting every radius-R ball with center in a larger ball contains the
inner ball. Separation turns the covering condition into a quantitative interior witness. -/
private theorem ball_subset_of_nearby_points {S : Set E} (hS : Convex ℝ S) (a : E) (R : ℝ)
    (hR : 0 < R) (hnear : ∀ y ∈ closedBall a (8 * R), ∃ z ∈ S, dist z y < R) : ball a R ⊆ S := by
  have hclosure : closedBall a R ⊆ closure S := by
    intro x hx
    by_contra hnot
    obtain ⟨f, u, hfu, hux⟩ :=
      geometric_hahn_banach_closed_point hS.closure isClosed_closure hnot
    obtain ⟨s, hs, _⟩ := hnear a (mem_closedBall_self (by positivity))
    have hf0 : f ≠ 0 := by
      intro hf0
      have hfs := hfu s (subset_closure hs)
      simp only [hf0, zero_apply] at hfs hux
      linarith
    have hfn : 0 < ‖f‖ := norm_pos_iff.mpr hf0
    have hfnn : 0 < ‖f‖₊ := by exact_mod_cast hfn
    obtain ⟨v, hvn, hvf⟩ := f.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm (half_lt_self hfnn)
    have hvn' : ‖v‖ = 1 := by
      simpa only [← coe_nnnorm, NNReal.coe_one] using congrArg ((↑) : NNReal → ℝ) hvn
    have hvf' : ‖f‖ / 2 < |f v| := by exact_mod_cast hvf
    obtain ⟨v, hvn, hvf⟩ : ∃ v : E, ‖v‖ = 1 ∧ ‖f‖ / 2 < f v := by
      rcases lt_abs.mp hvf' with h | h
      · exact ⟨v, hvn', h⟩
      · exact ⟨-v, by simpa using hvn', by simpa using h⟩
    let y := a + (8 * R) • v
    have hy : y ∈ closedBall a (8 * R) := by
      simp only [y, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 8 * R), hvn, mul_one, le_refl]
    obtain ⟨z, hz, hzy⟩ := hnear y hy
    have hzd : |f z - f y| ≤ ‖f‖ * dist z y := by
      simpa only [← map_sub, Real.norm_eq_abs, dist_eq_norm] using f.le_opNorm (z - y)
    have hxd : |f x - f a| ≤ ‖f‖ * R := by
      have h := f.le_opNorm (x - a)
      rw [map_sub, Real.norm_eq_abs] at h
      exact
        h.trans
          (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hx)
            hfn.le)
    have hfy : f y = f a + (8 * R) * f v := by simp [y]
    have hzf := hfu z (subset_closure hz)
    have hbound := mul_lt_mul_of_pos_left hzy hfn
    have hzlow := (abs_le.mp hzd).1
    have hxup := (abs_le.mp hxd).2
    nlinarith
  have hspan : affineSpan ℝ S = ⊤ := by
    have hsub : ball a R ⊆ affineSpan ℝ S :=
      ball_subset_closedBall.trans
        (hclosure.trans
          (closure_minimal (subset_affineSpan ℝ S)
            (affineSpan ℝ S).closed_of_finiteDimensional))
    apply top_unique
    rw [← isOpen_ball.affineSpan_eq_top (u := ball a R) (nonempty_ball.mpr hR)]
    exact affineSpan_le.mpr hsub
  have hi := hS.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hb : ball a R ⊆ interior (closure S) :=
    (isOpen_ball.subset_interior_iff).mpr (ball_subset_closedBall.trans hclosure)
  rw [hS.interior_closure_eq_interior_of_nonempty_interior hi] at hb
  exact hb.trans interior_subset

/-- Uniformly positive support masses force a high ball-average point near every center. -/
private theorem exists_uniform_ball_average_points (μ : ProbabilityMeasure E) (m : Measure E)
    [m.IsAddHaarMeasure] {K : Set E} (hK : IsCompact K) (hKs : K ⊆ (μ : Measure E).support)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ENNReal,
      0 < c ∧
        c ≠ ⊤ ∧
          ∀ r : ℝ,
            0 < r →
              r ≤ δ →
                ∀ y ∈ K,
                  ∃ z ∈ ball y (2 * δ),
                    c * m (closedBall (0 : E) r) ≤ (μ : Measure E) (closedBall z r) := by
  obtain ⟨γ, hγ, hγK⟩ :=
    Probability.exists_pos_le_measure_ball_on_isCompact (μ : Measure E) hK hKs δ hδ
  let D := m (ball (0 : E) (2 * δ))
  have hDt : D ≠ ⊤ := measure_ball_ne_top
  obtain ⟨c, hc, hcγ⟩ := exists_between (ENNReal.div_pos hγ.ne' hDt)
  have hct : c ≠ ⊤ := (hcγ.trans_le le_top).ne
  have hcD : c * D < γ := ENNReal.mul_lt_of_lt_div hcγ
  refine ⟨c, hc, hct, ?_⟩
  intro r hr hrδ y hy
  by_contra hn
  push Not at hn
  have hb0 : m (closedBall (0 : E) r) ≠ 0 := (measure_closedBall_pos m _ hr).ne'
  have hbt : m (closedBall (0 : E) r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hlower :=
    (mul_le_mul (le_refl (m (closedBall (0 : E) r))) (hγK y hy) (by positivity)
          (by positivity)).trans
      (Probability.measure_ball_mul_closedBall_le_lintegral (μ : Measure E) m y hrδ)
  have hupper :
    (∫⁻ z in ball y (2 * δ), (μ : Measure E) (closedBall z r) ∂m) ≤
      (c * m (closedBall (0 : E) r)) * D := by
    calc
      _ ≤ ∫⁻ _ in ball y (2 * δ), c * m (closedBall (0 : E) r) ∂m :=
        setLIntegral_mono' measurableSet_ball (fun z hz => (hn z hz).le)
      _ = _ := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Measure.addHaar_ball_center m,
          D]
  have hstrict := ENNReal.mul_lt_mul_left hb0 hbt hcD
  have hbad := hlower.trans hupper
  exact (not_lt_of_ge hbad) (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hstrict)

/-- On one fixed interior ball, all sufficiently small ball averages have a common
positive lower density bound. The radii and bound are independent of the averaging radius. -/
private theorem exists_uniform_ball_average_lower_bound {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (m : Measure E) [m.IsAddHaarMeasure]
    (hi : (interior (μ : Measure E).support).Nonempty) :
    ∃ (a : E) (R δ : ℝ) (c : ENNReal), 0 < R ∧ 0 < δ ∧ 0 < c ∧ c ≠ ⊤ ∧
      ∀ r : ℝ, 0 < r → r ≤ δ → ∀ x ∈ ball a R,
        c * m (closedBall (0 : E) r) ≤ (μ : Measure E) (closedBall x r) := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨ε, hε, hεS⟩ := nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  let R := ε / 8
  have hR : 0 < R := by dsimp [R]; positivity
  have hK : closedBall a (8 * R) ⊆ (μ : Measure E).support := by
    convert! hεS using 1
    congr 1
    dsimp [R]
    ring
  obtain ⟨c, hc, hct, hcK⟩ := exists_uniform_ball_average_points μ m
    (isCompact_closedBall a (8 * R)) hK (show 0 < R / 4 by positivity)
  refine ⟨a, R, R / 4, c, hR, by positivity, hc, hct, ?_⟩
  intro r hr hrδ
  apply ball_subset_of_nearby_points
    (hμ.convex_closedBall_superlevel r (c * m (closedBall (0 : E) r))) a R hR
  intro y hy
  obtain ⟨z, hz, hzc⟩ := hcK r hr hrδ y hy
  exact ⟨z, hzc, (mem_ball.mp hz).trans (by linarith)⟩

/-- A lower bound on one ball and the midpoint inequality give a global upper bound. -/
private theorem closedBall_le_of_ball_lower_bound {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (m : Measure E) [m.IsAddHaarMeasure]
    (a : E) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (c : ENNReal)
    (hc : 0 < c) (hct : c ≠ ⊤)
    (hlower : ∀ y ∈ ball a R, c * m (closedBall (0 : E) r) ≤
      (μ : Measure E) (closedBall y r)) (x : E) :
    (μ : Measure E) (closedBall x r) ≤
      (c * (m (ball (0 : E) (R / 2)) * m (ball (0 : E) (R / 2))))⁻¹ *
        m (closedBall (0 : E) r) := by
  let b := m (closedBall (0 : E) r)
  let V := m (ball (0 : E) (R / 2))
  let q := (μ : Measure E) (closedBall x r)
  let k := q ^ (1 / 2 : ℝ) * (c * b) ^ (1 / 2 : ℝ)
  let z₀ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • a
  have hk : ∀ z ∈ ball z₀ (R / 2), k ≤ (μ : Measure E) (closedBall z r) := by
    intro z hz
    let y := (2 : ℝ) • z - x
    have hy : y ∈ ball a R := by
      rw [mem_ball, dist_eq_norm]
      have he : y - a = (2 : ℝ) • (z - z₀) := by dsimp [y, z₀]; module
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hz' : ‖z - z₀‖ < R / 2 := by simpa only [mem_ball, dist_eq_norm] using hz
      linarith
    have hmid := hμ.closedBall_mul_le x y r (1 / 2) (by norm_num) (by norm_num)
    have he : (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y = z := by dsimp [y]; module
    rw [he] at hmid
    apply le_trans _ hmid
    dsimp [k, q, b]
    norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    gcongr
    exact hlower y hy
  have hkv : k * V ≤ b := by
    calc
      _ = ∫⁻ _ in ball z₀ (R / 2), k ∂m := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Measure.addHaar_ball_center m, V]
      _ ≤ ∫⁻ z in ball z₀ (R / 2), (μ : Measure E) (closedBall z r) ∂m :=
        setLIntegral_mono' measurableSet_ball hk
      _ ≤ ∫⁻ z, (μ : Measure E) (closedBall z r) ∂m := setLIntegral_le_lintegral _ _
      _ = b := by rw [Probability.lintegral_measure_closedBall]; simp [b]
  have hsquare : (k * V) * (k * V) ≤ b * b :=
    mul_le_mul hkv hkv (by positivity) (by positivity)
  have hsqrt (v : ENNReal) : v ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ) = v := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hkk : k * k = q * (c * b) := by
    calc
      _ = (q ^ (1 / 2 : ℝ) * q ^ (1 / 2 : ℝ)) *
          ((c * b) ^ (1 / 2 : ℝ) * (c * b) ^ (1 / 2 : ℝ)) := by dsimp [k]; ac_rfl
      _ = _ := by rw [hsqrt, hsqrt]
  have hsq : (q * (c * (V * V))) * b ≤ b * b := by
    calc
      _ = (k * k) * (V * V) := by rw [hkk]; ac_rfl
      _ = (k * V) * (k * V) := by ac_rfl
      _ ≤ _ := hsquare
  have hb0 : b ≠ 0 := (measure_closedBall_pos m _ hr).ne'
  have hbt : b ≠ ⊤ := measure_closedBall_lt_top.ne
  have hcancel := (ENNReal.mul_le_mul_iff_left hb0 hbt).mp hsq
  have hV0 : V ≠ 0 := (measure_ball_pos m _ (by positivity : 0 < R / 2)).ne'
  have hVt : V ≠ ⊤ := measure_ball_ne_top
  apply (ENNReal.mul_le_iff_le_inv (mul_ne_zero hc.ne' (mul_ne_zero hV0 hV0))
    (ENNReal.mul_ne_top hct (ENNReal.mul_ne_top hVt hVt))).mp
  simpa only [mul_comm] using hcancel

/-- Compact-set log-concavity and full-dimensional support give uniformly bounded small-ball
mass ratios. This is a bound for one fixed law, not a dimension-free KLS bound. -/
theorem exists_eventually_closedBall_le {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (m : Measure E) [m.IsAddHaarMeasure]
    (hi : (interior (μ : Measure E).support).Nonempty) :
    ∃ C : NNReal, ∀ x : E, ∀ᶠ r : ℝ in 𝓝[>] 0,
      (μ : Measure E) (closedBall x r) ≤ (C : ENNReal) * m (closedBall (0 : E) r) := by
  obtain ⟨a, R, δ, c, hR, hδ, hc, hct, hlower⟩ :=
    exists_uniform_ball_average_lower_bound hμ m hi
  let V := m (ball (0 : E) (R / 2))
  let B := (c * (V * V))⁻¹
  have hV0 : V ≠ 0 := (measure_ball_pos m _ (by positivity : 0 < R / 2)).ne'
  have hBt : B ≠ ⊤ := ENNReal.inv_ne_top.mpr (mul_ne_zero hc.ne' (mul_ne_zero hV0 hV0))
  refine ⟨B.toNNReal, fun x => ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with r hr hrδ
  rw [ENNReal.coe_toNNReal hBt]
  exact closedBall_le_of_ball_lower_bound hμ m a hR hr c hc hct (hlower r hr hrδ.le) x

/-- The absolute-continuity part of the finite-dimensional log-concave representation theorem.
Its input is the compact-set inequality and nonempty support interior; no density is assumed. -/
theorem absolutelyContinuous_of_interior_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (m : Measure E) [m.IsAddHaarMeasure]
    (hi : (interior (μ : Measure E).support).Nonempty) : (μ : Measure E) ≪ m := by
  obtain ⟨C, hC⟩ := hμ.exists_eventually_closedBall_le m hi
  apply Probability.absolutelyContinuous_of_eventually_closedBall_le (μ : Measure E) m C
  intro x
  simpa only [Measure.addHaar_closedBall_center m] using hC x

section Intrinsic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]

section IntrinsicAbsoluteContinuity

omit [CompleteSpace F]
/-- Every compact-set log-concave probability law is absolutely continuous in its own affine
support coordinates. Singular ambient measures and the zero-dimensional support are included. -/
theorem intrinsic_absolutelyContinuous {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m :=
  hμ.intrinsicMeasure.absolutelyContinuous_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty

/-- The intrinsic probability law, as well as Haar measure, assigns zero mass to the boundary
of its support. This is a consequence of the proved absolute-continuity theorem. -/
theorem intrinsic_frontier_support_eq_zero {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)
      (frontier (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction).support) = 0 := by
  exact hμ.intrinsic_absolutelyContinuous (Measure.addHaar)
    (hμ.haar_frontier_intrinsic_support Measure.addHaar)

end IntrinsicAbsoluteContinuity

end Intrinsic

end FunctionalInequalities.KLS.LogConcave
