/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.Basic
public import LeanPool.Vlasov.OT.Coupling
public import Mathlib.Analysis.ODE.Gronwall
import LeanPool.Vlasov.ForMathlib.PicardLindelof
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Characteristic construction and growth bounds

The phase-space vector field, Grönwall estimates, window predicates and characteristic
construction compile before the pushforward and fixed-point arguments that use them.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory ENNReal

/-! ## Vlasov velocity field and its Lipschitz lemma -/

/-- The Vlasov phase-space vector field:
`b_t(x, v) := (v, −(∇W ∗ ρ_t)(x))`.

Note that the first component is the identity in `v` (the position
ODE `x' = v`) and the second component is the mean-field force
`−∇W ∗ ρ_t` evaluated at `x` (the velocity ODE `v' = −(∇W ∗ ρ)(x)`).
-/
noncomputable def vlasovVectorField
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (t : ℝ) (z : PhaseSpace d) : PhaseSpace d :=
  (z.2, -(convolveFunctionMeasure gradW (ρ t) z.1))

/-- Position-side Lipschitz of the convolution `∇W ∗ ρ`.
For `gradW` L-Lipschitz and `ρ` a probability measure with finite
first moment (which guarantees integrability of the kernel), the map
`x ↦ (∇W ∗ ρ)(x)` is L-Lipschitz.

Proof sketch: by `LipschitzWith.dist_le_mul` applied pointwise to
`gradW`, then integration over the probability measure `ρ`:
  ‖∫ y, gradW(x−y) ∂ρ − ∫ y, gradW(x'−y) ∂ρ‖
    = ‖∫ y, (gradW(x−y) − gradW(x'−y)) ∂ρ‖
    ≤ ∫ y, ‖gradW(x−y) − gradW(x'−y)‖ ∂ρ
    ≤ ∫ y, L · ‖x − x'‖ ∂ρ
    = L · ‖x − x'‖ · ρ(univ)
    = L · ‖x − x'‖   (probability measure).

The integrability hypotheses on `gradW(x − ·)` for two distinct `x`s
are needed for `integral_sub` and `norm_integral_le_integral_norm`
to fire.  At the dobrushin call site these follow from finite first
moment of `ρ` + Lipschitz growth of `gradW`. -/
lemma convolveFunctionMeasure_lipschitz_in_x
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (h_int : ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) ρ) :
    LipschitzWith L (fun x => convolveFunctionMeasure gradW ρ x) := by
  refine LipschitzWith.of_dist_le_mul (fun x x' => ?_)
  unfold convolveFunctionMeasure
  rw [dist_eq_norm, ← integral_sub (h_int x) (h_int x')]
  -- Pointwise bound: ‖gradW(x − y) − gradW(x' − y)‖ ≤ L · ‖x − x'‖
  have h_pt : ∀ y, ‖gradW (x - y) - gradW (x' - y)‖ ≤ (L : ℝ) * ‖x - x'‖ :=
    fun y => by
    have h_sub : (x - y) - (x' - y) = x - x' := by
      rw [sub_sub_sub_cancel_right]
    have := hL.dist_le_mul (x - y) (x' - y)
    rw [dist_eq_norm, dist_eq_norm, h_sub] at this
    exact this
  -- Integrability of the pointwise bound function (a constant).
  have h_bound_int : Integrable (fun _ : PhysSpace d => (L : ℝ) * ‖x - x'‖) ρ :=
    integrable_const _
  -- Integrability of the norm of the difference, via mono'.
  have h_norm_int : Integrable (fun y => ‖gradW (x - y) - gradW (x' - y)‖) ρ :=
    Integrable.mono' h_bound_int ((h_int x).sub (h_int x')).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact h_pt y)
  calc ‖∫ y, gradW (x - y) - gradW (x' - y) ∂ρ‖
      ≤ ∫ y, ‖gradW (x - y) - gradW (x' - y)‖ ∂ρ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ _, (L : ℝ) * ‖x - x'‖ ∂ρ :=
        integral_mono_ae h_norm_int h_bound_int (Filter.Eventually.of_forall h_pt)
    _ = (L : ℝ) * ‖x - x'‖ := by
        simp [integral_const, measureReal_def, measure_univ]

/-- A Lipschitz force has an affine convolution bound controlled by the first moment. -/
lemma norm_convolveFunctionMeasure_le_affine
    {d : ℕ} (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (h_int : ∀ x, Integrable (fun y => gradW (x - y)) ρ)
    (h_y_int : Integrable (fun y : PhysSpace d => ‖y‖) ρ)
    (M : ℝ) (hM : ∫ y, ‖y‖ ∂ρ ≤ M) (x : PhysSpace d) :
    ‖convolveFunctionMeasure gradW ρ x‖ ≤ ‖gradW 0‖ + (L : ℝ) * M + (L : ℝ) * ‖x‖ := by
  have h_point : ∀ y, ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * (‖x‖ + ‖y‖) := by
    intro y
    have h_lipschitz := hL.dist_le_mul (x - y) 0
    simp only [dist_eq_norm, sub_zero] at h_lipschitz
    exact (norm_le_norm_add_norm_sub' (gradW (x - y)) (gradW 0)).trans
      (add_le_add le_rfl (h_lipschitz.trans
        (mul_le_mul_of_nonneg_left (norm_sub_le x y) L.coe_nonneg)))
  have h_sum_int : Integrable (fun y : PhysSpace d => ‖x‖ + ‖y‖) ρ :=
    (integrable_const ‖x‖).add h_y_int
  have h_bound_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * (‖x‖ + ‖y‖)) ρ :=
    (integrable_const ‖gradW 0‖).add (h_sum_int.const_mul (L : ℝ))
  calc
    ‖convolveFunctionMeasure gradW ρ x‖ ≤ ∫ y, ‖gradW (x - y)‖ ∂ρ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * (‖x‖ + ‖y‖)) ∂ρ :=
      integral_mono (h_int x).norm h_bound_int h_point
    _ = ‖gradW 0‖ + (L : ℝ) * (‖x‖ + ∫ y, ‖y‖ ∂ρ) := by
      rw [integral_add (integrable_const _) (h_sum_int.const_mul (L : ℝ)),
        integral_const_mul, integral_add (integrable_const _) h_y_int]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ ‖gradW 0‖ + (L : ℝ) * (‖x‖ + M) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hM) L.coe_nonneg)
    _ = ‖gradW 0‖ + (L : ℝ) * M + (L : ℝ) * ‖x‖ := by ring

/-! ## Flow distance growth bound (Gronwall on the characteristic ODE)

A standalone regularity theorem about `IsCharacteristicFlow`: solutions of
the characteristic ODE have at most linear growth in their initial condition,
with a constant depending on `T`, the Lipschitz constant of `gradW`, and a
uniform first-moment bound on the measure curve `ρ`.

Math content: Gronwall on the position-velocity pair, using
  `‖(∇W ∗ ρ_t)(x)‖ ≤ ‖gradW 0‖ + L · (‖x‖ + ∫‖y‖dρ_t)`
as the velocity-field bound. -/

/-- **`IsCharacteristicFlowOn`-flavored variant of `flow_distance_growth_bound`**.

Same Gronwall growth bound, but for a flow specified by **boundary regularity
hypotheses** (`h_init`, `h_cont_Icc`, `h_deriv_Ico`) instead of the universal-in-`t`
ODE of `IsCharacteristicFlow`.  This matches what
`exists_vlasov_characteristicFlow_global_smallT` produces (modulo deriving the
boundary regularity from `IsCharacteristicFlowOn`'s `Ioo 0 T` ODE clauses), and
mirrors the hypothesis-passing pattern of `charFlow_measurable_via_gronwall`.

**Used by**: `Phi_step` to derive the per-`z` growth bound
(`PhiAsVlasovMeasureCurve`'s `h_growth` hypothesis); window uniqueness is a
natural secondary consumer.

The global `flow_distance_growth_bound` follows by supplying its initial
condition, continuity and derivative statements as boundary regularity.

**Metric-dependence note**:
This bound uses the unbounded position difference `‖X^M(t,z) - X^{M'}(t,z)‖`,
which forces Gronwall and produces exponential-in-`T` constants
`C_T ≈ exp((1+L)·T)`.  The `Wbar = W_{min(|x-y|,1)}` analog (Dobrushin 1979, §5)
uses the bounded-and-Lipschitz absorption
  `|B_μ(x) - B_{μ'}(x)| ≤ max(2‖B‖_∞, C_B) · min(|x₁-x₂|, 1)`
and produces *linear-in-`T`* constants (Dobrushin 1979, eq. 5.7), changing this
output shape from `C_T · (‖z‖ + 1)` to a bounded analog. -/
theorem flow_distance_growth_bound_on
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    -- Boundary regularity, replacing IsCharacteristicFlow's universal ODE.
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z))
          (Set.Ici s) s)
    -- ρ regularity, identical to flow_distance_growth_bound's hypotheses.
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∃ C_T, 0 ≤ C_T ∧
      ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) := by
  -- Gronwall parameters: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ.
  set K := 1 + (L : ℝ) with hK_def
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ with hε₀_def
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Witness: C_T = gronwallBound 1 K ε₀ T.
  use gronwallBound 1 K ε₀ T
  refine ⟨?_, ?_⟩
  · have hmono := gronwallBound_mono (by norm_num : (0 : ℝ) ≤ 1) hε₀_nn hK_pos.le hT
    linarith [gronwallBound_x0 1 K ε₀]
  · intro t ht z
    -- Convolution bound: ‖(∇W ∗ ρ_t)(x)‖ ≤ ε₀ + L * ‖x‖.
    have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
        ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
      intro s hs x
      exact norm_convolveFunctionMeasure_le_affine gradW L hL (ρ s) (h_int s)
        (h_y_int s hs) M_ρ (hM_ρ s hs) x
    -- Gronwall step.  Boundary regularity comes from hypotheses, not from
    -- IsCharacteristicFlow.
    have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T) :=
      h_cont_Icc z
    have h_deriv : ∀ s ∈ Set.Ico 0 T,
        HasDerivWithinAt (fun s => (charX s z, charV s z))
          (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))
          (Set.Ici s) s := by
      intro s hs
      have hderiv := h_deriv_Ico z s hs
      -- vlasovVectorField gradW ρ s (charX s z, charV s z) = (charV s z, -conv ...)
      unfold vlasovVectorField at hderiv
      exact hderiv
    have h_init_norm : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by
      rw [h_init z]
    have h_bound : ∀ s ∈ Set.Ico 0 T,
        ‖(charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))‖ ≤
          K * ‖(charX s z, charV s z)‖ + ε₀ := by
      intro s hs
      have hs_mem : s ∈ Set.Icc 0 T := ⟨hs.1, le_of_lt hs.2⟩
      simp only [Prod.norm_def, norm_neg]
      have hFsz := le_max_left ‖charX s z‖ ‖charV s z‖
      have hGsz := le_max_right ‖charX s z‖ ‖charV s z‖
      have hM_nn : 0 ≤ max ‖charX s z‖ ‖charV s z‖ :=
        le_max_iff.mpr (Or.inl (norm_nonneg _))
      have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
              le_mul_of_one_le_left hM_nn (by linarith [NNReal.coe_nonneg L])
          _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := le_add_of_nonneg_right hε₀_nn
      have h_conv_le : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          K * max ‖charX s z‖ ‖charV s z‖ + ε₀ :=
        calc ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖
            ≤ ε₀ + (L : ℝ) * ‖charX s z‖ := h_conv_bound s hs_mem _
          _ ≤ ε₀ + K * max ‖charX s z‖ ‖charV s z‖ := by
              have hLK : (L : ℝ) ≤ K := le_add_of_nonneg_left zero_le_one
              linarith [mul_le_mul_of_nonneg_left hFsz (NNReal.coe_nonneg L),
                        mul_le_mul_of_nonneg_right hLK hM_nn]
          _ = K * max ‖charX s z‖ ‖charV s z‖ + ε₀ := by ring
      exact max_le h_v_le h_conv_le
    have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
      h_f_cont h_deriv h_init_norm h_bound t ht
    simp only [sub_zero] at h_grw
    calc ‖(charX t z, charV t z)‖
        ≤ gronwallBound ‖z‖ K ε₀ t := h_grw
      _ ≤ gronwallBound ‖z‖ K ε₀ T :=
          gronwallBound_mono (norm_nonneg _) hε₀_nn hK_pos.le ht.2
      _ ≤ gronwallBound 1 K ε₀ T * (‖z‖ + 1) := by
          rw [gronwallBound_of_K_ne_0 hK_pos.ne', gronwallBound_of_K_ne_0 hK_pos.ne']
          simp only [one_mul]
          have he1 : 0 ≤ Real.exp (K * T) - 1 :=
            by linarith [Real.one_le_exp (mul_nonneg hK_pos.le hT)]
          have hεK := div_nonneg hε₀_nn hK_pos.le
          nlinarith [norm_nonneg z, Real.exp_nonneg (K * T),
            mul_nonneg hεK he1, mul_nonneg (norm_nonneg z) (mul_nonneg hεK he1)]

/-- **Flow distance growth bound** (`L`-Lipschitz `gradW`, uniform first moment
on `ρ`).  Solutions of the characteristic ODE grow at most linearly in their
initial condition: `‖(charX t z, charV t z)‖ ≤ C_T · (‖z‖ + 1)` for some
`C_T` depending only on `T`, `L`, `‖gradW 0‖`, and the uniform first-moment
bound `M_ρ`. -/
theorem flow_distance_growth_bound
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlow gradW ρ charX charV)
    (T : ℝ) (hT : 0 ≤ T)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∃ C_T, 0 ≤ C_T ∧
      ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1) := by
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  refine flow_distance_growth_bound_on gradW L hL ρ charX charV T hT
    (fun z => Prod.ext (hflow_init z).1 (hflow_init z).2) ?_ ?_
    M_ρ hM_ρ_nn hM_ρ h_y_int h_int
  · intro z
    exact continuousOn_of_forall_continuousAt fun s _ =>
      (hflow_x s z).continuousAt.prodMk (hflow_v s z).continuousAt
  · intro z s _
    exact ((hflow_x s z).prodMk (hflow_v s z)).hasDerivWithinAt

/-- **Two-flow difference Gronwall bound** — the reusable core of the
integrated Dobrushin coupling bound.  The distance between two trajectories
`Φ_f · z₁`, `Φ_g · z₂` of flows generated by fields `b_f, b_g` (`b_f`
`L`-Lipschitz in space) grows by Gronwall: if the field difference *at the
second trajectory* is bounded by `ε` on `[0, T]` and the initial separation by
`δ`, then `‖Φ_f t z₁ - Φ_g t z₂‖ ≤ gronwallBound δ L ε t`.

Mirrors `flow_distance_growth_bound`'s Gronwall structure
(`norm_le_gronwallBound_of_norm_deriv_right_le`) but for the *difference* of two
flows.  In the integrated-bound application, `z₁ = ω.1`, `z₂ = ω.2` range over a
coupling `π₀` of `(f 0, g 0)`, `ε = (L : ℝ) * (wasserstein1 (f s) (g s)).toReal`
(the self-coupling diff-bound, uniform in the trajectory), and integrating this
pointwise bound over `π₀` against the pushforward bound gives the Dobrushin
estimate `W₁(f t, g t) ≤ … · W₁(f 0, g 0)`. -/
theorem flow_difference_growth_bound
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (b_f b_g : ℝ → α → α) (L : NNReal) (hL_f : ∀ t, LipschitzWith L (b_f t))
    (Φ_f Φ_g : ℝ → α → α) (z₁ z₂ : α)
    (T : ℝ)
    (hcont_f : ContinuousOn (fun s => Φ_f s z₁) (Set.Icc 0 T))
    (hcont_g : ContinuousOn (fun s => Φ_g s z₂) (Set.Icc 0 T))
    (hΦ_f : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_f u z₁) (b_f s (Φ_f s z₁)) (Set.Ici s) s)
    (hΦ_g : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_g u z₂) (b_g s (Φ_g s z₂)) (Set.Ici s) s)
    (δ ε : ℝ) (h_init : ‖Φ_f 0 z₁ - Φ_g 0 z₂‖ ≤ δ)
    (h_diff : ∀ s ∈ Set.Icc 0 T,
      ‖b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂)‖ ≤ ε) :
    ∀ t ∈ Set.Icc 0 T,
      ‖Φ_f t z₁ - Φ_g t z₂‖ ≤ gronwallBound δ (L : ℝ) ε t := by
  have hcont : ContinuousOn (fun s => Φ_f s z₁ - Φ_g s z₂) (Set.Icc 0 T) :=
    hcont_f.sub hcont_g
  have hderiv : ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun u => Φ_f u z₁ - Φ_g u z₂)
        (b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)) (Set.Ici s) s :=
    fun s hs => (hΦ_f s hs).sub (hΦ_g s hs)
  have hbound : ∀ s ∈ Set.Ico 0 T,
      ‖b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)‖ ≤
        (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ + ε := by
    intro s hs
    have hs_icc : s ∈ Set.Icc 0 T := ⟨hs.1, hs.2.le⟩
    have h_lip : ‖b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)‖ ≤
        (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ := by
      have := (hL_f s).dist_le_mul (Φ_f s z₁) (Φ_g s z₂)
      rwa [dist_eq_norm, dist_eq_norm] at this
    calc ‖b_f s (Φ_f s z₁) - b_g s (Φ_g s z₂)‖
        = ‖(b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)) +
            (b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂))‖ := by congr 1; abel
      _ ≤ ‖b_f s (Φ_f s z₁) - b_f s (Φ_g s z₂)‖ +
            ‖b_f s (Φ_g s z₂) - b_g s (Φ_g s z₂)‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖Φ_f s z₁ - Φ_g s z₂‖ + ε :=
            add_le_add h_lip (h_diff s hs_icc)
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv h_init hbound t ht
  simpa using hg

/-- **Per-trajectory mild (integral-form) difference bound.**
Mild-form companion to `flow_difference_growth_bound`:
the raw integral inequality
`‖γ_f t − γ_g t‖ ≤ ‖γ_f 0 − γ_g 0‖ + ∫₀ᵗ (L‖γ_f s − γ_g s‖ + ε s) ds`,
keeping the forcing `ε s` *inside* the integral.  After integrating this over
the base measure, the self-reference `ε s = L·W₁(f s,g s) ≤ L·Q(s)` is resolved
by `gronwall_mild_le` — avoiding the constant-`ε` smallness that
`flow_difference_growth_bound`'s closed form would force (and the blocked
windowing that smallness needs). -/
theorem flow_difference_mild_bound
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α]
    (b_f b_g : ℝ → α → α) (L : NNReal) (hL_f : ∀ t, LipschitzWith L (b_f t))
    (γ_f γ_g : ℝ → α) (T : ℝ)
    (hcont_f : ContinuousOn γ_f (Set.Icc 0 T))
    (hcont_g : ContinuousOn γ_g (Set.Icc 0 T))
    (hderiv_f : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt γ_f (b_f s (γ_f s)) (Set.Ioi s) s)
    (hderiv_g : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt γ_g (b_g s (γ_g s)) (Set.Ioi s) s)
    (hint : IntervalIntegrable (fun s => b_f s (γ_f s) - b_g s (γ_g s))
      MeasureTheory.volume 0 T)
    (ε : ℝ → ℝ) (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (h_diff : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖b_f s (γ_g s) - b_g s (γ_g s)‖ ≤ ε s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖γ_f t - γ_g t‖ ≤ ‖γ_f 0 - γ_g 0‖ +
        ∫ s in (0 : ℝ)..t, ((L : ℝ) * ‖γ_f s - γ_g s‖ + ε s) := by
  intro t ht
  have h0t : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hIcc_sub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right htT
  have hcont_diff : ContinuousOn (fun s => γ_f s - γ_g s) (Set.Icc 0 t) :=
    (hcont_f.mono hIcc_sub).sub (hcont_g.mono hIcc_sub)
  have hderiv_diff : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun s => γ_f s - γ_g s)
        (b_f s (γ_f s) - b_g s (γ_g s)) (Set.Ioi s) s := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs.1, hs.2.trans_le htT⟩
    exact (hderiv_f s hs').sub (hderiv_g s hs')
  have hint_t : IntervalIntegrable (fun s => b_f s (γ_f s) - b_g s (γ_g s))
      MeasureTheory.volume 0 t :=
    hint.mono_set (by
      rw [Set.uIcc_of_le h0t, Set.uIcc_of_le (h0t.trans htT)]; exact hIcc_sub)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h0t hcont_diff
    hderiv_diff hint_t
  have hsplit : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖b_f s (γ_f s) - b_g s (γ_g s)‖ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s := by
    intro s hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T := hIcc_sub hs
    have h_lip : ‖b_f s (γ_f s) - b_f s (γ_g s)‖ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ := by
      have := (hL_f s).dist_le_mul (γ_f s) (γ_g s)
      rwa [dist_eq_norm, dist_eq_norm] at this
    calc ‖b_f s (γ_f s) - b_g s (γ_g s)‖
        = ‖(b_f s (γ_f s) - b_f s (γ_g s)) + (b_f s (γ_g s) - b_g s (γ_g s))‖ := by
          congr 1; abel
      _ ≤ ‖b_f s (γ_f s) - b_f s (γ_g s)‖ + ‖b_f s (γ_g s) - b_g s (γ_g s)‖ :=
          norm_add_le _ _
      _ ≤ (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s := add_le_add h_lip (h_diff s hsT)
  have hci : IntervalIntegrable (fun s => (L:ℝ) * ‖γ_f s - γ_g s‖ + ε s)
      MeasureTheory.volume 0 t := by
    refine IntervalIntegrable.add (IntervalIntegrable.const_mul ?_ (L:ℝ))
      (hε_int.mono_set (by
        rw [Set.uIcc_of_le h0t, Set.uIcc_of_le (h0t.trans htT)]; exact hIcc_sub))
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le h0t]; exact hcont_diff.norm
  have hnorm_le : ‖∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ ≤
      ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖γ_f s - γ_g s‖ + ε s) := by
    calc ‖∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖
        ≤ ∫ s in (0 : ℝ)..t, ‖b_f s (γ_f s) - b_g s (γ_g s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm h0t
      _ ≤ ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖γ_f s - γ_g s‖ + ε s) :=
          intervalIntegral.integral_mono_on h0t hint_t.norm hci hsplit
  have ha_le : ‖γ_f t - γ_g t‖ ≤ ‖γ_f 0 - γ_g 0‖ +
      ‖∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ := by
    have heq : (γ_f t - γ_g t) - (γ_f 0 - γ_g 0) =
        ∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s)) := hftc.symm
    calc ‖γ_f t - γ_g t‖
        = ‖(γ_f 0 - γ_g 0) + ((γ_f t - γ_g t) - (γ_f 0 - γ_g 0))‖ := by congr 1; abel
      _ ≤ ‖γ_f 0 - γ_g 0‖ + ‖(γ_f t - γ_g t) - (γ_f 0 - γ_g 0)‖ := norm_add_le _ _
      _ = ‖γ_f 0 - γ_g 0‖ + ‖∫ s in (0 : ℝ)..t, (b_f s (γ_f s) - b_g s (γ_g s))‖ := by
          rw [heq]
  linarith [ha_le, hnorm_le]

/-- **Integrate a per-trajectory mild bound over the base measure (Tonelli step).**
Given a base probability measure `π` on `Ω` and a family `w : ℝ → Ω → α`, if each
trajectory satisfies the mild bound `‖w t ω‖ ≤ ‖w 0 ω‖ + ∫₀ᵗ (L‖w s ω‖ + ε s) ds`,
then the integrated quantity `Q t := ∫ ‖w t ω‖ ∂π` satisfies
`Q t ≤ Q 0 + ∫₀ᵗ (L · Q s + ε s) ds`. The `∫₀ᵗ L‖w s ω‖` term swaps via Tonelli. -/
theorem integral_mild_bound
    {Ω α : Type*} [MeasurableSpace Ω] [NormedAddCommGroup α]
    [MeasurableSpace α] [BorelSpace α]
    (π : Measure Ω) [IsProbabilityMeasure π]
    (w : ℝ → Ω → α) (L : ℝ) (hL : 0 ≤ L) (ε : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    -- joint-measurability inputs (Carathéodory: continuous-in-time + measurable-in-ω)
    (hw_cont : ∀ ω, Continuous (fun s => w s ω))
    (hw_meas : ∀ s, Measurable (w s))
    -- domination: ‖w s ω‖ ≤ dom ω uniformly on [0,T], dom integrable
    (dom : Ω → ℝ) (hdom_int : Integrable dom π)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖w s ω‖ ≤ dom ω)
    (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (hε_nn : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ ε s)
    -- the per-trajectory mild bound (e.g. from flow_difference_mild_bound)
    (hper : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖w t ω‖ ≤ ‖w 0 ω‖ + ∫ s in (0 : ℝ)..t, (L * ‖w s ω‖ + ε s)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖w t ω‖ ∂π) ≤ (∫ ω, ‖w 0 ω‖ ∂π) +
        ∫ s in (0 : ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
  -- joint measurability of `(s, ω) ↦ w s ω` and of its norm
  have hjoint : Measurable (Function.uncurry w) :=
    measurable_uncurry_of_continuous_of_measurable hw_cont hw_meas
  have hjoint_norm : Measurable (fun p : ℝ × Ω => ‖w p.1 p.2‖) := hjoint.norm
  -- abbreviation Q s := ∫ ω, ‖w s ω‖ ∂π
  set Q : ℝ → ℝ := fun s => ∫ ω, ‖w s ω‖ ∂π with hQ
  intro t ht
  have h0t : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hIcc_sub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc_right htT
  -- `w 0 ·` and `w t ·` are integrable over π (dominated by `dom`)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  have ht_mem : t ∈ Set.Icc (0 : ℝ) T := ht
  have hint0 : Integrable (fun ω => ‖w 0 ω‖) π := by
    refine hdom_int.mono' ((hw_meas 0).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hdom 0 h0_mem ω
  have hintt : Integrable (fun ω => ‖w t ω‖) π := by
    refine hdom_int.mono' ((hw_meas t).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hdom t ht_mem ω
  -- the inner integrand `g s ω := L * ‖w s ω‖ + ε s`
  set g : ℝ → Ω → ℝ := fun s ω => L * ‖w s ω‖ + ε s with hg
  -- product measure for the Tonelli swap
  -- `volume.restrict (Set.uIoc 0 t)` is a finite measure (`uIoc 0 t = Ioc 0 t`)
  have huIoc : Set.uIoc (0 : ℝ) t = Set.Ioc 0 t := Set.uIoc_of_le h0t
  have hvol_lt : MeasureTheory.volume (Set.uIoc (0 : ℝ) t) < ⊤ := by
    rw [huIoc, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hfin_restrict : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]; exact hvol_lt
  -- `ε` is integrable over `volume.restrict (uIoc 0 t)`
  have hε_int_t : IntervalIntegrable ε MeasureTheory.volume 0 t :=
    hε_int.mono_set (by
      rw [Set.uIcc_of_le h0t, Set.uIcc_of_le hT]; exact Set.Icc_subset_Icc_right htT)
  have hε_intOn : Integrable ε (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    hε_int_t.def'
  -- AEStronglyMeasurability of `uncurry g` over the product measure
  have hg_aesm : AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × Ω => L * ‖w p.1 p.2‖)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) :=
      (measurable_const.mul hjoint_norm).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ × Ω => ε p.1)
        ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) :=
      hε_intOn.aestronglyMeasurable.comp_fst
    exact h1.add h2
  -- product integrability of `uncurry g`, via the dominator `L·dom(ω) + ε(s)`
  have hdom_prod : Integrable (fun p : ℝ × Ω => L * dom p.2 + ε p.1)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) :=
    ((hdom_int.const_mul L).comp_snd
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))).add (hε_intOn.comp_fst π)
  have hae_fst : ∀ᵐ p : ℝ × Ω
      ∂((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π), p.1 ∈ Set.uIoc (0 : ℝ) t :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst).tendsto_ae.eventually
      (MeasureTheory.ae_restrict_mem measurableSet_uIoc)
  have hg_int : Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)).prod π) := by
    refine hdom_prod.mono' hg_aesm ?_
    filter_upwards [hae_fst] with p hp
    have hp_icc : p.1 ∈ Set.Icc (0 : ℝ) T := by
      rw [huIoc] at hp; exact ⟨le_of_lt hp.1, hp.2.trans htT⟩
    have hwle : ‖w p.1 p.2‖ ≤ dom p.2 := hdom p.1 hp_icc p.2
    have hεnn : 0 ≤ ε p.1 := hε_nn p.1 hp_icc
    have hg_nn : 0 ≤ L * ‖w p.1 p.2‖ + ε p.1 :=
      add_nonneg (mul_nonneg hL (norm_nonneg _)) hεnn
    change ‖L * ‖w p.1 p.2‖ + ε p.1‖ ≤ L * dom p.2 + ε p.1
    rw [Real.norm_of_nonneg hg_nn]
    nlinarith [mul_le_mul_of_nonneg_left hwle hL]
  -- inner intervalIntegral = integral against the restricted measure
  have hconv : ∀ ω, (∫ s in (0 : ℝ)..t, g s ω)
      = ∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
    intro ω
    rw [intervalIntegral.integral_of_le h0t, ← huIoc]
  -- marginal integrability `ω ↦ ∫ s, g s ω`
  have hmarg : Integrable
      (fun ω => ∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))) π :=
    hg_int.integral_prod_right
  have hinner_int : Integrable (fun ω => ∫ s in (0 : ℝ)..t, g s ω) π := by
    simpa only [hconv] using hmarg
  -- per-`s` identity  ∫ ω, g s ω ∂π = L · (∫ ω, ‖w s ω‖ ∂π) + ε s
  have hg_int_s : ∀ s ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => ‖w s ω‖) π := by
    intro s hs
    refine hdom_int.mono' ((hw_meas s).norm.aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hdom s hs ω
  have hQg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, g s ω ∂π) = L * (∫ ω, ‖w s ω‖ ∂π) + ε s := by
    intro s hs
    simp only [hg]
    rw [integral_add ((hg_int_s s hs).const_mul L) (integrable_const _), integral_const_mul]
    congr 1
    simp [integral_const, measureReal_def, measure_univ]
  -- the double integral, via Tonelli
  have hdouble : (∫ ω, (∫ s in (0 : ℝ)..t, g s ω) ∂π)
      = ∫ s in (0 : ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
    calc (∫ ω, (∫ s in (0 : ℝ)..t, g s ω) ∂π)
        = ∫ ω, (∫ s, g s ω ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))) ∂π := by
          simp only [hconv]
      _ = ∫ s, (∫ ω, g s ω ∂π) ∂(MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) :=
          (MeasureTheory.integral_integral_swap hg_int).symm
      _ = ∫ s in (0 : ℝ)..t, (∫ ω, g s ω ∂π) := by
          rw [huIoc, ← intervalIntegral.integral_of_le h0t]
      _ = ∫ s in (0 : ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
          refine intervalIntegral.integral_congr (fun s hs => ?_)
          rw [Set.uIcc_of_le h0t] at hs
          exact hQg s ⟨hs.1, hs.2.trans htT⟩
  -- assemble
  calc (∫ ω, ‖w t ω‖ ∂π)
      ≤ ∫ ω, (‖w 0 ω‖ + ∫ s in (0 : ℝ)..t, g s ω) ∂π :=
        integral_mono hintt (hint0.add hinner_int) (fun ω => hper ω t ht)
    _ = (∫ ω, ‖w 0 ω‖ ∂π) + ∫ ω, (∫ s in (0 : ℝ)..t, g s ω) ∂π :=
        integral_add hint0 hinner_int
    _ = (∫ ω, ‖w 0 ω‖ ∂π) + ∫ s in (0 : ℝ)..t, (L * (∫ ω, ‖w s ω‖ ∂π) + ε s) := by
        rw [hdouble]

/-- **Integrated coupling-Gronwall bound** (base-measure generic).

Given a base probability measure `π` on `Ω` and two parameter-families of
trajectories `X_f, X_g : ℝ → Ω → α` solving ODEs with `L`-Lipschitz vector fields
`b_f, b_g` on `[0, T]`, with a cross-field bound `‖b_f s y - b_g s y‖ ≤ ε s` whose
amplitude `ε s` is **self-referentially** controlled by the integrated trajectory
distance `Q s := ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π` (i.e. `ε s ≤ L · Q s`), the
integrated distance obeys the closed Gronwall bound
`Q t ≤ Q 0 · exp (2 L t)` on `[0, T]`.

**Composition** (the collapse pipeline):
* per-`ω`, `flow_difference_mild_bound` gives the mild integral inequality
  `‖X_f t ω - X_g t ω‖ ≤ ‖X_f 0 ω - X_g 0 ω‖ + ∫₀ᵗ (L‖X_f s ω - X_g s ω‖ + ε s)`;
* `integral_mild_bound` integrates this over `π` (Tonelli on a nonnegative
  integrand), yielding `Q t ≤ Q 0 + ∫₀ᵗ (L·Q s + ε s)`;
* the self-reference `ε s ≤ L·Q s` collapses the integrand to `2 L · Q s`;
* `gronwall_mild_le` (scalar mild Gronwall) closes to `Q 0 · exp (2 L t)`.

**Clamp bridge**: `integral_mild_bound` and the DCT continuity of `Q`
require *global*-in-`s` continuity, but the flow regularity is only on the
window `[0, T]`.  We work with the clamped flow `s ↦ X_f (clamp s) ω` (globally
continuous, agreeing with `X_f` on `[0, T]`), apply the window machinery to it,
and transfer back on `[0, T]` where `clamp = id` via integrand congruence.

**Base-measure genericity**: `π` is abstract, so this serves both the
uniqueness call site (`π = f 0`, `Q 0 = 0`, Foundation-B-free) and the
mean-field call site (`π` an optimal coupling, `Q 0 = W₁(f 0, g 0)`). -/
theorem integrated_coupling_gronwall_bound
    {Ω α : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup α] [NormedSpace ℝ α] [CompleteSpace α]
    [MeasurableSpace α] [BorelSpace α] [MeasurableSub₂ α]
    (π : Measure Ω) [IsProbabilityMeasure π]
    (X_f X_g : ℝ → Ω → α) (b_f b_g : ℝ → α → α) (L : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hL_f : ∀ t, LipschitzWith L (b_f t))
    -- per-`ω` flow regularity (matches `flow_difference_mild_bound`)
    (hcont_f : ∀ ω, ContinuousOn (fun s => X_f s ω) (Set.Icc 0 T))
    (hcont_g : ∀ ω, ContinuousOn (fun s => X_g s ω) (Set.Icc 0 T))
    (hderiv_f : ∀ ω, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => X_f s ω) (b_f s (X_f s ω)) (Set.Ioi s) s)
    (hderiv_g : ∀ ω, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => X_g s ω) (b_g s (X_g s ω)) (Set.Ioi s) s)
    (hint : ∀ ω, IntervalIntegrable
      (fun s => b_f s (X_f s ω) - b_g s (X_g s ω)) MeasureTheory.volume 0 T)
    -- measurability + domination for the Tonelli / DCT
    (hmeas_f : ∀ s, Measurable (X_f s)) (hmeas_g : ∀ s, Measurable (X_g s))
    (dom : Ω → ℝ) (hdom_int : Integrable dom π)
    (hdom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, ‖X_f s ω - X_g s ω‖ ≤ dom ω)
    -- the cross-field bound `ε` and its self-reference to `Q`
    (ε : ℝ → ℝ) (hε_int : IntervalIntegrable ε MeasureTheory.volume 0 T)
    (hε_nn : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ ε s)
    (h_diff : ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖b_f s (X_g s ω) - b_g s (X_g s ω)‖ ≤ ε s)
    (h_self : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ε s ≤ (L : ℝ) * ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖X_f t ω - X_g t ω‖ ∂π) ≤
        (∫ ω, ‖X_f 0 ω - X_g 0 ω‖ ∂π) * Real.exp (2 * (L:ℝ) * t) := by
  -- clamp into `[0, T]` (opaque; used only through its three properties)
  obtain ⟨clamp, hclamp_cont, hclamp_mem, hclamp_id⟩ :
      ∃ clamp : ℝ → ℝ, Continuous clamp ∧ (∀ s, clamp s ∈ Set.Icc (0 : ℝ) T) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T, clamp s = s) := by
    refine ⟨fun s => max 0 (min s T), ?_, ?_, ?_⟩
    · exact continuous_const.max (continuous_id.min continuous_const)
    · intro s; exact ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
    · intro s hs; change max 0 (min s T) = s
      rw [min_eq_left hs.2, max_eq_right hs.1]
  -- the clamped difference flow `W s ω = X_f (clamp s) ω - X_g (clamp s) ω`
  set W : ℝ → Ω → α := fun s ω => X_f (clamp s) ω - X_g (clamp s) ω with hW_def
  have hW_cont : ∀ ω, Continuous (fun s => W s ω) := by
    intro ω; simp only [hW_def]
    exact ((hcont_f ω).sub (hcont_g ω)).comp_continuous hclamp_cont hclamp_mem
  have hW_meas : ∀ s, Measurable (W s) := by
    intro s; simp only [hW_def]
    exact (hmeas_f (clamp s)).sub (hmeas_g (clamp s))
  have hW_dom : ∀ s, ∀ ω, ‖W s ω‖ ≤ dom ω := by
    intro s ω; simp only [hW_def]; exact hdom (clamp s) (hclamp_mem s) ω
  -- on `[0, T]`, `W` agrees with the unclamped difference, so the integrals agree
  have hQW_eq : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖W s ω‖ ∂π) = ∫ ω, ‖X_f s ω - X_g s ω‖ ∂π := by
    intro s hs
    apply integral_congr_ae
    filter_upwards with ω
    simp only [hW_def, hclamp_id s hs]
  -- per-`ω` mild bound (unclamped) via `flow_difference_mild_bound`
  have hper_w : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖X_f t ω - X_g t ω‖ ≤ ‖X_f 0 ω - X_g 0 ω‖ +
        ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖X_f s ω - X_g s ω‖ + ε s) := fun ω =>
    flow_difference_mild_bound b_f b_g L hL_f (fun s => X_f s ω) (fun s => X_g s ω) T
      (hcont_f ω) (hcont_g ω) (hderiv_f ω) (hderiv_g ω) (hint ω) ε hε_int (h_diff ω)
  -- transfer the mild bound to the clamped flow `W` (needed by `integral_mild_bound`)
  have hper_W : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖W t ω‖ ≤ ‖W 0 ω‖ + ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖W s ω‖ + ε s) := by
    intro ω t ht
    have h0t : (0 : ℝ) ≤ t := ht.1
    have hWt : W t ω = X_f t ω - X_g t ω := by simp only [hW_def, hclamp_id t ht]
    have hW0 : W 0 ω = X_f 0 ω - X_g 0 ω := by
      simp only [hW_def, hclamp_id 0 ⟨le_refl 0, hT⟩]
    have hintegrand : (∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖W s ω‖ + ε s))
        = ∫ s in (0 : ℝ)..t, ((L:ℝ) * ‖X_f s ω - X_g s ω‖ + ε s) := by
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le h0t] at hs
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      simp only [hW_def, hclamp_id s hsT]
    rw [hWt, hW0, hintegrand]; exact hper_w ω t ht
  -- integrate over `π` (Tonelli): `Q t ≤ Q 0 + ∫₀ᵗ (L·Q s + ε s)`
  have hQW := integral_mild_bound π W (L:ℝ) (NNReal.coe_nonneg L) ε T hT
    hW_cont hW_meas dom hdom_int (fun s _ ω => hW_dom s ω) hε_int hε_nn hper_W
  -- `Q` is globally continuous via DCT (clamped flow globally dominated)
  have hQW_cont : Continuous (fun s => ∫ ω, ‖W s ω‖ ∂π) := by
    refine continuous_of_dominated
      (fun s => (hW_meas s).norm.aestronglyMeasurable)
      (fun s => Filter.Eventually.of_forall (fun ω => ?_)) hdom_int
      (Filter.Eventually.of_forall (fun ω => (hW_cont ω).norm))
    rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hW_dom s ω
  -- collapse the integrand to `2 L · Q s` using the self-reference
  have hmild_W : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, ‖W t ω‖ ∂π) ≤ (∫ ω, ‖W 0 ω‖ ∂π)
        + (2 * (L:ℝ)) * ∫ s in (0 : ℝ)..t, (∫ ω, ‖W s ω‖ ∂π) := by
    intro t ht
    have h0t : (0 : ℝ) ≤ t := ht.1
    have hstep := hQW t ht
    have hII_lhs : IntervalIntegrable
        (fun s => (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s) MeasureTheory.volume 0 t :=
      ((hQW_cont.intervalIntegrable 0 t).const_mul (L:ℝ)).add
        (hε_int.mono_set (by
          rw [Set.uIcc_of_le h0t, Set.uIcc_of_le hT]
          exact Set.Icc_subset_Icc_right ht.2))
    have hII_rhs : IntervalIntegrable
        (fun s => (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π)) MeasureTheory.volume 0 t :=
      (hQW_cont.intervalIntegrable 0 t).const_mul (2 * (L:ℝ))
    have hmono : (∫ s in (0 : ℝ)..t, ((L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s))
        ≤ ∫ s in (0 : ℝ)..t, (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π) := by
      refine intervalIntegral.integral_mono_on h0t hII_lhs hII_rhs (fun s hs => ?_)
      have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have hεle : ε s ≤ (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by
        calc ε s ≤ (L:ℝ) * (∫ ω, ‖X_f s ω - X_g s ω‖ ∂π) := h_self s hsT
          _ = (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by rw [hQW_eq s hsT]
      have hring : (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π)
          = (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + (L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) := by ring
      rw [hring]; linarith [hεle]
    calc (∫ ω, ‖W t ω‖ ∂π)
        ≤ (∫ ω, ‖W 0 ω‖ ∂π)
          + ∫ s in (0 : ℝ)..t, ((L:ℝ) * (∫ ω, ‖W s ω‖ ∂π) + ε s) := hstep
      _ ≤ (∫ ω, ‖W 0 ω‖ ∂π)
          + ∫ s in (0 : ℝ)..t, (2 * (L:ℝ)) * (∫ ω, ‖W s ω‖ ∂π) := by linarith [hmono]
      _ = (∫ ω, ‖W 0 ω‖ ∂π)
          + (2 * (L:ℝ)) * ∫ s in (0 : ℝ)..t, (∫ ω, ‖W s ω‖ ∂π) := by
            rw [intervalIntegral.integral_const_mul]
  -- scalar mild Gronwall on `Q`
  have hgron := gronwall_mild_le (fun s => ∫ ω, ‖W s ω‖ ∂π)
    (∫ ω, ‖W 0 ω‖ ∂π) (2 * (L:ℝ)) T
    (by have := NNReal.coe_nonneg L; linarith)
    (integral_nonneg (fun ω => norm_nonneg _))
    hQW_cont (fun s => integral_nonneg (fun ω => norm_nonneg _)) hmild_W
  -- transfer back to the unclamped difference on `[0, T]`
  intro t ht
  rw [← hQW_eq t ht, ← hQW_eq 0 ⟨le_refl 0, hT⟩]
  exact hgron t ht

/-- **Piece A (Option 2): time-dependent moment-envelope growth bound.**

Sharper sibling of `flow_distance_growth_bound_on`.  Instead of a single
constant moment bound `M_ρ` (which forces the constant-sup growth constant
`C_T` and, downstream, an `M_f₀`-dependent fixed-point on the curve space),
this takes a **monotone time-dependent envelope** `m : ℝ → ℝ` bounding the
spatial-marginal first moment, and concludes the **time-local** Gronwall bound

  `‖(charX t z, charV t z)‖ ≤ gronwallBound ‖z‖ (1+L) (‖gradW 0‖ + L · m t) t`,

with the force constant `ε(t) = ‖gradW 0‖ + L · m t` evaluated at the SAME time
`t` (not the sup `m T`).  Monotonicity of `m` lets the per-`t` Gronwall on
`[0, t]` use the endpoint value `ε(t)` while validating the derivative bound at
every `s ≤ t` (since `ε(s) ≤ ε(t)`).

**Why this is the option-2 foundation**: integrating the conclusion over a
probability `f₀` gives `M_{Φρ}(t) ≤ A(t) + B(t)·m(t)` with
`A(t) = M_f₀·e^{(1+L)t} + (‖gradW 0‖/(1+L))(e^{(1+L)t}-1)` and
`B(t) = (L/(1+L))(e^{(1+L)t}-1)` — crucially an **`M_f₀`-free** coefficient.
The canonical envelope `m*(t) := A(t)/(1-B(T))` is then Φ-invariant under the
**data-independent** constraint `B(T) < 1`, dissolving the constant-`M`
fixed-point without a data-dependent hypothesis.  (Contrast the constant-sup
bound, which feeds `m(T)` into `ε` and re-derives an `M_f₀`-dependent
smallness.) -/
theorem flow_distance_growth_bound_on_timedep
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (_hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z))
          (Set.Ici s) s)
    (m : ℝ → ℝ) (hm_mono : MonotoneOn m (Set.Icc 0 T))
    (hm : ∀ t ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ t) ≤ m t)
    (h_y_int : ∀ t ∈ Set.Icc 0 T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t)) :
    ∀ t ∈ Set.Icc 0 T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t := by
  intro t ht z
  set K : ℝ := 1 + (L : ℝ) with hK_def
  -- m t ≥ 0 (moment of a probability measure is nonneg, bounded by m t).
  have hmt_nn : 0 ≤ m t :=
    le_trans (integral_nonneg (fun y => norm_nonneg y)) (hm t ht)
  set εt : ℝ := ‖gradW 0‖ + (L : ℝ) * m t with hεt_def
  have hK_pos : 0 < K := by positivity
  have hεt_nn : 0 ≤ εt := by positivity
  -- Convolution force bound on [0, t], using m s ≤ m t (monotone).
  have h_conv_bound : ∀ s ∈ Set.Icc 0 t, ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ εt + (L : ℝ) * ‖x‖ := by
    intro s hs x
    have hs_T : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 ht.2⟩
    exact norm_convolveFunctionMeasure_le_affine gradW L hL (ρ s) (h_int s)
      (h_y_int s hs_T) (m t) ((hm s hs_T).trans (hm_mono hs_T ht hs.2)) x
  -- Gronwall on [0, t] with the endpoint force constant εt.
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have h_f_cont : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 t) :=
    (h_cont_Icc z).mono (Set.Icc_subset_Icc_right ht.2)
  have h_deriv : ∀ s ∈ Set.Ico 0 t,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))
        (Set.Ici s) s := by
    intro s hs
    have hs_T : s ∈ Set.Ico 0 T := ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩
    have hderiv := h_deriv_Ico z s hs_T
    unfold vlasovVectorField at hderiv
    exact hderiv
  have h_init_norm : ‖(charX 0 z, charV 0 z)‖ ≤ ‖z‖ := by rw [h_init z]
  have h_bound : ∀ s ∈ Set.Ico 0 t,
      ‖(charV s z, -convolveFunctionMeasure gradW (ρ s) (charX s z))‖ ≤
        K * ‖(charX s z, charV s z)‖ + εt := by
    intro s hs
    have hs_mem : s ∈ Set.Icc 0 t := ⟨hs.1, le_of_lt hs.2⟩
    simp only [Prod.norm_def, norm_neg]
    have hFsz := le_max_left ‖charX s z‖ ‖charV s z‖
    have hGsz := le_max_right ‖charX s z‖ ‖charV s z‖
    have hM_nn : 0 ≤ max ‖charX s z‖ ‖charV s z‖ :=
      le_max_iff.mpr (Or.inl (norm_nonneg _))
    have h_v_le : ‖charV s z‖ ≤ K * max ‖charX s z‖ ‖charV s z‖ + εt :=
      calc ‖charV s z‖ ≤ max ‖charX s z‖ ‖charV s z‖ := hGsz
        _ ≤ K * max ‖charX s z‖ ‖charV s z‖ :=
            le_mul_of_one_le_left hM_nn (by linarith [NNReal.coe_nonneg L])
        _ ≤ K * max ‖charX s z‖ ‖charV s z‖ + εt := le_add_of_nonneg_right hεt_nn
    have h_conv_le : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
        K * max ‖charX s z‖ ‖charV s z‖ + εt :=
      calc ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖
          ≤ εt + (L : ℝ) * ‖charX s z‖ := h_conv_bound s hs_mem _
        _ ≤ εt + K * max ‖charX s z‖ ‖charV s z‖ := by
            have hLK : (L : ℝ) ≤ K := le_add_of_nonneg_left zero_le_one
            linarith [mul_le_mul_of_nonneg_left hFsz (NNReal.coe_nonneg L),
                      mul_le_mul_of_nonneg_right hLK hM_nn]
        _ = K * max ‖charX s z‖ ‖charV s z‖ + εt := by ring
    exact max_le h_v_le h_conv_le
  have h_grw := norm_le_gronwallBound_of_norm_deriv_right_le
    h_f_cont h_deriv h_init_norm h_bound t (Set.right_mem_Icc.mpr ht0)
  simpa using h_grw

/-- **Piece A.3 (Option 2): the canonical moment envelope closes (data-free).**

Pure-algebra companion to `flow_distance_growth_bound_on_timedep`.  Under the
**`M_f₀`-free** smallness `B(T) := (L/(1+L))(e^{(1+L)T}-1) < 1`, the explicit
envelope `m*(t) := gronwallBound M_f₀ (1+L) g0 t / (1 - B(T))` is a Gronwall
super-solution:

* monotone on `[0, T]`,
* dominates the initial moment `M_f₀`,
* **Φ-invariant** at the moment level:
  `gronwallBound M_f₀ (1+L) (g0 + L·m* t) t ≤ m* t`.

Composed with Piece A integrated over `f₀` (which gives
`M_{Φρ}(t) ≤ gronwallBound M_f₀ (1+L) (g0 + L·m(t)) t`, `g0 = ‖gradW 0‖`), this
shows the Picard iterates stay inside the fixed envelope `m*` with **no**
data-dependent hypothesis — the faithful dissolution of the constant-`M`
fixed-point.  This lemma is the measure-free heart of the option-2 escape;
Pieces B–D thread it through the curve space, `Phi_step`, and #11. -/
theorem gronwall_envelope_exists
    (M_f₀ g0 : ℝ) (hM_f₀ : 0 ≤ M_f₀) (hg0 : 0 ≤ g0)
    (L : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ m : ℝ → ℝ, MonotoneOn m (Set.Icc 0 T) ∧
      (∀ t ∈ Set.Icc 0 T, M_f₀ ≤ m t) ∧
      (∀ t ∈ Set.Icc 0 T,
        gronwallBound M_f₀ (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t ≤ m t) := by
  set K : ℝ := 1 + (L : ℝ) with hK_def
  have hK_pos : 0 < K := by positivity
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hL_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  -- B(t) and its monotonicity.
  set Bf : ℝ → ℝ := fun t => (L : ℝ) / K * (Real.exp (K * t) - 1) with hBf_def
  have hBT_lt : Bf T < 1 := hB
  have hD_pos : 0 < 1 - Bf T := by linarith
  have hD_nn : (0 : ℝ) ≤ 1 - Bf T := hD_pos.le
  have hD_ne : (1 - Bf T) ≠ 0 := ne_of_gt hD_pos
  have hLK_nn : 0 ≤ (L : ℝ) / K := div_nonneg hL_nn hK_pos.le
  have hBf_T_nn : 0 ≤ Bf T := by
    have he1 : 0 ≤ Real.exp (K * T) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (K * T) := Real.one_le_exp (by positivity)
      linarith
    exact mul_nonneg hLK_nn he1
  have hBf_le : ∀ t ∈ Set.Icc (0 : ℝ) T, Bf t ≤ Bf T := by
    intro t ht
    have hexp : Real.exp (K * t) ≤ Real.exp (K * T) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.2, hK_pos.le])
    simp only [hBf_def]
    nlinarith [hexp, hLK_nn]
  -- A(t) := gronwallBound M_f₀ K g0 t, expanded + nonneg + monotone.
  set Af : ℝ → ℝ := fun t => gronwallBound M_f₀ K g0 t with hAf_def
  have hAf_expand : ∀ t,
      Af t = M_f₀ * Real.exp (K * t) + g0 / K * (Real.exp (K * t) - 1) := by
    intro t; simp only [hAf_def]; rw [gronwallBound_of_K_ne_0 hK_ne]
  have hAf_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Af t := by
    intro t ht
    rw [hAf_expand t]
    have he1 : 0 ≤ Real.exp (K * t) - 1 := by
      have : (1 : ℝ) ≤ Real.exp (K * t) := Real.one_le_exp (by nlinarith [ht.1, hK_pos.le])
      linarith
    have hgK_nn : 0 ≤ g0 / K := div_nonneg hg0 hK_pos.le
    positivity
  have hAf_mono : MonotoneOn Af (Set.Icc 0 T) := by
    intro s _ t _ hst
    simp only [hAf_def]
    exact gronwallBound_mono hM_f₀ hg0 hK_pos.le hst
  refine ⟨fun t => Af t / (1 - Bf T), ?_, ?_, ?_⟩
  · -- monotone: Af increasing, positive constant divisor.
    intro s hs t ht hst
    change Af s / (1 - Bf T) ≤ Af t / (1 - Bf T)
    gcongr
    exact hAf_mono hs ht hst
  · -- M_f₀ ≤ m t.
    intro t ht
    have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
    have hAf0 : Af 0 = M_f₀ := by rw [hAf_expand 0]; simp [Real.exp_zero]
    have h_mono : Af 0 / (1 - Bf T) ≤ Af t / (1 - Bf T) := by
      gcongr
      exact hAf_mono h0_mem ht ht.1
    rw [hAf0] at h_mono
    have h_self : M_f₀ ≤ M_f₀ / (1 - Bf T) := by
      rw [le_div_iff₀ hD_pos]; nlinarith [hM_f₀, hBf_T_nn]
    linarith
  · -- Φ-invariance.
    intro t ht
    change gronwallBound M_f₀ K (g0 + (L : ℝ) * (Af t / (1 - Bf T))) t
        ≤ Af t / (1 - Bf T)
    have h_lhs : gronwallBound M_f₀ K (g0 + (L : ℝ) * (Af t / (1 - Bf T))) t
              = Af t + Bf t * (Af t / (1 - Bf T)) := by
      rw [gronwallBound_of_K_ne_0 hK_ne, hAf_expand t]
      simp only [hBf_def]; ring
    rw [h_lhs]
    have hkey : 0 ≤ Af t * (Bf T - Bf t) :=
      mul_nonneg (hAf_nn t ht) (by linarith [hBf_le t ht])
    have hexpand : Af t / (1 - Bf T) - (Af t + Bf t * (Af t / (1 - Bf T)))
                 = Af t * (Bf T - Bf t) / (1 - Bf T) := by
      field_simp
      ring
    linarith [div_nonneg hkey hD_pos.le, hexpand]

/-- **Piece A.2 (Option 2): integrate the per-`z` growth bound to a moment bound.**

The measure-level bridge between Piece A and Piece A.3: given the per-`z`
time-local growth bound (Piece A's conclusion, taken here as the hypothesis
`h_growth` so this lemma is decoupled from the flow construction), the
**position pushforward** `Measure.map (charX t ·) f₀` has first moment bounded
by the same Gronwall functional evaluated at the *initial* moment `∫‖z‖ ∂f₀`:

  `∫ x, ‖x‖ ∂(Measure.map (charX t ·) f₀) ≤ gronwallBound (∫‖z‖ ∂f₀) (1+L) (g0 + L·m t) t`.

Proof: `integral_map` exchanges the pushforward; `‖charX t z‖ ≤ ‖(charX t z, charV t z)‖`
+ `h_growth` bounds the integrand by `gronwallBound ‖z‖ …`, which is affine in `‖z‖`,
so its `f₀`-integral is `gronwallBound (∫‖z‖) …` (probability measure ⇒ the constant
term integrates to itself).

Composing with `gronwall_envelope_exists` (Piece A.3): when `m = m*` the canonical
envelope and `g0 = ‖gradW 0‖`, the RHS is `≤ m* t`, i.e. `Φ` maps the envelope to
itself at the moment level — the measure-level statement of the data-free escape. -/
theorem phi_moment_envelope_le {d : ℕ}
    (L : NNReal) (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (g0 : ℝ) (T : ℝ) (m : ℝ → ℝ)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤ gronwallBound ‖z‖ (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (h_meas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX t z) f₀) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ x, ‖x‖ ∂(Measure.map (fun z : PhaseSpace d => charX t z) f₀)
        ≤ gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ)) (g0 + (L : ℝ) * m t) t := by
  intro t ht
  set K : ℝ := 1 + (L : ℝ) with hK_def
  set εt : ℝ := g0 + (L : ℝ) * m t with hεt_def
  have hK_ne : K ≠ 0 := by positivity
  -- gronwallBound is affine in its initial value: gb r = e^{Kt}·r + C.
  have h_gb : ∀ r : ℝ,
      gronwallBound r K εt t = Real.exp (K * t) * r + εt / K * (Real.exp (K * t) - 1) := by
    intro r; rw [gronwallBound_of_K_ne_0 hK_ne]; ring
  have h_dom_int : Integrable (fun z : PhaseSpace d => gronwallBound ‖z‖ K εt t) f₀ := by
    simp only [h_gb]
    exact (hf₀_int.const_mul _).add (integrable_const _)
  have h_charX_le : ∀ z : PhaseSpace d, ‖charX t z‖ ≤ gronwallBound ‖z‖ K εt t := fun z =>
    le_trans (norm_fst_le (charX t z, charV t z)) (h_growth t ht z)
  have h_charX_int : Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀ :=
    h_dom_int.mono' ((h_meas t ht).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact h_charX_le z)
  rw [integral_map (h_meas t ht) continuous_norm.aestronglyMeasurable]
  calc ∫ z, ‖charX t z‖ ∂f₀
      ≤ ∫ z, gronwallBound ‖z‖ K εt t ∂f₀ :=
        integral_mono h_charX_int h_dom_int h_charX_le
    _ = gronwallBound (∫ z, ‖z‖ ∂f₀) K εt t := by
        simp only [h_gb]
        rw [integral_add (hf₀_int.const_mul _) (integrable_const _), integral_const_mul,
            integral_const]
        simp [measureReal_def, measure_univ]

/-! ## Characteristic flow existence (Picard-Lindelöf wrapper)

This section wraps the vendored parametric Picard-Lindelöf theorem
(`LeanPool.Vlasov.ForMathlib.PicardLindelof`) to extract a characteristic flow
`(charX, charV)` for the Vlasov ODE.
The four `IsPicardLindelof` hypotheses (Lipschitz-on-ball,
continuous-in-time, norm bound, contraction) are derived from
`convolveFunctionMeasure_lipschitz_in_x`, plus narrow-continuity of the
spatial-marginal curve `ρ`, plus a uniform norm bound from the
finite-mass assumption.

The contraction condition `L · max(tmax − t₀, t₀ − tmin) ≤ a − r`
pins down the local time-interval size relative to the ball radius.
For the dobrushin application we work on a finite interval `[0, T]`;
the existence theorem is parametrised by `T` and produces a flow
on `Set.Icc 0 T` (extending the local flow by stitching overlapping
windows; technically a separate iteration argument, deferred to
the proof body).

This sub-section first establishes the **global Lipschitz constant**
for `vlasovVectorField` (a direct composition of
`convolveFunctionMeasure_lipschitz_in_x` with the 1-Lipschitz
identity on the velocity coordinate, combined via `LipschitzWith.prodMk`).
The global Lipschitz immediately restricts to any closed ball,
giving the first of the four `IsPicardLindelof` fields.

The full `exists_vlasov_characteristicFlow` proof packages the global
norm bound into a per-window `IsPicardLindelof`, invokes the vendored
Picard-Lindelöf (`exists_vlasov_extend_one_window`), and stitches
`N = ⌈T/δ⌉` windows per-`z` via `HasDerivWithinAt.union` under the
position/velocity inductive invariant.  Downstream callers discharge its
`hR`/`hbound` hypotheses; the single-ball `hR` discharge in
`exists_vlasov_trajectory` is what introduces the
`LocalSmallnessPLBuffer L T := L·T² < 1` constraint — see that
theorem's docstring for the arbitrary-`L` discussion. -/

/-- Localized variant of `IsCharacteristicFlow` from `Basic.lean`:
the same initial condition + position/velocity ODEs, but quantified
over a chosen time set `s_t : Set ℝ` and initial-condition set
`s_z : Set (PhaseSpace d)`.

The global `IsCharacteristicFlow gradW ρ charX charV` is the
specialisation `IsCharacteristicFlowOn ... Set.univ Set.univ`
(modulo the unconditional init clause). -/
def IsCharacteristicFlowOn
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (s_t : Set ℝ) (s_z : Set (PhaseSpace d)) : Prop :=
  (∀ z ∈ s_z, charX 0 z = z.1 ∧ charV 0 z = z.2) ∧
  (∀ t ∈ s_t, ∀ z ∈ s_z, HasDerivAt (fun s => charX s z) (charV t z) t) ∧
  (∀ t ∈ s_t, ∀ z ∈ s_z, HasDerivAt (fun s => charV s z)
      (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t)

/-- Monotonicity of `IsCharacteristicFlowOn` in both the time set and the
initial-condition set.  Used at the end of the global existence theorem
to restrict a flow produced on `Ioo 0 (N·δ)` (covering all of `[0, T]`)
down to `Ioo 0 T`. -/
lemma IsCharacteristicFlowOn.mono
    {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d}
    {ρ : ℝ → Measure (PhysSpace d)}
    {charX charV : ℝ → PhaseSpace d → PhysSpace d}
    {s_t s_t' : Set ℝ} {s_z s_z' : Set (PhaseSpace d)}
    (h : IsCharacteristicFlowOn gradW ρ charX charV s_t s_z)
    (hs_t : s_t' ⊆ s_t) (hs_z : s_z' ⊆ s_z) :
    IsCharacteristicFlowOn gradW ρ charX charV s_t' s_z' := by
  refine ⟨fun z hz => h.1 z (hs_z hz), fun t ht z hz => ?_, fun t ht z hz => ?_⟩
  · exact h.2.1 t (hs_t ht) z (hs_z hz)
  · exact h.2.2 t (hs_t ht) z (hs_z hz)

/-- Global Lipschitz constant for the Vlasov phase-space vector field.
`b_t(x, v) = (v, -(∇W ∗ ρ_t)(x))` is `max(1, L)`-Lipschitz when
`gradW` is `L`-Lipschitz: the velocity-side projection `(x, v) ↦ v`
is 1-Lipschitz (`LipschitzWith.prod_snd`), and the force-side map
`(x, v) ↦ -(∇W ∗ ρ_t)(x)` is `L`-Lipschitz (compose
`convolveFunctionMeasure_lipschitz_in_x` with `Neg.neg` and
`Prod.fst`, both 1-Lipschitz).  Combining the two via
`LipschitzWith.prodMk` yields `max(1, L)` on the product. -/
lemma vlasovVectorField_lipschitzWith
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (t : ℝ) :
    LipschitzWith (max 1 L) (vlasovVectorField gradW ρ t) := by
  -- Force-side `x ↦ (∇W ∗ ρ_t)(x)` is `L`-Lipschitz.
  have h_conv : LipschitzWith L
      (fun x : PhysSpace d => convolveFunctionMeasure gradW (ρ t) x) :=
    convolveFunctionMeasure_lipschitz_in_x gradW L hL (ρ t) (h_int t)
  -- Negate (`Neg.neg` is 1-Lipschitz): `x ↦ -(∇W ∗ ρ_t)(x)` is still `L`-Lipschitz.
  have h_neg_conv : LipschitzWith L
      (fun x : PhysSpace d => -convolveFunctionMeasure gradW (ρ t) x) := by
    simpa [Function.comp_def] using LipschitzWith.id.neg.comp h_conv
  -- Compose with `Prod.fst` (1-Lipschitz): `z ↦ -(∇W ∗ ρ_t)(z.1)` is `L`-Lipschitz.
  have h_force : LipschitzWith L
      (fun z : PhaseSpace d => -convolveFunctionMeasure gradW (ρ t) z.1) := by
    simpa [Function.comp_def] using h_neg_conv.comp
      (LipschitzWith.prod_fst (α := PhysSpace d) (β := PhysSpace d))
  -- Combine velocity-side projection (1-Lipschitz) with force-side (L-Lipschitz).
  exact (LipschitzWith.prod_snd (α := PhysSpace d) (β := PhysSpace d)).prodMk h_force

/-- Pointwise norm bound for the Vlasov phase-space vector field.
`‖b_t(x, v)‖ ≤ max(‖v‖, ‖(∇W ∗ ρ_t)(x)‖)` for the product `max`-norm
on `PhaseSpace d = PhysSpace d × PhysSpace d`.

This is the decomposition used to derive `IsPicardLindelof.norm_le`
once a uniform bound `M` for `‖(∇W ∗ ρ_t)(x)‖` on a closed ball is
known (e.g. from finite-first-moment + Lipschitz growth of `gradW`). -/
lemma vlasovVectorField_norm_le
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d)) (t : ℝ) (z : PhaseSpace d) :
    ‖vlasovVectorField gradW ρ t z‖ ≤
      max ‖z.2‖ ‖convolveFunctionMeasure gradW (ρ t) z.1‖ := by
  unfold vlasovVectorField
  -- Prod norm is the max of component norms; neg preserves norm.
  simp [Prod.norm_def, norm_neg]

/-- **Local-flow** existence for the Vlasov ODE.

Wraps the vendored parametric Picard-Lindelöf
(`IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined`,
`LeanPool.Vlasov.ForMathlib.PicardLindelof`)
into a `HasDerivAt`-on-`Ioo`-shaped characteristic flow.  The result
holds for initial conditions inside `closedBall z₀ (a/2)` and for
times in `Ioo 0 δ` where `δ` is a Picard-derived constant.

The new hypothesis `hbound` (uniform norm bound on the convolution
force on a slightly larger ball, over `[0, 1]`) is the genuine input
the Picard wrapper needs: the contraction condition + the `norm_le`
field of `IsPicardLindelof` both require a global bound on `‖b_t‖`.

The global existence form `exists_vlasov_characteristicFlow` (below)
is the stitched version on `[0, T]`, iterating this local theorem on
overlapping windows and gluing with `ODE_solution_unique`. -/
theorem exists_vlasov_characteristicFlow_local
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    -- Local-flow data: the basepoint `z₀`, the ball radius `a`, and a
    -- uniform force bound `M` on `closedBall z₀.1 (3a/2)` over `[0,1]`.
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
              ∀ x ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 δ) (Metric.closedBall z₀ ((a : ℝ) / 2)) := by
  classical
  -- IsPicardLindelof parameter choices.
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := ‖z₀.2‖₊ + a + M with hL_pl_def
  -- δ chosen to satisfy the contraction L_pl · δ ≤ a − r_pl = a/2.
  set δ : ℝ := min 1 ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min one_pos h_ratio_pos
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := min_le_right _ _
  -- t₀ ∈ Icc 0 δ.
  let t₀ : Set.Icc (0 : ℝ) δ := ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, le_of_lt hδ_pos⟩⟩
  -- Assemble IsPicardLindelof.
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ z₀ a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (a) lipschitzOnWith via vlasovVectorField_lipschitzWith.
      intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · -- (b) continuousOn: velocity component constant in t, force continuous by hρ_cont.
      intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · -- (c) norm_le.
      intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x z₀ ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - z₀‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - z₀.2‖ ≤ ‖x - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖z₀.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - z₀.2) + z₀.2‖ ≤ ‖x.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 z₀.1 ≤ dist x z₀ := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2) := by
        have hx1d : dist x.1 z₀.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have : dist x.1 z₀.1 ≤ 3 * (a : ℝ) / 2 := by
          have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
          linarith
        exact this
      have h_t_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ht.1, le_trans ht.2 hδ_le_one⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = ‖z₀.2‖ + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add, coe_nnnorm]
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M]
            · linarith [norm_nonneg z₀.2, NNReal.coe_nonneg a]
    · -- (d) mul_max_le: L_pl · max(δ − 0, 0 − 0) = L_pl · δ ≤ a − a/2 = a/2.
      show (L_pl : ℝ) * max (δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = 0 := rfl
      simp only [ht₀_eq, sub_zero, sub_self, max_eq_left (le_of_lt hδ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]
        ring
      rw [h_a_minus_r]
      -- L_pl * δ ≤ a/2 since δ ≤ (a/2)/(L_pl+1) and L_pl ≤ L_pl + 1.
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * δ ≤ (L_pl : ℝ) *
          ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_ratio h_Lpl_nn
      have h_rewrite : (L_pl : ℝ) * ((a : ℝ) / 2 / ((L_pl : ℝ) + 1))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by ring
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h_denom_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_rewrite ▸ h_step, h_bound]
  -- Invoke headline Picard-Lindelöf.
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  -- α : PhaseSpace d → ℝ → PhaseSpace d.  Define charX, charV by projection.
  refine ⟨δ, hδ_pos, fun t z => (α z t).1, fun t z => (α z t).2, ?_, ?_, ?_⟩
  · -- Initial condition: α z 0 = z gives both component equalities.
    intro z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢
      rw [hreq]; exact hz
    have h_init : α z (t₀ : ℝ) = z := (hα z hz_in_r).1
    have ht₀_eq : (t₀ : ℝ) = 0 := rfl
    rw [ht₀_eq] at h_init
    refine ⟨?_, ?_⟩
    · change (α z 0).1 = z.1; rw [h_init]
    · change (α z 0).2 = z.2; rw [h_init]
  · -- Position ODE: HasDerivAt (charX · z) (charV t z) t.
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [this]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) δ ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).1)
        (vlasovVectorField gradW ρ t (α z t)).1 t :=
      (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj
  · -- Velocity ODE: HasDerivAt (charV · z) (−(∇W∗ρ)(charX t z)) t.
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [this]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) δ ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).2)
        (vlasovVectorField gradW ρ t (α z t)).2 t :=
      (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj

/-- **Per-z, time-shifted single-trajectory Picard with a uniform velocity-bound parameter.**

Given a fixed phase-space point `w`, a starting time `t_start`, an a priori
velocity bound `V_max ≥ ‖w.2‖`, and a uniform force bound around `w` on the
time interval `[t_start, t_start + 1]`, this produces a single trajectory
`β : ℝ → PhaseSpace d` solving the Vlasov ODE on `Ioo t_start (t_start + δ)`
with `β t_start = w`.

**Why `V_max` as a separate parameter:** the Picard contraction time δ
depends on the norm-bound `L_pl := V_max + a + M` for the vector field on
the local ball.  Phrasing this via an explicit `V_max ≥ ‖w.2‖` rather than
the tight `‖w.2‖` makes δ uniform in `w` for any iteration centered at
points `w` whose velocity component is bounded by `V_max`.  This is the
input that lets the N-window iteration in
`exists_vlasov_characteristicFlow` pick a single δ valid across all
windows (by combining with the a priori bound
`‖w_n(z).2‖ ≤ ‖z₀.2‖ + a/2 + M·(T+1)` on a finite `[0, T]`-interval).

Implementation: build an IsPicardLindelof centered at `w` over `[t_start,
t_start + δ]` with `L_pl := V_max + a + M`.  Invoke the vendored headline
theorem.  Take the single trajectory `β t := α w t`. -/
lemma exists_vlasov_extend_one_window
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (w : PhaseSpace d) (a : NNReal) (ha : 0 < a) (M : NNReal)
    (V_max : NNReal) (hV : ‖w.2‖ ≤ (V_max : ℝ))
    (t_start : ℝ)
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (β : ℝ → PhaseSpace d),
      δ = min 1 ((a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1)) ∧
      β t_start = w ∧
      (∀ t ∈ Set.Ioo t_start (t_start + δ),
        HasDerivAt (fun s => (β s).1) (β t).2 t ∧
        HasDerivAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1)) t) ∧
      (∀ t ∈ Set.Icc t_start (t_start + δ),
        HasDerivWithinAt (fun s => (β s).1) (β t).2
          (Set.Icc t_start (t_start + δ)) t ∧
        HasDerivWithinAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
          (Set.Icc t_start (t_start + δ)) t) ∧
      (∀ s ∈ Set.Icc t_start (t_start + δ), β s ∈ Metric.closedBall w (a : ℝ)) := by
  classical
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := V_max + a + M with hL_pl_def
  set δ : ℝ := min 1 ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min one_pos h_ratio_pos
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := min_le_right _ _
  let t₀ : Set.Icc t_start (t_start + δ) :=
    ⟨t_start, Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩⟩
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ w a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x w ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - w‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - w.2‖ ≤ ‖x - w‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖w.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - w.2) + w.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - w.2) + w.2‖ ≤ ‖x.2 - w.2‖ + ‖w.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 w.1 ≤ dist x w := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2) := by
        rw [Metric.mem_closedBall]
        have hx1d : dist x.1 w.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
        linarith
      have h_t_Icc : t ∈ Set.Icc t_start (t_start + 1) :=
        ⟨ht.1, le_trans ht.2 (by linarith [hδ_le_one])⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = (V_max : ℝ) + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add]
      have h_x2_bound' : ‖x.2‖ ≤ (V_max : ℝ) + (a : ℝ) :=
        le_trans h_x2_bound (by linarith [hV])
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M, h_x2_bound']
            · linarith [norm_nonneg w.2, NNReal.coe_nonneg a, NNReal.coe_nonneg V_max]
    · show (L_pl : ℝ) * max ((t_start + δ) - (t₀ : ℝ)) ((t₀ : ℝ) - t_start)
          ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = t_start := rfl
      simp only [ht₀_eq, add_sub_cancel_left, sub_self, max_eq_left (le_of_lt hδ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]; ring
      rw [h_a_minus_r]
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * δ ≤ (L_pl : ℝ) *
          ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_ratio h_Lpl_nn
      have h_rewrite : (L_pl : ℝ) * ((a : ℝ) / 2 / ((L_pl : ℝ) + 1))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by ring
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h_denom_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_rewrite ▸ h_step, h_bound]
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  have hw_in_r : w ∈ Metric.closedBall w ((r_pl : ℝ)) := by
    rw [Metric.mem_closedBall, dist_self]
    exact r_pl.coe_nonneg
  have hα_w := hα w hw_in_r
  refine ⟨δ, hδ_pos, fun t => α w t, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · have h_init : α w (t₀ : ℝ) = w := hα_w.1
    have ht₀_eq : (t₀ : ℝ) = t_start := rfl
    rw [ht₀_eq] at h_init
    exact h_init
  · intro t ht
    have h_t_Icc : t ∈ Set.Icc t_start (t_start + δ) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := hα_w.2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc t_start (t_start + δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α w) (vlasovVectorField gradW ρ t (α w t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1 t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2 t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
  · intro t ht
    have h_dw := hα_w.2.1 t ht
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivWithinAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivWithinAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
  · -- confinement: β s ∈ closedBall w a (delivered by `_confined` variant)
    intro s hs
    exact hα_w.2.2 s hs

/-! ### Per-window helpers for the N-window induction in
    `exists_vlasov_characteristicFlow`.

    These three top-level lemmas are generic in `(β, ODE, confinement,
    field bound, IH bound, reference point)` with no mention of the
    N-window induction context (no `γ_k`, `k`, `N`, `z₀`).  This
    genericity gives each helper its own elaboration budget AND makes
    them composable for future call sites — the Lagrangian → Eulerian
    chain rule, well-posedness's Banach iteration, etc.

    Composition order: Helper 1 (confinement) → Helper 2 (window-wide
    velocity bound) → Helper 3 (endpoint position bound).
-/

/-- **Helper 1: Picard window confinement (projection from phase-space ball).**

For a trajectory β satisfying the Vlasov ODE on a Picard window
`[t_start, t_start + δ]` centered at `w`, the position component
stays within the local force-bound ball:
`(β s).1 ∈ closedBall w.1 (3a/2)` for `s` in the window.

**Argument.**  The strengthened Picard-Lindelöf theorem
`exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined`
(`LeanPool.Vlasov.ForMathlib.PicardLindelof`) exposes
`FunSpace.compProj_mem_closedBall` at the public theorem level,
delivering `β s ∈ closedBall w a` (phase-space ball of radius `a` —
the outer Lipschitz radius) as a side product of the existence
guarantee.  We project this to the position component via
`Prod.dist_eq` + `le_max_left`, then loosen `a ≤ 3a/2` by arithmetic.
The result is a 3-5 line projection.

**Hypothesis `hβ_confined`** is supplied by Vlasov-side callers from
the widened `exists_vlasov_extend_one_window` output.  The other
hypotheses (ODE, field
bound, contraction inequality) are retained for genericity / call
site compatibility; they are not consumed by the projection body but
remain available for future call sites that want to re-derive the
confinement directly (e.g. via supremum trick) without invoking
the vendored Mathlib API. -/
lemma vlasov_window_confinement
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (_hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    (_h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (_hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (w : PhaseSpace d) (a : NNReal) (_ha : 0 < a) (M : NNReal)
    (V_max : NNReal) (_hV : ‖w.2‖ ≤ (V_max : ℝ))
    (t_start δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le_one : δ ≤ 1)
    (_hδ_contract : δ ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (_hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (β : ℝ → PhaseSpace d) (_hβ_init : β t_start = w)
    (_hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).1) (β t).2
        (Set.Icc t_start (t_start + δ)) t ∧
      HasDerivWithinAt (fun s => (β s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
        (Set.Icc t_start (t_start + δ)) t)
    (hβ_confined : ∀ s ∈ Set.Icc t_start (t_start + δ),
      β s ∈ Metric.closedBall w (a : ℝ)) :
    ∀ s ∈ Set.Icc t_start (t_start + δ),
      (β s).1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2) := by
  intro s hs
  have h_phase : β s ∈ Metric.closedBall w (a : ℝ) := hβ_confined s hs
  rw [Metric.mem_closedBall] at h_phase ⊢
  -- dist (β s).1 w.1 ≤ dist (β s) w ≤ a ≤ 3a/2
  have h_proj : dist (β s).1 w.1 ≤ dist (β s) w := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have h_a_nn : (0 : ℝ) ≤ (a : ℝ) := a.coe_nonneg
  linarith

/-- **Helper 2: Window-wide velocity bound.**

For a trajectory β with velocity-component ODE
`(β · ).2' = -(∇W ∗ ρ_·)((β ·).1)` on `[t_start, t_start + δ]` and
force bound M (made applicable by `h_β_in_ball`), the velocity at
every interior `s` is bounded by `h_vel_init + M · (s - t_start)`.

**Math sketch.**  One application of
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `(β · ).2`
over the convex window `Icc t_start (t_start + δ)`, with `y := s`
universally quantified:
  `‖(β s).2 - (β t_start).2‖ ≤ M · ‖s - t_start‖ = M · (s - t_start)`.
Triangle with `‖(β t_start).2‖ = ‖w.2‖ ≤ h_vel_init` (using `hβ_init`)
gives the conclusion.

The universal quantification over `y` in the mean-value lemma is what
makes this WINDOW-WIDE from ONE invocation — no per-s re-application. -/
lemma vlasov_window_velocity_bound
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (w : PhaseSpace d) (a : NNReal) (M : NNReal)
    (t_start δ : ℝ) (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h_vel_init : ℝ) (hβ_init_vel_bound : ‖w.2‖ ≤ h_vel_init)
    (β : ℝ → PhaseSpace d) (hβ_init : β t_start = w)
    (hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
        (Set.Icc t_start (t_start + δ)) t)
    (h_β_in_ball : ∀ s ∈ Set.Icc t_start (t_start + δ),
      (β s).1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2))
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + 1),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∀ s ∈ Set.Icc t_start (t_start + δ),
      ‖(β s).2‖ ≤ h_vel_init + (M : ℝ) * (s - t_start) := by
  intro s hs
  -- Convexity of the window.
  have h_convex : Convex ℝ (Set.Icc t_start (t_start + δ)) := convex_Icc _ _
  have h_t_start_in : t_start ∈ Set.Icc t_start (t_start + δ) :=
    ⟨le_refl _, by linarith⟩
  -- Force bound on the window (via h_β_in_ball).
  have h_force_window : ∀ u ∈ Set.Icc t_start (t_start + δ),
      ‖-(convolveFunctionMeasure gradW (ρ u) (β u).1)‖ ≤ (M : ℝ) := by
    intro u hu
    rw [norm_neg]
    have hu_time : u ∈ Set.Icc t_start (t_start + 1) :=
      ⟨hu.1, le_trans hu.2 (by linarith [hδ_le_one])⟩
    exact hbound u hu_time (β u).1 (h_β_in_ball u hu)
  -- Velocity ODE on the window.
  have h_vel_ode : ∀ u ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun v => (β v).2)
        (-(convolveFunctionMeasure gradW (ρ u) (β u).1))
        (Set.Icc t_start (t_start + δ)) u :=
    fun u hu => hβ_ode_Icc u hu
  -- Apply Convex.norm_image_sub_le with x := t_start, y := s.
  have h_mv : ‖(β s).2 - (β t_start).2‖ ≤ (M : ℝ) * ‖s - t_start‖ :=
    h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      h_vel_ode h_force_window h_t_start_in hs
  have h_diff_nn : 0 ≤ s - t_start := by linarith [hs.1]
  rw [Real.norm_of_nonneg h_diff_nn] at h_mv
  -- β t_start = w, so (β t_start).2 = w.2.
  have h_β_t_start_vel : (β t_start).2 = w.2 := by rw [hβ_init]
  -- Triangle: ‖(β s).2‖ ≤ ‖(β s).2 - (β t_start).2‖ + ‖(β t_start).2‖.
  have h_decomp : (β s).2 = ((β s).2 - (β t_start).2) + (β t_start).2 :=
    (sub_add_cancel _ _).symm
  have h_triangle : ‖(β s).2‖
      ≤ ‖(β s).2 - (β t_start).2‖ + ‖(β t_start).2‖ := by
    calc ‖(β s).2‖ = ‖((β s).2 - (β t_start).2) + (β t_start).2‖ := by rw [← h_decomp]
      _ ≤ _ := norm_add_le _ _
  -- Combine: ‖(β s).2‖ ≤ M·(s - t_start) + ‖w.2‖ ≤ h_vel_init + M·(s - t_start).
  rw [h_β_t_start_vel] at h_triangle
  -- h_mv has `(β t_start).2`; rewrite to `w.2` for compatibility.
  rw [h_β_t_start_vel] at h_mv
  linarith [h_mv, hβ_init_vel_bound]

/-- **Helper 3: Window endpoint position bound.**

For a trajectory β with position-component ODE
`(β · ).1' = (β · ).2` on `[t_start, t_start + δ]` and a uniform
velocity bound `V_bound` (typically Helper 2's output composed with
a worst-case substitution), the position at `t_start + δ` is bounded
relative to an explicit reference point `x_ref`:
  `‖(β (t_start + δ)).1 - x_ref‖ ≤ h_pos_init + V_bound · δ`
where `h_pos_init ≥ ‖w.1 - x_ref‖`.

**Math sketch.**  One application of
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `(β · ).1`
over the convex window with `x := t_start`, `y := t_start + δ`:
  `‖(β (t_start + δ)).1 - (β t_start).1‖ ≤ V_bound · δ` (using
  `hβ_init` for `(β t_start).1 = w.1`).
Triangle with `‖w.1 - x_ref‖ ≤ h_pos_init` gives the conclusion.

**Genericity.**  `x_ref : PhysSpace d` is an explicit parameter, NOT
hardcoded to the N-window induction's `z₀.1`.  This makes the helper
reusable for the Lagrangian → Eulerian chain rule (reference point:
support of test function φ), well-posedness's Banach iteration
(reference point: fixed-point candidate), etc. -/
lemma vlasov_window_position_bound
    {d : ℕ}
    (_gradW : PhysSpace d → PhysSpace d)
    (_ρ : ℝ → Measure (PhysSpace d))
    (w : PhaseSpace d)
    (t_start δ : ℝ) (hδ_pos : 0 < δ)
    (V_bound : ℝ)
    (x_ref : PhysSpace d)
    (h_pos_init : ℝ) (hβ_init_pos_bound : ‖w.1 - x_ref‖ ≤ h_pos_init)
    (β : ℝ → PhaseSpace d) (hβ_init : β t_start = w)
    (hβ_ode_Icc : ∀ t ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun s => (β s).1) (β t).2
        (Set.Icc t_start (t_start + δ)) t)
    (h_window_vel : ∀ s ∈ Set.Icc t_start (t_start + δ),
      ‖(β s).2‖ ≤ V_bound) :
    ‖(β (t_start + δ)).1 - x_ref‖ ≤ h_pos_init + V_bound * δ := by
  -- Convexity of the window.
  have h_convex : Convex ℝ (Set.Icc t_start (t_start + δ)) := convex_Icc _ _
  have h_t_start_in : t_start ∈ Set.Icc t_start (t_start + δ) :=
    ⟨le_refl _, by linarith⟩
  have h_t_end_in : t_start + δ ∈ Set.Icc t_start (t_start + δ) :=
    ⟨by linarith, le_refl _⟩
  -- Position ODE on the window.
  have h_pos_ode : ∀ u ∈ Set.Icc t_start (t_start + δ),
      HasDerivWithinAt (fun v => (β v).1) (β u).2
        (Set.Icc t_start (t_start + δ)) u :=
    fun u hu => hβ_ode_Icc u hu
  -- Apply Convex.norm_image_sub_le with x := t_start, y := t_start + δ.
  have h_mv : ‖(β (t_start + δ)).1 - (β t_start).1‖
              ≤ V_bound * ‖(t_start + δ) - t_start‖ :=
    h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      h_pos_ode h_window_vel h_t_start_in h_t_end_in
  have h_δ_eq : (t_start + δ) - t_start = δ := by ring
  rw [h_δ_eq, Real.norm_of_nonneg (le_of_lt hδ_pos)] at h_mv
  -- β t_start = w, so (β t_start).1 = w.1.
  have h_β_t_start_pos : (β t_start).1 = w.1 := by rw [hβ_init]
  rw [h_β_t_start_pos] at h_mv
  -- Triangle: ‖(β (t_start+δ)).1 - x_ref‖
  --        ≤ ‖(β (t_start+δ)).1 - w.1‖ + ‖w.1 - x_ref‖
  --        ≤ V_bound · δ + h_pos_init.
  have h_decomp : (β (t_start + δ)).1 - x_ref
                = ((β (t_start + δ)).1 - w.1) + (w.1 - x_ref) := by
    rw [sub_add_sub_cancel]
  have h_triangle : ‖(β (t_start + δ)).1 - x_ref‖
      ≤ ‖(β (t_start + δ)).1 - w.1‖ + ‖w.1 - x_ref‖ := by
    calc ‖(β (t_start + δ)).1 - x_ref‖
        = ‖((β (t_start + δ)).1 - w.1) + (w.1 - x_ref)‖ := by rw [← h_decomp]
      _ ≤ _ := norm_add_le _ _
  linarith [h_mv, hβ_init_pos_bound]

/-- **Tight per-window Picard with an EXPLICIT step δ and an ADAPTIVE force-window.**

Tight form of `exists_vlasov_extend_one_window`: the force bound is required
only on `[t_start, t_start + δ]` (the actual step), not the loose unit window
`[t_start, t_start + 1]`, and `δ` is supplied by the caller (so the N-window
chain can tile exactly, `N·δ = T`, dissolving the `(T+1)²` → `T²` smallness). -/
lemma exists_vlasov_extend_one_window_tight
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (w : PhaseSpace d) (a : NNReal) (ha : 0 < a) (M : NNReal)
    (V_max : NNReal) (hV : ‖w.2‖ ≤ (V_max : ℝ))
    (t_start : ℝ)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (hbound : ∀ t ∈ Set.Icc t_start (t_start + δ),
              ∀ x ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ β : ℝ → PhaseSpace d,
      β t_start = w ∧
      (∀ t ∈ Set.Ioo t_start (t_start + δ),
        HasDerivAt (fun s => (β s).1) (β t).2 t ∧
        HasDerivAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1)) t) ∧
      (∀ t ∈ Set.Icc t_start (t_start + δ),
        HasDerivWithinAt (fun s => (β s).1) (β t).2
          (Set.Icc t_start (t_start + δ)) t ∧
        HasDerivWithinAt (fun s => (β s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (β t).1))
          (Set.Icc t_start (t_start + δ)) t) ∧
      (∀ s ∈ Set.Icc t_start (t_start + δ), β s ∈ Metric.closedBall w (a : ℝ)) := by
  classical
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := V_max + a + M with hL_pl_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by positivity
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / ((L_pl : ℝ) + 1) := hδ_le
  let t₀ : Set.Icc t_start (t_start + δ) :=
    ⟨t_start, Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩⟩
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ w a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x w ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - w‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - w.2‖ ≤ ‖x - w‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖w.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - w.2) + w.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - w.2) + w.2‖ ≤ ‖x.2 - w.2‖ + ‖w.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 w.1 ≤ dist x w := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall w.1 (3 * (a : ℝ) / 2) := by
        rw [Metric.mem_closedBall]
        have hx1d : dist x.1 w.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
        linarith
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t ht x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = (V_max : ℝ) + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add]
      have h_x2_bound' : ‖x.2‖ ≤ (V_max : ℝ) + (a : ℝ) :=
        le_trans h_x2_bound (by linarith [hV])
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M, h_x2_bound']
            · linarith [norm_nonneg w.2, NNReal.coe_nonneg a, NNReal.coe_nonneg V_max]
    · show (L_pl : ℝ) * max ((t_start + δ) - (t₀ : ℝ)) ((t₀ : ℝ) - t_start)
          ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = t_start := rfl
      simp only [ht₀_eq, add_sub_cancel_left, sub_self, max_eq_left (le_of_lt hδ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]; ring
      rw [h_a_minus_r]
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * δ ≤ (L_pl : ℝ) *
          ((a : ℝ) / 2 / ((L_pl : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hδ_le_ratio h_Lpl_nn
      have h_rewrite : (L_pl : ℝ) * ((a : ℝ) / 2 / ((L_pl : ℝ) + 1))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by ring
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        rw [div_le_one h_denom_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_rewrite ▸ h_step, h_bound]
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  have hw_in_r : w ∈ Metric.closedBall w ((r_pl : ℝ)) := by
    rw [Metric.mem_closedBall, dist_self]
    exact r_pl.coe_nonneg
  have hα_w := hα w hw_in_r
  refine ⟨fun t => α w t, ?_, ?_, ?_, ?_⟩
  · have h_init : α w (t₀ : ℝ) = w := hα_w.1
    have ht₀_eq : (t₀ : ℝ) = t_start := rfl
    rw [ht₀_eq] at h_init
    exact h_init
  · intro t ht
    have h_t_Icc : t ∈ Set.Icc t_start (t_start + δ) :=
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := hα_w.2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc t_start (t_start + δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α w) (vlasovVectorField gradW ρ t (α w t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1 t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2 t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
      simpa [vlasovVectorField] using h_proj
  · intro t ht
    have h_dw := hα_w.2.1 t ht
    refine ⟨?_, ?_⟩
    · have h_proj : HasDerivWithinAt (fun s => (α w s).1)
          (vlasovVectorField gradW ρ t (α w t)).1
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
    · have h_proj : HasDerivWithinAt (fun s => (α w s).2)
          (vlasovVectorField gradW ρ t (α w t)).2
          (Set.Icc t_start (t_start + δ)) t :=
        (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivWithinAt t h_dw
      simpa [vlasovVectorField] using h_proj
  · intro s hs
    exact hα_w.2.2 s hs

/-- On the degenerate interval `Icc c c`, every function trivially has every
within-derivative at `c` (the point is not an accumulation point of the
singleton).  Serves the `T = 0` branch and the tiling base case of the tight
flow construction. -/
private lemma hasDerivWithinAt_Icc_self {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (v : E) (c : ℝ) :
    HasDerivWithinAt f v (Set.Icc c c) c := by
  have h_notAccPt : ¬ AccPt c (Filter.principal (Set.Icc c c)) := by
    rw [accPt_iff_clusterPt, Filter.inf_principal]
    simp [ClusterPt, Set.Icc_self]
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  exact HasFDerivWithinAt.of_not_accPt h_notAccPt

/-- Adaptive-window force bound for the tight tiling: on any window
`[c, c + δ] ⊆ [0, T]` whose entry position `p` satisfies the linear drift
invariant `‖p - z₀.1‖ ≤ a/2 + V_max·c`, the global `hbound` (radius `R` from
the tight `hR`) restricts to the moving ball `closedBall p (3a/2)`. -/
private lemma charFlowTight_window_forceBound
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (z₀ : PhaseSpace d) (a M V_max R : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hV_max_def : V_max = ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (c δ : ℝ) (hc_nn : 0 ≤ c) (hc_le_T : c ≤ T) (hcδ_le_T : c + δ ≤ T)
    (p : PhysSpace d)
    (hp : ‖p - z₀.1‖ ≤ (a : ℝ) / 2 + (V_max : ℝ) * c) :
    ∀ t ∈ Set.Icc c (c + δ), ∀ x ∈ Metric.closedBall p (3 * (a : ℝ) / 2),
      ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M := by
  intro t ht x hx
  have h_t_in_global : t ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_trans hc_nn ht.1, le_trans ht.2 hcδ_le_T⟩
  have h_x_local : dist x p ≤ 3 * (a : ℝ) / 2 := hx
  have h_pos_chain : dist x z₀.1
      ≤ 3 * (a : ℝ) / 2 + ((a : ℝ) / 2 + (V_max : ℝ) * c) := by
    calc dist x z₀.1
        ≤ dist x p + dist p z₀.1 := dist_triangle _ _ _
      _ ≤ 3 * (a : ℝ) / 2 + _ := by
          rw [dist_eq_norm]
          exact add_le_add h_x_local hp
  have h_V_max_coe : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * T := by
    have h_V_def : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (T.toNNReal : ℝ) := by
      simp [hV_max_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_mul, NNReal.coe_div]
    rw [h_V_def, Real.coe_toNNReal _ hT]
  have h_V_max_nn : (0 : ℝ) ≤ (V_max : ℝ) := V_max.coe_nonneg
  have h_R_expand : 2 * (a : ℝ) + (V_max : ℝ) * T ≤ R := by
    have h_ring : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * T) * T
        = 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 := by ring
    rw [h_V_max_coe, h_ring]; exact hR
  have h_x_in_R : dist x z₀.1 ≤ (R : ℝ) := by
    have h_pos_worst : (V_max : ℝ) * c ≤ (V_max : ℝ) * T :=
      mul_le_mul_of_nonneg_left hc_le_T h_V_max_nn
    linarith [h_pos_chain]
  exact hbound t h_t_in_global x h_x_in_R

/-- Mean-value velocity carry along one window: if `β` solves the velocity ODE
on `[c, b]` with force bounded by `Mr`, then `‖(β s).2‖` grows at most linearly
from its entry value.  Shared by the velocity- and position-invariant steps of
`charFlowTight_window_step`. -/
private lemma charFlowTight_window_velocity_carry
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (β : ℝ → PhaseSpace d) (c b : ℝ) (hcb : c ≤ b) (Mr : ℝ)
    (h_vel : ∀ s ∈ Set.Icc c b,
      HasDerivWithinAt (fun u => (β u).2)
        (-(convolveFunctionMeasure gradW (ρ s) (β s).1)) (Set.Icc c b) s)
    (h_force : ∀ s ∈ Set.Icc c b,
      ‖convolveFunctionMeasure gradW (ρ s) (β s).1‖ ≤ Mr) :
    ∀ s ∈ Set.Icc c b, ‖(β s).2‖ ≤ ‖(β c).2‖ + Mr * (s - c) := by
  intro s hs
  have h_convex : Convex ℝ (Set.Icc c b) := convex_Icc _ _
  have h_c_in : c ∈ Set.Icc c b := ⟨le_refl _, hcb⟩
  have h_force_neg : ∀ u ∈ Set.Icc c b,
      ‖-(convolveFunctionMeasure gradW (ρ u) (β u).1)‖ ≤ Mr := by
    intro u hu; rw [norm_neg]; exact h_force u hu
  have h_mv : ‖(β s).2 - (β c).2‖ ≤ Mr * ‖s - c‖ :=
    h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le h_vel h_force_neg h_c_in hs
  have h_diff_nn : 0 ≤ s - c := by linarith [hs.1]
  rw [Real.norm_of_nonneg h_diff_nn] at h_mv
  have h_triangle : ‖(β s).2‖ ≤ ‖(β s).2 - (β c).2‖ + ‖(β c).2‖ := by
    have h_decomp : (β s).2 = ((β s).2 - (β c).2) + (β c).2 :=
      (sub_add_cancel _ _).symm
    calc ‖(β s).2‖ = ‖((β s).2 - (β c).2) + (β c).2‖ := by rw [← h_decomp]
      _ ≤ _ := norm_add_le _ _
  linarith

/-- Gluing step for the tight tiling: the `Set.piecewise (Set.Iic c)` splice of
a left solution on `[0, c]` and a right solution on `[c, b]` (agreeing at the
join) solves the characteristic ODE system on all of `[0, b]`, via
`HasDerivWithinAt.union` on `Icc 0 c ∪ Icc c b = Icc 0 b`. -/
private lemma charFlowTight_piecewise_ode
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (γL β : ℝ → PhaseSpace d)
    (c b : ℝ) (hc_nn : 0 ≤ c) (hcb : c ≤ b)
    (h_join : β c = γL c)
    (h_ode_L : ∀ t ∈ Set.Icc (0 : ℝ) c,
      HasDerivWithinAt (fun s => (γL s).1) (γL t).2 (Set.Icc (0 : ℝ) c) t ∧
      HasDerivWithinAt (fun s => (γL s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (γL t).1)) (Set.Icc (0 : ℝ) c) t)
    (h_ode_R : ∀ t ∈ Set.Icc c b,
      HasDerivWithinAt (fun s => (β s).1) (β t).2 (Set.Icc c b) t ∧
      HasDerivWithinAt (fun s => (β s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (β t).1)) (Set.Icc c b) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) b,
      HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).1)
        (Set.piecewise (Set.Iic c) γL β t).2 (Set.Icc (0 : ℝ) b) t ∧
      HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).2)
        (-(convolveFunctionMeasure gradW (ρ t)
            (Set.piecewise (Set.Iic c) γL β t).1)) (Set.Icc (0 : ℝ) b) t := by
  classical
  intro t ht
  have h_left : ∀ y ≤ c, Set.piecewise (Set.Iic c) γL β y = γL y := fun y hy =>
    Set.piecewise_eq_of_mem _ _ _ hy
  have h_right : ∀ y, c < y → Set.piecewise (Set.Iic c) γL β y = β y := fun y hy =>
    Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hy)
  have h_at_join : Set.piecewise (Set.Iic c) γL β c = γL c := h_left _ (le_refl _)
  have h_on_right_Icc : ∀ y ∈ Set.Icc c b,
      Set.piecewise (Set.Iic c) γL β y = β y := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with hy_eq | hy_lt
    · rw [← hy_eq, h_at_join, h_join]
    · exact h_right y hy_lt
  have h_set_union : Set.Icc (0 : ℝ) c ∪ Set.Icc c b = Set.Icc (0 : ℝ) b :=
    Set.Icc_union_Icc_eq_Icc hc_nn hcb
  have hA_pos : HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).1)
      (Set.piecewise (Set.Iic c) γL β t).2 (Set.Icc (0 : ℝ) c) t := by
    by_cases ht_left : t ≤ c
    · have ht_in : t ∈ Set.Icc (0 : ℝ) c := ⟨ht.1, ht_left⟩
      have h_γL_pos := (h_ode_L t ht_in).1
      have h_deriv_eq : (Set.piecewise (Set.Iic c) γL β t).2 = (γL t).2 := by
        rw [h_left t ht_left]
      rw [h_deriv_eq]
      refine h_γL_pos.congr (fun y hy => ?_) ?_
      · rw [h_left y hy.2]
      · rw [h_left t ht_left]
    · rw [not_le] at ht_left
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc, Set.mem_Icc]
      rintro ⟨_, _⟩; linarith
  have hB_pos : HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).1)
      (Set.piecewise (Set.Iic c) γL β t).2 (Set.Icc c b) t := by
    by_cases ht_right : c ≤ t
    · have ht_in : t ∈ Set.Icc c b := ⟨ht_right, ht.2⟩
      have h_β_pos := (h_ode_R t ht_in).1
      have h_deriv_eq : (Set.piecewise (Set.Iic c) γL β t).2 = (β t).2 := by
        rw [h_on_right_Icc t ht_in]
      rw [h_deriv_eq]
      refine h_β_pos.congr (fun y hy => ?_) ?_
      · rw [h_on_right_Icc y hy]
      · rw [h_on_right_Icc t ht_in]
    · rw [not_le] at ht_right
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc, Set.mem_Icc]
      rintro ⟨_, _⟩; linarith
  have hA_vel : HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).2)
      (-(convolveFunctionMeasure gradW (ρ t)
          (Set.piecewise (Set.Iic c) γL β t).1)) (Set.Icc (0 : ℝ) c) t := by
    by_cases ht_left : t ≤ c
    · have ht_in : t ∈ Set.Icc (0 : ℝ) c := ⟨ht.1, ht_left⟩
      have h_γL_vel := (h_ode_L t ht_in).2
      have h_pos_eq : (Set.piecewise (Set.Iic c) γL β t).1 = (γL t).1 := by
        rw [h_left t ht_left]
      rw [h_pos_eq]
      refine h_γL_vel.congr (fun y hy => ?_) ?_
      · rw [h_left y hy.2]
      · rw [h_left t ht_left]
    · rw [not_le] at ht_left
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc, Set.mem_Icc]
      rintro ⟨_, _⟩; linarith
  have hB_vel : HasDerivWithinAt (fun s => (Set.piecewise (Set.Iic c) γL β s).2)
      (-(convolveFunctionMeasure gradW (ρ t)
          (Set.piecewise (Set.Iic c) γL β t).1)) (Set.Icc c b) t := by
    by_cases ht_right : c ≤ t
    · have ht_in : t ∈ Set.Icc c b := ⟨ht_right, ht.2⟩
      have h_β_vel := (h_ode_R t ht_in).2
      have h_pos_eq : (Set.piecewise (Set.Iic c) γL β t).1 = (β t).1 := by
        rw [h_on_right_Icc t ht_in]
      rw [h_pos_eq]
      refine h_β_vel.congr (fun y hy => ?_) ?_
      · rw [h_on_right_Icc y hy]
      · rw [h_on_right_Icc t ht_in]
    · rw [not_le] at ht_right
      rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
      apply HasFDerivWithinAt.of_notMem_closure
      rw [closure_Icc, Set.mem_Icc]
      rintro ⟨_, _⟩; linarith
  constructor
  · have h_union_pos := hA_pos.union hB_pos
    rw [h_set_union] at h_union_pos
    exact h_union_pos
  · have h_union_vel := hA_vel.union hB_vel
    rw [h_set_union] at h_union_vel
    exact h_union_vel

/-- One tiling step for the tight flow: extend a trajectory satisfying the
tight invariants on `[0, c]` to `[0, c + δ']` via
`exists_vlasov_extend_one_window_tight`, splicing with `Set.piecewise`
(`charFlowTight_piecewise_ode`) and carrying the linear velocity- and
position-drift invariants (`charFlowTight_window_velocity_carry` +
`vlasov_window_position_bound`). -/
private lemma charFlowTight_window_step
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M V_max R : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hV_max_def : V_max = ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (δ' : ℝ) (hδ'_pos : 0 < δ')
    (hδ'_le_max : δ' ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (z : PhaseSpace d) (c : ℝ) (hc_nn : 0 ≤ c) (hcδ_le_T : c + δ' ≤ T)
    (γ_k : ℝ → PhaseSpace d) (h_γ0 : γ_k 0 = z)
    (h_ode_k : ∀ t ∈ Set.Icc (0 : ℝ) c,
      HasDerivWithinAt (fun s => (γ_k s).1) (γ_k t).2 (Set.Icc (0 : ℝ) c) t ∧
      HasDerivWithinAt (fun s => (γ_k s).2)
        (-(convolveFunctionMeasure gradW (ρ t) (γ_k t).1)) (Set.Icc (0 : ℝ) c) t)
    (h_vel_k : ‖(γ_k c).2‖ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * c)
    (h_pos_k : ‖(γ_k c).1 - z₀.1‖ ≤ (a : ℝ) / 2 + (V_max : ℝ) * c) :
    ∃ γ : ℝ → PhaseSpace d, γ 0 = z ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (c + δ'),
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2
          (Set.Icc (0 : ℝ) (c + δ')) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
          (Set.Icc (0 : ℝ) (c + δ')) t) ∧
      ‖(γ (c + δ')).2‖ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (c + δ') ∧
      ‖(γ (c + δ')).1 - z₀.1‖ ≤ (a : ℝ) / 2 + (V_max : ℝ) * (c + δ') := by
  classical
  have hc_lt_b : c < c + δ' := by linarith
  have hc_le_T : c ≤ T := by linarith
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  have h_V_max_coe : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * T := by
    have h_V_def : (V_max : ℝ) = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (T.toNNReal : ℝ) := by
      simp [hV_max_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_mul, NNReal.coe_div]
    rw [h_V_def, Real.coe_toNNReal _ hT]
  have h_vel_Vmax : ‖(γ_k c).2‖ ≤ (V_max : ℝ) := by
    rw [h_V_max_coe]
    calc ‖(γ_k c).2‖
        ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * c := h_vel_k
      _ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * T := by
          linarith [mul_le_mul_of_nonneg_left hc_le_T hM_nn]
  have hbound_local := charFlowTight_window_forceBound gradW ρ z₀ a M V_max R T hT
    hV_max_def hR hbound c δ' hc_nn hc_le_T hcδ_le_T (γ_k c).1 h_pos_k
  obtain ⟨β, hβ_init, _hβ_ode_Ioo, hβ_ode_Icc, hβ_confined⟩ :=
    exists_vlasov_extend_one_window_tight gradW L hL ρ h_int hρ_cont
      (γ_k c) a ha M V_max h_vel_Vmax c δ' hδ'_pos hδ'_le_max hbound_local
  have h_β_in_ball : ∀ s ∈ Set.Icc c (c + δ'),
      (β s).1 ∈ Metric.closedBall (γ_k c).1 (3 * (a : ℝ) / 2) := by
    intro s hs
    have h_phase : β s ∈ Metric.closedBall (γ_k c) (a : ℝ) := hβ_confined s hs
    rw [Metric.mem_closedBall] at h_phase ⊢
    have h_proj : dist (β s).1 (γ_k c).1 ≤ dist (β s) (γ_k c) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have h_a_nn : (0 : ℝ) ≤ (a : ℝ) := a.coe_nonneg
    linarith
  have h_force_window : ∀ s ∈ Set.Icc c (c + δ'),
      ‖convolveFunctionMeasure gradW (ρ s) (β s).1‖ ≤ (M : ℝ) := fun s hs =>
    hbound_local s hs (β s).1 (h_β_in_ball s hs)
  have h_vel_carry := charFlowTight_window_velocity_carry gradW ρ β c (c + δ')
    (le_of_lt hc_lt_b) (M : ℝ) (fun s hs => (hβ_ode_Icc s hs).2) h_force_window
  have h_β_c_vel : (β c).2 = (γ_k c).2 := by rw [hβ_init]
  have h_ode_pw := charFlowTight_piecewise_ode gradW ρ γ_k β c (c + δ') hc_nn
    (le_of_lt hc_lt_b) hβ_init h_ode_k hβ_ode_Icc
  have h_right_end : Set.piecewise (Set.Iic c) γ_k β (c + δ') = β (c + δ') :=
    Set.piecewise_eq_of_notMem _ _ _ (not_le.mpr hc_lt_b)
  have h_left0 : Set.piecewise (Set.Iic c) γ_k β 0 = γ_k 0 :=
    Set.piecewise_eq_of_mem _ _ _ hc_nn
  refine ⟨Set.piecewise (Set.Iic c) γ_k β, by rw [h_left0, h_γ0], h_ode_pw, ?_, ?_⟩
  · -- Velocity invariant at the new endpoint, via the mean-value carry.
    rw [h_right_end]
    have h_carry_b := h_vel_carry (c + δ') ⟨le_of_lt hc_lt_b, le_refl _⟩
    rw [h_β_c_vel] at h_carry_b
    have h_ring : (M : ℝ) * (c + δ' - c) = (M : ℝ) * δ' := by ring
    rw [h_ring] at h_carry_b
    calc ‖(β (c + δ')).2‖
        ≤ ‖(γ_k c).2‖ + (M : ℝ) * δ' := h_carry_b
      _ ≤ ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * c + (M : ℝ) * δ' := by linarith [h_vel_k]
      _ = ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (c + δ') := by ring
  · -- Position invariant at the new endpoint, via the window position bound.
    rw [h_right_end]
    have h_window_vel_Vmax : ∀ s ∈ Set.Icc c (c + δ'),
        ‖(β s).2‖ ≤ (V_max : ℝ) := by
      intro s hs
      have h_carry_s := h_vel_carry s hs
      rw [h_β_c_vel] at h_carry_s
      have h_s_le_T : s ≤ T := le_trans hs.2 hcδ_le_T
      have h_M_split : (M : ℝ) * (s - c) + (M : ℝ) * c = (M : ℝ) * s := by ring
      have h_M_mono : (M : ℝ) * s ≤ (M : ℝ) * T :=
        mul_le_mul_of_nonneg_left h_s_le_T hM_nn
      rw [h_V_max_coe]
      linarith [h_carry_s, h_vel_k]
    have h_pos_carry :=
      vlasov_window_position_bound gradW ρ (γ_k c) c δ' hδ'_pos
        (V_max : ℝ) z₀.1 ((a : ℝ) / 2 + (V_max : ℝ) * c) h_pos_k β hβ_init
        (fun t ht => (hβ_ode_Icc t ht).1) h_window_vel_Vmax
    calc ‖(β (c + δ')).1 - z₀.1‖
        ≤ (a : ℝ) / 2 + (V_max : ℝ) * c + (V_max : ℝ) * δ' := h_pos_carry
      _ = (a : ℝ) / 2 + (V_max : ℝ) * (c + δ') := by ring

/-- Per-`z` trajectory for the tight flow: `N`-fold exact tiling of
`[0, N·δ']` by windows of width `δ'`, by induction via
`charFlowTight_window_step`, carrying the tight velocity/position invariants
through the induction and discarding them at the end. -/
private lemma charFlowTight_perZ_trajectory
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M V_max R : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (hV_max_def : V_max = ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M)
    (N : ℕ) (δ' : ℝ) (hδ'_pos : 0 < δ')
    (hδ'_le_max : δ' ≤ (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1))
    (hNδ'_le_T : (N : ℝ) * δ' ≤ T)
    (z : PhaseSpace d) (hz : z ∈ Metric.closedBall z₀ ((a : ℝ) / 2)) :
    ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      ∀ t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ'),
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2
          (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
          (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t := by
  suffices h_strong : ∀ k : ℕ, k ≤ N → ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      (∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) * δ'),
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2
          (Set.Icc (0 : ℝ) ((k : ℝ) * δ')) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
          (Set.Icc (0 : ℝ) ((k : ℝ) * δ')) t) ∧
      ‖(γ ((k : ℝ) * δ')).2‖ ≤
        ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * ((k : ℝ) * δ') ∧
      ‖(γ ((k : ℝ) * δ')).1 - z₀.1‖ ≤
        (a : ℝ) / 2 + (V_max : ℝ) * ((k : ℝ) * δ') by
    obtain ⟨γ, hγ0, hode, _, _⟩ := h_strong N (le_refl N)
    exact ⟨γ, hγ0, hode⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => z, rfl, ?_, ?_, ?_⟩
    · intro t ht
      have ht_eq : t = 0 := le_antisymm (by simpa using ht.2) ht.1
      subst ht_eq
      have h_set_eq : Set.Icc (0 : ℝ) (((0 : ℕ) : ℝ) * δ') = Set.Icc (0 : ℝ) 0 := by
        norm_num
      rw [h_set_eq]
      exact ⟨hasDerivWithinAt_Icc_self _ _ _, hasDerivWithinAt_Icc_self _ _ _⟩
    · have hdist : ‖z - z₀‖ ≤ (a : ℝ) / 2 := by
        rw [← dist_eq_norm]; exact hz
      have h_z2_proj : ‖z.2 - z₀.2‖ ≤ ‖z - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_z2_bound : ‖z.2‖ ≤ ‖z₀.2‖ + (a : ℝ) / 2 := by
        have h1 : ‖z.2‖ = ‖(z.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(z.2 - z₀.2) + z₀.2‖ ≤ ‖z.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
        linarith [h_z2_proj, hdist]
      change ‖((fun _ => z) (((0 : ℕ) : ℝ) * δ')).2‖ ≤
        ‖z₀.2‖ + (a : ℝ) / 2 + (M : ℝ) * (((0 : ℕ) : ℝ) * δ')
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      linarith
    · have hdist : ‖z - z₀‖ ≤ (a : ℝ) / 2 := by
        rw [← dist_eq_norm]; exact hz
      have h_z1_proj : ‖z.1 - z₀.1‖ ≤ ‖z - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_left _ _
      change ‖((fun _ => z) (((0 : ℕ) : ℝ) * δ')).1 - z₀.1‖ ≤
        (a : ℝ) / 2 + (V_max : ℝ) * (((0 : ℕ) : ℝ) * δ')
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      linarith
  | succ k ih =>
    intro hk_succ_le_N
    obtain ⟨γ_k, h_γ0, h_ode_k, h_vel_k, h_pos_k⟩ :=
      ih (Nat.le_of_succ_le hk_succ_le_N)
    have h_kδ_nn : (0 : ℝ) ≤ (k : ℝ) * δ' := by positivity
    have h_kδ_succ_eq : (k : ℝ) * δ' + δ' = ((k + 1 : ℕ) : ℝ) * δ' := by
      push_cast; ring
    have h_succ_kδ_le_T : ((k + 1 : ℕ) : ℝ) * δ' ≤ T := by
      calc ((k + 1 : ℕ) : ℝ) * δ'
          ≤ (N : ℝ) * δ' := by
            have h_cast : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
              exact_mod_cast hk_succ_le_N
            exact mul_le_mul_of_nonneg_right h_cast (le_of_lt hδ'_pos)
        _ ≤ T := hNδ'_le_T
    obtain ⟨γ, hγ0, h_ode, h_vel, h_pos⟩ :=
      charFlowTight_window_step gradW L hL ρ h_int hρ_cont z₀ a ha M V_max R T hT
        hV_max_def hR hbound δ' hδ'_pos hδ'_le_max z ((k : ℝ) * δ') h_kδ_nn
        (by rw [h_kδ_succ_eq]; exact h_succ_kδ_le_T) γ_k h_γ0 h_ode_k h_vel_k h_pos_k
    rw [← h_kδ_succ_eq]
    exact ⟨γ, hγ0, h_ode, h_vel, h_pos⟩

/-- **Tight global per-ball flow: `[0,T]` force-window, `T²` smallness (no `+1`).**

Tight form of `exists_vlasov_characteristicFlow`.  By tiling `[0,T]`
EXACTLY (`N = ⌈T/δ_max⌉` windows of width `δ' = T/N ≤ δ_max`, so `N·δ' = T`) and
calling `exists_vlasov_extend_one_window_tight` with the adaptive force-window
`[k·δ', (k+1)·δ']`, the global force-bound is required only on `[0,T]` and the
position drift is `M·T²` (not `M·(T+1)²`).  Consumers' R-selection then needs only
`L·T² < 1`, satisfiable for any `L` (threshold `T < 1/√L`), dissolving the `L<1`
restriction. -/
theorem exists_vlasov_characteristicFlow_tight
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal) (T : ℝ) (hT : 0 ≤ T)
    (R : NNReal)
    (hR : 2 * (a : ℝ) + (‖z₀.2‖ + (a : ℝ) / 2) * T + (M : ℝ) * T ^ 2 ≤ R)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T,
              ∀ x ∈ Metric.closedBall z₀.1 (R : ℝ),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 T) (Metric.closedBall z₀ ((a : ℝ) / 2)) ∧
      (∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s => charX s z) (charV t z)
            (Set.Icc (0 : ℝ) T) t ∧
          HasDerivWithinAt (fun s => charV s z)
            (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
            (Set.Icc (0 : ℝ) T) t) := by
  classical
  -- ============================================================
  -- Parameter setup (uniform across all windows and initial z).
  -- TIGHT: V_max uses `T` (not `T+1`); EXACT tiling N·δ' = T.
  -- ============================================================
  set V_max : NNReal :=
    ‖z₀.2‖₊ + a / 2 + M * Real.toNNReal T with hV_max_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < (((V_max + a + M : NNReal) : ℝ) + 1) := by positivity
  set δ_max : ℝ := (a : ℝ) / 2 / (((V_max + a + M : NNReal) : ℝ) + 1) with hδ_max_def
  have hδ_max_pos : (0 : ℝ) < δ_max := by rw [hδ_max_def]; positivity
  -- T = 0 edge case: the conclusion's intervals collapse.
  rcases eq_or_lt_of_le hT with hT_eq | hT_pos
  · -- T = 0: Ioo 0 0 = ∅, Icc 0 0 = {0}.  Build the trivial flow γ_func z s = z.
    subst hT_eq
    -- charX/charV constant in time, equal to z (resp. its components).
    refine ⟨fun _ z => z.1, fun _ z => z.2, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro z hz; exact ⟨rfl, rfl⟩
    · intro t ht z hz; exact absurd (lt_trans ht.1 ht.2) (lt_irrefl 0)
    · intro t ht z hz; exact absurd (lt_trans ht.1 ht.2) (lt_irrefl 0)
    · intro z hz t ht
      have ht_eq : t = 0 := le_antisymm ht.2 ht.1
      subst ht_eq
      exact ⟨hasDerivWithinAt_Icc_self _ _ _, hasDerivWithinAt_Icc_self _ _ _⟩
  · -- T > 0: EXACT tiling.
    -- N := ⌈T/δ_max⌉₊ windows of width δ' = T/N ≤ δ_max, so N·δ' = T.
    set N : ℕ := ⌈T / δ_max⌉₊ with hN_def
    have hN_pos : 0 < N := by
      rw [hN_def, Nat.ceil_pos]
      positivity
    have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    set δ' : ℝ := T / (N : ℝ) with hδ'_def
    have hδ'_pos : (0 : ℝ) < δ' := by rw [hδ'_def]; positivity
    have hNδ'_eq : (N : ℝ) * δ' = T := by
      rw [hδ'_def]; field_simp
    -- δ' ≤ δ_max because N ≥ T/δ_max.
    have hδ'_le_max : δ' ≤ δ_max := by
      have h_ceil : T / δ_max ≤ (N : ℝ) := Nat.le_ceil _
      rw [hδ'_def, div_le_iff₀ hN_real_pos]
      calc T = (T / δ_max) * δ_max := by field_simp
        _ ≤ (N : ℝ) * δ_max :=
            mul_le_mul_of_nonneg_right h_ceil (le_of_lt hδ_max_pos)
        _ = δ_max * (N : ℝ) := by ring
    -- ============================================================
    -- Per-z induction: a curve solving the ODE on [0, N·δ'] = [0, T].
    -- ============================================================
    have h_perZ : ∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
        ∃ γ : ℝ → PhaseSpace d,
          γ 0 = z ∧
          ∀ t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ'),
            HasDerivWithinAt (fun s => (γ s).1) (γ t).2
              (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t ∧
            HasDerivWithinAt (fun s => (γ s).2)
              (-(convolveFunctionMeasure gradW (ρ t) (γ t).1))
              (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t :=
      fun z hz =>
        charFlowTight_perZ_trajectory gradW L hL ρ h_int hρ_cont z₀ a ha M V_max R
          T hT hV_max_def hR hbound N δ' hδ'_pos
          (by rw [← hδ_max_def]; exact hδ'_le_max) (le_of_eq hNδ'_eq) z hz
    -- ============================================================
    -- Bundle per-z curves into a joint flow via Classical.choose.
    -- ============================================================
    let γ_func : PhaseSpace d → ℝ → PhaseSpace d := fun z =>
      if hz : z ∈ Metric.closedBall z₀ ((a : ℝ) / 2)
      then Classical.choose (h_perZ z hz)
      else (fun _ => z)
    have h_Icc_T_sub : Set.Icc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) ((N : ℝ) * δ') :=
      fun t ht => ⟨ht.1, le_trans ht.2 (le_of_eq hNδ'_eq.symm)⟩
    have h_dw_on_big :
        ∀ z ∈ Metric.closedBall z₀ ((a : ℝ) / 2),
          ∀ t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ'),
            HasDerivWithinAt (fun s => (γ_func z s).1) (γ_func z t).2
              (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t ∧
            HasDerivWithinAt (fun s => (γ_func z s).2)
              (-(convolveFunctionMeasure gradW (ρ t) (γ_func z t).1))
              (Set.Icc (0 : ℝ) ((N : ℝ) * δ')) t := by
      intro z hz t ht
      have h_func_eq : γ_func z = Classical.choose (h_perZ z hz) := by
        simp only [γ_func, dite_eq_left hz]
      have h_ode := (Classical.choose_spec (h_perZ z hz)).2
      have h_pos_dw := (h_ode t ht).1
      have h_vel_dw := (h_ode t ht).2
      have h_eq_fun_pos : (fun s => (γ_func z s).1)
          = (fun s => ((Classical.choose (h_perZ z hz)) s).1) := by
        funext s; rw [h_func_eq]
      have h_eq_fun_vel : (fun s => (γ_func z s).2)
          = (fun s => ((Classical.choose (h_perZ z hz)) s).2) := by
        funext s; rw [h_func_eq]
      have h_eq_pt_vel : (γ_func z t).2 = (Classical.choose (h_perZ z hz) t).2 := by
        rw [h_func_eq]
      have h_eq_pt_pos : (γ_func z t).1 = (Classical.choose (h_perZ z hz) t).1 := by
        rw [h_func_eq]
      refine ⟨?_, ?_⟩
      · rw [h_eq_fun_pos, h_eq_pt_vel]; exact h_pos_dw
      · rw [h_eq_fun_vel, h_eq_pt_pos]; exact h_vel_dw
    refine ⟨fun t z => (γ_func z t).1, fun t z => (γ_func z t).2,
           ⟨?_, ?_, ?_⟩, ?_⟩
    · intro z hz
      have h_init : Classical.choose (h_perZ z hz) 0 = z :=
        (Classical.choose_spec (h_perZ z hz)).1
      have h_func_eq : γ_func z = Classical.choose (h_perZ z hz) := by
        simp only [γ_func, dite_eq_left hz]
      refine ⟨?_, ?_⟩
      · change (γ_func z 0).1 = z.1
        rw [h_func_eq, h_init]
      · change (γ_func z 0).2 = z.2
        rw [h_func_eq, h_init]
    · intro t ht z hz
      have h_t_in : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ') := by
        refine ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (le_of_eq hNδ'_eq.symm)⟩
      have hT_lt_N : t < (N : ℝ) * δ' := lt_of_lt_of_le ht.2 (le_of_eq hNδ'_eq.symm)
      have h_icc_nhds : Set.Icc (0 : ℝ) ((N : ℝ) * δ') ∈ nhds t :=
        Icc_mem_nhds ht.1 hT_lt_N
      exact ((h_dw_on_big z hz t h_t_in).1).hasDerivAt h_icc_nhds
    · intro t ht z hz
      have h_t_in : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ') := by
        refine ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (le_of_eq hNδ'_eq.symm)⟩
      have hT_lt_N : t < (N : ℝ) * δ' := lt_of_lt_of_le ht.2 (le_of_eq hNδ'_eq.symm)
      have h_icc_nhds : Set.Icc (0 : ℝ) ((N : ℝ) * δ') ∈ nhds t :=
        Icc_mem_nhds ht.1 hT_lt_N
      exact ((h_dw_on_big z hz t h_t_in).2).hasDerivAt h_icc_nhds
    · intro z hz t ht
      have h_t_in_big : t ∈ Set.Icc (0 : ℝ) ((N : ℝ) * δ') :=
        h_Icc_T_sub ht
      obtain ⟨h_pos_big, h_vel_big⟩ := h_dw_on_big z hz t h_t_in_big
      exact ⟨h_pos_big.mono h_Icc_T_sub, h_vel_big.mono h_Icc_T_sub⟩

/-- **Two-window** characteristic-flow existence.

A flow on `Ioo 0 (2δ)` for some `δ > 0` and initial conditions in
`closedBall z₀ (a/2)`.  Produces a strictly longer window than
`exists_vlasov_characteristicFlow_local` (which gave `Ioo 0 δ` with
the larger `δ := (a/2)/(L_pl + 1)`); here we tighten the contraction
constraint to `L_pl · (2δ) ≤ a/2`, yielding the smaller
`δ := (a/2)/(2·(L_pl + 1))` but covering a `2δ`-long interval.

**Implementation note.**  This is a single Picard call (the vendored
`_confined` wrapper) with
`tmax = 2δ`, not a literal "two-window stitch" via uniqueness on
overlapping windows.  Mathematically the two are equivalent: a
single Picard with an extended `tmax` and tightened `δ` recovers the
same set of solutions that a two-window stitch would produce.  The
genuine two-window stitch (per-z second Picard at varying centers
glued via `ODE_solution_unique`) becomes essential only when the
single-Picard contraction cannot be satisfied — i.e., when the total
time window needed exceeds the asymptotic threshold `≈ 1/2` regardless
of `a`.  For the upcoming N-window induction follow-up, this single-
Picard extension is iterated, with each iteration using a per-z
center from the previous window's endpoint. -/
theorem exists_vlasov_characteristicFlow_twoWindow
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (z₀ : PhaseSpace d) (a : NNReal) (ha : 0 < a)
    (M : NNReal)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (1 : ℝ),
              ∀ x ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2),
              ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M) :
    ∃ (δ : ℝ) (_ : 0 < δ) (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV
        (Set.Ioo 0 (2 * δ)) (Metric.closedBall z₀ ((a : ℝ) / 2)) := by
  classical
  -- IsPicardLindelof parameter choices.  Same K_pl, r_pl, L_pl as `_local`;
  -- only the time-step δ is halved to fit the 2δ contraction.
  set K_pl : NNReal := max 1 L with hK_pl_def
  set r_pl : NNReal := a / 2 with hr_pl_def
  set L_pl : NNReal := ‖z₀.2‖₊ + a + M with hL_pl_def
  -- δ chosen so the doubled window 2δ still satisfies L_pl · (2δ) ≤ a/2.
  set δ : ℝ := min (1 / 2) ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1))) with hδ_def
  have ha_real : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h_denom_pos : (0 : ℝ) < 2 * ((L_pl : ℝ) + 1) := by positivity
  have h_ratio_pos : (0 : ℝ) < (a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)) := by positivity
  have hδ_pos : (0 : ℝ) < δ := lt_min (by norm_num) h_ratio_pos
  have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_ratio : δ ≤ (a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)) := min_le_right _ _
  have h_2δ_pos : (0 : ℝ) < 2 * δ := by linarith
  have h_2δ_le_one : 2 * δ ≤ 1 := by linarith
  -- t₀ ∈ Icc 0 (2δ).
  let t₀ : Set.Icc (0 : ℝ) (2 * δ) :=
    ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, le_of_lt h_2δ_pos⟩⟩
  -- Assemble IsPicardLindelof on time window [0, 2δ].
  have hpl : IsPicardLindelof (vlasovVectorField gradW ρ) t₀ z₀ a r_pl L_pl K_pl := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _
      exact (vlasovVectorField_lipschitzWith gradW L hL ρ h_int t).lipschitzOnWith
    · intro x _
      apply Continuous.continuousOn
      simp only [vlasovVectorField]
      exact Continuous.prodMk continuous_const (hρ_cont x.1).neg
    · -- norm_le — verbatim from `_local` (uses hbound on Icc 0 1, ball 3a/2).
      intro t ht x hx
      have h_norm_field := vlasovVectorField_norm_le gradW ρ t x
      have hdist_le : dist x z₀ ≤ (a : ℝ) := hx
      have hdist_le_norm : ‖x - z₀‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at hdist_le
      have h_x2_proj : ‖x.2 - z₀.2‖ ≤ ‖x - z₀‖ := by
        rw [Prod.norm_def]; exact le_max_right _ _
      have h_x2_bound : ‖x.2‖ ≤ ‖z₀.2‖ + (a : ℝ) := by
        have h1 : ‖x.2‖ = ‖(x.2 - z₀.2) + z₀.2‖ := by rw [sub_add_cancel]
        have h2 : ‖(x.2 - z₀.2) + z₀.2‖ ≤ ‖x.2 - z₀.2‖ + ‖z₀.2‖ := norm_add_le _ _
        linarith [h_x2_proj, hdist_le_norm]
      have h_x1_proj : dist x.1 z₀.1 ≤ dist x z₀ := by
        simp only [Prod.dist_eq]; exact le_max_left _ _
      have h_x1_ball : x.1 ∈ Metric.closedBall z₀.1 (3 * (a : ℝ) / 2) := by
        have hx1d : dist x.1 z₀.1 ≤ (a : ℝ) := le_trans h_x1_proj hdist_le
        have : dist x.1 z₀.1 ≤ 3 * (a : ℝ) / 2 := by
          have ha_nn : (0 : ℝ) ≤ (a : ℝ) := le_of_lt ha_real
          linarith
        exact this
      have h_t_Icc : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨ht.1, le_trans ht.2 h_2δ_le_one⟩
      have h_force_bound : ‖convolveFunctionMeasure gradW (ρ t) x.1‖ ≤ (M : ℝ) :=
        hbound t h_t_Icc x.1 h_x1_ball
      have h_Lpl_eq : (L_pl : ℝ) = ‖z₀.2‖ + (a : ℝ) + (M : ℝ) := by
        simp [hL_pl_def, NNReal.coe_add, coe_nnnorm]
      calc ‖vlasovVectorField gradW ρ t x‖
          ≤ max ‖x.2‖ ‖convolveFunctionMeasure gradW (ρ t) x.1‖ := h_norm_field
        _ ≤ (L_pl : ℝ) := by
            rw [h_Lpl_eq]
            apply max_le
            · linarith [NNReal.coe_nonneg M]
            · linarith [norm_nonneg z₀.2, NNReal.coe_nonneg a]
    · -- mul_max_le: L_pl · (2δ) ≤ a − a/2 = a/2.  Tighter constraint than `_local`.
      show (L_pl : ℝ) * max (2 * δ - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ (a : ℝ) - (r_pl : ℝ)
      have ht₀_eq : (t₀ : ℝ) = 0 := rfl
      simp only [ht₀_eq, sub_zero, sub_self, max_eq_left (le_of_lt h_2δ_pos)]
      have h_a_minus_r : (a : ℝ) - (r_pl : ℝ) = (a : ℝ) / 2 := by
        simp [hr_pl_def, NNReal.coe_div]; ring
      rw [h_a_minus_r]
      have h_Lpl_nn : (0 : ℝ) ≤ (L_pl : ℝ) := L_pl.coe_nonneg
      have h_a_nn : (0 : ℝ) ≤ (a : ℝ) / 2 := by linarith [ha_real]
      have h_step : (L_pl : ℝ) * (2 * δ) ≤ (L_pl : ℝ) *
          (2 * ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1)))) := by
        apply mul_le_mul_of_nonneg_left _ h_Lpl_nn
        linarith [hδ_le_ratio]
      have h_simp : (L_pl : ℝ) *
          (2 * ((a : ℝ) / 2 / (2 * ((L_pl : ℝ) + 1))))
          = (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) := by
        field_simp
      have h_frac_le : (L_pl : ℝ) / ((L_pl : ℝ) + 1) ≤ 1 := by
        have h_pos : (0 : ℝ) < (L_pl : ℝ) + 1 := by linarith
        rw [div_le_one h_pos]; linarith
      have h_bound : (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2) ≤ (a : ℝ) / 2 := by
        calc (L_pl : ℝ) / ((L_pl : ℝ) + 1) * ((a : ℝ) / 2)
            ≤ 1 * ((a : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h_frac_le h_a_nn
          _ = (a : ℝ) / 2 := one_mul _
      linarith [h_step, h_simp ▸ h_step, h_bound]
  -- Invoke headline Picard-Lindelöf on the doubled window.
  obtain ⟨α, hα⟩ := hpl.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_confined
  -- Define charX, charV by projection.
  refine ⟨δ, hδ_pos, fun t z => (α z t).1, fun t z => (α z t).2, ?_, ?_, ?_⟩
  · -- Initial condition.
    intro z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢
      rw [hreq]; exact hz
    have h_init : α z (t₀ : ℝ) = z := (hα z hz_in_r).1
    have ht₀_eq : (t₀ : ℝ) = 0 := rfl
    rw [ht₀_eq] at h_init
    refine ⟨?_, ?_⟩
    · change (α z 0).1 = z.1; rw [h_init]
    · change (α z 0).2 = z.2; rw [h_init]
  · -- Position ODE on Ioo 0 (2δ).
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [hreq]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) (2 * δ) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) (2 * δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).1)
        (vlasovVectorField gradW ρ t (α z t)).1 t :=
      (hasFDerivAt_fst (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj
  · -- Velocity ODE on Ioo 0 (2δ).
    intro t ht z hz
    have hz_in_r : z ∈ Metric.closedBall z₀ (r_pl : ℝ) := by
      have hreq : (r_pl : ℝ) = (a : ℝ) / 2 := by simp [hr_pl_def, NNReal.coe_div]
      rw [Metric.mem_closedBall] at hz ⊢; rw [hreq]; exact hz
    have h_t_Icc : t ∈ Set.Icc (0 : ℝ) (2 * δ) := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have h_dw := (hα z hz_in_r).2.1 t h_t_Icc
    have h_icc_nhds : Set.Icc (0 : ℝ) (2 * δ) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have h_d : HasDerivAt (α z) (vlasovVectorField gradW ρ t (α z t)) t :=
      h_dw.hasDerivAt h_icc_nhds
    have h_proj : HasDerivAt (fun s => (α z s).2)
        (vlasovVectorField gradW ρ t (α z t)).2 t :=
      (hasFDerivAt_snd (E := PhysSpace d) (F := PhysSpace d)).comp_hasDerivAt t h_d
    simpa [vlasovVectorField] using h_proj


end Vlasov
