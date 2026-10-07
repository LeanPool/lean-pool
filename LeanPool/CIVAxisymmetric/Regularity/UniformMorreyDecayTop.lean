/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.ThetaDecayAbsoluteConstant
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.Iteration
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyDecayAux
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantityNonneg
public import LeanPool.CIVAxisymmetric.Regularity.UniformCrudeBounds
public import LeanPool.CIVAxisymmetric.Regularity.TopCylinderContainment
public import LeanPool.CIVAxisymmetric.Regularity.ThetaContraction
public import LeanPool.CIVAxisymmetric.Regularity.ThetaDescent
public import LeanPool.CIVAxisymmetric.Regularity.EnergyIntegrable
public import LeanPool.CIVAxisymmetric.Setting.SuitableWeakSolutionClass

/-!
# Uniform interior Morrey decay near the top boundary

The heart of the uniform interior route to `CIV.timeZeroSingularSetNull`: from top-cylinder gradient
smallness at the top time slice above an interior point `x` (uniform in the base scale up to
`r₀`), together with the global energy class and a `C^2`-bounded force, there are a radius
`r₅`, a Morrey constant `M₁` and a time window `(-σ, 0)`, all independent of the interior time
`s`, such that the three scale-invariant quantities `α, β, δ²` decay like `r^{2/5}` at every
point `(x, s)` with `s` in that window and every scale `r ≤ r₅`.

The proof follows the order fixed by the route review: the absolute decay constant `C₂₇` (and
the paired `C₂₈`) are obtained once from the CKN manuscript's one-step theta-decay inequality
and threaded through both the finite descent and the below-`r₅` iteration; a scale `r₄` is
fixed so small that the force term is controlled at both thresholds; the uniform crude bound
`Θ_bar` at `r₄` is combined with a finite, entrance-controlled descent (the entrance holds only
while the base time is within `ρ²` of the top, which is exactly what bounds the number of
descent steps) to reach `r₅ := κ^N r₄` with `θ ≤ η`; and the CKN manuscript's iteration
proposition, which needs no further gradient smallness, supplies the Morrey decay below `r₅`.

The iteration phase is discharged through the general-purpose engine `CKN.iteration_of_thetaDecay`
rather than the convenience wrapper `CKN.iteration_of_sws_absolute`: the wrapper re-derives its
own existential witness for `C₂₇` internally, which cannot be forced to coincide with the `C₂₇`
already fixed from the raw one-step decay used by the descent phase. Feeding the same `C₂₇`,
`C₂₈` and the same raw decay fact to `CKN.iteration_of_thetaDecay` directly is the only way to
honor the "thread the same `C₂₇`" requirement of the route review; it is also exactly what the
wrapper's own proof does internally.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CIV

/-! ### Helper A: local reproof of the private gradient-comparison bound -/

private lemma spatialGradientSq_le_nine_local (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    ENNReal.ofReal (spatialGradientSq u Du z) ≤ 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
  have hsq : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ 2 := by
    rw [spatialGradientSq]
    calc ∑ i, ∑ j, (Du z i j) ^ (2 : ℕ)
        ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _)
            ((norm_le_pi_norm (Du z i) j).trans (norm_le_pi_norm (Du z) i)) 2
      _ = 9 * ‖Du z‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hcast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  calc ENNReal.ofReal (spatialGradientSq u Du z)
      ≤ ENNReal.ofReal (9 * ‖Du z‖ ^ 2) := ENNReal.ofReal_le_ofReal hsq
    _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
          show ENNReal.ofReal (9 : ℝ) = 9 by norm_num, ← ofReal_norm,
          ENNReal.ofReal_pow (norm_nonneg _), hcast, ENNReal.rpow_natCast]

/-- The spatial-gradient integrand of the energy class is finite over the unit cylinder,
via the pointwise comparison with the `enorm` gradient and the energy class's own finite
`H¹` conjunct. -/
theorem lintegral_spatialGradientSq_ne_top_of_globalEnergyClass
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (henergy : GlobalEnergyClass u Du p) :
    (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤ := by
  have hDufin : (∫⁻ z in unitCylinder, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    have hle : (∫⁻ z in unitCylinder, ‖Du z‖ₑ ^ (2 : ℝ)) ≤
        ∫⁻ z in unitCylinder, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ) :=
      lintegral_mono fun z => le_add_self
    exact lt_of_le_of_lt hle henergy.2.1
  have hgradle : (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      9 * ∫⁻ z in unitCylinder, ‖Du z‖ₑ ^ (2 : ℝ) := by
    calc (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w))
        ≤ ∫⁻ w in unitCylinder, 9 * ‖Du w‖ₑ ^ (2 : ℝ) :=
          lintegral_mono (spatialGradientSq_le_nine_local u Du)
      _ = 9 * ∫⁻ z in unitCylinder, ‖Du z‖ₑ ^ (2 : ℝ) := lintegral_const_mul' 9 _ (by norm_num)
  have h9fin : (9 : ℝ≥0∞) * ∫⁻ z in unitCylinder, ‖Du z‖ₑ ^ (2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (by norm_num) hDufin
  exact (lt_of_le_of_lt hgradle h9fin).ne

/-! ### Helper C: the entrance bound `β ≤ ε_*` from top-cylinder gradient smallness -/

private lemma sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
  have h4 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
  have h4' : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rwa [h4'] at h4

private lemma one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
  rwa [Real.sqrt_one] at h

/-- The entrance step: an off-centre cylinder `Q_ρ(x,s)` whose base time `s` is no more than
`ρ²` below the top boundary sits inside the top-cylinder gradient-smallness hypothesis at the
enlarged radius `√2 ρ`, and the `β`-scale quantity there is bounded by `ε_*`. -/
theorem beta_le_epsilonStar_of_top_gradient_small {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {x : Vec3} {r₀ ρ s : ℝ}
    (hρ : 0 < ρ) (hρr₀ : Real.sqrt 2 * ρ ≤ r₀) (hs : s < 0)
    (hslow : -(ρ ^ 2) ≤ s)
    (hgrad : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0, ENNReal.ofReal (spatialGradientSq u Du w)) ≤
        ENNReal.ofReal (iterationEpsilonStar C₂₇ ^ 2 / 4 * r)) :
    beta u Du (x, s) ρ ≤ iterationEpsilonStar C₂₇ := by
  set r' := Real.sqrt 2 * ρ with hr'def
  have hr'pos : 0 < r' := by positivity
  have hrr' : ρ ≤ r' := by
    have h := mul_le_mul_of_nonneg_right one_le_sqrt_two hρ.le
    rw [one_mul] at h
    rw [hr'def]
    linarith only [h]
  have hr'sq : r' ^ 2 = 2 * ρ ^ 2 := by
    rw [hr'def, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsq : ρ ^ 2 - s ≤ r' ^ 2 := by
    rw [hr'sq]; linarith only [hslow]
  have hsub := CIV.parabolicCylinder_subset_topCylinder (x := x) hs hrr' hsq
  have hmono : (∫⁻ w in parabolicCylinder x s ρ, ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      ∫⁻ w in vec3Ball x r' ×ˢ Ioo (-(r' ^ 2)) 0, ENNReal.ofReal (spatialGradientSq u Du w) :=
    lintegral_mono_set hsub
  have hgradr' := hgrad r' hr'pos hρr₀
  have hcomb : (∫⁻ w in parabolicCylinder x s ρ, ENNReal.ofReal (spatialGradientSq u Du w)) ≤
      ENNReal.ofReal (iterationEpsilonStar C₂₇ ^ 2 / 4 * r') := hmono.trans hgradr'
  have htoReal : (∫⁻ w in parabolicCylinder x s ρ,
      ENNReal.ofReal (spatialGradientSq u Du w)).toReal ≤
      iterationEpsilonStar C₂₇ ^ 2 / 4 * r' := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcomb
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have hβsq : beta u Du (x, s) ρ ^ 2 =
      ρ⁻¹ * (∫⁻ w in parabolicCylinder x s ρ, ENNReal.ofReal (spatialGradientSq u Du w)).toReal
        := by
    change ((ρ⁻¹ * (∫⁻ w in parabolicCylinder (x, s).1 (x, s).2 ρ,
        ENNReal.ofReal (spatialGradientSq u Du w)).toReal) ^ (1 / 2 : ℝ)) ^ 2 = _
    exact CKN.Foundation.Euclidean.rpow_half_sq_of_nonneg (by positivity)
  have hβsq_le : beta u Du (x, s) ρ ^ 2 ≤ Real.sqrt 2 * iterationEpsilonStar C₂₇ ^ 2 / 4 := by
    rw [hβsq]
    have hmul : ρ⁻¹ * (∫⁻ w in parabolicCylinder x s ρ,
        ENNReal.ofReal (spatialGradientSq u Du w)).toReal ≤
        ρ⁻¹ * (iterationEpsilonStar C₂₇ ^ 2 / 4 * r') :=
      mul_le_mul_of_nonneg_left htoReal (inv_nonneg.mpr hρ.le)
    have heq : ρ⁻¹ * (iterationEpsilonStar C₂₇ ^ 2 / 4 * r') =
        Real.sqrt 2 * iterationEpsilonStar C₂₇ ^ 2 / 4 := by
      rw [hr'def]
      field_simp
    linarith only [hmul, heq]
  have hβnonneg : 0 ≤ beta u Du (x, s) ρ := beta_nonneg u Du (x, s) hρ.le
  have hεstarnonneg : 0 ≤ iterationEpsilonStar C₂₇ := (iterationEpsilonStar_pos hC₂₇).le
  have hfactor_le_one : Real.sqrt 2 / 4 ≤ 1 := by
    linarith only [sqrt_two_le_two]
  have hβsq_le_ε2 : beta u Du (x, s) ρ ^ 2 ≤ iterationEpsilonStar C₂₇ ^ 2 := by
    calc beta u Du (x, s) ρ ^ 2 ≤ Real.sqrt 2 * iterationEpsilonStar C₂₇ ^ 2 / 4 := hβsq_le
      _ = Real.sqrt 2 / 4 * iterationEpsilonStar C₂₇ ^ 2 := by ring
      _ ≤ 1 * iterationEpsilonStar C₂₇ ^ 2 :=
          mul_le_mul_of_nonneg_right hfactor_le_one (sq_nonneg _)
      _ = iterationEpsilonStar C₂₇ ^ 2 := by ring
  exact (abs_le_of_sq_le_sq' hβsq_le_ε2 hεstarnonneg).2

/-! ### Helper D: a small radius with a cubic force bound -/

/-- A pure real-number existence lemma: given a nonnegative force coefficient `Cf`, a positive
outer radius `r₀` and a positive target `B`, there is a scale `r₄ ≤ r₀ / 2` with
`Cf * r₄ ^ 3 ≤ B`. -/
theorem exists_r4_le_of_cube_bound {Cf r₀ B : ℝ} (hCf : 0 ≤ Cf) (hr₀ : 0 < r₀) (hB : 0 < B) :
    ∃ r₄ : ℝ, 0 < r₄ ∧ r₄ ≤ r₀ / 2 ∧ Cf * r₄ ^ 3 ≤ B := by
  set D : ℝ := Cf * (r₀ / 2) ^ 2 with hDdef
  have hDnonneg : 0 ≤ D := by positivity
  set r₄ : ℝ := min (r₀ / 2) (B / (D + 1)) with hr₄def
  have hr₀half : 0 < r₀ / 2 := by positivity
  have hDplus1 : 0 < D + 1 := lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_left hDnonneg)
  have hquot : 0 < B / (D + 1) := div_pos hB hDplus1
  have hr₄pos : 0 < r₄ := lt_min hr₀half hquot
  have hr₄half : r₄ ≤ r₀ / 2 := min_le_left _ _
  have hr₄quot : r₄ ≤ B / (D + 1) := min_le_right _ _
  refine ⟨r₄, hr₄pos, hr₄half, ?_⟩
  have hr₄sq : r₄ ^ 2 ≤ (r₀ / 2) ^ 2 := pow_le_pow_left₀ hr₄pos.le hr₄half 2
  have hcube : r₄ ^ 3 ≤ (r₀ / 2) ^ 2 * r₄ := by
    have h := mul_le_mul_of_nonneg_right hr₄sq hr₄pos.le
    calc r₄ ^ 3 = r₄ ^ 2 * r₄ := by ring
      _ ≤ (r₀ / 2) ^ 2 * r₄ := h
  have hCfcube : Cf * r₄ ^ 3 ≤ D * r₄ := by
    calc Cf * r₄ ^ 3 ≤ Cf * ((r₀ / 2) ^ 2 * r₄) := mul_le_mul_of_nonneg_left hcube hCf
      _ = D * r₄ := by rw [hDdef]; ring
  have hDrquot : D * r₄ ≤ D * (B / (D + 1)) := mul_le_mul_of_nonneg_left hr₄quot hDnonneg
  have hDratio : D / (D + 1) ≤ 1 := by
    rw [div_le_one hDplus1]
    exact le_add_of_nonneg_right (by norm_num)
  have hfinal : D * (B / (D + 1)) ≤ B := by
    have heq : D * (B / (D + 1)) = B * (D / (D + 1)) := by ring
    rw [heq]
    calc B * (D / (D + 1)) ≤ B * 1 := mul_le_mul_of_nonneg_left hDratio hB.le
      _ = B := by ring
  linarith only [hCfcube, hDrquot, hfinal]

/-! ### Helper E: the step count from the descent contraction -/

/-- A pure real-number existence lemma, via the descent contraction of the CKN
manuscript's iteration proposition: given a nonnegative crude bound `Θ_bar` at the initial
scale and a sufficiently small forcing budget, there is a step count `N` after which the
geometric bound, together with its residual forcing slack, sits below `η`. -/
theorem exists_N_of_theta_bar {C₂₇ C₂₈ Θbar Lbar : ℝ} (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    (hΘbar : 0 ≤ Θbar) (hLbar : 0 ≤ Lbar)
    (hLsmall : iterationC₂₉ C₂₇ C₂₈ * Lbar ≤ iterationEta C₂₇ / 16) :
    ∃ N : ℕ, (3 / 8 : ℝ) ^ N * Θbar + 8 / 5 * iterationC₂₉ C₂₇ C₂₈ * Lbar ≤ iterationEta C₂₇ := by
  set A : ℝ := iterationC₂₉ C₂₇ C₂₈ * Lbar with hAdef
  set Θabs : ℕ → ℝ → ℝ := fun n _ => (3 / 8 : ℝ) ^ n * Θbar + 8 / 5 * A with hΘabsdef
  have hAnonneg : 0 ≤ A := by
    rw [hAdef]; exact mul_nonneg (iterationC₂₉_pos hC₂₇ hC₂₈).le hLbar
  have hArec : ∀ n : ℕ, ∀ s : ℝ, s ∈ (Set.univ : Set ℝ) →
      Θabs (n + 1) s ≤ (3 / 8 : ℝ) * Θabs n s + iterationC₂₉ C₂₇ C₂₈ * Lbar := by
    intro n s _
    have heq : Θabs (n + 1) s = (3 / 8 : ℝ) * Θabs n s + iterationC₂₉ C₂₇ C₂₈ * Lbar := by
      simp only [hΘabsdef, hAdef, pow_succ]
      ring
    linarith only [heq]
  have hΘ0 : ∀ s ∈ (Set.univ : Set ℝ), Θabs 0 s ≤ Θbar + 8 / 5 * A := by
    intro s _
    have heq : Θabs 0 s = Θbar + 8 / 5 * A := by simp only [hΘabsdef]; ring
    linarith only [heq]
  have hΘnonneg : ∀ n : ℕ, ∀ s ∈ (Set.univ : Set ℝ), 0 ≤ Θabs n s := by
    intro n s _
    have : (0:ℝ) ≤ (3 / 8 : ℝ) ^ n * Θbar + 8 / 5 * A := by positivity
    simpa [hΘabsdef] using this
  obtain ⟨N, hN⟩ := theta_descent_uniform (C₂₇ := C₂₇) (C₂₈ := C₂₈) (Θ := Θabs)
    (S := (Set.univ : Set ℝ)) (Tbar := Θbar + 8 / 5 * A) (Lbar := Lbar)
    hC₂₇ hC₂₈ hΘnonneg hΘ0 hArec hLbar hLsmall
  refine ⟨N, ?_⟩
  have hNs := hN (0 : ℝ) (Set.mem_univ 0)
  have heq : Θabs N (0 : ℝ) = (3 / 8 : ℝ) ^ N * Θbar + 8 / 5 * iterationC₂₉ C₂₇ C₂₈ * Lbar := by
    simp only [hΘabsdef, hAdef]; ring
  linarith only [hNs, heq]

/-! ### The finite descent, extracted as its own declaration for elaboration budget -/

/-- The finite descent from the crude bound `Θ_bar` at scale `r₄` to scale `κ^N r₄`, valid on the
time window forced by `N` itself. Extracted from the main proof so that its induction gets an
independent elaboration budget. -/
theorem finite_descent_bound {C₂₇ C₂₈ : ℝ} (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {q : ℝ}
    {x : Vec3} {r₀ r₄ Θbar Cf σ : ℝ} {N : ℕ}
    (hr₄pos : 0 < r₄) (hCfnonneg : 0 ≤ Cf)
    (hgrad : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0, ENNReal.ofReal (spatialGradientSq u Du w)) ≤
        ENNReal.ofReal (iterationEpsilonStar C₂₇ ^ 2 / 4 * r))
    (hclosure_top : ∀ s' ρ' : ℝ, 0 < ρ' → ρ' ≤ r₄ → s' < 0 → -1 < s' - ρ' ^ 2 →
      closure (parabolicCylinder x s' ρ') ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0))
    (hdecay : ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) →
      theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                  lambda q f z ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ)
    (hLratio : ∀ s' ρ' : ℝ, 0 < ρ' → ρ' ≤ r₄ → s' < 0 → -1 < s' - ρ' ^ 2 →
      lambda q f (x, s') ρ' ≤ Cf * r₄ ^ 3)
    (hΘbarBound : ∀ s : ℝ, s < 0 → -1 < s - r₄ ^ 2 →
      theta (iterationKappa C₂₇) u Du p (x, s) r₄ ≤ Θbar)
    (hσdef : σ = (iterationKappa C₂₇ ^ N * r₄) ^ 2)
    (hlow_of_le_r4 : ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' ≤ r₄ → ∀ s' : ℝ, -σ < s' → -1 < s' - ρ' ^ 2)
    (hρr₀_of_le_r4 : ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' ≤ r₄ → Real.sqrt 2 * ρ' ≤ r₀) :
    ∀ n : ℕ, n ≤ N → ∀ s : ℝ, -σ < s → s < 0 →
      theta (iterationKappa C₂₇) u Du p (x, s) (iterationKappa C₂₇ ^ n * r₄) ≤
        (3 / 8 : ℝ) ^ n * Θbar + 8 / 5 * iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) := by
  have hκpos : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hκle1 : iterationKappa C₂₇ ≤ 1 := by
    have h := iterationKappa_le_half C₂₇
    linarith only [h]
  have hC₂₉pos : 0 < iterationC₂₉ C₂₇ C₂₈ := iterationC₂₉_pos hC₂₇ hC₂₈
  have hr₅pos : 0 < iterationKappa C₂₇ ^ N * r₄ := mul_pos (pow_pos hκpos N) hr₄pos
  intro n
  induction n with
  | zero =>
    intro _ s hsσ hsneg
    have hslow : -1 < s - r₄ ^ 2 := hlow_of_le_r4 r₄ hr₄pos.le (le_refl r₄) s hsσ
    have hb := hΘbarBound s hsneg hslow
    have hnonneg : (0 : ℝ) ≤ 8 / 5 * iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) := by positivity
    have heq0 : iterationKappa C₂₇ ^ (0 : ℕ) * r₄ = r₄ := by ring
    have hpoweq : (3 / 8 : ℝ) ^ (0 : ℕ) * Θbar +
        8 / 5 * iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) =
        Θbar + 8 / 5 * iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) := by norm_num
    rw [heq0, hpoweq]
    linarith only [hb, hnonneg]
  | succ n ih =>
    intro hnp1 s hsσ hsneg
    have hnN : n ≤ N := Nat.le_of_succ_le hnp1
    have hnltN : n < N := hnp1
    have ihs := ih hnN s hsσ hsneg
    set ρn : ℝ := iterationKappa C₂₇ ^ n * r₄ with hρndef
    clear_value ρn
    have hρnpos : 0 < ρn := by rw [hρndef]; positivity
    have hρnler4 : ρn ≤ r₄ := by
      rw [hρndef]
      have h1 : iterationKappa C₂₇ ^ n ≤ 1 := pow_le_one₀ hκpos.le hκle1
      calc iterationKappa C₂₇ ^ n * r₄ ≤ 1 * r₄ := mul_le_mul_of_nonneg_right h1 hr₄pos.le
        _ = r₄ := by ring
    have hρnger5 : iterationKappa C₂₇ ^ N * r₄ ≤ ρn := by
      rw [hρndef]
      have h1 : iterationKappa C₂₇ ^ N ≤ iterationKappa C₂₇ ^ n :=
        pow_le_pow_of_le_one hκpos.le hκle1 hnltN.le
      exact mul_le_mul_of_nonneg_right h1 hr₄pos.le
    have hρnsqger5sq : σ ≤ ρn ^ 2 := by
      rw [hσdef]; exact pow_le_pow_left₀ hr₅pos.le hρnger5 2
    have hentrance_s : -(ρn ^ 2) ≤ s := by linarith only [hsσ, hρnsqger5sq]
    have hslow' : -1 < s - ρn ^ 2 := hlow_of_le_r4 ρn hρnpos.le hρnler4 s hsσ
    have hβsmall : beta u Du (x, s) ρn ≤ iterationEpsilonStar C₂₇ :=
      beta_le_epsilonStar_of_top_gradient_small hC₂₇ hρnpos
        (hρr₀_of_le_r4 ρn hρnpos.le hρnler4) hsneg hentrance_s hgrad
    have hclosure' := hclosure_top s ρn hρnpos hρnler4 hsneg hslow'
    have hdec' := hdecay (z := (x, s)) (ρ := ρn) hρnpos hclosure'
    have hLle' := hLratio s ρn hρnpos hρnler4 hsneg hslow'
    have hthetaT_nonneg : 0 ≤ theta (iterationKappa C₂₇) u Du p (x, s) ρn := by
      have ha := alpha_nonneg u (x, s) hρnpos.le
      have hb := beta_nonneg u Du (x, s) hρnpos.le
      have hκ4 : (0 : ℝ) ≤ iterationKappa C₂₇ ^ (-4 : ℝ) := Real.rpow_nonneg hκpos.le _
      have hd2 : (0 : ℝ) ≤ delta p (x, s) ρn ^ 2 := sq_nonneg _
      have hterm3 : (0 : ℝ) ≤ iterationKappa C₂₇ ^ (-4 : ℝ) * delta p (x, s) ρn ^ 2 :=
        mul_nonneg hκ4 hd2
      unfold theta
      linarith only [ha, hb, hterm3]
    have hLnonneg : 0 ≤ lambda q f (x, s) ρn := lambda_nonneg q f (x, s) hρnpos.le
    have hbnonneg : 0 ≤ beta u Du (x, s) ρn := beta_nonneg u Du (x, s) hρnpos.le
    have hstep := theta_contraction_of_beta_small hC₂₇ hC₂₈ hthetaT_nonneg hLnonneg hbnonneg
      hβsmall hdec'
    have hρn1eq : iterationKappa C₂₇ * ρn = iterationKappa C₂₇ ^ (n + 1) * r₄ := by
      rw [hρndef]; ring
    rw [hρn1eq] at hstep
    have hLmono : iterationC₂₉ C₂₇ C₂₈ * lambda q f (x, s) ρn ≤
        iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) :=
      mul_le_mul_of_nonneg_left hLle' hC₂₉pos.le
    have hihsmul := mul_le_mul_of_nonneg_left ihs (by norm_num : (0 : ℝ) ≤ 3 / 8)
    have heqfinal : 3 / 8 * ((3 / 8 : ℝ) ^ n * Θbar +
          8 / 5 * iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3)) +
        iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) =
        (3 / 8 : ℝ) ^ (n + 1) * Θbar + 8 / 5 * iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) := by
      rw [pow_succ]; ring
    linarith only [hstep, hLmono, hihsmul, heqfinal.le, heqfinal.ge]

/-! ### The crude uniform bound at the fixed scale `r₄`, extracted for elaboration budget -/

/-- The uniform crude bound `Θ_bar` on `θ` at the fixed scale `r₄`, valid for every qualifying
time `s`, built from the three uniform crude bounds of `CIV.Regularity.UniformCrudeBounds`. -/
theorem exists_theta_bar_bound {C₂₇ : ℝ} (hC₂₇ : 0 < C₂₇)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (henergy : GlobalEnergyClass u Du p) {x : Vec3} {r₄ : ℝ} (hr₄pos : 0 < r₄)
    (hballr4 : vec3Ball x r₄ ⊆ vec3Ball 0 1) :
    ∃ Θbar : ℝ, 0 ≤ Θbar ∧ ∀ s : ℝ, s < 0 → -1 < s - r₄ ^ 2 →
      theta (iterationKappa C₂₇) u Du p (x, s) r₄ ≤ Θbar := by
  have hfinβ : (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w)) ≠ ⊤ :=
    lintegral_spatialGradientSq_ne_top_of_globalEnergyClass henergy
  have hfinδ : (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤ :=
    (lintegral_pressure_lt_top u Du p henergy).ne
  have hΘbarBound : ∀ s : ℝ, s < 0 → -1 < s - r₄ ^ 2 →
      theta (iterationKappa C₂₇) u Du p (x, s) r₄ ≤
        (r₄⁻¹ * (3 * essSup (fun τ => ∫⁻ y in vec3Ball 0 1, ‖u (y, τ)‖ₑ ^ (2 : ℝ))
            (volume.restrict (Ioo (-1) 0))).toReal) ^ (1 / 2 : ℝ) +
        (r₄⁻¹ * (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w)).toReal) ^
            (1 / 2 : ℝ) +
        iterationKappa C₂₇ ^ (-4 : ℝ) *
          ((r₄ ^ (-2 : ℝ) *
              (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^
            (1 / 3 : ℝ)) ^ 2 := by
    intro s hsneg hslow
    have hA := alpha_le_of_globalEnergyClass henergy hr₄pos hsneg hslow hballr4
    have hB := beta_le_of_globalEnergyClass hr₄pos hsneg hslow hballr4 hfinβ
    have hD := delta_le_of_globalEnergyClass hr₄pos hsneg hslow hballr4 hfinδ
    have hDsq : delta p (x, s) r₄ ^ 2 ≤
        ((r₄ ^ (-2 : ℝ) * (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^
          (1 / 3 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (delta_nonneg p (x, s) hr₄pos.le) hD 2
    have hκ4nonneg : (0 : ℝ) ≤ iterationKappa C₂₇ ^ (-4 : ℝ) :=
      Real.rpow_nonneg (iterationKappa_pos hC₂₇).le _
    have hDcomb : iterationKappa C₂₇ ^ (-4 : ℝ) * delta p (x, s) r₄ ^ 2 ≤
        iterationKappa C₂₇ ^ (-4 : ℝ) *
          ((r₄ ^ (-2 : ℝ) * (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^
            (1 / 3 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hDsq hκ4nonneg
    have hthetaeq : theta (iterationKappa C₂₇) u Du p (x, s) r₄ =
        alpha u (x, s) r₄ + beta u Du (x, s) r₄ +
          iterationKappa C₂₇ ^ (-4 : ℝ) * delta p (x, s) r₄ ^ 2 := rfl
    rw [hthetaeq]
    linarith only [hA, hB, hDcomb]
  refine ⟨_, ?_, hΘbarBound⟩
  have h1 : (0 : ℝ) ≤ (r₄⁻¹ * (3 * essSup (fun τ => ∫⁻ y in vec3Ball 0 1, ‖u (y, τ)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0))).toReal) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h2 : (0 : ℝ) ≤ (r₄⁻¹ *
      (∫⁻ w in unitCylinder, ENNReal.ofReal (spatialGradientSq u Du w)).toReal) ^
      (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h3 : (0 : ℝ) ≤ iterationKappa C₂₇ ^ (-4 : ℝ) *
      ((r₄ ^ (-2 : ℝ) * (∫⁻ w in unitCylinder, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) ^
        (1 / 3 : ℝ)) ^ 2 := by
    have hκ4 : (0 : ℝ) ≤ iterationKappa C₂₇ ^ (-4 : ℝ) :=
      Real.rpow_nonneg (iterationKappa_pos hC₂₇).le _
    positivity
  linarith only [h1, h2, h3]

/-! ### The Morrey decay below `r₅`, extracted for elaboration budget -/

/-- Once the descent has produced `r₅` with `θ(x,s;r₅) ≤ η` for every qualifying `s`, the
iteration proposition of the CKN manuscript (needing no further gradient smallness) gives the
Morrey decay for every scale `r ≤ r₅`. -/
theorem morrey_decay_below_r5 {C₂₇ C₂₈ : ℝ} (hC₂₇ : 0 < C₂₇) (hC₂₈ : 0 < C₂₈)
    {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    {x : Vec3} {r₄ r₅ σ Θbar Cf : ℝ} {N : ℕ}
    (hr₅def : r₅ = iterationKappa C₂₇ ^ N * r₄) (hr₅pos : 0 < r₅)
    (hr₅ler₄ : r₅ ≤ r₄)
    (hN : (3 / 8 : ℝ) ^ N * Θbar + 8 / 5 * iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) ≤
      iterationEta C₂₇)
    (hFinite : ∀ n : ℕ, n ≤ N → ∀ s : ℝ, -σ < s → s < 0 →
      theta (iterationKappa C₂₇) u Du p (x, s) (iterationKappa C₂₇ ^ n * r₄) ≤
        (3 / 8 : ℝ) ^ n * Θbar + 8 / 5 * iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3))
    (hlow_of_le_r4 : ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' ≤ r₄ → ∀ s' : ℝ, -σ < s' → -1 < s' - ρ' ^ 2)
    (hclosure_top : ∀ s' ρ' : ℝ, 0 < ρ' → ρ' ≤ r₄ → s' < 0 → -1 < s' - ρ' ^ 2 →
      closure (parabolicCylinder x s' ρ') ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0))
    (hLratio : ∀ s' ρ' : ℝ, 0 < ρ' → ρ' ≤ r₄ → s' < 0 → -1 < s' - ρ' ^ 2 →
      lambda q f (x, s') ρ' ≤ Cf * r₄ ^ 3)
    (hr₄Λ₀ : Cf * r₄ ^ 3 ≤ iterationLambda₀ C₂₇ C₂₈)
    (hdecayFull : ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) →
      theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                  lambda q f z ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ ∧
        (theta (iterationKappa C₂₇) u Du p z ρ ≤ 1 →
          theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
            C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
              2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    theta (iterationKappa C₂₇) u Du p z ρ +
              C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    lambda q f z ρ ^ (1 / 2 : ℝ) +
              C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ)) :
    ∃ M₁ : ℝ, 1 ≤ M₁ ∧
      ∀ s ∈ Ioo (-σ) (0 : ℝ), ∀ r : ℝ, 0 < r → r ≤ r₅ →
        max (max (alpha u (x, s) r) (beta u Du (x, s) r)) (delta p (x, s) r ^ 2) ≤
          M₁ * r ^ (2 / 5 : ℝ) := by
  have hκpos : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hκle1 : iterationKappa C₂₇ ≤ 1 := by
    have h := iterationKappa_le_half C₂₇
    linarith only [h]
  set M₁ : ℝ := max 1 (iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) * iterationEta C₂₇ *
      r₅ ^ (-iterationEpsilon)) with hM₁def
  clear_value M₁
  have hM₁ge1 : (1 : ℝ) ≤ M₁ := by rw [hM₁def]; exact le_max_left _ _
  refine ⟨M₁, hM₁ge1, ?_⟩
  intro s hs r hr hrler5
  obtain ⟨hsσ, hsneg⟩ := hs
  have hθr5 : theta (iterationKappa C₂₇) u Du p (x, s) r₅ ≤ iterationEta C₂₇ := by
    have hF := hFinite N (le_refl N) s hsσ hsneg
    have heqr5 : iterationKappa C₂₇ ^ N * r₄ = r₅ := hr₅def.symm
    rw [heqr5] at hF
    linarith only [hF, hN]
  have hslow5 : -1 < s - r₅ ^ 2 := hlow_of_le_r4 r₅ hr₅pos.le hr₅ler₄ s hsσ
  have hclosure5 := hclosure_top s r₅ hr₅pos hr₅ler₄ hsneg hslow5
  have hLamr5 : lambda q f (x, s) r₅ ≤ iterationLambda₀ C₂₇ C₂₈ := by
    have h1 := hLratio s r₅ hr₅pos hr₅ler₄ hsneg hslow5
    linarith only [h1, hr₄Λ₀]
  have hiter := @iteration_of_thetaDecay (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f
    (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol)
    (x, s) r₅ C₂₇ C₂₈ hC₂₇ hC₂₈ hr₅pos hclosure5 hθr5 hLamr5
    (fun {z} {ρ} hρz hzc => hdecayFull hρz hzc)
  have hthetabound := hiter.2 r hr hrler5
  have hmorrey := MorreyDecayAux.max_components_le_theta (u := u) (Du := Du) (p := p)
    (z := (x, s)) (r := r) hκpos hκle1 (alpha_nonneg u (x, s) hr.le) (beta_nonneg u Du (x, s) hr.le)
  have hM₁ge : iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) * iterationEta C₂₇ *
      r₅ ^ (-iterationEpsilon) ≤ M₁ := by rw [hM₁def]; exact le_max_right _ _
  have hrεnonneg : (0 : ℝ) ≤ r ^ iterationEpsilon := Real.rpow_nonneg hr.le _
  have hfinalbound : theta (iterationKappa C₂₇) u Du p (x, s) r ≤ M₁ * r ^ iterationEpsilon := by
    calc theta (iterationKappa C₂₇) u Du p (x, s) r
        ≤ iterationKappa C₂₇ ^ (-4 / 3 - iterationEpsilon) * iterationEta C₂₇ *
            r₅ ^ (-iterationEpsilon) * r ^ iterationEpsilon := hthetabound
      _ ≤ M₁ * r ^ iterationEpsilon := mul_le_mul_of_nonneg_right hM₁ge hrεnonneg
  have hεeq : iterationEpsilon = (2 / 5 : ℝ) := iterationEpsilon_eq
  rw [hεeq] at hfinalbound
  calc max (max (alpha u (x, s) r) (beta u Du (x, s) r)) (delta p (x, s) r ^ 2)
      ≤ theta (iterationKappa C₂₇) u Du p (x, s) r := hmorrey
    _ ≤ M₁ * r ^ (2 / 5 : ℝ) := hfinalbound

/-! ### Main theorem -/

theorem uniform_morrey_decay_of_top_gradient_small (q : ℝ) (hq : 5 / 2 < q) :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧
      ∀ (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f →
        GlobalEnergyClass u Du p → ForceC2Bounded f →
        ∀ (x : Vec3) (r₀ : ℝ), 0 < r₀ → r₀ ≤ 1 → vec3Ball x r₀ ⊆ vec3Ball 0 1 →
        (∀ r : ℝ, 0 < r → r ≤ r₀ →
          (∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (spatialGradientSq u Du w)) ≤
            ENNReal.ofReal (iterationEpsilonStar C₂₇ ^ (2 : ℕ) / 4 * r)) →
        ∃ r₅ M₁ σ : ℝ, 0 < r₅ ∧ 1 ≤ M₁ ∧ 0 < σ ∧
          ∀ s ∈ Ioo (-σ) (0 : ℝ), ∀ r : ℝ, 0 < r → r ≤ r₅ →
            max (max (alpha u (x, s) r) (beta u Du (x, s) r)) (delta p (x, s) r ^ 2) ≤
              M₁ * r ^ (2 / 5 : ℝ) := by
  obtain ⟨C₂₇, hC₂₇, hCdecayAll⟩ := CKN.thetaDecay_T_of_sws_absolute
  obtain ⟨C₂₈, hC₂₈, hdecay0⟩ := hCdecayAll q
  refine ⟨C₂₇, hC₂₇, ?_⟩
  intro u Du p f hsol henergy hforce x r₀ hr₀pos hr₀le1 hballr0 hgrad
  have hdecay : ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ unitCylinder →
      theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                  lambda q f z ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ := by
    intro z ρ hρ hz
    exact (hdecay0 (vec3Ball 0 1) (Ioo (-1) 0) u Du p f
      (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) hρ hz).1
  have hdecayFull : ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) →
      theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
          C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) * theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
              (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
            C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                  lambda q f z ρ ^ (1 / 2 : ℝ) +
            C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ ∧
        (theta (iterationKappa C₂₇) u Du p z ρ ≤ 1 →
          theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
            C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
              2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    theta (iterationKappa C₂₇) u Du p z ρ +
              C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    lambda q f z ρ ^ (1 / 2 : ℝ) +
              C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ) := by
    intro z ρ hρ hz
    exact hdecay0 (vec3Ball 0 1) (Ioo (-1) 0) u Du p f
      (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) hρ hz
  clear hdecay0
  obtain ⟨Cf, hCfnonneg, hCf⟩ := lambda_le_of_forceC2Bounded q hq hforce
  have hΛ₀pos : 0 < iterationLambda₀ C₂₇ C₂₈ := iterationLambda₀_pos hC₂₇ hC₂₈
  have hC₂₉pos : 0 < iterationC₂₉ C₂₇ C₂₈ := iterationC₂₉_pos hC₂₇ hC₂₈
  have hηpos : 0 < iterationEta C₂₇ := iterationEta_pos hC₂₇
  have hBpos : 0 < min (iterationLambda₀ C₂₇ C₂₈)
      (iterationEta C₂₇ / (16 * iterationC₂₉ C₂₇ C₂₈)) :=
    lt_min hΛ₀pos (by positivity)
  obtain ⟨r₄, hr₄pos, hr₄halfr₀, hr₄cube⟩ :=
    exists_r4_le_of_cube_bound hCfnonneg hr₀pos hBpos
  have hr₄Λ₀ : Cf * r₄ ^ 3 ≤ iterationLambda₀ C₂₇ C₂₈ := hr₄cube.trans (min_le_left _ _)
  have hr₄η16 : Cf * r₄ ^ 3 ≤ iterationEta C₂₇ / (16 * iterationC₂₉ C₂₇ C₂₈) :=
    hr₄cube.trans (min_le_right _ _)
  have hLsmall0 : iterationC₂₉ C₂₇ C₂₈ * (Cf * r₄ ^ 3) ≤ iterationEta C₂₇ / 16 := by
    have h := mul_le_mul_of_nonneg_left hr₄η16 hC₂₉pos.le
    have heq : iterationC₂₉ C₂₇ C₂₈ * (iterationEta C₂₇ / (16 * iterationC₂₉ C₂₇ C₂₈)) =
        iterationEta C₂₇ / 16 := by field_simp
    rwa [heq] at h
  have hr₄ler₀ : r₄ ≤ r₀ := hr₄halfr₀.trans (by linarith only [hr₀pos])
  have hr₄ltr₀ : r₄ < r₀ := lt_of_le_of_lt hr₄halfr₀ (by linarith only [hr₀pos])
  have hballr4 : vec3Ball x r₄ ⊆ vec3Ball 0 1 := (vec3Ball_mono hr₄ler₀).trans hballr0
  obtain ⟨Θbar, hΘbarnonneg, hΘbarBound⟩ := exists_theta_bar_bound hC₂₇ henergy hr₄pos hballr4
  have hLbarnonneg : 0 ≤ Cf * r₄ ^ 3 := by positivity
  obtain ⟨N, hN⟩ := exists_N_of_theta_bar hC₂₇ hC₂₈ hΘbarnonneg hLbarnonneg hLsmall0
  set r₅ : ℝ := iterationKappa C₂₇ ^ N * r₄ with hr₅def
  clear_value r₅
  set σ : ℝ := r₅ ^ 2 with hσdef
  clear_value σ
  have hκpos : 0 < iterationKappa C₂₇ := iterationKappa_pos hC₂₇
  have hκle1 : iterationKappa C₂₇ ≤ 1 := by
    have h := iterationKappa_le_half C₂₇
    linarith only [h]
  have hr₅pos : 0 < r₅ := by rw [hr₅def]; positivity
  have hr₅ler₄ : r₅ ≤ r₄ := by
    rw [hr₅def]
    have h1 : iterationKappa C₂₇ ^ N ≤ 1 := pow_le_one₀ hκpos.le hκle1
    calc iterationKappa C₂₇ ^ N * r₄ ≤ 1 * r₄ := mul_le_mul_of_nonneg_right h1 hr₄pos.le
      _ = r₄ := by ring
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  have hclosure_top : ∀ (s' ρ' : ℝ), 0 < ρ' → ρ' ≤ r₄ → s' < 0 → -1 < s' - ρ' ^ 2 →
      closure (parabolicCylinder x s' ρ') ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) := by
    intro s' ρ' hρ'pos hρ'ler4 hs'neg hs'low
    refine CIV.closure_parabolicCylinder_subset_unitCylinder x s' ρ' hρ'pos hs'neg hs'low ?_
    intro y hy
    have hylt : vec3EuclideanNorm (y - x) < r₀ := lt_of_le_of_lt (hy.trans hρ'ler4) hr₄ltr₀
    have hymem : y ∈ vec3Ball x r₀ := hylt
    exact hballr0 hymem
  have hLratio : ∀ (s' ρ' : ℝ), 0 < ρ' → ρ' ≤ r₄ → s' < 0 → -1 < s' - ρ' ^ 2 →
      lambda q f (x, s') ρ' ≤ Cf * r₄ ^ 3 := by
    intro s' ρ' hρ'pos hρ'ler4 hs'neg hs'low
    have hballρ' : vec3Ball x ρ' ⊆ vec3Ball 0 1 :=
      (vec3Ball_mono (hρ'ler4.trans hr₄ler₀)).trans hballr0
    have h1 := hCf x s' ρ' hρ'pos hs'neg hs'low hballρ'
    have h2 : Cf * ρ' ^ 3 ≤ Cf * r₄ ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ'pos.le hρ'ler4 3) hCfnonneg
    linarith only [h1, h2]
  have hr₄lehalf : r₄ ≤ 1 / 2 := hr₄halfr₀.trans (by linarith only [hr₀le1])
  have hr₄sqlequarter : r₄ ^ 2 ≤ 1 / 4 := by nlinarith only [hr₄lehalf, hr₄pos.le]
  have hσler4sq : σ ≤ r₄ ^ 2 := by
    rw [hσdef]; exact pow_le_pow_left₀ hr₅pos.le hr₅ler₄ 2
  have hlow_of_le_r4 : ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' ≤ r₄ → ∀ s' : ℝ, -σ < s' → -1 < s' - ρ' ^ 2 := by
    intro ρ' hρ'0 hρ'ler4 s' hs'σ
    have hρ'sq : ρ' ^ 2 ≤ r₄ ^ 2 := pow_le_pow_left₀ hρ'0 hρ'ler4 2
    linarith only [hs'σ, hσler4sq, hρ'sq, hr₄sqlequarter]
  have hρr₀_of_le_r4 : ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' ≤ r₄ → Real.sqrt 2 * ρ' ≤ r₀ := by
    intro ρ' hρ'0 hρ'ler4
    have hsqrt2nonneg : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h1 : Real.sqrt 2 * ρ' ≤ Real.sqrt 2 * r₄ := mul_le_mul_of_nonneg_left hρ'ler4 hsqrt2nonneg
    have h2 : Real.sqrt 2 * r₄ ≤ 2 * (r₀ / 2) :=
      mul_le_mul sqrt_two_le_two hr₄halfr₀ hr₄pos.le (by norm_num)
    have h3 : (2 : ℝ) * (r₀ / 2) = r₀ := by ring
    linarith only [h1, h2, h3.le, h3.ge]
  have hσdef' : σ = (iterationKappa C₂₇ ^ N * r₄) ^ 2 := by rw [hσdef, hr₅def]
  have hFinite := finite_descent_bound hC₂₇ hC₂₈ hr₄pos hCfnonneg hgrad hclosure_top hdecay
    hLratio hΘbarBound hσdef' hlow_of_le_r4 hρr₀_of_le_r4
  obtain ⟨M₁, hM₁ge1, hM₁conc⟩ := morrey_decay_below_r5 hC₂₇ hC₂₈ hsol hr₅def hr₅pos
    hr₅ler₄ hN hFinite hlow_of_le_r4 hclosure_top hLratio hr₄Λ₀ hdecayFull
  exact ⟨r₅, M₁, σ, hr₅pos, hM₁ge1, hσpos, hM₁conc⟩

end CIV
