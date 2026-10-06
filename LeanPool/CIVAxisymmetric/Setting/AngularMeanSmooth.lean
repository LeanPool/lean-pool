/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Continuity and smoothness of the angular mean

The angular mean `𝒫u = (2π)⁻¹ ∫₀^{2π} ℛ_φ u dφ` of `eq:interior:average` is as regular
as `u` on the unit cylinder: if `u` is continuous (respectively `C^n`) on `Q` then so is
`𝒫u`. This is differentiation under the integral sign for a parametric integral over the
compact angle interval `[0, 2π]`, whose integrand `(φ, z) ↦ Q_φ u(Q_φ⁻¹ x, t)` is jointly
`C^n` on `ℝ × Q` because the rotations preserve `Q`. For a `C¹` field the spatial partial
derivatives of the angular mean are the angular means of the spatial partial derivatives of the
rotated fields (`spatialPartial_angularMean`).

The first section proves the general statement: an integral over `Ioc a b` of an integrand
that is jointly `C^n` on `ℝ × s`, `s` open in a proper normed space, is `C^n` on `s`. The
derivative under the integral sign is `hasFDerivAt_integral_of_dominated_of_fderiv_le` with
the constant domination obtained from the compactness of `[a, b] × closedBall x₀ ε`; the
induction on the order of differentiability follows `contDiffOn_succ_iff_fderiv_of_isOpen`.
-/

public section

open MeasureTheory Set Metric Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### Parametric integrals over a compact interval -/

section ParametricIntegral

variable {H : Type} [NormedAddCommGroup H] {s : Set H} {x₀ : H}

/-- A function continuous on `ℝ × s`, `s` open, is bounded on `[a, b] × closedBall x₀ ε` for
some closed ball inside `s`. -/
theorem exists_closedBall_subset_bound_of_continuousOn [ProperSpace H] {E : Type}
    [NormedAddCommGroup E] (hs : IsOpen s) (hx₀ : x₀ ∈ s) {G : ℝ × H → E}
    (hG : ContinuousOn G (univ ×ˢ s)) (a b : ℝ) :
    ∃ ε > 0, closedBall x₀ ε ⊆ s ∧
      ∃ M : ℝ, ∀ t ∈ Icc a b, ∀ x ∈ closedBall x₀ ε, ‖G (t, x)‖ ≤ M := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hs.mem_nhds hx₀)
  have hsub : closedBall x₀ (ε / 2) ⊆ s :=
    (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hK : IsCompact (Icc a b ×ˢ closedBall x₀ (ε / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hG.mono (prod_mono (subset_univ _) hsub))
  exact ⟨ε / 2, half_pos hε, hsub, M, fun t ht x hx => hM (t, x) ⟨ht, hx⟩⟩

/-- The sections `t ↦ G (t, x)`, `x ∈ s`, of a function continuous on `ℝ × s`. -/
theorem continuous_section_of_continuousOn {E : Type} [TopologicalSpace E]
    {G : ℝ × H → E} (hG : ContinuousOn G (univ ×ˢ s)) {x : H} (hx : x ∈ s) :
    Continuous fun t : ℝ => G (t, x) := by
  rw [← continuousOn_univ]
  exact hG.comp (continuous_id.prodMk continuous_const).continuousOn
    fun t _ => ⟨mem_univ _, hx⟩

/-- Continuity of a parametric integral over `Ioc a b` with an integrand jointly continuous on
`ℝ × s`. -/
theorem continuousAt_parametric_integral_Ioc [ProperSpace H] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hs : IsOpen s) (hx₀ : x₀ ∈ s) {G : ℝ × H → E}
    (hG : ContinuousOn G (univ ×ˢ s)) (a b : ℝ) :
    ContinuousAt (fun x => ∫ t in Ioc a b, G (t, x)) x₀ := by
  obtain ⟨ε, hε, hsub, M, hM⟩ := exists_closedBall_subset_bound_of_continuousOn hs hx₀ hG a b
  refine continuousAt_of_dominated (μ := volume.restrict (Ioc a b)) (bound := fun _ => M)
    ?_ ?_ ?_ ?_
  · filter_upwards [hs.mem_nhds hx₀] with x hx
    exact (continuous_section_of_continuousOn hG hx).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds x₀ hε] with x hx
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      hM t (Ioc_subset_Icc_self ht) x hx
  · exact integrable_const M
  · refine ae_of_all _ fun t => ?_
    exact (hG.continuousAt ((isOpen_univ.prod hs).mem_nhds ⟨mem_univ _, hx₀⟩)).comp
      (continuous_const.prodMk continuous_id).continuousAt

/-- The partial derivative in the parameter of a function `C¹` on `ℝ × s`, `s` open, is the
composition of its derivative with the inclusion of the parameter factor. -/
theorem fderiv_section_of_contDiffOn [NormedSpace ℝ H] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hs : IsOpen s) {G : ℝ × H → E} (hG : ContDiffOn ℝ 1 G (univ ×ˢ s))
    (t : ℝ) {x : H} (hx : x ∈ s) :
    fderiv ℝ (fun x => G (t, x)) x = (fderiv ℝ G (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ H) :=
  (((hG.differentiableOn one_ne_zero).differentiableAt
    ((isOpen_univ.prod hs).mem_nhds ⟨mem_univ _, hx⟩)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right t x)).fderiv

/-- The partial derivative in the parameter of a function `C¹` on `ℝ × s`, `s` open, is jointly
continuous there. -/
theorem continuousOn_fderiv_section_of_contDiffOn [NormedSpace ℝ H] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hs : IsOpen s) {G : ℝ × H → E}
    (hG : ContDiffOn ℝ 1 G (univ ×ˢ s)) :
    ContinuousOn (fun p : ℝ × H => fderiv ℝ (fun x => G (p.1, x)) p.2) (univ ×ˢ s) := by
  refine ContinuousOn.congr ((hG.continuousOn_fderiv_of_isOpen (isOpen_univ.prod hs)
    le_rfl).clm_comp (f := fun _ => ContinuousLinearMap.inr ℝ ℝ H) continuousOn_const) ?_
  rintro ⟨t, x⟩ ⟨-, hx⟩
  exact fderiv_section_of_contDiffOn hs hG t hx

/-- Differentiation under the integral sign for a parametric integral over `Ioc a b` with an
integrand that is `C¹` on `ℝ × s`: the derivative is the integral of the partial derivative
in the parameter. -/
theorem hasFDerivAt_parametric_integral_Ioc [NormedSpace ℝ H] [ProperSpace H] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hs : IsOpen s) (hx₀ : x₀ ∈ s) {G : ℝ × H → E}
    (hG : ContDiffOn ℝ 1 G (univ ×ˢ s)) (a b : ℝ) :
    HasFDerivAt (fun x => ∫ t in Ioc a b, G (t, x))
      (∫ t in Ioc a b, fderiv ℝ (fun x => G (t, x)) x₀) x₀ := by
  have hopen : IsOpen (univ ×ˢ s : Set (ℝ × H)) := isOpen_univ.prod hs
  have hDcont := continuousOn_fderiv_section_of_contDiffOn hs hG
  have hdiff : ∀ t : ℝ, ∀ x ∈ s, HasFDerivAt (fun x => G (t, x))
      (fderiv ℝ (fun x => G (t, x)) x) x := fun t x hx =>
    (((hG.differentiableOn one_ne_zero).differentiableAt
      (hopen.mem_nhds ⟨mem_univ _, hx⟩)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_right t x)).differentiableAt.hasFDerivAt
  obtain ⟨ε, hε, hsub, M, hM⟩ :=
    exists_closedBall_subset_bound_of_continuousOn hs hx₀ hDcont a b
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ioc a b))
    (F' := fun x t => fderiv ℝ (fun x => G (t, x)) x) (bound := fun _ => M)
    (closedBall_mem_nhds x₀ hε) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hs.mem_nhds hx₀] with x hx
    exact (continuous_section_of_continuousOn hG.continuousOn hx).aestronglyMeasurable
  · exact (continuous_section_of_continuousOn hG.continuousOn hx₀).integrableOn_Ioc
  · exact (continuous_section_of_continuousOn hDcont hx₀).aestronglyMeasurable
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht x hx =>
      hM t (Ioc_subset_Icc_self ht) x hx
  · exact integrable_const M
  · exact ae_of_all _ fun t x hx => hdiff t x (hsub hx)

/-- A parametric integral over `Ioc a b` with an integrand jointly `C^n` on `ℝ × s`, `n : ℕ`,
is `C^n` on `s`. -/
theorem contDiffOn_parametric_integral_Ioc_nat [NormedSpace ℝ H] [ProperSpace H] (hs : IsOpen s)
    (a b : ℝ) (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : ℝ × H → E},
      ContDiffOn ℝ n G (univ ×ˢ s) → ContDiffOn ℝ n (fun x => ∫ t in Ioc a b, G (t, x)) s := by
  induction n with
  | zero =>
    intro E _ _ G hG
    rw [Nat.cast_zero, contDiffOn_zero] at hG ⊢
    exact fun x hx => (continuousAt_parametric_integral_Ioc hs hx hG a b).continuousWithinAt
  | succ n ih =>
    intro E _ _ G hG
    have hopen : IsOpen (univ ×ˢ s : Set (ℝ × H)) := isOpen_univ.prod hs
    rw [Nat.cast_add, Nat.cast_one] at hG ⊢
    have hG1 : ContDiffOn ℝ 1 G (univ ×ˢ s) := hG.of_le le_add_self
    have hderiv : ∀ x ∈ s, HasFDerivAt (fun x => ∫ t in Ioc a b, G (t, x))
        (∫ t in Ioc a b, fderiv ℝ (fun x => G (t, x)) x) x :=
      fun x hx => hasFDerivAt_parametric_integral_Ioc hs hx hG1 a b
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hD : ContDiffOn ℝ n
        (fun p : ℝ × H => (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ H)) (univ ×ˢ s) :=
      ContDiffOn.clm_comp (hG.fderiv_of_isOpen hopen le_rfl) contDiffOn_const
    refine (ih hD).congr fun x hx => ?_
    rw [(hderiv x hx).fderiv]
    congr 1
    funext t
    exact fderiv_section_of_contDiffOn hs hG1 t hx

/-- A parametric integral over `Ioc a b` with an integrand jointly `C^n` on `ℝ × s` is `C^n`
on `s`. -/
theorem contDiffOn_parametric_integral_Ioc [NormedSpace ℝ H] [ProperSpace H] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hs : IsOpen s) (a b : ℝ) (n : ℕ∞) {G : ℝ × H → E}
    (hG : ContDiffOn ℝ n G (univ ×ˢ s)) :
    ContDiffOn ℝ n (fun x => ∫ t in Ioc a b, G (t, x)) s := by
  induction n using ENat.recTopCoe with
  | top =>
    rw [contDiffOn_infty] at hG ⊢
    exact fun m => contDiffOn_parametric_integral_Ioc_nat hs a b m (hG m)
  | coe m =>
    rw [WithTop.coe_natCast] at hG ⊢
    exact contDiffOn_parametric_integral_Ioc_nat hs a b m hG

/-- A parametric interval integral `x ↦ ∫ t in a..b, G (t, x)`, `a ≤ b`, with an integrand
jointly `C^n` on `ℝ × s` is `C^n` on `s`. -/
theorem contDiffOn_parametric_intervalIntegral [NormedSpace ℝ H] [ProperSpace H] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hs : IsOpen s) {a b : ℝ} (hab : a ≤ b) (n : ℕ∞)
    {G : ℝ × H → E} (hG : ContDiffOn ℝ n G (univ ×ˢ s)) :
    ContDiffOn ℝ n (fun x => ∫ t in a..b, G (t, x)) s := by
  simp_rw [intervalIntegral.integral_of_le hab]
  exact contDiffOn_parametric_integral_Ioc hs a b n hG

end ParametricIntegral

/-! ### The rotated field is jointly smooth -/

/-- The unit cylinder is open for the product topology of `Vec3 × ℝ`. -/
theorem isOpen_unitCylinder_prod : IsOpen (X := Vec3 × ℝ) unitCylinder :=
  (isOpen_vec3Ball 0 1).prod isOpen_Ioo

/-- Joint smoothness of the rotation in the angle and the point. -/
theorem contDiff_rotZ_uncurry (n : WithTop ℕ∞) :
    ContDiff ℝ n fun p : ℝ × Vec3 => rotZ p.1 p.2 := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, rotZ_apply_zero]
    fun_prop
  · simp only [Fin.mk_one, Fin.isValue, rotZ_apply_one]
    fun_prop
  · simp only [Fin.reduceFinMk, rotZ_apply_two, Fin.isValue]
    fun_prop

/-- The rotated field `(φ, z) ↦ (ℛ_φ u)(z)` is jointly `C^n` on `ℝ × Q` when `u` is `C^n`
on `Q`. -/
theorem contDiffOn_rotField_uncurry (n : WithTop ℕ∞) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ n (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ n (fun p : ℝ × (Vec3 × ℝ) => rotField p.1 u p.2) (univ ×ˢ unitCylinder) := by
  have hinner : ContDiffOn ℝ n (fun p : ℝ × (Vec3 × ℝ) => (rotZ (-p.1) p.2.1, p.2.2))
      (univ ×ˢ unitCylinder) := by
    refine ContDiffOn.prodMk ?_ contDiffOn_snd.snd
    exact ((contDiff_rotZ_uncurry n).comp (contDiff_fst.neg.prodMk contDiff_snd.fst)).contDiffOn
  have hmaps : MapsTo (fun p : ℝ × (Vec3 × ℝ) => (rotZ (-p.1) p.2.1, p.2.2))
      (univ ×ˢ unitCylinder) unitCylinder := fun p hp => rotZ_mem_unitCylinder (-p.1) hp.2
  have hmid := hu.comp hinner hmaps
  have houter := (contDiff_rotZ_uncurry n).comp_contDiffOn (contDiffOn_fst.prodMk hmid)
  exact houter

/-! ### Regularity of the angular mean -/

/-- The angular mean of a `C^n` field on the unit cylinder is `C^n` there. -/
theorem contDiffOn_angularMean (n : ℕ∞) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ n (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ n (fun z : Vec3 × ℝ => angularMean u z) unitCylinder :=
  (contDiffOn_parametric_intervalIntegral isOpen_unitCylinder_prod Real.two_pi_pos.le n
    (contDiffOn_rotField_uncurry n hu)).const_smul (2 * Real.pi)⁻¹

/-- The angular mean of a smooth field on the unit cylinder is smooth there. -/
theorem contDiffOn_angularMean_smooth {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => angularMean u z) unitCylinder :=
  contDiffOn_angularMean ⊤ hu

/-- The angular mean of a continuous field on the unit cylinder is continuous there. -/
theorem continuousOn_angularMean {u : ParabolicPoint → Vec3}
    (hu : ContinuousOn (fun z : Vec3 × ℝ => u z) unitCylinder) :
    ContinuousOn (fun z : Vec3 × ℝ => angularMean u z) unitCylinder :=
  contDiffOn_zero.1 (contDiffOn_angularMean 0 (contDiffOn_zero.2 hu))

/-- For a `C¹` field, a spatial partial derivative of the angular mean is the angular mean of
the corresponding spatial partial derivatives of the rotated fields: the derivative passes under
the angular integral. -/
theorem spatialPartial_angularMean (i j : Fin 3) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) :
    spatialPartial (fun w => angularMean u w i) j z =
      (2 * Real.pi)⁻¹ *
        ∫ φ in (0 : ℝ)..(2 * Real.pi), spatialPartial (fun w => rotField φ u w i) j z := by
  obtain ⟨x₀, t⟩ := z
  have hx₀ : x₀ ∈ vec3Ball 0 1 := hz.1
  have ht : t ∈ Ioo (-1 : ℝ) 0 := hz.2
  have hball : IsOpen (vec3Ball 0 1) := isOpen_vec3Ball 0 1
  have hrot := contDiffOn_rotField_uncurry 1 hu
  set G : ℝ × Vec3 → ℝ := fun q => rotField q.1 u (q.2, t) i with hG_def
  have hGsm : ContDiffOn ℝ 1 G (univ ×ˢ vec3Ball 0 1) := by
    have hemb : ContDiffOn ℝ 1 (fun q : ℝ × Vec3 => (q.1, (q.2, t)))
        (univ ×ˢ vec3Ball 0 1) :=
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)).contDiffOn
    have hmaps : MapsTo (fun q : ℝ × Vec3 => (q.1, (q.2, t))) (univ ×ˢ vec3Ball 0 1)
        (univ ×ˢ unitCylinder) := fun q hq => ⟨mem_univ _, hq.2, ht⟩
    have h2 := hrot.comp hemb hmaps
    have h3 := contDiffOn_pi.1 h2 i
    exact h3
  have hev : (fun x => angularMean u (x, t) i) =ᶠ[𝓝 x₀]
      fun x => (2 * Real.pi)⁻¹ * ∫ φ in Ioc 0 (2 * Real.pi), G (φ, x) := by
    filter_upwards [hball.mem_nhds hx₀] with x hx
    have hint : IntegrableOn (fun φ => rotField φ u (x, t)) (Ioc 0 (2 * Real.pi)) :=
      (continuous_section_of_continuousOn hrot.continuousOn (x := (x, t))
        ⟨hx, ht⟩).integrableOn_Ioc
    change ((2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ u (x, t)) i = _
    rw [Pi.smul_apply, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    congr 1
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).integral_comp_comm
      hint).symm
  have hderiv := (hasFDerivAt_parametric_integral_Ioc hball hx₀ hGsm 0 (2 * Real.pi)).const_mul
    (2 * Real.pi)⁻¹
  have hDint : IntegrableOn (fun φ => fderiv ℝ (fun x => G (φ, x)) x₀) (Ioc 0 (2 * Real.pi)) :=
    (continuous_section_of_continuousOn (continuousOn_fderiv_section_of_contDiffOn hball hGsm)
      hx₀).integrableOn_Ioc
  change fderiv ℝ (fun x => angularMean u (x, t) i) x₀ (basisVec j) = _
  rw [hev.fderiv_eq, hderiv.fderiv, smul_apply, smul_eq_mul,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, ContinuousLinearMap.integral_apply hDint]
  rfl

end CIV
