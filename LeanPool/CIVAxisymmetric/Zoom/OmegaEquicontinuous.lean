/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.EquicontinuityByMollification
public import LeanPool.CIVAxisymmetric.Zoom.DivergenceIdentity
public import LeanPool.CIVAxisymmetric.Zoom.RescaledEquation
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Locally uniform extraction for the rescaled potential vorticity

Step 2 of the finite-`h` zoom-in argument of Section `sec:aniso:zoom`, the compactness
statement `eq:aniso:zoom:finite:compactness`: the rescaled potential vorticities `Ω_n` of
`eq:aniso:zoom:fields` converge, along a subsequence, locally uniformly on
`{R > 0} × ℝ × (-∞, -1]`.

The route is the one recorded for `prop:aniso:small`. Instead of a negative-order Sobolev norm
of `∂_τ Ω_n`, the regularity in time is carried by a *pairing bound*

  `|∫ (Ω_n(·, τ) - Ω_n(·, τ')) ψ| ≤ Cₒ B |τ - τ'|`,

for every test function `ψ` supported in the interior of a closed rectangle `K ⊆ {R > 0}` and
every bound `B` for `ψ` and its first two derivatives. Together with a uniform Lipschitz bound
in space this gives equicontinuity in time through
`CIV.equicontinuous_of_lipschitz_of_pairings`, hence a space–time modulus of continuity on
`K ×ˢ J`; Arzelà–Ascoli and a diagonal extraction over the rectangles
`[1/(j+1), j+1] × [-(j+1), j+1]` and the time intervals `[-(j+1), -1]` then produce one
subsequence converging uniformly on every compact subset of `{R > 0} × ℝ × (-∞, -1]`.

The file contains, in this order:

* the transport term of `eq:aniso:zoom:finite:equation` in divergence form, namely
  `V_n ∂_R Ω_n + W_n ∂_Z Ω_n = ∂_R (V_n Ω_n) + ∂_Z (W_n Ω_n) + (V_n / R) Ω_n`, which comes from
  the divergence identity `∂_R V_n + V_n / R + ∂_Z W_n = 0` of
  `eq:aniso:zoom:finite:identities`, and the whole equation rewritten in that form;
* integration by parts on the plane against a smooth compactly supported test function — the
  step which moves the derivatives of the equation onto `ψ` — together with the elementary
  bound for a pairing against a coefficient bounded on a set of finite measure;
* the space–time modulus of continuity on a rectangle, Arzelà–Ascoli on a compact set of a
  metric space, the extraction on a single rectangle, an abstract diagonal extraction, and
  their combination on `{R > 0} × ℝ × (-∞, -1]`.

The uniform Lipschitz bound in space and the pairing bound itself enter as hypotheses: the
first is supplied by the first-derivative bounds on `Ω_n`, the second by integrating the
equation in `τ` and integrating by parts with the lemmas of the second group above.
-/

public section

open Filter Set Topology
open CKN.Foundation.Parabolic CKN
open scoped BoundedContinuousFunction

noncomputable section

namespace CIV

/-! ### The transport term in divergence form -/

/-- The radial and vertical slices of the rescaled potential vorticity are differentiable off
the axis, where `Ω = ω_θ / r` is the smooth quotient of the azimuthal vorticity by the radius. -/
private theorem differentiableAt_zoomOmega_slice_of_ne_zero (lam h zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hr : p.1.1 ≠ 0) :
    DifferentiableAt ℝ (fun r : ℝ => zoomOmega lam h zc u ((r, p.1.2), p.2)) p.1.1 ∧
      DifferentiableAt ℝ (fun s : ℝ => zoomOmega lam h zc u ((p.1.1, s), p.2)) p.1.2 := by
  have hZ0 : (zoomPoint lam h zc p).1 0 = lam * p.1.1 := by simp [zoomPoint, meridional]
  have hZ0ne : (zoomPoint lam h zc p).1 0 ≠ 0 := by
    rw [hZ0]
    exact mul_ne_zero hlam.ne' hr
  set D : Set (Vec3 × ℝ) := {z : Vec3 × ℝ | z ∈ unitCylinder ∧ z.1 0 ≠ 0} with hD_def
  have hDopen : IsOpen D := by
    have hcont : Continuous (fun z : Vec3 × ℝ => z.1 0) := (continuous_apply 0).comp continuous_fst
    exact isOpen_unitCylinder_prod.inter (isOpen_ne.preimage hcont)
  have hsub : D ⊆ unitCylinder := fun z hz => hz.1
  have hZD : zoomPoint lam h zc p ∈ D := ⟨hp, hZ0ne⟩
  have hrad : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => z.1 0) D :=
    ((contDiff_apply ℝ ℝ (0 : Fin 3)).comp contDiff_fst).contDiffOn
  have hazi : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => azimuthalVorticity u z) D :=
    (contDiffOn_azimuthalVorticity hu).mono hsub
  have hOmegaTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => potentialVorticity u z) D :=
    (hazi.div hrad fun z hz => hz.2).congr fun z hz => potentialVorticity_eq_div u hz.2
  have hOmega1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => potentialVorticity u z) D :=
    hOmegaTop.of_le (by norm_num)
  exact ⟨((hasDerivAt_zoomScalar_r (Phi := potentialVorticity u) lam h zc hDopen hOmega1 p
      hZD).const_mul (lam ^ 3 * lam ^ (2 * h))).differentiableAt,
    ((hasDerivAt_zoomScalar_z (Phi := potentialVorticity u) lam h zc hDopen hOmega1 p
      hZD).const_mul (lam ^ 3 * lam ^ (2 * h))).differentiableAt⟩

/-- The transport term of `eq:aniso:zoom:finite:equation` in divergence form: off the axis
`V_n ∂_R Ω_n + W_n ∂_Z Ω_n = ∂_R (V_n Ω_n) + ∂_Z (W_n Ω_n) + (V_n / R) Ω_n`, the zeroth-order
term being `-Ω_n` times the divergence `∂_R V_n + ∂_Z W_n = -V_n / R` of
`eq:aniso:zoom:finite:identities`. This is the form in which the derivatives are moved onto a
test function in the passage to the limit. -/
theorem zoomOmega_transport_divergenceForm (lam h zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pres : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hr : p.1.1 ≠ 0) :
    zoomV lam h zc u p * dr (zoomOmega lam h zc u) p
        + zoomW lam h zc u p * dz (zoomOmega lam h zc u) p
      = dr (fun q => zoomV lam h zc u q * zoomOmega lam h zc u q) p
        + dz (fun q => zoomW lam h zc u q * zoomOmega lam h zc u q) p
        + zoomV lam h zc u p / p.1.1 * zoomOmega lam h zc u p := by
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder := hsol.1
  have hu1 : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  obtain ⟨hOr, hOz⟩ := differentiableAt_zoomOmega_slice_of_ne_zero lam h zc hlam u hu p hp hr
  have hVr : DifferentiableAt ℝ (fun r : ℝ => zoomV lam h zc u ((r, p.1.2), p.2)) p.1.1 :=
    ((hasDerivAt_zoom_component_r lam h zc hu1 p hp 0).const_mul lam).differentiableAt
  have hWz : DifferentiableAt ℝ (fun s : ℝ => zoomW lam h zc u ((p.1.1, s), p.2)) p.1.2 :=
    ((hasDerivAt_zoom_component_z lam h zc hu1 p hp 2).const_mul
      (lam * lam ^ (2 * h))).differentiableAt
  have hprodR : dr (fun q => zoomV lam h zc u q * zoomOmega lam h zc u q) p
      = dr (zoomV lam h zc u) p * zoomOmega lam h zc u p
        + zoomV lam h zc u p * dr (zoomOmega lam h zc u) p :=
    (hVr.hasDerivAt.mul hOr.hasDerivAt).deriv
  have hprodZ : dz (fun q => zoomW lam h zc u q * zoomOmega lam h zc u q) p
      = dz (zoomW lam h zc u) p * zoomOmega lam h zc u p
        + zoomW lam h zc u p * dz (zoomOmega lam h zc u) p :=
    (hWz.hasDerivAt.mul hOz.hasDerivAt).deriv
  have hdiv := zoom_divergence_identity lam h zc hlam u pres f hsol haxi p hp hr
  rw [hprodR, hprodZ]
  linear_combination (-(zoomOmega lam h zc u p)) * hdiv

/-- The rescaled potential vorticity equation `eq:aniso:zoom:finite:equation` with its transport
term in divergence form, off the axis. Every term on both sides is at most two derivatives of a
quantity bounded on a rectangle of `{R ≥ ε}`, which is what the passage to the limit uses. -/
theorem zoomOmega_pde_divergenceForm (lam h zc : ℝ) (hlam : 0 < lam)
    (u : ParabolicPoint → Vec3) (pres : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u pres f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPoint lam h zc p ∈ unitCylinder) (hr : p.1.1 ≠ 0) :
    dtPast (zoomOmega lam h zc u) p
        + dr (fun q => zoomV lam h zc u q * zoomOmega lam h zc u q) p
        + dz (fun q => zoomW lam h zc u q * zoomOmega lam h zc u q) p
        + zoomV lam h zc u p / p.1.1 * zoomOmega lam h zc u p
      = dr (dr (zoomOmega lam h zc u)) p
        + 3 / p.1.1 * dr (zoomOmega lam h zc u) p
        + (lam ^ (2 * h)) ^ 2 * dz (dz (zoomOmega lam h zc u)) p
        + dz (fun q => zoomS lam h zc u q ^ 2 / q.1.1 ^ 2) p
        + lam ^ 5 * lam ^ (2 * h) * potentialVorticity f (zoomPoint lam h zc p) := by
  have hpde := zoomOmega_pde lam h zc hlam u pres f hsol haxi p hp hr
  have htr := zoomOmega_transport_divergenceForm lam h zc hlam u pres f hsol haxi p hp hr
  linarith only [hpde, htr]

/-! ### Integration by parts against a compactly supported test function -/

/-- The product of a function continuous on an open set with a continuous function whose
support closes inside that set is continuous on the whole plane: near a point of the open set
both factors are continuous, and off the support the product vanishes identically. -/
private theorem continuous_mul_of_tsupport_subset {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {a b : ℝ × ℝ → ℝ} (ha : ContinuousOn a U) (hb : Continuous b) (hbU : tsupport b ⊆ U) :
    Continuous fun y => a y * b y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ tsupport b
  · exact (ha.continuousAt (hU.mem_nhds (hbU hy))).mul hb.continuousAt
  · have hopen : IsOpen (tsupport b)ᶜ := (isClosed_tsupport b).isOpen_compl
    have hev : (fun y => a y * b y) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
    exact ContinuousAt.congr continuousAt_const hev.symm

/-- The derivative of the first slice of a differentiable function is the first directional
derivative. -/
private theorem hasDerivAt_slice_fst {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) (y : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => ψ (t, y.2)) (fderiv ℝ ψ y (1, 0)) y.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, y.2)) ((1 : ℝ), (0 : ℝ)) y.1 :=
    (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := (hψ y).hasFDerivAt) (hf := hline) (hy := rfl)

/-- The derivative of the second slice of a differentiable function is the second directional
derivative. -/
private theorem hasDerivAt_slice_snd {ψ : ℝ × ℝ → ℝ} (hψ : Differentiable ℝ ψ) (y : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => ψ (y.1, s)) (fderiv ℝ ψ y (0, 1)) y.2 := by
  have hline : HasDerivAt (fun s : ℝ => (y.1, s)) ((0 : ℝ), (1 : ℝ)) y.2 :=
    (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
  exact HasFDerivAt.comp_hasDerivAt_of_eq (hl := (hψ y).hasFDerivAt) (hf := hline) (hy := rfl)

/-- Integration by parts in the first variable of the plane: if `Gp` is the partial derivative
of `F` in that variable on an open set `U`, both continuous on `U`, and `ψ` is smooth with
compact support inside `U`, then `∫ (∂₁F) ψ = -∫ F (∂₁ψ)`. This is the step which moves a
derivative off the coefficient and onto the test function. -/
theorem integral_partial_fst_mul_add_eq_zero {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F Gp : ℝ × ℝ → ℝ} (hFcont : ContinuousOn F U) (hGcont : ContinuousOn Gp U)
    (hFderiv : ∀ y ∈ U, HasDerivAt (fun t : ℝ => F (t, y.2)) (Gp y) y.1)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    (∫ y : ℝ × ℝ, Gp y * ψ y)
      + ∫ y : ℝ × ℝ, F y * deriv (fun t : ℝ => ψ (t, y.2)) y.1 = 0 := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hψcont : Continuous ψ := hψ.continuous
  have hslice : ∀ y : ℝ × ℝ,
      HasDerivAt (fun t : ℝ => ψ (t, y.2)) (fderiv ℝ ψ y (1, 0)) y.1 :=
    fun y => hasDerivAt_slice_fst hψd y
  have hψ1cont : Continuous fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ1zero : ∀ y : ℝ × ℝ, y ∉ tsupport ψ → fderiv ℝ ψ y (1, 0) = 0 := by
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ hy]
    rfl
  have hψ1supp : tsupport (fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0)) ⊆ tsupport ψ := by
    refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
    by_contra hc
    exact hy (hψ1zero y hc)
  have hψ1c : HasCompactSupport fun y : ℝ × ℝ => fderiv ℝ ψ y (1, 0) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) hψ1supp
  -- the two pairings and their sum
  have hint1 : MeasureTheory.Integrable fun y : ℝ × ℝ => Gp y * ψ y :=
    (continuous_mul_of_tsupport_subset hU hGcont hψcont hψU).integrable_of_hasCompactSupport
      hψc.mul_left
  have hint2 : MeasureTheory.Integrable fun y : ℝ × ℝ => F y * fderiv ℝ ψ y (1, 0) :=
    (continuous_mul_of_tsupport_subset hU hFcont hψ1cont
      (hψ1supp.trans hψU)).integrable_of_hasCompactSupport hψ1c.mul_left
  have hAcont : Continuous fun y : ℝ × ℝ => Gp y * ψ y + F y * fderiv ℝ ψ y (1, 0) :=
    (continuous_mul_of_tsupport_subset hU hGcont hψcont hψU).add
      (continuous_mul_of_tsupport_subset hU hFcont hψ1cont (hψ1supp.trans hψU))
  have hAzero : ∀ y : ℝ × ℝ, y ∉ tsupport ψ →
      Gp y * ψ y + F y * fderiv ℝ ψ y (1, 0) = 0 := by
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, hψ1zero y hy, mul_zero, mul_zero, add_zero]
  have hAsupp : HasCompactSupport fun y : ℝ × ℝ => Gp y * ψ y + F y * fderiv ℝ ψ y (1, 0) := by
    refine hψc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun y hy => ?_)
      (isClosed_tsupport ψ))
    by_contra hc
    exact hy (hAzero y hc)
  have hAint : MeasureTheory.Integrable fun y : ℝ × ℝ => Gp y * ψ y + F y * fderiv ℝ ψ y (1, 0) :=
    hAcont.integrable_of_hasCompactSupport hAsupp
  -- the slice product rule
  have hprod : ∀ y : ℝ × ℝ, HasDerivAt (fun t : ℝ => F (t, y.2) * ψ (t, y.2))
      (Gp y * ψ y + F y * fderiv ℝ ψ y (1, 0)) y.1 := by
    intro y
    by_cases hy : y ∈ tsupport ψ
    · exact (hFderiv y (hψU hy)).mul (hslice y)
    · have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
      have hset : IsOpen {t : ℝ | (t, y.2) ∈ (tsupport ψ)ᶜ} :=
        hopen.preimage (continuous_id.prodMk continuous_const)
      have hmem : y.1 ∈ {t : ℝ | (t, y.2) ∈ (tsupport ψ)ᶜ} := hy
      have hev : (fun t : ℝ => F (t, y.2) * ψ (t, y.2)) =ᶠ[𝓝 y.1] fun _ => (0 : ℝ) := by
        filter_upwards [hset.mem_nhds hmem] with t ht
        rw [image_eq_zero_of_notMem_tsupport ht, mul_zero]
      rw [hAzero y hy]
      exact (hasDerivAt_const y.1 (0 : ℝ)).congr_of_eventuallyEq hev
  -- the support of `ψ` lies in a vertical strip
  obtain ⟨M0, hM0⟩ := hψc.isBounded.subset_closedBall (0 : ℝ × ℝ)
  set M := max M0 0 with hMdef
  have hMnn : (0 : ℝ) ≤ M := le_max_right _ _
  have hM0M : M0 ≤ M := le_max_left _ _
  have hout : ∀ t b : ℝ, M < |t| → (t, b) ∉ tsupport ψ := by
    intro t b ht hmem
    have h1 := hM0 hmem
    rw [Metric.mem_closedBall, Prod.dist_eq] at h1
    simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero] at h1
    have h2 : |t| ≤ M0 := le_trans (le_max_left _ _) h1
    linarith only [ht, h2, hM0M]
  -- the inner integral in the first variable vanishes
  have hinner : ∀ b : ℝ, ∫ t : ℝ, (Gp (t, b) * ψ (t, b) + F (t, b) * fderiv ℝ ψ (t, b) (1, 0))
      = 0 := by
    intro b
    have hcontslice : Continuous fun t : ℝ =>
        Gp (t, b) * ψ (t, b) + F (t, b) * fderiv ℝ ψ (t, b) (1, 0) :=
      hAcont.comp (continuous_id.prodMk continuous_const)
    have hle : -(M + 1) ≤ M + 1 := by linarith only [hMnn]
    have hvanish : ∀ t : ℝ, M < |t| →
        Gp (t, b) * ψ (t, b) + F (t, b) * fderiv ℝ ψ (t, b) (1, 0) = 0 :=
      fun t ht => hAzero (t, b) (hout t b ht)
    have hzero : ∀ t : ℝ, t ∉ Ioc (-(M + 1)) (M + 1) →
        Gp (t, b) * ψ (t, b) + F (t, b) * fderiv ℝ ψ (t, b) (1, 0) = 0 := by
      intro t ht
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
      refine hvanish t ?_
      rcases ht with hlow | hhigh
      · have := neg_le_abs t
        linarith only [this, hlow, hMnn]
      · have := le_abs_self t
        linarith only [this, hhigh, hMnn]
    have hftc : (∫ t in (-(M + 1))..(M + 1),
        (Gp (t, b) * ψ (t, b) + F (t, b) * fderiv ℝ ψ (t, b) (1, 0)))
        = F (M + 1, b) * ψ (M + 1, b) - F (-(M + 1), b) * ψ (-(M + 1), b) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => F (t, b) * ψ (t, b)) (fun t _ => hprod (t, b))
        (hcontslice.intervalIntegrable _ _)
    have hψhigh : ψ (M + 1, b) = 0 := by
      refine image_eq_zero_of_notMem_tsupport (hout (M + 1) b ?_)
      rw [abs_of_nonneg (by linarith only [hMnn])]
      linarith only []
    have hψlow : ψ (-(M + 1), b) = 0 := by
      refine image_eq_zero_of_notMem_tsupport (hout (-(M + 1)) b ?_)
      rw [abs_of_nonpos (by linarith only [hMnn]), neg_neg]
      linarith only []
    rw [hψhigh, hψlow, mul_zero, mul_zero, sub_zero] at hftc
    rw [intervalIntegral.integral_of_le hle] at hftc
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    exact hftc
  -- Fubini
  have hfub : (∫ y : ℝ × ℝ, (Gp y * ψ y + F y * fderiv ℝ ψ y (1, 0))) = 0 := by
    have h1 : (∫ y : ℝ × ℝ, (Gp y * ψ y + F y * fderiv ℝ ψ y (1, 0)))
        = ∫ x : ℝ, ∫ t : ℝ, (Gp (x, t) * ψ (x, t) + F (x, t) * fderiv ℝ ψ (x, t) (1, 0)) :=
      MeasureTheory.integral_prod _ hAint
    have h2 : (∫ x : ℝ, ∫ t : ℝ, (Gp (x, t) * ψ (x, t) + F (x, t) * fderiv ℝ ψ (x, t) (1, 0)))
        = ∫ t : ℝ, ∫ x : ℝ, (Gp (x, t) * ψ (x, t) + F (x, t) * fderiv ℝ ψ (x, t) (1, 0)) :=
      MeasureTheory.integral_integral_swap hAint
    rw [h1, h2]
    simp only [hinner]
    exact MeasureTheory.integral_zero ℝ ℝ
  have hsplit : (∫ y : ℝ × ℝ, (Gp y * ψ y + F y * fderiv ℝ ψ y (1, 0)))
      = (∫ y : ℝ × ℝ, Gp y * ψ y) + ∫ y : ℝ × ℝ, F y * fderiv ℝ ψ y (1, 0) :=
    MeasureTheory.integral_add hint1 hint2
  have hconv : (fun y : ℝ × ℝ => F y * deriv (fun t : ℝ => ψ (t, y.2)) y.1)
      = fun y : ℝ × ℝ => F y * fderiv ℝ ψ y (1, 0) := by
    funext y
    rw [(hslice y).deriv]
  rw [hconv, ← hsplit, hfub]

/-- Integration by parts in the second variable of the plane, the companion of
`CIV.integral_partial_fst_mul_add_eq_zero`. -/
theorem integral_partial_snd_mul_add_eq_zero {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F Gp : ℝ × ℝ → ℝ} (hFcont : ContinuousOn F U) (hGcont : ContinuousOn Gp U)
    (hFderiv : ∀ y ∈ U, HasDerivAt (fun s : ℝ => F (y.1, s)) (Gp y) y.2)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    (∫ y : ℝ × ℝ, Gp y * ψ y)
      + ∫ y : ℝ × ℝ, F y * deriv (fun s : ℝ => ψ (y.1, s)) y.2 = 0 := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hψcont : Continuous ψ := hψ.continuous
  have hslice : ∀ y : ℝ × ℝ,
      HasDerivAt (fun s : ℝ => ψ (y.1, s)) (fderiv ℝ ψ y (0, 1)) y.2 :=
    fun y => hasDerivAt_slice_snd hψd y
  have hψ1cont : Continuous fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ1zero : ∀ y : ℝ × ℝ, y ∉ tsupport ψ → fderiv ℝ ψ y (0, 1) = 0 := by
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ hy]
    rfl
  have hψ1supp : tsupport (fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1)) ⊆ tsupport ψ := by
    refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
    by_contra hc
    exact hy (hψ1zero y hc)
  have hψ1c : HasCompactSupport fun y : ℝ × ℝ => fderiv ℝ ψ y (0, 1) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) hψ1supp
  have hint1 : MeasureTheory.Integrable fun y : ℝ × ℝ => Gp y * ψ y :=
    (continuous_mul_of_tsupport_subset hU hGcont hψcont hψU).integrable_of_hasCompactSupport
      hψc.mul_left
  have hint2 : MeasureTheory.Integrable fun y : ℝ × ℝ => F y * fderiv ℝ ψ y (0, 1) :=
    (continuous_mul_of_tsupport_subset hU hFcont hψ1cont
      (hψ1supp.trans hψU)).integrable_of_hasCompactSupport hψ1c.mul_left
  have hAcont : Continuous fun y : ℝ × ℝ => Gp y * ψ y + F y * fderiv ℝ ψ y (0, 1) :=
    (continuous_mul_of_tsupport_subset hU hGcont hψcont hψU).add
      (continuous_mul_of_tsupport_subset hU hFcont hψ1cont (hψ1supp.trans hψU))
  have hAzero : ∀ y : ℝ × ℝ, y ∉ tsupport ψ →
      Gp y * ψ y + F y * fderiv ℝ ψ y (0, 1) = 0 := by
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, hψ1zero y hy, mul_zero, mul_zero, add_zero]
  have hAsupp : HasCompactSupport fun y : ℝ × ℝ => Gp y * ψ y + F y * fderiv ℝ ψ y (0, 1) := by
    refine hψc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun y hy => ?_)
      (isClosed_tsupport ψ))
    by_contra hc
    exact hy (hAzero y hc)
  have hAint : MeasureTheory.Integrable fun y : ℝ × ℝ =>
      Gp y * ψ y + F y * fderiv ℝ ψ y (0, 1) :=
    hAcont.integrable_of_hasCompactSupport hAsupp
  have hprod : ∀ y : ℝ × ℝ, HasDerivAt (fun s : ℝ => F (y.1, s) * ψ (y.1, s))
      (Gp y * ψ y + F y * fderiv ℝ ψ y (0, 1)) y.2 := by
    intro y
    by_cases hy : y ∈ tsupport ψ
    · exact (hFderiv y (hψU hy)).mul (hslice y)
    · have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
      have hset : IsOpen {s : ℝ | (y.1, s) ∈ (tsupport ψ)ᶜ} :=
        hopen.preimage (continuous_const.prodMk continuous_id)
      have hmem : y.2 ∈ {s : ℝ | (y.1, s) ∈ (tsupport ψ)ᶜ} := hy
      have hev : (fun s : ℝ => F (y.1, s) * ψ (y.1, s)) =ᶠ[𝓝 y.2] fun _ => (0 : ℝ) := by
        filter_upwards [hset.mem_nhds hmem] with s hs
        rw [image_eq_zero_of_notMem_tsupport hs, mul_zero]
      rw [hAzero y hy]
      exact (hasDerivAt_const y.2 (0 : ℝ)).congr_of_eventuallyEq hev
  obtain ⟨M0, hM0⟩ := hψc.isBounded.subset_closedBall (0 : ℝ × ℝ)
  set M := max M0 0 with hMdef
  have hMnn : (0 : ℝ) ≤ M := le_max_right _ _
  have hM0M : M0 ≤ M := le_max_left _ _
  have hout : ∀ a s : ℝ, M < |s| → (a, s) ∉ tsupport ψ := by
    intro a s hs hmem
    have h1 := hM0 hmem
    rw [Metric.mem_closedBall, Prod.dist_eq] at h1
    simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero] at h1
    have h2 : |s| ≤ M0 := le_trans (le_max_right _ _) h1
    linarith only [hs, h2, hM0M]
  have hinner : ∀ a : ℝ, ∫ s : ℝ, (Gp (a, s) * ψ (a, s) + F (a, s) * fderiv ℝ ψ (a, s) (0, 1))
      = 0 := by
    intro a
    have hcontslice : Continuous fun s : ℝ =>
        Gp (a, s) * ψ (a, s) + F (a, s) * fderiv ℝ ψ (a, s) (0, 1) :=
      hAcont.comp (continuous_const.prodMk continuous_id)
    have hle : -(M + 1) ≤ M + 1 := by linarith only [hMnn]
    have hvanish : ∀ s : ℝ, M < |s| →
        Gp (a, s) * ψ (a, s) + F (a, s) * fderiv ℝ ψ (a, s) (0, 1) = 0 :=
      fun s hs => hAzero (a, s) (hout a s hs)
    have hzero : ∀ s : ℝ, s ∉ Ioc (-(M + 1)) (M + 1) →
        Gp (a, s) * ψ (a, s) + F (a, s) * fderiv ℝ ψ (a, s) (0, 1) = 0 := by
      intro s hs
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hs
      refine hvanish s ?_
      rcases hs with hlow | hhigh
      · have := neg_le_abs s
        linarith only [this, hlow, hMnn]
      · have := le_abs_self s
        linarith only [this, hhigh, hMnn]
    have hftc : (∫ s in (-(M + 1))..(M + 1),
        (Gp (a, s) * ψ (a, s) + F (a, s) * fderiv ℝ ψ (a, s) (0, 1)))
        = F (a, M + 1) * ψ (a, M + 1) - F (a, -(M + 1)) * ψ (a, -(M + 1)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s : ℝ => F (a, s) * ψ (a, s)) (fun s _ => hprod (a, s))
        (hcontslice.intervalIntegrable _ _)
    have hψhigh : ψ (a, M + 1) = 0 := by
      refine image_eq_zero_of_notMem_tsupport (hout a (M + 1) ?_)
      rw [abs_of_nonneg (by linarith only [hMnn])]
      linarith only []
    have hψlow : ψ (a, -(M + 1)) = 0 := by
      refine image_eq_zero_of_notMem_tsupport (hout a (-(M + 1)) ?_)
      rw [abs_of_nonpos (by linarith only [hMnn]), neg_neg]
      linarith only []
    rw [hψhigh, hψlow, mul_zero, mul_zero, sub_zero] at hftc
    rw [intervalIntegral.integral_of_le hle] at hftc
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    exact hftc
  have hfub : (∫ y : ℝ × ℝ, (Gp y * ψ y + F y * fderiv ℝ ψ y (0, 1))) = 0 := by
    have h1 : (∫ y : ℝ × ℝ, (Gp y * ψ y + F y * fderiv ℝ ψ y (0, 1)))
        = ∫ a : ℝ, ∫ s : ℝ, (Gp (a, s) * ψ (a, s) + F (a, s) * fderiv ℝ ψ (a, s) (0, 1)) :=
      MeasureTheory.integral_prod _ hAint
    rw [h1]
    simp only [hinner]
    exact MeasureTheory.integral_zero ℝ ℝ
  have hsplit : (∫ y : ℝ × ℝ, (Gp y * ψ y + F y * fderiv ℝ ψ y (0, 1)))
      = (∫ y : ℝ × ℝ, Gp y * ψ y) + ∫ y : ℝ × ℝ, F y * fderiv ℝ ψ y (0, 1) :=
    MeasureTheory.integral_add hint1 hint2
  have hconv : (fun y : ℝ × ℝ => F y * deriv (fun s : ℝ => ψ (y.1, s)) y.2)
      = fun y : ℝ × ℝ => F y * fderiv ℝ ψ y (0, 1) := by
    funext y
    rw [(hslice y).deriv]
  rw [hconv, ← hsplit, hfub]

/-- Integration by parts in the first variable, in the form in which the pairing estimate uses
it: the derivative moves from the coefficient onto the test function, at the cost of a sign. -/
theorem integral_partial_fst_mul_eq_neg {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F Gp : ℝ × ℝ → ℝ} (hFcont : ContinuousOn F U) (hGcont : ContinuousOn Gp U)
    (hFderiv : ∀ y ∈ U, HasDerivAt (fun t : ℝ => F (t, y.2)) (Gp y) y.1)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    (∫ y : ℝ × ℝ, Gp y * ψ y)
      = -∫ y : ℝ × ℝ, F y * deriv (fun t : ℝ => ψ (t, y.2)) y.1 :=
  eq_neg_of_add_eq_zero_left
    (integral_partial_fst_mul_add_eq_zero hU hFcont hGcont hFderiv hψ hψc hψU)

/-- Integration by parts in the second variable, in the form in which the pairing estimate uses
it. -/
theorem integral_partial_snd_mul_eq_neg {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F Gp : ℝ × ℝ → ℝ} (hFcont : ContinuousOn F U) (hGcont : ContinuousOn Gp U)
    (hFderiv : ∀ y ∈ U, HasDerivAt (fun s : ℝ => F (y.1, s)) (Gp y) y.2)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    (∫ y : ℝ × ℝ, Gp y * ψ y)
      = -∫ y : ℝ × ℝ, F y * deriv (fun s : ℝ => ψ (y.1, s)) y.2 :=
  eq_neg_of_add_eq_zero_left
    (integral_partial_snd_mul_add_eq_zero hU hFcont hGcont hFderiv hψ hψc hψU)

/-- The pairing of a function bounded on a set of finite measure with a test function supported
in that set is bounded by the product of the two bounds and the measure: this is the estimate
which collects the constant `Cₒ` of the pairing hypothesis from the bounds on the individual
terms of the equation. -/
theorem abs_integral_mul_le_of_tsupport_subset {S : Set (ℝ × ℝ)}
    (hSfin : MeasureTheory.volume S < ⊤) {a ψ : ℝ × ℝ → ℝ} {Ma B : ℝ}
    (hψS : tsupport ψ ⊆ S) (ha : ∀ y ∈ S, |a y| ≤ Ma) (hψ : ∀ y, |ψ y| ≤ B) :
    |∫ y : ℝ × ℝ, a y * ψ y| ≤ Ma * B * (MeasureTheory.volume S).toReal := by
  have hzero : ∀ y : ℝ × ℝ, y ∉ S → a y * ψ y = 0 := by
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport fun hc => hy (hψS hc), mul_zero]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hC : ∀ y ∈ S, ‖a y * ψ y‖ ≤ Ma * B := by
    intro y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (ha y hy) (hψ y) (abs_nonneg _) (le_trans (abs_nonneg _) (ha y hy))
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hSfin hC
  rwa [Real.norm_eq_abs] at h

/-! ### A uniform modulus of continuity -/

/-- A function with a uniform modulus of continuity on a set is continuous on it. -/
theorem continuousOn_of_modulus {X : Type*} [MetricSpace X] (S : Set X) (f : X → ℝ)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → |f x - f y| ≤ ε) :
    ContinuousOn f S := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  obtain ⟨δ, hδ, hd⟩ := hmod (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun a ha hab => ?_⟩
  have h := hd a ha b hb hab
  rw [Real.dist_eq]
  calc |f a - f b| ≤ ε / 2 := h
    _ < ε := by linarith only [hε]

/-! ### Arzelà–Ascoli on a compact set of a metric space -/

/-- Arzelà–Ascoli: a sequence of real functions that is uniformly bounded on a compact set `S`
of a metric space and shares one modulus of continuity on `S` has a subsequence converging
uniformly on `S` to a function continuous on `S`. -/
theorem exists_subseq_tendstoUniformlyOn_of_modulus {X : Type*} [MetricSpace X]
    (S : Set X) (hS : IsCompact S) (f : ℕ → X → ℝ) (M : ℝ)
    (hbdd : ∀ n, ∀ x ∈ S, |f n x| ≤ M)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → |f n x - f n y| ≤ ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℝ,
      ContinuousOn g S ∧ TendstoUniformlyOn (fun n => f (φ n)) g atTop S := by
  classical
  have hSC : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS
  have hcont : ∀ n, ContinuousOn (f n) S := by
    intro n
    refine continuousOn_of_modulus S (f n) ?_
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hmod ε hε
    exact ⟨δ, hδ, fun x hx y hy hxy => hd n x hx y hy hxy⟩
  set fc : ℕ → C(↥S, ℝ) := fun n =>
    ⟨S.domRestrict (f n), continuousOn_iff_continuous_domRestrict.mp (hcont n)⟩ with hfc
  set fb : ℕ → (↥S →ᵇ ℝ) := fun n => BoundedContinuousFunction.mkOfCompact (fc n) with hfb
  have hfbcoe : ∀ n, (fb n : ↥S → ℝ) = S.domRestrict (f n) := fun n => rfl
  have hEqui : Equicontinuous ((↑) : Set.range fb → ↥S → ℝ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hmod (ε / 2) (by positivity)
    refine ⟨δ, hδ, ?_⟩
    rintro x hx ⟨F, n, rfl⟩
    have hdx : dist (x : X) (x₀ : X) < δ := hx
    have hbound := hd n (x₀ : X) x₀.2 (x : X) x.2 (by rwa [dist_comm] at hdx)
    have hrw : dist ((fb n : ↥S → ℝ) x₀) ((fb n : ↥S → ℝ) x) = |f n (x₀ : X) - f n (x : X)| := by
      rw [hfbcoe]
      exact Real.dist_eq _ _
    change dist ((fb n : ↥S → ℝ) x₀) ((fb n : ↥S → ℝ) x) < ε
    rw [hrw]
    calc |f n (x₀ : X) - f n (x : X)| ≤ ε / 2 := hbound
      _ < ε := by linarith only [hε]
  have hin_s : ∀ (F : ↥S →ᵇ ℝ) (x : ↥S), F ∈ Set.range fb → F x ∈ Metric.closedBall (0 : ℝ) M := by
    rintro F x ⟨n, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hbdd n (x : X) x.2
  have hcompact : IsCompact (closure (Set.range fb)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) M)
      (isCompact_closedBall _ _) (Set.range fb) hin_s hEqui
  have hmemc : ∀ n, fb n ∈ closure (Set.range fb) := fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨glimb, -, φ, hφmono, hφtendsto⟩ := hcompact.tendsto_subseq hmemc
  set g : X → ℝ := fun x => if hx : x ∈ S then glimb ⟨x, hx⟩ else 0 with hg
  have huniform : TendstoUniformlyOn (fun n => f (φ n)) g atTop S := by
    have h1 : TendstoUniformly (fun n => (fb (φ n) : ↥S → ℝ)) (glimb : ↥S → ℝ) atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφtendsto
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    intro u hu
    filter_upwards [h1 u hu] with n hn x
    simpa [hg, hfbcoe, Set.domRestrict_eq, x.2] using hn x
  exact ⟨φ, hφmono, g,
    huniform.continuousOn (Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun n => hcont (φ n))), huniform⟩

/-! ### The space–time modulus on a rectangle -/

/-- The space–time modulus of continuity of the sequence on `K' ×ˢ J`, uniform in `n`: the
spatial Lipschitz bound `hlip` controls a move in space, and the pairing bound `hpair`
controls a move in time through `CIV.equicontinuous_of_lipschitz_of_pairings`. -/
theorem exists_modulus_of_lipschitz_of_pairings (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (J : Set ℝ) (Θ : ℕ → (ℝ × ℝ) × ℝ → ℝ) (L : ℝ)
    (hlip : ∀ n, ∀ τ ∈ J, LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) K)
    (hpair : ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
      ∀ B : ℝ, 0 ≤ B → (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ n : ℕ, ∀ τ ∈ J, ∀ τ' ∈ J,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'|)
    (K' : Set (ℝ × ℝ)) (hK' : IsCompact K') (hKK' : K' ⊆ interior K) :
    ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ p ∈ K' ×ˢ J, ∀ q ∈ K' ×ˢ J,
      dist p q < δ → |Θ n p - Θ n q| ≤ ε := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hd₁⟩ := equicontinuous_of_lipschitz_of_pairings K hK J Θ L hlip hpair
    K' hK' hKK' (ε / 2) (by positivity)
  set L' := max L 0 with hL'def
  have hL'nn : (0 : ℝ) ≤ L' := le_max_right _ _
  have hposden : (0 : ℝ) < 2 * (L' + 1) := by positivity
  refine ⟨min δ₁ (ε / (2 * (L' + 1))), lt_min hδ₁ (by positivity), ?_⟩
  intro n p hp q hq hpq
  have hp1 : p.1 ∈ K' := hp.1
  have hp2 : p.2 ∈ J := hp.2
  have hq1 : q.1 ∈ K' := hq.1
  have hq2 : q.2 ∈ J := hq.2
  have hsplit : dist p q = max (dist p.1 q.1) (dist p.2 q.2) := Prod.dist_eq
  have hd1 : dist p.1 q.1 ≤ dist p q := by rw [hsplit]; exact le_max_left _ _
  have hd2 : dist p.2 q.2 ≤ dist p q := by rw [hsplit]; exact le_max_right _ _
  -- the spatial move
  have hp1K : p.1 ∈ K := interior_subset (hKK' hp1)
  have hq1K : q.1 ∈ K := interior_subset (hKK' hq1)
  have hlipd := (hlip n p.2 hp2).dist_le_mul p.1 hp1K q.1 hq1K
  rw [Real.coe_toNNReal' ] at hlipd
  have hspace : |Θ n (p.1, p.2) - Θ n (q.1, p.2)| ≤ L' * dist p.1 q.1 := by
    rw [← Real.dist_eq]
    exact hlipd
  have hstep : L' * dist p.1 q.1 ≤ ε / 2 := by
    have hle1 : dist p.1 q.1 ≤ ε / (2 * (L' + 1)) :=
      le_trans hd1 (le_trans hpq.le (min_le_right _ _))
    have hle2 : L' * dist p.1 q.1 ≤ L' * (ε / (2 * (L' + 1))) :=
      mul_le_mul_of_nonneg_left hle1 hL'nn
    have hle3 : L' * (ε / (2 * (L' + 1))) ≤ (L' + 1) * (ε / (2 * (L' + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith only []) (by positivity)
    have heq : (L' + 1) * (ε / (2 * (L' + 1))) = ε / 2 := by
      have hne : L' + 1 ≠ 0 := by positivity
      field_simp
    linarith only [hle2, hle3, heq]
  -- the move in time
  have htime : |Θ n (q.1, p.2) - Θ n (q.1, q.2)| ≤ ε / 2 := by
    refine hd₁ n q.1 hq1 p.2 hp2 q.2 hq2 ?_
    have hlt : dist p.2 q.2 < δ₁ := lt_of_le_of_lt hd2 (lt_of_lt_of_le hpq (min_le_left _ _))
    rwa [Real.dist_eq] at hlt
  have hkey : Θ n p - Θ n q
      = (Θ n (p.1, p.2) - Θ n (q.1, p.2)) + (Θ n (q.1, p.2) - Θ n (q.1, q.2)) := by
    change Θ n (p.1, p.2) - Θ n (q.1, q.2) = _
    ring
  rw [hkey]
  calc |(Θ n (p.1, p.2) - Θ n (q.1, p.2)) + (Θ n (q.1, p.2) - Θ n (q.1, q.2))|
      ≤ |Θ n (p.1, p.2) - Θ n (q.1, p.2)| + |Θ n (q.1, p.2) - Θ n (q.1, q.2)| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add (le_trans hspace hstep) htime
    _ = ε := by ring

/-! ### Extraction on a single rectangle -/

/-- Step 2 on a single closed rectangle: from the uniform bound, the uniform spatial Lipschitz
bound, and the pairing bound on `K`, a subsequence of `Θ` converges uniformly on `K' ×ˢ J` for
every compact `K'` in the interior of `K`, and the limit is continuous there. -/
theorem exists_subseq_tendstoUniformlyOn_prod (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (J : Set ℝ) (hJ : IsCompact J) (Θ : ℕ → (ℝ × ℝ) × ℝ → ℝ) (M L : ℝ)
    (hbdd : ∀ n, ∀ y ∈ K, ∀ τ ∈ J, |Θ n (y, τ)| ≤ M)
    (hlip : ∀ n, ∀ τ ∈ J, LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) K)
    (hpair : ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
      ∀ B : ℝ, 0 ≤ B → (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ n : ℕ, ∀ τ ∈ J, ∀ τ' ∈ J,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'|)
    (K' : Set (ℝ × ℝ)) (hK' : IsCompact K') (hKK' : K' ⊆ interior K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : (ℝ × ℝ) × ℝ → ℝ,
      ContinuousOn Ω (K' ×ˢ J) ∧
      TendstoUniformlyOn (fun n => Θ (φ n)) Ω atTop (K' ×ˢ J) := by
  refine exists_subseq_tendstoUniformlyOn_of_modulus (K' ×ˢ J) (hK'.prod hJ) Θ M ?_ ?_
  · intro n x hx
    exact hbdd n x.1 (interior_subset (hKK' hx.1)) x.2 hx.2
  · exact exists_modulus_of_lipschitz_of_pairings K hK J Θ L hlip hpair K' hK' hKK'

/-! ### The diagonal extraction -/

/-- Diagonal extraction over a countable family of sets: if from every subsequence one can
extract a further subsequence converging uniformly on `S j`, then a single subsequence
converges uniformly on every `S j`, with one limit function. -/
theorem exists_subseq_tendstoUniformlyOn_forall {X : Type*} (S : ℕ → Set X) (f : ℕ → X → ℝ)
    (hstep : ∀ (j : ℕ) (g : ℕ → ℕ), StrictMono g →
      ∃ g' : ℕ → ℕ, StrictMono g' ∧ ∃ w : X → ℝ,
        TendstoUniformlyOn (fun n => f (g (g' n))) w atTop (S j)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : X → ℝ,
      ∀ j, TendstoUniformlyOn (fun n => f (φ n)) w atTop (S j) := by
  classical
  have hstep' : ∀ (j : ℕ) (g : {h : ℕ → ℕ // StrictMono h}),
      ∃ g' : {h : ℕ → ℕ // StrictMono h}, ∃ w : X → ℝ,
        TendstoUniformlyOn (fun n => f (g.1 (g'.1 n))) w atTop (S j) := by
    intro j g
    obtain ⟨g', hg', w, hw⟩ := hstep j g.1 g.2
    exact ⟨⟨g', hg'⟩, w, hw⟩
  choose rho w hw using hstep'
  obtain ⟨Psi, hPsisucc⟩ :
      ∃ P : ℕ → {h : ℕ → ℕ // StrictMono h},
        ∀ k, (P (k + 1)).1 = (P k).1 ∘ (rho k (P k)).1 :=
    ⟨fun j => Nat.rec (motive := fun _ => {h : ℕ → ℕ // StrictMono h})
      ⟨fun n => n, strictMono_id⟩
      (fun k p => ⟨p.1 ∘ (rho k p).1, p.2.comp (rho k p).2⟩) j, fun _ => rfl⟩
  have hconv : ∀ j,
      TendstoUniformlyOn (fun n => f ((Psi (j + 1)).1 n)) (w j (Psi j)) atTop (S j) := by
    intro j
    have h := hw j (Psi j)
    have heq : (fun n => f ((Psi (j + 1)).1 n))
        = fun n => f ((Psi j).1 ((rho j (Psi j)).1 n)) := by
      funext n
      rw [hPsisucc j]
      rfl
    rw [heq]
    exact h
  have hnest : ∀ j m, j ≤ m → ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∀ n, (Psi (m + 1)).1 n = (Psi (j + 1)).1 (κ n) := by
    intro j m hjm
    induction m, hjm using Nat.le_induction with
    | base => exact ⟨fun n => n, strictMono_id, fun _ => rfl⟩
    | succ m hm ih =>
        obtain ⟨κ, hκ, hκeq⟩ := ih
        refine ⟨fun n => κ ((rho (m + 1) (Psi (m + 1))).1 n),
          hκ.comp (rho (m + 1) (Psi (m + 1))).2, fun n => ?_⟩
        rw [hPsisucc (m + 1)]
        exact hκeq _
  have hφmono : StrictMono (fun n => (Psi (n + 1)).1 n) := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    have h1 : (Psi (n + 1 + 1)).1 (n + 1)
        = (Psi (n + 1)).1 ((rho (n + 1) (Psi (n + 1))).1 (n + 1)) := by
      rw [hPsisucc (n + 1)]
      rfl
    have h2 : n + 1 ≤ (rho (n + 1) (Psi (n + 1))).1 (n + 1) :=
      (rho (n + 1) (Psi (n + 1))).2.le_apply
    have h3 : (Psi (n + 1)).1 (n + 1)
        ≤ (Psi (n + 1)).1 ((rho (n + 1) (Psi (n + 1))).1 (n + 1)) := (Psi (n + 1)).2.monotone h2
    have h4 : (Psi (n + 1)).1 n < (Psi (n + 1)).1 (n + 1) :=
      (Psi (n + 1)).2 (Nat.lt_succ_self n)
    change (Psi (n + 1)).1 n < (Psi (n + 1 + 1)).1 (n + 1)
    rw [h1]
    exact lt_of_lt_of_le h4 h3
  refine ⟨fun n => (Psi (n + 1)).1 n, hφmono,
    fun x => limUnder atTop fun n => f ((Psi (n + 1)).1 n) x, fun j => ?_⟩
  have hmain : TendstoUniformlyOn (fun n => f ((Psi (n + 1)).1 n)) (w j (Psi j)) atTop (S j) := by
    intro u hu
    have h := hconv j u hu
    rw [eventually_atTop] at h ⊢
    obtain ⟨N, hN⟩ := h
    refine ⟨max N j, fun n hn => ?_⟩
    obtain ⟨κ, hκ, hκeq⟩ := hnest j n (le_trans (le_max_right N j) hn)
    have hκn : n ≤ κ n := hκ.le_apply
    have hNn : N ≤ κ n := le_trans (le_trans (le_max_left N j) hn) hκn
    have hstepN := hN (κ n) hNn
    intro x hx
    have h2 := hstepN x hx
    change (w j (Psi j) x, f ((Psi (n + 1)).1 n) x) ∈ u
    rw [hκeq n]
    exact h2
  refine hmain.congr_right fun x hx => ?_
  have hpt : Tendsto (fun n => f ((Psi (n + 1)).1 n) x) atTop (𝓝 (w j (Psi j) x)) :=
    hmain.tendsto_at hx
  exact hpt.limUnder_eq.symm

/-! ### Exhaustion of the region by closed rectangles -/

/-- The closed rectangles `[1/(j+1), j+1] × [-(j+1), j+1]` exhausting the open half-plane. -/
private def zoomRectangle (j : ℕ) : Set (ℝ × ℝ) :=
  Icc (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1) ×ˢ Icc (-((j : ℝ) + 1)) ((j : ℝ) + 1)

/-- The closed time intervals `[-(j+1), -1]` exhausting `(-∞, -1]`. -/
private def zoomTimeInterval (j : ℕ) : Set ℝ := Icc (-((j : ℝ) + 1)) (-1)

private theorem isCompact_zoomRectangle (j : ℕ) : IsCompact (zoomRectangle j) :=
  isCompact_Icc.prod isCompact_Icc

private theorem isCompact_zoomTimeInterval (j : ℕ) : IsCompact (zoomTimeInterval j) :=
  isCompact_Icc

private theorem pos_of_mem_zoomRectangle {j : ℕ} {y : ℝ × ℝ} (hy : y ∈ zoomRectangle j) :
    0 < y.1 := by
  have h1 : 1 / ((j : ℝ) + 1) ≤ y.1 := hy.1.1
  have h2 : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  linarith only [h1, h2]

private theorem le_of_mem_zoomTimeInterval {j : ℕ} {τ : ℝ} (hτ : τ ∈ zoomTimeInterval j) :
    τ ≤ -1 := hτ.2

private theorem mem_zoomRectangle_prod_iff (j : ℕ) (q : (ℝ × ℝ) × ℝ) :
    q ∈ zoomRectangle j ×ˢ zoomTimeInterval j ↔
      (1 / ((j : ℝ) + 1) ≤ q.1.1 ∧ q.1.1 ≤ (j : ℝ) + 1) ∧
        (-((j : ℝ) + 1) ≤ q.1.2 ∧ q.1.2 ≤ (j : ℝ) + 1) ∧
        (-((j : ℝ) + 1) ≤ q.2 ∧ q.2 ≤ -1) := by
  simp only [zoomRectangle, zoomTimeInterval, Set.mem_prod, Set.mem_Icc]
  tauto

private theorem exists_nat_add_one_gt_four (a b c d : ℝ) :
    ∃ j : ℕ, a < (j : ℝ) + 1 ∧ b < (j : ℝ) + 1 ∧ c < (j : ℝ) + 1 ∧ d < (j : ℝ) + 1 := by
  obtain ⟨j, hj⟩ := exists_nat_gt (max (max a b) (max c d))
  have h0 : ((j : ℕ) : ℝ) < (j : ℝ) + 1 := by linarith only []
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · exact lt_trans (lt_of_le_of_lt (le_trans (le_max_left a b) (le_max_left _ _)) hj) h0
  · exact lt_trans (lt_of_le_of_lt (le_trans (le_max_right a b) (le_max_left _ _)) hj) h0
  · exact lt_trans (lt_of_le_of_lt (le_trans (le_max_left c d) (le_max_right _ _)) hj) h0
  · exact lt_trans (lt_of_le_of_lt (le_trans (le_max_right c d) (le_max_right _ _)) hj) h0

/-- Every compact subset of `{R > 0} × ℝ × (-∞, -1]` lies in one of the exhausting rectangles:
the radius has a positive minimum and every coordinate a finite maximum on a compact set. -/
private theorem exists_subset_zoomRectangle_prod {C : Set ((ℝ × ℝ) × ℝ)} (hC : IsCompact C)
    (hCsub : ∀ q ∈ C, 0 < q.1.1 ∧ q.2 ≤ -1) :
    ∃ j : ℕ, C ⊆ zoomRectangle j ×ˢ zoomTimeInterval j := by
  rcases C.eq_empty_or_nonempty with hempty | hne
  · exact ⟨0, by rw [hempty]; exact empty_subset _⟩
  obtain ⟨a, haC, hamin⟩ :=
    hC.exists_isMinOn hne (continuous_fst.comp continuous_fst).continuousOn
  obtain ⟨b, hbC, hbmax⟩ :=
    hC.exists_isMaxOn hne (continuous_fst.comp continuous_fst).continuousOn
  obtain ⟨c, hcC, hcmax⟩ :=
    hC.exists_isMaxOn hne (continuous_snd.comp continuous_fst).abs.continuousOn
  obtain ⟨d, hdC, hdmax⟩ := hC.exists_isMaxOn hne continuous_snd.neg.continuousOn
  have hapos : 0 < a.1.1 := (hCsub a haC).1
  obtain ⟨j, hj1, hj2, hj3, hj4⟩ :=
    exists_nat_add_one_gt_four (1 / a.1.1) b.1.1 |c.1.2| (-d.2)
  have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hrad : 1 / ((j : ℝ) + 1) < a.1.1 := (one_div_lt hapos hjpos).mp hj1
  refine ⟨j, fun q hq => ?_⟩
  rw [mem_zoomRectangle_prod_iff]
  have hmin : a.1.1 ≤ q.1.1 := isMinOn_iff.mp hamin q hq
  have hmax : q.1.1 ≤ b.1.1 := isMaxOn_iff.mp hbmax q hq
  have hzmax : |q.1.2| ≤ |c.1.2| := isMaxOn_iff.mp hcmax q hq
  have htmax : -q.2 ≤ -d.2 := isMaxOn_iff.mp hdmax q hq
  have hzabs : |q.1.2| < (j : ℝ) + 1 := lt_of_le_of_lt hzmax hj3
  obtain ⟨hz1, hz2⟩ := abs_lt.mp hzabs
  exact ⟨⟨le_of_lt (lt_of_lt_of_le hrad hmin), le_of_lt (lt_of_le_of_lt hmax hj2)⟩,
    ⟨le_of_lt hz1, le_of_lt hz2⟩,
    by linarith only [htmax, hj4], (hCsub q hq).2⟩

/-! ### Enclosing a compact set in a rectangle -/

/-- A compact subset of the open half-plane `{R > 0}` lies in a closed rectangle whose radial
side starts at a positive radius. This is the bridge between the hypotheses below, stated for
compact sets, and the bounds on `Ω_n`, which are proved on rectangles `[Ra, Rb] × [Za, Zb]`
contained in `{R ≥ ε}`. -/
theorem exists_rectangle_of_isCompact {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKpos : ∀ y ∈ K, 0 < y.1) :
    ∃ a b c d : ℝ, 0 < a ∧ K ⊆ Icc a b ×ˢ Icc c d := by
  rcases K.eq_empty_or_nonempty with hempty | hne
  · exact ⟨1, 1, 0, 0, one_pos, by rw [hempty]; exact empty_subset _⟩
  obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
  obtain ⟨q, hqK, hqmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
  obtain ⟨r, hrK, hrmin⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
  obtain ⟨t, htK, htmax⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
  exact ⟨p.1, q.1, r.2, t.2, hKpos p hpK, fun y hy =>
    ⟨⟨isMinOn_iff.mp hpmin y hy, isMaxOn_iff.mp hqmax y hy⟩,
      isMinOn_iff.mp hrmin y hy, isMaxOn_iff.mp htmax y hy⟩⟩

/-- A compact set of rescaled times in `(-∞, -1]` lies in a closed interval `[-T, -1]`. -/
theorem exists_Icc_neg_one_of_isCompact {J : Set ℝ} (hJ : IsCompact J)
    (hJle : ∀ τ ∈ J, τ ≤ -1) :
    ∃ T : ℝ, J ⊆ Icc (-T) (-1) := by
  rcases J.eq_empty_or_nonempty with hempty | hne
  · exact ⟨0, by rw [hempty]; exact empty_subset _⟩
  obtain ⟨t, htJ, htmin⟩ :=
    hJ.exists_isMinOn hne (f := fun x : ℝ => x) continuous_id.continuousOn
  refine ⟨-t, fun τ hτ => ⟨?_, hJle τ hτ⟩⟩
  rw [neg_neg]
  exact isMinOn_iff.mp htmin τ hτ

/-! ### The locally uniform limit on `{R > 0} × ℝ × (-∞, -1]` -/

/-- Step 2 of the finite-axis zoom-in argument, `eq:aniso:zoom:finite:compactness`: a sequence
which on every closed rectangle of the open half-plane and every compact time interval in
`(-∞, -1]` is uniformly bounded, uniformly Lipschitz in space, and obeys the pairing bound in
time, has a subsequence converging uniformly on every compact subset of
`{R > 0} × ℝ × (-∞, -1]`, to a limit continuous there. -/
theorem exists_subseq_tendstoUniformlyOn_of_lipschitz_of_pairings (Θ : ℕ → (ℝ × ℝ) × ℝ → ℝ)
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ M : ℝ, ∀ n, ∀ y ∈ K, ∀ τ ∈ J, |Θ n (y, τ)| ≤ M)
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ L : ℝ, ∀ n, ∀ τ ∈ J, LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) K)
    (hpair : ∀ K : Set (ℝ × ℝ), IsCompact K → (∀ y ∈ K, 0 < y.1) →
      ∀ J : Set ℝ, IsCompact J → (∀ τ ∈ J, τ ≤ -1) →
      ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
        ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ interior K →
        ∀ B : ℝ, 0 ≤ B →
          (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
          ∀ n : ℕ, ∀ τ ∈ J, ∀ τ' ∈ J,
            |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ω : (ℝ × ℝ) × ℝ → ℝ,
      ContinuousOn Ω {q : (ℝ × ℝ) × ℝ | 0 < q.1.1 ∧ q.2 ≤ -1} ∧
      ∀ C : Set ((ℝ × ℝ) × ℝ), IsCompact C → C ⊆ {q : (ℝ × ℝ) × ℝ | 0 < q.1.1 ∧ q.2 ≤ -1} →
        TendstoUniformlyOn (fun n => Θ (φ n)) Ω atTop C := by
  classical
  have hopenHalf : IsOpen {y : ℝ × ℝ | 0 < y.1} := isOpen_lt continuous_const continuous_fst
  have hbig : ∀ j : ℕ, ∃ K : Set (ℝ × ℝ), IsCompact K ∧ (∀ y ∈ K, 0 < y.1) ∧
      zoomRectangle j ⊆ interior K := by
    intro j
    obtain ⟨ρ, hρ, hρsub⟩ := (isCompact_zoomRectangle j).exists_cthickening_subset_open
      hopenHalf fun y hy => pos_of_mem_zoomRectangle hy
    exact ⟨Metric.cthickening ρ (zoomRectangle j), (isCompact_zoomRectangle j).cthickening,
      fun y hy => hρsub hy,
      (Metric.self_subset_thickening hρ _).trans
        (Metric.thickening_subset_interior_cthickening ρ _)⟩
  choose Kb hKbc hKbp hKbs using hbig
  have hMex : ∀ j : ℕ, ∃ M : ℝ, ∀ n, ∀ y ∈ Kb j, ∀ τ ∈ zoomTimeInterval j,
      |Θ n (y, τ)| ≤ M := fun j =>
    hbdd (Kb j) (hKbc j) (hKbp j) (zoomTimeInterval j) (isCompact_zoomTimeInterval j)
      fun _ hτ => le_of_mem_zoomTimeInterval hτ
  choose Mc hMc using hMex
  have hLex : ∀ j : ℕ, ∃ L : ℝ, ∀ n, ∀ τ ∈ zoomTimeInterval j,
      LipschitzOnWith (Real.toNNReal L) (fun y => Θ n (y, τ)) (Kb j) := fun j =>
    hlip (Kb j) (hKbc j) (hKbp j) (zoomTimeInterval j) (isCompact_zoomTimeInterval j)
      fun _ hτ => le_of_mem_zoomTimeInterval hτ
  choose Lc hLc using hLex
  have hPc : ∀ j : ℕ, ∃ Cₒ : ℝ, 0 ≤ Cₒ ∧
      ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ interior (Kb j) → ∀ B : ℝ, 0 ≤ B →
      (∀ y, |ψ y| ≤ B ∧ ‖fderiv ℝ ψ y‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) →
      ∀ n : ℕ, ∀ τ ∈ zoomTimeInterval j, ∀ τ' ∈ zoomTimeInterval j,
        |∫ y, (Θ n (y, τ) - Θ n (y, τ')) * ψ y| ≤ Cₒ * B * |τ - τ'| := fun j =>
    hpair (Kb j) (hKbc j) (hKbp j) (zoomTimeInterval j) (isCompact_zoomTimeInterval j)
      fun _ hτ => le_of_mem_zoomTimeInterval hτ
  have hmod : ∀ j : ℕ, ∀ ε > 0, ∃ δ > 0, ∀ n,
      ∀ p ∈ zoomRectangle j ×ˢ zoomTimeInterval j, ∀ q ∈ zoomRectangle j ×ˢ zoomTimeInterval j,
      dist p q < δ → |Θ n p - Θ n q| ≤ ε := fun j =>
    exists_modulus_of_lipschitz_of_pairings (Kb j) (hKbc j) (zoomTimeInterval j)
      Θ (Lc j) (hLc j) (hPc j) (zoomRectangle j)
      (isCompact_zoomRectangle j) (hKbs j)
  have hstep : ∀ (j : ℕ) (g : ℕ → ℕ), StrictMono g →
      ∃ g' : ℕ → ℕ, StrictMono g' ∧ ∃ w : (ℝ × ℝ) × ℝ → ℝ,
        TendstoUniformlyOn (fun n => Θ (g (g' n))) w atTop
          (zoomRectangle j ×ˢ zoomTimeInterval j) := by
    intro j g _
    obtain ⟨Cₒ, hCₒ, hC⟩ := hPc j
    obtain ⟨g', hg'mono, w, -, hw⟩ :=
      exists_subseq_tendstoUniformlyOn_prod (Kb j) (hKbc j) (zoomTimeInterval j)
        (isCompact_zoomTimeInterval j) (fun n => Θ (g n)) (Mc j) (Lc j)
        (fun n => hMc j (g n)) (fun n => hLc j (g n))
        ⟨Cₒ, hCₒ, fun ψ h1 h2 h3 B hB hB' n => hC ψ h1 h2 h3 B hB hB' (g n)⟩
        (zoomRectangle j) (isCompact_zoomRectangle j) (hKbs j)
    exact ⟨g', hg'mono, w, hw⟩
  obtain ⟨φ, hφmono, Ω, hΩ⟩ :=
    exists_subseq_tendstoUniformlyOn_forall
      (fun j => zoomRectangle j ×ˢ zoomTimeInterval j) Θ hstep
  have hcontbox : ∀ j : ℕ, ContinuousOn Ω (zoomRectangle j ×ˢ zoomTimeInterval j) := by
    intro j
    refine (hΩ j).continuousOn (Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun n => ?_))
    refine continuousOn_of_modulus _ (Θ (φ n)) fun ε hε => ?_
    obtain ⟨δ, hδ, hd⟩ := hmod j ε hε
    exact ⟨δ, hδ, fun x hx y hy hxy => hd (φ n) x hx y hy hxy⟩
  refine ⟨φ, hφmono, Ω, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqR, hqτ⟩ := hq
    obtain ⟨j, hj1, hj2, hj3, hj4⟩ :=
      exists_nat_add_one_gt_four (1 / q.1.1) q.1.1 |q.1.2| (-q.2)
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hrad : 1 / ((j : ℝ) + 1) < q.1.1 := (one_div_lt hqR hjpos).mp hj1
    obtain ⟨hz1, hz2⟩ := abs_lt.mp hj3
    obtain ⟨U, hUopen, hqU, hUsub⟩ :
        ∃ U : Set ((ℝ × ℝ) × ℝ), IsOpen U ∧ q ∈ U ∧
          {x : (ℝ × ℝ) × ℝ | 0 < x.1.1 ∧ x.2 ≤ -1} ∩ U
            ⊆ zoomRectangle j ×ˢ zoomTimeInterval j := by
      refine ⟨(Ioo (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1) ×ˢ Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1)) ×ˢ
        Ioi (-((j : ℝ) + 1)), (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioi,
        ⟨⟨⟨hrad, hj2⟩, hz1, hz2⟩, Set.mem_Ioi.mpr (by linarith only [hj4])⟩, fun x hx => ?_⟩
      obtain ⟨⟨-, hx2⟩, ⟨⟨hu1, hu2⟩, hu3, hu4⟩, hu5⟩ := hx
      rw [mem_zoomRectangle_prod_iff]
      exact ⟨⟨hu1.le, hu2.le⟩, ⟨hu3.le, hu4.le⟩, le_of_lt hu5, hx2⟩
    have hmem : q ∈ zoomRectangle j ×ˢ zoomTimeInterval j := hUsub ⟨⟨hqR, hqτ⟩, hqU⟩
    have hcw : ContinuousWithinAt Ω ({x : (ℝ × ℝ) × ℝ | 0 < x.1.1 ∧ x.2 ≤ -1} ∩ U) q :=
      (hcontbox j q hmem).mono hUsub
    rwa [continuousWithinAt_inter (hUopen.mem_nhds hqU)] at hcw
  · intro C hC hCsub
    obtain ⟨j, hj⟩ := exists_subset_zoomRectangle_prod hC fun q hq => hCsub hq
    exact (hΩ j).mono hj


end CIV
