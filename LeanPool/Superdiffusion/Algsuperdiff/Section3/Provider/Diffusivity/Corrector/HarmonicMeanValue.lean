/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicSphereBump
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicGreen

/-!
# HarmonicMeanValue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The mean value property for the coordinate Laplacian on `Vec d`

Mathlib proves the mean value property for harmonic functions **only in the
complex plane** (`Analysis/Complex/Harmonic/MeanValue`, through
`circleAverage`); it has no `sphereAverage` at all, and its harmonic layer is
stated for `InnerProductSpace R E`, which the sup-normed carrier `Vec d` does not
satisfy.  CoarseGraining has no mean value property either.  This module
supplies one natively for CoarseGraining's coordinate Laplacian on `Vec d`, in
the *kernel* form that avoids surface measure entirely.

The argument is the classical one, run through the Green pairing of
`HarmonicGreen` rather than through the divergence theorem:

1. **Zero moment kills the pairing.**  If a continuous radial density `k` is
   supported in an annulus `[a, b]` with `0 < a < b` and its radial moment
   `int_0^b s^(d-1) k s ds` vanishes, then `HarmonicSphereBump` produces a
   compactly supported `C^2` function `psi` with `Delta psi = k(|· - z|)`, and
   Green's second identity gives `int u (x) k (|x - z|) dx = 0` for every `u`
   that is `C^2` and harmonic on the closed ball of radius `b`.  Taking `u = 1`
   -- itself harmonic -- gives the same statement for the mass of the density.
2. **Kernel independence.**  Applying step 1 to the combination
   `M_2 k_1 - M_1 k_2` of two densities with moments `M_1, M_2` shows that
   `M_2 * int u k_1 = M_1 * int u k_2`, and likewise for the masses.  Hence the
   *normalized* pairing `int u k / int k` does not depend on the density.
3. **Concentration.**  For a nonnegative density supported in the ball of radius
   `delta`, the normalized pairing differs from `u z` by at most the oscillation
   of `u` on that ball.  Shrinking `delta` and using continuity of `u` pins the
   common value of step 2 to `u z`.

No surface measure, no coarea formula and no polar decomposition are used: the
whole argument stays inside the Green pairing.  The explicit density
`annulusBump a b t = max 0 ((t - a) * (b - t))` makes the final statement
unconditional.

## Contents

* `integral_mul_radial_eq_zero_of_radialMoment_eq_zero` -- step 1.
* `integral_radial_eq_zero_of_radialMoment_eq_zero` -- step 1 with `u = 1`.
* `radialMoment_mul_integral_comm` -- step 2.
* `abs_integral_mul_radial_sub_le` -- step 3.
* `integral_mul_radial_eq_mul_integral_of_harmonic` -- **the mean value property
  in kernel form**: `int u (x) k (|x - z|) dx = u z * int k (|x - z|) dx`.
* `annulusBump`, `annulusBump_pos`, `radialMoment_annulusBump_pos` and
  `integral_radial_pos` -- the explicit density, its positivity on the open
  annulus, the positivity of its radial moment, and the positivity of the mass
  of any such radial density in every dimension `d >= 1`.  Dividing the kernel
  form by that mass is the normalized mean value property.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {m : ℕ} {k : ℝ → ℝ} {a b : ℝ} {z : Vec (m + 1)}

theorem euclideanCoordLaplacian_const {d : ℕ} (c : ℝ) (x : Vec d) :
    euclideanCoordLaplacian (fun _ : Vec d => c) x = 0 :=
  euclideanCoordLaplacian_eq_zero_of_locally_const isOpen_univ (Set.mem_univ x) fun _ _ => rfl

theorem continuous_comp_euclideanNorm_sub (hk : Continuous k) (z : Vec (m + 1)) :
    Continuous fun x : Vec (m + 1) => k (euclideanNorm (x - z)) :=
  hk.comp (continuous_euclideanNorm.comp (continuous_id.sub continuous_const))

theorem hasCompactSupport_mul_radial {u : Vec (m + 1) → ℝ} (hb : 0 < b)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) (z : Vec (m + 1)) :
    HasCompactSupport fun x : Vec (m + 1) => u x * k (euclideanNorm (x - z)) := by
  refine HasCompactSupport.intro (isCompact_euclideanClosedBall z hb.le) ?_
  intro x hx
  rw [mem_euclideanClosedBall_iff_euclideanNorm_le hb.le] at hx
  rw [hkb _ (le_of_lt (lt_of_not_ge hx)), mul_zero]

theorem integrable_mul_radial {u : Vec (m + 1) → ℝ} (hu : Continuous u) (hk : Continuous k)
    (hb : 0 < b) (hkb : ∀ s : ℝ, b ≤ s → k s = 0) (z : Vec (m + 1)) :
    Integrable (fun x : Vec (m + 1) => u x * k (euclideanNorm (x - z))) volume :=
  (hu.mul (continuous_comp_euclideanNorm_sub hk z)).integrable_of_hasCompactSupport
    (hasCompactSupport_mul_radial hb hkb z)

theorem integrable_radial (hk : Continuous k) (hb : 0 < b)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) (z : Vec (m + 1)) :
    Integrable (fun x : Vec (m + 1) => k (euclideanNorm (x - z))) volume := by
  simpa using integrable_mul_radial (u := fun _ : Vec (m + 1) => (1 : ℝ))
    continuous_const hk hb hkb z

/-- **Vanishing of the Green pairing against a radial density of zero moment.** -/
theorem integral_mul_radial_eq_zero_of_radialMoment_eq_zero {u : Vec (m + 1) → ℝ}
    (hu : ContDiff ℝ (2 : ℕ) u) (hk : Continuous k) (ha : 0 < a) (hb : 0 < b)
    (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) (hkb : ∀ s : ℝ, b ≤ s → k s = 0)
    (hmom : radialMoment m k b = 0)
    (hharm : ∀ x ∈ euclideanClosedBall z b, euclideanCoordLaplacian u x = 0) :
    ∫ x, u x * k (euclideanNorm (x - z)) ∂volume = 0 := by
  have hgreen := integral_mul_euclideanCoordLaplacian_eq_zero_of_forall_mem hu
    (contDiff_radialPotential_comp (m := m) hk ha hk0 b z)
    (hasCompactSupport_radialPotential_comp (m := m) hk hb hkb hmom z)
    (tsupport_radialPotential_comp_subset (m := m) hk hb hkb hmom z) hharm
  simpa only [euclideanCoordLaplacian_radialPotential (b := b) hk ha hk0 z] using hgreen

/-- The `u = 1` case: a radial density of zero moment integrates to zero. -/
theorem integral_radial_eq_zero_of_radialMoment_eq_zero (hk : Continuous k) (ha : 0 < a)
    (hb : 0 < b) (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) (hkb : ∀ s : ℝ, b ≤ s → k s = 0)
    (hmom : radialMoment m k b = 0) (z : Vec (m + 1)) :
    ∫ x, k (euclideanNorm (x - z)) ∂volume = 0 := by
  have h := integral_mul_radial_eq_zero_of_radialMoment_eq_zero (u := fun _ : Vec (m + 1) => (1 :
    ℝ))
    contDiff_const hk ha hb hk0 hkb hmom (z := z)
    (fun x _ => euclideanCoordLaplacian_const (1 : ℝ) x)
  simpa using h

theorem radialMoment_linear {k₁ k₂ : ℝ → ℝ} (hk₁ : Continuous k₁) (hk₂ : Continuous k₂)
    (c₁ c₂ : ℝ) (t : ℝ) :
    radialMoment m (fun s => c₁ * k₁ s + c₂ * k₂ s) t =
      c₁ * radialMoment m k₁ t + c₂ * radialMoment m k₂ t := by
  have h1 : Continuous fun s : ℝ => c₁ * (s ^ m * k₁ s) :=
    continuous_const.mul ((continuous_pow m).mul hk₁)
  have h2 : Continuous fun s : ℝ => c₂ * (s ^ m * k₂ s) :=
    continuous_const.mul ((continuous_pow m).mul hk₂)
  have hrw : ∀ s : ℝ, s ^ m * (c₁ * k₁ s + c₂ * k₂ s) =
      c₁ * (s ^ m * k₁ s) + c₂ * (s ^ m * k₂ s) := by
    intro s
    ring
  simp only [radialMoment, hrw]
  rw [intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- The explicit continuous annulus bump supported in `[a, b]`. -/
noncomputable def annulusBump (a b t : ℝ) : ℝ := max 0 ((t - a) * (b - t))

theorem continuous_annulusBump (a b : ℝ) : Continuous (annulusBump a b) :=
  continuous_const.max ((continuous_id.sub continuous_const).mul
    (continuous_const.sub continuous_id))

theorem annulusBump_nonneg (a b t : ℝ) : 0 ≤ annulusBump a b t := le_max_left _ _

theorem annulusBump_eq_zero_of_le (hab : a < b) {t : ℝ} (ht : t ≤ a) :
    annulusBump a b t = 0 := by
  have hnp : (t - a) * (b - t) ≤ 0 := by nlinarith
  simp [annulusBump, max_eq_left hnp]

theorem annulusBump_eq_zero_of_ge (hab : a < b) {t : ℝ} (ht : b ≤ t) :
    annulusBump a b t = 0 := by
  have hnp : (t - a) * (b - t) ≤ 0 := by nlinarith
  simp [annulusBump, max_eq_left hnp]

theorem annulusBump_pos {t : ℝ} (h1 : a < t) (h2 : t < b) : 0 < annulusBump a b t := by
  have hp : 0 < (t - a) * (b - t) := mul_pos (by linarith) (by linarith)
  simpa [annulusBump] using hp

theorem radialMoment_annulusBump_pos (ha : 0 < a) (hab : a < b) :
    0 < radialMoment m (annulusBump a b) b := by
  have hcont : Continuous fun s : ℝ => s ^ m * annulusBump a b s :=
    (continuous_pow m).mul (continuous_annulusBump a b)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (f := fun s : ℝ => s ^ m * annulusBump a b s) (a := 0) (b := a) (c := b)
    (hcont.intervalIntegrable 0 a) (hcont.intervalIntegrable a b)
  have h1 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..a, s ^ m * annulusBump a b s := by
    refine intervalIntegral.integral_nonneg ha.le fun s hs => ?_
    exact mul_nonneg (pow_nonneg hs.1 m) (annulusBump_nonneg a b s)
  have h2 : (0 : ℝ) < ∫ s in a..b, s ^ m * annulusBump a b s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable a b) (fun s hs => ?_) hab
    exact mul_pos (pow_pos (ha.trans hs.1) m) (annulusBump_pos hs.1 hs.2)
  rw [radialMoment, ← hsplit]
  linarith

theorem euclideanNorm_smul_basisVec {d : ℕ} (c : ℝ) (i : Fin d) :
    euclideanNorm (c • basisVec i) = |c| := by
  have h : vecNormSq (c • basisVec (d := d) i) = c ^ 2 := by
    simp [vecNormSq, vecDot, sq]
  rw [euclideanNorm, h, Real.sqrt_sq_eq_abs]

theorem integral_radial_pos (hk : Continuous k) (hknn : ∀ t : ℝ, 0 ≤ k t) (hb : 0 < b)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hkt₀ : 0 < k t₀)
    (z : Vec (m + 1)) : 0 < ∫ x, k (euclideanNorm (x - z)) ∂volume := by
  rw [integral_pos_iff_support_of_nonneg (fun x => hknn _) (integrable_radial hk hb hkb z)]
  have hopen : IsOpen (Function.support fun x : Vec (m + 1) => k (euclideanNorm (x - z))) :=
    isOpen_compl_singleton.preimage (continuous_comp_euclideanNorm_sub hk z)
  refine hopen.measure_pos volume ⟨z + t₀ • basisVec 0, ?_⟩
  have hsub : (z + t₀ • basisVec (d := m + 1) 0) - z = t₀ • basisVec 0 := by
    abel
  simp only [Function.mem_support, hsub, euclideanNorm_smul_basisVec, abs_of_nonneg ht₀]
  exact ne_of_gt hkt₀

/-- **Kernel independence.**  For a function harmonic on the closed ball of radius
`b`, the pairing against a radial density is proportional to the density's radial
moment, with a proportionality factor that does not depend on the density. -/
theorem radialMoment_mul_integral_comm {u : Vec (m + 1) → ℝ} (hu : ContDiff ℝ (2 : ℕ) u)
    {k₁ k₂ : ℝ → ℝ} (hk₁ : Continuous k₁) (hk₂ : Continuous k₂)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb : 0 < b)
    (hk₁0 : ∀ s : ℝ, s ≤ a₁ → k₁ s = 0) (hk₁b : ∀ s : ℝ, b ≤ s → k₁ s = 0)
    (hk₂0 : ∀ s : ℝ, s ≤ a₂ → k₂ s = 0) (hk₂b : ∀ s : ℝ, b ≤ s → k₂ s = 0)
    (hharm : ∀ x ∈ euclideanClosedBall z b, euclideanCoordLaplacian u x = 0) :
    radialMoment m k₂ b * ∫ x, u x * k₁ (euclideanNorm (x - z)) ∂volume =
      radialMoment m k₁ b * ∫ x, u x * k₂ (euclideanNorm (x - z)) ∂volume := by
  have hkc : Continuous fun s : ℝ =>
      radialMoment m k₂ b * k₁ s + (-radialMoment m k₁ b) * k₂ s :=
    (continuous_const.mul hk₁).add (continuous_const.mul hk₂)
  have hk0 : ∀ s : ℝ, s ≤ min a₁ a₂ →
      radialMoment m k₂ b * k₁ s + (-radialMoment m k₁ b) * k₂ s = 0 := by
    intro s hs
    rw [hk₁0 s (hs.trans (min_le_left _ _)), hk₂0 s (hs.trans (min_le_right _ _))]
    ring
  have hkb : ∀ s : ℝ, b ≤ s →
      radialMoment m k₂ b * k₁ s + (-radialMoment m k₁ b) * k₂ s = 0 := by
    intro s hs
    rw [hk₁b s hs, hk₂b s hs]
    ring
  have hmom : radialMoment m
      (fun s => radialMoment m k₂ b * k₁ s + (-radialMoment m k₁ b) * k₂ s) b = 0 := by
    rw [radialMoment_linear hk₁ hk₂]
    ring
  have hzero := integral_mul_radial_eq_zero_of_radialMoment_eq_zero hu hkc
    (lt_min ha₁ ha₂) hb hk0 hkb hmom hharm
  have hi₁ := integrable_mul_radial hu.continuous hk₁ hb hk₁b z
  have hi₂ := integrable_mul_radial hu.continuous hk₂ hb hk₂b z
  have hrw : ∀ x : Vec (m + 1),
      u x * (radialMoment m k₂ b * k₁ (euclideanNorm (x - z))
          + (-radialMoment m k₁ b) * k₂ (euclideanNorm (x - z))) =
        radialMoment m k₂ b * (u x * k₁ (euclideanNorm (x - z)))
          + (-radialMoment m k₁ b) * (u x * k₂ (euclideanNorm (x - z))) := by
    intro x
    ring
  rw [show (fun x : Vec (m + 1) => u x * (radialMoment m k₂ b * k₁ (euclideanNorm (x - z))
      + (-radialMoment m k₁ b) * k₂ (euclideanNorm (x - z)))) =
      fun x : Vec (m + 1) => radialMoment m k₂ b * (u x * k₁ (euclideanNorm (x - z)))
        + (-radialMoment m k₁ b) * (u x * k₂ (euclideanNorm (x - z))) from funext hrw,
    integral_add (hi₁.const_mul _) (hi₂.const_mul _), integral_const_mul,
    integral_const_mul] at hzero
  linarith

/-- **Concentration.**  A nonnegative radial density supported in the ball of radius
`b` reproduces the value at the centre up to the oscillation of `u` on that ball. -/
theorem abs_integral_mul_radial_sub_le {u : Vec (m + 1) → ℝ} (hu : Continuous u)
    (hk : Continuous k) (hknn : ∀ t : ℝ, 0 ≤ k t) (hb : 0 < b)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) {ε : ℝ}
    (hε : ∀ x ∈ euclideanClosedBall z b, |u x - u z| ≤ ε) :
    |∫ x, u x * k (euclideanNorm (x - z)) ∂volume
        - u z * ∫ x, k (euclideanNorm (x - z)) ∂volume| ≤
      ε * ∫ x, k (euclideanNorm (x - z)) ∂volume := by
  have hi := integrable_mul_radial hu hk hb hkb z
  have hi0 := integrable_radial hk hb hkb z
  have hrw : ∫ x, u x * k (euclideanNorm (x - z)) ∂volume
      - u z * ∫ x, k (euclideanNorm (x - z)) ∂volume
      = ∫ x, (u x - u z) * k (euclideanNorm (x - z)) ∂volume := by
    rw [← integral_const_mul, ← integral_sub hi (hi0.const_mul (u z))]
    congr 1
    funext x
    ring
  have hdiff : Integrable
      (fun x : Vec (m + 1) => (u x - u z) * k (euclideanNorm (x - z))) volume := by
    rw [show (fun x : Vec (m + 1) => (u x - u z) * k (euclideanNorm (x - z))) =
        fun x : Vec (m + 1) => u x * k (euclideanNorm (x - z))
          - u z * k (euclideanNorm (x - z)) from funext fun x => by ring]
    exact hi.sub (hi0.const_mul (u z))
  have hbound : ∀ x : Vec (m + 1), |(u x - u z) * k (euclideanNorm (x - z))| ≤
      ε * k (euclideanNorm (x - z)) := by
    intro x
    rw [abs_mul, abs_of_nonneg (hknn _)]
    by_cases hx : x ∈ euclideanClosedBall z b
    · exact mul_le_mul_of_nonneg_right (hε x hx) (hknn _)
    · rw [mem_euclideanClosedBall_iff_euclideanNorm_le hb.le] at hx
      rw [hkb _ (le_of_lt (lt_of_not_ge hx))]
      simp
  rw [hrw]
  calc |∫ x, (u x - u z) * k (euclideanNorm (x - z)) ∂volume|
      ≤ ∫ x, |(u x - u z) * k (euclideanNorm (x - z))| ∂volume :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, ε * k (euclideanNorm (x - z)) ∂volume :=
        integral_mono hdiff.abs (hi0.const_mul ε) hbound
    _ = ε * ∫ x, k (euclideanNorm (x - z)) ∂volume := integral_const_mul _ _


private theorem eq_of_forall_abs_sub_le {I cc w : ℝ} (hc : 0 < cc)
    (h : ∀ ε : ℝ, 0 < ε → |I - w * cc| ≤ ε * cc) : I = w * cc := by
  have hcne : cc ≠ 0 := ne_of_gt hc
  by_contra hne
  have habs : 0 < |I - w * cc| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have h2 := h (|I - w * cc| / (2 * cc)) (by positivity)
  have heq : |I - w * cc| / (2 * cc) * cc = |I - w * cc| / 2 := by
    field_simp
  rw [heq] at h2
  linarith

/-- **The mean value property, in kernel form.**  If `u` is `C^2` with vanishing
coordinate Laplacian on the closed Euclidean ball of radius `b` about `z`, then
its pairing against any nonnegative continuous radial density supported in the
annulus `[a, b]` of positive radial moment is `u z` times the mass of the
density. -/
theorem integral_mul_radial_eq_mul_integral_of_harmonic {u : Vec (m + 1) → ℝ}
    (hu : ContDiff ℝ (2 : ℕ) u) (hk : Continuous k)
    (ha : 0 < a) (hab : a < b) (hk0 : ∀ s : ℝ, s ≤ a → k s = 0)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) (hmom : 0 < radialMoment m k b)
    (hharm : ∀ x ∈ euclideanClosedBall z b, euclideanCoordLaplacian u x = 0) :
    ∫ x, u x * k (euclideanNorm (x - z)) ∂volume =
      u z * ∫ x, k (euclideanNorm (x - z)) ∂volume := by
  have hb : 0 < b := ha.trans hab
  have hcu : Continuous u := hu.continuous
  have main : ∀ δ : ℝ, 0 < δ → δ ≤ b → ∀ ε : ℝ, 0 < ε →
      (∀ x ∈ euclideanClosedBall z δ, |u x - u z| ≤ ε) →
      |(∫ x, u x * k (euclideanNorm (x - z)) ∂volume)
          - u z * ∫ x, k (euclideanNorm (x - z)) ∂volume|
        ≤ ε * ∫ x, k (euclideanNorm (x - z)) ∂volume
      ∧ 0 < ∫ x, k (euclideanNorm (x - z)) ∂volume := by
    intro δ hδ hδb ε hε hosc
    have hδ2 : 0 < δ / 2 := by linarith
    have hδ2δ : δ / 2 < δ := by linarith
    have hgc : Continuous (annulusBump (δ / 2) δ) := continuous_annulusBump _ _
    have hgnn : ∀ t : ℝ, 0 ≤ annulusBump (δ / 2) δ t := annulusBump_nonneg _ _
    have hg0 : ∀ s : ℝ, s ≤ δ / 2 → annulusBump (δ / 2) δ s = 0 :=
      fun s hs => annulusBump_eq_zero_of_le hδ2δ hs
    have hgδ : ∀ s : ℝ, δ ≤ s → annulusBump (δ / 2) δ s = 0 :=
      fun s hs => annulusBump_eq_zero_of_ge hδ2δ hs
    have hgb : ∀ s : ℝ, b ≤ s → annulusBump (δ / 2) δ s = 0 :=
      fun s hs => hgδ s (hδb.trans hs)
    have hMg : 0 < radialMoment m (annulusBump (δ / 2) δ) b := by
      rw [radialMoment_eq_of_ge hgc hgδ hδb]
      exact radialMoment_annulusBump_pos hδ2 hδ2δ
    have hcg : 0 < ∫ x, annulusBump (δ / 2) δ (euclideanNorm (x - z)) ∂volume := by
      refine integral_radial_pos hgc hgnn hδ hgδ (t₀ := 3 * δ / 4) (by linarith)
        (annulusBump_pos (by linarith) (by linarith)) z
    have hcross := radialMoment_mul_integral_comm hu hk hgc ha hδ2 hb hk0 hkb hg0 hgb hharm
    have hcross1 := radialMoment_mul_integral_comm (u := fun _ : Vec (m + 1) => (1 : ℝ))
      contDiff_const hk hgc ha hδ2 hb hk0 hkb hg0 hgb (z := z)
      (fun x _ => euclideanCoordLaplacian_const (1 : ℝ) x)
    simp only [one_mul] at hcross1
    have hc0 : 0 < ∫ x, k (euclideanNorm (x - z)) ∂volume := by
      have hpos : 0 < radialMoment m (annulusBump (δ / 2) δ) b *
          ∫ x, k (euclideanNorm (x - z)) ∂volume := by
        rw [hcross1]
        exact mul_pos hmom hcg
      nlinarith [hpos, hMg]
    refine ⟨?_, hc0⟩
    have hconc := abs_integral_mul_radial_sub_le hcu hgc hgnn hδ hgδ hosc
    have e2 : radialMoment m (annulusBump (δ / 2) δ) b *
          ((∫ x, u x * k (euclideanNorm (x - z)) ∂volume)
            - u z * ∫ x, k (euclideanNorm (x - z)) ∂volume) =
        radialMoment m k b *
          ((∫ x, u x * annulusBump (δ / 2) δ (euclideanNorm (x - z)) ∂volume)
            - u z * ∫ x, annulusBump (δ / 2) δ (euclideanNorm (x - z)) ∂volume) := by
      linear_combination hcross - u z * hcross1
    have hkey : radialMoment m (annulusBump (δ / 2) δ) b *
        |(∫ x, u x * k (euclideanNorm (x - z)) ∂volume)
          - u z * ∫ x, k (euclideanNorm (x - z)) ∂volume|
        ≤ radialMoment m (annulusBump (δ / 2) δ) b *
          (ε * ∫ x, k (euclideanNorm (x - z)) ∂volume) := by
      rw [← abs_of_pos hMg, ← abs_mul, e2, abs_mul, abs_of_pos hmom]
      calc radialMoment m k b *
            |(∫ x, u x * annulusBump (δ / 2) δ (euclideanNorm (x - z)) ∂volume)
              - u z * ∫ x, annulusBump (δ / 2) δ (euclideanNorm (x - z)) ∂volume|
          ≤ radialMoment m k b *
              (ε * ∫ x, annulusBump (δ / 2) δ (euclideanNorm (x - z)) ∂volume) :=
            mul_le_mul_of_nonneg_left hconc hmom.le
        _ = ε * (radialMoment m k b *
              ∫ x, annulusBump (δ / 2) δ (euclideanNorm (x - z)) ∂volume) := by ring
        _ = ε * (radialMoment m (annulusBump (δ / 2) δ) b *
              ∫ x, k (euclideanNorm (x - z)) ∂volume) := by rw [hcross1]
        _ = radialMoment m (annulusBump (δ / 2) δ) b *
              (ε * ∫ x, k (euclideanNorm (x - z)) ∂volume) := by ring
        _ = |radialMoment m (annulusBump (δ / 2) δ) b| *
              (ε * ∫ x, k (euclideanNorm (x - z)) ∂volume) := by rw [abs_of_pos hMg]
    exact le_of_mul_le_mul_left hkey hMg
  have hfinal : ∀ ε : ℝ, 0 < ε →
      |(∫ x, u x * k (euclideanNorm (x - z)) ∂volume)
          - u z * ∫ x, k (euclideanNorm (x - z)) ∂volume|
        ≤ ε * ∫ x, k (euclideanNorm (x - z)) ∂volume
      ∧ 0 < ∫ x, k (euclideanNorm (x - z)) ∂volume := by
    intro ε hε
    obtain ⟨η, hη, hηlt⟩ := Metric.continuousAt_iff.mp hcu.continuousAt ε hε
    have hmin : 0 < min (η / 2) b := lt_min (by linarith) hb
    refine main (min (η / 2) b) hmin (min_le_right _ _) ε hε fun x hx => ?_
    have hx1 : x ∈ Metric.closedBall z (min (η / 2) b) :=
      euclideanClosedBall_subset_metricClosedBall hmin.le hx
    have hle : dist x z ≤ min (η / 2) b := Metric.mem_closedBall.mp hx1
    have hmin2 : min (η / 2) b ≤ η / 2 := min_le_left _ _
    have hd : dist x z < η := by linarith
    have := hηlt hd
    rw [Real.dist_eq] at this
    exact this.le
  exact eq_of_forall_abs_sub_le (hfinal 1 one_pos).2 fun ε hε => (hfinal ε hε).1


end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
