/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisBounds
public import LeanPool.CIVAxisymmetric.Zoom.FiniteLift
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Passing the finite-axis zoom sequence to its limit

Elementary limit lemmas for `eq:aniso:zoom:finite:limit`, the equation obeyed by the locally
uniform limit `Ω_∞` of the rescaled potential vorticities `Ω_n` of `eq:aniso:zoom:fields`, along a
sequence of zoom scales `λ_n → 0⁺`:

* `λ_n → 0⁺` forces `δ_n = λ_n^{2h} → 0` and, for any sequence uniformly bounded by `M`,
  `δ_n² · (\text{that sequence}) → 0` — the mechanism removing `δ_n² ∂_{ZZ} Ω_n` from the
  equation (`tendsto_zoomDeltaSq_nhdsWithin_zero`, `tendsto_zoomDeltaSq_mul_of_bounded`).
* the force term `G_n` of `eq:interior:force:scaled` tends to zero *uniformly in the point*
  along every scale sequence (`eventually_forall_abs_zoomForce_lt`), transporting the scale limit
  `tendsto_zoomForce_bound_nhdsWithin_zero` of `CIV.Zoom.FiniteLift` along an arbitrary
  `λ_n → 0⁺`.
* the algebraic divergence identity `div_{X,Z} B_n = 2 V_n / R` of `CIV.Zoom.FiniteAxisBounds`
  (`zoomDriftDivergence_eq`) holds for every finite `n`, so it passes to the limit once `V_n / R`
  does (`tendsto_zoomDriftDivergence_of_tendsto_zoomV_div`): this is the
  "`With div_{X,Z} B = 2 V / R`" clause of `eq:aniso:zoom:finite:limit`.
* the products `B_n Ω_n` and `(V_n/R) Ω_n` pass to the limit under an integral against a fixed
  test function by dominated convergence, given almost-everywhere convergence of the pointwise
  product and a uniform domination (`tendsto_integral_mul_of_ae_tendsto`).

The limit equation itself, `CIV.IsDistributionalDriftDiffusion 5 4 (Set.Iio (-1)) B divB Ω_∞`
with an admissible drift, is `CIV.exists_admissibleDrift_zoomOmegaLimit`.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### `δ_n → 0` removes the `δ_n² ∂_{ZZ} Ω_n` term -/

/-- `δ = λ^{2h} → 0` as the zoom scale `λ → 0⁺`, for any positive anisotropy exponent `h`. -/
theorem tendsto_zoomDelta_nhdsWithin_zero {h : ℝ} (hh : 0 < h) :
    Tendsto (fun lam : ℝ => lam ^ (2 * h)) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  Tendsto.rpow_const_nhds_zero
    (continuous_id.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (by linarith only [hh])

/-- `δ² = (λ^{2h})² → 0` as `λ → 0⁺`. -/
theorem tendsto_zoomDeltaSq_nhdsWithin_zero {h : ℝ} (hh : 0 < h) :
    Tendsto (fun lam : ℝ => (lam ^ (2 * h)) ^ 2) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  simpa using (tendsto_zoomDelta_nhdsWithin_zero hh).pow 2

/-- `δ_n² · D_n → 0` whenever `D_n` is uniformly bounded and `λ_n → 0⁺`: the mechanism that
removes `δ_n² ∂_{ZZ} Ω_n` from `eq:aniso:zoom:finite:equation` in the limit, given the uniform
bound on `∂_{ZZ} Ω_n` as an explicit hypothesis. -/
theorem tendsto_zoomDeltaSq_mul_of_bounded {h M : ℝ} (hh : 0 < h) {D : ℝ → ℝ}
    (hD : ∀ lam, |D lam| ≤ M) :
    Tendsto (fun lam : ℝ => (lam ^ (2 * h)) ^ 2 * D lam) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hg : Tendsto (fun lam : ℝ => (lam ^ (2 * h)) ^ 2 * M) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (tendsto_zoomDeltaSq_nhdsWithin_zero hh).mul_const M
  refine squeeze_zero_norm (fun lam => ?_) hg
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hD lam) (sq_nonneg _)

/-! ### The force term `G_n → 0` uniformly along a scale sequence -/

/-- The force term `G_n = zoomForce` of `eq:interior:force:scaled` tends to zero *uniformly in
the point* along every scale sequence `λ_n → 0⁺`: composing the scale limit
`tendsto_zoomForce_bound_nhdsWithin_zero` of `CIV.Zoom.FiniteLift` along `λ_n` with the
uniform-in-the-point bound `abs_zoomForce_le` (reproved directly from
`abs_potentialVorticity_force_le` so the same bounding constant is used at every `n`). This is
the "`G_n → 0` uniformly" clause of `eq:aniso:zoom:finite:limit`. -/
theorem eventually_forall_abs_zoomForce_lt (h : ℝ) (hh0 : 0 ≤ h) {lamSeq zcSeq : ℕ → ℝ}
    (hlam : Tendsto lamSeq atTop (nhdsWithin 0 (Ioi 0)))
    {f : ParabolicPoint → Vec3}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder) (hMf : ForceC2Bounded f)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p : (ℝ × ℝ) × ℝ,
      zoomPoint (lamSeq n) h (zcSeq n) p ∈ unitCylinder →
      |zoomForce (lamSeq n) h (zcSeq n) f p| < ε := by
  obtain ⟨C, hC, hCbound⟩ := abs_potentialVorticity_force_le hf hfaxi hMf
  have hpos : ∀ᶠ n in atTop, 0 < lamSeq n := hlam.eventually self_mem_nhdsWithin
  have hbig : Tendsto (fun n => C * (lamSeq n ^ 5 * lamSeq n ^ (2 * h))) atTop (nhds 0) :=
    (tendsto_zoomForce_bound_nhdsWithin_zero (C := C) hh0).comp hlam
  have hsmall : ∀ᶠ n in atTop, C * (lamSeq n ^ 5 * lamSeq n ^ (2 * h)) < ε :=
    (tendsto_order.mp hbig).2 ε hε
  filter_upwards [hpos, hsmall] with n hnpos hnsmall p hp
  have hpv : |potentialVorticity f (zoomPoint (lamSeq n) h (zcSeq n) p)| ≤ C := hCbound _ _ _ hp
  have hnn : (0 : ℝ) ≤ lamSeq n ^ 5 * lamSeq n ^ (2 * h) := by positivity
  calc |zoomForce (lamSeq n) h (zcSeq n) f p|
      = lamSeq n ^ 5 * lamSeq n ^ (2 * h)
          * |potentialVorticity f (zoomPoint (lamSeq n) h (zcSeq n) p)| := by
        rw [zoomForce, abs_mul, abs_of_nonneg hnn]
    _ ≤ lamSeq n ^ 5 * lamSeq n ^ (2 * h) * C := mul_le_mul_of_nonneg_left hpv hnn
    _ = C * (lamSeq n ^ 5 * lamSeq n ^ (2 * h)) := by ring
    _ < ε := hnsmall

/-! ### `div_{X,Z} B = 2 V / R` passes to the limit -/

/-- The exact algebraic identity `zoomDriftDivergence_eq` of `CIV.Zoom.FiniteAxisBounds`,
`div_{X,Z} B_n = 2 V_n / R`, holds at every finite `n`, so it passes to the limit outright as
soon as `V_n / R` converges: the "`With div_{X,Z} B = 2 V / R`" clause of
`eq:aniso:zoom:finite:limit`, conditioned only on the convergence of `V_n / R`. -/
theorem tendsto_zoomDriftDivergence_of_tendsto_zoomV_div (h : ℝ) {lamSeq zcSeq : ℕ → ℝ}
    (hlam : ∀ n, 0 < lamSeq n) (u : ParabolicPoint → Vec3) (pr : ParabolicPoint → ℝ)
    (fo : ParabolicPoint → Vec3) (hsol : IsClassicalSolutionOn u pr fo unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ} (hR : 0 < zoomLiftRadius q.1)
    (hp : ∀ n, zoomPoint (lamSeq n) h (zcSeq n) (zoomLiftPoint q) ∈ unitCylinder) {L : ℝ}
    (hL : Tendsto (fun n => zoomV (lamSeq n) h (zcSeq n) u (zoomLiftPoint q) / zoomLiftRadius q.1)
      atTop (nhds L)) :
    Tendsto (fun n => zoomDriftDivergence (lamSeq n) h (zcSeq n) u q) atTop (nhds (2 * L)) := by
  have heq : ∀ n, zoomDriftDivergence (lamSeq n) h (zcSeq n) u q
      = 2 * (zoomV (lamSeq n) h (zcSeq n) u (zoomLiftPoint q) / zoomLiftRadius q.1) :=
    fun n => zoomDriftDivergence_eq (lamSeq n) h (zcSeq n) (hlam n) u pr fo hsol haxi (hp n) hR
  exact Tendsto.congr (fun n => (heq n).symm) (Tendsto.const_mul (2 : ℝ) hL)

/-! ### Passing a product of two convergent sequences to the limit under an integral -/

/-- The elementary bound behind "passing the products `B_n Ω_n` to the limit": a product of two
sequences bounded pointwise by `CΩ`, `CB` is bounded, against any third factor, by `CΩ CB` times
that factor's absolute value. -/
private theorem abs_mul_mul_le {A B φ CΩ CB : ℝ} (hA : |A| ≤ CΩ) (hB : |B| ≤ CB) :
    |A * B * φ| ≤ CΩ * CB * |φ| := by
  have hCΩnn : (0 : ℝ) ≤ CΩ := (abs_nonneg A).trans hA
  have hAB : |A| * |B| ≤ CΩ * CB := mul_le_mul hA hB (abs_nonneg B) hCΩnn
  calc |A * B * φ| = |A| * |B| * |φ| := by rw [abs_mul, abs_mul]
    _ ≤ CΩ * CB * |φ| := mul_le_mul_of_nonneg_right hAB (abs_nonneg φ)

/-- The pointwise mechanism of "passing the products `B_n Ω_n` and `(V_n/R) Ω_n` to the limit":
if two sequences converge at a point, so does their product against a fixed third factor. -/
theorem tendsto_mul_mul_of_tendsto {Ω B : ℕ → Vec 5 × ℝ → ℝ} {Ωlim Blim φ : Vec 5 × ℝ → ℝ}
    {z : Vec 5 × ℝ} (hΩ : Tendsto (fun n => Ω n z) atTop (nhds (Ωlim z)))
    (hB : Tendsto (fun n => B n z) atTop (nhds (Blim z))) :
    Tendsto (fun n => Ω n z * B n z * φ z) atTop (nhds (Ωlim z * Blim z * φ z)) :=
  (hΩ.mul hB).mul_const (φ z)

/-- Passing the product `Ω_n B_n` to the limit inside a fixed integral against `φ`, by the
Lebesgue dominated convergence theorem: given almost-everywhere convergence of the pointwise
product and a uniform domination by `M |φ|`, the paired integrals converge. This is the
integral-level mechanism of "the weak-* convergence of `B_n` against the strong convergence of
`Ω_n` … passes the products `B_n Ω_n` and `(V_n/R) Ω_n` to the limit" of
`eq:aniso:zoom:finite:limit`. -/
theorem tendsto_integral_mul_of_ae_tendsto {Ω B : ℕ → Vec 5 × ℝ → ℝ} {Ωlim Blim φ : Vec 5 × ℝ → ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (fun z => Ω n z * B n z * φ z) volume)
    {M : ℝ} (hφ : Integrable φ volume)
    (hbound : ∀ n, ∀ᵐ z ∂volume, |Ω n z * B n z * φ z| ≤ M * |φ z|)
    (hlim : ∀ᵐ z ∂volume,
      Tendsto (fun n => Ω n z * B n z * φ z) atTop (nhds (Ωlim z * Blim z * φ z))) :
    Tendsto (fun n => ∫ z, Ω n z * B n z * φ z) atTop (nhds (∫ z, Ωlim z * Blim z * φ z)) := by
  refine tendsto_integral_of_dominated_convergence (fun z => M * |φ z|) hmeas
    (hφ.abs.const_mul M) (fun n => ?_) hlim
  filter_upwards [hbound n] with z hz
  simpa [Real.norm_eq_abs] using hz

end CIV
