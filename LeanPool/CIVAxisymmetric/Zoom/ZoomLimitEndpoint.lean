/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.ZoomLimitComparisonVanishing
public import LeanPool.CIVAxisymmetric.Zoom.RecedingCompactnessMovingCentre
public import LeanPool.CIVAxisymmetric.Zoom.PassToLimit

/-!
# The endpoint vanishing of the rescaled vorticities along the zoom sequence

The endpoint vanishing in Steps 2 and 3 of the proof of
`prop:aniso:small`: once the rescaled scalar (the potential vorticity `Ω_n` in the finite-axis
case, the azimuthal vorticity `Θ_n` in the receding-axis case) converges locally uniformly up to
`τ = -1`, and its limit solves the limit equation (`eq:aniso:zoom:finite:limit`, respectively
`eq:aniso:zoom:receding:limit:a`) with an admissible drift, the limit inherits the decay bound
of `eq:aniso:zoom:finite:bound` (respectively `eq:aniso:zoom:receding:bound`) because
`δ_n → 0`, the comparison principle `lem:aniso:comparison` makes it vanish, and hence the
rescaled scalars tend to zero at every point of `{τ = -1}` (off the axis in the finite-axis
case). The zoom centres move with `n`, as in `eq:aniso:zoom:finite:variables` and
`eq:aniso:zoom:receding:variables`.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- A fixed point of the zoomed variables with `τ < 0` is eventually mapped into the unit
cylinder by the finite-axis zoom about the moving axis points `(0, zc n)`, `|zc n| ≤ ρ < 1`. -/
theorem eventually_zoomPoint_mem_unitCylinder_moving {h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ) {lam : ℕ → ℝ}
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) (p : (ℝ × ℝ) × ℝ) (hp : p.2 < 0) :
    ∀ᶠ n in atTop, zoomPoint (lam n) h (zc n) p ∈ unitCylinder := by
  have hcz : ∀ n, (0 : ℝ) ^ 2 + zc n ^ 2 ≤ ρ ^ 2 := fun n => by
    have := sq_le_sq' (abs_le.mp (hzc n)).1 (abs_le.mp (hzc n)).2
    simpa using this
  have hall := eventually_mem_zoomPointRec_moving hh hρ0 hρ1 (by norm_num : (-1 : ℝ) < 0) hcz
    hlam_lim {p} isCompact_singleton (fun q hq => by rw [mem_singleton_iff.mp hq]; exact hp)
  filter_upwards [hall] with n hn
  have hq := hn p rfl
  have heq : zoomPointRec (lam n) h 0 (zc n) p = zoomPoint (lam n) h (zc n) p := by
    unfold zoomPointRec zoomPoint; rw [zero_add]
  rw [heq] at hq
  exact ⟨hq.1, hq.2⟩

/-- `δ_n² = (λ_n^{2h})² → 0` along a zoom sequence `λ_n → 0⁺`. -/
theorem tendsto_zoomDeltaSq_seq {h : ℝ} (hh : 0 < h) {lam : ℕ → ℝ}
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0))) :
    Tendsto (fun n => (lam n ^ (2 * h)) ^ 2) atTop (nhds 0) :=
  (tendsto_zoomDeltaSq_nhdsWithin_zero hh).comp hlam_lim

/-- The decay bound of the finite-axis limit, inherited from `eq:aniso:zoom:finite:bound`
since `δ_n → 0`: at a point with `τ < 0`, a limit of `Ω_n` along the zoom sequence is bounded by
`C |τ|^{-3/2-h}`. -/
theorem abs_le_of_tendsto_zoomOmega {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ) {lam : ℕ → ℝ} (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    {p : (ℝ × ℝ) × ℝ} (hp : p.2 < 0) {L : ℝ}
    (hL : Tendsto (fun n => zoomOmega (lam n) h (zc n) u p) atTop (nhds L)) :
    |L| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) - h) := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hbd : Tendsto (fun n => C * ((lam n ^ (2 * h)) ^ 2 * (-p.2) ^ (-(3 / 2 : ℝ) + h)
      + (-p.2) ^ (-(3 / 2 : ℝ) - h))) atTop
      (nhds (C * (0 * (-p.2) ^ (-(3 / 2 : ℝ) + h) + (-p.2) ^ (-(3 / 2 : ℝ) - h)))) :=
    ((tendsto_zoomDeltaSq_seq hh.1 hlam_lim).mul_const _ |>.add_const _).const_mul C
  rw [zero_mul, zero_add] at hbd
  refine le_of_tendsto_of_tendsto hL.abs hbd ?_
  filter_upwards [eventually_zoomPoint_mem_unitCylinder_moving hh hρ0 hρ1 hzc hlam_lim p hp]
    with n hn
  exact abs_zoomOmega_le_of_mem (hlam_pos n) hb hu2 haxi hn

/-- The decay bound of the receding-axis limit, inherited from
`eq:aniso:zoom:receding:bound` since `δ_n → 0`. -/
theorem abs_le_of_tendsto_zoomTheta {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) {lam : ℕ → ℝ}
    (hlam_pos : ∀ n, 0 < lam n) (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    {p : (ℝ × ℝ) × ℝ} (hp : p.2 < 0) {L : ℝ}
    (hL : Tendsto (fun n => zoomTheta (lam n) h (rc n) (zc n) u p) atTop (nhds L)) :
    |L| ≤ C * (-p.2) ^ (-1 - h) := by
  have hu2 : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder := hu.of_le (by simp)
  have hbd : Tendsto (fun n => C * ((lam n ^ (2 * h)) ^ 2 * (-p.2) ^ (-1 + h)
      + (-p.2) ^ (-1 - h))) atTop
      (nhds (C * (0 * (-p.2) ^ (-1 + h) + (-p.2) ^ (-1 - h)))) :=
    ((tendsto_zoomDeltaSq_seq hh.1 hlam_lim).mul_const _ |>.add_const _).const_mul C
  rw [zero_mul, zero_add] at hbd
  refine le_of_tendsto_of_tendsto hL.abs hbd ?_
  have hall := eventually_mem_zoomPointRec_moving hh hρ0 hρ1 (by norm_num : (-1 : ℝ) < 0) hcz
    hlam_lim {p} isCompact_singleton (fun q hq => by rw [mem_singleton_iff.mp hq]; exact hp)
  filter_upwards [hall] with n hn
  have hq := hn p rfl
  exact abs_zoomTheta_le C h (lam n) (rc n) (zc n) (hlam_pos n) u hb hu2 p ⟨hq.1, hq.2⟩

/-- The finite-axis endpoint vanishing along the zoom sequence: if the rescaled potential
vorticities at the moving axis points converge locally uniformly on `{R > 0, τ ≤ -1}` to a
limit `Ω` whose lift solves `eq:aniso:zoom:finite:limit` with an admissible drift, then
`Ω_n(·, -1)` tends to zero at every point off the axis. -/
theorem tendsto_zoomOmega_endpoint_of_limit {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ) {lam : ℕ → ℝ} (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (Ω : (ℝ × ℝ) × ℝ → ℝ) (hΩc : ContinuousOn Ω {p | 0 < p.1.1 ∧ p.2 ≤ -1})
    (hconv : ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K → K ⊆ {p | 0 < p.1.1 ∧ p.2 ≤ -1} →
      TendstoUniformlyOn (fun n => zoomOmega (lam n) h (zc n) u) Ω atTop K)
    (B : Vec 5 × ℝ → Vec 5) (divB : Vec 5 × ℝ → ℝ)
    (hB : IsAdmissibleDrift 5 (Iio (-1)) B divB)
    (heq : IsDistributionalDriftDiffusion 5 4 (Iio (-1)) B divB
      (fun z => Ω (zoomLiftPoint z))) :
    ∀ q : ℝ × ℝ, 0 < q.1 →
      Tendsto (fun n => zoomOmega (lam n) h (zc n) u (q, -1)) atTop (nhds 0) := by
  have hpt : ∀ p : (ℝ × ℝ) × ℝ, 0 < p.1.1 → p.2 ≤ -1 →
      Tendsto (fun n => zoomOmega (lam n) h (zc n) u p) atTop (nhds (Ω p)) := by
    intro p hp1 hp2
    have hK := hconv {p} isCompact_singleton
      (fun x hx => by rw [mem_singleton_iff.mp hx]; exact ⟨hp1, hp2⟩)
    exact hK.tendsto_at (mem_singleton p)
  have hΩb : ∀ p : (ℝ × ℝ) × ℝ, 0 < p.1.1 → p.2 ≤ -1 →
      |Ω p| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) - h) := fun p hp1 hp2 =>
    abs_le_of_tendsto_zoomOmega hh hρ0 hρ1 hb hu haxi hzc hlam_pos hlam_lim
      (by linarith only [hp2]) (hpt p hp1 hp2)
  have hzero := zoomOmegaLimit_endpoint_eq_zero hh.1 Ω hΩc hΩb B divB hB heq
  intro q hq
  have := hpt (q, -1) hq le_rfl
  rwa [hzero q hq] at this

/-- The receding-axis endpoint vanishing along the zoom sequence: if the rescaled azimuthal
vorticities at the moving centres converge locally uniformly on `ℝ² × (-∞, -1]` to a limit `Θ`
solving `eq:aniso:zoom:receding:limit:a` with an admissible drift, then `Θ_n(·, -1)` tends to
zero at every point. -/
theorem tendsto_zoomTheta_endpoint_of_limit {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {rc zc : ℕ → ℝ} (hcz : ∀ n, rc n ^ 2 + zc n ^ 2 ≤ ρ ^ 2) {lam : ℕ → ℝ}
    (hlam_pos : ∀ n, 0 < lam n) (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (Θ : (ℝ × ℝ) × ℝ → ℝ) (hΘc : ContinuousOn Θ {p | p.2 ≤ -1})
    (hconv : ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K → K ⊆ {p | p.2 ≤ -1} →
      TendstoUniformlyOn (fun n => zoomTheta (lam n) h (rc n) (zc n) u) Θ atTop K)
    (B : Vec 2 × ℝ → Vec 2) (divB : Vec 2 × ℝ → ℝ)
    (hB : IsAdmissibleDrift 2 (Iio (-1)) B divB)
    (heq : IsDistributionalDriftDiffusion 2 1 (Iio (-1)) B divB
      (fun z => Θ (planeLiftPoint z))) :
    ∀ q : ℝ × ℝ,
      Tendsto (fun n => zoomTheta (lam n) h (rc n) (zc n) u (q, -1)) atTop (nhds 0) := by
  have hpt : ∀ p : (ℝ × ℝ) × ℝ, p.2 ≤ -1 →
      Tendsto (fun n => zoomTheta (lam n) h (rc n) (zc n) u p) atTop (nhds (Θ p)) := by
    intro p hp
    have hK := hconv {p} isCompact_singleton
      (fun x hx => by rw [mem_singleton_iff.mp hx]; exact hp)
    exact hK.tendsto_at (mem_singleton p)
  have hΘb : ∀ p : (ℝ × ℝ) × ℝ, p.2 ≤ -1 → |Θ p| ≤ C * (-p.2) ^ (-1 - h) := fun p hp =>
    abs_le_of_tendsto_zoomTheta hh hρ0 hρ1 hb hu hcz hlam_pos hlam_lim
      (by linarith only [hp]) (hpt p hp)
  have hzero := zoomThetaLimit_endpoint_eq_zero hh.1 Θ hΘc hΘb B divB hB heq
  intro q
  have := hpt (q, -1) le_rfl
  rwa [hzero q] at this

/-- `F2-Q`: the lifted limit of the rescaled potential vorticities is locally bounded on
`ℝ⁵ × (-∞, -1)`, with the decay of `eq:aniso:zoom:finite:bound` inherited from `δ_n → 0`. -/
theorem isLocallyBoundedOn_zoomOmegaLimit {C h ρ : ℝ} (hh : 0 < h ∧ h < 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    {zc : ℕ → ℝ} (hzc : ∀ n, |zc n| ≤ ρ) {lam : ℕ → ℝ} (hlam_pos : ∀ n, 0 < lam n)
    (hlam_lim : Tendsto lam atTop (nhdsWithin 0 (Ioi 0)))
    (Ω : (ℝ × ℝ) × ℝ → ℝ) (hΩc : ContinuousOn Ω {p | 0 < p.1.1 ∧ p.2 ≤ -1})
    (hconv : ∀ K : Set ((ℝ × ℝ) × ℝ), IsCompact K → K ⊆ {p | 0 < p.1.1 ∧ p.2 ≤ -1} →
      TendstoUniformlyOn (fun n => zoomOmega (lam n) h (zc n) u) Ω atTop K) :
    IsLocallyBoundedOn 5 (Iio (-1)) (fun z => Ω (zoomLiftPoint z)) := by
  refine isLocallyBoundedOn_zoomLift (C := C) hh.1 Ω hΩc (fun p hp1 hp2 => ?_)
  have hK := hconv {p} isCompact_singleton
    (fun x hx => by rw [mem_singleton_iff.mp hx]; exact ⟨hp1, hp2⟩)
  exact abs_le_of_tendsto_zoomOmega hh hρ0 hρ1 hb hu haxi hzc hlam_pos hlam_lim
    (by linarith only [hp2]) (hK.tendsto_at (mem_singleton p))

/-- Uniform convergence on a set of finite measure gives convergence of the integral of the
distance, in `ℝ≥0∞`. -/
theorem tendsto_setLIntegral_enorm_sub_of_tendstoUniformlyOn {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : Set X} (hKm : MeasurableSet K) (hKf : μ K ≠ ⊤)
    {F : ℕ → X → ℝ} {g : X → ℝ} (hF : TendstoUniformlyOn F g atTop K) :
    Tendsto (fun n => ∫⁻ x in K, ‖F n x - g x‖ₑ ∂μ) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne (μ K) 0 with h0 | h0
  · refine Eventually.of_forall fun n => ?_
    rw [Measure.restrict_eq_zero.mpr h0, lintegral_zero_measure]
    exact zero_le
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hKf hε.ne'
  have hu := Metric.tendstoUniformlyOn_iff.mp hF (δ : ℝ) (by exact_mod_cast hδ)
  filter_upwards [hu] with n hn
  calc ∫⁻ x in K, ‖F n x - g x‖ₑ ∂μ ≤ ∫⁻ _ in K, (δ : ℝ≥0∞) ∂μ := by
        refine setLIntegral_mono' hKm fun x hx => ?_
        have h1 := hn x hx
        rw [dist_comm, Real.dist_eq] at h1
        rw [← ofReal_norm, Real.norm_eq_abs]
        exact le_trans (ENNReal.ofReal_le_ofReal h1.le) (by simp)
    _ = (δ : ℝ≥0∞) * μ K := by rw [setLIntegral_const]
    _ ≤ ε := hδε.le

/-- `R2-L1`: locally uniform convergence on `Vec m × (-∞, T]` gives `L¹` convergence on every
compact subset of `Vec m × (-∞, T)`. -/
theorem tendsto_lintegral_of_tendstoUniformlyOn {m : ℕ} {T : ℝ}
    (qn : ℕ → Vec m × ℝ → ℝ) (q : Vec m × ℝ → ℝ)
    (hconv : ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iic T →
      TendstoUniformlyOn qn q atTop K) :
    ∀ K : Set (Vec m × ℝ), IsCompact K → K ⊆ univ ×ˢ Iio T →
      Tendsto (fun n => ∫⁻ z in K, ‖qn n z - q z‖ₑ) atTop (nhds 0) := by
  intro K hK hKs
  exact tendsto_setLIntegral_enorm_sub_of_tendstoUniformlyOn hK.measurableSet
    hK.measure_lt_top.ne
    (hconv K hK (hKs.trans (prod_mono subset_rfl Iio_subset_Iic_self)))

end CIV
