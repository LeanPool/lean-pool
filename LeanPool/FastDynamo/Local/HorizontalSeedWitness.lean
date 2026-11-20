/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.HorizontalModeContour

/-!
# The compactly supported spectral witness `f_*` of `prop:local-seed`

The proof of `prop:local-seed` in the paper: *"We choose a unit vector `x ∈ Ran P⁰`.  Since
`P⁰x = x`, density gives a unit function `f_* ∈ C_c^∞(ℝ²; ℂ²)` such that
`re ⟨P⁰f_*, f_*⟩ > 3/4`.  We choose `L_* > 0` with `supp f_* ⊂ D(0, L_*)`."*

This module produces exactly that witness for the unperturbed projection
`P⁰ = (HorizontalMode.modeIsolation hd).projection` of `Local/HorizontalModeContour.lean`.

Two points about the formalised statement.

* **The truncation is an `L²` element, not a `C_c^∞` function.**  The paper smooths as
  well as truncates; the global layer (`eq:local-spectral-witness` and everything that consumes
  it) uses only `f_* ∈ L²`, `‖f_*‖₂ = 1`, `f_* = 0` a.e. off `D(0, L_*)` and
  `re⟨P_δ f_*, f_*⟩ > 1/2`.  The witness built here is the indicator truncation
  `f_L = 1_{D(0,L)}x` of the normalised eigenvector, renormalised; smoothing it further would
  change nothing downstream, so it is not done.
* **`‖f_L - x‖₂ → 0` is the generic `L²` dominated-convergence statement**
  (`tendsto_wholePlaneC2ExteriorCutoff_apply_zero`), not the quantitative exponential tail
  `integral_sq_norm_horizontalModeField_tail_le` of the mode.  The exponential tail gives an
  explicit `L_*`; the qualitative statement gives an unspecified one, which is all that
  `eq:local-spectral-witness` asks for.

## Contents

* The disc truncation `1_{D(0,L)}` on `L²(ℝ²; ℂ²)`, its support, and `1_{D(0,L)}f → f`.
* `exists_diskSupported_witness`: for any bounded `P` fixing a unit vector `x` and any `c < 1`
  there are `L_* ≥ 1` and a unit `f_*` vanishing a.e. off `D(0, L_*)` with
  `c < re⟨P f_*, f_*⟩`.
* `HorizontalMode.exists_horizontalSeedWitness`: the same at `P⁰` and `x = b/‖b‖`, with the
  paper's threshold `c = 3/4`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open PonomarenkoFreeOmegaInterface

/-! ## The disc truncation on `L²(ℝ²; ℂ²)` -/

/-- The closed disc `D(0, L)` of the whole plane. -/
def wholePlaneDisk (L : ℝ) : Set WholePlane :=
  Metric.closedBall (0 : WholePlane) L

/-- A point lies in `D(0, L)` exactly when its norm is at most `L`. -/
@[simp] theorem mem_wholePlaneDisk_iff (L : ℝ) (y : WholePlane) :
    y ∈ wholePlaneDisk L ↔ ‖y‖ ≤ L := by
  simp [wholePlaneDisk, Metric.mem_closedBall]

/-- Discs are measurable. -/
theorem measurableSet_wholePlaneDisk (L : ℝ) : MeasurableSet (wholePlaneDisk L) :=
  measurableSet_closedBall

/-- The disc is the complement of the exterior region of the same radius. -/
theorem wholePlaneExterior_eq_compl (L : ℝ) :
    wholePlaneExterior L = (wholePlaneDisk L)ᶜ := rfl

/-- Multiplication by the indicator of `D(0, L)` on `L²(ℝ²; ℂ²)`: the spatial truncation
`f ↦ 1_{D(0,L)}f` behind the paper's `supp f_* ⊂ D(0, L_*)`.

It is *not* the paper's "Restricting to `L²` gives the resolvents of `𝓛_{h,δ}` on `Γ`"
(proof of `prop:local-seed`): that sentence restricts the inverses of the sesquilinear pencil
`𝔸_{h,δ}(z)` from `V^* → V` to `L²`, an operator-theoretic restriction with no spatial
cut-off in it, and it is formalised in `FastDynamo/Local/HorizontalDeltaResolvent.lean`. -/
def wholePlaneC2DiskCutoff (L : ℝ) : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2 :=
  l2MeasurableSetRestriction volume (wholePlaneDisk L) (measurableSet_wholePlaneDisk L)

/-- Representative formula for the disc truncation. -/
theorem wholePlaneC2DiskCutoff_coe_ae (L : ℝ) (f : WholePlaneC2L2) :
    (wholePlaneC2DiskCutoff L f : WholePlane → C2) =ᵐ[volume]
      (wholePlaneDisk L).indicator (fun y => (f : WholePlane → C2) y) :=
  l2MeasurableSetRestriction_coe_ae volume _ _ f

/-- **The support statement.**  The disc truncation vanishes almost everywhere off `D(0, L)`. -/
theorem wholePlaneC2DiskCutoff_ae_eq_zero (L : ℝ) (f : WholePlaneC2L2) :
    ∀ᵐ y ∂(volume : Measure WholePlane), L < ‖y‖ →
      (wholePlaneC2DiskCutoff L f : WholePlane → C2) y = 0 := by
  filter_upwards [wholePlaneC2DiskCutoff_coe_ae L f] with y hy hyL
  have hnot : y ∉ wholePlaneDisk L := by
    simp only [mem_wholePlaneDisk_iff]
    exact not_le.2 hyL
  rw [hy, Set.indicator_of_notMem hnot]

/-- The disc truncation and the exterior cutoff of the same radius add up to the identity. -/
theorem wholePlaneC2DiskCutoff_add_exteriorCutoff (L : ℝ) (f : WholePlaneC2L2) :
    wholePlaneC2DiskCutoff L f + wholePlaneC2ExteriorCutoff L f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (wholePlaneC2DiskCutoff L f) (wholePlaneC2ExteriorCutoff L f),
    wholePlaneC2DiskCutoff_coe_ae L f,
    wholePlaneExteriorCutoff_coe_ae (E := C2) L f] with y hadd hdisk hext
  rw [hadd, Pi.add_apply, hdisk, hext]
  by_cases hy : y ∈ wholePlaneDisk L
  · rw [Set.indicator_of_mem hy,
      Set.indicator_of_notMem (by rw [wholePlaneExterior_eq_compl]; simpa using hy), add_zero]
  · rw [Set.indicator_of_notMem hy,
      Set.indicator_of_mem (by rw [wholePlaneExterior_eq_compl]; exact hy), zero_add]

/-- **`1_{D(0,L)}f → f` in `L²` as `L → ∞`.**  This is the density step of the proof of
`prop:local-seed`, *"density gives a unit function `f_* ∈ C_c^∞(ℝ²; ℂ²)`"*, with an indicator
truncation in place of a `C_c^∞` approximation. -/
theorem tendsto_wholePlaneC2DiskCutoff (f : WholePlaneC2L2) :
    Tendsto (fun L : ℝ => wholePlaneC2DiskCutoff L f) atTop (𝓝 f) := by
  have hzero := tendsto_wholePlaneC2ExteriorCutoff_apply_zero f
  have hsub : Tendsto (fun L : ℝ => f - wholePlaneC2ExteriorCutoff L f) atTop (𝓝 (f - 0)) :=
    tendsto_const_nhds.sub hzero
  rw [sub_zero] at hsub
  exact hsub.congr fun L => (eq_sub_of_add_eq (wholePlaneC2DiskCutoff_add_exteriorCutoff L f)).symm

/-! ## The abstract witness -/

/-- The Rayleigh functional `y ↦ ‖y‖⁻²·re⟨P y, y⟩` of a bounded operator `P`. -/
def rayleighRe (P : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2) (y : WholePlaneC2L2) : ℝ :=
  ‖y‖⁻¹ ^ 2 * (inner ℂ (P y) y).re

/-- The Rayleigh functional is unchanged by normalisation. -/
theorem rayleighRe_eq_re_inner_normalized (P : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2)
    (g : WholePlaneC2L2) :
    (inner ℂ (P (((‖g‖⁻¹ : ℝ) : ℂ) • g)) (((‖g‖⁻¹ : ℝ) : ℂ) • g)).re = rayleighRe P g := by
  rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_mul]
  simp only [rayleighRe, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  rw [← pow_two]

/-- At a unit fixed vector of `P` the Rayleigh functional equals one. -/
theorem rayleighRe_of_norm_one (P : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2)
    {x : WholePlaneC2L2} (hx : ‖x‖ = 1) (hPx : P x = x) : rayleighRe P x = 1 := by
  have hinner : (inner ℂ x x : ℂ) = ((‖x‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K x
  rw [rayleighRe, hPx, hinner, hx]
  norm_num

/-- The Rayleigh functional is continuous away from the origin. -/
theorem continuousAt_rayleighRe (P : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2)
    {x : WholePlaneC2L2} (hx : x ≠ 0) : ContinuousAt (rayleighRe P) x := by
  have hnorm : ContinuousAt (fun y : WholePlaneC2L2 => ‖y‖⁻¹ ^ 2) x :=
    ((continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.2 hx)).pow 2
  have hinner : ContinuousAt (fun y : WholePlaneC2L2 => (inner ℂ (P y) y).re) x := by
    refine (Complex.continuous_re.comp ?_).continuousAt
    exact continuous_inner.comp (P.continuous.prodMk continuous_id)
  exact hnorm.mul hinner

/--
**The compactly supported spectral witness.**  If a bounded operator `P` on `L²(ℝ²; ℂ²)` fixes a
unit vector `x` then, for every threshold `c < 1`, there are a radius `L_* ≥ 1` and a unit field
`f_*` vanishing almost everywhere off `D(0, L_*)` with `c < re⟨P f_*, f_*⟩`.

This is the choice of `f_*` in the proof of `prop:local-seed`, with the paper's
`c = 3/4`.
-/
theorem exists_diskSupported_witness (P : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2)
    {x : WholePlaneC2L2} (hx : ‖x‖ = 1) (hPx : P x = x) {c : ℝ} (hc : c < 1) :
    ∃ (Lstar : ℝ) (f : WholePlaneC2L2), 1 ≤ Lstar ∧ ‖f‖ = 1 ∧
      (∀ᵐ y ∂(volume : Measure WholePlane), Lstar < ‖y‖ →
        (f : WholePlane → C2) y = 0) ∧
      c < (inner ℂ (P f) f).re := by
  have hxne : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact zero_ne_one hx
  have hcut := tendsto_wholePlaneC2DiskCutoff x
  have hray : Tendsto (fun L : ℝ => rayleighRe P (wholePlaneC2DiskCutoff L x)) atTop
      (𝓝 (rayleighRe P x)) := (continuousAt_rayleighRe P hxne).tendsto.comp hcut
  rw [rayleighRe_of_norm_one P hx hPx] at hray
  have hnorm : Tendsto (fun L : ℝ => ‖wholePlaneC2DiskCutoff L x‖) atTop (𝓝 1) := by
    have h := hcut.norm
    rwa [hx] at h
  have hpos : ∀ᶠ L : ℝ in atTop, 0 < ‖wholePlaneC2DiskCutoff L x‖ :=
    hnorm (lt_mem_nhds one_pos)
  have hne : ∀ᶠ L : ℝ in atTop, wholePlaneC2DiskCutoff L x ≠ 0 := by
    filter_upwards [hpos] with L hL hzero
    rw [hzero, norm_zero] at hL
    exact lt_irrefl (0 : ℝ) hL
  have hgt : ∀ᶠ L : ℝ in atTop, c < rayleighRe P (wholePlaneC2DiskCutoff L x) :=
    hray (lt_mem_nhds hc)
  obtain ⟨L, hL1, hLne, hLc⟩ := ((eventually_ge_atTop (1 : ℝ)).and (hne.and hgt)).exists
  set g : WholePlaneC2L2 := wholePlaneC2DiskCutoff L x with hg
  have hgnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.2 hLne
  refine ⟨L, ((‖g‖⁻¹ : ℝ) : ℂ) • g, hL1, ?_, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ hgnorm]
  · filter_upwards [Lp.coeFn_smul (((‖g‖⁻¹ : ℝ) : ℂ)) g,
      wholePlaneC2DiskCutoff_ae_eq_zero L x] with y hy hzero hyL
    rw [hy, Pi.smul_apply, hzero hyL, smul_zero]
  · rw [rayleighRe_eq_re_inner_normalized P g]
    exact hLc

/-! ## The witness of the horizontal seed -/

namespace HorizontalMode

/--
**The seed witness.**  At the certified interface data of the horizontal mode, the unperturbed
Riesz projection `P⁰ = (modeIsolation hd).projection` admits a unit `L²` field `f_*` supported
in a disc `D(0, L_*)` with `re⟨P⁰ f_*, f_*⟩ > 3/4`.

This is the choice of `f_*` in the proof of `prop:local-seed`.  The unit vector of the
paper is `x = b/‖b‖` with `b` the eigenmode of `lem:jump-horizontal-mode`; `P⁰x = x`
because `P⁰b = b` (`modeIsolation_spec`).
-/
theorem exists_horizontalSeedWitness {N Omega : ℝ} {kappa : ℂ}
    (hd : CertifiedInterfaceData N Omega kappa) (hweak : HorizontalModeWeakIdentity hd) :
    ∃ (Lstar : ℝ) (f : WholePlaneC2L2), 1 ≤ Lstar ∧ ‖f‖ = 1 ∧
      (∀ᵐ y ∂(volume : Measure WholePlane), Lstar < ‖y‖ →
        (f : WholePlane → C2) y = 0) ∧
      3 / 4 < (inner ℂ ((modeIsolation hd).projection f) f).re := by
  obtain ⟨-, -, hproj, -, -⟩ := modeIsolation_spec hd hweak
  set b : WholePlaneC2L2 := wholePlaneH1Embedding C2 (horizontalMode hd) with hb
  have hbne : b ≠ 0 := wholePlaneH1Embedding_horizontalMode_ne_zero hd
  have hbnorm : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hbne
  refine exists_diskSupported_witness (modeIsolation hd).projection
    (x := ((‖b‖⁻¹ : ℝ) : ℂ) • b) ?_ ?_ (by norm_num)
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ hbnorm]
  · rw [map_smul, hproj]

end HorizontalMode

end

end FastDynamo
