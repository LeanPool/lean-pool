/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusChartC2Transfer

/-!
# The placed spectral witness `f_n = U_n f_*` of `lem:global-riesz-nonzero`

The proof of `lem:global-riesz-nonzero`.  The local seed supplies
a unit vector `f_*` of `L²(ℝ²; ℂ²)` vanishing almost everywhere off the disc `D(0, L_*)` with
`Re⟨P_δ f_*, f_*⟩ > 1/2`.  (The paper's `prop:local-seed` takes `f_* ∈ C_c^∞(ℝ²; ℂ²)`; this
module uses, and assumes, only `L²` membership, the unit norm and the support bound.)  Since
`L_* ≤ R_v`, the core containment `eq:local-support-in-buffer` gives
`eq:scaled-witness-support`

`L_* ℓ_n < R_n / 5`

for every `n ≥ 0`, with no further enlargement of `K_0`
(`FastDynamo.GlobalParameterChoice.witnessSupport`), so the rescaled witness `U_n f_*` is
supported inside the plateau `closedBall(p_n, R_n/5)` of the input cut-off `φ_n` — a fortiori inside
the plateau `closedBall(p_n, R_n/3)` of the output cut-off `ψ_n`, and
inside the half-buffer `closedBall(p_n, R_n/2)` which the no-wrap hypothesis places in the fixed
chart.

This module regards `f_n = U_n f_*` as a torus field by the chart transport `extendStateC2` of
`FastDynamo/Global/TorusChartC2Transfer.lean` and proves, exactly (not approximately):

* `extendStateC2_coe_ae` — the almost-everywhere representative of the chart transport
  (multiplication by `ψ_n`, evaluation at the canonical chart representative); on the placed
  witness the output cut-off is one on the support;
* `inputMul_stateMul_placedWitness` and `outputMul_stateMul_placedWitness` — `φ_n f_n = f_n` and
  `ψ_n f_n = f_n`;
* `restrictInputC2_placedWitness` — `φ_n`-restriction back to the plane returns `U_n f_*`;
* `norm_placedWitness` — `‖f_n‖₂ = ‖f_*‖₂`;
* `inner_placedWitness_extendStateC2` — the transfer of the inner product
  `⟨f_n, ψ_n G⟩_{T²} = ⟨U_n f_*, G⟩_{ℝ²}` used by `eq:selected-contour-identity`.

Everything is stated for a general radius `rho` of the witness support with `rho ≤ R/5`, so that
`eq:scaled-witness-support` enters exactly once, as the numerical hypothesis
`Lstar * ell ≤ R / 5` (non-strict; the paper's `eq:scaled-witness-support` is strict).  The
parameter chain discharges it from `R_v ≥ L_*`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Metric Set

namespace TorusSelectedWitness

open ParametrixExplicitCutoff
open TorusChartC2Transfer
open TorusChartL2
open TorusPlacedCutoffC2
open TransverseSmoothBumpPeriodization
open WholePlaneHorizontalFibre

/-! ## Whole-plane fields vanishing off a disc -/

/-- An `L²` class on the plane vanishes almost everywhere outside the closed disc `closedBall(p,
ρ)`. -/
def VanishesOutsideDisk (p : WholePlane) (rho : ℝ) (g : WholePlaneC2L2) : Prop :=
  ∀ᵐ x ∂volume, rho < dist x p → (g : WholePlane → C2) x = 0

/-! ## The rescaled and the placed witness -/

/-- The rescaled witness `U_n f_* = ℓ_n⁻¹ f_*((· - p_n)/ℓ_n)` on the plane. -/
def scaledWitness (p : WholePlane) (ell : ℝ) (hell : 0 < ell) (fstar : WholePlaneC2L2) :
    WholePlaneC2L2 :=
  wholePlaneRescaleLinearIsometryEquiv C2 p ell hell fstar

/-- The rescaling is an isometry, so the rescaled witness keeps the seed's norm. -/
@[simp] theorem norm_scaledWitness (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (fstar : WholePlaneC2L2) : ‖scaledWitness p ell hell fstar‖ = ‖fstar‖ :=
  (wholePlaneRescaleLinearIsometryEquiv C2 p ell hell).norm_map fstar

/-- Undoing the rescaling returns the seed witness. -/
theorem rescale_symm_scaledWitness (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (fstar : WholePlaneC2L2) :
    (wholePlaneRescaleLinearIsometryEquiv C2 p ell hell).symm
        (scaledWitness p ell hell fstar) = fstar :=
  (wholePlaneRescaleLinearIsometryEquiv C2 p ell hell).symm_apply_apply fstar

/-- **The support of the rescaled witness** (cf. `eq:scaled-witness-support`):
a seed supported in `closedBall(0, L_*)` rescales to a field supported in `closedBall(p_n, L_*
ℓ_n)`. -/
theorem vanishesOutsideDisk_scaledWitness (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (fstar : WholePlaneC2L2) {Lstar : ℝ}
    (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0) :
    VanishesOutsideDisk p (Lstar * ell) (scaledWitness p ell hell fstar) := by
  have hsmul : ∀ᵐ y ∂(ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)),
      Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0 :=
    Measure.ae_smul_measure hsupp (ENNReal.ofReal (ell ^ 2))
  have hpull := (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae hsmul
  filter_upwards [wholePlaneRescale_coe_ae C2 p ell hell fstar, hpull] with y hy hzero hdist
  have hnorm : ‖wholePlaneAffine p ell y‖ = ell⁻¹ * dist y p := by
    rw [wholePlaneAffine, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hell),
      dist_eq_norm]
  have hlt : Lstar < ‖wholePlaneAffine p ell y‖ := by
    rw [hnorm]
    rw [lt_inv_mul_iff₀ hell]
    linarith [hdist]
  change (scaledWitness p ell hell fstar : WholePlane → C2) y = 0
  rw [show (scaledWitness p ell hell fstar : WholePlane → C2) y =
      (wholePlaneRescale C2 p ell hell fstar : WholePlane → C2) y from rfl, hy, hzero hlt,
    smul_zero]

/-- **The placed witness `f_n`**: the rescaled witness regarded as a torus field by restriction
to the fixed chart and extension by zero (proof of `lem:global-riesz-nonzero`). -/
def placedWitness (p : WholePlane) (R : ℝ) (hR : 0 < R) (ell : ℝ) (hell : 0 < ell)
    (fstar : WholePlaneC2L2) : TransverseC2L2 :=
  extendStateC2 p R hR (scaledWitness p ell hell fstar)

/-! ## The chart transport of the placed witness -/

/-- A.e. representative of the two-component output chart transport: multiply by the output
cut-off `ψ_n` and evaluate at the canonical chart representative. -/
theorem extendStateC2_coe_ae (p : WholePlane) (R : ℝ) (hR : 0 < R) (G : WholePlaneC2L2) :
    (extendStateC2 p R hR G : TransverseTorus → C2) =ᵐ[transverseMeasure]
      fun q ↦ outputCutoffComplex p R hR (torusWholePlaneRepresentative q) •
        (G : WholePlane → C2) (torusWholePlaneRepresentative q) := by
  have hze : ((wholePlaneVerticalZeroExtendL2 G : WholePlaneC3L2) : WholePlane → C3)
      =ᵐ[volume.restrict wholePlaneFundamentalBox]
        fun x ↦ verticalZeroExtendPoint ((G : WholePlane → C2) x) :=
    (wholePlaneVerticalZeroExtendL2_coe_ae G).filter_mono (ae_mono Measure.restrict_le_self)
  have hpull :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp hze
  have hpull' : (fun q ↦ ((wholePlaneVerticalZeroExtendL2 G : WholePlaneC3L2) : WholePlane → C3)
        (torusWholePlaneRepresentative q)) =ᵐ[transverseMeasure]
      fun q ↦ verticalZeroExtendPoint
        ((G : WholePlane → C2) (torusWholePlaneRepresentative q)) := by
    simpa [Function.comp_def] using hpull
  filter_upwards [horizontalProjL2_coe_ae (wholePlaneOutputLocalizationL2 p R hR
      (wholePlaneVerticalZeroExtendL2 G)),
    wholePlaneOutputLocalizationL2_coe_ae p R hR (wholePlaneVerticalZeroExtendL2 G),
    hpull'] with q h1 h2 h3
  have h1' : ((extendStateC2 p R hR G : TransverseC2L2) : TransverseTorus → C2) q =
      horizontalProjPoint (((wholePlaneOutputLocalizationL2 p R hR
        (wholePlaneVerticalZeroExtendL2 G) : TransverseC3L2) : TransverseTorus → C3) q) := h1
  rw [h1', h2, h3, map_smul, horizontalProjPoint_verticalZeroExtendPoint]

/-- Disc-support statements transport to the canonical chart representative. -/
theorem vanishes_at_representative {p : WholePlane} {rho : ℝ} {g : WholePlaneC2L2}
    (h : VanishesOutsideDisk p rho g) :
    ∀ᵐ q ∂transverseMeasure, rho < dist (torusWholePlaneRepresentative q) p →
      (g : WholePlane → C2) (torusWholePlaneRepresentative q) = 0 :=
  measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae
    (h.filter_mono (ae_mono Measure.restrict_le_self))

/-- **The zero extension of a chart-transported field.**  Pushing `ψ_n G` to the torus and back
to the plane by zero extension multiplies by the indicator of the fixed chart. -/
theorem torusToWholePlane_verticalZeroExtend_extendStateC2
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (G : WholePlaneC2L2) :
    ((torusToWholePlaneL2 (verticalZeroExtendL2 (extendStateC2 p R hR G)) : WholePlaneC3L2) :
        WholePlane → C3) =ᵐ[volume]
      wholePlaneFundamentalBox.indicator
        (fun y ↦ verticalZeroExtendPoint
          (outputCutoffComplex p R hR y • (G : WholePlane → C2) y)) := by
  have hcomb : ((verticalZeroExtendL2 (extendStateC2 p R hR G) : TransverseC3L2) :
        TransverseTorus → C3) =ᵐ[transverseMeasure]
      fun q ↦ verticalZeroExtendPoint
        (outputCutoffComplex p R hR (torusWholePlaneRepresentative q) •
          (G : WholePlane → C2) (torusWholePlaneRepresentative q)) := by
    filter_upwards [verticalZeroExtendL2_coe_ae (extendStateC2 p R hR G),
      extendStateC2_coe_ae p R hR G] with q ha hb
    rw [ha, hb]
  have hind : wholePlaneFundamentalBox.indicator
        (fun y ↦ ((verticalZeroExtendL2 (extendStateC2 p R hR G) : TransverseC3L2) :
          TransverseTorus → C3) (wholePlaneTorusPoint y)) =ᵐ[volume]
      wholePlaneFundamentalBox.indicator
        (fun y ↦ verticalZeroExtendPoint
          (outputCutoffComplex p R hR
              (torusWholePlaneRepresentative (wholePlaneTorusPoint y)) •
            (G : WholePlane → C2)
              (torusWholePlaneRepresentative (wholePlaneTorusPoint y)))) :=
    (ae_eq_restrict_iff_indicator_ae_eq measurableSet_wholePlaneFundamentalBox).1
      (by
        simpa [Function.comp_def] using
          measurePreserving_wholePlaneTorusPoint.quasiMeasurePreserving.ae_eq_comp hcomb)
  filter_upwards [torusToWholePlaneL2_coe_ae (verticalZeroExtendL2 (extendStateC2 p R hR G)),
    hind] with x h1 h2
  rw [h1, h2]
  by_cases hx : x ∈ wholePlaneFundamentalBox
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      torusWholePlaneRepresentative_wholePlaneTorusPoint hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-! ## The exact identities on a disc-supported field -/

/-- The whole-plane axial zero extension preserves inner products. -/
theorem inner_wholePlaneVerticalZeroExtendL2 (f g : WholePlaneC2L2) :
    (inner ℂ (wholePlaneVerticalZeroExtendL2 f) (wholePlaneVerticalZeroExtendL2 g) : ℂ) =
      inner ℂ f g := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [wholePlaneVerticalZeroExtendL2_coe_ae f,
    wholePlaneVerticalZeroExtendL2_coe_ae g] with x hf hg
  rw [hf, hg]
  exact inner_verticalZeroExtendPoint _ _

/-- The whole-plane axial zero extension is injective. -/
theorem wholePlaneVerticalZeroExtendL2_injective :
    Function.Injective (wholePlaneVerticalZeroExtendL2) := by
  intro f g h
  have := congrArg wholePlaneHorizontalProjL2 h
  rwa [wholePlaneHorizontalProjL2_wholePlaneVerticalZeroExtendL2,
    wholePlaneHorizontalProjL2_wholePlaneVerticalZeroExtendL2] at this

/-- **The chart round trip on a disc-supported field**: pushing `g` to the torus through
`ψ_n` and back by zero extension returns `g` itself, because `ψ_n = 1` on `closedBall(p_n, ρ)` and
that
disc lies inside the fixed chart. -/
theorem torusToWholePlane_verticalZeroExtend_extendStateC2_of_support
    (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    {rho : ℝ} (hrho : rho ≤ R / 3) {g : WholePlaneC2L2} (hsupp : VanishesOutsideDisk p rho g) :
    torusToWholePlaneL2 (verticalZeroExtendL2 (extendStateC2 p R hR g)) =
      wholePlaneVerticalZeroExtendL2 g := by
  have hbox' : closedBall p (R / 2) ⊆ wholePlaneFundamentalBox := hbox
  apply Lp.ext
  filter_upwards [torusToWholePlane_verticalZeroExtend_extendStateC2 p R hR g,
    wholePlaneVerticalZeroExtendL2_coe_ae g, hsupp] with x h1 h2 h3
  rw [h1, h2]
  by_cases hd : dist x p ≤ rho
  · have hxb : x ∈ wholePlaneFundamentalBox :=
      hbox' (Metric.mem_closedBall.mpr (by linarith))
    rw [Set.indicator_of_mem hxb, outputCutoffComplex,
      outputCutoff_eq_one_of_dist_le p R hR (le_trans hd hrho)]
    simp
  · have hzero : (g : WholePlane → C2) x = 0 := h3 (lt_of_not_ge hd)
    by_cases hxb : x ∈ wholePlaneFundamentalBox
    · rw [Set.indicator_of_mem hxb, hzero, smul_zero, map_zero]
    · rw [Set.indicator_of_notMem hxb, hzero, map_zero]

/-- `‖ψ_n g‖₂ = ‖g‖₂` for a field supported in the plateau of `ψ_n` inside the chart. -/
theorem norm_extendStateC2_of_support (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    {rho : ℝ} (hrho : rho ≤ R / 3) {g : WholePlaneC2L2} (hsupp : VanishesOutsideDisk p rho g) :
    ‖extendStateC2 p R hR g‖ = ‖g‖ := by
  have hA := torusToWholePlane_verticalZeroExtend_extendStateC2_of_support p R hR hbox hrho hsupp
  calc ‖extendStateC2 p R hR g‖
      = ‖verticalZeroExtendL2 (extendStateC2 p R hR g)‖ :=
        (norm_verticalZeroExtendL2 _).symm
    _ = ‖torusToWholePlaneL2 (verticalZeroExtendL2 (extendStateC2 p R hR g))‖ :=
        (torusToWholePlaneL2.norm_map _).symm
    _ = ‖wholePlaneVerticalZeroExtendL2 g‖ := by rw [hA]
    _ = ‖g‖ := norm_wholePlaneVerticalZeroExtendL2 g

/-- **`⟨ψ_n G, f_n⟩ = ⟨G, g⟩`** (proof of `lem:global-riesz-nonzero`): the chart transport is
inner-product preserving
against a field supported in the plateau of `ψ_n`. -/
theorem inner_extendStateC2_of_support (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    {rho : ℝ} (hrho : rho ≤ R / 3) {g : WholePlaneC2L2} (hsupp : VanishesOutsideDisk p rho g)
    (G : WholePlaneC2L2) :
    (inner ℂ (extendStateC2 p R hR g) (extendStateC2 p R hR G) : ℂ) = inner ℂ g G := by
  have hbox' : closedBall p (R / 2) ⊆ wholePlaneFundamentalBox := hbox
  have hA := torusToWholePlane_verticalZeroExtend_extendStateC2_of_support p R hR hbox hrho hsupp
  have e4 : (inner ℂ (wholePlaneVerticalZeroExtendL2 g)
        (torusToWholePlaneL2 (verticalZeroExtendL2 (extendStateC2 p R hR G))) : ℂ) =
      inner ℂ (wholePlaneVerticalZeroExtendL2 g) (wholePlaneVerticalZeroExtendL2 G) := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [wholePlaneVerticalZeroExtendL2_coe_ae g,
      wholePlaneVerticalZeroExtendL2_coe_ae G,
      torusToWholePlane_verticalZeroExtend_extendStateC2 p R hR G, hsupp] with x hg hG hZ hs
    rw [hg, hG, hZ]
    by_cases hd : dist x p ≤ rho
    · have hxb : x ∈ wholePlaneFundamentalBox :=
        hbox' (Metric.mem_closedBall.mpr (by linarith))
      rw [Set.indicator_of_mem hxb, outputCutoffComplex,
        outputCutoff_eq_one_of_dist_le p R hR (le_trans hd hrho)]
      simp
    · rw [hs (lt_of_not_ge hd)]
      simp
  calc (inner ℂ (extendStateC2 p R hR g) (extendStateC2 p R hR G) : ℂ)
      = inner ℂ (verticalZeroExtendL2 (extendStateC2 p R hR g))
          (verticalZeroExtendL2 (extendStateC2 p R hR G)) :=
        (inner_verticalZeroExtendL2 _ _).symm
    _ = inner ℂ (torusToWholePlaneL2 (verticalZeroExtendL2 (extendStateC2 p R hR g)))
          (torusToWholePlaneL2 (verticalZeroExtendL2 (extendStateC2 p R hR G))) :=
        (torusToWholePlaneL2.inner_map_map _ _).symm
    _ = inner ℂ (wholePlaneVerticalZeroExtendL2 g)
          (torusToWholePlaneL2 (verticalZeroExtendL2 (extendStateC2 p R hR G))) := by rw [hA]
    _ = inner ℂ (wholePlaneVerticalZeroExtendL2 g) (wholePlaneVerticalZeroExtendL2 G) := e4
    _ = inner ℂ g G := inner_wholePlaneVerticalZeroExtendL2 g G

/-- **`φ_n f_n = f_n`** (proof of `lem:global-riesz-nonzero`): the input cut-off is one on the
plateau containing the
support of the transported field. -/
theorem inputMul_stateMul_extendStateC2_of_support (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    {rho : ℝ} (hrho : rho ≤ R / 5) {g : WholePlaneC2L2} (hsupp : VanishesOutsideDisk p rho g) :
    (inputMul p R hR).stateMul (extendStateC2 p R hR g) = extendStateC2 p R hR g := by
  apply Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae (E := C2) transverseMeasure (inputMul p R hR).value
      (extendStateC2 p R hR g),
    inputMul_value_ae p R hR hbox, extendStateC2_coe_ae p R hR g,
    vanishes_at_representative hsupp] with q h1 h2 h3 h4
  have h1' : (((inputMul p R hR).stateMul (extendStateC2 p R hR g) : TransverseC2L2) :
        TransverseTorus → C2) q =
      ((inputMul p R hR).value : TransverseTorus → ℂ) q •
        ((extendStateC2 p R hR g : TransverseC2L2) : TransverseTorus → C2) q := h1
  rw [h1', h2, h3, ← torusWholePlaneRepresentative_eq_iocRepresentative q]
  by_cases hd : dist (torusWholePlaneRepresentative q) p ≤ rho
  · rw [inputCutoff_eq_one_of_dist_le p R hR (le_trans hd hrho)]
    simp
  · rw [h4 (lt_of_not_ge hd)]
    simp

/-- **`ψ_n f_n = f_n`** (proof of `lem:global-riesz-nonzero`): the output cut-off is one on the
plateau containing the
support of the transported field. -/
theorem outputMul_stateMul_extendStateC2_of_support (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    {rho : ℝ} (hrho : rho ≤ R / 3) {g : WholePlaneC2L2} (hsupp : VanishesOutsideDisk p rho g) :
    (outputMul p R hR).stateMul (extendStateC2 p R hR g) = extendStateC2 p R hR g := by
  apply Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae (E := C2) transverseMeasure (outputMul p R hR).value
      (extendStateC2 p R hR g),
    outputMul_value_ae p R hR hbox, extendStateC2_coe_ae p R hR g,
    vanishes_at_representative hsupp] with q h1 h2 h3 h4
  have h1' : (((outputMul p R hR).stateMul (extendStateC2 p R hR g) : TransverseC2L2) :
        TransverseTorus → C2) q =
      ((outputMul p R hR).value : TransverseTorus → ℂ) q •
        ((extendStateC2 p R hR g : TransverseC2L2) : TransverseTorus → C2) q := h1
  rw [h1', h2, h3, ← torusWholePlaneRepresentative_eq_iocRepresentative q]
  by_cases hd : dist (torusWholePlaneRepresentative q) p ≤ rho
  · rw [outputCutoff_eq_one_of_dist_le p R hR (le_trans hd hrho)]
    simp
  · rw [h4 (lt_of_not_ge hd)]
    simp

/-- **The chart round trip of `eq:selected-contour-identity`**: restricting the transported field
through `φ_n` returns the original disc-supported plane field. -/
theorem restrictInputC2_extendStateC2_of_support (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
    {rho : ℝ} (hrho : rho ≤ R / 5) {g : WholePlaneC2L2} (hsupp : VanishesOutsideDisk p rho g) :
    restrictInputC2 p R hR (extendStateC2 p R hR g) = g := by
  have hA := torusToWholePlane_verticalZeroExtend_extendStateC2_of_support p R hR hbox
    (le_trans hrho (by linarith)) hsupp
  refine wholePlaneVerticalZeroExtendL2_injective ?_
  refine (wholePlaneVerticalZeroExtendL2_restrictInputC2 p R hR _).trans ?_
  have hstep : torusInputLocalizationL2 p R hR
        (verticalZeroExtendL2 (extendStateC2 p R hR g)) =
      inputCutoffMulL2 p R hR (wholePlaneVerticalZeroExtendL2 g) := by
    change inputCutoffMulL2 p R hR
      (torusToWholePlaneL2 (verticalZeroExtendL2 (extendStateC2 p R hR g))) = _
    rw [hA]
  rw [hstep]
  apply Lp.ext
  filter_upwards [inputCutoffMulL2_coe_ae p R hR (wholePlaneVerticalZeroExtendL2 g),
    wholePlaneVerticalZeroExtendL2_coe_ae g, hsupp] with x h1 h2 h3
  rw [h1, h2]
  by_cases hd : dist x p ≤ rho
  · rw [inputCutoffComplex, inputCutoff_eq_one_of_dist_le p R hR (le_trans hd hrho)]
    simp
  · rw [h3 (lt_of_not_ge hd), map_zero, smul_zero]

/-! ## The placed witness of `lem:global-riesz-nonzero` -/

section PlacedWitness

variable (p : WholePlane) (R : ℝ) (hR : 0 < R) (ell : ℝ) (hell : 0 < ell)
  (fstar : WholePlaneC2L2)

variable {Lstar : ℝ}
  (hsupp : ∀ᵐ y ∂volume, Lstar < ‖y‖ → (fstar : WholePlane → C2) y = 0)
  (hbox : closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox)
  (hfit : Lstar * ell ≤ R / 5)

include hsupp hbox hfit in
/-- **`‖f_n‖₂ = ‖f_*‖₂`** (proof of `lem:global-riesz-nonzero`): the chart transport and the
rescaling are isometries on
the disc-supported witness. -/
theorem norm_placedWitness : ‖placedWitness p R hR ell hell fstar‖ = ‖fstar‖ := by
  have hsupp' := vanishesOutsideDisk_scaledWitness p ell hell fstar hsupp
  calc ‖placedWitness p R hR ell hell fstar‖
      = ‖scaledWitness p ell hell fstar‖ :=
        norm_extendStateC2_of_support p R hR hbox (le_trans hfit (by linarith)) hsupp'
    _ = ‖fstar‖ := norm_scaledWitness p ell hell fstar

include hsupp hbox hfit in
/-- **`φ_n f_n = f_n`** (proof of `lem:global-riesz-nonzero`). -/
theorem inputMul_stateMul_placedWitness :
    (inputMul p R hR).stateMul (placedWitness p R hR ell hell fstar) =
      placedWitness p R hR ell hell fstar :=
  inputMul_stateMul_extendStateC2_of_support p R hR hbox hfit
    (vanishesOutsideDisk_scaledWitness p ell hell fstar hsupp)

include hsupp hbox hfit in
/-- **`ψ_n f_n = f_n`** (proof of `lem:global-riesz-nonzero`). -/
theorem outputMul_stateMul_placedWitness :
    (outputMul p R hR).stateMul (placedWitness p R hR ell hell fstar) =
      placedWitness p R hR ell hell fstar :=
  outputMul_stateMul_extendStateC2_of_support p R hR hbox (le_trans hfit (by linarith))
    (vanishesOutsideDisk_scaledWitness p ell hell fstar hsupp)

include hsupp hbox hfit in
/-- **`φ_n`-restriction of `f_n` is `U_n f_*`**: the chart round trip of
`eq:selected-contour-identity`. -/
theorem restrictInputC2_placedWitness :
    restrictInputC2 p R hR (placedWitness p R hR ell hell fstar) =
      scaledWitness p ell hell fstar :=
  restrictInputC2_extendStateC2_of_support p R hR hbox hfit
    (vanishesOutsideDisk_scaledWitness p ell hell fstar hsupp)

include hsupp hbox hfit in
/-- **`⟨f_n, ψ_n G⟩ = ⟨U_n f_*, G⟩`** (proof of `lem:global-riesz-nonzero`): the inner product
against the placed
witness only sees the plane field. -/
theorem inner_placedWitness_extendStateC2 (G : WholePlaneC2L2) :
    (inner ℂ (placedWitness p R hR ell hell fstar) (extendStateC2 p R hR G) : ℂ) =
      inner ℂ (scaledWitness p ell hell fstar) G :=
  inner_extendStateC2_of_support p R hR hbox (le_trans hfit (by linarith))
    (vanishesOutsideDisk_scaledWitness p ell hell fstar hsupp) G

end PlacedWitness

end TorusSelectedWitness

end

end FastDynamo
