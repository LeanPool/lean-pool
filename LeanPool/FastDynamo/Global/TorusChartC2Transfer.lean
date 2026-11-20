/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.WholePlaneHorizontalFibre
public import LeanPool.FastDynamo.Global.TorusSupportedH2Output
public import LeanPool.FastDynamo.Global.TorusPlacedCutoffC2

/-!
# The two-component chart transports between a torus cell and the whole plane

§7.1 of the paper builds the selected summand of `eq:Rapp` by extending `φ_n f` by zero from the
fixed chart to `ℝ²`, applying the resolvent on `ℝ²` for the selected cell, and restricting the
product with `ψ_n` back to the torus.  The library contains that chart calculus at the
**three**-component fibre (`Global/TorusChartL2Operators.lean`, `Global/TorusChartH2Transfer.lean`,
`Global/TorusSupportedH2Output.lean`).  The paper's proof works at `ℂ²`.

Rather than repeating that calculus at `ℂ²`, the three-component transports are
**conjugated** with the isometric zero extension `ι_⊥ : ℂ² ↪ ℂ³`
(`Global/HorizontalTransportSkewness.lean` on the torus, `Global/WholePlaneHorizontalFibre.lean`
on the plane) and the horizontal projection `π_⊥ : ℂ³ ↠ ℂ²`
(`Operator/HorizontalSector.lean` and `Global/WholePlaneHorizontalFibre.lean`).
This is legitimate because every chart map is a
scalar multiplier composed with measure-preserving substitutions, hence acts **diagonally in the
fibre**; the key lemma making the conjugation exact is
`wholePlaneVerticalZeroExtendL2_restrictInputC2`, which says that the three-component input
transport of a zero-extended torus field is the zero extension of the two-component transport.

The module supplies the four items the `SelectedLocalResolventData` interface of
`Global/TorusTwoSummandParametrix.lean` asks for: the three transports, the embedding
intertwining `ι_{H²} ∘ extendDomain = extendState ∘ ι_{H²}`, the round trip
`extendState ∘ restrictInput = φ_n·` (`eq:parametrix-cutoff-identities`, at the
chart level), and the two norm bounds.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Set

namespace TorusChartC2Transfer

open ParametrixCutoffs
open ParametrixExplicitCutoff
open TorusChartL2
open TorusPlacedCutoffC2
open TorusSupportedH2Output
open TransverseSmoothBumpPeriodization
open WholePlaneHorizontalFibre

variable (p : WholePlane) (R : ℝ) (hR : 0 < R)

/-! ## Pointwise fibre bounds on the transverse torus -/

/-- The transverse horizontal projection is an `L²` contraction. -/
theorem norm_horizontalProjL2_apply_le (f : TransverseC3L2) :
    ‖horizontalProjL2 f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_ae (Lp.aestronglyMeasurable _) ?_)
  filter_upwards [horizontalProjL2_coe_ae f] with x hx
  rw [hx]
  exact norm_horizontalProjPoint_le _

/-- The transverse axial zero extension is an `L²` isometry. -/
theorem norm_verticalZeroExtendL2 (f : TransverseC2L2) :
    ‖verticalZeroExtendL2 f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [verticalZeroExtendL2_coe_ae f] with x hx
  rw [hx, norm_verticalZeroExtendPoint]

/-! ## The three transports -/

/-- `restrictInput` of `SelectedLocalResolventData`: multiply a two-component torus field by the
input cut-off `φ_n`, pull it back through the chart and extend it by zero to `ℝ²`.  It is the
three-component transport `torusInputLocalizationL2` conjugated with the fibre maps. -/
def restrictInputC2 : TransverseC2L2 →L[ℂ] WholePlaneC2L2 :=
  wholePlaneHorizontalProjL2.comp
    ((torusInputLocalizationL2 p R hR).comp verticalZeroExtendL2)

/-- `extendState` of `SelectedLocalResolventData`: multiply a two-component whole-plane field by
the output cut-off `ψ_n` and restrict it to the torus through the chart. -/
def extendStateC2 : WholePlaneC2L2 →L[ℂ] TransverseC2L2 :=
  horizontalProjL2.comp
    ((wholePlaneOutputLocalizationL2 p R hR).comp wholePlaneVerticalZeroExtendL2)

/-- `extendDomain` of `SelectedLocalResolventData`: the same output localization at `H²`
regularity.  The hypothesis is the no-wrap condition of `eq:chart-packing`: the
closed half-buffer disc does not wrap around the transverse torus. -/
def extendDomainC2 (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneFundamentalBox) :
    WholePlaneC2H2 →L[ℂ] TransverseC2H2 :=
  horizontalProjH2.comp
    ((wholePlaneOutputLocalizationH2 p R hR hbox).comp wholePlaneVerticalZeroExtendH2)

/-- Unfolded value of the two-component output transport on states. -/
theorem extendStateC2_apply (g : WholePlaneC2L2) :
    extendStateC2 p R hR g =
      horizontalProjL2
        (wholePlaneOutputLocalizationL2 p R hR (wholePlaneVerticalZeroExtendL2 g)) :=
  rfl

/-- Unfolded value of the two-component output transport on the domain. -/
theorem extendDomainC2_apply
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneFundamentalBox) (u : WholePlaneC2H2) :
    extendDomainC2 p R hR hbox u =
      horizontalProjH2
        (wholePlaneOutputLocalizationH2 p R hR hbox (wholePlaneVerticalZeroExtendH2 u)) :=
  rfl

/-! ## The embedding intertwining -/

/-- The `H²` output transport lies over the `L²` one: this is the `embedding_intertwining`
field of `SelectedLocalResolventData`. -/
theorem transverseH2Embedding_extendDomainC2
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneFundamentalBox) (u : WholePlaneC2H2) :
    transverseH2Embedding (extendDomainC2 p R hR hbox u) =
      extendStateC2 p R hR (wholePlaneH2Embedding C2 u) := by
  rw [extendDomainC2_apply, extendStateC2_apply,
    transverseH2Embedding_horizontalProjH2,
    transverseH2Embedding_wholePlaneOutputLocalizationH2,
    wholePlaneH2Embedding_wholePlaneVerticalZeroExtendH2]

/-- Operator form of the embedding intertwining. -/
theorem transverseH2Embedding_comp_extendDomainC2
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneFundamentalBox) :
    transverseH2Embedding.comp (extendDomainC2 p R hR hbox) =
      (extendStateC2 p R hR).comp (wholePlaneH2Embedding C2) := by
  apply ContinuousLinearMap.ext
  intro u
  exact transverseH2Embedding_extendDomainC2 p R hR hbox u

/-! ## Norms -/

/-- The input transport is a contraction: the chart map is an isometry, `‖φ_n‖_∞ ≤ 1`. -/
theorem norm_restrictInputC2_apply_le (f : TransverseC2L2) :
    ‖restrictInputC2 p R hR f‖ ≤ ‖f‖ := by
  calc ‖restrictInputC2 p R hR f‖ ≤
      ‖torusInputLocalizationL2 p R hR (verticalZeroExtendL2 f)‖ :=
        norm_wholePlaneHorizontalProjL2_apply_le _
    _ ≤ ‖verticalZeroExtendL2 f‖ :=
        norm_torusInputLocalizationL2_apply_le p R hR _
    _ = ‖f‖ := norm_verticalZeroExtendL2 f

/-- The output transport is a contraction on states. -/
theorem norm_extendStateC2_apply_le (g : WholePlaneC2L2) :
    ‖extendStateC2 p R hR g‖ ≤ ‖g‖ := by
  calc ‖extendStateC2 p R hR g‖ ≤
      ‖wholePlaneOutputLocalizationL2 p R hR (wholePlaneVerticalZeroExtendL2 g)‖ :=
        norm_horizontalProjL2_apply_le _
    _ ≤ ‖wholePlaneVerticalZeroExtendL2 g‖ :=
        norm_wholePlaneOutputLocalizationL2_apply_le p R hR _
    _ = ‖g‖ := norm_wholePlaneVerticalZeroExtendL2 g

/-! ## The round trip `extendState ∘ restrictInput = φ_n·` -/

/-- The two canonical `(0,1]²` representatives of a transverse-torus point agree. -/
theorem torusWholePlaneRepresentative_eq_iocRepresentative (q : TransverseTorus) :
    torusWholePlaneRepresentative q = wholePlaneIocRepresentative q := by
  ext j
  rfl

/-- Zero extension after projection restores a vector that is itself a zero extension. -/
theorem verticalZeroExtendPoint_horizontalProjPoint_verticalZeroExtendPoint
    (u : C2) :
    verticalZeroExtendPoint (horizontalProjPoint (verticalZeroExtendPoint u)) =
      verticalZeroExtendPoint u := by
  rw [horizontalProjPoint_verticalZeroExtendPoint]

/-- The larger output cut-off acts as the identity against the smaller input cut-off, in the
complexified spelling (`eq:parametrix-cutoff-identities`). -/
theorem outputCutoffComplex_mul_inputCutoffComplex (x : WholePlane) :
    outputCutoffComplex p R hR x * inputCutoffComplex p R hR x =
      inputCutoffComplex p R hR x := by
  rw [mul_comm]
  simpa only [inputCutoffComplex, outputCutoffComplex, Complex.ofReal_mul] using
    congrArg Complex.ofReal (inputCutoff_mul_outputCutoff p R hR x)

/-- **The fibre commutation lemma.**  The three-component input transport of a zero-extended
torus field is the zero extension of the two-component input transport.  Everything in the chart
acts diagonally in the fibre, so the axial component never gets populated. -/
theorem wholePlaneVerticalZeroExtendL2_restrictInputC2 (f : TransverseC2L2) :
    wholePlaneVerticalZeroExtendL2 (restrictInputC2 p R hR f) =
      torusInputLocalizationL2 p R hR (verticalZeroExtendL2 f) := by
  apply Lp.ext
  have hvze : ((verticalZeroExtendL2 f : TransverseC3L2) : TransverseTorus → C3) =ᵐ[
      transverseMeasure] fun q ↦ verticalZeroExtendPoint ((f : TransverseTorus → C2) q) :=
    verticalZeroExtendL2_coe_ae f
  have hpull := measurePreserving_wholePlaneTorusPoint.quasiMeasurePreserving.ae_eq_comp hvze
  have hind : wholePlaneFundamentalBox.indicator
        (fun y ↦ ((verticalZeroExtendL2 f : TransverseC3L2) : TransverseTorus → C3)
          (wholePlaneTorusPoint y)) =ᵐ[volume]
      wholePlaneFundamentalBox.indicator
        (fun y ↦ verticalZeroExtendPoint
          ((f : TransverseTorus → C2) (wholePlaneTorusPoint y))) :=
    (ae_eq_restrict_iff_indicator_ae_eq measurableSet_wholePlaneFundamentalBox).1
      (by simpa [Function.comp_def] using hpull)
  filter_upwards [wholePlaneVerticalZeroExtendL2_coe_ae (restrictInputC2 p R hR f),
    wholePlaneHorizontalProjL2_coe_ae
      (torusInputLocalizationL2 p R hR (verticalZeroExtendL2 f)),
    torusInputLocalizationL2_coe_ae p R hR (verticalZeroExtendL2 f), hind] with x h1 h2 h3 h4
  rw [h1]
  have h2' : ((restrictInputC2 p R hR f : WholePlaneC2L2) : WholePlane → C2) x =
      horizontalProjPoint
        ((torusInputLocalizationL2 p R hR (verticalZeroExtendL2 f) : WholePlane → C3) x) := h2
  rw [h2', h3, h4]
  by_cases hx : x ∈ wholePlaneFundamentalBox
  · rw [Set.indicator_of_mem hx, ← map_smul verticalZeroExtendPoint,
      verticalZeroExtendPoint_horizontalProjPoint_verticalZeroExtendPoint]
  · rw [Set.indicator_of_notMem hx, smul_zero, map_zero, map_zero]

/-- **The chart round trip.**  Restricting the input and extending the state again is exactly
multiplication by the periodized input cut-off `φ_n`.  This is the `roundTrip` field of
`SelectedLocalResolventData`, i.e. `ψ_nφ_n = φ_n` read through the chart. -/
theorem extendStateC2_restrictInputC2
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) (f : TransverseC2L2) :
    extendStateC2 p R hR (restrictInputC2 p R hR f) = (inputMul p R hR).stateMul f := by
  have hA := wholePlaneVerticalZeroExtendL2_restrictInputC2 p R hR f
  rw [extendStateC2_apply, hA]
  apply Lp.ext
  have hplane := torusInputLocalizationL2_coe_ae p R hR (verticalZeroExtendL2 f)
  have hrestrict :
      ((torusInputLocalizationL2 p R hR (verticalZeroExtendL2 f) : WholePlaneC3L2) :
          WholePlane → C3) =ᵐ[volume.restrict wholePlaneFundamentalBox]
        fun x ↦ inputCutoffComplex p R hR x •
          wholePlaneFundamentalBox.indicator
            (fun y ↦ ((verticalZeroExtendL2 f : TransverseC3L2) : TransverseTorus → C3)
              (wholePlaneTorusPoint y)) x :=
    hplane.filter_mono (ae_mono Measure.restrict_le_self)
  have hpull := measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
    hrestrict
  have hvze : ((verticalZeroExtendL2 f : TransverseC3L2) : TransverseTorus → C3) =ᵐ[
      transverseMeasure] fun q ↦ verticalZeroExtendPoint ((f : TransverseTorus → C2) q) :=
    verticalZeroExtendL2_coe_ae f
  have hpull' : (fun q ↦ ((torusInputLocalizationL2 p R hR (verticalZeroExtendL2 f) :
        WholePlaneC3L2) : WholePlane → C3) (torusWholePlaneRepresentative q)) =ᵐ[
      transverseMeasure] fun q ↦
        inputCutoffComplex p R hR (torusWholePlaneRepresentative q) •
          wholePlaneFundamentalBox.indicator
            (fun y ↦ ((verticalZeroExtendL2 f : TransverseC3L2) : TransverseTorus → C3)
              (wholePlaneTorusPoint y)) (torusWholePlaneRepresentative q) := hpull
  filter_upwards [horizontalProjL2_coe_ae (wholePlaneOutputLocalizationL2 p R hR
      (torusInputLocalizationL2 p R hR (verticalZeroExtendL2 f))),
    wholePlaneOutputLocalizationL2_coe_ae p R hR
      (torusInputLocalizationL2 p R hR (verticalZeroExtendL2 f)),
    hpull', hvze,
    scalarVectorMulL2_coe_ae (E := C2) transverseMeasure (inputMul p R hR).value f,
    inputMul_value_ae p R hR hbox]
      with q h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, Set.indicator_of_mem (torusWholePlaneRepresentative_mem q),
    wholePlaneTorusPoint_torusWholePlaneRepresentative, h4, smul_smul,
    outputCutoffComplex_mul_inputCutoffComplex, map_smul,
    horizontalProjPoint_verticalZeroExtendPoint]
  rw [show ((inputMul p R hR).stateMul f : TransverseTorus → C2) q =
      ((inputMul p R hR).value : TransverseTorus → ℂ) q • ((f : TransverseTorus → C2) q)
    from h5, h6, torusWholePlaneRepresentative_eq_iocRepresentative]
  rfl

/-- Operator form of the chart round trip. -/
theorem extendStateC2_comp_restrictInputC2
    (hbox : Metric.closedBall p (R / 2) ⊆ wholePlaneIocFundamentalBox) :
    (extendStateC2 p R hR).comp (restrictInputC2 p R hR) = (inputMul p R hR).stateMul := by
  apply ContinuousLinearMap.ext
  intro f
  exact extendStateC2_restrictInputC2 p R hR hbox f

end TorusChartC2Transfer

end

end FastDynamo
