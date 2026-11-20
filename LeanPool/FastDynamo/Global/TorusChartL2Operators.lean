/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusChartFourierWeakTransfer
public import LeanPool.FastDynamo.Global.ParametrixExplicitCutoffDerivatives

/-!
# Bounded `L²` maps for the transverse torus chart

This file realizes the extension and restriction maps used implicitly by
the paper's local parametrix.  The quotient map from the canonical
fundamental rectangle to `TransverseTorus` is measure preserving.  Pullback,
extension by zero, and the volume-preserving `PiLp` coordinate change then
give an isometric torus-to-whole-plane map.  Restriction in the other
direction is a contraction.

The module also records pointwise formulae for both maps, the predicate
`IsSupportedInWholePlaneFundamentalBox` of support in the chart, and the explicit input and
output cut-offs of §7.1 as `L∞` multipliers on whole-plane `L²`, with the input localization
`torusInputLocalizationL2` (torus to whole plane) and the output localization
`wholePlaneOutputLocalizationL2` (whole plane to torus).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped ENNReal

namespace TorusChartL2

/-! ## The measure-preserving fundamental chart -/

/-- Raw two-dimensional Euclidean coordinates used by Mathlib's product
fundamental-domain theorem. -/
abbrev RawPlane := Fin 2 → ℝ

/-- The canonical `(0,1]²` rectangle. -/
abbrev rawFundamentalBox : Set RawPlane :=
  ScaleFamily.TorusCellPlacement.EuclideanCellSourceCertificate.iocFundamentalBox

/-- The canonical `(0,1]²` rectangle is measurable, being a product of `Ioc` intervals. -/
theorem measurableSet_rawFundamentalBox :
    MeasurableSet (rawFundamentalBox : Set RawPlane) :=
  ScaleFamily.TorusCellPlacement.EuclideanCellSourceCertificate.measurableSet_iocFundamentalBox

/-- Coordinatewise quotient from the raw fundamental rectangle to the
transverse torus. -/
def rawTorusPoint (x : RawPlane) : TransverseTorus :=
  fun j ↦ (x j : UnitAddCircle)

/-- The coordinatewise quotient from raw plane coordinates to the transverse torus is
measurable. -/
theorem measurable_rawTorusPoint : Measurable rawTorusPoint := by
  exact Measurable.of_eval fun j ↦
    AddCircle.measurable_mk'.comp (measurable_pi_apply j)

/-- The quotient is measure preserving when Lebesgue measure is restricted
to the canonical fundamental rectangle. -/
theorem measurePreserving_rawTorusPoint :
    MeasurePreserving rawTorusPoint
      (volume.restrict rawFundamentalBox) transverseMeasure := by
  rw [show transverseMeasure = torusHaarMeasure (Fin 2) from
    volume_unitAddTorus_eq_haar]
  let a : Fin 2 → ℝ := fun _ ↦ 0
  let chartSubtype :=
    {x : RawPlane // ∀ j, x j ∈ Set.Ioc (a j) (a j + 1)}
  let e : TransverseTorus ≃ᵐ chartSubtype :=
    UnitAddTorus.measurableEquivPiIoc a
  have hs : MeasurableSet
      {x : RawPlane | ∀ j, x j ∈ Set.Ioc (a j) (a j + 1)} :=
    MeasurableSet.univ_pi' (fun _ ↦ measurableSet_Ioc)
  have hcoe := measurePreserving_subtype_coe
    (μa := (volume : Measure RawPlane)) hs
  have he := (UnitAddTorus.measurePreserving_equivPiIoc a).symm
  refine ⟨measurable_rawTorusPoint, ?_⟩
  have hset : rawFundamentalBox =
      {x : RawPlane | ∀ j, x j ∈ Set.Ioc (a j) (a j + 1)} := by
    rfl
  rw [hset, ← hcoe.map_eq]
  rw [Measure.map_map measurable_rawTorusPoint hcoe.measurable]
  have hfun : rawTorusPoint ∘ (Subtype.val : chartSubtype → RawPlane) =
      (e.symm : chartSubtype → TransverseTorus) := by
    funext x
    rfl
  calc
    Measure.map (rawTorusPoint ∘ (Subtype.val : chartSubtype → RawPlane))
        (Measure.comap Subtype.val volume) =
        Measure.map (e.symm : chartSubtype → TransverseTorus)
          (Measure.comap Subtype.val volume) :=
      congrArg (fun f : chartSubtype → TransverseTorus ↦
        Measure.map f (Measure.comap Subtype.val volume)) hfun
    _ = torusHaarMeasure (Fin 2) := he.map_eq

/-! ## Generic restriction and zero extension on `L²` -/

section SameDomain

variable {X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (μ : Measure X) (s : Set X) (hs : MeasurableSet s)

/-- Extend an `L²(μ.restrict s)` representative by zero to `L²(μ)`. -/
def zeroExtensionL2Fun (f : Lp E 2 (μ.restrict s)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hs.nullMeasurableSet).2 (Lp.memLp f)).toLp
    (s.indicator fun x ↦ f x)

omit [NormedSpace ℂ E] in
/-- The zero extension of an `L²(μ.restrict s)` class is represented almost everywhere by the
indicator of `s` times the original representative. -/
theorem zeroExtensionL2Fun_coe_ae (f : Lp E 2 (μ.restrict s)) :
    (zeroExtensionL2Fun μ s hs f : X → E) =ᵐ[μ]
      s.indicator (fun x ↦ f x) :=
  MemLp.coeFn_toLp _

omit [NormedSpace ℂ E] in
/-- Extension by zero preserves the `L²` norm, since the restricted `eLpNorm` of a class equals
the global `eLpNorm` of its indicator. -/
theorem norm_zeroExtensionL2Fun (f : Lp E 2 (μ.restrict s)) :
    ‖zeroExtensionL2Fun μ s hs f‖ = ‖f‖ := by
  rw [zeroExtensionL2Fun, Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet, Lp.norm_def]

/-- Extension by zero is a complex-linear isometry. -/
def zeroExtensionL2 :
    Lp E 2 (μ.restrict s) →ₗᵢ[ℂ] Lp E 2 μ where
  toFun := zeroExtensionL2Fun μ s hs
  map_add' f g := by
    apply Lp.ext
    have hadd :
        s.indicator (fun x ↦ (f + g) x) =ᵐ[μ]
          s.indicator (fun x ↦ f x + g x) :=
      (ae_eq_restrict_iff_indicator_ae_eq hs).1 (Lp.coeFn_add f g)
    filter_upwards [zeroExtensionL2Fun_coe_ae μ s hs (f + g),
      zeroExtensionL2Fun_coe_ae μ s hs f,
      zeroExtensionL2Fun_coe_ae μ s hs g,
      Lp.coeFn_add (zeroExtensionL2Fun μ s hs f)
        (zeroExtensionL2Fun μ s hs g), hadd] with x hfg hf hg hout ha
    rw [hfg, hout, Pi.add_apply, hf, hg, ha]
    by_cases hx : x ∈ s <;> simp [hx]
  map_smul' c f := by
    change zeroExtensionL2Fun μ s hs (c • f) =
      c • zeroExtensionL2Fun μ s hs f
    apply Lp.ext
    have hsmul :
        s.indicator (fun x ↦ (c • f) x) =ᵐ[μ]
          s.indicator (fun x ↦ c • f x) :=
      (ae_eq_restrict_iff_indicator_ae_eq hs).1 (Lp.coeFn_smul c f)
    filter_upwards [zeroExtensionL2Fun_coe_ae μ s hs (c • f),
      zeroExtensionL2Fun_coe_ae μ s hs f,
      Lp.coeFn_smul c (zeroExtensionL2Fun μ s hs f), hsmul]
      with x hcf hf hout ha
    rw [hcf, hout, Pi.smul_apply, hf, ha]
    by_cases hx : x ∈ s <;> simp [hx]
  norm_map' := norm_zeroExtensionL2Fun μ s hs

/-- Restrict an `L²(μ)` class to the measure `μ.restrict s`. -/
def restrictionL2Fun (f : Lp E 2 μ) : Lp E 2 (μ.restrict s) :=
  (Lp.memLp f).restrict s |>.toLp (fun x ↦ f x)

omit [NormedSpace ℂ E] in
/-- The restriction of an `L²(μ)` class is represented, `μ.restrict s`-almost everywhere, by the
same function. -/
theorem restrictionL2Fun_coe_ae (f : Lp E 2 μ) :
    (restrictionL2Fun μ s f : X → E) =ᵐ[μ.restrict s]
      fun x ↦ f x :=
  MemLp.coeFn_toLp _

omit [NormedSpace ℂ E] in
/-- Restriction to a measurable set does not increase the `L²` norm, `μ.restrict s` being at most
`μ`. -/
theorem norm_restrictionL2Fun_le (f : Lp E 2 μ) :
    ‖restrictionL2Fun μ s f‖ ≤ ‖f‖ := by
  rw [restrictionL2Fun, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Restriction to a measurable set is a complex-linear contraction. -/
def restrictionL2 : Lp E 2 μ →L[ℂ] Lp E 2 (μ.restrict s) :=
  LinearMap.mkContinuous
    { toFun := restrictionL2Fun μ s
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [restrictionL2Fun_coe_ae μ s (f + g),
          restrictionL2Fun_coe_ae μ s f,
          restrictionL2Fun_coe_ae μ s g,
          (Lp.coeFn_add f g).filter_mono
            (ae_mono Measure.restrict_le_self),
          Lp.coeFn_add (restrictionL2Fun μ s f)
            (restrictionL2Fun μ s g)] with x hfg hf hg hin hout
        rw [hfg, hout, Pi.add_apply, hf, hg, hin]
        rfl
      map_smul' := fun c f ↦ by
        change restrictionL2Fun μ s (c • f) =
          c • restrictionL2Fun μ s f
        apply Lp.ext
        filter_upwards [restrictionL2Fun_coe_ae μ s (c • f),
          restrictionL2Fun_coe_ae μ s f,
          (Lp.coeFn_smul c f).filter_mono
            (ae_mono Measure.restrict_le_self),
          Lp.coeFn_smul c (restrictionL2Fun μ s f)]
          with x hcf hf hin hout
        rw [hcf, hout, Pi.smul_apply, hf, hin]
        rfl }
    1 (fun f ↦ by simpa using norm_restrictionL2Fun_le μ s f)

end SameDomain

/-! ## The two chart operators -/

/-- Pull torus `L²` back to the raw canonical fundamental rectangle. -/
def torusToRawRestrictedL2 :
    TransverseC3L2 →ₗᵢ[ℂ]
      Lp C3 2 (volume.restrict rawFundamentalBox) :=
  Lp.compMeasurePreservingₗᵢ ℂ rawTorusPoint
    measurePreserving_rawTorusPoint

/-- Raw Euclidean coordinates and `WholePlane = PiLp 2` have the same
Lebesgue volume. -/
def rawToWholePlaneL2 :
    Lp C3 2 (volume : Measure RawPlane) →ₗᵢ[ℂ] WholePlaneC3L2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (@WithLp.ofLp 2 RawPlane)
    (PiLp.volume_preserving_ofLp (Fin 2))

/-- Isometric localization of a torus field to the whole-plane canonical
chart, extended by zero outside the chart. -/
def torusToWholePlaneL2 : TransverseC3L2 →ₗᵢ[ℂ] WholePlaneC3L2 :=
  rawToWholePlaneL2.comp
    ((zeroExtensionL2 volume rawFundamentalBox
      measurableSet_rawFundamentalBox).comp torusToRawRestrictedL2)

/-- The canonical measurable representative of a torus point in the raw
fundamental rectangle. -/
def rawFundamentalRepresentative (q : TransverseTorus) : rawFundamentalBox :=
  UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 ↦ (0 : ℝ)) q

/-! ## Pointwise chart formulae -/

/-- The raw coordinates of a `WholePlane` point. -/
def wholePlaneRawCoordinate (x : WholePlane) : RawPlane :=
  @WithLp.ofLp 2 RawPlane x

/-- The canonical fundamental rectangle, now regarded as a subset of
`WholePlane`. -/
def wholePlaneFundamentalBox : Set WholePlane :=
  wholePlaneRawCoordinate ⁻¹' rawFundamentalBox

/-- The canonical fundamental rectangle, seen inside `WholePlane`, is measurable. -/
theorem measurableSet_wholePlaneFundamentalBox :
    MeasurableSet wholePlaneFundamentalBox :=
  measurableSet_rawFundamentalBox.preimage
    (PiLp.volume_preserving_ofLp (Fin 2)).measurable

/-- The quotient map from `WholePlane` coordinates to the transverse
torus. -/
def wholePlaneTorusPoint (x : WholePlane) : TransverseTorus :=
  rawTorusPoint (wholePlaneRawCoordinate x)

/-- The canonical `(0,1]²` representative of a transverse-torus point,
written in `WholePlane` coordinates. -/
def torusWholePlaneRepresentative (q : TransverseTorus) : WholePlane :=
  @WithLp.toLp 2 RawPlane (rawFundamentalRepresentative q).1

/-- The canonical representative of a torus point lies in the fundamental rectangle. -/
theorem torusWholePlaneRepresentative_mem (q : TransverseTorus) :
    torusWholePlaneRepresentative q ∈ wholePlaneFundamentalBox := by
  exact (rawFundamentalRepresentative q).2

/-- Taking the canonical representative and projecting back to the torus is the identity on the
torus. -/
theorem wholePlaneTorusPoint_torusWholePlaneRepresentative
    (q : TransverseTorus) :
    wholePlaneTorusPoint (torusWholePlaneRepresentative q) = q := by
  change rawTorusPoint (rawFundamentalRepresentative q).1 = q
  exact (UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 ↦ (0 : ℝ))).symm_apply_apply q

/-- On the fundamental rectangle the canonical representative of the quotient class of `x` is `x`
itself, so the rectangle is a fundamental domain. -/
theorem torusWholePlaneRepresentative_wholePlaneTorusPoint
    {x : WholePlane} (hx : x ∈ wholePlaneFundamentalBox) :
    torusWholePlaneRepresentative (wholePlaneTorusPoint x) = x := by
  apply WithLp.ofLp_injective (p := 2)
  change (rawFundamentalRepresentative
    (rawTorusPoint (wholePlaneRawCoordinate x))).1 = wholePlaneRawCoordinate x
  let xs : rawFundamentalBox := ⟨wholePlaneRawCoordinate x, hx⟩
  exact congrArg Subtype.val
    ((UnitAddTorus.measurableEquivPiIoc
      (fun _ : Fin 2 ↦ (0 : ℝ))).apply_symm_apply xs)

/-- The linear coordinate equivalence preserves the restricted volume of
the canonical rectangle. -/
theorem toLp_preimage_wholePlaneFundamentalBox :
    (@WithLp.toLp 2 RawPlane) ⁻¹' wholePlaneFundamentalBox =
      rawFundamentalBox := by
  ext x
  rfl

/-- The linear coordinate change `RawPlane ≃ WholePlane` carries Lebesgue measure restricted to
the raw rectangle to Lebesgue measure restricted to the same rectangle inside `WholePlane`. -/
theorem measurePreserving_toLp_restricted :
    MeasurePreserving (@WithLp.toLp 2 RawPlane)
      (volume.restrict rawFundamentalBox)
      (volume.restrict wholePlaneFundamentalBox) := by
  have h := (PiLp.volume_preserving_toLp (Fin 2)).restrict_preimage
    measurableSet_wholePlaneFundamentalBox
  simpa [toLp_preimage_wholePlaneFundamentalBox] using h

/-- The canonical raw representative preserves physical transverse volume
onto Lebesgue volume restricted to the fundamental rectangle. -/
theorem measurePreserving_rawFundamentalRepresentativeVal :
    MeasurePreserving (fun q : TransverseTorus ↦
      (rawFundamentalRepresentative q).1)
      transverseMeasure (volume.restrict rawFundamentalBox) := by
  rw [show transverseMeasure = torusHaarMeasure (Fin 2) from
    volume_unitAddTorus_eq_haar]
  have hcoe := measurePreserving_subtype_coe
    (μa := (volume : Measure RawPlane)) measurableSet_rawFundamentalBox
  have he := UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin 2 ↦ (0 : ℝ))
  exact hcoe.comp he

/-- The canonical `WholePlane` representative is measure preserving onto
the restricted fundamental rectangle. -/
theorem measurePreserving_torusWholePlaneRepresentative :
    MeasurePreserving torusWholePlaneRepresentative transverseMeasure
      (volume.restrict wholePlaneFundamentalBox) := by
  exact measurePreserving_toLp_restricted.comp
    measurePreserving_rawFundamentalRepresentativeVal

/-- Conversely, quotienting the restricted whole-plane rectangle preserves
volume onto the transverse torus. -/
theorem measurePreserving_wholePlaneTorusPoint :
    MeasurePreserving wholePlaneTorusPoint
      (volume.restrict wholePlaneFundamentalBox) transverseMeasure := by
  have hof := (PiLp.volume_preserving_ofLp (Fin 2)).restrict_preimage
    measurableSet_rawFundamentalBox
  have hset : (@WithLp.ofLp 2 RawPlane) ⁻¹' rawFundamentalBox =
      wholePlaneFundamentalBox := rfl
  rw [hset] at hof
  exact measurePreserving_rawTorusPoint.comp hof

/-- Restrict a whole-plane field to the canonical chart and pull it back
through the canonical torus representative.  This is the bounded
chart restriction map; its norm is at most one. -/
def wholePlaneToTorusL2 : WholePlaneC3L2 →L[ℂ] TransverseC3L2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ torusWholePlaneRepresentative
      measurePreserving_torusWholePlaneRepresentative).toContinuousLinearMap.comp
    (restrictionL2 volume wholePlaneFundamentalBox)

/-- The torus-to-raw-rectangle pullback is represented, on the restricted measure, by composition
with the quotient map `rawTorusPoint`. -/
theorem torusToRawRestrictedL2_coe_ae (f : TransverseC3L2) :
    (torusToRawRestrictedL2 f : RawPlane → C3) =ᵐ[
      volume.restrict rawFundamentalBox] fun x ↦ f (rawTorusPoint x) := by
  exact Lp.coeFn_compMeasurePreserving f measurePreserving_rawTorusPoint

/-- The coordinate change from raw to `PiLp` plane coordinates is represented by composition with
`wholePlaneRawCoordinate`. -/
theorem rawToWholePlaneL2_coe_ae
    (f : Lp C3 2 (volume : Measure RawPlane)) :
    (rawToWholePlaneL2 f : WholePlane → C3) =ᵐ[volume]
      fun x ↦ f (wholePlaneRawCoordinate x) := by
  exact Lp.coeFn_compMeasurePreserving f
    (PiLp.volume_preserving_ofLp (Fin 2))

/-- Pointwise representative of the isometric torus-to-plane chart map:
pull back through the quotient inside the canonical rectangle and use zero
outside it. -/
theorem torusToWholePlaneL2_coe_ae (f : TransverseC3L2) :
    (torusToWholePlaneL2 f : WholePlane → C3) =ᵐ[volume]
      wholePlaneFundamentalBox.indicator
        (fun x ↦ f (wholePlaneTorusPoint x)) := by
  let g : Lp C3 2 (volume : Measure RawPlane) :=
    zeroExtensionL2 volume rawFundamentalBox
      measurableSet_rawFundamentalBox (torusToRawRestrictedL2 f)
  have hzero : (g : RawPlane → C3) =ᵐ[volume]
      rawFundamentalBox.indicator
        (fun x ↦ (torusToRawRestrictedL2 f) x) :=
    zeroExtensionL2Fun_coe_ae volume rawFundamentalBox
      measurableSet_rawFundamentalBox (torusToRawRestrictedL2 f)
  have hchart :
      rawFundamentalBox.indicator
          (fun x ↦ (torusToRawRestrictedL2 f) x) =ᵐ[volume]
        rawFundamentalBox.indicator (fun x ↦ f (rawTorusPoint x)) :=
    (ae_eq_restrict_iff_indicator_ae_eq
      measurableSet_rawFundamentalBox).1
      (torusToRawRestrictedL2_coe_ae f)
  have hraw : (g : RawPlane → C3) =ᵐ[volume]
      rawFundamentalBox.indicator (fun x ↦ f (rawTorusPoint x)) :=
    hzero.trans hchart
  have hpull := (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving
    |>.ae_eq_comp hraw
  have hout : (torusToWholePlaneL2 f : WholePlane → C3) =ᵐ[volume]
      fun x ↦ g (wholePlaneRawCoordinate x) := by
    exact rawToWholePlaneL2_coe_ae g
  filter_upwards [hout, hpull] with x hx hp
  rw [hx]
  have hp' : g (wholePlaneRawCoordinate x) =
      rawFundamentalBox.indicator (fun y ↦ f (rawTorusPoint y))
        (wholePlaneRawCoordinate x) := by
    simpa [wholePlaneRawCoordinate] using hp
  rw [hp']
  by_cases hbox : x ∈ wholePlaneFundamentalBox
  · have hrawBox : wholePlaneRawCoordinate x ∈ rawFundamentalBox := hbox
    rw [Set.indicator_of_mem hrawBox, Set.indicator_of_mem hbox]
    rfl
  · have hrawBox : wholePlaneRawCoordinate x ∉ rawFundamentalBox := hbox
    rw [Set.indicator_of_notMem hrawBox, Set.indicator_of_notMem hbox]

/-- Zero extension through the chart is an isometry on torus `L²`:
`‖torusToWholePlaneL2 f‖ = ‖f‖`. -/
theorem norm_torusToWholePlaneL2 (f : TransverseC3L2) :
    ‖torusToWholePlaneL2 f‖ = ‖f‖ :=
  LinearIsometry.norm_map _ f

/-- Pointwise representative of chart restriction: evaluate a whole-plane
field at the canonical fundamental representative of the torus point. -/
theorem wholePlaneToTorusL2_coe_ae (f : WholePlaneC3L2) :
    (wholePlaneToTorusL2 f : TransverseTorus → C3) =ᵐ[transverseMeasure]
      fun q ↦ f (torusWholePlaneRepresentative q) := by
  let r : Lp C3 2 (volume.restrict wholePlaneFundamentalBox) :=
    restrictionL2 volume wholePlaneFundamentalBox f
  have hcomp : (wholePlaneToTorusL2 f : TransverseTorus → C3) =ᵐ[
      transverseMeasure] fun q ↦ r (torusWholePlaneRepresentative q) := by
    exact Lp.coeFn_compMeasurePreserving r
      measurePreserving_torusWholePlaneRepresentative
  have hres : (r : WholePlane → C3) =ᵐ[
      volume.restrict wholePlaneFundamentalBox] fun x ↦ f x :=
    restrictionL2Fun_coe_ae volume wholePlaneFundamentalBox f
  have hpull := measurePreserving_torusWholePlaneRepresentative
    |>.quasiMeasurePreserving |>.ae_eq_comp hres
  exact hcomp.trans (by simpa [Function.comp_def] using hpull)

/-- An `L²` class is supported in the canonical chart when it vanishes
almost everywhere outside the chart. -/
def IsSupportedInWholePlaneFundamentalBox (f : WholePlaneC3L2) : Prop :=
  ∀ᵐ x ∂volume, x ∉ wholePlaneFundamentalBox → f x = 0

/-! ## The explicit input and output cutoffs of §7.1 -/

/-- Complex-valued spelling of the real input cutoff. -/
def inputCutoffComplex (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (x : WholePlane) : ℂ :=
  (ParametrixExplicitCutoff.inputCutoff p R hR x : ℂ)

/-- Complex-valued spelling of the real output cutoff. -/
def outputCutoffComplex (p : WholePlane) (R : ℝ) (hR : 0 < R)
    (x : WholePlane) : ℂ :=
  (ParametrixExplicitCutoff.outputCutoff p R hR x : ℂ)

/-- The complexified input cutoff is bounded by one in modulus, its real values lying in
`[0, 1]`. -/
theorem norm_inputCutoffComplex_le_one
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    ‖inputCutoffComplex p R hR x‖ ≤ 1 := by
  rw [inputCutoffComplex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ParametrixExplicitCutoff.inputCutoff_mem_Icc
      p R hR x).1]
  exact (ParametrixExplicitCutoff.inputCutoff_mem_Icc p R hR x).2

/-- The complexified output cutoff is bounded by one in modulus, its real values lying in
`[0, 1]`. -/
theorem norm_outputCutoffComplex_le_one
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (x : WholePlane) :
    ‖outputCutoffComplex p R hR x‖ ≤ 1 := by
  rw [outputCutoffComplex, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ParametrixExplicitCutoff.outputCutoff_mem_Icc
      p R hR x).1]
  exact (ParametrixExplicitCutoff.outputCutoff_mem_Icc p R hR x).2

/-- The smaller input cutoff as a bounded whole-plane multiplier. -/
def inputCutoffLInf (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    Lp ℂ ∞ (volume : Measure WholePlane) :=
  (memLp_top_of_bound
    (Complex.continuous_ofReal.comp
      (ParametrixExplicitCutoff.inputCutoff_contDiff p R hR).continuous
      ).aestronglyMeasurable
    1 (ae_of_all volume (norm_inputCutoffComplex_le_one p R hR))).toLp
      (inputCutoffComplex p R hR)

/-- The larger output cutoff as a bounded whole-plane multiplier. -/
def outputCutoffLInf (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    Lp ℂ ∞ (volume : Measure WholePlane) :=
  (memLp_top_of_bound
    (Complex.continuous_ofReal.comp
      (ParametrixExplicitCutoff.outputCutoff_contDiff p R hR).continuous
      ).aestronglyMeasurable
    1 (ae_of_all volume (norm_outputCutoffComplex_le_one p R hR))).toLp
      (outputCutoffComplex p R hR)

/-- The bundled `L∞` class of the input cutoff is represented a.e. by the pointwise complexified
cutoff. -/
theorem inputCutoffLInf_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    (inputCutoffLInf p R hR : WholePlane → ℂ) =ᵐ[volume]
      inputCutoffComplex p R hR :=
  MemLp.coeFn_toLp _

/-- The bundled `L∞` class of the output cutoff is represented a.e. by the pointwise complexified
cutoff. -/
theorem outputCutoffLInf_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    (outputCutoffLInf p R hR : WholePlane → ℂ) =ᵐ[volume]
      outputCutoffComplex p R hR :=
  MemLp.coeFn_toLp _

/-- The input cutoff has `L∞` norm at most one. -/
theorem norm_inputCutoffLInf_le_one
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    ‖inputCutoffLInf p R hR‖ ≤ 1 := by
  rw [Lp.norm_def]
  apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [inputCutoffLInf_coe_ae p R hR] with x hx
  rw [hx]
  exact norm_inputCutoffComplex_le_one p R hR x

/-- The output cutoff has `L∞` norm at most one. -/
theorem norm_outputCutoffLInf_le_one
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    ‖outputCutoffLInf p R hR‖ ≤ 1 := by
  rw [Lp.norm_def]
  apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [outputCutoffLInf_coe_ae p R hR] with x hx
  rw [hx]
  exact norm_outputCutoffComplex_le_one p R hR x

/-- Multiplication by the explicit input cutoff on whole-plane `L²`. -/
def inputCutoffMulL2 (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    WholePlaneC3L2 →L[ℂ] WholePlaneC3L2 :=
  scalarVectorMulL2 volume (inputCutoffLInf p R hR)

/-- Multiplication by the explicit output cutoff on whole-plane `L²`. -/
def outputCutoffMulL2 (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    WholePlaneC3L2 →L[ℂ] WholePlaneC3L2 :=
  scalarVectorMulL2 volume (outputCutoffLInf p R hR)

/-- The bounded parametrix input-localization map from torus `L²` to
whole-plane `L²`. -/
def torusInputLocalizationL2
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    TransverseC3L2 →L[ℂ] WholePlaneC3L2 :=
  (inputCutoffMulL2 p R hR).comp
    torusToWholePlaneL2.toContinuousLinearMap

/-- The bounded parametrix output-localization map from whole-plane `L²`
back to torus `L²`. -/
def wholePlaneOutputLocalizationL2
    (p : WholePlane) (R : ℝ) (hR : 0 < R) :
    WholePlaneC3L2 →L[ℂ] TransverseC3L2 :=
  wholePlaneToTorusL2.comp (outputCutoffMulL2 p R hR)

/-- Multiplication by the input cutoff is represented a.e. by the pointwise product
`x ↦ φ_in(x) • f x`. -/
theorem inputCutoffMulL2_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (f : WholePlaneC3L2) :
    (inputCutoffMulL2 p R hR f : WholePlane → C3) =ᵐ[volume]
      fun x ↦ inputCutoffComplex p R hR x • f x := by
  filter_upwards [scalarVectorMulL2_coe_ae volume
      (inputCutoffLInf p R hR) f,
    inputCutoffLInf_coe_ae p R hR] with x hmul hcut
  change (scalarVectorMulL2 volume (inputCutoffLInf p R hR) f :
    WholePlane → C3) x = _
  rw [hmul, hcut]

/-- Multiplication by the output cutoff is represented a.e. by the pointwise product
`x ↦ ψ_out(x) • f x`. -/
theorem outputCutoffMulL2_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (f : WholePlaneC3L2) :
    (outputCutoffMulL2 p R hR f : WholePlane → C3) =ᵐ[volume]
      fun x ↦ outputCutoffComplex p R hR x • f x := by
  filter_upwards [scalarVectorMulL2_coe_ae volume
      (outputCutoffLInf p R hR) f,
    outputCutoffLInf_coe_ae p R hR] with x hmul hcut
  change (scalarVectorMulL2 volume (outputCutoffLInf p R hR) f :
    WholePlane → C3) x = _
  rw [hmul, hcut]

/-- Multiplication by the input cutoff is a pointwise contraction on `L²`, the cutoff being
bounded by one. -/
theorem norm_inputCutoffMulL2_apply_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (f : WholePlaneC3L2) :
    ‖inputCutoffMulL2 p R hR f‖ ≤ ‖f‖ := by
  calc
    ‖inputCutoffMulL2 p R hR f‖ ≤
        ‖inputCutoffLInf p R hR‖ * ‖f‖ :=
      norm_scalarVectorMulL2_apply_le volume (inputCutoffLInf p R hR) f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (norm_inputCutoffLInf_le_one p R hR) (norm_nonneg f)
    _ = ‖f‖ := one_mul _

/-- Multiplication by the output cutoff is a pointwise contraction on `L²`, the cutoff being
bounded by one. -/
theorem norm_outputCutoffMulL2_apply_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (f : WholePlaneC3L2) :
    ‖outputCutoffMulL2 p R hR f‖ ≤ ‖f‖ := by
  calc
    ‖outputCutoffMulL2 p R hR f‖ ≤
        ‖outputCutoffLInf p R hR‖ * ‖f‖ :=
      norm_scalarVectorMulL2_apply_le volume (outputCutoffLInf p R hR) f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (norm_outputCutoffLInf_le_one p R hR) (norm_nonneg f)
    _ = ‖f‖ := one_mul _

/-- Chart restriction does not increase the `L²` norm of any whole-plane field. -/
theorem norm_wholePlaneToTorusL2_apply_le (f : WholePlaneC3L2) :
    ‖wholePlaneToTorusL2 f‖ ≤ ‖f‖ := by
  change ‖Lp.compMeasurePreserving torusWholePlaneRepresentative
      measurePreserving_torusWholePlaneRepresentative
      (restrictionL2 volume wholePlaneFundamentalBox f)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  exact norm_restrictionL2Fun_le volume wholePlaneFundamentalBox f

/-- The parametrix input localization does not increase norms: zero extension is an isometry and
the input cutoff is a contraction. -/
theorem norm_torusInputLocalizationL2_apply_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (f : TransverseC3L2) :
    ‖torusInputLocalizationL2 p R hR f‖ ≤ ‖f‖ := by
  change ‖inputCutoffMulL2 p R hR (torusToWholePlaneL2 f)‖ ≤ ‖f‖
  exact (norm_inputCutoffMulL2_apply_le p R hR
    (torusToWholePlaneL2 f)).trans_eq (norm_torusToWholePlaneL2 f)

/-- The parametrix output localization does not increase norms: the output cutoff is a contraction
and chart restriction does not increase norms. -/
theorem norm_wholePlaneOutputLocalizationL2_apply_le
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (f : WholePlaneC3L2) :
    ‖wholePlaneOutputLocalizationL2 p R hR f‖ ≤ ‖f‖ := by
  change ‖wholePlaneToTorusL2 (outputCutoffMulL2 p R hR f)‖ ≤ ‖f‖
  exact (norm_wholePlaneToTorusL2_apply_le
    (outputCutoffMulL2 p R hR f)).trans
      (norm_outputCutoffMulL2_apply_le p R hR f)

/-- AE formula for input localization: zero-extension through the chart,
then multiplication by the smaller cutoff. -/
theorem torusInputLocalizationL2_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (f : TransverseC3L2) :
    (torusInputLocalizationL2 p R hR f : WholePlane → C3) =ᵐ[volume]
      fun x ↦ inputCutoffComplex p R hR x •
        wholePlaneFundamentalBox.indicator
          (fun y ↦ f (wholePlaneTorusPoint y)) x := by
  filter_upwards [inputCutoffMulL2_coe_ae p R hR
      (torusToWholePlaneL2 f),
    torusToWholePlaneL2_coe_ae f] with x hmul hext
  change (inputCutoffMulL2 p R hR (torusToWholePlaneL2 f) :
    WholePlane → C3) x = _
  rw [hmul, hext]

/-- AE formula for output localization: multiply by the larger compactly
supported cutoff, then evaluate at the canonical torus representative. -/
theorem wholePlaneOutputLocalizationL2_coe_ae
    (p : WholePlane) (R : ℝ) (hR : 0 < R) (f : WholePlaneC3L2) :
    (wholePlaneOutputLocalizationL2 p R hR f : TransverseTorus → C3)
      =ᵐ[transverseMeasure] fun q ↦
        outputCutoffComplex p R hR (torusWholePlaneRepresentative q) •
          f (torusWholePlaneRepresentative q) := by
  have hrestrict := wholePlaneToTorusL2_coe_ae
    (outputCutoffMulL2 p R hR f)
  have hmul :
      (outputCutoffMulL2 p R hR f : WholePlane → C3) =ᵐ[
        volume.restrict wholePlaneFundamentalBox]
        fun x ↦ outputCutoffComplex p R hR x • f x :=
    (outputCutoffMulL2_coe_ae p R hR f).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hpull := measurePreserving_torusWholePlaneRepresentative
    |>.quasiMeasurePreserving |>.ae_eq_comp hmul
  exact hrestrict.trans (by simpa [Function.comp_def] using hpull)

end TorusChartL2

end

end FastDynamo
