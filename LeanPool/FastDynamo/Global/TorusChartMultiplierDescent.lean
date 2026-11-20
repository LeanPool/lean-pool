/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.DomainOperatorClosedRangeAdjoint
public import LeanPool.FastDynamo.Global.TorusCellAxialPlateauBridge
public import LeanPool.FastDynamo.Global.TorusCellSeedCoefficientBridge
public import LeanPool.FastDynamo.Global.ReducedInductionEnergyIdentity
public import LeanPool.FastDynamo.Global.TorusFullVelocityConcrete
public import LeanPool.FastDynamo.Global.WholePlaneAESupport

/-!
# Multiplication and diffusion through the supported torus chart

This module supplies the quotient-safe atoms that turn coefficient agreement on a set into an
operator identity through the chart `wholePlaneToTorusL2`:

* scalar and vector multipliers commute with chart descent when the periodic and whole-plane
  coefficients agree almost everywhere on a set containing the support of the whole-plane input
  (`scalarVectorMulTransverse_wholePlaneToTorusL2_eq`,
  `vectorScalarMulTransverse_wholePlaneToTorusL2_eq`), also up to an added constant, as for
  the constant axial plateau (`scalarVectorMulTransverse_wholePlaneToTorusL2_eq_add_const`);
* the periodic and whole-plane fixed-mode diffusions commute exactly through the supported `H²`
  chart (`reducedInductionDiffusion_wholePlaneChartToTransverseH2`).

No pointwise representative of an arbitrary `H²` class is chosen: every comparison is made after
descent to `L²`.  `Global/TorusChartActionBridge.lean` assembles these atoms into the
coefficient agreement of the proof of `lem:parametrix-error`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace TorusChartMultiplierDescent

open ScaleFamily.TorusCellPlacement
open ScaleFamily.TorusCellPlacement.EuclideanCellSourceCertificate
open ScaleFamily.TorusCellPlacement.FullVelocityConcrete
open TorusChartH2
open TorusChartL2
open WholePlaneAESupport

/-! ## Quotient-safe multiplication through the chart -/

/-- Scalar multiplication commutes with chart descent when the two scalar
coefficients agree on the support of the whole-plane input. -/
theorem scalarVectorMulTransverse_wholePlaneToTorusL2_eq
    {s : Set WholePlane} {aT : TransverseScalarLInf}
    {aW : WholePlaneScalarLInf} {f : WholePlaneC3L2}
    (ha : ∀ᵐ q ∂transverseMeasure,
      torusWholePlaneRepresentative q ∈ s →
        (aT : TransverseTorus → ℂ) q =
          (aW : WholePlane → ℂ) (torusWholePlaneRepresentative q))
    (hf : IsAEL2SupportedIn s f) :
    scalarVectorMulTransverse aT (wholePlaneToTorusL2 f) =
      wholePlaneToTorusL2
        (scalarVectorMulL2 (E := C3) volume aW f) := by
  apply Lp.ext
  have hfRestrict :
      ∀ᵐ x ∂volume.restrict wholePlaneFundamentalBox,
        x ∉ s → (f : WholePlane → C3) x = 0 :=
    hf.filter_mono (ae_mono Measure.restrict_le_self)
  have hfChart :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae
      hfRestrict
  have hmulW := scalarVectorMulL2_coe_ae
    (E := C3) volume aW f
  have hmulWRestrict :
      ((scalarVectorMulL2 (E := C3) volume aW f : WholePlane → C3))
        =ᵐ[volume.restrict wholePlaneFundamentalBox]
          fun x ↦ (aW : WholePlane → ℂ) x • (f : WholePlane → C3) x :=
    hmulW.filter_mono (ae_mono Measure.restrict_le_self)
  have hmulWChart :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
      hmulWRestrict
  filter_upwards [scalarVectorMulTransverse_coe_ae aT
      (wholePlaneToTorusL2 f),
    wholePlaneToTorusL2_coe_ae f,
    wholePlaneToTorusL2_coe_ae
      (scalarVectorMulL2 (E := C3) volume aW f),
    ha, hfChart, hmulWChart] with q hleft hfq hright hagree hsupport hmul
  rw [hleft, hfq, hright]
  rw [show
    (scalarVectorMulL2 (E := C3) volume aW f : WholePlane → C3)
        (torusWholePlaneRepresentative q) =
      (aW : WholePlane → ℂ) (torusWholePlaneRepresentative q) •
        (f : WholePlane → C3) (torusWholePlaneRepresentative q) by
    simpa only [Function.comp_apply] using hmul]
  by_cases hqs : torusWholePlaneRepresentative q ∈ s
  · rw [hagree hqs]
  · rw [show (f : WholePlane → C3) (torusWholePlaneRepresentative q) = 0 by
      simpa only [Function.comp_apply] using hsupport hqs]
    simp

/-- Vector-times-coordinate multiplication commutes with chart descent under
the analogous vector-coefficient agreement. -/
theorem vectorScalarMulTransverse_wholePlaneToTorusL2_eq
    {s : Set WholePlane} {aT : TransverseC3LInf}
    {aW : WholePlaneC3LInf} {f : WholePlaneC3L2} (i : Fin 3)
    (ha : ∀ᵐ q ∂transverseMeasure,
      torusWholePlaneRepresentative q ∈ s →
        (aT : TransverseTorus → C3) q =
          (aW : WholePlane → C3) (torusWholePlaneRepresentative q))
    (hf : IsAEL2SupportedIn s f) :
    vectorScalarMulTransverse aT
        (transverseCoordL2 i (wholePlaneToTorusL2 f)) =
      wholePlaneToTorusL2
        (vectorScalarMulL2 (E := C3) volume aW
          (wholePlaneCoordL2 i f)) := by
  apply Lp.ext
  have hfRestrict :
      ∀ᵐ x ∂volume.restrict wholePlaneFundamentalBox,
        x ∉ s → (f : WholePlane → C3) x = 0 :=
    hf.filter_mono (ae_mono Measure.restrict_le_self)
  have hfChart :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae
      hfRestrict
  have hmulW := vectorScalarMulL2_coe_ae
    (E := C3) volume aW (wholePlaneCoordL2 i f)
  have hmulWRestrict :
      ((vectorScalarMulL2 (E := C3) volume aW
        (wholePlaneCoordL2 i f) : WholePlane → C3))
        =ᵐ[volume.restrict wholePlaneFundamentalBox]
          fun x ↦ (wholePlaneCoordL2 i f : WholePlane → ℂ) x •
            (aW : WholePlane → C3) x :=
    hmulW.filter_mono (ae_mono Measure.restrict_le_self)
  have hmulWChart :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
      hmulWRestrict
  have hcoordWRestrict :
      ((wholePlaneCoordL2 i f : WholePlane → ℂ))
        =ᵐ[volume.restrict wholePlaneFundamentalBox]
          fun x ↦ (f : WholePlane → C3) x i :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL f).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hcoordWChart :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
      hcoordWRestrict
  filter_upwards [vectorScalarMulTransverse_coe_ae aT
      (transverseCoordL2 i (wholePlaneToTorusL2 f)),
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (wholePlaneToTorusL2 f),
    wholePlaneToTorusL2_coe_ae f,
    wholePlaneToTorusL2_coe_ae
      (vectorScalarMulL2 (E := C3) volume aW
        (wholePlaneCoordL2 i f)),
    ha, hfChart, hmulWChart, hcoordWChart] with q hleft hcoordT hfq hright
      hagree hsupport hmul hcoordW
  change (transverseCoordL2 i (wholePlaneToTorusL2 f) :
      TransverseTorus → ℂ) q =
    (wholePlaneToTorusL2 f : TransverseTorus → C3) q i at hcoordT
  rw [hleft, hcoordT, hfq, hright]
  change ((f : WholePlane → C3) (torusWholePlaneRepresentative q)) i •
      (aT : TransverseTorus → C3) q = _
  rw [show
    (vectorScalarMulL2 (E := C3) volume aW
        (wholePlaneCoordL2 i f) : WholePlane → C3)
          (torusWholePlaneRepresentative q) =
      ((f : WholePlane → C3) (torusWholePlaneRepresentative q)) i •
        (aW : WholePlane → C3) (torusWholePlaneRepresentative q) by
    rw [show
      (vectorScalarMulL2 (E := C3) volume aW
        (wholePlaneCoordL2 i f) : WholePlane → C3)
          (torusWholePlaneRepresentative q) =
        (wholePlaneCoordL2 i f : WholePlane → ℂ)
            (torusWholePlaneRepresentative q) •
          (aW : WholePlane → C3) (torusWholePlaneRepresentative q) by
          simpa only [Function.comp_apply] using hmul]
    rw [show
      (wholePlaneCoordL2 i f : WholePlane → ℂ)
          (torusWholePlaneRepresentative q) =
        ((f : WholePlane → C3) (torusWholePlaneRepresentative q)) i by
          simpa only [Function.comp_apply] using hcoordW]]
  by_cases hqs : torusWholePlaneRepresentative q ∈ s
  · rw [hagree hqs]
  · rw [show (f : WholePlane → C3) (torusWholePlaneRepresentative q) = 0 by
      simpa only [Function.comp_apply] using hsupport hqs]
    simp

/-- Shifted scalar version used for the constant axial plateau.  The
constant is kept outside the compactly supported whole-plane coefficient
package because the local operator realizes it separately as a scalar
shift. -/
theorem scalarVectorMulTransverse_wholePlaneToTorusL2_eq_add_const
    {s : Set WholePlane} {aT : TransverseScalarLInf}
    {aW : WholePlaneScalarLInf} {f : WholePlaneC3L2} (c : ℂ)
    (ha : ∀ᵐ q ∂transverseMeasure,
      torusWholePlaneRepresentative q ∈ s →
        (aT : TransverseTorus → ℂ) q =
          (aW : WholePlane → ℂ) (torusWholePlaneRepresentative q) + c)
    (hf : IsAEL2SupportedIn s f) :
    scalarVectorMulTransverse aT (wholePlaneToTorusL2 f) =
      wholePlaneToTorusL2
          (scalarVectorMulL2 (E := C3) volume aW f) +
        c • wholePlaneToTorusL2 f := by
  apply Lp.ext
  have hfRestrict :
      ∀ᵐ x ∂volume.restrict wholePlaneFundamentalBox,
        x ∉ s → (f : WholePlane → C3) x = 0 :=
    hf.filter_mono (ae_mono Measure.restrict_le_self)
  have hfChart :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae
      hfRestrict
  have hmulWRestrict :
      ((scalarVectorMulL2 (E := C3) volume aW f : WholePlane → C3))
        =ᵐ[volume.restrict wholePlaneFundamentalBox]
          fun x ↦ (aW : WholePlane → ℂ) x • (f : WholePlane → C3) x :=
    (scalarVectorMulL2_coe_ae (E := C3) volume aW f).filter_mono
      (ae_mono Measure.restrict_le_self)
  have hmulWChart :=
    measurePreserving_torusWholePlaneRepresentative.quasiMeasurePreserving.ae_eq_comp
      hmulWRestrict
  filter_upwards [scalarVectorMulTransverse_coe_ae aT
      (wholePlaneToTorusL2 f),
    wholePlaneToTorusL2_coe_ae f,
    wholePlaneToTorusL2_coe_ae
      (scalarVectorMulL2 (E := C3) volume aW f),
    Lp.coeFn_add
      (wholePlaneToTorusL2
        (scalarVectorMulL2 (E := C3) volume aW f))
      (c • wholePlaneToTorusL2 f),
    Lp.coeFn_smul c (wholePlaneToTorusL2 f),
    ha, hfChart, hmulWChart] with q hleft hfq hlocal hadd hsmul
      hagree hsupport hmul
  rw [hleft, hfq, hadd]
  simp only [Pi.add_apply]
  rw [hlocal, hsmul]
  simp only [Pi.smul_apply]
  rw [hfq]
  rw [show
    (scalarVectorMulL2 (E := C3) volume aW f : WholePlane → C3)
        (torusWholePlaneRepresentative q) =
      (aW : WholePlane → ℂ) (torusWholePlaneRepresentative q) •
        (f : WholePlane → C3) (torusWholePlaneRepresentative q) by
          simpa only [Function.comp_apply] using hmul]
  by_cases hqs : torusWholePlaneRepresentative q ∈ s
  · rw [hagree hqs]
    module
  · rw [show (f : WholePlane → C3) (torusWholePlaneRepresentative q) = 0 by
      simpa only [Function.comp_apply] using hsupport hqs]
    simp

/-! ## Diffusion through the chart -/

/-- Periodic and whole-plane fixed-mode diffusion commute exactly through
the supported `H²` chart. -/
theorem reducedInductionDiffusion_wholePlaneChartToTransverseH2
    (K : ℤ) (b : ChartSupportedWholePlaneC3H2) :
    reducedInductionDiffusion K (wholePlaneChartToTransverseH2 b) =
      wholePlaneToTorusL2
        (wholePlaneLocalDiffusion (wholePlaneAxialWavenumber K) b.1) := by
  rw [reducedInductionDiffusion_apply, wholePlaneLocalDiffusion_apply,
    transverseLaplacianFromH2_wholePlaneChartToTransverseH2,
    chartLaplacianL2_eq_wholePlaneLaplacian,
    transverseH2Embedding_wholePlaneChartToTransverseH2]
  simp only [chartValueL2_apply, map_sub, map_smul]
  congr 2
  simp [wholePlaneAxialWavenumber]

end TorusChartMultiplierDescent

end

end FastDynamo
