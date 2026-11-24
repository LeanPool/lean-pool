/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.FullSpaceClosedBallDomains
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Jacobian transport on a full-space regular closed ball

The parameterization of a regular patch of a full-dimensional subvariety is a
biholomorphism on its literal parameter domain.  Intersecting its image with a
coordinate neighbourhood for a smooth potential gives an honest source and
range for the local change-of-variables formula.  This file supplies that
geometric and measure-theoretic transport; it deliberately stops before the
separate identification of the transported smooth density with the global
non-pluripolar patch measure.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.FullSpaceClosedBallTransport

open FirstPass FirstPass.NumericalRestrictedVolume
  FirstPass.AdmissibleCurrentFormPositivity
open FullSpaceRegularPatch FullSpaceClosedBallDomains BedfordTaylor

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The full-space regular-patch coordinate parametrization with its ambient
source type made explicit.  The definition unfolds the certified equality of
the subvariety dimension with `n` once, so Jacobian APIs never have to solve
that reduction implicitly. -/
def fullSpaceCoordinateParametrization
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) :
    ComplexModel n → ComplexModel n := fun w => P.coordinateParametrization w

@[simp] theorem fullSpaceCoordinateParametrization_apply
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) (w : ComplexModel n) :
    fullSpaceCoordinateParametrization P w = P.coordinateParametrization w := rfl

/-- The explicit ambient-typed parametrization has the same biholomorphic
certificate as the original regular-patch map. -/
theorem fullSpaceCoordinateParametrization_isBiholomorphic
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim)) :
    IsBiholomorphicPair (fullParameterDomain P) (flatteningSource P)
      (fullSpaceCoordinateParametrization P) P.flattening.toFun := by
  let h := coordinateParametrization_isBiholomorphic P
  refine ⟨?_, h.holo_inv, ?_, h.mapsTo_inv, ?_, ?_⟩
  · change ContDiffOn ℂ ∞ (fun w : ComplexModel n => P.coordinateParametrization w)
      (fullParameterDomain P : Set (ComplexModel n))
    exact h.holo
  · intro w hw
    change P.coordinateParametrization w ∈ (flatteningSource P : Set (ComplexModel n))
    exact h.mapsTo hw
  · intro w hw
    change P.flattening.toFun (P.coordinateParametrization w) = w
    exact h.left_inv w hw
  · intro z hz
    change P.coordinateParametrization (P.flattening.toFun z) = z
    exact h.right_inv z hz

/-- Restricting the full-dimensional patch parametrization to the parameters
whose image lies in `U` maps onto exactly `U ∩ flatteningSource`. -/
theorem coordinateParametrization_image_regularParameterDomain
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) :
    fullSpaceCoordinateParametrization P '' (regularParameterDomain P U : Set (ComplexModel n)) =
      (regularPotentialDomain P U : Set (ComplexModel n)) := by
  let h := fullSpaceCoordinateParametrization_isBiholomorphic P
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hwA, hwU⟩ := (mem_regularParameterDomain_iff P U w).mp hw
    exact ⟨hwU, h.mapsTo hwA⟩
  · intro hz
    refine ⟨P.flattening.toFun z, ?_, h.right_inv z hz.2⟩
    apply (mem_regularParameterDomain_iff P U (P.flattening.toFun z)).mpr
    refine ⟨h.mapsTo_inv hz.2, ?_⟩
    change fullSpaceCoordinateParametrization P (P.flattening.toFun z) ∈ (U : Set (ComplexModel n))
    rw [h.right_inv z hz.2]
    exact hz.1

/-- The full-space parametrization remains injective after restricting to the
local-potential parameter domain. -/
theorem coordinateParametrization_injOn_regularParameterDomain
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) :
    InjOn (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n)) := by
  let h := fullSpaceCoordinateParametrization_isBiholomorphic P
  intro x hx y hy hxy
  have hxA : x ∈ fullParameterDomain P :=
    (mem_regularParameterDomain_iff P U x).mp hx |>.1
  have hyA : y ∈ fullParameterDomain P :=
    (mem_regularParameterDomain_iff P U y).mp hy |>.1
  calc
    x = P.flattening.toFun (fullSpaceCoordinateParametrization P x) := (h.left_inv x hxA).symm
    _ = P.flattening.toFun (fullSpaceCoordinateParametrization P y) :=
      congrArg P.flattening.toFun hxy
    _ = y := h.left_inv y hyA

/-- Every point of the parameter-potential intersection has a closed
coordinate ball contained in it.  This is the compact piece on which the
Jacobian formula can be applied. -/
theorem exists_closedBall_subset_regularParameterDomain
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {w : ComplexModel n}
    (hw : w ∈ regularParameterDomain P U) :
    ∃ r > 0, closedBall w r ⊆ (regularParameterDomain P U : Set (ComplexModel n)) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (regularParameterDomain P U).isOpen w hw
  refine ⟨r / 2, half_pos hr, ?_⟩
  exact (closedBall_subset_ball (by linarith)).trans hsub

section Jacobian

/-- On every measurable compact parameter piece contained in the literal
biholomorphic domain, the coordinate image integral is exactly the real
Jacobian-weighted parameter integral.  This is the genuine mathlib
change-of-variables theorem, with the differentiability and injectivity
premises supplied by the full-space regular patch. -/
theorem lintegral_coordinateImage_eq_lintegral_abs_det_fderiv_mul
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {K : Set (ComplexModel n)}
    (hK : MeasurableSet K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    (g : ComplexModel n → ℝ≥0∞) :
    ∫⁻ z in fullSpaceCoordinateParametrization P '' K, g z ∂volume =
      ∫⁻ w in K,
        ENNReal.ofReal |(fderiv ℝ (fullSpaceCoordinateParametrization P) w).det| *
          g (fullSpaceCoordinateParametrization P w) ∂volume := by
  let h := fullSpaceCoordinateParametrization_isBiholomorphic P
  have hKA : K ⊆ (fullParameterDomain P : Set (ComplexModel n)) := fun w hw =>
    (mem_regularParameterDomain_iff P U w).mp (hKU hw) |>.1
  have hderiv : ∀ w ∈ K,
      HasFDerivWithinAt (fullSpaceCoordinateParametrization P)
        (fderiv ℝ (fullSpaceCoordinateParametrization P) w) K w := by
    intro w hw
    exact ((((h.holo.restrict_scalars ℝ) w (hKA hw)).contDiffAt
      ((fullParameterDomain P).isOpen.mem_nhds (hKA hw))).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn (fullSpaceCoordinateParametrization P) K := fun x hx y hy hxy =>
    coordinateParametrization_injOn_regularParameterDomain P U (hKU hx) (hKU hy) hxy
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK hderiv hinj g

/-- The coordinate image of a closed ball contained in the parameter-potential
intersection is measurable.  Thus it is admissible as the measurable image
piece in the subsequent `withDensity` calculation. -/
theorem measurableSet_coordinateImage_closedBall
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) (w : ComplexModel n) {r : ℝ}
    (hball : closedBall w r ⊆ (regularParameterDomain P U : Set (ComplexModel n))) :
    MeasurableSet (fullSpaceCoordinateParametrization P '' closedBall w r) := by
  let h := fullSpaceCoordinateParametrization_isBiholomorphic P
  exact ((isCompact_closedBall w r).image_of_continuousOn
    (h.holo.continuousOn.mono fun x hx =>
      (mem_regularParameterDomain_iff P U x).mp (hball hx) |>.1)).measurableSet

/-- Holomorphic covariance identifies the Jacobian-weighted ambient smooth
density with the ordinary smooth density of the pulled-back potential.  This
is the density equality needed to turn the change-of-variables formula into a
parameter-side top-power integral. -/
theorem jacobian_smoothDensity_eq_smoothDensity_comp_coordinateParametrization
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n))
    {f : ComplexModel n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (regularPotentialDomain P U))
    {w : ComplexModel n} (hw : w ∈ regularParameterDomain P U) :
    ENNReal.ofReal |(fderiv ℝ (fullSpaceCoordinateParametrization P) w).det| *
        ENNReal.ofReal (FirstPass.MongeAmpere.smoothDensity f
          (fullSpaceCoordinateParametrization P w)) =
      ENNReal.ofReal (FirstPass.MongeAmpere.smoothDensity
        (fun x => f (fullSpaceCoordinateParametrization P x)) w) := by
  let h := fullSpaceCoordinateParametrization_isBiholomorphic P
  have hsub : (regularParameterDomain P U : Set (ComplexModel n)) ⊆
      (fullParameterDomain P : Set (ComplexModel n)) := fun x hx =>
    (mem_regularParameterDomain_iff P U x).mp hx |>.1
  have hmap : MapsTo (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n))
      (regularPotentialDomain P U : Set (ComplexModel n)) := fun x hx => by
    obtain ⟨hxA, hxU⟩ := (mem_regularParameterDomain_iff P U x).mp hx
    exact ⟨hxU, h.mapsTo hxA⟩
  have hτ : ContDiffOn ℂ ∞ (fullSpaceCoordinateParametrization P)
      (regularParameterDomain P U : Set (ComplexModel n)) := h.holo.mono hsub
  have hcomp : FirstPass.MongeAmpere.smoothDensity
      (fun x => f (fullSpaceCoordinateParametrization P x)) w =
      Complex.normSq (HolomorphicMixedDensity.jacobianMatrix (fullSpaceCoordinateParametrization
        P) w).det *
        FirstPass.MongeAmpere.smoothDensity f (fullSpaceCoordinateParametrization P w) := by
    simpa using
      HolomorphicMixedDensity.mixedDensity_comp_holomorphic
        (regularParameterDomain P U).isOpen (regularPotentialDomain P U).isOpen hτ
        (fun _ => hf) hmap hw
  have hdiff : DifferentiableAt ℂ (fullSpaceCoordinateParametrization P) w :=
    ((hτ w hw).contDiffAt ((regularParameterDomain P U).isOpen.mem_nhds hw)).differentiableAt
      (by simp)
  rw [HolomorphicMixedDensity.det_fderiv_eq_normSq hdiff,
    abs_of_nonneg (Complex.normSq_nonneg _),
    ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), ← hcomp]

/-- The preceding Jacobian identity is also the literal evaluation formula for
`FirstPass.MongeAmpere.smoothMeasure` on the coordinate image.  The only
measure simplification used here is that this image lies in the open domain of
the smooth potential. -/
theorem smoothMeasure_coordinateImage_eq_lintegral_jacobian
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {K : Set (ComplexModel n)}
    (hK : IsCompact K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    {f : ComplexModel n → ℝ}
    (hf : FirstPass.MongeAmpere.IsSmoothPshOn (regularPotentialDomain P U) f) :
    FirstPass.MongeAmpere.smoothMeasure (regularPotentialDomain P U) f hf
        (fullSpaceCoordinateParametrization P '' K) =
      ∫⁻ w in K,
        ENNReal.ofReal |(fderiv ℝ (fullSpaceCoordinateParametrization P) w).det| *
          ENNReal.ofReal (FirstPass.MongeAmpere.smoothDensity f
            (fullSpaceCoordinateParametrization P w)) ∂volume := by
  let h := fullSpaceCoordinateParametrization_isBiholomorphic P
  have himage : MeasurableSet (fullSpaceCoordinateParametrization P '' K) := by
    exact (hK.image_of_continuousOn
      (h.holo.continuousOn.mono fun w hw =>
        (mem_regularParameterDomain_iff P U w).mp (hKU hw) |>.1)).measurableSet
  have himageU : fullSpaceCoordinateParametrization P '' K ⊆
      (regularPotentialDomain P U : Set (ComplexModel n)) := by
    rintro z ⟨w, hw, rfl⟩
    obtain ⟨hwA, hwU⟩ := (mem_regularParameterDomain_iff P U w).mp (hKU hw)
    exact ⟨hwU, h.mapsTo hwA⟩
  unfold FirstPass.MongeAmpere.smoothMeasure
  calc
    _ = ∫⁻ z in fullSpaceCoordinateParametrization P '' K,
        ENNReal.ofReal (FirstPass.MongeAmpere.smoothDensity f z) ∂
          (volume.restrict (regularPotentialDomain P U : Set (ComplexModel n))) := by
      exact @MeasureTheory.withDensity_apply (ComplexModel n) _
        (volume.restrict (regularPotentialDomain P U : Set (ComplexModel n)))
        (fun z => ENNReal.ofReal (FirstPass.MongeAmpere.smoothDensity f z))
        (fullSpaceCoordinateParametrization P '' K) himage
    _ = ∫⁻ z in fullSpaceCoordinateParametrization P '' K,
        ENNReal.ofReal (FirstPass.MongeAmpere.smoothDensity f z) ∂volume := by
      rw [Measure.restrict_restrict_of_subset himageU]
    _ = _ := lintegral_coordinateImage_eq_lintegral_abs_det_fderiv_mul P U hK.measurableSet hKU
      (fun z => ENNReal.ofReal (FirstPass.MongeAmpere.smoothDensity f z))

/-- Combining `withDensity` evaluation with holomorphic density covariance,
the smooth mass of the coordinate image of a compact regular parameter piece
is exactly the smooth top-density integral of the pulled-back potential. -/
theorem smoothMeasure_coordinateImage_eq_lintegral_smoothDensity_comp
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {hcarrier : V.carrier = univ} {hdim : V.dim = n}
    (P : RegularPatch (fullSpaceSubvariety V hcarrier hdim))
    (U : Opens (ComplexModel n)) {K : Set (ComplexModel n)}
    (hK : IsCompact K)
    (hKU : K ⊆ (regularParameterDomain P U : Set (ComplexModel n)))
    {f : ComplexModel n → ℝ}
    (hf : FirstPass.MongeAmpere.IsSmoothPshOn (regularPotentialDomain P U) f) :
    FirstPass.MongeAmpere.smoothMeasure (regularPotentialDomain P U) f hf
        (fullSpaceCoordinateParametrization P '' K) =
      ∫⁻ w in K,
        ENNReal.ofReal (FirstPass.MongeAmpere.smoothDensity
          (fun x => f (fullSpaceCoordinateParametrization P x)) w) ∂volume := by
  refine (smoothMeasure_coordinateImage_eq_lintegral_jacobian P U hK hKU hf).trans ?_
  refine setLIntegral_congr_fun hK.measurableSet fun w hw => ?_
  exact jacobian_smoothDensity_eq_smoothDensity_comp_coordinateParametrization P U hf.1
    (hKU hw)

end Jacobian

end SGPT.Foundations.Analysis.Pending.FullSpaceClosedBallTransport
