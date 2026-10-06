/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.UniformRelativeBound
public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormSerrin
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeEnergyAssembly
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinEstimate

/-!
# Relative convection on almost every slice

The finite Serrin assumption and the weak slice properties put the relative
convection into the fixed-time Hölder, interpolation, and Young estimate.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The finite Serrin branch supplies the fixed-time relative convection
estimate on almost every slice, with a coefficient independent of time. -/
theorem lps_finite_relative_convection_bound_ae
    {T s : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x, t)) ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x, t)) +
        (lps_power_young_coefficient (3 / s) *
          (9 * ((6 : ℝ) * gagliardoNirenbergSobolevConstant.toReal) ^ (3 / s)) ^
            (2 * s / (s - 3))) *
          (eLpNorm (fun x : Vec3 =>
            vec3EuclideanNorm (u (x, t))) (ENNReal.ofReal s) volume).toReal ^
              (2 * s / (s - 3)) *
          lpsComparisonDistanceSq u v t := by
  have hSlices := serrinWeak_slices_ae hU
  have hRiesz := lps_finite_branch_slice_memLp_ae hU.meas_u hs hmix
  filter_upwards [hSlices, serrinWeak_slices_ae hV, hRiesz] with t hu hv huS
  obtain ⟨hu2, hDu2, hug, -, -⟩ := hu
  obtain ⟨hv2, hDv2, hvg, -, -⟩ := hv
  have hw2 : MemLp (fun x : Vec3 => v (x, t) - u (x, t)) 2 volume := hv2.sub hu2
  have hDw2 : MemLp (fun x : Vec3 => Dv (x, t) - Du (x, t)) 2 volume :=
    hDv2.sub hDu2
  have hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x : Vec3 => (v (x, t) - u (x, t)) i)
      (fun x : Vec3 => (Dv (x, t) - Du (x, t)) i) := by
    intro i j
    exact serrin_weakPartialDeriv_sub (hv2.eval i) (hu2.eval i)
      ((hDv2.eval i).eval j) ((hDu2.eval i).eval j) (hvg i j) (hug i j)
  have hfixed := lps_slice_relative_bound_finite_uniform hs
    (u := fun x => u (x, t)) (w := fun x => v (x, t) - u (x, t))
    (Dw := fun x => Dv (x, t) - Du (x, t))
    hu2.aestronglyMeasurable huS hw2 hDw2 hgrad
  have hfixed' :
      |∫ x : Vec3, lpsRelativeConvection u v Du Dv (x, t)| ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x, t)) +
        (lps_power_young_coefficient (3 / s) *
          (9 * ((6 : ℝ) * gagliardoNirenbergSobolevConstant.toReal) ^ (3 / s)) ^
            (2 * s / (s - 3))) *
          (eLpNorm (fun x : Vec3 =>
            vec3EuclideanNorm (u (x, t))) (ENNReal.ofReal s) volume).toReal ^
              (2 * s / (s - 3)) *
          lpsComparisonDistanceSq u v t := by
    simpa only [lpsRelativeConvection, lpsRelativeGradientSq,
      lpsComparisonDistanceSq, Pi.sub_apply] using hfixed
  exact (le_abs_self _).trans hfixed'

end ESS

end
