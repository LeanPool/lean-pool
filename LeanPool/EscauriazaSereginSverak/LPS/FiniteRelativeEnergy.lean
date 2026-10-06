/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedCrossFiniteRelative
public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormSerrin
public import LeanPool.EscauriazaSereginSverak.LPS.RelativeEnergyAssembly
public import LeanPool.EscauriazaSereginSverak.LPS.SerrinSliceRelativeBound
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinGronwallInputs
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinLerayHopf

/-!
# Relative energy for a finite Serrin distinguished solution

The distinguished solution's a.e. energy equality enters as an explicit
hypothesis, matching the provider in `EnergyEquality`. The competitor uses
only the Leray--Hopf energy inequality.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The relative gradient square is integrable on the full time slab for two
Leray--Hopf velocity fields. -/
theorem lps_relative_gradient_sq_integrable
    {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T b v Dv pv) :
    Integrable (lpsRelativeGradientSq Du Dv)
      (volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))) := by
  let μT : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet Set.univ (Ioo 0 T))
  have hDu2 := serrinWeak_gradient_memLp_two hU
  have hDv2 := serrinWeak_gradient_memLp_two hV
  have hDiff2 : MemLp (fun z : ParabolicPoint => Dv z - Du z) 2 μT :=
    hDv2.sub hDu2
  have hcoord (k j : Fin 3) : Integrable
      (fun z : ParabolicPoint => (Dv z k j - Du z k j) ^ 2) μT := by
    have hmem := (hDiff2.eval k).eval j
    have hsq := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
    exact hsq.congr (Eventually.of_forall fun z => by simp)
  have hsum : Integrable
      (fun z : ParabolicPoint =>
        ∑ k : Fin 3, ∑ j : Fin 3, (Dv z k j - Du z k j) ^ 2) μT :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hcoord k j
  exact hsum.congr (Eventually.of_forall fun z => by
    simp [lpsRelativeGradientSq])

/-- The finite Serrin cross identity, the distinguished energy equality, the
competitor energy inequality, and the exponent-general slice bound imply that
the two solutions have zero relative energy almost everywhere. The a.e.
energy-equality premise is deliberately explicit; `lem:lps-energy-equality` supplies it. -/
theorem lps_finite_relative_energy_zero
    {T s : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hULH : IsLerayHopfSolution T a u Du)
    (hVLH : IsLerayHopfSolution T a v Dv)
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤)
    (hEnergyEquality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ z in spaceTimeSet Set.univ (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t = 0 := by
  let ell : ℝ := 2 * s / (s - 3)
  let m : ℝ → ℝ := fun t =>
    (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal s) volume).toReal ^ ell
  let K : ℝ := lpsPowerYoungCoefficient (3 / s) *
    (9 * ((6 : ℝ) * gagliardoNirenbergSobolevConstant.toReal) ^ (3 / s)) ^ ell
  have hs0 : 0 < s := by linarith only [hs]
  have hθ0 : 0 < 3 / s := div_pos (by norm_num) hs0
  have hθ1 : 3 / s < 1 := by
    rw [div_lt_one hs0]
    linarith only [hs]
  have hell : ell = 2 * s / (s - 3) := rfl
  have hK : 0 ≤ K := by
    dsimp [K, ell]
    unfold lpsPowerYoungCoefficient
    positivity
  have hCrossPack := lps_finite_relative_cross_identity
    hULH hVLH hU hV hs hmix
  have hRelativeCross := hCrossPack.1
  have hC := hCrossPack.2
  have hSliceBound : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x,τ)) ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x,τ)) +
        K * (m τ * lpsComparisonDistanceSq u v τ) := by
    have hBound := lps_finite_relative_convection_bound_ae hU hV hs hmix
    simpa only [m, K, hell, mul_assoc, lpsComparisonDistanceSq,
      lpsRelativeConvection, lpsRelativeGradientSq] using hBound
  have hGradient := lps_relative_gradient_sq_integrable hU hV
  obtain ⟨Bu, hBu⟩ := serrinWeak_slice_energy_bound hU
  obtain ⟨Bv, hBv⟩ := serrinWeak_slice_energy_bound hV
  have hDistanceBound : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t ≤ 2 * Bu + 2 * Bv := by
    filter_upwards [hBu, hBv, serrinWeak_slices_ae hU, serrinWeak_slices_ae hV]
      with t hBu_t hBv_t hu hv
    have hu2 := hu.1
    have hv2 := hv.1
    have hUsq : Integrable (fun x : Vec3 => ∑ k : Fin 3, u (x, t) k ^ 2) volume :=
      integrable_finsetSum _ fun k _ =>
        ((hu2.eval k).integrable_mul (hu2.eval k)).congr
          (Eventually.of_forall fun x => by simp [pow_two])
    have hVsq : Integrable (fun x : Vec3 => ∑ k : Fin 3, v (x, t) k ^ 2) volume :=
      integrable_finsetSum _ fun k _ =>
        ((hv2.eval k).integrable_mul (hv2.eval k)).congr
          (Eventually.of_forall fun x => by simp [pow_two])
    have hRhsInt : Integrable (fun x : Vec3 =>
        2 * (∑ k : Fin 3, v (x, t) k ^ 2) +
          2 * (∑ k : Fin 3, u (x, t) k ^ 2)) volume :=
      (hVsq.const_mul 2).add (hUsq.const_mul 2)
    have hPoint (x : Vec3) :
        (∑ k : Fin 3, (v (x, t) k - u (x, t) k) ^ 2) ≤
          2 * (∑ k : Fin 3, v (x, t) k ^ 2) +
            2 * (∑ k : Fin 3, u (x, t) k ^ 2) := by
      calc
        _ ≤ ∑ k : Fin 3,
            (2 * v (x, t) k ^ 2 + 2 * u (x, t) k ^ 2) :=
          Finset.sum_le_sum fun k _ => by
            nlinarith only [sq_nonneg (v (x, t) k + u (x, t) k)]
        _ = (∑ k : Fin 3, 2 * v (x, t) k ^ 2) +
              ∑ k : Fin 3, 2 * u (x, t) k ^ 2 := Finset.sum_add_distrib
        _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
    have hIntegral := integral_mono_of_nonneg
      (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ => sq_nonneg _)
      hRhsInt (Eventually.of_forall hPoint)
    have hExpand :
        (∫ x : Vec3, 2 * (∑ k : Fin 3, v (x, t) k ^ 2) +
          2 * (∑ k : Fin 3, u (x, t) k ^ 2)) =
          2 * (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k ^ 2) +
            2 * (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k ^ 2) := by
      rw [integral_add (hVsq.const_mul 2) (hUsq.const_mul 2),
        integral_const_mul, integral_const_mul]
    change (∫ x : Vec3, ∑ k : Fin 3,
      (v (x, t) k - u (x, t) k) ^ 2) ≤ 2 * Bu + 2 * Bv
    rw [hExpand] at hIntegral
    calc
      _ ≤ 2 * (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k ^ 2) +
          2 * (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k ^ 2) := hIntegral
      _ ≤ 2 * Bv + 2 * Bu := by gcongr
      _ = 2 * Bu + 2 * Bv := by ring
  have hDistanceMeas := serrin_distance_aestronglyMeasurable hU hV
  have hE_nonneg (t : ℝ) : 0 ≤ lpsComparisonDistanceSq u v t := by
    unfold lpsComparisonDistanceSq
    exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hDistanceBoundNorm : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ‖lpsComparisonDistanceSq u v t‖ ≤ 2 * Bu + 2 * Bv := by
    filter_upwards [hDistanceBound] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hE_nonneg t)]
    exact ht
  have hm : IntegrableOn m (Ioo 0 T) := by
    simpa [m, ell] using lps_finite_branch_time_moment_integrable
      hU.meas_u hs hmix
  have hmNonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ m t := by
    filter_upwards [] with t
    positivity
  have hmE : IntegrableOn
      (fun t => m t * lpsComparisonDistanceSq u v t) (Ioo 0 T) := by
    have hm' : Integrable m (volume.restrict (Ioo 0 T)) := by
      exact hm
    have hE' : AEStronglyMeasurable (lpsComparisonDistanceSq u v)
        (volume.restrict (Ioo 0 T)) := hDistanceMeas
    have hprod := hm'.mul_bdd hE' hDistanceBoundNorm
    exact hprod
  have hEnergyInequality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ z in spaceTimeSet Set.univ (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    have hSlices := (ae_restrict_iff' measurableSet_Ioo).mp (serrinWeak_slices_ae hV)
    filter_upwards [hSlices] with t ht htI
    exact lerayHopf_energy_inequality_real hVLH ⟨htI.1.le, htI.2.le⟩ (ht htI).1
  exact lps_relative_energy_zero_from_slice_bound hU hV hK
    hEnergyEquality hEnergyInequality hRelativeCross hSliceBound hC hGradient
    hm hmNonneg hmE

end ESS

end
