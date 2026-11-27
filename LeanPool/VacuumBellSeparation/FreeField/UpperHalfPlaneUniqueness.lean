/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PositiveEnergyLaplace

/-!
# Boundary uniqueness from actual complex derivatives on the closed half-plane

A zero boundary interval gives zero tangential derivative. Gluing the function
above the real axis to zero below therefore gives an actual holomorphic function
on the union of the upper half-plane and a vertical strip. The ordinary analytic
identity theorem proves uniqueness. No reflection or boundary uniqueness axiom
is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Set
open scoped Topology

/-- Upper zero extension defined as `if 0 ≤ z.im then F z else 0`. -/
noncomputable def upperZeroExtension (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then F z else 0

theorem HasDerivWithinAt.comp_ofReal_upper {F : ℂ → ℂ} {d : ℂ} {x : ℝ}
    (h : HasDerivWithinAt F d {z : ℂ | 0 ≤ z.im} (x : ℂ)) :
    HasDerivAt (fun t : ℝ => F (t : ℂ)) d x := by
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]
    using h.scomp_hasDerivAt x Complex.ofRealCLM.hasDerivAt (by intro t; simp)

theorem upper_derivative_eq_zero_of_boundary_zero
    {F : ℂ → ℂ} {d : ℂ} {x : ℝ}
    (h : HasDerivWithinAt F d {z : ℂ | 0 ≤ z.im} (x : ℂ))
    (hzero : (fun t : ℝ => F (t : ℂ)) =ᶠ[𝓝 x] 0) : d = 0 := by
  exact (HasDerivWithinAt.comp_ofReal_upper h).unique ((hasDerivAt_const x
    (0 : ℂ)).congr_of_eventuallyEq hzero)

theorem differentiableAt_upperZeroExtension
    {F D : ℂ → ℂ} {a b : ℝ}
    (hF : ∀ z, 0 ≤ z.im → HasDerivWithinAt F (D z) {w : ℂ | 0 ≤ w.im} z)
    (hzero : ∀ x ∈ Ioo a b, F (x : ℂ) = 0)
    {z : ℂ} (hz : 0 < z.im ∨ z.re ∈ Ioo a b) :
    DifferentiableAt ℂ (upperZeroExtension F) z := by
  by_cases hp : 0 < z.im
  · have hd := (hF z hp.le).hasDerivAt
      (Filter.mem_of_superset
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hp) (fun w
          (hw : 0 < w.im) => hw.le))
    apply (hd.congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hp] with w hw
    simp [upperZeroExtension, hw.le]
  by_cases hn : z.im < 0
  · apply ((hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hn] with w hw
    simp [upperZeroExtension, not_le.mpr hw]
  have hi : z.im = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
  have hr : z.re ∈ Ioo a b := hz.resolve_left hp
  have hzreal : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
  have hd0 : D z = 0 := by
    apply upper_derivative_eq_zero_of_boundary_zero
      (x := z.re) (by simpa only [hzreal] using hF z (by rw [hi]))
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact hzero t ht
  have hupper : HasDerivWithinAt (upperZeroExtension F) 0 {w : ℂ | 0 ≤ w.im} z := by
    apply ((hF z (by rw [hi])).congr_deriv hd0).congr
    · intro w hw
      exact ite_eq_left hw
    · simp [upperZeroExtension, hi]
  have hlower : HasDerivWithinAt (upperZeroExtension F) 0 {w : ℂ | w.im ≤ 0} z := by
    apply (hasDerivAt_const z (0 : ℂ)).hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hr)] with w hw hwr
      by_cases hw0 : 0 ≤ w.im
      · have hwi : w.im = 0 := le_antisymm hw hw0
        have hwreal : (w.re : ℂ) = w := by apply Complex.ext <;> simp [hwi]
        simp only [upperZeroExtension, ite_eq_left hw0]
        exact hwreal ▸ hzero w.re hwr
      · simp [upperZeroExtension, hw0]
    · simp only [upperZeroExtension, hi, le_refl, ite_eq_left]
      exact hzreal ▸ hzero z.re hr
  have hu : {w : ℂ | 0 ≤ w.im} ∪ {w : ℂ | w.im ≤ 0} = univ := by
    ext w
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total 0 w.im
  exact (hasDerivWithinAt_univ.mp (hu ▸ hupper.union hlower)).differentiableAt

theorem upper_halfPlane_eq_zero_of_boundary_interval
    {F D : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hF : ∀ z, 0 ≤ z.im → HasDerivWithinAt F (D z) {w : ℂ | 0 ≤ w.im} z)
    (hzero : ∀ x ∈ Ioo a b, F (x : ℂ) = 0) :
    ∀ z : ℂ, 0 < z.im → F z = 0 := by
  let U : Set ℂ := {z | 0 < z.im}
  let S : Set ℂ := {z | z.re ∈ Ioo a b}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hSopen : IsOpen S := isOpen_Ioo.preimage Complex.continuous_re
  have hUconvex : Convex ℝ U := (convex_Ioi (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap
  have hSconvex : Convex ℝ S := (convex_Ioo a b).linear_preimage Complex.reCLM.toLinearMap
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  have hjoin : ((c : ℂ) + Complex.I) ∈ U ∩ S := by
    change 0 < ((c : ℂ) + Complex.I).im ∧ ((c : ℂ) + Complex.I).re ∈ Ioo a b
    simpa using And.intro (show (0 : ℝ) < 1 by norm_num) hc
  have hconn : IsPreconnected (U ∪ S) :=
    IsPreconnected.union' ⟨_, hjoin⟩ hUconvex.isPreconnected hSconvex.isPreconnected
  have hhol : AnalyticOnNhd ℂ (upperZeroExtension F) (U ∪ S) := by
    apply DifferentiableOn.analyticOnNhd _ (hUopen.union hSopen)
    intro z hz
    exact (differentiableAt_upperZeroExtension hF hzero hz).differentiableWithinAt
  have hbelow : ((c : ℂ) - Complex.I) ∈ U ∪ S := by
    exact Or.inr (by simpa [S] using hc)
  have hneg : ((c : ℂ) - Complex.I).im < 0 := by simp
  have hlocal : upperZeroExtension F =ᶠ[𝓝 ((c : ℂ) - Complex.I)] 0 := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg] with w hw
    simp [upperZeroExtension, not_le.mpr hw]
  have hall := hhol.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hbelow hlocal
  intro z hz
  simpa [upperZeroExtension, hz.le] using hall (Or.inl hz)

theorem positiveEnergyLaplace_eq_zero_of_boundary_interval
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {ω : α → ℝ} {A : α → ℂ}
    (hω : MeasureTheory.AEStronglyMeasurable ω μ) (hω₀ : ∀ x, 0 ≤ ω x)
    (hA : MeasureTheory.Integrable A μ)
    (hωA : MeasureTheory.Integrable (fun x => ω x * ‖A x‖) μ)
    {a b : ℝ} (hab : a < b)
    (hzero : ∀ t ∈ Ioo a b, positiveEnergyLaplace μ ω A (t : ℂ) = 0) :
    ∀ z : ℂ, 0 < z.im → positiveEnergyLaplace μ ω A z = 0 := by
  exact upper_halfPlane_eq_zero_of_boundary_interval hab
    (fun _ hz => hasDerivWithinAt_positiveEnergyLaplace hω hω₀ hA hωA hz) hzero

end VacuumBellSeparation
