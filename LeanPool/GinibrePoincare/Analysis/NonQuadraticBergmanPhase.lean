/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticBergmanPhase.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBergmanComplex
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2PiOperators
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticHolomorphicHomogeneity
public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Actual phase action on the nonquadratic weighted Bergman space -/

@[expose] public section
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- The unitary of `L²(ℂ)` given by composition with the rotation `z ↦ a z`, for `‖a‖ = 1`. -/
def planarLebesguePhase (a : ℂ) (ha : ‖a‖ = 1) : PlanarLebesgueL2 ≃ₗᵢ[ℂ] PlanarLebesgueL2 :=
  l2PullbackEquiv (complexMulMeasurableEquiv a (by intro h; simp [h] at ha))
    (measurePreserving_complex_mul_of_norm_one a ha)

private theorem planarHalfWeight_rotates (n : ℕ) (V : ℂ → ℝ)
    (hr : ∀ (a : ℂ), ‖a‖ = 1 → ∀ z, V (a * z) = V z)
    (a : ℂ) (ha : ‖a‖ = 1) (z : ℂ) :
    planarPotentialHalfWeight n V (a * z) = planarPotentialHalfWeight n V z := by
  simp only [planarPotentialHalfWeight, hr a ha z]

/-- The actual weighted holomorphic subspace is preserved by every unit
phase, using its genuine entire representatives. -/
theorem planarLebesguePhase_preserves_bergman (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V)
    (hr : ∀ (a : ℂ), ‖a‖ = 1 → ∀ z, V (a * z) = V z)
    (a : ℂ) (ha : ‖a‖ = 1) (u : PlanarLebesgueL2)
    (hu : u ∈ planarBergmanKernel n V hV) :
    planarLebesguePhase a ha u ∈ planarBergmanKernel n V hV := by
  obtain ⟨F, hF, hm, he⟩ :=
    (mem_planarWeakDbarKernel_iff_holomorphic_representative n V hV u).mp hu
  let mp := measurePreserving_complex_mul_of_norm_one a ha
  have hm' : MemLp (fun z => F (a * z) * planarPotentialHalfWeight n V z) 2 volume := by
    convert hm.comp_measurePreserving mp using 1
    funext z
    exact congrArg (fun w => F (a * z) * w) (planarHalfWeight_rotates n V hr a ha z).symm
  have he' : hm'.toLp _ = planarLebesguePhase a ha u := by
    rw [← he]
    change hm'.toLp _ = Lp.compMeasurePreserving (fun z : ℂ => a * z) mp (hm.toLp _)
    rw [Lp.toLp_compMeasurePreserving]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun z =>
      congrArg (fun w => F (a * z) * w) (planarHalfWeight_rotates n V hr a ha z).symm)
  rw [← he']
  exact weighted_holomorphic_mem_weak_dbar_kernel n V (hV.of_le (by norm_num)) _
    (hF.comp (differentiable_const a |>.mul differentiable_id)) hm'
/-- Actual weighted Bergman phase eigenvectors have genuine monomial
representatives; the conclusion follows from the actual L² phase equation. -/
theorem planarBergman_phase_eigenvector_is_monomial
    (n d : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ (a : ℂ), ‖a‖ = 1 → ∀ z, V (a * z) = V z)
    (u : PlanarLebesgueL2) (hu : u ∈ planarBergmanKernel n V hV)
    (hp : ∀ (a : ℂ) (ha : ‖a‖ = 1), planarLebesguePhase a ha u = a ^ d • u) :
    ∃ c : ℂ, ∃ hm : MemLp (fun z => c * z ^ d * planarPotentialHalfWeight n V z) 2 volume,
      hm.toLp _ = u := by
  obtain ⟨F, hF, hm, he⟩ :=
    (mem_planarWeakDbarKernel_iff_holomorphic_representative n V hV u).mp hu
  have hwc : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    fun_prop
  have hcov (a : ℂ) (ha : ‖a‖ = 1) : ∀ z, F (a * z) = a ^ d * F z := by
    let mp := measurePreserving_complex_mul_of_norm_one a ha
    have hup := hp a ha
    rw [← he] at hup
    have hc := Lp.coeFn_compMeasurePreserving (hm.toLp _) mp
    have haF := mp.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp
    have hae : (fun z => F (a * z) * planarPotentialHalfWeight n V (a * z)) =ᵐ[volume]
        (fun z => a ^ d * (F z * planarPotentialHalfWeight n V z)) := by
      filter_upwards [hc, haF, hm.coeFn_toLp, Lp.coeFn_smul (a ^ d) (hm.toLp _)] with z hz hzF hz0
          hzs
      have hv := congrArg (fun w : PlanarLebesgueL2 => w z) hup
      change (Lp.compMeasurePreserving (fun z : ℂ => a * z) mp (hm.toLp _)) z = _ at hv
      rw [hz, hzF, hzs] at hv
      change F (a * z) * planarPotentialHalfWeight n V (a * z) = a ^ d * (hm.toLp _) z at hv
      rw [hz0] at hv
      exact hv
    have heq := ((hF.continuous.comp (continuous_const.mul continuous_id)).mul
      (hwc.comp (continuous_const.mul continuous_id))).ae_eq_iff_eq volume
      (continuous_const.mul (hF.continuous.mul hwc)) |>.mp hae
    intro z
    have hz := congrFun heq z
    change F (a * z) * planarPotentialHalfWeight n V (a * z) = a ^ d * (F z *
        planarPotentialHalfWeight n V z) at hz
    rw [planarHalfWeight_rotates n V hr a ha z, ← mul_assoc] at hz
    exact mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hz
  have hmF : ∀ z, F z = z ^ d * F 1 :=
    entire_eq_monomial_of_unit_circle F hF d (F 1) (fun a ha => by simpa using hcov a ha 1)
  have hm' : MemLp (fun z => F 1 * z ^ d * planarPotentialHalfWeight n V z) 2 volume := by
    convert hm using 1
    funext z
    rw [hmF z]
    ring
  refine ⟨F 1, hm', ?_⟩
  apply Eq.trans _ he
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  intro z
  change F 1 * z ^ d * planarPotentialHalfWeight n V z = F z * planarPotentialHalfWeight n V z
  rw [hmF z]
  ring

/-- A genuine unitary preserving a closed subspace in both directions
commutes with its actual orthogonal projection. -/
theorem unitary_closed_projection_intertwines
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : ClosedSubmodule ℂ H) (U : H ≃ₗᵢ[ℂ] H)
    (hf : ∀ x ∈ K, U x ∈ K) (hb : ∀ x ∈ K, U.symm x ∈ K) (x : H) :
    U (K.starProjection x) = K.starProjection (U x) := by
  apply (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := K.toSubmodule)
    (hf _ (Submodule.starProjection_apply_mem K.toSubmodule x)) ?_).symm
  intro w hw
  rw [← U.map_sub, ← U.apply_symm_apply w, U.inner_map_map]
  exact Submodule.starProjection_inner_eq_zero (K := K.toSubmodule) x _ (hb w hw)

private theorem planarLebesguePhase_inverse_apply (a : ℂ) (ha : ‖a‖ = 1)
    (u : PlanarLebesgueL2) :
    (planarLebesguePhase a ha).symm u =
      planarLebesguePhase a⁻¹ (by simp [ha]) u := by
  apply (planarLebesguePhase a ha).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change u = Lp.compMeasurePreserving (fun z : ℂ => a * z) _
    (Lp.compMeasurePreserving (fun z : ℂ => a⁻¹ * z) _ u)
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hn : a ≠ 0 := by intro h; simp [h] at ha
  have hi : (fun z : ℂ => a⁻¹ * z) ∘ (fun z : ℂ => a * z) = id := by
    funext z
    simp [Function.comp_apply, hn]
  simp only [hi, Lp.compMeasurePreserving_id_apply]

/-- The actual nonquadratic Bergman projection intertwines unit phases. -/
theorem planarBergmanProjection_phase_intertwines (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V)
    (hr : ∀ (a : ℂ), ‖a‖ = 1 → ∀ z, V (a * z) = V z)
    (a : ℂ) (ha : ‖a‖ = 1) (u : PlanarLebesgueL2) :
    planarLebesguePhase a ha (planarBergmanProjection n V hV u) =
      planarBergmanProjection n V hV (planarLebesguePhase a ha u) := by
  apply unitary_closed_projection_intertwines (planarBergmanKernelClosed n V hV)
    (planarLebesguePhase a ha)
  · exact fun x hx => planarLebesguePhase_preserves_bergman n V hV hr a ha x hx
  · intro x hx
    rw [planarLebesguePhase_inverse_apply]
    exact planarLebesguePhase_preserves_bergman n V hV hr _ _ x hx

end
end GinibrePoincare
