/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticRadialBochner.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBochner
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticRadialConfinement
public import LeanPool.GinibrePoincare.Analysis.SmoothTestLocalization

/-! # Actual positive-radius diffusion coercivity
The logarithmic barrier is localized by a genuine smooth extension near the
compact test support. No regularity across radius zero is assumed.
-/

@[expose] public section
open MeasureTheory Set
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- Extend a function smooth on an open set near a closed subset, using an
actual smooth cutoff. The extension agrees on a neighborhood of each point. -/
theorem exists_contDiff_extension_near_closed (W : ℝ → ℝ) (K U : Set ℝ)
    (hK : IsClosed K) (hU : IsOpen U) (hs : K ⊆ U)
    (hW : ∀ x ∈ U, ContDiffAt ℝ 2 W x) :
    ∃ Wext : ℝ → ℝ, ContDiff ℝ 2 Wext ∧ ∀ x ∈ K, Wext =ᶠ[𝓝 x] W := by
  obtain ⟨χ, hχ, hχs, hχone⟩ := exists_smooth_open_cutoff K U hK hU hs
  let Wext := fun x => χ x * W x
  refine ⟨Wext, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact (hχ.contDiffAt.of_le (by decide)).mul (hW x (hχs hx))
    · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
      have he : Wext =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [hz] with y hy
        simp only [Wext, hy, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro x hx
    filter_upwards [hχone x hx] with y hy
    simp only [Wext, hy, Pi.one_apply, one_mul]

/-- Weighted coercivity for an actual potential smooth only near the compact
support. This applies to the singular logarithmic radial barrier. -/
theorem scalarConfinement_generator_coercivity_on_open (W f : ℝ → ℝ) (κ : ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hW : ∀ x ∈ U, ContDiffAt ℝ 2 W x)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ U)
    (hcurv : ∀ x ∈ tsupport f, κ ≤ deriv (deriv W) x) :
    κ * (∫ x, deriv f x ^ 2 * scalarConfinementWeight W x) ≤
      ∫ x, scalarConfinementGenerator W f x ^ 2 * scalarConfinementWeight W x := by
  obtain ⟨Wext, hWext, he⟩ := exists_contDiff_extension_near_closed W (tsupport f) U
    (isClosed_tsupport f) hU hs hW
  have hcurvExt : ∀ x ∈ tsupport f, κ ≤ deriv (deriv Wext) x := by
    intro x hx
    rw [(he x hx).deriv.deriv_eq]
    exact hcurv x hx
  have hi := scalarConfinement_generator_coercivity Wext f κ hWext hf hc hcurvExt
  have hb : (fun x => deriv f x ^ 2 * scalarConfinementWeight Wext x) =
      (fun x => deriv f x ^ 2 * scalarConfinementWeight W x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · rw [scalarConfinementWeight, scalarConfinementWeight, (he x hx).self_of_nhds]
    · have hd0 : deriv f x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx' => hx (tsupport_deriv_subset hx'))
      simp [hd0]
  have hg : (fun x => scalarConfinementGenerator Wext f x ^ 2 * scalarConfinementWeight Wext x) =
      (fun x => scalarConfinementGenerator W f x ^ 2 * scalarConfinementWeight W x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · unfold scalarConfinementGenerator scalarConfinementWeight
      rw [(he x hx).self_of_nhds, (he x hx).deriv_eq]
    · have hd0 : deriv f x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx' => hx (tsupport_deriv_subset hx'))
      have hdd0 : deriv (deriv f) x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hx' => hx (tsupport_deriv_subset (tsupport_deriv_subset hx')))
      simp [scalarConfinementGenerator, hd0, hdd0]
  rw [hb, hg] at hi
  exact hi

/-- The radial effective potential is C² at every strictly positive radius. -/
theorem contDiffAt_radialEffectivePotential (n k : ℕ) {V : Potential}
    (hV : ContDiff ℝ 2 V) (r : ℝ) (hr : 0 < r) :
    ContDiffAt ℝ 2 (radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))) r := by
  have hQ : ContDiffAt ℝ 2 (fun t : ℝ => V (t : ℂ)) r :=
    (hV.comp Complex.ofRealCLM.contDiff).contDiffAt
  have hlog : ContDiffAt ℝ 2 Real.log r := Real.contDiffAt_log.mpr hr.ne'
  exact (contDiffAt_const.mul hQ).sub (contDiffAt_const.mul hlog)

/-- The effective confinement weight is literally the paper's positive-radius
density r^(2k−1) exp(-nV(r)), including the correct barrier exponent. -/
theorem scalarConfinementWeight_radialEffectivePotential (n k : ℕ) (hk : 1 ≤ k)
    (V : Potential) (r : ℝ) (hr : 0 < r) :
    scalarConfinementWeight (radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))) r =
      r ^ (2 * k - 1) * Real.exp (-(n : ℝ) * V (r : ℂ)) := by
  have hc : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    norm_num
  unfold scalarConfinementWeight radialEffectivePotential
  rw [neg_sub]
  have he : (2 * (k : ℝ) - 1) * Real.log r - (n : ℝ) * V (r : ℂ) =
      ((2 * k - 1 : ℕ) : ℝ) * Real.log r + -(n : ℝ) * V (r : ℂ) := by rw [hc]; ring
  rw [he, Real.exp_add, Real.exp_nat_mul, Real.exp_log hr]

/-- Actual weighted coercivity on the positive half-line for the arbitrary
strongly convex radial confinement. The sharp curvature scale is nρ. -/
theorem radialConfinement_generator_coercivity (n k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hcV : IsRhoConvexPotential ρ V)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hcf : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi 0) :
    (n : ℝ) * ρ *
      (∫ x in Ioi 0, deriv f x ^ 2 *
        scalarConfinementWeight (radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))) x) ≤
      ∫ x in Ioi 0,
        scalarConfinementGenerator (radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))) f x ^ 2 *
          scalarConfinementWeight (radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))) x := by
  let W := radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))
  have hi := scalarConfinement_generator_coercivity_on_open W f ((n : ℝ) * ρ) (Ioi 0)
    isOpen_Ioi (fun x hx => contDiffAt_radialEffectivePotential n k hV x hx) hf hcf hs
    (fun x hx => rhoConvexPotential_radial_curvature n k hk ρ hV hcV x (hs hx))
  have hd0 (x : ℝ) (hx : x ∉ Ioi (0 : ℝ)) : deriv f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hx' => hx (hs (tsupport_deriv_subset hx')))
  have hdd0 (x : ℝ) (hx : x ∉ Ioi (0 : ℝ)) : deriv (deriv f) x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun hx' => hx (hs (tsupport_deriv_subset (tsupport_deriv_subset hx'))))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hd0 x hx]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [scalarConfinementGenerator, hd0 x hx, hdd0 x hx])]
  exact hi

end
end GinibrePoincare
