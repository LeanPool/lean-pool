/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralRadialProjectionModes.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralRadialProjectionPhase
public import LeanPool.GinibrePoincare.Analysis.GeneralRadialProjectionCharacters
public import Mathlib.Analysis.Convex.Integral

/-!
# General radial projection modes

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarRotationCoefficient_eigen`, `planarRotationCoefficient_mem_bergman`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem planarLebesguePhase_comp (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (u : PlanarLebesgueL2) :
    planarLebesguePhase a ha (planarLebesguePhase b hb u) =
      planarLebesguePhase (b * a) (by rw [norm_mul, ha, hb, one_mul]) u := by
  let mpa := measurePreserving_complex_mul_of_norm_one a ha
  let mpb := measurePreserving_complex_mul_of_norm_one b hb
  let mpba := measurePreserving_complex_mul_of_norm_one (b * a)
    (by rw [norm_mul, ha, hb, one_mul])
  change Lp.compMeasurePreserving (fun z : ℂ => a * z) mpa
    (Lp.compMeasurePreserving (fun z : ℂ => b * z) mpb u) =
    Lp.compMeasurePreserving (fun z : ℂ => (b * a) * z) mpba u
  have h := Lp.compMeasurePreserving_comp_apply u mpb mpa
  have he : ((fun z : ℂ => b * z) ∘ (fun z : ℂ => a * z)) =
      (fun z : ℂ => (b * a) * z) := by
    funext z
    exact (mul_assoc b a z).symm
  simpa only [he] using h.symm

/-- The `k`-th Fourier coefficient, over the circle `AddCircle T`, of the rotated functions
`t ↦ u ∘ (z ↦ e^(2πit/T) z)`: the angular mode of order `k` of `u ∈ L²(ℂ)`. -/
def planarRotationCoefficient {T : ℝ} [Fact (0 < T)]
    (u : PlanarLebesgueL2) (k : ℤ) : PlanarLebesgueL2 :=
  fourierCoeff (fun t : AddCircle T =>
    planarLebesguePhase (AddCircle.toCircle t) (Circle.norm_coe _) u) k

theorem planarRotationCoefficient_eigen {T : ℝ} [Fact (0 < T)]
    (u : PlanarLebesgueL2) (k : ℤ) (s : AddCircle T) :
    planarLebesguePhase (AddCircle.toCircle s) (Circle.norm_coe _)
      (planarRotationCoefficient (T := T) u k) =
    fourier k s • planarRotationCoefficient (T := T) u k := by
  unfold planarRotationCoefficient
  apply circle_orbit_fourierCoeff_eigen (fun t : AddCircle T =>
    planarLebesguePhase (AddCircle.toCircle t) (Circle.norm_coe _)) u
  · exact planarLebesguePhase_circle_continuous u
  · intro s t
    rw [planarLebesguePhase_comp]
    have he : (AddCircle.toCircle t : ℂ) * (AddCircle.toCircle s : ℂ) =
        (AddCircle.toCircle (t + s) : ℂ) := congrArg Subtype.val (AddCircle.toCircle_add t s).symm
    simp only [he]

theorem planarRotationCoefficient_mem_bergman {T : ℝ} [Fact (0 < T)]
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a * z) = V z)
    (u : PlanarLebesgueL2) (hu : u ∈ planarBergmanKernel n V hV) (k : ℤ) :
    planarRotationCoefficient (T := T) u k ∈ planarBergmanKernel n V hV := by
  let K := planarBergmanKernelClosed n V hV
  apply (K.toSubmodule.restrictScalars ℝ).convex.integral_mem K.isClosed
  · exact Filter.Eventually.of_forall fun t => K.toSubmodule.smul_mem _
      (planarLebesguePhase_preserves_bergman n V hV hr _ (Circle.norm_coe _) u hu)
  · exact ((planarLebesguePhase_circle_continuous (T := T) u).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).fourier_smul (-k)

end
end GinibrePoincare
