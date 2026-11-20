/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultLpBall.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultApproximation
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultTruncatedCorrespondence
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultIBP
public import Mathlib.Data.List.FinRange

/-!
# Correspondence auxiliary local Dolbeault lp ball

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `localDolbeault_compactLp_ball`.
-/

@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section

/-- Local ordinary L² Dolbeault solvability for an arbitrary compact L²
source closed distributionally on a ball. No Gaussian membership is used. -/
theorem localDolbeault_compactLp_ball {n : ℕ}
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, MemLp (α j) 2 volume)
    (hcα : ∀ j, HasCompactSupport (α j)) (x : Configuration n) (r : ℝ) (hr : 0 < r)
    (hclosed : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ ball x r → ∀ j k,
        (∫ y, dbarComponent θ k y*α j y) = ∫ y, dbarComponent θ j y*α k y) :
    ∃ U : Set (Configuration n), IsOpen U ∧ x ∈ U ∧ U ⊆ ball x r ∧
      ∃ u : dolbeaultOrdinaryL2 n, ∀ θ : Configuration n → ℂ,
        ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U → ∀ j,
          (∫ p, θ p*α j p) = -(∫ p, dbarComponent θ j p*u p) := by
  let W : Fin n → Set ℂ := fun j => ball (x j) (r/4)
  let V : Fin n → Set ℂ := fun j => ball (x j) (r/16)
  let b : (j : Fin n) → ContDiffBump (x j) := fun _ =>
    { rIn := r/16, rOut := r/8, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let χ : Fin n → ℂ → ℂ := fun j z => Complex.ofReal (b j z)
  have hχ (j : Fin n) : ContDiff ℝ ∞ (χ j) := Complex.ofRealCLM.contDiff.comp (b j).contDiff
  have hcχ (j : Fin n) : HasCompactSupport (χ j) :=
    (b j).hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hs (j : Fin n) : tsupport (χ j) ⊆ closedBall (x j) (r/8) := by
    have h := tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero (b j)
    simpa only [(b j).tsupport_eq] using! h
  have hχW (j : Fin n) : tsupport (χ j) ⊆ W j :=
    (hs j).trans (closedBall_subset_ball (by linarith))
  have hχone (j : Fin n) (z : ℂ) (hz : z ∈ V j) : χ j z = 1 := by
    change Complex.ofReal (b j z) = 1
    rw [(b j).one_of_mem_closedBall (ball_subset_closedBall hz), Complex.ofReal_one]
  have hR (j : Fin n) (p : Configuration n) (hp : p ∈ dolbeaultCylinder W Finset.univ)
      (z : ℂ) (hz : z ∈ tsupport (χ j)) : ‖p j-z‖ ≤ r := by
    have h1 := hp j (Finset.mem_univ j)
    have h2 := hs j hz
    have ht := dist_triangle (p j) (x j) z
    rw [dist_comm (x j) z] at ht
    simp only [W, mem_ball] at h1
    simp only [mem_closedBall] at h2
    rw [← dist_eq_norm]
    linarith
  let l : List (Fin n) := List.ofFn (fun j : Fin n => j)
  have hl : l.Nodup := List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hlj (j : Fin n) : j ∈ l := List.mem_ofFn.mpr ⟨j, rfl⟩
  let U := dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V l.toFinset
  have hU : IsOpen U := (dolbeaultCylinder_isOpen W (fun _ => isOpen_ball) _).inter
    (dolbeaultCylinder_isOpen V (fun _ => isOpen_ball) _)
  have hxU : x ∈ U := ⟨fun _ _ => mem_ball_self (by positivity), fun _ _ => mem_ball_self (by
      positivity)⟩
  have hWdist (p : Configuration n) (hp : p ∈ dolbeaultCylinder W Finset.univ) : dist p x < r/4 :=
    (dist_pi_lt_iff (by positivity)).mpr (fun j => hp j (Finset.mem_univ j))
  have hUb : U ⊆ ball x r := fun p hp => by
    have h := hWdist p hp.1
    change dist p x < r
    linarith
  let φ : ℕ → ContDiffBump (0 : ℂ) := planarPiShrinkingBump
  have hφ := planarPiShrinkingBump_rOut_tendsto
  let A : ℕ → Fin n → Configuration n → ℂ := fun m j =>
    piPlanarBump n (φ m) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] α j
  have hA (m : ℕ) (j : Fin n) : ContDiff ℝ ∞ (A m j) :=
    dolbeaultPiBump_convolution_smooth n (φ m) (α j) (hα j)
  have hcA (m : ℕ) (j : Fin n) : HasCompactSupport (A m j) :=
    (piPlanarBump_compact n (φ m)).convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hcα j)
  let a : Fin n → dolbeaultOrdinaryL2 n := fun j => (hα j).toLp (α j)
  let aM : ℕ → Fin n → dolbeaultOrdinaryL2 n := fun m j =>
    ((hA m j).continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) (hcA m j)).toLp (A m j)
  have haM (j : Fin n) : Tendsto (fun m => aM m j) atTop (𝓝 (a j)) :=
    dolbeaultPiBump_convolution_tendsto n φ hφ (α j) (hα j) (hcα j)
  let u : dolbeaultOrdinaryL2 n := dolbeaultPrimitiveLp r χ hχ hcχ a l
  let uM : ℕ → dolbeaultOrdinaryL2 n := fun m => dolbeaultPrimitiveLp r χ hχ hcχ (aM m) l
  have huM : Tendsto uM atTop (𝓝 u) := dolbeaultPrimitiveLp_tendsto r χ hχ hcχ aM a haM l
  have hsmall : ∀ᶠ m in atTop, (φ m).rOut < r/4 :=
    (tendsto_order.mp hφ).2 _ (by positivity)
  refine ⟨U, hU, hxU, hUb, u,?_⟩
  intro θ hθ hcθ hsθ j
  have hident : ∀ᶠ m in atTop,
      (∫ p, θ p*aM m j p) = -(∫ p, dbarComponent θ j p*uM m p) := by
    filter_upwards [hsmall] with m hm
    have hclosedA (s t : Fin n) (p : Configuration n)
        (hp : p ∈ dolbeaultCylinder W Finset.univ) :
        dbarComponent (A m s) t p = dbarComponent (A m t) s p := by
      apply ordinaryDolbeaultPiMollification_closed_ball α hα x r hclosed (φ m) p _ s t
      have hd := hWdist p hp
      linarith
    have hsol (p : Configuration n) (hp : p ∈ U) :
        dbarComponent (truncatedDolbeaultPrimitive r χ (A m) l) j p = A m j p :=
      truncatedDolbeaultPrimitive_solves (A m) (hA m) W V (fun _ => isOpen_ball)
        (fun _ => isOpen_ball) hclosedA χ hχ hcχ hχone hχW r hR l hl p hp j (hlj j)
    have hf := (truncatedDolbeaultPrimitive_smooth_compact r χ hχ (A m) (hA m) (hcA m) l).1
    have he := localDolbeault_smooth_weak_identity U (A m j)
      (truncatedDolbeaultPrimitive r χ (A m) l) θ hf hθ hcθ hsθ j hsol
    have hleft : (∫ p, θ p*aM m j p) = ∫ p, θ p*A m j p := by
      apply integral_congr_ae
      filter_upwards [((hA m j).continuous.memLp_of_hasCompactSupport
        (p := 2) (μ := volume) (hcA m j)).coeFn_toLp] with p hp
      exact congrArg (fun z => θ p*z) hp
    have hright : (∫ p, dbarComponent θ j p*uM m p) =
        ∫ p, dbarComponent θ j p*truncatedDolbeaultPrimitive r χ (A m) l p := by
      apply integral_congr_ae
      filter_upwards [dolbeaultPrimitiveLp_ae r χ hχ hcχ (A m) (hA m) (hcA m) l] with p hp
      exact congrArg (fun z => dbarComponent θ j p*z) hp
    rw [hleft, hright]
    exact he
  have he := dolbeault_weak_identity_of_eventual_strong_limit uM (fun m => aM m j)
    u (a j) huM (haM j) θ hθ hcθ j hident
  have hleft : (∫ p, θ p*a j p) = ∫ p, θ p*α j p := by
    apply integral_congr_ae
    filter_upwards [(hα j).coeFn_toLp] with p hp
    exact congrArg (fun z => θ p*z) hp
  rw [hleft] at he
  exact he

end
end GinibrePoincare
