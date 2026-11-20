/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialProjectionPermutation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBergman
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialVandermondeSymmetry

/-!
# General potential projection permutation

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiBergmanProjection_preserves_alternating`,
`planarPiBergmanProjection_preserves_symmetric`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

private theorem planarPiBergmanProjection_list_pure {m : ℕ} (n : ℕ) (V : Potential)
    (hV : ContDiff ℝ 2 V) (l : List (Fin (m + 1))) (hl : l.Nodup)
    (u : Fin (m + 1) → PlanarLebesgueL2) :
    complexSuccessiveProjections (l.map (planarPiBergmanCoordinate n V hV))
      (l2PiProductVector (fun _ => (volume : Measure ℂ)) u) =
      l2PiProductVector (fun _ => (volume : Measure ℂ))
        (fun j => if j ∈ l then planarBergmanProjection n V hV (u j) else u j) := by
  classical
  induction l with
  | nil => simp [complexSuccessiveProjections]
  | cons i l ih =>
    have hh := List.nodup_cons.mp hl
    simp only [List.map_cons, complexSuccessiveProjections, List.foldr_cons,
      ContinuousLinearMap.comp_apply]
    change planarPiBergmanCoordinate n V hV i
      (complexSuccessiveProjections (l.map (planarPiBergmanCoordinate n V hV))
        (l2PiProductVector (fun _ => (volume : Measure ℂ)) u)) = _
    rw [ih hh.2]
    rw [planarPiBergmanCoordinate, l2PiCoordinateOperator_pure]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      simp [hh.1]
    · simp [Function.update, hj]

theorem planarPiBergmanProjection_pure {m : ℕ} (n : ℕ) (V : Potential)
    (hV : ContDiff ℝ 2 V) (u : Fin (m + 1) → PlanarLebesgueL2) :
    planarPiBergmanProjection n V hV (l2PiProductVector (fun _ => (volume : Measure ℂ)) u) =
      l2PiProductVector (fun _ => (volume : Measure ℂ))
        (fun i => planarBergmanProjection n V hV (u i)) := by
  unfold planarPiBergmanProjection
  simpa only [List.mem_finRange, ite_true] using
    planarPiBergmanProjection_list_pure n V hV (List.finRange (m+1)) (List.nodup_finRange _) u
theorem volumePermutationL2_pure {d : ℕ} (e : ParticlePermutation d)
    (u : Fin d → PlanarLebesgueL2) :
    volumePermutationL2 e (l2PiProductVector (fun _ => (volume : Measure ℂ)) u) =
      l2PiProductVector (fun _ => (volume : Measure ℂ)) (fun i => u (e.symm i)) := by
  unfold volumePermutationL2
  change Lp.compMeasurePreserving (permute e) (measurePreserving_permute_configurationVolume e)
    (l2PiProductVector (fun _ => (volume : Measure ℂ)) u) = _
  apply Lp.ext
  have hp := (measurePreserving_permute_configurationVolume e).quasiMeasurePreserving.ae_eq_comp
    (l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ)) u)
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (l2PiProductVector (fun _ => (volume : Measure ℂ)) u)
    (measurePreserving_permute_configurationVolume e), hp,
    l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ)) (fun i => u (e.symm i))] with z hz hp hq
  have hh := Equiv.prod_comp e (fun j => u (e.symm j) (z j))
  have hprod : (∏ i, u i (permute e z i)) = ∏ i, u (e.symm i) (z i) := by
    simpa [permute] using hh
  exact hz.trans (hp.trans (hprod.trans hq.symm))

/-- Identical scalar Bergman factors make the actual whole-product projection
commute with every configuration permutation. -/
theorem planarPiBergmanProjection_commutes_permutation {m : ℕ} (n : ℕ) (V : Potential)
    (hV : ContDiff ℝ 2 V) (e : ParticlePermutation (m + 1)) :
    (planarPiBergmanProjection n V hV).comp (volumePermutationL2 e).toContinuousLinearMap =
      (volumePermutationL2 e).toContinuousLinearMap.comp (planarPiBergmanProjection n V hV) := by
  apply l2PiOperators_ext_on_pure (m+1) (fun _ => (volume : Measure ℂ))
  intro u
  change planarPiBergmanProjection n V hV
    (volumePermutationL2 e (l2PiProductVector (fun _ => (volume : Measure ℂ)) u)) =
    volumePermutationL2 e (planarPiBergmanProjection n V hV
      (l2PiProductVector (fun _ => (volume : Measure ℂ)) u))
  rw [volumePermutationL2_pure, planarPiBergmanProjection_pure,
    planarPiBergmanProjection_pure, volumePermutationL2_pure]

/-- The genuine product Bergman projection preserves alternating vectors. -/
theorem planarPiBergmanProjection_preserves_alternating {m : ℕ} (n : ℕ) (V : Potential)
    (hV : ContDiff ℝ 2 V) (F : PlanarPiLebesgueL2 (m + 1))
    (hF : ∀ e : ParticlePermutation (m+1), volumePermutationL2 e F = permutationSign e • F)
    (e : ParticlePermutation (m+1)) :
    volumePermutationL2 e (planarPiBergmanProjection n V hV F) =
      permutationSign e • planarPiBergmanProjection n V hV F := by
  have hh := DFunLike.congr_fun (planarPiBergmanProjection_commutes_permutation n V hV e) F
  change planarPiBergmanProjection n V hV (volumePermutationL2 e F) =
    volumePermutationL2 e (planarPiBergmanProjection n V hV F) at hh
  rw [hF e, map_smul] at hh
  exact hh.symm

/-- The genuine product Bergman projection preserves symmetric vectors. -/
theorem planarPiBergmanProjection_preserves_symmetric {m : ℕ} (n : ℕ) (V : Potential)
    (hV : ContDiff ℝ 2 V) (F : PlanarPiLebesgueL2 (m + 1))
    (hF : ∀ e : ParticlePermutation (m+1), volumePermutationL2 e F = F)
    (e : ParticlePermutation (m+1)) :
    volumePermutationL2 e (planarPiBergmanProjection n V hV F) =
      planarPiBergmanProjection n V hV F := by
  have hh := DFunLike.congr_fun (planarPiBergmanProjection_commutes_permutation n V hV e) F
  change planarPiBergmanProjection n V hV (volumePermutationL2 e F) =
    volumePermutationL2 e (planarPiBergmanProjection n V hV F) at hh
  rw [hF e] at hh
  exact hh.symm

end
end GinibrePoincare
