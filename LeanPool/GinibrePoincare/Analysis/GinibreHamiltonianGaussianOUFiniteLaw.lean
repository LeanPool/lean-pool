/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianGaussianOUFiniteLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUCovariance

/-!
# Ginibre Hamiltonian Gaussian OU finite law

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreBrownianOU_stationary_finite_law_reversal`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace GinibrePoincare
noncomputable section

theorem gaussianEuclidean_law_eq_of_coordinate_mean_covariance
    {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → EuclideanSpace ℝ ι) (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P)
    (hm : ∀ i, (∫ ω, X ω i ∂P) = (∫ ω, Y ω i ∂P))
    (hc : ∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P =
      covariance (fun ω => Y ω i) (fun ω => Y ω j) P) :
    P.map X = P.map Y := by
  have := Fintype.ofFinite ι
  classical
  have hx (i : ι) : MemLp (fun ω => X ω i) 2 P :=
    (hX.map (PiLp.proj 2 (fun _ : ι => ℝ) i : EuclideanSpace ℝ ι →L[ℝ] ℝ)).memLp_two
  have hy (i : ι) : MemLp (fun ω => Y ω i) 2 P :=
    (hY.map (PiLp.proj 2 (fun _ : ι => ℝ) i : EuclideanSpace ℝ ι →L[ℝ] ℝ)).memLp_two
  apply Measure.ext_of_charFun
  funext v
  rw [hX.charFun_map_eq, hY.charFun_map_eq]
  have hm' : (∫ ω, inner ℝ v (X ω) ∂P)=(∫ ω, inner ℝ v (Y ω) ∂P) := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    rw [integral_finsetSum _ (fun i _ => ((hx i).integrable (by simp)).const_mul _),
      integral_finsetSum _ (fun i _ => ((hy i).integrable (by simp)).const_mul _)]
    simp_rw [integral_const_mul, hm]
  have hv : variance (fun ω => inner ℝ v (X ω)) P =
      variance (fun ω => inner ℝ v (Y ω)) P := by
    have hXi : AEMeasurable (fun ω => inner ℝ v (X ω)) P := by
      simpa [Function.comp_def] using (hX.map (innerSL ℝ v)).aemeasurable
    have hYi : AEMeasurable (fun ω => inner ℝ v (Y ω)) P := by
      simpa [Function.comp_def] using (hY.map (innerSL ℝ v)).aemeasurable
    rw [← covariance_self hXi,← covariance_self hYi]
    simp only [PiLp.inner_apply, Real.inner_apply]
    rw [covariance_fun_sum_fun_sum (fun i => (hx i).const_mul (v i)) (fun i => (hx i).const_mul (v
        i)),
      covariance_fun_sum_fun_sum (fun i => (hy i).const_mul (v i)) (fun i => (hy i).const_mul (v
          i))]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, hc]
  rw [hm', hv]

theorem gaussianProcess_finite_euclidean_hasGaussianLaw
    {Ω ι T : Type*} [MeasurableSpace Ω] [Finite ι]
    (P : Measure Ω) (X : T → Ω → ℝ) (hX : IsGaussianProcess X P) (t : ι → T) :
    HasGaussianLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω)) P := by
  have := Fintype.ofFinite ι
  classical
  let I : Finset T := Finset.univ.image t
  let L : (I → ℝ) →L[ℝ] EuclideanSpace ℝ ι :=
    { toFun := fun v => WithLp.toLp 2 (fun i => v ⟨t i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
        rfl⟩⟩)
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro c x; ext i; rfl }
  exact (hX.hasGaussianLaw I).map L

theorem ginibreBrownianOU_stationary_finite_law_reversal
    {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1 / 2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate T : ℝ≥0)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) :
    P.map (fun ω => WithLp.toLp 2 (fun i =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) (t i) ω)) =
    P.map (fun ω => WithLp.toLp 2 (fun i =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) ((T-t i : ℝ≥0) : ℝ) ω)) := by
  have := Fintype.ofFinite ι
  have hG := ginibreBrownianOU_gaussian_initial_isGaussianProcess P B hB Z hZ.hasGaussianLaw hind
      rate
  apply gaussianEuclidean_law_eq_of_coordinate_mean_covariance P _ _
    (gaussianProcess_finite_euclidean_hasGaussianLaw P _ hG t)
    (gaussianProcess_finite_euclidean_hasGaussianLaw P _ hG (fun i => T-t i))
  · intro i
    exact (ginibreBrownianOU_stationary_mean B P hB Z hZ rate (t i)).trans
      (ginibreBrownianOU_stationary_mean B P hB Z hZ rate (T-t i)).symm
  · intro i j
    change covariance (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) (t i) ω)
      (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) (t j) ω) P = _
    rw [ginibreBrownianOU_stationary_covariance B P hB Z hZ hind rate (t i) (t j),
      ginibreBrownianOU_stationary_covariance B P hB Z hZ hind rate (T-t i) (T-t j)]
    congr 2
    rcases le_total (t i) (t j) with h | h
    · have hr : T-t j ≤ T-t i := tsub_le_tsub_left h T
      rw [max_eq_right h, min_eq_left h, max_eq_left hr, min_eq_right hr,
        tsub_tsub_tsub_cancel_left (ht j)]
    · have hr : T-t i ≤ T-t j := tsub_le_tsub_left h T
      rw [max_eq_left h, min_eq_right h, max_eq_right hr, min_eq_left hr,
        tsub_tsub_tsub_cancel_left (ht i)]

end
end GinibrePoincare
