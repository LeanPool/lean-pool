/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiDbar.lean.
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
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticComplexTestInverse

/-!
# Non quadratic pi dbar

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `rhoSubharmonicPotential_pi_compact_core_gap`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- The tensor product in `L²(ℂ^(m+1))` of the weighted values `f i * exp (-n V / 2)` of a
family of complex planar tests. -/
def planarPiPureWeightedValue {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : Fin (m + 1) → PlanarComplexCompactTest) : PlanarPiLebesgueL2 (m+1) :=
  l2PiProductVector (fun _ => (volume : Measure ℂ)) (fun i => planarComplexWeightedValueL2 n V hV (f
      i))

/-- The `i`-th weighted `∂̄` of a pure tensor: the tensor product of the weighted values of the
tests `f j`, with the `i`-th factor replaced by the weighted `∂̄` of `f i`. -/
def planarPiPureWeightedDbar {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : Fin (m + 1) → PlanarComplexCompactTest) (i : Fin (m + 1)) : PlanarPiLebesgueL2 (m+1) :=
  l2PiProductVector (fun _ => (volume : Measure ℂ))
    (Function.update (fun j => planarComplexWeightedValueL2 n V hV (f j)) i
      (planarComplexWeightedDbarL2 n V hV (f i)))

theorem planarPiPure_inverse_action {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (f : Fin (m+1) → PlanarComplexCompactTest) (i : Fin (m+1)) :
    l2PiCoordinateOperator (fun _ => (volume : Measure ℂ)) i T
        (planarPiPureWeightedDbar n V hV.continuous f i) =
      planarPiPureWeightedValue n V hV.continuous f -
        planarPiBergmanCoordinate n V hV i (planarPiPureWeightedValue n V hV.continuous f) := by
  let E := l2PiCoordinateEquiv (fun _ : Fin (m+1) => (volume : Measure ℂ)) i
  apply E.injective
  change E ((E).symm
    (l2ProductLeftOperator T (E (planarPiPureWeightedDbar n V hV.continuous f i)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  dsimp [E]
  unfold planarPiPureWeightedDbar
  rw [l2PiProductVector_split, l2ProductLeftOperator_pure]
  simp only [Function.update_self]
  rw [hT, map_sub]
  change _ = E (planarPiPureWeightedValue n V hV.continuous f) -
    E ((E).symm
      (l2ProductLeftOperator (planarBergmanProjection n V hV)
        (E (planarPiPureWeightedValue n V hV.continuous f))))
  rw [LinearIsometryEquiv.apply_symm_apply]
  unfold planarPiPureWeightedValue
  rw [l2PiProductVector_split, l2ProductLeftOperator_pure]
  change l2ProductBilinear (_ - _) _ = _
  simp only [Function.update_of_ne (Fin.succAbove_ne i _)]
  rw [map_sub]
  rfl

/-- The weighted value of a finite linear combination `∑ c • ⊗ f` of pure tensors of tests,
given as a list of coefficient–family pairs. -/
def planarPiCoreWeightedValue {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (fs : List (ℂ × (Fin (m + 1) → PlanarComplexCompactTest))) : PlanarPiLebesgueL2 (m+1) :=
  (fs.map (fun cf => cf.1 • planarPiPureWeightedValue n V hV cf.2)).sum

/-- The `i`-th weighted `∂̄` of a finite linear combination `∑ c • ⊗ f` of pure tensors of
tests, given as a list of coefficient–family pairs. -/
def planarPiCoreWeightedDbar {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (fs : List (ℂ × (Fin (m + 1) → PlanarComplexCompactTest))) (i : Fin (m + 1)) :
        PlanarPiLebesgueL2
        (m+1) :=
  (fs.map (fun cf => cf.1 • planarPiPureWeightedDbar n V hV cf.2 i)).sum

theorem planarPiCore_inverse_action {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (fs : List (ℂ × (Fin (m+1) → PlanarComplexCompactTest))) (i : Fin (m+1)) :
    l2PiCoordinateOperator (fun _ => (volume : Measure ℂ)) i T
        (planarPiCoreWeightedDbar n V hV.continuous fs i) =
      planarPiCoreWeightedValue n V hV.continuous fs -
        planarPiBergmanCoordinate n V hV i (planarPiCoreWeightedValue n V hV.continuous fs) := by
  induction fs with
  | nil => simp [planarPiCoreWeightedDbar, planarPiCoreWeightedValue]
  | cons cf fs ih =>
    simp only [planarPiCoreWeightedDbar, planarPiCoreWeightedValue, List.map_cons, List.sum_cons,
      map_add, map_smul] at ih ⊢
    rw [planarPiPure_inverse_action n V hV T hT, ih, smul_sub]
    abel

/-- The exact arbitrary-dimensional Hörmander bound on the genuine finite
separated compact core, including arbitrary complex linear combinations. -/
theorem rhoSubharmonicPotential_pi_compact_core_gap {m : ℕ}
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (fs : List (ℂ × (Fin (m + 1) → PlanarComplexCompactTest))) :
    let F := planarPiCoreWeightedValue n V hV.continuous fs
    ‖F - planarPiBergmanProjection n V hV F‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) *
        ((List.finRange (m+1)).map (fun i => ‖planarPiCoreWeightedDbar n V hV.continuous fs i‖ ^
            2)).sum := by
  obtain ⟨T, hnorm, hT⟩ := rhoSubharmonicPotential_exists_bounded_dbar_inverse n hn V ρ hρpos hV hρ
  let C := 2 / ((n : ℝ) * ρ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := Real.sq_sqrt hC
  have hb (i : Fin (m+1)) :
      ‖planarPiCoreWeightedValue n V hV.continuous fs -
        planarPiBergmanCoordinate n V hV i (planarPiCoreWeightedValue n V hV.continuous fs)‖ ^ 2 ≤
      C * ‖planarPiCoreWeightedDbar n V hV.continuous fs i‖ ^ 2 := by
    let S := l2PiCoordinateOperator (fun _ : Fin (m+1) => (volume : Measure ℂ)) i T
    let G := planarPiCoreWeightedDbar n V hV.continuous fs i
    have hb : ‖S‖ ≤ Real.sqrt C := (l2PiCoordinateOperator_norm_le (fun _ : Fin (m+1) => (volume :
        Measure ℂ)) i T).trans hnorm
    have hh := (S.le_opNorm G).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg G))
    have hsq := (sq_le_sq₀ (norm_nonneg (S G))
      (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg G))).mpr hh
    have he : S G = _ := planarPiCore_inverse_action n V hV T hT fs i
    rw [he] at hsq
    simpa only [mul_pow, hs] using hsq
  have sum_bound (is : List (Fin (m+1))) :
      (is.map (fun i => ‖planarPiCoreWeightedValue n V hV.continuous fs -
        planarPiBergmanCoordinate n V hV i (planarPiCoreWeightedValue n V hV.continuous fs)‖ ^
            2)).sum ≤
      C * (is.map (fun i => ‖planarPiCoreWeightedDbar n V hV.continuous fs i‖ ^ 2)).sum := by
    induction is with
    | nil => simp
    | cons i is ih => simpa only [List.map_cons, List.sum_cons, mul_add] using add_le_add (hb i) ih
  exact (planarPiBergmanProjection_error n V hV _).trans (sum_bound _)

end
end GinibrePoincare
