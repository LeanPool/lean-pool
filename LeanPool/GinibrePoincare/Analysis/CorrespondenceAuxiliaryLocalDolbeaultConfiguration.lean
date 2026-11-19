/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultConfiguration.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultCoordinate
public import LeanPool.GinibrePoincare.Concrete.Wirtinger

/-!
# Correspondence auxiliary local Dolbeault configuration

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `configurationCauchyGreenPotential_contDiff`,
`configurationCauchyGreenPotential_solves`, `configurationCauchyGreenPotential_preserves_CR`.
-/

@[expose] public section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- The real-linear map sending `(p, z)` to `p` with its `j`-th coordinate replaced by `z`. -/
def dolbeaultReplaceCoordinate {n : ℕ} (j : Fin n) :
    Configuration n × ℂ →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi (fun k => if k = j then ContinuousLinearMap.snd ℝ _ ℂ else
    (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℝ _ ℂ))

theorem dolbeaultReplaceCoordinate_apply {n : ℕ} (j : Fin n)
    (p : Configuration n) (z : ℂ) (k : Fin n) :
    dolbeaultReplaceCoordinate j (p, z) k = if k = j then z else p k := by
  simp only [dolbeaultReplaceCoordinate, ContinuousLinearMap.pi_apply]
  split_ifs <;> simp

theorem dolbeaultReplaceCoordinate_same {n : ℕ} (j : Fin n) (p : Configuration n) :
    dolbeaultReplaceCoordinate j (p, p j) = p := by
  ext k
  rw [dolbeaultReplaceCoordinate_apply]
  split_ifs with h
  · subst k; rfl
  · rfl

theorem dolbeaultReplaceCoordinate_direction_zero {n : ℕ} (j : Fin n) (w : ℂ) :
    dolbeaultReplaceCoordinate j (coordinateDirection j w, 0) = 0 := by
  ext k
  simp only [dolbeaultReplaceCoordinate_apply, coordinateDirection, Pi.zero_apply]
  split_ifs <;> simp_all

theorem dolbeaultReplaceCoordinate_direction_other {n : ℕ} (j k : Fin n)
    (hkj : k ≠ j) (w : ℂ) :
    dolbeaultReplaceCoordinate j (coordinateDirection k w, 0) = coordinateDirection k w := by
  ext l
  simp only [dolbeaultReplaceCoordinate_apply, coordinateDirection]
  split_ifs <;> simp_all

/-- The localized Cauchy–Green potential of `a` with cutoff `χ` in the `j`-th coordinate,
evaluated at `p` with the other coordinates of `p` frozen. -/
def configurationCauchyGreenPotential {n : ℕ} (j : Fin n) (χ : ℂ → ℂ)
    (a : Configuration n → ℂ) (p : Configuration n) : ℂ :=
  localizedCauchyGreenPotential χ
    (fun q z => a (dolbeaultReplaceCoordinate j (q, z))) (p, p j)

theorem configurationCauchyGreenPotential_contDiff {n : ℕ} (j : Fin n)
    (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (configurationCauchyGreenPotential j χ a) := by
  have hs : ContDiff ℝ ∞ (Function.uncurry
      (fun q z => a (dolbeaultReplaceCoordinate j (q, z)))) := by
    simpa only [Function.uncurry] using! ha.comp (dolbeaultReplaceCoordinate j).contDiff
  have hp : ContDiff ℝ ∞ (fun p : Configuration n => p j) := by
    simpa using! (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ).contDiff
  exact (localizedCauchyGreenPotential_contDiff χ _ hχ hc hs).comp
    (contDiff_id.prodMk hp)

theorem configurationCauchyGreen_parameter_derivative_zero {n : ℕ} (j : Fin n)
    (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ha : ContDiff ℝ ∞ a)
    (q : Configuration n × ℂ) (w : ℂ) :
    fderiv ℝ (localizedCauchyGreenPotential χ
      (fun p z => a (dolbeaultReplaceCoordinate j (p, z)))) q
        (coordinateDirection j w, 0) = 0 := by
  let A : Configuration n → ℂ → ℂ := fun p z => χ z * a (dolbeaultReplaceCoordinate j (p, z))
  have hA : ContDiff ℝ ∞ (Function.uncurry A) :=
    (hχ.comp contDiff_snd).mul (ha.comp (dolbeaultReplaceCoordinate j).contDiff)
  have hs : ∀ p z, z ∉ tsupport χ → A p z = 0 := by
    intro p z hz
    simp only [A, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  change fderiv ℝ (parametricCauchyGreenPotential A) q _ = 0
  rw [parametricCauchyGreenPotential_directional_derivative A hA (tsupport χ) hc hs]
  have hz (z : ℂ) : fderiv ℝ (Function.uncurry A) (q.1, z)
      (coordinateDirection j w, 0) = 0 := by
    have hχ' := (hχ.differentiable (by simp) z).hasFDerivAt.comp (q.1, z)
      (ContinuousLinearMap.snd ℝ _ ℂ).hasFDerivAt
    have ha' := (ha.differentiable (by simp)
      (dolbeaultReplaceCoordinate j (q.1, z))).hasFDerivAt.comp (q.1, z)
        (dolbeaultReplaceCoordinate j).hasFDerivAt
    have hh := hχ'.mul ha'
    have hh' : HasFDerivAt (Function.uncurry A)
        (χ z • (fderiv ℝ a (dolbeaultReplaceCoordinate j (q.1, z))).comp
            (dolbeaultReplaceCoordinate j) +
          a (dolbeaultReplaceCoordinate j (q.1, z)) •
            (fderiv ℝ χ z).comp (ContinuousLinearMap.snd ℝ _ ℂ)) (q.1, z) := by
      simpa only [A, Function.uncurry, Function.comp_def, Pi.mul_apply,
        ContinuousLinearMap.coe_snd] using! hh
    rw [hh'.fderiv]
    simp [dolbeaultReplaceCoordinate_direction_zero]
  simp only [hz, mul_zero]
  exact integral_zero ℂ ℂ

theorem configurationCauchyGreenPotential_solves {n : ℕ} (j : Fin n)
    (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ha : ContDiff ℝ ∞ a)
    (p : Configuration n) :
    dbarComponent (configurationCauchyGreenPotential j χ a) j p = χ (p j) * a p := by
  let F : Configuration n × ℂ → ℂ := localizedCauchyGreenPotential χ
    (fun q z => a (dolbeaultReplaceCoordinate j (q, z)))
  have hs : ContDiff ℝ ∞ (Function.uncurry
      (fun q z => a (dolbeaultReplaceCoordinate j (q, z)))) := by
    simpa only [Function.uncurry] using! ha.comp (dolbeaultReplaceCoordinate j).contDiff
  have hF : ContDiff ℝ ∞ F := localizedCauchyGreenPotential_contDiff χ _ hχ hc hs
  let D : Configuration n →L[ℝ] Configuration n × ℂ :=
    (ContinuousLinearMap.id ℝ _).prod (ContinuousLinearMap.proj j)
  have hh := (hF.differentiable (by simp) (p, p j)).hasFDerivAt.comp p D.hasFDerivAt
  have hh' : HasFDerivAt (configurationCauchyGreenPotential j χ a)
      ((fderiv ℝ F (p, p j)).comp D) p := by
    simpa only [configurationCauchyGreenPotential, F, D, Function.comp_def,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.proj_apply] using! hh
  have hv (w : ℂ) : fderiv ℝ (configurationCauchyGreenPotential j χ a) p
      (coordinateDirection j w) = fderiv ℝ F (p, p j) (0, w) := by
    rw [hh'.fderiv]
    change fderiv ℝ F (p, p j) (D (coordinateDirection j w)) = _
    have hD : D (coordinateDirection j w) = (coordinateDirection j w, w) := by
      simp [D, coordinateDirection]
    rw [hD]
    have hp : (coordinateDirection j w, w) = (coordinateDirection j w, 0) + (0, w) := by simp
    rw [hp, map_add]
    have hz := configurationCauchyGreen_parameter_derivative_zero j χ a hχ hc ha (p, p j) w
    change fderiv ℝ F (p, p j) (coordinateDirection j w, 0) = 0 at hz
    rw [hz, zero_add]
  simp only [dbarComponent, realCoordinateDirection, imaginaryCoordinateDirection, hv]
  change finiteComplexDbar (0, 1) (0, Complex.I) F (p, p j) = _
  rw [localizedCauchyGreenPotential_solves χ _ hχ hc hs,
    dolbeaultReplaceCoordinate_same]

/-- Actual coordinate Cauchy–Green integration preserves the other
Cauchy–Riemann equations on each parameter slice. -/
theorem configurationCauchyGreenPotential_preserves_CR_on_support {n : ℕ} (j k : Fin n)
    (hkj : k ≠ j) (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ha : ContDiff ℝ ∞ a)
    (p : Configuration n)
    (hCR : ∀ z ∈ tsupport χ,
      dbarComponent a k (dolbeaultReplaceCoordinate j (p, z)) = 0) :
    dbarComponent (configurationCauchyGreenPotential j χ a) k p = 0 := by
  let A : Configuration n → ℂ → ℂ := fun q z => a (dolbeaultReplaceCoordinate j (q, z))
  let F : Configuration n × ℂ → ℂ := localizedCauchyGreenPotential χ A
  have hs : ContDiff ℝ ∞ (Function.uncurry A) := by
    simpa only [A, Function.uncurry] using! ha.comp (dolbeaultReplaceCoordinate j).contDiff
  have hF : ContDiff ℝ ∞ F := localizedCauchyGreenPotential_contDiff χ A hχ hc hs
  let D : Configuration n →L[ℝ] Configuration n × ℂ :=
    (ContinuousLinearMap.id ℝ _).prod (ContinuousLinearMap.proj j)
  have hh := (hF.differentiable (by simp) (p, p j)).hasFDerivAt.comp p D.hasFDerivAt
  have hh' : HasFDerivAt (configurationCauchyGreenPotential j χ a)
      ((fderiv ℝ F (p, p j)).comp D) p := by
    simpa only [configurationCauchyGreenPotential, F, A, D, Function.comp_def,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.proj_apply] using! hh
  have hv (w : ℂ) : fderiv ℝ (configurationCauchyGreenPotential j χ a) p
      (coordinateDirection k w) = fderiv ℝ F (p, p j) (coordinateDirection k w, 0) := by
    rw [hh'.fderiv]
    change fderiv ℝ F (p, p j) (D (coordinateDirection k w)) = _
    simp [D, coordinateDirection, Ne.symm hkj]
  have h := localizedCauchyGreenPotential_transverse_CR_on_support χ A hχ hc hs
    (coordinateDirection k 1) (coordinateDirection k Complex.I) (p, p j) (fun z hz => by
      have hd := (ha.differentiable (by simp)
        (dolbeaultReplaceCoordinate j (p, z))).hasFDerivAt.comp (p, z)
          (dolbeaultReplaceCoordinate j).hasFDerivAt
      have hd' : HasFDerivAt (Function.uncurry A)
          ((fderiv ℝ a (dolbeaultReplaceCoordinate j (p, z))).comp
            (dolbeaultReplaceCoordinate j)) (p, z) := by
        simpa only [A, Function.uncurry, Function.comp_def] using! hd
      simp only [finiteComplexDbar, hd'.fderiv, ContinuousLinearMap.comp_apply,
        dolbeaultReplaceCoordinate_direction_other j k hkj]
      exact hCR z hz)
  simpa only [dbarComponent, realCoordinateDirection, imaginaryCoordinateDirection,
    hv, finiteComplexDbar, F] using! h

theorem configurationCauchyGreenPotential_preserves_CR {n : ℕ} (j k : Fin n)
    (hkj : k ≠ j) (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ha : ContDiff ℝ ∞ a)
    (p : Configuration n)
    (hCR : ∀ z, dbarComponent a k (dolbeaultReplaceCoordinate j (p, z)) = 0) :
    dbarComponent (configurationCauchyGreenPotential j χ a) k p = 0 :=
  configurationCauchyGreenPotential_preserves_CR_on_support j k hkj χ a hχ hc ha p
    (fun z _ => hCR z)

end
end GinibrePoincare
