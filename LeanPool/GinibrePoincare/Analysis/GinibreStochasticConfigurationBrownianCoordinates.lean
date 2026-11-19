/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticConfigurationBrownianCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticConfigurationBrownianBracket
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyCrossBracket

/-! All real coordinates and mixed brackets of the actual configuration noise. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The real coordinate `p` of the configuration Brownian noise: the real part (`p.2 = 0`) or the
imaginary part (otherwise) of particle `p.1`. -/
def ginibreConfigurationBrownianRealCoordinate {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (p : Fin n × Fin 2)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if p.2 = 0 then (ginibreConfigurationBrownianNoise n B α ω t p.1).re
    else (ginibreConfigurationBrownianNoise n B α ω t p.1).im

theorem ginibreConfigurationBrownianRealCoordinate_eq {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (p : Fin n × Fin 2)
    (t : ℝ≥0) (ω : Ω) :
    ginibreConfigurationBrownianRealCoordinate n B α p t ω =
      Real.sqrt (2*α/(n : ℝ)^2)*B p t ω := by
  rcases p with ⟨j, k⟩
  fin_cases k <;> simp [ginibreConfigurationBrownianRealCoordinate,
      ginibreConfigurationBrownianNoise,
    Complex.mul_re, Complex.mul_im]

theorem ginibreConfigurationBrownianRealCoordinate_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (p : Fin n × Fin 2) :
    Martingale (ginibreConfigurationBrownianRealCoordinate n B α p)
      (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_coordinate_martingale B P hB hind p).smul
    (Real.sqrt (2*α/(n : ℝ)^2))
  convert! h using 1
  funext t ω
  simp only [ginibreConfigurationBrownianRealCoordinate_eq, Pi.smul_apply, smul_eq_mul]

theorem ginibreConfigurationBrownianRealCoordinate_cross_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (p q : Fin n × Fin 2) (hpq : p ≠ q) :
    Martingale (fun t ω => ginibreConfigurationBrownianRealCoordinate n B α p t ω*
      ginibreConfigurationBrownianRealCoordinate n B α q t ω)
      (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_cross_martingale B P hB hind p q hpq).smul
    ((Real.sqrt (2*α/(n : ℝ)^2))^2)
  convert! h using 1
  funext t ω
  simp only [ginibreConfigurationBrownianRealCoordinate_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem ginibreConfigurationBrownianRealCoordinate_square_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0) (p : Fin n × Fin 2) :
    Martingale (fun t ω => (ginibreConfigurationBrownianRealCoordinate n B α p t ω)^2-
      (2*(α : ℝ)/(n : ℝ)^2)*(t : ℝ)) (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_square_martingale B P hB hind p).smul
    (2*(α : ℝ)/(n : ℝ)^2)
  have hσ : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2 = 2*(α : ℝ)/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  convert! h using 1
  funext t ω
  simp only [ginibreConfigurationBrownianRealCoordinate_eq, mul_pow, hσ, Pi.smul_apply, smul_eq_mul]
  ring

end
end GinibrePoincare
