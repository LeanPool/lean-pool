/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianHermitePhase.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction

/-! # Exact global phase characters of all complex Hermite modes -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

private theorem phase_powers_cancel (u : ℂ) (hu : ‖u‖ = 1) (p q k : ℕ)
    (hkp : k ≤ p) (hkq : k ≤ q) :
    u ^ (p - k) * (conj u) ^ (q - k) = u ^ p * (conj u) ^ q := by
  have huc : u * conj u = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hu]
    norm_num
  calc
    _ = (u ^ (p - k) * (conj u) ^ (q - k)) * (u * conj u) ^ k := by rw [huc]; simp
    _ = (u ^ (p - k) * u ^ k) * ((conj u) ^ (q - k) * (conj u) ^ k) := by rw [mul_pow]; ring
    _ = _ := by rw [← pow_add, ← pow_add, Nat.sub_add_cancel hkp, Nat.sub_add_cancel hkq]

/-- Every raw complex Hermite polynomial has its true mixed phase character. -/
theorem complexHermite_eval_globalPhase (ρ : ℝ) (p q : ℕ) (u z : ℂ) (hu : ‖u‖ = 1) :
    ComplexHermite.eval ρ p q (u * z) =
      (u ^ p * (conj u) ^ q) * ComplexHermite.eval ρ p q z := by
  unfold ComplexHermite.eval ComplexHermite.raw
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_pow, ComplexHermite.Z, ComplexHermite.W, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkmin : k ≤ min p q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hphase := phase_powers_cancel u hu p q k (hkmin.trans (min_le_left _ _))
    (hkmin.trans (min_le_right _ _))
  calc
    _ = (u ^ (p - k) * (conj u) ^ (q - k)) *
      (((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) * (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ) *
        z ^ (p - k) * (conj z) ^ (q - k)) := by ring
    _ = _ := by rw [hphase]

/-- The normalized mixed Hermite function has the same phase character. -/
theorem normalizedEval_globalPhase (n : ℕ) (hn : 0 < n) (p q : ℕ)
    (u z : ℂ) (hu : ‖u‖ = 1) :
    ComplexHermite.normalizedEval n hn p q (u * z) =
      (u ^ p * (conj u) ^ q) * ComplexHermite.normalizedEval n hn p q z := by
  unfold ComplexHermite.normalizedEval ComplexHermite.normalized
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  change _ * ComplexHermite.eval ((n : ℝ)⁻¹) p q (u * z) =
    (u ^ p * (conj u) ^ q) * (_ * ComplexHermite.eval ((n : ℝ)⁻¹) p q z)
  rw [complexHermite_eval_globalPhase _ p q u z hu]
  ring

/-- Every multivariate mixed mode has its exact holomorphic-antiholomorphic character. -/
theorem multivariateNormalized_globalPhase (n : ℕ) (hn : 0 < n) (p q : Fin n → ℕ)
    (u : ℂ) (hu : ‖u‖ = 1) (z : Configuration n) :
    ComplexHermite.multivariateNormalized n hn p q (globalPhase u z) =
      (u ^ totalHolomorphicDegree p * (conj u) ^ totalHolomorphicDegree q) *
        ComplexHermite.multivariateNormalized n hn p q z := by
  unfold ComplexHermite.multivariateNormalized
  simp_rw [globalPhase_apply, normalizedEval_globalPhase n hn _ _ u _ hu]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rfl

/-- Every actual Gaussian L² Hermite basis vector has the exact mixed phase character. -/
theorem gaussianGlobalPhaseL2_hermite (n : ℕ) (hn : 0 < n)
    (u : ℂ) (hu : ‖u‖ = 1) (p q : Fin n → ℕ) :
    gaussianGlobalPhaseL2 hn u hu (ComplexHermite.hermiteL2Family n hn (p, q)) =
      (u ^ totalHolomorphicDegree p * (conj u) ^ totalHolomorphicDegree q) •
        ComplexHermite.hermiteL2Family n hn (p, q) := by
  apply Lp.ext
  have hsource := (measurePreserving_globalPhase_complexGaussianMeasure hn u
    hu).quasiMeasurePreserving.ae_eq_comp
    (ComplexHermite.hermiteL2Family_coeFn n hn (p, q))
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (ComplexHermite.hermiteL2Family n hn (p, q))
    (measurePreserving_globalPhase_complexGaussianMeasure hn u hu), hsource,
    ComplexHermite.hermiteL2Family_coeFn n hn (p, q),
    Lp.coeFn_smul (u ^ totalHolomorphicDegree p * (conj u) ^ totalHolomorphicDegree q)
      (ComplexHermite.hermiteL2Family n hn (p, q))] with z hp hs ht hm
  change ComplexHermite.hermiteL2Family n hn (p, q) (globalPhase u z) =
    ComplexHermite.multivariateNormalized n hn p q (globalPhase u z) at hs
  change ComplexHermite.hermiteL2Family n hn (p, q) z =
    ComplexHermite.multivariateNormalized n hn p q z at ht
  change (gaussianGlobalPhaseL2 hn u hu (ComplexHermite.hermiteL2Family n hn (p, q))) z = _ at hp
  rw [hp, hm]
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [hs, ht]
  exact multivariateNormalized_globalPhase n hn p q u hu z

/-- Global phase rotations preserve every actual fixed antiholomorphic degree space. -/
theorem gaussianGlobalPhaseL2_mem_antiDegreeClosedSpan {n : ℕ} (hn : 0 < n)
    (d : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    {x : Lp ℂ 2 (complexGaussianMeasure n)}
    (hx : x ∈ ComplexHermite.hermiteAntiDegreeClosedSpan n hn d) :
    gaussianGlobalPhaseL2 hn u hu x ∈ ComplexHermite.hermiteAntiDegreeClosedSpan n hn d := by
  let T := gaussianGlobalPhaseL2 hn u hu
  let M := ComplexHermite.hermiteAntiDegreeSpan n hn d
  have hspan : Set.MapsTo T (M : Set _) (M : Set _) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨p, q⟩, hdeg, rfl⟩ := hy
      rw [gaussianGlobalPhaseL2_hermite n hn u hu p q]
      exact M.smul_mem _ (Submodule.subset_span ⟨(p, q), hdeg, rfl⟩)
    | zero => simp [T, M]
    | add a b ha hb ihA ihB =>
      rw [map_add]
      exact M.add_mem ihA ihB
    | smul c a ha ih =>
      rw [map_smul]
      exact M.smul_mem c ih
  exact (Set.MapsTo.closure hspan T.continuous) hx

/-- Conjugate phases give the actual inverse pullback on all Gaussian L². -/
theorem gaussianGlobalPhaseL2_conj_inverse {n : ℕ} (hn : 0 < n)
    (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianGlobalPhaseL2 hn u hu
      (gaussianGlobalPhaseL2 hn (conj u) (by simpa using hu) x) = x := by
  have huc : conj u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, hu]
    norm_num
  change Lp.compMeasurePreserving (globalPhase u)
    (measurePreserving_globalPhase_complexGaussianMeasure hn u hu)
    (Lp.compMeasurePreserving (globalPhase (conj u))
      (measurePreserving_globalPhase_complexGaussianMeasure hn (conj u) (by simpa using hu)) x) = x
  rw [← Lp.compMeasurePreserving_comp_apply x]
  have he : globalPhase (conj u) ∘ globalPhase u = (id : Configuration n → Configuration n) := by
    funext z
    simp only [Function.comp_apply, globalPhase_mul, huc, globalPhase_one, id_eq]
  simp [he]

/-- Actual Gaussian Hermite antiholomorphic projections commute with phase rotations. -/
theorem gaussianGlobalPhaseL2_comm_antiDegreeProjection {n : ℕ} (hn : 0 < n)
    (d : ℕ) (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianGlobalPhaseL2 hn u hu (ComplexHermite.hermiteAntiDegreeProjection n hn d x) =
      ComplexHermite.hermiteAntiDegreeProjection n hn d (gaussianGlobalPhaseL2 hn u hu x) := by
  let U : Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) :=
    ComplexHermite.hermiteAntiDegreeClosedSpan n hn d
  let T := gaussianGlobalPhaseL2 hn u hu
  have hmap : U.map T.toLinearMap = U := by
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact gaussianGlobalPhaseL2_mem_antiDegreeClosedSpan hn d u hu hz
    · intro y hy
      refine ⟨gaussianGlobalPhaseL2 hn (conj u) (by simpa using hu) y,
        gaussianGlobalPhaseL2_mem_antiDegreeClosedSpan hn d (conj u) (by simpa using hu) hy, ?_⟩
      exact gaussianGlobalPhaseL2_conj_inverse hn u hu y
  let : (U.map T.toLinearMap).HasOrthogonalProjection := hmap.symm ▸ inferInstance
  calc
    T (U.starProjection x) = (U.map T.toLinearMap).starProjection (T x) := T.map_starProjection U x
    _ = U.starProjection (T x) := by simp only [hmap]

end
end GinibrePoincare
