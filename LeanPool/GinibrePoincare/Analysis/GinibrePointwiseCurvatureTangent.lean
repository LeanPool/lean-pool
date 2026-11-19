/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePointwiseCurvatureTangent.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseCurvature
public import LeanPool.GinibrePoincare.Analysis.EquilibriumFactorization

/-! Actual Hessian in arbitrary directions, including the center-zero tangent space. -/

@[expose] public section
open scoped BigOperators ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreHamiltonian_directional_hessian {n : ℕ} (z v : Configuration n)
    (hz : CollisionFree z) :
    secondDirectionalDerivative (ginibreHamiltonian n) v z =
      ∑ j : Fin n, (2*(n : ℝ)*(conj (v j)*v j).re +
        2*∑ k ∈ Finset.univ.erase j,
          (v j*(z j-z k)⁻¹*(v j-v k)*(z j-z k)⁻¹).re) := by
  have hsum : (∑ j : Fin n, coordinateDirection j (v j)) = v := by
    ext i
    simp [coordinateDirection]
  have heq : (fun x => fderiv ℝ (ginibreHamiltonian n) x v) =
      fun x => ∑ j : Fin n, fderiv ℝ (ginibreHamiltonian n) x (coordinateDirection j (v j)) := by
    funext x
    calc
      _ = fderiv ℝ (ginibreHamiltonian n) x (∑ j, coordinateDirection j (v j)) := by rw [hsum]
      _ = _ := by rw [map_sum]
  have hd (j : Fin n) : DifferentiableAt ℝ
      (fun x => fderiv ℝ (ginibreHamiltonian n) x (coordinateDirection j (v j))) z := by
    exact (((ginibreHamiltonian_contDiffAt n z hz).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  unfold secondDirectionalDerivative
  rw [heq, fderiv_fun_sum (fun j _ => hd j)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact ginibreHamiltonian_coordinate_hessian z v hz j (v j)

theorem ginibreHamiltonian_real_configuration_imaginary_direction {n : ℕ}
    (x u : Fin n → ℝ) (hx : Function.Injective x) :
    secondDirectionalDerivative (ginibreHamiltonian n) (fun i => (u i : ℂ)*Complex.I)
      (fun i => (x i : ℂ)) =
      2*(n : ℝ)*(∑ i, (u i)^2) -
        2*∑ i, ∑ k ∈ Finset.univ.erase i,
          u i*(u i-u k)*((x i-x k)⁻¹)^2 := by
  have hz : CollisionFree (fun i => (x i : ℂ)) := by
    intro i k h
    exact hx (Complex.ofReal_injective h)
  rw [ginibreHamiltonian_directional_hessian _ _ hz]
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, zero_mul, mul_zero, add_zero, zero_add,
    mul_one, sub_zero, zero_sub]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, pow_two]
  simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- A fixed genuine center-zero imaginary direction; its squared Euclidean norm is two. -/
def ginibreCurvaturePairDirection {n : ℕ} (j k : Fin n) : Configuration n :=
  fun i => ((if i=j then (1 : ℝ) else if i=k then -1 else 0) : ℂ)*Complex.I

theorem ginibreCurvaturePairDirection_sum {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    coordinateSum (ginibreCurvaturePairDirection j k) = 0 := by
  have he : ginibreCurvaturePairDirection j k =
      imaginaryCoordinateDirection j-imaginaryCoordinateDirection k := by
    funext i
    simp only [ginibreCurvaturePairDirection, imaginaryCoordinateDirection, coordinateDirection,
      Pi.sub_apply]
    split_ifs <;> simp_all
  rw [he]
  simp [coordinateSum, imaginaryCoordinateDirection, coordinateDirection,
    Finset.sum_sub_distrib]

theorem ginibreCurvaturePairDirection_norm {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    configurationNormSq (ginibreCurvaturePairDirection j k) = 2 := by
  unfold configurationNormSq ginibreCurvaturePairDirection
  have he (i : Fin n) :
      Complex.normSq (((if i=j then (1 : ℝ) else if i=k then -1 else 0) : ℂ)*Complex.I) =
        (if i=j then (1 : ℝ) else 0)+(if i=k then (1 : ℝ) else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  norm_num [Finset.sum_add_distrib]

theorem ginibreHamiltonian_pair_direction_le {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (j k : Fin n) (hjk : j ≠ k) :
    secondDirectionalDerivative (ginibreHamiltonian n) (ginibreCurvaturePairDirection j k)
      (fun i => (x i : ℂ)) ≤ 4*(n : ℝ)-4*((x j-x k)⁻¹)^2 := by
  let u : Fin n → ℝ := fun i => if i=j then 1 else if i=k then -1 else 0
  have hs : (∑ i, (u i)^2) = 2 := by
    have he (i : Fin n) : (u i)^2 = (if i=j then (1 : ℝ) else 0)+(if i=k then 1 else 0) := by
      dsimp [u]
      split_ifs <;> simp_all
    simp_rw [he]
    norm_num [Finset.sum_add_distrib]
  have he : ginibreCurvaturePairDirection j k = fun i => (u i : ℂ)*Complex.I := by
    funext i
    dsimp [ginibreCurvaturePairDirection, u]
    split_ifs <;> simp
  rw [he]
  rw [ginibreHamiltonian_real_configuration_imaginary_direction x u hx, hs]
  have hn (i l : Fin n) : 0 ≤ u i*(u i-u l)*((x i-x l)⁻¹)^2 := by
    have hp : 0 ≤ u i*(u i-u l) := by
      dsimp [u]
      split_ifs <;> norm_num
    exact mul_nonneg hp (sq_nonneg _)
  have hi : 2*((x j-x k)⁻¹)^2 ≤
      ∑ i, ∑ l ∈ Finset.univ.erase i, u i*(u i-u l)*((x i-x l)⁻¹)^2 := by
    have hinner := Finset.single_le_sum (fun l _ => hn j l)
      (Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩)
    have houter : (∑ l ∈ Finset.univ.erase j, u j*(u j-u l)*((x j-x l)⁻¹)^2) ≤
        ∑ i, ∑ l ∈ Finset.univ.erase i, u i*(u i-u l)*((x i-x l)⁻¹)^2 :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun l _ => hn i l)) (Finset.mem_univ j)
    exact le_trans (by simpa [u, hjk, hjk.symm, show (1 : ℝ)+1=2 by norm_num] using hinner) houter
  linarith

/-- Even on the genuine center-zero hyperplane, normalized Hessian Rayleigh
quotients have no real lower bound. The displayed tangent vector has norm² two. -/
theorem ginibre_recentered_pointwise_curvature_unbounded_below {n : ℕ}
    (hn : 2 ≤ n) (B : ℝ) :
    ∃ z v : Configuration n, CollisionFree z ∧ coordinateSum z = 0 ∧
      coordinateSum v = 0 ∧ configurationNormSq v = 2 ∧
      secondDirectionalDerivative (ginibreHamiltonian n) v z /
        ((n : ℝ)*configurationNormSq v) < B := by
  let C : ℝ := 2*(n : ℝ)*B
  let L : ℝ := |C|+4*(n : ℝ)+2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hL : 0 < L := by dsimp [L]; positivity
  have hL0 : L ≠ 0 := ne_of_gt hL
  let a : ℝ := (∑ i : Fin n, (i.val : ℝ)/L)/(n : ℝ)
  let x : Fin n → ℝ := fun i => (i.val : ℝ)/L-a
  have hx : Function.Injective x := by
    intro i k h
    apply Fin.ext
    have he : (i.val : ℝ)/L = (k.val : ℝ)/L := by dsimp [x] at h; linarith
    exact_mod_cast (div_left_inj' hL0).mp he
  let j : Fin n := ⟨0, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  have hjk : j ≠ k := by intro h; have := congrArg Fin.val h; simp [j, k] at this
  have hp := ginibreHamiltonian_pair_direction_le x hx j k hjk
  have hid : (x j-x k)⁻¹ = -L := by
    dsimp [x, j, k]
    norm_num only [Nat.cast_zero, Nat.cast_one]
    rw [show (0 : ℝ)/L-a-((1 : ℝ)/L-a) = -(1/L) by ring]
    simp
  rw [hid] at hp
  refine ⟨fun i => (x i : ℂ), ginibreCurvaturePairDirection j k, ?_, ?_,
    ginibreCurvaturePairDirection_sum j k hjk, ginibreCurvaturePairDirection_norm j k hjk, ?_⟩
  · intro i k h
    exact hx (Complex.ofReal_injective h)
  · unfold coordinateSum
    rw [← Complex.ofReal_sum]
    norm_cast
    change (∑ i, x i) = 0
    dsimp [x]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    dsimp [a]
    field_simp
    ring
  · rw [ginibreCurvaturePairDirection_norm j k hjk]
    apply (div_lt_iff₀ (mul_pos hnpos (by norm_num : (0 : ℝ)<2))).mpr
    have hC : -|C| ≤ C := neg_abs_le C
    have hL1 : 1 ≤ L := by dsimp [L]; nlinarith [abs_nonneg C]
    have hsq : L ≤ L^2 := by nlinarith
    have ht : 4*(n : ℝ)-4*(-L)^2 < C := by
      dsimp [L] at hsq
      nlinarith
    have hfinal := lt_of_le_of_lt hp ht
    dsimp [C] at hfinal
    nlinarith

end
end GinibrePoincare
