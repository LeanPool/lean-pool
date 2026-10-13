/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.IterationStep
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ShellPerturbation

/-!
# DivergenceContraction

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The divergence of a matrix field is a contraction of its gradient

The perturbation step of the injection estimate feeds the field
`∇ · (k_m - k_n)` into a Leibniz rule, while the size bounds available on the
large-scale event are bounds on the full gradient `∇(k_m - k_n)`.  The two are
related by an algebraic contraction: if `k` is differentiable at `x` with
derivative `D`, then

```text
  (∇ · k)_j (x) = ∑_i (D e_i)_{i j} ,
```

a linear function of `D` whose ambient norm is at most `d ‖D‖`.  Since the
contraction is linear, the same factor `d` transfers a two-point bound on the
gradient into a two-point bound on the divergence, so the `1/2`-Hölder gauge of
the divergence is at most `d` times that of the gradient.

The second half of the file specializes both bounds to the stream increment
`k_m - k_n` on the cube `y + □_n`, where the gradient bounds are those of
`ShellPerturbation.lean`, and records the two structural facts about the
increment that the iteration step consumes: its entries are `C¹` and its values
are antisymmetric.

## Main results

* `norm_matFieldDiv_le` — `‖(∇ · k)(x)‖ ≤ d ‖D‖`.
* `norm_matFieldDiv_sub_le` — the same factor on a difference of two points.
* `norm_matFieldDiv_cutoff_sub_le`, `holderSeminormBoundOn_matFieldDiv_cutoff_sub`
  — the two sizes of `∇ · (k_m - k_n)` on `y + □_n`, uniform in `m`.
* `contDiff_one_cutoff_sub_entry`, `matTranspose_cutoff_sub` — the regularity
  and the antisymmetry of `k_m - k_n`.

## References

* ABK26, the perturbation step of the injection estimate of Section 5.1.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open Algsuperdiff.Section3.Provider.Stream
open scoped Matrix.Norms.Elementwise ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. The contraction and its size -/

/-- Evaluation of one entry of a matrix, as a continuous linear map. -/
def matEntryCLM (d : ℕ) (i j : Fin d) : Mat d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)

private theorem matEntryCLM_apply (d : ℕ) (i j : Fin d) (A : Mat d) :
    matEntryCLM d i j A = A i j := rfl

/-- The ambient norm of a coordinate vector of `Vec d` is at most one. -/
private theorem norm_basisVec_le_one (i : Fin d) : ‖(basisVec i : Vec d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  rcases eq_or_ne j i with h | h
  · subst h
    simp [basisVec]
  · simp [basisVec, h]

/-- One entry of the derivative of a matrix field, read off the Fréchet
derivative. -/
private theorem fderiv_entry_apply {k : Vec d → Mat d} {D : Vec d →L[ℝ] Mat d} {x : Vec d}
    (hk : HasFDerivAt k D x) (i j : Fin d) :
    fderiv ℝ (fun y => k y i j) x (basisVec i) = D (basisVec i) i j := by
  have h0 : HasFDerivAt (⇑(matEntryCLM d i j) ∘ k) ((matEntryCLM d i j).comp D) x :=
    (matEntryCLM d i j).hasFDerivAt.comp x hk
  have h : HasFDerivAt (fun y => k y i j) ((matEntryCLM d i j).comp D) x := h0
  rw [h.fderiv, ContinuousLinearMap.comp_apply, matEntryCLM_apply]

/-- **The divergence at a point is the contraction of the derivative.** -/
theorem matFieldDiv_eq_sum_apply {k : Vec d → Mat d} {D : Vec d →L[ℝ] Mat d} {x : Vec d}
    (hk : HasFDerivAt k D x) :
    matFieldDiv k x = fun j => ∑ i : Fin d, D (basisVec i) i j := by
  funext j
  rw [matFieldDiv_apply]
  exact Finset.sum_congr rfl fun i _ => fderiv_entry_apply hk i j

/-- Each entry of the value of a continuous linear map at a coordinate vector is
bounded by its operator norm. -/
private theorem abs_apply_basisVec_entry_le (D : Vec d →L[ℝ] Mat d) (i j : Fin d) :
    |D (basisVec i) i j| ≤ ‖D‖ := by
  have h1 : ‖D (basisVec i) i j‖ ≤ ‖D (basisVec i)‖ :=
    Matrix.norm_entry_le_entrywise_sup_norm _
  have h2 : ‖D (basisVec i)‖ ≤ ‖D‖ * ‖(basisVec i : Vec d)‖ := D.le_opNorm _
  have h4 : ‖D‖ * ‖(basisVec i : Vec d)‖ ≤ ‖D‖ * 1 :=
    mul_le_mul_of_nonneg_left (norm_basisVec_le_one i) (norm_nonneg _)
  rw [Real.norm_eq_abs] at h1
  linarith only [h1, h2, h4]

/-- **The divergence of a matrix field is at most `d` times its gradient.** -/
theorem norm_matFieldDiv_le {k : Vec d → Mat d} {D : Vec d →L[ℝ] Mat d} {x : Vec d}
    (hk : HasFDerivAt k D x) : ‖matFieldDiv k x‖ ≤ (d : ℝ) * ‖D‖ := by
  rw [matFieldDiv_eq_sum_apply hk]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  calc |∑ i : Fin d, D (basisVec i) i j|
      ≤ ∑ i : Fin d, |D (basisVec i) i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖D‖ := Finset.sum_le_sum fun i _ => abs_apply_basisVec_entry_le D i j
    _ = (d : ℝ) * ‖D‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The two-point form.**  The contraction is linear, so a two-point bound on
the gradient becomes a two-point bound on the divergence at the same cost `d`. -/
theorem norm_matFieldDiv_sub_le {k : Vec d → Mat d} {Dx Dz : Vec d →L[ℝ] Mat d}
    {x z : Vec d} (hx : HasFDerivAt k Dx x) (hz : HasFDerivAt k Dz z) :
    ‖matFieldDiv k x - matFieldDiv k z‖ ≤ (d : ℝ) * ‖Dx - Dz‖ := by
  have hrw : matFieldDiv k x - matFieldDiv k z = fun j => ∑ i : Fin d, (Dx - Dz) (basisVec i) i j := by
    funext j
    rw [Pi.sub_apply, matFieldDiv_eq_sum_apply hx, matFieldDiv_eq_sum_apply hz,
      ← Finset.sum_sub_distrib]
    rfl
  rw [hrw]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  calc |∑ i : Fin d, (Dx - Dz) (basisVec i) i j|
      ≤ ∑ i : Fin d, |(Dx - Dz) (basisVec i) i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖Dx - Dz‖ :=
        Finset.sum_le_sum fun i _ => abs_apply_basisVec_entry_le (Dx - Dz) i j
    _ = (d : ℝ) * ‖Dx - Dz‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ## 2. The stream increment on the cube -/

/-- The stored derivative of the increment shell field is the derivative of the
perturbation field `k_m - k_n`, in the spelling the series identification
uses. -/
private theorem hasFDerivAt_perturbation (omega : Cutoff.CutoffSample d) {n m : ℤ}
    (hnm : n ≤ m) (x : Vec d) :
    HasFDerivAt (fun z : Vec d => Cutoff.cutoff m omega z - Cutoff.cutoff n omega z)
      ((shellIncrement omega.1 n m).deriv x) x :=
  hasFDerivAt_cutoff_sub omega hnm x

/-- **The supremum size of `∇ · (k_m - k_n)` on `y + □_n`**, uniform in `m`. -/
theorem norm_matFieldDiv_cutoff_sub_le {M : ABKModel d} {n m : ℤ} {y : Vec d} {theta : ℝ}
    {omega : Cutoff.CutoffSample d} (hmem : omega ∈ largeScaleEvent M n y theta)
    (htheta : 0 ≤ theta) (hnm : n ≤ m) {x : Vec d} (hx : x ∈ cubeSetAt y n) :
    ‖matFieldDiv (fun z : Vec d => Cutoff.cutoff m omega z - Cutoff.cutoff n omega z) x‖ ≤
      (d : ℝ) * (Real.sqrt d * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) := by
  have hrpow : (0 : ℝ) < Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnn : (0 : ℝ) ≤ Real.sqrt d * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) := by
    positivity
  have hsup := (supNormOn_le_ofReal_iff hnn).1 (supNormOn_deriv_shellIncrement_le (m := m) hmem htheta)
  refine (norm_matFieldDiv_le (hasFDerivAt_perturbation omega hnm x)).trans ?_
  exact mul_le_mul_of_nonneg_left (hsup x hx) (Nat.cast_nonneg d)

/-- **The `1/2`-Hölder size of `∇ · (k_m - k_n)` on `y + □_n`**, uniform in
`m`. -/
theorem holderSeminormBoundOn_matFieldDiv_cutoff_sub {M : ABKModel d} {n m : ℤ} {y : Vec d}
    {theta : ℝ} {omega : Cutoff.CutoffSample d}
    (hmem : omega ∈ largeScaleEvent M n y theta) (htheta : 0 ≤ theta) (hnm : n ≤ m) :
    Section4.Support.HolderSeminormBoundOn (cubeSetAt y n) (1 / 2)
      ((d : ℝ) * (Real.sqrt 2 * ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ))))))
      (matFieldDiv fun z : Vec d => Cutoff.cutoff m omega z - Cutoff.cutoff n omega z) := by
  intro x hx z hz
  have hgrad := holderSeminormBoundOn_half_deriv_shellIncrement (m := m) hmem htheta x hx z hz
  have hstep := norm_matFieldDiv_sub_le (hasFDerivAt_perturbation omega hnm x)
    (hasFDerivAt_perturbation omega hnm z)
  have hmul := mul_le_mul_of_nonneg_left hgrad (Nat.cast_nonneg (α := ℝ) d)
  calc ‖matFieldDiv (fun z : Vec d => Cutoff.cutoff m omega z - Cutoff.cutoff n omega z) x -
          matFieldDiv (fun z : Vec d => Cutoff.cutoff m omega z - Cutoff.cutoff n omega z) z‖
      ≤ (d : ℝ) * ‖(shellIncrement omega.1 n m).deriv x -
          (shellIncrement omega.1 n m).deriv z‖ := hstep
    _ ≤ (d : ℝ) * (Real.sqrt 2 *
          ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)))) *
            ‖x - z‖ ^ (1 / 2 : ℝ)) := hmul
    _ = (d : ℝ) * (Real.sqrt 2 *
          ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ))))) *
            ‖x - z‖ ^ (1 / 2 : ℝ) := by ring

/-! ## 3. Regularity and antisymmetry of the perturbation field -/

/-- The entries of `k_m - k_n` are continuously differentiable. -/
theorem contDiff_one_cutoff_sub_entry (omega : Cutoff.CutoffSample d) {n m : ℤ}
    (hnm : n ≤ m) (p q : Fin d) :
    ContDiff ℝ 1 fun x : Vec d => (Cutoff.cutoff m omega x - Cutoff.cutoff n omega x) p q := by
  have hfun : (fun x : Vec d => (Cutoff.cutoff m omega x - Cutoff.cutoff n omega x) p q) =
      fun x : Vec d => shellIncrement omega.1 n m x p q := by
    funext x
    rw [shellIncrement_apply_eq_cutoff_sub omega hnm x]
  rw [hfun]
  exact contDiff_one_shellIncrement_entry omega.1 n m p q

/-- The values of `k_m - k_n` are antisymmetric. -/
theorem matTranspose_cutoff_sub (omega : Cutoff.CutoffSample d) {n m : ℤ} (hnm : n ≤ m)
    (x : Vec d) :
    matTranspose (Cutoff.cutoff m omega x - Cutoff.cutoff n omega x) =
      -(Cutoff.cutoff m omega x - Cutoff.cutoff n omega x) := by
  have h := matTranspose_shellIncrement omega.1 n m x
  rwa [shellIncrement_apply_eq_cutoff_sub omega hnm x] at h

end

end Algsuperdiff.Section5.Provider
