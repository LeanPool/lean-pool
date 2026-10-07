/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.DivCurlSecond
public import LeanPool.CIVAxisymmetric.Closure.CutoffCommutatorSecond

/-!
# The Hessian half of `eq:aniso:closure:elliptic`

This file proves the second elliptic bound of `eq:aniso:closure:elliptic`, the estimate the
gradient bound `integral_sq_fderiv_smul_le` leaves open: for a field `v` smooth and divergence
free on an open set `U` and a cutoff `χ` supported in `U`,

`∫ |∇²(χ v)|² ≤ 4 ∫ χ² |∇ curl v|² + 24 N² ∫ |∇χ|² + 24 N² ∫ |∇²χ|²`,

where `N` bounds the first-order jet `|v|² + |∇v|²` of `v` on the support of `∇χ`. The first term
on the right is the enstrophy dissipation `M t` of `lem:aniso:closure`.

The proof applies the second-order identity `integral_sq_fderiv_fderiv_eq_curl_add_div` to the
globally smooth compactly supported field `χ v`, which splits `∫ |∇²(χv)|²` as
`∫ |∇ curl (χv)|² + ∫ |∇ div (χv)|²`, and then expands each half by the Leibniz rule:

* `curl (χ v) = χ curl v + ∇χ × v`, so one more derivative produces four terms, three of which
  carry a derivative of `χ` and are therefore supported where the jet bound applies;
* `div (χ v) = ∇χ · v` on `U`, since `v` is divergence free there, so one more derivative
  produces two terms, both carrying a derivative of `χ`.

The cross-product terms are controlled by `sum_sq_cross3_le`, and the dot-product term by the
Lagrange identity.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### Regularity of the curl on the smoothness set -/

/-- A coordinate derivative of a scalar smooth on an open set is smooth there. -/
theorem contDiffOn_fderiv_scalar_apply {G : Vec3 → ℝ} {U : Set Vec3} (hU : IsOpen U)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) (k : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => fderiv ℝ G x (basisVec k)) U :=
  (hG.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

/-- A component of the curl of a field smooth on an open set is smooth there. -/
theorem contDiffOn_curlVec_comp {V : Vec3 → Vec3} {U : Set Vec3} (hU : IsOpen U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => curlVec V y i) U := by
  fin_cases i
  · exact (contDiffOn_fderiv_comp_apply hU hV 2 1).sub (contDiffOn_fderiv_comp_apply hU hV 1 2)
  · exact (contDiffOn_fderiv_comp_apply hU hV 0 2).sub (contDiffOn_fderiv_comp_apply hU hV 2 0)
  · exact (contDiffOn_fderiv_comp_apply hU hV 1 0).sub (contDiffOn_fderiv_comp_apply hU hV 0 1)

/-- The curl of a field vanishes near any point outside the support of the field, so all of its
derivatives vanish there too. -/
private lemma fderiv_curlVec_eq_zero_of_notMem {Z : Vec3 → Vec3} {x : Vec3}
    (hx : x ∉ tsupport Z) (i k : Fin 3) :
    fderiv ℝ (fun y : Vec3 => curlVec Z y i) x (basisVec k) = 0 := by
  have hEq : (fun y : Vec3 => curlVec Z y i) =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport Z).isOpen_compl.mem_nhds hx] with y hy
    have hz : ∀ a : Fin 3, fderiv ℝ (fun z : Vec3 => Z z a) y = 0 := by
      intro a
      have hEqa : (fun z : Vec3 => Z z a) =ᶠ[nhds y] fun _ : Vec3 => (0 : ℝ) := by
        filter_upwards [eventuallyEq_zero_nhds_of_notMem_tsupport Z hy] with z hz'
        rw [hz']
        rfl
      rw [hEqa.fderiv_eq]
      simp
    fin_cases i <;> simp [curlVec, hz]
  rw [hEq.fderiv_eq]
  simp

/-! ### One derivative of the cross-product term -/

/-- The Leibniz rule for a cross product of two fields, componentwise. -/
private lemma fderiv_cross3_apply (g V : Vec3 → Vec3) (i k : Fin 3) {x : Vec3}
    (hg : ∀ a : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => g y a) x)
    (hV : ∀ a : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => V y a) x) :
    fderiv ℝ (fun y : Vec3 => cross3 (g y) (V y) i) x (basisVec k)
      = cross3 (partialVec g k x) (V x) i + cross3 (g x) (partialVec V k x) i := by
  have hprod : ∀ a b : Fin 3, fderiv ℝ (fun y : Vec3 => g y a * V y b) x (basisVec k)
      = fderiv ℝ (fun y : Vec3 => g y a) x (basisVec k) * V x b
        + g x a * fderiv ℝ (fun y : Vec3 => V y b) x (basisVec k) := by
    intro a b
    rw [fderiv_fun_mul (hg a) (hV b)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hsub : ∀ a b : Fin 3,
      fderiv ℝ (fun y : Vec3 => g y a * V y b - g y b * V y a) x (basisVec k)
        = (fderiv ℝ (fun y : Vec3 => g y a) x (basisVec k) * V x b
            + g x a * fderiv ℝ (fun y : Vec3 => V y b) x (basisVec k))
          - (fderiv ℝ (fun y : Vec3 => g y b) x (basisVec k) * V x a
            + g x b * fderiv ℝ (fun y : Vec3 => V y a) x (basisVec k)) := by
    intro a b
    rw [fderiv_fun_sub ((hg a).fun_mul (hV b)) ((hg b).fun_mul (hV a)), sub_apply,
      hprod a b, hprod b a]
  have hentry : ∀ a b : Fin 3,
      fderiv ℝ (fun y : Vec3 => g y a * V y b - g y b * V y a) x (basisVec k)
        = (fderiv ℝ (fun y : Vec3 => g y a) x (basisVec k) * V x b
            - fderiv ℝ (fun y : Vec3 => g y b) x (basisVec k) * V x a)
          + (g x a * fderiv ℝ (fun y : Vec3 => V y b) x (basisVec k)
            - g x b * fderiv ℝ (fun y : Vec3 => V y a) x (basisVec k)) := by
    intro a b
    rw [hsub a b]
    ring
  fin_cases i
  · exact hentry 1 2
  · exact hentry 2 0
  · exact hentry 0 1

/-- A component of a cross product of two fields differentiable at a point is differentiable
there. -/
private lemma differentiableAt_cross3_comp (g V : Vec3 → Vec3) (i : Fin 3) {x : Vec3}
    (hg : ∀ a : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => g y a) x)
    (hV : ∀ a : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => V y a) x) :
    DifferentiableAt ℝ (fun y : Vec3 => cross3 (g y) (V y) i) x := by
  have hentry : ∀ a b : Fin 3,
      DifferentiableAt ℝ (fun y : Vec3 => g y a * V y b - g y b * V y a) x := fun a b =>
    ((hg a).fun_mul (hV b)).fun_sub ((hg b).fun_mul (hV a))
  fin_cases i
  · exact hentry 1 2
  · exact hentry 2 0
  · exact hentry 0 1

/-! ### One derivative of the curl and the divergence of a cutoff product -/

/-- **One derivative of the curl of a cutoff product.** On the set where the field is smooth,
`∂_k curl(χ v)` splits into four terms: two carrying the cutoff undifferentiated or once
differentiated against `curl v`, and two cross products carrying a derivative of the cutoff. -/
private lemma fderiv_curlVec_smul_apply (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3)
    (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (i k : Fin 3) {x : Vec3} (hx : x ∈ U) :
    fderiv ℝ (fun y : Vec3 => curlVec (fun z : Vec3 => w z • V z) y i) x (basisVec k)
      = gradVec w x k * curlVec V x i
        + w x * fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)
        + cross3 (partialVec (gradVec w) k x) (V x) i
        + cross3 (gradVec w x) (partialVec V k x) i := by
  have hwdiff : ∀ y : Vec3, DifferentiableAt ℝ w y := fun y => hw.differentiable (by simp) y
  have hVdiff : ∀ y ∈ U, ∀ a : Fin 3, DifferentiableAt ℝ (fun z : Vec3 => V z a) y :=
    fun y hy a => (((contDiffOn_pi.mp hV) a).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hy)
  have hgdiff : ∀ a : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => gradVec w y a) x := fun a =>
    (contDiff_fderiv_apply_scalar w hw a).differentiable (by simp) x
  have hVd : ∀ a : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => V y a) x := hVdiff x hx
  have hAdiff : DifferentiableAt ℝ (fun y : Vec3 => curlVec V y i) x :=
    ((contDiffOn_curlVec_comp hU hV i).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hx)
  have hBdiff : DifferentiableAt ℝ (fun y : Vec3 => cross3 (gradVec w y) (V y) i) x :=
    differentiableAt_cross3_comp (gradVec w) V i hgdiff hVd
  have hEq : (fun y : Vec3 => curlVec (fun z : Vec3 => w z • V z) y i)
      =ᶠ[nhds x] fun y : Vec3 =>
        w y * curlVec V y i + cross3 (gradVec w y) (V y) i := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have h := congrFun (curlVec_smul (hwdiff y) (hVdiff y hy)) i
    simpa using h
  rw [hEq.fderiv_eq, fderiv_fun_add ((hwdiff x).fun_mul hAdiff) hBdiff, add_apply,
    fderiv_fun_mul (hwdiff x) hAdiff,
    fderiv_cross3_apply (gradVec w) V i k hgdiff hVd]
  simp only [add_apply, smul_apply, smul_eq_mul, gradVec]
  ring

/-- **One derivative of the divergence of a cutoff product.** For a divergence-free field the
divergence of the product is `∇χ · v`, so one more derivative produces exactly two terms, both
carrying a derivative of the cutoff. -/
private lemma fderiv_div_smul_apply (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3)
    (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (hdiv : ∀ x ∈ U, ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => V y j) x (basisVec j) = 0)
    (k : Fin 3) {x : Vec3} (hx : x ∈ U) :
    fderiv ℝ (fun y : Vec3 =>
        ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j)) x (basisVec k)
      = (∑ j : Fin 3, partialVec (gradVec w) k x j * V x j)
        + ∑ j : Fin 3, gradVec w x j * partialVec V k x j := by
  have hwdiff : ∀ y : Vec3, DifferentiableAt ℝ w y := fun y => hw.differentiable (by simp) y
  have hVdiff : ∀ y ∈ U, ∀ a : Fin 3, DifferentiableAt ℝ (fun z : Vec3 => V z a) y :=
    fun y hy a => (((contDiffOn_pi.mp hV) a).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hy)
  have hgdiff : ∀ a : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => gradVec w y a) x := fun a =>
    (contDiff_fderiv_apply_scalar w hw a).differentiable (by simp) x
  have hVd : ∀ a : Fin 3, DifferentiableAt ℝ (fun y : Vec3 => V y a) x := hVdiff x hx
  have hEq : (fun y : Vec3 =>
        ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j))
      =ᶠ[nhds x] fun y : Vec3 => ∑ j : Fin 3, gradVec w y j * V y j := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [div_smul (hwdiff y) (hVdiff y hy), hdiv y hy]
    ring
  have hsum : fderiv ℝ (fun y : Vec3 => ∑ j : Fin 3, gradVec w y j * V y j) x
      = ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => gradVec w y j * V y j) x :=
    fderiv_fun_sum fun j _ => (hgdiff j).fun_mul (hVd j)
  rw [hEq.fderiv_eq, hsum, sum_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_mul (hgdiff j) (hVd j)]
  simp only [add_apply, smul_apply, smul_eq_mul, partialVec_apply]
  ring

/-! ### Elementary sum inequalities -/

/-- A four-term expansion costs a factor four in the squared sum. -/
private lemma sum_sq_four_le (F A B C D : Fin 3 → Fin 3 → ℝ)
    (h : ∀ i k : Fin 3, F i k = A i k + B i k + C i k + D i k) :
    ∑ i : Fin 3, ∑ k : Fin 3, (F i k) ^ 2
      ≤ 4 * (∑ i : Fin 3, ∑ k : Fin 3, (A i k) ^ 2)
        + 4 * (∑ i : Fin 3, ∑ k : Fin 3, (B i k) ^ 2)
        + 4 * (∑ i : Fin 3, ∑ k : Fin 3, (C i k) ^ 2)
        + 4 * (∑ i : Fin 3, ∑ k : Fin 3, (D i k) ^ 2) := by
  have hstep : ∀ i k : Fin 3, (F i k) ^ 2
      ≤ 4 * (A i k) ^ 2 + 4 * (B i k) ^ 2 + 4 * (C i k) ^ 2 + 4 * (D i k) ^ 2 := by
    intro i k
    rw [h i k]
    nlinarith only [sq_nonneg (A i k - B i k), sq_nonneg (A i k - C i k),
      sq_nonneg (A i k - D i k), sq_nonneg (B i k - C i k), sq_nonneg (B i k - D i k),
      sq_nonneg (C i k - D i k)]
  calc ∑ i : Fin 3, ∑ k : Fin 3, (F i k) ^ 2
      ≤ ∑ i : Fin 3, ∑ k : Fin 3, (4 * (A i k) ^ 2 + 4 * (B i k) ^ 2 + 4 * (C i k) ^ 2
          + 4 * (D i k) ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hstep i k
    _ = 4 * (∑ i : Fin 3, ∑ k : Fin 3, (A i k) ^ 2)
          + 4 * (∑ i : Fin 3, ∑ k : Fin 3, (B i k) ^ 2)
          + 4 * (∑ i : Fin 3, ∑ k : Fin 3, (C i k) ^ 2)
          + 4 * (∑ i : Fin 3, ∑ k : Fin 3, (D i k) ^ 2) := by
        simp only [Fin.sum_univ_three]
        ring

/-- A separated product of squares factors. -/
private lemma sum_sq_prod_left (gw cv : Vec3) :
    ∑ i : Fin 3, ∑ k : Fin 3, (gw k * cv i) ^ 2
      = (∑ k : Fin 3, (gw k) ^ 2) * ∑ i : Fin 3, (cv i) ^ 2 := by
  simp only [Fin.sum_univ_three]
  ring

/-- A constant factors out of a doubly indexed sum of squares. -/
private lemma sum_sq_const_mul (c : ℝ) (b : Fin 3 → Fin 3 → ℝ) :
    ∑ i : Fin 3, ∑ k : Fin 3, (c * b i k) ^ 2
      = c ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3, (b i k) ^ 2 := by
  simp only [Fin.sum_univ_three]
  ring

/-- Swapping the two indices of a doubly indexed sum. -/
private lemma sum_comm_two (f : Fin 3 → Fin 3 → ℝ) :
    ∑ k : Fin 3, ∑ j : Fin 3, f j k = ∑ i : Fin 3, ∑ j : Fin 3, f i j := Finset.sum_comm

/-- A family of cross products with a varying left factor. -/
private lemma sum_sq_cross3_left_le (D : Fin 3 → Vec3) (b : Vec3) :
    ∑ i : Fin 3, ∑ k : Fin 3, (cross3 (D k) b i) ^ 2
      ≤ (∑ k : Fin 3, ∑ j : Fin 3, (D k j) ^ 2) * ∑ i : Fin 3, (b i) ^ 2 := by
  rw [Finset.sum_comm, Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => sum_sq_cross3_le (D k) b

/-- A family of cross products with a varying right factor. -/
private lemma sum_sq_cross3_right_le (a : Vec3) (E : Fin 3 → Vec3) :
    ∑ i : Fin 3, ∑ k : Fin 3, (cross3 a (E k) i) ^ 2
      ≤ (∑ i : Fin 3, (a i) ^ 2) * ∑ k : Fin 3, ∑ j : Fin 3, (E k j) ^ 2 := by
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => sum_sq_cross3_le a (E k)

/-- The squared length of the curl is at most twice the gradient energy. -/
private lemma sum_sq_curlVec_le_two_mul (V : Vec3 → Vec3) (x : Vec3) :
    ∑ i : Fin 3, (curlVec V x i) ^ 2
      ≤ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 := by
  simp only [curlVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  nlinarith only [
    sq_nonneg (fderiv ℝ (fun y : Vec3 => V y 2) x (basisVec 1)
      + fderiv ℝ (fun y : Vec3 => V y 1) x (basisVec 2)),
    sq_nonneg (fderiv ℝ (fun y : Vec3 => V y 0) x (basisVec 2)
      + fderiv ℝ (fun y : Vec3 => V y 2) x (basisVec 0)),
    sq_nonneg (fderiv ℝ (fun y : Vec3 => V y 1) x (basisVec 0)
      + fderiv ℝ (fun y : Vec3 => V y 0) x (basisVec 1)),
    sq_nonneg (fderiv ℝ (fun y : Vec3 => V y 0) x (basisVec 0)),
    sq_nonneg (fderiv ℝ (fun y : Vec3 => V y 1) x (basisVec 1)),
    sq_nonneg (fderiv ℝ (fun y : Vec3 => V y 2) x (basisVec 2))]

/-- The support of a cutoff product sits inside the support of the cutoff. -/
private lemma tsupport_smul_subset (w : Vec3 → ℝ) (V : Vec3 → Vec3) :
    tsupport (fun y : Vec3 => w y • V y) ⊆ tsupport w := by
  refine closure_minimal (fun y hy => ?_) (isClosed_tsupport w)
  by_contra hyn
  refine hy ?_
  change w y • V y = 0
  rw [image_eq_zero_of_notMem_tsupport hyn, zero_smul]

/-! ### The pointwise bound on one derivative of the curl -/

/-- The pointwise bound on `|∇ curl(χ v)|²`: four terms, three of which are supported where a
derivative of the cutoff is nonzero and are therefore controlled by the jet bound. -/
private lemma sum_sq_fderiv_curlVec_smul_le (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3)
    (N : ℝ) (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hsupp : tsupport w ⊆ U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (hjet : ∀ x ∈ tsupport (gradVec w), (∑ i : Fin 3, (V x i) ^ 2)
        + ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 ≤ N ^ 2)
    (x : Vec3) :
    ∑ i : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => curlVec (fun z : Vec3 => w z • V z) y i) x (basisVec k)) ^ 2
      ≤ 4 * (w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2)
        + 12 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)
        + 4 * N ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) := by
  have hMcnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hGnn : (0 : ℝ) ≤ ∑ i : Fin 3, (gradVec w x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hHnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hNnn : (0 : ℝ) ≤ N ^ 2 := sq_nonneg N
  have hNG : (0 : ℝ) ≤ N ^ 2 * ∑ i : Fin 3, (gradVec w x i) ^ 2 := mul_nonneg hNnn hGnn
  have hNH : (0 : ℝ) ≤ N ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 := mul_nonneg hNnn hHnn
  by_cases hxU : x ∈ U
  · have hfour : ∑ i : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => curlVec (fun z : Vec3 => w z • V z) y i) x (basisVec k)) ^ 2
          ≤ 4 * (∑ i : Fin 3, ∑ k : Fin 3, (gradVec w x k * curlVec V x i) ^ 2)
            + 4 * (∑ i : Fin 3, ∑ k : Fin 3,
                (w x * fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2)
            + 4 * (∑ i : Fin 3, ∑ k : Fin 3,
                (cross3 (partialVec (gradVec w) k x) (V x) i) ^ 2)
            + 4 * (∑ i : Fin 3, ∑ k : Fin 3,
                (cross3 (gradVec w x) (partialVec V k x) i) ^ 2) :=
      sum_sq_four_le
        (fun i k => fderiv ℝ (fun y : Vec3 =>
          curlVec (fun z : Vec3 => w z • V z) y i) x (basisVec k))
        (fun i k => gradVec w x k * curlVec V x i)
        (fun i k => w x * fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k))
        (fun i k => cross3 (partialVec (gradVec w) k x) (V x) i)
        (fun i k => cross3 (gradVec w x) (partialVec V k x) i)
        fun i k => fderiv_curlVec_smul_apply w V U hU hw hV i k hxU
    have hA : (∑ i : Fin 3, ∑ k : Fin 3, (gradVec w x k * curlVec V x i) ^ 2)
        = (∑ i : Fin 3, (gradVec w x i) ^ 2) * ∑ i : Fin 3, (curlVec V x i) ^ 2 :=
      sum_sq_prod_left (gradVec w x) (curlVec V x)
    have hB : (∑ i : Fin 3, ∑ k : Fin 3,
          (w x * fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2)
        = w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2 :=
      sum_sq_const_mul (w x)
        fun i k => fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)
    have hC : (∑ i : Fin 3, ∑ k : Fin 3,
          (cross3 (partialVec (gradVec w) k x) (V x) i) ^ 2)
        ≤ (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)
          * ∑ i : Fin 3, (V x i) ^ 2 := by
      refine le_trans (sum_sq_cross3_left_le (fun k => partialVec (gradVec w) k x) (V x))
        (le_of_eq ?_)
      congr 1
      simp only [partialVec_apply]
      exact sum_comm_two fun a b => (fderiv ℝ (fun y : Vec3 => gradVec w y a) x (basisVec b)) ^ 2
    have hD : (∑ i : Fin 3, ∑ k : Fin 3, (cross3 (gradVec w x) (partialVec V k x) i) ^ 2)
        ≤ (∑ i : Fin 3, (gradVec w x i) ^ 2)
          * ∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 := by
      refine le_trans (sum_sq_cross3_right_le (gradVec w x) (fun k => partialVec V k x))
        (le_of_eq ?_)
      congr 1
      simp only [partialVec_apply]
      exact sum_comm_two fun a b => (fderiv ℝ (fun y : Vec3 => V y a) x (basisVec b)) ^ 2
    have hCnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ k : Fin 3,
        (cross3 (partialVec (gradVec w) k x) (V x) i) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
    have hDnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ k : Fin 3,
        (cross3 (gradVec w x) (partialVec V k x) i) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
    have hCv := sum_sq_curlVec_le_two_mul V x
    by_cases hxs : x ∈ tsupport (gradVec w)
    · have hjx := hjet x hxs
      have hPnn : (0 : ℝ) ≤ ∑ i : Fin 3, (V x i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hQnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hQle : (∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2) ≤ N ^ 2 := by
        linarith only [hjx, hPnn]
      have hPle : (∑ i : Fin 3, (V x i) ^ 2) ≤ N ^ 2 := by linarith only [hjx, hQnn]
      have hCvle : (∑ i : Fin 3, (curlVec V x i) ^ 2) ≤ 2 * N ^ 2 := by
        linarith only [hCv, hQle]
      have e1 := mul_le_mul_of_nonneg_left hCvle hGnn
      have e2 := mul_le_mul_of_nonneg_left hPle hHnn
      have e3 := mul_le_mul_of_nonneg_left hQle hGnn
      nlinarith only [hfour, hA, hB, hC, hD, e1, e2, e3]
    · have hg : gradVec w x = 0 := image_eq_zero_of_notMem_tsupport hxs
      have hgz : ∀ i : Fin 3, fderiv ℝ (fun y : Vec3 => gradVec w y i) x = 0 := by
        intro i
        have hEq : (fun y : Vec3 => gradVec w y i) =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
          filter_upwards [eventuallyEq_zero_nhds_of_notMem_tsupport (gradVec w) hxs] with y hy
          rw [hy]
          rfl
        rw [hEq.fderiv_eq]
        simp
      have hG0 : (∑ i : Fin 3, (gradVec w x i) ^ 2) = 0 := by simp [hg]
      have hH0 : (∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) = 0 := by simp [hgz]
      have hGCv : (∑ i : Fin 3, (gradVec w x i) ^ 2) * ∑ i : Fin 3, (curlVec V x i) ^ 2 = 0 := by
        rw [hG0]; ring
      have hHP : (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)
          * ∑ i : Fin 3, (V x i) ^ 2 = 0 := by rw [hH0]; ring
      have hGQ : (∑ i : Fin 3, (gradVec w x i) ^ 2)
          * ∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 = 0 := by rw [hG0]; ring
      have hNG0 : N ^ 2 * ∑ i : Fin 3, (gradVec w x i) ^ 2 = 0 := by rw [hG0]; ring
      have hNH0 : N ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 = 0 := by rw [hH0]; ring
      linarith only [hfour, hA, hB, hC, hD, hCnn, hDnn, hGCv, hHP, hGQ, hNG0, hNH0]
  · have hx' : x ∉ tsupport (fun y : Vec3 => w y • V y) := fun hc =>
      hxU (hsupp (tsupport_smul_subset w V hc))
    have hzero : ∑ i : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 =>
          curlVec (fun z : Vec3 => w z • V z) y i) x (basisVec k)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
      rw [fderiv_curlVec_eq_zero_of_notMem hx' i k]
      ring
    rw [hzero]
    have hMc : (0 : ℝ) ≤ w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2 :=
      mul_nonneg (sq_nonneg _) hMcnn
    linarith only [hMc, hNG, hNH]

/-! ### The pointwise bound on one derivative of the divergence -/

/-- The Cauchy–Schwarz inequality in three components, via the Lagrange identity. -/
private lemma sq_dot3_le_prod (a b : Vec3) :
    (∑ i : Fin 3, a i * b i) ^ 2 ≤ (∑ i : Fin 3, a i ^ 2) * ∑ i : Fin 3, b i ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith only [sq_nonneg (a 0 * b 1 - a 1 * b 0), sq_nonneg (a 0 * b 2 - a 2 * b 0),
    sq_nonneg (a 1 * b 2 - a 2 * b 1)]

/-- Off the support of the cutoff product the divergence vanishes on a neighbourhood, so its
derivatives vanish there. -/
private lemma fderiv_div_smul_eq_zero_of_notMem (w : Vec3 → ℝ) (V : Vec3 → Vec3) {x : Vec3}
    (hx : x ∉ tsupport (fun y : Vec3 => w y • V y)) (k : Fin 3) :
    fderiv ℝ (fun y : Vec3 =>
        ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j)) x
      (basisVec k) = 0 := by
  have hEq : (fun y : Vec3 =>
      ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j))
      =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport (fun y : Vec3 => w y • V y)).isOpen_compl.mem_nhds hx]
      with y hy
    refine Finset.sum_eq_zero fun j _ => ?_
    have hEqj : (fun z : Vec3 => (w z • V z) j) =ᶠ[nhds y] fun _ : Vec3 => (0 : ℝ) := by
      filter_upwards [eventuallyEq_zero_nhds_of_notMem_tsupport
        (fun y' : Vec3 => w y' • V y') hy] with z hz
      have hz' : w z • V z = 0 := hz
      change (w z • V z) j = 0
      rw [hz']
      rfl
    rw [hEqj.fderiv_eq]
    simp
  rw [hEq.fderiv_eq]
  simp

/-- Splitting a sum of two separated products over the outer index. -/
private lemma sum_two_terms_eq (P G : ℝ) (D E : Fin 3 → Fin 3 → ℝ) :
    ∑ k : Fin 3, (2 * ((∑ j : Fin 3, (D k j) ^ 2) * P) + 2 * (G * ∑ j : Fin 3, (E k j) ^ 2))
      = 2 * ((∑ k : Fin 3, ∑ j : Fin 3, (D k j) ^ 2) * P)
        + 2 * (G * ∑ k : Fin 3, ∑ j : Fin 3, (E k j) ^ 2) := by
  simp only [Fin.sum_univ_three]
  ring

/-- The pointwise bound on `|∇ div(χ v)|²` for a divergence-free field: both terms carry a
derivative of the cutoff. -/
private lemma sq_fderiv_div_smul_le (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3) (N : ℝ)
    (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hsupp : tsupport w ⊆ U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (hdiv : ∀ x ∈ U, ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => V y j) x (basisVec j) = 0)
    (hjet : ∀ x ∈ tsupport (gradVec w), (∑ i : Fin 3, (V x i) ^ 2)
        + ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 ≤ N ^ 2)
    (x : Vec3) :
    ∑ k : Fin 3, (fderiv ℝ (fun y : Vec3 =>
          ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j)) x
        (basisVec k)) ^ 2
      ≤ 2 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)
        + 2 * N ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) := by
  have hGnn : (0 : ℝ) ≤ ∑ i : Fin 3, (gradVec w x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hHnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hNnn : (0 : ℝ) ≤ N ^ 2 := sq_nonneg N
  have hNG : (0 : ℝ) ≤ N ^ 2 * ∑ i : Fin 3, (gradVec w x i) ^ 2 := mul_nonneg hNnn hGnn
  have hNH : (0 : ℝ) ≤ N ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 := mul_nonneg hNnn hHnn
  by_cases hxU : x ∈ U
  · have hstep : ∀ k : Fin 3, (fderiv ℝ (fun y : Vec3 =>
          ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j)) x
            (basisVec k)) ^ 2
        ≤ 2 * ((∑ j : Fin 3, (partialVec (gradVec w) k x j) ^ 2) * ∑ j : Fin 3, (V x j) ^ 2)
          + 2 * ((∑ j : Fin 3, (gradVec w x j) ^ 2)
              * ∑ j : Fin 3, (partialVec V k x j) ^ 2) := by
      intro k
      rw [fderiv_div_smul_apply w V U hU hw hV hdiv k hxU]
      have h1 := sq_dot3_le_prod (partialVec (gradVec w) k x) (V x)
      have h2 := sq_dot3_le_prod (gradVec w x) (partialVec V k x)
      nlinarith only [h1, h2,
        sq_nonneg ((∑ j : Fin 3, partialVec (gradVec w) k x j * V x j)
          - ∑ j : Fin 3, gradVec w x j * partialVec V k x j)]
    have hHeq : (∑ k : Fin 3, ∑ j : Fin 3, (partialVec (gradVec w) k x j) ^ 2)
        = ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 := by
      simp only [partialVec_apply]
      exact sum_comm_two fun a b => (fderiv ℝ (fun y : Vec3 => gradVec w y a) x (basisVec b)) ^ 2
    have hQeq : (∑ k : Fin 3, ∑ j : Fin 3, (partialVec V k x j) ^ 2)
        = ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 := by
      simp only [partialVec_apply]
      exact sum_comm_two fun a b => (fderiv ℝ (fun y : Vec3 => V y a) x (basisVec b)) ^ 2
    have hsum : ∑ k : Fin 3, (fderiv ℝ (fun y : Vec3 =>
            ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j)) x
          (basisVec k)) ^ 2
        ≤ 2 * ((∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)
            * ∑ j : Fin 3, (V x j) ^ 2)
          + 2 * ((∑ i : Fin 3, (gradVec w x i) ^ 2)
              * ∑ i : Fin 3, ∑ j : Fin 3,
                  (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2) := by
      refine le_trans (Finset.sum_le_sum fun k _ => hstep k) (le_of_eq ?_)
      rw [sum_two_terms_eq (∑ j : Fin 3, (V x j) ^ 2) (∑ j : Fin 3, (gradVec w x j) ^ 2)
        (fun k j => partialVec (gradVec w) k x j) (fun k j => partialVec V k x j),
        hHeq, hQeq]
    by_cases hxs : x ∈ tsupport (gradVec w)
    · have hjx := hjet x hxs
      have hPnn : (0 : ℝ) ≤ ∑ i : Fin 3, (V x i) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hQnn : (0 : ℝ) ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hQle : (∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2) ≤ N ^ 2 := by
        linarith only [hjx, hPnn]
      have hPle : (∑ i : Fin 3, (V x i) ^ 2) ≤ N ^ 2 := by linarith only [hjx, hQnn]
      have e1 := mul_le_mul_of_nonneg_left hPle hHnn
      have e2 := mul_le_mul_of_nonneg_left hQle hGnn
      nlinarith only [hsum, e1, e2]
    · have hg : gradVec w x = 0 := image_eq_zero_of_notMem_tsupport hxs
      have hgz : ∀ i : Fin 3, fderiv ℝ (fun y : Vec3 => gradVec w y i) x = 0 := by
        intro i
        have hEq : (fun y : Vec3 => gradVec w y i) =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
          filter_upwards [eventuallyEq_zero_nhds_of_notMem_tsupport (gradVec w) hxs] with y hy
          rw [hy]
          rfl
        rw [hEq.fderiv_eq]
        simp
      have hG0 : (∑ i : Fin 3, (gradVec w x i) ^ 2) = 0 := by simp [hg]
      have hH0 : (∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) = 0 := by simp [hgz]
      have hHP : (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)
          * ∑ j : Fin 3, (V x j) ^ 2 = 0 := by rw [hH0]; ring
      have hGQ : (∑ i : Fin 3, (gradVec w x i) ^ 2)
          * ∑ i : Fin 3, ∑ j : Fin 3,
              (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 = 0 := by rw [hG0]; ring
      have hNG0 : N ^ 2 * ∑ i : Fin 3, (gradVec w x i) ^ 2 = 0 := by rw [hG0]; ring
      have hNH0 : N ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 = 0 := by rw [hH0]; ring
      linarith only [hsum, hHP, hGQ, hNG0, hNH0]
  · have hx' : x ∉ tsupport (fun y : Vec3 => w y • V y) := fun hc =>
      hxU (hsupp (tsupport_smul_subset w V hc))
    have hzero : ∑ k : Fin 3, (fderiv ℝ (fun y : Vec3 =>
          ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j)) x
        (basisVec k)) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [fderiv_div_smul_eq_zero_of_notMem w V hx' k]
      ring
    rw [hzero]
    linarith only [hNG, hNH]

/-! ### Integrability of the cutoff-weighted curl dissipation -/

/-- A function continuous on an open set and vanishing outside a closed subset of it is
continuous everywhere. -/
private lemma continuous_of_continuousOn_zero_off_closed {F : Vec3 → ℝ} {U K : Set Vec3}
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (hF : ContinuousOn F U)
    (hzero : ∀ x : Vec3, x ∉ K → F x = 0) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ K
  · exact hF.continuousAt (hU.mem_nhds (hKU hx))
  · have heq : F =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      exact hzero y hy
    exact heq.continuousAt

/-- `χ² |∇ curl v|²` is integrable when `χ` is a cutoff supported inside the smoothness set of
`v`. This is the enstrophy dissipation of `lem:aniso:closure`. -/
theorem integrable_cutoff_sq_sum_sq_fderiv_curlVec (w : Vec3 → ℝ) (V : Vec3 → Vec3)
    (U : Set Vec3) (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hws : HasCompactSupport w)
    (hsupp : tsupport w ⊆ U) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U) :
    Integrable (fun x : Vec3 => w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2) := by
  have hzero : ∀ x : Vec3, x ∉ tsupport w →
      w x ^ 2 * (∑ i : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hMcOn : ContinuousOn (fun x : Vec3 => ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2) U :=
    continuousOn_finsetSum Finset.univ fun i _ =>
      continuousOn_finsetSum Finset.univ fun k _ =>
        (contDiffOn_fderiv_scalar_apply hU (contDiffOn_curlVec_comp hU hV i) k).continuousOn.pow 2
  have hcontOn : ContinuousOn (fun x : Vec3 => w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2) U :=
    (hw.continuous.continuousOn.pow 2).mul hMcOn
  have hcont : Continuous (fun x : Vec3 => w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2) :=
    continuous_of_continuousOn_zero_off_closed hU (isClosed_tsupport w) hsupp hcontOn hzero
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hws hzero)

/-! ### The Hessian bound -/

/-- **The Hessian half of `eq:aniso:closure:elliptic`.** For a field `v` smooth and divergence
free on an open set `U`, a cutoff `χ` smooth and compactly supported inside `U`, and `N`
bounding the first-order jet of `v` on the support of `∇χ`,

`∫ |∇²(χ v)|² ≤ 4 ∫ χ² |∇ curl v|² + 24 N² ∫ |∇χ|² + 24 N² ∫ |∇²χ|²`.

It is the second-order identity `integral_sq_fderiv_fderiv_eq_curl_add_div` applied to `χ v`,
followed by the Leibniz expansions of `curl (χ v)` and `div (χ v)`. -/
theorem integral_sq_fderiv_fderiv_smul_le (w : Vec3 → ℝ) (V : Vec3 → Vec3) (U : Set Vec3)
    (N : ℝ) (hU : IsOpen U) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hws : HasCompactSupport w)
    (hsupp : tsupport w ⊆ U) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (hdiv : ∀ x ∈ U, ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => V y j) x (basisVec j) = 0)
    (hjet : ∀ x ∈ tsupport (gradVec w), (∑ i : Fin 3, (V x i) ^ 2)
        + ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => V y i) x (basisVec j)) ^ 2 ≤ N ^ 2) :
    ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x
          (basisVec k)) ^ 2
      ≤ 4 * (∫ x : Vec3, w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2)
        + 24 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, (gradVec w x i) ^ 2)
        + 24 * N ^ 2 * (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) := by
  obtain ⟨hWcd, hWcs⟩ := contDiff_smul_of_contDiffOn w V U hU hw hws hsupp hV
  have hMcInt : Integrable (fun x : Vec3 => w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2) :=
    integrable_cutoff_sq_sum_sq_fderiv_curlVec w V U hU hw hws hsupp hV
  have hGint : Integrable (fun x : Vec3 => ∑ i : Fin 3, (gradVec w x i) ^ 2) :=
    integrable_sum_sq_gradVec_cutoff w hw hws
  have hHint : Integrable (fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2) :=
    integrable_sum_sq_fderiv_gradVec_cutoff w hw hws
  have hid : ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : Vec3 => fderiv ℝ (fun z : Vec3 => (w z • V z) i) y (basisVec j)) x
          (basisVec k)) ^ 2
      = (∫ x : Vec3, ∑ i : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 =>
            curlVec (fun z : Vec3 => w z • V z) y i) x (basisVec k)) ^ 2)
        + ∫ x : Vec3, ∑ k : Fin 3,
            (fderiv ℝ (fun y : Vec3 =>
              ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j)) x
                (basisVec k)) ^ 2 :=
    integral_sq_fderiv_fderiv_eq_curl_add_div (fun y : Vec3 => w y • V y) hWcd hWcs
  have hmaj₁ : Integrable (fun x : Vec3 =>
      4 * (w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2)
        + 12 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)) :=
    (hMcInt.const_mul 4).add (hGint.const_mul (12 * N ^ 2))
  have hmaj₂ : Integrable (fun x : Vec3 =>
      4 * (w x ^ 2 * ∑ i : Fin 3, ∑ k : Fin 3,
          (fderiv ℝ (fun y : Vec3 => curlVec V y i) x (basisVec k)) ^ 2)
        + 12 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)
        + 4 * N ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)) :=
    hmaj₁.add (hHint.const_mul (4 * N ^ 2))
  have hcurlnn : (0 : Vec3 → ℝ) ≤ᵐ[volume] fun x : Vec3 => ∑ i : Fin 3, ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 =>
        curlVec (fun z : Vec3 => w z • V z) y i) x (basisVec k)) ^ 2 :=
    Filter.Eventually.of_forall fun x =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hcurlle := integral_mono_of_nonneg hcurlnn hmaj₂
    (Filter.Eventually.of_forall fun x =>
      sum_sq_fderiv_curlVec_smul_le w V U N hU hw hsupp hV hjet x)
  rw [integral_add hmaj₁ (hHint.const_mul (4 * N ^ 2)),
    integral_add (hMcInt.const_mul 4) (hGint.const_mul (12 * N ^ 2)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hcurlle
  have hmaj₃ : Integrable (fun x : Vec3 =>
      2 * N ^ 2 * (∑ i : Fin 3, (gradVec w x i) ^ 2)
        + 2 * N ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
            (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2)) :=
    (hGint.const_mul (2 * N ^ 2)).add (hHint.const_mul (2 * N ^ 2))
  have hdivnn : (0 : Vec3 → ℝ) ≤ᵐ[volume] fun x : Vec3 => ∑ k : Fin 3,
      (fderiv ℝ (fun y : Vec3 =>
        ∑ j : Fin 3, fderiv ℝ (fun z : Vec3 => (w z • V z) j) y (basisVec j)) x
          (basisVec k)) ^ 2 :=
    Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hdivle := integral_mono_of_nonneg hdivnn hmaj₃
    (Filter.Eventually.of_forall fun x =>
      sq_fderiv_div_smul_le w V U N hU hw hsupp hV hdiv hjet x)
  rw [integral_add (hGint.const_mul (2 * N ^ 2)) (hHint.const_mul (2 * N ^ 2)),
    integral_const_mul, integral_const_mul] at hdivle
  have hGnn : (0 : ℝ) ≤ ∫ x : Vec3, ∑ i : Fin 3, (gradVec w x i) ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hHnn : (0 : ℝ) ≤ ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hNG : (0 : ℝ) ≤ N ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec w x i) ^ 2 :=
    mul_nonneg (sq_nonneg N) hGnn
  have hNH : (0 : ℝ) ≤ N ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => gradVec w y i) x (basisVec j)) ^ 2 :=
    mul_nonneg (sq_nonneg N) hHnn
  rw [hid]
  linarith only [hcurlle, hdivle, hNG, hNH]

end CIV
