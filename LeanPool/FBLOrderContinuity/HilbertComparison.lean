/-
Copyright (c) 2026 Raúl E. Pariente-Martín, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raúl E. Pariente-Martín, Pedro Tradacete
-/

module

public import LeanPool.FBLOrderContinuity.ParameterWitness
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Sqrt



/-!
# A uniform comparison of the free norms on a real Hilbert space

Finite averages over all sign choices give a scalar lower Khintchine estimate and
a Hilbert-space second-moment estimate. `finite_hilbert_estimate` combines them with
weak one-summability. Maximizing a regularized square-root sum on a compact convex
set yields the positive weights in `hilbert_dual_weights`.

`hilbert_dual_factorization` factors a weakly one-summable dual family through a
weakly two-summable family with coefficient ell-two norm at most 3. Homogeneity and
Cauchy–Schwarz give `hilbert_free_norm_comparison`: the one-free norm is at most
three times the two-free norm. This explicit estimate proves the Hilbert example
in Remark 5.4; the constant is sufficient for norm equivalence and is not claimed
optimal. Completeness of the real inner-product space is unnecessary.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal Topology
open Filter Set

namespace FBLOrderContinuousLH
namespace HilbertComparison

/-- Finite sign choices for n coordinates, encoded recursively as Boolean products.
The uniform finite average over this type supplies all expectations in the moment estimates. -/
abbrev Signs : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Signs n

private instance signsFintype : (n : ℕ) → Fintype (Signs n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := signsFintype n; inferInstanceAs (Fintype (Bool × Signs n))

private instance signsNonempty : (n : ℕ) → Nonempty (Signs n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n + 1 => letI := signsNonempty n; inferInstanceAs (Nonempty (Bool × Signs n))

/-- Sum a finite family with the signs encoded by `Signs n`: true contributes a vector
and false its negative. The empty signed sum is zero. -/
def signedSum {H : Type*} [AddCommGroup H] :
    {n : ℕ} → (Fin n → H) → Signs n → H
  | 0, _, _ => 0
  | _ + 1, x, ε => (if ε.1 then x 0 else -x 0) + signedSum (fun i => x i.succ) ε.2

/-- Split a uniform finite average over one sign and the remaining choices into the
mean of the positive and negative branches. -/
private theorem expect_bool_prod {ι : Type*} [Fintype ι] (f : Bool × ι → ℝ) :
    (𝔼 ε, f ε) = 𝔼 ε : ι, (f (true, ε) + f (false, ε)) / 2 := by
  simp [Finset.expect, NNRat.smul_def, Fintype.sum_prod_type, ← Finset.sum_div,
    Finset.sum_add_distrib]
  ring

/-- The average squared norm of a signed sum in a real inner-product space equals
the sum of the squared norms. The induction step is the parallelogram identity. -/
private theorem signedSum_second_moment {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (x : Fin n → H) :
    (𝔼 ε, ‖signedSum x ε‖ ^ 2) = ∑ i, ‖x i‖ ^ 2 := by
  induction n with
  | zero => simp [signedSum]
  | succ n ih =>
    rw [expect_bool_prod]
    have hpar (ε : Signs n) :
        (‖signedSum x (true, ε)‖ ^ 2 + ‖signedSum x (false, ε)‖ ^ 2) / 2 =
          ‖x 0‖ ^ 2 + ‖signedSum (fun i => x i.succ) ε‖ ^ 2 := by
      simpa [signedSum, neg_add_eq_sub, norm_sub_rev] using
        congrArg (fun t : ℝ => t / 2)
          (parallelogram_law_with_norm ℝ (x 0) (signedSum (fun i => x i.succ) ε))
    simp only [hpar, Finset.expect_add_distrib, Fintype.expect_const, ih, Fin.sum_univ_succ]

/-- The fourth moment of a scalar signed sum is at most three times the square
of its second moment. Expanding the two signs cancels the odd terms. -/
private theorem signedSum_fourth_moment {n : ℕ} (a : Fin n → ℝ) :
    (𝔼 ε, (signedSum a ε) ^ 4) ≤ 3 * (∑ i, a i ^ 2) ^ 2 := by
  induction n with
  | zero => simp [signedSum]
  | succ n ih =>
    rw [expect_bool_prod]
    have hpoly (ε : Signs n) :
        (signedSum a (true, ε) ^ 4 + signedSum a (false, ε) ^ 4) / 2 =
          a 0 ^ 4 + 6 * a 0 ^ 2 * (signedSum (fun i => a i.succ) ε) ^ 2 +
            (signedSum (fun i => a i.succ) ε) ^ 4 := by
      simp only [signedSum, Bool.false_eq_true, ↓reduceIte]
      ring
    simp only [hpoly, Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect,
      Fin.sum_univ_succ]
    have hsecond : (𝔼 ε, (signedSum (fun i : Fin n => a i.succ) ε) ^ 2) =
        ∑ i : Fin n, a i.succ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using signedSum_second_moment (fun i => a i.succ)
    rw [hsecond]
    nlinarith [ih (fun i => a i.succ), sq_nonneg (a 0 ^ 2)]

/-- A finite scalar Khintchine lower bound: the ell-two norm of the coefficients
is at most √3 times the mean absolute signed sum. Two Cauchy–Schwarz estimates
combine the exact second moment with the fourth-moment bound. -/
private theorem signedSum_abs_lower {n : ℕ} (a : Fin n → ℝ) :
    Real.sqrt (∑ i, a i ^ 2) ≤ Real.sqrt 3 * (𝔼 ε, |signedSum a ε|) := by
  let X : Signs n → ℝ := signedSum a
  have hsecond : (𝔼 ε, X ε ^ 2) = ∑ i, a i ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using signedSum_second_moment a
  have hcs₁ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ε => Real.sqrt |X ε|) (fun ε => Real.sqrt |X ε| * |X ε|)
  simp only [← mul_assoc, ← sq, sq_abs, mul_pow, Real.sq_sqrt (abs_nonneg _)] at hcs₁
  have hcs₂ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ε => |X ε|) (fun ε => X ε ^ 2)
  simp only [sq_abs, ← pow_mul, Nat.reduceMul] at hcs₂
  have hfourth : (𝔼 ε, X ε ^ 4) ≤ 3 * (∑ i, a i ^ 2) ^ 2 := signedSum_fourth_moment a
  have hv : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hA : 0 ≤ 𝔼 ε, |X ε| := Finset.expect_nonneg (fun _ _ => abs_nonneg _)
  rw [hsecond] at hcs₁ hcs₂
  have hbound : ∑ i, a i ^ 2 ≤ 3 * (𝔼 ε, |X ε|) ^ 2 := by
    rcases hv.eq_or_lt with hz | hp
    · rw [← hz]; positivity
    have h₁ := mul_self_le_mul_self (sq_nonneg _) hcs₁
    have h₂ := mul_le_mul_of_nonneg_left
      (hcs₂.trans (mul_le_mul_of_nonneg_left hfourth hv)) (sq_nonneg (𝔼 ε, |X ε|))
    have hh : (∑ i, a i ^ 2) * (∑ i, a i ^ 2) ^ 3 ≤
        (3 * (𝔼 ε, |X ε|) ^ 2) * (∑ i, a i ^ 2) ^ 3 := by
      nlinarith only [h₁, h₂]
    exact le_of_mul_le_mul_right hh (pow_pos hp 3)
  apply Real.sqrt_le_iff.mpr
  exact ⟨mul_nonneg (Real.sqrt_nonneg _) hA,
    by simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using hbound⟩

/-- A continuous linear functional commutes with the finite signed sum. -/
private theorem map_signedSum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n : ℕ} (φ : Dual H) (x : Fin n → H) (ε : Signs n) :
    φ (signedSum x ε) = signedSum (fun i => φ (x i)) ε := by
  induction n with
  | zero => simp [signedSum]
  | succ n ih =>
    simp only [signedSum, map_add, apply_ite φ, map_neg, ih]

/-- The mean norm of a Hilbert-space signed sum is bounded by the ell-two sum
of the vector norms, by Cauchy–Schwarz and the second-moment identity. -/
private theorem signedSum_norm_upper {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (x : Fin n → H) :
    (𝔼 ε, ‖signedSum x ε‖) ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  have hcs := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ε => ‖signedSum x ε‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const, signedSum_second_moment] at hcs
  exact Real.le_sqrt_of_sq_le hcs

/-- For a weakly one-summable dual family with bound one, the sum over functionals
of the Euclidean norms of their values on a vector family is at most √3 times the
Euclidean sum of the vector norms. Scalar signed-sum lower bounds and the Hilbert
second-moment estimate provide the factorization estimate without a dimension factor. -/
theorem finite_hilbert_estimate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n m : ℕ} (φ : Fin n → Dual H)
    (hφ : NormAdmissible Exponent.one φ) (x : Fin m → H) :
    ∑ i, Real.sqrt (∑ j, (φ i (x j)) ^ 2) ≤
      Real.sqrt 3 * Real.sqrt (∑ j, ‖x j‖ ^ 2) := by
  have hbound (ε : Signs m) : ∑ i, |φ i (signedSum x ε)| ≤ ‖signedSum x ε‖ := by
    simpa [scalarPSum, Exponent.one] using
      normAdmissible_eval_le_norm Exponent.one φ hφ (signedSum x ε)
  calc
    _ ≤ ∑ i, Real.sqrt 3 * (𝔼 ε, |signedSum (fun j => φ i (x j)) ε|) :=
      Finset.sum_le_sum (fun i _ => signedSum_abs_lower (fun j => φ i (x j)))
    _ = Real.sqrt 3 * (𝔼 ε, ∑ i, |φ i (signedSum x ε)|) := by
      simp only [← Finset.mul_sum, Finset.expect_sum_comm, map_signedSum]
    _ ≤ Real.sqrt 3 * (𝔼 ε, ‖signedSum x ε‖) :=
      mul_le_mul_of_nonneg_left (Finset.expect_le_expect (fun ε _ => hbound ε))
        (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (signedSum_norm_upper x) (Real.sqrt_nonneg _)

/-- If a compact convex set of nonnegative coordinate vectors has square-root sums
bounded by C, positive weights of total mass one bound every weighted coordinate sum
by `(C + 1)^2`. Maximize `∑ i, sqrt (a i + δ)` with `δ = (1/n)^2` and differentiate
along feasible segments to obtain the supporting inequality. -/
private theorem positive_weights_of_compact_convex {n : ℕ} (hn : 0 < n)
    (K : Set (Fin n → ℝ)) (hne : K.Nonempty) (hc : IsCompact K) (hconv : Convex ℝ K)
    (hpos : ∀ a ∈ K, ∀ i, 0 ≤ a i) (C : ℝ)
    (hbound : ∀ a ∈ K, ∑ i, Real.sqrt (a i) ≤ C) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
      ∀ b ∈ K, ∑ i, b i / w i ≤ (C + 1) ^ 2 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let δ : ℝ := (1 / (n : ℝ)) ^ 2
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hδ : 0 < δ := sq_pos_of_pos (one_div_pos.mpr hn')
  let F (a : Fin n → ℝ) : ℝ := ∑ i, Real.sqrt (a i + δ)
  have hF : Continuous F := continuous_finsetSum _ (fun i _ =>
    Real.continuous_sqrt.comp ((continuous_apply i).add continuous_const))
  obtain ⟨a, ha, hmax⟩ := hc.exists_isMaxOn hne hF.continuousOn
  let r (i : Fin n) := Real.sqrt (a i + δ)
  have hr (i : Fin n) : 0 < r i := Real.sqrt_pos.mpr (lt_add_of_le_of_pos (hpos a ha i) hδ)
  have hd : HasFDerivAt F
      (∑ i, (1 / (2 * r i)) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) a :=
    HasFDerivAt.fun_sum (fun i _ =>
      ((hasFDerivAt_apply i a).add_const δ).sqrt (ne_of_gt (lt_add_of_le_of_pos (hpos a ha i) hδ)))
  have hderiv (b : Fin n → ℝ) (hb : b ∈ K) :
      ∑ i, (b i - a i) / (2 * r i) ≤ 0 := by
    have hh := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hconv.segment_subset ha hb))
    simpa only [sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, Pi.sub_apply, smul_eq_mul, one_div, div_eq_mul_inv,
      mul_comm, one_mul] using hh
  let S : ℝ := ∑ i, r i
  have hS : 0 < S := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  have hSbound : S ≤ C + 1 := by
    have hi (i : Fin n) : r i ≤ Real.sqrt (a i) + 1 / (n : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨add_nonneg (Real.sqrt_nonneg _) (one_div_nonneg.mpr hn'.le), ?_⟩
      have hs := Real.sq_sqrt (hpos a ha i)
      have hm := mul_nonneg (Real.sqrt_nonneg (a i)) (one_div_nonneg.mpr hn'.le)
      dsimp [δ]
      nlinarith
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one_div_cancel hn'.ne'] at hh
    exact hh.trans (add_le_add (hbound a ha) le_rfl)
  have hlinear (b : Fin n → ℝ) (hb : b ∈ K) : ∑ i, b i / r i ≤ S := by
    have hh := mul_le_mul_of_nonneg_right (hderiv b hb) (by norm_num : (0 : ℝ) ≤ 2)
    rw [Finset.sum_mul, zero_mul] at hh
    have hi (i : Fin n) : (b i - a i) / (2 * r i) * 2 = b i / r i - a i / r i := by
      field_simp
    simp only [hi, Finset.sum_sub_distrib] at hh
    have hdiag : ∑ i, a i / r i ≤ S := by
      apply Finset.sum_le_sum
      intro i _
      apply (div_le_iff₀ (hr i)).mpr
      have hs : r i ^ 2 = a i + δ := Real.sq_sqrt (add_nonneg (hpos a ha i) hδ.le)
      nlinarith
    linarith
  refine ⟨fun i => r i / S, fun i => div_pos (hr i) hS, ?_, fun b hb => ?_⟩
  · rw [← Finset.sum_div, show ∑ i, r i = S from rfl, div_self hS.ne']
  · calc
      ∑ i, b i / (r i / S) = (∑ i, b i / r i) * S := by
        simp only [Finset.sum_mul, div_div_eq_mul_div, div_mul_eq_mul_div]
      _ ≤ S * S := mul_le_mul_of_nonneg_right (hlinear b hb) hS.le
      _ ≤ (C + 1) ^ 2 := by
        simpa only [sq] using mul_self_le_mul_self hS.le hSbound

/-- The set of squared evaluation vectors `(φ i x)^2` as x runs over the closed
unit ball. Its closed convex hull is the domain for the weight-selection argument. -/
def quadraticImage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n : ℕ} (φ : Fin n → Dual H) : Set (Fin n → ℝ) :=
  {a | ∃ x : H, ‖x‖ ≤ 1 ∧ ∀ i, a i = (φ i x) ^ 2}

/-- The finite Hilbert estimate bounds the sum of square roots by √3 on the convex
hull of squared evaluation vectors. Convex coefficients are absorbed into the vectors
through their square roots. -/
private theorem quadratic_convexHull_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (φ : Fin n → Dual H)
    (hφ : NormAdmissible Exponent.one φ) {a : Fin n → ℝ}
    (ha : a ∈ convexHull ℝ (quadraticImage φ)) :
    (∀ i, 0 ≤ a i) ∧ ∑ i, Real.sqrt (a i) ≤ Real.sqrt 3 := by
  classical
  obtain ⟨ι, hι, w, z, hw, hws, hz, hza⟩ := mem_convexHull_iff_exists_fintype.mp ha
  choose x hx hzx using hz
  let e := (Fintype.equivFin ι).symm
  have hreindex (g : ι → ℝ) : ∑ j : Fin (Fintype.card ι), g (e j) = ∑ j, g j :=
    e.sum_comp g
  have hai (i : Fin n) : a i = ∑ j, w j * (φ i (x j)) ^ 2 := by
    rw [← hza]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hzx]
  have hnonneg (i : Fin n) : 0 ≤ a i := by
    rw [hai]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  refine ⟨hnonneg, ?_⟩
  let y (j : Fin (Fintype.card ι)) := Real.sqrt (w (e j)) • x (e j)
  have hy (i : Fin n) : ∑ j, (φ i (y j)) ^ 2 = a i := by
    simp only [y, map_smul, smul_eq_mul, mul_pow, Real.sq_sqrt (hw _), hai]
    exact hreindex (fun j => w j * (φ i (x j)) ^ 2)
  have hynorm : ∑ j, ‖y j‖ ^ 2 ≤ 1 := by
    simp only [y, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (hw _)]
    rw [hreindex (fun j => w j * ‖x j‖ ^ 2)]
    calc
      ∑ j, w j * ‖x j‖ ^ 2 ≤ ∑ j, w j * 1 :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          (by nlinarith [hx j, norm_nonneg (x j)]) (hw j))
      _ = 1 := by simpa only [mul_one] using hws
  have hh := finite_hilbert_estimate φ hφ y
  simp only [hy] at hh
  exact hh.trans (by simpa using
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hynorm) (Real.sqrt_nonneg 3))

/-- A weakly one-summable family on a real inner-product space has positive weights
with total mass at most one such that `∑ i, (φ i x)^2 / w i ≤ 9` on the unit ball.
The empty family is included. The weights come from a compact-convex maximization
argument and are used to construct `hilbert_dual_factorization`. -/
theorem hilbert_dual_weights {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (φ : Fin n → Dual H) (hφ : NormAdmissible Exponent.one φ) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i ≤ 1 ∧
      ∀ x : H, ‖x‖ ≤ 1 → ∑ i, (φ i x) ^ 2 / w i ≤ 9 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  let K := closure (convexHull ℝ (quadraticImage φ))
  have hpos (a : Fin n → ℝ) (ha : a ∈ K) (i : Fin n) : 0 ≤ a i :=
    closure_minimal (fun b hb => (quadratic_convexHull_bound φ hφ hb).1 i)
      (isClosed_le continuous_const (continuous_apply i)) ha
  have hbound (a : Fin n → ℝ) (ha : a ∈ K) : ∑ i, Real.sqrt (a i) ≤ Real.sqrt 3 :=
    closure_minimal (fun b hb => (quadratic_convexHull_bound φ hφ hb).2)
      (isClosed_le (continuous_finsetSum _ (fun i _ =>
        Real.continuous_sqrt.comp (continuous_apply i))) continuous_const) ha
  have hbounded : Bornology.IsBounded (convexHull ℝ (quadraticImage φ)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨3, fun a ha => (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun i => ?_)⟩
    obtain ⟨hpos, hbound⟩ := quadratic_convexHull_bound φ hφ ha
    have hi : Real.sqrt (a i) ≤ Real.sqrt 3 :=
      (Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (a j)) (Finset.mem_univ i)).trans hbound
    have hh := mul_self_le_mul_self (Real.sqrt_nonneg _) hi
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos i), ← sq,
      Real.sq_sqrt (hpos i), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using hh
  have hne : K.Nonempty :=
    ⟨0, subset_closure (subset_convexHull ℝ (quadraticImage φ)
      ⟨0, by simp, by simp⟩)⟩
  obtain ⟨w, hw, hws, hwb⟩ := positive_weights_of_compact_convex hn K hne
    hbounded.isCompact_closure (convex_convexHull ℝ _).closure hpos (Real.sqrt 3) hbound
  refine ⟨w, hw, hws.le, fun x hx => ?_⟩
  have hh := hwb (fun i => (φ i x) ^ 2)
    (subset_closure (subset_convexHull ℝ (quadraticImage φ) ⟨x, hx, fun _ => rfl⟩))
  have hs : Real.sqrt 3 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- At exponent 2, the scalar p-sum is the square root of the sum of squares. -/
private theorem scalarPSum_two_eq_sqrt {n : ℕ} (a : Fin n → ℝ) :
    scalarPSum Exponent.two a = Real.sqrt (∑ i, a i ^ 2) := by
  simp [scalarPSum, Exponent.two, Real.sqrt_eq_rpow, sq_abs]

/-- Factor an admissible one-family as `φ i = c i • ψ i`, where every coefficient
is positive, the sum of their squares is at most 9, and ψ is an admissible two-family.
This converts one-free-norm tests to two-free-norm tests with a uniform factor 3. -/
theorem hilbert_dual_factorization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (φ : Fin n → Dual H)
    (hφ : NormAdmissible Exponent.one φ) :
    ∃ (c : Fin n → ℝ) (ψ : Fin n → Dual H), (∀ i, 0 < c i) ∧
      (∑ i, c i ^ 2) ≤ 9 ∧ NormAdmissible Exponent.two ψ ∧ ∀ i, φ i = c i • ψ i := by
  obtain ⟨w, hw, hws, hwb⟩ := hilbert_dual_weights φ hφ
  let c (i : Fin n) := 3 * Real.sqrt (w i)
  let ψ (i : Fin n) : Dual H := (c i)⁻¹ • φ i
  have hc (i : Fin n) : 0 < c i := mul_pos (by norm_num) (Real.sqrt_pos.mpr (hw i))
  have hcs : ∑ i, c i ^ 2 ≤ 9 := by
    simp only [c, mul_pow, Real.sq_sqrt (hw _).le, ← Finset.mul_sum]
    nlinarith [hws]
  refine ⟨c, ψ, hc, hcs, ?_, fun i => ?_⟩
  · intro x hx
    rw [scalarPSum_two_eq_sqrt, Real.sqrt_le_iff]
    refine ⟨zero_le_one, ?_⟩
    have hi (i : Fin n) : (ψ i x) ^ 2 = ((φ i x) ^ 2 / w i) / 9 := by
      simp only [ψ, c, smul_apply, smul_eq_mul, mul_pow, inv_pow,
        Real.sq_sqrt (hw i).le]
      norm_num
      ring
    simp only [hi, ← Finset.sum_div, one_pow]
    exact (div_le_one (by norm_num)).mpr (hwb x hx)
  · simp only [ψ, smul_smul, mul_inv_cancel₀ (hc i).ne', one_smul]

/-- Each admissible one-family evaluates an algebraic free function with sum of
absolute values at most three times its two-free norm. Apply positive homogeneity
to the factorization and then Cauchy–Schwarz. -/
private theorem hilbert_family_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (φ : Fin n → Dual H)
    (hφ : NormAdmissible Exponent.one φ) (f : Free Exponent.two H) :
    ∑ i, |f (φ i)| ≤ 3 * ‖f‖ := by
  obtain ⟨c, ψ, hc, hcs, hψ, hfac⟩ := hilbert_dual_factorization φ hφ
  have hi (i : Fin n) : |f (φ i)| = c i * |f (ψ i)| := by
    rw [hfac i, f.1.2.1 (c i) (hc i).le (ψ i), abs_mul, abs_of_pos (hc i)]
  have hnorm : Real.sqrt (∑ i, |f (ψ i)| ^ 2) ≤ ‖f‖ := by
    simpa only [scalarPSum_two_eq_sqrt, sq_abs] using
      freeNorm_family_le Exponent.two f ψ hψ
  calc
    ∑ i, |f (φ i)| = ∑ i, c i * |f (ψ i)| := by simp only [hi]
    _ ≤ Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, |f (ψ i)| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ 3 * ‖f‖ := mul_le_mul
      (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; exact hcs⟩) hnorm
      (Real.sqrt_nonneg _) (by norm_num)

/-- On every real inner-product space, the one-free norm of an algebraic free-lattice
element is at most three times its two-free norm. Taking the supremum over admissible
one-families in `hilbert_family_bound` proves the estimate. It gives the norm equivalence
used in Remark 5.4; neither completeness nor finite dimensionality is assumed. -/
theorem hilbert_free_norm_comparison {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : FVL H) :
    ‖ofFVL Exponent.one v‖ ≤ 3 * ‖ofFVL Exponent.two v‖ := by
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [← freeNormExt_eq_norm]
  change (⨆ n, ⨆ φ : Fin n → Dual H, ⨆ (_ : NormAdmissible Exponent.one φ),
    ENNReal.ofReal (scalarPSum Exponent.one (fun i => ofFVL Exponent.one v (φ i)))) ≤ _
  refine iSup_le fun n => iSup_le fun φ => iSup_le fun hφ => ENNReal.ofReal_le_ofReal ?_
  have hsum (a : Fin n → ℝ) : scalarPSum Exponent.one a = ∑ i, |a i| := by
    simp [scalarPSum, Exponent.one]
  simpa only [hsum, (model_evaluation Exponent.one (0 : H) v _).2,
    (model_evaluation Exponent.two (0 : H) v _).2] using
      hilbert_family_bound φ hφ (ofFVL Exponent.two v)

end HilbertComparison
end FBLOrderContinuousLH
