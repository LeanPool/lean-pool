/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers

/-!
# High-contrast homogenization: Analytic.EuclideanAmbient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Euclidean structure of the ambient space

The ambient norm of `Vec d = Fin d → ℝ` is the supremum norm, so every Euclidean
quantity entering the volume-normalized spaces of `s.introduction` is carried
by `vecDot` and `vecNormSq`, and the bilinear identities behind it have to be
supplied by hand: the expansion of `vecNormSq` on sums and differences,
Cauchy–Schwarz, and the triangle inequality, direct and reverse, for
`Real.sqrt ∘ vecNormSq`.

The second half describes the Euclidean ball `euclideanBallAt c r`: it is open,
it contains its centre, its frontier lies on the Euclidean sphere, and it is
compared in both directions with the ambient `Metric.ball`, which is the ball of
the supremum norm — an open cube — and not a Euclidean ball.  The outward
comparison costs a factor `√d`.

A last section records the two facts about `matVecMul` needed when a linear image
of a domain is taken: it is continuous, and the identity matrix acts trivially.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Elementary real scaffolding -/

/-- A real number is dominated by a nonnegative real whose square dominates its
square. -/
theorem lt_of_sq_lt_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra hcon
  push Not at hcon
  have h1 : b * b ≤ a * a := mul_self_le_mul_self hb hcon
  have h2 : b ^ 2 ≤ a ^ 2 := by
    calc b ^ 2 = b * b := pow_two b
      _ ≤ a * a := h1
      _ = a ^ 2 := (pow_two a).symm
  linarith only [h, h2]

/-! ## Euclidean bilinear algebra on `Vec d`

The ambient norm of `Vec d` is the supremum norm, so every Euclidean quantity is
written through `vecDot`/`vecNormSq` and the bilinear identities have to be
supplied by hand. -/

theorem vecDot_sub_left (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]

theorem vecDot_sub_right (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, ← sub_eq_add_neg]

theorem vecNormSq_add (x y : Vec d) :
    vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
  have h1 : vecDot (x + y) (x + y) = vecDot x (x + y) + vecDot y (x + y) :=
    vecDot_add_left x y (x + y)
  have h2 : vecDot x (x + y) = vecDot x x + vecDot x y := vecDot_add_right x x y
  have h3 : vecDot y (x + y) = vecDot y x + vecDot y y := vecDot_add_right y x y
  have h4 : vecDot y x = vecDot x y := vecDot_comm y x
  simp only [vecNormSq]
  rw [h1, h2, h3, h4]
  ring

theorem vecNormSq_sub (x y : Vec d) :
    vecNormSq (x - y) = vecNormSq x - 2 * vecDot x y + vecNormSq y := by
  have h1 : vecDot (x - y) (x - y) = vecDot x (x - y) - vecDot y (x - y) :=
    vecDot_sub_left x y (x - y)
  have h2 : vecDot x (x - y) = vecDot x x - vecDot x y := vecDot_sub_right x x y
  have h3 : vecDot y (x - y) = vecDot y x - vecDot y y := vecDot_sub_right y x y
  have h4 : vecDot y x = vecDot x y := vecDot_comm y x
  simp only [vecNormSq]
  rw [h1, h2, h3, h4]
  ring

theorem vecNormSq_neg (x : Vec d) : vecNormSq (-x) = vecNormSq x := by
  simp only [vecNormSq]
  rw [vecDot_neg_left, vecDot_neg_right, neg_neg]

theorem vecNormSq_eq_sum_sq (x : Vec d) : vecNormSq x = ∑ i, x i ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

/-- Cauchy–Schwarz in the form used for the Euclidean triangle inequality. -/
theorem vecDot_le_sqrt_mul_sqrt (x y : Vec d) :
    vecDot x y ≤ Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y) := by
  have h := sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  have h1 : Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y)
      = Real.sqrt (vecNormSq x * vecNormSq y) :=
    (Real.sqrt_mul (vecNormSq_nonneg x) _).symm
  rw [h1]
  calc vecDot x y ≤ |vecDot x y| := le_abs_self _
    _ = Real.sqrt (vecDot x y ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (vecNormSq x * vecNormSq y) := Real.sqrt_le_sqrt h

/-- The Euclidean triangle inequality for `Real.sqrt ∘ vecNormSq`. -/
theorem sqrt_vecNormSq_add_le (x y : Vec d) :
    Real.sqrt (vecNormSq (x + y)) ≤ Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y) := by
  have hxx : Real.sqrt (vecNormSq x) ^ 2 = vecNormSq x := Real.sq_sqrt (vecNormSq_nonneg x)
  have hyy : Real.sqrt (vecNormSq y) ^ 2 = vecNormSq y := Real.sq_sqrt (vecNormSq_nonneg y)
  have hcs : vecDot x y ≤ Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y) :=
    vecDot_le_sqrt_mul_sqrt x y
  have hexp : (Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y)) ^ 2
      = vecNormSq x + 2 * (Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y))
        + vecNormSq y := by
    linear_combination hxx + hyy
  have key : vecNormSq (x + y) ≤ (Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y)) ^ 2 := by
    rw [vecNormSq_add, hexp]
    linarith only [hcs]
  calc Real.sqrt (vecNormSq (x + y))
      ≤ Real.sqrt ((Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y)) ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y) := Real.sqrt_sq (by positivity)

/-- The reverse Euclidean triangle inequality for `Real.sqrt ∘ vecNormSq`. -/
theorem abs_sqrt_vecNormSq_sub_le (x y : Vec d) :
    |Real.sqrt (vecNormSq x) - Real.sqrt (vecNormSq y)| ≤ Real.sqrt (vecNormSq (x - y)) := by
  have hxy : (x - y) + y = x := by ext i; simp
  have hyx : (y - x) + x = y := by ext i; simp
  have hsym : vecNormSq (y - x) = vecNormSq (x - y) := by
    rw [show y - x = -(x - y) by ext i; simp, vecNormSq_neg]
  have h1 : Real.sqrt (vecNormSq x)
      ≤ Real.sqrt (vecNormSq (x - y)) + Real.sqrt (vecNormSq y) := by
    have h := sqrt_vecNormSq_add_le (x - y) y
    rwa [hxy] at h
  have h2 : Real.sqrt (vecNormSq y)
      ≤ Real.sqrt (vecNormSq (x - y)) + Real.sqrt (vecNormSq x) := by
    have h := sqrt_vecNormSq_add_le (y - x) x
    rwa [hyx, hsym] at h
  exact abs_sub_le_iff.mpr ⟨by linarith only [h1], by linarith only [h2]⟩

/-! ## The Euclidean ball `euclideanBallAt` -/

theorem mem_euclideanBallAt_iff {c : Vec d} {r : ℝ} (x : Vec d) :
    x ∈ euclideanBallAt c r ↔ vecNormSq (x - c) < r ^ 2 := Iff.rfl

theorem mem_euclideanBall_iff {R : ℝ} (x : Vec d) :
    x ∈ euclideanBall d R ↔ vecNormSq x < R ^ 2 := by
  simp [euclideanBall, euclideanBallAt]

theorem center_mem_euclideanBallAt (c : Vec d) {r : ℝ} (hr : 0 < r) :
    c ∈ euclideanBallAt c r := by
  change vecNormSq (c - c) < r ^ 2
  rw [sub_self, show vecNormSq (0 : Vec d) = 0 from vecNormSq_eq_zero_iff.mpr rfl]
  exact pow_pos hr 2

theorem continuous_vecNormSq : Continuous (fun x : Vec d => vecNormSq x) := by
  simp only [vecNormSq, vecDot]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

theorem continuous_vecNormSq_sub (c : Vec d) :
    Continuous (fun x : Vec d => vecNormSq (x - c)) :=
  continuous_vecNormSq.comp (continuous_id.sub continuous_const)

theorem isOpen_euclideanBallAt (c : Vec d) (r : ℝ) : IsOpen (euclideanBallAt c r) :=
  isOpen_lt (continuous_vecNormSq_sub c) continuous_const

theorem isOpen_euclideanBall (d : ℕ) (R : ℝ) : IsOpen (euclideanBall d R) :=
  isOpen_euclideanBallAt _ _

/-- The easy half of the boundary description of the Euclidean ball: every
frontier point lies on the Euclidean sphere.  (The reverse inclusion is not
needed anywhere.) -/
theorem vecNormSq_of_mem_frontier_euclideanBall {R : ℝ} {c : Vec d}
    (hc : c ∈ frontier (euclideanBall d R)) : vecNormSq c = R ^ 2 := by
  have hopen := isOpen_euclideanBall d R
  have hclosed : IsClosed {x : Vec d | vecNormSq x ≤ R ^ 2} :=
    isClosed_le continuous_vecNormSq continuous_const
  have hsub : euclideanBall d R ⊆ {x : Vec d | vecNormSq x ≤ R ^ 2} := fun x hx =>
    le_of_lt ((mem_euclideanBall_iff x).mp hx)
  have h1 : vecNormSq c ≤ R ^ 2 :=
    closure_minimal hsub hclosed (frontier_subset_closure hc)
  have h2 : c ∉ euclideanBall d R := by
    intro hmem
    exact hc.2 (by rwa [hopen.interior_eq])
  have h3 : ¬ vecNormSq c < R ^ 2 := fun h => h2 ((mem_euclideanBall_iff c).mpr h)
  exact le_antisymm h1 (le_of_not_gt h3)

/-! ## Comparison of the Euclidean ball with the ambient (sup-norm) ball

`Metric.ball` on `Vec d = Fin d → ℝ` is the ball of the SUP norm — an open cube —
not the Euclidean ball.  These are the two comparison inclusions. -/

theorem euclideanBallAt_subset_metricBall (c : Vec d) {r : ℝ} (hr : 0 < r) :
    euclideanBallAt c r ⊆ Metric.ball c r := by
  intro x hx
  have hx' : vecNormSq (x - c) < r ^ 2 := hx
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro i
  have h1 : (x - c) i ^ 2 ≤ vecNormSq (x - c) := sq_apply_le_vecNormSq (x - c) i
  have h2 : |x i - c i| ^ 2 < r ^ 2 := by
    have hcoord : (x - c) i = x i - c i := rfl
    rw [hcoord] at h1
    rw [sq_abs]
    linarith only [h1, hx']
  have hdist : dist (x i) (c i) = |x i - c i| := Real.dist_eq _ _
  rw [hdist]
  exact lt_of_sq_lt_sq' hr.le h2

theorem vecNormSq_sub_le_of_mem_metricBall {c x : Vec d} {r : ℝ}
    (hx : x ∈ Metric.ball c r) : vecNormSq (x - c) ≤ (d : ℝ) * r ^ 2 := by
  have hcoord : ∀ i : Fin d, |x i - c i| < r := by
    intro i
    have h := Metric.mem_ball.mp hx
    have h1 : dist (x i) (c i) ≤ dist x c := by
      simpa [Real.dist_eq, Real.norm_eq_abs] using!
        norm_le_pi_norm (x - c) i
    have h2 : dist (x i) (c i) < r := lt_of_le_of_lt h1 h
    rwa [Real.dist_eq] at h2
  have hsum : ∑ i, (x - c) i ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hci : (x - c) i = x i - c i := rfl
    rw [hci, ← sq_abs]
    have habs : 0 ≤ |x i - c i| := abs_nonneg _
    calc |x i - c i| ^ 2 = |x i - c i| * |x i - c i| := pow_two _
      _ ≤ r * r := mul_self_le_mul_self habs (hcoord i).le
      _ = r ^ 2 := (pow_two r).symm
  have hconst : ∑ _i : Fin d, r ^ 2 = (d : ℝ) * r ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [vecNormSq_eq_sum_sq]
  linarith only [hsum, hconst]

theorem vecNormSq_sub_lt_of_mem_metricBall {c x : Vec d} {r : ℝ} (hd : 0 < d)
    (hx : x ∈ Metric.ball c r) : vecNormSq (x - c) < (d : ℝ) * r ^ 2 := by
  have hcoord : ∀ i : Fin d, |x i - c i| < r := by
    intro i
    have h := Metric.mem_ball.mp hx
    have h1 : dist (x i) (c i) ≤ dist x c := by
      simpa [Real.dist_eq, Real.norm_eq_abs] using!
        norm_le_pi_norm (x - c) i
    have h2 : dist (x i) (c i) < r := lt_of_le_of_lt h1 h
    rwa [Real.dist_eq] at h2
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hsum : ∑ i, (x - c) i ^ 2 < ∑ _i : Fin d, r ^ 2 := by
    refine Finset.sum_lt_sum_of_nonempty hne fun i _ => ?_
    have hci : (x - c) i = x i - c i := rfl
    rw [hci, ← sq_abs]
    have habs : 0 ≤ |x i - c i| := abs_nonneg _
    have hlt : |x i - c i| < r := hcoord i
    calc |x i - c i| ^ 2 = |x i - c i| * |x i - c i| := pow_two _
      _ < r * r := mul_self_lt_mul_self habs hlt
      _ = r ^ 2 := (pow_two r).symm
  have hconst : ∑ _i : Fin d, r ^ 2 = (d : ℝ) * r ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [vecNormSq_eq_sum_sq]
  linarith only [hsum, hconst]

/-! ## Linear maps on `Vec d` -/

theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := Matrix.one_mulVec x

theorem continuous_matVecMul (M : Mat d) : Continuous (fun x : Vec d => matVecMul M x) := by
  refine continuous_pi fun i => ?_
  simp only [matVecMul]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

end

end HighContrast
end HCPolySupport
