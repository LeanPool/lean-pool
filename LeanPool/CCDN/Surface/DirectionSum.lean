/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Height.ProjectiveZeroLocus
import LeanPool.CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import LeanPool.CCDN.Plane.ProjectivePlaneLinearCount

/-! The reciprocal heights of distinct rational projective points on a
plane curve of degree at least three have a uniform, coefficient-independent
sum. Geometric height bands turn the proved projective point count into
the weighted estimate used for surface-line directions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem sum_inv_height_geometric_bound {α : Type*}
    (s : Finset α) (h : α → ℝ) (M : ℝ) (_hM : 0 ≤ M) (N : ℕ)
    (hheight : ∀ x ∈ s, 1 ≤ h x)
    (hmax : ∀ x ∈ s, h x ≤ (8 : ℝ) ^ N)
    (hcount : ∀ k : ℕ,
      ((s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) ≤ M * 4 ^ k) :
    ∑ x ∈ s, 1 / h x ≤ 9 * M - 8 * M * (1 / 2 : ℝ) ^ N := by
  classical
  induction N generalizing s with
  | zero =>
    have he (x : α) (hx : x ∈ s) : h x = 1 := by
      have := hmax x hx
      have := hheight x hx
      norm_num at *
      linarith
    have hs : s.filter (fun x => h x ≤ (8 : ℝ) ^ 0) = s := by
      exact Finset.filter_eq_self.mpr hmax
    have hc := hcount 0
    rw [hs] at hc
    have hsum : ∑ x ∈ s, 1 / h x = (s.card : ℝ) := by
      calc
        _ = ∑ _x ∈ s, (1 : ℝ) := Finset.sum_congr rfl (fun x hx => by rw [he x hx]; norm_num)
        _ = _ := by simp
    rw [hsum]
    simpa only [pow_zero, mul_one, show 9 * M - 8 * M = M by ring] using hc
  | succ N ih =>
    let t := s.filter (fun x => h x ≤ (8 : ℝ) ^ N)
    let u := s.filter (fun x => ¬h x ≤ (8 : ℝ) ^ N)
    have ht : ∑ x ∈ t, 1 / h x ≤ 9 * M - 8 * M * (1 / 2 : ℝ) ^ N := by
      apply ih t
      · intro x hx
        exact hheight x (Finset.mem_filter.mp hx).1
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · intro k
        have hs : (t.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card ≤
            (s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨hx, hk⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hk⟩
        exact (show ((t.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) ≤
          ((s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) by
            exact_mod_cast hs).trans (hcount k)
    have hscard : (s.card : ℝ) ≤ M * 4 ^ (N + 1) := by
      have hs : s.filter (fun x => h x ≤ (8 : ℝ) ^ (N + 1)) = s :=
        Finset.filter_eq_self.mpr hmax
      simpa only [hs] using hcount (N + 1)
    have hu : ∑ x ∈ u, 1 / h x ≤ 4 * M * (1 / 2 : ℝ) ^ N := by
      calc
        _ ≤ ∑ _x ∈ u, 1 / (8 : ℝ) ^ N := by
          apply Finset.sum_le_sum
          intro x hx
          exact one_div_le_one_div_of_le (by positivity)
            (le_of_not_ge (Finset.mem_filter.mp hx).2)
        _ = (u.card : ℝ) / (8 : ℝ) ^ N := by simp [div_eq_mul_inv]
        _ ≤ (s.card : ℝ) / (8 : ℝ) ^ N := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ s)
        _ ≤ (M * 4 ^ (N + 1)) / (8 : ℝ) ^ N :=
          div_le_div_of_nonneg_right hscard (by positivity)
        _ = 4 * M * (1 / 2 : ℝ) ^ N := by
          rw [pow_succ]
          calc
            _ = 4 * M * ((4 : ℝ) ^ N / (8 : ℝ) ^ N) := by ring
            _ = _ := by rw [← div_pow]; norm_num
    have he : (∑ x ∈ t, 1 / h x) + (∑ x ∈ u, 1 / h x) =
        ∑ x ∈ s, 1 / h x := Finset.sum_filter_add_sum_filter_not _ _ _
    rw [pow_succ]
    linarith

/-- A finite weighted-count lemma with geometric counting thresholds. Its
application below obtains the threshold counts from the proved curve theorem. -/
private theorem sum_inv_height_le_of_geometric_count {α : Type*}
    (s : Finset α) (h : α → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hheight : ∀ x ∈ s, 1 ≤ h x)
    (hcount : ∀ k : ℕ,
      ((s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) ≤ M * 4 ^ k) :
    ∑ x ∈ s, 1 / h x ≤ 9 * M := by
  classical
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ x ∈ s, h x) (show (1 : ℝ) < 8 by norm_num)
  have hmax (x : α) (hx : x ∈ s) : h x ≤ (8 : ℝ) ^ N := by
    have hs : h x ≤ ∑ x ∈ s, h x := Finset.single_le_sum
      (fun y hy => (zero_le_one.trans (hheight y hy))) hx
    exact hs.trans hN.le
  have hh := sum_inv_height_geometric_bound s h M hM N hheight hmax hcount
  have hnonneg : 0 ≤ 8 * M * (1 / 2 : ℝ) ^ N := by positivity
  linarith

private lemma eight_pow_two_thirds (k : ℕ) :
    ((8 : ℝ) ^ k) ^ (2 / 3 : ℝ) = (4 : ℝ) ^ k := by
  have he : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := by
    calc
      _ = ((2 : ℝ) ^ (3 : ℝ)) ^ (2 / 3 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ ((3 : ℝ) * (2 / 3 : ℝ)) := (Real.rpow_mul (by norm_num) _ _).symm
      _ = 4 := by norm_num
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (k : ℝ),
    Real.rpow_mul_natCast (by norm_num), he]

/-- A uniform reciprocal-height sum for distinct rational projective
zeros. The constant precedes the equation, its degree and the finite set. -/
private theorem projective_plane_reciprocal_height_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 3 ≤ d →
      ∀ f : MvPolynomial (Fin 3) ℚ, f.IsHomogeneous d → Irreducible f →
      ∀ s : Finset (ProjectivePoint 2), (∀ x ∈ s, x ∈ projectiveZeroLocus f) →
        ∑ x ∈ s, 1 / x.mulHeight ≤ C * (d : ℝ) ^ 4 := by
  classical
  refine ⟨9 * projectivePlaneAbsoluteConstant, by
    exact mul_pos (by norm_num) projectivePlaneAbsoluteConstant_pos, ?_⟩
  intro d hd f hf hir s hs
  have hC := projectivePlaneAbsoluteConstant_pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h := sum_inv_height_le_of_geometric_count s (fun x => x.mulHeight)
    (projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4)
    (by positivity) (fun x _ => x.one_le_mulHeight) ?_
  · convert h using 1
    ring
  intro k
  have hB : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
  have hc : (s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card ≤
      projectiveCount (projectiveZeroLocus f) ((8 : ℝ) ^ k) := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxs, hheight⟩ := Finset.mem_filter.mp hx
    exact mem_projectivePoints.mpr ⟨hheight, hs x hxs⟩
  have hcR : ((s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card : ℝ) ≤
      (projectiveCount (projectiveZeroLocus f) ((8 : ℝ) ^ k) : ℝ) := by exact_mod_cast hc
  have hp : ((8 : ℝ) ^ k) ^ (2 / (d : ℝ)) ≤ (4 : ℝ) ^ k := by
    calc
      _ ≤ ((8 : ℝ) ^ k) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB
        ((div_le_div_iff₀ hd0 (by norm_num)).mpr (by nlinarith))
      _ = _ := eight_pow_two_thirds k
  exact (hcR.trans (projective_plane_equation_bound f hf (by omega) hir hB)).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

/-- There is an absolute constant `C` such that, for every absolutely irreducible integer
homogeneous polynomial `F` of degree `d ≥ 3` in three variables, the sum of the reciprocal
multiplicative heights of any finite set of rational points of the plane curve `F = 0` is at
most `C d⁴`; no primitivity or coefficient-height hypothesis is needed. -/
theorem integer_projective_plane_reciprocal_height_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 3 ≤ d →
      ∀ F : MvPolynomial (Fin 3) ℤ, F.IsHomogeneous d →
      AbsolutelyIrreducible F →
      ∀ s : Finset (ProjectivePoint 2),
        (∀ x ∈ s, x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) F)) →
        ∑ x ∈ s, 1 / x.mulHeight ≤ C * (d : ℝ) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := projective_plane_reciprocal_height_sum
  refine ⟨C, hC, ?_⟩
  intro d hd F hF hir s hs
  exact hbound d hd (map (Int.castRingHom ℚ) F) (hF.map _)
    (rational_irreducible_of_charZero_map F hir) s hs

end
end CCDN
