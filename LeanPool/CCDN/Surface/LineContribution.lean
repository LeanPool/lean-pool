/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Plane.IntegralAffineLine
import LeanPool.CCDN.Surface.DirectionSum
import LeanPool.CCDN.Surface.LineDirections
import LeanPool.CCDN.Surface.NonlinearCount
import LeanPool.CCDN.Surface.ParallelLines

/-! Finite families of rational affine lines on a surface. Grouping
lines by their projective direction combines the primitive spacing bound
with the uniform reciprocal-height sum. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Weighted finite sums with a uniform bound on the cardinality of each
fiber. No injectivity of the indexing map is required. -/
private theorem sum_comp_le_fiber_card_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (p : α → β) (w : β → ℝ) (M : ℝ)
    (hw : ∀ q ∈ s.image p, 0 ≤ w q)
    (hfiber : ∀ q ∈ s.image p, ((s.filter (fun x => p x = q)).card : ℝ) ≤ M) :
    ∑ x ∈ s, w (p x) ≤ M * ∑ q ∈ s.image p, w q := by
  classical
  calc
    _ = ∑ q ∈ s.image p, ∑ x ∈ s.filter (fun x => p x = q), w (p x) :=
      (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem p hx) _).symm
    _ ≤ ∑ q ∈ s.image p, M * w q := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        _ = ∑ _x ∈ s.filter (fun x => p x = q), w q :=
          Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])
        _ = ((s.filter (fun x => p x = q)).card : ℝ) * w q := by simp
        _ ≤ M * w q := mul_le_mul_of_nonneg_right (hfiber q hq) (hw q hq)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The aggregation step, stated separately so that the geometric
parallel-line theorem can supply its only remaining input. -/
private theorem surface_line_contribution_of_parallel_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      3 ≤ f.totalDegree →
      ∀ (B : ℝ), 0 ≤ B →
      ∀ s : Finset (Set (RatPoint 3)),
      (∀ L ∈ s, ∃ a v, L = rationalAffineLine a v) →
      (∀ L ∈ s, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) →
      (∀ (v : RatPoint 3), v ≠ 0 →
        ∀ t : Finset (Set (RatPoint 3)), t ⊆ s →
          (∀ L ∈ t, ∃ a, L = rationalAffineLine a v) →
          t.card ≤ f.totalDegree * (f.totalDegree - 1)) →
      (∑ L ∈ s, (count L B : ℝ)) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + s.card ∧
      (count (⋃ L ∈ s, L) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + s.card := by
  classical
  obtain ⟨K, hK, hweight⟩ := integer_projective_plane_reciprocal_height_sum
  refine ⟨4 * K, by positivity, ?_⟩
  intro f hir hd B hB s hlines hsurface hparallel
  let t := s.filter (fun L => 1 < count L B)
  have hdir (L : Set (RatPoint 3)) (hL : L ∈ t) :
      ∃ p : ProjectivePoint 2,
        p ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
        0 < p.mulHeight ∧ p.mulHeight ≤ 2 * B ∧
        (∃ a, L = rationalAffineLine a p.rep) ∧
        (count L B : ℝ) ≤ 4 * B / p.mulHeight :=
    surface_line_projective_direction f L (hlines L (Finset.mem_filter.mp hL).1)
      (hsurface L (Finset.mem_filter.mp hL).1) hB (Finset.mem_filter.mp hL).2
  let p : Set (RatPoint 3) → ProjectivePoint 2 := fun L =>
    if hL : L ∈ t then (hdir L hL).choose else Classical.choice inferInstance
  have hp (L : Set (RatPoint 3)) (hL : L ∈ t) :
      p L ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
      0 < (p L).mulHeight ∧ (p L).mulHeight ≤ 2 * B ∧
      (∃ a, L = rationalAffineLine a (p L).rep) ∧
      (count L B : ℝ) ≤ 4 * B / (p L).mulHeight := by
    simpa only [p, dite_eq_left hL] using (hdir L hL).choose_spec
  have hfib (q : ProjectivePoint 2) (_hq : q ∈ t.image p) :
      ((t.filter (fun L => p L = q)).card : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by
    have hc := hparallel q.rep q.rep_nonzero (t.filter (fun L => p L = q))
      (fun L hL => (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).1) (by
        intro L hL
        obtain ⟨hLt, he⟩ := Finset.mem_filter.mp hL
        obtain ⟨-, -, -, hLdir, -⟩ := hp L hLt
        simpa only [he] using hLdir)
    have hdle : f.totalDegree * (f.totalDegree - 1) ≤ f.totalDegree ^ 2 := by
      nlinarith [Nat.sub_le f.totalDegree 1]
    exact_mod_cast hc.trans hdle
  have himage : ∑ q ∈ t.image p, 1 / q.mulHeight ≤ K * (f.totalDegree : ℝ) ^ 4 := by
    apply hweight f.totalDegree hd (homogeneousComponent f.totalDegree f)
      (homogeneousComponent_isHomogeneous _ _) hir
    intro q hq
    obtain ⟨L, hLt, rfl⟩ := Finset.mem_image.mp hq
    exact (hp L hLt).1
  have hsum : ∑ L ∈ t, 1 / (p L).mulHeight ≤ K * (f.totalDegree : ℝ) ^ 6 := by
    calc
      _ ≤ (f.totalDegree : ℝ) ^ 2 * ∑ q ∈ t.image p, 1 / q.mulHeight :=
        sum_comp_le_fiber_card_mul t p (fun q => 1 / q.mulHeight) _
          (fun q _ => by positivity) hfib
      _ ≤ (f.totalDegree : ℝ) ^ 2 * (K * (f.totalDegree : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left himage (by positivity)
      _ = _ := by ring
  have hgood : ∑ L ∈ t, (count L B : ℝ) ≤ (4 * K) * (f.totalDegree : ℝ) ^ 6 * B := by
    calc
      _ ≤ ∑ L ∈ t, 4 * B / (p L).mulHeight :=
        Finset.sum_le_sum (fun L hL => by obtain ⟨-, -, -, -, hLcount⟩ := hp L hL; exact hLcount)
      _ = 4 * B * ∑ L ∈ t, 1 / (p L).mulHeight := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      _ ≤ 4 * B * (K * (f.totalDegree : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have hbad : ∑ L ∈ s.filter (fun L => ¬1 < count L B), (count L B : ℝ) ≤ s.card := by
    calc
      _ ≤ ∑ _L ∈ s.filter (fun L => ¬1 < count L B), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro L hL
        exact_mod_cast (show count L B ≤ 1 from Nat.le_of_not_gt (Finset.mem_filter.mp hL).2)
      _ = ((s.filter (fun L => ¬1 < count L B)).card : ℝ) := by simp
      _ ≤ s.card := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hall : ∑ L ∈ s, (count L B : ℝ) ≤
      (4 * K) * (f.totalDegree : ℝ) ^ 6 * B + s.card := by
    have he : (∑ L ∈ t, (count L B : ℝ)) +
        (∑ L ∈ s.filter (fun L => ¬1 < count L B), (count L B : ℝ)) =
        ∑ L ∈ s, (count L B : ℝ) := Finset.sum_filter_add_sum_filter_not _ _ _
    linarith
  refine ⟨hall, ?_⟩
  have hc : (count (⋃ L ∈ s, L) B : ℝ) ≤ ∑ L ∈ s, (count L B : ℝ) := by
    exact_mod_cast count_biUnion_finset_le s (fun L => L) B
  exact hc.trans hall

/-- Corrected CCDN Proposition 4.3.3 for a finite set of rational
affine lines. Absolute irreducibility of the leading form supplies the
parallel-line bound inside the proof. The constant is chosen before the
surface, its degree, the radius and the family of lines. -/
theorem surface_line_contribution :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      3 ≤ f.totalDegree →
      ∀ (B : ℝ), 0 ≤ B →
      ∀ s : Finset (Set (RatPoint 3)),
      (∀ L ∈ s, ∃ a v, L = rationalAffineLine a v) →
      (∀ L ∈ s, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) →
      (∑ L ∈ s, (count L B : ℝ)) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + s.card ∧
      (count (⋃ L ∈ s, L) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + s.card := by
  obtain ⟨C, hC, hbound⟩ := surface_line_contribution_of_parallel_bound
  refine ⟨C, hC, ?_⟩
  intro f hir hd B hB s hlines hsurface
  apply hbound f hir hd B hB s hlines hsurface
  intro v hv t ht htv
  exact surface_parallel_lines_card_le f hir (by omega) v hv t htv
    (fun L hL => hsurface L (ht hL))

end
end CCDN
