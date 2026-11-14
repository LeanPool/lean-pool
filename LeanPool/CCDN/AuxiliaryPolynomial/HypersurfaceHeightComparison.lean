/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.HypersurfaceHeightDeterminant
import LeanPool.CCDN.Determinant.HomogeneousDeterminantComparison

/-! Exact-rank Bombieri--Vaaler comparison for higher-dimensional hypersurfaces.
Absence of an auxiliary polynomial forces the explicit numerical inequality. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The Hilbert function `s` of a degree-`d` hypersurface in `n + 3` variables, defined by
`s + C(n + 2 + (M - d), M - d) = C(n + 2 + M, M)`, is positive in every degree `M ≥ d`. -/
lemma hypersurface_homogeneous_rank_pos {n d M s : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M) : 0 < s := by
  rw [← Nat.choose_symm_add (a := n + 2) (b := M - d),
    ← Nat.choose_symm_add (a := n + 2) (b := M)] at hr
  have hM : 0 < M := lt_of_lt_of_le hd hdM
  have hmon := Nat.choose_le_choose (n + 2)
    (show n + 2 + (M - d) ≤ n + 1 + M by omega)
  have hpascal : (n + 2 + M).choose (n + 2) =
      (n + 1 + M).choose (n + 1) + (n + 1 + M).choose (n + 2) := by
    convert Nat.choose_succ_succ' (n + 1 + M) (n + 1) using 1
    congr 1
    omega
  have hp : 0 < (n + 1 + M).choose (n + 1) := Nat.choose_pos (by omega)
  omega

/-- With no auxiliary nonmultiple of degree M, the exact homogeneous Hilbert
rank satisfies the archimedean/nonarchimedean determinant comparison. -/
theorem hypersurface_no_auxiliary_height_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hdM : d ≤ M)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    {B : ℝ} {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hrel : ∀ g : MvPolynomial (Fin (n + 3)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    ∃ s : ℕ, 0 < s ∧ s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M ∧
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
          (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + Real.log (1 + Real.log H / (d : ℝ) ^ 2)) -
            hypersurfaceHeightDeterminantError n) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((n + 2 + M).choose M) +
          s * M * Real.log B - (((n + 2 + M).choose M : ℝ) - s) *
            Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hzB.eval_eq_zero
      hzB.one_le_radius hzB.abs_le hrel
  have hs := hypersurface_homogeneous_rank_pos hd hdM hr
  refine ⟨s, hs, hr, ?_⟩
  let F := fun j => (monomial (homogeneousMonomials (n + 2) M j) 1 : MvPolynomial (Fin (n + 3)) ℤ)
  have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
    isHomogeneous_monomial _ (homogeneousMonomials_degree (n + 2) M j)
  have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
      evaluationMatrix (homogeneousMonomials (n + 2) M) (z ∘ a) := by
    ext i j
    simp [F, evaluationMatrix, eval_monomial]
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i j => eval ((z ∘ a) i) (F j)).map ((↑) : ℤ → ℚ)).row := by
    rw [he]
    exact hi
  have hlower := hypersurface_determinant_log_lower_height (z := z ∘ a) hs f hf hd hir H hH
    hcoeff ⟨hF, fun i => hzB.primitive (a i), fun i => hzB.eval_eq_zero (a i), hi'⟩
  rw [he] at hlower
  exact hlower.trans hupper

end
end CCDN
