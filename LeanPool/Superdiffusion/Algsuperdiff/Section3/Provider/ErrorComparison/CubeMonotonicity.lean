/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.ExponentMonotonicity

/-!
# CubeMonotonicity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Cube monotonicity of the multiscale lower ellipticity at the centered cubes

This module supplies it.  The centered cube `square_{k-1}` is the *middle
child* of `square_k` — CoarseGraining's `middleChild_mem_childCubes` at a cube
with vanishing index — so an induction on the depth places `square_m` in the
descendant tree of `square_n`.

## Main results

* `originCube_pred_mem_childCubes`: `square_{n-1}` is a child of `square_n`.
* `originCube_mem_descendantsAtDepth`: `square_{n-j}` is a depth-`j` descendant
  of `square_n`.
* `lambdaSq_originCube_le_descendantWeight_mul_lambdaSq`: the named
  cube-monotonicity lemma at the centered pair,
  `lambda_{s,q}(square_n; a) <= 3^{2s(n-m)} lambda_{s,q}(square_m; a)`.

## References

* ABK26, `l.bad.event.lemma` (decomposition, recombination).
* ABK26, `e.ellipticities.monotone.ordered`.
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

variable {d : ℕ}

/-! ## The centered cubes form a descendant chain -/

/-- The centered cube of scale `n - 1` is the middle child of the centered cube
of scale `n`. -/
theorem originCube_pred_mem_childCubes (d : ℕ) (n : ℤ) :
    originCube d (n - 1) ∈ childCubes (originCube d n) := by
  have h := middleChild_mem_childCubes (originCube d n)
  have hEq :
      ({ scale := (originCube d n).scale - 1
         index := fun i => 3 * (originCube d n).index i } : TriadicCube d) =
        originCube d (n - 1) := by
    simp only [originCube, Pi.zero_apply, mul_zero]
    rfl
  rwa [hEq] at h

/-- The centered cube of scale `n - j` is a depth-`j` triadic descendant of the
centered cube of scale `n`. -/
theorem originCube_mem_descendantsAtDepth (d : ℕ) (n : ℤ) (j : ℕ) :
    originCube d (n - (j : ℤ)) ∈ descendantsAtDepth (originCube d n) j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [descendantsAtDepth_succ]
      refine Finset.mem_biUnion.2 ⟨originCube d (n - (j : ℤ)), ih, ?_⟩
      have h := originCube_pred_mem_childCubes d (n - (j : ℤ))
      have hstep : n - (j : ℤ) - 1 = n - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [hstep] at h

/-- **The membership.**  For `m <= n` the centered cube `square_m` is a triadic
descendant of `square_n` at scale `m`. -/
theorem originCube_mem_descendantsAtScale {m n : ℤ} (hmn : m ≤ n) :
    originCube d m ∈ descendantsAtScale (originCube d n) m := by
  have hk : m ≤ (originCube d n).scale := hmn
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d n) hk]
  have h := originCube_mem_descendantsAtDepth d n
    ((originCube d n).scale - m).toNat
  have hred : n - (((originCube d n).scale - m).toNat : ℤ) = m := by
    have hscale : (originCube d n).scale = n := rfl
    rw [hscale]
    omega
  rwa [hred] at h

/-! ## Cube monotonicity at the centered pair -/

/-- For `m <= n`,

`lambda_{s,q}(square_n; a) <= 3^{2s(n-m)} lambda_{s,q}(square_m; a)`. -/
theorem lambdaSq_originCube_le_descendantWeight_mul_lambdaSq [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) {m n : ℤ} (hmn : m ≤ n) {s : ℝ}
    {q : Book.Ch02.MultiscaleExponent} (hs : 0 < s) (hq : q.IsAdmissible) :
    Book.Ch02.lambdaSq (originCube d n) s q a ≤
      Book.Ch02.multiscaleDescendantWeight (originCube d n) m s *
        Book.Ch02.lambdaSq (originCube d m) s q a :=
  lambdaSq_le_descendantWeight_mul_lambdaSq a (originCube_mem_descendantsAtScale hmn)
    hs hq

/-- The weight of the previous theorem, in closed form. -/
theorem multiscaleDescendantWeight_originCube (m n : ℤ) (s : ℝ) :
    Book.Ch02.multiscaleDescendantWeight (originCube d n) m s =
      (3 : ℝ) ^ (2 * s * ((n : ℝ) - (m : ℝ))) := by
  rw [Book.Ch02.multiscaleDescendantWeight]
  norm_num [originCube]

/-- `lambda_{1/8,2}(square_n; a) <= 3^{(n-m)/4} lambda_{1/8,2}(square_m; a)`. -/
theorem lambdaSq_originCube_eighth_le [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) {m n : ℤ} (hmn : m ≤ n) :
    Book.Ch02.lambdaSq (originCube d n) (1 / 8) (.finite 2) a ≤
      (3 : ℝ) ^ (((n : ℝ) - (m : ℝ)) / 4) *
        Book.Ch02.lambdaSq (originCube d m) (1 / 8) (.finite 2) a := by
  have h := lambdaSq_originCube_le_descendantWeight_mul_lambdaSq a hmn
    (s := 1 / 8) (q := .finite 2) (by norm_num) (by norm_num)
  rwa [multiscaleDescendantWeight_originCube,
    show (2 : ℝ) * (1 / 8) * ((n : ℝ) - (m : ℝ)) = ((n : ℝ) - (m : ℝ)) / 4 by ring] at h

end Algsuperdiff.Section3.Provider.ErrorComparison
