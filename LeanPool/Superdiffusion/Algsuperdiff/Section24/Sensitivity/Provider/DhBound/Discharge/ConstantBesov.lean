/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.Definitions
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfacesPositiveQTwo
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# ConstantBesov

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The negative Besov seminorm of a constant vector field

Source: ABK26, the third summand of the three-way split of `∇u = ∇w + ∇w* +
ℓ_p` inside `e.split.besov.stuff.begin`: the affine piece `ℓ_p` contributes the
*constant* gradient `p`, whose concrete negative Besov seminorm is a pure
geometric series.

Every descendant average of a constant field is that constant, so

```
[c]_{B^{-s}_{2,2}(Q), N} = |c| ( ∑_{j ≤ N} 3^{-2 s j} )^{1/2}
                         ≤ |c| (1 - 3^{-2s})^{-1/2}          (0 < s).
```

The bound is uniform in the depth `N`, so it also bounds the infinite-depth
`sSup` seminorm, and it exhibits the required `BddAbove` witness.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge

open HCPolySupport HCPolySupport.Book.Ch02
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- CoarseGraining writes the triadic weights with explicit `Real.rpow`; Mathlib's
`^`-notation lemmas do not rewrite against it.  This definitional bridge lets
`simp only` move between the two. -/
private theorem rpow_eq_pow (x y : ℝ) : Real.rpow x y = x ^ y := rfl

/-! ## The depth-level quantities of a constant field -/

theorem cubeBesovNegativeVectorDepthAverage_const (Q : TriadicCube d) (c : Vec d)
    (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q (fun _ => c) j = vecNormSq c := by
  unfold cubeBesovNegativeVectorDepthAverage
  simp [descendantsAverage_const_eq Q j (vecNormSq c)]

theorem sqrt_vecNormSq_eq_vecNorm (c : Vec d) :
    Real.sqrt (vecNormSq c) = vecNorm c := by
  rw [← vecNorm_sq_eq_vecNormSq]
  exact Real.sqrt_sq (vecNorm_nonneg c)

theorem cubeBesovNegativeVectorDepthSeminorm_const (Q : TriadicCube d) (s : ℝ)
    (c : Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s (fun _ => c) j =
      Real.rpow (3 : ℝ) (-s * (j : ℝ)) * vecNorm c := by
  unfold cubeBesovNegativeVectorDepthSeminorm
  rw [cubeBesovNegativeVectorDepthAverage_const, sqrt_vecNormSq_eq_vecNorm]

/-! ## The geometric constant -/

/-- The geometric constant of the constant-field negative Besov bound. -/
def constantFieldBesovConst (s : ℝ) : ℝ :=
  Real.sqrt ((1 - Real.rpow (3 : ℝ) (-(2 * s)))⁻¹)

theorem constantFieldBesovConst_nonneg (s : ℝ) : 0 ≤ constantFieldBesovConst s :=
  Real.sqrt_nonneg _

/-! ## The finite-depth bound -/

theorem cubeBesovNegativeVectorPartialSeminormTwo_const_le (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (N : ℕ) (c : Vec d) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun _ => c) ≤
      constantFieldBesovConst s * vecNorm c := by
  classical
  have hgeom :
      (∑ j ∈ Finset.range (N + 1),
          Real.rpow (3 : ℝ) (-(2 * s) * (j : ℝ))) ≤
        (1 - Real.rpow (3 : ℝ) (-(2 * s)))⁻¹ := by
    simpa using
      sum_filter_triadicDepthWeight_le_geometric_inv (2 * s) N (fun _ : ℕ => True)
        (by linarith)
  have hentry : ∀ j ∈ Finset.range (N + 1),
      (cubeBesovNegativeVectorDepthSeminorm Q s (fun _ => c) j) ^ 2 =
        Real.rpow (3 : ℝ) (-(2 * s) * (j : ℝ)) * vecNormSq c := by
    intro j _
    rw [cubeBesovNegativeVectorDepthSeminorm_const, mul_pow,
      ← vecNorm_sq_eq_vecNormSq]
    congr 1
    simp only [rpow_eq_pow]
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hsum :
      (∑ j ∈ Finset.range (N + 1),
          (cubeBesovNegativeVectorDepthSeminorm Q s (fun _ => c) j) ^ 2) =
        (∑ j ∈ Finset.range (N + 1),
          Real.rpow (3 : ℝ) (-(2 * s) * (j : ℝ))) * vecNormSq c := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl hentry
  have hle :
      (∑ j ∈ Finset.range (N + 1),
          (cubeBesovNegativeVectorDepthSeminorm Q s (fun _ => c) j) ^ 2) ≤
        (1 - Real.rpow (3 : ℝ) (-(2 * s)))⁻¹ * vecNormSq c := by
    rw [hsum]
    exact mul_le_mul_of_nonneg_right hgeom (vecNormSq_nonneg c)
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  refine (Real.sqrt_le_sqrt hle).trans (le_of_eq ?_)
  have hnn : (0 : ℝ) ≤ (1 - Real.rpow (3 : ℝ) (-(2 * s)))⁻¹ := by
    have hlt : Real.rpow (3 : ℝ) (-(2 * s)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact le_of_lt (inv_pos.mpr (by linarith))
  rw [Real.sqrt_mul hnn, sqrt_vecNormSq_eq_vecNorm]
  rfl

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound.Discharge
