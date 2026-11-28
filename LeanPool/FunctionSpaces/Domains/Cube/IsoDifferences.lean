/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.Modulus
public import LeanPool.FunctionSpaces.Analysis.Differences.TranslationAlgebra

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Isotropic differences and their expansion into coordinate differences

The **isotropic difference** of order `r` with step `h ∈ ℝ^d`,
`Δ_h^r f(x) = ∑_k (-1)^(r-k) C(r,k) f(x + kh)` (`Rd.higherDiff`, `Cube.higherDiff_apply`), moves all
coordinates at once; with the step `t e_i` it is the difference in coordinate `i`
(`Cube.higherDiff_single`). The translation algebra `ℂ[ℝ^d]` of
`FunctionSpaces.Analysis.Differences.TranslationAlgebra` expands it into differences in single
coordinates: the element `(δ_{h_i e_i} - 1)^m` acts by the coordinate difference `Δ^m_{h_i e_i}`
(`Cube.diffAct_coordElem_pow`), a product of such elements along a list of coordinates by the mixed
coordinate difference `M_m f = Δ^{m_0}_{h_0 e_0} ⋯ Δ^{m_{d-1}}_{h_{d-1} e_{d-1}} f`
(`Cube.mixedDiff`, `Cube.diffAct_list_prod`), and the expansion
`(δ_h - 1)^r = ∑_α δ_{s_α} ∏_i (δ_i - 1)^{m_i(α)}` (`TranslationAlgebra.single_sub_one_pow_eq_sum`)
gives `Δ_h^r f(x) = ∑_α M_{m(α)} f(x + s_α)` (`Cube.higherDiff_eq_sum`): a sum of `d^r` mixed
coordinate differences of total order `r`, at points shifted by `s_α`.

The slices in coordinate `i` of a mixed difference in other coordinates are combinations of
slices of `f` (`Cube.slice_mixedDiff_mem`), so they stay in every subspace of functions of one
variable that contains the slices of `f`.
-/

@[expose] public section

open MeasureTheory Set
open Rd (higherDiff)
open scoped ENNReal

namespace Cube

open Interval TranslationAlgebra

variable {d : ℕ}

/-! ### Isotropic differences -/

/-- `Δ_h^r f(x) = ∑_{k ≤ r} (-1)^(r-k) C(r,k) f(x + kh)`. -/
theorem higherDiff_apply (r : ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    higherDiff r h f x = ∑ k ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (x + (k : ℝ) • h) :=
  Rd.higherDiff_apply r h f x

/-- Isotropic differences are linear. -/
theorem higherDiff_add (r : ℕ) (h : Fin d → ℝ) (f g : (Fin d → ℝ) → ℂ) :
    higherDiff r h (f + g) = higherDiff r h f + higherDiff r h g :=
  fwdDiff_iter_add h f g r

/-- **Isotropic differences in a coordinate direction** are the coordinate differences: the
isotropic difference with step `t e_i` is the difference `Cube.cubeDiff r t i` in coordinate `i`. -/
theorem higherDiff_single (r : ℕ) (i : Fin d) (t : ℝ) (f : (Fin d → ℝ) → ℂ) :
    higherDiff r (Pi.single i t) f = cubeDiff r t i f := by
  funext x
  rw [higherDiff_apply, cubeDiff_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  funext c
  by_cases hc : c = i
  · subst hc
    simp
  · simp [hc]

/-! ### Mixed coordinate differences -/

/-- The **mixed coordinate difference** along a list of coordinates: the difference of order
`m_i` with step `h_i` in each coordinate `i` of the list, the last one first. -/
noncomputable def mixedDiff (m : Fin d → ℕ) (h : Fin d → ℝ) (l : List (Fin d))
    (f : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  l.foldr (fun i g => cubeDiff (m i) (h i) i g) f

/-- The mixed difference along the empty list is the function itself. -/
theorem mixedDiff_nil (m : Fin d → ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) :
    mixedDiff m h [] f = f := rfl

/-- The mixed difference along `i :: l`. -/
theorem mixedDiff_cons (m : Fin d → ℕ) (h : Fin d → ℝ) (i : Fin d) (l : List (Fin d))
    (f : (Fin d → ℝ) → ℂ) :
    mixedDiff m h (i :: l) f = cubeDiff (m i) (h i) i (mixedDiff m h l f) := rfl

/-- Mixed differences of measurable functions are measurable. -/
theorem measurable_mixedDiff (m : Fin d → ℕ) (h : Fin d → ℝ) (l : List (Fin d))
    {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) : Measurable (mixedDiff m h l f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact measurable_cubeDiff ih _ _ i

/-- `(δ_{h_i e_i} - 1)^m` acts by the coordinate difference `Δ^m_{h_i e_i}`. -/
theorem diffAct_coordElem_pow (h : Fin d → ℝ) (i : Fin d) (m : ℕ) (f : (Fin d → ℝ) → ℂ) :
    diffAct (coordElem h i ^ m) f = cubeDiff m (h i) i f := by
  rw [coordElem, ← higherDiff_eq_diffAct, higherDiff_single]

/-- **Products of coordinate elements act by mixed differences**. -/
theorem diffAct_list_prod (m : Fin d → ℕ) (h : Fin d → ℝ) (l : List (Fin d))
    (f : (Fin d → ℝ) → ℂ) :
    diffAct ((l.map fun i => coordElem h i ^ m i).prod) f = mixedDiff m h l f := by
  induction l with
  | nil => simp [mixedDiff_nil]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp, ih,
      diffAct_coordElem_pow, mixedDiff_cons]

/-! ### The expansion -/

/-- **The isotropic difference as a sum of mixed coordinate differences**:
`Δ_h^r f(x) = ∑_α M_{m(α)} f(x + s_α)`, summed over the words `α : Fin r → Fin d`, with the
multiplicities `m_i(α)` and the shifts `s_α`. -/
theorem higherDiff_eq_sum (r : ℕ) (h : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    higherDiff r h f x = ∑ α : Fin r → Fin d,
      mixedDiff (count α) h (List.finRange d) f (x + shiftVec h α) := by
  rw [higherDiff_eq_diffAct, single_sub_one_pow_eq_sum, map_sum, LinearMap.sum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, mul_apply_eq_comp, diffAct_single_one, transl_apply, Fin.prod_univ_def,
    diffAct_list_prod]

/-! ### Slices of mixed differences -/

/-- **Slices of coordinate differences in other coordinates**: for `c ≠ i`, the slice in
coordinate `i` of `Δ^m_{t e_c} G` is a combination of slices of `G` in coordinate `i`. -/
theorem slice_cubeDiff_of_ne (m : ℕ) (t : ℝ) {c i : Fin d} (hci : c ≠ i)
    (G : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    slice (cubeDiff m t c G) x i = ∑ k ∈ Finset.range (m + 1),
      ((-1 : ℂ) ^ (m - k) * (m.choose k : ℂ)) •
        slice G (Function.update x c (x c + k * t)) i := by
  funext s
  rw [Finset.sum_apply]
  simp only [slice, cubeDiff_eq, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Function.update_of_ne hci, Function.update_comm hci]

/-- **Slices of mixed differences stay in a subspace**: if every slice of `f` in coordinate `i`
lies in a subspace `V` of functions of one variable, so does every slice in coordinate `i` of a
mixed difference along a list of coordinates `≠ i`. -/
theorem slice_mixedDiff_mem (V : Submodule ℂ (ℝ → ℂ)) (m : Fin d → ℕ) (h : Fin d → ℝ)
    {i : Fin d} {l : List (Fin d)} (hl : i ∉ l) {f : (Fin d → ℝ) → ℂ}
    (hf : ∀ x, slice f x i ∈ V) (x : Fin d → ℝ) : slice (mixedDiff m h l f) x i ∈ V := by
  induction l generalizing x with
  | nil => exact hf x
  | cons c l ih =>
    have hci : c ≠ i := fun h => hl (h ▸ List.mem_cons_self)
    have hl' : i ∉ l := fun h => hl (List.mem_cons_of_mem c h)
    rw [mixedDiff_cons, slice_cubeDiff_of_ne _ _ hci]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (ih hl' _)

end Cube
