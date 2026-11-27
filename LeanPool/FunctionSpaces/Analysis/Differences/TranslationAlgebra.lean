/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Differences.Differences
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The translation algebra

For an additive commutative monoid `G`, the commutative algebra `ℂ[G]` (Mathlib's
`AddMonoidAlgebra`) acts on functions `G → ℂ` by an algebra homomorphism
(`TranslationAlgebra.diffAct`, from Mathlib's `AddMonoidAlgebra.lift`): the generator `δ_v` acts
by the translation `τ_v f(x) = f(x + v)` (`TranslationAlgebra.transl`). The difference of order
`r` is a power, `Δ_h^r = (δ_h - 1)^r` (`TranslationAlgebra.higherDiff_eq_diffAct`), so identities
between differences become ring identities in `ℂ[G]`.

On `ℝ^d = Fin d → ℝ`, with `δ_i = δ_{h_i e_i}`, `δ_h = ∏_i δ_i` and
`δ_h - 1 = ∑_i (δ_i - 1) ∏_{j<i} δ_j` (`TranslationAlgebra.single_sub_one_eq_sum`, from Mathlib's
`Finset.prod_add_ordered`). The `r`-th power is a sum over the words `α : Fin r → Fin d`,
`(δ_h - 1)^r = ∑_α δ_{s_α} ∏_i (δ_i - 1)^{m_i(α)}` (`TranslationAlgebra.single_sub_one_pow_eq_sum`),
with the multiplicities `m_i(α) = #α⁻¹(i)` of total `r` (`TranslationAlgebra.count`,
`TranslationAlgebra.sum_count`) and the shifts `(s_α)_i = h_i #{l : i < α_l}`
(`TranslationAlgebra.shiftVec`, `TranslationAlgebra.shiftVec_apply`).
-/

@[expose] public section

open Rd (higherDiff)

namespace TranslationAlgebra

/-! ### The action on functions -/

section Action

variable {G : Type*} [AddCommMonoid G]

/-- The **translation** `τ_v f(x) = f(x + v)`, a linear map of functions on `G`. -/
def transl (v : G) : Module.End ℂ (G → ℂ) where
  toFun f x := f (x + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `τ_v f(x) = f(x + v)`. -/
@[simp] theorem transl_apply (v : G) (f : G → ℂ) (x : G) : transl v f x = f (x + v) := rfl

/-- The translations form a monoid homomorphism from `G`, written multiplicatively. -/
def translHom : Multiplicative G →* Module.End ℂ (G → ℂ) where
  toFun v := transl v.toAdd
  map_one' := by
    ext f x
    simp
  map_mul' v w := by
    ext f x
    simp [mul_apply_eq_comp, add_assoc]

/-- The **action of the translation algebra** `ℂ[G]` on functions on `G`: `δ_v` acts by the
translation `τ_v` (Mathlib's `AddMonoidAlgebra.lift`). -/
noncomputable def diffAct : AddMonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ (G → ℂ) :=
  AddMonoidAlgebra.lift ℂ (Module.End ℂ (G → ℂ)) G translHom

/-- `c δ_v` acts by `c τ_v`. -/
theorem diffAct_single (v : G) (c : ℂ) (f : G → ℂ) (x : G) :
    diffAct (AddMonoidAlgebra.single v c) f x = c * f (x + v) := by
  rw [diffAct, AddMonoidAlgebra.lift_single]
  rfl

/-- `δ_v` acts by the translation `τ_v`. -/
theorem diffAct_single_one (v : G) : diffAct (AddMonoidAlgebra.single v (1 : ℂ)) = transl v := by
  ext f x
  rw [diffAct_single, one_mul, transl_apply]

/-- **The difference is a power in the translation algebra**: `Δ_h^r = (δ_h - 1)^r`. -/
theorem higherDiff_eq_diffAct (r : ℕ) (h : G) (f : G → ℂ) :
    higherDiff r h f = diffAct ((AddMonoidAlgebra.single h (1 : ℂ) - 1) ^ r) f := by
  have hfwd : ⇑(diffAct (AddMonoidAlgebra.single h (1 : ℂ) - 1)) = fwdDiff h := by
    funext g x
    rw [map_sub, map_one, diffAct_single_one, LinearMap.sub_apply, Pi.sub_apply, transl_apply,
      one_apply_eq_self]
    rfl
  rw [map_pow, pow_apply_eq_iterate, hfwd, Rd.higherDiff_def]

/-- `δ_{∑ v_i} = ∏ δ_{v_i}` (Mathlib's `AddMonoidAlgebra.prod_single`). -/
theorem single_sum_one {ι : Type*} (s : Finset ι) (v : ι → G) :
    AddMonoidAlgebra.single (∑ i ∈ s, v i) (1 : ℂ) = ∏ i ∈ s, AddMonoidAlgebra.single (v i) 1 := by
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]

end Action

/-! ### Coordinate differences on `ℝ^d` -/

section Coordinates

variable {d : ℕ}

/-- The element `δ_{h_i e_i} - 1` of the translation algebra, the first difference in
coordinate `i`. -/
noncomputable def coordElem (h : Fin d → ℝ) (i : Fin d) : AddMonoidAlgebra ℂ (Fin d → ℝ) :=
  AddMonoidAlgebra.single (Pi.single i (h i)) 1 - 1

/-- The multiplicities `m_i(α) = #{l : α_l = i}` of a word `α : Fin r → Fin d`. -/
def count {r : ℕ} (α : Fin r → Fin d) (i : Fin d) : ℕ :=
  (Finset.univ.filter fun l => α l = i).card

/-- The multiplicities of a word add up to its length. -/
theorem sum_count {r : ℕ} (α : Fin r → Fin d) : ∑ i, count α i = r := by
  simp only [count]
  rw [← Finset.card_eq_sum_card_fiberwise (fun l _ => Finset.mem_univ (α l)), Finset.card_univ,
    Fintype.card_fin]

/-- The vector `∑_{j < i} h_j e_j`. -/
def lowerVec (h : Fin d → ℝ) (i : Fin d) : Fin d → ℝ := fun c => if c < i then h c else 0

/-- The shift `s_α = ∑_l ∑_{j < α_l} h_j e_j` of the term of a word `α`. -/
def shiftVec {r : ℕ} (h : Fin d → ℝ) (α : Fin r → Fin d) : Fin d → ℝ := ∑ l, lowerVec h (α l)

/-- The coordinates of the shift: `(s_α)_c = #{l : c < α_l} h_c`. -/
theorem shiftVec_apply {r : ℕ} (h : Fin d → ℝ) (α : Fin r → Fin d) (c : Fin d) :
    shiftVec h α c = (Finset.univ.filter fun l => c < α l).card * h c := by
  simp only [shiftVec, lowerVec, Finset.sum_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The shift and the multiplicity of a coordinate add up to at most the length of the word:
`#{l : c < α_l} + #{l : α_l = c} ≤ r`. -/
theorem card_lt_add_count_le {r : ℕ} (α : Fin r → Fin d) (c : Fin d) :
    (Finset.univ.filter fun l => c < α l).card + count α c ≤ r := by
  rw [count, ← Finset.card_union_of_disjoint]
  · calc _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_le_univ _
      _ = r := by rw [Finset.card_univ, Fintype.card_fin]
  · rw [Finset.disjoint_filter]
    intro l _ hl heq
    rw [heq] at hl
    exact lt_irrefl c hl

/-- The lower products: `∏_{j < i} δ_{h_j e_j} = δ_{∑_{j<i} h_j e_j}`. -/
theorem prod_lt_single (h : Fin d → ℝ) (i : Fin d) :
    ∏ j ∈ Finset.univ.filter (· < i), AddMonoidAlgebra.single (Pi.single j (h j)) (1 : ℂ) =
      AddMonoidAlgebra.single (lowerVec h i) 1 := by
  rw [← single_sum_one]
  congr 1
  funext c
  simp only [lowerVec, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp

/-- **The first-order telescoping**: `δ_h - 1 = ∑_i (δ_{h_i e_i} - 1) δ_{∑_{j<i} h_j e_j}`
(Mathlib's `Finset.prod_add_ordered` for `∏_i (1 + (δ_{h_i e_i} - 1))`). -/
theorem single_sub_one_eq_sum (h : Fin d → ℝ) :
    AddMonoidAlgebra.single h (1 : ℂ) - 1 =
      ∑ i, coordElem h i * AddMonoidAlgebra.single (lowerVec h i) 1 := by
  have hprod : AddMonoidAlgebra.single h (1 : ℂ) =
      ∏ i, (1 + coordElem h i) := by
    conv_lhs => rw [← Finset.univ_sum_single h]
    rw [single_sum_one]
    exact Finset.prod_congr rfl fun i _ => by rw [coordElem, add_sub_cancel]
  rw [hprod, Finset.prod_add_ordered]
  simp only [Finset.prod_const_one, mul_one, add_sub_cancel_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← prod_lt_single]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [coordElem, add_sub_cancel]

/-- **The expansion in the translation algebra**:
`(δ_h - 1)^r = ∑_α δ_{s_α} ∏_i (δ_{h_i e_i} - 1)^{m_i(α)}`, summed over the words
`α : Fin r → Fin d`. -/
theorem single_sub_one_pow_eq_sum (r : ℕ) (h : Fin d → ℝ) :
    (AddMonoidAlgebra.single h (1 : ℂ) - 1) ^ r = ∑ α : Fin r → Fin d,
      AddMonoidAlgebra.single (shiftVec h α) 1 * ∏ i, coordElem h i ^ count α i := by
  classical
  rw [single_sub_one_eq_sum, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.prod_mul_distrib, mul_comm]
  congr 1
  · rw [shiftVec, single_sum_one]
  · rw [← Finset.prod_fiberwise Finset.univ α fun l => coordElem h (α l)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.1 hl).2],
      Finset.prod_const, count]

end Coordinates

end TranslationAlgebra
