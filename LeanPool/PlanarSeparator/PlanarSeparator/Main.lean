/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Spec
public import LeanPool.PlanarSeparator.PlanarSeparator.Square
public import LeanPool.PlanarSeparator.NestedDissection.Main
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Encode

/-!
# The targets of `PlanarSeparator/Spec.lean`

The targets are stated in `PlanarSeparator/Spec.lean`; this file proves them from the library.

* `PlanarSeparator.separator_theorem` (`SeparatorTheorem`): `PlanarSeparator.planar_separator`.
* `PlanarSeparator.separator_theorem_induced` (`SeparatorTheoremInduced`):
  `PlanarSeparator.planar_separator_induce`.
* `PlanarSeparator.sepTree_exists` (`SepTreeExists`): `PlanarSeparator.exists_sepTree`.
* `PlanarSeparator.square_sepTree_exists` (`SquareSepTreeExists`):
  `PlanarSeparator.exists_sepTree_square`.
* `PlanarSeparator.fill_bound` (`FillBound`): `NestedDissection.card_edgeFinset_fill_le`.
* `PlanarSeparator.planar_nested_dissection` (`PlanarNestedDissection`) and
  `PlanarSeparator.square_nested_dissection` (`SquareNestedDissection`): the separator trees above
  with `NestedDissection.card_edgeFinset_fill_le` and
  `NestedDissection.nestedDissection_elimination`, in the order `NestedDissection.SepTree.ndPerm`.
* `PlanarSeparator.separator_machine` (`SeparatorMachine`): the program
  `compile SepProg.sepProg 0 ++ [halt]` and `PlanarSeparator.SepProg.sepProg_sepOut`, through
  `PlanarSeparator.SepProg.separatorMachine_holds`.
-/

@[expose] public section

namespace PlanarSeparator

open Finset NestedDissection NestedDissection.SepTree

universe u

/-- **The planar separator theorem.** -/
theorem separator_theorem : SeparatorTheorem.{u} := by
  intro V _ _ G _ R hR w hw h1
  exact planar_separator hR hw h1

/-- **The planar separator theorem for induced subgraphs.** -/
theorem separator_theorem_induced : SeparatorTheoremInduced.{u} := by
  intro V _ _ G _ R hR U w hw h1
  exact planar_separator_induce hR U hw h1

/-- **Separator trees of plane graphs.** -/
theorem sepTree_exists : SepTreeExists.{u} := by
  intro V _ _ G _ R hR
  exact exists_sepTree hR

/-- **Separator trees of squares of plane graphs of bounded degree.** -/
theorem square_sepTree_exists : SquareSepTreeExists.{u} := by
  intro V _ _ G _ R hR Δ hΔ
  exact exists_sepTree_square hR hΔ

/-- **The fill of nested dissection.** -/
theorem fill_bound : FillBound := by
  intro n G _ α β hα hβ t hd hv hsq hs _
  exact card_edgeFinset_fill_le hα hβ t hd hv hsq hs

/-- The nested dissection order of `t` lists the vertices `ndPerm t hd hv 0, 1, …`. -/
theorem order_getElem?_ndPerm {n : ℕ} {G : SimpleGraph (Fin n)} {t : SepTree (Fin n)}
    (hd : IsDissection G t) (hv : t.verts = univ) (k : Fin n) :
    t.order[k.val]? = some (ndPerm t hd hv k) := by
  have hk : k.val < t.order.length := by
    have := ndPerm_symm_apply t hd hv ((ndPerm t hd hv) k)
    rw [Equiv.symm_apply_apply] at this
    rw [this]
    exact List.idxOf_lt_length_of_mem (mem_order.mpr (hv ▸ mem_univ _))
  rw [List.getElem?_eq_getElem hk]
  rfl

/-- Nested dissection along a separator tree with the bounds `T √m`: the fill and the
elimination, for the graph `G` (a plane graph, or the square of one). -/
theorem nested_dissection_of_sepTree {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : ℝ} (hT : 0 ≤ T) {t : SepTree (Fin n)} (hv : t.verts = univ) (hd : IsDissection G t)
    (hsq : AllNodes (SqrtBound G T T) t) (hs : AllNodes Shrinks t) :
    ∃ (t : SepTree (Fin n)) (σ : Equiv.Perm (Fin n)), t.verts = univ ∧ IsDissection G t ∧
      (∀ k : Fin n, t.order[k.val]? = some (σ k)) ∧
      (∀ [DecidableRel (fill G fun x => t.order.idxOf x).Adj],
        ((fill G fun x => t.order.idxOf x).edgeFinset.card : ℝ) ≤
          T * (T + T) * (n * (1 + Real.logb (3 / 2) n))) ∧
      ∀ (K : Type u) [Field K] (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H = fill (G.comap σ) Fin.val →
        ∀ A : Matrix (Fin n) (Fin n) K, (∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) →
          (sparseCounted H (A.submatrix σ σ) n).val = stage (A.submatrix σ σ) n ∧
            ((sparseCounted H (A.submatrix σ σ) n).cost.total : ℝ) ≤
              12 * T * (T + T) ^ 2 * (n * √n) :=
  ⟨t, ndPerm t hd hv, hv, hd, order_getElem?_ndPerm hd hv,
    fun {_} => card_edgeFinset_fill_le hT hT t hd hv hsq hs,
    fun _ _ H _ hH A hA => nestedDissection_elimination hT t hd hv hsq hs H hH A hA⟩

/-- **Nested dissection of plane graphs.** -/
theorem planar_nested_dissection : PlanarNestedDissection.{u} := by
  intro n G _ R hR
  obtain ⟨t, hv, hd, hsq, hs⟩ := exists_sepTree (G := G) hR
  exact nested_dissection_of_sepTree (by norm_num) hv hd hsq hs

/-- **Nested dissection for squares of plane graphs of bounded degree.** -/
theorem square_nested_dissection : SquareNestedDissection.{u} := by
  intro n G _ R hR Δ hΔ
  obtain ⟨t, hv, hd, hsq, hs⟩ := exists_sepTree_square hR hΔ
  exact nested_dissection_of_sepTree (by positivity) hv hd hsq hs

/-- **The planar separator theorem on the machine in linear time.** -/
theorem separator_machine : SeparatorMachine := SepProg.separatorMachine_holds

end PlanarSeparator

end
