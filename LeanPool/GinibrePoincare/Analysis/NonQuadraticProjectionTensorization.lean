/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticProjectionTensorization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Sharp successive orthogonal-projection estimates
These Hilbert lemmas give the factor-one tensorization step. Concrete
coordinate projections must still be constructed for the particle law. -/

@[expose] public section
open scoped InnerProductSpace
namespace GinibrePoincare
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Applying one more orthogonal projection costs at most its own squared
projection error, with no dimensional factor. -/
theorem orthogonalProjection_composition_error (K : ClosedSubmodule ℝ H)
    (B : H →L[ℝ] H) (x : H) :
    ‖x - K.starProjection (B x)‖ ^ 2 ≤
      ‖x - K.starProjection x‖ ^ 2 + ‖x - B x‖ ^ 2 := by
  have horth : ⟪x - K.starProjection x, K.starProjection (x - B x)⟫_ℝ = 0 :=
    Submodule.starProjection_inner_eq_zero x _
      (Submodule.starProjection_apply_mem K.toSubmodule _)
  have he : x - K.starProjection (B x) =
      (x - K.starProjection x) + K.starProjection (x - B x) := by
    rw [map_sub]
    abel
  have hn : ‖(x - K.starProjection x) + K.starProjection (x - B x)‖ ^ 2 =
      ‖x - K.starProjection x‖ ^ 2 + ‖K.starProjection (x - B x)‖ ^ 2 := by
    simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [he, hn]
  exact add_le_add (le_refl _) ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (Submodule.norm_starProjection_apply_le K.toSubmodule _))

/-- Successive concrete orthogonal projections. -/
def successiveOrthogonalProjections (Ks : List (ClosedSubmodule ℝ H)) : H →L[ℝ] H :=
  Ks.foldr (fun K B => K.starProjection.comp B) (ContinuousLinearMap.id ℝ H)

/-- Sharp finite projection tensorization without a dimension loss. -/
theorem successiveOrthogonalProjections_error
    (Ks : List (ClosedSubmodule ℝ H)) (x : H) :
    ‖x - successiveOrthogonalProjections Ks x‖ ^ 2 ≤
      (Ks.map (fun K => ‖x - K.starProjection x‖ ^ 2)).sum := by
  induction Ks with
  | nil => simp [successiveOrthogonalProjections]
  | cons K Ks ih =>
    change ‖x - K.starProjection (successiveOrthogonalProjections Ks x)‖ ^ 2 ≤ _
    simpa only [List.map_cons, List.sum_cons] using
      (orthogonalProjection_composition_error K (successiveOrthogonalProjections Ks) x).trans
        (add_le_add (le_refl _) ih)

/-- A projection commuting with a fixed orthogonal projection preserves
its actual closed subspace. -/
theorem commutingOrthogonalProjection_preserves (K L : ClosedSubmodule ℝ H)
    (hcomm : Function.Commute K.starProjection L.starProjection) (x : H) (hx : x ∈ K) :
    L.starProjection x ∈ K := by
  apply Submodule.starProjection_eq_self_iff.mp
  rw [hcomm x, Submodule.starProjection_eq_self_iff.mpr hx]

/-- Successive commuting coordinate projections land in every concrete
coordinate kernel, hence in their intersection. -/
theorem successiveOrthogonalProjections_mem_intersection
    (Ks : List (ClosedSubmodule ℝ H)) (x : H) :
    (∀ K ∈ Ks, ∀ L ∈ Ks, Function.Commute K.starProjection L.starProjection) →
      ∀ K ∈ Ks, successiveOrthogonalProjections Ks x ∈ K := by
  induction Ks with
  | nil => simp
  | cons L Ks ih =>
    intro hc K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact Submodule.starProjection_apply_mem K.toSubmodule _
    · have hct : ∀ K ∈ Ks, ∀ L ∈ Ks, Function.Commute K.starProjection L.starProjection := by
        intro K hK L hL
        exact hc K (List.mem_cons_of_mem _ hK) L (List.mem_cons_of_mem _ hL)
      have hi := ih hct K hK
      exact commutingOrthogonalProjection_preserves K L
        (hc K (List.mem_cons_of_mem _ hK) L (List.mem_cons_self ..)) _ hi

end
end GinibrePoincare
