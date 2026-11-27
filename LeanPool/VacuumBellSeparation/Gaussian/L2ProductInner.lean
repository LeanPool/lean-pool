/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.L2ProductTotality

/-!
# Inner products and bounded bilinear extension from total families

These use actual absolutely convergent ℓ² inner-product series. Equality
of bounded bilinear maps follows from equality on two total families by
two closed-subspace arguments.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped lp

open scoped ComplexConjugate

theorem inner_l2ProductVector {ι κ η : Type*} (e : κ ≃ ι × η)
    (x x' : ℓ²(ι, ℂ)) (y y' : ℓ²(η, ℂ)) :
    inner ℂ (l2ProductVector e x y) (l2ProductVector e x' y') =
      inner ℂ x x' * inner ℂ y y' := by
  have hx : HasSum (fun i : ι => inner ℂ (x i) (x' i)) (inner ℂ x x') :=
    lp.hasSum_inner (𝕜 := ℂ) x x'
  have hy : HasSum (fun j : η => inner ℂ (y j) (y' j)) (inner ℂ y y') :=
    lp.hasSum_inner (𝕜 := ℂ) y y'
  have hxn : Summable (fun i : ι => ‖inner ℂ (x i) (x' i)‖) := hx.summable.norm
  have hyn : Summable (fun j : η => ‖inner ℂ (y j) (y' j)‖) := hy.summable.norm
  have hp : HasSum (fun k : ι × η =>
      inner ℂ (x k.1) (x' k.1) * inner ℂ (y k.2) (y' k.2))
      (inner ℂ x x' * inner ℂ y y') := by
    have hsum := (summable_mul_of_summable_norm (R := ℂ) hxn hyn).hasSum
    have heq := tsum_mul_tsum_of_summable_norm (R := ℂ) hxn hyn
    rw [hx.tsum_eq, hy.tsum_eq] at heq
    exact heq.symm ▸ hsum
  have hp' := e.hasSum_iff.mpr hp
  have hactual := lp.hasSum_inner (𝕜 := ℂ) (l2ProductVector e x y) (l2ProductVector e x' y')
  apply hactual.unique
  convert hp' using 1
  funext k
  simp only [Function.comp_def, l2ProductVector_apply, RCLike.inner_apply', map_mul]
  ring

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem continuousLinearMap_eq_of_dense_span {α : Type*} (f : α → E)
    (hf : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤)
    (L M : E →L[ℂ] F) (h : ∀ a, L (f a) = M (f a)) : L = M := by
  have hz := continuousLinearMap_mem_of_dense_span f hf (⊥ : Submodule ℂ F)
    (by
      have hbot : ((⊥ : Submodule ℂ F) : Set F) = {0} := by
        ext x
        exact Submodule.mem_bot ℂ
      rw [hbot]
      exact isClosed_singleton)
    (L - M) (fun a => by simpa only [sub_apply,
      Submodule.mem_bot, sub_eq_zero] using h a)
  ext x
  exact sub_eq_zero.mp (show L x - M x = 0 from hz x)

theorem continuousBilinear_eq_of_dense_spans {α β : Type*} (f : α → E) (g : β → F)
    (hf : (Submodule.span ℂ (Set.range f)).topologicalClosure = ⊤)
    (hg : (Submodule.span ℂ (Set.range g)).topologicalClosure = ⊤)
    (L M : E →L[ℂ] F →L[ℂ] G) (h : ∀ a b, L (f a) (g b) = M (f a) (g b)) : L = M := by
  apply continuousLinearMap_eq_of_dense_span f hf
  intro a
  exact continuousLinearMap_eq_of_dense_span g hg (L (f a)) (M (f a)) (h a)

end VacuumBellSeparation.Gaussian
