/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3PuncturedModel
import LeanPool.GraphMinor.Surface.NormalWord
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# The complexity condition for applying VII

The surface theorem used in XII (3.1), page 245, requires complexity
at least three. The excluded cases are a sphere with at most two holes.
We identify the model with no handles, cross-caps or holes directly
from its quotient definition. The hypothesis of XII (3.1) then gives
the required complexity bound.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- With no identifications or deletions, the model is the sphere.
The map sends the class of a point to that same point. -/
theorem isSphere_model_zero : IsSphere (SurfaceModel 0 0 0) := by
  have hr : ∀ x y : modelBase (2 * 0 + 0 + 0),
      ModelGlue 0 0 (2 * 0 + 0 + 0) x y → x.val = y.val := by
    intro x y h
    cases h <;> omega
  let f : SurfaceModel 0 0 0 → OnePoint EuclideanPlane := Quot.lift Subtype.val hr
  have hf : Continuous f := continuous_quot_lift hr continuous_subtype_val
  have hi : Function.Injective f := by
    intro x y
    refine Quot.inductionOn x ?_
    intro p
    refine Quot.inductionOn y ?_
    intro q hpq
    exact congrArg (Quot.mk _) (Subtype.ext hpq)
  have hs : Function.Surjective f := by
    intro x
    exact ⟨Quot.mk _ ⟨x, by simp [modelBase]⟩, rfl⟩
  let := (isSurface_model 0 0 0).1.1
  exact ⟨hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hi, hs⟩)⟩

/-- The sphere exception in XII (3.1) is exactly what ensures the
complexity required by VII for the punctured model. -/
theorem model_complexity_of_not_sphere_or_three_discs
    {S : Type*} [TopologicalSpace S] {a b t : ℕ}
    (e : S ≃ₜ SurfaceModel a b 0) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    3 ≤ 3 * a + 3 * b + t := by
  rcases hcase with hn | ht
  · by_contra h
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    obtain ⟨eM⟩ := isSphere_model_zero
    exact hn ⟨e.trans eM⟩
  · omega

/-- A connected closed surface has a model with no cuffs. -/
theorem exists_closed_surface_model
    {S : Type*} [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S) :
    ∃ a b : ℕ, Nonempty (S ≃ₜ SurfaceModel a b 0) := by
  have hsurf : IsSurface S :=
    ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification S hsurf inferInstance
  have hbd : bd S = ∅ := Set.eq_empty_iff_forall_notMem.mpr
    (fun x hx => hx (hS.2.2 x))
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  let := ht
  have hc : c = 0 := by
    calc
      c = (cuffs (SurfaceModel a b c)).ncard := (ncard_cuffs hf).symm
      _ = (cuffs S).ncard := (ncard_cuffs_congr e).symm
      _ = 0 := by simp [cuffs, hbd, componentsIn]
  exact ⟨a, b, ⟨hc ▸ e⟩⟩

/-- The parameters needed by VII in XII (3.1) depend only on the
original surface and the number of discs. This supplies both the model
and its complexity for every allowed placement of the discs. -/
theorem exists_uniform_discComplement_model
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t : ℕ) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    ∃ a b : ℕ, 3 ≤ 3 * a + 3 * b + t ∧
      ∀ Δ : Fin t → Set S, (∀ i, IsClosedDisc (Δ i)) →
        Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
        Nonempty (discComplement Δ ≃ₜ SurfaceModel a b t) := by
  obtain ⟨a, b, ⟨e⟩⟩ := exists_closed_surface_model hS
  refine ⟨a, b, model_complexity_of_not_sphere_or_three_discs e hcase, ?_⟩
  intro Δ hΔ hd
  exact Eq.mp (congrArg
    (fun n => Nonempty (discComplement Δ ≃ₜ SurfaceModel a b n)) (Nat.card_fin t))
    (discComplement_model_of_closed_model hS Δ hΔ hd e)

end GraphMinor.GM12
