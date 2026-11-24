/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
public import LeanPool.GraphMinor.GM07.ForestPeel
import LeanPool.GraphMinor.GM07.Section46ClosedComponents
import LeanPool.GraphMinor.GM07.Section46CuffComponents
import LeanPool.GraphMinor.GM07.Section46ComponentsMeetVertices
import LeanPool.GraphMinor.GM07.Section46Constants
import LeanPool.GraphMinor.GM07.Section2

/-!
# The upper cuff bound in VII (4.6)

On page 226, each component of `U(L) ∪ bd(Σ)` contains an old seam
vertex. Distinct components are disjoint, so their number is at most
`|V(J)|`. The cut-cuff correspondence and (2.4) then give
`c′ ≤ 2(2a+b+c-1)`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

private theorem ncard_components_le_meeting_set {S : Type*} [TopologicalSpace S]
    {B V : Set S} (hV : V.Finite)
    (hmeet : ∀ C ∈ componentsIn B, (C ∩ V).Nonempty) :
    (componentsIn B).ncard ≤ V.ncard := by
  classical
  have : Finite V := hV.to_subtype
  choose p hp using fun C : componentsIn B => hmeet C.1 C.2
  let f : componentsIn B → V := fun C => ⟨p C, (hp C).2⟩
  have hi : Function.Injective f := by
    intro C D heq
    apply Subtype.ext
    by_contra hne
    have hdis := disjoint_of_mem_componentsIn_ne C.2 D.2 hne
    have hpEq : p C = p D := congrArg Subtype.val heq
    have hpD : p C ∈ D.1 := by rw [hpEq]; exact (hp D).1
    exact disjoint_left.mp hdis (hp C).1 hpD
  exact Nat.card_le_card_of_injective f hi

/-- The cuffs of `Σ′` are counted by old seam vertices, in VII (4.6),
page 226. -/
theorem cut_cuffs_le_old_vertices {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
    (hS : IsSurface S) (N : Net S) {G J J' L : Drawing S}
    (hJ : N.IsSeamGraphFor J) {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    (hLE : L.E = forestSeamEdges J' (centralEdges G J μ w γ s t))
    (hLn : HasNoIsolatedVertices L) {θ : S' → S}
    (hcut : IsCutAlongGraph L S' θ) (hNo : NoArcs L) :
    (cuffs S').ncard ≤ J.V.ncard := by
  rw [ncard_cuffs_cut_eq_components hS hcut hNo]
  exact ncard_components_le_meeting_set J.finite_V
    (boundary_components_meet_old_vertices hS N hJ hγ s t W hcuts hU hV hLE hLn)

/-- The numerical upper cuff bound `c′ ≤ 2(2a+b+c-1)` in VII (4.6),
page 226. -/
theorem cut_model_cuff_bound_4_6 {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
    (hS : IsSurface S) (N : Net S) {G J J' L : Drawing S}
    (hG : G.IsProper) (hmin : N.IsMinimalFor G) (hJ : N.IsSeamGraphFor J)
    {a b c c' μ w : ℕ} (hc : 2 ≤ c) (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hmodel' : Nonempty (S' ≃ₜ SurfaceModel a b c'))
    {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    (s t : longSeamEdges G J μ w → unitInterval) (W : longSeamEdges G J μ w → Set S)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)})
    (hU : J'.U = J.U) (hV : J'.V = J.V ∪ ⋃ e, W e)
    (hLE : L.E = forestSeamEdges J' (centralEdges G J μ w γ s t))
    (hLn : HasNoIsolatedVertices L) {θ : S' → S}
    (hcut : IsCutAlongGraph L S' θ) (hNo : NoArcs L) :
    c' ≤ 2 * (2 * a + b + c - 1) := by
  have hbound := cut_cuffs_le_old_vertices hS N hJ hγ s t W hcuts hU hV hLE hLn hcut hNo
  have hv := (theorem_2_4_proof hS (by omega) hmodel hG hmin hJ).1
  rw [ncard_cuffs_eq_of_surface_model hmodel'.some] at hbound
  exact hbound.trans hv

end GraphMinor.GM07
