/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.ForestPeel
import LeanPool.GraphMinor.GM07.Section46RetainedCircles
import LeanPool.GraphMinor.GM07.Section46RetainedArcs

/-!
# The no-arc conclusion for `L` and its cut surface

VII (4.6), page 226, excludes circles and then boundary-to-boundary
arcs from `U(L)`. The forest cutting construction can therefore be
applied to `L`. It preserves the two genus parameters and adds cuffs,
giving the surface `Σ′` and its associated map `θ`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

/-- The no-`O`-arc and no-`I`-arc conclusion of VII (4.6), page 226. -/
theorem noArcs_L_of_contact_sum {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {G J J' L : Drawing S} (hJ : N.IsSeamGraphFor J) (hG : G.IsProper)
    (hnorm : G.IsNormal J.U) (hL : L.IsSubdrawing J') (hU : J'.U = J.U)
    (hLp : L.IsProper) {v : ℕ}
    (hsum : (G.V ∩ L.U).ncard + (G.V ∩ bd S).ncard ≤ v)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ v →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ v →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard) : NoArcs L :=
  ⟨fun _F hF => not_isOArc_of_subset_retained hS N hcuffs hJ hG hnorm hL hU hLp hsum hii hiii hF,
   fun _F hF => not_isIArc_of_subset_retained hS N hcuffs hJ hG hnorm hL hU hLp hsum hi hii hiii hF⟩

/-- Cutting along the graph `L` of VII (4.6), page 226, after the no-arc
argument: the genus parameters are unchanged and the cuff count increases. -/
theorem exists_cut_L_4_6 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) {a b c : ℕ} (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {G J J' L : Drawing S} (hJ : N.IsSeamGraphFor J) (hG : G.IsProper)
    (hnorm : G.IsNormal J.U) (hL : L.IsSubdrawing J') (hU : J'.U = J.U)
    (hLp : L.IsProper) (hLn : HasNoIsolatedVertices L) {v : ℕ}
    (hsum : (G.V ∩ L.U).ncard + (G.V ∩ bd S).ncard ≤ v)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ v →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ v →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard) :
    ∃ (S' : Type u) (_ : TopologicalSpace S') (θ : S' → S) (c' : ℕ),
      IsCutAlongGraph L S' θ ∧ c ≤ c' ∧ Nonempty (S' ≃ₜ SurfaceModel a b c') := by
  have hN := noArcs_L_of_contact_sum hS N hcuffs hJ hG hnorm hL hU hLp hsum hi hii hiii
  obtain ⟨S', top, θ, k, hcut, hmodel', _⟩ := exists_isCutAlongGraph hS hmodel hLp hLn hN
  exact ⟨S', top, θ, c + k, hcut, Nat.le_add_right _ _, hmodel'⟩

end GraphMinor.GM07
