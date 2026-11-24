/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.MinimalNet
import LeanPool.GraphMinor.GM07.Section46Constants
import LeanPool.GraphMinor.GM07.Section46FibreValency
import LeanPool.GraphMinor.GM07.Section46FirstEdge
import Mathlib.Combinatorics.Pigeonhole

/-!
# Choosing the lift `l(z)` in VII (4.6)

On page 225, assign each indexed path to the unique lifted incidence of
its first edge. The fibre bound and the definition of `v` ensure that at
least `μ` paths have the same incidence. The count uses indexed paths,
so it also applies when a one-edge path occurs more than once.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

/-- The choice of `l(z)` in VII (4.6), page 225, for the paths obtained
in the first step of the proof. At least `μ` lifted first edges are incident
with the chosen point over `z`. -/
theorem Net.exists_common_lifted_first_edge {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {a b c k : ℕ}
    (hc : 2 ≤ c) (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    {G J : Drawing S} (hG : G.IsProper) (hmin : N.IsMinimalFor G)
    (hJ : N.IsSeamGraphFor J) (hnorm : G.IsNormal J.U)
    {z : S} (hzbd : z ∈ bd S)
    (P : Fin (vModel a b c k - 2 * k) → Drawing S)
    (t : Fin (vModel a b c k - 2 * k) → S)
    (hP : ∀ i, (P i).IsSubdrawing G ∧ z ≠ t i ∧ (P i).IsPathBetween z (t i)) :
    ∃ l : N.D, N.φ l = z ∧
      ∃ I : Finset (Fin (vModel a b c k - 2 * k)), muModel a b c k ≤ I.card ∧
        ∀ i ∈ I, ∃ e ∈ (P i).E, l ∈ closure (N.φ ⁻¹' e) ∧
          ∀ x ∈ closure (N.φ ⁻¹' e), N.φ x = z → x = l := by
  classical
  have hfirst := fun i =>
    N.exists_lifted_first_edge hS hJ hnorm (hP i).1 (hP i).2.1 (hP i).2.2
  choose e he l hl hle hu using hfirst
  let X := N.φ ⁻¹' {z}
  have : Finite X := (N.finite_fiber z).to_subtype
  let : Fintype X := Fintype.ofFinite X
  have : Nonempty X := by
    obtain ⟨x, hx⟩ := N.quotientMap_φ.surjective z
    exact ⟨⟨x, hx⟩⟩
  let f : Fin (vModel a b c k - 2 * k) → X := fun i => ⟨l i, hl i⟩
  have hbound := N.boundary_fibre_ncard_bound_4_6 hS (by omega) hmodel hG hmin hJ hzbd
  have hmul : Fintype.card X * muModel a b c k ≤
      Fintype.card (Fin (vModel a b c k - 2 * k)) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Fintype.card_fin]
    exact (Nat.mul_le_mul_right _ hbound).trans (constants_bounds_4_6 hc).2.2
  obtain ⟨l₀, hcount⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f hmul
  refine ⟨l₀, l₀.2, Finset.univ.filter (fun i => f i = l₀), hcount, ?_⟩
  intro i hi
  have hi' : f i = l₀ := (Finset.mem_filter.mp hi).2
  have hil : l i = l₀.1 := congrArg Subtype.val hi'
  refine ⟨e i, he i, hil ▸ hle i, ?_⟩
  intro x hx hxz
  exact (hu i x hx hxz).trans hil

end GraphMinor.GM07
