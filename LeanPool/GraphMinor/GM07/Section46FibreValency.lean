/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.MinimalNet
import LeanPool.GraphMinor.GM07.Section46Fibres
import LeanPool.GraphMinor.GM07.Section46InteriorIncidences
import LeanPool.GraphMinor.GM07.Section46Valency
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The boundary fibre bound in VII (4.6)

The pasted endpoint pairs join the preimages of a seam vertex. Each pair
contributes an interior seam incidence, and the cuff contributes two more.
Thus the fibre has at most the valency minus one points. The valency bound
from (2.4) then gives the denominator used to choose `l(z)`, on page 225.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

private theorem endpoint_pair_card {S : Type u} [TopologicalSpace S]
    (N : Net S) (v : S) :
    Nat.card {p : Fin N.r × Bool //
      N.φ (N.f p.1 (if p.2 then 1 else 0)) = v} =
      (N.F₁ v).card + 2 * (N.F₂ v).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  have hlocal : ∀ i : Fin N.r,
      (∑ b : Bool, if N.φ (N.f i (if b then 1 else 0)) = v then 1 else 0) =
      (if i ∈ N.F₁ v then 1 else 0) + 2 * (if i ∈ N.F₂ v then 1 else 0) := by
    intro i
    rw [Fintype.sum_bool]
    by_cases h0 : N.φ (N.f i 0) = v <;>
      by_cases h1 : N.φ (N.f i 1) = v <;>
      simp [Net.mem_F₁_iff, Net.mem_F₂_iff, h0, h1]
  simp_rw [hlocal]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

/-- The boundary fibre estimate in VII (4.6), page 225, before applying
(2.4). The two cuff incidences are included in `vertexValency`. -/
theorem Net.fibre_ncard_add_one_le_valency {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) {z : S} (hz : z ∈ J.V) (hzbd : z ∈ bd S) :
    (N.φ ⁻¹' {z}).ncard + 1 ≤ vertexValency J z := by
  have hf := N.fibre_card_le_endpoint_pairs (hJ.2.2 ▸ hz)
  rw [endpoint_pair_card] at hf
  have hd := N.interior_valency_add_two_le hS hJ hz hzbd
  omega

/-- A boundary point outside the seam vertex set has a singleton fibre,
as used in VII (4.6), page 225. -/
theorem Net.fibre_ncard_eq_one_of_notMem_seamV {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {z : S}
    (hzbd : z ∈ bd S) (hzV : z ∉ N.seamV) :
    (N.φ ⁻¹' {z}).ncard = 1 := by
  have : T2Space S := hS.2.1
  have hf : ∀ i t, N.φ (N.f i t) ≠ z := by
    intro i t heq
    rcases unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · exact hzV ⟨i, .inl heq⟩
    · exact hzV ⟨i, .inr heq⟩
    · exact N.notMem_bd_of_mem_Ioo hS i ht (heq ▸ hzbd)
  obtain ⟨x, hx⟩ := N.quotientMap_φ.surjective z
  have hs : N.φ ⁻¹' {z} = {x} := by
    apply Subset.antisymm
    · intro y hy
      have hclosed : ∀ i t, N.f i t ∈ ({x} : Set N.D) ↔ N.g i t ∈ ({x} : Set N.D) := by
        intro i t
        have hfx : N.f i t ≠ x := fun h => hf i t ((congrArg N.φ h).trans hx)
        have hgx : N.g i t ≠ x := fun h =>
          hf i t ((N.pasting_eq i t).trans ((congrArg N.φ h).trans hx))
        simp [hfx, hgx]
      exact N.mem_of_eq hclosed (hx.trans hy.symm) (mem_singleton x)
    · exact singleton_subset_iff.mpr hx
  rw [hs, ncard_singleton]

/-- The uniform boundary fibre bound on page 225 of VII (4.6), obtained
from (2.4). This includes boundary points outside the seam vertex set. -/
theorem Net.boundary_fibre_ncard_bound_4_6 {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {a b c : ℕ}
    (habc : 1 < 2 * a + b + c) (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    {G J : Drawing S} (hG : G.IsProper) (hmin : N.IsMinimalFor G)
    (hJ : N.IsSeamGraphFor J) {z : S} (hzbd : z ∈ bd S) :
    (N.φ ⁻¹' {z}).ncard ≤ 6 * (2 * a + b + c - 1) := by
  by_cases hzV : z ∈ J.V
  · have hf := N.fibre_ncard_add_one_le_valency hS hJ hzV hzbd
    have hd := seam_vertexValency_bound_4_6 hS habc hmodel hG hmin hJ hzV
    omega
  · have hz : z ∉ N.seamV := fun h => hzV (hJ.2.2 ▸ h)
    rw [N.fibre_ncard_eq_one_of_notMem_seamV hS hzbd hz]
    omega

end GraphMinor.GM07
