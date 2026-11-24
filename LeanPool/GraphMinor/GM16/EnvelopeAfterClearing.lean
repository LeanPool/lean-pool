/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9ZonePreservation
import LeanPool.GraphMinor.GM16.Section9Dials
import LeanPool.GraphMinor.GM11.Section810

/-!
# The remaining envelope after one clearing

Other centres and zones survive clearing a disjoint member of the
envelope. Clearing any further subfamily gives the same drawing as
clearing its union with the first member, so rigidity also survives.
This is the envelope induction used for the horns in XVI (7.1),
Claim (4), page 69.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Clearing one member leaves an envelope on all the other centres. -/
theorem envelope_after_clearing {H : Drawing S}
    {T T₁ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d₁ : Set S → Set S → ℕ} {θ γ : ℕ} {Y : Set S} {Λ : S → Set S} {j : S}
    (hj : j ∉ Y) (hEnv : IsEnvelope H d (insert j Y) γ Λ)
    (hClear : IsClearedTangle H T d θ γ (Λ j) T₁ d₁) :
    IsEnvelope (clearedSubdrawing H (Λ j)) d₁ Y γ Λ := by
  have hZone := hEnv.2.1
  have hDis := hEnv.2.2.1
  have hY : Y ⊆ (clearedSubdrawing H (Λ j)).V := by
    intro y hy
    have hyj : y ≠ j := fun h => hj (h ▸ hy)
    exact (mem_interSet_V_iff (isClosed_univ.sdiff (hZone j (mem_insert j Y)).isOpenDisc.1)).mpr
      ⟨hEnv.1 (mem_insert_of_mem _ hy), mem_univ _, fun hyΛ =>
        (hDis y (mem_insert_of_mem _ hy) j (mem_insert _ _) hyj).notMem_of_mem_left
          (subset_closure ((hZone y (mem_insert_of_mem _ hy)).z_subset (mem_singleton y)))
            (subset_closure hyΛ)⟩
  refine ⟨hY, ?_, ?_, ?_⟩
  · intro y hy
    exact zone_after_disjoint_clearing (hEnv.1 (mem_insert_of_mem _ hy))
      (hZone y (mem_insert_of_mem _ hy)) (hZone j (mem_insert _ _))
      (hDis y (mem_insert_of_mem _ hy) j (mem_insert _ _) (fun h => hj (h ▸ hy))) hClear
  · exact fun y hy z hz => hDis y (mem_insert_of_mem _ hy) z (mem_insert_of_mem _ hz)
  · intro Y' hY'
    change IsRigid (clearEnvelopeDrawing (clearedSubdrawing H (Λ j)) Y' Λ)
    rw [clearFamily_after_single H Y' Λ j (fun y hy =>
      (hZone y ((insert_subset_insert hY') hy)).isOpenDisc.1)]
    exact hEnv.2.2.2 (insert j Y') (insert_subset_insert hY')

end GraphMinor.GM16
