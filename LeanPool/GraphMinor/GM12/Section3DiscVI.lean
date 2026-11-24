/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DiscChordDivision
public import LeanPool.GraphMinor.GM12.Section3VIConnections
import LeanPool.GraphMinor.GM12.Section3DiscChainRedundancy
import LeanPool.GraphMinor.GM12.Section3DualPointSet
import LeanPool.GraphMinor.GM06.DualExists
import LeanPool.GraphMinor.GM06.Section2Dual

/-!
# Applying VI (3.6) after the normal-chord inequality

The final case of XII (3.2), pages 247--248, uses VI (3.6).
The boundary parts form a division. Choose a dual point in every
boundary segment. The minimum-arc chord bound gives the division
count bound, and the chain-carrier lemmas give nonnegative chain
redundancy. VI (3.6) then supplies a realization. Its components
are the desired connected subdrawings.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06

/-- The application of VI (3.6) in XII (3.2), pages 247--248,
after the cross-free and minimum-arc chord conditions are established. -/
theorem connecting_subdrawings_of_disc_chord_bound
    {S : Type*} [TopologicalSpace S] (G : Drawing S) (hDisc : IsClosedDiscSpace S)
    (hProper : G.IsProper) {p : ℕ} (Zs : Fin p → Set S)
    (hne : ∀ j, (Zs j).Nonempty) (hcover : (⋃ j, Zs j) = G.V ∩ bd S)
    (hdis : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hCF : GM06.IsCrossFree (bd S) (range Zs))
    (hmin : ∀ (x y : S) (A B P : Set S), IsLineWithEnds A x y → IsLineWithEnds B x y →
      IsLineWithEnds P x y → A ∩ B = {x, y} → A ∩ P = {x, y} → B ∩ P = {x, y} →
      bd S = A ∪ B → P ∩ bd S = {x, y} → G.IsNormal P →
        min (G.V ∩ A).ncard (G.V ∩ B).ncard ≤ (G.V ∩ P).ncard) :
    HasConnectingSubdrawings G (G.V ∩ bd S) Zs := by
  let : T2Space S := GM06.t2Space_of_isClosedDiscSpace hDisc
  have hΔ : IsDivision (range Zs) := by
    refine ⟨finite_range Zs, ?_, ?_⟩
    · rintro δ ⟨j, rfl⟩
      exact hne j
    · rintro δ ⟨i, rfl⟩ δ' ⟨j, rfl⟩ hij
      exact hdis i j (fun he => hij (congrArg Zs he))
  have hUnion : divisionUnion (range Zs) = G.V ∩ bd S := by
    rw [divisionUnion, Set.sUnion_range]
    exact hcover
  obtain ⟨U, hU⟩ := exists_dual_point_set (bd S) (divisionUnion (range Zs))
  have hUB : U ⊆ bd S := (GM06.isDualPointSet_subset_diff hU).trans sdiff_subset
  have hVB : divisionUnion (range Zs) ⊆ bd S := hUnion.subset.trans inter_subset_right
  have hchord : ∀ (x y : S), x ∈ bd S → y ∈ bd S → x ≠ y →
      ∀ P : Set S, IsLineWithEnds P x y → G.IsNormal P → P ∩ bd S = {x, y} →
        divisionCount (bd S) (range Zs) x y ≤ (G.V ∩ P).ncard := by
    intro x y hx hy hxy P hP hn hcap
    exact divisionCount_le_of_normal_chord_min_bound G hDisc hΔ hUnion hmin hx hy hxy P hP hcap hn
  have hfeas : GM06.IsFeasible G.toGraph (range Zs) := by
    apply (GM06.theorem_3_6_proof G (range Zs) U hDisc hProper hΔ hUnion hU).mpr
    refine ⟨hCF, ?_⟩
    intro x hx y hy A hA
    exact chainRedundancy_nonneg_of_normal_chord_bound hDisc hProper hΔ hUnion hchord
      (hx.elim (fun h => hUB h) (fun h => hVB h)) (hy.elim (fun h => hUB h) (fun h => hVB h)) hA
  have hconnect := hasConnectingSubdrawings_of_vi_feasible G Zs hne hdis hfeas
  rwa [hcover] at hconnect

end GraphMinor.GM12
