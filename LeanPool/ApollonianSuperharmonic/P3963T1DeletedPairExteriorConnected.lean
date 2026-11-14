/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.P3350T1GraphCellUnionConnected

-- [TABLET NODE: P3963T1DeletedPairExteriorConnected]

/-!
# P3963T1DeletedPairExteriorConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3963T1DeletedPairExteriorConnected {ι : Type}
    (P : PeriodicTileComplex ι) (a b : ι) :
    FourNeighborConnected
      ((↑((P.tile a).cells ∪ (P.tile b).cells) : Set LatticeCell)ᶜ) := by
-- BODY
  classical
  have hindexed := PeriodicTileIndexedMultiplicityOne P
  let D : Finset ι := {a, b}
  have hcard : D.card < 3 := by
    have h := Finset.card_insert_le a ({b} : Finset ι)
    simp only [Finset.card_singleton] at h
    dsimp [D]
    omega
  have hunion : {x : LatticeCell | ∃ c ∈ (D : Set ι)ᶜ,
      x ∈ (P.tile c).cells} =
      ((↑((P.tile a).cells ∪ (P.tile b).cells) : Set LatticeCell)ᶜ) := by
    ext x
    constructor
    · rintro ⟨c, hc, hxc⟩ hx
      have hcab : c ≠ a ∧ c ≠ b := by simpa [D] using hc
      simp only [Finset.mem_coe, Finset.mem_union] at hx
      rcases hx with hxa | hxb
      · exact hcab.1 ((hindexed x).unique hxc hxa)
      · exact hcab.2 ((hindexed x).unique hxc hxb)
    · intro hx
      obtain ⟨c, hxc, _⟩ := hindexed x
      refine ⟨c, ?_, hxc⟩
      have hca : c ≠ a := by
        intro heq
        exact hx (by simp [← heq, hxc])
      have hcb : c ≠ b := by
        intro heq
        exact hx (by simp [← heq, hxc])
      simpa [D] using And.intro hca hcb
  have hnonempty : ((D : Set ι)ᶜ).Nonempty := by
    let : Infinite LatticeCell := by
      apply Infinite.of_injective (fun n : Nat => (n : GaussianInt))
      intro m n h
      have hh := congrArg Zsqrtd.re h
      norm_num at hh ⊢
      omega
    obtain ⟨x, hx⟩ := ((P.tile a).cells ∪ (P.tile b).cells).exists_notMem
    have hx' : x ∈ ((↑((P.tile a).cells ∪ (P.tile b).cells) :
        Set LatticeCell)ᶜ) := hx
    rw [← hunion] at hx'
    obtain ⟨c, hc, _⟩ := hx'
    exact ⟨c, hc⟩
  rw [← hunion]
  exact P3350T1GraphCellUnionConnected P.plane.adjacent
    P.plane.adjacent_irreflexive P.tile (D : Set ι)ᶜ hnonempty
    (fun c _ => (LatticeTileGridStructure _ (P.tiles_are_disks c)).1)
    (by
      intro c _ d _ hcd
      exact Finset.disjoint_left.mpr
        (fun x hxc hxd => hcd ((hindexed x).unique hxc hxd)))
    (fun c _ d _ _ hcd => P.adjacent_has_common_edge c d hcd)
    (P.plane.three_connected D hcard)

end ApollonianSuperharmonic

end
