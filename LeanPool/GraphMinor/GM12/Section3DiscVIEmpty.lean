/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DiscVI
public import LeanPool.GraphMinor.GM12.Section3EmptyClasses
import Mathlib.Data.Fintype.EquivFin
import LeanPool.GraphMinor.GM06.RegionLocal

/-!
# Empty parts in the disc application of VI (3.6)

The partition interface for XII (3.2), page 247, permits empty
parts. Apply the proved VI reduction to its nonempty parts. Their
union, disjointness, and cross-free property are preserved. Restore
the empty parts with empty subdrawings.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06

/-- The VI (3.6) application in XII (3.2), allowing empty partition
parts in the connected-subdrawing interface. -/
theorem connecting_subdrawings_of_disc_chord_bound_allowing_empty
    {S : Type*} [TopologicalSpace S] (G : Drawing S) (hDisc : IsClosedDiscSpace S)
    (hProper : G.IsProper) {p : ℕ} (Zs : Fin p → Set S)
    (hcover : (⋃ j, Zs j) = G.V ∩ bd S)
    (hdis : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j))
    (hCF : GM06.IsCrossFree (bd S) (range Zs))
    (hmin : ∀ (x y : S) (A B P : Set S), IsLineWithEnds A x y → IsLineWithEnds B x y →
      IsLineWithEnds P x y → A ∩ B = {x, y} → A ∩ P = {x, y} → B ∩ P = {x, y} →
      bd S = A ∪ B → P ∩ bd S = {x, y} → G.IsNormal P →
        min (G.V ∩ A).ncard (G.V ∩ B).ncard ≤ (G.V ∩ P).ncard) :
    HasConnectingSubdrawings G (G.V ∩ bd S) Zs := by
  classical
  let : T2Space S := GM06.t2Space_of_isClosedDiscSpace hDisc
  let I := {j : Fin p // (Zs j).Nonempty}
  let := Fintype.ofFinite I
  let q := Fintype.card I
  let e : I ≃ Fin q := Fintype.equivFin I
  let f : Fin q → Fin p := fun j => (e.symm j).val
  have hf : Function.Injective f := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hcover' : (⋃ j, Zs (f j)) = G.V ∩ bd S := by
    rw [← hcover]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨f j, hj⟩
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      let k : I := ⟨j, x, hj⟩
      refine mem_iUnion.mpr ⟨e k, ?_⟩
      simpa only [f, e.symm_apply_apply] using hj
  have hCF' : GM06.IsCrossFree (bd S) (range (fun j => Zs (f j))) := by
    rintro ⟨δ, ⟨i, hi⟩, δ', ⟨j, hj⟩, hne, a, ha, c, hc, b, hb, d, hd, hcross⟩
    exact hCF ⟨δ, ⟨f i, hi⟩, δ', ⟨f j, hj⟩, hne, a, ha, c, hc, b, hb, d, hd, hcross⟩
  apply hasConnectingSubdrawings_of_nonempty_restriction e
  exact connecting_subdrawings_of_disc_chord_bound G hDisc hProper (fun j => Zs (f j))
    (fun j => (e.symm j).property) hcover'
    (fun i j hij => hdis (f i) (f j) (fun he => hij (hf he))) hCF' hmin

end GraphMinor.GM12
