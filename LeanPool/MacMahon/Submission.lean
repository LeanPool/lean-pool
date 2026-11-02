/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.MacMahon.Theorems

/-!
# Physical classification and geometric coverage
-/

@[expose] public section
namespace MacMahon

/-- The multiplicity conclusion expressed using physical face matching. -/
theorem physical_minimum_has_no_repeats (a : Inventory) (hz : DiagonalZero a)
    (ht : total a = 12) (h : PhysicalUniversal a) : ∀ p, a p ≤ 1 :=
  minimum_has_no_repeats a hz ht ((universal_iff_physical a).mpr h)

/-- Every assignment of six distinct nonzero colours is represented by the tableau. -/
theorem face_assignment_coverage (f : Fin 6 → Fin 7) (hi : Function.Injective f)
    (hn : ∀ d, f d ≠ 0) :
    ∃ i j : Label, i ≠ j ∧ ∃ r : Fin 24,
      ∀ d : Fin 6, f d = faceColours i j (rotations r d) := by
  let g : Fin 6 → NonzeroColour := fun d => ⟨f d, hn d⟩
  have hg : Function.Injective g := by
    intro d e h
    exact hi (congrArg Subtype.val h)
  let e : Colouring := Equiv.ofBijective g
    ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, Fintype.card_congr colourEquiv⟩)
  obtain ⟨⟨⟨⟨i, j⟩, hij⟩, r⟩, he⟩ := all_colourings.2 e
  refine ⟨i, j, hij, r, ?_⟩
  intro d
  exact (congrArg (fun x : Colouring => (x d).val) he).symm

/-- The variety and rotation representing a face assignment are unique. -/
theorem face_assignment_unique (i j : Label) (hij : i ≠ j)
    (u v : Label) (huv : u ≠ v) (r s : Fin 24)
    (hf : ∀ d : Fin 6, faceColours i j (rotations r d) = faceColours u v (rotations s d)) :
    i = u ∧ j = v ∧ r = s := by
  have he : orientedColouring (⟨(i, j), hij⟩, r) = orientedColouring (⟨(u, v), huv⟩, s) := by
    ext d
    exact congrArg Fin.val (hf d)
  have hp := orientedColouring_injective he
  have hq := congrArg (fun x : Variety × Fin 24 => x.1.val) hp
  exact ⟨congrArg Prod.fst hq, congrArg Prod.snd hq, congrArg Prod.snd hp⟩

end MacMahon
