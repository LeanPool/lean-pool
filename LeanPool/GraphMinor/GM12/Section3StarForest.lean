/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# A star has no circuits

The topological feasibility discs in XII (3.1), page 245, can carry
stars connecting their prescribed boundary vertices. Each edge joins
the centre to a leaf, and a leaf has only one incident edge. A closed
simple walk would either repeat that edge immediately or revisit the
centre. This proves the forest part of the construction.
-/

public section

namespace GraphMinor.GM12

open Surface GM11

/-- A loopless graph whose edges join one centre to leaves, each with
at most one incident edge, is a forest. This is the combinatorial
part of the star construction in XII (3.1), page 245. -/
theorem isGraphForest_of_star
    {α β : Type*} (G : Graph α β) (c : α)
    (hshape : ∀ {e x y}, G.IsLink e x y → x ≠ y ∧ (x = c ∨ y = c))
    (hunique : ∀ x, x ≠ c → ∀ {e f y z},
      G.IsLink e x y → G.IsLink f x z → e = f) : IsGraphForest G := by
  intro u W hW
  cases W with
  | nil hu => rfl
  | cons he rest =>
    cases rest with
    | nil hv => exact False.elim ((hshape he).1 rfl)
    | cons hf tail =>
      rename_i v e w f
      change (v :: tail.support).Nodup ∧ (e :: f :: tail.edges).Nodup at hW
      have hef : e ≠ f := by
        intro heq
        exact (List.nodup_cons.mp hW.2).1 (List.mem_cons.mpr (Or.inl heq))
      by_cases huc : u = c
      · have hvc : v ≠ c := by
          intro hvc
          exact (hshape he).1 (huc.trans hvc.symm)
        exact False.elim (hef (hunique v hvc he.symm hf))
      · have hvc : v = c := (hshape he).2.resolve_left huc
        have hwc : w ≠ c := by
          intro hwc
          exact (hshape hf).1 (hvc.trans hwc.symm)
        cases tail with
        | nil hu => exact False.elim (hef (hunique u huc he hf.symm))
        | cons ht tailrest =>
          have htc : _ = c := (hshape ht).2.resolve_left hwc
          have hmem : v ∈ tailrest.support := by
            rw [hvc, ← htc]
            exact GraphMinor.Surface.GraphWalk.start_mem_support tailrest
          exact False.elim ((List.nodup_cons.mp hW.1).1 (List.mem_cons_of_mem w hmem))

end GraphMinor.GM12
