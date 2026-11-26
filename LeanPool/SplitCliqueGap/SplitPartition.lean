/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Main
public import LeanPool.StructuralGraphClasses.Split

/-! The split witnesses in this development give split partitions in the shared graph API. -/

public section

namespace GapExtremal

/-- The clique-and-complement condition is equivalent to admitting a split partition. -/
theorem isSplit_iff_simpleGraph_isSplit {V : Type*} (G : SimpleGraph V) :
    IsSplit G ↔ G.IsSplit := by
  constructor
  · rintro ⟨K, hK, hOutside⟩
    exact ⟨{
      clique := K
      independent := Kᶜ
      isClique := fun u hu v hv hne => hK u hu v hv hne
      isIndepSet := fun u hu v hv _ => hOutside u hu v hv
      disjoint := disjoint_compl_right
      cover := Set.union_compl_self K
    }⟩
  · rintro ⟨P⟩
    refine ⟨P.clique, fun _ hu _ hv hne => P.isClique hu hv hne, ?_⟩
    intro u hu v hv hAdj
    have hu' := (P.mem_clique_or_mem_independent u).resolve_left hu
    have hv' := (P.mem_clique_or_mem_independent v).resolve_left hv
    exact P.isIndepSet hu' hv' hAdj.ne hAdj

end GapExtremal
