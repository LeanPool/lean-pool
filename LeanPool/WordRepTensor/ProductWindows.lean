/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.ProductWindow

/-! The product windows preserve the three columns and their common root.
The far cross-edges distinguish the two window types. -/

@[expose] public section

namespace WordRepTensor

open SimpleGraph

theorem productWindowsMu :
  ∀ (k K : ℕ) [NeZero K] (hk : 3 ≤ k), 5 ≤ K → k ≤ K → k % 2 = 1 → K % 2 = 1 →
      ∀ i : Fin K, Function.Injective (productWinMap hk i) ∧
        ((∀ x y, (tensorProd (mu k) (muExt K)).Adj (productWinMap hk i x) (productWinMap hk i y) ↔
          wadjOf winMuEdges x y = true) ∨
         (∀ x y, (tensorProd (mu k) (muExt K)).Adj (productWinMap hk i x) (productWinMap hk i y) ↔
          wadjOf winExtEdges x y = true)) := by
  intro k K _ hk hK hkK hkOdd hKOdd i
  refine ⟨?_, ?_⟩
  · intro x y h
    exact winMap_inj hK i (congrArg Prod.snd h)
  obtain ⟨a01, a12, a02, d01, d12, d02⟩ := cyc_facts hK i
  have f01 := fold_adj hk hkK hKOdd hkOdd a01
  have f12 := fold_adj hk hkK hKOdd hkOdd a12
  have a20 : ¬ (cycleGraph K).Adj (i + 1 + 1) i := fun h => a02 h.symm
  have farRev : (cycleGraph k).Adj (fold hk (i + 1 + 1)) (fold hk i) ↔
      (cycleGraph k).Adj (fold hk i) (fold hk (i + 1 + 1)) :=
    SimpleGraph.adj_comm (cycleGraph k) _ _
  have windowAdj (x y : Fin 7) :
      (tensorProd (mu k) (muExt K)).Adj (productWinMap hk i x) (productWinMap hk i y) ↔
        (if (cycleGraph k).Adj (fold hk i) (fold hk (i + 1 + 1)) then
          wadjOf winExtEdges x y else wadjOf winMuEdges x y) = true := by
    fin_cases x <;> fin_cases y <;>
      simp (config := { decide := true }) [tensorProd_adj, productWinMap, foldVertex, winMap,
        mu, muExt, myc_adj_inl_inl, myc_adj_inl_sh, myc_adj_sh_inl, myc_not_adj_inl_root,
        myc_not_adj_root_inl, myc_not_adj_sh_sh, myc_adj_sh_root, myc_adj_root_sh,
        ext_adj_inl_inl, ext_adj_inl_sh, ext_adj_sh_inl, ext_adj_sh_root, ext_adj_root_sh,
        a01, a12, a01.symm, a12.symm, a02, a20, d01, d12, d02, Ne.symm d01,
        Ne.symm d12, Ne.symm d02, f01, f12, f01.symm, f12.symm, farRev]
  by_cases hfar : (cycleGraph k).Adj (fold hk i) (fold hk (i + 1 + 1))
  · exact Or.inr fun x y => by simpa [hfar] using windowAdj x y
  · exact Or.inl fun x y => by simpa [hfar] using windowAdj x y

theorem productWindowsExt :
  ∀ (k K : ℕ) [NeZero K] (hk : 3 ≤ k), 5 ≤ K → k ≤ K → k % 2 = 1 → K % 2 = 1 →
      ∀ i : Fin K, Function.Injective (productWinMap hk i) ∧
        ((∀ x y, (tensorProd (muExt k) (muExt K)).Adj
            (productWinMap hk i x) (productWinMap hk i y) ↔
          wadjOf winMuEdges x y = true) ∨
         (∀ x y, (tensorProd (muExt k) (muExt K)).Adj
            (productWinMap hk i x) (productWinMap hk i y) ↔
          wadjOf winExtEdges x y = true)) := by
  intro k K _ hk hK hkK hkOdd hKOdd i
  refine ⟨?_, ?_⟩
  · intro x y h
    exact winMap_inj hK i (congrArg Prod.snd h)
  obtain ⟨a01, a12, a02, d01, d12, d02⟩ := cyc_facts hK i
  have f01 := fold_adj hk hkK hKOdd hkOdd a01
  have f12 := fold_adj hk hkK hKOdd hkOdd a12
  have a20 : ¬ (cycleGraph K).Adj (i + 1 + 1) i := fun h => a02 h.symm
  have farRev : fold hk (i + 1 + 1) ≠ fold hk i ↔
      fold hk i ≠ fold hk (i + 1 + 1) := ne_comm
  have windowAdj (x y : Fin 7) :
      (tensorProd (muExt k) (muExt K)).Adj
            (productWinMap hk i x) (productWinMap hk i y) ↔
        (if fold hk i ≠ fold hk (i + 1 + 1) then
          wadjOf winExtEdges x y else wadjOf winMuEdges x y) = true := by
    fin_cases x <;> fin_cases y <;>
      simp (config := { decide := true }) [tensorProd_adj, productWinMap, foldVertex, winMap,
        muExt, ext_adj_inl_inl, ext_adj_inl_sh, ext_adj_sh_inl, ext_not_adj_inl_root,
        ext_not_adj_root_inl, ext_not_adj_sh_sh, ext_adj_sh_root, ext_adj_root_sh,
        a01, a12, a01.symm, a12.symm, a02, a20, d01, d12, d02, Ne.symm d01,
        Ne.symm d12, Ne.symm d02, f01, f12, f01.symm, f12.symm, f01.ne, f12.ne,
        f01.symm.ne, f12.symm.ne, farRev]
  by_cases hfar : fold hk i ≠ fold hk (i + 1 + 1)
  · exact Or.inr fun x y => by simpa [hfar] using windowAdj x y
  · exact Or.inl fun x y => by simpa [hfar] using windowAdj x y

end WordRepTensor
