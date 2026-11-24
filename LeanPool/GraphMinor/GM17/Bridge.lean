/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.Section9
public import LeanPool.GraphMinor.GM17.Section9b
public import LeanPool.GraphMinor.GM17.Section11
public import LeanPool.GraphMinor.GM17.Section14
public import LeanPool.GraphMinor.GM17.Section14b
public import LeanPool.GraphMinor.GM17.Section13d
public import LeanPool.GraphMinor.GM19.Cited
import LeanPool.GraphMinor.GM17.PasteCuff
import LeanPool.GraphMinor.GM17.ArcDisc
import LeanPool.GraphMinor.GM17.MarkCross
import LeanPool.GraphMinor.GM17.ReplaceDisc
import LeanPool.GraphMinor.GM17.RegionDisc
import LeanPool.GraphMinor.GM17.CutArcPaint
import LeanPool.GraphMinor.GM17.PushNode
import LeanPool.GraphMinor.GM17.RegionBoundary
import LeanPool.GraphMinor.GM17.IndentMain
import LeanPool.GraphMinor.GM17.CellPartitionMain

import LeanPool.GraphMinor.GM16.MainProof

import LeanPool.GraphMinor.GM17.Section11Proved

import LeanPool.GraphMinor.GM17.Section8Proved

import LeanPool.GraphMinor.GM17.Section9Proved

import LeanPool.GraphMinor.GM17.Section9bProved

/-!
# Graph Minors XVII: Bridge Theorems for Cited Statements in XX

This file proves the Graph Minors XVII statements cited in `GraphMinor/GM20/Cited.lean`:
- `gm17Theorem82` (`GM20.GM17Theorem82Statement`, (8.2), page 181);
- `gm17Theorem83` (`GM20.GM17Theorem83Statement`, (8.3), page 182);
- `gm17Theorem84` (`GM20.GM17Theorem84Statement`, (8.4), page 182);
- `gm17Theorem85` (`GM20.GM17Theorem85Statement`, (8.5), page 182);
- `gm17Theorem87` (`GM20.GM17Theorem87Statement`, (8.7), page 182);
- `gm17Theorem88` (`GM20.GM17Theorem88Statement`, (8.8), page 183);
- `gm17Theorem91` (`GM20.GM17Theorem91Statement`, (9.1), page 183);
- `gm17Theorem98` (`GM20.GM17Theorem98Statement`, (9.8), page 187);
- `gm17Theorem142` (`GM20.GM17Theorem142Statement`, (14.2), page 209), from (13.1);
- `gm17Theorem117` (`GM20.GM17Theorem117Statement`, (11.7), page 195).
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface
open GraphMinor.GM10
open GraphMinor.Hypergraph

universe u v

/-- Proof of `GM20.GM17Theorem82Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (8.2), page 181). -/
theorem gm17Theorem82 :
    GM20.GM17Theorem82Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand
  obtain ⟨h1, h2, _⟩ :=
    theorem_8_2_proof
      hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt
  exact ⟨by simpa [Painting.regions, Set.compl_eq_univ_sdiff] using h1, h2⟩

/-- Proof of `GM20.GM17Theorem83Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (8.3), page 182). -/
theorem gm17Theorem83 :
    GM20.GM17Theorem83Statement.{u, v} :=
  gm17_theorem_8_3

/-- Proof of `GM20.GM17Theorem84Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (8.4), page 182). -/
theorem gm17Theorem84 :
    GM20.GM17Theorem84Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand
  exact theorem_8_4_proof
    hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt

/-- Proof of `GM20.GM17Theorem85Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (8.5), page 182). -/
theorem gm17Theorem85 :
    GM20.GM17Theorem85Statement.{u, v} :=
  gm17_theorem_8_5

/-- Proof of `GM20.GM17Theorem87Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (8.7), page 182). -/
theorem gm17Theorem87 :
    GM20.GM17Theorem87Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand n hn
  exact theorem_8_7_proof
    hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt hn

/-- Proof of `GM20.GM17Theorem88Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (8.8), page 183). -/
theorem gm17Theorem88 :
    GM20.GM17Theorem88Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand c₁ hc₁ c₂ hc₂ hne hsub
  exact theorem_8_8_proof
    hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt hc₁ hc₂ hne hsub

/-- Proof of `GM20.GM17Theorem91Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (9.1), page 183). -/
theorem gm17Theorem91 :
    GM20.GM17Theorem91Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand c₀ hc₀ hint₀ n₁ hn₁ n₂ hn₂ hne
  exact theorem_9_1_proof
    hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt
    hc₀ hint₀ hn₁ hn₂ hne

/-- Proof of `GM20.GM17Theorem98Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (9.8), page 187). -/
theorem gm17Theorem98 :
    GM20.GM17Theorem98Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand Θ hΘ c₀ hc₀ hc₀_Θ n₁ hn₁ n₂ hn₂ hne
  exact theorem_9_8_proof
    hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt
    hΘ hc₀ hc₀_Θ hn₁ hn₂ hne

/-- Proof of `GM20.GM17Theorem117Statement` in `GraphMinor/GM20/Cited.lean`
(Graph Minors XVII, (11.7), page 195). -/
theorem gm17Theorem117 : GM20.GM17Theorem117Statement.{u, v} := by
  intro α β G 𝒯 θ p π hstand c₀ hc₀ A B hAB hc₀A hle
  exact theorem_11_7_proof
    hstand.isTangle π hstand.isTrue hstand.isRedundant hstand.warp_le hstand.lt
    hc₀ hAB hc₀A hle

/-- Proof of `GM19.GM17Theorem141Statement` in `GraphMinor/GM19/Cited.lean`
(Graph Minors XVII, (14.1), page 207). -/
theorem gm17Theorem141 : GM19.GM17Theorem141Statement.{u} := by
  intro V E G θ θstar T h1 hlt hT
  exact theorem_14_1_proof h1 hlt hT

/-- `GM20.GM17Theorem142Statement`: Graph Minors XVII, (14.2) (page 209), from XVI (3.1). -/
theorem gm17Theorem142 : GM20.GM17Theorem142Statement.{u, v} :=
  fun H hH => theorem_14_2_proof H hH

end GraphMinor.GM17
