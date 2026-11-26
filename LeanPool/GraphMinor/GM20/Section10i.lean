/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10h

/-!
# Graph Minors XX, Section 10: the properties of the location of a true portrayal

We finish the part of the proof of (10.3) that uses Graph Minors XVII. For a portrayal `π` that
meets
the standing hypothesis of Section 8 of that paper, `(P, ℒ)` is shelled (`isShelled_of_standing`).
With the
stronger standing hypothesis of Section 11, `ℒ` is linked to `𝒯` (`isLinkedTo_of_standing`).
The deductions using other proved results are in `Section10iProved`.
-/

@[expose] public section

namespace GraphMinor.GM20.GM17.Standing

open GraphMinor.GM17

variable {α : Type*} {β : Type*} {G : Hypergraph α β} {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
  {θ p r t r' t' : ℕ} {π : Portrayal G}

/-- The standing hypothesis gets weaker when `r` and `t` decrease. -/
theorem mono (h : Standing 𝒯 θ p r t π) (hr : r' ≤ r) (ht : t' ≤ t) :
    Standing 𝒯 θ p r' t' π where
  isTangle := h.isTangle
  isTrue := h.isTrue
  isRedundant := ⟨by have := h.isRedundant.1; omega,
    fun Z hZ hZc ↦ h.isRedundant.2 Z hZ (hZc.trans hr)⟩
  warp_le := h.warp_le
  lt := by have := h.lt; omega

end GraphMinor.GM20.GM17.Standing

namespace GraphMinor.GM17.Portrayal

open Set Topology GraphMinor.Surface GraphMinor.GM18 GraphMinor.GM20 GraphMinor.GM10
  GraphMinor.GM20.GM17

universe u v

variable {α : Type u} {β : Type v} {P : UnlabeledPatchwork α β} {π : Portrayal P.G.toHypergraph}
  {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ p : ℕ}

/-- The warp at a cuff is at most the warp. -/
theorem warpAt_le_warp_of_mem {G : Hypergraph α β} (π : Portrayal G) {Θ : Set π.S}
    (hΘ : Θ ∈ cuffs π.S) : π.warpAt Θ ≤ π.warp := by
  classical
  obtain ⟨-, hfin, -⟩ := cuff_statement.{0} π.S π.isSurface
  unfold warp
  rw [ite_eq_left ⟨Θ, hΘ⟩]
  apply le_trans _ (le_max_right 1 _)
  refine le_csSup ?_ ⟨Θ, hΘ, rfl⟩
  refine (hfin.image π.warpAt).bddAbove.mono ?_
  rintro _ ⟨Θ', h, rfl⟩
  exact ⟨Θ', h, rfl⟩

/-- A second attachment of a cell. -/
theorem exists_other_end {G : Hypergraph α β} {π : Portrayal G}
    (h₂ : ∀ c ∈ π.Γ.C, 2 ≤ (tilde c).ncard) {c : Set π.S} (hc : c ∈ π.Γ.C) (n : π.S) :
    ∃ m ∈ tilde c, m ≠ n := by
  have h : 1 < (tilde c).ncard := h₂ c hc
  exact Set.exists_ne_of_one_lt_ncard h n


end GraphMinor.GM17.Portrayal
