/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10j
public import LeanPool.GraphMinor.GM19.Section12a
public import LeanPool.GraphMinor.GM11.Section92

/-!
# Two poles at small distance lie in a tie

The first step of the text before (10.4): "since $dist(\Gamma) \ge \frac{1}{2}n + 1$, it follows
from Theorem 9.2 of [6] that there exists $F \subseteq \Gamma^*$".
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

/-- A closed walk whose inside meets the region of a vertex `r*` has `r*` in its inside. -/
theorem center_mem_ins (D : TangleDatum cap χ) (hrep : 1 ≤ D.rep) {w : Shat} (hw : w ∈ D.rad.Rstar)
    (T : ClosedWalkIns D.rad D.ord D.𝒯) (hm : (D.rad.regionOf w ∩ T.ins).Nonempty) : w ∈ T.ins := by
  have hS := χ.isSurface
  obtain ⟨hρ, hwm⟩ := D.rad.regionOf_mem hw
  obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
  obtain ⟨w', ⟨hw', hwG⟩, huniq⟩ := hG3 _ hρ
  obtain rfl : w = w' := huniq w ⟨hwm, hw.1⟩
  obtain ⟨y, hyz, hy⟩ := hm
  have hX := (isRestraint_ins D hrep T).1
  by_cases hyU : y ∈ D.rad.G.U
  · by_cases hyV : y ∈ D.rad.G.V
    · rw [huniq y ⟨hyz, hyV⟩] at hy
      exact hy
    · obtain ⟨e, he, hye⟩ := D.rad.G.exists_edge_of_mem hyU hyV
      have hsub : e ⊆ T.ins := nice_atom hX.isGammaNice (Or.inl (Or.inr he)) ⟨y, hye, hy⟩
      exact closure_minimal hsub hX.isClosed (D.rad.center_mem_closure hS he hρ ⟨y, hye,
        hyz⟩ hw' hwG)
  · obtain ⟨s, hs, hys⟩ := exists_region_of_notMem hyU
    have hsub := nice_region hX.isGammaNice hs ⟨y, hys, hy⟩
    exact closure_minimal hsub hX.isClosed (D.rad.center_mem_closure_region hS hs hρ ⟨y, hys,
      hyz⟩ hw' hwG)

/-- Two poles at distance at most `n < rep(𝒯)` lie in a tie of length at most `2n`, by XI (8.5) and
XI (9.2). -/
theorem exists_pole_tie (D : TangleDatum cap χ) {n : ℕ} (hn : n < D.rep) {r₁ r₂ : Shat}
  (h₁ : r₁ ∈ D.rad.poles)
    (h₂ : r₂ ∈ D.rad.poles) (hne : r₁ ≠ r₂) (hd : D.vDist r₁ r₂ ≤ n) :
    ∃ X, IsTie D.rad.G D.ins (2 * D.rep) X ∧ r₁ ∈ X ∧ r₂ ∈ X ∧ perimeterWalkLength D.rad.G X
      ≤ 2 * n := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hrep : 1 ≤ D.rep := by omega
  have ha₁ : D.rad.atomOf r₁ = D.rad.regionOf r₁ := by
    classical
    unfold RadialDrawing.atomOf
    rw [ite_eq_right h₁.1.2]
  have ha₂ : D.rad.atomOf r₂ = D.rad.regionOf r₂ := by
    classical
    unfold RadialDrawing.atomOf
    rw [ite_eq_right h₂.1.2]
  have hreg : D.rad.regionOf r₁ ≠ D.rad.regionOf r₂ := fun heq ↦ by
    obtain ⟨-, -, hG3, -⟩ := id D.rad.isPreRadial
    have m₁ := D.rad.regionOf_mem h₁.1
    have m₂ := D.rad.regionOf_mem h₂.1
    exact hne ((hG3 _ m₁.1).unique ⟨m₁.2, h₁.1.1⟩ ⟨heq ▸ m₂.2, h₂.1.1⟩)
  have hd' : D.dist (D.rad.regionOf r₁) (D.rad.regionOf r₂) < D.rep := by
    have : D.vDist r₁ r₂ = D.dist (D.rad.regionOf r₁) (D.rad.regionOf r₂) := by
      rw [vDist, ha₁, ha₂]
    omega
  obtain ⟨T, hm₁, hm₂, hl⟩ := D.exists_of_dist_lt hreg hd'
  have hr₁ := D.center_mem_ins hrep h₁.1 T hm₁
  have hr₂ := D.center_mem_ins hrep h₂.1 T hm₂
  obtain ⟨hY, hlY⟩ := isRestraint_ins D hrep T
  have hA : ∀ {r : Shat}, r ∈ D.rad.poles → ({r} : Set Shat) ∈ D.rad.G.A := fun {r} hr ↦
    Or.inl (Or.inl ⟨r, hr.1.1, rfl⟩)
  obtain ⟨X, hX, hs₁, hs₂, -, hle⟩ := GM11.theorem_9_2_proof hT (D.isSlope hrep) (hA h₁) (hA h₂) hY
    (singleton_subset_iff.2 hr₁)
    (singleton_subset_iff.2 hr₂)
  refine ⟨X, hX, hs₁ rfl, hs₂ rfl, hle.trans (hlY.trans ?_)⟩
  have : D.vDist r₁ r₂ = T.halfLen := by
    rw [hl, vDist, ha₁, ha₂]
  omega

end TangleDatum

end GraphMinor.GM19
