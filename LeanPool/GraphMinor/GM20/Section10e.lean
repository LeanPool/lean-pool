/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10c
public import LeanPool.GraphMinor.GM17.Defs
public import LeanPool.GraphMinor.Surface.InvarianceOfDomain
public import LeanPool.GraphMinor.Surface.Disc

/-!
# Graph Minors XX, Section 10: paintings from portrayals

The proof of (10.3) starts with a portrayal from Graph Minors XVII, whose painting has no marches of
cells. This file makes it a painting in the sense of Graph Minors XX. The one fact that needs proof
is
that `cTilde ⊆ N(Γ)` for a cell `c`. If `x ∈ cTilde` were not a node, then `c ∪ {x}` would be a
larger arcwise
connected subset of `U(Γ) \ N(Γ)` (`isPathConnected_of_ball_subset`).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- A set between the open and the closed unit disc is arcwise connected, since it is star-shaped
around the origin. -/
theorem isPathConnected_of_ball_subset {Z : Set EuclideanPlane} (h₁ : OpenUnitDisc ⊆ Z)
    (h₂ : Z ⊆ ClosedUnitDisc) : IsPathConnected Z := by
  have hstar : StarConvex ℝ 0 Z := by
    intro y hy a b _ hb hab
    have hy' : ‖y‖ ≤ 1 := by simpa [ClosedUnitDisc] using h₂ hy
    rcases hb.eq_or_lt with hb₀ | hb₀
    · apply h₁
      subst hb₀
      simp [OpenUnitDisc]
    by_cases hb₁ : b = 1
    · subst hb₁
      have ha : a = 0 := by linarith
      simpa [ha] using hy
    · apply h₁
      have hb₂ : b < 1 := lt_of_le_of_ne (by linarith) hb₁
      simp only [OpenUnitDisc, Metric.mem_ball, dist_zero_right, smul_zero, zero_add, norm_smul,
        Real.norm_eq_abs, abs_of_pos hb₀]
      nlinarith [norm_nonneg y]
  exact hstar.isPathConnected (h₁ (by simp [OpenUnitDisc]))

/-- In a painting of Graph Minors XVII, the attachments of a cell are nodes. -/
theorem tilde_subset_nodes (Γ : GM17.Painting S) {c : Set S} (hc : c ∈ Γ.C) : tilde c ⊆ Γ.N := by
  intro x hx
  by_contra hxN
  obtain ⟨⟨φ⟩, hsub, -, -⟩ := Γ.cell_disc c hc
  have hbdy := disc_boundary (closure c) φ
  have hcU : c ⊆ Γ.U \ Γ.N := hc.2.1
  have hclU : closure c ⊆ Γ.U := closure_minimal (hcU.trans sdiff_subset) Γ.isClosed_U
  let Z : Set EuclideanPlane := {z | ∃ hz : z ∈ ClosedUnitDisc, (φ ⟨z, hz⟩).1 ∈ insert x c}
  have hZ : IsPathConnected Z := by
    refine isPathConnected_of_ball_subset (fun z hz ↦ ?_) fun z hz ↦ hz.1
    have hzc : z ∈ ClosedUnitDisc := Metric.ball_subset_closedBall hz
    refine ⟨hzc, Or.inr ?_⟩
    by_contra hnc
    have hmem : (φ ⟨z, hzc⟩).1 ∈ tilde c := ⟨(φ ⟨z, hzc⟩).2, hnc⟩
    have hm₂ := hsub hmem
    rw [hbdy] at hm₂
    obtain ⟨w, hw, hwe⟩ := hm₂
    have heq : w = ⟨z, hzc⟩ := φ.injective (Subtype.ext hwe)
    subst heq
    have h₁ : z ∈ UnitCircle := hw
    have h₂ : z ∈ OpenUnitDisc := hz
    simp only [UnitCircle, OpenUnitDisc, Metric.mem_sphere, Metric.mem_ball] at h₁ h₂
    linarith
  have hZ' : IsPathConnected (Subtype.val ⁻¹' Z : Set ClosedUnitDisc) := by
    rw [IsInducing.subtypeVal.isPathConnected_iff]
    have hZsub : Z ⊆ ClosedUnitDisc := fun _ hz ↦ hz.1
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hZsub]
  have hY : (fun z ↦ (φ z).1) '' (Subtype.val ⁻¹' Z : Set ClosedUnitDisc) = insert x c := by
    ext y
    constructor
    · rintro ⟨z, ⟨_, hz⟩, rfl⟩
      exact hz
    · intro hy
      have hyc : y ∈ closure c := by
        rcases hy with rfl | hy
        · exact hx.1
        · exact subset_closure hy
      refine ⟨φ.symm ⟨y, hyc⟩, ⟨(φ.symm ⟨y, hyc⟩).2, ?_⟩, by simp⟩
      simpa using hy
  have hpath : IsPathConnected (insert x c) := by
    rw [← hY]
    exact hZ'.image (continuous_subtype_val.comp φ.continuous)
  have hsub₂ : insert x c ⊆ Γ.U \ Γ.N := by
    rintro y (rfl | hy)
    · exact ⟨hclU hx.1, hxN⟩
    · exact hcU hy
  have heq := hc.2.2.2 _ hsub₂ hpath (subset_insert _ _)
  exact hx.2 (heq ▸ mem_insert _ _)

/-- A painting of Graph Minors XVII with marches on its cells, and with every cell of size at least
two,
is a painting of Graph Minors XX. -/
noncomputable def paintingOf (Γ : GM17.Painting S) (g : Set S → List S)
    (hsize : ∀ c ∈ Γ.C, 2 ≤ (tilde c).ncard) (hg : ∀ c ∈ Γ.C, (g c).Nodup)
    (hset : ∀ c ∈ Γ.C, {n | n ∈ g c} = tilde c) : Painting S where
  U := Γ.U
  N := Γ.N
  γ := g
  isClosed_U := Γ.isClosed_U
  N_subset := Γ.N_subset
  finite_N := Γ.finite_N
  bd_subset := Γ.bd_subset
  finite_cells := Γ.finite_cells
  cell_disc c hc := (Γ.cell_disc c hc).1
  cell_size c hc := by
    obtain ⟨-, -, h₁, h₂⟩ := Γ.cell_disc c hc
    have h₃ := hsize c hc
    exact ⟨h₁, by omega⟩
  closure_inter c hc := by
    ext x
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨h₁, fun h₃ ↦ (hc.2.1 h₃).2 h₂⟩
    · intro h₁
      exact ⟨h₁.1, tilde_subset_nodes Γ hc h₁⟩
  tilde_subset c hc := (Γ.cell_disc c hc).2.1
  border_cell c hc hb := by
    obtain ⟨h₁, -, h₂, h₃⟩ := Γ.border_cell c hc hb
    exact ⟨h₁, h₂, h₃⟩
  γ_nodup := hg
  γ_set := hset

end GraphMinor.GM20
