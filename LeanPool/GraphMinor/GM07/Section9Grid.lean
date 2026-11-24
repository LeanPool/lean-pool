/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section9Cylinder
public import LeanPool.GraphMinor.GM16.RectangularGridDrawing
import LeanPool.GraphMinor.GM16.SpherePlaneEmbedding
import LeanPool.GraphMinor.GM16.RectangularDisc
import LeanPool.GraphMinor.GM16.DrawingGraphPaths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Proof of Graph Minors VII, (9.6) from (9.5) (page 246)

This file proves the grid reduction step of Graph Minors VII, (9.6) (page 246):
in a sufficiently large `N × N`-grid drawn in a sphere `Σ`, there exist two disjoint `G`-normal
`O`-arcs `F₁, F₂` in `Σ` satisfying conditions (i) and (ii) of (9.4)/(9.5) with
`r = rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Function Topology
open Graph SimpleGraph
open GraphMinor.Surface GraphMinor.GM01 GraphMinor.GM11 GraphMinor.GM16

universe u

/-- A drawing `G` in `S` is isomorphic to an `N × N`-grid (Graph Minors VII, (9.6), page 246:
"[The $N \times N$-grid is the adjacency graph of the squares of a chessboard with $N^2$
squares.]"): it is the image under an open embedding `j : ℝ × ℝ → S` of the standard `N × N`
rectangular grid drawing in `ℝ × ℝ`, together with a graph isomorphism between `GM01.gridGraph N`
and `G.toGraph`. -/
def IsGridDrawing {S : Type u} [TopologicalSpace S] (G : Drawing S) (N : ℕ) : Prop :=
  ∃ (j : (ℝ × ℝ) → S) (iso : GraphMinor.Iso (GM01.gridGraph N) G.toGraph),
    IsOpenEmbedding j ∧
    G.V = range (j ∘ @rectangularGridPoint N N) ∧
    (∀ v : V(GM01.gridGraph N), (iso.vertexEquiv v).val = j (rectangularGridPoint v.val)) ∧
    (∀ e : E(GM01.gridGraph N), closure (iso.edgeEquiv e).val = j '' rectangularGridLine e.val)

/-- Every sphere admits a drawing of the `N × N`-grid satisfying `IsGridDrawing`. -/
theorem exists_isGridDrawing {S : Type u} [TopologicalSpace S] [T2Space S]
    (hSph : IsSphere S) (N : ℕ) :
    ∃ G : Drawing S, IsGridDrawing G N := by
  obtain ⟨j, hj⟩ := exists_plane_openEmbedding_of_isSphere hSph
  obtain ⟨Γ, hV, hVertices, hEdges⟩ :=
    exists_rectangularGrid_embedded_drawing (pathGraph N □ pathGraph N) le_rfl j hj.isEmbedding
  exact ⟨Γ.drawing, j, Γ.iso, hj, hV, hVertices, hEdges⟩

/-- The 45-degree rotation/scaling homeomorphism `(u, v) ↦ (u - v, u + v)` of `ℝ × ℝ`. -/
noncomputable def diamondHomeo : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1 - p.2, p.1 + p.2)
  invFun q := ((q.1 + q.2) / 2, (q.2 - q.1) / 2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv q := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem diamondHomeo_apply (p : ℝ × ℝ) :
    diamondHomeo p = (p.1 - p.2, p.1 + p.2) :=
  rfl

/-- Coordinate bounds and integrality of at least one coordinate for points in `G.U` of an
`N × N`-grid drawing. -/
theorem mem_grid_U_coords {S : Type u} [TopologicalSpace S] {G : Drawing S} {N : ℕ}
    {j : (ℝ × ℝ) → S} {iso : GraphMinor.Iso (GM01.gridGraph N) G.toGraph}
    (hj : IsOpenEmbedding j)
    (hV : G.V = range (j ∘ @rectangularGridPoint N N))
    (hEdges : ∀ e : E(GM01.gridGraph N),
      closure (iso.edgeEquiv e).val = j '' rectangularGridLine e.val)
    {p : ℝ × ℝ} (hp : j p ∈ G.U) :
    0 ≤ p.1 ∧ p.1 < (N : ℝ) ∧ 0 ≤ p.2 ∧ p.2 < (N : ℝ) ∧
      ((∃ i : Fin N, p.1 = (i.val : ℝ)) ∨ (∃ k : Fin N, p.2 = (k.val : ℝ))) := by
  by_cases hpV : j p ∈ G.V
  · rw [hV] at hpV
    obtain ⟨v, hv⟩ := hpV
    have hp_eq : rectangularGridPoint v = p := hj.injective hv
    have hp1 : p.1 = (v.1.val : ℝ) := (congrArg Prod.fst hp_eq).symm
    have hp2 : p.2 = (v.2.val : ℝ) := (congrArg Prod.snd hp_eq).symm
    refine ⟨hp1 ▸ Nat.cast_nonneg _, hp1 ▸ Nat.cast_lt.mpr v.1.isLt,
      hp2 ▸ Nat.cast_nonneg _, hp2 ▸ Nat.cast_lt.mpr v.2.isLt, Or.inl ⟨v.1, hp1⟩⟩
  · have hpUV : j p ∈ G.U \ G.V := ⟨hp, hpV⟩
    let e_S : Set S := pathComponentIn (G.U \ G.V) (j p)
    have he_S : e_S ∈ G.E := pathComponentIn_mem_arcComponentsIn hpUV
    have hjp_cl : j p ∈ closure e_S := subset_closure (mem_pathComponentIn_self hpUV)
    let e_G : E(GM01.gridGraph N) := iso.edgeEquiv.symm ⟨e_S, he_S⟩
    have he_eq : (iso.edgeEquiv e_G).val = e_S :=
      congrArg Subtype.val (iso.edgeEquiv.apply_symm_apply ⟨e_S, he_S⟩)
    have hcl_eq : closure e_S = j '' rectangularGridLine e_G.val := by
      rw [← he_eq, hEdges e_G]
    rw [hcl_eq] at hjp_cl
    obtain ⟨q, hq, hqp⟩ := hjp_cl
    have hp_mem : p ∈ rectangularGridLine e_G.val := hj.injective hqp ▸ hq
    rcases rectangularGridLine_spec e_G.property with
      ⟨i, k, hi, _, hLine⟩ | ⟨i, k, hk, _, hLine⟩
    · rw [hLine] at hp_mem
      have hp1_lo : (i.val : ℝ) ≤ p.1 := hp_mem.1.1
      have hp1_hi : p.1 ≤ (i.val : ℝ) + 1 := hp_mem.1.2
      have hp2_eq : p.2 = (k.val : ℝ) := hp_mem.2
      have hi_lt : (i.val : ℝ) + 1 < (N : ℝ) := by exact_mod_cast hi
      have hi0 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
      refine ⟨by linarith, by linarith, hp2_eq ▸ Nat.cast_nonneg _,
        hp2_eq ▸ Nat.cast_lt.mpr k.isLt, Or.inr ⟨k, hp2_eq⟩⟩
    · rw [hLine] at hp_mem
      have hp1_eq : p.1 = (i.val : ℝ) := hp_mem.1
      have hp2_lo : (k.val : ℝ) ≤ p.2 := hp_mem.2.1
      have hp2_hi : p.2 ≤ (k.val : ℝ) + 1 := hp_mem.2.2
      have hk_lt : (k.val : ℝ) + 1 < (N : ℝ) := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
      refine ⟨hp1_eq ▸ Nat.cast_nonneg _, hp1_eq ▸ Nat.cast_lt.mpr i.isLt,
        by linarith, by linarith, Or.inl ⟨i, hp1_eq⟩⟩

/-- Any point `p : ℝ × ℝ` with integer coordinates in `[0, N)` maps into `G.V`. -/
theorem mem_grid_V_of_int_coords {S : Type u} [TopologicalSpace S] {G : Drawing S} {N : ℕ}
    {j : (ℝ × ℝ) → S}
    (hV : G.V = range (j ∘ @rectangularGridPoint N N))
    {p : ℝ × ℝ} (hp1_ge : 0 ≤ p.1) (hp1_lt : p.1 < (N : ℝ))
    (hp2_ge : 0 ≤ p.2) (hp2_lt : p.2 < (N : ℝ))
    {z₁ z₂ : ℤ} (hz₁ : p.1 = (z₁ : ℝ)) (hz₂ : p.2 = (z₂ : ℝ)) :
    j p ∈ G.V := by
  have hz₁_nn : 0 ≤ z₁ := by exact_mod_cast (hz₁ ▸ hp1_ge : (0 : ℝ) ≤ (z₁ : ℝ))
  have hz₁_lt : z₁ < (N : ℤ) := by exact_mod_cast (hz₁ ▸ hp1_lt : (z₁ : ℝ) < (N : ℝ))
  have hz₂_nn : 0 ≤ z₂ := by exact_mod_cast (hz₂ ▸ hp2_ge : (0 : ℝ) ≤ (z₂ : ℝ))
  have hz₂_lt : z₂ < (N : ℤ) := by exact_mod_cast (hz₂ ▸ hp2_lt : (z₂ : ℝ) < (N : ℝ))
  have hi : z₁.toNat < N := by omega
  have hk : z₂.toNat < N := by omega
  have hp_eq : p = rectangularGridPoint (⟨z₁.toNat, hi⟩, ⟨z₂.toNat, hk⟩) := by
    ext
    · change p.1 = (z₁.toNat : ℝ)
      rw [hz₁]
      exact_mod_cast (Int.toNat_of_nonneg hz₁_nn).symm
    · change p.2 = (z₂.toNat : ℝ)
      rw [hz₂]
      exact_mod_cast (Int.toNat_of_nonneg hz₂_nn).symm
  rw [hV, hp_eq]
  exact ⟨(⟨z₁.toNat, hi⟩, ⟨z₂.toNat, hk⟩), rfl⟩

/-- For any rectangle `R = [a, b] × [c, d]` with integer coordinates `a < b` and `c < d`,
`(j ∘ diamondHomeo) '' frontier R` is a `G`-normal `O`-arc in `S`. -/
theorem diamond_frontier_isOArc_and_isNormal {S : Type u} [TopologicalSpace S] [T2Space S]
    {G : Drawing S} {N : ℕ}
    {j : (ℝ × ℝ) → S} {iso : GraphMinor.Iso (GM01.gridGraph N) G.toGraph}
    (hj : IsOpenEmbedding j)
    (hV : G.V = range (j ∘ @rectangularGridPoint N N))
    (hEdges : ∀ e : E(GM01.gridGraph N),
      closure (iso.edgeEquiv e).val = j '' rectangularGridLine e.val)
    {a b c d : ℤ} (hab : a < b) (hcd : c < d) :
    let R : Set (ℝ × ℝ) := Icc (a : ℝ) (b : ℝ) ×ˢ Icc (c : ℝ) (d : ℝ)
    let F : Set S := (j ∘ diamondHomeo) '' frontier R
    IsOArc F ∧ G.IsNormal F := by
  intro R F
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hcdR : (c : ℝ) < (d : ℝ) := by exact_mod_cast hcd
  have hemb : IsEmbedding (j ∘ diamondHomeo) := hj.isEmbedding.comp diamondHomeo.isEmbedding
  obtain ⟨hDiscR, hBdR⟩ := isClosedDisc_real_rectangle_with_boundary habR hcdR
  obtain ⟨hDiscImg, hBdImg⟩ := isClosedDisc_image_injOn hDiscR (isCompact_Icc.prod isCompact_Icc)
    hemb.continuous.continuousOn hemb.injective.injOn
  have hF_bd : discBd ((j ∘ diamondHomeo) '' R) = F := by
    rw [hBdImg, hBdR]
  refine ⟨hF_bd ▸ hDiscImg.isOArc_discBd, ?_⟩
  rintro w ⟨⟨p, hp_fr, rfl⟩, hwU⟩
  change j (diamondHomeo p) ∈ G.U at hwU
  obtain ⟨hq1_ge, hq1_lt, hq2_ge, hq2_lt, hq_int⟩ := mem_grid_U_coords hj hV hEdges hwU
  have hp_mem : p ∈ R := (isClosed_Icc.prod isClosed_Icc).frontier_subset hp_fr
  have hp_not_int : p ∉ Ioo (a : ℝ) (b : ℝ) ×ˢ Ioo (c : ℝ) (d : ℝ) := by
    have hint : interior R = Ioo (a : ℝ) (b : ℝ) ×ˢ Ioo (c : ℝ) (d : ℝ) := by
      rw [interior_prod_eq, interior_Icc, interior_Icc]
    rw [← hint]
    exact hp_fr.2
  have hp_coord_int : (∃ m : ℤ, p.1 = (m : ℝ)) ∨ (∃ n : ℤ, p.2 = (n : ℝ)) := by
    by_contra hnot
    push Not at hnot
    apply hp_not_int
    refine ⟨⟨lt_of_le_of_ne hp_mem.1.1 (hnot.1 a).symm, lt_of_le_of_ne hp_mem.1.2 (hnot.1 b)⟩,
      ⟨lt_of_le_of_ne hp_mem.2.1 (hnot.2 c).symm, lt_of_le_of_ne hp_mem.2.2 (hnot.2 d)⟩⟩
  have hboth_int : ∃ z₁ z₂ : ℤ, (diamondHomeo p).1 = (z₁ : ℝ) ∧ (diamondHomeo p).2 = (z₂ : ℝ) := by
    rcases hp_coord_int with ⟨m, hm⟩ | ⟨n, hn⟩ <;> rcases hq_int with ⟨i, hi⟩ | ⟨k, hk⟩
    · refine ⟨(i.val : ℤ), 2 * m - (i.val : ℤ), by exact_mod_cast hi, ?_⟩
      change p.1 + p.2 = _
      change p.1 - p.2 = (i.val : ℝ) at hi
      push_cast
      linarith
    · refine ⟨2 * m - (k.val : ℤ), (k.val : ℤ), ?_, by exact_mod_cast hk⟩
      change p.1 - p.2 = _
      change p.1 + p.2 = (k.val : ℝ) at hk
      push_cast
      linarith
    · refine ⟨(i.val : ℤ), (i.val : ℤ) + 2 * n, by exact_mod_cast hi, ?_⟩
      change p.1 + p.2 = _
      change p.1 - p.2 = (i.val : ℝ) at hi
      push_cast
      linarith
    · refine ⟨(k.val : ℤ) - 2 * n, (k.val : ℤ), ?_, by exact_mod_cast hk⟩
      change p.1 - p.2 = _
      change p.1 + p.2 = (k.val : ℝ) at hk
      push_cast
      linarith
  obtain ⟨z₁, z₂, hz₁, hz₂⟩ := hboth_int
  exact mem_grid_V_of_int_coords hV hq1_ge hq1_lt hq2_ge hq2_lt hz₁ hz₂

/-- Any real number `t ∈ [a, b]` with `a < b` in `ℕ` lies in `[m, m + 1]` for some `m : ℕ` with
`a ≤ m` and `m + 1 ≤ b`. -/
theorem exists_nat_unit_interval_of_mem_Icc {a b : ℕ} (hab : a < b) {t : ℝ}
    (ht1 : (a : ℝ) ≤ t) (ht2 : t ≤ (b : ℝ)) :
    ∃ m : ℕ, a ≤ m ∧ m + 1 ≤ b ∧ (m : ℝ) ≤ t ∧ t ≤ (m : ℝ) + 1 := by
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg a) ht1
  have hfl_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have hlt_fl : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have ha_le : a ≤ ⌊t⌋₊ := Nat.le_floor ht1
  by_cases hlt : ⌊t⌋₊ < b
  · exact ⟨⌊t⌋₊, ha_le, hlt, hfl_le, le_of_lt hlt_fl⟩
  · have hb_le : (b : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast not_lt.mp hlt
    have htb : t = (b : ℝ) := le_antisymm ht2 (le_trans hb_le hfl_le)
    refine ⟨b - 1, by omega, by omega, ?_, ?_⟩
    · rw [htb, Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      linarith
    · rw [htb, Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      linarith

/-- Every point on the boundary of an integer box `[x₁, x₂] × [y₁, y₂]` (`x₁ < x₂ < N`,
`y₁ < y₂ < N`) maps into `G.U`. -/
theorem box_boundary_subset_grid_U {S : Type u} [TopologicalSpace S] {G : Drawing S} {N : ℕ}
    {j : (ℝ × ℝ) → S} {iso : GraphMinor.Iso (GM01.gridGraph N) G.toGraph}
    (hEdges : ∀ e : E(GM01.gridGraph N),
      closure (iso.edgeEquiv e).val = j '' rectangularGridLine e.val)
    {x₁ x₂ y₁ y₂ : ℕ} (hx : x₁ < x₂) (hxN : x₂ < N) (hy : y₁ < y₂) (hyN : y₂ < N)
    {p : ℝ × ℝ}
    (hp_in : p ∈ Icc (x₁ : ℝ) (x₂ : ℝ) ×ˢ Icc (y₁ : ℝ) (y₂ : ℝ))
    (hp_out : p ∉ Ioo (x₁ : ℝ) (x₂ : ℝ) ×ˢ Ioo (y₁ : ℝ) (y₂ : ℝ)) :
    j p ∈ G.U := by
  have hedge_sub : ∀ e : E(GM01.gridGraph N), j '' rectangularGridLine e.val ⊆ G.U := by
    intro e
    rw [← hEdges e]
    exact G.isClosed_U.closure_subset_iff.mpr
      ((iso.edgeEquiv e).property.2.1.trans sdiff_subset)
  have hhoriz : ∀ (i k : ℕ) (hi : i + 1 < N) (hk : k < N),
      (i : ℝ) ≤ p.1 → p.1 ≤ (i : ℝ) + 1 → p.2 = (k : ℝ) → j p ∈ G.U := by
    intro i k hi hk hp1_lo hp1_hi hp2_eq
    let u : Fin N × Fin N := (⟨i, by omega⟩, ⟨k, hk⟩)
    let v : Fin N × Fin N := (⟨i + 1, hi⟩, ⟨k, hk⟩)
    have hadj : (pathGraph N □ pathGraph N).Adj u v :=
      Or.inl ⟨pathGraph_adj.mpr (Or.inl rfl), rfl⟩
    let e : E(GM01.gridGraph N) := ⟨s(u, v), hadj⟩
    have hline : rectangularGridLine e.val = horizontalLatticeLine i k := by
      change rectangularGridLinePair u v = _
      simp only [rectangularGridLinePair, u, v, ite_true, Nat.min_eq_left (Nat.le_succ i), min_self]
    apply hedge_sub e
    rw [hline]
    exact ⟨p, ⟨⟨hp1_lo, hp1_hi⟩, hp2_eq⟩, rfl⟩
  have hvert : ∀ (i k : ℕ) (hi : i < N) (hk : k + 1 < N),
      p.1 = (i : ℝ) → (k : ℝ) ≤ p.2 → p.2 ≤ (k : ℝ) + 1 → j p ∈ G.U := by
    intro i k hi hk hp1_eq hp2_lo hp2_hi
    let u : Fin N × Fin N := (⟨i, hi⟩, ⟨k, by omega⟩)
    let v : Fin N × Fin N := (⟨i, hi⟩, ⟨k + 1, hk⟩)
    have hadj : (pathGraph N □ pathGraph N).Adj u v :=
      Or.inr ⟨pathGraph_adj.mpr (Or.inl rfl), rfl⟩
    let e : E(GM01.gridGraph N) := ⟨s(u, v), hadj⟩
    have hne : u.2 ≠ v.2 := by
      intro h
      have := congrArg Fin.val h
      dsimp [u, v] at this
      omega
    have hline : rectangularGridLine e.val = verticalLatticeLine i k := by
      change rectangularGridLinePair u v = _
      rw [rectangularGridLinePair, ite_eq_right hne]
      simp only [u, v, min_self, Nat.min_eq_left (Nat.le_succ k)]
    apply hedge_sub e
    rw [hline]
    exact ⟨p, ⟨hp1_eq, ⟨hp2_lo, hp2_hi⟩⟩, rfl⟩
  have hbd : (p.1 = (x₁ : ℝ) ∨ p.1 = (x₂ : ℝ)) ∨ (p.2 = (y₁ : ℝ) ∨ p.2 = (y₂ : ℝ)) := by
    by_contra hnot
    push Not at hnot
    exact hp_out ⟨⟨lt_of_le_of_ne hp_in.1.1 hnot.1.1.symm, lt_of_le_of_ne hp_in.1.2 hnot.1.2⟩,
      ⟨lt_of_le_of_ne hp_in.2.1 hnot.2.1.symm, lt_of_le_of_ne hp_in.2.2 hnot.2.2⟩⟩
  rcases hbd with (hp1 | hp1) | (hp2 | hp2)
  · obtain ⟨k, _, hk2, hk_lo, hk_hi⟩ := exists_nat_unit_interval_of_mem_Icc hy hp_in.2.1 hp_in.2.2
    exact hvert x₁ k (by omega) (by omega) hp1 hk_lo hk_hi
  · obtain ⟨k, _, hk2, hk_lo, hk_hi⟩ := exists_nat_unit_interval_of_mem_Icc hy hp_in.2.1 hp_in.2.2
    exact hvert x₂ k hxN (by omega) hp1 hk_lo hk_hi
  · obtain ⟨i, _, hi2, hi_lo, hi_hi⟩ := exists_nat_unit_interval_of_mem_Icc hx hp_in.1.1 hp_in.1.2
    exact hhoriz i y₁ (by omega) (by omega) hi_lo hi_hi hp2
  · obtain ⟨i, _, hi2, hi_lo, hi_hi⟩ := exists_nat_unit_interval_of_mem_Icc hx hp_in.1.1 hp_in.1.2
    exact hhoriz i y₂ (by omega) hyN hi_lo hi_hi hp2

/-- Walk along row `y` of the `N × N`-grid from column `a` to column `b = a + n`. -/
noncomputable def gridRowWalkTo {S : Type u} [TopologicalSpace S] {G : Drawing S} {N : ℕ}
    (iso : GraphMinor.Iso (GM01.gridGraph N) G.toGraph) (y b : Fin N) :
    ∀ (n a : ℕ) (ha : a < N) (_ : a + n = b.val),
      GraphWalk G.toGraph
        (iso.vertexEquiv ⟨(⟨a, ha⟩, y), mem_univ _⟩).val
        (iso.vertexEquiv ⟨(b, y), mem_univ _⟩).val
  | 0, a, ha, hab =>
      have h_eq : (⟨a, ha⟩ : Fin N) = b := Fin.ext hab
      h_eq ▸ GraphWalk.nil (iso.vertexEquiv ⟨(⟨a, ha⟩, y), mem_univ _⟩).property
  | n + 1, a, ha, hab =>
      have ha1 : a + 1 < N := by omega
      have hab1 : (a + 1) + n = b.val := by omega
      have hadj : (GM01.gridGraph N).IsLink
          s((⟨a, ha⟩, y), (⟨a + 1, ha1⟩, y)) (⟨a, ha⟩, y) (⟨a + 1, ha1⟩, y) :=
        ⟨rfl, Or.inl ⟨pathGraph_adj.mpr (Or.inl rfl), rfl⟩⟩
      have hlink : G.toGraph.IsLink
          (iso.edgeEquiv ⟨s((⟨a, ha⟩, y), (⟨a + 1, ha1⟩, y)), hadj.2⟩).val
          (iso.vertexEquiv ⟨(⟨a, ha⟩, y), mem_univ _⟩).val
          (iso.vertexEquiv ⟨(⟨a + 1, ha1⟩, y), mem_univ _⟩).val :=
        (iso.isLink_iff ⟨s((⟨a, ha⟩, y), (⟨a + 1, ha1⟩, y)), hadj.2⟩
          ⟨(⟨a, ha⟩, y), mem_univ _⟩ ⟨(⟨a + 1, ha1⟩, y), mem_univ _⟩).mp hadj
      GraphWalk.cons hlink (gridRowWalkTo iso y b n (a + 1) ha1 hab1)

theorem gridRowWalkTo_mem_support {S : Type u} [TopologicalSpace S] {G : Drawing S} {N : ℕ}
    (iso : GraphMinor.Iso (GM01.gridGraph N) G.toGraph) (y b : Fin N) :
    ∀ (n a : ℕ) (ha : a < N) (hab : a + n = b.val) {w : S},
      w ∈ (gridRowWalkTo iso y b n a ha hab).support →
      ∃ i : Fin N, a ≤ i.val ∧ i.val ≤ b.val ∧
        w = (iso.vertexEquiv ⟨(i, y), mem_univ _⟩).val
  | 0, a, ha, hab, w, hw => by
      have h_eq : (⟨a, ha⟩ : Fin N) = b := Fin.ext hab
      subst h_eq
      simp only [gridRowWalkTo, GraphWalk.support, List.mem_singleton] at hw
      exact ⟨⟨a, ha⟩, le_rfl, le_rfl, hw⟩
  | n + 1, a, ha, hab, w, hw => by
      simp only [gridRowWalkTo, GraphWalk.support, List.mem_cons] at hw
      rcases hw with rfl | hw_rest
      · exact ⟨⟨a, ha⟩, le_rfl, by change a ≤ b.val; omega, rfl⟩
      · obtain ⟨i, hi_lo, hi_hi, rfl⟩ :=
          gridRowWalkTo_mem_support iso y b n (a + 1) (by omega) (by omega) hw_rest
        exact ⟨i, by omega, hi_hi, rfl⟩

theorem gridRowWalkTo_isSimple {S : Type u} [TopologicalSpace S] {G : Drawing S} {N : ℕ}
    (iso : GraphMinor.Iso (GM01.gridGraph N) G.toGraph) (y b : Fin N) :
    ∀ (n a : ℕ) (ha : a < N) (hab : a + n = b.val),
      (gridRowWalkTo iso y b n a ha hab).IsSimple
  | 0, a, ha, hab => by
      have h_eq : (⟨a, ha⟩ : Fin N) = b := Fin.ext hab
      subst h_eq
      exact List.nodup_singleton _
  | n + 1, a, ha, hab => by
      change (GraphWalk.support _).Nodup
      simp only [gridRowWalkTo, GraphWalk.support, List.nodup_cons]
      refine ⟨?_, gridRowWalkTo_isSimple iso y b n (a + 1) (by omega) (by omega)⟩
      intro hmem
      obtain ⟨i, hi_lo, _, heq⟩ :=
        gridRowWalkTo_mem_support iso y b n (a + 1) (by omega) (by omega) hmem
      have h_inj := iso.vertexEquiv.injective (Subtype.ext heq)
      have h_fst : (⟨a, ha⟩ : Fin N) = i := congrArg (Prod.fst ∘ Subtype.val) h_inj
      have : a = i.val := congrArg Fin.val h_fst
      omega

private theorem first_box_diamond_coordinate_bounds
    {r : ℕ} :
    let a₁ : ℤ := 2 * ↑r + 2
    let b₁ : ℤ := 3 * ↑r + 2
    let c₁ : ℤ := 0
    let d₁ : ℤ := 1
    let R₁ : Set (ℝ × ℝ) := Icc ↑a₁ ↑b₁ ×ˢ Icc ↑c₁ ↑d₁
    ∀ p ∈ R₁, 2 * ↑r + 1 ≤ (diamondHomeo p).1 ∧ (diamondHomeo p).1 ≤ 3 * ↑r + 2 ∧ 2 * ↑r + 2 ≤
      (diamondHomeo p).2 ∧ (diamondHomeo p).2 ≤ 3 * ↑r + 3 := by
  intro a₁ b₁ c₁ d₁ R₁ p ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩
  change (2 * (r : ℤ) + 2 : ℤ) ≤ p.1 at hu1
  change p.1 ≤ (3 * (r : ℤ) + 2 : ℤ) at hu2
  change (0 : ℤ) ≤ p.2 at hv1
  change p.2 ≤ (1 : ℤ) at hv2
  push_cast at hu1 hu2 hv1 hv2
  dsimp [diamondHomeo]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem second_box_diamond_coordinate_bound
    {r : ℕ} :
    let a₂ : ℤ := 4 * ↑r + 2
    let b₂ : ℤ := 5 * ↑r + 2
    let c₂ : ℤ := -(2 * ↑r + 1)
    let d₂ : ℤ := -(2 * ↑r)
    let R₂ : Set (ℝ × ℝ) := Icc ↑a₂ ↑b₂ ×ˢ Icc ↑c₂ ↑d₂
    ∀ p ∈ R₂, 6 * ↑r + 2 ≤ (diamondHomeo p).1 := by
  intro a₂ b₂ c₂ d₂ R₂ p ⟨⟨hu1, _⟩, ⟨_, hv2⟩⟩
  change (4 * (r : ℤ) + 2 : ℤ) ≤ p.1 at hu1
  change p.2 ≤ (-(2 * (r : ℤ)) : ℤ) at hv2
  push_cast at hu1 hv2
  dsimp [diamondHomeo]
  linarith

private theorem diamond_box_boundaries_disjoint
    {S : Type u}
    [TopologicalSpace S]
    {r : ℕ}
    (hr : 1 ≤ r)
    (j : ℝ × ℝ → S)
    (hj : IsOpenEmbedding j)
    (R₁ : Set (ℝ × ℝ))
    (R₂ : Set (ℝ × ℝ)) (hclosed₁ : IsClosed R₁) (hclosed₂ : IsClosed R₂) :
    let F₁ : Set S := j ∘ ⇑diamondHomeo '' frontier R₁
    let F₂ : Set S := j ∘ ⇑diamondHomeo '' frontier R₂
    (∀ p ∈ R₁, 2 * ↑r + 1 ≤ (diamondHomeo p).1 ∧ (diamondHomeo p).1 ≤ 3 * ↑r + 2 ∧
      2 * ↑r + 2 ≤ (diamondHomeo p).2 ∧ (diamondHomeo p).2 ≤ 3 * ↑r + 3) →
    (∀ p ∈ R₂, 6 * ↑r + 2 ≤ (diamondHomeo p).1) →
    Disjoint F₁ F₂ := by
  intro F₁ F₂ hR₁_bounds hR₂_bounds
  rw [Set.disjoint_left]
  rintro _ ⟨p₁, hp₁, rfl⟩ ⟨p₂, hp₂, heq⟩
  have hp₁R : p₁ ∈ R₁ := hclosed₁.frontier_subset hp₁
  have hp₂R : p₂ ∈ R₂ := hclosed₂.frontier_subset hp₂
  have h_eq : diamondHomeo p₁ = diamondHomeo p₂ := hj.injective heq.symm
  have h1 := (hR₁_bounds p₁ hp₁R).2.1
  have h2 := hR₂_bounds p₂ hp₂R
  rw [← h_eq] at h2
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  linarith

/-- In the `N × N`-grid drawing (`N ≥ 7r + 3`, `r ≥ 1`), the two diamond `O`-arcs `F₁` and `F₂`
satisfy (i) and (ii) of (9.4)/(9.5): every `G`-normal `[0, 1]`-arc meeting `F₁` and `F₂` contains
at least `2r` vertices of `G`, and `k(F₁, F₂) ≥ r`. -/
theorem sphereGridMinorReduction_aux {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S)
    {G : Drawing S} {N r : ℕ} (hr : 1 ≤ r) (hN : 7 * r + 3 ≤ N)
    (hGrid : IsGridDrawing G N) :
    ∃ F₁ F₂ : Set S,
      G.IsNormal F₁ ∧ G.IsNormal F₂ ∧
      IsOArc F₁ ∧ IsOArc F₂ ∧ Disjoint F₁ F₂ ∧
      (∀ F : Set S, G.IsNormal F → IsLine F →
        (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
        2 * r ≤ (G.V ∩ F).ncard) ∧
      r ≤ maxDisjointPaths G F₁ F₂ := by
  have : T2Space S := hS.2.1
  obtain ⟨j, iso, hj, hV, hVertices, hEdges⟩ := hGrid
  let a₁ : ℤ := 2 * (r : ℤ) + 2
  let b₁ : ℤ := 3 * (r : ℤ) + 2
  let c₁ : ℤ := 0
  let d₁ : ℤ := 1
  let a₂ : ℤ := 4 * (r : ℤ) + 2
  let b₂ : ℤ := 5 * (r : ℤ) + 2
  let c₂ : ℤ := -(2 * (r : ℤ) + 1)
  let d₂ : ℤ := -(2 * (r : ℤ))
  let R₁ : Set (ℝ × ℝ) := Icc (a₁ : ℝ) (b₁ : ℝ) ×ˢ Icc (c₁ : ℝ) (d₁ : ℝ)
  let R₂ : Set (ℝ × ℝ) := Icc (a₂ : ℝ) (b₂ : ℝ) ×ˢ Icc (c₂ : ℝ) (d₂ : ℝ)
  let F₁ : Set S := (j ∘ diamondHomeo) '' frontier R₁
  let F₂ : Set S := (j ∘ diamondHomeo) '' frontier R₂
  have hab₁ : a₁ < b₁ := by dsimp [a₁, b₁]; omega
  have hcd₁ : c₁ < d₁ := by dsimp [c₁, d₁]; omega
  have hab₂ : a₂ < b₂ := by dsimp [a₂, b₂]; omega
  have hcd₂ : c₂ < d₂ := by dsimp [c₂, d₂]; omega
  obtain ⟨hO₁, hNorm₁⟩ := diamond_frontier_isOArc_and_isNormal hj hV hEdges hab₁ hcd₁
  obtain ⟨hO₂, hNorm₂⟩ := diamond_frontier_isOArc_and_isNormal hj hV hEdges hab₂ hcd₂
  have hR₁_bounds : ∀ p ∈ R₁,
      2 * (r : ℝ) + 1 ≤ (diamondHomeo p).1 ∧ (diamondHomeo p).1 ≤ 3 * (r : ℝ) + 2 ∧
      2 * (r : ℝ) + 2 ≤ (diamondHomeo p).2 ∧ (diamondHomeo p).2 ≤ 3 * (r : ℝ) + 3 := by
    exact first_box_diamond_coordinate_bounds (r := r)
  have hR₂_bounds : ∀ p ∈ R₂, 6 * (r : ℝ) + 2 ≤ (diamondHomeo p).1 := by
    exact second_box_diamond_coordinate_bound (r := r)
  have hDisj : Disjoint F₁ F₂ := by
    exact diamond_box_boundaries_disjoint (S := S) (r := r) hr j hj R₁ R₂
      (isClosed_Icc.prod isClosed_Icc) (isClosed_Icc.prod isClosed_Icc) hR₁_bounds hR₂_bounds
  refine ⟨F₁, F₂, hNorm₁, hNorm₂, hO₁, hO₂, hDisj, ?_, ?_⟩
  · -- Condition (i): every G-normal line F meeting F₁ and F₂ has ≥ 2r vertices of G
    intro F hF_norm hF_line hFF₁ hFF₂
    obtain ⟨fF⟩ := hF_line
    have hF_ends : IsLineWithEnds F (fF 0).1 (fF 1).1 := ⟨fF, rfl, rfl⟩
    have hF_pc : IsPreconnected F := (IsLineWithEnds.isConnected hF_ends).2
    let x₁ : Fin (2 * r) → ℕ := fun m => 2 * r - m.val
    let x₂ : Fin (2 * r) → ℕ := fun m => 3 * r + 4 + m.val
    let Box : Fin (2 * r) → Set (ℝ × ℝ) := fun m =>
      Icc (x₁ m : ℝ) (x₂ m : ℝ) ×ˢ Icc (x₁ m : ℝ) (x₂ m : ℝ)
    let OpenBox : Fin (2 * r) → Set (ℝ × ℝ) := fun m =>
      Ioo (x₁ m : ℝ) (x₂ m : ℝ) ×ˢ Ioo (x₁ m : ℝ) (x₂ m : ℝ)
    let BdBox : Fin (2 * r) → Set (ℝ × ℝ) := fun m => Box m \ OpenBox m
    have hex_pt : ∀ m : Fin (2 * r), ∃ p ∈ BdBox m, j p ∈ G.V ∩ F := by
      intro m
      let A : Set S := j '' Box m
      let B : Set S := (j '' OpenBox m)ᶜ
      have hA_closed : IsClosed A :=
        ((isCompact_Icc.prod isCompact_Icc).image hj.continuous).isClosed
      have hB_closed : IsClosed B :=
        (hj.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo)).isClosed_compl
      have hcov : F ⊆ A ∪ B := fun w _ => by
        by_cases hw : w ∈ j '' OpenBox m
        · exact Or.inl (image_mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hw)
        · exact Or.inr hw
      have hF₁_sub_A : F₁ ⊆ A := by
        rintro _ ⟨p, hp, rfl⟩
        have hpR : p ∈ R₁ := (isClosed_Icc.prod isClosed_Icc).frontier_subset hp
        obtain ⟨hb1, hb2, hb3, hb4⟩ := hR₁_bounds p hpR
        have hx₁_le : (x₁ m : ℝ) ≤ 2 * (r : ℝ) := by
          exact_mod_cast (Nat.sub_le (2 * r) m.val)
        have hx₂_ge : 3 * (r : ℝ) + 4 ≤ (x₂ m : ℝ) := by
          exact_mod_cast (Nat.le_add_right (3 * r + 4) m.val)
        exact ⟨diamondHomeo p, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, rfl⟩
      have hF₂_sub_B : F₂ ⊆ B := by
        rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
        have hpR : p ∈ R₂ := (isClosed_Icc.prod isClosed_Icc).frontier_subset hp
        have hb := hR₂_bounds p hpR
        have hq_eq : q = diamondHomeo p := hj.injective hqp
        have hq_hi : q.1 < (x₂ m : ℝ) := hq.1.2
        have hx₂_le : (x₂ m : ℝ) ≤ 5 * (r : ℝ) + 3 := by
          have : x₂ m ≤ 5 * r + 3 := by dsimp [x₂]; omega
          exact_mod_cast this
        rw [hq_eq] at hq_hi
        have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        linarith
      obtain ⟨w, hwF, hwAB⟩ := preconnected_inter_nonempty_of_closed_cover hF_pc
        hA_closed hB_closed hcov (hFF₁.mono (inter_subset_inter_right F hF₁_sub_A))
        (hFF₂.mono (inter_subset_inter_right F hF₂_sub_B))
      obtain ⟨⟨p, hpBox, rfl⟩, hpNotOpen⟩ := hwAB
      have hpOpen : p ∉ OpenBox m := fun h => hpNotOpen ⟨p, h, rfl⟩
      have hjpU : j p ∈ G.U := box_boundary_subset_grid_U hEdges
        (by dsimp [x₁, x₂]; omega) (by dsimp [x₂]; omega)
        (by dsimp [x₁, x₂]; omega) (by dsimp [x₂]; omega) hpBox hpOpen
      exact ⟨p, ⟨hpBox, hpOpen⟩, hF_norm ⟨hwF, hjpU⟩, hwF⟩
    choose p hp_bd hp_VF using hex_pt
    have hsub_VF : range (j ∘ p) ⊆ G.V ∩ F := by
      rintro _ ⟨m, rfl⟩
      exact hp_VF m
    have hinj_jp : Injective (j ∘ p) := by
      intro m₁ m₂ heq
      have hp_eq : p m₁ = p m₂ := hj.injective heq
      by_contra hne
      have hlt_or : m₁.val < m₂.val ∨ m₂.val < m₁.val :=
        lt_or_gt_of_ne (Fin.val_ne_of_ne hne)
      have hsub_open : ∀ a b : Fin (2 * r), a.val < b.val → Box a ⊆ OpenBox b := by
        intro a b hab q ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩
        have hx₁_lt : (x₁ b : ℝ) < (x₁ a : ℝ) := by
          have : x₁ b < x₁ a := by dsimp [x₁]; omega
          exact_mod_cast this
        have hx₂_lt : (x₂ a : ℝ) < (x₂ b : ℝ) := by
          have : x₂ a < x₂ b := by dsimp [x₂]; omega
          exact_mod_cast this
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      rcases hlt_or with hlt | hlt
      · exact (hp_bd m₂).2 (hp_eq ▸ hsub_open m₁ m₂ hlt (hp_bd m₁).1)
      · exact (hp_bd m₁).2 (hp_eq.symm ▸ hsub_open m₂ m₁ hlt (hp_bd m₂).1)
    have hcard_range : (range (j ∘ p)).ncard = 2 * r := by
      rw [← image_univ, ncard_image_of_injective _ hinj_jp, ncard_univ, Nat.card_fin]
    exact hcard_range ▸ ncard_le_ncard hsub_VF (G.finite_V.inter_of_left F)
  · -- Condition (ii): r ≤ maxDisjointPaths G F₁ F₂
    apply le_csSup ⟨G.V.ncard, fun _ hk => hasDisjointPathsBetween_le_ncard_V hk⟩
    let rowIdx : Fin r → Fin N := fun k => ⟨2 * r + 2 + k.val, by omega⟩
    let startCol : Fin r → Fin N := fun k => ⟨2 * r + 2 + k.val, by omega⟩
    let endCol : Fin r → Fin N := fun k => ⟨6 * r + 2 + k.val, by omega⟩
    let W : ∀ k : Fin r,
        GraphWalk G.toGraph
          (iso.vertexEquiv ⟨(startCol k, rowIdx k), mem_univ _⟩).val
          (iso.vertexEquiv ⟨(endCol k, rowIdx k), mem_univ _⟩).val :=
      fun k => gridRowWalkTo iso (rowIdx k) (endCol k) (4 * r) (2 * r + 2 + k.val)
        (by omega) (by dsimp [endCol]; omega)
    let P : Fin r → Drawing S := fun k => walkDrawing G (W k)
    let s : Fin r → S := fun k => (iso.vertexEquiv ⟨(startCol k, rowIdx k), mem_univ _⟩).val
    let t : Fin r → S := fun k => (iso.vertexEquiv ⟨(endCol k, rowIdx k), mem_univ _⟩).val
    refine ⟨P, s, t, ?_, ?_⟩
    · intro k
      refine ⟨walkDrawing_isSubdrawing G (W k), ?_, ?_,
        walkDrawing_isPathBetween G (gridRowWalkTo_isSimple iso (rowIdx k) (endCol k)
          (4 * r) (2 * r + 2 + k.val) (by omega) (by dsimp [endCol]; omega))⟩
      · -- s k ∈ F₁
        have hs_eq : s k = j (rectangularGridPoint (startCol k, rowIdx k)) :=
          hVertices ⟨(startCol k, rowIdx k), mem_univ _⟩
        rw [hs_eq]
        let p₁ : ℝ × ℝ := ((2 * r + 2 + k.val : ℝ), 0)
        have hp₁_in : p₁ ∈ R₁ := by
          refine ⟨⟨?_, ?_⟩, ⟨by dsimp [p₁, c₁]; norm_num, by dsimp [p₁, d₁]; norm_num⟩⟩
          · dsimp [p₁, a₁]; push_cast; linarith
          · have : k.val ≤ r := le_of_lt k.isLt
            have hk_le : (k.val : ℝ) ≤ (r : ℝ) := by exact_mod_cast this
            dsimp [p₁, b₁]; push_cast; linarith
        have hp₁_out : p₁ ∉ interior R₁ := by
          rw [interior_prod_eq, interior_Icc, interior_Icc]
          intro h
          have : (c₁ : ℝ) < p₁.2 := h.2.1
          dsimp [p₁, c₁] at this
          norm_num at this
        have h_img : diamondHomeo p₁ = rectangularGridPoint (startCol k, rowIdx k) := by
          ext <;> dsimp [diamondHomeo, p₁, rectangularGridPoint, latticePoint, startCol, rowIdx] <;>
            push_cast <;> ring
        exact ⟨p₁, ⟨subset_closure hp₁_in, hp₁_out⟩, congrArg j h_img⟩
      · -- t k ∈ F₂
        have ht_eq : t k = j (rectangularGridPoint (endCol k, rowIdx k)) :=
          hVertices ⟨(endCol k, rowIdx k), mem_univ _⟩
        rw [ht_eq]
        let p₂ : ℝ × ℝ := ((4 * r + 2 + k.val : ℝ), -(2 * (r : ℝ)))
        have hp₂_in : p₂ ∈ R₂ := by
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
          · dsimp [p₂, a₂]; push_cast; linarith
          · have : k.val ≤ r := le_of_lt k.isLt
            have hk_le : (k.val : ℝ) ≤ (r : ℝ) := by exact_mod_cast this
            dsimp [p₂, b₂]; push_cast; linarith
          · dsimp [p₂, c₂]; push_cast; linarith
          · dsimp [p₂, d₂]; push_cast; linarith
        have hp₂_out : p₂ ∉ interior R₂ := by
          rw [interior_prod_eq, interior_Icc, interior_Icc]
          intro h
          have : p₂.2 < (d₂ : ℝ) := h.2.2
          dsimp [p₂, d₂] at this
          push_cast at this
          linarith
        have h_img : diamondHomeo p₂ = rectangularGridPoint (endCol k, rowIdx k) := by
          ext <;> dsimp [diamondHomeo, p₂, rectangularGridPoint, latticePoint, endCol, rowIdx] <;>
            push_cast <;> ring
        exact ⟨p₂, ⟨subset_closure hp₂_in, hp₂_out⟩, congrArg j h_img⟩
    · -- Pairwise vertex-disjointness of P k₁ and P k₂ for k₁ ≠ k₂
      intro k₁ k₂ hne
      rw [Set.disjoint_left]
      intro w hw₁ hw₂
      have hw₁_supp : w ∈ (W k₁).support := by
        have : w ∈ (P k₁).V := hw₁
        rwa [walkDrawing_V G (W k₁)] at this
      have hw₂_supp : w ∈ (W k₂).support := by
        have : w ∈ (P k₂).V := hw₂
        rwa [walkDrawing_V G (W k₂)] at this
      obtain ⟨i₁, _, _, heq₁⟩ := gridRowWalkTo_mem_support iso (rowIdx k₁) (endCol k₁)
        (4 * r) (2 * r + 2 + k₁.val) (by omega) (by dsimp [endCol]; omega) hw₁_supp
      obtain ⟨i₂, _, _, heq₂⟩ := gridRowWalkTo_mem_support iso (rowIdx k₂) (endCol k₂)
        (4 * r) (2 * r + 2 + k₂.val) (by omega) (by dsimp [endCol]; omega) hw₂_supp
      have h_inj := iso.vertexEquiv.injective (Subtype.ext (heq₁.symm.trans heq₂))
      have h_snd : rowIdx k₁ = rowIdx k₂ := congrArg (Prod.snd ∘ Subtype.val) h_inj
      have : 2 * r + 2 + k₁.val = 2 * r + 2 + k₂.val := congrArg Fin.val h_snd
      exact hne (Fin.ext (by omega))

/-- **Graph Minors VII, proof of (9.6) from (9.5)** (page 246):
In a sufficiently large `N × N`-grid drawn on a sphere `Σ`, there exist two disjoint `G`-normal
`O`-arcs `F₁, F₂` satisfying conditions (i) and (ii) of (9.4)/(9.5) with
`r = rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)`. -/
theorem sphereGridMinorReduction :
    ∀ (S : Type u) [TopologicalSpace S],
      IsSurface S →
      ∀ H : SurfaceDigraph S,
        ∃ N₀ : ℕ, ∀ (N : ℕ) (G : SurfaceDigraph S),
          N₀ ≤ N → IsGridDrawing G.G N →
          ∃ F₁ F₂ : Set S,
            G.G.IsNormal F₁ ∧ G.G.IsNormal F₂ ∧
            IsOArc F₁ ∧ IsOArc F₂ ∧ Disjoint F₁ F₂ ∧
            (∀ F : Set S, G.G.IsNormal F → IsLine F →
              (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
              2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard) ∧
            rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂ := by
  intro S _ hS H
  let t := H.G.V.ncard + H.G.E.ncard
  let r := rCylinderBound H.G * 5 ^ t
  have hr : 1 ≤ r := by
    have hv : 1 ≤ vModel 0 0 (t + 4) (2 * t + 4) := by unfold vModel; omega
    have hrC : 1 ≤ rCylinderBound H.G := by
      unfold rCylinderBound
      dsimp
      have : 1 * 1 ≤ (84 * (t + 2)) * vModel 0 0 (t + 4) (2 * t + 4) :=
        Nat.mul_le_mul (by omega) hv
      omega
    have hpow : 1 ≤ 5 ^ t := Nat.one_le_pow t 5 (by decide)
    exact le_trans (by decide : 1 ≤ 1 * 1) (Nat.mul_le_mul hrC hpow)
  exact ⟨7 * r + 3, fun N G hN hGrid => sphereGridMinorReduction_aux hS hr hN hGrid⟩

end GraphMinor.GM07
