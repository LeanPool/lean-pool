/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section5
public import LeanPool.GraphMinor.GM07.CuffStep
public import LeanPool.GraphMinor.GM07.CuffFinal
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# Graph Minors VII, Section 6: Allowing Smaller Cuffs

This file formalizes Section 6 (pages 237–238) of N. Robertson and P. D. Seymour,
*Graph Minors. VII. Disjoint paths on a surface*, J. Combin. Theory Ser. B 45 (1988) 212–254:
- `ncard_small_cuffs_le`: `{C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard ≤ c`;
- `theorem_6_1_general`: proof by induction on `g = {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard`
  that `IsGFeasibleProper G H` holds whenever `(G.V ∩ bd S).ncard ≤ 2 * k - 2 * g`, using
  `theorem_5_9` in the base case `g = 0` and `smallCuffReductionStep` in the inductive
  step `g = g₀ + 1`;
- `(6.1)` (`theorem_6_1`): third version of the main feasibility theorem, removing the condition
  `|V(G) ∩ C| ≥ 2` for each cuff `C`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- On a surface `S ≃ₜ SurfaceModel a b c`, the number `g` of cuffs `C` of `S` with
`(G.V ∩ C).ncard ≤ 1` is at most `c`. -/
theorem ncard_small_cuffs_le (hS : IsSurface S) {a b c : ℕ}
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) (G : Drawing S) :
    {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard ≤ c := by
  have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
  calc
    {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard
      ≤ (cuffs S).ncard := ncard_le_ncard (fun _ h => h.1) hfin
    _ = c := ncard_cuffs_of_homeomorph_surfaceModel he

/-- A forest with no vertex on the boundary is feasible: only paths between boundary vertices count,
so it is homotopic to the empty forest. -/
theorem isGFeasible_of_no_boundary_vertices [T1Space S] {G H : Drawing S}
    (hH : IsSurfaceForest H)
    (hb : H.V ∩ bd S = ∅) : IsGFeasible G H := by
  have hE : (G.span ∅ ∅).E = ∅ := by
    rw [Drawing.span_E, empty_inter]
  have hV : (G.span ∅ ∅).V = ∅ := by
    rw [Drawing.span_V, Drawing.spanV]
    simp
  have hU : (G.span ∅ ∅).U = ∅ := by
    rw [Drawing.span_U, Drawing.spanU, Drawing.spanV]
    simp
  have hF : IsSurfaceForest (G.span ∅ ∅) := by
    refine ⟨?_, fun u W _ => ?_⟩
    · rintro x ⟨-, hx⟩
      rw [hU] at hx
      exact hx.elim
    · cases W with
      | nil hv => rfl
      | cons hlink _ =>
        have := hlink.1
        rw [hE] at this
        exact this.elim
  refine ⟨G.span ∅ ∅, hF, ⟨Homeomorph.refl S, fun _ _ => rfl, ?_⟩, Drawing.span_isSubdrawing _ _ _⟩
  rw [mapDrawingHomeo_refl]
  refine ⟨hH.1, hF.1, hH.2, hF.2, ?_, fun s hs => ?_⟩
  · rw [hb, hV, empty_inter]
  · rw [hb] at hs
    exact hs.elim

/-- General form of Graph Minors VII, (6.1) (pages 237–238), proved by induction on
`g = {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard` under the weaker hypothesis
`|V(G) ∩ bd(Σ)| ≤ 2k - 2g`. -/
theorem theorem_6_1_general
    {a b c k g : ℕ} (hc : 2 ≤ c) (hne : (a, b, c) ≠ (0, 0, 2)) :
    ∀ (S : Type u) [TopologicalSpace S] [T1Space S],
      IsSurface S → Nonempty (S ≃ₜ SurfaceModel a b c) →
      ∀ (G H : Drawing S),
        IsBoundaryLinked G →
        {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard = g →
        (G.V ∩ bd S).ncard ≤ 2 * k - 2 * g →
        9 * k * vSurface S k < alpha G →
        IsSurfaceForest H → G.V ∩ bd S = H.V ∩ bd S →
        IsGFeasible G H := by
  induction g with
  | zero =>
    intro S _ _ hS he G H hBL hg0 hbd_card halpha hH hbd_eq
    have hfin_cuffs : (cuffs S).Finite := (cuff_statement S hS).2.1
    have hfin_small : {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.Finite :=
      hfin_cuffs.subset (fun _ h => h.1)
    have hempty : {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1} = ∅ :=
      (ncard_eq_zero hfin_small).mp hg0
    have hcuff2 : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard := by
      intro C hC
      by_contra hlt
      have hle1 : (G.V ∩ C).ncard ≤ 1 := by omega
      have hmem : C ∈ {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1} := ⟨hC, hle1⟩
      rw [hempty] at hmem
      exact hmem
    have hbd_card' : (G.V ∩ bd S).ncard ≤ 2 * k := by omega
    exact theorem_5_9_proof hS hc hne he k G H hBL hbd_card' halpha hcuff2 hH hbd_eq
  | succ g₀ ih =>
    intro S _ _ hS he G H hBL hg_succ hbd_card halpha hH hbd_eq
    by_cases hk : g₀ + 1 ≤ k
    swap
    · -- When the bound is negative, the boundary has no vertices.
      have hb0 : (G.V ∩ bd S).ncard = 0 := by omega
      have hempty : G.V ∩ bd S = ∅ := (ncard_eq_zero (G.finite_V.subset inter_subset_left)).mp hb0
      exact isGFeasible_of_no_boundary_vertices hH (hbd_eq ▸ hempty)
    obtain ⟨S', tS', t1S', G', H', hS', he', hBL', hg₀', hbd_card', halpha', hH', hbd_eq', himp⟩ :=
      smallCuffReductionStep S hS a b c hc hne he k g₀ G H hk hBL hg_succ hbd_card halpha hH hbd_eq
    exact himp (@ih S' tS' t1S' hS' he' G' H' hBL' hg₀' hbd_card' halpha' hH' hbd_eq')

/-- Graph Minors VII, (6.1) (pages 237–238):
"(6.1) *Let $\Sigma \cong \Sigma(a, b, c)$, where $c \ge 2$ and $(a, b, c) \ne (0, 0, 2)$. Let
$k \ge 0$ be an integer. Let $G$ be a boundary-linked proper graph in $\Sigma$ with
$|V(G) \cap bd(\Sigma)| \le 2k - 2c$ and with $\alpha(G) > 9kv(\Sigma, k)$. Let $H$ be a forest in
$\Sigma$ with $V(G) \cap bd(\Sigma) = V(H) \cap bd(\Sigma)$. Then $H$ is $G$-feasible.*" -/
theorem theorem_6_1_proof
    [T1Space S] (hS : IsSurface S) {a b c : ℕ} (hc : 2 ≤ c) (hne : (a, b, c) ≠ (0, 0, 2))
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (k : ℕ) (G H : Drawing S)
    (hBL : IsBoundaryLinked G)
    (hbd_card : (G.V ∩ bd S).ncard ≤ 2 * k - 2 * c)
    (halpha : 9 * k * vSurface S k < alpha G)
    (hH : IsSurfaceForest H) (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by
  have hg_le_c : {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard ≤ c :=
    ncard_small_cuffs_le hS he G
  have hbd_card_g :
      (G.V ∩ bd S).ncard ≤ 2 * k - 2 * {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard := by
    omega
  exact theorem_6_1_general hc hne S hS he G H hBL rfl
    hbd_card_g halpha hH hbd_eq

end GraphMinor.GM07
