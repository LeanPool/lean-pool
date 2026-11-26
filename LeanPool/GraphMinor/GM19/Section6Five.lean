/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Comp
public import LeanPool.GraphMinor.GM19.Section6Tri
public import LeanPool.GraphMinor.GM19.Conditional

import LeanPool.GraphMinor.GM19.Section6aProved

/-!
# Graph Minors XIX, (6.5)

We prove (6.5) (page 341) from (6.4), as the paper does (`theorem_6_5`). The drawing `H` is a
triangulation of the surface (`exists_triang_drawing`). By (6.4) it has an enlargement in `G`, and
so in `G'`. By (6.3) it is isomorphic to a drawing `H'` with `rep(H') ≤ rep(G')`. If `rep(H') = 0`
then a curve misses `U(H')`, and `edges_lt_of_curve` gives too few edges.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

theorem exists_curve_of_rep_lt {G : Drawing S} {k : ℕ∞} (h : G.rep < k) :
    ∃ F, IsOArc F ∧ G.IsNormal F ∧ ¬ IsNullHomotopicOArc F ∧ ((F ∩ G.V).ncard : ℕ∞) < k := by
  obtain ⟨n, ⟨F, h1, h2, h3, rfl⟩, h4⟩ := sInf_lt_iff.mp h
  exact ⟨F, h1, h2, h3, h4⟩

/-- Isomorphic drawings: the facts we need on `H'`. -/
theorem isIso_facts {H H' : Drawing S}
  (hiso : H.IsIsomorphic H') (hs : ∀ e ∈ H.E, ∀ f ∈ H.E, tilde e = tilde f → e = f)
    (hc : ∀ v ∈ H.V, ConnIn H (H.V \ {v})) :
    H'.V.ncard = H.V.ncard ∧ H'.E.ncard = H.E.ncard ∧ (∀ e ∈ H'.E, ∀ f ∈ H'.E, tilde e = tilde f
      → e = f) ∧ ∀ v ∈ H'.V, ConnIn H' (H'.V \ {v}) := by
  obtain ⟨βv, βe, hbv, hbe, hinc⟩ := hiso
  have ht : ∀ e ∈ H.E, tilde (βe e) = βv '' tilde e := fun e he => by
    have h1 : tilde e ⊆ H.V := fun x hx => by
      rw [tilde_eq_inter_V H he] at hx
      exact hx.2
    have h2 : tilde (βe e) ⊆ H'.V := fun x hx => by
      rw [tilde_eq_inter_V H' (hbe.mapsTo he)] at hx
      exact hx.2
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hbv.surjOn (h2 hy)
      exact ⟨x, (hinc x hx e he).mpr hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hinc x (h1 hx) e he).mp hx
  refine ⟨by rw [← hbv.image_eq, hbv.injOn.ncard_image], by rw [← hbe.image_eq,
    hbe.injOn.ncard_image], ?_, ?_⟩
  · intro e' he' f' hf' hef
    obtain ⟨e, he, rfl⟩ := hbe.surjOn he'
    obtain ⟨f, hf, rfl⟩ := hbe.surjOn hf'
    rw [ht e he, ht f hf] at hef
    have h1 : tilde e ⊆ H.V := fun x hx => by
      rw [tilde_eq_inter_V H he] at hx
      exact hx.2
    have h2 : tilde f ⊆ H.V := fun x hx => by
      rw [tilde_eq_inter_V H hf] at hx
      exact hx.2
    rw [hs e he f hf ((hbv.injOn.image_eq_image_iff h1 h2).mp hef)]
  · intro v' hv' Y hY hne hcl
    obtain ⟨v, hv, rfl⟩ := hbv.surjOn hv'
    obtain ⟨y₀, hy₀⟩ := hne
    obtain ⟨x₀, hx₀, rfl⟩ := hbv.surjOn (hY hy₀).1
    have hx₀v : x₀ ≠ v := fun h' => (hY hy₀).2 (h' ▸ rfl)
    have hY₀ := hc v hv {x | x ∈ H.V \ {v} ∧ βv x ∈ Y} (fun x hx => hx.1) ⟨x₀, ⟨hx₀, hx₀v⟩, hy₀⟩ (by
      rintro a ⟨ha, haY⟩ b hb ⟨hab, -, -, e, he, hae, hbe'⟩
      refine ⟨hb, hcl _ haY _ ⟨hbv.mapsTo hb.1, fun h' => hb.2 (hbv.injOn hb.1 hv h')⟩ ⟨fun h'
        => hab (hbv.injOn ha.1 hb.1 h'), hbv.mapsTo ha.1, hbv.mapsTo hb.1, βe e, hbe.mapsTo he, ?_,
          ?_⟩⟩
      · exact (hinc a ha.1 e he).mp hae
      · exact (hinc b hb.1 e he).mp hbe')
    refine Subset.antisymm hY fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hbv.surjOn hy.1
    have hxv : x ≠ v := fun h' => hy.2 (h' ▸ rfl)
    have h1 : x ∈ {x | x ∈ H.V \ {v} ∧ βv x ∈ Y} := hY₀.symm ▸ (⟨hx, hxv⟩ : x ∈ H.V \ {v})
    exact h1.2

/-- **Graph Minors XIX, (6.5)** (page 341): "For every surface $\Sigma$ with $bd(\Sigma) =
\emptyset$, not a sphere, there is a number
$k\ge 0$ such that if $G$ is a drawing in $\Sigma$ with $rep(G)\ge k$ and $G'$ is a drawing
in $\Sigma$ such that there is an enlargement of $G$ in $G'$, then $rep(G')\ge 1$." -/
def Theorem65Statement : Prop :=
  ∀ (S : Type) [TopologicalSpace S], IsSurface S → ConnectedSpace S → bd S = ∅ → ¬ IsSphere S →
    ∃ k : ℕ, ∀ G : Drawing S, G.IsGM19Drawing → (k : ℕ∞) ≤ G.rep → ∀ G' : Drawing S,
      G'.IsGM19Drawing →
      ∀ (σv : S → Drawing S) (σe : Set S → Set S), IsEnlargement G G' σv σe → 1 ≤ G'.rep

/-- A drawing with an enlargement of the triangulation has `rep ≥ 1`. -/
theorem rep_pos_of_enlargement (hT : IsClosedSurface S) [ConnectedSpace S] {H G' : Drawing S}
  (hl : LoopFree H) (hs : ∀ e ∈ H.E, ∀ f ∈ H.E, tilde e = tilde f → e = f)
    (h3V : 3 ≤ H.V.ncard) (h3E : 3 ≤ H.E.ncard) (hc : ∀ v ∈ H.V, ConnIn H (H.V \ {v})) {κ : ℕ}
      (hκ : Nat.card (KCl S (ZMod 2)) = 2 ^ κ)
    (hE : (H.E.ncard : ℤ) = 3 * H.V.ncard - 6 + 3 * κ) (hG' : G'.IsGM19Drawing) {σv : S
      → Drawing S} {σe : Set S → Set S}
    (hσ : IsEnlargement H G' σv σe) : 1 ≤ G'.rep := by
  have ht2 : T2Space S := hT.2.1
  have hb : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hT.2.2 x)
  have hH : H.IsGM19Drawing := gm19_of_loopFree hb hl
  obtain ⟨H', hH', hiso, hle⟩ := theorem_6_3_proof hT hb hH hG' hσ
  have hl' := loopFree_of_gm19 hH'
  obtain ⟨hV, hE', hs', hc'⟩ := isIso_facts hiso hs hc
  by_contra hlt
  have hlt' : H'.rep < 1 := lt_of_le_of_lt hle (not_le.mp hlt)
  obtain ⟨F, hO, hnorm, hnull, hcount⟩ := exists_curve_of_rep_lt hlt'
  have h0 : (F ∩ H'.V).ncard = 0 := by
    have : ((F ∩ H'.V).ncard : ℕ∞) < ((1 : ℕ) : ℕ∞) := by exact_mod_cast hcount
    have := Nat.cast_lt.mp this
    omega
  have he : F ∩ H'.V = ∅ := (ncard_eq_zero (H'.finite_V.subset inter_subset_right)).mp h0
  have hd : Disjoint H'.U F := disjoint_left.mpr fun x hxU hxF => by
    have h1 : x ∈ F ∩ H'.V := ⟨hxF, hnorm ⟨hxF, hxU⟩⟩
    rw [he] at h1
    exact h1
  have hnn : ¬ ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F := by
    rintro ⟨Δ, hΔ, hbd⟩
    have hdisc := (epstein S univ F hT.isSurface ‹_› hO (subset_univ _) (by simp [hb])).2.1
    exact hnull (hdisc ⟨Δ, subset_univ _, hΔ, hbd ▸ discBd_subset Δ⟩)
  have hlt₂ := edges_lt_of_curve hT H' hl' hs' (by omega) (by omega) hc' hO hnn hd hκ
  rw [hV, hE'] at hlt₂
  omega

/-- **Graph Minors XIX, (6.5)**, from (6.4). -/
theorem theorem_6_5_proof : Theorem65Statement := by
  intro S _ hS hconn hb hsph
  have ht2 : T2Space S := hS.2.1
  have hT : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x => by
    by_contra hx
    have : x ∈ bd S := hx
    rw [hb] at this
    exact this⟩
  obtain ⟨H, hl, hs, h3V, h3E, hc, κ, hκ, hE⟩ := exists_triang_drawing hT
  have hH : H.IsGM19Drawing := gm19_of_loopFree hb hl
  obtain ⟨k, hk⟩ := GraphMinor.GM19.theorem_6_4_proof.{0} S hS hconn hb hsph H hH
  refine ⟨k, fun G hG hrep G' hG' σv σe hσ => ?_⟩
  obtain ⟨τv, τe, hτ⟩ := hk G hG hrep
  obtain ⟨ρv, hρ, -⟩ := IsEnlargement.comp (loopFree_of_gm19 hG) (loopFree_of_gm19 hG') hτ hσ
  exact rep_pos_of_enlargement hT hl hs h3V h3E hc hκ hE hG' hρ

end GraphMinor.GM19
