/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Graph
public import LeanPool.GraphMinor.GM19.Section6Cut

/-!
# Graphs that a curve misses

Let `D` be a drawing in a connected closed surface `S`, with no loops and no parallel edges, in
which no vertex cuts the graph. If an `O`-arc that bounds no closed disc misses `U(D)`, then `D` has
fewer edges than a triangulation of `S` with the same number of vertices (`edges_lt_of_curve`).

This is the count of Euler characteristics in the proof of Graph Minors XIX, (6.5) (page 341). We
cut along the curve with `exists_simpler_side`, extend the image of `D` to a triangulation of the
new surface, and count with `IsTriang.graph_bound`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

local notation "K" => ZMod 2

variable {S : Type} [TopologicalSpace S]

theorem twoConn_image {T : Type} [TopologicalSpace T] {Z : Set S} (h : TwoConn Z)
  (hZ : IsPreconnected Z) {ι : S → T} (hc : ContinuousOn ι Z) (hi : InjOn ι Z) :
    TwoConn (ι '' Z) := fun p => by
  by_cases hp : p ∈ ι '' Z
  · obtain ⟨x, hx, rfl⟩ := hp
    have he : ι '' Z \ {ι x} = ι '' (Z \ {x}) := by
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hne⟩
        exact ⟨z, ⟨hz, fun h' => hne (h' ▸ rfl)⟩, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz.1, rfl⟩, fun h' => hz.2 (hi hz.1 hx h')⟩
    rw [he]
    exact (h x).image _ (hc.mono sdiff_subset)
  · rw [sdiff_singleton_eq_self hp]
    exact hZ.image _ hc

/-- **The count.** See the module docstring. -/
theorem edges_lt_of_curve (hT : IsClosedSurface S) [ConnectedSpace S] (D : Drawing S)
  (hl : LoopFree D) (hs : ∀ e ∈ D.E, ∀ f ∈ D.E, tilde e = tilde f → e = f)
    (h3V : 3 ≤ D.V.ncard) (h3E : 3 ≤ D.E.ncard) (hc : ∀ v ∈ D.V, ConnIn D (D.V \ {v})) {F : Set S}
      (hO : IsOArc F) (hnn : ¬ ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F)
    (hd : Disjoint D.U F) {κ : ℕ} (hκ : Nat.card (KCl S K) = 2 ^ κ) :
      (D.E.ncard : ℤ) < 3 * D.V.ncard - 6 + 3 * κ := by
  have ht2S : T2Space S := hT.2.1
  have hTC := twoConn_U D hl h3V hc
  obtain ⟨φ⟩ := id hO
  have hpF : (φ 1).1 ∉ D.U := fun h => disjoint_left.mp hd h (φ 1).2
  have hZ : IsPreconnected D.U := by
    have := hTC (φ 1).1
    rwa [sdiff_singleton_eq_self hpF] at this
  obtain ⟨T, tT, cT, ι, ι', hT₁, hιc, -, hleft, hlt⟩ := exists_simpler_side hT hO hnn hZ hd
  have ht2T : T2Space T := hT₁.2.1
  have hne : Nonempty T := cT.toNonempty
  have hinj : InjOn ι D.U := hleft.injOn
  have hg := isGraph_of_loopFree D hl
  have hgU : gr D.V (closure '' D.E) = D.U := (U_eq D).symm
  have hg₁ := isGraph_image hg hgU.subset hιc hinj
  have hVU : D.V ∪ ⋃₀ (closure '' D.E) = ⋃₀ (closure '' D.E) := union_eq_right.mpr
    (V_subset_edges D h3V hc)
  have hUe : D.U = ⋃₀ (closure '' D.E) := by rw [U_eq D, hVU]
  have hU₁ : ⋃₀ ((fun e => ι '' e) '' (closure '' D.E)) = ι '' D.U := by
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨e, he, rfl⟩, rfl⟩, x, hx, rfl⟩
      exact ⟨x, D.closure_subset_U he hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hUe] at hx
      obtain ⟨_, ⟨e, he, rfl⟩, hxe⟩ := hx
      exact ⟨_, ⟨_, ⟨e, he, rfl⟩, rfl⟩, x, hxe, rfl⟩
  have hno : ι '' D.V ⊆ ⋃₀ ((fun e => ι '' e) '' (closure '' D.E)) := by
    rw [hU₁]
    exact image_mono D.V_subset_U
  have hTC₁ := twoConn_image hTC hZ hιc hinj
  have hV₁ : (ι '' D.V).ncard = D.V.ncard := (hinj.mono D.V_subset_U).ncard_image
  obtain ⟨a, b, d, ha, hb, hd', hab, had, hbd⟩ := (two_lt_ncard_iff D.finite_V).mp
    (show 2 < D.V.ncard by omega)
  have hinj' : ∀ {x y}, x ∈ D.V → y ∈ D.V → x ≠ y → ι x ≠ ι y := fun hx hy hxy he => hxy (hinj
    (D.V_subset_U hx) (D.V_subset_U hy) he)
  obtain ⟨V₂, E₂, 𝓕₂, hsubV, hsubU, hdis⟩ := exists_dissection hT₁ hg₁ hno (𝓒c := {ι '' D.U})
    (finite_singleton _)
    (by rintro _ rfl; exact hTC₁)
    (by
      rintro _ rfl
      exact ⟨ι a, ι b, ι d, ⟨a, D.V_subset_U ha, rfl⟩, ⟨b, D.V_subset_U hb, rfl⟩, ⟨d,
        D.V_subset_U hd', rfl⟩, hinj' ha hb hab, hinj' ha hd' had, hinj' hb hd' hbd⟩)
    (by
      intro G hG hmeet
      obtain ⟨x, y, hx, hy, hxy⟩ := hmeet _ rfl
      rw [hU₁]
      exact hG.union hTC₁ hx hy hxy)
  obtain ⟨V₃, E₃, 𝓕₃, htr, hV₃, hU₃, -⟩ := hdis.exists_triang
  have hE₁ : ((fun e => ι '' e) '' (closure '' D.E)).ncard = D.E.ncard := by
    have h1 : InjOn closure D.E := fun e he f hf hef => by
      rw [← D.closure_diff_V he, ← D.closure_diff_V hf]
      exact congrArg (· \ D.V) hef
    have h2 : InjOn (fun e => ι '' e) (closure '' D.E) := by
      rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ hef
      exact (hinj.image_eq_image_iff (D.closure_subset_U he) (D.closure_subset_U hf)).mp hef
    rw [h2.ncard_image, h1.ncard_image]
  have hle := htr.graph_bound hT₁ hg₁ (fun y hy => hV₃ ⟨hsubV hy, hsubU (hno hy)⟩)
    (hsubU.trans hU₃) (by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩ _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ hef
    have h5 : ∀ {g}, g ∈ D.E → ι '' closure g ∩ ι '' D.V = ι '' tilde g := fun {g} hg' => by
      rw [tilde_eq_inter_V D hg', hinj.image_inter (D.closure_subset_U hg') D.V_subset_U]
    have hsub_e : tilde e ⊆ D.U := fun _ hx => D.closure_subset_U he hx.1
    have hsub_f : tilde f ⊆ D.U := fun _ hx => D.closure_subset_U hf hx.1
    have h6 := hs e he f hf ((hinj.image_eq_image_iff hsub_e hsub_f).mp
      ((h5 he).symm.trans (hef.trans (h5 hf))))
    rw [h6]) (by rw [hE₁]; exact h3E)
  obtain ⟨κ₁, h1, h2⟩ := htr.euler_ncard hT₁
  have h4 := hlt κ κ₁ hκ h1
  rw [hE₁, hV₁] at hle
  omega

end GraphMinor.GM19
