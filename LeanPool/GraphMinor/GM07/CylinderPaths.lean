/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.SideDisc
public import LeanPool.GraphMinor.GM16.DrawingSkeletonPaths
public import LeanPool.GraphMinor.Menger.Basic
public import LeanPool.GraphMinor.Thomas.Separator

/-!
# Disjoint paths across a cylinder

Graph Minors VII, (5.8), condition (i) says that every `O`-arc that is normal, not null-homotopic,
meets the graph in at least `r` vertices. The paper gets the `r` paths from this
in one word, by Menger's theorem. Here `exists_cylinder_paths` is that step in a sphere with two
disjoint discs. A vertex set `X` that separates the discs gives, by
`exists_disc_of_side`, a closed disc about the first disc whose boundary meets the drawing inside
`X`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- **Menger's theorem across a cylinder.** -/
theorem exists_cylinder_paths (hS : IsClosedSurface T) (hsph : IsSphere T)
  (Γ : Drawing T) {D₁ D₂ : Set T} (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂)
    (hd : Disjoint D₁ D₂)
    (hU₁ : Γ.U ∩ D₁ ⊆ Γ.V) (hi₁ : Disjoint Γ.U (discInt D₁)) (hU₂ : Γ.U ∩ D₂ ⊆ Γ.V)
      (hi₂ : Disjoint Γ.U (discInt D₂)) {r : ℕ}
    (hi : ∀ B, IsClosedDisc B → D₁ ⊆ B → Disjoint (discInt D₂) B → discBd B ∩ Γ.U ⊆ Γ.V → r ≤
      (discBd B ∩ Γ.U).ncard) :
    ∃ (P : Fin r → Drawing T) (u v : Fin r → T), (∀ i, (P i).IsSubdrawing Γ ∧ u i ∈ D₁ ∧ v i ∈ D₂ ∧
      (P i).IsPathBetween (u i) (v i)) ∧ ∀ i i', i ≠ i' → Disjoint (P i).V (P i').V := by
  classical
  set Z₁ := Γ.V ∩ D₁ with hZ₁
  set Z₂ := Γ.V ∩ D₂ with hZ₂
  have hZ₁V : Z₁ ⊆ Γ.toHypergraph.vertexSet := inter_subset_left
  have hZ₂V : Z₂ ⊆ Γ.toHypergraph.vertexSet := inter_subset_left
  by_cases hp : HasDisjointPaths Γ.toHypergraph.skeleton Z₁ Z₂ r
  · obtain ⟨Q, hQ⟩ := hp
    have hex : ∀ i, ∃ P : Drawing T, P.IsPathBetween (Q i).first (Q i).last ∧ P.IsSubdrawing Γ
      ∧ P.V = {x | x ∈ (Q i).walk.support} := fun i =>
      GraphMinor.GM16.drawing_path_of_skeleton_path (Q i).first_mem.1 (Q i).walk (Q i).isPath
    choose P hP hPs hPV using hex
    refine ⟨P, fun i => (Q i).first, fun i => (Q i).last, fun i => ⟨hPs i, (Q i).first_mem.2,
      (Q i).last_mem.2, hP i⟩, fun i i' hne => ?_⟩
    rw [hPV, hPV]
    exact hQ hne
  · exfalso
    obtain ⟨X, hsep, hlt⟩ := Thomas.exists_separates_lt_of_not_hasDisjointPaths Γ.toHypergraph hZ₁V
      hZ₂V hp
    set K₀ := Γ.toHypergraph.skeleton
    set K := Thomas.sepCompLeft K₀ Γ.V X Z₁ with hK
    have hXV : X ⊆ Γ.V := hsep.1
    let P : T → ℕ → Prop := fun u n => ∃ z ∈ Z₁ \ X, ∃ p : K₀.Walk z u,
      (∀ w ∈ p.support, w ∈ Γ.V \ X) ∧ p.length = n
    have hne : ∀ u ∈ K, {n | P u n}.Nonempty :=
      fun u ⟨_, z, hz, p, hp⟩ => ⟨_, z, hz, p, hp, rfl⟩
    let ρ : T → ℕ := fun u => sInf {n | P u n}
    have hρ : ∀ u ∈ K, P u (ρ u) := fun u hu => Nat.sInf_mem (s := {n | P u n}) (hne u hu)
    have hKsub : K ⊆ Γ.V \ X := Thomas.sepCompLeft_subset_sdiff _ _ _ _
    have hedge : ∀ e ∈ Γ.E, ∀ u ∈ K, u ∈ closure e → ∀ w ∈ Γ.V, w ∈ closure e → w ∈ K ∪ X
      := fun e he u hu hue w hw hwe => by
      by_cases huw : u = w
      · exact .inl (huw ▸ hu)
      by_contra hn
      have hw' : w ∈ Thomas.sepCompRight K₀ Γ.V X Z₁ := by
        refine ⟨⟨hw, fun h => hn (.inr h)⟩, fun h => hn (.inl h)⟩
      exact Thomas.not_adj_sepCompLeft_sepCompRight hu hw' ⟨huw, e, ⟨he, (hKsub hu).1, hue⟩, ⟨he,
        hw, hwe⟩⟩
    have hZbd : ∀ {z}, z ∈ Z₁ → z ∈ discBd D₁ := fun {z} hz => by
      by_contra hn
      exact disjoint_left.mp hi₁ (Γ.V_subset_U hz.1) ⟨hz.2, hn⟩
    have hreach : ∀ u ∈ K, u ∉ discBd D₁ → ∃ e ∈ Γ.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e
      ∧ w ∈ closure e ∧ (w ∉ discBd D₁ → ρ w < ρ u) := fun u hu hub => by
      obtain ⟨z, hz, p, hp, hl⟩ := hρ u hu
      have huz : u ≠ z := fun h => hub (h ▸ hZbd hz.1)
      obtain ⟨w, hadj, q, hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne huz p.reverse
      obtain ⟨huw, e, h1, h2⟩ := hadj
      have hsup : ∀ y ∈ q.support, y ∈ Γ.V \ X := fun y hy => hp y (by
        have : y ∈ p.reverse.support := by
          rw [hq]
          exact List.mem_cons_of_mem _ hy
        rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this)
      have hsup' : ∀ y ∈ q.reverse.support, y ∈ Γ.V \ X := fun y hy => hsup y
        (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy)
      have hw : w ∈ K := ⟨hsup w q.start_mem_support, z, hz, q.reverse, hsup'⟩
      refine ⟨e, h1.1, w, hw, huw.symm, h1.2.2, h2.2.2, fun _ => ?_⟩
      have hle : ρ w ≤ q.reverse.length := Nat.sInf_le ⟨z, hz, q.reverse, hsup', rfl⟩
      have hlen : q.length + 1 = p.length := by
        have h3 : p.reverse.length = q.length + 1 := by
          rw [hq]
          rfl
        rw [SimpleGraph.Walk.length_reverse] at h3
        exact h3.symm
      rw [SimpleGraph.Walk.length_reverse] at hle
      omega
    have hc : Γ.V ∩ discBd D₁ ⊆ K ∪ X := fun x hx => by
      by_cases hxX : x ∈ X
      · exact .inr hxX
      · have hz : x ∈ Z₁ := ⟨hx.1, Surface.discBd_subset _ hx.2⟩
        exact .inl ⟨⟨hx.1, hxX⟩, x, ⟨hz, hxX⟩, SimpleGraph.Walk.nil, fun w hw => by
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          exact hw ▸ ⟨hx.1, hxX⟩⟩
    have hke : Disjoint K D₂ := disjoint_left.mpr fun u hu hu₂ => by
      obtain ⟨hV, z, hz, p, hp⟩ := hu
      obtain ⟨x, hx, hxX⟩ := hsep.2 hz.1 (⟨hV.1, hu₂⟩ : u ∈ Z₂) p (fun w hw => (hp w hw).1)
      exact (hp x hx).2 hxX
    obtain ⟨B, hB, hsub, hdis, hbdB⟩ := exists_disc_of_side (K := K) (X := X) (ρ
      := ρ) hS hsph Γ h₁ h₂ hd (fun x hx => hU₁ ⟨hx.1, Surface.discBd_subset _ hx.2⟩) hi₁ hU₂ hi₂
        (fun x hx => (hKsub hx).1) hXV
      (Thomas.disjoint_sepCompLeft_sep _ _ _ _).symm hc hke hedge hreach
    have hle := hi B hB hsub hdis (hbdB.trans hXV)
    have := Set.ncard_le_ncard hbdB (Γ.finite_V.subset hXV)
    omega

end GraphMinor.GM07
