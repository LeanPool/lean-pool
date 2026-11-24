/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import Mathlib.Topology.UnitInterval

/-!
# Graph Minors XI, Section 7: some topological lemmas

This file proves the point-set lemmas of Section 7 of Graph Minors XI that need no input on
surfaces: (7.7), which says that two subsets with connected, disjoint boundaries are nested, and
(7.10), which cuts an arc-connected set along a closed set with arc-connected boundary.

The boundary `bd(X)` of the paper is `subBd X`, which is the frontier of `X`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

theorem subBd_eq_frontier (X : Set S) : subBd X = frontier X := by
  rw [frontier_eq_closure_inter_closure, subBd, compl_eq_univ_sdiff]

/-- A set with empty frontier, in a connected space, is empty or everything. -/
private theorem eq_empty_or_univ_of_frontier [ConnectedSpace S] {X : Set S}
    (h : frontier X = ∅) : X = ∅ ∨ X = univ :=
  isClopen_iff.mp (isClopen_iff_frontier_eq_empty.mpr h)

/-- A preconnected set that misses `frontier Y`, and that meets the complement of `closure Y`,
misses `closure Y`. -/
private theorem preconnected_subset_compl_closure {F Y : Set S} (hF : IsPreconnected F)
    (hd : Disjoint F (frontier Y)) {z : S} (hzF : z ∈ F) (hz : z ∉ closure Y) :
    Disjoint F (closure Y) := by
  have hcover : F ⊆ interior Y ∪ (closure Y)ᶜ := by
    intro x hx
    by_cases hxc : x ∈ closure Y
    · left
      by_contra hxi
      exact disjoint_left.mp hd hx ⟨hxc, hxi⟩
    · exact Or.inr hxc
  have hdisj : Disjoint (interior Y) (closure Y)ᶜ :=
    disjoint_left.mpr fun x hx hx' => hx' (subset_closure (interior_subset hx))
  have hsub : F ⊆ (closure Y)ᶜ := by
    have := hF.subset_right_of_subset_union isOpen_interior isClosed_closure.isOpen_compl hdisj
      hcover ⟨z, hzF, hz⟩
    exact this
  exact disjoint_left.mpr fun x hx hx' => hsub hx hx'

/-- The main case of (7.7). -/
private theorem nested_aux [ConnectedSpace S] {X Y : Set S}
    (hX : IsPreconnected (frontier X)) (hY : IsPreconnected (frontier Y))
    (hne : (X ∩ Y).Nonempty) (hun : X ∪ Y ≠ univ) (hdisj : Disjoint (frontier X) (frontier Y))
    {z : S} (hzX : z ∈ frontier X) (hzY : z ∈ closure Yᶜ) : Y ⊆ X := by
  have hzY' : z ∉ closure Y := fun h => disjoint_left.mp hdisj hzX ⟨h, by
    rw [closure_compl] at hzY; exact hzY⟩
  have hF1 : Disjoint (frontier X) (closure Y) :=
    preconnected_subset_compl_closure hX hdisj hzX hzY'
  by_contra hYX
  obtain ⟨y, hyY, hyX⟩ := not_subset.mp hYX
  obtain ⟨x, hxX, hxY⟩ := hne
  have hclX : closure X = interior X ∪ frontier X := by
    rw [frontier, union_sdiff_self, union_eq_self_of_subset_left interior_subset_closure]
  have hclY : closure Y = interior Y ∪ frontier Y := by
    rw [frontier, union_sdiff_self, union_eq_self_of_subset_left interior_subset_closure]
  -- `frontier Y` is not empty, else `Y` would be everything.
  have hYne : (frontier Y).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    rcases eq_empty_or_univ_of_frontier h with h | h
    · exact (h ▸ hyY : y ∈ (∅ : Set S))
    · exact hun (by rw [h, union_univ])
  have hdis2 : Disjoint (interior X) (closure X)ᶜ :=
    disjoint_left.mpr fun x hx hx' => hx' (subset_closure (interior_subset hx))
  have hcover : frontier Y ⊆ interior X ∪ (closure X)ᶜ := by
    intro w hw
    by_cases hwc : w ∈ closure X
    · left
      by_contra hwi
      exact disjoint_left.mp hdisj ⟨hwc, hwi⟩ hw
    · exact Or.inr hwc
  rcases (isPreconnected_iff_subset_of_disjoint.mp hY) _ _ isOpen_interior
      isClosed_closure.isOpen_compl hcover (by
        rw [disjoint_iff_inter_eq_empty.mp hdis2]
        simp) with hin | hout
  · -- `bd(Y)` lies inside `X`: the part of `closure Y` outside `X` is open and closed.
    have hA : IsClopen (closure Y \ interior X) := by
      refine ⟨isClosed_closure.sdiff isOpen_interior, ?_⟩
      have hEq : closure Y \ interior X = interior Y ∩ (closure X)ᶜ := by
        ext w
        constructor
        · rintro ⟨hw1, hw2⟩
          have hw3 : w ∉ closure X := by
            intro h
            rw [hclX] at h
            rcases h with h | h
            · exact hw2 h
            · exact disjoint_left.mp hF1 h hw1
          refine ⟨?_, hw3⟩
          rw [hclY] at hw1
          rcases hw1 with h | h
          · exact h
          · exact absurd (hin h) hw2
        · rintro ⟨hw1, hw2⟩
          exact ⟨interior_subset_closure hw1, fun h => hw2 (interior_subset_closure h)⟩
      rw [hEq]
      exact isOpen_interior.inter isClosed_closure.isOpen_compl
    rcases isClopen_iff.mp hA with h | h
    · have : y ∈ closure Y \ interior X :=
        ⟨subset_closure hyY, fun h' => hyX (interior_subset h')⟩
      rw [h] at this
      exact this
    · have hx' : x ∈ closure Y \ interior X := h ▸ mem_univ x
      have hxc : x ∈ closure X := subset_closure hxX
      rw [hclX] at hxc
      rcases hxc with h' | h'
      · exact hx'.2 h'
      · exact disjoint_left.mp hF1 h' hx'.1
  · -- `bd(Y)` lies outside `X`: the part of `closure Y` inside `X` is open and closed.
    have hA : IsClopen (closure Y ∩ closure X) := by
      refine ⟨isClosed_closure.inter isClosed_closure, ?_⟩
      have hEq : closure Y ∩ closure X = interior Y ∩ interior X := by
        ext w
        constructor
        · rintro ⟨hw1, hw2⟩
          have hw3 : w ∈ interior X := by
            rw [hclX] at hw2
            rcases hw2 with h | h
            · exact h
            · exact absurd hw1 (disjoint_left.mp hF1 h)
          refine ⟨?_, hw3⟩
          rw [hclY] at hw1
          rcases hw1 with h | h
          · exact h
          · exact absurd (interior_subset_closure hw3) (hout h)
        · rintro ⟨hw1, hw2⟩
          exact ⟨interior_subset_closure hw1, interior_subset_closure hw2⟩
      rw [hEq]
      exact isOpen_interior.inter isOpen_interior
    rcases isClopen_iff.mp hA with h | h
    · have : x ∈ closure Y ∩ closure X := ⟨subset_closure hxY, subset_closure hxX⟩
      rw [h] at this
      exact this
    · have hy' : y ∈ closure Y ∩ closure X := h ▸ mem_univ y
      have hyc := hy'.2
      rw [hclX] at hyc
      rcases hyc with h' | h'
      · exact hyX (interior_subset h')
      · exact disjoint_left.mp hF1 h' hy'.1

/-- Graph Minors XI, (7.7) (page 94): "If $\Sigma$ is connected, $X, Y \subseteq \Sigma$ and
$bd(X)$, $bd(Y)$ are both arc-wise
connected, and $X \cap Y \ne \emptyset$, $X \cup Y \ne \Sigma$, and $bd(X) \cap bd(Y) =
\emptyset$, then either $X \subseteq Y$ or $Y \subseteq X$." We assume only that the two boundaries
are preconnected. -/
theorem theorem_7_7_proof [ConnectedSpace S] {X Y : Set S}
    (hX : IsPreconnected (subBd X)) (hY : IsPreconnected (subBd Y))
    (hne : (X ∩ Y).Nonempty) (hun : X ∪ Y ≠ univ) (hdisj : Disjoint (subBd X) (subBd Y)) :
    X ⊆ Y ∨ Y ⊆ X := by
  simp only [subBd_eq_frontier] at hX hY hdisj
  -- There exists `z ∈ bd(X ∪ Y)`, since `∅ ≠ X ∪ Y ≠ Σ`.
  have hfr : (frontier (X ∪ Y)).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    rcases eq_empty_or_univ_of_frontier h with h | h
    · obtain ⟨x, hx, -⟩ := hne
      have : x ∈ X ∪ Y := Or.inl hx
      rw [h] at this
      exact this
    · exact hun h
  obtain ⟨z, hz⟩ := hfr
  rcases frontier_union_subset X Y hz with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
  · exact Or.inr (nested_aux hX hY hne hun hdisj hz1 hz2)
  · refine Or.inl (nested_aux hY hX ?_ ?_ hdisj.symm hz2 hz1)
    · rwa [inter_comm]
    · rwa [union_comm]

/-- Graph Minors XI, (7.10) (page 95): "If $X \subseteq \Sigma$ is arc-wise connected, $Y \subseteq
\Sigma$ is closed, $bd(Y)$ is
arc-wise connected, and $\emptyset \ne bd(Y) \subseteq X$, then $X \cap Y$ is arc-wise
connected." -/
theorem theorem_7_10_proof {X Y : Set S} (hX : IsPathConnected X) (hY : IsClosed Y)
    (hb : IsPathConnected (subBd Y)) (hsub : subBd Y ⊆ X) : IsPathConnected (X ∩ Y) := by
  have hbY : subBd Y ⊆ Y := fun x hx => hY.closure_subset_iff.mpr subset_rfl hx.1
  have hbin : subBd Y ⊆ X ∩ Y := subset_inter hsub hbY
  obtain ⟨y₀, hy₀⟩ := hb.nonempty
  refine ⟨y₀, hbin hy₀, fun {x} hx => ?_⟩
  suffices JoinedIn (X ∩ Y) x y₀ from this.symm
  -- Follow a path in `X` from `x` to `y₀`, up to the first point where it leaves `Y`.
  obtain ⟨γ, hγ⟩ := hX.joinedIn x hx.1 y₀ (hsub hy₀)
  by_cases hstay : ∀ t, γ t ∈ Y
  · exact ⟨γ, fun t => ⟨hγ t, hstay t⟩⟩
  · set B : Set I := {t | γ t ∉ Y} with hB
    have hBne : B.Nonempty := not_forall.mp hstay
    have hBopen : IsOpen B := hY.isOpen_compl.preimage γ.continuous
    set α : I := sInf B with hα
    have hbelow : ∀ t, t < α → γ t ∈ Y := by
      intro t ht
      by_contra h
      exact not_lt.mpr (sInf_le h) ht
    have hαcl : α ∈ closure B := by
      exact csInf_mem_closure hBne (OrderBot.bddBelow B)
    have hγα : γ α ∈ closure Yᶜ := by
      have : γ '' closure B ⊆ closure (γ '' B) := image_closure_subset_closure_image γ.continuous
      refine closure_mono ?_ (this ⟨α, hαcl, rfl⟩)
      rintro _ ⟨t, ht, rfl⟩
      exact ht
    have hαY : γ α ∈ Y := by
      by_cases h0 : α = 0
      · rw [h0, γ.source]
        exact hx.2
      · have hlt : (0 : I) < α := bot_lt_iff_ne_bot.mpr h0
        have hcl : α ∈ closure (Iio α) := by
          rw [closure_Iio' (show (Iio α).Nonempty from ⟨0, hlt⟩)]
          exact self_mem_Iic
        have : γ '' closure (Iio α) ⊆ closure (γ '' Iio α) :=
          image_closure_subset_closure_image γ.continuous
        refine hY.closure_subset_iff.mpr ?_ (this ⟨α, hcl, rfl⟩)
        rintro _ ⟨t, ht, rfl⟩
        exact hbelow t ht
    have hαb : γ α ∈ subBd Y := ⟨subset_closure hαY, by
      rwa [← compl_eq_univ_sdiff]⟩
    have hj1 : JoinedIn (X ∩ Y) x (γ α) := by
      refine ⟨⟨⟨fun t => γ (α * t), ?_⟩, ?_, ?_⟩, fun t => ⟨hγ _, ?_⟩⟩
      · exact γ.continuous.comp (continuous_const.mul continuous_id)
      · simp
      · simp
      · change γ (α * t) ∈ Y
        rcases (unitInterval.mul_le_left (x := α) (y := t)).lt_or_eq with h | h
        · exact hbelow _ h
        · rw [h]
          exact hαY
    have hj2 : JoinedIn (X ∩ Y) (γ α) y₀ := (hb.joinedIn _ hαb _ hy₀).mono hbin
    exact hj1.trans hj2

end GraphMinor.GM11
