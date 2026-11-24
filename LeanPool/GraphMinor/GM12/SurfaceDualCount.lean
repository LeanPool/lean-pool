/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialExists
public import LeanPool.GraphMinor.GM11.RadialFacts
public import LeanPool.GraphMinor.GM12.Section72MaximalCriterion

/-!
# Counting the edges of a radial drawing

If `Γ'` satisfies (i)-(iv) for `Γ`, and each vertex of `Γ` has an edge, then `Γ'` has at most
`2 |E(Γ)|` edges (`ncard_spokes_le_two_mul`). If `Γ'` is radial and `Γ` has an edge, then it has at
least this many (`two_mul_le_ncard_spokes`). In both cases we step from one half-edge to the next
around a vertex, as in `ncard_spokes_le`.

We use this to prove the maximality clause of a radial drawing: a drawing with `2 |E(Γ)|` edges that
satisfies (i)-(iv) has no proper extension (`radMax_of_card`).
-/


@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {Γ Γ' : Drawing S}

/-- See the module docstring. An edge `s` of `Γ'` has just one half-edge at a vertex of `Γ`, and
that
vertex also has an edge of `Γ`. So the rotation there exists, and the half-edge after `s` is a
half-edge of `Γ` by `corner_has_edge`. This map is injective, since `s` determines its half-edge and
the rotation is injective. -/
theorem ncard_spokes_le_two_mul (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')
    (hS : IsClosedSurface S) (hall : ∀ x ∈ Γ.V, ∃ e ∈ Γ.E, x ∈ closure e) :
    Γ'.E.ncard ≤ 2 * Γ.E.ncard := by
  classical
  by_cases hemp : Γ'.E = ∅
  · simp [hemp]
  obtain ⟨s₀, hs₀⟩ := nonempty_iff_ne_empty.mpr hemp
  obtain ⟨y₀, -⟩ := hs₀.1
  have hne : Nonempty S := ⟨y₀⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  let H := radialUnion hrad
  have hHV : ∀ y : Γ.V, y.1 ∈ H.V := fun y => by
    rw [show H.V = Γ'.V from radialUnion_V hrad]
    exact radial_V hrad y.2
  have hspoke : ∀ s : Γ'.E, ∃ (y : Γ.V) (a : halfEdges H γ y.1), a.1.1 = s.1 := fun s => by
    obtain ⟨x, φ, h, -⟩ := spoke_half_unique hrad hS s.2 hγ
    exact ⟨x, φ, h⟩
  choose y a ha using hspoke
  have htwo : ∀ s : Γ'.E, 2 ≤ Nat.card (halfEdges H γ (y s).1) := fun s => by
    obtain ⟨e, he, hxe⟩ := hall _ (y s).2
    have heH : e ∈ H.E := by
      rw [show H.E = Γ.E ∪ Γ'.E from radialUnion_E hrad]
      exact Or.inl he
    obtain ⟨b, hb⟩ := exists_end_eq hγ heH (hHV _) hxe
    refine (one_lt_ncard (finite_halfEdges H γ _)).mpr ⟨(e, b), ⟨heH, hb⟩, a s, (a s).2,
      fun h => ?_⟩
    have h' : e = s.1 := (congrArg Prod.fst h).trans (ha s)
    exact edge_not_both hrad he (h' ▸ s.2)
  have hsec : ∀ y : Γ.V, ∃ next : halfEdges H γ y.1 → halfEdges H γ y.1,
      2 ≤ Nat.card (halfEdges H γ y.1) → ∃ ρ P W Q τ, IsSectors H γ y.1 next ρ P W Q τ := fun y
        => by
    by_cases h : 2 ≤ Nat.card (halfEdges H γ y.1)
    · obtain ⟨next, h'⟩ := exists_sectors hS _ hγ (hHV y) h
      exact ⟨next, fun _ => h'⟩
    · exact ⟨id, fun h' => absurd h' h⟩
  choose next hnext using hsec
  let Φ : Γ'.E → Set S × Bool := fun s => (next (y s) (a s)).1
  have hmaps : ∀ s, Φ s ∈ Γ.E ×ˢ (univ : Set Bool) := by
    intro s
    obtain ⟨ρ, P, W, Q, τ, hc⟩ := hnext _ (htwo s)
    refine ⟨(edge_cases hrad (next (y s) (a s))).resolve_right fun h' => ?_, mem_univ _⟩
    exact corner_has_edge hrad hS hγ (y s).2 hc (a s) (by rw [ha]; exact s.2) h'
  have hinj : Function.Injective Φ := by
    intro s t hst
    have hvx : y s = y t := by
      have h₁ := (next (y s) (a s)).2.2
      have h₂ := (next (y t) (a t)).2.2
      have hst' : (next (y s) (a s)).1 = (next (y t) (a t)).1 := hst
      rw [hst'] at h₁
      exact Subtype.ext (h₁.symm.trans h₂)
    obtain ⟨ρ, P, W, Q, τ, hc⟩ := hnext _ (htwo s)
    have hat : (a s).1 = (a t).1 := by
      have hst' : (next (y s) (a s)).1 = (next (y t) (a t)).1 := hst
      generalize a t = b at hst'
      generalize a s = a' at hst' hc
      generalize y t = z at hvx b hst'
      subst hvx
      exact congrArg Subtype.val (hc.corners.inj (Subtype.ext hst'))
    exact Subtype.ext (by rw [← ha s, ← ha t, hat])
  have hEf : (Γ.E ×ˢ (univ : Set Bool)).Finite := Γ.finite_edges.prod finite_univ
  have hle : Γ'.E.ncard ≤ (Γ.E ×ˢ (univ : Set Bool)).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have := hEf.to_subtype
    exact Nat.card_le_card_of_injective (fun s => (⟨Φ s, hmaps s⟩ : (Γ.E ×ˢ
      (univ : Set Bool) : Set _)))
      fun s t h => hinj (congrArg Subtype.val h)
  have h₃ : (Γ.E ×ˢ (univ : Set Bool)).ncard = Γ.E.ncard * 2 := by
    rw [ncard_prod]
    simp
  omega

variable [ConnectedSpace S]

/-- See the module docstring. Send a half-edge of `Γ` to the half-edge after it, which belongs to an
edge of `Γ'` by `corner_alternates`. This map is injective on half-edges. -/
theorem two_mul_le_ncard_spokes (hrad : PreRad (PaintingOrDrawing.drawing Γ) Γ')
    (hS : IsClosedSurface S) (hmax : RadMax (PaintingOrDrawing.drawing Γ) Γ') (hE : Γ.E.Nonempty) :
    2 * Γ.E.ncard ≤ Γ'.E.ncard := by
  classical
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  let H := radialUnion hrad
  have hHV : ∀ {y : S}, y ∈ Γ.V → y ∈ H.V := fun h => by
    rw [show H.V = Γ'.V from radialUnion_V hrad]
    exact radial_V hrad h
  have hsec : ∀ y : Γ.V, ∃ next : halfEdges H γ y.1 → halfEdges H γ y.1,
      ∃ ρ P W Q τ, IsSectors H γ y.1 next ρ P W Q τ := fun y =>
    exists_sectors hS _ hγ (hHV y.2) (two_half_edges hrad hS hmax hE hγ y.2)
  choose next hnext using hsec
  let Half := Γ.E ×ˢ (univ : Set Bool)
  have hend : ∀ q : Half, ∃ y : Γ.V, ∃ k : halfEdges H γ y.1, k.1 = q.1 := by
    rintro ⟨⟨e, b⟩, he, -⟩
    have heH : e ∈ H.E := by
      rw [show H.E = Γ.E ∪ Γ'.E from radialUnion_E hrad]
      exact Or.inl he
    have hmem : γ e (endOf b) ∈ Γ.V := by
      have h₁ := end_mem_closure hγ heH b
      have h₂ : γ e (endOf b) ∈ Γ'.V := by
        have : γ e (endOf b) ∈ H.V := by
          cases b
          · exact hγ.zero e heH
          · exact hγ.one e heH
        rwa [show H.V = Γ'.V from radialUnion_V hrad] at this
      exact radial_inter hrad ▸ ⟨Γ.closure_subset_U he h₁, Γ'.V_subset_U h₂⟩
    exact ⟨⟨_, hmem⟩, ⟨(e, b), heH, rfl⟩, rfl⟩
  choose y k hk using hend
  have hmaps : ∀ q : Half, (next (y q) (k q)).1.1 ∈ Γ'.E := by
    intro q
    obtain ⟨ρ, P, W, Q, τ, hc⟩ := hnext (y q)
    rcases corner_alternates hrad hS hmax hE hγ (y q).2 hc (k q) with h | h
    · exact absurd (hk q ▸ h.1) (fun h' => edge_not_both hrad q.2.1 h')
    · exact h.2
  have hinj : Function.Injective fun q : Half => (next (y q) (k q)).1.1 := by
    intro q q' hqq
    obtain ⟨x, φ, -, huniq⟩ := spoke_half_unique hrad hS (hmaps q) hγ
    obtain ⟨hy, hφ⟩ := huniq (y q) _ rfl
    obtain ⟨hy', hφ'⟩ := huniq (y q') _ (Eq.symm hqq)
    have hyy : y q = y q' := hy.trans hy'.symm
    have hval : (next (y q) (k q)).1 = (next (y q') (k q')).1 := hφ.trans hφ'.symm
    obtain ⟨ρ, P, W, Q, τ, hc⟩ := hnext (y q)
    have hkk : (k q).1 = (k q').1 := by
      generalize k q' = b at hval
      generalize k q = a at hval hc
      generalize y q' = z at hyy b hval
      subst hyy
      exact congrArg Subtype.val (hc.corners.inj (Subtype.ext hval))
    exact Subtype.ext (by rw [← hk q, ← hk q', hkk])
  have hEf : (Γ.E ×ˢ (univ : Set Bool)).Finite := Γ.finite_edges.prod finite_univ
  have hle : (Γ.E ×ˢ (univ : Set Bool)).ncard ≤ Γ'.E.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have : Finite Γ'.E := Γ'.finite_edges.to_subtype
    exact Nat.card_le_card_of_injective (fun q : Half => (⟨_, hmaps q⟩ : Γ'.E))
      fun s t h => hinj (congrArg Subtype.val h)
  have h₃ : (Γ.E ×ˢ (univ : Set Bool)).ncard = Γ.E.ncard * 2 := by
    rw [ncard_prod]
    simp
  omega

omit [ConnectedSpace S] in
/-- See the module docstring. An extension of `Γ'` has the same vertices. Its edges include those of
`Γ'`, and it has no more of them, so the edges are the same. -/
theorem radMax_of_card (hS : IsClosedSurface S) (hT : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    (hpre : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing Γ')
    (hall : ∀ x ∈ Γ.V, ∃ e ∈ Γ.E, x ∈ closure e) (hcard : 2 * Γ.E.ncard ≤ Γ'.E.ncard) :
    RadMax (PaintingOrDrawing.drawing Γ) Γ' := by
  intro J hJ hsub
  have hle := ncard_spokes_le_two_mul (⟨hT, hJ⟩ : PreRad (PaintingOrDrawing.drawing Γ) J) hS hall
  have hE : J.E = Γ'.E := (Set.eq_of_subset_of_ncard_le hsub.2 (by omega) J.finite_edges).symm
  exact ⟨(preRadial_vertices_eq_of_extension hpre hJ hsub).subset, hE.subset⟩

end GraphMinor.GM12
