/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section8f
public import LeanPool.GraphMinor.GM11.HubCollar
public import LeanPool.GraphMinor.GM19.Section6Graph

/-!
# Graph Minors XIX, proof of (6.7): the perimeter of a region

Let `D` be a drawing with no loops in a connected closed surface, with a radial drawing `G₃`. The
spokes at the vertex `c` of `G₃` in a region `r` of `D` come in a cyclic order, and two consecutive
spokes end at the two ends of an edge of `D` (`GM11.corner_data`). If each vertex of `D` has only
one
spoke to `c`, then this cyclic sequence runs through the vertices in the closure of `r`, each once
(`exists_perimeter`). This is the statement of the paper's proof of (6.7), page 342, that the closed
curve tracing the perimeter of `r` has no repeated vertices.

A cyclic sequence without one term is still connected (`perimeter_avoid`), and this is the step
"which is impossible" of that proof.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {T : Type} [TopologicalSpace T]

theorem bool_cases {a b : Bool} (h : a ≠ b) {P : Bool → Prop} (ha : P a) (hb : P b)
  (c : Bool) : P c := by
  by_cases hc : c = a
  · exact hc ▸ ha
  · have : c = b := by
      revert h hc
      cases a <;> cases b <;> cases c <;> simp
    exact this ▸ hb

/-- **The perimeter of a region.** -/
theorem exists_perimeter [ConnectedSpace T] (hT : IsClosedSurface T) {D G₃ : Drawing T}
    (hrad : PreRad (PaintingOrDrawing.drawing D) G₃)
    (hmax : RadMax (PaintingOrDrawing.drawing D) G₃) (hE : D.E.Nonempty)
    (hloop : ∀ e ∈ D.E, ∃ x y, x ≠ y ∧ closure e ∩ D.V = {x, y}) {r : Set T} (hr : r ∈ D.R)
    (honce : ∀ e₁ ∈ G₃.E, ∀ e₂ ∈ G₃.E, e₁ ⊆ r → e₂ ⊆ r → ∀ v ∈ D.V, ∀ c ∈ r, c ∈ G₃.V →
      closure e₁ ∩ G₃.V = {v, c} → closure e₂ ∩ G₃.V = {v, c} → e₁ = e₂) :
    ∃ (κ : Type) (_ : Finite κ) (next : κ → κ) (A : κ → T), Function.Injective A ∧
      Function.Injective next ∧ range A = D.V ∩ closure r ∧
      (∀ k, ∃ e ∈ D.E, closure e ∩ D.V = {A k, A (next k)}) ∧
      ∀ a b, Relation.ReflTransGen (fun x y => y = next x) a b := by
  classical
  have hlc : LocallyConnectedSpace T := IsClosedSurface.locallyConnectedSpace hT
  have hne : Nonempty T := ⟨(region_nonempty hr).some⟩
  have : T2Space T := hT.2.1
  obtain ⟨γ, hγ⟩ := exists_edgePar (radialUnion hrad)
  obtain ⟨c, ⟨hc, hcV⟩, -⟩ := hrad.2.2.2.1 r hr
  change c ∈ r at hc
  change c ∈ G₃.V at hcV
  have hcH : c ∈ (radialUnion hrad).V := by
    rw [radialUnion_V]
    exact hcV
  obtain ⟨next, ρ, Pc, Wc, Qc, τc, hsec⟩ := exists_sectors hT _ hγ hcH
    (hub_two_halves hrad hT hmax hE hloop hγ hr hc hcV)
  have hcor := IsSectors.corners hsec
  have hR : ∀ k, ρ k ∈ (radialUnion hrad).R := IsCorners.region hcor
  have hρr : ∀ k, ρ k ⊆ r := fun k => by
    obtain ⟨r', hr', hsub⟩ := exists_region_of_sub hrad (hR k)
    obtain ⟨w, hw', hw⟩ := mem_closure_iff.mp (IsCorners.closure_v hcor k) r (region_isOpen hr) hc
    obtain rfl := region_eq_of_mem hr' hr (hsub hw) hw'
    exact hsub
  have hdata := corner_data hrad hT hmax hE hloop hγ hr hc hcV hsec hρr
  choose E' hE' A B hAB hA hB hcap hep hcapa hcapb hfr using hdata
  have hsp : ∀ k : halfEdges (radialUnion hrad) γ c, k.1.1 ∈ G₃.E :=
    fun k => hub_half_spoke hrad hr hc k hγ
  have hBnext : ∀ k, B k = A (next k) := by
    intro k
    have h₁ : B k ∈ closure (next k).1.1 ∩ G₃.V := by rw [hcapb]; simp
    rw [hcapa] at h₁
    rcases h₁ with h | h
    · exact h
    · exact (region_subset hr hc (D.V_subset_U (h ▸ hB k))).elim
  have hAc : ∀ k, A k ≠ c := fun k h => region_subset hr hc (D.V_subset_U (h ▸ hA k))
  have hspr : ∀ k : halfEdges (radialUnion hrad) γ c, k.1.1 ⊆ r := by
    intro k
    obtain ⟨v, hv, r', hr', w, hw, hwV, hset, hsub⟩ := spoke_ends hrad hT (hsp k)
    have hcl : c ∈ closure k.1.1 ∩ G₃.V := by rw [hcapa]; simp
    rw [hset] at hcl
    have hcw : c = w := by
      rcases hcl with h | h
      · exact absurd (h ▸ hv) fun h' => region_subset hr hc (D.V_subset_U h')
      · exact h
    subst hcw
    obtain rfl := region_eq_of_mem hr' hr hw hc
    exact hsub
  have hAinj : Function.Injective A := by
    intro k j hkj
    have h₁ : k.1.1 = j.1.1 := honce _ (hsp k) _ (hsp j) (hspr k) (hspr j) (A k) (hA k) c hc hcV
      (hcapa k) (by rw [hkj]; exact hcapa j)
    have hkH : k.1.1 ∈ (radialUnion hrad).E := k.2.1
    have hb : k.1.2 = j.1.2 := by
      by_contra hne
      have hk₂ : γ k.1.1 (endOf k.1.2) = c := k.2.2
      have hj₂ : γ k.1.1 (endOf j.1.2) = c := by
        rw [h₁]
        exact j.2.2
      have hend : ∀ b : Bool, γ k.1.1 (endOf b) = c := fun b =>
        bool_cases hne (P := fun b => γ k.1.1 (endOf b) = c) hk₂ hj₂ b
      have hm : A k ∈ closure k.1.1 ∩ G₃.V := by rw [hcapa]; exact Or.inl rfl
      obtain ⟨b, hb⟩ := exists_end_eq hγ hkH (by rw [radialUnion_V]; exact hm.2) hm.1
      exact hAc k (by rw [← hb, hend])
    exact Subtype.ext (Prod.ext h₁ hb)
  refine ⟨halfEdges (radialUnion hrad) γ c, (finite_halfEdges _ _ _).to_subtype, next, A, hAinj,
    IsCorners.inj hcor, Subset.antisymm ?_ ?_, fun k => ⟨E' k, hE' k, ?_⟩, IsCorners.reach hcor⟩
  · rintro _ ⟨k, rfl⟩
    have hm : A k ∈ closure k.1.1 ∩ G₃.V := by rw [hcapa]; simp
    exact ⟨hA k, closure_mono (hspr k) hm.1⟩
  · rintro x ⟨hxV, hxr⟩
    obtain ⟨h, hh, hset⟩ := exists_spoke_at hrad hmax hT hE hr hc hcV hxV hxr
    have hhH : h ∈ (radialUnion hrad).E := by
      rw [radialUnion_E]
      exact Or.inr hh
    have hcl : c ∈ closure h ∩ G₃.V := by rw [hset]; simp
    obtain ⟨b, hb⟩ := exists_end_eq hγ hhH hcH hcl.1
    let k : halfEdges (radialUnion hrad) γ c := ⟨(h, b), hhH, hb⟩
    have hx : x ∈ closure k.1.1 ∩ G₃.V := by
      change x ∈ closure h ∩ G₃.V
      rw [hset]
      simp
    rw [hcapa] at hx
    refine ⟨k, ?_⟩
    rcases hx with hx | hx
    · exact hx.symm
    · exact absurd (hx ▸ hxV) fun h' => region_subset hr hc (D.V_subset_U h')
  · rw [hcap, hBnext]

/-- **A cycle without one term is connected.** Let `next` be a cyclic permutation. A nonempty set of
terms without `b`, closed under `next` and its inverse except at `b`, holds each term other than
`b`. -/
theorem cycle_avoid {κ : Type} {next : κ → κ}
    (hreach : ∀ a b, Relation.ReflTransGen (fun x y => y = next x) a b) (b : κ)
    {Y : Set κ} (hne : Y.Nonempty) (hb : b ∉ Y)
    (hstep : ∀ a ∈ Y, next a ≠ b → next a ∈ Y)
    (hback : ∀ a, next a ∈ Y → a ≠ b → a ∈ Y) : ∀ j, j ≠ b → j ∈ Y := by
  obtain ⟨k, hk⟩ := hne
  by_cases hn : next b ∈ Y
  · intro j hj
    have key : ∀ i, Relation.ReflTransGen (fun x y => y = next x) b i → i ∈ Y ∨ i = b := by
      intro i h
      induction h with
      | refl => exact Or.inr rfl
      | tail _ hs ih =>
        subst hs
        rename_i a _
        rcases ih with h | h
        · by_cases hnb : next a = b
          · exact Or.inr hnb
          · exact Or.inl (hstep _ h hnb)
        · subst h
          exact Or.inl hn
    exact (key j (hreach b j)).resolve_right hj
  · have key : ∀ i, Relation.ReflTransGen (fun x y => y = next x) b i → i ∉ Y := by
      intro i h
      induction h with
      | refl => exact hb
      | tail _ hs ih =>
        subst hs
        rename_i a _
        by_cases hab : a = b
        · subst hab
          exact hn
        · exact fun hc => ih (hback a hc hab)
    exact absurd hk (key k (hreach b k))

end GraphMinor.GM19
