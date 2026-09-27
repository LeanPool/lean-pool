/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.LPDuality
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.Reduction


/-! # Strong duality for triangle packing and covering -/

@[expose] public section

open Finset SimpleGraph Nibble.YusterE LPDuality

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Object type: the triangles of `G`. -/
abbrev Tri := {t : Finset V // t ∈ G.cliqueFinset 3}
/-- Constraint type: the edges of `G`. -/
abbrev Edg := {e : Sym2 V // e ∈ G.edgeFinset}

/-- Incidence: the edges contained in a triangle. -/
noncomputable def triInc (t : Tri G) : Finset (Edg G) :=
  Finset.univ.filter (fun e : Edg G => e.val ∈ edgesIn G t.val)

/-- Every triangle has an incident graph edge. -/
theorem triInc_nonempty (t : Tri G) : (triInc G t).Nonempty := by
  classical
  have ht := SimpleGraph.mem_cliqueFinset_iff.mp t.property
  obtain ⟨hc, hcard⟩ := ht
  obtain ⟨v, hv⟩ : t.val.Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; decide)
  have hc_erase : #(t.val.erase v) = 2 := by
    rw [Finset.card_erase_of_mem hv, hcard]
  obtain ⟨w, hw⟩ : (t.val.erase v).Nonempty :=
    Finset.card_pos.mp (by rw [hc_erase]; decide)
  have hvw : w ≠ v := (Finset.mem_erase.mp hw).1
  have hadj : G.Adj w v := hc (Finset.mem_of_mem_erase hw) hv hvw
  let e : Sym2 V := s(w, v)
  have heG : e ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact hadj
  have heIn : e ∈ edgesIn G t.val := by
    rw [edgesIn, Finset.mem_filter]
    refine ⟨heG, ?_⟩
    intro x hx
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_of_mem_erase hw
    · exact hv
  refine ⟨⟨e, heG⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heIn⟩

/-- **Bridge 1 (cover side).** The abstract cover optimum over the triangle–edge incidence equals
`τ₃*`. -/
theorem coverOpt_triInc_eq_tau3Star : coverOpt (triInc G) = tau3Star G := by
  -- Helper: edgesIn is nonempty for any triangle
  have edgesIn_ne : ∀ (t : Finset V), G.IsNClique 3 t → (edgesIn G t).Nonempty := fun t ht => by
    have ht' : t ∈ G.cliqueFinset 3 := by rwa [SimpleGraph.mem_cliqueFinset_iff]
    rw [edgesIn]
    -- The clique has 3 vertices
    have hCLIQUEN := SimpleGraph.mem_cliqueFinset_iff.mp ht'
    obtain ⟨hc, hcard⟩ := hCLIQUEN
    -- Get two distinct vertices from the clique
    have hne : t.Nonempty := Finset.card_pos.mp (by rw [hcard]; decide)
    obtain ⟨v, hv⟩ := hne
    -- There exists another vertex (since card = 3 > 1)
    have hc_erase : #(t.erase v) = 2 := by rw [Finset.card_erase_of_mem hv, hcard]
    have hne2 : (t.erase v).Nonempty := Finset.card_pos.mp (by rw [hc_erase]; decide)
    obtain ⟨w, hw⟩ := hne2
    -- v and w are distinct and both in t
    have hvw : w ≠ v := by
      rw [Finset.mem_erase] at hw
      exact hw.1
    -- Since t is a clique, w and v are adjacent
    have hadj : G.Adj w v := hc (Finset.mem_of_mem_erase hw) hv hvw
    -- The edge {w, v} is in edgesIn G t
    let e : Sym2 V := s(w, v)
    have hmem : e ∈ {e ∈ G.edgeFinset | ∀ v ∈ e, v ∈ t} := by
      simp only [Finset.mem_filter]
      constructor
      · rw [SimpleGraph.mem_edgeFinset]
        exact hadj
      · intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> [exact Finset.mem_of_mem_erase hw; exact hv]
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.ne_empty_of_mem hmem)
  apply le_antisymm
  · -- coverOpt ≤ tau3Star
    apply csInf_le_csInf
    · -- coverOpt set is bounded below
      refine ⟨0, fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      exact Finset.sum_nonneg fun _ _ => hy.1 _
    · -- τ ∈ tau3Star set (to show nonempty)
      use ∑ _e ∈ G.edgeFinset, (1 : ℝ)
      use fun _ => (1 : ℝ)
      constructor
      · constructor
        · intro _; norm_num
        · intro t ht
          have ht' := SimpleGraph.mem_cliqueFinset_iff.mp ht
          have hne : (edgesIn G t).Nonempty := by exact edgesIn_ne t ht'
          have : (1 : ℝ) ≤ ∑ _e ∈ edgesIn G t, (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simp only [mul_one]
            exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hne)
          exact this
      · rfl
    · -- subset: tau3Star set ⊆ coverOpt set
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      use (fun (c : Edg G) => y c)
      constructor
      · constructor
        · intro ⟨e, _⟩; exact hy.1 e
        · intro ⟨t, ht⟩
          have h := hy.2 t ht
          have eq_sums : (@Finset.sum (Edg G) ℝ _ (@triInc V _ _ G _ ⟨t, ht⟩) (fun c : Edg G => y (c : Sym2 V))) = ∑ e ∈ edgesIn G t, y e := by
            rw [triInc]
            refine Finset.sum_bij (fun e _ => e.val) ?_ ?_ ?_ ?_
            · intro e he
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
              exact he
            · intro e₁ _ e₂ _ h; exact Subtype.ext h
            · intro e he
              have he' : e ∈ G.edgeFinset := Finset.filter_subset _ _ he
              use ⟨e, he'⟩
              simp [he]
            · intro b _; rfl
          rw [eq_sums]
          exact h
      · refine Finset.sum_bij (fun e (he : e ∈ G.edgeFinset) => ⟨e, he⟩) ?_ ?_ ?_ ?_
        · intro e _; exact Finset.mem_univ _
        · intro e₁ _ e₂ _ h; simp at h; exact h
        · intro c _; use c.val; simp
        · intro e _; rfl
  · -- tau3Star ≤ coverOpt
    apply csInf_le_csInf
    · -- coverOpt set is bounded below
      refine ⟨0, fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      exact Finset.sum_nonneg fun _ _ => hy.1 _
    · -- tau3Star set is nonempty
      refine ⟨∑ _e ∈ G.edgeFinset, (1 : ℝ), ?_⟩
      use fun _ => (1 : ℝ)
      constructor
      · refine ⟨fun _ => by norm_num, ?_⟩
        intro ⟨t, ht⟩
        have hne : (edgesIn G t).Nonempty := by exact edgesIn_ne t (SimpleGraph.mem_cliqueFinset_iff.mp ht)
        have hcard : #(triInc G ⟨t, ht⟩) = #(edgesIn G t) := by
          rw [triInc]
          refine Finset.card_bij (fun e _ => e.val) ?_ ?_ ?_
          · intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
            exact he
          · intro _ _ _ _ h; exact Subtype.ext h
          · intro e he
            simp only [edgesIn, Finset.mem_filter] at he
            have he' : e ∈ edgesIn G t := Finset.mem_filter.mpr ⟨he.1, he.2⟩
            use ⟨e, he.1⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            simp [he']
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
        exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr hne)
      · symm
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Finset.card_univ, Fintype.card_coe]
        simp
    · -- subset: coverOpt set ⊆ tau3Star set
      intro x hx
      -- x ∈ {x | ∃ y : Edg G → ℝ, IsCover (triInc G) y ∧ x = ∑ c, y c}
      obtain ⟨y, hy, rfl⟩ := hx
      -- y : Edg G → ℝ
      -- Extend y to Sym2 V by setting non-edges to 0
      let y' : Sym2 V → ℝ := fun e => if h : e ∈ G.edgeFinset then y ⟨e, h⟩ else 0
      use y'
      refine ⟨?_, ?_⟩
      · -- IsFracCover G y'
        constructor
        · intro e; simp only [y']; split_ifs with h <;> [exact hy.1 ⟨e, h⟩; norm_num]
        · intro t ht
          have h := hy.2 ⟨t, ht⟩
          have eq_sums : (@Finset.sum (Edg G) ℝ _ (@triInc V _ _ G _ ⟨t, ht⟩) y) = ∑ e ∈ (edgesIn G t).attach, y ⟨e.val, Finset.filter_subset (fun e => ∀ v ∈ e, v ∈ t) G.edgeFinset e.prop⟩ := by
            rw [triInc]
            have toMem : ∀ c : Edg G, c ∈ Finset.univ.filter (fun e : Edg G => e.val ∈ edgesIn G t) → c.val ∈ edgesIn G t := by simp
            refine Finset.sum_bij (fun c _ => ⟨c.val, toMem c ‹_›⟩) ?_ ?_ ?_ ?_
            · intro c _; simp
            · intro c₁ _ c₂ _ h; simpa using h
            · intro e he
              use ⟨e.val, Finset.filter_subset _ _ e.prop⟩
              simp
            · intro c _; rfl
          rw [← Finset.sum_attach]
          simp only [y']
          have h2 : ∀ x ∈ (edgesIn G t).attach, (if h : x.val ∈ G.edgeFinset then y ⟨x.val, h⟩ else 0) = y ⟨x.val, Finset.filter_subset (fun e => ∀ v ∈ e, v ∈ t) G.edgeFinset x.prop⟩ := by
            intro x hx
            have hx' : x.val ∈ edgesIn G t := x.2
            rw [dite_eq_left (Finset.filter_subset _ _ hx')]
          rw [Finset.sum_congr rfl h2]
          rw [eq_sums.symm]
          exact h
      · symm
        refine Finset.sum_bij (fun e he => ⟨e, he⟩) ?_ ?_ ?_ ?_
        · intro e he; simp
        · intro e₁ he₁ e₂ he₂ h; simpa using h
        · intro c _; use c.val; simp
        · intro e he; simp only [y', he, dite_eq_left]

/-- **Bridge 2 (packing side).** The abstract packing optimum over the triangle–edge incidence equals
`ν₃*`. -/
theorem packOpt_triInc_eq_nu3star : packOpt (triInc G) = nu3star G := by
  unfold packOpt nu3star
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hinj : ∀ t1 t2 : Tri G, t1.val.powersetCard 2 = t2.val.powersetCard 2 → t1 = t2 := by
      intro ⟨t1, ht1⟩ ⟨t2, ht2⟩ h
      simp [SimpleGraph.mem_cliqueFinset_iff] at ht1 ht2
      exact Subtype.ext (powersetCard_two_inj (by rw [ht1.card_eq]; omega) (by rw [ht2.card_eq]; omega) h)
    let w' : Finset (Finset V) → ℝ := fun T => if hT : T ∈ triangleHypergraphE G then
      w ⟨(Classical.choose (Finset.mem_image.mp hT)), (Classical.choose_spec (Finset.mem_image.mp hT)).1⟩
      else (0 : ℝ)
    refine ⟨w', ⟨?nneg, ?zero, ?cap⟩, ?sum⟩
    case nneg =>
      intro T
      simp only [w']
      split_ifs with hT
      · exact hw.1 _
      · exact le_refl 0
    case zero =>
      intro T hT
      simp [w', hT]
    case cap =>
      intro e
      by_cases he : e.card = 2
      · -- e is a 2-element finset, corresponding to an edge of G (as Sym2 V)
        -- Check if e corresponds to an edge of G
        -- Define: e is an edge iff there exists Sym2 edge with toFinset = e
        let isEdge : Finset V → Prop := fun f => ∃ e' ∈ G.edgeFinset, Sym2.toFinset e' = f
        by_cases he' : isEdge e
        · -- e corresponds to an edge; use packing constraint
          obtain ⟨e', he'_edge, he'_eq⟩ := he'
          -- e' is in G.edgeFinset, and Sym2.toFinset e' = e
          -- Construct the Edg G element
          let ec : Edg G := ⟨e', he'_edge⟩
          -- The constraint says: ∑ t ∈ {t | ec ∈ triInc t}, w t ≤ 1
          have hcon := hw.2 ec
          -- We need to show: ∑ T ∈ triangleHypergraphE G with e ∈ T, w' T ≤ 1
          -- These are the same set of triangles
          -- Rewrite "with" to filter form
          rw [Finset.sum_filter]
          rw [Finset.sum_filter] at hcon
          -- The two sums are equal: triangles containing e = triangles containing ec
          -- First, rewrite the sum over triangleHypergraphE G as a sum over Tri G
          have heq_sum : ∑ T ∈ triangleHypergraphE G, (if e ∈ T then w' T else (0 : ℝ)) =
                         ∑ t : Tri G, (if e ∈ t.val.powersetCard 2 then w t else (0 : ℝ)) := by
            rw [triangleHypergraphE]
            rw [Finset.sum_image (fun x hx y hy hxy => by
              have := hinj ⟨x, hx⟩ ⟨y, hy⟩ hxy
              simpa using this)]
            rw [Finset.sum_subtype]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            have hT : t.val.powersetCard 2 ∈ triangleHypergraphE G := by
              rw [triangleHypergraphE, Finset.mem_image]
              exact ⟨t.val, t.prop, rfl⟩
            -- The choose gives the original triangle by injectivity
            have hcs := Classical.choose_spec (Finset.mem_image.mp hT)
            have hchoose : Classical.choose (Finset.mem_image.mp hT) = t.val :=
              Subtype.ext_iff.mp (hinj ⟨Classical.choose (Finset.mem_image.mp hT), hcs.1⟩ t hcs.2)
            have hw_eq : w ⟨Classical.choose (Finset.mem_image.mp hT), hcs.1⟩ = w t := by
              congr 1
              exact Subtype.ext hchoose
            simp only [w', hT, hchoose]
            all_goals simp
          rw [heq_sum]
          -- Now show this equals the constraint sum
          have heq_sum2 : ∑ t : Tri G, (if e ∈ t.val.powersetCard 2 then w t else 0) =
                          ∑ t : Tri G, (if ec ∈ triInc G t then w t else 0) := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            simp only [triInc]
            -- Need: e ∈ t.val.powersetCard 2 ↔ ec.val ∈ edgesIn G t.val
            -- ec.val = e' where e'.toFinset = e, and e' ∈ G.edgeFinset
            -- Since he : e.card = 2, we have e ∈ t.val.powersetCard 2 ↔ e ⊆ t.val
            -- And ec.val ∈ edgesIn G t.val ↔ ec.val.toFinset ⊆ t.val (by definition of edgesIn)
            -- Since ec.val.toFinset = e, these are equivalent
            simp [edgesIn, Finset.mem_powersetCard]
            have h_equiv : (e ⊆ t.val ∧ e.card = 2) ↔ ∀ v ∈ ec.val, v ∈ t.val := by
              constructor
              · intro ⟨hsub, _⟩ v hv
                have hve : v ∈ e := by
                  rw [← he'_eq]
                  exact Sym2.mem_toFinset.mpr hv
                exact hsub hve
              · intro h
                exact ⟨by
                  intro v hv
                  rw [← he'_eq] at hv
                  exact h v (Sym2.mem_toFinset.mp hv), he⟩
            simp [h_equiv]
          rw [heq_sum2]
          exact hcon
        · -- e does not correspond to an edge; sum is empty
          have hdisj : ∀ t ∈ G.cliqueFinset 3, e ∉ t.powersetCard 2 := by
            intro t ht h
            rw [Finset.mem_powersetCard] at h
            obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp he
            apply he'
            use s(a, b)
            simp [Sym2.toFinset, heq]
            -- Need to show (a, b) is an edge of G
            -- Since e ⊆ t and t is a clique, a and b are adjacent
            have hsub := h.1
            rw [heq] at hsub
            have ha : a ∈ t := hsub (Finset.mem_insert_self a {b})
            have hb : b ∈ t := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
            refine ⟨?adj, ?finset⟩
            · have htc : G.IsNClique 3 t := by simpa using ht
              exact htc.isClique ha hb hab
            · simp [Sym2.toMultiset]
          have hempty : (triangleHypergraphE G).filter (fun T => e ∈ T) = ∅ := by
            rw [triangleHypergraphE]
            rw [Finset.filter_eq_empty_iff]
            intro T hT
            rw [Finset.mem_image] at hT
            obtain ⟨t, ht, rfl⟩ := hT
            exact hdisj t ht
          rw [hempty, Finset.sum_empty]
          exact zero_le_one
      · have hempty : (triangleHypergraphE G).filter (fun T => e ∈ T) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro T hT
          rw [triangleHypergraphE, Finset.mem_image] at hT
          obtain ⟨t, ht, rfl⟩ := hT
          simp only [SimpleGraph.mem_cliqueFinset_iff] at ht
          rw [Finset.mem_powersetCard]
          exact fun h => he h.2
        simp [hempty]
    case sum =>
      -- Need: ∑ t : Tri G, w t = ∑ T ∈ triangleHypergraphE G, w' T
      -- triangleHypergraphE G = (G.cliqueFinset 3).image (fun t => t.powersetCard 2)
      -- w' T = w ⟨choose(T), ...⟩ if T ∈ triangleHypergraphE G, else 0
      -- Since choose(T) is the unique t with t.powersetCard 2 = T, we get the equality
      rw [triangleHypergraphE]
      rw [Finset.sum_image (fun x hx y hy hxy => by
        have := hinj ⟨x, hx⟩ ⟨y, hy⟩ hxy
        simpa using this)]
      -- Now: ∑ t : Tri G, w t = ∑ x ∈ G.cliqueFinset 3, w' (x.powersetCard 2)
      -- Both sides are sums over the same index set
      -- Convert LHS to sum over G.cliqueFinset 3
      rw [← Finset.sum_coe_sort (s := G.cliqueFinset 3)]
      refine Finset.sum_congr rfl ?_
      intro t ht
      -- Goal: w ⟨t.val, t.prop⟩ = w' (t.val.powersetCard 2)
      have hT : t.val.powersetCard 2 ∈ triangleHypergraphE G := by
        rw [triangleHypergraphE, Finset.mem_image]
        exact ⟨t.val, t.prop, rfl⟩
      show w ⟨t.val, t.prop⟩ = w' (t.val.powersetCard 2)
      change w ⟨t.val, t.prop⟩ = (if hT : t.val.powersetCard 2 ∈ triangleHypergraphE G then
        w ⟨(Classical.choose (Finset.mem_image.mp hT)), (Classical.choose_spec (Finset.mem_image.mp hT)).1⟩
        else (0 : ℝ))
      have hcs := Classical.choose_spec (Finset.mem_image.mp hT)
      have hchoose : Classical.choose (Finset.mem_image.mp hT) = t.val :=
        Subtype.ext_iff.mp (hinj ⟨Classical.choose (Finset.mem_image.mp hT), hcs.1⟩ ⟨t.val, t.prop⟩ hcs.2)
      split_ifs
      · congr 1; exact Subtype.ext hchoose.symm
  · rintro ⟨w, hw, rfl⟩
    -- w is a fractional packing on the triangle hypergraph
    -- Define packing on triangles: w' t = w (t.val.powersetCard 2)
    let w' : Tri G → ℝ := fun t => w (t.val.powersetCard 2)
    use w'
    refine ⟨?hw', ?rfl⟩
    · constructor
      · intro t; exact hw.1 _
      · intro e
        -- Sum over triangles containing e equals sum over T ∈ triangleHypergraphE G with e ∈ T
        have he : #(Sym2.toFinset e.val) = 2 := by
          rw [Sym2.toFinset]
          have hmem : e.val ∈ G.edgeFinset := e.property
          -- For an edge, the two endpoints are distinct (simple graph is loopless)
          have hn : (Sym2.toMultiset e.val).Nodup := by
            simp only [Sym2.toMultiset]
            haveI := e.property
            generalize hv : e.val = x
            induction x using Sym2.ind with
            | h a b =>
              have hmem : s(a, b) ∈ G.edgeFinset := by
                rw [hv] at this
                exact this
              have hne : a ≠ b := by
                intro hab
                rw [hab] at hmem
                simp at hmem
              simp [Sym2.lift, hne]
          rw [Multiset.toFinset_card_of_nodup hn]
          rw [Sym2.card_toMultiset e.val]
        -- The sum ∑ t with e ∈ triInc t of w' t equals ∑ T ∈ filter (e.val ∈ ·) of w T
        have heq : ∑ o with e ∈ triInc G o, w' o =
                   ∑ T ∈ (triangleHypergraphE G).filter (fun T => e.val.toFinset ∈ T), w T := by
          simp only [Finset.sum_filter]
          rw [show (∑ o : Tri G, if e ∈ triInc G o then w' o else 0) =
              ∑ o ∈ Finset.univ, if e ∈ triInc G o then w' o else 0 from rfl]
          rw [triangleHypergraphE]
          rw [Finset.sum_image (fun x hx y hy hxy => by
            have hinj : ∀ t1 t2 : Tri G, t1.val.powersetCard 2 = t2.val.powersetCard 2 → t1 = t2 := by
              intro ⟨t1, ht1⟩ ⟨t2, ht2⟩ h
              simp [SimpleGraph.mem_cliqueFinset_iff] at ht1 ht2
              exact Subtype.ext (powersetCard_two_inj (by rw [ht1.card_eq]; omega) (by rw [ht2.card_eq]; omega) h)
            have := hinj ⟨x, hx⟩ ⟨y, hy⟩ hxy
            simpa using this)]
          rw [← Finset.sum_coe_sort (s := G.cliqueFinset 3)]
          refine Finset.sum_congr rfl (fun t ht => ?_)
          by_cases h : e.val.toFinset ∈ t.val.powersetCard 2
          · -- pos: e.val.toFinset ∈ t.val.powersetCard 2, so e ∈ triInc t
            have hmem : e ∈ triInc G t := by
              simp only [triInc, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [edgesIn]
              rw [Finset.mem_powersetCard] at h
              exact Finset.mem_filter.mpr ⟨e.property, by simpa [Finset.subset_iff] using h.1⟩
            simp only [hmem, ↓reduceIte, h]
            rfl
          · -- neg: e.val.toFinset ∉ t.val.powersetCard 2, so e ∉ triInc t
            have hni : e ∉ triInc G t := by
              simp only [triInc, Finset.mem_filter, Finset.mem_univ, true_and]
              intro hc
              apply h
              rw [edgesIn] at hc
              have ⟨_, hsub⟩ := Finset.mem_filter.mp hc
              rw [Finset.mem_powersetCard]
              exact ⟨by simpa [Finset.subset_iff] using hsub, he⟩
            simp only [hni, ↓reduceIte, h]
        rw [heq]
        exact hw.2.2 e.val.toFinset
    · rw [triangleHypergraphE]
      rw [Finset.sum_image (fun x hx y hy hxy => by
        have hinj : ∀ t1 t2 : Tri G, t1.val.powersetCard 2 = t2.val.powersetCard 2 → t1 = t2 := by
          intro ⟨t1, ht1⟩ ⟨t2, ht2⟩ h
          simp [SimpleGraph.mem_cliqueFinset_iff] at ht1 ht2
          exact Subtype.ext (powersetCard_two_inj (by rw [ht1.card_eq]; omega) (by rw [ht2.card_eq]; omega) h)
        have := hinj ⟨x, hx⟩ ⟨y, hy⟩ hxy
        simpa using this)]
      rw [← Finset.sum_coe_sort (s := G.cliqueFinset 3)]

/-- **`StrongDualityHyp` — the instantiation.** `τ₃* ≤ ν₃*` follows from the abstract finite LP strong
duality applied to the triangle–edge incidence, via the two value bridges. -/
theorem tau3Star_le_nu3star : tau3Star G ≤ nu3star G := by
  rw [← coverOpt_triInc_eq_tau3Star G, ← packOpt_triInc_eq_nu3star G]
  exact lp_strong_duality (triInc G)

/-- **`StrongDualityHyp` DISCHARGED** — the cover-side strong-duality obligation of the AX1 chain is now
a theorem (via the abstract finite LP duality + the triangle–edge encoding bridges). One of the three AX1
obligations is closed, independently of the nibble. -/
theorem strongDualityHyp_holds : StrongDualityHyp :=
  fun {_} _ _ G _ => tau3Star_le_nu3star G

/-- Weak duality in the reverse direction for the triangle–edge incidence. -/
theorem nu3star_le_tau3Star : nu3star G ≤ tau3Star G := by
  rw [← packOpt_triInc_eq_nu3star G, ← coverOpt_triInc_eq_tau3Star G]
  exact packOpt_le_coverOpt (triInc G) (triInc_nonempty G)

/-- The cover-side AX1 statement yields the unconditional packing-gap formulation. -/
theorem nibbleGapHyp_of_ax1 (hAX1 : AX1Statement) : NibbleGapHyp := by
  intro ε hε
  obtain ⟨n₀, hmain⟩ := hAX1 ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hn
  have hcover := hmain V G hn
  have hweak := nu3star_le_tau3Star G
  linarith

/-- The remaining AX1 obligation is precisely the unconditional packing gap. -/
theorem ax1_of_nibbleGap (hgap : NibbleGapHyp) : AX1Statement :=
  ax1_of_strongDuality_and_nibbleGap strongDualityHyp_holds hgap

end Nibble.AX1
