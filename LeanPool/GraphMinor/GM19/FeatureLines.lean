/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FeatureOrient
public import LeanPool.GraphMinor.GM19.FeatureCode
public import LeanPool.GraphMinor.GM19.CutDrawing2
public import LeanPool.GraphMinor.GM11.Walks
public import LeanPool.GraphMinor.GM07.Defs

/-!
# From a feature to a family of lines

To count features we cut the surface along each feature, with the boundary. So we turn a feature `K`
in a frame `Φ` into a finite family
of lines. The edges of `K` that are lines are lines of the family, and an edge that is an `O`-arc
gives two lines. The vertices of `Φ`
and of `K` cut the boundary into further lines (`exists_feature_lines`). The number of lines is
bounded in terms of the size of `K`, so we
keep count of the edges while we add points to a graph (`exists_counted_line_graph`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function Metric GraphMinor.Surface

local notation "𝕀" => unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-- `IsGraph.add_point`, with a count of the edges. Each new edge lies in an old edge. -/
theorem exists_add_point_counted [T2Space X] {V : Set X} {E : Set (Set X)} (h : IsGraph V E)
  (x : X) :
    ∃ E', IsGraph (insert x V) E' ∧ gr (insert x V) E' = insert x (gr V E) ∧ ⋃₀ E ⊆ ⋃₀ E'
      ∧ E'.ncard ≤ E.ncard + 1 ∧
      ∀ f ∈ E', ∃ e ∈ E, f ⊆ e :=
  h.add_point_counted x

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- `L` is a line in the closure of the edge `e`, with ends vertices or `m`, and with all the rest
in `e`. -/
def GoodEdgeLine (K : Drawing S) (e L : Set S) (m : S) : Prop :=
  ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ (u ∈ K.V ∨ u = m) ∧ (v ∈ K.V ∨ v = m) ∧ L \ {u, v} ⊆ e ∧
    (m ∈ L → m = u ∨ m = v)

/-- The closure of an edge of a drawing is the union of two lines. For an edge that is an `O`-arc,
these are its two parts between its
vertex and a point `m` of the edge. -/
theorem exists_edge_lines (K : Drawing S) {e : Set S} (he : e ∈ K.E) :
    ∃ L₁ L₂ m, L₁ ∪ L₂ = closure e ∧ GoodEdgeLine K e L₁ m ∧ GoodEdgeLine K e L₂ m ∧ (L₁ ≠ L₂
      → L₁ ∩ L₂ ⊆ K.V ∪ {m}) ∧
      (m ∈ K.V ∨ m ∈ e) := by
  have hcd := K.closure_diff_V he
  rcases K.edge_cond e he with ⟨u, v, huv, hcap, hL⟩ | ⟨u, hcap, hF⟩
  · have hu : u ∈ closure e ∩ K.V := hcap ▸ .inl rfl
    have hv : v ∈ closure e ∩ K.V := hcap ▸ .inr rfl
    have hgood : GoodEdgeLine K e (closure e) u := by
      refine ⟨u, v, huv, hL, .inl hu.2, .inl hv.2, ?_, fun _ ↦ .inl rfl⟩
      rintro x ⟨hx, hxn⟩
      rw [← hcd]
      exact ⟨hx, fun hxV ↦ hxn (hcap ▸ ⟨hx, hxV⟩)⟩
    exact ⟨_, _, u, union_self _, hgood, hgood, fun h ↦ absurd rfl h, .inl hu.2⟩
  · have hu : u ∈ closure e ∩ K.V := hcap ▸ rfl
    obtain ⟨a, b, d, ha, hb, -, hab, -, -⟩ := hF.exists_three
    obtain ⟨m, hm, hmu⟩ : ∃ m ∈ closure e, u ≠ m := by
      by_cases h : u = a
      · exact ⟨b, hb, h ▸ hab⟩
      · exact ⟨a, ha, h⟩
    have hoff : ∀ x, x ∈ closure e → x ≠ u → x ∈ e := fun x hx hxu ↦ by
      rw [← hcd]
      refine ⟨hx, fun hxV ↦ hxu ?_⟩
      have h1 : x ∈ closure e ∩ K.V := ⟨hx, hxV⟩
      rw [hcap] at h1
      exact h1
    obtain ⟨A, B, hA, hB, hAB, hi⟩ := hF.lines hu.1 hm hmu
    have hgood : ∀ L, L ⊆ closure e → IsLineWithEnds L u m → GoodEdgeLine K e L m := fun L hLc hl ↦
      ⟨u, m, hmu, hl, .inl hu.2, .inr rfl, fun x hx ↦ hoff x (hLc hx.1) fun h ↦ hx.2
        (.inl h), fun _ ↦ .inr rfl⟩
    refine ⟨A, B, m, hAB, hgood A (hAB ▸ subset_union_left) hA, hgood B
      (hAB ▸ subset_union_right) hB, fun _ ↦ ?_,
      .inr (hoff m hm hmu.symm)⟩
    rw [hi]
    rintro x (rfl | rfl)
    · exact .inl hu.2
    · exact .inr rfl

/-- A family of lines made from a feature `K` in a frame `Φ`, with a dissection that holds the
lines. -/
structure FeatureLines (Φ : Frame S) (K : Drawing S) {m : ℕ} (b : Fin m → 𝕀 → S) (inner : Fin m
  → Prop) : Prop where
  family : IsLineFamily b inner
  cuts : ∃ (V : Set S) (E 𝓕 : Set (Set S)), IsDissection V E 𝓕 ∧ (∀ i, b i 0 ∈ V ∧ b i 1 ∈ V)
    ∧ ∀ i, range (b i) ⊆ gr V E
  eqU : K.U = ⋃ i ∈ {i | inner i}, range (b i)
  vertK : ∀ v ∈ K.V, ∃ i, inner i ∧ (b i 0 = v ∨ b i 1 = v)
  vertΦ : ∀ v ∈ Φ.V, ∃ i, b i 0 = v ∨ b i 1 = v
  border : ∀ x ∈ bd S, ∃ i, ¬ inner i ∧ x ∈ range (b i)
  side : ∀ i, ¬ inner i → ∃ s ∈ Φ.sides, range (b i) \ Φ.V ⊆ s

private theorem feature_half_edges_have_two_marked_ends
    {S : Type u}
    [TopologicalSpace S]
    (Φ : Frame S)
    (K : Drawing S)
    (m : Set S → S)
    (𝓔 : Set (Set S))
    (hgood : ∀ L ∈ 𝓔, ∃ e ∈ Drawing.E K, GoodEdgeLine K e L (m e) ∧ L ⊆ closure e)
    (hoffV : ∀ e ∈ Drawing.E K, ∀ x ∈ e, x ∉ K.V)
    (hoffb : ∀ e ∈ Drawing.E K, ∀ x ∈ e, x ∉ bd S)
    (hoffm : ∀ e ∈ Drawing.E K, ∀ x ∈ e, ∀ e' ∈ Drawing.E K, e' ≠ e → x ≠ m e')
    (hmN : ∀ e ∈ Drawing.E K, m e ∈ (Φ.V ∪ K.V ∪ m '' Drawing.E K)) :
    ∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ (Φ.V ∪ K.V ∪ m '' Drawing.E K) = {u, v} := by
  let N := Φ.V ∪ K.V ∪ m '' Drawing.E K
  intro L hL
  obtain ⟨e, he, ⟨u, v, huv, hl, hu, hv, hop, hmm⟩, -⟩ := hgood L hL
  have huN : u ∈ N := by
    rcases hu with h | h
    · exact .inl (.inr h)
    · exact h ▸ hmN e he
  have hvN : v ∈ N := by
    rcases hv with h | h
    · exact .inl (.inr h)
    · exact h ▸ hmN e he
  refine ⟨u, v, huv, hl, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxL, hxN⟩
    by_contra hxn
    have hxe := hop ⟨hxL, hxn⟩
    rcases hxN with (h | h) | ⟨e', he', rfl⟩
    · exact hoffb e he x hxe (Φ.V_subset h)
    · exact hoffV e he x hxe h
    · by_cases hee : e' = e
      · subst hee
        exact hxn (hmm hxL)
      · exact hoffm e he _ hxe e' he' hee rfl
  · rintro x (rfl | rfl)
    · exact ⟨hl.left_mem, huN⟩
    · exact ⟨hl.right_mem, hvN⟩

private theorem feature_half_edges_meet_at_marked_points
    {S : Type u}
    [TopologicalSpace S]
    (Φ : Frame S)
    (K : Drawing S)
    (L₁ : Set S → Set S)
    (L₂ : Set S → Set S)
    (m : Set S → S)
    (hun : ∀ e ∈ Drawing.E K, L₁ e ∪ L₂ e = closure e)
    (hne12 : ∀ e ∈ Drawing.E K, L₁ e ≠ L₂ e → L₁ e ∩ L₂ e ⊆ K.V ∪ {m e})
    (𝓔 : Set (Set S))
    (hdec : ∀ L ∈ 𝓔, ∃ e ∈ Drawing.E K, L = L₁ e ∨ L = L₂ e)
    (hmN : ∀ e ∈ Drawing.E K, m e ∈ (Φ.V ∪ K.V ∪ m '' Drawing.E K)) :
    ∀ L ∈ 𝓔, ∀ L' ∈ 𝓔, L ≠ L' → L ∩ L' ⊆ (Φ.V ∪ K.V ∪ m '' Drawing.E K) := by
  let N := Φ.V ∪ K.V ∪ m '' Drawing.E K
  intro L hL L' hL' hne x hx
  obtain ⟨e, he, h1⟩ := hdec L hL
  obtain ⟨e', he', h2⟩ := hdec L' hL'
  have hLc : ∀ {A e}, e ∈ K.E → (A = L₁ e ∨ A = L₂ e) → A ⊆ closure e := by
    rintro A e he (rfl | rfl)
    · exact (hun e he) ▸ subset_union_left
    · exact (hun e he) ▸ subset_union_right
  by_cases hxV : x ∈ K.V
  · exact .inl (.inr hxV)
  have hxe : x ∈ e := by
    rw [← K.closure_diff_V he]
    exact ⟨hLc he h1 hx.1, hxV⟩
  have hxe' : x ∈ e' := by
    rw [← K.closure_diff_V he']
    exact ⟨hLc he' h2 hx.2, hxV⟩
  obtain rfl := K.edge_eq_of_mem he he' hxe hxe'
  have hin : x ∈ K.V ∪ {m e} → x ∈ N := by
    rintro (h5 | h5)
    · exact .inl (.inr h5)
    · exact h5 ▸ hmN e he
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact absurd rfl hne
  · exact hin (hne12 e he hne hx)
  · exact hin (hne12 e he hne.symm ⟨hx.2, hx.1⟩)
  · exact absurd rfl hne

private theorem feature_half_edges_meet_boundary_at_marked_points
    {S : Type u}
    [TopologicalSpace S]
    (Φ : Frame S)
    (K : Drawing S)
    (m : Set S → S)
    (𝓔 : Set (Set S))
    (hgood : ∀ L ∈ 𝓔, ∃ e ∈ Drawing.E K, GoodEdgeLine K e L (m e) ∧ L ⊆ closure e)
    (hoffb : ∀ e ∈ Drawing.E K, ∀ x ∈ e, x ∉ bd S)
    (hmN : ∀ e ∈ Drawing.E K, m e ∈ (Φ.V ∪ K.V ∪ m '' Drawing.E K))
    (hline : ∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ (Φ.V ∪ K.V ∪ m '' Drawing.E K) =
      {u, v}) :
    ∀ L ∈ 𝓔, L ∩ bd S ⊆ (Φ.V ∪ K.V ∪ m '' Drawing.E K) := by
  let N := Φ.V ∪ K.V ∪ m '' Drawing.E K
  rintro L hL x ⟨hxL, hxb⟩
  obtain ⟨u, v, -, -, hi⟩ := hline L hL
  obtain ⟨e, he, ⟨u', v', -, hl, hu, hv, hop, -⟩, -⟩ := hgood L hL
  by_cases hx : x ∈ ({u', v'} : Set S)
  · rcases hx with rfl | rfl
    · rcases hu with h | h
      · exact .inl (.inr h)
      · exact h ▸ hmN e he
    · rcases hv with h | h
      · exact .inl (.inr h)
      · exact h ▸ hmN e he
  · exact absurd hxb (hoffb e he x (hop ⟨hxL, hx⟩))

private theorem feature_line_family_cardinality_bound
    {S : Type u}
    [TopologicalSpace S]
    (Φ : Frame S)
    (B : ℕ)
    (K : Drawing S)
    (hEf : (Drawing.E K).Finite)
    (L₁ : Set S → Set S)
    (L₂ : Set S → Set S)
    (m : Set S → S)
    (E : Set (Set S))
    (hcard : E.ncard ≤ B + (Φ.V ∪ K.V ∪ m '' Drawing.E K).ncard + (L₁ '' Drawing.E K ∪ L₂ ''
      Drawing.E K).ncard) :
    Nat.card ↑E ≤ B + Φ.V.ncard + K.V.ncard + 3 * (Drawing.E K).ncard := by
  let 𝓔 := L₁ '' Drawing.E K ∪ L₂ '' Drawing.E K
  let N := Φ.V ∪ K.V ∪ m '' Drawing.E K
  rw [Nat.card_coe_set_eq]
  change E.ncard ≤ B + N.ncard + 𝓔.ncard at hcard
  have h1 : N.ncard ≤ (Φ.V ∪ K.V).ncard + (m '' K.E).ncard := ncard_union_le _ _
  have h2 : (Φ.V ∪ K.V).ncard ≤ Φ.V.ncard + K.V.ncard := ncard_union_le _ _
  have h3 : (m '' K.E).ncard ≤ K.E.ncard := ncard_image_le hEf
  have h4 : 𝓔.ncard ≤ (L₁ '' K.E).ncard + (L₂ '' K.E).ncard := ncard_union_le _ _
  have h5 : (L₁ '' K.E).ncard ≤ K.E.ncard := ncard_image_le hEf
  have h6 : (L₂ '' K.E).ncard ≤ K.E.ncard := ncard_image_le hEf
  omega

/-- Each feature in `Φ` gives a family of lines, and the number of lines is bounded in terms of the
size of the feature. -/
theorem exists_feature_lines (hS : IsSurface S) [ConnectedSpace S] (Φ : Frame S) :
    ∃ B : ℕ, ∀ K : Drawing S, IsFeature Φ K → ∃ (m : ℕ) (b : Fin m → 𝕀 → S) (inner : Fin m → Prop),
      m ≤ B + Φ.V.ncard + K.V.ncard + 3 * K.E.ncard ∧ FeatureLines Φ K b inner := by
  classical
  obtain ⟨B, hB⟩ := exists_counted_line_graph hS
  refine ⟨B, fun K hK ↦ ?_⟩
  have : Nonempty S := inferInstance
  have hEf : K.E.Finite := K.finite_edges
  have hVf : K.V.Finite := K.finite_V
  have hch := fun e (he : e ∈ K.E) ↦ exists_edge_lines K he
  choose! L₁ L₂ m hun hg1 hg2 hne12 hm using hch
  let 𝓔 : Set (Set S) := L₁ '' K.E ∪ L₂ '' K.E
  let N : Set S := Φ.V ∪ K.V ∪ m '' K.E
  have hNf : N.Finite := (Φ.finite_V.union hVf).union (hEf.image _)
  have h𝓔f : 𝓔.Finite := (hEf.image _).union (hEf.image _)
  have hdec : ∀ L ∈ 𝓔, ∃ e ∈ K.E, (L = L₁ e ∨ L = L₂ e) := by
    rintro _ (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, he, .inl rfl⟩
    · exact ⟨e, he, .inr rfl⟩
  have hgood : ∀ L ∈ 𝓔, ∃ e ∈ K.E, GoodEdgeLine K e L (m e) ∧ L ⊆ closure e := by
    intro L hL
    obtain ⟨e, he, rfl | rfl⟩ := hdec L hL
    · exact ⟨e, he, hg1 e he, (hun e he) ▸ subset_union_left⟩
    · exact ⟨e, he, hg2 e he, (hun e he) ▸ subset_union_right⟩
  have hoffV : ∀ e ∈ K.E, ∀ x ∈ e, x ∉ K.V := fun e he x hx ↦ (he.2.1 hx).2
  have hoffb : ∀ e ∈ K.E, ∀ x ∈ e, x ∉ bd S := fun e he x hx ↦ Set.disjoint_left.mp
    (hK.no_border_edges e he) hx
  have hoffm : ∀ e ∈ K.E, ∀ x ∈ e, ∀ e' ∈ K.E, e' ≠ e → x ≠ m e' := by
    rintro e he x hx e' he' hne rfl
    rcases hm e' he' with h | h
    · exact hoffV e he _ hx h
    · exact hne (K.edge_eq_of_mem he' he h hx)
  have hmN : ∀ e ∈ K.E, m e ∈ N := fun e he ↦ .inr ⟨e, he, rfl⟩
  have hline : ∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ N = {u, v} := by
    exact feature_half_edges_have_two_marked_ends (S := S) Φ K m 𝓔 hgood hoffV hoffb hoffm hmN
  have hdisj : ∀ L ∈ 𝓔, ∀ L' ∈ 𝓔, L ≠ L' → L ∩ L' ⊆ N := by
    exact feature_half_edges_meet_at_marked_points (S := S) Φ K L₁ L₂ m hun hne12 𝓔 hdec hmN
  have hbdN : ∀ L ∈ 𝓔, L ∩ bd S ⊆ N := by
    exact feature_half_edges_meet_boundary_at_marked_points (S := S) Φ K m 𝓔 hgood hoffb hmN hline
  have hcl : ∀ e ∈ K.E, closure e ⊆ ⋃₀ 𝓔 := fun e he x hx ↦ by
    rw [← hun e he] at hx
    rcases hx with hx | hx
    · exact ⟨_, .inl ⟨e, he, rfl⟩, hx⟩
    · exact ⟨_, .inr ⟨e, he, rfl⟩, hx⟩
  have hKV : ∀ v ∈ K.V, ∃ e ∈ K.E, v ∈ closure e := fun v hv ↦ by
    obtain ⟨e, he, h⟩ := hK.no_isolated_vertices v hv
    exact ⟨e, he, h.1⟩
  have hNs : N ⊆ bd S ∪ ⋃₀ 𝓔 := by
    rintro x ((h | h) | ⟨e, he, rfl⟩)
    · exact .inl (Φ.V_subset h)
    · obtain ⟨e, he, hc⟩ := hKV x h
      exact .inr (hcl e he hc)
    · rcases hm e he with h | h
      · obtain ⟨e', he', hc⟩ := hKV _ h
        exact .inr (hcl e' he' hc)
      · exact .inr (hcl e he (subset_closure h))
  obtain ⟨V, E, hNV, hg, hV, hUU, h𝓔E, hcard, hnon, hcov⟩ := hB hNf h𝓔f hline hdisj hbdN hNs
  have hbE : bd S ⊆ ⋃₀ E := hUU ▸ subset_union_left
  obtain ⟨V', E', 𝓕, hd, hVV, hEE⟩ := exists_dissection_graph hS hg hV hbE
  have hedge : ∀ e : E, ∃ a : 𝕀 → S, IsArcMap a ∧ range a = e.1 ∧ e.1 ∩ V = {a 0, a 1} := by
    rintro ⟨e, he⟩
    obtain ⟨u, v, -, hl, hi⟩ := hg.edge e he
    obtain ⟨a, ha, h1, h2, h3⟩ := hl.exists_arc
    exact ⟨a, ha, h1, by simp only [hi, h2, h3]⟩
  choose a ha har hai using hedge
  have : Finite E := hg.fine.to_subtype
  let eqv : Fin (Nat.card E) ≃ E := (Finite.equivFin E).symm
  let b : Fin (Nat.card E) → 𝕀 → S := fun i ↦ a (eqv i)
  let inner : Fin (Nat.card E) → Prop := fun i ↦ (eqv i).1 ∈ 𝓔
  have hb : ∀ i, IsArcMap (b i) := fun i ↦ ha _
  have hr : ∀ i, range (b i) = (eqv i).1 := fun i ↦ har _
  have hi : ∀ i, (eqv i).1 ∩ V = {b i 0, b i 1} := fun i ↦ hai _
  have hsurj : ∀ e ∈ E, ∃ i, (eqv i).1 = e := fun e he ↦ ⟨eqv.symm ⟨e, he⟩, by rw
    [Equiv.apply_symm_apply]⟩
  have hendm : ∀ i (t : 𝕀), b i t ∈ V → t = 0 ∨ t = 1 := fun i t ht ↦ by
    have h1 : b i t ∈ (eqv i).1 ∩ V := ⟨hr i ▸ mem_range_self t, ht⟩
    rw [hi] at h1
    rcases h1 with h1 | h1
    · exact .inl ((hb i).2 h1)
    · exact .inr ((hb i).2 h1)
  have hmemV : ∀ (e : Set S) i, (eqv i).1 = e → ∀ x ∈ e, x ∈ V → b i 0 = x ∨ b i 1 = x := by
    rintro e i rfl x hx hxV
    have h1 : x ∈ (eqv i).1 ∩ V := ⟨hx, hxV⟩
    rw [hi] at h1
    rcases h1 with h1 | h1
    · exact .inl h1.symm
    · exact .inr h1.symm
  have hΦV : Φ.V ⊆ V := fun x hx ↦ hNV (.inl (.inl hx))
  have hfam : IsLineFamily b inner := by
    refine ⟨hb, ?_, ?_, ?_, ?_⟩
    · intro i j u v hu hv he
      rw [extI_of_mem _ hu, extI_of_mem _ hv] at he
      by_cases hij : i = j
      · subst hij
        exact .inl ⟨rfl, congrArg Subtype.val ((hb i).2 he)⟩
      · right
        have hne : (eqv i).1 ≠ (eqv j).1 := fun h ↦ hij (eqv.injective (Subtype.ext h))
        have hx : b i ⟨u, hu⟩ ∈ V := hg.disj _ (eqv i).2 _ (eqv j).2 hne
          ⟨hr i ▸ mem_range_self _, by rw [he]; exact hr j ▸ mem_range_self _⟩
        have hx' : b j ⟨v, hv⟩ ∈ V := he ▸ hx
        refine ⟨?_, ?_⟩
        · rcases hendm i _ hx with h | h
          · exact .inl (congrArg Subtype.val h)
          · exact .inr (congrArg Subtype.val h)
        · rcases hendm j _ hx' with h | h
          · exact .inl (congrArg Subtype.val h)
          · exact .inr (congrArg Subtype.val h)
    · intro i hin u hu hbd
      have hu' : u ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hu
      rw [extI_of_mem _ hu'] at hbd
      have hx : b i ⟨u, hu'⟩ ∈ V := hNV (hbdN _ hin ⟨hr i ▸ mem_range_self _, hbd⟩)
      rcases hendm i _ hx with h | h
      · exact hu.1.ne' (congrArg Subtype.val h)
      · exact hu.2.ne (congrArg Subtype.val h)
    · intro i hin u hu
      rw [extI_of_mem _ hu]
      exact hnon _ (eqv i).2 hin (hr i ▸ mem_range_self _)
    · intro x hx
      obtain ⟨e, he, hxe⟩ := hbE hx
      obtain ⟨i, rfl⟩ := hsurj e he
      exact ⟨i, hr i ▸ hxe⟩
  have hbound : Nat.card E ≤ B + Φ.V.ncard + K.V.ncard + 3 * K.E.ncard := by
    exact feature_line_family_cardinality_bound (S := S) Φ B K hEf L₁ L₂ m E hcard
  refine ⟨_, b, inner, hbound, hfam, ⟨V', E', 𝓕, hd, fun i ↦ ?_, fun i ↦ ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : b i 0 ∈ (eqv i).1 ∩ V := hi i ▸ .inl rfl
    have h1 : b i 1 ∈ (eqv i).1 ∩ V := hi i ▸ .inr rfl
    exact ⟨hVV h0.2, hVV h1.2⟩
  · rw [hr]
    exact (subset_sUnion_of_mem (eqv i).2).trans hEE
  · apply Subset.antisymm
    · intro x hx
      rw [K.U_eq] at hx
      have hin : x ∈ ⋃₀ 𝓔 := by
        rcases hx with hx | hx
        · obtain ⟨e, he, hc⟩ := hKV x hx
          exact hcl e he hc
        · obtain ⟨e, he, hc⟩ := mem_iUnion₂.mp hx
          exact hcl e he hc
      obtain ⟨L, hL, hxL⟩ := hin
      obtain ⟨i, hie⟩ := hsurj L (h𝓔E hL)
      refine mem_biUnion (show i ∈ {i | inner i} from ?_) (by rw [hr, hie]; exact hxL)
      change (eqv i).1 ∈ 𝓔
      rw [hie]
      exact hL
    · refine iUnion₂_subset fun i hin ↦ ?_
      rw [hr]
      obtain ⟨e, he, -, hLc⟩ := hgood _ hin
      exact hLc.trans (K.closure_subset_U he)
  · intro v hv
    obtain ⟨e, he, hc⟩ := hKV v hv
    have hvin := hcl e he hc
    obtain ⟨L, hL, hxL⟩ := hvin
    obtain ⟨i, hie⟩ := hsurj L (h𝓔E hL)
    refine ⟨i, ?_, hmemV L i hie v hxL (hNV (.inl (.inr hv)))⟩
    change (eqv i).1 ∈ 𝓔
    rw [hie]
    exact hL
  · intro v hv
    obtain ⟨e, he, hxe⟩ := hbE (Φ.V_subset hv)
    obtain ⟨i, hie⟩ := hsurj e he
    exact ⟨i, hmemV e i hie v hxe (hΦV hv)⟩
  · intro x hx
    obtain ⟨e, he, hne, hxe⟩ := hcov x hx
    obtain ⟨i, rfl⟩ := hsurj e he
    exact ⟨i, hne, hr i ▸ hxe⟩
  · intro i hin
    have h12 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hcon : Continuous (extI (b i)) := continuous_extI (hb i).1
    have hoffE : ∀ u ∈ Ioo (0 : ℝ) 1, extI (b i) u ∉ Φ.V := fun u hu hx ↦ by
      have hu' := Ioo_subset_Icc_self hu
      rw [extI_of_mem _ hu'] at hx
      rcases hendm i _ (hΦV hx) with h | h
      · exact hu.1.ne' (congrArg Subtype.val h)
      · exact hu.2.ne (congrArg Subtype.val h)
    let J : Set ℝ := {u | u ∈ Icc (0 : ℝ) 1 ∧ extI (b i) u ∉ Φ.V}
    have hJ : J.OrdConnected := by
      refine ⟨fun x hx y hy z hz ↦ ?_⟩
      by_cases hzx : z = x
      · exact hzx ▸ hx
      by_cases hzy : z = y
      · exact hzy ▸ hy
      have h0 : 0 < z := lt_of_le_of_lt hx.1.1 (lt_of_le_of_ne hz.1 (Ne.symm hzx))
      have h1 : z < 1 := lt_of_lt_of_le (lt_of_le_of_ne hz.2 hzy) hy.1.2
      exact ⟨⟨h0.le, h1.le⟩, hoffE z ⟨h0, h1⟩⟩
    have hJne : J.Nonempty := ⟨1 / 2, h12, hoffE _ (by norm_num)⟩
    have hpc : IsPathConnected (extI (b i) '' J) := (hJ.convex.isPathConnected hJne).image hcon
    have hsub : extI (b i) '' J ⊆ bd S \ Φ.V := by
      rintro _ ⟨u, hu, rfl⟩
      refine ⟨?_, hu.2⟩
      rw [extI_of_mem _ hu.1]
      exact hnon _ (eqv i).2 hin (hr i ▸ mem_range_self _)
    have hx₀ : extI (b i) (1 / 2) ∈ extI (b i) '' J := ⟨1 / 2, ⟨h12, hoffE _ (by norm_num)⟩, rfl⟩
    refine ⟨_, GM07.pathComponentIn_mem_arcComponentsIn (hsub hx₀), ?_⟩
    rintro _ ⟨⟨t, rfl⟩, hx⟩
    exact hpc.subset_pathComponentIn hx₀ hsub ⟨t, ⟨t.2, by rwa [extI_coe]⟩, extI_coe _ _⟩

end GraphMinor.GM19
