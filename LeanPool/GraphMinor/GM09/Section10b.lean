/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section10
public import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM09.Section2a
public import LeanPool.GraphMinor.GM09.Section2d
public import LeanPool.GraphMinor.GM09.Section2e
public import LeanPool.GraphMinor.GM09.Section3a
public import LeanPool.GraphMinor.GM09.Section3c
public import LeanPool.GraphMinor.GM09.Section4a
public import LeanPool.GraphMinor.GM09.Section4c
public import LeanPool.GraphMinor.GM09.Section5a
public import LeanPool.GraphMinor.GM09.Section5b
public import LeanPool.GraphMinor.GM09.Section6
public import LeanPool.GraphMinor.GM09.Section7
public import LeanPool.GraphMinor.GM09.Section8
public import LeanPool.GraphMinor.GM09.Section9
public import LeanPool.GraphMinor.GM09.Section11b
public import LeanPool.GraphMinor.GM09.NestUncrossing
public import LeanPool.GraphMinor.GM06.Section2Dual
public import LeanPool.GraphMinor.GM06.Section3Dual
public import LeanPool.GraphMinor.Surface.InvarianceOfDomain
public import LeanPool.GraphMinor.Surface.Crossing
public import Mathlib.Data.Set.Card

/-!
# Graph Minors IX, (5.2) for paths with internal vertices in `ΩBar`

(5.2) asks that the paths `Q_i` have no internal vertex in `ΩBar`. The proof of (10.3) uses (5.2)
for the paths of (10.2), and those may have such vertices. To drop the condition we add to each
vertex of `ΩBar` a new pendant vertex, and let
the new vertices carry the cyclic order (`Society.spiked`). Paths, crosses and crooked transactions
pass between the two societies. The new vertices have degree one, so no path has one as an internal
vertex.
-/

@[expose] public section

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v

variable {α : Type u} {β : Type v}

namespace GraphMinor.GM09

/-- Left injection `α → α ⊕ α` for original vertices. -/
abbrev inlV (x : α) : α ⊕ α := Sum.inl x

/-- Right injection `α → α ⊕ α` for pendant spike vertices. -/
abbrev inrV (x : α) : α ⊕ α := Sum.inr x

/-- Left injection `β → β ⊕ α` for original edges. -/
abbrev inlE (e : β) : β ⊕ α := Sum.inl e

/-- Right injection `α → β ⊕ α` for pendant spike edges. -/
abbrev inrE (x : α) : β ⊕ α := Sum.inr x

theorem inlV_injective : Function.Injective (inlV : α → α ⊕ α) := Sum.inl_injective
theorem inrV_injective : Function.Injective (inrV : α → α ⊕ α) := Sum.inr_injective
theorem inlE_injective : Function.Injective (inlE : β → β ⊕ α) := Sum.inl_injective
theorem inrE_injective : Function.Injective (inrE : α → β ⊕ α) := Sum.inr_injective

/-- Push a `CyclicPerm α` forward along `inrV : α → α ⊕ α`. -/
def CyclicPerm.mapInr (Ω : CyclicPerm α) : CyclicPerm (α ⊕ α) where
  bar := inrV '' Ω.bar
  toFun := Sum.elim inlV (inrV ∘ Ω.toFun)
  finite_bar := Ω.finite_bar.image inrV
  bijOn := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨Ω.toFun x, Ω.bijOn.mapsTo hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact congrArg inrV (Ω.bijOn.injOn hx hy (Sum.inr.inj hxy))
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Ω.bijOn.surjOn hy
      exact ⟨inrV x, ⟨x, hx, rfl⟩, rfl⟩
  single_orbit := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := Ω.single_orbit x hx y hy
    refine ⟨k, ?_⟩
    have h_iter : ∀ n : ℕ, ((Sum.elim inlV (inrV ∘ Ω.toFun))^[n]) (inrV x) =
        inrV ((Ω.toFun^[n]) x) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        rfl
    rw [h_iter k, hk]

theorem CyclicPerm.mapInr_iterate (Ω : CyclicPerm α) (n : ℕ) (x : α) :
    ((Ω.mapInr.toFun)^[n]) (inrV x) = inrV ((Ω.toFun^[n]) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rfl

theorem CyclicPerm.mapInr_firstHitIn_iff (Ω : CyclicPerm α) (X : Set α) (x y : α) :
    Ω.mapInr.FirstHitIn (inrV '' X) (inrV x) (inrV y) ↔ Ω.FirstHitIn X x y := by
  dsimp [CyclicPerm.FirstHitIn]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [Ω.mapInr_iterate k x, inrV_injective.eq_iff, inrV_injective.mem_set_image]
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun j => ?_
  rw [Ω.mapInr_iterate j x, inrV_injective.mem_set_image]

theorem CyclicPerm.mapInr_isClockwiseSeq_iff (Ω : CyclicPerm α) (L : List α) :
    Ω.mapInr.IsClockwiseSeq (L.map inrV) ↔ Ω.IsClockwiseSeq L := by
  dsimp [CyclicPerm.IsClockwiseSeq]
  rw [List.nodup_map_iff inrV_injective]
  refine and_congr_right fun _ => ?_
  have hmem : (∀ v ∈ L.map inrV, v ∈ Ω.mapInr.bar) ↔ ∀ v ∈ L, v ∈ Ω.bar := by
    simp [CyclicPerm.mapInr]
  rw [hmem]
  refine and_congr_right fun _ => ?_
  simp only [List.length_map, List.getElem_map]
  have hset : {v | v ∈ L.map inrV} = inrV '' {v | v ∈ L} := by
    ext z; simp
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [hset, Ω.mapInr_firstHitIn_iff]

theorem CyclicPerm.mapInr_crosses_iff (Ω : CyclicPerm α) (v₁ v₃ v₂ v₄ : α) :
    Ω.mapInr.Crosses (inrV v₁) (inrV v₃) (inrV v₂) (inrV v₄) ↔
      Ω.Crosses v₁ v₃ v₂ v₄ := by
  dsimp [CyclicPerm.Crosses]
  have h1 : [inrV v₁, inrV v₂, inrV v₃, inrV v₄] = [v₁, v₂, v₃, v₄].map inrV := rfl
  have h2 : [inrV v₄, inrV v₃, inrV v₂, inrV v₁] = [v₄, v₃, v₂, v₁].map inrV := rfl
  rw [h1, h2, Ω.mapInr_isClockwiseSeq_iff, Ω.mapInr_isClockwiseSeq_iff]

theorem CyclicPerm.mapInr_interval (Ω : CyclicPerm α) (v₁ v₂ : α) :
    Ω.mapInr.interval (inrV v₁) (inrV v₂) = inrV '' Ω.interval v₁ v₂ := by
  ext z
  rcases z with u | v
  · simp [CyclicPerm.interval, CyclicPerm.IsClockwise3, CyclicPerm.IsClockwiseSeq,
      CyclicPerm.mapInr]
  · simp only [CyclicPerm.interval, mem_ofPred_eq, CyclicPerm.IsClockwise3,
      inrV_injective.mem_set_image]
    have h : [inrV v₁, inrV v, inrV v₂] = [v₁, v, v₂].map inrV := rfl
    rw [h, Ω.mapInr_isClockwiseSeq_iff]
    refine and_congr_left fun _ => ?_
    simp [CyclicPerm.mapInr]

theorem CyclicPerm.mapInr_isFence_iff (Ω : CyclicPerm α) {A B : Set α} :
    Ω.mapInr.IsFence (inrV '' A) (inrV '' B) ↔ Ω.IsFence A B := by
  refine ⟨fun ⟨hA, hB, hdisj, hunion, hno_cr⟩ => ?_, fun ⟨hA, hB, hdisj, hunion, hno_cr⟩ => ?_⟩
  · refine ⟨image_subset_image_iff inrV_injective |>.mp hA,
      image_subset_image_iff inrV_injective |>.mp hB,
      disjoint_of_subset (subset_preimage_image inrV A) (subset_preimage_image inrV B)
        (hdisj.preimage inrV), ?_, ?_⟩
    · apply inrV_injective.image_injective
      rw [image_union, hunion]
      rfl
    · intro a₁ ha₁ a₂ ha₂ ha12 b₁ hb₁ b₂ hb₂ hb12 hcr
      exact hno_cr (inrV a₁) (mem_image_of_mem inrV ha₁) (inrV a₂) (mem_image_of_mem inrV ha₂)
        (inrV_injective.ne ha12) (inrV b₁) (mem_image_of_mem inrV hb₁)
        (inrV b₂) (mem_image_of_mem inrV hb₂) (inrV_injective.ne hb12)
        ((Ω.mapInr_crosses_iff a₁ a₂ b₁ b₂).mpr hcr)
  · refine ⟨image_mono hA, image_mono hB, Set.disjoint_image_of_injective inrV_injective hdisj,
      by rw [← image_union, hunion]; rfl, ?_⟩
    rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨a₂, ha₂, rfl⟩ ha12 _ ⟨b₁, hb₁, rfl⟩ _ ⟨b₂, hb₂, rfl⟩ hb12 hcr
    exact hno_cr a₁ ha₁ a₂ ha₂ (fun h => ha12 (congrArg inrV h))
      b₁ hb₁ b₂ hb₂ (fun h => hb12 (congrArg inrV h))
      ((Ω.mapInr_crosses_iff a₁ a₂ b₁ b₂).mp hcr)

/-- Link relation for the pendant-spike graph `spikeGraph H X`. -/
inductive SpikeIsLink (H : Graph α β) (X : Set α) : (β ⊕ α) → (α ⊕ α) → (α ⊕ α) → Prop
  | inl {e : β} {x y : α} : H.IsLink e x y → SpikeIsLink H X (inlE e) (inlV x) (inlV y)
  | inr_lr {x : α} : x ∈ X ∩ V(H) → SpikeIsLink H X (inrE x) (inlV x) (inrV x)
  | inr_rl {x : α} : x ∈ X ∩ V(H) → SpikeIsLink H X (inrE x) (inrV x) (inlV x)

/-- The pendant-spike extension of a graph `H : Graph α β` along a subset `X ⊆ V(H)`:
adds a pendant vertex `inrV x` and pendant edge `inrE x` linking `inlV x` and `inrV x`
for each `x ∈ X ∩ V(H)`. -/
def spikeGraph (H : Graph α β) (X : Set α) : Graph (α ⊕ α) (β ⊕ α) where
  vertexSet := (inlV '' V(H)) ∪ (inrV '' (X ∩ V(H)))
  edgeSet := (inlE '' E(H)) ∪ (inrE '' (X ∩ V(H)))
  IsLink := SpikeIsLink H X
  isLink_symm _ _ := ⟨fun _ _ h => by
    rcases h with ⟨hlink⟩ | ⟨hx⟩ | ⟨hx⟩
    · exact .inl hlink.symm
    · exact .inr_rl hx
    · exact .inr_lr hx⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := by
    rcases h1 with ⟨hlink₁⟩ | ⟨hx₁⟩ | ⟨hx₁⟩ <;> rcases h2 with ⟨hlink₂⟩ | ⟨hx₂⟩ | ⟨hx₂⟩
    · rcases hlink₁.left_eq_or_eq hlink₂ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  edge_mem_iff_exists_isLink e := by
    constructor
    · rintro (⟨e₀, he₀, rfl⟩ | ⟨x, hx, rfl⟩)
      · obtain ⟨u, v, huv⟩ := H.exists_isLink_of_mem_edgeSet he₀
        exact ⟨inlV u, inlV v, .inl huv⟩
      · exact ⟨inlV x, inrV x, .inr_lr hx⟩
    · rintro ⟨_, _, ⟨hlink⟩ | ⟨hx⟩ | ⟨hx⟩⟩
      · exact Or.inl ⟨_, hlink.edge_mem, rfl⟩
      · exact Or.inr ⟨_, hx, rfl⟩
      · exact Or.inr ⟨_, hx, rfl⟩
  left_mem_of_isLink _ _ _ h := by
    rcases h with ⟨hlink⟩ | ⟨hx⟩ | ⟨hx⟩
    · exact Or.inl ⟨_, hlink.left_mem, rfl⟩
    · exact Or.inl ⟨_, hx.2, rfl⟩
    · exact Or.inr ⟨_, hx, rfl⟩

theorem spikeGraph_isLink_inrV_left {G : Graph α β} {B : Set α} {e : β ⊕ α} {a : α} {w : α ⊕ α}
    (hl : (spikeGraph G B).IsLink e (inrV a) w) :
    a ∈ B ∩ V(G) ∧ e = inrE a ∧ w = inlV a := by
  rcases hl with _ | _ | ⟨ha⟩
  exact ⟨ha, rfl, rfl⟩

theorem spikeGraph_isLink_inlV_left {G : Graph α β} {B : Set α} {e : β ⊕ α} {u : α} {w : α ⊕ α}
    (hl : (spikeGraph G B).IsLink e (inlV u) w) :
    (∃ e₀ v, e = inlE e₀ ∧ w = inlV v ∧ G.IsLink e₀ u v) ∨
      (u ∈ B ∩ V(G) ∧ e = inrE u ∧ w = inrV u) := by
  rcases hl with ⟨hlink⟩ | ⟨hu⟩ | _
  · exact Or.inl ⟨_, _, rfl, rfl, hlink⟩
  · exact Or.inr ⟨hu, rfl, rfl⟩

theorem spikeGraph_le {H G : Graph α β} {X Y : Set α} (hHG : H ≤ G) (hXY : X ∩ V(H) ⊆ Y ∩ V(G)) :
    spikeGraph H X ≤ spikeGraph G Y where
  vertexSet_mono := union_subset_union (image_mono hHG.vertexSet_mono) (image_mono hXY)
  isLink_mono _ _ _ h := by
    rcases h with ⟨hlink⟩ | ⟨hx⟩ | ⟨hx⟩
    · exact .inl (hlink.mono hHG)
    · exact .inr_lr (hXY hx)
    · exact .inr_rl (hXY hx)

/-- The spiked society obtained by attaching a pendant spike to each vertex in `S.Ω.bar`. -/
def Society.spiked (S : Society α β) : Society (α ⊕ α) (β ⊕ α) where
  G := spikeGraph S.G S.Ω.bar
  Ω := S.Ω.mapInr
  finite_V := (S.finite_V.image inlV).union ((S.Ω.finite_bar.inter_of_left _).image inrV)
  finite_E := (S.finite_E.image inlE).union ((S.Ω.finite_bar.inter_of_left _).image inrE)
  bar_subset := by
    rintro _ ⟨x, hx, rfl⟩
    exact Or.inr ⟨x, ⟨hx, S.bar_subset hx⟩, rfl⟩

theorem walk_start_mem_V {G : Graph α β} {u v : α} (W : GraphWalk G u v) : u ∈ V(G) :=
  W.mem_vertexSet_of_mem_support W.start_mem_support

theorem walk_end_mem_V {G : Graph α β} {u v : α} (W : GraphWalk G u v) : v ∈ V(G) :=
  W.mem_vertexSet_of_mem_support W.end_mem_support

/-- Map a walk `W : GraphWalk H u v` into `spikeGraph H X` on the `inlV` vertices. -/
def mapSpikeInl {H : Graph α β} (X : Set α) :
    ∀ {u v : α}, GraphWalk H u v → GraphWalk (spikeGraph H X) (inlV u) (inlV v)
  | _, _, .nil hu => .nil (Or.inl ⟨_, hu, rfl⟩)
  | _, _, .cons hl rest => .cons (.inl hl) (mapSpikeInl X rest)

@[simp]
theorem support_mapSpikeInl {H : Graph α β} (X : Set α) {u v : α} (W : GraphWalk H u v) :
    (mapSpikeInl X W).support = W.support.map inlV := by
  induction W with
  | nil _ => rfl
  | cons _ rest ih =>
    change inlV _ :: (mapSpikeInl X rest).support = inlV _ :: rest.support.map inlV
    rw [ih]

@[simp]
theorem edges_mapSpikeInl {H : Graph α β} (X : Set α) {u v : α} (W : GraphWalk H u v) :
    (mapSpikeInl X W).edges = W.edges.map inlE := by
  induction W with
  | nil _ => rfl
  | cons _ rest ih =>
    change inlE _ :: (mapSpikeInl X rest).edges = inlE _ :: rest.edges.map inlE
    rw [ih]

/-- Extend a walk `W : GraphWalk P a b` with `a, b ∈ V(P)` by the two pendant spikes at `a` and `b`.
-/
def spikePathWalk {P : Graph α β} {a b : α} (W : GraphWalk P a b) :
    GraphWalk (spikeGraph P {a, b}) (inrV a) (inrV b) :=
  have ha : a ∈ ({a, b} : Set α) ∩ V(P) := ⟨Or.inl rfl, walk_start_mem_V W⟩
  have hb : b ∈ ({a, b} : Set α) ∩ V(P) := ⟨Or.inr rfl, walk_end_mem_V W⟩
  GraphWalk.cons (.inr_rl ha)
    ((mapSpikeInl {a, b} W).append
      (GraphWalk.cons (.inr_lr hb) (GraphWalk.nil (Or.inr ⟨b, hb, rfl⟩))))

theorem support_spikePathWalk {P : Graph α β} {a b : α} (W : GraphWalk P a b) :
    (spikePathWalk W).support = inrV a :: (W.support.map inlV ++ [inrV b]) := by
  dsimp [spikePathWalk]
  change inrV a :: ((mapSpikeInl {a, b} W).append _).support = _
  rw [GraphWalk.support_append, support_mapSpikeInl]
  rfl

theorem edges_spikePathWalk {P : Graph α β} {a b : α} (W : GraphWalk P a b) :
    (spikePathWalk W).edges = inrE a :: (W.edges.map inlE ++ [inrE b]) := by
  dsimp [spikePathWalk]
  change inrE a :: ((mapSpikeInl {a, b} W).append _).edges = _
  rw [GraphWalk.edges_append, edges_mapSpikeInl]
  rfl

theorem isSimple_spikePathWalk {P : Graph α β} {a b : α} (W : GraphWalk P a b)
    (hW : W.IsSimple) (hab : a ≠ b) :
    (spikePathWalk W).IsSimple := by
  rw [GraphWalk.IsSimple, support_spikePathWalk, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_map, Sum.inl_ne_inr, and_false, exists_false,
      List.mem_singleton, inrV_injective.eq_iff, false_or]
    exact hab
  · rw [List.nodup_append]
    refine ⟨(List.nodup_map_iff inlV_injective).mpr hW, List.nodup_singleton _, ?_⟩
    intro x hx y hy hxy
    rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
    rw [List.mem_singleton] at hy
    subst hy
    exact Sum.inl_ne_inr hxy

theorem isOmegaPathWithEnds_spikeGraph (S : Society α β) {P : Graph α β} {a b : α}
    (hP : S.IsOmegaPathWithEnds P a b) :
    (Society.spiked S).IsOmegaPathWithEnds (spikeGraph P {a, b}) (inrV a) (inrV b) ∧
      Disjoint (pathInternalVerts (Society.spiked S).G (spikeGraph P {a, b}))
        (Society.spiked S).Ω.bar := by
  obtain ⟨⟨hP_le, W, hW_s, hVP, hEP⟩, hab, ha_bar, hb_bar⟩ := hP
  have hle_spiked : spikeGraph P {a, b} ≤ (Society.spiked S).G := by
    refine spikeGraph_le hP_le ?_
    rintro x ⟨rfl | rfl, hxP⟩
    · exact ⟨ha_bar, hP_le.vertexSet_mono hxP⟩
    · exact ⟨hb_bar, hP_le.vertexSet_mono hxP⟩
  have hpath : IsGraphPathWithEnds (Society.spiked S).G (spikeGraph P {a, b}) (inrV a) (inrV b)
    := by
    refine ⟨hle_spiked, spikePathWalk W, isSimple_spikePathWalk W hW_s hab, ?_, ?_⟩
    · ext z
      rw [support_spikePathWalk]
      simp only [mem_ofPred_eq, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
        or_false]
      rcases z with u | v
      · simp [spikeGraph, hVP]
      · simp only [spikeGraph, mem_union, mem_image, inrV_injective.mem_set_image,
          inrV_injective.eq_iff]
        constructor
        · rintro (⟨x, _, h_eq⟩ | ⟨rfl | rfl, _⟩)
          · exact (Sum.inl_ne_inr h_eq).elim
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
        · rintro (rfl | ⟨x, _, h_eq⟩ | rfl)
          · exact Or.inr ⟨Or.inl rfl, walk_start_mem_V W⟩
          · exact (Sum.inl_ne_inr h_eq).elim
          · exact Or.inr ⟨Or.inr rfl, walk_end_mem_V W⟩
    · ext e
      rw [edges_spikePathWalk]
      simp only [mem_ofPred_eq, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
        or_false]
      rcases e with e₀ | v
      · simp [spikeGraph, hEP]
      · simp only [spikeGraph, mem_union, mem_image, inrE_injective.mem_set_image,
          inrE_injective.eq_iff]
        constructor
        · rintro (⟨x, _, h_eq⟩ | ⟨rfl | rfl, _⟩)
          · exact (Sum.inl_ne_inr h_eq).elim
          · exact Or.inl rfl
          · exact Or.inr (Or.inr rfl)
        · rintro (rfl | ⟨x, _, h_eq⟩ | rfl)
          · exact Or.inr ⟨Or.inl rfl, walk_start_mem_V W⟩
          · exact (Sum.inl_ne_inr h_eq).elim
          · exact Or.inr ⟨Or.inr rfl, walk_end_mem_V W⟩
  have h_omega : (Society.spiked S).IsOmegaPathWithEnds (spikeGraph P {a, b}) (inrV a) (inrV b) :=
    ⟨hpath, inrV_injective.ne hab, mem_image_of_mem inrV ha_bar, mem_image_of_mem inrV hb_bar⟩
  refine ⟨h_omega, ?_⟩
  rw [disjoint_left]
  rintro z ⟨hz_V, hz_not_end⟩ ⟨x, _, rfl⟩
  rw [hpath.pathEnds_eq] at hz_not_end
  rcases hz_V with ⟨u, _, h_eq⟩ | ⟨u, ⟨rfl | rfl, _⟩, h_eq⟩
  · exact Sum.inl_ne_inr h_eq
  · exact hz_not_end (Or.inl h_eq.symm)
  · exact hz_not_end (Or.inr (mem_singleton_iff.mpr h_eq.symm))

/-- Every simple walk in `spikeGraph G B` from `inlV u` to `inrV b` projects to a simple walk in `G`
from `u` to `b` followed by the spike edge `inrE b`. -/
theorem exists_unspike_walk_of_simple_aux {G : Graph α β} {B : Set α}
    {z w : α ⊕ α} (W : GraphWalk (spikeGraph G B) z w) :
    ∀ (u b : α), z = inlV u → w = inrV b → W.IsSimple →
      ∃ W₀ : GraphWalk G u b, W₀.IsSimple ∧
        W.support = W₀.support.map inlV ++ [inrV b] ∧
        W.edges = W₀.edges.map inlE ++ [inrE b] := by
  induction W with
  | nil _ =>
    intro u b hz hw _
    exact (Sum.inl_ne_inr (hz.symm.trans hw)).elim
  | cons hl rest ih =>
    intro u b hz hw hW_s
    subst hz hw
    have hcons_s : inlV u ∉ rest.support ∧ rest.IsSimple := by
      rwa [GraphWalk.IsSimple, GraphWalk.support_cons, List.nodup_cons] at hW_s
    rcases spikeGraph_isLink_inlV_left hl with ⟨e₀, v, rfl, rfl, hlink⟩ | ⟨hu, rfl, rfl⟩
    · obtain ⟨W₀', hW₀'_s, hsupp, hedges⟩ := ih v b rfl rfl hcons_s.2
      refine ⟨.cons hlink W₀', ?_, ?_, ?_⟩
      · rw [GraphWalk.IsSimple, GraphWalk.support_cons, List.nodup_cons]
        refine ⟨fun hu_mem => hcons_s.1 ?_, hW₀'_s⟩
        rw [hsupp, List.mem_append]
        exact Or.inl (List.mem_map_of_mem hu_mem)
      · change inlV u :: rest.support = (u :: W₀'.support).map inlV ++ [inrV b]
        rw [hsupp, List.map_cons, List.cons_append]
      · change inlE e₀ :: rest.edges = (e₀ :: W₀'.edges).map inlE ++ [inrE b]
        rw [hedges, List.map_cons, List.cons_append]
    · rcases rest with _ | ⟨hl₂, rest₂⟩
      · refine ⟨.nil hu.2, by simp [GraphWalk.IsSimple, GraphWalk.support_nil], rfl, rfl⟩
      · exfalso
        obtain ⟨_, _, rfl⟩ := spikeGraph_isLink_inrV_left hl₂
        exact hcons_s.1 (List.mem_cons_of_mem _ rest₂.start_mem_support)

/-- Every simple walk in `spikeGraph G B` from `inrV a` to `inrV b` (`a ≠ b`) is `spikePathWalk W₀`
on support and edges for some simple walk `W₀ : GraphWalk G a b`. -/
theorem exists_unspike_walk_of_simple {G : Graph α β} {B : Set α} {a b : α}
    (W : GraphWalk (spikeGraph G B) (inrV a) (inrV b)) (hW_s : W.IsSimple) (hab : a ≠ b) :
    ∃ W₀ : GraphWalk G a b, W₀.IsSimple ∧
      W.support = inrV a :: (W₀.support.map inlV ++ [inrV b]) ∧
      W.edges = inrE a :: (W₀.edges.map inlE ++ [inrE b]) := by
  rcases W with _ | ⟨hl₁, rest⟩
  · exact (hab rfl).elim
  · have hcons_s : inrV a ∉ rest.support ∧ rest.IsSimple := by
      rwa [GraphWalk.IsSimple, GraphWalk.support_cons, List.nodup_cons] at hW_s
    obtain ⟨_, rfl, rfl⟩ := spikeGraph_isLink_inrV_left hl₁
    obtain ⟨W₀, hW₀_s, hsupp, hedges⟩ := exists_unspike_walk_of_simple_aux rest a b rfl rfl
      hcons_s.2
    exact ⟨W₀, hW₀_s, congrArg (List.cons (inrV a)) hsupp, congrArg (List.cons (inrE a)) hedges⟩

/-- Project a subgraph `K ≤ spikeGraph G B` back to a subgraph of `G`. -/
def unspikeGraph (G : Graph α β) (K : Graph (α ⊕ α) (β ⊕ α)) : Graph α β :=
  (G.induce (inlV ⁻¹' V(K))).restrict (inlE ⁻¹' E(K))

/-- Every `Ω`-path `K` in `Society.spiked S` with ends `inrV a, inrV b` comes from an `Ω`-path `P₀`
in `S` with ends `a, b` such that `V(K) = (inlV '' V(P₀)) ∪ {inrV a, inrV b}` and
`P₀ = unspikeGraph S.G K`. -/
theorem isOmegaPathWithEnds_unspikeGraph (S : Society α β) {K : Graph (α ⊕ α) (β ⊕ α)} {a b : α}
    (hK : (Society.spiked S).IsOmegaPathWithEnds K (inrV a) (inrV b)) :
    S.IsOmegaPathWithEnds (unspikeGraph S.G K) a b ∧
      V(K) = (inlV '' V(unspikeGraph S.G K)) ∪ {inrV a, inrV b} := by
  obtain ⟨⟨hK_le, W_K, hWK_s, hVK, hEK⟩, hab_inr, ha_bar_inr, hb_bar_inr⟩ := hK
  have hab : a ≠ b := fun h => hab_inr (congrArg inrV h)
  have ha_bar : a ∈ S.Ω.bar := (inrV_injective.mem_set_image).mp ha_bar_inr
  have hb_bar : b ∈ S.Ω.bar := (inrV_injective.mem_set_image).mp hb_bar_inr
  have hK_le' : K ≤ spikeGraph S.G S.Ω.bar := hK_le
  obtain ⟨W_sp, hs_sp, he_sp⟩ := exists_walk_up_of_le hK_le' W_K
  have hWsp_s : W_sp.IsSimple := by rw [GraphWalk.IsSimple, hs_sp]; exact hWK_s
  obtain ⟨W₀, hW₀_s, hsupp, hedges⟩ := exists_unspike_walk_of_simple W_sp hWsp_s hab
  have hVK_eq : V(K) = (inlV '' {u | u ∈ W₀.support}) ∪ {inrV a, inrV b} := by
    ext z
    rw [hVK, mem_ofPred_eq, ← hs_sp, hsupp]
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
      or_false, mem_union, mem_image, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    exact or_left_comm
  have hEK_eq : E(K) = (inlE '' {e | e ∈ W₀.edges}) ∪ {inrE a, inrE b} := by
    ext e
    rw [hEK, mem_ofPred_eq, ← he_sp, hedges]
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
      or_false, mem_union, mem_image, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    exact or_left_comm
  have hpre_V : inlV ⁻¹' V(K) = {u | u ∈ W₀.support} := by
    ext u
    simp only [mem_preimage, hVK_eq, mem_union, inlV_injective.mem_set_image, mem_insert_iff,
      mem_singleton_iff, Sum.inl_ne_inr, or_false, mem_ofPred_eq]
  have hpre_E : inlE ⁻¹' E(K) = {e | e ∈ W₀.edges} := by
    ext e
    simp only [mem_preimage, hEK_eq, mem_union, inlE_injective.mem_set_image, mem_insert_iff,
      mem_singleton_iff, Sum.inl_ne_inr, or_false, mem_ofPred_eq]
  have hP₀_eq : unspikeGraph S.G K = walkSubgraph W₀ := by
    rw [walkSubgraph_eq]
    dsimp [unspikeGraph]
    rw [hpre_V, hpre_E]
  have hP₀_path : IsGraphPathWithEnds S.G (unspikeGraph S.G K) a b := by
    rw [hP₀_eq]
    exact isGraphPathWithEnds_walkSubgraph hW₀_s
  refine ⟨⟨hP₀_path, hab, ha_bar, hb_bar⟩, ?_⟩
  rw [hP₀_eq, vertexSet_walkSubgraph, hVK_eq]

/-- Canonical spike of an `Ω`-path `P` in `S` along its ends `pathEnds S.G P`. -/
def spikeOmegaPath (S : Society α β) (P : Graph α β) : Graph (α ⊕ α) (β ⊕ α) :=
  spikeGraph P (pathEnds S.G P)

theorem spikeOmegaPath_eq (S : Society α β) {P : Graph α β} {a b : α}
    (hP : S.IsOmegaPathWithEnds P a b) :
    spikeOmegaPath S P = spikeGraph P {a, b} := by
  dsimp [spikeOmegaPath]
  rw [hP.1.pathEnds_eq]

theorem vertexSet_spikeGraph_of_ends (S : Society α β) {P : Graph α β} {a b : α}
    (hP : S.IsOmegaPathWithEnds P a b) :
    V(spikeGraph P {a, b}) = (inlV '' V(P)) ∪ {inrV a, inrV b} := by
  have ha : a ∈ V(P) := hP.1.left_mem
  have hb : b ∈ V(P) := hP.1.right_mem
  have h_inter : ({a, b} : Set α) ∩ V(P) = {a, b} :=
    inter_eq_left.mpr (by rintro x (rfl | rfl) <;> assumption)
  dsimp [spikeGraph]
  rw [h_inter, image_pair]

theorem disjoint_spikeGraph_iff (S : Society α β) {P₁ P₂ : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (hP₁ : S.IsOmegaPathWithEnds P₁ a₁ b₁) (hP₂ : S.IsOmegaPathWithEnds P₂ a₂ b₂) :
    Disjoint V(spikeGraph P₁ {a₁, b₁}) V(spikeGraph P₂ {a₂, b₂}) ↔ Disjoint V(P₁) V(P₂) := by
  rw [vertexSet_spikeGraph_of_ends S hP₁, vertexSet_spikeGraph_of_ends S hP₂]
  constructor
  · intro hdisj
    rw [disjoint_left] at hdisj ⊢
    intro u hu₁ hu₂
    exact hdisj (Or.inl ⟨u, hu₁, rfl⟩) (Or.inl ⟨u, hu₂, rfl⟩)
  · intro hdisj
    have ha₁ : a₁ ∈ V(P₁) := hP₁.1.left_mem
    have hb₁ : b₁ ∈ V(P₁) := hP₁.1.right_mem
    have ha₂ : a₂ ∈ V(P₂) := hP₂.1.left_mem
    have hb₂ : b₂ ∈ V(P₂) := hP₂.1.right_mem
    rw [disjoint_left] at hdisj ⊢
    rintro z (⟨u, hu₁, rfl⟩ | rfl | rfl) (⟨v, hu₂, h_eq⟩ | h_eq | h_eq)
    · exact hdisj hu₁ (inlV_injective h_eq ▸ hu₂)
    · exact Sum.inl_ne_inr h_eq
    · exact Sum.inl_ne_inr h_eq
    · exact Sum.inl_ne_inr h_eq
    · exact hdisj ha₁ (inrV_injective h_eq ▸ ha₂)
    · exact hdisj ha₁ (inrV_injective h_eq ▸ hb₂)
    · exact Sum.inl_ne_inr h_eq
    · exact hdisj hb₁ (inrV_injective h_eq ▸ ha₂)
    · exact hdisj hb₁ (inrV_injective h_eq ▸ hb₂)

theorem isSeparatingOmegaPath_spikeGraph (S : Society α β) {P : Graph α β} {a b : α}
    (hP : S.IsOmegaPathWithEnds P a b) (hsep : S.IsSeparatingOmegaPath P) :
    (Society.spiked S).IsSeparatingOmegaPath (spikeGraph P {a, b}) := by
  have hP' := (isOmegaPathWithEnds_spikeGraph S hP).1
  refine ⟨⟨inrV a, inrV b, hP'⟩, ?_⟩
  rintro ⟨K, hdisj, s₁', t₁', s₂', t₂', hK_ends, hP''_ends, hcr'⟩
  rcases hK_ends.2.2.1 with ⟨s₁, hs₁_bar, rfl⟩
  rcases hK_ends.2.2.2 with ⟨t₁, ht₁_bar, rfl⟩
  obtain ⟨hP₀_ends, hVK_eq⟩ := isOmegaPathWithEnds_unspikeGraph S hK_ends
  have hdisj₀ : Disjoint V(unspikeGraph S.G K) V(P) := by
    rw [disjoint_left] at hdisj ⊢
    intro u hu₁ hu₂
    exact hdisj (by rw [hVK_eq]; exact Or.inl ⟨u, hu₁, rfl⟩) (Or.inl ⟨u, hu₂, rfl⟩)
  rcases hP''_ends.ends_eq (Society.spiked S) hP' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsep.2 ⟨unspikeGraph S.G K, hdisj₀, s₁, t₁, a, b, hP₀_ends, hP,
      (S.Ω.mapInr_crosses_iff s₁ t₁ a b).mp hcr'⟩
  · exact hsep.2 ⟨unspikeGraph S.G K, hdisj₀, s₁, t₁, b, a, hP₀_ends, hP.symm S,
      (S.Ω.mapInr_crosses_iff s₁ t₁ b a).mp hcr'⟩

theorem isFenceFor_spikeOmegaPath (S : Society α β) {P_set : Set (Graph α β)} {A B : Set α}
    (hfence : S.IsFenceFor P_set A B) :
    (Society.spiked S).IsFenceFor (spikeOmegaPath S '' P_set) (inrV '' A) (inrV '' B) ∧
      InjOn (spikeOmegaPath S) P_set ∧
      (Society.spiked S).transactionEnds (spikeOmegaPath S '' P_set) =
        inrV '' S.transactionEnds P_set := by
  obtain ⟨⟨hpaths, hdisj⟩, hAB, hends⟩ := hfence
  have hinj : InjOn (spikeOmegaPath S) P_set := by
    intro P₁ hP₁ P₂ hP₂ h_eq
    by_contra hne
    obtain ⟨a₁, _, b₁, _, hP₁_ab⟩ := hends P₁ hP₁
    obtain ⟨a₂, _, b₂, _, hP₂_ab⟩ := hends P₂ hP₂
    have hdisj' := (disjoint_spikeGraph_iff S hP₁_ab hP₂_ab).mpr (hdisj hP₁ hP₂ hne)
    rw [← spikeOmegaPath_eq S hP₁_ab, ← spikeOmegaPath_eq S hP₂_ab, h_eq] at hdisj'
    have hmem : inlV a₂ ∈ V(spikeOmegaPath S P₂) := by
      rw [spikeOmegaPath_eq S hP₂_ab, vertexSet_spikeGraph_of_ends S hP₂_ab]
      exact Or.inl ⟨a₂, hP₂_ab.1.left_mem, rfl⟩
    exact disjoint_left.mp hdisj' hmem hmem
  have hfence' : (Society.spiked S).IsFenceFor (spikeOmegaPath S '' P_set) (inrV '' A) (inrV '' B)
    := by
    refine ⟨⟨?_, ?_⟩, (S.Ω.mapInr_isFence_iff).mpr hAB, ?_⟩
    · rintro _ ⟨P, hP, rfl⟩
      obtain ⟨a, _, b, _, hP_ab⟩ := hends P hP
      rw [spikeOmegaPath_eq S hP_ab]
      exact ⟨inrV a, inrV b, (isOmegaPathWithEnds_spikeGraph S hP_ab).1⟩
    · rintro _ ⟨P₁, hP₁, rfl⟩ _ ⟨P₂, hP₂, rfl⟩ hne
      obtain ⟨a₁, _, b₁, _, hP₁_ab⟩ := hends P₁ hP₁
      obtain ⟨a₂, _, b₂, _, hP₂_ab⟩ := hends P₂ hP₂
      rw [spikeOmegaPath_eq S hP₁_ab, spikeOmegaPath_eq S hP₂_ab]
      exact (disjoint_spikeGraph_iff S hP₁_ab hP₂_ab).mpr
        (hdisj hP₁ hP₂ fun h => hne (congrArg (spikeOmegaPath S) h))
    · rintro _ ⟨P, hP, rfl⟩
      obtain ⟨a, ha, b, hb, hP_ab⟩ := hends P hP
      rw [spikeOmegaPath_eq S hP_ab]
      exact ⟨inrV a, mem_image_of_mem inrV ha, inrV b, mem_image_of_mem inrV hb,
        (isOmegaPathWithEnds_spikeGraph S hP_ab).1⟩
  refine ⟨hfence', hinj, ?_⟩
  ext z
  constructor
  · rintro ⟨_, ⟨P, hP, rfl⟩, w, hP'_zw⟩
    obtain ⟨a, _, b, _, hP_ab⟩ := hends P hP
    have hP'_ab : (Society.spiked S).IsOmegaPathWithEnds (spikeOmegaPath S P) (inrV a) (inrV b)
      := by
      rw [spikeOmegaPath_eq S hP_ab]
      exact (isOmegaPathWithEnds_spikeGraph S hP_ab).1
    rcases hP'_ab.ends_eq (Society.spiked S) hP'_zw with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨a, ⟨P, hP, b, hP_ab⟩, rfl⟩
    · exact ⟨b, ⟨P, hP, a, hP_ab.symm S⟩, rfl⟩
  · rintro ⟨a, ⟨P, hP, b, hP_ab⟩, rfl⟩
    refine ⟨spikeOmegaPath S P, mem_image_of_mem _ hP, inrV b, ?_⟩
    rw [spikeOmegaPath_eq S hP_ab]
    exact (isOmegaPathWithEnds_spikeGraph S hP_ab).1

theorem isCrookedTransaction_spikeOmegaPath (S : Society α β) {P_set : Set (Graph α β)}
    (hcr : S.IsCrookedTransaction P_set) :
    (Society.spiked S).IsCrookedTransaction (spikeOmegaPath S '' P_set) ∧
      (spikeOmegaPath S '' P_set).ncard = P_set.ncard := by
  obtain ⟨⟨A, B, hfence⟩, hno_periph⟩ := hcr
  obtain ⟨hfence', hinj, hW_eq⟩ := isFenceFor_spikeOmegaPath S hfence
  refine ⟨⟨⟨inrV '' A, inrV '' B, hfence'⟩, ?_⟩, hinj.ncard_image⟩
  rintro _ ⟨P, hP, rfl⟩ ⟨_, a', b', hP'_ab', hdisj_or⟩
  obtain ⟨a, _, b, _, hP_ab⟩ := hfence.2.2 P hP
  have hP'_ab : (Society.spiked S).IsOmegaPathWithEnds (spikeOmegaPath S P) (inrV a) (inrV b) := by
    rw [spikeOmegaPath_eq S hP_ab]
    exact (isOmegaPathWithEnds_spikeGraph S hP_ab).1
  rcases hP'_ab.ends_eq (Society.spiked S) hP'_ab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply hno_periph P hP ⟨hP, a, b, hP_ab, ?_⟩
    change Disjoint (S.Ω.mapInr.interval (inrV a) (inrV b)) _ ∨
      Disjoint (S.Ω.mapInr.interval (inrV b) (inrV a)) _ at hdisj_or
    rw [S.Ω.mapInr_interval, S.Ω.mapInr_interval, hW_eq,
      Set.disjoint_image_iff inrV_injective, Set.disjoint_image_iff inrV_injective] at hdisj_or
    exact hdisj_or
  · apply hno_periph P hP ⟨hP, b, a, hP_ab.symm S, ?_⟩
    change Disjoint (S.Ω.mapInr.interval (inrV b) (inrV a)) _ ∨
      Disjoint (S.Ω.mapInr.interval (inrV a) (inrV b)) _ at hdisj_or
    rw [S.Ω.mapInr_interval, S.Ω.mapInr_interval, hW_eq,
      Set.disjoint_image_iff inrV_injective, Set.disjoint_image_iff inrV_injective] at hdisj_or
    exact hdisj_or

theorem isCrookedTransaction_unspikeGraph (S : Society α β)
    {P_set' : Set (Graph (α ⊕ α) (β ⊕ α))}
    (hcr' : (Society.spiked S).IsCrookedTransaction P_set') :
    S.IsCrookedTransaction (unspikeGraph S.G '' P_set') ∧
      (unspikeGraph S.G '' P_set').ncard = P_set'.ncard ∧
      (Society.spiked S).transactionEnds P_set' =
        inrV '' S.transactionEnds (unspikeGraph S.G '' P_set') := by
  obtain ⟨⟨A', B', ⟨hpaths', hdisj'⟩, hAB', hends'⟩, hno_periph'⟩ := hcr'
  let A := inrV ⁻¹' A'
  let B := inrV ⁻¹' B'
  have hA'_eq : inrV '' A = A' :=
    image_preimage_eq_of_subset (hAB'.1.trans (image_subset_range inrV S.Ω.bar))
  have hB'_eq : inrV '' B = B' :=
    image_preimage_eq_of_subset (hAB'.2.1.trans (image_subset_range inrV S.Ω.bar))
  have hAB : S.Ω.IsFence A B := by
    apply (S.Ω.mapInr_isFence_iff).mp
    rwa [hA'_eq, hB'_eq]
  have hdisj₀ : ∀ K₁ ∈ P_set', ∀ K₂ ∈ P_set', K₁ ≠ K₂ →
      Disjoint V(unspikeGraph S.G K₁) V(unspikeGraph S.G K₂) := by
    intro K₁ hK₁ K₂ hK₂ hne
    obtain ⟨a₁', _, b₁', _, hK₁_ab'⟩ := hends' K₁ hK₁
    obtain ⟨a₂', _, b₂', _, hK₂_ab'⟩ := hends' K₂ hK₂
    rcases hK₁_ab'.2.2.1 with ⟨a₁, _, rfl⟩
    rcases hK₁_ab'.2.2.2 with ⟨b₁, _, rfl⟩
    rcases hK₂_ab'.2.2.1 with ⟨a₂, _, rfl⟩
    rcases hK₂_ab'.2.2.2 with ⟨b₂, _, rfl⟩
    obtain ⟨_, hVK₁⟩ := isOmegaPathWithEnds_unspikeGraph S hK₁_ab'
    obtain ⟨_, hVK₂⟩ := isOmegaPathWithEnds_unspikeGraph S hK₂_ab'
    have hd : Disjoint V(K₁) V(K₂) := hdisj' hK₁ hK₂ hne
    rw [disjoint_left] at hd ⊢
    intro u hu₁ hu₂
    exact hd (by rw [hVK₁]; exact Or.inl ⟨u, hu₁, rfl⟩) (by rw [hVK₂]; exact Or.inl ⟨u, hu₂, rfl⟩)
  have hinj : InjOn (unspikeGraph S.G) P_set' := by
    intro K₁ hK₁ K₂ hK₂ h_eq
    by_contra hne
    obtain ⟨a₁', _, b₁', _, hK₁_ab'⟩ := hends' K₁ hK₁
    rcases hK₁_ab'.2.2.1 with ⟨a₁, _, rfl⟩
    rcases hK₁_ab'.2.2.2 with ⟨b₁, _, rfl⟩
    obtain ⟨hP₁_ab, _⟩ := isOmegaPathWithEnds_unspikeGraph S hK₁_ab'
    have hmem : a₁ ∈ V(unspikeGraph S.G K₁) := hP₁_ab.1.left_mem
    exact disjoint_left.mp (hdisj₀ K₁ hK₁ K₂ hK₂ hne) hmem (h_eq ▸ hmem)
  have hfence : S.IsFenceFor (unspikeGraph S.G '' P_set') A B := by
    refine ⟨⟨?_, ?_⟩, hAB, ?_⟩
    · rintro _ ⟨K, hK, rfl⟩
      obtain ⟨a', _, b', _, hK_ab'⟩ := hends' K hK
      rcases hK_ab'.2.2.1 with ⟨a, _, rfl⟩
      rcases hK_ab'.2.2.2 with ⟨b, _, rfl⟩
      exact ⟨a, b, (isOmegaPathWithEnds_unspikeGraph S hK_ab').1⟩
    · rintro _ ⟨K₁, hK₁, rfl⟩ _ ⟨K₂, hK₂, rfl⟩ hne
      exact hdisj₀ K₁ hK₁ K₂ hK₂ fun h => hne (congrArg (unspikeGraph S.G) h)
    · rintro _ ⟨K, hK, rfl⟩
      obtain ⟨a', ha', b', hb', hK_ab'⟩ := hends' K hK
      rcases hK_ab'.2.2.1 with ⟨a, _, rfl⟩
      rcases hK_ab'.2.2.2 with ⟨b, _, rfl⟩
      exact ⟨a, ha', b, hb', (isOmegaPathWithEnds_unspikeGraph S hK_ab').1⟩
  have hW_eq : (Society.spiked S).transactionEnds P_set' =
      inrV '' S.transactionEnds (unspikeGraph S.G '' P_set') := by
    ext z
    constructor
    · rintro ⟨K, hK, w, hK_zw⟩
      rcases hK_zw.2.2.1 with ⟨a, _, rfl⟩
      rcases hK_zw.2.2.2 with ⟨b, _, rfl⟩
      exact ⟨a, ⟨unspikeGraph S.G K, mem_image_of_mem _ hK, b,
        (isOmegaPathWithEnds_unspikeGraph S hK_zw).1⟩, rfl⟩
    · rintro ⟨a, ⟨_, ⟨K, hK, rfl⟩, b, hP₀_ab⟩, rfl⟩
      obtain ⟨a', _, b', _, hK_ab'⟩ := hends' K hK
      rcases hK_ab'.2.2.1 with ⟨a₀, _, rfl⟩
      rcases hK_ab'.2.2.2 with ⟨b₀, _, rfl⟩
      have hP₀_ab₀ := (isOmegaPathWithEnds_unspikeGraph S hK_ab').1
      rcases hP₀_ab₀.ends_eq S hP₀_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨K, hK, inrV b, hK_ab'⟩
      · exact ⟨K, hK, inrV b, hK_ab'.symm (Society.spiked S)⟩
  refine ⟨⟨⟨A, B, hfence⟩, ?_⟩, hinj.ncard_image, hW_eq⟩
  rintro _ ⟨K, hK, rfl⟩ ⟨_, a, b, hP₀_ab, hdisj_or⟩
  obtain ⟨a', _, b', _, hK_ab'⟩ := hends' K hK
  rcases hK_ab'.2.2.1 with ⟨a₀, _, rfl⟩
  rcases hK_ab'.2.2.2 with ⟨b₀, _, rfl⟩
  have hP₀_ab₀ := (isOmegaPathWithEnds_unspikeGraph S hK_ab').1
  rcases hP₀_ab₀.ends_eq S hP₀_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply hno_periph' K hK ⟨hK, inrV a, inrV b, hK_ab', ?_⟩
    change Disjoint (S.Ω.mapInr.interval (inrV a) (inrV b)) _ ∨
      Disjoint (S.Ω.mapInr.interval (inrV b) (inrV a)) _
    rw [S.Ω.mapInr_interval, S.Ω.mapInr_interval, hW_eq,
      Set.disjoint_image_iff inrV_injective, Set.disjoint_image_iff inrV_injective]
    exact hdisj_or
  · apply hno_periph' K hK ⟨hK, inrV a, inrV b, hK_ab'.symm (Society.spiked S), ?_⟩
    change Disjoint (S.Ω.mapInr.interval (inrV a) (inrV b)) _ ∨
      Disjoint (S.Ω.mapInr.interval (inrV b) (inrV a)) _
    rw [S.Ω.mapInr_interval, S.Ω.mapInr_interval, hW_eq,
      Set.disjoint_image_iff inrV_injective, Set.disjoint_image_iff inrV_injective]
    exact hdisj_or

/-- Variant of `spikeGraph` with additional isolated pendant vertices `inrV z` for `z ∈ Z ∩ V(H)`
(used to include `inrV (a m), inrV (b m)` in `V(G₂')` without duplicating their spike edges). -/
def spikeGraphWithVerts (H : Graph α β) (X Z : Set α) : Graph (α ⊕ α) (β ⊕ α) where
  vertexSet := (inlV '' V(H)) ∪ (inrV '' ((X ∪ Z) ∩ V(H)))
  edgeSet := (inlE '' E(H)) ∪ (inrE '' (X ∩ V(H)))
  IsLink := SpikeIsLink H X
  isLink_symm := (spikeGraph H X).isLink_symm
  eq_or_eq_of_isLink_of_isLink := (spikeGraph H X).eq_or_eq_of_isLink_of_isLink
  edge_mem_iff_exists_isLink := (spikeGraph H X).edge_mem_iff_exists_isLink
  left_mem_of_isLink _ _ _ h := by
    rcases h with ⟨hlink⟩ | ⟨hx⟩ | ⟨hx⟩
    · exact Or.inl ⟨_, hlink.left_mem, rfl⟩
    · exact Or.inl ⟨_, hx.2, rfl⟩
    · exact Or.inr ⟨_, ⟨Or.inl hx.1, hx.2⟩, rfl⟩

/-- **(5.2) without `hno_int`**: deduced from `Society.theorem_5_2_proof` applied to `Society.spiked
S`. -/
theorem Society.theorem_5_2_without_no_internal (S : Society α β) {p : ℕ} (hp2 : 2 ≤ p)
  (hp3 : p ≠ 3)
    (hex_cr : ∃ P₀ : Set (Graph α β), S.IsCrookedTransaction P₀ ∧ p ≤ P₀.ncard)
    {Q : Fin (p + 4) → Graph α β} {a b : Fin (p + 4) → α}
    (hinj_Q : Function.Injective Q)
    (htr_Q : S.IsTransaction (range Q))
    (hsep_Q : ∀ i : Fin (p + 4), S.IsSeparatingOmegaPath (Q i))
    (hends_Q : ∀ i : Fin (p + 4), S.IsOmegaPathWithEnds (Q i) (a i) (b i))
    (hcw : S.Ω.IsClockwiseSeq ((List.ofFn a).reverse ++ List.ofFn b))
    {G₁ G₂ : Graph α β} (hsep_G : IsGraphSeparation S.G G₁ G₂)
    (hinter_G : V(G₁) ∩ V(G₂) = V(Q ⟨p + 3, by omega⟩))
    (hint_G₁ : S.Ω.interval (a ⟨p + 3, by omega⟩) (b ⟨p + 3, by omega⟩) ⊆ V(G₁))
    (hint_G₂ : S.Ω.interval (b ⟨p + 3, by omega⟩) (a ⟨p + 3, by omega⟩) ⊆ V(G₂)) :
    (∃ P₁ P₂ : Graph α β, S.OmegaPathsCross P₁ P₂ ∧
      Disjoint V(P₁) V(G₂) ∧ Disjoint V(P₂) V(G₂)) ∨
    (∃ P_set : Set (Graph α β), S.IsCrookedTransaction P_set ∧ P_set.ncard = p ∧
      Disjoint (S.Ω.interval (a ⟨0, by omega⟩) (b ⟨0, by omega⟩)) (S.transactionEnds P_set)) := by
  let S' := Society.spiked S
  have : Finite V(S'.G) := S'.finite_V
  have : Finite E(S'.G) := S'.finite_E
  obtain ⟨P₀, hcr_P₀, hp_P₀⟩ := hex_cr
  obtain ⟨hcr_P₀', hcard_P₀'⟩ := isCrookedTransaction_spikeOmegaPath S hcr_P₀
  have hex_cr' : ∃ P₀' : Set (Graph (α ⊕ α) (β ⊕ α)),
      S'.IsCrookedTransaction P₀' ∧ p ≤ P₀'.ncard :=
    ⟨spikeOmegaPath S '' P₀, hcr_P₀', hcard_P₀' ▸ hp_P₀⟩
  let Q' : Fin (p + 4) → Graph (α ⊕ α) (β ⊕ α) := fun i => spikeOmegaPath S (Q i)
  let a' : Fin (p + 4) → α ⊕ α := inrV ∘ a
  let b' : Fin (p + 4) → α ⊕ α := inrV ∘ b
  have hQ'_eq : ∀ i, Q' i = spikeGraph (Q i) {a i, b i} :=
    fun i => spikeOmegaPath_eq S (hends_Q i)
  obtain ⟨A_Q, B_Q, hfence_Q⟩ := htr_Q
  obtain ⟨hfence_Q', hinj_Q_on, _⟩ := isFenceFor_spikeOmegaPath S hfence_Q
  have hrange_Q' : range Q' = spikeOmegaPath S '' range Q :=
    range_comp (spikeOmegaPath S) Q
  have hinj_Q' : Function.Injective Q' :=
    fun i j hij => hinj_Q (hinj_Q_on (mem_range_self i) (mem_range_self j) hij)
  have htr_Q' : S'.IsTransaction (range Q') := by
    rw [hrange_Q']
    exact ⟨inrV '' A_Q, inrV '' B_Q, hfence_Q'⟩
  have hsep_Q' : ∀ i : Fin (p + 4), S'.IsSeparatingOmegaPath (Q' i) := by
    intro i
    rw [hQ'_eq i]
    exact isSeparatingOmegaPath_spikeGraph S (hends_Q i) (hsep_Q i)
  have hno_int' : ∀ i : Fin (p + 4), Disjoint (pathInternalVerts S'.G (Q' i)) S'.Ω.bar := by
    intro i
    rw [hQ'_eq i]
    exact (isOmegaPathWithEnds_spikeGraph S (hends_Q i)).2
  have hends_Q' : ∀ i : Fin (p + 4), S'.IsOmegaPathWithEnds (Q' i) (a' i) (b' i) := by
    intro i
    rw [hQ'_eq i]
    exact (isOmegaPathWithEnds_spikeGraph S (hends_Q i)).1
  have hcw' : S'.Ω.IsClockwiseSeq ((List.ofFn a').reverse ++ List.ofFn b') := by
    have h_list : (List.ofFn a').reverse ++ List.ofFn b' =
        ((List.ofFn a).reverse ++ List.ofFn b).map inrV := by
      rw [List.map_append, List.map_reverse, List.map_ofFn, List.map_ofFn]
    rw [h_list]
    exact (S.Ω.mapInr_isClockwiseSeq_iff _).mpr hcw
  let m : Fin (p + 4) := ⟨p + 3, by omega⟩
  have hm_ends := hends_Q m
  have ha_m_Qm : a m ∈ V(Q m) := hm_ends.1.left_mem
  have hb_m_Qm : b m ∈ V(Q m) := hm_ends.1.right_mem
  have ha_m_G₁ : a m ∈ V(G₁) := (hinter_G ▸ ha_m_Qm : a m ∈ V(G₁) ∩ V(G₂)).1
  have hb_m_G₁ : b m ∈ V(G₁) := (hinter_G ▸ hb_m_Qm : b m ∈ V(G₁) ∩ V(G₂)).1
  have ha_m_G₂ : a m ∈ V(G₂) := (hinter_G ▸ ha_m_Qm : a m ∈ V(G₁) ∩ V(G₂)).2
  have hb_m_G₂ : b m ∈ V(G₂) := (hinter_G ▸ hb_m_Qm : b m ∈ V(G₁) ∩ V(G₂)).2
  let X₁ : Set α := {a m, b m} ∪ S.Ω.interval (a m) (b m)
  let X₂ : Set α := S.Ω.interval (b m) (a m)
  have hfence_m : S.Ω.IsFence X₁ X₂ :=
    S.Ω.isFence_interval_compl hm_ends.2.2.1 hm_ends.2.2.2 hm_ends.2.1
  have hX₁_sub_G₁ : X₁ ⊆ V(G₁) := by
    rintro x ((rfl | rfl) | hx)
    · exact ha_m_G₁
    · exact hb_m_G₁
    · exact hint_G₁ hx
  have hX₁_inter : X₁ ∩ V(G₁) = X₁ := inter_eq_left.mpr hX₁_sub_G₁
  have hX₂_inter : X₂ ∩ V(G₂) = X₂ := inter_eq_left.mpr hint_G₂
  have hX₂Z_inter : (X₂ ∪ {a m, b m}) ∩ V(G₂) = X₂ ∪ {a m, b m} := by
    refine inter_eq_left.mpr ?_
    rintro x (hx | rfl | rfl)
    · exact hint_G₂ hx
    · exact ha_m_G₂
    · exact hb_m_G₂
  have hbar_inter : S.Ω.bar ∩ V(S.G) = S.Ω.bar := inter_eq_left.mpr S.bar_subset
  let G₁' := spikeGraph G₁ X₁
  let G₂' := spikeGraphWithVerts G₂ X₂ {a m, b m}
  have hG₁'_le : G₁' ≤ S'.G :=
    spikeGraph_le hsep_G.1 (by rw [hX₁_inter, hbar_inter]; exact hfence_m.1)
  have hG₂'_le : G₂' ≤ S'.G := by
    refine ⟨union_subset_union (image_mono hsep_G.2.1.vertexSet_mono) (image_mono ?_), ?_⟩
    · rw [hX₂Z_inter, hbar_inter]
      rintro x (hx | rfl | rfl)
      · exact hfence_m.2.1 hx
      · exact hm_ends.2.2.1
      · exact hm_ends.2.2.2
    · intro e x y h
      rcases h with ⟨hlink⟩ | ⟨hx⟩ | ⟨hx⟩
      · exact .inl (hlink.mono hsep_G.2.1)
      · exact .inr_lr ⟨hfence_m.2.1 hx.1, hsep_G.2.1.vertexSet_mono hx.2⟩
      · exact .inr_rl ⟨hfence_m.2.1 hx.1, hsep_G.2.1.vertexSet_mono hx.2⟩
  have hsep_G' : IsGraphSeparation S'.G G₁' G₂' := by
    refine ⟨hG₁'_le, hG₂'_le, ?_, ?_, ?_⟩
    · change ((inlV '' V(G₁)) ∪ (inrV '' (X₁ ∩ V(G₁)))) ∪
        ((inlV '' V(G₂)) ∪ (inrV '' ((X₂ ∪ {a m, b m}) ∩ V(G₂)))) =
        (inlV '' V(S.G)) ∪ (inrV '' (S.Ω.bar ∩ V(S.G)))
      rw [hX₁_inter, hX₂Z_inter, hbar_inter, union_union_union_comm, ← image_union, ← image_union,
        hsep_G.2.2.1]
      congr 2
      apply Subset.antisymm
      · rintro x (hx₁ | hx₂ | rfl | rfl)
        · exact hfence_m.1 hx₁
        · exact hfence_m.2.1 hx₂
        · exact hm_ends.2.2.1
        · exact hm_ends.2.2.2
      · intro x hx
        rw [← hfence_m.2.2.2.1] at hx
        rcases hx with hx₁ | hx₂
        · exact Or.inl hx₁
        · exact Or.inr (Or.inl hx₂)
    · change ((inlE '' E(G₁)) ∪ (inrE '' (X₁ ∩ V(G₁)))) ∪
        ((inlE '' E(G₂)) ∪ (inrE '' (X₂ ∩ V(G₂)))) =
        (inlE '' E(S.G)) ∪ (inrE '' (S.Ω.bar ∩ V(S.G)))
      rw [hX₁_inter, hX₂_inter, hbar_inter, union_union_union_comm, ← image_union, ← image_union,
        hsep_G.2.2.2.1, hfence_m.2.2.2.1]
    · change Disjoint ((inlE '' E(G₁)) ∪ (inrE '' (X₁ ∩ V(G₁))))
        ((inlE '' E(G₂)) ∪ (inrE '' (X₂ ∩ V(G₂))))
      rw [hX₁_inter, hX₂_inter]
      rw [disjoint_left]
      rintro e (⟨e₁, he₁, rfl⟩ | ⟨x₁, hx₁, rfl⟩) (⟨e₂, he₂, h_eq⟩ | ⟨x₂, hx₂, h_eq⟩)
      · exact disjoint_left.mp hsep_G.2.2.2.2 he₁ (inlE_injective h_eq ▸ he₂)
      · exact Sum.inl_ne_inr h_eq.symm
      · exact Sum.inl_ne_inr h_eq
      · exact disjoint_left.mp hfence_m.2.2.1 hx₁ (inrE_injective h_eq ▸ hx₂)
  have hinter_G' : V(G₁') ∩ V(G₂') = V(Q' m) := by
    rw [hQ'_eq m, vertexSet_spikeGraph_of_ends S hm_ends]
    change ((inlV '' V(G₁)) ∪ (inrV '' (X₁ ∩ V(G₁)))) ∩
      ((inlV '' V(G₂)) ∪ (inrV '' ((X₂ ∪ {a m, b m}) ∩ V(G₂)))) =
      (inlV '' V(Q m)) ∪ {inrV (a m), inrV (b m)}
    rw [hX₁_inter, hX₂Z_inter]
    ext z
    rcases z with u | v
    · simp only [mem_inter_iff, mem_union, inlV_injective.mem_set_image, mem_image,
        Sum.inr_ne_inl, and_false, exists_false, or_false, mem_insert_iff, mem_singleton_iff,
        Sum.inl_ne_inr]
      rw [← mem_inter_iff, hinter_G]
    · simp only [mem_inter_iff, mem_union, inrV_injective.mem_set_image, mem_image,
        Sum.inl_ne_inr, and_false, exists_false, false_or, mem_insert_iff, mem_singleton_iff,
        inrV_injective.eq_iff]
      constructor
      · rintro ⟨hv₁ | hv₁, hv₂ | hv₂⟩
        · exact hv₁
        · exact hv₁
        · exact (disjoint_left.mp hfence_m.2.2.1 (Or.inr hv₁) hv₂).elim
        · exact hv₂
      · rintro (rfl | rfl)
        · exact ⟨Or.inl (Or.inl rfl), Or.inr (Or.inl rfl)⟩
        · exact ⟨Or.inl (Or.inr rfl), Or.inr (Or.inr rfl)⟩
  have hint_G₁' : S'.Ω.interval (a' m) (b' m) ⊆ V(G₁') := by
    change S.Ω.mapInr.interval (inrV (a m)) (inrV (b m)) ⊆
      (inlV '' V(G₁)) ∪ (inrV '' (X₁ ∩ V(G₁)))
    rw [S.Ω.mapInr_interval, hX₁_inter]
    exact subset_union_of_subset_right (image_mono subset_union_right) _
  have hint_G₂' : S'.Ω.interval (b' m) (a' m) ⊆ V(G₂') := by
    change S.Ω.mapInr.interval (inrV (b m)) (inrV (a m)) ⊆
      (inlV '' V(G₂)) ∪ (inrV '' ((X₂ ∪ {a m, b m}) ∩ V(G₂)))
    rw [S.Ω.mapInr_interval, hX₂Z_inter]
    exact subset_union_of_subset_right (image_mono subset_union_left) _
  rcases S'.theorem_5_2_proof hp2 hp3 hex_cr' hinj_Q' htr_Q' hsep_Q' hno_int' hends_Q' hcw'
      hsep_G' hinter_G' hint_G₁' hint_G₂' with
    ⟨K₁, K₂, ⟨hdisj_K12, s₁', t₁', s₂', t₂', hK₁_ends, hK₂_ends, hcr_K12⟩, hd_K₁, hd_K₂⟩ |
    ⟨P_set', hcr_P', hcard_P', hdisj_P'⟩
  · left
    rcases hK₁_ends.2.2.1 with ⟨s₁, _, rfl⟩
    rcases hK₁_ends.2.2.2 with ⟨t₁, _, rfl⟩
    rcases hK₂_ends.2.2.1 with ⟨s₂, _, rfl⟩
    rcases hK₂_ends.2.2.2 with ⟨t₂, _, rfl⟩
    obtain ⟨hP₁_ends, hVK₁⟩ := isOmegaPathWithEnds_unspikeGraph S hK₁_ends
    obtain ⟨hP₂_ends, hVK₂⟩ := isOmegaPathWithEnds_unspikeGraph S hK₂_ends
    refine ⟨unspikeGraph S.G K₁, unspikeGraph S.G K₂, ⟨?_, s₁, t₁, s₂, t₂, hP₁_ends, hP₂_ends,
      (S.Ω.mapInr_crosses_iff s₁ t₁ s₂ t₂).mp hcr_K12⟩, ?_, ?_⟩
    · rw [disjoint_left] at hdisj_K12 ⊢
      intro u hu₁ hu₂
      exact hdisj_K12 (by rw [hVK₁]; exact Or.inl ⟨u, hu₁, rfl⟩)
        (by rw [hVK₂]; exact Or.inl ⟨u, hu₂, rfl⟩)
    · rw [disjoint_left] at hd_K₁ ⊢
      intro u hu₁ hu₂
      exact hd_K₁ (by rw [hVK₁]; exact Or.inl ⟨u, hu₁, rfl⟩) (Or.inl ⟨u, hu₂, rfl⟩)
    · rw [disjoint_left] at hd_K₂ ⊢
      intro u hu₁ hu₂
      exact hd_K₂ (by rw [hVK₂]; exact Or.inl ⟨u, hu₁, rfl⟩) (Or.inl ⟨u, hu₂, rfl⟩)
  · right
    obtain ⟨hcr_P, hcard_P, hW_eq⟩ := isCrookedTransaction_unspikeGraph S hcr_P'
    refine ⟨unspikeGraph S.G '' P_set', hcr_P, hcard_P.trans hcard_P', ?_⟩
    let i₀ : Fin (p + 4) := ⟨0, by omega⟩
    change Disjoint (S.Ω.mapInr.interval (inrV (a i₀)) (inrV (b i₀))) _ at hdisj_P'
    rwa [S.Ω.mapInr_interval, hW_eq, Set.disjoint_image_iff inrV_injective] at hdisj_P'

end GraphMinor.GM09
