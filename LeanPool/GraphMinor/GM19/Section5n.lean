/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5m
public import LeanPool.GraphMinor.GM19.Poles

/-!
# Graph Minors XIX, proof of (5.4): a path of `Γ*` between two poles gives a line in `Σ`

The paper takes a path of `Γ*` between distinct poles whose vertices are off `bd(Σ)`, except the
first two and the last
two. We take instead a part of any path between distinct poles. Label each vertex of the path that
lies on a cuff, and
each pole, by its cuff. The two ends have different labels, so somewhere two labelled vertices that
follow each other
among the labelled ones have different labels. Two neighbours have the same label if they have
labels, so these two
vertices are not poles, and the part of the path between them is a line in `Σ` that meets `bd(Σ)` in
its two ends.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

namespace GraphWalk

open GraphMinor.Surface.GraphWalk GraphMinor.GM11.GraphWalk

variable {α : Type} {β : Type} {G : Graph α β}

theorem append_assoc' {u v w x : α} (A : Surface.GraphWalk G u v) (B : Surface.GraphWalk G v w)
    (C : Surface.GraphWalk G w x) : (A.append B).append C = A.append (B.append C) := by
  induction A with
  | nil _ => rfl
  | cons h r ih =>
    change Surface.GraphWalk.cons h ((r.append B).append C) = Surface.GraphWalk.cons h (r.append
      (B.append C))
    rw [ih]

theorem IsSimple.of_append {u v w : α} {A : Surface.GraphWalk G u v} {B : Surface.GraphWalk G v w}
    (h : (A.append B).IsSimple) : A.IsSimple ∧ B.IsSimple :=
  Surface.GraphWalk.simple_parts_of_append h

variable {γ : Type} (ℓ : α → Option γ)

/-- The first labelled vertex of a walk that ends at a labelled vertex. -/
theorem exists_first {u v : α} (W : Surface.GraphWalk G u v) {b : γ} (hv : ℓ v = some b) :
    ∃ (y : α) (d : γ) (M : Surface.GraphWalk G u y) (R : Surface.GraphWalk G y v), W = M.append R
      ∧ ℓ y = some d ∧
      ∀ z ∈ M.support, z ≠ y → ℓ z = none := by
  induction W with
  | @nil v hv₀ => exact ⟨v, b, .nil hv₀, .nil hv₀, rfl, hv, fun z hz hne ↦ absurd
    (by simpa using hz) hne⟩
  | @cons u w v e h r ih =>
    cases hu : ℓ u with
    | none =>
      obtain ⟨y, d, M, R, rfl, hy, hM⟩ := ih hv
      refine ⟨y, d, .cons h M, R, rfl, hy, fun z hz hne ↦ ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hu
      · exact hM z hz hne
    | some d =>
      exact ⟨u, d, .nil (h.left_mem), .cons h r, rfl, hu, fun z hz hne ↦ absurd
        (by simpa using hz) hne⟩

/-- Two labelled vertices next to each other among the labelled vertices with different labels. -/
theorem exists_change : ∀ (n : ℕ) {u v : α} (W : Surface.GraphWalk G u v) {a b : γ}, W.length ≤ n
  → ℓ u = some a →
    ℓ v = some b → a ≠ b →
    ∃ (x y : α) (c d : γ) (W₁ : Surface.GraphWalk G u x) (M : Surface.GraphWalk G x y)
      (W₂ : Surface.GraphWalk G y v), W = W₁.append (M.append W₂) ∧ ℓ x = some c ∧ ℓ y = some d
        ∧ c ≠ d ∧
      ∀ z ∈ M.support, z ≠ x → z ≠ y → ℓ z = none := by
  intro n
  induction n with
  | zero =>
    intro u v W a b hl hu hv hne
    obtain rfl := eq_of_length_eq_zero (Nat.le_zero.mp hl)
    exact absurd (Option.some.inj (hu.symm.trans hv)) hne
  | succ n ih =>
    intro u v W a b hl hu hv hne
    cases W with
    | nil h => exact absurd (Option.some.inj (hu.symm.trans hv)) hne
    | @cons _ w _ e h r =>
      obtain ⟨y, d, M, R, rfl, hy, hM⟩ := exists_first ℓ r hv
      by_cases hd : d = a
      · subst hd
        have hlen : R.length ≤ n := by
          rw [length_cons, length_append] at hl
          omega
        obtain ⟨x', y', c, d', W₁, M', W₂, hW, hx', hy', hcd, hz⟩ := ih R hlen hy hv hne
        refine ⟨x', y', c, d', (Surface.GraphWalk.cons h M).append W₁, M', W₂, ?_, hx', hy', hcd,
          hz⟩
        rw [hW, append_assoc']
        rfl
      · refine ⟨u, y, a, d, .nil h.left_mem, .cons h M, R, rfl, hu, hy, fun hc ↦ hd hc.symm,
          fun z hz hzu hzy ↦ ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd rfl hzu
        · exact hM z hz hzy

end GraphWalk

section Comap

variable {S T : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace T] [Nonempty S] {j : S → T}

omit [T2Space S] [Nonempty S] in
theorem isLine_comap (hj : IsClosedEmbedding j) {L : Set S} {u v : S} (h : IsLineWithEnds (j '' L)
  (j u) (j v)) :
    IsLineWithEnds L u v := by
  obtain ⟨f, h0, h1⟩ := h
  let c := hj.isEmbedding.homeomorphImage L
  refine ⟨f.trans c.symm, hj.injective ?_, hj.injective ?_⟩
  · refine Eq.trans ?_ h0
    exact congrArg Subtype.val (c.apply_symm_apply (f 0))
  · refine Eq.trans ?_ h1
    exact congrArg Subtype.val (c.apply_symm_apply (f 1))

omit [T2Space S] [Nonempty S] in
theorem isOArc_comap (hj : IsClosedEmbedding j) {L : Set S} (h : IsOArc (j '' L)) : IsOArc L := by
  obtain ⟨f⟩ := h
  exact ⟨f.trans (hj.isEmbedding.homeomorphImage L).symm⟩

omit [TopologicalSpace S] [T2Space S] [Nonempty S] in
theorem image_comap_sdiff {P : Drawing T} (hP : P.U ⊆ range j) : j '' (j ⁻¹' P.U \ j ⁻¹' P.V)
  = P.U \ P.V := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · rintro ⟨hy, hn⟩
    obtain ⟨x, rfl⟩ := hP hy
    exact ⟨x, ⟨hy, hn⟩, rfl⟩

omit [T2Space S] in
theorem arcs_comap (hj : IsClosedEmbedding j) {P : Drawing T} (hP : P.U ⊆ range j) :
    arcComponentsIn (P.U \ P.V) = image j '' arcComponentsIn (j ⁻¹' P.U \ j ⁻¹' P.V) := by
  have hl : Function.LeftInverse (Function.invFun j) j := Function.leftInverse_invFun hj.injective
  rw [← image_comap_sdiff hP]
  refine GM11.arcComponentsIn_image hj.continuous.continuousOn ?_ fun x _ ↦ hl x
  refine hj.isInducing.continuousOn_iff.mpr (continuousOn_id.congr ?_)
  rintro _ ⟨x, -, rfl⟩
  simp [hl x]

/-- A drawing in `T` that lies in `S`, as a drawing in `S`. -/
noncomputable def Drawing.comap (P : Drawing T) (hj : IsClosedEmbedding j)
  (hP : P.U ⊆ range j) : Drawing S where
  U := j ⁻¹' P.U
  V := j ⁻¹' P.V
  V_subset_U := preimage_mono P.V_subset_U
  isClosed_U := P.isClosed_U.preimage hj.continuous
  finite_V := P.finite_V.preimage hj.injective.injOn
  finite_edges := by
    refine Finite.of_finite_image ?_ (image_injective.mpr hj.injective).injOn
    rw [← arcs_comap hj hP]
    exact P.finite_edges
  edge_cond e he := by
    have hE : j '' e ∈ arcComponentsIn (P.U \ P.V) := by
      rw [arcs_comap hj hP]
      exact mem_image_of_mem _ he
    have hset : ∀ {A : Set T}, closure (j '' e) ∩ P.V = A → j '' (closure e ∩ j ⁻¹' P.V) = A := by
      rintro A rfl
      rw [hj.closure_image_eq]
      ext y
      constructor
      · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
        exact ⟨mem_image_of_mem j hx₁, hx₂⟩
      · rintro ⟨⟨x, hx, rfl⟩, hy⟩
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    rcases P.edge_cond _ hE with ⟨u, v, hne, hs, hl⟩ | ⟨u, hs, ho⟩
    · have hs' := hset hs
      obtain ⟨u', -, rfl⟩ : u ∈ j '' (closure e ∩ j ⁻¹' P.V) := hs' ▸ mem_insert _ _
      obtain ⟨v', -, rfl⟩ : v ∈ j '' (closure e ∩ j ⁻¹' P.V) := hs' ▸ mem_insert_of_mem _ rfl
      refine Or.inl ⟨u', v', fun h ↦ hne (congrArg j h), ?_, isLine_comap hj ?_⟩
      · apply image_injective.mpr hj.injective
        rw [hs', image_pair]
      · rw [← hj.closure_image_eq]
        exact hl
    · have hs' := hset hs
      obtain ⟨u', -, rfl⟩ : u ∈ j '' (closure e ∩ j ⁻¹' P.V) := hs' ▸ rfl
      refine Or.inr ⟨u', ?_, isOArc_comap hj ?_⟩
      · apply image_injective.mpr hj.injective
        rw [hs', image_singleton]
      · rw [← hj.closure_image_eq]
        exact ho

end Comap

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}

/-- What the proof of (5.4) needs of a feature `K`: a line `s t` of size at most `n` from one cuff
to another, that
meets the boundary only in `s` and `t` and meets `Γ` only in vertices. -/
structure IsCrossLine (Φ : Frame S) (Γ : Painting S) (n : ℕ) (K : Drawing S) : Prop where
  feature : IsFeature Φ K
  size : K.V.ncard + K.E.ncard ≤ n
  line : ∃ s t, s ≠ t ∧ K.U ∩ bd S = {s, t} ∧ IsLineWithEnds K.U s t ∧
    connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t
  inter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V
  lines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
    ∧ IsLineWithEnds (closure e) u v

open Classical in
/-- The label of a point of `Σ̂`: the cuff whose closed pasted disc holds the point, if there is
one. -/
noncomputable def cuffLabel (cap : IsCappedSurface S Shat) (x : Shat) : Option (Set S) :=
  if h : ∃ Θ ∈ cuffs S, x ∈ closure (cap.cuffDisc Θ) then some h.choose else none

omit [T2Space S] [T2Space Shat] in
theorem cuffLabel_eq {x : Shat} {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hx : x ∈ closure (cap.cuffDisc Θ)) :
    cuffLabel cap x = some Θ := by
  have h : ∃ Θ ∈ cuffs S, x ∈ closure (cap.cuffDisc Θ) := ⟨Θ, hΘ, hx⟩
  rw [cuffLabel, dite_eq_left_of_eq_true (eq_true h)]
  by_contra hne
  have hne' : h.choose ≠ Θ := fun e ↦ hne (congrArg some e)
  exact disjoint_left.mp (cap.cuffDisc_disjoint _ h.choose_spec.1 _ hΘ hne') h.choose_spec.2 hx

omit [T2Space S] [T2Space Shat] in
theorem cuffLabel_some {x : Shat} {Θ : Set S} (h : cuffLabel cap x = some Θ) :
    Θ ∈ cuffs S ∧ x ∈ closure (cap.cuffDisc Θ) := by
  by_cases h' : ∃ Θ ∈ cuffs S, x ∈ closure (cap.cuffDisc Θ)
  · rw [cuffLabel, dite_eq_left_of_eq_true (eq_true h')] at h
    rw [← Option.some.inj h]
    exact h'.choose_spec
  · rw [cuffLabel, dite_eq_right_of_eq_false (eq_false h')] at h
    exact absurd h (by simp)

variable (hS : IsSurface S) (rad : RadialDrawing cap Γ)
include hS

omit [T2Space S] [T2Space Shat] in
omit hS in
theorem cuffLabel_emb {v : S} {Θ : Set S} (hΘ : Θ ∈ cuffs S) (hv : v ∈ Θ) : cuffLabel cap
  (cap.emb v) = some Θ :=
  cuffLabel_eq hΘ (by
    rw [cap.closure_cuffDisc hΘ]
    exact Or.inr (mem_image_of_mem _ hv))

omit [T2Space S] [T2Space Shat] in
omit hS in
theorem cuffLabel_emb_bd {v : S} (hv : v ∈ bd S) : ∃ Θ ∈ cuffs S, v ∈ Θ ∧ cuffLabel cap (cap.emb v)
  = some Θ := by
  obtain ⟨Θ, hΘ, hvΘ⟩ := sUnion_cuffs (S := S) ▸ hv
  exact ⟨Θ, hΘ, hvΘ, cuffLabel_emb hΘ hvΘ⟩

omit [T2Space S] [T2Space Shat] in
omit hS in
/-- A point of a closed pasted disc that lies in `Σ` lies on the cuff. -/
theorem mem_cuff_of_label {v : S} {Θ : Set S} (h : cuffLabel cap (cap.emb v)
  = some Θ) : Θ ∈ cuffs S ∧ v ∈ Θ := by
  obtain ⟨hΘ, hx⟩ := cuffLabel_some h
  rw [cap.closure_cuffDisc hΘ] at hx
  rcases hx with hx | ⟨y, hy, hyv⟩
  · exact absurd ⟨v, rfl⟩ (cap.notMem_range hΘ hx)
  · exact ⟨hΘ, cap.isEmbedding.injective hyv ▸ hy⟩

include rad in
omit [T2Space S] [T2Space Shat] in
omit hS in
/-- A vertex of `R*` with a label is a pole. -/
theorem pole_of_label {w : Shat} {Θ : Set S} (hw : w ∈ rad.Rstar) (h : cuffLabel cap w = some Θ) :
    w ∈ rad.poles ∧ Θ ∈ cuffs S ∧ rad.regionOf w = cap.cuffDisc Θ := by
  obtain ⟨hΘ, hx⟩ := cuffLabel_some h
  have hG : w ∈ rad.G.U := rad.G.V_subset_U hw.1
  have hwc : w ∈ cap.cuffDisc Θ := by
    rw [cap.closure_cuffDisc hΘ] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hx
    · have hU : cap.emb y ∈ Γ.hatU cap ∩ rad.G.U :=
        ⟨mem_image_of_mem _ (Γ.bd_subset (cuff_subset_bd ⟨Θ, hΘ⟩ hy)), hG⟩
      rw [rad.isPreRadial.1] at hU
      exact absurd hU hw.2
  have hp : w ∈ rad.poles := ⟨hw, fun hsub ↦ cap.notMem_range hΘ hwc (hsub (rad.regionOf_mem hw).2)⟩
  obtain ⟨Θ', hΘ', hreg, hw'⟩ := rad.pole_cases hp
  have : Θ' = Θ := by
    by_contra hne
    exact disjoint_left.mp (cap.cuffDisc_disjoint _ hΘ' _ hΘ hne) (subset_closure hw')
      (subset_closure hwc)
  subst this
  exact ⟨hp, hΘ, hreg⟩

include rad in
omit [T2Space S] [T2Space Shat] in
omit hS in
/-- A vertex joined to a labelled vertex of `R*` has the same label. -/
theorem label_step {e : Set Shat} {v : S} {w : Shat} {Θ : Set S} (he : e ∈ rad.G.E)
  (hw : w ∈ rad.Rstar)
    (hset : closure e ∩ rad.G.V = {cap.emb v, w}) (h : cuffLabel cap w = some Θ) : cuffLabel cap
      (cap.emb v) = some Θ := by
  obtain ⟨hp, hΘ, hreg⟩ := pole_of_label rad hw h
  exact cuffLabel_emb hΘ (rad.pole_edge he hp hΘ hreg hset).2

include rad in
omit [T2Space S] [T2Space Shat] in
omit hS in
/-- Two vertices joined by an edge of `Γ*`, both with labels, have the same label. -/
theorem label_link {e : Set Shat} {x y : Shat} {a b : Set S} (hl : rad.G.toGraph.IsLink e x y)
    (hx : cuffLabel cap x = some a) (hy : cuffLabel cap y = some b) : a = b := by
  obtain ⟨v, hv, w, hw, hset⟩ := rad.edge_ends hl.1
  have hpair : ({x, y} : Set Shat) = {cap.emb v, w} := hl.2.2.2.symm.trans hset
  rcases (Set.pair_eq_pair_iff.mp hpair) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Option.some.inj (hx.symm.trans (label_step rad hl.1 hw hset hy))
  · exact Option.some.inj ((label_step rad hl.1 hw hset hx).symm.trans hy)


omit [T2Space S] [T2Space Shat] in
omit hS in
/-- The two ends of a path of `Γ*`. -/
theorem cuff_of_end {x y : Shat} (M : Surface.GraphWalk rad.G.toGraph x y) {c d : Set S}
    (hx : cuffLabel cap x = some c) (hy : cuffLabel cap y = some d) (hcd : c ≠ d)
    (hz : ∀ z ∈ M.support, z ≠ x → z ≠ y → cuffLabel cap z = none) (hxV : x ∈ rad.G.V) :
    ∃ s ∈ c, cap.emb s = x ∧ c ∈ cuffs S := by
  have hxh : x ∉ rad.Rstar := by
    intro hw
    cases M with
    | nil _ => exact hcd (Option.some.inj (hx.symm.trans hy))
    | @cons _ w' _ e h r =>
      have hset : closure e ∩ rad.G.V = {x, w'} := h.2.2.2
      obtain ⟨v, hv, w, hw', hset'⟩ := rad.edge_ends h.1
      have hpair : ({x, w'} : Set Shat) = {cap.emb v, w} := hset.symm.trans hset'
      have hne : x ≠ w' := by
        intro hxw
        subst hxw
        rw [pair_eq_singleton] at hset
        have h₁ : cap.emb v ∈ ({x} : Set Shat) := by
          rw [← hset, hset']
          exact mem_insert _ _
        exact hw.2 ⟨v, hv, h₁⟩
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := Set.pair_eq_pair_iff.mp hpair
      · exact absurd ⟨v, hv, rfl⟩ hw.2
      · have hl := label_step rad h.1 hw (by rw [hset, pair_comm]) hx
        by_cases hwy : cap.emb v = y
        · exact hcd (Option.some.inj (hl.symm.trans (hwy ▸ hy)))
        · rw [hz _ (by simp [r.start_mem_support]) hne.symm hwy] at hl
          exact absurd hl (by simp)
  obtain ⟨s, hs, rfl⟩ : x ∈ Γ.hatV cap := by
    by_contra hn
    exact hxh ⟨hxV, hn⟩
  obtain ⟨hΘ, hsc⟩ := mem_cuff_of_label hx
  exact ⟨s, hsc, rfl, hΘ⟩

omit [T2Space S] hS in
omit [T2Space Shat] in
theorem exists_walk_of_dist {n : ℕ} (hd : Painting.dist rad ≤ n) :
    ∃ (p₁ p₂ : Shat) (W : Surface.GraphWalk rad.G.toGraph p₁ p₂), p₁ ∈ rad.poles ∧ p₂ ∈ rad.poles
      ∧ p₁ ≠ p₂ ∧ W.IsSimple ∧
      W.length ≤ 2 * n + 1 := by
  set A : Set ℕ∞ := {n : ℕ∞ | ∃ (F : Drawing Shat) (p₁ p₂ : Shat),
    p₁ ∈ rad.poles ∧ p₂ ∈ rad.poles ∧ p₁ ≠ p₂ ∧ F.IsPathOf rad.G p₁ p₂ ∧ n =
      (F.E.ncard / 2 : ℕ)} with hA
  have hne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have : Painting.dist rad = ⊤ := by
      change sInf A = ⊤
      rw [h, sInf_empty]
    rw [this] at hd
    exact absurd hd (by simp)
  obtain ⟨F, p₁, p₂, hp₁, hp₂, hpne, hF, heq⟩ := csInf_mem hne
  have hle : ((F.E.ncard / 2 : ℕ) : ℕ∞) ≤ n := by
    rw [← heq]
    exact hd
  have hle' : F.E.ncard / 2 ≤ n := by exact_mod_cast hle
  obtain ⟨W, hW, -, hE⟩ := hF.2
  obtain ⟨W', hs, he⟩ := hF.1.exists_walk_up W
  refine ⟨p₁, p₂, W', hp₁, hp₂, hpne, by unfold Surface.GraphWalk.IsSimple; rw [hs]; exact hW, ?_⟩
  have hl : W'.length = F.E.ncard := by
    rw [Surface.GraphWalk.length, he, hE]
    have := hW.edges_nodup
    rw [← List.coe_toFinset, ncard_coe_finset, List.toFinset_card_of_nodup this]
  omega

omit hS in
/-- Each vertex of a walk of positive length is an end of one of its edges. -/
theorem exists_edge_at {T : Type} [TopologicalSpace T] {G : Drawing T} {u v : T}
  (W : Surface.GraphWalk G.toGraph u v)
    (hl : 0 < W.length) {z : T} (hz : z ∈ W.support) : ∃ e ∈ W.edges, z ∈ closure e := by
  induction W with
  | nil h => simp [Surface.GraphWalk.length] at hl
  | @cons a b c e h r ih =>
    have hset : closure e ∩ G.V = {a, b} := h.2.2.2
    have ha : a ∈ closure e := (hset.symm ▸ mem_insert a {b} : a ∈ closure e ∩ G.V).1
    have hb : b ∈ closure e := (hset.symm ▸ mem_insert_of_mem a rfl : b ∈ closure e ∩ G.V).1
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨e, by simp, ha⟩
    · by_cases hr : 0 < r.length
      · obtain ⟨f, hf, hzf⟩ := ih hr hz
        exact ⟨f, by simp [hf], hzf⟩
      · cases r with
        | nil _ =>
          obtain rfl : z = b := by simpa using hz
          exact ⟨e, by simp, hb⟩
        | cons h' r' => simp [Surface.GraphWalk.length] at hr

omit hS in
theorem walk_length_support {T : Type} [TopologicalSpace T] {G : Drawing T} {u v : T}
  (W : Surface.GraphWalk G.toGraph u v) :
    W.support.length = W.length + 1 := by
  induction W with
  | nil h => rfl
  | cons h r ih =>
    simp only [Surface.GraphWalk.support_cons, List.length_cons, ih]
    simp [Surface.GraphWalk.length]

omit hS in
/-- A point of a subdrawing that is a vertex of the drawing is a vertex of the subdrawing. -/
theorem IsSubdrawing.mem_V {T : Type} [TopologicalSpace T] {C G : Drawing T}
  (h : C.IsSubdrawing G) {x : T}
    (hx : x ∈ C.U) (hxG : x ∈ G.V) : x ∈ C.V := by
  by_contra hn
  obtain ⟨f, hf, hxf⟩ := C.exists_edge_of_mem hx hn
  exact ((h.2 hf).2.1 hxf).2 hxG

omit [T2Space S] in
/-- **The path of the proof of (5.4).** If `dist(Γ) ≤ n`, then there is a line of `Σ` of size at
most `4n + 3` from one
cuff to another, which meets `U(Γ)` only in vertices. -/
theorem exists_crossLine [Nonempty S] {Φ : Frame S} (hfit : Γ.Fits Φ) {n : ℕ}
  (hd : Painting.dist rad ≤ n) :
    ∃ K : Drawing S, IsCrossLine Φ Γ (4 * n + 3) K := by
  classical
  have hcS : CompactSpace S := hS.1
  obtain ⟨p₁, p₂, W, hp₁, hp₂, hpne, hW, hlen⟩ := exists_walk_of_dist rad hd
  obtain ⟨Θ₁, hΘ₁, hreg₁, hmem₁⟩ := rad.pole_cases hp₁
  obtain ⟨Θ₂, hΘ₂, hreg₂, hmem₂⟩ := rad.pole_cases hp₂
  have hne₁₂ : Θ₁ ≠ Θ₂ := by
    rintro rfl
    obtain ⟨-, -, hG3, -⟩ := id rad.isPreRadial
    exact hpne ((hG3 _ (rad.regionOf_mem hp₁.1).1).unique ⟨(rad.regionOf_mem hp₁.1).2, hp₁.1.1⟩
      ⟨hreg₁.trans hreg₂.symm ▸ (rad.regionOf_mem hp₂.1).2, hp₂.1.1⟩)
  obtain ⟨x, y, c, d, W₁, M, W₂, hWe, hx, hy, hcd, hz⟩ :=
    GraphWalk.exists_change (cuffLabel cap) W.length W le_rfl (cuffLabel_eq hΘ₁
      (subset_closure hmem₁))
      (cuffLabel_eq hΘ₂ (subset_closure hmem₂)) hne₁₂
  have hsimple : M.IsSimple := by
    rw [hWe] at hW
    exact (GraphWalk.IsSimple.of_append (GraphWalk.IsSimple.of_append hW).2).1
  have hxG : x ∈ rad.G.V := M.mem_vertexSet_of_mem_support M.start_mem_support
  have hyG : y ∈ rad.G.V := M.mem_vertexSet_of_mem_support M.end_mem_support
  obtain ⟨s, hsc, rfl, hc⟩ := cuff_of_end rad M hx hy hcd hz hxG
  obtain ⟨t, htc, rfl, hd'⟩ := cuff_of_end rad M.reverse hy hx hcd.symm
    (fun z hz' h₁ h₂ ↦ by
      rw [Surface.GraphWalk.support_reverse, List.mem_reverse] at hz'
      exact hz z hz' h₂ h₁) hyG
  have hst : s ≠ t := by
    rintro rfl
    exact hcd (Option.some.inj (hx.symm.trans hy))
  have hemb : cap.emb s ≠ cap.emb t := fun h ↦ hst (cap.isEmbedding.injective h)
  have hlenpos : 0 < M.length := by
    by_contra hl
    exact hemb (Surface.GraphWalk.eq_of_length_eq_zero (Nat.le_zero.mp (not_lt.mp hl)))
  have hj : IsClosedEmbedding cap.emb := cap.isEmbedding.continuous.isClosedEmbedding
    cap.isEmbedding.injective
  have hnp : ∀ z ∈ M.support, z ∉ rad.poles := by
    intro z hz' hp
    obtain ⟨Θ, hΘ, -, hmem⟩ := rad.pole_cases hp
    have hnr := cap.notMem_range hΘ hmem
    by_cases h₁ : z = cap.emb s
    · exact hnr ⟨s, h₁.symm⟩
    · by_cases h₂ : z = cap.emb t
      · exact hnr ⟨t, h₂.symm⟩
      · have := hz z hz' h₁ h₂
        rw [cuffLabel_eq hΘ (subset_closure hmem)] at this
        exact absurd this (by simp)
  have hrv : ∀ z ∈ rad.G.V, z ∉ rad.poles → z ∈ range cap.emb := by
    intro z hzG hzp
    by_cases hV : z ∈ Γ.hatV cap
    · obtain ⟨v, -, rfl⟩ := hV
      exact mem_range_self v
    · have hw : z ∈ rad.Rstar := ⟨hzG, hV⟩
      exact rad.region_subset_range hw hzp (rad.regionOf_mem hw).2
  set P := walkDrawing rad.G M with hPdef
  have hsub : P.IsSubdrawing rad.G := walkDrawing_isSubdrawing _ _
  have hpath : P.IsPathBetween (cap.emb s) (cap.emb t) := walkDrawing_isPathBetween _ hsimple
  have hPV : ∀ z, z ∈ P.V ↔ z ∈ M.support := fun z ↦ by rw [hPdef, walkDrawing_V]; rfl
  have hPE : ∀ e, e ∈ P.E ↔ e ∈ M.edges := fun e ↦ by rw [hPdef, walkDrawing_E]; rfl
  have hed : ∀ e ∈ P.E, e ⊆ range cap.emb := by
    intro e he
    have heG := hsub.2 he
    obtain ⟨v, hv, w, hw, hset⟩ := rad.edge_ends heG
    have hwP : w ∈ closure e ∩ P.V := by
      rw [hsub.closure_inter_V he, hset]
      exact mem_insert_of_mem _ rfl
    exact rad.edge_subset_range heG hw (hnp w ((hPV w).mp hwP.2)) hset
  have hP : P.U ⊆ range cap.emb := by
    intro z hzU
    rcases (mem_walkDrawing_U _ _).mp hzU with h | ⟨e, he, hze⟩
    · exact hrv z (M.mem_vertexSet_of_mem_support h) (hnp z h)
    · exact closure_minimal (hed e ((hPE e).mpr he)) hj.isClosed_range hze
  let K : Drawing S := GM19.Drawing.comap P hj hP
  have hKU : cap.emb '' K.U = P.U := image_preimage_eq_of_subset hP
  have hKV : cap.emb '' K.V = P.V := image_preimage_eq_of_subset (P.V_subset_U.trans hP)
  have hsK : s ∈ K.V := (hPV _).mpr M.start_mem_support
  have htK : t ∈ K.V := (hPV _).mpr M.end_mem_support
  have hinter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V := by
    rintro x ⟨hxΓ, hxK⟩
    have hU : cap.emb x ∈ Γ.hatU cap ∩ rad.G.U := ⟨mem_image_of_mem _ hxΓ, hsub.U_subset hxK⟩
    rw [rad.isPreRadial.1] at hU
    obtain ⟨v, hv, hvx⟩ := hU
    obtain rfl := cap.isEmbedding.injective hvx
    exact ⟨hv, IsSubdrawing.mem_V hsub hxK (rad.isPreRadial.2.1 ⟨_, hv, rfl⟩)⟩
  have hbdK : K.U ∩ bd S = {s, t} := by
    apply subset_antisymm
    · rintro x ⟨hxK, hxb⟩
      have hxV := (hinter ⟨Γ.bd_subset hxb, hxK⟩).2
      obtain ⟨Θ, hΘ, -, hl⟩ := cuffLabel_emb_bd (cap := cap) hxb
      by_contra hn
      have h₁ : cap.emb x ≠ cap.emb s := fun h ↦ hn (Or.inl (cap.isEmbedding.injective h))
      have h₂ : cap.emb x ≠ cap.emb t := fun h ↦ hn (Or.inr (cap.isEmbedding.injective h))
      rw [hz _ ((hPV _).mp hxV) h₁ h₂] at hl
      exact absurd hl (by simp)
    · rintro x (rfl | rfl)
      · exact ⟨K.V_subset_U hsK, cuff_subset_bd ⟨c, hc⟩ hsc⟩
      · exact ⟨K.V_subset_U htK, cuff_subset_bd ⟨d, hd'⟩ htc⟩
  have hsize : K.V.ncard + K.E.ncard ≤ 4 * n + 3 := by
    have h₁ : K.V.ncard = P.V.ncard := by
      rw [← hKV, ncard_image_of_injective _ cap.isEmbedding.injective]
    have h₂ : K.E.ncard = P.E.ncard := by
      change (arcComponentsIn (cap.emb ⁻¹' P.U \ cap.emb ⁻¹' P.V)).ncard = (arcComponentsIn
        (P.U \ P.V)).ncard
      rw [arcs_comap hj hP, ncard_image_of_injective _ (image_injective.mpr
        cap.isEmbedding.injective)]
    have h₃ : P.V.ncard = M.length + 1 := by
      have : P.V = ↑M.support.toFinset := by
        ext z
        rw [hPV]
        simp
      rw [this, ncard_coe_finset, List.toFinset_card_of_nodup hsimple, walk_length_support]
    have h₄ : P.E.ncard = M.length := by
      have : P.E = ↑M.edges.toFinset := by
        ext e
        rw [hPE]
        simp
      rw [this, ncard_coe_finset, List.toFinset_card_of_nodup hsimple.edges_nodup,
        Surface.GraphWalk.length]
    have h₅ : M.length ≤ W.length := by
      rw [hWe, Surface.GraphWalk.length_append, Surface.GraphWalk.length_append]
      omega
    omega
  have hE' : ∀ e ∈ arcComponentsIn (K.U \ K.V), cap.emb '' e ∈ P.E := fun e he ↦ by
    change cap.emb '' e ∈ arcComponentsIn (P.U \ P.V)
    rw [arcs_comap hj hP]
    exact mem_image_of_mem _ he
  have hfeat : IsFeature Φ K := by
    refine ⟨fun e he ↦ disjoint_left.mpr fun x hxe hxb ↦ ?_, fun v hv ↦ ?_,
      fun s₀ hs₀ ↦ disjoint_left.mpr fun x hx hxs ↦ ?_⟩
    · have hx' : x ∈ K.U ∩ bd S := ⟨(he.2.1 hxe).1, hxb⟩
      rw [hbdK] at hx'
      rcases hx' with h | h
      · exact (he.2.1 hxe).2 (h ▸ hsK)
      · exact (he.2.1 hxe).2 ((mem_singleton_iff.mp h) ▸ htK)
    · obtain ⟨e, he, hve⟩ := exists_edge_at M hlenpos ((hPV _).mp hv)
      have heP : e ∈ arcComponentsIn (P.U \ P.V) := (hPE e).mpr he
      rw [arcs_comap hj hP] at heP
      obtain ⟨e', he', rfl⟩ := heP
      rw [hj.closure_image_eq] at hve
      obtain ⟨v', hv', hvv⟩ := hve
      obtain rfl := cap.isEmbedding.injective hvv
      exact ⟨e', he', hv', fun h ↦ (he'.2.1 h).2 hv⟩
    · have hxb : x ∈ bd S := (hs₀.1.2.1 hxs).1
      have hxV := (hinter ⟨Γ.bd_subset hxb, hx⟩).1
      exact Γ.disjoint_V (hfit.short_sides hs₀) hxs hxV
  refine ⟨K, hfeat, hsize, ⟨s, t, hst, hbdK, isLine_comap hj ?_, ?_⟩, hinter, fun e he ↦ ?_⟩
  · rw [hKU]
    exact isLine_of_isPathBetween hpath hemb
  · obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨b, hb, rfl⟩ := hd'
    rw [← connectedComponentIn_eq hsc, ← connectedComponentIn_eq htc]
    exact hcd
  · rcases K.edge_cond e he with h | ⟨u, hs', -⟩
    · exact h
    · exfalso
      have heP := hE' e he
      have heG := hsub.2 heP
      obtain ⟨v, hv, w, hw, hset⟩ := rad.edge_ends heG
      have hset' : closure (cap.emb '' e) ∩ P.V = {cap.emb v, w} := by
        rw [hsub.closure_inter_V heP, hset]
      have hmem : ∀ z, z ∈ closure (cap.emb '' e) ∩ P.V → z = cap.emb u := by
        rintro z ⟨hz₁, hz₂⟩
        rw [hj.closure_image_eq] at hz₁
        obtain ⟨z', hz', rfl⟩ := hz₁
        have : z' ∈ closure e ∩ K.V := ⟨hz', hz₂⟩
        rw [hs'] at this
        rw [mem_singleton_iff.mp this]
      have h₁ := hmem (cap.emb v) (hset' ▸ mem_insert _ _)
      have h₂ := hmem w (hset' ▸ mem_insert_of_mem _ rfl)
      exact hw.2 ⟨v, hv, h₁.trans h₂.symm⟩

end GraphMinor.GM19
