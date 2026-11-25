/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5p

/-!
# The feature of the proof of (5.5)

`F ∩ Σ` is a feature (`comap_facts`). If `dist(Γ)` is large then `F` meets at most one cuff
(`label_eq`), and the choice of
`F` leaves the shapes of `IsCutShape`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S}


omit [T2Space S] [T2Space Shat] in
/-- A subdrawing of `Γ*` that lies in `Σ` is a feature that meets `Γ` only in vertices. -/
theorem comap_facts [Nonempty S] (rad : RadialDrawing cap Γ) {Φ : Frame S}
  (hfit : Γ.Fits Φ) {P : Drawing Shat} (hsub : P.IsSubdrawing rad.G)
    (hP : P.U ⊆ range cap.emb) (hj : IsClosedEmbedding cap.emb) (hiso : ∀ v ∈ P.V, ∃ e ∈ P.E, v ∈
      closure e) :
    Γ.U ∩ (GM19.Drawing.comap P hj hP).U ⊆ Γ.V ∩ (GM19.Drawing.comap P hj hP).V ∧
    IsFeature Φ (GM19.Drawing.comap P hj hP) ∧
    (∀ e ∈ arcComponentsIn ((GM19.Drawing.comap P hj hP).U \ (GM19.Drawing.comap P hj hP).V), ∃ u
      v, u ≠ v ∧
      closure e ∩ (GM19.Drawing.comap P hj hP).V = {u, v} ∧ IsLineWithEnds (closure e) u v) ∧
    (GM19.Drawing.comap P hj hP).V.ncard = P.V.ncard ∧ (GM19.Drawing.comap P hj hP).E.ncard
      = P.E.ncard := by
  set K : Drawing S := GM19.Drawing.comap P hj hP with hKdef
  have hKU : cap.emb '' K.U = P.U := image_preimage_eq_of_subset hP
  have hKV : cap.emb '' K.V = P.V := image_preimage_eq_of_subset (P.V_subset_U.trans hP)
  have hinter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V := by
    rintro x ⟨hxΓ, hxK⟩
    have hU : cap.emb x ∈ Γ.hatU cap ∩ rad.G.U := ⟨mem_image_of_mem _ hxΓ, hsub.U_subset hxK⟩
    rw [rad.isPreRadial.1] at hU
    obtain ⟨v, hv, hvx⟩ := hU
    obtain rfl := cap.isEmbedding.injective hvx
    exact ⟨hv, IsSubdrawing.mem_V hsub hxK (rad.isPreRadial.2.1 ⟨_, hv, rfl⟩)⟩
  have hE' : ∀ e ∈ arcComponentsIn (K.U \ K.V), cap.emb '' e ∈ P.E := fun e he ↦ by
    change cap.emb '' e ∈ arcComponentsIn (P.U \ P.V)
    rw [arcs_comap hj hP]
    exact mem_image_of_mem _ he
  have hfeat : IsFeature Φ K := by
    refine ⟨fun e he ↦ disjoint_left.mpr fun x hxe hxb ↦ ?_, fun v hv ↦ ?_,
      fun s₀ hs₀ ↦ disjoint_left.mpr fun x hx hxs ↦ ?_⟩
    · exact (he.2.1 hxe).2 (hinter ⟨Γ.bd_subset hxb, (he.2.1 hxe).1⟩).2
    · obtain ⟨e, he, hve⟩ := hiso _ hv
      have heP : e ∈ arcComponentsIn (P.U \ P.V) := he
      rw [arcs_comap hj hP] at heP
      obtain ⟨e', he', rfl⟩ := heP
      rw [hj.closure_image_eq] at hve
      obtain ⟨v', hv', hvv⟩ := hve
      obtain rfl := cap.isEmbedding.injective hvv
      exact ⟨e', he', hv', fun h ↦ (he'.2.1 h).2 hv⟩
    · have hxb : x ∈ bd S := (hs₀.1.2.1 hxs).1
      have hxV := (hinter ⟨Γ.bd_subset hxb, hx⟩).1
      exact Γ.disjoint_V (hfit.short_sides hs₀) hxs hxV
  refine ⟨hinter, hfeat, fun e he ↦ ?_, ?_, ?_⟩
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
  · rw [← hKV, ncard_image_of_injective _ cap.isEmbedding.injective]
  · change (arcComponentsIn (cap.emb ⁻¹' P.U \ cap.emb ⁻¹' P.V)).ncard = (arcComponentsIn
      (P.U \ P.V)).ncard
    rw [arcs_comap hj hP, ncard_image_of_injective _ (image_injective.mpr
      cap.isEmbedding.injective)]

variable (hS : IsSurface S) (rad : RadialDrawing cap Γ) (h3 : Γ.IsInternallyThreeConnected)
include hS

omit [T2Space Shat] in
/-- A vertex of `Γ*` with a label is the pole of that cuff or is next to it. -/
theorem exists_walk_to_pole {x p : Shat} {c : Set S} (hx : x ∈ rad.G.V) (hl : cuffLabel cap x
  = some c)
    (hp : p ∈ rad.poles) (hreg : rad.regionOf p = cap.cuffDisc c) (h3 :
      Γ.IsInternallyThreeConnected) :
    ∃ W : Surface.GraphWalk rad.G.toGraph p x, W.length ≤ 1 := by
  classical
  obtain ⟨hc, hxc⟩ := cuffLabel_some hl
  by_cases hV : x ∈ Γ.hatV cap
  · obtain ⟨v, hv, rfl⟩ := hV
    obtain ⟨-, hvc⟩ := mem_cuff_of_label hl
    obtain ⟨e, he, hs⟩ := rad.exists_pole_edge hS h3 hp hc hreg hv hvc
    exact ⟨.cons (⟨he, hp.1.1, hx, by rw [Set.pair_comm]; exact hs⟩ : rad.G.toGraph.IsLink e p
      (cap.emb v)) (.nil hx),
      by simp [Surface.GraphWalk.length, Surface.GraphWalk.edges]⟩
  · have hw : x ∈ rad.Rstar := ⟨hx, hV⟩
    have hxd : x ∈ cap.cuffDisc c := by
      rw [cap.closure_cuffDisc hc] at hxc
      rcases hxc with h | ⟨y, hy, rfl⟩
      · exact h
      · exfalso
        have hr := (rad.regionOf_mem hw).2
        have hU : cap.emb y ∈ Γ.hatU cap := mem_image_of_mem _ (Γ.bd_subset
          (cuff_subset_bd ⟨c, hc⟩ hy))
        exact (connectedComponentIn_subset _ _ hr) hU
    obtain ⟨-, -, hG3, -⟩ := id rad.isPreRadial
    have hpr := rad.regionOf_mem hp.1
    obtain rfl : x = p := (hG3 _ hpr.1).unique ⟨hreg ▸ hxd, hx⟩ ⟨hpr.2, hp.1.1⟩
    exact ⟨.nil hx, by simp [Surface.GraphWalk.length, Surface.GraphWalk.edges]⟩

/-- If `dist(Γ)` is large, then a short circuit meets one cuff at most. -/
theorem label_eq {n : ℕ} (hd : ((n + 1 : ℕ) : ℕ∞) < Painting.dist rad) {F : Drawing Shat}
  (hF : IsShortCircuit rad n F)
    (h3 : Γ.IsInternallyThreeConnected) {x y : Shat} (hx : x ∈ F.V) (hy : y ∈ F.V) {c d : Set S}
    (hlx : cuffLabel cap x = some c) (hly : cuffLabel cap y = some d) : c = d := by
  classical
  by_contra hcd
  have hxy : x ≠ y := by
    rintro rfl
    exact hcd (Option.some.inj (hlx.symm.trans hly))
  obtain ⟨hc, -⟩ := cuffLabel_some hlx
  obtain ⟨hd', -⟩ := cuffLabel_some hly
  obtain ⟨p₁, hp₁, hm₁, hr₁⟩ := rad.exists_pole hc
  obtain ⟨p₂, hp₂, hm₂, hr₂⟩ := rad.exists_pole hd'
  have hpne : p₁ ≠ p₂ := by
    rintro rfl
    exact disjoint_left.1 (cap.cuffDisc_disjoint _ hc _ hd' hcd) (subset_closure hm₁)
      (subset_closure hm₂)
  obtain ⟨hFG, hFc⟩ := hF.1
  obtain ⟨W₁, hW₁⟩ := exists_walk_to_pole hS rad (hFG.1 hx) hlx hp₁ hr₁ h3
  obtain ⟨W₂, hW₂⟩ := exists_walk_to_pole hS rad (hFG.1 hy) hly hp₂ hr₂ h3
  obtain ⟨P, -, hP, -, sP, -, -, -, -, -, heq⟩ := hFc.exists_two_paths hx hy hxy
  obtain ⟨M, hMs, -, hME⟩ := hP
  obtain ⟨M', hs, he⟩ := (sP.trans hFG).exists_walk_up M
  have hMl : M'.length ≤ F.E.ncard := by
    have h₁ : P.E.ncard = M'.length := by
      rw [hME, Surface.GraphWalk.length, he, ← List.coe_toFinset, ncard_coe_finset,
        List.toFinset_card_of_nodup hMs.edges_nodup]
    rw [← h₁]
    exact ncard_le_ncard sP.2 F.finite_edges
  let T := (W₁.append M').append W₂.reverse
  obtain ⟨T', hTs, -, hTe⟩ := GraphWalk.exists_isSimple T
  have hTl : T'.length ≤ T.length := by
    have h₁ : T'.edges.toFinset ⊆ T.edges.toFinset := fun e he' ↦ by
      rw [List.mem_toFinset] at he' ⊢
      exact hTe e he'
    have h₂ := Finset.card_le_card h₁
    rw [List.toFinset_card_of_nodup hTs.edges_nodup] at h₂
    exact h₂.trans (List.toFinset_card_le _)
  have hTlen : T.length ≤ F.E.ncard + 2 := by
    have h₁ : W₂.reverse.length = W₂.length := by
      rw [Surface.GraphWalk.length, Surface.GraphWalk.length, Surface.GraphWalk.edges_reverse,
        List.length_reverse]
    simp only [T, Surface.GraphWalk.length_append, h₁]
    omega
  set R := walkDrawing rad.G T' with hR
  have hRp : GM19.Drawing.IsPathOf R rad.G p₁ p₂ := ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hTs⟩
  have hRE : R.E.ncard = T'.length := by
    rw [hR, walkDrawing_E]
    have : {e | e ∈ T'.edges} = ↑T'.edges.toFinset := by
      ext e
      simp
    rw [this, ncard_coe_finset, List.toFinset_card_of_nodup hTs.edges_nodup,
      Surface.GraphWalk.length]
  have hle : Painting.dist rad ≤ ((R.E.ncard / 2 : ℕ) : ℕ∞) := sInf_le ⟨R, p₁, p₂, hp₁, hp₂, hpne,
    hRp, rfl⟩
  have hb : R.E.ncard / 2 ≤ n + 1 := by
    have := hF.2.2
    omega
  exact absurd (hle.trans (by exact_mod_cast hb)) (not_le.2 hd)

/-- The part `K` of a circuit `F` of `Γ*` in `Σ`. -/
structure IsCircuitPart (cap : IsCappedSurface S Shat) (Φ : Frame S) (Γ : Painting S)
  (F : Drawing Shat) (K : Drawing S) : Prop where
  feature : IsFeature Φ K
  inter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V
  lines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
    ∧ IsLineWithEnds (closure e) u v
  V_le : K.V.ncard ≤ F.V.ncard
  E_le : K.E.ncard ≤ F.E.ncard
  form : IsCutFormOf cap K F.U

/-- What the proof of (5.5) needs of a feature `K`. Its size is at most `n`, it meets `Γ` only in
vertices, and it has two
vertices of `Γ`. -/
structure IsCutShape (cap : IsCappedSurface S Shat) (Φ : Frame S) (Γ : Painting S) (n : ℕ)
  (K : Drawing S) : Prop where
  feature : IsFeature Φ K
  size : K.V.ncard + K.E.ncard ≤ n
  inter : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V
  lines : ∀ e ∈ arcComponentsIn (K.U \ K.V), ∃ u v, u ≠ v ∧ closure e ∩ K.V = {u, v}
    ∧ IsLineWithEnds (closure e) u v
  two : ∃ a ∈ K.U ∩ Γ.V, ∃ b ∈ K.U ∩ Γ.V, a ≠ b
  form : IsCutForm cap K

omit [T2Space S] hS in
omit [T2Space Shat] in
theorem exists_short {n : ℕ} (hrep : Painting.rep rad ≤ n) : ∃ F, IsShortCircuit rad n F := by
  set A : Set ℕ∞ := {n : ℕ∞ | ∃ F : Drawing Shat, F.IsCircuitOf rad.G ∧ ¬ IsNullHomotopicOArc F.U ∧
    n = (F.E.ncard / 2 : ℕ)} with hA
  have hne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have : Painting.rep rad = ⊤ := by
      change sInf A = ⊤
      rw [h, sInf_empty]
    rw [this] at hrep
    exact absurd hrep (by simp)
  obtain ⟨F, hc, hn, heq⟩ := csInf_mem hne
  have hle : ((F.E.ncard / 2 : ℕ) : ℕ∞) ≤ n := by
    rw [← heq]
    exact hrep
  exact ⟨F, hc, hn, by exact_mod_cast hle⟩

omit [T2Space S] hS in
omit [T2Space Shat] in
theorem exists_minimal {n : ℕ} (hrep : Painting.rep rad ≤ n) :
    ∃ F, IsShortCircuit rad n F ∧ ∀ F', IsShortCircuit rad n F' →
      (F.V ∩ range cap.emb).ncard ≤ (F'.V ∩ range cap.emb).ncard := by
  classical
  have hex : ∃ k, ∃ F, IsShortCircuit rad n F ∧ (F.V ∩ range cap.emb).ncard = k := by
    obtain ⟨F, hF⟩ := exists_short rad hrep
    exact ⟨_, F, hF, rfl⟩
  obtain ⟨F, hF, hk⟩ := Nat.find_spec hex
  refine ⟨F, hF, fun F' hF' ↦ ?_⟩
  rw [hk]
  exact Nat.find_min' hex ⟨F', hF', rfl⟩

omit hS in
omit [T2Space Shat] in
/-- A simple walk that holds an edge between its ends is that edge. -/
theorem simple_single {G : Drawing Shat} {a b : Shat} (W : Surface.GraphWalk G.toGraph a b)
  (hW : W.IsSimple) (hab : a ≠ b)
    {e : Set Shat} (he : e ∈ W.edges) (hl : closure e ∩ G.V = {a, b}) : W.support = [a, b]
      ∧ W.edges = [e] := by
  cases W with
  | nil _ => exact absurd rfl hab
  | @cons _ w _ e' h rest =>
    have hn : a ∉ rest.support := (List.nodup_cons.1 hW).1
    have hr : rest.IsSimple := (List.nodup_cons.1 hW).2
    by_cases hee : e' = e
    · subst hee
      have hs : ({a, w} : Set Shat) = {a, b} := h.2.2.2.symm.trans hl
      have hwb : w = b := by
        rcases Set.pair_eq_pair_iff.1 hs with ⟨-, h₁⟩ | ⟨h₁, h₂⟩
        · exact h₁
        · exact absurd h₁ hab
      subst hwb
      obtain ⟨h₁, h₂⟩ := simple_self hr
      refine ⟨?_, ?_⟩
      · change a :: rest.support = _
        rw [h₂]
      · change e' :: rest.edges = _
        rw [h₁]
    · have he' : e ∈ rest.edges := by
        rcases List.mem_cons.1 he with h₁ | h₁
        · exact absurd h₁.symm hee
        · exact h₁
      have ha : a ∈ closure e ∩ G.V := hl ▸ mem_insert _ _
      exact absurd (mem_support_of_mem_edges rest he' ha.1 ha.2) hn

omit hS in
omit [T2Space Shat] in
theorem exists_first {G : Drawing Shat} {a b : Shat} (W : Surface.GraphWalk G.toGraph a b)
  (hab : a ≠ b) :
    ∃ (c : Shat) (e : Set Shat) (_ : G.toGraph.IsLink e a c) (r : Surface.GraphWalk G.toGraph c b),
      W.support = a :: r.support ∧ W.edges = e :: r.edges := by
  cases W with
  | nil _ => exact absurd rfl hab
  | @cons _ c _ e h r => exact ⟨c, e, h, r, rfl, rfl⟩

variable [ConnectedSpace Shat]
include h3

omit [ConnectedSpace Shat] h3 in
omit [T2Space S] [T2Space Shat] hS in
/-- A subdrawing of `Γ*` with no pole lies in `Σ`. -/
theorem subset_range_of_no_pole {T : Drawing Shat} (hT : T.IsSubdrawing rad.G)
    (hnp : ∀ z ∈ T.V, z ∉ rad.poles) :
    T.U ⊆ range cap.emb := by
  have hrangeG : ∀ z ∈ rad.G.V, z ∉ rad.poles → z ∈ range cap.emb := by
    intro z hzG hzp
    by_cases hV : z ∈ Γ.hatV cap
    · obtain ⟨v, -, rfl⟩ := hV
      exact mem_range_self v
    · have hw : z ∈ rad.Rstar := ⟨hzG, hV⟩
      exact rad.region_subset_range hw hzp (rad.regionOf_mem hw).2
  intro z hz
  by_cases hzV : z ∈ T.V
  · exact hrangeG z (hT.1 hzV) (hnp z hzV)
  · obtain ⟨f, hf, hzf⟩ := T.exists_edge_of_mem hz hzV
    obtain ⟨v, hv, w, hw, hset⟩ := rad.edge_ends (hT.2 hf)
    have hwT : w ∈ closure f ∩ T.V := by
      rw [hT.closure_inter_V hf, hset]
      exact mem_insert_of_mem _ rfl
    exact rad.edge_subset_range (hT.2 hf) hw (hnp w hwT.2) hset hzf

omit hS [ConnectedSpace Shat] h3 in
omit [T2Space Shat] in
/-- Each vertex of a circuit is on an edge of it. -/
theorem circuit_iso {F : Drawing Shat} (hFc : F.IsCircuit) : ∀ v ∈ F.V, ∃ e ∈ F.E, v ∈ closure e
  := by
  obtain ⟨u₀, W₀, -, hpos₀, hV₀, hE₀⟩ := id hFc
  intro v hv
  rw [hV₀] at hv
  obtain ⟨e, he, hve⟩ := exists_edge_at W₀ hpos₀ hv
  exact ⟨e, hE₀ ▸ he, hve⟩

omit [ConnectedSpace Shat] in
/-- A circuit of `Γ*` through a pole `p`, with no other pole, whose vertices on `bd(Σ)` are next to
`p`, gives a line `K` with both
ends on the cuff of `p`. -/
theorem chord_of_circuit [Nonempty S] {Φ : Frame S} (hfit : Γ.Fits Φ) {F : Drawing Shat}
  (hFG : F.IsSubdrawing rad.G)
    (hFc : F.IsCircuit) {p : Shat} (hp : p ∈ rad.poles) (hpF : p ∈ F.V)
      (hnp₀ : ∀ z ∈ F.V, z ∈ rad.poles → z = p)
    (hnb : ∀ {x : S}, x ∈ bd S → x ∈ Γ.V → cap.emb x ∈ F.V → ∃ e ∈ F.E, closure e ∩ rad.G.V
      = {cap.emb x, p}) :
    ∃ K, IsCircuitPart cap Φ Γ F K ∧ ∃ a ∈ K.U ∩ Γ.V, ∃ b ∈ K.U ∩ Γ.V, a ≠ b := by
  classical
  have hj := cap.isClosedEmbedding hS
  have hiso := circuit_iso hFc
  obtain ⟨Θ, hΘ, hreg, hpd⟩ := rad.pole_cases hp
  have hpm : p ∉ range cap.emb := cap.notMem_range hΘ hpd
  obtain ⟨e₀, he₀, hpe₀⟩ := hiso p hpF
  have he₀G := hFG.2 he₀
  obtain ⟨v₀, hv₀, w₀, hw₀, hset₀⟩ := rad.edge_ends he₀G
  have hw₀p : w₀ = p := by
    have : p ∈ closure e₀ ∩ rad.G.V := ⟨hpe₀, hp.1.1⟩
    rw [hset₀] at this
    rcases this with h | h
    · exact absurd ⟨v₀, h.symm⟩ hpm
    · exact h.symm
  subst hw₀p
  have hx₀F : cap.emb v₀ ∈ F.V := by
    have : cap.emb v₀ ∈ closure e₀ ∩ F.V := by
      rw [hFG.closure_inter_V he₀, hset₀]
      exact mem_insert _ _
    exact this.2
  have hne₀ : w₀ ≠ cap.emb v₀ := fun h ↦ hpm ⟨v₀, h.symm⟩
  obtain ⟨P₀, Q₀, hP₀, hQ₀, sP₀, sQ₀, -, -, hPQ₀, hdE₀, heq₀⟩ := hFc.exists_two_paths hpF hx₀F hne₀
  have hFV₀ : F.V = P₀.V ∪ Q₀.V := by rw [← Drawing.sup_V sP₀ sQ₀, heq₀]
  have hFE₀ : F.E = P₀.E ∪ Q₀.E := by rw [← Drawing.sup_E sP₀ sQ₀, heq₀]
  obtain ⟨P, Q, hP, hQ, sP, sQ, hdE, heQ, hFV, hFE⟩ : ∃ P Q : Drawing Shat, P.IsPathBetween w₀
    (cap.emb v₀) ∧
      Q.IsPathBetween w₀ (cap.emb v₀) ∧ P.IsSubdrawing F ∧ Q.IsSubdrawing F ∧ Disjoint P.E Q.E
        ∧ e₀ ∈ Q.E ∧
      F.V = P.V ∪ Q.V ∧ F.E = P.E ∪ Q.E := by
    by_cases h : e₀ ∈ Q₀.E
    · exact ⟨P₀, Q₀, hP₀, hQ₀, sP₀, sQ₀, hdE₀, h, hFV₀, hFE₀⟩
    · have h' : e₀ ∈ P₀.E := by
        rw [hFE₀] at he₀
        exact he₀.resolve_right h
      exact ⟨Q₀, P₀, hQ₀, hP₀, sQ₀, sP₀, hdE₀.symm, h', by rw [hFV₀, union_comm], by rw [hFE₀,
        union_comm]⟩
  have heP : e₀ ∉ P.E := fun h ↦ disjoint_left.1 hdE h heQ
  obtain ⟨Wq, hWq, hQV, hQE⟩ := hQ
  obtain ⟨Wq', hsq, heq⟩ := (sQ.trans hFG).exists_walk_up Wq
  obtain ⟨hsq₂, heq₂⟩ := simple_single Wq' (by unfold Surface.GraphWalk.IsSimple; rw [hsq]; exact
    hWq) hne₀
    (by rw [heq, ← mem_ofPred_eq (p := fun e ↦ e ∈ Wq.edges), ← hQE]; exact heQ)
      (by rw [hset₀, Set.pair_comm])
  have hQVs : Q.V ⊆ {w₀, cap.emb v₀} := fun z hz ↦ by
    rw [hQV, mem_ofPred_eq, ← hsq, hsq₂] at hz
    simpa using hz
  have hQEs : Q.E ⊆ {e₀} := fun z hz ↦ by
    rw [hQE, mem_ofPred_eq, ← heq, heq₂] at hz
    simpa using hz
  obtain ⟨Wp, hWp, hPV, hPE⟩ := hP
  obtain ⟨Wp', hsp, hep⟩ := (sP.trans hFG).exists_walk_up Wp
  obtain ⟨y, e₂, hl₂, M, hsM, heM⟩ := exists_first Wp' hne₀
  have hsimp : Wp'.IsSimple := by
    unfold Surface.GraphWalk.IsSimple
    rw [hsp]
    exact hWp
  have hnod : (w₀ :: M.support).Nodup := by
    have := hsimp
    unfold Surface.GraphWalk.IsSimple at this
    rwa [hsM] at this
  have hpM : w₀ ∉ M.support := (List.nodup_cons.1 hnod).1
  have hMs : M.IsSimple := (List.nodup_cons.1 hnod).2
  have he₂P : e₂ ∈ P.E := by
    rw [hPE, mem_ofPred_eq, ← hep, heM]
    exact List.mem_cons_self
  have he₂G := hl₂.1
  obtain ⟨v₁, hv₁, w₁, hw₁, hset₁⟩ := rad.edge_ends he₂G
  have hyv : y = cap.emb v₁ := by
    rcases Set.pair_eq_pair_iff.1 (hl₂.2.2.2.symm.trans hset₁) with ⟨h₁, -⟩ | ⟨-, h₁⟩
    · exact absurd ⟨v₁, h₁.symm⟩ hpm
    · exact h₁
  subst hyv
  have hset₁' : closure e₂ ∩ rad.G.V = {cap.emb v₁, w₀} := by
    rw [hl₂.2.2.2, Set.pair_comm]
  have hvne : v₁ ≠ v₀ := by
    rintro rfl
    exact heP (rad.edge_unique hS h3 he₂G he₀G hv₀ hw₀ hset₁' hset₀ ▸ he₂P)
  have hembne : cap.emb v₁ ≠ cap.emb v₀ := fun h ↦ hvne (cap.isEmbedding.injective h)
  set T := walkDrawing rad.G M with hTdef
  have hsubT : T.IsSubdrawing rad.G := walkDrawing_isSubdrawing _ _
  have hTV : ∀ z, z ∈ T.V ↔ z ∈ M.support := fun z ↦ by rw [hTdef, walkDrawing_V]; rfl
  have hTE : ∀ e, e ∈ T.E ↔ e ∈ M.edges := fun e ↦ by rw [hTdef, walkDrawing_E]; rfl
  have hMV : ∀ z ∈ M.support, z ∈ P.V := fun z hz ↦ by
    rw [hPV, mem_ofPred_eq, ← hsp, hsM]
    exact List.mem_cons_of_mem _ hz
  have hME : ∀ e ∈ M.edges, e ∈ P.E := fun e he ↦ by
    rw [hPE, mem_ofPred_eq, ← hep, heM]
    exact List.mem_cons_of_mem _ he
  have hPF : P.V ⊆ F.V := hFV ▸ subset_union_left
  have hPEF : P.E ⊆ F.E := hFE ▸ subset_union_left
  have hTF : T.IsSubdrawing F := by
    refine ⟨fun z hz ↦ hPF (hMV z ((hTV z).1 hz)), fun e he ↦ hPEF (hME e ((hTE e).1 he))⟩
  have hlabel : cuffLabel cap w₀ = some Θ := cuffLabel_eq hΘ (subset_closure hpd)
  have hnp : ∀ z ∈ T.V, z ∉ rad.poles := by
    intro z hz hzp
    exact hpM ((hnp₀ z (hTF.1 hz) hzp) ▸ (hTV z).1 hz)
  have hU : T.U ⊆ range cap.emb := subset_range_of_no_pole rad hsubT hnp
  have hlenpos : 0 < M.length := by
    by_contra hl
    exact hembne (Surface.GraphWalk.eq_of_length_eq_zero (Nat.le_zero.mp (not_lt.mp hl)))
  have hisoT : ∀ v ∈ T.V, ∃ e ∈ T.E, v ∈ closure e := fun v hv ↦ by
    obtain ⟨e, he, hve⟩ := exists_edge_at M hlenpos ((hTV v).1 hv)
    exact ⟨e, (hTE e).2 he, hve⟩
  obtain ⟨hinter, hfeat, hlines, hcV, hcE⟩ := comap_facts rad hfit hsubT hU hj hisoT
  set K : Drawing S := GM19.Drawing.comap T hj hU with hKdef
  have hKU : cap.emb '' K.U = T.U := image_preimage_eq_of_subset hU
  have hv₁Θ : v₁ ∈ Θ := (rad.pole_edge he₂G hp hΘ hreg hset₁').2
  have hv₀Θ : v₀ ∈ Θ := (rad.pole_edge he₀G hp hΘ hreg hset₀).2
  have hs : v₁ ∈ K.V := (hTV _).2 M.start_mem_support
  have ht : v₀ ∈ K.V := (hTV _).2 M.end_mem_support
  have hbdK : K.U ∩ bd S = {v₁, v₀} := by
    apply subset_antisymm
    · rintro x ⟨hxK, hxb⟩
      obtain ⟨hxV, hxK'⟩ := hinter ⟨Γ.bd_subset hxb, hxK⟩
      have hxF : cap.emb x ∈ F.V := hTF.1 hxK'
      by_contra hnot
      obtain ⟨e, he, hset⟩ := hnb hxb hxV hxF
      have hxe : cap.emb x ∈ closure e ∩ rad.G.V := hset ▸ mem_insert _ _
      have hpe : w₀ ∈ closure e ∩ rad.G.V := hset ▸ mem_insert_of_mem _ rfl
      rw [hFE] at he
      rcases he with he | he
      · rw [hPE, mem_ofPred_eq, ← hep, heM] at he
        rcases List.mem_cons.1 he with rfl | he
        · rw [hset₁'] at hset
          rcases Set.pair_eq_pair_iff.1 hset with ⟨h₁, -⟩ | ⟨h₁, -⟩
          · exact hnot (Or.inl (cap.isEmbedding.injective h₁).symm)
          · exact hpm ⟨_, h₁⟩
        · exact hpM (mem_support_of_mem_edges M he hpe.1 hpe.2)
      · rcases hQEs he with rfl
        rw [hset₀] at hset
        rcases Set.pair_eq_pair_iff.1 hset with ⟨h₁, -⟩ | ⟨h₁, -⟩
        · exact hnot (Or.inr (cap.isEmbedding.injective h₁).symm)
        · exact hpm ⟨_, h₁⟩
    · rintro x (rfl | rfl)
      · exact ⟨K.V_subset_U hs, cuff_subset_bd ⟨Θ, hΘ⟩ hv₁Θ⟩
      · exact ⟨K.V_subset_U ht, cuff_subset_bd ⟨Θ, hΘ⟩ hv₀Θ⟩
  have h₁ : T.V.ncard ≤ F.V.ncard := ncard_le_ncard hTF.1 F.finite_V
  have h₂ : T.E.ncard ≤ F.E.ncard := ncard_le_ncard hTF.2 F.finite_edges
  refine ⟨K, ⟨hfeat, hinter, hlines, hcV.le.trans h₁, hcE.le.trans h₂,
    Or.inr ⟨v₁, v₀, Θ, hΘ, hvne, hv₁Θ, hv₀Θ, hbdK, ?_, ?_, ?_⟩⟩,
    ⟨v₁, ⟨K.V_subset_U hs, hv₁⟩, v₀, ⟨K.V_subset_U ht, hv₀⟩, hvne⟩⟩
  · refine isLine_comap hj ?_
    rw [hKU]
    exact isLine_of_isPathBetween (walkDrawing_isPathBetween _ hMs) hembne
  · rw [hKU]
    exact hTF.U_subset
  · rintro z ⟨hzF, hzT⟩
    rw [hKU] at hzT
    have hedge : ∀ {e : Set Shat} {x : Shat}, e ∈ rad.G.E → closure e ∩ rad.G.V = {x, w₀} → z ∈ e
      → z ∈ cap.cuffDisc Θ := by
      intro e x he hs hze
      exact hreg ▸ rad.edge_subset_region he hp.1 hs hze
    by_cases hzV : z ∈ F.V
    · rw [hFV] at hzV
      rcases hzV with hz | hz
      · rw [hPV, mem_ofPred_eq, ← hsp, hsM] at hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hpd
        · exact absurd (T.V_subset_U ((hTV z).2 hz)) hzT
      · rcases hQVs hz with rfl | rfl
        · exact hpd
        · exact absurd (T.V_subset_U ((hTV _).2 M.end_mem_support)) hzT
    · obtain ⟨f, hf, hzf⟩ := F.exists_edge_of_mem hzF hzV
      rw [hFE] at hf
      rcases hf with hf | hf
      · rw [hPE, mem_ofPred_eq, ← hep, heM] at hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hedge he₂G hset₁' hzf
        · have hfT : f ∈ T.E := (hTE f).2 hf
          exact absurd (hfT.2.1 hzf).1 hzT
      · rcases hQEs hf with rfl
        exact hedge he₀G hset₀ hzf

omit h3 [ConnectedSpace Shat] in
omit [T2Space S] in
/-- A circuit of `Γ*` with no pole, with at most one point on `bd(Σ)`, is a feature. -/
theorem ring_of_circuit [Nonempty S] {Φ : Frame S} (hfit : Γ.Fits Φ) {F : Drawing Shat}
  (hFG : F.IsSubdrawing rad.G)
    (hFc : F.IsCircuit) (hpole : ∀ z ∈ F.V, z ∉ rad.poles)
    (hone : ∀ {x y : S}, x ∈ bd S → y ∈ bd S → cap.emb x ∈ F.U → cap.emb y ∈ F.U → x = y) :
    ∃ K, IsCircuitPart cap Φ Γ F K ∧ F.U = cap.emb '' K.U ∧ IsOArc K.U ∧ (K.U ∩ bd S).Subsingleton
      := by
  have hj := cap.isClosedEmbedding hS
  have hiso := circuit_iso hFc
  have hU : F.U ⊆ range cap.emb := subset_range_of_no_pole rad hFG hpole
  obtain ⟨hinter, hfeat, hlines, hcV, hcE⟩ := comap_facts rad hfit hFG hU hj hiso
  set K : Drawing S := GM19.Drawing.comap F hj hU with hKdef
  have hKU : cap.emb '' K.U = F.U := image_preimage_eq_of_subset hU
  have hsing : (K.U ∩ bd S).Subsingleton := fun x hx y hy ↦ hone hx.2 hy.2 hx.1 hy.1
  have hO : IsOArc K.U := isOArc_comap hj (hKU ▸ IsCircuit.isOArc_U hFc)
  exact ⟨K, ⟨hfeat, hinter, hlines, hcV.le, hcE.le, Or.inl ⟨hKU.symm, hO, hsing⟩⟩, hKU.symm, hO,
    hsing⟩

/-- **The feature of the proof of (5.5).** -/
theorem exists_shape [Nonempty S] {Φ : Frame S} (hfit : Γ.Fits Φ) {n : ℕ} (hd :
  ((n + 1 : ℕ) : ℕ∞) < Painting.dist rad)
    (hrep : Painting.rep rad ≤ n) : ∃ K, IsCutShape cap Φ Γ (4 * n + 3) K := by
  classical
  obtain ⟨F, hF, hmin⟩ := exists_minimal rad hrep
  have hFs := hF
  obtain ⟨⟨hFG, hFc⟩, hnn, hlen⟩ := hFs
  have hVE : F.V.ncard = F.E.ncard := IsCircuit.ncard_V hFc
  have hEn : F.E.ncard ≤ 2 * n + 1 := by omega
  have hsmall : (∃ F', IsShortCircuit rad n F' ∧ (F'.V ∩ range cap.emb).ncard <
    (F.V ∩ range cap.emb).ncard) → False :=
    fun ⟨_, h, hl⟩ ↦ absurd hl (not_lt.2 (hmin _ h))
  have hpack : ∀ {K}, IsCircuitPart cap Φ Γ F K → (∃ a ∈ K.U ∩ Γ.V, ∃ b ∈ K.U ∩ Γ.V, a ≠ b) →
      IsCutShape cap Φ Γ (4 * n + 3) K := fun h₁ h₂ ↦
    ⟨h₁.feature, by have := h₁.V_le; have := h₁.E_le; omega, h₁.inter, h₁.lines, h₂,
      F.U, IsCircuit.isOArc_U hFc, hnn, h₁.form⟩
  by_cases hpole : ∃ p ∈ rad.poles, p ∈ F.V
  · obtain ⟨p, hp, hpF⟩ := hpole
    obtain ⟨Θ, hΘ, hreg, hpd⟩ := rad.pole_cases hp
    have hlabel : cuffLabel cap p = some Θ := cuffLabel_eq hΘ (subset_closure hpd)
    obtain ⟨K, h₁, h₂⟩ := chord_of_circuit hS rad h3 hfit hFG hFc hp hpF (fun z hz hzp ↦ by
      obtain ⟨Θ', hΘ', hreg', hzd⟩ := rad.pole_cases hzp
      obtain rfl := label_eq hS rad hd hF h3 hz hpF (cuffLabel_eq hΘ' (subset_closure hzd)) hlabel
      obtain ⟨-, -, hG3, -⟩ := id rad.isPreRadial
      exact (hG3 _ (rad.regionOf_mem hp.1).1).unique
        ⟨hreg.trans hreg'.symm ▸ (rad.regionOf_mem hzp.1).2, hzp.1.1⟩ ⟨(rad.regionOf_mem hp.1).2,
          hp.1.1⟩)
      (fun {x} hxb hxV hxF ↦ by
        obtain ⟨Θ', hΘ', hxΘ, hl₁⟩ := cuffLabel_emb_bd (cap := cap) hxb
        obtain rfl := label_eq hS rad hd hF h3 hxF hpF hl₁ hlabel
        by_contra hno
        push Not at hno
        exact hsmall (exists_smaller_of_pole hS rad h3 hF hp hpF hΘ' hreg hxV hxΘ hxF hno))
    exact ⟨K, hpack h₁ h₂⟩
  · push Not at hpole
    have hnp : ∀ z ∈ F.V, z ∉ rad.poles := fun z hz hp ↦ hpole z hp hz
    have hU := subset_range_of_no_pole rad hFG hnp
    obtain ⟨K, h₁, hKU, hO, hsing⟩ := ring_of_circuit hS rad hfit hFG hFc hnp
      (fun {x y} hxb hyb hxF hyF ↦ by
      by_contra hne
      have hmemV : ∀ {x : S}, x ∈ bd S → cap.emb x ∈ F.U → x ∈ Γ.V ∧ cap.emb x ∈ F.V
        := fun {x} hxb hxF ↦ by
        obtain ⟨-, -, -, -, -, -⟩ := id rad.isPreRadial
        have hxU : cap.emb x ∈ Γ.hatU cap ∩ rad.G.U := ⟨mem_image_of_mem _
          (Γ.bd_subset hxb), hFG.U_subset hxF⟩
        rw [rad.isPreRadial.1] at hxU
        obtain ⟨v, hv, hvx⟩ := hxU
        obtain rfl := cap.isEmbedding.injective hvx
        exact ⟨hv, IsSubdrawing.mem_V hFG hxF (rad.isPreRadial.2.1 ⟨_, hv, rfl⟩)⟩
      obtain ⟨hxV, hxK'⟩ := hmemV hxb hxF
      obtain ⟨hyV, hyK'⟩ := hmemV hyb hyF
      obtain ⟨Θ, hΘ, hxΘ, hl₁⟩ := cuffLabel_emb_bd (cap := cap) hxb
      obtain ⟨Θ', hΘ', hyΘ, hl₂⟩ := cuffLabel_emb_bd (cap := cap) hyb
      obtain rfl := label_eq hS rad hd hF h3 hxK' hyK' hl₁ hl₂
      obtain ⟨p, hp, -, hr⟩ := rad.exists_pole hΘ
      exact hsmall (exists_smaller_of_two hS rad h3 hF hp (hpole p hp) hΘ hr hxV hyV hxΘ hyΘ hne
        hxK' hyK'))
    refine ⟨K, hpack h₁ ?_⟩
    have hinter := h₁.inter
    have hfinU : (K.U ∩ Γ.V).Finite := Γ.finite_V.inter_of_right _
    have hfinb : (K.U ∩ bd S).Finite := hsing.finite
    by_contra hno
    push Not at hno
    have hsub : (K.U ∩ Γ.V).Subsingleton := fun a ha b hb ↦ hno a ha b hb
    have hle₁ : (K.U ∩ Γ.V).ncard ≤ 1 := (ncard_le_one hfinU).2 fun a ha b hb ↦ hsub ha hb
    have hle₂ : (K.U ∩ bd S).ncard ≤ 1 := (ncard_le_one hfinb).2 fun a ha b hb ↦ hsing ha hb
    obtain ⟨Δ, hΔ, hb, -⟩ := h3.2 K.U hO (fun x hx ↦ (hinter ⟨hx.2, hx.1⟩).1) hfinb (by omega)
    have hd' := isClosedDisc_image hΔ cap.isEmbedding
    refine hnn ((epstein Shat univ _ cap.isSurface inferInstance (IsCircuit.isOArc_U hFc)
      (subset_univ _) ?_).2.1
      ⟨cap.emb '' Δ, subset_univ _, hd'.1, ?_⟩)
    · rw [cap.bd_empty]
      exact disjoint_bot_right
    · rw [hKU, ← hb]
      exact image_mono (Surface.discBd_subset _)

end GraphMinor.GM19
