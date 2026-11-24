/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section4d
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Section 4 of "Quickly excluding a planar graph": (4.4)

Robertson, Seymour and Thomas, J. Combin. Theory Ser. B 62 (1994), (4.4), pages 338–339. `Chain`
records the nodules `G_r, 𝒯_r, Z_r` of the proof after `r` steps. The paths `P c` are
the paper's paths `P_i`, and the sets `𝒞 s` are the components `C_r`.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β κ ι : Type*} {G : Hypergraph α β} {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α β)}

/-- (2.4) used as in the proof of (4.4): a free set extends to a free set of any size up to the
order. -/
theorem exists_free_superset (hT : IsTangle G θ T) {X : Set α} (hX : IsFreeSet G T θ X) {n : ℕ}
  (h₁ : X.ncard ≤ n) (h₂ : n ≤ θ) :
    ∃ Y, X ⊆ Y ∧ Y.ncard = n ∧ IsFreeSet G T θ Y := by
  obtain ⟨M, hE, hind, hrk⟩ := GraphMinor.GM10.theorem_12_2_proof G hT
  obtain ⟨B, hB, hXB⟩ := ((hind X).2 hX).exists_isBase_superset
  have hBfree : IsFreeSet G T θ B := (hind B).1 hB.indep
  have hrank : tangleRank T θ G.vertexSet = θ := by
    refine le_antisymm (tangleRank_le_order hT _) ((le_rank_iff le_rfl).2 fun A B' hm hV => ?_)
    exact absurd (subset_antisymm (hT.isSeparation hm).left_le.vertexSet_subset hV) (hT.axiom3 hm)
  have hBfin : B.Finite := G.vertexSet_finite.subset hBfree.1
  have hBc : B.ncard = θ := by
    have h₃ : M.eRk M.E = B.encard := by
      rw [Matroid.eRk_ground, hB.encard_eq_eRank]
    rw [hE, hrk _ subset_rfl, hrank, ← hBfin.cast_ncard_eq] at h₃
    exact (Nat.cast_inj.1 h₃).symm
  obtain ⟨Y, hXY, hYB, hYc⟩ := exists_subsuperset_card_eq hXB h₁ (hBc ▸ h₂)
  exact ⟨Y, hXY, hYc, hBfree.subset hT hYB⟩

/-- Two paths that share only their common vertex make a path. -/
theorem isPath_append {K : SimpleGraph α} {a b c : α} {w₁ : K.Walk a b} {w₂ : K.Walk b c}
  (h₁ : w₁.IsPath) (h₂ : w₂.IsPath)
    (hd : ∀ x ∈ w₁.support, x ∈ w₂.support → x = b) : (w₁.append w₂).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append]
  have hn := h₂.support_nodup
  rw [← SimpleGraph.Walk.cons_tail_support, List.nodup_cons] at hn
  refine ⟨h₁.support_nodup, hn.2, fun x hx y hy he => ?_⟩
  subst he
  have hxw : x ∈ w₂.support := by
    rw [← SimpleGraph.Walk.cons_tail_support]
    exact List.mem_cons_of_mem _ hy
  exact hn.1 (hd x hx hxw ▸ hy)

/-- Among disjoint sets, more of them than the size of `X`, one misses `X`. -/
theorem exists_avoid {γ : Type*} (s : Finset γ) (U : γ → Set α) (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j
  → Disjoint (U i) (U j)) {X : Set α} (hX : X.Finite)
    (hlt : X.ncard < s.card) : ∃ i ∈ s, Disjoint (U i) X := by
  by_contra hcon
  push Not at hcon
  have hpos : ∀ i ∈ s, 1 ≤ (X ∩ U i).ncard := fun i hi => by
    obtain ⟨x, hx₁, hx₂⟩ := not_disjoint_iff.1 (hcon i hi)
    exact (ncard_pos (hX.subset inter_subset_left)).2 ⟨x, hx₂, hx₁⟩
  have h₁ : s.card ≤ ∑ i ∈ s, (X ∩ U i).ncard := by
    calc s.card = ∑ _i ∈ s, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hpos
  rw [sum_ncard_eq _ _ (fun i => hX.subset inter_subset_left) fun i hi j hj hij =>
    (hd i hi j hj hij).mono inter_subset_right inter_subset_right] at h₁
  have h₂ := ncard_le_ncard (iUnion₂_subset fun i (_ : i ∈ s) => (inter_subset_left : X ∩ U i ⊆ X))
    hX
  omega

/-- A walk of `G` that avoids `W` is a walk of the graph `G \ W`. -/
theorem exists_walk_delete (hG : G.IsGraph) {W : Set α} {a b : α} (w : G.skeleton.Walk a b)
  (hw : ∀ x ∈ w.support, x ∉ W) :
    ∃ w' : (G.deleteVertices W).skeleton.Walk a b, w'.support = w.support := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x y c hadj q ih =>
    obtain ⟨q', hq'⟩ := ih fun t ht => hw t (by simp [ht])
    obtain ⟨hne, f, h₁, h₂⟩ := id hadj
    have hno : ∀ v ∈ W, ¬ G.Inc f v := fun v hv hi => by
      rcases end_eq_or hG h₁ h₂ hne hi with rfl | rfl
      · exact hw _ (by simp) hv
      · exact hw _ (by simp) hv
    have hadj' : (G.deleteVertices W).skeleton.Adj x y := ⟨hne, f, ⟨h₁, hno⟩, ⟨h₂, hno⟩⟩
    exact ⟨SimpleGraph.Walk.cons hadj' q', by simp [hq']⟩

/-- A connected set that avoids `W` is connected in `G \ W`. -/
theorem Conn.delete (hG : G.IsGraph) {W D : Set α} (hD : Conn G D) (hW : Disjoint D W) : Conn
  (G.deleteVertices W) D :=
  ⟨hD.1, fun x hx y hy => by
    obtain ⟨w, hw⟩ := hD.2 x hx y hy
    obtain ⟨w', hw'⟩ := exists_walk_delete hG w fun t ht => disjoint_left.1 hW (hw t ht)
    exact ⟨w', fun t ht => hw t (hw' ▸ ht)⟩⟩

/-- The nodules `G_r, 𝒯_r, Z_r` after `r` steps of the proof of (4.4). -/
structure Chain (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) (y₀ : κ
  → α) (r : ℕ) (G' : Hypergraph α β)
    (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (y' : κ → α) (P : ∀ c, G.skeleton.Walk
      (y₀ c) (y' c)) (𝒞 : ℕ → Set α) : Prop where
  nodule : Nodule G' T' θ' y'
  le : G' ≤ G
  conformal : Conformal G G' T T' θ θ'
  link : IsLinkage G G' y₀ y' P
  avoid : r ≠ 0 → ∀ c, y₀ c ∉ G'.vertexSet
  fix : r = 0 → ∀ c, y' c = y₀ c
  conn : ∀ s < r, Conn G (𝒞 s)
  disj : ∀ s < r, ∀ s' < r, s ≠ s' → Disjoint (𝒞 s) (𝒞 s')
  off : ∀ s < r, ∀ x ∈ 𝒞 s, x ∉ G'.vertexSet
  hit : ∀ s < r, ∀ c, ∃ t ∈ (P c).support, t ∈ 𝒞 s ∧ t ≠ y' c

/-- One step of the proof of (4.4). -/
theorem Chain.step [Fintype κ] (hG : G.IsGraph) (hT : IsTangle G θ T) {y₀ y' : κ
  → α} {r θ' b : ℕ} {G' : Hypergraph α β} {T' : Set (Hypergraph α β × Hypergraph α β)}
    {P : ∀ c, G.skeleton.Walk (y₀ c) (y' c)} {𝒞 : ℕ → Set α} (hc : Chain G T θ y₀ r G' T' θ' y' P
      𝒞) (hn : 2 ≤ Fintype.card κ) (hk : Fintype.card κ ≤ 2 * b)
    (hθ : b * 20 ^ Fintype.card κ ≤ θ') :
    ∃ G₂ T₂ θ₂ y₂ P₂ 𝒞₂, Chain G T θ y₀ (r + 1) G₂ T₂ θ₂ y₂ P₂ 𝒞₂ ∧ b ≤ θ₂ := by
  classical
  have hG' : G'.IsGraph := IsGraph.of_le hG hc.le
  obtain ⟨G₂, T₂, θ₂, y₂, hR, hb, D, hD, hyD, hDav⟩ := theorem_4_3 hG' hc.nodule hn hk hθ
  obtain ⟨p, hp₁, hp₂, hp₃⟩ := hR.link
  obtain ⟨hP₁, hP₂, hP₃⟩ := hc.link
  let P₂ : ∀ c, G.skeleton.Walk (y₀ c) (y₂ c) := fun c => (P c).append ((p c).mapLe
    (skeleton_mono hc.le))
  have hmem : ∀ c t, t ∈ (P₂ c).support ↔ t ∈ (P c).support ∨ t ∈ (p c).support := fun c t => by
    simp [P₂, SimpleGraph.Walk.mem_support_append_iff]
  have hpG : ∀ c t, t ∈ (p c).support → t ∈ G'.vertexSet := fun c t ht =>
    support_mem (p c) (hc.nodule.free.1 (mem_range_self c)) ht
  have hG₂ : ∀ {x}, x ∈ G₂.vertexSet → x ∈ G'.vertexSet := fun hx => hR.le.vertexSet_subset hx
  have hDG : D ⊆ G'.vertexSet := by
    obtain ⟨c⟩ : Nonempty κ := Fintype.card_pos_iff.1 (by omega)
    intro x hx
    obtain ⟨w, hw⟩ := hD.2 (y' c) (hyD (mem_range_self c)) x hx
    exact support_mem w (hc.nodule.free.1 (mem_range_self c)) w.end_mem_support
  refine ⟨G₂, T₂, θ₂, y₂, P₂, Function.update 𝒞 r D, ?_, hb⟩
  have hup : ∀ s < r, Function.update 𝒞 r D s = 𝒞 s := fun s hs => Function.update_of_ne hs.ne _ _
  have hupr : Function.update 𝒞 r D r = D := Function.update_self _ _ _
  refine ⟨hR.nodule, hR.le.trans hc.le, Conformal.trans hc.le hR.le hT hc.nodule.tangle
    hR.nodule.tangle hc.conformal hR.conformal, ⟨fun c => ?_, fun c t ht htG => ?_,
    fun i j hij => disjoint_left.2 fun t ht ht' => ?_⟩, fun _ c hcG => ?_, fun h => absurd h
      (Nat.succ_ne_zero r), fun s hs => ?_, fun s hs s' hs' hne => ?_, fun s hs x hx hxG
        => ?_, fun s hs c => ?_⟩
  · refine isPath_append (hP₁ c) ((hp₁ c).mapLe _) fun x hx hx' => hP₂ c x hx (hpG c x
    (by simpa using hx'))
  · rcases (hmem c t).1 ht with h | h
    · have := hP₂ c t h (hG₂ htG)
      exact absurd (this ▸ htG) (hR.avoid c)
    · exact hp₂ c t h htG
  · have hx : ∀ i j, i ≠ j → t ∈ (P i).support → t ∉ (p j).support := fun i j hij hi hj => by
      have := hP₂ i t hi (hpG j t hj)
      subst this
      exact disjoint_left.1 (hp₃ hij) (p i).start_mem_support hj
    rcases (hmem i t).1 ht with h₁ | h₁ <;> rcases (hmem j t).1 ht' with h₂ | h₂
    · exact disjoint_left.1 (hP₃ hij) h₁ h₂
    · exact hx i j hij h₁ h₂
    · exact hx j i hij.symm h₂ h₁
    · exact disjoint_left.1 (hp₃ hij) h₁ h₂
  · by_cases hr : r = 0
    · subst hr
      exact hR.avoid c (hc.fix rfl c ▸ hcG)
    · exact hc.avoid hr c (hG₂ hcG)
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · rw [hup s hs]
      exact hc.conn s hs
    · rw [hupr]
      exact hD.mono hc.le
  · have hoff : ∀ s < r, ∀ s' ≤ r, s' = r → Disjoint (𝒞 s) D := fun s hs _ _ _ =>
      disjoint_left.2 fun x hx hxD => hc.off s hs x hx (hDG hxD)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs₁ | rfl <;> rcases Nat.lt_succ_iff_lt_or_eq.1 hs'
      with hs₂ | rfl
    · rw [hup s hs₁, hup s' hs₂]
      exact hc.disj s hs₁ s' hs₂ hne
    · rw [hup s hs₁, hupr]
      exact hoff s hs₁ _ le_rfl rfl
    · rw [hup s' hs₂, hupr]
      exact (hoff s' hs₂ _ le_rfl rfl).symm
    · exact absurd rfl hne
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs₁ | rfl
    · rw [hup s hs₁] at hx
      exact hc.off s hs₁ x hx (hG₂ hxG)
    · rw [hupr] at hx
      exact hDav x hx hxG
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs₁ | rfl
    · obtain ⟨t, ht₁, ht₂, -⟩ := hc.hit s hs₁ c
      rw [hup s hs₁]
      refine ⟨t, (hmem c t).2 (Or.inl ht₁), ht₂, fun e => hc.off s hs₁ t ht₂ ?_⟩
      exact e ▸ hG₂ (hR.nodule.free.1 (mem_range_self c))
    · rw [hupr]
      exact ⟨y' c, (hmem c _).2 (Or.inl (P c).end_mem_support), hyD (mem_range_self c),
        fun e => hR.avoid c (e ▸ hR.nodule.free.1 (mem_range_self c))⟩

/-- `h` steps of the proof of (4.4), by induction. -/
theorem exists_chain [Fintype κ] (hG : G.IsGraph) {y₀ : κ → α} (hN : Nodule G T θ y₀) {k h : ℕ}
  (hn : 2 ≤ Fintype.card κ) (hk : Fintype.card κ ≤ 2 * k)
    (hθ : k * 20 ^ (Fintype.card κ * h) ≤ θ) (r : ℕ) (hr : r ≤ h) :
    ∃ G' T' θ' y' P 𝒞, Chain G T θ y₀ r G' T' θ' y' P 𝒞 ∧ k * 20 ^ (Fintype.card κ * (h - r)) ≤ θ'
      := by
  induction r with
  | zero =>
    refine ⟨G, T, θ, y₀, fun c => SimpleGraph.Walk.nil, fun _ => ∅, ⟨hN, le_rfl,
      conformal_of_subset hN.tangle le_rfl subset_rfl, ⟨fun _ => SimpleGraph.Walk.IsPath.nil, fun c
        t ht _ => ?_,
      fun i j hij => ?_⟩, fun h => absurd rfl h, fun _ _ => rfl, fun s hs => absurd hs
        (Nat.not_lt_zero s), fun s hs => absurd hs (Nat.not_lt_zero s), fun s hs => absurd hs
          (Nat.not_lt_zero s),
      fun s hs => absurd hs (Nat.not_lt_zero s)⟩, hθ⟩
    · simpa using ht
    · simpa using fun e => hij (hN.inj e)
  | succ r ih =>
    obtain ⟨G', T', θ', y', P, 𝒞, hc, hb⟩ := ih (by omega)
    have hpow : Fintype.card κ * (h - r) = Fintype.card κ * (h - (r + 1)) + Fintype.card κ := by
      obtain ⟨m, hm⟩ : ∃ m, h - r = m + 1 := ⟨h - r - 1, by omega⟩
      rw [hm, show h - (r + 1) = m by omega, Nat.mul_succ]
    have hb₂ : k * 20 ^ (Fintype.card κ * (h - (r + 1))) * 20 ^ Fintype.card κ ≤ θ' := by
      rw [Nat.mul_assoc, ← pow_add, ← hpow]
      exact hb
    have hk₂ : Fintype.card κ ≤ 2 * (k * 20 ^ (Fintype.card κ * (h - (r + 1)))) :=
      hk.trans (Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right k (by positivity)))
    obtain ⟨G₂, T₂, θ₂, y₂, P₂, 𝒞₂, hc₂, hb₃⟩ := hc.step hG hN.tangle hn hk₂ hb₂
    exact ⟨G₂, T₂, θ₂, y₂, P₂, 𝒞₂, hc₂, hb₃⟩

/-- **(4.4)** (page 338). The set `Y₀` is the paper's `Z₀`, and it indexes `Y`. -/
theorem theorem_4_4 [Fintype ι] (hG : G.IsGraph) {z : ι → α} (hN : Nodule G T θ z) {k n : ℕ}
  (hh : 2 ≤ Fintype.card ι) (hhn : Fintype.card ι ≤ n) (hn : n ≤ 2 * k)
    (hθ : k * 20 ^ (n * Fintype.card ι) ≤ θ) :
    ∃ (Y₀ : Set α) (_ : Fintype Y₀) (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α
      β)) (θ' : ℕ) (y : Y₀ → α), Fintype.card Y₀ = n ∧
      Nodule G' T' θ' y ∧ k ≤ θ' ∧ G' ≤ G ∧ Conformal G G' T T' θ θ' ∧ (∀ i, z i ∉ G'.vertexSet)
        ∧ ∀ Z' : Set α, Z' ⊆ range y → Z'.ncard = Fintype.card ι →
        ∃ z' : ι → α, range z' = Z' ∧ Residual G T θ z G' T' θ' z' := by
  classical
  have hZc := ncard_range hN.inj
  have h1 : n ≤ k * 20 ^ (n * Fintype.card ι) := by
    have hk1 : 1 ≤ k := by omega
    have h₂ : 2 * n ≤ 20 ^ (n * Fintype.card ι) := by
      have h₃ : n * 2 ≤ 2 ^ n * 2 := Nat.mul_le_mul_right 2 n.lt_two_pow_self.le
      have h₄ : 2 ^ (n + 1) ≤ 20 ^ (n + 1) := Nat.pow_le_pow_left (by omega) _
      have h₅ : 20 ^ (n + 1) ≤ 20 ^ (n * Fintype.card ι) := Nat.pow_le_pow_right (by omega)
        (by nlinarith)
      rw [pow_succ] at h₄
      omega
    nlinarith
  obtain ⟨Y₀, hZY, hYc, hYfree⟩ := exists_free_superset hN.tangle hN.free (by omega) (h1.trans hθ)
  have hYf : Y₀.Finite := G.vertexSet_finite.subset hYfree.1
  have hF : Fintype Y₀ := hYf.fintype
  have hcard : Fintype.card Y₀ = n := by
    rw [← hYc, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hN₀ : Nodule G T θ (Subtype.val : Y₀ → α) := by
    refine ⟨hN.tangle, Subtype.val_injective, ?_⟩
    rw [Subtype.range_coe]
    exact hYfree
  obtain ⟨G', T', θ', y, P, 𝒞, hc, hb⟩ := exists_chain (h := Fintype.card ι) (κ := Y₀) hG hN₀ (k
    := k) (by omega) (by omega) (by rw [hcard]; exact hθ) _ le_rfl
  rw [Nat.sub_self, Nat.mul_zero, pow_zero, Nat.mul_one] at hb
  have hr0 : Fintype.card ι ≠ 0 := by omega
  have hav := hc.avoid hr0
  obtain ⟨hP₁, hP₂, hP₃⟩ := hc.link
  have hzav : ∀ i, z i ∉ G'.vertexSet := fun i => hav ⟨z i, hZY (mem_range_self i)⟩
  refine ⟨Y₀, hF, G', T', θ', y, hcard, hc.nodule, hb, hc.le, hc.conformal, hzav, fun Z' hZ' hZ'c
    => ?_⟩
  have hyinj := hc.nodule.inj
  let W : Set α := G'.vertexSet \ Z'
  let J := G.deleteVertices W
  have hJG : J ≤ G := deleteVertices_le _ _
  have hZ'V : Z' ⊆ G'.vertexSet := hZ'.trans hc.nodule.free.1
  have hzJ : range z ⊆ J.vertexSet := by
    rintro _ ⟨i, rfl⟩
    exact ⟨hN.free.1 (mem_range_self i), fun h => hzav i h.1⟩
  have hZ'J : Z' ⊆ J.vertexSet := fun x hx => ⟨hc.le.vertexSet_subset (hZ'V hx), fun h => h.2 hx⟩
  have hZ'f : Z'.Finite := toFinite _ |>.subset hZ'
  let eY : ι → Y₀ := fun i => ⟨z i, hZY (mem_range_self i)⟩
  have heY : Function.Injective eY := fun i j he => hN.inj (congrArg Subtype.val he)
  have hsep : ∀ A₁ B₁, J.IsSeparation A₁ B₁ → range z ⊆ A₁.vertexSet → Z' ⊆ B₁.vertexSet →
    (range z).ncard ≤ separationOrder A₁ B₁ := by
    intro A₁ B₁ hs₁ hzA hZB
    by_contra hlt
    push Not at hlt
    rw [hZc] at hlt
    have hXf : (A₁ ∩ B₁).vertexSet.Finite := (A₁ ∩ B₁).vertexSet_finite
    have hlt' : (A₁ ∩ B₁).vertexSet.ncard < Fintype.card ι := hlt
    obtain ⟨c₁, hc₁, hd₁⟩ := exists_avoid (Finset.univ.image eY) (fun c => {x | x ∈ (P c).support})
      (fun i _ j _ hij => hP₃ hij) hXf (by
      rw [Finset.card_image_of_injective _ heY, Finset.card_univ]
      exact hlt')
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc₁
    have hs₂c : (Finset.univ.filter fun c => y c ∈ Z').card = Fintype.card ι := by
      rw [← hZ'c, ← Finset.card_image_of_injective _ hyinj, ← ncard_coe_finset]
      congr 1
      ext x
      simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, mem_image,
        mem_ofPred_eq]
      constructor
      · rintro ⟨c, hc', rfl⟩
        exact hc'
      · intro hx
        obtain ⟨c, rfl⟩ := hZ' hx
        exact ⟨c, hx, rfl⟩
    obtain ⟨c₂, hc₂, hd₂⟩ := exists_avoid (Finset.univ.filter fun c => y c ∈ Z') (fun c => {x | x ∈
      (P c).support}) (fun i _ j _ hij => hP₃ hij) hXf (by
      rw [hs₂c]
      exact hlt')
    have hc₂' : y c₂ ∈ Z' := (Finset.mem_filter.1 hc₂).2
    obtain ⟨s, hs, hd₃⟩ := exists_avoid (Finset.range (Fintype.card ι)) 𝒞 (fun i hi j hj hij
      => hc.disj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) hij) hXf (by
      rw [Finset.card_range]
      exact hlt')
    have hs' := Finset.mem_range.1 hs
    obtain ⟨t₁, ht₁, ht₁C, ht₁ne⟩ := hc.hit s hs' (eY i)
    obtain ⟨t₂, ht₂, ht₂C, -⟩ := hc.hit s hs' c₂
    let q := (P (eY i)).takeUntil t₁ ht₁
    have hqs : ∀ x ∈ q.support, x ∈ (P (eY i)).support ∧ x ≠ y (eY i) := fun x hx =>
      ⟨(P (eY i)).support_takeUntil_subset_support ht₁ hx, fun e => by
        subst e
        exact notMem_takeUntil (P (eY i)) (hP₁ _) ht₁ ht₁ne hx⟩
    have hU := ((conn_support q).union (hc.conn s hs') ⟨t₁, q.end_mem_support, ht₁C⟩).union
      (conn_support (P c₂)) ⟨t₂, Or.inr ht₂C, ht₂⟩
    have hUW : Disjoint ({x | x ∈ q.support} ∪ 𝒞 s ∪ {x | x ∈ (P c₂).support}) W := by
      refine disjoint_left.2 ?_
      rintro x ((hx | hx) | hx) ⟨hxG, hxZ⟩
      · obtain ⟨h₁, h₂⟩ := hqs x hx
        exact h₂ (hP₂ _ x h₁ hxG)
      · exact hc.off s hs' x hx hxG
      · exact hxZ (hP₂ c₂ x hx hxG ▸ hc₂')
    obtain ⟨x, hx, hxS⟩ := (hU.delete hG hUW).meets_sep hs₁ (a := z i) (b := y c₂) (Or.inl
      (Or.inl q.start_mem_support)) (Or.inr (P c₂).end_mem_support) (hzA (mem_range_self i))
        (hZB hc₂')
    rcases hx with (hx | hx) | hx
    · exact disjoint_left.1 hd₁ (hqs x hx).1 hxS
    · exact disjoint_left.1 hd₃ hx hxS
    · exact disjoint_left.1 hd₂ hx hxS
  obtain ⟨Q, hQ⟩ := (menger J (range z) Z' hzJ hZ'J _).1 hsep
  have hdis : Pairwise fun i j => Disjoint (pathV (Q i)) (pathV (Q j)) := hQ
  have hstart : ∀ i, (Q i).first ∈ pathV (Q i) := fun i => (Q i).walk.start_mem_support
  have hend : ∀ i, (Q i).last ∈ pathV (Q i) := fun i => (Q i).walk.end_mem_support
  have hinj₁ : Function.Injective fun i => (Q i).first := fun i j he => by
    by_contra hij
    exact disjoint_left.1 (hdis hij) (hstart i) ((show (Q i).first = (Q j).first from he) ▸ hstart
      j)
  have hinj₂ : Function.Injective fun i => (Q i).last := fun i j he => by
    by_contra hij
    exact disjoint_left.1 (hdis hij) (hend i) ((show (Q i).last = (Q j).last from he) ▸ hend j)
  have hb' : ∀ i, ∃ j, (Q j).first = z i := fun i =>
    exists_index _ (toFinite _) rfl hinj₁ (fun j => (Q j).first_mem) (mem_range_self i)
  choose b hb' using hb'
  have hbinj : Function.Injective b := fun i j he => hN.inj (by rw [← hb' i, ← hb' j, he])
  let z' : ι → α := fun i => (Q (b i)).last
  have hz'inj : Function.Injective z' := hinj₂.comp hbinj
  have hrange : range z' = Z' := eq_of_subset_of_ncard_le (range_subset_iff.2 fun i => (Q
    (b i)).last_mem)
    (by rw [ncard_range hz'inj, hZ'c]) hZ'f
  refine ⟨z', hrange, ⟨hc.nodule.tangle, hz'inj, hc.nodule.free.subset hc.nodule.tangle
    (hrange ▸ hZ')⟩, hc.le, hzav, hc.conformal, ?_⟩
  let R : ∀ i, G.skeleton.Walk (z i) (z' i) := fun i => ((Q (b i)).walk.copy (hb' i) rfl).mapLe
    (skeleton_mono hJG)
  have hRs : ∀ i t, t ∈ (R i).support → t ∈ pathV (Q (b i)) := fun i t ht => by
    simpa [R, pathV] using ht
  refine ⟨R, fun i => ((SimpleGraph.Walk.isPath_copy ..).2 (Q (b i)).isPath).mapLe _, fun i t ht
    htG => ?_, fun i j hij => disjoint_left.2 fun t ht ht' => ?_⟩
  · have htJ : t ∈ J.vertexSet := support_mem (Q (b i)).walk (hzJ (Q (b i)).first_mem) (hRs i t ht)
    have htZ : t ∈ Z' := by
      by_contra hn
      exact htJ.2 ⟨htG, hn⟩
    have hrZ : t ∈ range z' := hrange ▸ htZ
    obtain ⟨j, rfl⟩ := hrZ
    by_cases hij : i = j
    · rw [hij]
    · exact absurd (hend (b j)) (disjoint_left.1 (hdis fun e => hij (hbinj e)) (hRs i _ ht))
  · exact disjoint_left.1 (hdis fun e => hij (hbinj e)) (hRs i t ht) (hRs j t ht')

end GraphMinor.RST94
