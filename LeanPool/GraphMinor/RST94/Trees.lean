/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Set.Card

/-!
# Trees, for (5.4) of "Quickly excluding a planar graph"

The two facts about trees in the proof of (5.4) (page 342). A tree with `r` leaves and many vertices
has `2g + 1` consecutive vertices of valency 2 (`exists_long_run`). Adding an edge at the middle of
such a run gives a spanning tree with more leaves (`exists_more_leaves`).
-/

@[expose] public section

namespace GraphMinor.RST94

open Set

variable {ι : Type*} {S : SimpleGraph ι}

/-- The extended valency of a vertex. -/
noncomputable def deg (S : SimpleGraph ι) (v : ι) : ℕ∞ := (S.neighborSet v).encard

/-- On a finite neighbor set, extended valency agrees with Mathlib's natural valency. -/
theorem deg_eq_degree (S : SimpleGraph ι) (v : ι) [Fintype (S.neighborSet v)] :
    deg S v = S.degree v := by
  rw [deg, ← S.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    Set.coe_ncard_eq_encard]

/-- The leaves of a graph: vertices of valency 1 (page 341). -/
def leaves (S : SimpleGraph ι) : Set ι := {v | deg S v = 1}

/-- The two neighbours of a vertex of valency 2. -/
theorem neighborSet_eq {x y z : ι} (h : deg S x = 2) (hy : S.Adj x y) (hz : S.Adj x z)
    (hne : y ≠ z) : S.neighborSet x = {y, z} := by
  refine (((finite_singleton z).insert y).eq_of_subset_of_encard_le ?_ ?_).symm
  · rintro w (rfl | rfl)
    · exact hy
    · exact hz
  · rw [encard_pair hne]
    exact h.le

/-- A vertex closer to the root has only one neighbour closer to the root. -/
theorem closer_unique (hS : S.IsTree) {ρ v w w' : ι} (h : S.Adj w v) (h' : S.Adj w' v)
  (hd : S.dist ρ w + 1 = S.dist ρ v) (hd' : S.dist ρ w' + 1 = S.dist ρ v) : w = w' := by
  classical
  have key : ∀ {w : ι} (h : S.Adj w v), S.dist ρ w + 1 = S.dist ρ v → ∃ q : S.Walk ρ w,
    (q.concat h).IsPath := fun {w} h hd => by
    obtain ⟨q, hq, hl⟩ := hS.connected.exists_path_of_dist ρ w
    refine ⟨q, hq.concat ?_ h⟩
    intro hv
    have h₁ : S.dist ρ v ≤ (q.takeUntil v hv).length := SimpleGraph.dist_le _
    have h₂ := q.length_takeUntil_le_length hv
    omega
  obtain ⟨q, hq⟩ := key h hd
  obtain ⟨q', hq'⟩ := key h' hd'
  have he := (hS.existsUnique_path ρ v).unique hq hq'
  exact (SimpleGraph.Walk.concat_inj he).1

/-- Valency is at least 1 in a tree with at least two vertices. -/
theorem one_le_deg [Nontrivial ι] (hS : S.IsTree) (v : ι) : 1 ≤ deg S v := by
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨q⟩ := hS.connected v w
  cases q with
  | nil => exact absurd rfl hw
  | cons h _ => exact one_le_encard_iff_nonempty.2 ⟨_, h⟩

/-- The count of vertices of valency other than 2. -/
theorem card_not_two_add_two [Finite ι] [Nontrivial ι] (hS : S.IsTree) :
    (leaves S).ncard * 2 ≥ {v | deg S v ≠ 2}.ncard + 2 := by
  classical
  let := Fintype.ofFinite ι
  have hsum : ∑ v, S.degree v + 2 = 2 * Fintype.card ι := by
    have h₁ := S.sum_degrees_eq_twice_card_edges
    have h₂ := hS.card_edgeFinset
    omega
  have hL : (leaves S).ncard = ∑ v, if deg S v = 1 then 1 else 0 := by
    rw [← Finset.card_filter, ← ncard_coe_finset]
    congr 1
    ext v
    simp [leaves]
  have hB : {v | deg S v ≠ 2}.ncard = ∑ v, if deg S v ≠ 2 then 1 else 0 := by
    rw [← Finset.card_filter, ← ncard_coe_finset]
    congr 1
    ext v
    simp
  have hH (v : ι) :
      (if deg S v ≠ 2 then 1 else 0) + 2 ≤ S.degree v + 2 * (if deg S v = 1 then 1 else 0) := by
    have hpos := one_le_deg hS v
    rw [deg_eq_degree] at hpos
    have hpos' : 1 ≤ S.degree v := ENat.natCast_le_natCast.mp hpos
    have h₁ : deg S v = 1 ↔ S.degree v = 1 := by
      rw [deg_eq_degree]
      exact ENat.natCast_inj (b := 1)
    have h₂ : deg S v = 2 ↔ S.degree v = 2 := by
      rw [deg_eq_degree]
      exact ENat.natCast_inj (b := 2)
    by_cases htwo : S.degree v = 2
    · have hne₁ : deg S v ≠ 1 := fun h => by have := h₁.mp h; omega
      rw [ite_eq_right (fun h => h (h₂.mpr htwo)), ite_eq_right hne₁]
      omega
    · rw [ite_eq_left (fun h => htwo (h₂.mp h))]
      by_cases hone : S.degree v = 1
      · rw [ite_eq_left (h₁.mpr hone), hone]
      · rw [ite_eq_right (fun h => hone (h₁.mp h))]
        omega
  have h₃ := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hH v
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h₃
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h₃
  rw [← hL, ← hB] at h₃
  omega

/-- **The first fact in the proof of (5.4)** (page 342): a tree with few leaves has `2g + 1`
consecutive vertices of valency 2. -/
theorem exists_long_run [Fintype ι] [Nontrivial ι] (hS : S.IsTree) {g : ℕ} (hn : (2 * g + 1) * (2 *
  (leaves S).ncard - 3) + 1 < Fintype.card ι) :
    ∃ c : ℕ → ι, (∀ a b, a ≤ 2 * g → b ≤ 2 * g → c a = c b → a = b) ∧ (∀ a, a < 2 * g → S.Adj (c a)
      (c (a + 1))) ∧ ∀ a, a ≤ 2 * g → deg S (c a) = 2 := by
  classical
  have hcount := card_not_two_add_two hS
  obtain ⟨ρ, hρ⟩ : ∃ ρ, deg S ρ = 1 := by
    obtain ⟨v, hv⟩ := hS.exists_vert_degree_one_of_nontrivial
    refine ⟨v, ?_⟩
    simp [deg_eq_degree, hv]
  have hpar : ∀ v, ∃ w, v ≠ ρ → S.Adj v w ∧ S.dist ρ w + 1 = S.dist ρ v := fun v => by
    by_cases hv : v = ρ
    · exact ⟨v, fun h => absurd hv h⟩
    obtain ⟨q, hq⟩ := hS.connected.exists_walk_length_eq_dist v ρ
    cases q with
    | nil => exact absurd rfl hv
    | @cons _ w _ h q =>
      refine ⟨w, fun _ => ⟨h, ?_⟩⟩
      have h₁ : S.dist w ρ ≤ q.length := SimpleGraph.dist_le q
      rw [SimpleGraph.Walk.length_cons] at hq
      rw [SimpleGraph.dist_comm (u := ρ) (v := w), SimpleGraph.dist_comm (u := ρ) (v := v), ← hq]
      have h₂ := hS.dist_eq_dist_add_one_of_adj ρ h
      rw [SimpleGraph.dist_comm (u := ρ) (v := w), SimpleGraph.dist_comm (u := ρ) (v := v)] at h₂
      omega
  choose p hp using hpar
  have hρd : S.dist ρ ρ = 0 := SimpleGraph.dist_self
  have hdown : ∀ {v w}, S.Adj v w → S.dist ρ w = S.dist ρ v + 1 → p w = v := fun {v w} h hd => by
    have hw : w ≠ ρ := fun e => by
      rw [e] at hd
      omega
    obtain ⟨h₁, h₂⟩ := hp w hw
    exact closer_unique hS h₁.symm h h₂ hd.symm
  have hne : ∀ {v}, deg S v = 2 → v ≠ ρ := fun {v} h e => by
    rw [e, hρ] at h
    exact (by decide : (1 : ℕ∞) ≠ 2) h
  obtain ⟨N, hN⟩ : ∃ N, ∀ v, S.dist ρ v ≤ N := ⟨Finset.univ.sup fun v => S.dist ρ v, fun v
    => Finset.le_sup (Finset.mem_univ v)⟩
  have hchild : ∀ {v}, deg S v = 2 → ∃ w, S.Adj v w ∧ S.dist ρ w = S.dist ρ v + 1 := fun {v} hv
    => by
    obtain ⟨h₁, h₂⟩ := hp v (hne hv)
    obtain ⟨w, hw, hwn⟩ := exists_ne_of_one_lt_encard (s := S.neighborSet v) (by
      change 1 < deg S v
      rw [hv]
      decide) (p v)
    refine ⟨w, hw, (hS.dist_eq_dist_add_one_of_adj ρ hw).resolve_left fun h₃ => hwn ?_⟩
    exact closer_unique hS hw.symm h₁.symm h₃.symm h₂
  have hcover : ∀ k v, N - S.dist ρ v ≤ k → deg S v = 2 → ∃ b e, deg S b ≠ 2 ∧ b ≠ ρ ∧ 1 ≤ e
    ∧ p^[e] b = v ∧ ∀ e', 1 ≤ e' → e' ≤ e → deg S (p^[e'] b) = 2 := by
    intro k
    induction k with
    | zero =>
      intro v hk hv
      obtain ⟨w, -, hd⟩ := hchild hv
      have := hN w
      omega
    | succ k ih =>
      intro v hk hv
      obtain ⟨w, hw, hd⟩ := hchild hv
      have hpw := hdown hw hd
      by_cases hw2 : deg S w = 2
      · obtain ⟨b, e, h₁, h₂, h₃, h₄, h₅⟩ := ih w (by have := hN w; omega) hw2
        refine ⟨b, e + 1, h₁, h₂, by omega, by rw [Function.iterate_succ_apply', h₄, hpw], fun e'
          h₆ h₇ => ?_⟩
        rcases Nat.lt_or_ge e e' with h₈ | h₈
        · obtain rfl : e' = e + 1 := by omega
          rw [Function.iterate_succ_apply', h₄, hpw]
          exact hv
        · exact h₅ e' h₆ h₈
      · refine ⟨w, 1, hw2, fun e => ?_, le_rfl, hpw, fun e' h₆ h₇ => ?_⟩
        · rw [e] at hd
          omega
        · obtain rfl : e' = 1 := by omega
          rw [Function.iterate_one, hpw]
          exact hv
  by_cases hrun : ∃ b, deg S b ≠ 2 ∧ b ≠ ρ ∧ ∀ e', 1 ≤ e' → e' ≤ 2 * g + 1 → deg S (p^[e'] b) = 2
  · obtain ⟨b, -, hb, hdeg⟩ := hrun
    have hdist : ∀ e, e ≤ 2 * g + 1 → S.dist ρ (p^[e] b) + e = S.dist ρ b := by
      intro e
      induction e with
      | zero => exact fun _ => rfl
      | succ e ih =>
        intro he
        have hx : p^[e] b ≠ ρ := by
          rcases Nat.eq_zero_or_pos e with rfl | h₁
          · exact hb
          · exact hne (hdeg e h₁ (by omega))
        have := (hp _ hx).2
        rw [Function.iterate_succ_apply']
        have := ih (by omega)
        omega
    refine ⟨fun a => p^[a + 1] b, fun x y hx hy he => ?_, fun a ha => ?_, fun a ha => hdeg _
      (by omega) (by omega)⟩
    · have h₁ := hdist (x + 1) (by omega)
      have h₂ := hdist (y + 1) (by omega)
      simp only at he
      rw [he] at h₁
      omega
    · have := (hp _ (hne (hdeg (a + 1) (by omega) (by omega)))).1
      simp only
      rw [Function.iterate_succ_apply' p (a + 1)]
      exact this
  · exfalso
    let Bf : Finset ι := Finset.univ.filter fun v => deg S v ≠ 2
    let Df : Finset ι := Finset.univ.filter fun v => ¬ deg S v ≠ 2
    have hBf : {v | deg S v ≠ 2}.ncard = Bf.card := by
      rw [← ncard_coe_finset]
      congr 1
      ext v
      simp [Bf]
    have hρB : ρ ∈ Bf := by simp [Bf, hρ]
    have hsum : Bf.card + Df.card = Fintype.card ι := Finset.card_filter_add_card_filter_not _
    have hsub : Df ⊆ ((Bf.erase ρ) ×ˢ Finset.Icc 1 (2 * g)).image fun q => p^[q.2] q.1 := by
      intro v hv
      have hv2 : deg S v = 2 := by simpa [Df] using hv
      obtain ⟨b, e, h₁, h₂, h₃, h₄, h₅⟩ := hcover _ v le_rfl hv2
      have he : e ≤ 2 * g := by
        by_contra hlt
        exact hrun ⟨b, h₁, h₂, fun e' h₆ h₇ => h₅ e' h₆ (by omega)⟩
      refine Finset.mem_image.2 ⟨(b, e), ?_, h₄⟩
      simp [Bf, h₁, h₂, h₃, he]
    have hD := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [Finset.card_product, Finset.card_erase_of_mem hρB, Nat.card_Icc] at hD
    have hpos : 1 ≤ Bf.card := Finset.card_pos.2 ⟨ρ, hρB⟩
    rw [hBf] at hcount
    generalize (leaves S).ncard = L at hcount hn
    obtain ⟨u, hu⟩ : ∃ u, Bf.card = u + 1 := ⟨Bf.card - 1, by omega⟩
    rw [hu] at hD hcount hsum
    simp only [Nat.add_sub_cancel] at hD
    have h₁ : (2 * g + 1) * u ≤ (2 * g + 1) * (2 * L - 3) := Nat.mul_le_mul_left _ (by omega)
    have h₂ : (2 * g + 1) * u = u * (2 * g) + u := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega

/-- The core of the second fact: the path from `a₀` to `t` goes through `u`, then `v`. Delete the
edge `uv` and add `a₀t`. -/
theorem exists_more_leaves_side [Finite ι] (hS : S.IsTree) {a₀ u v t : ι} (h₁ : S.Adj a₀ u)
  (h₂ : S.Adj u v) (hva : v ≠ a₀) (hd₀ : deg S a₀ = 2) (hdu : deg S u = 2)
    (hdv : deg S v = 2) (π : S.Walk v t) (hπ : u ∉ π.support) (hta : t ≠ a₀) (htu : t ≠ u)
      (hnot : ¬ S.Adj a₀ t) :
    ∃ S' : SimpleGraph ι, S'.IsTree ∧ (∀ x y, S'.Adj x y → S.Adj x y ∨ s(x, y) = s(a₀, t)) ∧
      (leaves S).ncard + 1 ≤ (leaves S').ncard := by
  classical
  let := Fintype.ofFinite ι
  have hua : u ≠ a₀ := h₁.ne.symm
  have huv : u ≠ v := h₂.ne
  let S' : SimpleGraph ι :=
    { Adj := fun x y => (S.Adj x y ∧ s(x, y) ≠ s(u, v)) ∨ s(x, y) = s(a₀, t)
      symm := ⟨fun x y h => by
        rcases h with ⟨h, h'⟩ | h
        · exact Or.inl ⟨h.symm, by rwa [Sym2.eq_swap]⟩
        · exact Or.inr (by rwa [Sym2.eq_swap])⟩
      loopless := ⟨fun x h => by
        rcases h with ⟨h, -⟩ | h
        · exact h.ne rfl
        · have h₃ : x = a₀ ∧ x = t := by simpa [eq_comm] using h
          exact hta (h₃.2.symm.trans h₃.1)⟩ }
  have hS' : ∀ x y, S'.Adj x y ↔ (S.Adj x y ∧ s(x, y) ≠ s(u, v)) ∨ s(x, y) = s(a₀, t) := fun _ _
    => Iff.rfl
  have hwalk : ∀ {x y} (w : S.Walk x y), u ∉ w.support → S'.Reachable x y := fun {x y} w => by
    induction w with
    | nil => exact fun _ => SimpleGraph.Reachable.refl _
    | @cons x y z h q ih =>
      intro hu
      have hq : u ∉ q.support := fun h' => hu (by simp [h'])
      have hx : x ≠ u := fun e => hu (by simp [e])
      have hy : y ≠ u := fun e => hq (e ▸ q.start_mem_support)
      refine SimpleGraph.Adj.reachable (Or.inl ⟨h, fun e => ?_⟩) |>.trans (ih hq)
      rcases Sym2.eq_iff.1 e with ⟨h₃, -⟩ | ⟨-, h₃⟩
      · exact hx h₃
      · exact hy h₃
  have hR : S'.Reachable u v := by
    have h₃ : S'.Adj u a₀ := Or.inl ⟨h₁.symm, fun e => by
      rcases Sym2.eq_iff.1 e with ⟨-, h₄⟩ | ⟨h₄, -⟩
      · exact hva h₄.symm
      · exact huv h₄⟩
    have h₄ : S'.Adj a₀ t := Or.inr rfl
    exact h₃.reachable.trans (h₄.reachable.trans (hwalk π hπ).symm)
  have hconn : S'.Connected := by
    have := hS.connected.nonempty
    refine ⟨fun x y => ?_⟩
    obtain ⟨w⟩ := hS.connected x y
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons x y z h q ih =>
      refine SimpleGraph.Reachable.trans ?_ ih
      by_cases he : s(x, y) = s(u, v)
      · rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hR
        · exact hR.symm
      · exact SimpleGraph.Adj.reachable (Or.inl ⟨h, he⟩)
  have hedge : S'.edgeSet = (S.edgeSet \ {s(u, v)}) ∪ {s(a₀, t)} := by
    ext e
    induction e with
    | _ x y =>
      simp only [SimpleGraph.mem_edgeSet, mem_union, mem_sdiff, mem_singleton_iff, hS']
  have htree : S'.IsTree := by
    refine SimpleGraph.isTree_iff_connected_and_card.2 ⟨hconn, ?_⟩
    have h₃ := SimpleGraph.isTree_iff_connected_and_card.1 hS |>.2
    rw [Nat.card_coe_set_eq] at h₃ ⊢
    rw [hedge, ncard_union_eq _ (toFinite _) (toFinite _), ncard_singleton,
      ncard_sdiff_singleton_of_mem (show s(u, v) ∈ S.edgeSet from h₂)]
    · have : 1 ≤ S.edgeSet.ncard := (ncard_pos (toFinite _)).2 ⟨_, show s(u, v) ∈ S.edgeSet from h₂⟩
      omega
    · rw [disjoint_singleton_right]
      exact fun h => hnot h.1
  refine ⟨S', htree, fun x y h => ?_, ?_⟩
  · rcases h with ⟨h, -⟩ | h
    · exact Or.inl h
    · exact Or.inr h
  have hsame : ∀ w, w ≠ a₀ → w ≠ t → w ≠ u → w ≠ v → deg S' w = deg S w := fun w h₃ h₄ h₅ h₆ => by
    have : S'.neighborSet w = S.neighborSet w := by
      ext x
      simp only [SimpleGraph.mem_neighborSet, hS']
      constructor
      · rintro (⟨h, -⟩ | h)
        · exact h
        · rcases Sym2.eq_iff.1 h with ⟨h₇, -⟩ | ⟨h₇, -⟩
          · exact absurd h₇ h₃
          · exact absurd h₇ h₄
      · refine fun h => Or.inl ⟨h, fun e => ?_⟩
        rcases Sym2.eq_iff.1 e with ⟨h₇, -⟩ | ⟨h₇, -⟩
        · exact h₅ h₇
        · exact h₆ h₇
    rw [deg, deg, this]
  have hdeg_u : deg S' u = 1 := by
    have h₃ := neighborSet_eq hdu h₁.symm h₂ hva.symm
    have : S'.neighborSet u = {a₀} := by
      ext x
      simp only [SimpleGraph.mem_neighborSet, hS', mem_singleton_iff]
      constructor
      · rintro (⟨h, h'⟩ | h)
        · have hx : x ∈ S.neighborSet u := h
          rw [h₃] at hx
          rcases hx with rfl | rfl
          · rfl
          · exact absurd rfl h'
        · rcases Sym2.eq_iff.1 h with ⟨h₇, -⟩ | ⟨h₇, -⟩
          · exact absurd h₇ hua
          · exact absurd h₇.symm htu
      · rintro rfl
        refine Or.inl ⟨h₁.symm, fun e => ?_⟩
        rcases Sym2.eq_iff.1 e with ⟨-, h₄⟩ | ⟨h₄, -⟩
        · exact hva h₄.symm
        · exact huv h₄
    rw [deg, this, encard_singleton]
  have hLf : (leaves S).Finite := toFinite _
  have hnl : ∀ {w}, deg S w = 2 → w ∉ leaves S := fun {w} h h' => by
    exact (by decide : (2 : ℕ∞) ≠ 1) (h.symm.trans h')
  by_cases htv : t = v
  · have hsub : insert u (leaves S) ⊆ leaves S' := by
      rintro w (rfl | hw)
      · exact hdeg_u
      · have hw' : deg S w = 1 := hw
        have := hsame w (fun e => hnl (e ▸ hd₀) hw) (fun e => hnl (e ▸ htv ▸ hdv) hw) (fun e => hnl
          (e ▸ hdu) hw) (fun e => hnl (e ▸ hdv) hw)
        exact this.trans hw'
    have h₃ := ncard_le_ncard hsub (toFinite _)
    rw [ncard_insert_of_notMem (hnl hdu) hLf] at h₃
    exact h₃
  · have hdeg_v : deg S' v = 1 := by
      have : S'.neighborSet v = S.neighborSet v \ {u} := by
        ext x
        simp only [SimpleGraph.mem_neighborSet, hS', mem_sdiff, mem_singleton_iff]
        constructor
        · rintro (⟨h, h'⟩ | h)
          · refine ⟨h, ?_⟩
            rintro rfl
            exact h' Sym2.eq_swap
          · rcases Sym2.eq_iff.1 h with ⟨h₇, -⟩ | ⟨h₇, -⟩
            · exact absurd h₇ hva
            · exact absurd h₇.symm htv
        · rintro ⟨h, h'⟩
          refine Or.inl ⟨h, fun e => ?_⟩
          rcases Sym2.eq_iff.1 e with ⟨-, h₄⟩ | ⟨-, h₄⟩
          · exact h.ne h₄.symm
          · exact h' h₄
      have hcard := encard_sdiff_singleton_add_one (show u ∈ S.neighborSet v from h₂.symm)
      change (S.neighborSet v \ {u}).encard + 1 = deg S v at hcard
      rw [hdv] at hcard
      rw [deg, this]
      exact (ENat.addLECancellable_of_ne_top ENat.one_ne_top).inj_left.mp hcard
    have hsub : insert u (insert v (leaves S \ {t})) ⊆ leaves S' := by
      rintro w (rfl | rfl | ⟨hw, hwt⟩)
      · exact hdeg_u
      · exact hdeg_v
      · have hw' : deg S w = 1 := hw
        have := hsame w (fun e => hnl (e ▸ hd₀) hw) hwt (fun e => hnl (e ▸ hdu) hw) (fun e => hnl
          (e ▸ hdv) hw)
        exact this.trans hw'
    have h₃ := ncard_le_ncard hsub (toFinite _)
    have hv : v ∉ leaves S \ {t} := fun h => hnl hdv h.1
    have hu : u ∉ insert v (leaves S \ {t}) := by
      rintro (h | h)
      · exact huv h
      · exact hnl hdu h.1
    rw [ncard_insert_of_notMem hu (hLf.sdiff.insert _), ncard_insert_of_notMem hv hLf.sdiff] at h₃
    have h₄ := pred_ncard_le_ncard_sdiff_singleton (leaves S) t
    omega

/-- **The second fact in the proof of (5.4)** (page 342): adding an edge at the middle of five
consecutive vertices of valency 2 gives a spanning tree with more leaves. -/
theorem exists_more_leaves [Finite ι] (hS : S.IsTree) {a₂ a₁ a₀ b₁ b₂ t : ι} (h₁ : S.Adj a₂ a₁)
  (h₂ : S.Adj a₁ a₀) (h₃ : S.Adj a₀ b₁) (h₄ : S.Adj b₁ b₂) (hd₁ : deg S a₂ = 2) (hd₂ : deg S a₁
    = 2) (hd₃ : deg S a₀ = 2)
    (hd₄ : deg S b₁ = 2) (hd₅ : deg S b₂ = 2) (hab : a₁ ≠ b₁) (ha : a₂ ≠ a₀) (hb : b₂ ≠ a₀)
      (ht₁ : t ≠ a₁) (ht₂ : t ≠ a₀) (ht₃ : t ≠ b₁) :
    ∃ S' : SimpleGraph ι, S'.IsTree ∧ (∀ x y, S'.Adj x y → S.Adj x y ∨ s(x, y) = s(a₀, t)) ∧
      (leaves S).ncard + 1 ≤ (leaves S').ncard := by
  classical
  let := Fintype.ofFinite ι
  have hN₀ := neighborSet_eq hd₃ h₂.symm h₃ hab
  have hnot : ¬ S.Adj a₀ t := fun h => by
    have hm : t ∈ S.neighborSet a₀ := h
    rw [hN₀] at hm
    rcases hm with h' | h'
    · exact ht₁ h'
    · exact ht₃ h'
  have side : ∀ {u v : ι} (_ : S.Adj a₀ u) (_ : S.Adj u v) (_ : v ≠ a₀) (_ : deg S u = 2)
    (_ : deg S v = 2) (_ : t ≠ u) (q : S.Walk u t), q.IsPath → a₀ ∉ q.support →
      ∃ S' : SimpleGraph ι, S'.IsTree ∧ (∀ x y, S'.Adj x y → S.Adj x y ∨ s(x, y) = s(a₀, t)) ∧
        (leaves S).ncard + 1 ≤ (leaves S').ncard := by
    intro u v hu huv hv hdu hdv htu q hq hq₂
    cases q with
    | nil => exact absurd rfl htu
    | @cons _ w _ h' q' =>
      have hw : w = v := by
        have hm : w ∈ S.neighborSet u := h'
        rw [neighborSet_eq hdu hu.symm huv hv.symm] at hm
        rcases hm with rfl | hm
        · exact absurd (by simp) hq₂
        · exact hm
      subst hw
      refine exists_more_leaves_side hS hu huv hv hd₃ hdu hdv q' ?_ ht₂ htu hnot
      exact ((SimpleGraph.Walk.cons_isPath_iff _ _).1 hq).2
  obtain ⟨π, hπ⟩ := hS.connected.exists_isPath a₀ t
  cases π with
  | nil => exact absurd rfl ht₂
  | @cons _ w _ h' q =>
    have hm : w ∈ S.neighborSet a₀ := h'
    have hq₁ := (SimpleGraph.Walk.cons_isPath_iff _ _).1 hπ
    rw [hN₀] at hm
    rcases hm with rfl | hm
    · exact side h₂.symm h₁.symm ha hd₂ hd₁ ht₁ q hq₁.1 hq₁.2
    · obtain rfl : w = b₁ := hm
      exact side h₃ h₄ hb hd₄ hd₅ ht₃ q hq₁.1 hq₁.2

end GraphMinor.RST94
