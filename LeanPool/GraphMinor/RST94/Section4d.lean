/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section4c

/-!
# Section 4 of "Quickly excluding a planar graph": (4.3)

Robertson, Seymour and Thomas, J. Combin. Theory Ser. B 62 (1994), (4.3), page 338. A component of
`G \ V(G')` that holds `Z` is given as a connected set that holds `Z` and avoids
`V(G')`.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β ι : Type*} {G : Hypergraph α β} {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α β)}

/-- The vertices of `Z` lie in the union of at most `r` connected sets that avoid `V(G')`, as in the
proof of (4.3). -/
def Cover (G G' : Hypergraph α β) (z : ι → α) (r : ℕ) : Prop :=
  ∃ 𝒟 : Finset (Set α), 𝒟.card ≤ r ∧ (∀ D ∈ 𝒟, Conn G D ∧ ∀ x ∈ D, x ∉ G'.vertexSet)
    ∧ ∀ i, ∃ D ∈ 𝒟, z i ∈ D

/-- The numbers in the proof of (4.3). -/
theorem bound_4_3 {n k r : ℕ} (hn : 2 ≤ n) (hk : n ≤ 2 * k) (hr : 1 ≤ r) :
    18 * (n + k * 20 ^ r) + 3 ≤ k * 20 ^ (r + 1) ∧ n ≤ k * 20 ^ r := by
  have h₁ : 20 ≤ 20 ^ r := by
    calc 20 = 20 ^ 1 := rfl
      _ ≤ 20 ^ r := Nat.pow_le_pow_right (by omega) hr
  have h₂ : k * 20 ≤ k * 20 ^ r := Nat.mul_le_mul_left k h₁
  have h₃ : k * 20 ^ (r + 1) = k * 20 ^ r * 20 := by rw [pow_succ, Nat.mul_assoc]
  rw [h₃]
  omega

variable [Fintype ι]

/-- The connected set `M` in the proof of (4.3): the union of two connected sets that hold `z i`, `z
j`, the two paths of the linkage, and `Q`. -/
theorem conn_merge {G₁ : Hypergraph α β} (hle : G₁ ≤ G) {a b c d : α} {D D' : Set α}
  (hD : Conn G D) (hD' : Conn G D')
    (ha : a ∈ D) (hb : b ∈ D') (p : G.skeleton.Walk a c) (p' : G.skeleton.Walk b d)
      (Q : G₁.skeleton.Walk c d) :
    Conn G (D ∪ {x | x ∈ p.support} ∪ {x | x ∈ Q.support} ∪ {x | x ∈ p'.support} ∪ D') := by
  have h₁ := hD.union (conn_support p) ⟨a, ha, p.start_mem_support⟩
  have h₂ := h₁.union ((conn_support Q).mono hle) ⟨c, Or.inr p.end_mem_support, Q.start_mem_support⟩
  have h₃ := h₂.union (conn_support p') ⟨d, Or.inr Q.end_mem_support, p'.end_mem_support⟩
  exact h₃.union hD' ⟨b, Or.inr p'.start_mem_support, hb⟩

/-- **(4.3)** (page 338), by the induction on `r` of the paper. -/
theorem cover_descent (hG : G.IsGraph) (hT : IsTangle G θ T) {z : ι → α} {k : ℕ} (hn : 2
  ≤ Fintype.card ι) (hk : Fintype.card ι ≤ 2 * k) (r : ℕ) :
    ∀ (G₁ : Hypergraph α β) (T₁ : Set (Hypergraph α β × Hypergraph α β)) (θ₁ : ℕ) (z₁ : ι
      → α), Residual G T θ z G₁ T₁ θ₁ z₁ → k * 20 ^ (r + 1) ≤ θ₁ → Cover G G₁ z (r + 1) →
      ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι
        → α), Residual G T θ z G' T' θ' z' ∧ k ≤ θ' ∧
        ∃ D, Conn G D ∧ range z ⊆ D ∧ ∀ x ∈ D, x ∉ G'.vertexSet := by
  classical
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hne
  induction r with
  | zero =>
    rintro G₁ T₁ θ₁ z₁ hR hθ ⟨𝒟, h𝒟, hmem, hcov⟩
    obtain ⟨D, hD, hzD⟩ := hcov i₀
    refine ⟨G₁, T₁, θ₁, z₁, hR, by omega, D, (hmem D hD).1, ?_, (hmem D hD).2⟩
    rintro _ ⟨i, rfl⟩
    obtain ⟨D', hD', hz⟩ := hcov i
    have := Finset.card_le_one.1 h𝒟 D' hD' D hD
    exact this ▸ hz
  | succ r ih =>
    rintro G₁ T₁ θ₁ z₁ hR hθ ⟨𝒟, h𝒟, hmem, hcov⟩
    obtain ⟨D₀, hD₀, hz₀⟩ := hcov i₀
    by_cases hall : ∀ j, z j ∈ D₀
    · exact ih G₁ T₁ θ₁ z₁ hR (by
        have h₁ : k * 20 ^ (r + 1) ≤ k * 20 ^ (r + 1 + 1) := Nat.mul_le_mul_left k
          (Nat.pow_le_pow_right (by omega) (by omega))
        omega) ⟨{D₀}, by simp, by
          intro D hD
          rw [Finset.mem_singleton] at hD
          exact hD ▸ hmem D₀ hD₀, fun i => ⟨D₀, by simp, hall i⟩⟩
    push Not at hall
    obtain ⟨j₀, hj₀⟩ := hall
    obtain ⟨D₁, hD₁, hz₁⟩ := hcov j₀
    have hij : i₀ ≠ j₀ := fun e => hj₀ (e ▸ hz₀)
    have hDne : D₁ ≠ D₀ := fun e => hj₀ (e ▸ hz₁)
    obtain ⟨hb₁, hb₂⟩ := bound_4_3 (r := r + 1) hn hk (by omega)
    have hG₁ : G₁.IsGraph := IsGraph.of_le hG hR.le
    obtain ⟨G₂, T₂, z₂, P, Q, hR₂, -, -, hQ, -⟩ := theorem_4_2 (k := k * 20 ^
      (r + 1)) hG₁ hR.nodule hb₂ (by omega) hij
    obtain ⟨p, hp₁, hp₂, hp₃⟩ := hR.link
    refine ih G₂ T₂ _ z₂ (hR.trans hT hR₂) le_rfl ?_
    have hG₂₁ : ∀ {x}, x ∈ G₂.vertexSet → x ∈ G₁.vertexSet := fun hx => hR₂.le.vertexSet_subset hx
    have hpav : ∀ i, ∀ x ∈ (p i).support, x ∉ G₂.vertexSet := fun i x hx hxG => by
      have := hp₂ i x hx (hG₂₁ hxG)
      exact hR₂.avoid i (this ▸ hxG)
    let M : Set α := D₀ ∪ {x | x ∈ (p i₀).support} ∪ {x | x ∈ Q.support} ∪ {x | x ∈
      (p j₀).support} ∪ D₁
    have hMconn : Conn G M := conn_merge hR.le (hmem D₀ hD₀).1 (hmem D₁ hD₁).1 hz₀ hz₁ (p i₀)
      (p j₀) Q
    have hMav : ∀ x ∈ M, x ∉ G₂.vertexSet := by
      rintro x ((((hx | hx) | hx) | hx) | hx) hxG
      · exact (hmem D₀ hD₀).2 x hx (hG₂₁ hxG)
      · exact hpav _ x hx hxG
      · exact hQ x hx hxG
      · exact hpav _ x hx hxG
      · exact (hmem D₁ hD₁).2 x hx (hG₂₁ hxG)
    refine ⟨insert M ((𝒟.erase D₀).erase D₁), ?_, ?_, fun i => ?_⟩
    · have h₁ := Finset.card_insert_le M ((𝒟.erase D₀).erase D₁)
      have h₂ : ((𝒟.erase D₀).erase D₁).card = 𝒟.card - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hDne, hD₁⟩), Finset.card_erase_of_mem hD₀]
        omega
      have h₃ : 2 ≤ 𝒟.card := Finset.one_lt_card.2 ⟨D₀, hD₀, D₁, hD₁, hDne.symm⟩
      omega
    · intro D hD
      rcases Finset.mem_insert.1 hD with rfl | hD
      · exact ⟨hMconn, hMav⟩
      · have hD' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hD)
        exact ⟨(hmem D hD').1, fun x hx hxG => (hmem D hD').2 x hx (hG₂₁ hxG)⟩
    · obtain ⟨D, hD, hz⟩ := hcov i
      by_cases h₀ : D = D₀
      · exact ⟨M, Finset.mem_insert_self _ _, Or.inl (Or.inl (Or.inl (Or.inl (h₀ ▸ hz))))⟩
      by_cases h₁ : D = D₁
      · exact ⟨M, Finset.mem_insert_self _ _, Or.inr (h₁ ▸ hz)⟩
      exact ⟨D, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h₁, Finset.mem_erase.2 ⟨h₀, hD⟩⟩), hz⟩

/-- **(4.3)** (page 338). -/
theorem theorem_4_3 (hG : G.IsGraph) {z : ι → α} (hN : Nodule G T θ z) {k : ℕ} (hn : 2
  ≤ Fintype.card ι) (hk : Fintype.card ι ≤ 2 * k)
    (hθ : k * 20 ^ Fintype.card ι ≤ θ) :
    ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : ι
      → α), Residual G T θ z G' T' θ' z' ∧ k ≤ θ' ∧
      ∃ D, Conn G D ∧ range z ⊆ D ∧ ∀ x ∈ D, x ∉ G'.vertexSet := by
  classical
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card ι)
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card ι = r + 1 + 1 := ⟨Fintype.card ι - 2, by omega⟩
  obtain ⟨hb₁, hb₂⟩ := bound_4_3 (r := r + 1) hn hk (by omega)
  rw [← hr] at hb₁
  obtain ⟨G₁, T₁, z₁, P, Q, hR, -, -, hQ, -⟩ := theorem_4_2 (k := k * 20 ^ (r + 1)) hG hN hb₂
    (by omega) hij
  refine cover_descent hG hN.tangle hn hk r G₁ T₁ _ z₁ hR le_rfl ?_
  refine ⟨insert {x | x ∈ Q.support} ((Finset.univ.erase i).erase j |>.image fun l =>
    ({z l} : Set α)), ?_, ?_, fun l => ?_⟩
  · have h₁ := Finset.card_insert_le ({x | x ∈ Q.support} : Set α) (((Finset.univ.erase i).erase
    j).image fun l => ({z l} : Set α))
    have h₂ := Finset.card_image_le (s := (Finset.univ.erase i).erase j) (f := fun l =>
      ({z l} : Set α))
    have h₃ : ((Finset.univ.erase i).erase j).card = Fintype.card ι - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      omega
    omega
  · intro D hD
    rcases Finset.mem_insert.1 hD with rfl | hD
    · exact ⟨conn_support Q, hQ⟩
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hD
      exact ⟨conn_singleton, fun x hx => (show x = z l from hx) ▸ hR.avoid l⟩
  · by_cases hi : l = i
    · exact ⟨_, Finset.mem_insert_self _ _, hi ▸ Q.start_mem_support⟩
    by_cases hj : l = j
    · exact ⟨_, Finset.mem_insert_self _ _, hj ▸ Q.end_mem_support⟩
    exact ⟨{z l}, Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨l, by simp [hi, hj], rfl⟩), rfl⟩

end GraphMinor.RST94
