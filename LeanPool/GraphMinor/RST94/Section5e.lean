/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section5d
import Mathlib.Tactic.Positivity

/-!
# Section 5 of "Quickly excluding a planar graph": arrays and (5.6)

Arrays (page 343), and (5.6). We build the columns of the array one at a time, as in the proof of
(5.6) on pages 343-344: each step uses (5.5), and the last column uses (2.12).
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G : Hypergraph α β}

/-- An `m × n` array (page 343), with `i ≤ m` and `j < n`. -/
structure IsArray (G : Hypergraph α β) (m n : ℕ) (W : ℕ → ℕ → Set α) : Prop where
  sub : ∀ i ≤ m, ∀ j < n, W i j ⊆ G.vertexSet
  conn : ∀ i ≤ m, ∀ j < n, Conn G (W i j)
  disj : ∀ i ≤ m, ∀ j < n, ∀ i' ≤ m, ∀ j' < n, (i, j) ≠ (i', j') → Disjoint (W i j) (W i' j')
  apex : ∀ i, 1 ≤ i → i ≤ m → ∀ j < n, ∃ x ∈ W 0 j, ∃ y ∈ W i j, G.skeleton.Adj x y
  row : ∀ i, 1 ≤ i → i ≤ m → ∀ j, j + 1 < n → ∃ x ∈ W i j, ∃ y ∈ W i (j + 1), G.skeleton.Adj x y

/-- The array built so far: columns `j < r`, with `W₀` the column of `W_{0j}`. -/
structure Arr (G : Hypergraph α β) (T : Set (Hypergraph α β × Hypergraph α β)) (θ m r : ℕ)
  (G' : Hypergraph α β) (z' : Fin m → α) (W : Fin m → ℕ → Set α) (W₀ : ℕ → Set α) : Prop where
  sub : ∀ i, ∀ j < r, W i j ⊆ G.vertexSet
  sub₀ : ∀ j < r, W₀ j ⊆ G.vertexSet
  conn : ∀ i, ∀ j < r, Conn G (W i j)
  conn₀ : ∀ j < r, Conn G (W₀ j)
  disj : ∀ i, ∀ j < r, ∀ i', ∀ j' < r, (i, j) ≠ (i', j') → Disjoint (W i j) (W i' j')
  disj₀ : ∀ j < r, ∀ j' < r, j ≠ j' → Disjoint (W₀ j) (W₀ j')
  cross : ∀ j < r, ∀ i, ∀ j' < r, Disjoint (W₀ j) (W i j')
  off : ∀ i, ∀ j < r, ∀ x ∈ W i j, x ∉ G'.vertexSet
  off₀ : ∀ j < r, ∀ x ∈ W₀ j, x ∉ G'.vertexSet
  apex : ∀ i, ∀ j < r, ∃ x ∈ W₀ j, ∃ y ∈ W i j, G.skeleton.Adj x y
  row : ∀ i, ∀ j, j + 1 < r → ∃ x ∈ W i j, ∃ y ∈ W i (j + 1), G.skeleton.Adj x y
  last : ∀ i, ∀ j, j + 1 = r → ∃ x ∈ W i j, G.skeleton.Adj x (z' i)
  rank : ∀ j < r, m ≤ tangleRank T θ (W₀ j ∪ ⋃ i, W i j)

/-- The rank of the current end vertices, by (2.7). -/
theorem rank_range {T T' : Set (Hypergraph α β × Hypergraph α β)} {θ θ' m : ℕ}
  (hT : IsTangle G θ T) {z' : Fin m → α} {G' : Hypergraph α β} (hN : Nodule G' T' θ' z') (hle : G'
    ≤ G)
    (hc : Conformal G G' T T' θ θ') : m ≤ tangleRank T θ (range z') := by
  have h₂ := ((isFreeSet_iff_tangleRank_eq hN.tangle).1 hN.free).2
  rw [ncard_range hN.inj, Fintype.card_fin] at h₂
  exact h₂.symm.le.trans (rank_le_of_conformal hle hT hN.tangle hc hN.free.1)

/-- One more column. In the middle of the array the new sets are given, and at the end they come
from (2.12). -/
theorem Arr.add {T T' : Set (Hypergraph α β × Hypergraph α β)} {θ θ' m r : ℕ}
  (hT : IsTangle G θ T) {G' G₂ : Hypergraph α β} {z' z₂ : Fin m → α} {W : Fin m → ℕ
    → Set α} {W₀ : ℕ → Set α} (ha : Arr G T θ m r G' z' W W₀) (hN : Nodule G' T' θ' z')
    (hle : G' ≤ G) (hc : Conformal G G' T T' θ θ') {N : Fin m → Set α} {C : Set α}
      (hN₁ : ∀ i, Conn G' (N i)) (hN₂ : ∀ i, N i ⊆ G'.vertexSet) (hN₃ : ∀ i, z' i ∈ N i)
        (hN₄ : Pairwise fun i j => Disjoint (N i) (N j))
    (hC₁ : Conn G' C) (hC₂ : C ⊆ G'.vertexSet) (hC₃ : ∀ i, Disjoint C (N i))
      (hC₄ : ∀ i, ∃ x ∈ C, ∃ y ∈ N i, G'.skeleton.Adj x y) (hoffN : ∀ i, ∀ x ∈ N i, x ∉
        G₂.vertexSet) (hoffC : ∀ x ∈ C, x ∉ G₂.vertexSet) (hle₂ : G₂ ≤ G')
    (hlast : ∀ i, ∃ x ∈ N i, G'.skeleton.Adj x (z₂ i)) :
    ∃ W₂ W₂₀, Arr G T θ m (r + 1) G₂ z₂ W₂ W₂₀ := by
  classical
  have hmono : ∀ {x y}, G'.skeleton.Adj x y → G.skeleton.Adj x y := fun h => skeleton_mono hle h
  have hG₂ : ∀ {x}, x ∈ G₂.vertexSet → x ∈ G'.vertexSet := fun h => hle₂.vertexSet_subset h
  let W₂ : Fin m → ℕ → Set α := fun i j => if j = r then N i else W i j
  let W₂₀ : ℕ → Set α := fun j => if j = r then C else W₀ j
  have hWr : ∀ i, W₂ i r = N i := fun i => by simp [W₂]
  have hW₀r : W₂₀ r = C := by simp [W₂₀]
  have hWo : ∀ i j, j < r → W₂ i j = W i j := fun i j hj => by simp [W₂, hj.ne]
  have hW₀o : ∀ j, j < r → W₂₀ j = W₀ j := fun j hj => by simp [W₂₀, hj.ne]
  have hcases : ∀ j, j < r + 1 → j < r ∨ j = r := fun j hj => by omega
  have hdN : ∀ i i', ∀ j < r, Disjoint (N i) (W i' j) := fun i i' j hj
    => disjoint_left.2 fun x hx hx' => ha.off i' j hj x hx' (hN₂ i hx)
  have hdC : ∀ i', ∀ j < r, Disjoint C (W i' j) := fun i' j hj => disjoint_left.2 fun x hx hx'
    => ha.off i' j hj x hx' (hC₂ hx)
  have hd₀N : ∀ i, ∀ j < r, Disjoint (W₀ j) (N i) := fun i j hj => disjoint_right.2 fun x hx hx'
    => ha.off₀ j hj x hx' (hN₂ i hx)
  have hd₀C : ∀ j < r, Disjoint (W₀ j) C := fun j hj => disjoint_right.2 fun x hx hx'
    => ha.off₀ j hj x hx' (hC₂ hx)
  refine ⟨W₂, W₂₀, ⟨fun i j hj => ?_, fun j hj => ?_, fun i j hj => ?_, fun j hj
    => ?_, fun i j hj i' j' hj' hne => ?_, fun j hj j' hj' hne => ?_, fun j hj i j' hj'
      => ?_, fun i j hj x hx hxG => ?_, fun j hj x hx hxG => ?_,
    fun i j hj => ?_, fun i j hj => ?_, fun i j hj => ?_, fun j hj => ?_⟩⟩
  · rcases hcases j hj with h | rfl
    · rw [hWo _ _ h]
      exact ha.sub i j h
    · rw [hWr]
      exact (hN₂ i).trans hle.vertexSet_subset
  · rcases hcases j hj with h | rfl
    · rw [hW₀o _ h]
      exact ha.sub₀ j h
    · rw [hW₀r]
      exact hC₂.trans hle.vertexSet_subset
  · rcases hcases j hj with h | rfl
    · rw [hWo _ _ h]
      exact ha.conn i j h
    · rw [hWr]
      exact (hN₁ i).mono hle
  · rcases hcases j hj with h | rfl
    · rw [hW₀o _ h]
      exact ha.conn₀ j h
    · rw [hW₀r]
      exact hC₁.mono hle
  · rcases hcases j hj with h | rfl <;> rcases hcases j' hj' with h' | rfl
    · rw [hWo _ _ h, hWo _ _ h']
      exact ha.disj i j h i' j' h' hne
    · rw [hWo _ _ h, hWr]
      exact (hdN i' i j h).symm
    · rw [hWr, hWo _ _ h']
      exact hdN i i' j' h'
    · rw [hWr, hWr]
      exact hN₄ fun e => hne (by rw [e])
  · rcases hcases j hj with h | rfl <;> rcases hcases j' hj' with h' | rfl
    · rw [hW₀o _ h, hW₀o _ h']
      exact ha.disj₀ j h j' h' hne
    · rw [hW₀o _ h, hW₀r]
      exact hd₀C j h
    · rw [hW₀r, hW₀o _ h']
      exact (hd₀C j' h').symm
    · exact absurd rfl hne
  · rcases hcases j hj with h | rfl <;> rcases hcases j' hj' with h' | rfl
    · rw [hW₀o _ h, hWo _ _ h']
      exact ha.cross j h i j' h'
    · rw [hW₀o _ h, hWr]
      exact hd₀N i j h
    · rw [hW₀r, hWo _ _ h']
      exact hdC i j' h'
    · rw [hW₀r, hWr]
      exact hC₃ i
  · rcases hcases j hj with h | rfl
    · rw [hWo _ _ h] at hx
      exact ha.off i j h x hx (hG₂ hxG)
    · rw [hWr] at hx
      exact hoffN i x hx hxG
  · rcases hcases j hj with h | rfl
    · rw [hW₀o _ h] at hx
      exact ha.off₀ j h x hx (hG₂ hxG)
    · rw [hW₀r] at hx
      exact hoffC x hx hxG
  · rcases hcases j hj with h | rfl
    · rw [hW₀o _ h, hWo _ _ h]
      exact ha.apex i j h
    · rw [hW₀r, hWr]
      obtain ⟨x, hx, y, hy, hxy⟩ := hC₄ i
      exact ⟨x, hx, y, hy, hmono hxy⟩
  · rcases hcases (j + 1) hj with h | h
    · rw [hWo _ _ h, hWo _ _ (by omega)]
      exact ha.row i j h
    · subst h
      rw [hWo _ _ (by omega), hWr]
      obtain ⟨x, hx, hxz⟩ := ha.last i j rfl
      exact ⟨x, hx, z' i, hN₃ i, hxz⟩
  · obtain rfl : j = r := by omega
    rw [hWr]
    obtain ⟨x, hx, hxz⟩ := hlast i
    exact ⟨x, hx, hmono hxz⟩
  · rcases hcases j hj with h | rfl
    · simp only [hW₀o _ h, hWo _ _ h]
      exact ha.rank j h
    · simp only [hW₀r, hWr]
      refine (rank_range hT hN hle hc).trans (tangleRank_mono hT ?_)
      rintro _ ⟨i, rfl⟩
      exact Or.inr (mem_iUnion.2 ⟨i, hN₃ i⟩)

/-- The first `n - 1` columns: the induction in the proof of (5.6) (page 343). -/
theorem exists_arr (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} {m : ℕ} {z
  : Fin m → α} (hN : Nodule G T θ z) {g n N t : ℕ} (hg : 2 ≤ g) (hm : 3 ≤ m)
    (ht : t = 2 * g * (m - 2) + N * (m + 1)) (hN' : N = (2 * g + 1) * (2 * m - 5) + 2) (hθ : 20 ^
      (n * t) ≤ θ) (hno : ¬ HasGrid G T θ g) (r : ℕ) (hr : r + 1 ≤ n) :
    ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (θ' : ℕ) (z' : Fin m → α)
      (W : Fin m → ℕ → Set α) (W₀ : ℕ → Set α),
      Nodule G' T' θ' z' ∧ G' ≤ G ∧ Conformal G G' T T' θ θ' ∧ 20 ^ ((n - r) * t) ≤ θ'
        ∧ Arr G T θ m r G' z' W W₀ := by
  have hT := hN.tangle
  induction r with
  | zero =>
    refine ⟨G, T, θ, z, fun _ _ => ∅, fun _ => ∅, hN, le_rfl, conformal_of_subset hT le_rfl
      subset_rfl, hθ, ?_⟩
    constructor <;> intros <;> omega
  | succ r ih =>
    obtain ⟨G', T', θ', z', W, W₀, hN₁, hle, hc, hb, ha⟩ := ih (by omega)
    obtain ⟨e, he⟩ : ∃ e, n - (r + 1) = e + 1 := ⟨n - (r + 1) - 1, by omega⟩
    have hsplit : n - r = n - (r + 1) + 1 := by omega
    set K := 20 ^ ((n - (r + 1)) * t) with hK
    have htN : N ≤ t := by
      have : N * 1 ≤ N * (m + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hk : N ≤ 2 * K := by
      have h₁ : t ≤ (n - (r + 1)) * t := by
        rw [he, Nat.succ_mul]
        omega
      have h₂ : (n - (r + 1)) * t < K := Nat.lt_pow_self (by omega)
      omega
    have hθ₂ : K * 20 ^ (2 * g * (m - 2) + N * (m + 1)) ≤ θ' := by
      rw [← ht, hK, ← pow_add, ← Nat.succ_mul, Nat.succ_eq_add_one, ← hsplit]
      exact hb
    have hG' : G'.IsGraph := IsGraph.of_le hG hle
    have hno' : ¬ HasGrid G' T' θ' g := fun h => hno (h.of_conformal hle hT hN₁.tangle hc)
    obtain ⟨G₂, T₂, θ₂, z₂, P, C, hR, hb₂, hL, hC, hCV, hCoff, hCt⟩ := theorem_5_5 hG' hN₁ hg hm
      hN' (Fintype.card_fin m) hk hθ₂ hno'
    obtain ⟨hP₁, hP₂, hP₃⟩ := hL
    have hne : ∀ i, z' i ≠ z₂ i := fun i e => hR.avoid i (e ▸ hR.nodule.free.1 (mem_range_self i))
    have hlast := fun i => exists_butlast (P i) (hP₁ i) (hne i)
    choose d q hd hq using hlast
    have hC₄ : ∀ i, ∃ x ∈ C, ∃ y ∈ {x | x ∈ (q i).support}, G'.skeleton.Adj x y := fun i => by
      obtain ⟨-, x, hx, u, hu, hun, hadj⟩ := hCt i
      exact ⟨x, hx, u, (hq i u).2 ⟨hu, hun⟩, hadj⟩
    obtain ⟨W₂, W₂₀, ha₂⟩ := ha.add (N := fun i => {x | x ∈ (q i).support}) (C := C) hT hN₁ hle hc
      (fun i => conn_support (q i)) (fun i x hx => support_mem (q i) (hN₁.free.1
        (mem_range_self i)) hx)
      (fun i => (q i).start_mem_support) (fun i j hij => disjoint_left.2 fun x hx hx'
        => disjoint_left.1 (hP₃ hij) ((hq i x).1 hx).1 ((hq j x).1 hx').1) hC hCV
      (fun i => disjoint_left.2 fun x hx hx' => (hCt i).1 x ((hq i x).1 hx').1 hx) hC₄
        (fun i x hx hxG => ((hq i x).1 hx).2 (hP₂ i x ((hq i x).1 hx).1 hxG)) hCoff hR.le (fun i
          => ⟨d i, (q i).end_mem_support, hd i⟩)
    exact ⟨G₂, T₂, θ₂, z₂, W₂, W₂₀, hR.nodule, hR.le.trans hle, Conformal.trans hle hR.le hT
      hN₁.tangle hR.nodule.tangle hc hR.conformal, hb₂, ha₂⟩

/-- The array of all `n` columns, with the last column from (2.12). -/
theorem exists_arr_all (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ} {m : ℕ}
  {z : Fin m → α} (hN : Nodule G T θ z) {g n N t : ℕ} (hg : 2 ≤ g) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (ht : t = 2 * g * (m - 2) + N * (m + 1)) (hN' : N = (2 * g + 1) * (2 * m - 5) + 2) (hθ : 20 ^
      (n * t) ≤ θ) (hno : ¬ HasGrid G T θ g) :
    ∃ (G' : Hypergraph α β) (z' : Fin m → α) (W : Fin m → ℕ → Set α) (W₀ : ℕ
      → Set α), Arr G T θ m n G' z' W W₀ := by
  have hT := hN.tangle
  obtain ⟨G', T', θ', z', W, W₀, hN₁, hle, hc, hb, ha⟩ := exists_arr hG hN hg hm ht hN' hθ hno
    (n - 1) (by omega)
  rw [show n - (n - 1) = 1 by omega, Nat.one_mul] at hb
  have hmt : m < θ' := by
    have h₁ : m * 1 ≤ m * ((2 * g + 1) * (2 * m - 5) + 2) := Nat.mul_le_mul_left _ (by omega)
    have h₂ : t < 20 ^ t := Nat.lt_pow_self (by omega)
    have h₃ : (m + 1) * 1 ≤ (m + 1) * N := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm (m + 1) N] at h₃
    omega
  have hrank : (range z').ncard < θ' := by
    rwa [ncard_range hN₁.inj, Fintype.card_fin]
  obtain ⟨C, hC₁, hC₂, hC₃, hC₄⟩ := theorem_2_12 hN₁.tangle hN₁.free hrank
  have hadj : ∀ i, ∃ y, y ∈ C ∧ G'.skeleton.Adj (z' i) y := fun i => hC₄ _ (mem_range_self i)
  choose y hy hy₂ using hadj
  obtain ⟨W₂, W₂₀, ha₂⟩ := ha.add (G₂ := G'.deleteVertices G'.vertexSet) (z₂ := y) (N := fun i
    => {z' i}) (C := C) hT hN₁ hle hc (fun i => conn_singleton) (fun i => singleton_subset_iff.2
      (hN₁.free.1 (mem_range_self i))) (fun i => rfl)
    (fun i j hij => disjoint_singleton.2 fun e => hij (hN₁.inj e)) hC₁ hC₂ (fun i
      => disjoint_singleton_right.2 fun h => disjoint_left.1 hC₃ h (mem_range_self i)) (fun i
        => ⟨y i, hy i, z' i, rfl, (hy₂ i).symm⟩)
    (fun i x _ hxG => hxG.2 hxG.1) (fun x _ hxG => hxG.2 hxG.1) (deleteVertices_le _ _) (fun i
      => ⟨z' i, rfl, hy₂ i⟩)
  rw [show n - 1 + 1 = n by omega] at ha₂
  exact ⟨_, y, W₂, W₂₀, ha₂⟩

/-- **(5.6)** (page 343). `𝒯` dominates the array means the bound on the rank in the conclusion. -/
theorem theorem_5_6 (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
  (hT : IsTangle G θ T) {g m n N t : ℕ} (hg : 2 ≤ g) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (ht : t = 2 * g * (m - 2) + N * (m + 1)) (hN' : N = (2 * g + 1) * (2 * m - 5) + 2) (hθ : 20 ^
      (n * t) ≤ θ) (hno : ¬ HasGrid G T θ g) :
    ∃ W, IsArray G m n W ∧ ∀ i ≤ m, min m n ≤ tangleRank T θ (⋃ j ∈ {j | j < n}, W i j) := by
  classical
  have hmθ : m ≤ θ := by
    have h₁ : m * 1 ≤ m * ((2 * g + 1) * (2 * m - 5) + 2) := Nat.mul_le_mul_left _ (by omega)
    have h₂ : t * 1 ≤ t * n := Nat.mul_le_mul_left _ hn
    have h₃ : n * t < 20 ^ (n * t) := Nat.lt_pow_self (by omega)
    have h₄ : (m + 1) * 1 ≤ (m + 1) * N := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm (m + 1) N] at h₄
    rw [Nat.mul_comm n t] at h₃ hθ
    omega
  obtain ⟨Y, -, hYc, hYf⟩ := exists_free_superset hT (X := ∅) ⟨empty_subset _, by simp, by simp⟩ (n
    := m) (by simp) hmθ
  have hYfin : Y.Finite := G.vertexSet_finite.subset hYf.1
  let e : hYfin.toFinset ≃ Fin m := Finset.equivFinOfCardEq (by rw [← ncard_eq_toFinset_card Y
    hYfin, hYc])
  let z : Fin m → α := fun i => (e.symm i).1
  have hzr : range z = Y := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact hYfin.mem_toFinset.1 (e.symm i).2
    · intro hx
      exact ⟨e ⟨x, hYfin.mem_toFinset.2 hx⟩, by simp [z]⟩
  have hN : Nodule G T θ z := by
    refine ⟨hT, fun _ _ h => e.symm.injective (Subtype.ext h), ?_⟩
    rwa [hzr]
  obtain ⟨G', z', W, W₀, ha⟩ := exists_arr_all hG hN hg hm hn ht hN' hθ hno
  let U : ℕ → ℕ → Set α := fun i j => if h : i = 0 then W₀ j else if h' : i - 1 < m then W ⟨i - 1,
    h'⟩ j else ∅
  have hU0 : ∀ j, U 0 j = W₀ j := fun j => by simp [U]
  have hUi : ∀ (c : Fin m) j, U (c.1 + 1) j = W c j := fun c j => by simp [U, c.2]
  have hcase : ∀ i, i ≤ m → i = 0 ∨ ∃ c : Fin m, i = c.1 + 1 := fun i hi => by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inl h
    · exact Or.inr ⟨⟨i - 1, by omega⟩, by simp; omega⟩
  let X : ℕ → Set α := fun j => W₀ j ∪ ⋃ i, W i j
  have hsubX : ∀ i ≤ m, ∀ j, U i j ⊆ X j := fun i hi j => by
    rcases hcase i hi with rfl | ⟨c, rfl⟩
    · rw [hU0]
      exact subset_union_left
    · rw [hUi]
      exact (subset_iUnion (fun i => W i j) c).trans subset_union_right
  have hXd : ∀ j < n, ∀ j' < n, j ≠ j' → Disjoint (X j) (X j') := fun j hj j' hj' hne => by
    refine disjoint_union_left.2 ⟨disjoint_union_right.2 ⟨ha.disj₀ j hj j' hj' hne,
      disjoint_iUnion_right.2 fun i => ha.cross j hj i j' hj'⟩, disjoint_iUnion_left.2 fun i =>
      disjoint_union_right.2 ⟨(ha.cross j' hj' i j hj).symm, disjoint_iUnion_right.2 fun i'
        => ha.disj i j hj i' j' hj' fun e => hne (Prod.ext_iff.1 e).2⟩⟩
  have hXc : ∀ j < n, Conn G (X j) := fun j hj => by
    have h₁ := conn_union_iUnion (E := fun i => W₀ j ∪ W i j) (ha.conn₀ j hj) (fun i => by
      obtain ⟨x, hx, y, hy, hxy⟩ := ha.apex i j hj
      exact (ha.conn₀ j hj).union_adj (ha.conn i j hj) hx hy hxy) (fun i => by
      obtain ⟨x, hx⟩ := (ha.conn₀ j hj).1
      exact ⟨x, hx, Or.inl hx⟩)
    have heq : (W₀ j ∪ ⋃ i, (W₀ j ∪ W i j)) = X j := by
      ext v
      simp only [X, mem_union, mem_iUnion]
      constructor
      · rintro (h | ⟨i, h | h⟩)
        · exact Or.inl h
        · exact Or.inl h
        · exact Or.inr ⟨i, h⟩
      · rintro (h | ⟨i, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, Or.inr h⟩
    rw [heq] at h₁
    exact h₁
  refine ⟨U, ⟨fun i hi j hj => ?_, fun i hi j hj => ?_, fun i hi j hj i' hi' j' hj' hne => ?_,
    fun i h₁ h₂ j hj => ?_, fun i h₁ h₂ j hj => ?_⟩, fun i hi => ?_⟩
  · rcases hcase i hi with rfl | ⟨c, rfl⟩
    · rw [hU0]
      exact ha.sub₀ j hj
    · rw [hUi]
      exact ha.sub c j hj
  · rcases hcase i hi with rfl | ⟨c, rfl⟩
    · rw [hU0]
      exact ha.conn₀ j hj
    · rw [hUi]
      exact ha.conn c j hj
  · rcases hcase i hi with rfl | ⟨c, rfl⟩ <;> rcases hcase i' hi' with rfl | ⟨c', rfl⟩
    · rw [hU0, hU0]
      exact ha.disj₀ j hj j' hj' fun e => hne (by rw [e])
    · rw [hU0, hUi]
      exact ha.cross j hj c' j' hj'
    · rw [hU0, hUi]
      exact (ha.cross j' hj' c j hj).symm
    · rw [hUi, hUi]
      exact ha.disj c j hj c' j' hj' fun e => hne (by
        have h₁ : c = c' := (Prod.ext_iff.1 e).1
        have h₂ : j = j' := (Prod.ext_iff.1 e).2
        rw [h₁, h₂])
  · rcases hcase i h₂ with rfl | ⟨c, rfl⟩
    · omega
    · rw [hU0, hUi]
      exact ha.apex c j hj
  · rcases hcase i h₂ with rfl | ⟨c, rfl⟩
    · omega
    · rw [hUi, hUi]
      exact ha.row c j hj
  · refine (le_rank_iff ((min_le_left _ _).trans hmθ)).2 fun A B hAB hY => ?_
    by_contra hlt
    push Not at hlt
    have hs : G.IsSeparation A B := hT.isSeparation hAB
    have hcard : (A ∩ B).vertexSet.ncard < (Finset.range n).card := by
      rw [Finset.card_range]
      have : separationOrder A B < n := hlt.trans_le (min_le_right _ _)
      exact this
    obtain ⟨j, hj, hd⟩ := exists_avoid (Finset.range n) X (fun a ha' b hb' hab => hXd a
      (Finset.mem_range.1 ha') b (Finset.mem_range.1 hb') hab) (A ∩ B).vertexSet_finite hcard
    have hj' : j < n := Finset.mem_range.1 hj
    obtain ⟨a, ha₁⟩ := (ha.conn₀ j hj').1
    obtain ⟨x, hx⟩ : (U i j).Nonempty := by
      rcases hcase i hi with rfl | ⟨c, rfl⟩
      · rw [hU0]
        exact (ha.conn₀ j hj').1
      · rw [hUi]
        exact (ha.conn c j hj').1
    have hxA : x ∈ A.vertexSet := hY (mem_iUnion₂.2 ⟨j, hj', hx⟩)
    have hXA : X j ⊆ A.vertexSet := fun b hb => by
      by_contra hbA
      have hbV : b ∈ G.vertexSet := by
        rcases hb with h | h
        · exact ha.sub₀ j hj' h
        · obtain ⟨c, hc⟩ := mem_iUnion.1 h
          exact ha.sub c j hj' hc
      have hbB : b ∈ B.vertexSet := (mem_V_or hs hbV).resolve_left hbA
      obtain ⟨v, hv, hvS⟩ := (hXc j hj').meets_sep hs (hsubX i hi j hx) hb hxA hbB
      exact disjoint_left.1 hd hv hvS
    have h₁ := tangleRank_le_separationOrder (θ := θ) hAB hXA
    have h₂ : m ≤ tangleRank T θ (X j) := ha.rank j hj'
    exact absurd (h₂.trans h₁) (not_le.2 (hlt.trans_le (min_le_left _ _)))

end GraphMinor.RST94
