/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Round
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Control.Decor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Uniform.System
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Spectral.Placements
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.GeometryPrices

/-!
# Parameters for routing on packed permutations
-/

@[expose] public section

section
/- The three-stage routing problem on packed permutations. -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Coloring

/-- A single controller works for every input permutation preserving
the base of the given product chart. Entries outside the packed set
are unspecified. The cost exponent is uniform over all charts. -/
def Factors (F : Type) [Field F] (cost : ℕ) : Prop :=
  ∀ (h : ℕ) (X C A D : Type) [Fintype X] [Fintype C] [Fintype A] [Fintype D]
    (s : X ≃ C × (A × D)) (e : X ↪ B h),
    ∃ f, Cheap F h h (Perm h) (.pair (Perm h) (.pair (Perm h) (Perm h))) f cost ∧
      ∀ (g : Equiv.Perm X), (∀ i, (s (g i)).1 = (s i).1) →
      ∀ y : (Perm h).obj, (∀ i, y (e i) = e (g i)) →
      ∃ u v w : Equiv.Perm X, g = u * v * w ∧
        (∀ i, (s (u i)).1 = (s i).1 ∧ (s (u i)).2.1 = (s i).2.1) ∧
        (∀ i, (s (v i)).1 = (s i).1 ∧ (s (v i)).2.2 = (s i).2.2) ∧
        (∀ i, (s (w i)).1 = (s i).1 ∧ (s (w i)).2.1 = (s i).2.1) ∧
        (∀ i, (f y).1 (e i) = e (u i)) ∧ (∀ i, (f y).2.1 (e i) = e (v i)) ∧
        (∀ i, (f y).2.2 (e i) = e (w i))

end MatrixMultiplicationAllFields.MatrixExponent.Coloring
end

/-
# A bounded-overlap market from a finite set of group elements
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing
open Spectral
open scoped Pointwise

variable {G I K S : Type} [Group G] [MulAction G I] (H : Finset G) (hH : 1 ∈ H)
  (r : ℕ) (g : G) (hg : letI := Classical.decEq G; g ∈ H ^ r)

open scoped Classical in
/-- The value specified by `Board.choose H r hH g hg ⟨I, i⟩`. -/
abbrev board (i : I) : Board H r := Board.choose H r hH g hg ⟨I, i⟩

open scoped Classical in
/-- Bundles the indexing function as an equivalence. -/
def labels (i : I) : (board H hH r g hg i).Site ≃ ball H r i :=
  Equiv.ofBijective (Board.name ⟨I, i⟩ (board H hH r g hg i))
    ((Board.valid_iff _ _ _).mp (Board.valid_choose H r hH g hg ⟨I, i⟩)).1

open scoped Classical in
/-- Builds `Market I (H ^ r).card where size i` with the specified `size`, `shape`, `name`,
`origin`. -/
def market : Market I (H ^ r).card where
  size i := (board H hH r g hg i).1.1
  shape i := (board H hH r g hg i).1.2
  name i := (labels H hH r g hg i).toEmbedding.trans (Function.Embedding.subtype _)
  origin i := ((Board.valid_iff _ _ _).mp (Board.valid_choose H r hH g hg ⟨I, i⟩)).2.1
  overlap x := by
    refine ⟨(H ^ r).image (fun a => a • x), Finset.card_image_le, fun i t ht => ?_⟩
    have hx : x ∈ ball H r i := ht ▸ (labels H hH r g hg i t).property
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨a, ha, by simp [← he]⟩

variable [Field K] [Fintype S] [DecidableEq S] (A : Finset (Tensor K S))

open scoped Classical in
theorem market_dst (i : I) :
    (market H hH r g hg).name i ((market H hH r g hg).shape i).dst = g⁻¹ • i :=
  ((Board.valid_iff _ _ _).mp (Board.valid_choose H r hH g hg ⟨I, i⟩)).2.2.1

open scoped Classical in
theorem market_link (i : I) (e : ((market H hH r g hg).shape i).edges) :
    let n := (market H hH r g hg).name i
    link H (n e.val.1) (n e.val.2) ∨ link H (n e.val.2) (n e.val.1) :=
  (((Board.valid_iff _ _ _).mp (Board.valid_choose H r hH g hg ⟨I, i⟩)).2.2.2 _ _).mp e.property

open scoped Classical in
theorem market_edge (i : I) (x y : ball H r i) (he : link H x.val y.val) :
    ((labels H hH r g hg i).symm x, (labels H hH r g hg i).symm y) ∈
      ((market H hH r g hg).shape i).edges := by
  let e := labels H hH r g hg i
  apply (((Board.valid_iff _ _ _).mp (Board.valid_choose H r hH g hg ⟨I, i⟩)).2.2.2 _ _).mpr
  left
  change link H (e (e.symm x)).val (e (e.symm y)).val
  simpa using he

variable [Fintype I]

open scoped Classical in
theorem market_passes (p : (market (I := I) H hH r g hg).Request A → ℝ) (ρ : ℝ) (i : I)
    (hp : let b := market H hH r g hg
      NearPrices ((b.shape i).tensor A) ((b.shape i).demands A) ρ (b.rates A p ∘ b.assign A i)) :
    ∃ P, (P = 0 ∨ ∃ D, P ∈ Tensor.ordinary K (ball H r i) D) ∧
      Passes A (ball H r i) (link H) i (g⁻¹ • i) (p (.inl i)) ((market H hH r g hg).quote A p) ρ P
        := by
  let b := market (I := I) H hH r g hg
  let e := (labels H hH r g hg i).symm
  change NearPrices _ _ _ (b.rates A p ∘ b.assign A i) at hp
  rw [b.rates_assign] at hp
  obtain ⟨P, hP, he⟩ := BallShape.near_passes A (b.shape i) e (link H)
    (market_edge H hH r g hg i) (p (.inl i)) (b.quote A p) ρ hp
  change Passes _ _ _ (b.name i (b.shape i).src) (b.name i (b.shape i).dst) _ _ _ _ at he
  rw [b.origin, show b.name i (b.shape i).dst = _ from market_dst H hH r g hg i] at he
  exact ⟨P, hP, he⟩

end MatrixMultiplicationAllFields.MatrixExponent.Routing
end

/-
# Direct transport along an orbit path

The baseline price of a payload is its path length. The path stays
inside its own center's ball, even when the radius is larger.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing
open Spectral
open scoped Pointwise

variable {I G K B : Type} [Group G] [MulAction G I] [Field K] [Fintype B] [DecidableEq B]

namespace BallShape

variable (K) (b : BallShape B)

open scoped Classical in
/-- Uses `Tensor.wire K e.val.1 e.val.2 2` as the representation. -/
def wire (e : b.edges) := Tensor.wire K e.val.1 e.val.2 2

open scoped Classical in
/-- The condition `∃ z : b.edges → ℕ, (∑ e, z e) ≤ d ∧ D ≤ Stock.bundle (b.wire K) z` on the
specified data. -/
def Direct (D : Tensor K B) (d : ℕ) : Prop :=
  ∃ z : b.edges → ℕ, (∑ e, z e) ≤ d ∧ D ≤ Stock.bundle (b.wire K) z

open scoped Classical in
theorem direct_self (x : B) : b.Direct K (Tensor.wire K x x 2) 0 := by
  refine ⟨fun _ => 0, by simp, ?_⟩
  simp [Stock.bundle, Tensor.wire_self K x (n := 2) (by decide)]

open scoped Classical in
theorem direct_step (x y t : B) (d : ℕ) (h : (y, t) ∈ b.edges)
    (h' : b.Direct K (Tensor.wire K x y 2) d) : b.Direct K (Tensor.wire K x t 2) (d + 1) := by
  obtain ⟨z, hz, hz'⟩ := h'
  let e : b.edges := ⟨(y, t), h⟩
  refine ⟨fun i => Stock.copies {e} 1 i + z i, ?_, ?_⟩
  · rw [Finset.sum_add_distrib]
    have he : (∑ i, Stock.copies {e} 1 i) = 1 := by simp [Stock.copies]
    rw [he]
    omega
  · rw [Stock.bundle_add, Stock.bundle_copies, Finset.prod_singleton, pow_one]
    refine (Tensor.wire_triangle K x y t 2).trans ?_
    rw [mul_comm]
    exact Tensor.mul_le_mul_left _ _ _ hz'

end BallShape

open scoped Classical in
theorem market_path (H : Finset G) (hH : 1 ∈ H) (r : ℕ) (g : G) (hg : g ∈ H ^ r)
    (d : ℕ) (hd : d ≤ r) (hgd : g ∈ H ^ d) (i : I) :
    let b := (market H hH r g hg).shape i
    b.Direct K (Tensor.wire K b.src b.dst 2) d := by
  let V := ball H r i
  let e := (labels H hH r g hg i).symm
  let b := (market H hH r g hg).shape i
  let Q (x : I) (n : ℕ) := ∀ hx : x ∈ V, b.Direct K (Tensor.wire K b.src (e ⟨x, hx⟩) 2) n
  have q : Q (g⁻¹ • i) d := by
    refine ball_path hH i (Q := Q) ?_ ?_ hd hgd
    · intro hi
      have he : e ⟨i, hi⟩ = b.src := (labels H hH r g hg i).symm_apply_eq.mpr
        (Subtype.ext ((market H hH r g hg).origin i).symm)
      change b.Direct K (Tensor.wire K b.src (e ⟨i, hi⟩) 2) 0
      rw [he]
      exact b.direct_self K _
    · intro x hx y hy n hxy hx' _
      have he := market_edge H hH r g hg i ⟨x, hx⟩ ⟨y, hy⟩ hxy
      exact b.direct_step K _ _ _ n he (hx' hx)
  have he : e ⟨g⁻¹ • i, mem_ball i hg⟩ = b.dst := (labels H hH r g hg i).symm_apply_eq.mpr
    (Subtype.ext (market_dst H hH r g hg i).symm)
  change b.Direct K (Tensor.wire K b.src b.dst 2) d
  rw [← he]
  exact q (mem_ball i hg)

end MatrixMultiplicationAllFields.MatrixExponent.Routing
end

/-
# Uniform cost of supplying a local tensor

On a fixed shape a connected core can broadcast as many labels as
the coordinate expansion requires. There are only finitely many
shapes and tuple commodities, so a uniform cap suffices.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing
open Spectral

variable {K S B : Type} [Field K] [Fintype S] [DecidableEq S] [Fintype B] [DecidableEq B]

open scoped Classical in
theorem BallShape.Direct.mono {b : BallShape B} {D : Tensor K B} {d e : ℕ}
    (h : b.Direct K D d) (he : d ≤ e) : b.Direct K D e := by
  obtain ⟨z, h, h'⟩ := h
  exact ⟨z, h.trans he, h'⟩

open scoped Classical in
theorem BallShape.direct_exists (b : BallShape B) (D : Tensor K B) : ∃ n, b.Direct K D n := by
  let _ : Nonempty B := ⟨b.src⟩
  have hc := b.broadcast (∅ : Finset (Tensor K B))
  rw [BallShape.links, Finset.prod_map] at hc
  change (2 : Tensor K B) ≤ ∏ e, b.wire K e at hc
  obtain ⟨n, hn⟩ := Tensor.exists_bound D
  have he := (Tensor.natCast_le (K := K) (S := B) (Nat.lt_two_pow_self (n := n)).le)
  rw [Nat.cast_pow, Nat.cast_ofNat] at he
  refine ⟨_, fun _ => n, le_rfl, (hn.trans he).trans ?_⟩
  rw [Stock.bundle, Finset.prod_pow]
  exact Tensor.powers_le hc _

open scoped Classical in
/-- The condition `∀ (b : Shape N) (j : b.2.Goods A), b.2.Direct K (b.2.tensor A j) M` on the
specified data. -/
def UniformCap (N : ℕ) (A : Finset (Tensor K S)) (M : ℕ) : Prop :=
  ∀ (b : Shape N) (j : b.2.Goods A), b.2.Direct K (b.2.tensor A j) M

open scoped Classical in
theorem uniform_cap (N : ℕ) (A : Finset (Tensor K S)) (d : ℕ) :
    ∃ M : ℕ, d ≤ M ∧ UniformCap N A M := by
  let _ : Fintype (Shape N) := Fintype.ofFinite _
  let J := Σ b : Shape N, b.2.Goods A
  choose n hn using fun j : J => j.1.2.direct_exists (j.1.2.tensor A j.2)
  refine ⟨d + ∑ j, n j, Nat.le_add_right _ _, fun b j => ?_⟩
  refine (hn ⟨b, j⟩).mono ?_
  exact (Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ _)).trans
    (Nat.le_add_left _ _)

end MatrixMultiplicationAllFields.MatrixExponent.Routing
end

/-
# Many admissible substitutions when payload prices are high
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing

open Spectral
open scoped BigOperators Pointwise

variable {I G K S : Type} [Field K] [Fintype S] [DecidableEq S] [Fintype I] [Nonempty I]

open scoped Classical in
/-- The defining condition `∀ p : b.Request A → ℝ, (∀ i, |p (.inl i)| ≤ d) → 1201 < (𝔼 i, p
(.inl i)) → ∃ J : Finset I, ρ * Fintype.card I < J.card ∧ ∀ i ∈ J, b.Fails A p ρ i`. -/
def Market.Frequent {N : ℕ} (b : Market I N) (A : Finset (Tensor K S)) (ρ d : ℝ) : Prop :=
  ∀ p : b.Request A → ℝ, (∀ i, |p (.inl i)| ≤ d) → 1201 < (𝔼 i, p (.inl i)) →
    ∃ J : Finset I, ρ * Fintype.card I < J.card ∧ ∀ i ∈ J, b.Fails A p ρ i

variable [Group G] [MulAction G I]

open scoped Classical in
theorem market_frequent (H : Finset G) (hH : 1 ∈ H) (r : ℕ) (g : G) (hg : g ∈ H ^ r)
    (A : Finset (Tensor K S)) (ρ d : ℝ)
    (h : ∀ (v : I → ℝ) (x : (S → I) → Tensor K S → ℝ) (good : Set I),
      (∀ i, |v i| ≤ d) → badFraction good ≤ ρ →
      (∀ i ∈ good, ∃ P : Tensor K (ball H r i) → ℝ,
        (P = 0 ∨ ∃ D, P ∈ Tensor.ordinary K (ball H r i) D) ∧
        Passes A (ball H r i) (link H) i (g⁻¹ • i) (v i) x ρ P) →
      (𝔼 i, v i) ≤ 1201) : (market (I := I) H hH r g hg).Frequent A ρ d := by
  let b := market (I := I) H hH r g hg
  intro p hp h₀
  let J := Finset.univ.filter (b.Fails A p ρ)
  let good := {i | ¬ b.Fails A p ρ i}
  refine ⟨J, ?_, fun i hi => (Finset.mem_filter.mp hi).2⟩
  by_contra! hsmall
  apply h₀.not_ge
  apply h _ (b.quote A p) good hp
  · rw [badFraction, Fintype.expect_eq_sum_div_card, div_le_iff₀ (by positivity)]
    simp only [J, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      at hsmall
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) hsmall
    by_cases h : b.Fails A p ρ i <;> simp [good, h]
  · intro i hi
    exact market_passes H hH r g hg A p ρ i (not_not.mp hi)

end MatrixMultiplicationAllFields.MatrixExponent.Routing
end

/-
# Certified rounds in a bounded-overlap market
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Market

open Spectral
open scoped BigOperators

variable {I S K : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S] [Field K]
  {N : ℕ} (b : Market I N) (A : Finset (Tensor K S))

open scoped Classical in
/-- Computes the payload by the application `Finset.univ.map Function.Embedding.inl`. -/
def payload : Finset (b.Request A) := Finset.univ.map Function.Embedding.inl

omit [DecidableEq I] [DecidableEq S] in
open scoped Classical in
theorem card_payload : (b.payload A).card = Fintype.card I := by simp [payload]

open scoped Classical in
/-- Chooses the operation for the left or right summand. -/
def cap (d M : ℕ) : b.Request A → ℝ := Sum.elim (fun _ => d) (fun _ => M)

variable {A} {M : ℕ} {ρ : ℝ}

open scoped Classical in
/-- Record the actual local moves, besides the induced order relation and
the volume bound for each newly issued request. -/
def Allowed (a : Atlas N A M ρ) (m : ℕ) (q : Intervention (b.Request A) b.Edge) : Prop :=
  q.Covers (b.tensor A ∘ Sum.inl) (b.tensor A ∘ Sum.inr) ∧
  (∀ u i, q.put u i ≤ N * (a.capacity * m)) ∧
  ∃ (J : Finset I) (moves : (i : J) → (b.code i).Move A),
    (∀ i : J, moves i ∈ a.menu (b.code i)) ∧
    q = Intervention.parallel (fun i : J => b.batch A i (moves i) m)

open scoped Classical in
theorem high_price_round [Nonempty I] [Nonempty S]
    (a : Atlas N A M ρ) (hM : 1 ≤ M) (m d : ℕ) (hd : d ≤ M)
    (hf : b.Frequent A ρ d)
    (p : b.Request A → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ b.cap A d M i)
    (h : 1201 * (b.payload A).card < ∑ i ∈ b.payload A, p i) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (q : J → Intervention (b.Request A) b.Edge),
      ρ * (b.payload A).card ≤ Fintype.card J ∧ Intervention.Overlap q N ∧
      (∀ j, (q j).Efficient p a.margin a.capacity m) ∧ b.Allowed a m (Intervention.parallel q) := by
  have hp' (i) : p i ∈ Set.Icc 0 (M : ℝ) := by
    refine ⟨(hp i).1, (hp i).2.trans ?_⟩
    cases i with
    | inl x => exact Nat.cast_le.mpr hd
    | inr x => exact le_rfl
  have hp'' (i) : |p (.inl i)| ≤ d := by
    rw [abs_of_nonneg (hp _).1]
    exact (hp _).2
  have h' : 1201 < (𝔼 i, p (.inl i)) := by
    rw [Fintype.expect_eq_sum_div_card, lt_div_iff₀ (by positivity)]
    rw [card_payload, payload, Finset.sum_map] at h
    exact h
  obtain ⟨J, hJ, hj⟩ := hf p hp'' h'
  choose moves hmove htrade using fun i : J =>
    b.choose_batch a (by exact_mod_cast hM) p hp' i (hj _ i.property)
  let q := fun i : J => b.batch A i (moves i) m
  have ho : Intervention.Overlap q N := b.batch_overlap J moves m
  have he (i : J) : (q i).Efficient p a.margin a.capacity m := (htrade i m).2
  refine ⟨J, inferInstance, inferInstance, q, ?_, ho, he,
    Intervention.parallel_covers q (fun i => (htrade i m).1), ?_, J, moves, hmove, rfl⟩
  · simpa only [card_payload, Fintype.card_coe] using hJ.le
  · exact fun u i => (Intervention.parallel_bounds q ho he i).2.2 u

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Market
end

/-
# Width at each core slot

Slots of different centers carry separate labels. Within a center the
selector communication is paid on top of the stock for the supplied
link tensors.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing
open Spectral Stock Finset

variable {I E J K S : Type} [Fintype I] [DecidableEq I] [DecidableEq E] [Fintype J] [DecidableEq J]
  [Field K] [Fintype S]

omit [Fintype I] in
open scoped Classical in
theorem Proposal.trade_core {T : J → Tensor K S} {H : ℝ} (q : Proposal T H)
    (g : J → I ⊕ E) (hg : Function.Injective g) (u : Finset J) (m C : ℕ)
    (ho : ∀ j, ∑ k, q.move.count j k ≤ C) (h : (q.trade g u m).choice) (e : E) :
    (q.trade g u m).core h e ≤ (q.move.bits + C) * m := by
  by_cases hz : (q.trade g u m).core h e = 0
  · rw [hz]; exact Nat.zero_le _
  obtain ⟨j, hj, _⟩ := collect_nonzero hz
  change collect g _ (.inr e) ≤ _
  rw [← hj, collect_inj hg, Proposal.output, add_mul]
  apply Nat.add_le_add
  · unfold copies
    split <;> simp
  · calc
      _ ≤ ∑ k, C * h.val k := by
        apply sum_le_sum
        intro k _
        apply Nat.mul_le_mul_right
        exact (sum_le_sum_of_subset (filter_subset _ _)).trans (ho k)
      _ = _ := by rw [← mul_sum, mem_histograms.mp h.property]

omit [Fintype I] in
open scoped Classical in
theorem Proposal.trade_edge {T : J → Tensor K S} {H : ℝ} (q : Proposal T H)
    (g : J → I ⊕ E) (u : Finset J) (m : ℕ) (h : (q.trade g u m).choice) (e : E)
    (hn : (q.trade g u m).core h e ≠ 0) : ∃ j, g j = .inr e := by
  obtain ⟨j, hj, _⟩ := collect_nonzero hn
  exact ⟨j, hj⟩

variable [DecidableEq S] {A : Finset (Tensor K S)} {N M : ℕ} {ρ : ℝ}

open scoped Classical in
theorem Market.width (b : Market I N) (a : Atlas N A M ρ) (C : ℕ)
    (hc : ∀ s q, q ∈ a.menu s → q.move.bits ≤ C)
    (m : ℕ) (q : Intervention (b.Request A) b.Edge) (hq : b.Allowed a m q)
    (h : q.choice) (e : b.Edge) : q.core h e ≤ (C + a.capacity) * m := by
  obtain ⟨_, _, J, moves, hm, rfl⟩ := hq
  let v (j : J) := (b.batch A j (moves j) m).core (h j) e
  have zero (j : J) (hj : j.val ≠ e.1) : v j = 0 := by
    by_contra hn
    obtain ⟨i, hi⟩ := (moves j).trade_edge _ _ _ _ _ hn
    rcases i with x | y
    · contradiction
    · exact hj (congrArg Sigma.fst (Sum.inr.inj hi))
  change (∑ j, v j) ≤ _
  by_cases he : e.1 ∈ J
  · let j : J := ⟨e.1, he⟩
    rw [Fintype.sum_eq_single j (fun i hi => zero i fun h => hi (Subtype.ext h))]
    exact ((moves j).trade_core _ (b.assign_injective _ _) _ _ _ (a.small _ _ (hm j)).2 _ e).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (hc _ _ (hm j)) _))
  · rw [sum_eq_zero (fun j _ => zero j fun h => he (h ▸ j.property))]
    exact Nat.zero_le _

end MatrixMultiplicationAllFields.MatrixExponent.Routing
end

/- # Polynomial cost of choosing histograms in parallel -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Atlas

open Spectral Finset

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S]
  {N : ℕ} {A : Finset (Tensor K S)} {ρ : ℝ}

/-- The atlas has finitely many shapes and finitely many moves at each shape. -/
theorem bound {M : ℝ} (a : Atlas N A M ρ) (f : (b : Shape N) → b.Move A → ℕ) :
    ∃ D, ∀ b q, q ∈ a.menu b → f b q ≤ D := by
  classical
  let _ : Fintype (Shape N) := Fintype.ofFinite _
  let g (b : Shape N) := (a.menu b).sup (f b)
  exact ⟨univ.sup g, fun b q h =>
    (le_sup (f := f b) h).trans (le_sup (f := g) (mem_univ b))⟩

/-- Each selected center contributes a histogram on a bounded alphabet. -/
theorem card_choice {M : ℕ} (a : Atlas N A M ρ) :
    ∃ C : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Market I N) (m : ℕ)
      (q : Intervention (b.Request A) b.Edge),
      b.Allowed a m q → Fintype.card q.choice ≤ (m + 1) ^ (C * Fintype.card I) := by
  classical
  obtain ⟨C, hC⟩ := a.bound (fun _ q => Fintype.card q.move.letter)
  refine ⟨C, fun I _ _ b m q h => ?_⟩
  obtain ⟨_, _, J, moves, hm, rfl⟩ := h
  change Fintype.card (∀ i : J, ↥(histograms (moves i).move.letter m)) ≤ _
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _ : J, (m + 1) ^ C := by
      apply prod_le_prod
      intro i _
      rw [Fintype.card_coe]
      exact (card_histograms _ _).trans (Nat.pow_le_pow_right (by omega) (hC _ _ (hm i)))
    _ = (m + 1) ^ (C * J.card) := by rw [prod_const, card_univ, Fintype.card_coe, pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left C (card_le_univ J))

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Atlas
end

/-
# Terminal supply of outstanding requests

Each request can be assigned a route wholly inside one ball. Thus
each edge is charged by only boundedly many request types.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Market
open Spectral

variable {I S K : Type} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S] [Field K]
  {N d M : ℕ} (b : Market I N) (A : Finset (Tensor K S))

open scoped Classical in
/-- The condition `∀ i, (b.shape i).Direct K ((b.shape i).tensor A (.inl none)) d` on the
specified data. -/
def ready (d : ℕ) : Prop :=
  ∀ i, (b.shape i).Direct K ((b.shape i).tensor A (.inl none)) d

open scoped Classical in
theorem supply_route (i : I) (j : BallShape.Requests (b.Site i) A)
    (h : (b.shape i).Direct K ((b.shape i).tensor A (.inl j)) d) :
    ∃ z : b.Edge → ℕ, (∑ e, z e) ≤ d ∧
      b.tensor A (.inl (b.request A i j)) ≤ Stock.bundle (b.tensor A ∘ Sum.inr) z ∧
      ∀ e, z e ≠ 0 → e.1 = i := by
  obtain ⟨z, hz, hz'⟩ := h
  let g : (b.shape i).edges → b.Edge := fun e => ⟨i, e⟩
  refine ⟨Stock.collect g z, ?_, ?_, ?_⟩
  · rw [show (∑ e, Stock.collect g z e) = ∑ e, z e from Finset.sum_fiberwise _ _ _]
    exact hz
  · rw [Stock.bundle_collect]
    let F : Tensor K (b.Site i) →* Tensor K I :=
      { toFun := Tensor.place (b.name i)
        map_one' := Tensor.place_one _
        map_mul' := Tensor.place_mul _ }
    have he : F ((b.shape i).tensor A (.inl j)) ≤ F (Stock.bundle ((b.shape i).wire K) z) :=
      Tensor.place_mono _ hz'
    refine (b.place_tensor A i (.inl j)).symm.le.trans (he.trans_eq ?_)
    unfold Stock.bundle
    rw [map_prod]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [map_pow]
    exact congrArg (· ^ z e) (b.place_tensor A i (.inr e))
  · intro e he
    obtain ⟨k, hk, _⟩ := Stock.collect_nonzero he
    exact congrArg Sigma.fst hk.symm

omit [Fintype I] [DecidableEq I] in
open scoped Classical in
theorem local_count (i : I) :
    Fintype.card (BallShape.Requests (b.Site i) A) ≤ 1 + N ^ Fintype.card S * A.card := by
  simp only [BallShape.Requests, Fintype.card_option, Fintype.card_prod, Fintype.card_fun,
    Site, Fintype.card_fin, add_comm 1]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_left (Nat.lt_succ_iff.mp (b.size i).isLt) _)) _

open scoped Classical in
theorem supply (h : b.ready A d) (hd : d ≤ M) (hM : UniformCap N A M) :
    ∃ z : b.Request A → b.Edge → ℕ,
      (∀ x, (∑ e, z x e : ℕ) ≤ b.cap A d M x ∧
        b.tensor A (.inl x) ≤ Stock.bundle (b.tensor A ∘ Sum.inr) (z x)) ∧
      ∀ e, ∑ x, z x e ≤ (1 + N ^ Fintype.card S * A.card) * M := by
  let U (i : I) := Finset.univ.image (b.request A i)
  have hu (i) : (U i).card ≤ 1 + N ^ Fintype.card S * A.card :=
    Finset.card_image_le.trans (b.local_count A i)
  have each (x : b.Request A) : ∃ z : b.Edge → ℕ,
      (∑ e, z e : ℕ) ≤ b.cap A d M x ∧
      b.tensor A (.inl x) ≤ Stock.bundle (b.tensor A ∘ Sum.inr) z ∧
      ∀ e, z e ≠ 0 → x ∈ U e.1 := by
    rcases x with i | ⟨⟨z, ⟨i, u⟩, rfl⟩, j⟩
    · obtain ⟨z, hz, ht, hu⟩ := b.supply_route A i none (h i)
      refine ⟨z, Nat.cast_le.mpr hz, ht, fun e he => ?_⟩
      rw [hu e he]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ none)
    · let a := some (u, j)
      obtain ⟨z, hz, ht, hu⟩ := b.supply_route A i a (hM (b.code i) (.inl a))
      refine ⟨z, Nat.cast_le.mpr hz, ht, fun e he => ?_⟩
      rw [hu e he]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  choose z hz ht he using each
  refine ⟨z, fun x => ⟨hz x, ht x⟩, fun e => ?_⟩
  rw [← Finset.sum_subset (Finset.subset_univ (U e.1))
    (fun x _ hx => Classical.byContradiction (fun hn => hx (he x e hn)))]
  calc
    _ ≤ ∑ _ ∈ U e.1, M := Finset.sum_le_sum fun x _ => by
      have hcap : b.cap A d M x ≤ M := by cases x <;> simp [cap, hd]
      exact (Finset.single_le_sum (fun i _ => Nat.zero_le (z x i)) (Finset.mem_univ e)).trans
        (Nat.cast_le.mp ((hz x).trans hcap))
    _ ≤ _ := by simpa using Nat.mul_le_mul_right M (hu e.1)

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Market
end

/-
# Finite parameters uniform over permutation actions

The finite detection radius may exceed the designated payload path
length. Keeping these separate permits an independent cap for all
auxiliary requests created inside a ball.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing
open Spectral
open scoped Pointwise

variable {k G J E A B E' A' B' : Type} [Field k] [Group G]

open scoped Classical in
/-- The data for the parameters construction, including `sites`, `start`, `core`, `unit`, `hop`. -/
structure Parameters (k : Type) [Field k] (K : J → Subgroup G) (g : G) where
  /-- The `Parameters` component of type `Finset G`. -/
  sites : Finset G
  start : 1 ∈ sites
  /-- The `Parameters` component of type `Finset G`. -/
  core : Finset G
  unit : 1 ∈ core
  hop : (↑core : Set G) ⊆ hops K
  /-- Stores the path associated with this `Parameters`. -/
  path : ℕ
  /-- Stores the radius associated with this `Parameters`. -/
  radius : ℕ
  path_pos : 0 < path
  path_le : path ≤ radius
  route : g ∈ core ^ path
  reach : g ∈ core ^ radius
  /-- The local table at each indexed position carried by `Parameters`, with type `Finset
  (Tensor k sites)`. -/
  table : Finset (Tensor k sites)
  nz : 0 ∉ table
  /-- Stores the tolerance associated with this `Parameters`. -/
  tolerance : ℝ
  pos : 0 < tolerance
  /-- Stores the limit associated with this `Parameters`. -/
  limit : ℕ
  pay : path ≤ limit
  local_supply : UniformCap (core ^ radius).card table limit
  /-- The `Parameters` component of type `Atlas (core ^ radius).card table limit tolerance`. -/
  offers : Atlas (core ^ radius).card table limit tolerance
  frequent : ∀ (I : Type) [Fintype I] [Nonempty I] [MulAction G I],
    (market (I := I) core unit radius g reach).Frequent table tolerance path

variable {K : J → Subgroup G} {g : G}

namespace Parameters

open scoped Classical in
/-- The value specified by `market (I := I) a.core a.unit a.radius g a.reach`. -/
abbrev balls (a : Parameters k K g) (I : Type) [MulAction G I] :=
  market (I := I) a.core a.unit a.radius g a.reach

open scoped Classical in
theorem ready (a : Parameters k K g) (I : Type) [MulAction G I] :
    (a.balls I).ready a.table a.path :=
  fun i => market_path _ _ _ _ _ _ a.path_le a.route i

end Parameters

variable [Fintype E] [Fintype A] [Fintype E'] [Fintype A']
  [Nonempty E] [Nonempty A] [Nonempty E'] [Nonempty A'] [Nonempty J]
  {p : E → A} {l : E → B} {p' : E' → A'} {l' : E' → B'}

open scoped Classical in
theorem Rigid.parameters (hgen : iSup K = ⊤) (h : Rigid (hops K) p l p' l')
    (hm : HasModels k p l p' l') (g : G) : Nonempty (Parameters k K g) := by
  obtain ⟨S, H, d, r, T, ρ, hS, hH, _, hhop, hd, hdr, hgd, hT, hρ, hh⟩ :=
    Rigid.finite_detection K hgen h hm g
  have hgr := Finset.pow_subset_pow_right hH hdr hgd
  let _ : Nonempty S := ⟨⟨1, hS⟩⟩
  obtain ⟨M, hdM, hM⟩ := uniform_cap (H ^ r).card T d
  obtain ⟨a⟩ := atlas (H ^ r).card T hT M hρ
  exact ⟨⟨S, hS, H, hH, hhop, d, r, hd, hdr, hgd, hgr, T, hT, ρ, hρ, M, hdM, hM, a,
    fun I _ _ _ => market_frequent H hH r g hgr T ρ d (hh I)⟩⟩

end MatrixMultiplicationAllFields.MatrixExponent.Routing
end
