/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Separator

/-!
# The separator of Lipton and Tarjan from explicit choices

`PlanarSeparator.exists_separation_of_reaches` proves the separator theorem by choosing a median
level, two thin levels and a balanced fundamental cycle. This file states the same construction
for *given* choices, in natural numbers, in the form in which a program computes it:

* levels `L` with a spanning tree `T₀` of the graph descending one level towards the root, and
  adjacent vertices at most one level apart;
* a median level `l₁`: the vertices below it, and those above it, weigh at most half;
* `j, j'` with `(t + 1) #K ≤ n` and `(t + 1) #K' ≤ n` for the levels `K = l₁ - j` and
  `K' = l₁ + 1 + j'`, where `t = ⌊√n⌋`;
* a dart `a` of the stellar subdivision and at most three vertices `X` such that, for the weights
  restricted to the middle levels, the vertices inside `a` and those outside `a`, both without
  `X`, weigh at most `2/3`;
* a test `ins` of the side of `a` for the vertices off the root paths of `a`.

The separator `S` consists of `K`, `K'` and the vertices of the middle levels on the root paths
of `a` or in `X`. The other vertices form four pieces (below `K`, above `K'`, inside, outside),
which are grouped greedily into two parts (`gpart`). The result (`levelSep`) is a separation
with both parts of weight at most `2/3` and `#S ≤ #K + #K' + 2 (j + j') + 3 ≤ 6 √n + 3`.

## References

* R. J. Lipton, R. E. Tarjan, *A separator theorem for planar graphs*, SIAM J. Appl. Math. 36
  (1979), 177–189.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

/-! ### Grouping four pieces greedily -/

/-- The weight accepted into the first part before piece `i`: a piece is accepted when the
first part stays within `2/3` of `Wt`. -/
def gacc (Wt : ℕ) (p : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if 3 * (gacc Wt p i + p i) ≤ 2 * Wt then gacc Wt p i + p i else gacc Wt p i

/-- The part of piece `i`: `1` if it is accepted, `2` otherwise. -/
def gpart (Wt : ℕ) (p : ℕ → ℕ) (i : ℕ) : ℕ := if 3 * (gacc Wt p i + p i) ≤ 2 * Wt then 1 else 2

lemma gpart_eq (Wt : ℕ) (p : ℕ → ℕ) (i : ℕ) : gpart Wt p i = 1 ∨ gpart Wt p i = 2 := by
  unfold gpart; split_ifs <;> simp

/-- **Greedy grouping.** Four pieces of weight at most `2/3` each and of total at most `Wt` are
grouped into two parts of weight at most `2/3` each. -/
theorem greedy4 (Wt : ℕ) (p : ℕ → ℕ) (hp : ∀ i < 4, 3 * p i ≤ 2 * Wt)
    (hs : p 0 + p 1 + p 2 + p 3 ≤ Wt) :
    3 * ∑ i ∈ range 4 with gpart Wt p i = 1, p i ≤ 2 * Wt ∧
      3 * ∑ i ∈ range 4 with gpart Wt p i = 2, p i ≤ 2 * Wt := by
  have h0 := hp 0 (by omega); have h1 := hp 1 (by omega); have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  have hg1 : ∀ i, (gpart Wt p i = 1) = (3 * (gacc Wt p i + p i) ≤ 2 * Wt) := by
    intro i; unfold gpart; split_ifs <;> simp_all
  have hg2 : ∀ i, (gpart Wt p i = 2) = ¬ (3 * (gacc Wt p i + p i) ≤ 2 * Wt) := by
    intro i; unfold gpart; split_ifs <;> simp_all
  simp only [hg1, hg2]
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [sum_range_succ, sum_range_zero, gacc, zero_add]
  split_ifs <;> omega

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {R : Kasteleyn.RotationSystem G}

/-! ### The construction -/

section Construction

variable (L : V → ℕ) (l₁ j j' : ℕ)

/-- The middle levels. -/
def MidL (v : V) : Prop := l₁ < L v + j ∧ L v < l₁ + 1 + j'

instance : DecidablePred (MidL L l₁ j j') := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The weights restricted to the middle levels, on the vertices of the stellar subdivision. -/
def wMid (w : V → ℕ) : V ⊕ (Map.ofRotation R).Face → ℕ :=
  Sum.elim (fun v => if MidL L l₁ j j' v then w v else 0) 0

variable (T : (Map.ofRotation R).stellar.SpTree) (a : StDart G.Dart)
  (X : Finset (V ⊕ (Map.ofRotation R).Face))

/-- The separator: the two thin levels and the vertices of the middle levels on the root paths of
`a` or in `X`. -/
def InS (v : V) : Prop :=
  L v + j = l₁ ∨ L v = l₁ + 1 + j' ∨ (MidL L l₁ j j' v ∧ (Sum.inl v : V ⊕ _) ∈ T.sep a ∪ X)

instance : DecidablePred (InS L l₁ j j' T a X) := fun _ => by unfold InS; infer_instance

/-- The piece of a vertex off the separator: `0` below, `1` above, `2` inside, `3` outside. -/
def piece (ins : V → Bool) (v : V) : ℕ :=
  if L v + j < l₁ then 0 else if l₁ + 1 + j' < L v then 1 else if ins v then 2 else 3

/-- The weight of a piece. -/
def pw (ins : V → Bool) (w : V → ℕ) (i : ℕ) : ℕ :=
  ∑ v with ¬ InS L l₁ j j' T a X v ∧ piece L l₁ j j' ins v = i, w v

end Construction

section Main

variable {L : V → ℕ} {l₁ j j' : ℕ}

omit [Fintype V] in
omit [DecidableEq V] [DecidableRel G.Adj] in
lemma sum_le_of_inl {Y : Finset (V ⊕ (Map.ofRotation R).Face)} (w : V → ℕ) {s : Finset V}
    (hs : ∀ v ∈ s, MidL L l₁ j j' v ∧ (Sum.inl v : V ⊕ _) ∈ Y) :
    ∑ v ∈ s, w v ≤ ∑ x ∈ Y, wMid (R := R) L l₁ j j' w x := by
  calc ∑ v ∈ s, w v = ∑ v ∈ s, wMid (R := R) L l₁ j j' w (Sum.inl v) :=
        sum_congr rfl fun v hv => by simp [wMid, (hs v hv).1]
    _ = ∑ x ∈ s.map Function.Embedding.inl, wMid (R := R) L l₁ j j' w x := by rw [sum_map]; rfl
    _ ≤ ∑ x ∈ Y, wMid (R := R) L l₁ j j' w x := sum_le_sum_of_subset (fun x hx => by
        obtain ⟨v, hv, rfl⟩ := mem_map.1 hx
        exact (hs v hv).2)

lemma sum_wMid_le (w : V → ℕ) : ∑ x, wMid (R := R) L l₁ j j' w x ≤ ∑ v, w v := by
  rw [Fintype.sum_sum_type]
  simp only [wMid, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, sum_const_zero, add_zero]
  exact sum_le_sum fun v _ => by split_ifs <;> simp

/-- **The separator of Lipton and Tarjan from explicit choices.** -/
theorem levelSep (hR : R.IsPlane) (T₀ : GTree G)
    (hpar : ∀ v, v ≠ T₀.root → L (T₀.parent v) + 1 = L v)
    (hadj : ∀ u v, G.Adj u v → L v ≤ L u + 1)
    (rep : (Map.ofRotation R).Face → G.Dart) (hrep : ∀ f, (Map.ofRotation R).face (rep f) = f)
    (w : V → ℕ) (hlow : 2 * ∑ v with L v < l₁, w v ≤ ∑ v, w v)
    (hhigh : 2 * ∑ v with l₁ < L v, w v ≤ ∑ v, w v)
    (a : StDart G.Dart) (X : Finset (V ⊕ (Map.ofRotation R).Face)) (hX : #X ≤ 3)
    (hin : 3 * ∑ x ∈ (liftTreeWith R T₀ rep hrep).inV a \ X, wMid L l₁ j j' w x ≤
      2 * ∑ x, wMid (R := R) L l₁ j j' w x)
    (hout : 3 * ∑ x ∈ (liftTreeWith R T₀ rep hrep).outV a \ X, wMid L l₁ j j' w x ≤
      2 * ∑ x, wMid (R := R) L l₁ j j' w x)
    (ins : V → Bool) (hins : ∀ v, (Sum.inl v : V ⊕ _) ∉ (liftTreeWith R T₀ rep hrep).sep a →
      (ins v = true ↔ (Sum.inl v : V ⊕ _) ∈ (liftTreeWith R T₀ rep hrep).inV a)) :
    IsSeparation G univ
      {v | InS L l₁ j j' (liftTreeWith R T₀ rep hrep) a X v}
      {v | ¬ InS L l₁ j j' (liftTreeWith R T₀ rep hrep) a X v ∧
        gpart (∑ v, w v) (pw L l₁ j j' (liftTreeWith R T₀ rep hrep) a X ins w)
          (piece L l₁ j j' ins v) = 1}
      {v | ¬ InS L l₁ j j' (liftTreeWith R T₀ rep hrep) a X v ∧
        gpart (∑ v, w v) (pw L l₁ j j' (liftTreeWith R T₀ rep hrep) a X ins w)
          (piece L l₁ j j' ins v) = 2} ∧
    3 * ∑ v with ¬ InS L l₁ j j' (liftTreeWith R T₀ rep hrep) a X v ∧
        gpart (∑ v, w v) (pw L l₁ j j' (liftTreeWith R T₀ rep hrep) a X ins w)
          (piece L l₁ j j' ins v) = 1, w v ≤ 2 * ∑ v, w v ∧
    3 * ∑ v with ¬ InS L l₁ j j' (liftTreeWith R T₀ rep hrep) a X v ∧
        gpart (∑ v, w v) (pw L l₁ j j' (liftTreeWith R T₀ rep hrep) a X ins w)
          (piece L l₁ j j' ins v) = 2, w v ≤ 2 * ∑ v, w v ∧
    #{v | InS L l₁ j j' (liftTreeWith R T₀ rep hrep) a X v} ≤
      #{v | L v + j = l₁} + #{v | L v = l₁ + 1 + j'} + 2 * (j + j') + 3 := by
  classical
  set M₁ := (Map.ofRotation R).stellar
  have hM₁ : M₁.IsPlane := Map.isPlane_stellar (Map.isPlane_ofRotation hR)
  set T := liftTreeWith R T₀ rep hrep
  set Wt := ∑ v, w v
  set S : V → Prop := InS L l₁ j j' T a X
  set κ := piece L l₁ j j' ins
  set p := pw L l₁ j j' T a X ins w
  have hκ4 : ∀ v, κ v < 4 := fun v => by simp only [κ, piece]; split_ifs <;> omega
  have hmid : ∀ v, ¬ S v → ¬ L v + j < l₁ → ¬ l₁ + 1 + j' < L v →
      MidL L l₁ j j' v ∧ (Sum.inl v : V ⊕ _) ∉ T.sep a ∪ X := by
    intro v hv h1 h2
    simp only [S, InS, not_or, not_and] at hv
    have hM : MidL L l₁ j j' v := ⟨by omega, by omega⟩
    exact ⟨hM, hv.2.2 hM⟩
  -- adjacent vertices off the separator lie in the same piece
  have hadjκ : ∀ u v, ¬ S u → ¬ S v → G.Adj u v → κ u = κ v := by
    intro u v hu hv huv
    have l1 := hadj u v huv
    have l2 := hadj v u huv.symm
    have a1 : L u + j ≠ l₁ ∧ L u ≠ l₁ + 1 + j' := by
      simp only [S, InS, not_or] at hu; exact ⟨hu.1, hu.2.1⟩
    have b1 : L v + j ≠ l₁ ∧ L v ≠ l₁ + 1 + j' := by
      simp only [S, InS, not_or] at hv; exact ⟨hv.1, hv.2.1⟩
    simp only [κ, piece]
    by_cases c1 : L u + j < l₁
    · rw [ite_eq_left c1, ite_eq_left (by omega)]
    rw [ite_eq_right c1, ite_eq_right (show ¬ L v + j < l₁ by omega)]
    by_cases c2 : l₁ + 1 + j' < L u
    · rw [ite_eq_left c2, ite_eq_left (by omega)]
    rw [ite_eq_right c2, ite_eq_right (show ¬ l₁ + 1 + j' < L v by omega)]
    obtain ⟨-, hu'⟩ := hmid u hu c1 c2
    obtain ⟨-, hv'⟩ := hmid v hv (by omega) (by omega)
    have hu'' : (Sum.inl u : V ⊕ _) ∉ T.sep a := fun h => hu' (mem_union_left _ h)
    have hv'' : (Sum.inl v : V ⊕ _) ∉ T.sep a := fun h => hv' (mem_union_left _ h)
    have hsep : ∀ x y : V, G.Adj x y → (Sum.inl x : V ⊕ _) ∈ T.inV a →
        (Sum.inl y : V ⊕ _) ∉ T.sep a → (Sum.inl y : V ⊕ _) ∈ T.inV a := by
      intro x y hxy hx hy
      by_contra hy'
      exact T.vert_α_ne_of_mem_inV hM₁ hx (mem_filter.2 ⟨mem_univ _, hy, hy'⟩)
        (d := StDart.old ⟨(x, y), hxy⟩) rfl rfl
    have e : ins u = ins v := by
      rw [Bool.eq_iff_iff, hins u hu'', hins v hv'']
      exact ⟨fun h => hsep u v huv h hv'', fun h => hsep v u huv.symm h hu''⟩
    rw [e]
  -- the pieces
  have hp0 : 3 * p 0 ≤ 2 * Wt := by
    have : p 0 ≤ ∑ v with L v < l₁, w v := by
      refine sum_le_sum_of_subset fun v hv => ?_
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      by_contra h
      have : κ v ≠ 0 := by simp only [κ, piece]; rw [ite_eq_right (by omega)]; split_ifs <;> simp
      exact this hv.2
    omega
  have hp1 : 3 * p 1 ≤ 2 * Wt := by
    have : p 1 ≤ ∑ v with l₁ < L v, w v := by
      refine sum_le_sum_of_subset fun v hv => ?_
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      by_contra h
      have : κ v ≠ 1 := by
        simp only [κ, piece]; rw [ite_eq_right (show ¬ l₁ + 1 + j' < L v by omega)]
        split_ifs <;> simp
      exact this hv.2
    omega
  have hWm := sum_wMid_le (R := R) (L := L) (l₁ := l₁) (j := j) (j' := j') w
  have hp2 : 3 * p 2 ≤ 2 * Wt := by
    have : p 2 ≤ ∑ x ∈ T.inV a \ X, wMid L l₁ j j' w x := by
      refine sum_le_of_inl w fun v hv => ?_
      simp only [mem_filter, mem_univ, true_and] at hv
      obtain ⟨hvS, hv2⟩ := hv
      by_cases c1 : L v + j < l₁
      · simp [piece, c1] at hv2
      by_cases c2 : l₁ + 1 + j' < L v
      · simp [piece, c1, c2] at hv2
      obtain ⟨hM, hX'⟩ := hmid v hvS c1 c2
      have hi : ins v = true := by
        by_contra hi; simp [piece, c1, c2, hi] at hv2
      refine ⟨hM, mem_sdiff.2 ⟨(hins v fun h => hX' (mem_union_left _ h)).1 hi,
        fun h => hX' (mem_union_right _ h)⟩⟩
    omega
  have hp3 : 3 * p 3 ≤ 2 * Wt := by
    have : p 3 ≤ ∑ x ∈ T.outV a \ X, wMid L l₁ j j' w x := by
      refine sum_le_of_inl w fun v hv => ?_
      simp only [mem_filter, mem_univ, true_and] at hv
      obtain ⟨hvS, hv2⟩ := hv
      by_cases c1 : L v + j < l₁
      · simp [piece, c1] at hv2
      by_cases c2 : l₁ + 1 + j' < L v
      · simp [piece, c1, c2] at hv2
      obtain ⟨hM, hX'⟩ := hmid v hvS c1 c2
      have hi : ins v = false := by
        by_contra hi; simp [piece, c1, c2, hi] at hv2
      have hs : (Sum.inl v : V ⊕ _) ∉ T.sep a := fun h => hX' (mem_union_left _ h)
      refine ⟨hM, mem_sdiff.2 ⟨mem_filter.2 ⟨mem_univ _, hs, fun h => ?_⟩,
        fun h => hX' (mem_union_right _ h)⟩⟩
      have := (hins v hs).2 h
      rw [hi] at this; exact Bool.false_ne_true this
    omega
  have hfib : ∀ g : ℕ, ∑ v with ¬ S v ∧ gpart Wt p (κ v) = g, w v =
      ∑ i ∈ range 4 with gpart Wt p i = g, p i := by
    intro g
    rw [← sum_fiberwise_of_maps_to (g := κ) (t := (range 4).filter fun i => gpart Wt p i = g)
      (fun v hv => by
        simp only [mem_filter, mem_univ, true_and, mem_range] at hv ⊢
        exact ⟨hκ4 v, hv.2⟩)]
    refine sum_congr rfl fun i hi => ?_
    simp only [p, pw, filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_range] at hi ⊢
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      change gpart Wt p (piece L l₁ j j' ins v) = g
      rw [h3]; exact hi.2
  have htot : p 0 + p 1 + p 2 + p 3 ≤ Wt := by
    have : ∑ i ∈ range 4, p i ≤ Wt := by
      have e := sum_fiberwise_of_maps_to (s := univ.filter fun v => ¬ S v) (g := κ)
        (t := range 4) (f := w) (fun v _ => mem_range.2 (hκ4 v))
      have e' : ∑ i ∈ range 4, p i = ∑ v with ¬ S v, w v := by
        rw [← e]
        refine sum_congr rfl fun i _ => ?_
        simp only [p, pw, filter_filter]
        rfl
      rw [e']
      exact sum_le_sum_of_subset (subset_univ _)
    simpa [sum_range_succ] using this
  obtain ⟨hA, hB⟩ := greedy4 Wt p (fun i hi => by
    interval_cases i <;> assumption) htot
  rw [← hfib 1] at hA
  rw [← hfib 2] at hB
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hA, hB, ?_⟩
  · ext v
    simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
    rcases gpart_eq Wt p (κ v) with h | h <;> tauto
  · exact disjoint_filter.2 fun v _ h1 h2 => h2.1 h1
  · exact disjoint_filter.2 fun v _ h1 h2 => h2.1 h1
  · exact disjoint_filter.2 fun v _ h1 h2 => by omega
  · intro u hu v hv huv
    simp only [mem_filter, mem_univ, true_and] at hu hv
    have := hadjκ u v hu.1 hv.1 huv
    rw [this] at hu
    omega
  · -- the size of the separator
    set Mid : Finset V := {v | MidL L l₁ j j' v}
    set I := (range (l₁ + 1 + j')).filter fun l => l₁ < l + j
    have hI : #I ≤ j + j' := by
      have : I ⊆ Ico (l₁ + 1 - j) (l₁ + 1 + j') := fun l hl => by
        obtain ⟨h1, h2⟩ := mem_filter.1 hl
        rw [mem_range] at h1
        rw [mem_Ico]
        omega
      refine (card_le_card this).trans ?_
      rw [Nat.card_Ico]
      omega
    have hTC : ∀ v ∈ (univ : Finset V), v ≠ T₀.root →
        T₀.parent v ∈ (univ : Finset V) ∧ L (T₀.parent v) + 1 = L v :=
      fun v _ hvr => ⟨mem_univ _, hpar v hvr⟩
    have hMidI : ∀ v ∈ Mid, L v ∈ I := fun v hv => by
      obtain ⟨-, h1, h2⟩ := mem_filter.1 hv
      exact mem_filter.2 ⟨mem_range.2 h2, h1⟩
    have hpath : ∀ x, #(Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc x) ≤ j + j' :=
      fun x => (card_filter_anc_le_with T₀ hTC (subset_univ Mid) hMidI x).trans hI
    have hXV : #((univ : Finset V).filter fun v => (Sum.inl v : V ⊕ _) ∈ X) ≤ 3 := by
      refine le_trans ?_ hX
      rw [← card_map Function.Embedding.inl]
      exact card_le_card fun x hx => by
        obtain ⟨v, hv, rfl⟩ := mem_map.1 hx
        exact (mem_filter.1 hv).2
    have hsub : ((univ : Finset V).filter fun v => S v) ⊆
        ((univ.filter fun v => L v + j = l₁) ∪ (univ.filter fun v => L v = l₁ + 1 + j')) ∪
          ((Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert a)) ∪
            (Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert (M₁.α a)))) ∪
          ((univ : Finset V).filter fun v => (Sum.inl v : V ⊕ _) ∈ X) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, S, InS] at hv
      simp only [mem_union, mem_filter, mem_univ, true_and, Mid]
      rcases hv with h | h | ⟨hM, h⟩
      · tauto
      · tauto
      · rcases mem_union.1 h with h | h
        · rcases mem_union.1 h with h | h <;> tauto
        · tauto
    refine (card_le_card hsub).trans ?_
    have e1 := card_union_le (((univ.filter fun v => L v + j = l₁) ∪
      (univ.filter fun v => L v = l₁ + 1 + j')) ∪
          ((Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert a)) ∪
            (Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert (M₁.α a)))))
      ((univ : Finset V).filter fun v => (Sum.inl v : V ⊕ _) ∈ X)
    have e2 := card_union_le ((univ.filter fun v => L v + j = l₁) ∪
      (univ.filter fun v => L v = l₁ + 1 + j'))
          ((Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert a)) ∪
            (Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert (M₁.α a))))
    have e3 := card_union_le (univ.filter fun v => L v + j = l₁)
      (univ.filter fun v => L v = l₁ + 1 + j')
    have e4 := card_union_le (Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert a))
      (Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert (M₁.α a)))
    have := hpath (M₁.vert a)
    have := hpath (M₁.vert (M₁.α a))
    omega

/-- The bound `#K + #K' + 2 (j + j') + 3 ≤ 6 √n + 3` for thin levels chosen among `t + 1`
levels, `t = ⌊√n⌋`. -/
theorem card_bound_real {n K K' j j' : ℕ} (hK : (Nat.sqrt n + 1) * K ≤ n)
    (hK' : (Nat.sqrt n + 1) * K' ≤ n) (hj : j ≤ Nat.sqrt n) (hj' : j' ≤ Nat.sqrt n) {s : ℕ}
    (hs : s ≤ K + K' + 2 * (j + j') + 3) : (s : ℝ) ≤ 6 * √(n : ℝ) + 3 := by
  have h1 := le_sqrt_of_mul_le hK
  have h2 := le_sqrt_of_mul_le hK'
  have h3 := sqrt_le_sqrt_real n
  have h4 : (s : ℝ) ≤ K + K' + 2 * (j + j') + 3 := by exact_mod_cast hs
  have h5 : (j : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hj
  have h6 : (j' : ℝ) ≤ Nat.sqrt n := by exact_mod_cast hj'
  linarith

end Main

end PlanarSeparator
