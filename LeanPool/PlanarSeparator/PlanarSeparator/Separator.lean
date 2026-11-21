/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Spec
public import LeanPool.PlanarSeparator.PlanarSeparator.Fundamental
public import LeanPool.PlanarSeparator.PlanarSeparator.Stellar
public import LeanPool.PlanarSeparator.PlanarSeparator.Levels
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The planar separator theorem

`IsSeparation` is defined in `PlanarSeparator/Spec.lean`.

Let `R` be a plane rotation system (a combinatorial embedding in the sphere) of a simple graph
`G` with `n` vertices, and let `w` be nonnegative weights on the vertices with total at most
`1`. The **planar separator theorem** of Lipton and Tarjan says that there is a set `S` of
`O(√n)` vertices whose removal leaves two parts `A` and `B`, with no edge between them, each of
weight at most `2/3`. We prove it with the constant `6`: `#S ≤ 6 √n`
(`PlanarSeparator.planar_separator`).

The theorem holds for every induced subgraph of a plane graph, with `√m` for an induced subgraph
with `m` vertices (`PlanarSeparator.planar_separator_induce`): the vertex set `U` of the induced
subgraph is split as `S ∪ A ∪ B = U` with `#S ≤ 6 √(#U)`, no edge of `G` between `A` and `B`,
and the weights of `A` and `B` (for weights on `U` of total at most `1`) at most `2/3`.

## The proof

We first treat a vertex set `C` which is connected inside itself. Breadth-first search inside
`C` from a vertex `r` gives levels; let `l₁` be a median level for the weights. Among the
`t + 1` levels `l₁ - j` (`j ≤ t`, where `t = ⌊√n⌋`) one has at most `√n` vertices, and likewise
among the levels `l₁ + 1 + j'`. Removing these two levels `K` and `K'` leaves the vertices below
`K` (weight at most `1/2`), those above `K'` (weight at most `1/2`), and the middle part `Mid`,
spanning at most `2t` levels. To split `Mid` we apply the cycle separator lemma
(`PlanarSeparator.Map.SpTree.exists_balanced`) to the stellar subdivision of the map of `R`
(a plane map all of whose faces are triangles), with a spanning tree extending the
breadth-first tree of `C`, and with the weights restricted to `Mid`. The separator consists of
two root paths of this tree, which meet `Mid` in at most `2t` vertices. This gives four pieces,
pairwise without edges, of weight at most `2/3` each, which we group into two parts
(`PlanarSeparator.exists_separation_of_pieces`). In total `#S ≤ 2√n + 4t ≤ 6√n`.

Two simplifications compared with the original proof: no contraction of the inner levels is
needed, since the root paths of the spanning tree may leave `Mid` and only their vertices in
`Mid` are put in the separator; and the graph is not triangulated by adding chords inside the
faces, but by adding a vertex in each face (the stellar subdivision), which has the same effect
on the separating cycles and needs no choices. For the same reason no rotation system of an
induced subgraph is needed: its separating cycles are taken in the whole plane graph, and only
their vertices in the induced subgraph are counted.

For a general vertex set `U`, either every connected component of `U` has weight at most `2/3`,
and the components are grouped into two parts, or one component is heavier and is separated as
above.

## References

* R. J. Lipton, R. E. Tarjan, *A separator theorem for planar graphs*, SIAM J. Appl. Math. 36
  (1979), 177–189.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Grouping pieces into two parts -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Grouping pieces.** Suppose the vertices of `U \ S` are labelled so that adjacent vertices
have the same label, each label class (piece) has weight at most `2/3`, and the total weight is
at most `1`. Then the pieces can be grouped into two parts of weight at most `2/3` each. -/
theorem exists_separation_of_pieces {ι : Type*} [DecidableEq ι] {U S : Finset V} (hS : S ⊆ U)
    (κ : V → ι) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (hadj : ∀ u ∈ U \ S, ∀ v ∈ U \ S, G.Adj u v → κ u = κ v)
    (hpiece : ∀ i, ∑ v ∈ U \ S with κ v = i, w v ≤ 2 / 3) (htot : ∑ v ∈ U \ S, w v ≤ 1) :
    ∃ A B, IsSeparation G U S A B ∧ ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3 := by
  set X := U \ S
  set L := X.image κ
  set p : ι → ℝ := fun i => ∑ v ∈ X with κ v = i, w v
  have hp0 : ∀ i, 0 ≤ p i := fun i => sum_nonneg fun v _ => hw v
  set Fam := L.powerset.filter fun J => ∑ i ∈ J, p i ≤ 2 / 3
  have hFam : Fam.Nonempty := ⟨∅, by simp [Fam]; norm_num⟩
  obtain ⟨J, hJ, hmax⟩ := exists_max_image Fam (fun J => ∑ i ∈ J, p i) hFam
  obtain ⟨hJL, hJp⟩ := mem_filter.1 hJ
  rw [mem_powerset] at hJL
  set A := X.filter fun v => κ v ∈ J
  set B := X.filter fun v => κ v ∉ J
  have hA : ∑ v ∈ A, w v = ∑ i ∈ J, p i := by
    rw [← sum_fiberwise_of_maps_to (s := A) (t := J) (g := κ) (fun v hv => (mem_filter.1 hv).2)]
    refine sum_congr rfl fun i hi => ?_
    simp only [p, A, filter_filter]
    congr 1
    ext v
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨h1, hi, rfl⟩
  have hAB : ∑ v ∈ A, w v + ∑ v ∈ B, w v = ∑ v ∈ X, w v := sum_filter_add_sum_filter_not _ _ _
  have hBle : ∑ v ∈ B, w v ≤ 2 / 3 := by
    by_contra hB
    push Not at hB
    have hJs : ∑ i ∈ J, p i < 1 / 3 := by linarith
    obtain ⟨v, hvB, hv⟩ : ∃ v ∈ B, 0 < w v := by
      by_contra h
      push Not at h
      have : ∑ v ∈ B, w v ≤ 0 := sum_nonpos h
      linarith
    obtain ⟨hvX, hvJ⟩ := mem_filter.1 hvB
    have hiL : κ v ∈ L := mem_image_of_mem κ hvX
    have hpi : w v ≤ p (κ v) :=
      single_le_sum (f := w) (fun u _ => hw u) (mem_filter.2 ⟨hvX, rfl⟩)
    have h1 : p (κ v) ≤ ∑ i ∈ J, p i := by
      have := hmax {κ v} (mem_filter.2 ⟨by simpa using hiL, by simpa using hpiece (κ v)⟩)
      simpa using this
    have h2 := hmax (insert (κ v) J) (mem_filter.2 ⟨by
      rw [mem_powerset]; exact insert_subset hiL hJL, by
      rw [sum_insert hvJ]; linarith⟩)
    rw [sum_insert hvJ] at h2
    linarith
  refine ⟨A, B, ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [hA]; exact hJp, hBle⟩
  · rw [union_assoc, filter_union_filter_not_eq, union_sdiff_of_subset hS]
  · exact disjoint_of_subset_right (filter_subset _ _) disjoint_sdiff
  · exact disjoint_of_subset_right (filter_subset _ _) disjoint_sdiff
  · exact disjoint_filter_filter_not _ _ _
  · intro a ha b hb hab
    obtain ⟨haX, haJ⟩ := mem_filter.1 ha
    obtain ⟨hbX, hbJ⟩ := mem_filter.1 hb
    exact hbJ (hadj a haX b hbX hab ▸ haJ)

/-! ### Auxiliary counting -/

omit [Fintype V] [DecidableEq V] in
/-- A median level. -/
lemma exists_median (C : Finset V) (f : V → ℕ) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (h1 : ∑ v ∈ C, w v ≤ 1) :
    ∃ l, ∑ v ∈ C with f v < l, w v ≤ 1 / 2 ∧ ∑ v ∈ C with l < f v, w v ≤ 1 / 2 := by
  classical
  set W := ∑ v ∈ C, w v
  have hex : ∃ l, W / 2 ≤ ∑ v ∈ C with f v ≤ l, w v := by
    refine ⟨C.sup f, ?_⟩
    rw [filter_true_of_mem fun v hv => le_sup hv]
    have : 0 ≤ W := sum_nonneg fun v _ => hw v
    linarith
  refine ⟨Nat.find hex, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h]
      simp
    · have hmin := Nat.find_min hex (Nat.sub_lt h one_pos)
      push Not at hmin
      have : (C.filter fun v => f v < Nat.find hex) = C.filter fun v => f v ≤ Nat.find hex - 1 :=
        filter_congr fun v _ => by omega
      rw [this]
      linarith
  · have hs := Nat.find_spec hex
    have := sum_filter_add_sum_filter_not C (fun v => f v ≤ Nat.find hex) w
    have e : (C.filter fun v => ¬ f v ≤ Nat.find hex) = C.filter fun v => Nat.find hex < f v :=
      filter_congr fun v _ => by omega
    rw [e] at this
    linarith

omit [Fintype V] in
omit [DecidableEq V] in
/-- Among `m` disjoint subsets of `C`, one has at most `#C / m` elements. -/
lemma exists_mul_card_le (C : Finset V) (K : ℕ → Finset V) (hK : ∀ j, K j ⊆ C)
    (hdisj : ∀ i j, i ≠ j → Disjoint (K i) (K j)) {m : ℕ} (hm : 0 < m) :
    ∃ j < m, m * #(K j) ≤ #C := by
  classical
  have hsum : ∑ j ∈ range m, #(K j) ≤ #C := by
    rw [← card_biUnion fun i _ j _ hij => hdisj i j hij]
    exact card_le_card (biUnion_subset.2 fun j _ => hK j)
  by_contra h
  push Not at h
  have : ∑ j ∈ range m, #C < ∑ j ∈ range m, m * #(K j) :=
    sum_lt_sum_of_nonempty (nonempty_range_iff.2 hm.ne') fun j hj => h j (mem_range.1 hj)
  rw [sum_const, card_range, smul_eq_mul, ← mul_sum] at this
  have := Nat.mul_le_mul_left m hsum
  omega

lemma le_sqrt_of_mul_le {n k : ℕ} (h : (Nat.sqrt n + 1) * k ≤ n) : (k : ℝ) ≤ √(n : ℝ) := by
  have hlt : √(n : ℝ) < Nat.sqrt n + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast Nat.lt_succ_sqrt' n
  have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have h' : ((Nat.sqrt n : ℝ) + 1) * k ≤ n := by exact_mod_cast h
  have h0 := Real.sqrt_nonneg (n : ℝ)
  by_contra hk
  push Not at hk
  nlinarith

lemma sqrt_le_sqrt_real (n : ℕ) : (Nat.sqrt n : ℝ) ≤ √(n : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast Nat.sqrt_le' n

/-! ### Lifting a spanning tree of the graph to the stellar subdivision -/

section Lift

variable (R : Kasteleyn.RotationSystem G)

open StDart

/-- A dart of a face of the map of `R`. -/
noncomputable def faceRep (f : (Map.ofRotation R).Face) : G.Dart :=
  ((Map.ofRotation R).face_surjective f).choose

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma face_faceRep (f : (Map.ofRotation R).Face) : (Map.ofRotation R).face (faceRep R f) = f :=
  ((Map.ofRotation R).face_surjective f).choose_spec

/-- The spanning tree of the stellar subdivision of the map of `R` extending a spanning tree of
the graph, given a dart `rep f` on every face `f`: the centre of each face `f` hangs from the
initial vertex of `rep f`. -/
noncomputable def liftTreeWith (T : GTree G) (rep : (Map.ofRotation R).Face → G.Dart)
    (hrep : ∀ f, (Map.ofRotation R).face (rep f) = f) : (Map.ofRotation R).stellar.SpTree where
  root := .inl T.root
  par x h := match x, h with
    | .inl v, h => old ⟨(v, T.parent v), T.adj v (fun e => h (congrArg Sum.inl e))⟩
    | .inr f, _ => down (rep f)
  height x := match x with
    | .inl v => T.height v
    | .inr f => T.height (rep f).fst + 1
  vert_par x h := match x, h with
    | .inl _, _ => rfl
    | .inr f, _ => congrArg Sum.inr (hrep f)
  height_lt x h := match x, h with
    | .inl v, h => T.height_lt v (fun e => h (congrArg Sum.inl e))
    | .inr _, _ => Nat.lt_succ_self _

/-- The spanning tree of the stellar subdivision of the map of `R` extending a spanning tree of
the graph: the centre of each face hangs from a corner of the face. -/
noncomputable def liftTree (T : GTree G) : (Map.ofRotation R).stellar.SpTree :=
  liftTreeWith R T (faceRep R) (face_faceRep R)

variable {R}

lemma liftTreeWith_parent_inl (T : GTree G) {rep : (Map.ofRotation R).Face → G.Dart}
    {hrep : ∀ f, (Map.ofRotation R).face (rep f) = f} {v : V} (hv : v ≠ T.root) :
    (liftTreeWith R T rep hrep).parent (.inl v) = .inl (T.parent v) := by
  rw [Map.SpTree.parent_of_ne (liftTreeWith R T rep hrep) (fun e => hv (Sum.inl_injective e))]
  rfl

lemma liftTree_parent_inl (T : GTree G) {v : V} (hv : v ≠ T.root) :
    (liftTree R T).parent (.inl v) = .inl (T.parent v) :=
  liftTreeWith_parent_inl T hv

/-- The root paths of the lifted tree meet a breadth-first part `C` of the graph tree in at most
one vertex per level. -/
lemma card_filter_anc_le_with (T : GTree G) {rep : (Map.ofRotation R).Face → G.Dart}
    {hrep : ∀ f, (Map.ofRotation R).face (rep f) = f} {C Mid : Finset V} {lev : V → ℕ}
    (hT : ∀ v ∈ C, v ≠ T.root → T.parent v ∈ C ∧ lev (T.parent v) + 1 = lev v)
    (hMid : Mid ⊆ C) {I : Finset ℕ} (hI : ∀ v ∈ Mid, lev v ∈ I) (x : V ⊕ (Map.ofRotation R).Face) :
    #(Mid.filter fun v => (Sum.inl v : V ⊕ (Map.ofRotation R).Face) ∈
      (liftTreeWith R T rep hrep).anc x) ≤ #I := by
  classical
  set Q : Finset (V ⊕ (Map.ofRotation R).Face) := C.map Function.Embedding.inl
  set lev' : V ⊕ (Map.ofRotation R).Face → ℕ := Sum.elim lev fun _ => 0
  have hQ : ∀ y ∈ Q, y ≠ (liftTreeWith R T rep hrep).root →
      (liftTreeWith R T rep hrep).parent y ∈ Q ∧
        lev' ((liftTreeWith R T rep hrep).parent y) + 1 = lev' y := by
    intro y hy hyr
    obtain ⟨v, hv, rfl⟩ := mem_map.1 hy
    have hvr : v ≠ T.root := fun e => hyr (congrArg Sum.inl e)
    rw [Function.Embedding.inl_apply, liftTreeWith_parent_inl T hvr]
    obtain ⟨h1, h2⟩ := hT v hv hvr
    exact ⟨mem_map_of_mem _ h1, h2⟩
  refine le_trans ?_ ((liftTreeWith R T rep hrep).card_anc_filter_le hQ x I)
  rw [← card_map Function.Embedding.inl]
  refine card_le_card fun y hy => ?_
  obtain ⟨v, hv, rfl⟩ := mem_map.1 hy
  obtain ⟨hvM, hva⟩ := mem_filter.1 hv
  exact mem_filter.2 ⟨hva, mem_map_of_mem _ (hMid hvM), hI v hvM⟩

/-- The root paths of the lifted tree meet a breadth-first part `C` of the graph tree in at most
one vertex per level. -/
lemma card_filter_anc_le (T : GTree G) {C Mid : Finset V} {lev : V → ℕ}
    (hT : ∀ v ∈ C, v ≠ T.root → T.parent v ∈ C ∧ lev (T.parent v) + 1 = lev v)
    (hMid : Mid ⊆ C) {I : Finset ℕ} (hI : ∀ v ∈ Mid, lev v ∈ I) (x : V ⊕ (Map.ofRotation R).Face) :
    #(Mid.filter fun v => (Sum.inl v : V ⊕ (Map.ofRotation R).Face) ∈ (liftTree R T).anc x) ≤
      #I :=
  card_filter_anc_le_with T hT hMid hI x

end Lift

/-! ### The separator theorem for connected vertex sets -/

variable {R : Kasteleyn.RotationSystem G}

/-- **The planar separator theorem for a connected vertex set.** Let `C` be a set of vertices of
a plane graph, connected inside itself (every vertex of `C` is reached from `r` inside `C`), and
let `w` be nonnegative weights with total weight on `C` at most `1`. Then `C` is separated by at
most `6 √(#C)` vertices into two parts of weight at most `2/3`. -/
theorem exists_separation_of_reaches (hR : R.IsPlane) {C : Finset V} {r : V}
    (hC : Reaches G {r} C) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v ∈ C, w v ≤ 1) :
    ∃ S A B, IsSeparation G C S A B ∧ (#S : ℝ) ≤ 6 * √(#C : ℝ) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3 := by
  classical
  have hr : r ∈ C := hC.1 (mem_singleton_self r)
  have hlift : ∀ y, Relation.ReflTransGen G.Adj r y →
      Relation.ReflTransGen (fun a b => G.Adj a b ∧ b ∈ univ) r y := fun y h => by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hab ih => exact ih.tail ⟨hab, mem_univ _⟩
  have hGr : Reaches G C univ := ⟨subset_univ _, fun y _ => ⟨r, hr,
    hlift y ((SimpleGraph.reachable_iff_reflTransGen r y).1 (hR.connected.preconnected r y))⟩⟩
  set lv := lev G {r} C with hlv
  set n := #C
  set t := Nat.sqrt n
  obtain ⟨l₁, hlow, hhigh⟩ := exists_median C lv hw h1
  obtain ⟨j, hj, hjK⟩ := exists_mul_card_le C (fun j => C.filter fun v => lv v + j = l₁)
    (fun j => filter_subset _ _) (fun i j hij => disjoint_filter.2 fun v _ h1 h2 => hij (by omega))
    (Nat.succ_pos t)
  obtain ⟨j', hj', hj'K⟩ := exists_mul_card_le C (fun j => C.filter fun v => lv v = l₁ + 1 + j)
    (fun j => filter_subset _ _) (fun i j hij => disjoint_filter.2 fun v _ h1 h2 => hij (by omega))
    (Nat.succ_pos t)
  set K := C.filter fun v => lv v + j = l₁
  set K' := C.filter fun v => lv v = l₁ + 1 + j'
  set Mid := C.filter fun v => l₁ < lv v + j ∧ lv v < l₁ + 1 + j'
  -- the plane triangulated map and the spanning tree
  set M₁ := (Map.ofRotation R).stellar
  have hM₁ : M₁.IsPlane := Map.isPlane_stellar (Map.isPlane_ofRotation hR)
  have hT₁ : ∀ δ, M₁.IsTriangle δ := Map.isTriangle_stellar _ (Map.ofRotation_vert_α_ne R)
  set T₀ := GTree.ofLevels hC hGr
  set T := liftTree R T₀
  set w₁ : V ⊕ (Map.ofRotation R).Face → ℝ := Sum.elim (fun v => if v ∈ Mid then w v else 0) 0
  have hw₁ : ∀ x, 0 ≤ w₁ x := by
    rintro (v | f)
    · simp only [w₁, Sum.elim_inl]
      split_ifs
      · exact hw v
      · exact le_rfl
    · exact le_rfl
  have hMidC : Mid ⊆ C := filter_subset _ _
  have hsumMid : ∑ v ∈ Mid, w v ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg hMidC fun v _ _ => hw v).trans h1
  have h1₁ : ∑ x, w₁ x ≤ 1 := by
    rw [Fintype.sum_sum_type]
    simp only [w₁, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, sum_const_zero, add_zero]
    rw [← sum_filter]
    simpa using hsumMid
  have htransfer : ∀ (s : Finset V) (Y : Finset (V ⊕ (Map.ofRotation R).Face)),
      (∀ v ∈ s, v ∈ Mid ∧ (Sum.inl v : V ⊕ _) ∈ Y) → ∑ v ∈ s, w v ≤ ∑ x ∈ Y, w₁ x := by
    intro s Y hs
    calc ∑ v ∈ s, w v = ∑ v ∈ s, w₁ (Sum.inl v) :=
          sum_congr rfl fun v hv => by simp [w₁, (hs v hv).1]
      _ = ∑ x ∈ s.map Function.Embedding.inl, w₁ x := by rw [sum_map]; rfl
      _ ≤ ∑ x ∈ Y, w₁ x := sum_le_sum_of_subset_of_nonneg (fun x hx => by
          obtain ⟨v, hv, rfl⟩ := mem_map.1 hx
          exact (hs v hv).2) fun x _ _ => hw₁ x
  obtain ⟨d₀, -⟩ := hR.exists_dart r
  obtain ⟨δ, hin, hout⟩ := T.exists_balanced hM₁ hT₁ hw₁ h1₁ (StDart.old d₀)
  -- the separator
  set S := K ∪ K' ∪ Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.sep δ
  have hSC : S ⊆ C := union_subset (union_subset (filter_subset _ _) (filter_subset _ _))
    (fun v hv => hMidC (mem_filter.1 hv).1)
  have hnotS : ∀ v ∈ C \ S, lv v + j ≠ l₁ ∧ lv v ≠ l₁ + 1 + j' ∧
      (v ∈ Mid → (Sum.inl v : V ⊕ _) ∉ T.sep δ) := by
    intro v hv
    obtain ⟨hvC, hvS⟩ := mem_sdiff.1 hv
    refine ⟨fun h => hvS (by simp [S, K, hvC, h]), fun h => hvS (by simp [S, K', hvC, h]),
      fun hM h => hvS (mem_union_right _ (mem_filter.2 ⟨hM, h⟩))⟩
  -- the labels of the pieces
  set κ : V → ℕ := fun v => if lv v + j < l₁ then 0 else if l₁ + 1 + j' < lv v then 1 else
    if (Sum.inl v : V ⊕ _) ∈ T.inV δ then 2 else 3
  have hmid : ∀ v ∈ C \ S, ¬ lv v + j < l₁ → ¬ l₁ + 1 + j' < lv v → v ∈ Mid := by
    intro v hv h1 h2
    obtain ⟨e1, e2, -⟩ := hnotS v hv
    exact mem_filter.2 ⟨(mem_sdiff.1 hv).1, by omega, by omega⟩
  have hadj : ∀ u ∈ C \ S, ∀ v ∈ C \ S, G.Adj u v → κ u = κ v := by
    intro u hu v hv huv
    have hu' := (mem_sdiff.1 hu).1
    have hv' := (mem_sdiff.1 hv).1
    have l1 : lv v ≤ lv u + 1 := hC.lev_le_lev_add_one hu' hv' huv
    have l2 : lv u ≤ lv v + 1 := hC.lev_le_lev_add_one hv' hu' huv.symm
    obtain ⟨a1, a2, a3⟩ := hnotS u hu
    obtain ⟨b1, b2, b3⟩ := hnotS v hv
    simp only [κ]
    by_cases c1 : lv u + j < l₁
    · rw [ite_eq_left c1, ite_eq_left (by omega)]
    rw [ite_eq_right c1, ite_eq_right (show ¬ lv v + j < l₁ by omega)]
    by_cases c2 : l₁ + 1 + j' < lv u
    · rw [ite_eq_left c2, ite_eq_left (by omega)]
    rw [ite_eq_right c2, ite_eq_right (show ¬ l₁ + 1 + j' < lv v by omega)]
    have huM := hmid u hu c1 c2
    have hvM := hmid v hv (by omega) (by omega)
    have hsep : ∀ x y : V, G.Adj x y → (Sum.inl x : V ⊕ _) ∈ T.inV δ →
        (Sum.inl y : V ⊕ _) ∉ T.sep δ → (Sum.inl y : V ⊕ _) ∈ T.inV δ := by
      intro x y hxy hx hy
      by_contra hy'
      exact T.vert_α_ne_of_mem_inV hM₁ hx (mem_filter.2 ⟨mem_univ _, hy, hy'⟩)
        (d := StDart.old ⟨(x, y), hxy⟩) rfl rfl
    by_cases hU : (Sum.inl u : V ⊕ _) ∈ T.inV δ
    · rw [ite_eq_left hU, ite_eq_left (hsep u v huv hU (b3 hvM))]
    · rw [ite_eq_right hU, ite_eq_right fun hV => hU (hsep v u huv.symm hV (a3 huM))]
  have hpiece : ∀ i, ∑ v ∈ C \ S with κ v = i, w v ≤ 2 / 3 := by
    intro i
    have hsub : ∀ (s s' : Finset V), s ⊆ s' → ∑ v ∈ s, w v ≤ ∑ v ∈ s', w v :=
      fun s s' h => sum_le_sum_of_subset_of_nonneg h fun v _ _ => hw v
    match i with
    | 0 =>
      refine (hsub _ (C.filter fun v => lv v < l₁) fun v hv => ?_).trans (by linarith)
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      refine mem_filter.2 ⟨(mem_sdiff.1 hv1).1, ?_⟩
      by_contra c1
      have c1' : ¬ lv v + j < l₁ := by omega
      have : κ v ≠ 0 := by
        simp only [κ, ite_eq_right c1']
        split_ifs <;> simp
      exact this hv2
    | 1 =>
      refine (hsub _ (C.filter fun v => l₁ < lv v) fun v hv => ?_).trans (by linarith)
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      refine mem_filter.2 ⟨(mem_sdiff.1 hv1).1, ?_⟩
      by_contra c2
      have c2' : ¬ l₁ + 1 + j' < lv v := by omega
      have : κ v ≠ 1 := by
        simp only [κ, ite_eq_right c2']
        split_ifs <;> simp
      exact this hv2
    | 2 =>
      refine (htransfer _ (T.inV δ) fun v hv => ?_).trans hin
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      by_cases c1 : lv v + j < l₁
      · simp [κ, c1] at hv2
      by_cases c2 : l₁ + 1 + j' < lv v
      · simp [κ, c1, c2] at hv2
      by_cases c3 : (Sum.inl v : V ⊕ _) ∈ T.inV δ
      · exact ⟨hmid v hv1 c1 c2, c3⟩
      · simp [κ, c1, c2, c3] at hv2
    | 3 =>
      refine (htransfer _ (T.outV δ) fun v hv => ?_).trans hout
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      by_cases c1 : lv v + j < l₁
      · simp [κ, c1] at hv2
      by_cases c2 : l₁ + 1 + j' < lv v
      · simp [κ, c1, c2] at hv2
      by_cases c3 : (Sum.inl v : V ⊕ _) ∈ T.inV δ
      · simp [κ, c1, c2, c3] at hv2
      · have hM := hmid v hv1 c1 c2
        exact ⟨hM, mem_filter.2 ⟨mem_univ _, (hnotS v hv1).2.2 hM, c3⟩⟩
    | k + 4 =>
      have : (C \ S).filter (fun v => κ v = k + 4) = ∅ := by
        refine filter_false_of_mem fun v _ => ?_
        simp only [κ]
        split_ifs <;> simp
      rw [this, sum_empty]
      norm_num
  have htot : ∑ v ∈ C \ S, w v ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg sdiff_subset fun v _ _ => hw v).trans h1
  obtain ⟨A, B, hsepAB, hA, hB⟩ := exists_separation_of_pieces hSC κ hw hadj hpiece htot
  refine ⟨S, A, B, hsepAB, ?_, hA, hB⟩
  -- the size of the separator
  have hK : (#K : ℝ) ≤ √(n : ℝ) := le_sqrt_of_mul_le (by simpa [K] using hjK)
  have hK' : (#K' : ℝ) ≤ √(n : ℝ) := le_sqrt_of_mul_le (by simpa [K'] using hj'K)
  set I := (range (l₁ + 1 + j')).filter fun L => l₁ < L + j
  have hI : #I ≤ j + j' := by
    have : I ⊆ Ico (l₁ + 1 - j) (l₁ + 1 + j') := fun L hL => by
      obtain ⟨h1, h2⟩ := mem_filter.1 hL
      rw [mem_range] at h1
      rw [mem_Ico]
      omega
    refine (card_le_card this).trans ?_
    rw [Nat.card_Ico]
    omega
  have hTC : ∀ v ∈ C, v ≠ T₀.root → T₀.parent v ∈ C ∧ lv (T₀.parent v) + 1 = lv v :=
    fun v hv hvr => GTree.ofLevels_parent hC hGr hv hvr
  have hMidI : ∀ v ∈ Mid, lv v ∈ I := fun v hv => by
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hv
    exact mem_filter.2 ⟨mem_range.2 h2, h1⟩
  have hpath : ∀ x, #(Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc x) ≤ j + j' :=
    fun x => (card_filter_anc_le T₀ hTC hMidC hMidI x).trans hI
  have hS3 : #(Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.sep δ) ≤ 2 * (j + j') := by
    have : (Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.sep δ) ⊆
        (Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert δ)) ∪
          (Mid.filter fun v => (Sum.inl v : V ⊕ _) ∈ T.anc (M₁.vert (M₁.α δ))) := by
      intro v hv
      obtain ⟨h1, h2⟩ := mem_filter.1 hv
      rcases mem_union.1 h2 with h | h
      · exact mem_union_left _ (mem_filter.2 ⟨h1, h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨h1, h⟩)
    have := (card_le_card this).trans (card_union_le _ _)
    have := hpath (M₁.vert δ)
    have := hpath (M₁.vert (M₁.α δ))
    omega
  have hcard : #S ≤ #K + #K' + 2 * (j + j') :=
    (card_union_le _ _).trans (add_le_add (card_union_le _ _) hS3)
  have ht : (t : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt_real n
  have hjt : j + j' ≤ 2 * t := by omega
  have : (#S : ℝ) ≤ #K + #K' + 2 * (2 * t) := by
    have : (#S : ℝ) ≤ ((#K + #K' + 2 * (j + j') : ℕ) : ℝ) := by exact_mod_cast hcard
    have h2 : ((j + j' : ℕ) : ℝ) ≤ 2 * t := by exact_mod_cast hjt
    push_cast at this h2
    linarith
  linarith

/-! ### Connected components of a vertex set -/

variable (G) in
/-- Adjacency inside `U`. -/
def AdjIn (U : Finset V) (a b : V) : Prop := G.Adj a b ∧ a ∈ U ∧ b ∈ U

variable (G) in
/-- The connected component of `v` in the subgraph induced on `U`. -/
noncomputable def comp (U : Finset V) (v : V) : Finset V :=
  open Classical in U.filter fun u => Relation.ReflTransGen (AdjIn G U) v u

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma adjIn_symm {U : Finset V} {a b : V} (h : AdjIn G U a b) : AdjIn G U b a :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma rtg_symm {U : Finset V} {a b : V} (h : Relation.ReflTransGen (AdjIn G U) a b) :
    Relation.ReflTransGen (AdjIn G U) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (adjIn_symm hab) ih

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma mem_comp {U : Finset V} {v u : V} :
    u ∈ comp G U v ↔ u ∈ U ∧ Relation.ReflTransGen (AdjIn G U) v u := by
  classical
  simp [comp]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma comp_subset (U : Finset V) (v : V) : comp G U v ⊆ U := fun _ h => (mem_comp.1 h).1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma mem_comp_self {U : Finset V} {v : V} (hv : v ∈ U) : v ∈ comp G U v :=
  mem_comp.2 ⟨hv, Relation.ReflTransGen.refl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma comp_eq_of_adj {U : Finset V} {u x : V} (hu : u ∈ U) (hx : x ∈ U) (h : G.Adj u x) :
    comp G U u = comp G U x := by
  ext y
  rw [mem_comp, mem_comp]
  have hux : AdjIn G U u x := ⟨h, hu, hx⟩
  constructor
  · rintro ⟨hy, h'⟩
    exact ⟨hy, Relation.ReflTransGen.head (adjIn_symm hux) h'⟩
  · rintro ⟨hy, h'⟩
    exact ⟨hy, Relation.ReflTransGen.head hux h'⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma comp_eq_comp {U : Finset V} {v u : V} (hu : u ∈ comp G U v) : comp G U u = comp G U v := by
  ext y
  rw [mem_comp, mem_comp]
  have h := (mem_comp.1 hu).2
  constructor
  · rintro ⟨hy, h'⟩
    exact ⟨hy, h.trans h'⟩
  · rintro ⟨hy, h'⟩
    exact ⟨hy, (rtg_symm h).trans h'⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A connected component is closed under adjacency inside `U`. -/
lemma mem_comp_of_adj {U : Finset V} {v u x : V} (hu : u ∈ comp G U v) (hx : x ∈ U)
    (h : G.Adj u x) : x ∈ comp G U v := by
  obtain ⟨huU, hvu⟩ := mem_comp.1 hu
  exact mem_comp.2 ⟨hx, hvu.tail ⟨h, huU, hx⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A connected component is reached from each of its vertices inside itself. -/
lemma reaches_comp {U : Finset V} {v : V} (hv : v ∈ U) : Reaches G {v} (comp G U v) := by
  refine ⟨singleton_subset_iff.2 (mem_comp_self hv), fun y hy => ⟨v, mem_singleton_self v, ?_⟩⟩
  have h := (mem_comp.1 hy).2
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hva hab ih =>
    exact (ih (mem_comp.2 ⟨hab.2.1, hva⟩)).tail ⟨hab.1, mem_comp.2 ⟨hab.2.2, hva.tail hab⟩⟩

/-! ### The planar separator theorem -/

/-- **The planar separator theorem for induced subgraphs** (Lipton–Tarjan). Let `R` be a plane
rotation system of the graph `G`, let `U` be a set of vertices and let `w` be nonnegative weights
with total weight on `U` at most `1`. Then `U` is separated by a set `S` of at most `6 √(#U)` of
its vertices into two parts `A` and `B`, with no edge of `G` between them, each of weight at most
`2/3`. -/
theorem planar_separator_induce (hR : R.IsPlane) (U : Finset V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v ∈ U, w v ≤ 1) :
    ∃ S A B, IsSeparation G U S A B ∧ (#S : ℝ) ≤ 6 * √(#U : ℝ) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3 := by
  classical
  have hsub : ∀ (s s' : Finset V), s ⊆ s' → ∑ v ∈ s, w v ≤ ∑ v ∈ s', w v :=
    fun s s' h => sum_le_sum_of_subset_of_nonneg h fun v _ _ => hw v
  by_cases hheavy : ∃ v ∈ U, 2 / 3 < ∑ u ∈ comp G U v, w u
  · obtain ⟨v, hv, hvw⟩ := hheavy
    set C := comp G U v
    have hCU : C ⊆ U := comp_subset U v
    obtain ⟨S, A₀, B₀, hsep, hsize, hA₀, hB₀⟩ :=
      exists_separation_of_reaches (C := C) hR (reaches_comp hv) hw ((hsub _ _ hCU).trans h1)
    have hSC : S ⊆ C := fun x hx => hsep.union_eq ▸ mem_union_left _ (mem_union_left _ hx)
    have hAC : A₀ ⊆ C := fun x hx => hsep.union_eq ▸ mem_union_left _ (mem_union_right _ hx)
    have hBC : B₀ ⊆ C := fun x hx => hsep.union_eq ▸ mem_union_right _ hx
    set κ : V → ℕ := fun x => if x ∈ A₀ then 0 else if x ∈ B₀ then 1 else 2
    have hCS : ∀ x ∈ C, x ∉ S → x ∈ A₀ ∨ x ∈ B₀ := fun x hx hxS => by
      rw [← hsep.union_eq] at hx
      simp only [mem_union] at hx
      tauto
    have hadj : ∀ x ∈ U \ S, ∀ y ∈ U \ S, G.Adj x y → κ x = κ y := by
      intro x hx y hy hxy
      obtain ⟨hxU, hxS⟩ := mem_sdiff.1 hx
      obtain ⟨hyU, hyS⟩ := mem_sdiff.1 hy
      by_cases hxC : x ∈ C
      · have hyC : y ∈ C := mem_comp_of_adj hxC hyU hxy
        rcases hCS x hxC hxS with h | h <;> rcases hCS y hyC hyS with h' | h'
        · simp [κ, h, h']
        · exact absurd hxy (hsep.not_adj x h y h')
        · exact absurd hxy.symm (hsep.not_adj y h' x h)
        · have : x ∉ A₀ := Finset.disjoint_right.1 hsep.disjoint h
          have : y ∉ A₀ := Finset.disjoint_right.1 hsep.disjoint h'
          simp [κ, *]
      · have hyC : y ∉ C := fun hyC => hxC (mem_comp_of_adj hyC hxU hxy.symm)
        have h1 : x ∉ A₀ := fun h => hxC (hAC h)
        have h2 : x ∉ B₀ := fun h => hxC (hBC h)
        have h3 : y ∉ A₀ := fun h => hyC (hAC h)
        have h4 : y ∉ B₀ := fun h => hyC (hBC h)
        simp [κ, h1, h2, h3, h4]
    have hpiece : ∀ i, ∑ x ∈ U \ S with κ x = i, w x ≤ 2 / 3 := by
      intro i
      match i with
      | 0 =>
        refine (hsub _ A₀ fun x hx => ?_).trans hA₀
        have := (mem_filter.1 hx).2
        by_contra h
        simp only [κ, h, ite_false] at this
        split_ifs at this
      | 1 =>
        refine (hsub _ B₀ fun x hx => ?_).trans hB₀
        have := (mem_filter.1 hx).2
        by_contra h
        by_cases h' : x ∈ A₀
        · simp [κ, h'] at this
        · simp [κ, h, h'] at this
      | 2 =>
        refine (hsub _ (U \ C) fun x hx => ?_).trans ?_
        · obtain ⟨hx1, hx2⟩ := mem_filter.1 hx
          refine mem_sdiff.2 ⟨(mem_sdiff.1 hx1).1, fun hxC => ?_⟩
          rcases hCS x hxC (mem_sdiff.1 hx1).2 with h'' | h''
          · simp [κ, h''] at hx2
          · have : x ∉ A₀ := Finset.disjoint_right.1 hsep.disjoint h''
            simp [κ, h'', this] at hx2
        · have := sum_sdiff hCU (f := w)
          linarith
      | k + 3 =>
        have : (U \ S).filter (fun x => κ x = k + 3) = ∅ := by
          refine filter_false_of_mem fun x _ => ?_
          simp only [κ]
          split_ifs <;> simp
        rw [this, sum_empty]
        norm_num
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_separation_of_pieces (hSC.trans hCU) κ hw hadj hpiece
      ((hsub _ _ sdiff_subset).trans h1)
    refine ⟨S, A, B, hAB, hsize.trans ?_, hA, hB⟩
    have : (#C : ℝ) ≤ #U := by exact_mod_cast card_le_card hCU
    have := Real.sqrt_le_sqrt this
    linarith
  · push Not at hheavy
    have hadj : ∀ x ∈ U \ ∅, ∀ y ∈ U \ ∅, G.Adj x y → comp G U x = comp G U y :=
      fun x hx y hy hxy => comp_eq_of_adj (mem_sdiff.1 hx).1 (mem_sdiff.1 hy).1 hxy
    have hpiece : ∀ i, ∑ x ∈ U \ ∅ with comp G U x = i, w x ≤ 2 / 3 := by
      intro i
      by_cases hi : ∃ x ∈ U, comp G U x = i
      · obtain ⟨x, hx, rfl⟩ := hi
        refine (hsub _ (comp G U x) fun y hy => ?_).trans (hheavy x hx)
        obtain ⟨hy1, hy2⟩ := mem_filter.1 hy
        rw [← hy2]
        exact mem_comp_self (mem_sdiff.1 hy1).1
      · push Not at hi
        rw [filter_false_of_mem fun x hx => hi x (mem_sdiff.1 hx).1, sum_empty]
        norm_num
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_separation_of_pieces (empty_subset U) (comp G U) hw
      hadj hpiece (by rw [sdiff_empty]; exact h1)
    exact ⟨∅, A, B, hAB, by simp, hA, hB⟩

/-- **The planar separator theorem** (Lipton–Tarjan, weighted form). Let `R` be a plane rotation
system of a graph `G` with `n` vertices, and let `w` be nonnegative weights on the vertices with
total at most `1`. Then there is a set `S` of at most `6 √n` vertices whose removal leaves two
parts `A` and `B`, with no edge between them, each of weight at most `2/3`. -/
theorem planar_separator (hR : R.IsPlane) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (h1 : ∑ v, w v ≤ 1) :
    ∃ S A B, IsSeparation G univ S A B ∧ (#S : ℝ) ≤ 6 * √(Fintype.card V : ℝ) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3 := by
  simpa using planar_separator_induce hR univ hw h1

/-- **The planar separator theorem for induced subgraphs, unweighted form.** Every set `U` of
`m` vertices of a plane graph is separated by at most `6 √m` of its vertices into two parts of at
most `2m/3` vertices each. -/
theorem planar_separator_card (hR : R.IsPlane) (U : Finset V) :
    ∃ S A B, IsSeparation G U S A B ∧ (#S : ℝ) ≤ 6 * √(#U : ℝ) ∧
      3 * #A ≤ 2 * #U ∧ 3 * #B ≤ 2 * #U := by
  classical
  set w : V → ℝ := fun _ => 1 / (#U : ℝ)
  have hw : ∀ v, 0 ≤ w v := fun v => by positivity
  have hsum : ∀ s : Finset V, ∑ v ∈ s, w v = #s / (#U : ℝ) := fun s => by
    simp [w, div_eq_mul_inv]
  have h1 : ∑ v ∈ U, w v ≤ 1 := by
    rw [hsum]
    exact div_self_le_one _
  obtain ⟨S, A, B, hsep, hS, hA, hB⟩ := planar_separator_induce hR U hw h1
  refine ⟨S, A, B, hsep, hS, ?_, ?_⟩ <;>
  · rcases Nat.eq_zero_or_pos #U with h0 | h0
    · have hU : U = ∅ := card_eq_zero.1 h0
      have : A ⊆ U := fun x hx => hsep.union_eq ▸ mem_union_left _ (mem_union_right _ hx)
      have : B ⊆ U := fun x hx => hsep.union_eq ▸ mem_union_right _ hx
      simp_all
    · rw [hsum, div_le_iff₀ (by exact_mod_cast h0)] at hA hB
      have hA' : (3 * #A : ℝ) ≤ 2 * #U := by linarith
      have hB' : (3 * #B : ℝ) ≤ 2 * #U := by linarith
      first
        | exact_mod_cast hA'
        | exact_mod_cast hB'

/-! ### Separator oracles -/

variable (G) in
/-- `G` has `c √m`-separators: every set `U` of `m` vertices, with nonnegative weights of total
weight on `U` at most `1`, is separated in `G` by at most `c √m` of its vertices into two parts of
weight at most `2/3`. -/
def HasSqrtSeparators (c : ℝ) : Prop :=
  ∀ (U : Finset V) (w : V → ℝ), (∀ v, 0 ≤ w v) → ∑ v ∈ U, w v ≤ 1 →
    ∃ S A B, IsSeparation G U S A B ∧ (#S : ℝ) ≤ c * √(#U : ℝ) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3

/-- Plane graphs have `6 √m`-separators. -/
theorem hasSqrtSeparators_of_isPlane (hR : R.IsPlane) : HasSqrtSeparators G 6 :=
  fun U _ hw h1 => planar_separator_induce hR U hw h1

end PlanarSeparator
