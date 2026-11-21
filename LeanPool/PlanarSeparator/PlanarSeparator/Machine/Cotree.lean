/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Fundamental

/-!
# The dual tree of a spanning tree and the weights inside fundamental cycles

Let `T` be a spanning tree of a plane map `M` all of whose faces are triangles. This file proves
the facts that let the cycle separator lemma (`PlanarSeparator.Map.SpTree.exists_balanced`) be
*computed* in linear time, as in Lipton and Tarjan:

* **The recurrence of the insides.** For a dart `δ` off the tree, with triangle `δ, φ δ, φ² δ`,
  the inside of `δ` is the disjoint union of the face of `δ` and the insides of the reversals of
  `φ δ` and `φ² δ` (`inside_eq`, `disjoint_inside`). Hence the weights of the insides, for any
  weights `fw` on the faces, satisfy `I δ = fw (face δ) + I (α φ δ) + I (α φ² δ)`
  (`sum_inside_eq`), and the inside of `α δ` is the complement (`sum_inside_α`).
* **The dual tree.** A search of the faces through the darts off the tree (`IsSearch`: every
  face other than the root face `F₀` has a dart `pd F` off the tree leading to a face found
  earlier) uses every dart off the tree in one of its two directions (`IsSearch.pd_or`), so the
  values `J F = I (pd F)` are obtained by one pass over the faces in the reverse order of the
  search (`IsSearch.eq_of_rec`). A set of faces containing a face and closed under crossing
  darts off the tree contains every face (`eq_univ_of_closed`), so the search reaches every face.
* **Vertex weights as face weights.** Every vertex `v` gives its weight to the face of a chosen
  dart `first v` at `v` (`fwt`). The vertices inside `δ` weigh at most the faces inside `δ`
  (`sum_inV_le`), and the vertices outside `δ` that are not corners of a face `F` outside `δ`
  weigh at most the faces outside `δ` other than `F` (`sum_outV_le`).
* **The walk.** From a dart whose inside is heavier than `2/3`, the heavier of the two darts
  `α φ δ`, `α φ² δ` either is still heavier than `2/3`, or gives a balanced separation once the
  three corners of the face of `δ` are added to its root paths (`walk_stop`).

## References

* R. J. Lipton, R. E. Tarjan, *A separator theorem for planar graphs*, SIAM J. Appl. Math. 36
  (1979), 177–189, Lemma 2 and Section 4.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

namespace Map

namespace SpTree

variable {D P : Type*} {M : Map D P} (T : SpTree M) [DecidableEq D] [DecidableEq P] [Fintype D]
  [Fintype P]

/-! ### The recurrence of the insides -/

section Rec

variable {T} (hM : M.IsPlane) {δ : D} (hδ : M.IsTriangle δ) (hnt : ¬ T.IsTree δ)
include hM hδ hnt

/-- The insides of the reversals of the two other darts of the triangle of `δ` are disjoint. -/
lemma disjoint_inside :
    Disjoint (T.inside (M.α (M.φ δ))) (T.inside (M.α (M.φ (M.φ δ)))) := by
  set a₁ := M.α (M.φ δ)
  set a₂ := M.α (M.φ (M.φ δ))
  by_cases h₁ : T.IsTree a₁
  · rw [inside_eq_empty hM h₁]; exact disjoint_empty_left _
  by_cases h₂ : T.IsTree a₂
  · rw [inside_eq_empty hM h₂]; exact disjoint_empty_right _
  have hs₁ := inside_α_subset hM hnt (δ' := M.φ δ) (M.face_φ δ) hδ.edge_ne₁
  have hs₂ := inside_α_subset hM hnt (δ' := M.φ (M.φ δ)) ((M.face_φ _).trans (M.face_φ δ))
    hδ.edge_ne₂
  have hf₁ : M.face δ ∉ T.inside a₁ := fun h => by simpa using hs₁ h
  have hf₂ : M.face δ ∉ T.inside a₂ := fun h => by simpa using hs₂ h
  have hα₁ : M.face (M.α a₁) = M.face δ := by rw [M.α_α, M.face_φ]
  have hα₂ : M.face (M.α a₂) = M.face δ := by rw [M.α_α, M.face_φ, M.face_φ]
  -- the edges of `a₁` and `a₂` are distinct
  have hne := ne_of_edge_ne hδ.edge_ne₃
  have e1 : a₁ ≠ a₂ := fun h => hne.1 (M.α_injective h)
  have e2 : a₁ ≠ M.α a₂ := fun h => hne.2.1 (by
    have := congrArg M.α h; rwa [M.α_α, M.α_α] at this)
  -- the face of `a₁` is not inside `a₂`, and conversely
  have g₁ : M.face a₁ ∉ T.inside a₂ := by
    rw [iff_of_ne hM h₁ e1 e2, hα₁]; exact hf₂
  have g₂ : M.face a₂ ∉ T.inside a₁ := by
    rw [iff_of_ne hM h₂ (Ne.symm e1) (fun h => e2 (by rw [h, M.α_α])), hα₂]; exact hf₁
  set Z := T.inside a₁ ∩ T.inside a₂
  have hZ : ∀ d, ¬ T.IsTree d → (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) := by
    intro d hd
    simp only [Z, mem_inter]
    by_cases k₁ : d = a₁ ∨ d = M.α a₁
    · rcases k₁ with rfl | rfl
      · rw [hα₁]; exact iff_of_false (fun h => g₁ h.2) (fun h => hf₁ h.1)
      · refine iff_of_false (fun h => hf₁ (hα₁ ▸ h.1)) (fun h => g₁ ?_)
        have := h.2; rwa [M.α_α] at this
    by_cases k₂ : d = a₂ ∨ d = M.α a₂
    · rcases k₂ with rfl | rfl
      · rw [hα₂]; exact iff_of_false (fun h => g₂ h.1) (fun h => hf₂ h.2)
      · refine iff_of_false (fun h => hf₂ (hα₂ ▸ h.2)) (fun h => g₂ ?_)
        have := h.1; rwa [M.α_α] at this
    push Not at k₁ k₂
    rw [iff_of_ne hM hd k₁.1 k₁.2, iff_of_ne hM hd k₂.1 k₂.2]
  rcases T.eq_empty_or_eq_univ hM Z hZ with hZ0 | hZ0
  · exact disjoint_iff_inter_eq_empty.2 hZ0
  · exfalso
    have : M.face δ ∈ Z := by rw [hZ0]; exact mem_univ _
    exact hf₁ (mem_inter.1 this).1

/-- **The recurrence of the insides.** The inside of a dart off the tree is its face together
with the insides of the reversals of the two other darts of its triangle. -/
lemma inside_eq :
    T.inside δ = insert (M.face δ) (T.inside (M.α (M.φ δ)) ∪ T.inside (M.α (M.φ (M.φ δ)))) := by
  refine (inside_subset hM hδ hnt).antisymm ?_
  have hs₁ := inside_α_subset hM hnt (δ' := M.φ δ) (M.face_φ δ) hδ.edge_ne₁
  have hs₂ := inside_α_subset hM hnt (δ' := M.φ (M.φ δ)) ((M.face_φ _).trans (M.face_φ δ))
    hδ.edge_ne₂
  refine insert_subset (face_mem_inside hM hnt) (union_subset ?_ ?_)
  · exact fun F hF => mem_of_mem_erase (hs₁ hF)
  · exact fun F hF => mem_of_mem_erase (hs₂ hF)

/-- The face of `δ` lies inside neither of the reversals of the other two darts. -/
lemma face_notMem_inside_union :
    M.face δ ∉ T.inside (M.α (M.φ δ)) ∪ T.inside (M.α (M.φ (M.φ δ))) := by
  have hs₁ := inside_α_subset hM hnt (δ' := M.φ δ) (M.face_φ δ) hδ.edge_ne₁
  have hs₂ := inside_α_subset hM hnt (δ' := M.φ (M.φ δ)) ((M.face_φ _).trans (M.face_φ δ))
    hδ.edge_ne₂
  rw [mem_union, not_or]
  exact ⟨fun h => by simpa using hs₁ h, fun h => by simpa using hs₂ h⟩

/-- **The recurrence of the inside weights.** -/
lemma sum_inside_eq {β : Type*} [AddCommMonoid β] (fw : M.Face → β) :
    ∑ F ∈ T.inside δ, fw F = fw (M.face δ) + ∑ F ∈ T.inside (M.α (M.φ δ)), fw F +
      ∑ F ∈ T.inside (M.α (M.φ (M.φ δ))), fw F := by
  rw [inside_eq hM hδ hnt, sum_insert (face_notMem_inside_union hM hδ hnt),
    sum_union (disjoint_inside hM hδ hnt), add_assoc]

/-- The insides of the two other darts are smaller. -/
lemma card_inside_lt₁ : #(T.inside (M.α (M.φ δ))) < #(T.inside δ) := by
  rw [inside_eq hM hδ hnt, card_insert_of_notMem (face_notMem_inside_union hM hδ hnt)]
  exact Nat.lt_succ_of_le (card_le_card subset_union_left)

lemma card_inside_lt₂ : #(T.inside (M.α (M.φ (M.φ δ)))) < #(T.inside δ) := by
  rw [inside_eq hM hδ hnt, card_insert_of_notMem (face_notMem_inside_union hM hδ hnt)]
  exact Nat.lt_succ_of_le (card_le_card subset_union_right)

end Rec

/-- The two sides of a dart off the tree partition the faces. -/
lemma sum_inside_α {β : Type*} [AddCommMonoid β] (hM : M.IsPlane) {δ : D}
    (hnt : ¬ T.IsTree δ) (fw : M.Face → β) :
    ∑ F ∈ T.inside (M.α δ), fw F + ∑ F ∈ T.inside δ, fw F = ∑ F, fw F := by
  rw [inside_α hM hnt, sum_compl_add_sum]

/-- The inside of a tree dart is empty. -/
lemma sum_inside_of_isTree {β : Type*} [AddCommMonoid β] (hM : M.IsPlane) {δ : D}
    (h : T.IsTree δ) (fw : M.Face → β) : ∑ F ∈ T.inside δ, fw F = 0 := by
  rw [inside_eq_empty hM h, sum_empty]

/-- A dart with a nonempty inside is off the tree. -/
lemma not_isTree_of_sum_pos (hM : M.IsPlane) {δ : D} (fw : M.Face → ℕ)
    (h : 0 < ∑ F ∈ T.inside δ, fw F) : ¬ T.IsTree δ := fun ht => by
  rw [sum_inside_of_isTree T hM ht] at h; exact lt_irrefl 0 h

/-! ### The dual tree -/

omit [DecidableEq P] in
/-- A set of faces containing a face and closed under crossing darts off the tree contains
every face. -/
theorem eq_univ_of_closed (hM : M.IsPlane) (Z : Finset M.Face) (hne : Z.Nonempty)
    (hZ : ∀ d, ¬ T.IsTree d → M.face d ∈ Z → M.face (M.α d) ∈ Z) : Z = univ := by
  rcases T.eq_empty_or_eq_univ hM Z (fun d hd => ⟨hZ d hd, fun h => by
    have := hZ (M.α d) (by rwa [T.isTree_α]) h
    rwa [M.α_α] at this⟩) with h | h
  · exact absurd h (nonempty_iff_ne_empty.1 hne)
  · exact h

/-- A search of the faces through the darts off the tree, from the root face `F₀`: every other
face `F` has a dart `pd F` off the tree on `F` whose reverse lies on a face found earlier. -/
structure IsSearch (F₀ : M.Face) (ord : M.Face → ℕ) (pd : M.Face → D) : Prop where
  face_pd : ∀ F, F ≠ F₀ → M.face (pd F) = F
  not_isTree : ∀ F, F ≠ F₀ → ¬ T.IsTree (pd F)
  ord_lt : ∀ F, F ≠ F₀ → ord (M.face (M.α (pd F))) < ord F

namespace IsSearch

variable {T} {F₀ : M.Face} {ord : M.Face → ℕ} {pd : M.Face → D} (hS : T.IsSearch F₀ ord pd)
include hS

omit [DecidableEq P] in
/-- **Every dart off the tree is a dart of the search**, in one of its two directions. -/
theorem pd_or (hM : M.IsPlane) {y : D} (hy : ¬ T.IsTree y) :
    (M.face y ≠ F₀ ∧ pd (M.face y) = y) ∨ (M.face (M.α y) ≠ F₀ ∧ pd (M.face (M.α y)) = M.α y) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hav : ∀ A, A ≠ F₀ → pd A ≠ y ∧ pd A ≠ M.α y := by
    intro A hA
    constructor
    · intro e
      have hA' : M.face y = A := e ▸ hS.face_pd A hA
      subst hA'
      exact h1 hA e
    · intro e
      have hA' : M.face (M.α y) = A := e ▸ hS.face_pd A hA
      subst hA'
      exact h2 hA e
  have key : ∀ F, F ∈ T.inside y ↔ F₀ ∈ T.inside y := by
    intro F
    induction hn : ord F using Nat.strong_induction_on generalizing F with
    | _ n ih =>
      by_cases hF : F = F₀
      · rw [hF]
      · obtain ⟨n1, n2⟩ := hav F hF
        have hfp := hS.face_pd F hF
        have := iff_of_ne hM (hS.not_isTree F hF) (δ := y) n1 n2
        rw [hfp] at this
        rw [this]
        exact ih _ (hn ▸ hS.ord_lt F hF) _ rfl
  have hin := face_mem_inside (T := T) hM hy
  have hout := T.face_α_notMem_inside y
  exact hout ((key _).2 ((key _).1 hin))

/-- **The pass over the dual tree.** If `J F = fw F + J' (φ (pd F)) + J' (φ² (pd F))` for every
face `F ≠ F₀`, where `J' x` is `0` for a tree dart and `J (face (α x))` otherwise, then
`J F` is the weight of the inside of `pd F`. -/
theorem eq_of_rec (hM : M.IsPlane) (hT : ∀ δ, M.IsTriangle δ) {β : Type*} [AddCommMonoid β]
    (fw : M.Face → β) (J : M.Face → β) [DecidablePred T.IsTree]
    (hJ : ∀ F, F ≠ F₀ → J F = fw F +
      (if T.IsTree (M.φ (pd F)) then 0 else J (M.face (M.α (M.φ (pd F))))) +
      (if T.IsTree (M.φ (M.φ (pd F))) then 0 else J (M.face (M.α (M.φ (M.φ (pd F))))))) :
    ∀ F, F ≠ F₀ → J F = ∑ G ∈ T.inside (pd F), fw G := by
  intro F
  induction hn : #(T.inside (pd F)) using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    intro hF
    have hnt := hS.not_isTree F hF
    have hδ := hT (pd F)
    have hfp := hS.face_pd F hF
    have child : ∀ x, M.face x = F → x ≠ pd F → ¬ T.IsTree x →
        #(T.inside (M.α x)) < n → J (M.face (M.α x)) = ∑ G ∈ T.inside (M.α x), fw G := by
      intro x hx hxne hxt hlt
      rcases hS.pd_or hM hxt with ⟨-, e⟩ | ⟨h', e⟩
      · exact absurd (hx ▸ e).symm hxne
      · rw [ih _ hlt _ (by rw [e]) h', e]
    rw [hJ F hF, sum_inside_eq hM hδ hnt]
    have hne := ne_of_edge_ne hδ.edge_ne₁
    have hne' := ne_of_edge_ne hδ.edge_ne₂
    congr 1
    · congr 1
      · rw [hfp]
      · split_ifs with h
        · rw [sum_inside_of_isTree T hM (by rwa [T.isTree_α])]
        · exact child _ (by rw [M.face_φ, hfp]) (Ne.symm hne.1) h (hn ▸ card_inside_lt₁ hM hδ hnt)
    · split_ifs with h
      · rw [sum_inside_of_isTree T hM (by rwa [T.isTree_α])]
      · exact child _ (by rw [M.face_φ, M.face_φ, hfp]) (Ne.symm hne'.1) h
          (hn ▸ card_inside_lt₂ hM hδ hnt)

end IsSearch

/-! ### Vertex weights as face weights -/

section Weights

variable (first : P → D) (w : P → ℕ)

variable (M) in
/-- The weight given to a face: the weights of the vertices `v` whose dart `first v` lies on
it. -/
def fwt (F : M.Face) : ℕ := ∑ v with M.face (first v) = F, w v

omit [DecidableEq P] in
lemma sum_fwt (Y : Finset M.Face) :
    ∑ F ∈ Y, fwt M first w F = ∑ v with M.face (first v) ∈ Y, w v := by
  symm
  rw [← sum_fiberwise_of_maps_to (g := fun v => M.face (first v)) (t := Y)
    (fun v hv => (mem_filter.1 hv).2)]
  refine sum_congr rfl fun F hF => ?_
  unfold fwt
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · rintro rfl; exact ⟨hF, rfl⟩

omit [DecidableEq P] in
lemma sum_fwt_univ : ∑ F, fwt M first w F = ∑ v, w v := by
  rw [sum_fwt]; simp

variable {T first}
variable (hM : M.IsPlane) (hfirst : ∀ v, M.vert (first v) = v)
include hM hfirst

/-- The vertices inside `δ` weigh at most the faces inside `δ`. -/
lemma sum_inV_le (δ : D) : ∑ v ∈ T.inV δ, w v ≤ ∑ F ∈ T.inside δ, fwt M first w F := by
  rw [sum_fwt]
  refine sum_le_sum_of_subset fun v hv => mem_filter.2 ⟨mem_univ _, ?_⟩
  exact (mem_inV_iff hM (notMem_sep_of_mem_inV hv) (hfirst v)).1 hv

/-- The vertices outside `δ` which are not corners of the triangle of `δ'`, whose face lies
outside `δ`, weigh at most the faces outside `δ` other than that face. -/
lemma sum_outV_le (δ : D) {δ' : D} (h3 : M.φ (M.φ (M.φ δ')) = δ')
    (hout : M.face δ' ∉ T.inside δ) :
    ∑ v ∈ T.outV δ with v ≠ M.vert δ' ∧ v ≠ M.vert (M.φ δ') ∧ v ≠ M.vert (M.φ (M.φ δ')),
      w v + ∑ F ∈ T.inside δ, fwt M first w F + fwt M first w (M.face δ') ≤ ∑ v, w v := by
  rw [← sum_fwt_univ first w]
  rw [← sum_compl_add_sum (T.inside δ), ← add_sum_erase _ _ (mem_compl.2 hout)]
  have : ∑ v ∈ T.outV δ with v ≠ M.vert δ' ∧ v ≠ M.vert (M.φ δ') ∧
      v ≠ M.vert (M.φ (M.φ δ')), w v ≤ ∑ F ∈ (T.inside δ)ᶜ.erase (M.face δ'), fwt M first w F := by
    rw [sum_fwt]
    refine sum_le_sum_of_subset fun v hv => ?_
    obtain ⟨hvo, hv1, hv2, hv3⟩ := mem_filter.1 hv
    obtain ⟨hvs, hvi⟩ := (mem_filter.1 hvo).2
    refine mem_filter.2 ⟨mem_univ _, mem_erase.2 ⟨fun e => ?_, mem_compl.2 fun h => hvi
      ((mem_inV_iff hM hvs (hfirst v)).2 h)⟩⟩
    rcases M.eq_of_face_eq_of_φ_three h3 e with e' | e' | e' <;>
    · have := congrArg M.vert e'; rw [hfirst] at this; tauto
  omega

end Weights

/-! ### The walk -/

/-- **The stopping step of the walk.** Let `δ` be a dart whose inside weighs more than `2/3`
of the total `tot`, and let `a` be the heavier of `α φ δ` and `α φ² δ`, its inside weighing at
most `2/3`. Then the inside of `a` weighs at most `2/3`, and the faces outside `a` other than
the face of `δ` weigh at most `2/3`. (In natural numbers: `3 I ≤ 2 tot`.) -/
lemma walk_stop {tot Iδ f I₁ I₂ Ia : ℕ} (hrec : Iδ = f + I₁ + I₂) (hheavy : 2 * tot < 3 * Iδ)
    (ha : Ia = I₁ ∧ I₂ ≤ I₁ ∨ Ia = I₂ ∧ I₁ ≤ I₂) (hlight : 3 * Ia ≤ 2 * tot) :
    3 * (tot - Ia - f) ≤ 2 * tot := by
  omega

end SpTree

end Map

end PlanarSeparator
