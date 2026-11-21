/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Tree
public import Mathlib.Basic.Real.Basic

/-!
# Fundamental cycles and the cycle separator lemma

Let `T` be a spanning tree of a plane map `M`. Every dart `δ` determines a *fundamental cochain*
`fund δ`: the edge of `δ` together with the paths in `T` from the two ends of `δ` to the root.
It is closed, so by the combinatorial Jordan curve theorem
(`PlanarSeparator.Map.IsPlane.exists_face_cochain`) it splits the faces into two sides. We call
`inside δ` the side containing the face of `δ` (when `δ` is not a tree dart; for a tree dart the
fundamental cochain vanishes and `inside δ` is empty).

The set `sep δ` of the vertices of the two root paths has at most `2h + 1` vertices for a tree
of depth `h`. Every vertex `v` outside `sep δ` has all its faces on the same side, so the
vertices outside `sep δ` are split into `inV δ` (those inside) and `outV δ` (those outside), and
no edge joins `inV δ` to `outV δ` (`PlanarSeparator.Map.SpTree.vert_α_ne_of_mem_inV`).

The key tool for comparing different sides is the following consequence of the fact that a tree
carries no nonzero closed cochain (`PlanarSeparator.Map.SpTree.eq_zero`): a set of faces whose
boundary consists of tree edges is empty or contains all faces
(`PlanarSeparator.Map.SpTree.eq_empty_or_eq_univ`).

## The cycle separator lemma

When all faces are triangles, the argument of Lipton and Tarjan gives a dart `δ` for which both
`inV δ` and `outV δ` have weight at most `2/3`, for any nonnegative weights of total at most `1`
(`PlanarSeparator.Map.SpTree.exists_balanced`). Starting from a dart whose inside is too heavy,
let `δ, δ₁, δ₂` be the triangle of `δ`. The inside of `δ` consists of the face of `δ` and the
insides of the reversals of `δ₁` and `δ₂`, which are smaller; the vertices inside `δ` are inside
one of these, or lie on the path from the third corner `y` of the triangle to the root. Passing
to the heavier of the two, either its inside is still too heavy and we continue, or both of its
sides have weight at most `2/3`.

## References

* R. J. Lipton, R. E. Tarjan, *A separator theorem for planar graphs*, SIAM J. Appl. Math. 36
  (1979), 177–189, Lemma 2.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} {M : Map D P}

lemma ne_of_edge_ne {a b : D} (h : M.edge a ≠ M.edge b) :
    b ≠ a ∧ b ≠ M.α a ∧ M.α b ≠ a ∧ M.α b ≠ M.α a := by
  rw [Ne, edge_eq_edge_iff, not_or] at h
  refine ⟨h.1, h.2, fun h' => h.2 ?_, fun h' => h.1 (M.α_injective h')⟩
  rw [← h', M.α_α]

namespace SpTree

variable (T : SpTree M) [DecidableEq D] [DecidableEq P]

/-! ### The fundamental cochain -/

/-- The fundamental cochain of a dart: its edge together with the tree paths from its two ends
to the root. -/
def fund (δ : D) : D → ZMod 2 := M.edgeInd δ + T.pathC (M.vert δ) + T.pathC (M.vert (M.α δ))

lemma fund_apply (δ d : D) :
    T.fund δ d = M.edgeInd δ d + T.pathC (M.vert δ) d + T.pathC (M.vert (M.α δ)) d := rfl

lemma fund_α_apply (δ d : D) : T.fund δ (M.α d) = T.fund δ d := by
  simp only [fund_apply, edgeInd_α, pathC_α]

lemma fund_α (δ : D) : T.fund (M.α δ) = T.fund δ := by
  funext d
  simp only [fund_apply, edgeInd_of_α, M.α_α]
  ring

lemma fund_ne_zero {δ d : D} (h : T.fund δ d ≠ 0) : T.IsTree d ∨ d = δ ∨ d = M.α δ := by
  rw [fund_apply] at h
  by_cases h1 : M.edgeInd δ d = 0
  · left
    by_cases h2 : T.pathC (M.vert δ) d = 0
    · rw [h1, h2, zero_add, zero_add] at h
      exact T.isTree_of_pathC_ne_zero h
    · exact T.isTree_of_pathC_ne_zero h2
  · exact Or.inr (edgeInd_ne_zero h1)

/-- The two root paths of a dart. -/
def sep (δ : D) : Finset P := T.anc (M.vert δ) ∪ T.anc (M.vert (M.α δ))

omit [DecidableEq D] in
lemma sep_α (δ : D) : T.sep (M.α δ) = T.sep δ := by
  rw [sep, sep, M.α_α, union_comm]

omit [DecidableEq D] in
lemma vert_mem_sep (δ : D) : M.vert δ ∈ T.sep δ := mem_union_left _ (T.mem_anc_self _)

omit [DecidableEq D] in
lemma vert_α_mem_sep (δ : D) : M.vert (M.α δ) ∈ T.sep δ := mem_union_right _ (T.mem_anc_self _)

/-- The support of the fundamental cochain lies on the two root paths. -/
lemma vert_mem_sep_of_fund_ne_zero {δ d : D} (h : T.fund δ d ≠ 0) : M.vert d ∈ T.sep δ := by
  rw [fund_apply] at h
  by_cases h1 : M.edgeInd δ d = 0
  · by_cases h2 : T.pathC (M.vert δ) d = 0
    · rw [h1, h2, zero_add, zero_add] at h
      exact mem_union_right _ (T.vert_mem_anc_of_pathC_ne_zero h)
    · exact mem_union_left _ (T.vert_mem_anc_of_pathC_ne_zero h2)
  · rcases edgeInd_ne_zero h1 with rfl | rfl
    · exact T.vert_mem_sep d
    · exact T.vert_α_mem_sep _

lemma fund_of_isTree {δ : D} (h : T.IsTree δ) : T.fund δ = 0 := by
  have key : ∀ v (hv : v ≠ T.root), T.fund (T.par v hv) = 0 := by
    intro v hv
    funext d
    rw [fund_apply, T.vert_par, ← T.parent_of_ne hv, T.pathC_of_ne hv, Pi.add_apply,
      Pi.zero_apply]
    generalize M.edgeInd (T.par v hv) d = a
    generalize T.pathC (T.parent v) d = b
    revert a b
    decide
  obtain ⟨v, hv, rfl | rfl⟩ := h
  · exact key v hv
  · rw [fund_α, key v hv]

lemma fund_self {δ : D} (h : ¬ T.IsTree δ) : T.fund δ δ = 1 := by
  have h1 : ∀ v, T.pathC v δ = 0 := fun v => by
    by_contra h'
    exact h (T.isTree_of_pathC_ne_zero h')
  rw [fund_apply, edgeInd_self, h1, h1, add_zero, add_zero]

variable [Fintype D]

/-- The fundamental cochain is closed. -/
lemma sum_fund (δ : D) (v : P) : ∑ d with M.vert d = v, T.fund δ d = 0 := by
  simp only [fund_apply, sum_add_distrib, sum_edgeInd, sum_pathC]
  generalize (if M.vert δ = v then (1 : ZMod 2) else 0) = a
  generalize (if M.vert (M.α δ) = v then (1 : ZMod 2) else 0) = b
  generalize (if T.root = v then (1 : ZMod 2) else 0) = c
  revert a b c
  decide

variable [Fintype P]

/-! ### The sides of a fundamental cochain -/

/-- A function on the faces whose coboundary is the fundamental cochain of `δ` (for a plane
map). -/
noncomputable def side (δ : D) : M.Face → ZMod 2 :=
  if H : ∃ h : M.Face → ZMod 2, ∀ d, h (M.face d) + h (M.face (M.α d)) = T.fund δ d then
    H.choose else 0

variable {T}

lemma side_spec (hM : M.IsPlane) (δ d : D) :
    T.side δ (M.face d) + T.side δ (M.face (M.α d)) = T.fund δ d := by
  have H := hM.exists_face_cochain (T.fund δ) (T.fund_α_apply δ) (T.sum_fund δ)
  rw [side, dite_eq_left H]
  exact H.choose_spec d

variable (T)

/-- The faces on the side of the fundamental cochain of `δ` containing the face of `δ`. -/
noncomputable def inside (δ : D) : Finset M.Face :=
  {F | T.side δ F ≠ T.side δ (M.face (M.α δ))}

omit [Fintype P] in
lemma face_α_notMem_inside (δ : D) : M.face (M.α δ) ∉ T.inside δ := by
  simp [inside]

variable {T}

/-- An edge separates the inside of `δ` from its complement exactly when it lies on the
fundamental cochain of `δ`. -/
lemma inside_iff (hM : M.IsPlane) (δ d : D) :
    (M.face d ∈ T.inside δ ↔ M.face (M.α d) ∈ T.inside δ) ↔ T.fund δ d = 0 := by
  rw [← side_spec hM δ d]
  simp only [inside, mem_filter, mem_univ, true_and]
  generalize T.side δ (M.face d) = a
  generalize T.side δ (M.face (M.α d)) = b
  generalize T.side δ (M.face (M.α δ)) = c
  revert a b c
  decide

lemma iff_of_ne (hM : M.IsPlane) {δ d : D} (hd : ¬ T.IsTree d) (h1 : d ≠ δ) (h2 : d ≠ M.α δ) :
    M.face d ∈ T.inside δ ↔ M.face (M.α d) ∈ T.inside δ := by
  rw [inside_iff hM]
  by_contra h
  rcases T.fund_ne_zero h with h | h | h
  · exact hd h
  · exact h1 h
  · exact h2 h

lemma inside_eq_empty (hM : M.IsPlane) {δ : D} (h : T.IsTree δ) : T.inside δ = ∅ := by
  have h0 := T.fund_of_isTree h
  have hconst : ∀ F F', T.side δ F = T.side δ F' := hM.connected.face_const fun d => by
    have := side_spec (T := T) hM δ d
    rw [h0, Pi.zero_apply] at this
    exact (Kasteleyn.ZMod.two_eq_of_add_eq_zero this).symm
  ext F
  simp [inside, hconst F (M.face (M.α δ))]

lemma face_mem_inside (hM : M.IsPlane) {δ : D} (h : ¬ T.IsTree δ) : M.face δ ∈ T.inside δ := by
  have h1 := (inside_iff hM δ δ).not.2 (by rw [T.fund_self h]; exact one_ne_zero)
  have h2 := T.face_α_notMem_inside δ
  tauto

/-- The two sides of a dart which is not a tree dart are complementary. -/
lemma inside_α (hM : M.IsPlane) {δ : D} (h : ¬ T.IsTree δ) :
    T.inside (M.α δ) = (T.inside δ)ᶜ := by
  have hsum : ∀ F F', T.side (M.α δ) F + T.side δ F = T.side (M.α δ) F' + T.side δ F' :=
    hM.connected.face_const fun d => by
      have h1 := side_spec (T := T) hM (M.α δ) d
      have h2 := side_spec (T := T) hM δ d
      rw [T.fund_α] at h1
      rw [← h2] at h1
      generalize T.side (M.α δ) (M.face d) = a at h1 ⊢
      generalize T.side (M.α δ) (M.face (M.α d)) = b at h1 ⊢
      generalize T.side δ (M.face d) = c at h1 ⊢
      generalize T.side δ (M.face (M.α d)) = e at h1 ⊢
      revert a b c e
      decide
  have h1 := side_spec (T := T) hM δ δ
  rw [T.fund_self h] at h1
  ext F
  have hF := hsum F (M.face δ)
  simp only [inside, mem_filter, mem_univ, true_and, mem_compl, M.α_α]
  generalize T.side (M.α δ) F = a at hF ⊢
  generalize T.side δ F = b at hF ⊢
  generalize T.side (M.α δ) (M.face δ) = c at hF ⊢
  generalize T.side δ (M.face δ) = e at hF h1 ⊢
  generalize T.side δ (M.face (M.α δ)) = g at h1 ⊢
  revert a b c e g
  decide

omit [DecidableEq P] in
/-- **Sets of faces bounded by tree edges.** In a plane map, a set of faces such that every edge
with exactly one side in the set is a tree edge is empty or contains every face. -/
theorem eq_empty_or_eq_univ (hM : M.IsPlane) (Z : Finset M.Face)
    (hZ : ∀ d, ¬ T.IsTree d → (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z)) : Z = ∅ ∨ Z = univ := by
  classical
  set ι : M.Face → ZMod 2 := fun F => if F ∈ Z then 1 else 0
  set c : D → ZMod 2 := fun d => ι (M.face d) + ι (M.face (M.α d))
  have hcα : ∀ d, c (M.α d) = c d := fun d => by simp only [c, M.α_α]; ring
  have hc : ∀ v, ∑ d with M.vert d = v, c d = 0 := by
    intro v
    simp only [c, sum_add_distrib]
    rw [← sum_congr rfl fun d _ => congrArg ι (M.face_σ d), M.sum_vert_σ v (fun d => ι (M.face d)),
      Kasteleyn.ZMod.two_add_self]
  have hT : ∀ d, c d ≠ 0 → T.IsTree d := by
    intro d hd
    by_contra h
    exact hd (by simp only [c, ι, hZ d h]; exact Kasteleyn.ZMod.two_add_self _)
  have h0 := T.eq_zero c hcα hc hT
  have hconst : ∀ F F', ι F = ι F' := hM.connected.face_const fun d =>
    (Kasteleyn.ZMod.two_eq_of_add_eq_zero (h0 d)).symm
  by_cases hZe : Z = ∅
  · exact Or.inl hZe
  · right
    obtain ⟨F₀, hF₀⟩ := nonempty_iff_ne_empty.2 hZe
    rw [eq_univ_iff_forall]
    intro F
    have := hconst F F₀
    simp only [ι, hF₀, ite_true] at this
    by_contra hF
    simp [hF] at this

/-! ### Vertices on the two sides -/

variable (T)

/-- The vertices off the two root paths of `δ` lying on the inside of `δ`. -/
noncomputable def inV (δ : D) : Finset P :=
  {v | v ∉ T.sep δ ∧ ∃ d, M.vert d = v ∧ M.face d ∈ T.inside δ}

/-- The vertices off the two root paths of `δ` lying on the outside of `δ`. -/
noncomputable def outV (δ : D) : Finset P := {v | v ∉ T.sep δ ∧ v ∉ T.inV δ}

variable {T}

lemma notMem_sep_of_mem_inV {δ : D} {v : P} (h : v ∈ T.inV δ) : v ∉ T.sep δ :=
  (mem_filter.1 h).2.1

/-- Around a vertex off the two root paths all faces lie on the same side. -/
lemma face_iff_of_notMem_sep (hM : M.IsPlane) {δ : D} {v : P} (hv : v ∉ T.sep δ) {d d' : D}
    (hd : M.vert d = v) (hd' : M.vert d' = v) :
    M.face d ∈ T.inside δ ↔ M.face d' ∈ T.inside δ := by
  obtain ⟨n, rfl⟩ := M.exists_σ_pow_eq (hd.trans hd'.symm)
  clear hd'
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx : T.fund δ ((M.σ ^ n) d) = 0 := by
      by_contra h
      exact hv (by have := T.vert_mem_sep_of_fund_ne_zero h; rwa [M.vert_σ_pow, hd] at this)
    rw [pow_succ', Equiv.Perm.mul_apply, face_σ, ← (inside_iff hM δ _).2 hx]
    exact ih

lemma mem_inV_iff (hM : M.IsPlane) {δ d : D} {v : P} (hv : v ∉ T.sep δ) (hd : M.vert d = v) :
    v ∈ T.inV δ ↔ M.face d ∈ T.inside δ := by
  simp only [inV, mem_filter, mem_univ, true_and, hv, not_false_eq_true]
  constructor
  · rintro ⟨d', hd', h⟩
    exact (face_iff_of_notMem_sep hM hv hd' hd).1 h
  · exact fun h => ⟨d, hd, h⟩

/-- **Separation.** No edge joins a vertex inside `δ` to a vertex outside `δ`. -/
theorem vert_α_ne_of_mem_inV (hM : M.IsPlane) {δ : D} {u v : P} (hu : u ∈ T.inV δ)
    (hv : v ∈ T.outV δ) {d : D} (hd : M.vert d = u) : M.vert (M.α d) ≠ v := by
  intro hdv
  have hus := notMem_sep_of_mem_inV hu
  obtain ⟨hvs, hvi⟩ := (mem_filter.1 hv).2
  have h1 := (mem_inV_iff hM hus hd).1 hu
  have h2 : T.fund δ d = 0 := by
    by_contra h
    exact hus (hd ▸ T.vert_mem_sep_of_fund_ne_zero h)
  exact hvi ((mem_inV_iff hM hvs hdv).2 (((inside_iff hM δ d).2 h2).1 h1))

variable (T) in
lemma outV_eq (δ : D) : T.outV δ = (T.sep δ)ᶜ \ T.inV δ := by
  ext v
  simp [outV]

variable (T) in
lemma inV_subset (δ : D) : T.inV δ ⊆ (T.sep δ)ᶜ := fun _ h =>
  mem_compl.2 (notMem_sep_of_mem_inV h)

variable (T) in
/-- The weights of the two sides and of the root paths add up to the total weight. -/
lemma sum_inV_add_sum_outV (w : P → ℝ) (δ : D) :
    ∑ v ∈ T.inV δ, w v + ∑ v ∈ T.outV δ, w v + ∑ v ∈ T.sep δ, w v = ∑ v, w v := by
  rw [T.outV_eq, add_comm (∑ v ∈ T.inV δ, w v), sum_sdiff (T.inV_subset δ), add_comm,
    sum_add_sum_compl]

lemma inV_α (hM : M.IsPlane) {δ : D} (h : ¬ T.IsTree δ) : T.inV (M.α δ) = T.outV δ := by
  ext v
  by_cases hv : v ∈ T.sep δ
  · simp [inV, outV, T.sep_α, hv]
  · obtain ⟨d, hd⟩ := hM.exists_dart v
    have hv' : v ∉ T.sep (M.α δ) := by rwa [T.sep_α]
    rw [mem_inV_iff hM hv' hd, inside_α hM h, mem_compl]
    simp only [outV, mem_filter, mem_univ, true_and, hv, not_false_eq_true,
      mem_inV_iff hM hv hd]

/-! ### Triangles -/

section Triangle

variable (hM : M.IsPlane) {δ : D} (hδ : M.IsTriangle δ) (hnt : ¬ T.IsTree δ)
include hM hnt

/-- For a dart `δ'` of the face of `δ` with another edge, the inside of the reversal of `δ'` is
contained in the inside of `δ`, without the face of `δ`. -/
lemma inside_α_subset {δ' : D} (hface : M.face δ' = M.face δ) (hne : M.edge δ' ≠ M.edge δ) :
    T.inside (M.α δ') ⊆ (T.inside δ).erase (M.face δ) := by
  obtain ⟨n1, n2, n3, n4⟩ := ne_of_edge_ne hne
  have hf0X : M.face δ ∈ T.inside δ := face_mem_inside hM hnt
  have hf0Y : M.face δ ∉ T.inside (M.α δ') := by
    have := T.face_α_notMem_inside (M.α δ')
    rwa [M.α_α, hface] at this
  have hαY : M.face (M.α δ) ∉ T.inside (M.α δ') := fun h =>
    hf0Y ((iff_of_ne hM hnt n2 (by rw [M.α_α]; exact n1)).2 h)
  set Z := T.inside (M.α δ') \ T.inside δ
  have hZ : ∀ d, ¬ T.IsTree d → (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) := by
    intro d hd
    simp only [Z, mem_sdiff]
    by_cases h1 : d = δ ∨ d = M.α δ
    · rcases h1 with rfl | rfl
      · exact iff_of_false (fun h => h.2 hf0X) (fun h => hαY h.1)
      · rw [M.α_α]
        exact iff_of_false (fun h => hαY h.1) (fun h => h.2 hf0X)
    by_cases h2 : d = δ' ∨ d = M.α δ'
    · have hd' : ¬ T.IsTree δ' := by
        rcases h2 with rfl | rfl
        · exact hd
        · rwa [T.isTree_α] at hd
      have hαX : M.face (M.α δ') ∈ T.inside δ := by
        rw [← iff_of_ne hM hd' (Ne.symm n1) (Ne.symm n3), hface]
        exact hf0X
      have hδ'Y : M.face δ' ∉ T.inside (M.α δ') := by rw [hface]; exact hf0Y
      rcases h2 with rfl | rfl
      · exact iff_of_false (fun h => hδ'Y h.1) (fun h => h.2 hαX)
      · rw [M.α_α]
        exact iff_of_false (fun h => h.2 hαX) (fun h => hδ'Y h.1)
    · push Not at h1 h2
      rw [iff_of_ne hM hd h1.1 h1.2, iff_of_ne hM hd h2.2 (by rw [M.α_α]; exact h2.1)]
  rcases T.eq_empty_or_eq_univ hM Z hZ with hZ0 | hZ0
  · intro F hF
    rw [mem_erase]
    refine ⟨fun h => hf0Y (h ▸ hF), ?_⟩
    by_contra hFX
    have : F ∈ Z := mem_sdiff.2 ⟨hF, hFX⟩
    rw [hZ0] at this
    exact notMem_empty F this
  · exfalso
    have : M.face δ ∈ Z := by rw [hZ0]; exact mem_univ _
    exact (mem_sdiff.1 this).2 hf0X

include hδ

/-- The inside of `δ` is the face of `δ` together with the insides of the reversals of the two
other darts of its triangle. -/
lemma inside_subset :
    T.inside δ ⊆ insert (M.face δ) (T.inside (M.α (M.φ δ)) ∪ T.inside (M.α (M.φ (M.φ δ)))) := by
  have hf1 : M.face (M.φ δ) = M.face δ := M.face_φ δ
  have hf2 : M.face (M.φ (M.φ δ)) = M.face δ := (M.face_φ _).trans hf1
  have h3 := hδ.φ_three
  set δ₁ := M.φ δ
  set δ₂ := M.φ δ₁
  set Y₁ := T.inside (M.α δ₁)
  set Y₂ := T.inside (M.α δ₂)
  set X := T.inside δ
  set Z := X \ insert (M.face δ) (Y₁ ∪ Y₂)
  have hfaceZ : ∀ d, M.face d = M.face δ → M.face d ∉ Z := fun d hd => by
    simp [Z, hd]
  have h1Z : ¬ T.IsTree δ₁ → M.face (M.α δ₁) ∉ Z := fun h => by
    have := face_mem_inside (T := T) hM (δ := M.α δ₁) (by rwa [T.isTree_α])
    simp [Z, Y₁, this]
  have h2Z : ¬ T.IsTree δ₂ → M.face (M.α δ₂) ∉ Z := fun h => by
    have := face_mem_inside (T := T) hM (δ := M.α δ₂) (by rwa [T.isTree_α])
    simp [Z, Y₂, this]
  have h0Z : M.face (M.α δ) ∉ Z := by
    simp [Z, X, T.face_α_notMem_inside δ]
  have hmemZ : ∀ F, F ∈ Z ↔ F ∈ X ∧ F ≠ M.face δ ∧ F ∉ Y₁ ∧ F ∉ Y₂ := fun F => by
    simp only [Z, mem_sdiff, mem_insert, mem_union, not_or]
  have hZ : ∀ d, ¬ T.IsTree d → (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) := by
    intro d hd
    have hdα : ¬ T.IsTree (M.α d) := by rwa [T.isTree_α]
    by_cases h : d = δ ∨ d = δ₁ ∨ d = δ₂ ∨ d = M.α δ ∨ d = M.α δ₁ ∨ d = M.α δ₂
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact iff_of_false (hfaceZ _ rfl) h0Z
      · exact iff_of_false (hfaceZ _ hf1) (h1Z hd)
      · exact iff_of_false (hfaceZ _ hf2) (h2Z hd)
      · rw [M.α_α]
        exact iff_of_false h0Z (hfaceZ _ rfl)
      · rw [M.α_α] at hdα ⊢
        exact iff_of_false (h1Z hdα) (hfaceZ _ hf1)
      · rw [M.α_α] at hdα ⊢
        exact iff_of_false (h2Z hdα) (hfaceZ _ hf2)
    · push Not at h
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
      have hX := iff_of_ne hM hd e1 e4
      have hY1 := iff_of_ne (T := T) hM hd e5 (by simpa [M.α_α] using e2)
      have hY2 := iff_of_ne (T := T) hM hd e6 (by simpa [M.α_α] using e3)
      have hf : M.face d ≠ M.face δ := fun hfd => by
        rcases M.eq_of_face_eq_of_φ_three h3 hfd with h | h | h
        · exact e1 h
        · exact e2 h
        · exact e3 h
      have hfα : M.face (M.α d) ≠ M.face δ := fun hfd => by
        rcases M.eq_of_face_eq_of_φ_three h3 hfd with h | h | h
        · exact e4 ((M.α_α d).symm.trans (congrArg M.α h))
        · exact e5 ((M.α_α d).symm.trans (congrArg M.α h))
        · exact e6 ((M.α_α d).symm.trans (congrArg M.α h))
      rw [hmemZ, hmemZ, hX, hY1, hY2]
      simp only [ne_eq, hf, hfα, not_false_eq_true, true_and]
      rfl
  rcases T.eq_empty_or_eq_univ hM Z hZ with hZ0 | hZ0
  · intro F hF
    by_contra hF'
    have : F ∈ Z := mem_sdiff.2 ⟨hF, hF'⟩
    rw [hZ0] at this
    exact notMem_empty F this
  · exfalso
    exact hfaceZ δ rfl (by rw [hZ0]; exact mem_univ _)

/-- The vertices inside `δ` are inside one of the reversals of the two other darts of its
triangle, or lie on the root path of the third corner of the triangle. -/
lemma inV_subset_union :
    T.inV δ ⊆ T.inV (M.α (M.φ δ)) ∪ T.inV (M.α (M.φ (M.φ δ))) ∪ T.anc (M.vert (M.φ (M.φ δ))) := by
  intro v hv
  obtain ⟨hvs, d, hd, hdX⟩ := (mem_filter.1 hv).2
  by_cases hy : v ∈ T.anc (M.vert (M.φ (M.φ δ)))
  · exact mem_union_right _ hy
  apply mem_union_left
  have hx : v ∉ T.anc (M.vert δ) := fun h => hvs (mem_union_left _ h)
  have hz : v ∉ T.anc (M.vert (M.α δ)) := fun h => hvs (mem_union_right _ h)
  have hz' : M.vert (M.φ δ) = M.vert (M.α δ) := M.vert_φ δ
  have hy' : M.vert (M.α (M.φ δ)) = M.vert (M.φ (M.φ δ)) := (M.vert_φ _).symm
  have hx' : M.vert (M.α (M.φ (M.φ δ))) = M.vert δ := by rw [← M.vert_φ, hδ.φ_three]
  have hf : M.face d ≠ M.face δ := fun hfd => by
    rcases M.eq_of_face_eq_of_φ_three hδ.φ_three hfd with rfl | rfl | rfl
    · exact hx (hd ▸ T.mem_anc_self _)
    · exact hz (by rw [← hd, hz']; exact T.mem_anc_self _)
    · exact hy (hd ▸ T.mem_anc_self _)
  have := inside_subset hM hδ hnt hdX
  rw [mem_insert, mem_union] at this
  rcases this with h | h | h
  · exact absurd h hf
  · refine mem_union_left _ ((mem_inV_iff hM ?_ hd).2 h)
    simp only [sep, M.α_α, hy', hz', mem_union, not_or]
    exact ⟨hy, hz⟩
  · refine mem_union_right _ ((mem_inV_iff hM ?_ hd).2 h)
    simp only [sep, M.α_α, hx', mem_union, not_or]
    exact ⟨hx, hy⟩

end Triangle

omit [DecidableEq D] [DecidableEq P] [Fintype D] [Fintype P] in
/-- In a triangle with three distinct edges, not all edges are tree edges. -/
lemma not_isTree_of_isTriangle [Finite D] [Finite P] {δ : D} (hδ : M.IsTriangle δ) :
    ¬ T.IsTree δ ∨ ¬ T.IsTree (M.φ δ) ∨ ¬ T.IsTree (M.φ (M.φ δ)) := by
  classical
  let := Fintype.ofFinite D
  let := Classical.decEq D
  let := Classical.decEq P
  by_contra h
  push Not at h
  obtain ⟨h0, h1, h2⟩ := h
  obtain ⟨a1, a2, -, -⟩ := ne_of_edge_ne hδ.edge_ne₁
  obtain ⟨b1, b2, -, -⟩ := ne_of_edge_ne hδ.edge_ne₂
  set c : D → ZMod 2 := M.edgeInd δ + M.edgeInd (M.φ δ) + M.edgeInd (M.φ (M.φ δ))
  have hcα : ∀ d, c (M.α d) = c d := fun d => by simp only [c, Pi.add_apply, edgeInd_α]
  have hc : ∀ v, ∑ d with M.vert d = v, c d = 0 := by
    intro v
    simp only [c, Pi.add_apply, sum_add_distrib]
    rw [sum_edgeInd (M := M) δ v, sum_edgeInd (M := M) (M.φ δ) v,
      sum_edgeInd (M := M) (M.φ (M.φ δ)) v]
    rw [← M.vert_φ δ, ← M.vert_φ (M.φ δ), ← M.vert_φ (M.φ (M.φ δ)), hδ.φ_three]
    generalize (if M.vert δ = v then (1 : ZMod 2) else 0) = a
    generalize (if M.vert (M.φ δ) = v then (1 : ZMod 2) else 0) = b
    generalize (if M.vert (M.φ (M.φ δ)) = v then (1 : ZMod 2) else 0) = e
    revert a b e
    decide
  have hT : ∀ d, c d ≠ 0 → T.IsTree d := by
    intro d hd
    simp only [c, Pi.add_apply] at hd
    by_cases e1 : M.edgeInd δ d = 0
    · by_cases e2 : M.edgeInd (M.φ δ) d = 0
      · rw [e1, e2, zero_add, zero_add] at hd
        rcases edgeInd_ne_zero hd with rfl | rfl
        · exact h2
        · rwa [T.isTree_α]
      · rcases edgeInd_ne_zero e2 with rfl | rfl
        · exact h1
        · rwa [T.isTree_α]
    · rcases edgeInd_ne_zero e1 with rfl | rfl
      · exact h0
      · rwa [T.isTree_α]
  have := T.eq_zero c hcα hc hT δ
  simp only [c, Pi.add_apply, edgeInd_self, edgeInd_eq_zero a1 a2, edgeInd_eq_zero b1 b2,
    add_zero] at this
  exact one_ne_zero this

/-! ### The cycle separator lemma -/

omit [Fintype P] in
lemma sum_union_le {s t : Finset P} {w : P → ℝ} (hw : ∀ v, 0 ≤ w v) :
    ∑ v ∈ s ∪ t, w v ≤ ∑ v ∈ s, w v + ∑ v ∈ t, w v := by
  rw [← sum_union_inter]
  exact le_add_of_nonneg_right (sum_nonneg fun v _ => hw v)

/-- The recursive step: from a dart whose inside is too heavy one reaches a balanced dart. -/
theorem exists_balanced_of_lt (hM : M.IsPlane) (hT : ∀ δ, M.IsTriangle δ) {w : P → ℝ}
    (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) :
    ∀ n, ∀ δ, #(T.inside δ) = n → 2 / 3 < ∑ v ∈ T.inV δ, w v →
      ∃ δ', ∑ v ∈ T.inV δ', w v ≤ 2 / 3 ∧ ∑ v ∈ T.outV δ', w v ≤ 2 / 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro δ hn hI
  have hnt : ¬ T.IsTree δ := by
    intro h
    have : T.inV δ = ∅ := by
      ext v
      simp [inV, inside_eq_empty hM h]
    rw [this, sum_empty] at hI
    norm_num at hI
  have hδ := hT δ
  set a₁ := M.α (M.φ δ)
  set a₂ := M.α (M.φ (M.φ δ))
  set y := M.vert (M.φ (M.φ δ))
  set W : Finset P → ℝ := fun s => ∑ v ∈ s, w v with hW
  have hW0 : ∀ s, 0 ≤ W s := fun s => sum_nonneg fun v _ => hw v
  have hWmono : ∀ s t, s ⊆ t → W s ≤ W t := fun s t hst =>
    sum_le_sum_of_subset_of_nonneg hst fun v _ _ => hw v
  -- the vertices inside `δ` on the root path of `y`
  set B := T.inV δ ∩ T.anc y
  have hcover : T.inV δ ⊆ T.inV a₁ ∪ T.inV a₂ ∪ B := by
    intro v hv
    rcases mem_union.1 (inV_subset_union hM hδ hnt hv) with h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_inter.2 ⟨hv, h⟩)
  have hI' : W (T.inV δ) ≤ W (T.inV a₁) + W (T.inV a₂) + W B :=
    (hWmono _ _ hcover).trans ((sum_union_le hw).trans
      (add_le_add_left (sum_union_le hw) _))
  have hB₁ : B ⊆ T.sep a₁ := fun v hv => by
    have := (mem_inter.1 hv).2
    simp only [sep, a₁, mem_union]
    left
    rw [← M.vert_φ]
    exact this
  have hB₂ : B ⊆ T.sep a₂ := fun v hv => by
    have := (mem_inter.1 hv).2
    simp only [sep, a₂, M.α_α, mem_union]
    right
    exact this
  have hout₁ : W (T.outV a₁) ≤ 1 - W (T.inV a₁) - W B := by
    have := T.sum_inV_add_sum_outV w a₁
    have := hWmono _ _ hB₁
    simp only [W] at *
    linarith
  have hout₂ : W (T.outV a₂) ≤ 1 - W (T.inV a₂) - W B := by
    have := T.sum_inV_add_sum_outV w a₂
    have := hWmono _ _ hB₂
    simp only [W] at *
    linarith
  have hX := face_mem_inside (T := T) hM hnt
  have hlt₁ : #(T.inside a₁) < n := hn ▸ (card_le_card (inside_α_subset hM hnt
    (M.face_φ δ) hδ.edge_ne₁)).trans_lt (card_erase_lt_of_mem hX)
  have hlt₂ : #(T.inside a₂) < n := hn ▸ (card_le_card (inside_α_subset hM hnt
    ((M.face_φ _).trans (M.face_φ δ)) hδ.edge_ne₂)).trans_lt (card_erase_lt_of_mem hX)
  have hB0 := hW0 B
  rcases le_total (W (T.inV a₂)) (W (T.inV a₁)) with h | h
  · by_cases hh : 2 / 3 < W (T.inV a₁)
    · exact ih _ hlt₁ a₁ rfl hh
    · refine ⟨a₁, not_lt.1 hh, ?_⟩
      change W (T.outV a₁) ≤ 2 / 3
      change 2 / 3 < W (T.inV δ) at hI
      linarith
  · by_cases hh : 2 / 3 < W (T.inV a₂)
    · exact ih _ hlt₂ a₂ rfl hh
    · refine ⟨a₂, not_lt.1 hh, ?_⟩
      change W (T.outV a₂) ≤ 2 / 3
      change 2 / 3 < W (T.inV δ) at hI
      linarith

/-- **The cycle separator lemma** (Lipton–Tarjan). Let `T` be a spanning tree of a plane map all
of whose faces are triangles, and let `w` be nonnegative weights on the vertices with total at
most `1`. Then there is a dart `δ` such that the vertices off the two root paths of `δ` on either
side of its fundamental cycle have weight at most `2/3`. -/
theorem exists_balanced (hM : M.IsPlane) (hT : ∀ δ, M.IsTriangle δ) {w : P → ℝ}
    (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) (d₀ : D) :
    ∃ δ, ∑ v ∈ T.inV δ, w v ≤ 2 / 3 ∧ ∑ v ∈ T.outV δ, w v ≤ 2 / 3 := by
  obtain ⟨δ, hδ⟩ : ∃ δ, ¬ T.IsTree δ := by
    rcases T.not_isTree_of_isTriangle (hT d₀) with h | h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  by_cases hin : 2 / 3 < ∑ v ∈ T.inV δ, w v
  · exact T.exists_balanced_of_lt hM hT hw h1 _ δ rfl hin
  by_cases hout : ∑ v ∈ T.outV δ, w v ≤ 2 / 3
  · exact ⟨δ, not_lt.1 hin, hout⟩
  rw [not_le, ← inV_α hM hδ] at hout
  exact T.exists_balanced_of_lt hM hT hw h1 _ _ rfl hout

end SpTree

end Map

end PlanarSeparator
