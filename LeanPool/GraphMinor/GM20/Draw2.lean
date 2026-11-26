/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Draw1
public import LeanPool.GraphMinor.GM11.Forest
public import LeanPool.GraphMinor.GM11.Fan

/-!
# Drawing a graph in a surface of large genus: slabs

We draw `n` disjoint curves that run from left to right across a vertical strip of the model. A
`Slab` from `x₁` to `x₂` with permutation `s` is such a family: the curve from height `p` at `x₁`
ends at
height `s p` at `x₂`. Two slabs compose (`Slab.comp`). So it is enough to have a slab for each swap
of two
neighbouring heights, and that is done in the next file with one handle or one cross-cap.
-/

@[expose] public section

namespace GraphMinor.GM20.Draw

open Set Topology GraphMinor.Surface unitInterval

variable {a b c : ℕ}

/-- The part of the model between the vertical lines at `x₁` and `x₂`. -/
noncomputable def Zone (a b c : ℕ) (x₁ x₂ : ℝ) : Set (SurfaceModel a b c) :=
  qq a b c '' {z | Ok a b c z ∧ x₁ ≤ z.1 ∧ z.1 ≤ x₂}

/-- A family of `n` disjoint lines across the strip from `x₁` to `x₂`, from `(x₁, p)` to `(x₂, s
p)`,
which touch the two sides only at their ends. -/
def Slab (a b c n : ℕ) (x₁ x₂ : ℝ) (s : Equiv.Perm (Fin n)) : Prop :=
  ∃ P : Fin n → Set (SurfaceModel a b c),
    (∀ p, IsLineWithEnds (P p) (qq a b c (x₁, p)) (qq a b c (x₂, s p))) ∧
    (Pairwise fun p p' ↦ Disjoint (P p) (P p')) ∧
    (∀ p, P p ⊆ Zone a b c x₁ x₂) ∧
    (∀ p z, Ok a b c z → z.1 ≤ x₁ → qq a b c z ∈ P p → qq a b c z = qq a b c (x₁, p)) ∧
    (∀ p z, Ok a b c z → x₂ ≤ z.1 → qq a b c z ∈ P p → qq a b c z = qq a b c (x₂, s p))

theorem mem_of_line {S : Type*} [TopologicalSpace S] {L : Set S} {u v : S}
    (h : IsLineWithEnds L u v) : u ∈ L ∧ v ∈ L := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨(f 0).2, (f 1).2⟩

/-- Two slabs side by side form a slab. -/
theorem Slab.comp [T2Space (SurfaceModel a b c)] {n : ℕ} {x₁ x₂ x₃ : ℝ}
    {s t : Equiv.Perm (Fin n)} (h₁ : Slab a b c n x₁ x₂ s) (h₂ : Slab a b c n x₂ x₃ t)
    (h₁₂ : x₁ ≤ x₂) (h₂₃ : x₂ ≤ x₃) : Slab a b c n x₁ x₃ (t * s) := by
  obtain ⟨P, hP, hPd, hPz, hPl, hPr⟩ := h₁
  obtain ⟨Q, hQ, hQd, hQz, hQl, hQr⟩ := h₂
  have hPQ : ∀ {p p' w}, w ∈ P p → w ∈ Q p' → w = qq a b c (x₂, s p) ∧ w = qq a b c (x₂, p') := by
    intro p p' w hw hw'
    obtain ⟨z, ⟨hz₁, hz₂, hz₃⟩, rfl⟩ := hPz p hw
    obtain ⟨z', ⟨hz₁', hz₂', hz₃'⟩, heq⟩ := hQz p' hw'
    exact ⟨heq ▸ hPr p z' hz₁' hz₂' (heq ▸ hw), hQl p' z hz₁ hz₃ hw'⟩
  refine ⟨fun p ↦ P p ∪ Q (s p), fun p ↦ ?_, ?_, fun p ↦ ?_, fun p z hz hzl hmem ↦ ?_,
    fun p z hz hzr hmem ↦ ?_⟩
  · refine GM11.IsLineWithEnds.union (GM11.IsLineWithEnds.symm (hP p)) (hQ (s p)) ?_
    ext w
    constructor
    · rintro ⟨h₃, h₄⟩
      exact (hPQ h₃ h₄).1
    · rintro rfl
      exact ⟨(mem_of_line (hP p)).2, (mem_of_line (hQ (s p))).1⟩
  · intro p p' hne
    have hne' : s p ≠ s p' := fun h ↦ hne (s.injective h)
    rw [Set.disjoint_left]
    rintro w (h₃ | h₃) (h₄ | h₄)
    · exact Set.disjoint_left.mp (hPd hne) h₃ h₄
    · have h₅ := (hPQ h₃ h₄)
      refine Set.disjoint_left.mp (hQd hne') (mem_of_line (hQ (s p))).1 ?_
      rw [← h₅.1, h₅.2]
      exact (mem_of_line (hQ (s p'))).1
    · have h₅ := (hPQ h₄ h₃)
      refine Set.disjoint_left.mp (hQd hne') (mem_of_line (hQ (s p))).1 ?_
      rw [← h₅.2, h₅.1]
      exact (mem_of_line (hQ (s p'))).1
    · exact Set.disjoint_left.mp (hQd hne') h₃ h₄
  · rintro w (h₃ | h₃)
    · obtain ⟨z, ⟨h₄, h₅, h₆⟩, rfl⟩ := hPz p h₃
      exact ⟨z, ⟨h₄, h₅, h₆.trans h₂₃⟩, rfl⟩
    · obtain ⟨z, ⟨h₄, h₅, h₆⟩, rfl⟩ := hQz _ h₃
      exact ⟨z, ⟨h₄, h₁₂.trans h₅, h₆⟩, rfl⟩
  · rcases hmem with h₃ | h₃
    · exact hPl p z hz hzl h₃
    · have h₄ := hQl (s p) z hz (hzl.trans h₁₂) h₃
      exact hPl p z hz hzl (h₄ ▸ (mem_of_line (hP p)).2)
  · rcases hmem with h₃ | h₃
    · have h₄ := hPr p z hz (h₂₃.trans hzr) h₃
      exact hQr (s p) z hz hzr (h₄ ▸ (mem_of_line (hQ (s p))).1)
    · exact hQr (s p) z hz hzr h₃

/-! ### Curves in the plane -/

/-- The graph of `f` over `[l, r]` in the plane. -/
def gr (f : ℝ → ℝ) (l r : ℝ) : Set (ℝ × ℝ) := (fun x ↦ (x, f x)) '' Icc l r

/-- The graph of a continuous function is a line in the model, if the graph is outside the open
discs
and at most one point `e` is on a circle. -/
theorem isLine_gr [T2Space (SurfaceModel a b c)] {f : ℝ → ℝ} {l r e : ℝ} (hlr : l < r)
    (hf : ContinuousOn f (Icc l r)) (hok : ∀ x ∈ Icc l r, Ok a b c (x, f x))
    (hc : ∀ x ∈ Icc l r, x ≠ e → Clear a b c (x, f x)) :
    IsLineWithEnds (qq a b c '' gr f l r) (qq a b c (l, f l)) (qq a b c (r, f r)) := by
  have hmem : ∀ t : I, l + t.1 * (r - l) ∈ Icc l r := fun t ↦ by
    have h₁ := t.2.1
    have h₂ := t.2.2
    constructor <;> nlinarith
  let g : I → SurfaceModel a b c := fun t ↦ qq a b c (l + t.1 * (r - l), f (l + t.1 * (r - l)))
  have hline : Continuous fun t : I ↦ l + t.1 * (r - l) := by fun_prop
  have hg : Continuous g := by
    have h₁ : Continuous fun t : I ↦ ((l + t.1 * (r - l), f (l + t.1 * (r - l))) : ℝ × ℝ) := by
      refine hline.prodMk ?_
      exact hf.comp_continuous hline hmem
    exact continuousOn_qq.comp_continuous h₁ fun t ↦ hok _ (hmem t)
  have hinj : Function.Injective g := by
    intro s t hst
    have hpar : ∀ {s t : I}, l + s.1 * (r - l) = l + t.1 * (r - l) → s = t := by
      intro s t h
      apply Subtype.ext
      have h₁ : r - l ≠ 0 := by linarith
      exact mul_right_cancel₀ h₁ (by linarith)
    by_cases h₁ : l + s.1 * (r - l) = e
    · by_cases h₂ : l + t.1 * (r - l) = e
      · exact hpar (h₁.trans h₂.symm)
      · have := eq_of_qq_eq (hc _ (hmem t) h₂) (hok _ (hmem s)) hst.symm
        exact hpar (congrArg Prod.fst this).symm
    · have := eq_of_qq_eq (hc _ (hmem s) h₁) (hok _ (hmem t)) hst
      exact hpar (congrArg Prod.fst this)
  have hrange : range g = qq a b c '' gr f l r := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, ⟨_, hmem t, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hd : 0 < r - l := by linarith
      refine ⟨⟨(x - l) / (r - l), div_nonneg (by linarith [hx.1]) hd.le,
        (div_le_one hd).mpr (by linarith [hx.2])⟩, ?_⟩
      have : l + (x - l) / (r - l) * (r - l) = x := by field_simp; ring
      simp only [g, this]
  have := GM11.isLineWithEnds_range ⟨g, hg⟩ hinj
  have h₀ : g 0 = qq a b c (l, f l) := by simp [g]
  have h₁ : g 1 = qq a b c (r, f r) := by simp [g]
  simp only [ContinuousMap.coe_mk] at this
  rwa [hrange, h₀, h₁] at this

theorem clear_of_abs {x y : ℝ} (h : 1 < |y|) : Clear a b c (x, y) := by
  intro i _
  have h₁ : 1 < y ^ 2 := by
    rw [← sq_abs]
    nlinarith
  have h₂ := sq_nonneg (x - 3 * i)
  simp only
  linarith

theorem clear_of_gap {x y : ℝ} (m : ℤ) (h₁ : 3 * (m : ℝ) + 1 < x) (h₂ : x < 3 * m + 2) :
    Clear a b c (x, y) := by
  intro i _
  have h₃ := sq_nonneg y
  simp only
  rcases le_or_gt (i : ℤ) m with h | h
  · have h₄ : (i : ℝ) ≤ m := by exact_mod_cast h
    nlinarith
  · have h₄ : (m : ℝ) + 1 ≤ i := by exact_mod_cast h
    nlinarith

/-- A plane set `S` of a strand: all its points are clear but for the listed points on circles. -/
theorem disjoint_of_below {S S' : Set (ℝ × ℝ)} (hS : ∀ z ∈ S, Ok a b c z)
    (hS' : ∀ z ∈ S', Clear a b c z) (h : Disjoint S S') :
    Disjoint (qq a b c '' S) (qq a b c '' S') := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', heq⟩
  exact Set.disjoint_left.mp h hz ((eq_of_qq_eq (hS' _ hz') (hS _ hz) heq) ▸ hz')

end GraphMinor.GM20.Draw
