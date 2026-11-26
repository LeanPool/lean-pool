/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.LocalCone
public import LeanPool.GraphMinor.GM11.PathClasses
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# An `O`-arc in a closed curve

This file is the combinatorial heart of Graph Minors VII, (11.2), and of Graph Minors XI, (7.3). Let
`T` be a
Hausdorff space and let `Sm` be a family of small sets, closed under subsets, such that two small
sets that
meet have a union in which paths with the same ends are homotopic (`Flat`). Let `Y ⊆ T`, and suppose
that
each `O`-arc in `Y` is null-homotopic. Then each closed curve in `Y` that is a product of finitely
many small
pieces is null-homotopic (`Ch.eq_refl`).

The proof follows the paper. First, (11.1) lets us take each piece to be a line or a point
(`IsArmTo`). A
closed curve with pieces `A₁, …, Aₙ` is treated by induction on `n`. If two pieces that are not
consecutive
meet in a point, then the curve splits there into two closed curves with fewer pieces. So we may
assume
that pieces that are not consecutive are disjoint. At each junction the paper "removes" a small
loop, and
after all of the junctions are done, the curve is an `O`-arc. We do this in order along the curve:
`exists_tri` treats all of the junctions but the last two, and `tri_close` treats these two.

Paths are taken up to homotopy with fixed ends (`Cl`), since in this way the products of paths are
associative. `Arw A f` says that the class `f` contains a path in `A`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {T : Type u} [TopologicalSpace T]

/-- A line or a point: `A` is a line from `a` to `b`, or `a = b` and `A` is this point. -/
def IsArmTo (A : Set T) (a b : T) : Prop := (a = b ∧ A = {a}) ∨ IsLineWithEnds A a b

section Arms

variable {A B : Set T} {a b c : T}

theorem IsArmTo.left_mem (h : IsArmTo A a b) : a ∈ A := by
  rcases h with ⟨-, rfl⟩ | h
  · rfl
  · exact IsLineWithEnds.left_mem h

theorem IsArmTo.right_mem (h : IsArmTo A a b) : b ∈ A := by
  rcases h with ⟨rfl, rfl⟩ | h
  · rfl
  · exact IsLineWithEnds.right_mem h

theorem IsArmTo.symm (h : IsArmTo A a b) : IsArmTo A b a := by
  rcases h with ⟨rfl, rfl⟩ | h
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (IsLineWithEnds.symm h)

theorem isArmTo_point (a : T) : IsArmTo {a} a a := Or.inl ⟨rfl, rfl⟩

theorem ends_ne (h : IsLineWithEnds A a b) : a ≠ b := by
  obtain ⟨f, h0, h1⟩ := h
  intro he
  have : f 0 = f 1 := Subtype.ext (by rw [h0, h1, he])
  exact zero_ne_one (f.injective this)

/-- The path along a line or a point. -/
theorem IsArmTo.exists_arw (h : IsArmTo A a b) : ∃ f : Cl a b, Arw A f := by
  rcases h with ⟨rfl, rfl⟩ | h
  · exact ⟨Cl.rf a, arw_refl rfl⟩
  · obtain ⟨g, g0, g1⟩ := h
    have hg : Continuous fun t : I => (g t).1 := by fun_prop
    exact ⟨Cl.mk ⟨⟨fun t => (g t).1, hg⟩, g0, g1⟩, _, fun u => (g u).2, rfl⟩

theorem IsArmTo.isSimplyConnected (h : IsArmTo A a b) : IsSimplyConnectedSet A := by
  rcases h with ⟨-, rfl⟩ | ⟨f, -, -⟩
  · exact isSimplyConnected_singleton a
  · exact IsLine.isSimplyConnected ⟨f⟩

theorem IsArmTo.flat (h : IsArmTo A a b) : Flat A :=
  IsSimplyConnectedSet.flat h.isSimplyConnected

variable [T2Space T]

/-- Two arms that meet only at a common end join to an arm. -/
theorem IsArmTo.join (h₁ : IsArmTo A a b) (h₂ : IsArmTo B b c) (h : A ∩ B = {b}) :
    IsArmTo (A ∪ B) a c := by
  rcases h₁ with ⟨rfl, rfl⟩ | h₁
  · rwa [union_eq_right.mpr (singleton_subset_iff.mpr h₂.left_mem)]
  rcases h₂ with ⟨rfl, rfl⟩ | h₂
  · rw [union_eq_left.mpr (singleton_subset_iff.mpr (IsLineWithEnds.right_mem h₁))]
    exact Or.inr h₁
  · exact Or.inr (IsLineWithEnds.union (IsLineWithEnds.symm h₁) h₂ h)

/-- An arc is cut in two arms at each of its points. -/
theorem arc_cut {e : I → T} (he : IsArcMap e) (t : I) :
    IsArmTo (e '' Iic t) (e 0) (e t) ∧ IsArmTo (e '' Ici t) (e t) (e 1) := by
  rcases eq_or_lt_of_le (unitInterval.nonneg t) with h0 | h0
  · have ht : t = 0 := Subtype.ext h0.symm
    subst ht
    refine ⟨Or.inl ⟨rfl, ?_⟩, Or.inr ?_⟩
    · have : Iic (0 : I) = {0} := subset_antisymm
        (fun s hs => Subtype.ext (le_antisymm hs (unitInterval.nonneg s)))
        (fun s hs => by rw [mem_singleton_iff.mp hs]; exact mem_Iic.mpr le_rfl)
      rw [this, image_singleton]
    · have : Ici (0 : I) = univ := eq_univ_of_forall fun s => unitInterval.nonneg s
      rw [this, image_univ]
      exact he.isLineWithEnds
  rcases eq_or_lt_of_le (unitInterval.le_one t) with h1 | h1
  · have ht : t = 1 := Subtype.ext h1
    subst ht
    refine ⟨Or.inr ?_, Or.inl ⟨rfl, ?_⟩⟩
    · have : Iic (1 : I) = univ := eq_univ_of_forall fun s => unitInterval.le_one s
      rw [this, image_univ]
      exact he.isLineWithEnds
    · have : Ici (1 : I) = {1} := subset_antisymm
        (fun s hs => Subtype.ext (le_antisymm (unitInterval.le_one s) hs))
        (fun s hs => by rw [mem_singleton_iff.mp hs]; exact mem_Ici.mpr le_rfl)
      rw [this, image_singleton]
  have h0' : (0 : ℝ) < t := h0
  have h1' : (t : ℝ) < 1 := h1
  have a1 := isArcMap_pieceA he le_rfl h0' h1'.le
  have a2 := isArcMap_pieceA he h0'.le h1' le_rfl
  have e1 : extI e 0 = e 0 := extI_coe e 0
  have e2 : extI e 1 = e 1 := extI_coe e 1
  have e3 : extI e t = e t := extI_coe e t
  have r1 : e '' Iic t = range (pieceA e 0 t) := by
    rw [range_pieceA e le_rfl h0'.le h1'.le]
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, ⟨s.2.1, hs⟩, extI_coe e s⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1, hs.2.trans h1'.le⟩, hs.2, (extI_of_mem e _).symm⟩
  have r2 : e '' Ici t = range (pieceA e t 1) := by
    rw [range_pieceA e h0'.le h1'.le le_rfl]
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, ⟨hs, s.2.2⟩, extI_coe e s⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, h0'.le.trans hs.1, hs.2⟩, hs.1, (extI_of_mem e _).symm⟩
  refine ⟨Or.inr ?_, Or.inr ?_⟩
  · rw [r1]
    have := a1.isLineWithEnds
    rwa [pieceA_zero, pieceA_one, e1, e3] at this
  · rw [r2]
    have := a2.isLineWithEnds
    rwa [pieceA_zero, pieceA_one, e2, e3] at this

/-- **Cutting an arm at the first point of a closed set.** -/
theorem IsArmTo.exists_first (h : IsArmTo A a b) {C : Set T} (hC : IsClosed C) (hne :
  (A ∩ C).Nonempty) :
    ∃ x ∈ A ∩ C, ∃ A₁ A₂ : Set T, IsArmTo A₁ a x ∧ IsArmTo A₂ x b ∧ A₁ ∪ A₂ = A ∧ A₁ ∩ A₂ = {x} ∧
      A₁ ∩ C = {x} := by
  rcases h with ⟨rfl, rfl⟩ | h
  · obtain ⟨x, rfl, hx⟩ := hne
    refine ⟨x, ⟨rfl, hx⟩, {x}, {x}, isArmTo_point x, isArmTo_point x, by simp, by simp, ?_⟩
    simpa using hx
  obtain ⟨e, he, rfl, rfl, rfl⟩ := h.exists_arc
  have hcl : IsCompact (e ⁻¹' C) := (hC.preimage he.1).isCompact
  obtain ⟨t, ht, htle⟩ := hcl.exists_isLeast (by
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hne
    exact ⟨s, hs⟩)
  obtain ⟨h₁, h₂⟩ := arc_cut he t
  refine ⟨e t, ⟨mem_range_self t, ht⟩, e '' Iic t, e '' Ici t, h₁, h₂, ?_, ?_, ?_⟩
  · rw [← image_union, Iic_union_Ici, image_univ]
  · ext y
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨s', hs', he'⟩⟩
      have h₁ : s' = s := he.2 he'
      have h₂ : s = t := le_antisymm hs (h₁ ▸ hs')
      rw [h₂]
      rfl
    · rintro rfl
      exact ⟨⟨t, le_rfl, rfl⟩, ⟨t, le_rfl, rfl⟩⟩
  · ext y
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hsC⟩
      have h₂ : s = t := le_antisymm hs (htle hsC)
      rw [h₂]
      rfl
    · rintro rfl
      exact ⟨⟨t, le_rfl, rfl⟩, ht⟩

theorem IsArmTo.isClosed (h : IsArmTo A a b) : IsClosed A := by
  rcases h with ⟨-, rfl⟩ | h
  · exact isClosed_singleton
  · exact h.isCompact.isClosed

/-- An arm is cut in two arms at each of its points, and a path in it is cut with it. -/
theorem IsArmTo.cut_arw (h : IsArmTo A a b) {w : T} (hw : w ∈ A) {f : Cl a b} (hf : Arw A f) :
    ∃ (A₁ A₂ : Set T) (f₁ : Cl a w) (f₂ : Cl w b), IsArmTo A₁ a w ∧ IsArmTo A₂ w b ∧ A₁ ⊆ A
      ∧ A₂ ⊆ A ∧
      Arw A₁ f₁ ∧ Arw A₂ f₂ ∧ f = f₁.trans f₂ := by
  obtain ⟨x, ⟨-, hx⟩, A₁, A₂, h₁, h₂, hu, -, -⟩ := h.exists_first (isClosed_singleton (x
    := w)) ⟨w, hw, rfl⟩
  obtain rfl : x = w := hx
  obtain ⟨f₁, hf₁⟩ := h₁.exists_arw
  obtain ⟨f₂, hf₂⟩ := h₂.exists_arw
  have hs₁ : A₁ ⊆ A := hu ▸ subset_union_left
  have hs₂ : A₂ ⊆ A := hu ▸ subset_union_right
  exact ⟨A₁, A₂, f₁, f₂, h₁, h₂, hs₁, hs₂, hf₁, hf₂, h.flat.eq hf ((hf₁.mono hs₁).trans
    (hf₂.mono hs₂))⟩

end Arms

/-! ## Chains of small pieces -/

/-- `Ch Y Sm l a b f`: the class `f` is a product of paths along the arms of the list `l`, each of
them a
small subset of `Y`. -/
inductive Ch (Y : Set T) (Sm : Set T → Prop) : List (Set T) → (a b : T) → Cl a b → Prop
  | nil (a : T) : Ch Y Sm [] a a (Cl.rf a)
  | cons {A : Set T} {l : List (Set T)} {a b c : T} {f : Cl a b} {g : Cl b c} :
      IsArmTo A a b → A ⊆ Y → Sm A → Arw A f → Ch Y Sm l b c g → Ch Y Sm (A :: l) a c (f.trans g)

section Chains

variable {Y : Set T} {Sm : Set T → Prop}

theorem Ch.append {l₁ l₂ : List (Set T)} {a b c : T} {f : Cl a b} {g : Cl b c}
  (h₁ : Ch Y Sm l₁ a b f)
    (h₂ : Ch Y Sm l₂ b c g) : Ch Y Sm (l₁ ++ l₂) a c (f.trans g) := by
  induction h₁ with
  | nil a =>
    rw [cl_refl_trans]
    exact h₂
  | cons h₁ h₃ h₄ h₅ _ ih =>
    rw [cl_assoc]
    exact Ch.cons h₁ h₃ h₄ h₅ (ih h₂)

theorem Ch.of_cons {A : Set T} {l : List (Set T)} {a c : T} {h : Cl a c} (hc : Ch Y Sm
  (A :: l) a c h) :
    ∃ (b : T) (f : Cl a b) (g : Cl b c), IsArmTo A a b ∧ A ⊆ Y ∧ Sm A ∧ Arw A f ∧ Ch Y Sm l b c g ∧
      h = f.trans g := by
  cases hc with
  | cons h₁ h₂ h₃ h₄ h₅ => exact ⟨_, _, _, h₁, h₂, h₃, h₄, h₅, rfl⟩

theorem Ch.split : ∀ {l₁ l₂ : List (Set T)} {a c : T} {h : Cl a c}, Ch Y Sm (l₁ ++ l₂) a c h →
    ∃ (b : T) (f : Cl a b) (g : Cl b c), Ch Y Sm l₁ a b f ∧ Ch Y Sm l₂ b c g ∧ h = f.trans g := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ a c h hc
    exact ⟨a, _, h, .nil a, hc, (cl_refl_trans h).symm⟩
  | cons A l₁ ih =>
    intro l₂ a c h hc
    obtain ⟨b, f, g, h₁, h₂, h₃, h₄, h₅, rfl⟩ := Ch.of_cons hc
    obtain ⟨m, g₁, g₂, c₁, c₂, rfl⟩ := ih h₅
    exact ⟨m, f.trans g₁, g₂, .cons h₁ h₂ h₃ h₄ c₁, c₂, (cl_assoc _ _ _).symm⟩

theorem Ch.single {A : Set T} {a b : T} {f : Cl a b} (h₁ : IsArmTo A a b) (h₂ : A ⊆ Y) (h₃ : Sm A)
    (h₄ : Arw A f) : Ch Y Sm [A] a b f := by
  have := Ch.cons h₁ h₂ h₃ h₄ (.nil b)
  rwa [cl_trans_refl] at this

theorem Ch.of_single {A : Set T} {a b : T} {f : Cl a b} (h : Ch Y Sm [A] a b f) :
    IsArmTo A a b ∧ A ⊆ Y ∧ Sm A ∧ Arw A f := by
  obtain ⟨_, f', g, h₁, h₂, h₃, h₄, h₅, rfl⟩ := Ch.of_cons h
  cases h₅
  rw [cl_trans_refl]
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- A class with `f.trans g` the identity at a junction can be dropped from a longer product. -/
private theorem drop {a b c d : T} (p : Cl a b) (x : Cl b c) (y : Cl c b) (q : Cl b d)
    (h : x.trans y = Cl.rf b) : p.trans (x.trans (y.trans q)) = p.trans q := by
  rw [← cl_assoc x y q, h, cl_refl_trans]

variable [T2Space T]

/-- If two pieces that are not consecutive meet, then the curve splits in two closed curves with
fewer
pieces. This is (2) in the paper's proof of VII, (11.2). -/
theorem Ch.split_of_meet (hmono : ∀ {A B : Set T}, Sm A → B ⊆ A → Sm B) {l₁ l₂ l₃ : List (Set T)}
    {A B : Set T} {a : T} {c : Cl a a}
    (ih : ∀ (l : List (Set T)) (x : T) (h : Cl x x), l.length < (l₁ ++ A :: (l₂ ++ B :: l₃)).length
      →
      Ch Y Sm l x x h → h = Cl.rf x)
    (hc : Ch Y Sm (l₁ ++ A :: (l₂ ++ B :: l₃)) a a c) (h₂ : l₂ ≠ []) (h₁₃ : l₁ ≠ [] ∨ l₃ ≠ [])
    (hne : (A ∩ B).Nonempty) : c = Cl.rf a := by
  obtain ⟨w, hwA, hwB⟩ := hne
  obtain ⟨p, g₁, r₁, c₁, r₂, rfl⟩ := Ch.split hc
  obtain ⟨p', x, r₃, hA, hAY, hAs, hx, r₄, rfl⟩ := Ch.of_cons r₂
  obtain ⟨q, g₂, r₅, c₂, r₆, rfl⟩ := Ch.split r₄
  obtain ⟨q', y, g₃, hB, hBY, hBs, hy, c₃, rfl⟩ := Ch.of_cons r₆
  obtain ⟨A₁, A₂, x₁, x₂, a₁, a₂, s₁, s₂, m₁, m₂, rfl⟩ := hA.cut_arw hwA hx
  obtain ⟨B₁, B₂, y₁, y₂, b₁, b₂, t₁, t₂, n₁, n₂, rfl⟩ := hB.cut_arw hwB hy
  have hl₂ : 0 < l₂.length := List.length_pos_iff.mpr h₂
  have hl₁₃ : 0 < l₁.length + l₃.length := by
    rcases h₁₃ with h | h
    · have := List.length_pos_iff.mpr h
      omega
    · have := List.length_pos_iff.mpr h
      omega
  have hA₂ : Ch Y Sm (A₂ :: (l₂ ++ [B₁])) w w (x₂.trans (g₂.trans y₁)) :=
    .cons a₂ (s₂.trans hAY) (hmono hAs s₂) m₂ (c₂.append (.single b₁ (t₁.trans hBY)
      (hmono hBs t₁) n₁))
  have hin : x₂.trans (g₂.trans y₁) = Cl.rf w := by
    refine ih _ _ _ ?_ hA₂
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  have hout : Ch Y Sm (l₁ ++ A₁ :: B₂ :: l₃) a a (g₁.trans (x₁.trans (y₂.trans g₃))) :=
    c₁.append (.cons a₁ (s₁.trans hAY) (hmono hAs s₁) m₁ (.cons b₂ (t₂.trans hBY)
      (hmono hBs t₂) n₂ c₃))
  have hout' := ih _ _ _ (by
    simp only [List.length_cons, List.length_append]
    omega) hout
  rw [← hout']
  have e : (x₁.trans x₂).trans (g₂.trans ((y₁.trans y₂).trans g₃)) =
      x₁.trans ((x₂.trans (g₂.trans y₁)).trans (y₂.trans g₃)) := by
    simp only [cl_assoc]
  rw [e, hin, cl_refl_trans]

variable (hmono : ∀ {A B : Set T}, Sm A → B ⊆ A → Sm B)
  (hpair : ∀ {A B : Set T}, Sm A → Sm B → (A ∩ B).Nonempty → Flat (A ∪ B))

include hmono hpair in
/-- All junctions but two: the first `n - 1` pieces of a closed curve are replaced by a line, in
three parts.
`H` lies in the first piece, `R` in the last, and `M` in the pieces between them. -/
theorem exists_tri (A : Set T) (mid : List (Set T)) : ∀ (B : Set T) (a b : T) (c : Cl a b),
    Ch Y Sm (A :: (mid ++ [B])) a b c →
    (∀ (l₁ : List (Set T)) (X : Set T) (l₂ : List (Set T)) (Z : Set T) (l₃ : List (Set T)),
      A :: (mid ++ [B]) = l₁ ++ X :: (l₂ ++ Z :: l₃) → l₂ ≠ [] → Disjoint X Z) →
    ∃ (H M R : Set T) (h g : T) (u : Cl a h) (w : Cl h g) (v : Cl g b),
      IsArmTo H a h ∧ IsArmTo M h g ∧ IsArmTo R g b ∧ H ∩ M = {h} ∧ (H ∪ M) ∩ R = {g} ∧ H ⊆ A
        ∧ R ⊆ B ∧
      H ⊆ Y ∧ M ⊆ Y ∧ R ⊆ Y ∧ Sm H ∧ Sm R ∧ (∀ y ∈ M, y = h ∨ ∃ Z ∈ mid, y ∈ Z) ∧ Arw H u ∧ Arw M w
        ∧
      Arw R v ∧ c = u.trans (w.trans v) := by
  induction mid using List.reverseRecOn with
  | nil =>
    intro B a b c hc _
    obtain ⟨p, f, g, hA, hAY, hAs, hf, r, rfl⟩ := Ch.of_cons hc
    obtain ⟨hB, hBY, hBs, hg⟩ := Ch.of_single r
    obtain ⟨x, ⟨hxA, hxB⟩, A₁, A₂, a₁, a₂, hu, hi, hfirst⟩ := hA.exists_first hB.isClosed
      ⟨p, hA.right_mem, hB.left_mem⟩
    have s₁ : A₁ ⊆ A := hu ▸ subset_union_left
    have s₂ : A₂ ⊆ A := hu ▸ subset_union_right
    obtain ⟨f₁, m₁⟩ := a₁.exists_arw
    obtain ⟨f₂, m₂⟩ := a₂.exists_arw
    have hff : f = f₁.trans f₂ := hA.flat.eq hf ((m₁.mono s₁).trans (m₂.mono s₂))
    obtain ⟨B₁, B₂, g₁, g₂, b₁, b₂, t₁, t₂, n₁, n₂, rfl⟩ := hB.cut_arw hxB hg
    have hloop : f₂.trans g₁ = Cl.rf x :=
      (hpair hAs hBs ⟨p, hA.right_mem, hB.left_mem⟩).eq ((m₂.mono (s₂.trans
        subset_union_left)).trans
        (n₁.mono (t₁.trans subset_union_right))) (arw_refl (Or.inl hxA))
    have hxA₁ : x ∈ A₁ := a₁.right_mem
    have hxB₂ : x ∈ B₂ := b₂.left_mem
    refine ⟨A₁, {x}, B₂, x, x, f₁, Cl.rf x, g₂, a₁, isArmTo_point x, b₂, ?_, ?_, s₁, t₂,
      s₁.trans hAY, ?_,
      t₂.trans hBY, hmono hAs s₁, hmono hBs t₂, ?_, m₁, arw_refl rfl, n₂, ?_⟩
    · simpa using hxA₁
    · rw [union_eq_left.mpr (singleton_subset_iff.mpr hxA₁)]
      ext y
      constructor
      · rintro ⟨h₁, h₂⟩
        have : y ∈ A₁ ∩ B := ⟨h₁, t₂ h₂⟩
        rwa [hfirst] at this
      · rintro rfl
        exact ⟨hxA₁, hxB₂⟩
    · exact singleton_subset_iff.mpr (hAY hxA)
    · exact fun y hy => Or.inl hy
    · rw [hff, cl_refl_trans, cl_assoc, drop f₁ f₂ g₁ g₂ hloop]
  | append_singleton mid D ih =>
    intro X a b c hc hdis
    have hsplit : A :: ((mid ++ [D]) ++ [X]) = (A :: (mid ++ [D])) ++ [X] := rfl
    rw [hsplit] at hc
    obtain ⟨b', c₀, f, r₁, r₂, rfl⟩ := Ch.split hc
    obtain ⟨hX, hXY, hXs, hf⟩ := Ch.of_single r₂
    have hdis' : ∀ (l₁ : List (Set T)) (X' : Set T) (l₂ : List (Set T)) (Z : Set T) (l₃ : List
      (Set T)),
        A :: (mid ++ [D]) = l₁ ++ X' :: (l₂ ++ Z :: l₃) → l₂ ≠ [] → Disjoint X' Z := by
      intro l₁ X' l₂ Z l₃ e hl
      refine hdis l₁ X' l₂ Z (l₃ ++ [X]) ?_ hl
      have := congrArg (· ++ [X]) e
      simpa [List.append_assoc] using this
    obtain ⟨H, M, R, h, g, u, w, v, aH, aM, aR, hHM, hHMR, hHA, hRD, hHY, hMY, hRY, hHs, hRs, hMid,
      mu, mw,
      mv, rfl⟩ := ih D a b' c₀ r₁ hdis'
    have hAX : Disjoint A X := hdis [] A (mid ++ [D]) X [] (by simp) (by simp)
    have hmX : ∀ Z ∈ mid, Disjoint Z X := by
      intro Z hZ
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hZ
      exact hdis (A :: s) Z (t ++ [D]) X [] (by simp) (by simp)
    have hoff : ∀ y ∈ H ∪ M, y ∉ X := by
      have hH : ∀ y ∈ H, y ∉ X := fun y hy => disjoint_left.mp hAX (hHA hy)
      rintro y (hy | hy)
      · exact hH y hy
      · rcases hMid y hy with rfl | ⟨Z, hZ, hyZ⟩
        · exact hH _ aH.right_mem
        · exact disjoint_left.mp (hmX Z hZ) hyZ
    obtain ⟨x, ⟨hxR, hxX⟩, R₁, R₂, a₁, a₂, hu, hi, hfirst⟩ := aR.exists_first hX.isClosed
      ⟨b', aR.right_mem, hX.left_mem⟩
    have s₁ : R₁ ⊆ R := hu ▸ subset_union_left
    have s₂ : R₂ ⊆ R := hu ▸ subset_union_right
    obtain ⟨v₁, m₁⟩ := a₁.exists_arw
    obtain ⟨v₂, m₂⟩ := a₂.exists_arw
    have hvv : v = v₁.trans v₂ := aR.flat.eq mv ((m₁.mono s₁).trans (m₂.mono s₂))
    obtain ⟨X₁, X₂, f₁, f₂, b₁, b₂, t₁, t₂, n₁, n₂, rfl⟩ := hX.cut_arw hxX hf
    have hloop : v₂.trans f₁ = Cl.rf x :=
      (hpair hRs hXs ⟨b', aR.right_mem, hX.left_mem⟩).eq ((m₂.mono (s₂.trans
        subset_union_left)).trans
        (n₁.mono (t₁.trans subset_union_right))) (arw_refl (Or.inl hxR))
    have hgR : g ∈ R := aR.left_mem
    have hgHM : g ∈ H ∪ M := Or.inr aM.right_mem
    have hmeet : ∀ y ∈ H ∪ M, y ∈ R → y = g := fun y h₁ h₂ => by
      have : y ∈ (H ∪ M) ∩ R := ⟨h₁, h₂⟩
      rwa [hHMR] at this
    have hxX₂ : x ∈ X₂ := b₂.left_mem
    have hxR₁ : x ∈ R₁ := a₁.right_mem
    refine ⟨H, M ∪ R₁, X₂, h, x, u, w.trans v₁, f₂, aH, aM.join a₁ ?_, b₂, ?_, ?_, hHA, t₂, hHY,
      union_subset hMY (s₁.trans hRY), t₂.trans hXY, hHs, hmono hXs t₂, ?_, mu,
      (mw.mono subset_union_left).trans (m₁.mono subset_union_right), n₂, ?_⟩
    · ext y
      constructor
      · rintro ⟨h₁, h₂⟩
        exact hmeet y (Or.inr h₁) (s₁ h₂)
      · rintro rfl
        exact ⟨aM.right_mem, a₁.left_mem⟩
    · ext y
      constructor
      · rintro ⟨h₁, h₂ | h₂⟩
        · have : y ∈ H ∩ M := ⟨h₁, h₂⟩
          rwa [hHM] at this
        · have e₁ := hmeet y (Or.inl h₁) (s₁ h₂)
          have : y ∈ H ∩ M := ⟨h₁, e₁ ▸ aM.right_mem⟩
          rwa [hHM] at this
      · rintro rfl
        exact ⟨aH.right_mem, Or.inl aM.left_mem⟩
    · ext y
      constructor
      · rintro ⟨h₁ | h₁ | h₁, h₂⟩
        · exact (hoff y (Or.inl h₁) (t₂ h₂)).elim
        · exact (hoff y (Or.inr h₁) (t₂ h₂)).elim
        · have : y ∈ R₁ ∩ X := ⟨h₁, t₂ h₂⟩
          rwa [hfirst] at this
      · rintro rfl
        exact ⟨Or.inr (Or.inr hxR₁), hxX₂⟩
    · rintro y (hy | hy)
      · rcases hMid y hy with h₁ | ⟨Z, hZ, hyZ⟩
        · exact Or.inl h₁
        · exact Or.inr ⟨Z, List.mem_append_left _ hZ, hyZ⟩
      · exact Or.inr ⟨D, by simp, hRD (s₁ hy)⟩
    · rw [hvv]
      have e : (u.trans (w.trans (v₁.trans v₂))).trans (f₁.trans f₂) =
          u.trans ((w.trans v₁).trans ((v₂.trans f₁).trans f₂)) := by
        simp only [cl_assoc]
      rw [e, hloop, cl_refl_trans, cl_assoc]

include hpair in
/-- The last two junctions. The line `H ∪ M ∪ R` and the arm `Q` close up to an `O`-arc, once a
small loop
at each end of `Q` is removed. -/
theorem tri_close {H M R Q : Set T} {a h g b : T} {u : Cl a h} {w : Cl h g} {v : Cl g b} {z : Cl b
  a}
    (aH : IsArmTo H a h) (aM : IsArmTo M h g) (aR : IsArmTo R g b) (aQ : IsArmTo Q b a)
      (hHM : H ∩ M = {h})
    (hHMR : (H ∪ M) ∩ R = {g}) (hHY : H ⊆ Y) (hMY : M ⊆ Y) (hRY : R ⊆ Y) (hQY : Q ⊆ Y) (hHs : Sm H)
    (hRs : Sm R) (hQs : Sm Q) (hQM : ∀ y ∈ M, y ∈ Q → y = h) (mu : Arw H u) (mw : Arw M w)
      (mv : Arw R v)
    (mz : Arw Q z)
    (hO : ∀ {x y : T} {L₁ L₂ : Set T}, IsLineWithEnds L₁ x y → IsLineWithEnds L₂ x y
      → L₁ ∩ L₂ ⊆ {x, y} →
      L₁ ∪ L₂ ⊆ Y → ∀ f g : Cl x y, Arw L₁ f → Arw L₂ g → f = g) :
    (u.trans (w.trans v)).trans z = Cl.rf a := by
  -- The first point of `R` on `Q`.
  obtain ⟨x, ⟨hxR, hxQ⟩, R₁, R₂, a₁, a₂, hu, hi, hfirst⟩ := aR.exists_first aQ.isClosed
    ⟨b, aR.right_mem, aQ.left_mem⟩
  have s₁ : R₁ ⊆ R := hu ▸ subset_union_left
  have s₂ : R₂ ⊆ R := hu ▸ subset_union_right
  obtain ⟨v₁, m₁⟩ := a₁.exists_arw
  obtain ⟨v₂, m₂⟩ := a₂.exists_arw
  have hvv : v = v₁.trans v₂ := aR.flat.eq mv ((m₁.mono s₁).trans (m₂.mono s₂))
  obtain ⟨Q₁, Q₂, z₁, z₂, b₁, b₂, t₁, t₂, n₁, n₂, rfl⟩ := aQ.cut_arw hxQ mz
  have hloop₁ : v₂.trans z₁ = Cl.rf x :=
    (hpair hRs hQs ⟨b, aR.right_mem, aQ.left_mem⟩).eq ((m₂.mono (s₂.trans subset_union_left)).trans
      (n₁.mono (t₁.trans subset_union_right))) (arw_refl (Or.inl hxR))
  -- The last point of `H` on the rest of `Q`.
  obtain ⟨y, ⟨hyH, hyQ⟩, H₂, H₁, a₃, a₄, hu', hi', hfirst'⟩ := aH.symm.exists_first b₂.isClosed
    ⟨a, aH.left_mem, b₂.right_mem⟩
  have s₃ : H₁ ⊆ H := hu' ▸ subset_union_right
  have s₄ : H₂ ⊆ H := hu' ▸ subset_union_left
  obtain ⟨u₁, m₃⟩ := a₄.symm.exists_arw
  obtain ⟨u₂, m₄⟩ := a₃.symm.exists_arw
  have huu : u = u₁.trans u₂ := aH.flat.eq mu ((m₃.mono s₃).trans (m₄.mono s₄))
  obtain ⟨Q₃, Q₄, z₃, z₄, b₃, b₄, t₃, t₄, n₃, n₄, rfl⟩ := b₂.cut_arw hyQ n₂
  have hloop₂ : z₄.trans u₁ = Cl.rf y :=
    (hpair hQs hHs ⟨a, aQ.right_mem, aH.left_mem⟩).eq (((n₄.mono (t₄.trans
      (t₂.trans subset_rfl))).mono
      subset_union_left).trans (m₃.mono (s₃.trans subset_union_right))) (arw_refl (Or.inr hyH))
  -- The `O`-arc.
  have hP₁ : IsArmTo (H₂ ∪ M) y g := a₃.symm.join aM (by
    ext p
    constructor
    · rintro ⟨h₁, h₂⟩
      have : p ∈ H ∩ M := ⟨s₄ h₁, h₂⟩
      rwa [hHM] at this
    · rintro rfl
      exact ⟨a₃.left_mem, aM.left_mem⟩)
  have hmeet : ∀ p ∈ H ∪ M, p ∈ R → p = g := fun p h₁ h₂ => by
    have : p ∈ (H ∪ M) ∩ R := ⟨h₁, h₂⟩
    rwa [hHMR] at this
  have hP : IsArmTo ((H₂ ∪ M) ∪ R₁) y x := hP₁.join a₁ (by
    ext p
    constructor
    · rintro ⟨h₁, h₂⟩
      refine hmeet p ?_ (s₁ h₂)
      rcases h₁ with h₁ | h₁
      · exact Or.inl (s₄ h₁)
      · exact Or.inr h₁
    · rintro rfl
      exact ⟨Or.inr aM.right_mem, a₁.left_mem⟩)
  have hcap : ((H₂ ∪ M) ∪ R₁) ∩ Q₃ ⊆ {x, y} := by
    rintro p ⟨(h₁ | h₁) | h₁, h₂⟩
    · have : p ∈ H₂ ∩ Q₂ := ⟨h₁, t₃ h₂⟩
      rw [hfirst'] at this
      exact Or.inr this
    · have e₁ := hQM p h₁ (t₂ (t₃ h₂))
      have : p ∈ H₂ ∩ Q₂ := ⟨e₁ ▸ a₃.left_mem, t₃ h₂⟩
      rw [hfirst'] at this
      exact Or.inr this
    · have : p ∈ R₁ ∩ Q := ⟨h₁, t₂ (t₃ h₂)⟩
      rw [hfirst] at this
      exact Or.inl this
  have hmP : Arw ((H₂ ∪ M) ∪ R₁) (u₂.trans (w.trans v₁)) :=
    (m₄.mono (subset_union_left.trans subset_union_left)).trans
      ((mw.mono (subset_union_right.trans subset_union_left)).trans (m₁.mono subset_union_right))
  have hPY : (H₂ ∪ M) ∪ R₁ ⊆ Y :=
    union_subset (union_subset (s₄.trans hHY) hMY) (s₁.trans hRY)
  have hmid : (u₂.trans (w.trans v₁)).trans z₃ = Cl.rf y := by
    by_cases hxy : x = y
    · subst hxy
      have hpt : (H₂ ∪ M) ∪ R₁ = {x} := by
        rcases hP with ⟨-, e⟩ | hl
        · exact e
        · exact (ends_ne hl rfl).elim
      have hq : Q₃ = {x} := by
        rcases b₃ with ⟨-, e⟩ | hl
        · exact e
        · exact (ends_ne hl rfl).elim
      rw [hpt] at hmP
      rw [hq] at n₃
      exact (isArmTo_point x).flat.eq (hmP.trans n₃) (arw_refl rfl)
    · have l₁ : IsLineWithEnds ((H₂ ∪ M) ∪ R₁) y x := by
        rcases hP with ⟨e, -⟩ | hl
        · exact (hxy e.symm).elim
        · exact hl
      have l₂ : IsLineWithEnds Q₃ x y := by
        rcases b₃ with ⟨e, -⟩ | hl
        · exact (hxy e).elim
        · exact hl
      have hsw : ((H₂ ∪ M) ∪ R₁) ∩ Q₃ ⊆ {y, x} := fun p hp => (hcap hp).symm
      have := hO l₁ (IsLineWithEnds.symm l₂) hsw (union_subset hPY (t₃.trans
        (t₂.trans hQY))) _ _ hmP n₃.symm
      rw [this]
      exact cl_symm_trans z₃
  subst huu hvv
  have e₁ : ((u₁.trans u₂).trans (w.trans (v₁.trans v₂))).trans (z₁.trans (z₃.trans z₄)) =
      u₁.trans (((u₂.trans (w.trans v₁)).trans ((v₂.trans z₁).trans z₃)).trans z₄) := by
    simp only [cl_assoc]
  rw [e₁, hloop₁, cl_refl_trans, hmid, cl_refl_trans]
  have e₂ : z₄ = u₁.symm := by
    calc z₄ = z₄.trans (u₁.trans u₁.symm) := by rw [cl_trans_symm, cl_trans_refl]
      _ = u₁.symm := by rw [← cl_assoc, hloop₂, cl_refl_trans]
  rw [e₂]
  exact cl_trans_symm u₁

include hmono hpair in
/-- **A closed chain of small pieces is null-homotopic**, if each `O`-arc in `Y` is null-homotopic.
This is
the main step of the proof of Graph Minors VII, (11.2) (page 249), in the setting of the proof of
Graph
Minors XI, (7.3). -/
theorem Ch.eq_refl
    (hO : ∀ {x y : T} {L₁ L₂ : Set T}, IsLineWithEnds L₁ x y → IsLineWithEnds L₂ x y
      → L₁ ∩ L₂ ⊆ {x, y} →
      L₁ ∪ L₂ ⊆ Y → ∀ f g : Cl x y, Arw L₁ f → Arw L₂ g → f = g) :
    ∀ (n : ℕ) (l : List (Set T)) (a : T) (c : Cl a a), l.length = n → Ch Y Sm l a a c → c = Cl.rf a
      := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l a c hn hc
  have ih' : ∀ (l' : List (Set T)) (x : T) (h : Cl x x), l'.length < l.length → Ch Y Sm l' x x h →
      h = Cl.rf x := fun l' x h hl hc' => ih l'.length (hn ▸ hl) l' x h rfl hc'
  by_cases hbad : ∃ (l₁ : List (Set T)) (A : Set T) (l₂ : List (Set T)) (B : Set T) (l₃ : List
    (Set T)),
      l = l₁ ++ A :: (l₂ ++ B :: l₃) ∧ l₂ ≠ [] ∧ (l₁ ≠ [] ∨ l₃ ≠ []) ∧ (A ∩ B).Nonempty
  · obtain ⟨l₁, A, l₂, B, l₃, rfl, h₂, h₁₃, hne⟩ := hbad
    exact Ch.split_of_meet hmono ih' hc h₂ h₁₃ hne
  push Not at hbad
  have hdisj : ∀ (l₁ : List (Set T)) (A : Set T) (l₂ : List (Set T)) (B : Set T) (l₃ : List
    (Set T)),
      l = l₁ ++ A :: (l₂ ++ B :: l₃) → l₂ ≠ [] → (l₁ ≠ [] ∨ l₃ ≠ []) → Disjoint A B := by
    intro l₁ A l₂ B l₃ e h₂ h₁₃
    have := hbad l₁ A l₂ B l₃ e h₂ h₁₃
    exact Set.disjoint_iff_inter_eq_empty.mpr this
  rcases l with - | ⟨A, t⟩
  · cases hc
    rfl
  rcases List.eq_nil_or_concat' t with rfl | ⟨t', Q, rfl⟩
  · obtain ⟨hA, -, -, hf⟩ := Ch.of_single hc
    exact hA.flat.eq hf (arw_refl hA.left_mem)
  obtain ⟨b, f, g, hA, hAY, hAs, hf, r, rfl⟩ := Ch.of_cons hc
  rcases List.eq_nil_or_concat' t' with rfl | ⟨mid, B, rfl⟩
  · obtain ⟨hQ, hQY, hQs, hg⟩ := Ch.of_single r
    exact (hpair hAs hQs ⟨b, hA.right_mem, hQ.left_mem⟩).eq
      ((hf.mono subset_union_left).trans (hg.mono subset_union_right)) (arw_refl
        (Or.inl hA.left_mem))
  have hch := Ch.cons hA hAY hAs hf r
  have hsplit : A :: ((mid ++ [B]) ++ [Q]) = (A :: (mid ++ [B])) ++ [Q] := rfl
  rw [hsplit] at hch
  obtain ⟨b', c₀, z, r₁, r₂, hz⟩ := Ch.split hch
  obtain ⟨hQ, hQY, hQs, mz⟩ := Ch.of_single r₂
  have hdis' : ∀ (l₁ : List (Set T)) (X' : Set T) (l₂ : List (Set T)) (Z : Set T) (l₃ : List
    (Set T)),
      A :: (mid ++ [B]) = l₁ ++ X' :: (l₂ ++ Z :: l₃) → l₂ ≠ [] → Disjoint X' Z := by
    intro l₁ X' l₂ Z l₃ e hl
    refine hdisj l₁ X' l₂ Z (l₃ ++ [Q]) ?_ hl (Or.inr (by simp))
    have := congrArg (· ++ [Q]) e
    simpa [List.append_assoc] using this
  obtain ⟨H, M, R, h, g', u, w, v, aH, aM, aR, hHM, hHMR, -, -, hHY, hMY, hRY, hHs, hRs, hMid, mu,
    mw,
    mv, rfl⟩ := exists_tri hmono hpair A mid B a b' c₀ r₁ hdis'
  rw [hz]
  refine tri_close hpair aH aM aR hQ hHM hHMR hHY hMY hRY hQY hHs hRs hQs ?_ mu mw mv mz hO
  intro y hy hyQ
  rcases hMid y hy with h₁ | ⟨Z, hZ, hyZ⟩
  · exact h₁
  · obtain ⟨s, t, rfl⟩ := List.append_of_mem hZ
    have := hdisj (A :: s) Z (t ++ [B]) Q [] (by simp) (by simp) (Or.inl (by simp))
    exact (disjoint_left.mp this hyZ hyQ).elim

end Chains

end GraphMinor.GM11
