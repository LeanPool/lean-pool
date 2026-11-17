/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Constraints.Closure

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Least shapes of flat constraints

The least shape has the constructor exactly where it is supported both from below and from above.
Pruning below its first leaf gives a solution whenever the constraint has no label clash. This
solution is used to obtain finite and symmetric solutions.

## Main declarations

- `LowerLabel`, `UpperLabel`: labels supported along a path.
- `shapeLabel`, `leastShape`, `leastShape_mono`, `leastShape_sat`: the least shape, monotonicity,
  and satisfaction.
- `satisfiable_iff_not_labelClash`: satisfiability is the absence of a label clash.
-/

@[expose] public section


namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics

variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

/-! ## Supported labels -/

/-- Syntactically supported lower bounds on the label of `x` at the path `π`. -/
def LowerLabel (Γ : List (LitT n V)) (π : List (Fin n)) : Semantics.Sym → V → Prop
  | .top, x => ∃ y, LitT.eqTop y ∈ Γ ∧ LowerAt Γ π y x
  | .f, x => ∃ a y, LitT.fLe a y ∈ Γ ∧ LowerAt Γ π y x
  | .bot, _ => True

@[simp] theorem lowerLabel_nil_f {x : V} :
    LowerLabel Γ [] .f x ↔ LowerF Γ x := by
  simp [LowerLabel, LowerF]

theorem LowerLabel.cons_fLe {π : List (Fin n)} {g : Semantics.Sym} {a : Fin n → V} {x : V}
    (hl : LitT.fLe a x ∈ Γ) (i : Fin n) (h : LowerLabel Γ π g (a i)) :
    LowerLabel Γ (i :: π) g x := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨b, y, hy, hp⟩ := h
    exact ⟨b, y, hy, .cons hl (.refl x) hp⟩
  | top =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons hl (.refl x) hp⟩

theorem LowerLabel.decompose {π π' : List (Fin n)} {g : Semantics.Sym} {x y : V}
    (h : LowerLabel Γ (π ++ π') g x) (hu : UpperAt Γ π x y) :
    LowerLabel Γ π' g y := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨a, z, hz, hp⟩ := h
    exact ⟨a, z, hz, hp.decompose_lower hu⟩
  | top =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hp.decompose_lower hu⟩

end DeciSigma1.Satisfiability

namespace DeciSigma1.Satisfiability

open DeciSigma1.Constraints DeciSigma1.Semantics

variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

/-! ## Upper label bounds -/

/-- Syntactically supported upper bounds on the label of `x` at the path `π`. -/
def UpperLabel (Γ : List (LitT n V)) (π : List (Fin n)) : Semantics.Sym → V → Prop
  | .bot, x => ∃ y, LitT.eqBot y ∈ Γ ∧ UpperAt Γ π x y
  | .f, x => ∃ y b, LitT.leF y b ∈ Γ ∧ UpperAt Γ π x y
  | .top, _ => True

/-- Cancel a lower path from an upper label judgment; the dual of `LowerLabel.decompose`. -/
theorem UpperLabel.decompose {π π' : List (Fin n)} {g : Semantics.Sym} {x y : V}
    (h : UpperLabel Γ (π ++ π') g x) (hl : LowerAt Γ π y x) :
    UpperLabel Γ π' g y := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hl.decompose_upper hp⟩
  | f =>
    obtain ⟨z, b, hz, hp⟩ := h
    exact ⟨z, b, hz, hl.decompose_upper hp⟩

theorem UpperLabel.cons_leF {π : List (Fin n)} {g : Semantics.Sym} {x : V} {b : Fin n → V}
    (hl : LitT.leF x b ∈ Γ) (i : Fin n) (h : UpperLabel Γ π g (b i)) :
    UpperLabel Γ (i :: π) g x := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons (.refl x) hl hp⟩
  | f =>
    obtain ⟨y, c, hy, hp⟩ := h
    exact ⟨y, c, hy, .cons (.refl x) hl hp⟩

@[simp] theorem upperLabel_nil_bot {x : V} :
    UpperLabel Γ [] .bot x ↔ UpperBot Γ x := by
  simp [UpperLabel, UpperBot]

@[simp] theorem upperLabel_nil_f {x : V} :
    UpperLabel Γ [] .f x ↔ UpperF Γ x := by
  simp [UpperLabel, UpperF]

/-! ## Shape labels and trees -/

/-- The label of the least shape: `f` when the constructor is supported from below and from above,
`⊥` when it is not supported from below but `⊥` or `f` is supported from above, and `⊤`
otherwise. -/
noncomputable def shapeLabel (Γ : List (LitT n V)) (x : V) (π : List (Fin n)) : Semantics.Sym := by
  classical
  exact if LowerLabel Γ π .f x ∧ UpperLabel Γ π .f x then .f
    else if ¬ LowerLabel Γ π .f x ∧
      (UpperLabel Γ π .bot x ∨ UpperLabel Γ π .f x) then .bot else .top

theorem shapeLabel_eq_f_iff {π : List (Fin n)} {x : V} :
    shapeLabel Γ x π = .f ↔ LowerLabel Γ π .f x ∧ UpperLabel Γ π .f x := by
  classical
  unfold shapeLabel
  split_ifs <;> simp_all

theorem shapeLabel_eq_bot_iff {π : List (Fin n)} {x : V} :
    shapeLabel Γ x π = .bot ↔ ¬ LowerLabel Γ π .f x ∧
      (UpperLabel Γ π .bot x ∨ UpperLabel Γ π .f x) := by
  classical
  unfold shapeLabel
  split_ifs <;> simp_all

theorem f_le_shapeLabel {π : List (Fin n)} {x : V}
    (h : LowerLabel Γ π .f x) : Sym.f ≤ shapeLabel Γ x π := by
  cases he : shapeLabel Γ x π with
  | bot => exact False.elim ((shapeLabel_eq_bot_iff.mp he).1 h)
  | f => exact le_rfl
  | top => exact Sym.le_top _

theorem shapeLabel_le_f {π : List (Fin n)} {x : V}
    (h : UpperLabel Γ π .f x) : shapeLabel Γ x π ≤ Sym.f := by
  classical
  by_cases hl : LowerLabel Γ π .f x
  · rw [shapeLabel_eq_f_iff.mpr ⟨hl, h⟩]
  · rw [shapeLabel_eq_bot_iff.mpr ⟨hl, Or.inr h⟩]
    exact Sym.bot_le _

/-- The shape label is monotone: if support of `f` from below passes from `x` at `π` to `y` at `τ`
and support from above passes back, the label of `x` at `π` is at most that of `y` at `τ`. -/
theorem shapeLabel_mono {π τ : List (Fin n)} {x y : V}
    (hl : LowerLabel Γ π .f x → LowerLabel Γ τ .f y)
    (hu : ∀ g, UpperLabel Γ τ g y → UpperLabel Γ π g x) :
    shapeLabel Γ x π ≤ shapeLabel Γ y τ := by
  cases he : shapeLabel Γ y τ with
  | top => exact Sym.le_top _
  | f => exact shapeLabel_le_f (hu .f (shapeLabel_eq_f_iff.mp he).2)
  | bot =>
    obtain ⟨hn, hb | hf⟩ := shapeLabel_eq_bot_iff.mp he
    · rw [shapeLabel_eq_bot_iff.mpr ⟨fun hx => hn (hl hx), Or.inl (hu .bot hb)⟩]
    · rw [shapeLabel_eq_bot_iff.mpr ⟨fun hx => hn (hl hx), Or.inr (hu .f hf)⟩]

/-- The least shape: the shape labels, pruned below the first leaf on each path. -/
noncomputable def leastShape (Γ : List (LitT n V)) (x : V) : Semantics.Tree n := by
  classical
  exact {
    fn :=
        fun π => if Semantics.IsLivePrefix (shapeLabel Γ x) π then some (shapeLabel Γ x π) else none
    wf := by
      constructor
      · simp
      · intro π i
        simp only [Semantics.isLivePrefix_append_singleton]
        by_cases ha : Semantics.IsLivePrefix (shapeLabel Γ x) π <;> simp [ha]
  }

open Classical in
theorem leastShape_fn (Γ : List (LitT n V)) (x : V) (π : List (Fin n)) :
    (leastShape Γ x).fn π =
      if Semantics.IsLivePrefix (shapeLabel Γ x) π then some (shapeLabel Γ x π) else none := by
  classical
  rfl

@[simp] theorem leastShape_fn_nil (Γ : List (LitT n V)) (x : V) :
    (leastShape Γ x).fn [] = some (shapeLabel Γ x []) := by
  simp [leastShape_fn]

theorem leastShape_label_eq {π : List (Fin n)} {x : V} {a : Semantics.Sym}
    (h : (leastShape Γ x).fn π = some a) : a = shapeLabel Γ x π := by
  classical
  rw [leastShape_fn] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

/-! ## Satisfaction by the least shape -/

/-- A variable fixed to `⊥` is `⊥` in the least shape. -/
theorem leastShape_eq_bot (hn : ¬ LabelClash Γ) {x : V}
    (hl : LitT.eqBot x ∈ Γ) : leastShape Γ x = Tree.bot := by
  apply (Tree.root_eq_bot_iff _).mp
  rw [leastShape_fn_nil]
  congr 1
  apply shapeLabel_eq_bot_iff.mpr
  have hu : UpperBot Γ x := ⟨x, hl, .refl x⟩
  exact ⟨fun hf => hn ⟨x, Or.inr (Or.inr ⟨lowerLabel_nil_f.mp hf, hu⟩)⟩,
    Or.inl (upperLabel_nil_bot.mpr hu)⟩

/-- A variable fixed to `⊤` is `⊤` in the least shape. -/
theorem leastShape_eq_top (hn : ¬ LabelClash Γ) {x : V}
    (hl : LitT.eqTop x ∈ Γ) : leastShape Γ x = Tree.top := by
  classical
  have htop : LowerTop Γ x := ⟨x, hl, .refl x⟩
  have hub : ¬ UpperLabel Γ [] .bot x :=
    fun h => hn ⟨x, Or.inl ⟨htop, upperLabel_nil_bot.mp h⟩⟩
  have huf : ¬ UpperLabel Γ [] .f x :=
    fun h => hn ⟨x, Or.inr (Or.inl ⟨htop, upperLabel_nil_f.mp h⟩)⟩
  apply (Tree.root_eq_top_iff _).mp
  simp [leastShape_fn_nil, shapeLabel, hub, huf]

/-- The least shape satisfies the lower constructor bounds. -/
theorem node_le_leastShape {a : Fin n → V} {x : V} (hl : LitT.fLe a x ∈ Γ) :
    Semantics.Tree.node (leastShape Γ ∘ a) ≤ leastShape Γ x := by
  intro π c d hc hd
  rw [leastShape_label_eq hd]
  cases π with
  | nil =>
    have he : c = .f := (Option.some.inj hc).symm
    subst c
    exact f_le_shapeLabel ⟨a, x, hl, .nil (.refl x)⟩
  | cons i π =>
    have hc' : (leastShape Γ (a i)).fn π = some c := hc
    rw [leastShape_label_eq hc']
    have hp : LowerAt Γ [i] (a i) x := .cons hl (.refl x) (.nil (.refl _))
    exact shapeLabel_mono (fun h => h.cons_fLe hl i)
      (fun _ h => UpperLabel.decompose (π := [i]) h hp)

/-- The least shape satisfies the upper constructor bounds. -/
theorem leastShape_le_node {x : V} {b : Fin n → V} (hl : LitT.leF x b ∈ Γ) :
    leastShape Γ x ≤ Semantics.Tree.node (leastShape Γ ∘ b) := by
  intro π c d hc hd
  rw [leastShape_label_eq hc]
  cases π with
  | nil =>
    have he : d = .f := (Option.some.inj hd).symm
    subst d
    exact shapeLabel_le_f ⟨x, b, hl, .nil (.refl x)⟩
  | cons i π =>
    have hd' : (leastShape Γ (b i)).fn π = some d := hd
    rw [leastShape_label_eq hd']
    have hp : UpperAt Γ [i] x (b i) := .cons (.refl x) hl (.nil (.refl _))
    exact shapeLabel_mono (fun h => LowerLabel.decompose (π := [i]) h hp)
      (fun _ h => h.cons_leF hl i)

/-- Derived inequalities are respected by the least shape. -/
theorem leastShape_mono {x y : V} (h : Derives Γ x y) :
    leastShape Γ x ≤ leastShape Γ y := by
  intro π a b ha hb
  rw [leastShape_label_eq ha, leastShape_label_eq hb]
  apply shapeLabel_mono
  · rintro ⟨a, z, hz, hp⟩
    exact ⟨a, z, hz, hp.trans_right h⟩
  · intro g hg
    cases g with
    | top => trivial
    | bot =>
      obtain ⟨z, hz, hp⟩ := hg
      exact ⟨z, hz, hp.trans_left h⟩
    | f =>
      obtain ⟨z, a, hz, hp⟩ := hg
      exact ⟨z, a, hz, hp.trans_left h⟩

/-- The least shape solves every constraint without label clash. -/
theorem leastShape_sat (hn : ¬ LabelClash Γ) : Covariant.Sat (leastShape Γ) Γ := by
  intro l hl
  cases l with
  | le x y => exact leastShape_mono (.lit hl)
  | leF x b => exact leastShape_le_node hl
  | fLe a x => exact node_le_leastShape hl
  | eqBot x => exact leastShape_eq_bot hn hl
  | eqTop x => exact leastShape_eq_top hn hl

/-- A covariant constraint is satisfiable exactly when it has no label clash. -/
theorem satisfiable_iff_not_labelClash : (∃ ρ, Covariant.Sat ρ Γ) ↔ ¬ LabelClash Γ :=
  ⟨fun hs hc => hc.unsatisfiable hs, fun hn => ⟨leastShape Γ, leastShape_sat hn⟩⟩

end DeciSigma1.Satisfiability
