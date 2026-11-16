/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Semantics.Tree
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # The subtype order with argument variance

With a variance `c : Fin n → Bool` (`c i = true` for a contravariant argument), the polarity of a
path is the parity of its contravariant steps. The subtype order `Tree.Le c t u` compares the labels
of `t` and `u` at every common path, reversed at paths of negative polarity. Normalizing a tree,
that is, exchanging `⊥` and `⊤` at the leaves of negative polarity, reduces this order to the
covariant order `Tree.CovLe` (`treeLe_iff_normalize`). The module also characterizes the covariant
order through the labels reached along a path (`Tree.HasLabel`), which yields finite witnesses to
its failure.

## Main declarations

- `polarity`, `Sym.flip`: path polarity and the exchange of `⊥` and `⊤`.
- `Tree.normalize`, `Tree.dual`, `FTree.normalize`, `FTree.dual`: normalization of trees.
- `Tree.trace`, `Tree.HasLabel`: following a path, staying at the first leaf reached.
- `le_iff_forall_hasLabel`: the covariant order through the labels along each path.
- `Tree.Le`, `treeLe_iff_normalize`: the subtype order with variance.
-/

@[expose] public section


namespace DeciSigma1.Semantics

variable {n : ℕ}

/-- The polarity of a path: `true` (negative) when it takes an odd number of contravariant
argument positions. -/
def polarity (c : Fin n → Bool) : List (Fin n) → Bool
  | [] => false
  | i :: π => Bool.xor (c i) (polarity c π)

@[simp] theorem pol_nil (c : Fin n → Bool) : polarity c [] = false := rfl
@[simp] theorem pol_cons (c : Fin n → Bool) (i : Fin n) (π : List (Fin n)) :
    polarity c (i :: π) = Bool.xor (c i) (polarity c π) := rfl
@[simp] theorem pol_false (π : List (Fin n)) : polarity (fun _ => false) π = false := by
  induction π with
  | nil => rfl
  | cons i π ih => simp [polarity, ih]

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics.Sym
open DeciSigma1.Semantics.Sym

/-- The order of labels at a path of polarity `p`: `a ≤ b`, reversed when `p = true`. -/
def LeWithPolarity (p : Bool) (a b : Sym) : Prop := if p then b ≤ a else a ≤ b

/-- Exchange `⊥` and `⊤` when the polarity is `true`; `f` is fixed. -/
def flip : Bool → Sym → Sym
  | false, a => a
  | true, bot => top
  | true, f => f
  | true, top => bot

@[simp] theorem flip_false (a : Sym) : flip false a = a := rfl
@[simp] theorem flip_f (p : Bool) : flip p f = f := by cases p <;> rfl
@[simp] theorem flip_involutive (p : Bool) (a : Sym) : flip p (flip p a) = a := by
  cases p <;> cases a <;> rfl
@[simp] theorem flip_eq_f (p : Bool) (a : Sym) : flip p a = f ↔ a = f := by
  cases p <;> cases a <;> decide

theorem leWithPolarity_iff_flip (p : Bool) (a b : Sym) :
    LeWithPolarity p a b ↔ flip p a ≤ flip p b := by
  cases p <;> cases a <;> cases b <;> simp [LeWithPolarity, flip]

end DeciSigma1.Semantics.Sym

namespace DeciSigma1.Semantics

variable {n : ℕ}

/-- The normalization of `t` relative to the polarity `p`: the leaf label at each path `π` is
exchanged with its dual when `p ⊕ polarity c π` is `true`. -/
def Tree.normalize (c : Fin n → Bool) (p : Bool) (t : Tree n) : Tree n where
  fn π := (t.fn π).map (Sym.flip (Bool.xor p (polarity c π)))
  wf := by
    constructor
    · simpa using t.wf.1
    · intro π i
      simpa only [Option.isSome_map, Option.map_eq_some_iff, Sym.flip_eq_f,
        exists_eq_right] using t.wf.2 π i

@[simp] theorem normalize_fn (c : Fin n → Bool) (p : Bool) (t : Tree n) (π : List (Fin n)) :
    (Tree.normalize c p t).fn π = (t.fn π).map (Sym.flip (Bool.xor p (polarity c π))) := rfl

theorem normalize_constructor (c : Fin n → Bool) (p : Bool) (t : Tree n)
    (π : List (Fin n)) :
    (Tree.normalize c p t).fn π = some Sym.f ↔ t.fn π = some Sym.f := by
  simp only [normalize_fn, Option.map_eq_some_iff, Sym.flip_eq_f, exists_eq_right]

@[simp] theorem normalize_involutive (c : Fin n → Bool) (p : Bool) (t : Tree n) :
    Tree.normalize c p (Tree.normalize c p t) = t := by
  apply Tree.ext; funext π
  cases h : t.fn π <;> simp [h]

theorem normalize_injective (c : Fin n → Bool) (p : Bool) :
    Function.Injective (Tree.normalize c p) :=
  Function.LeftInverse.injective (normalize_involutive c p)

@[simp] theorem normalize_bot (c : Fin n → Bool) (p : Bool) :
    Tree.normalize c p Tree.bot = if p then Tree.top else Tree.bot := by
  apply Tree.ext; funext π
  cases p <;> cases π <;> simp [Sym.flip]

@[simp] theorem normalize_top (c : Fin n → Bool) (p : Bool) :
    Tree.normalize c p Tree.top = if p then Tree.bot else Tree.top := by
  apply Tree.ext; funext π
  cases p <;> cases π <;> simp [Sym.flip]

@[simp] theorem normalize_node (c : Fin n → Bool) (p : Bool) (a : Fin n → Tree n) :
    Tree.normalize c p (Tree.node a) =
        Tree.node (fun i => Tree.normalize c (Bool.xor p (c i)) (a i)) := by
  apply Tree.ext; funext w
  cases w with
  | nil => simp
  | cons i w => simp

@[simp] theorem normalize_false_variance (t : Tree n) :
    Tree.normalize (fun _ => false) false t = t := by
  apply Tree.ext; funext π; cases h : t.fn π <;> simp [h]

/-- The dual of a tree, exchanging `⊥` and `⊤` at every leaf. -/
def Tree.dual : Tree n → Tree n := normalize (fun _ => false) true

@[simp] theorem dual_fn (t : Tree n) (π : List (Fin n)) :
    (Tree.dual t).fn π = (t.fn π).map (Sym.flip true) := by simp [Tree.dual]

@[simp] theorem dual_involutive (t : Tree n) :
    Tree.dual (Tree.dual t) = t := normalize_involutive _ _ _
@[simp] theorem dual_bot : Tree.dual (Tree.bot : Tree n) = Tree.top := by simp [Tree.dual]
@[simp] theorem dual_top : Tree.dual (Tree.top : Tree n) = Tree.bot := by simp [Tree.dual]
@[simp] theorem dual_node (a : Fin n → Tree n) :
    Tree.dual (Tree.node a) = Tree.node (fun i => Tree.dual (a i)) := by simp [Tree.dual]

@[simp] theorem normalize_true (c : Fin n → Bool) (t : Tree n) :
    Tree.normalize c true t = Tree.dual (Tree.normalize c false t) := by
  apply Tree.ext; funext π
  cases h : t.fn π with
  | none => simp [h]
  | some a => cases hp : polarity c π <;> simp [h, hp]

@[simp] theorem dual_le_iff (t u : Tree n) : Tree.dual t ≤ Tree.dual u ↔ u ≤ t := by
  constructor
  · intro h π a b ha hb
    have hh := h π (Sym.flip true b) (Sym.flip true a)
      (by simp [hb]) (by simp [ha])
    exact (Sym.leWithPolarity_iff_flip true b a).mpr hh
  · intro h π a b ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    simpa using (Sym.leWithPolarity_iff_flip true a' b').mp (h π b' a' hb' ha')

/-- The normalization of a finite tree: each leaf is exchanged with its dual when the polarity
`p ⊕ polarity c π` of its path `π` is negative. It represents `Tree.normalize c p`. -/
def FTree.normalize (c : Fin n → Bool) : Bool → FTree n → FTree n
  | p, .bot => if p then .top else .bot
  | p, .top => if p then .bot else .top
  | p, .node a => .node fun i => normalize c (Bool.xor p (c i)) (a i)

@[simp] theorem FTree.toTree_normalize (c : Fin n → Bool) (p : Bool) (t : FTree n) :
    (t.normalize c p).toTree = Tree.normalize c p t.toTree := by
  induction t generalizing p with
  | bot => cases p <;> simp [normalize]
  | top => cases p <;> simp [normalize]
  | node a ih => simp [normalize, ih]

/-- The dual of a finite tree, exchanging `⊥` and `⊤`. It represents `Tree.dual`. -/
def FTree.dual (t : FTree n) : FTree n := t.normalize (fun _ => false) true

@[simp] theorem FTree.toTree_dual (t : FTree n) : t.dual.toTree = Tree.dual t.toTree :=
  FTree.toTree_normalize _ _ _

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics
variable {n : ℕ}
namespace Tree

/-- The `i`-th child of `t`, or `t` itself when `t` is a leaf. -/
def descend (t : Tree n) (i : Fin n) : Tree n :=
  if h : t.fn [] = some Sym.f then t.branch i h else t

@[simp] theorem descend_bot (i : Fin n) : descend Tree.bot i = Tree.bot := by
  simp [descend]

@[simp] theorem descend_top (i : Fin n) : descend Tree.top i = Tree.top := by
  simp [descend]

@[simp] theorem descend_node (a : Fin n → Tree n) (i : Fin n) :
    descend (Tree.node a) i = a i := by
  apply Tree.ext
  funext w
  simp [descend, Tree.branch]

/-- The subtree reached along a path, staying at the first leaf when the path leaves the domain. -/
def trace (t : Tree n) : List (Fin n) → Tree n
  | [] => t
  | i :: ν => trace (descend t i) ν

@[simp] theorem trace_nil (t : Tree n) : trace t [] = t := rfl
@[simp] theorem trace_cons (t : Tree n) (i : Fin n) (ν : List (Fin n)) :
    trace t (i :: ν) = trace (descend t i) ν := rfl
@[simp] theorem trace_bot (ν : List (Fin n)) : trace Tree.bot ν = Tree.bot := by
  induction ν <;> simp_all
@[simp] theorem trace_top (ν : List (Fin n)) : trace Tree.top ν = Tree.top := by
  induction ν <;> simp_all

theorem trace_append (t : Tree n) (ν μ : List (Fin n)) :
    trace t (ν ++ μ) = trace (trace t ν) μ := by
  induction ν generalizing t <;> simp_all

theorem descend_mono {t u : Tree n} (h : t ≤ u) (i : Fin n) :
    descend t i ≤ descend u i := by
  rcases (Tree.le_iff_root_cases _ _).mp h with rfl | rfl |
    ⟨a, b, rfl, rfl, hab⟩
  · simp
  · simp
  · simpa using hab i

theorem trace_mono {t u : Tree n} (h : t ≤ u) (ν : List (Fin n)) :
    trace t ν ≤ trace u ν := by
  induction ν generalizing t u with
  | nil => exact h
  | cons i ν ih => exact ih (descend_mono h i)

/-- Some prefix of the path `ν`, possibly `ν` itself, is in the domain of `t` with label `s`. -/
def HasLabel (t : Tree n) (ν : List (Fin n)) (s : Sym) : Prop :=
  ∃ τ, τ <+: ν ∧ t.fn τ = some s

@[simp] theorem hasLabel_nil (t : Tree n) (s : Sym) :
    HasLabel t [] s ↔ t.fn [] = some s := by simp [HasLabel]

@[simp] theorem hasLabel_bot (ν : List (Fin n)) (s : Sym) :
    HasLabel Tree.bot ν s ↔ s = Sym.bot := by
  constructor
  · rintro ⟨τ, _, h⟩; cases τ <;> simpa using h.symm
  · rintro rfl; exact ⟨[], List.nil_prefix, rfl⟩

@[simp] theorem hasLabel_top (ν : List (Fin n)) (s : Sym) :
    HasLabel Tree.top ν s ↔ s = Sym.top := by
  constructor
  · rintro ⟨τ, _, h⟩; cases τ <;> simpa using h.symm
  · rintro rfl; exact ⟨[], List.nil_prefix, rfl⟩

theorem hasLabel_node_cons (a : Fin n → Tree n) (i : Fin n) (w : List (Fin n))
    (s : Sym) (hs : s ≠ Sym.f) :
    HasLabel (Tree.node a) (i :: w) s ↔ HasLabel (a i) w s := by
  constructor
  · rintro ⟨v, hp, h⟩
    cases v with
    | nil => exact False.elim (hs (Option.some.inj h).symm)
    | cons j v =>
      obtain ⟨z, he⟩ := hp
      have hij : j = i := (List.cons.inj he).1
      subst j
      exact ⟨v, ⟨z, (List.cons.inj he).2⟩, h⟩
  · rintro ⟨v, ⟨z, he⟩, h⟩
    exact ⟨i :: v, ⟨z, by simp [he]⟩, h⟩

theorem trace_eq_bot_iff (t : Tree n) (ν : List (Fin n)) :
    trace t ν = Tree.bot ↔ HasLabel t ν Sym.bot := by
  induction ν generalizing t with
  | nil => simp
  | cons i ν ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · rw [trace_cons, descend_node, ih, hasLabel_node_cons _ _ _ _ (by decide)]

theorem trace_eq_top_iff (t : Tree n) (ν : List (Fin n)) :
    trace t ν = Tree.top ↔ HasLabel t ν Sym.top := by
  induction ν generalizing t with
  | nil => simp
  | cons i ν ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · rw [trace_cons, descend_node, ih, hasLabel_node_cons _ _ _ _ (by decide)]

/-- If `ν` is labeled `a`, no prefix of `ν` carries a leaf label `s` other than `a`. -/
theorem not_hasLabel_of_label {t : Tree n} {ν : List (Fin n)} {a s : Sym}
    (h : t.fn ν = some a) (hs : s ≠ Sym.f) (ha : a ≠ s) : ¬ HasLabel t ν s := by
  rintro ⟨τ, hp, ht⟩
  by_cases he : τ = ν
  · subst τ; exact ha (Option.some.inj (h.symm.trans ht))
  · have hf := t.label_eq_f_of_proper_prefix hp he (by simp [h])
    exact hs (Option.some.inj (ht.symm.trans hf))

/-- `t ≤ u` fails exactly when some path leads `t` to a tree other than `⊥` and `u` to `⊥`, or
leads `t` to `⊤` and `u` to a tree other than `⊤`. -/
theorem not_le_iff_unsafe (t u : Tree n) :
    ¬ t ≤ u ↔ ∃ ν, (trace t ν ≠ Tree.bot ∧ trace u ν = Tree.bot) ∨
      (trace t ν = Tree.top ∧ trace u ν ≠ Tree.top) := by
  classical
  constructor
  · intro h
    change ¬ (∀ ν a b, t.fn ν = some a → u.fn ν = some b → a ≤ b) at h
    push Not at h
    obtain ⟨ν, a, b, ht, hu, hab⟩ := h
    have hc : (b = Sym.bot ∧ a ≠ Sym.bot) ∨ (a = Sym.top ∧ b ≠ Sym.top) := by
      cases a <;> cases b <;> first
        | exact Or.inl ⟨rfl, by decide⟩
        | exact Or.inr ⟨rfl, by decide⟩
        | exact absurd hab (by decide)
    refine ⟨ν, ?_⟩
    rcases hc with ⟨rfl, ha⟩ | ⟨rfl, hb⟩
    · exact Or.inl ⟨fun h => not_hasLabel_of_label ht (by decide) ha
        ((trace_eq_bot_iff _ _).mp h),
        (trace_eq_bot_iff _ _).mpr ⟨ν, List.prefix_refl _, hu⟩⟩
    · exact Or.inr ⟨(trace_eq_top_iff _ _).mpr ⟨ν, List.prefix_refl _, ht⟩,
        fun h => not_hasLabel_of_label hu (by decide) hb ((trace_eq_top_iff _ _).mp h)⟩
  · rintro ⟨ν, h⟩ hle
    have hm := trace_mono hle ν
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hy] at hm; exact hx ((Tree.le_bot_iff _).mp hm)
    · rw [hx] at hm; exact hy ((Tree.top_le_iff _).mp hm)

end Tree

/-- `t ≤ u` in the covariant order exactly when along every path, `u` reaches `⊤` whenever `t`
does and `t` reaches `⊥` whenever `u` does. -/
theorem le_iff_forall_hasLabel (t u : Tree n) :
    t ≤ u ↔ ∀ π, (t.HasLabel π .top → u.HasLabel π .top) ∧
      (u.HasLabel π .bot → t.HasLabel π .bot) := by
  have h := Tree.not_le_iff_unsafe t u
  simp only [ne_eq, Tree.trace_eq_bot_iff, Tree.trace_eq_top_iff] at h
  classical
  constructor
  · intro hle π
    constructor
    · intro ht
      by_contra hu
      exact (h.mpr ⟨π, Or.inr ⟨ht, hu⟩⟩) hle
    · intro hu
      by_contra ht
      exact (h.mpr ⟨π, Or.inl ⟨ht, hu⟩⟩) hle
  · intro hs
    by_contra hn
    obtain ⟨π, ⟨ht, hu⟩ | ⟨ht, hu⟩⟩ := h.mp hn
    · exact ht ((hs π).2 hu)
    · exact hu ((hs π).1 ht)

end DeciSigma1.Semantics

namespace DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

/-- The subtype order with variance `c`: at every path in both domains, the labels are ordered by
`⊥ < f < ⊤`, reversed at paths of negative polarity. -/
def Tree.Le (c : Fin n → Bool) (t u : Tree n) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → if polarity c π then b ≤ a else a ≤ b

/-- The order with variance `c` is the covariant order on normalizations. -/
theorem treeLe_iff_normalize (c : Fin n → Bool) (t u : Tree n) :
    Le c t u ↔ Tree.normalize c false t ≤ Tree.normalize c false u := by
  constructor
  · intro h π a b ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    simpa using (Sym.leWithPolarity_iff_flip (polarity c π) a' b').mp (h π a' b' ha' hb')
  · intro h π a b ha hb
    apply (Sym.leWithPolarity_iff_flip (polarity c π) a b).mpr
    exact h π _ _ (by simp [ha]) (by simp [hb])

@[simp] theorem treeLe_false_iff_le (t u : Tree n) :
    Le (fun _ => false) t u ↔ t ≤ u := by rw [treeLe_iff_normalize]; simp

theorem treeLe_refl (c : Fin n → Bool) (t : Tree n) : Le c t t :=
  (treeLe_iff_normalize c t t).mpr le_rfl

theorem treeLe_antisymm {c : Fin n → Bool} {t u : Tree n}
    (htu : Le c t u) (hut : Le c u t) : t = u :=
  normalize_injective c false (_root_.le_antisymm ((treeLe_iff_normalize c t u).mp htu)
    ((treeLe_iff_normalize c u t).mp hut))

theorem normalize_le_normalize_iff (c : Fin n → Bool) (p : Bool) (t u : Tree n) :
    Tree.normalize c p t ≤ Tree.normalize c p u ↔ if p then Le c u t else Le c t u := by
  cases p <;> simp [treeLe_iff_normalize]

@[simp] theorem bot_treeLe (c : Fin n → Bool) (t : Tree n) : Le c bot t := by
  rw [treeLe_iff_normalize]; simp
@[simp] theorem treeLe_top (c : Fin n → Bool) (t : Tree n) : Le c t top := by
  rw [treeLe_iff_normalize]; simp
@[simp] theorem treeLe_bot_iff (c : Fin n → Bool) (t : Tree n) : Le c t bot ↔ t = bot :=
  ⟨fun h => treeLe_antisymm h (bot_treeLe c t), fun h => h ▸ treeLe_refl c bot⟩
@[simp] theorem top_treeLe_iff (c : Fin n → Bool) (t : Tree n) : Le c top t ↔ t = top :=
  ⟨fun h => treeLe_antisymm (treeLe_top c t) h, fun h => h ▸ treeLe_refl c top⟩

@[simp] theorem node_treeLe_node_iff (c : Fin n → Bool) (a b : Fin n → Tree n) :
    Le c (node a) (node b) ↔ ∀ i, if c i then Le c (b i) (a i) else Le c (a i) (b i) := by
  rw [treeLe_iff_normalize]
  simp only [normalize_node, Bool.false_xor, node_le_node_iff, normalize_le_normalize_iff]

end DeciSigma1.Semantics
