/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.InverseSystems.Omega1
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Types.Basic

/-!
# An Aronszajn tree of bounded increasing rational sequences (Construction 4.3)

Following Jech [Je, proof of Theorem 9.16], we construct by recursion on `α < ω₁` countable
sets `T_α` of strictly increasing bounded sequences of rationals of length `α`. A node of level
`α` is modelled as a function `ω₁ → ℚ` vanishing from `α` on.

* `T_α = {∅}` for the least `α`;
* `T_{γ+1}` consists of the extensions of nodes `f ∈ T_γ` by one value `p > f`;
* for a limit `α`, `T_α` consists of the limits of chains through a cofinal sequence of levels,
  starting at a node `f ∈ T_β` below `a` and staying below rationals increasing to `b > a`.

By induction, every level is countable, closed under restriction, and has the extension
property (9.10): every node of level `β ≤ α` bounded by `a < q` extends to a node of level `α`
bounded by some `a' < q`. A compatible family would give a strictly increasing map `ω₁ → ℚ`,
which is impossible, so the inverse limit of the levels is empty.
-/

@[expose] public section

namespace ExtriangulatedRealization

namespace Aronszajn

open Omega1 Ordinal

universe u

/-! ### Nodes -/

/-- The restriction of a node to the levels below `α`. -/
noncomputable def restr (α : Omega1.{u}) (f : Omega1.{u} → ℚ) : Omega1.{u} → ℚ :=
  fun ξ => if ξ < α then f ξ else 0

lemma restr_of_lt {α ξ : Omega1.{u}} (h : ξ < α) (f : Omega1.{u} → ℚ) : restr α f ξ = f ξ := by
  simp [restr, h]

lemma restr_of_not_lt {α ξ : Omega1.{u}} (h : ¬ ξ < α) (f : Omega1.{u} → ℚ) : restr α f ξ = 0 := by
  simp [restr, h]

lemma restr_restr {β α : Omega1.{u}} (h : β ≤ α) (f : Omega1.{u} → ℚ) :
    restr β (restr α f) = restr β f := by
  funext ξ
  by_cases hξ : ξ < β
  · rw [restr_of_lt hξ, restr_of_lt hξ, restr_of_lt (hξ.trans_le h)]
  · rw [restr_of_not_lt hξ, restr_of_not_lt hξ]

/-- The extension of a node of level `γ` by the value `p` at `γ`. -/
noncomputable def extend (γ : Omega1.{u}) (f : Omega1.{u} → ℚ) (p : ℚ) : Omega1.{u} → ℚ :=
  fun ξ => if ξ < γ then f ξ else if ξ = γ then p else 0

/-- All values of a node below level `α` are less than `q`. -/
def Below (α : Omega1.{u}) (f : Omega1.{u} → ℚ) (q : ℚ) : Prop := ∀ ξ, ξ < α → f ξ < q

lemma Below.mono {α : Omega1.{u}} {f : Omega1.{u} → ℚ} {q q' : ℚ} (h : Below α f q)
    (hq : q ≤ q') : Below α f q' :=
  fun ξ hξ => (h ξ hξ).trans_le hq

/-! ### Cofinal sequences below limit levels -/

/-- A monotone sequence of levels below `α`, cofinal in `α`. -/
def IsCofinalSeq (α : Omega1.{u}) (e : ℕ → Omega1.{u}) : Prop :=
  (∀ n, e n < α) ∧ Monotone e ∧ ∀ δ, δ < α → ∃ n, δ < e n

lemma exists_cofinalSeq {α : Omega1.{u}} (hne : ∃ δ, δ < α)
    (hlim : ∀ δ, δ < α → ∃ δ', δ < δ' ∧ δ' < α) : ∃ e, IsCofinalSeq α e := by
  obtain ⟨δ₀, hδ₀⟩ := hne
  obtain ⟨a, ha⟩ := (countable_Iio α).exists_eq_range ⟨δ₀, hδ₀⟩
  have haα : ∀ n, a n < α := fun n => by
    have : a n ∈ Set.range a := ⟨n, rfl⟩
    rw [← ha] at this
    exact this
  let e : ℕ → Omega1.{u} := fun n =>
    (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr n.succ_pos⟩ a
  refine ⟨e, fun n => (Finset.sup'_lt_iff _).mpr fun m _ => haα m,
    fun n n' h => Finset.sup'_mono _ (Finset.range_subset_range.mpr (Nat.succ_le_succ h)) _,
    fun δ hδ => ?_⟩
  obtain ⟨δ', h1, h2⟩ := hlim δ hδ
  have : δ' ∈ Set.range a := by
    rw [← ha]
    exact h2
  obtain ⟨n, rfl⟩ := this
  exact ⟨n, h1.trans_le (Finset.le_sup' a (Finset.mem_range.mpr n.lt_succ_self))⟩

open Classical in
/-- A chosen cofinal sequence below `α` (meaningful when `α` is a limit). -/
noncomputable def cofSeq (α : Omega1.{u}) : ℕ → Omega1.{u} :=
  if h : ∃ e, IsCofinalSeq α e then h.choose else fun _ => α

/-- The levels of a chain from `β` towards `α`. -/
noncomputable def chainLevel (α β : Omega1.{u}) : ℕ → Omega1.{u}
  | 0 => β
  | n + 1 => β ⊔ cofSeq α n

/-- Rational bounds increasing from `a` towards `b`. -/
def chainBound (a b : ℚ) (n : ℕ) : ℚ := b - (b - a) / 2 ^ n

lemma chainBound_zero (a b : ℚ) : chainBound a b 0 = a := by simp [chainBound]

lemma chainBound_lt_succ {a b : ℚ} (hab : a < b) (n : ℕ) :
    chainBound a b n < chainBound a b (n + 1) := by
  have h : 0 < (b - a) / 2 ^ (n + 1) := by have := sub_pos.mpr hab; positivity
  have h2 : (b - a) / 2 ^ n = 2 * ((b - a) / 2 ^ (n + 1)) := by
    rw [pow_succ]
    ring
  rw [chainBound, chainBound, h2]
  linarith

lemma chainBound_lt {a b : ℚ} (hab : a < b) (n : ℕ) : chainBound a b n < b := by
  have h : 0 < (b - a) / 2 ^ n := by have := sub_pos.mpr hab; positivity
  rw [chainBound]
  linarith

open Classical in
/-- A chain of nodes through the levels `chainLevel α β n`, each extending the previous one and
bounded by `chainBound a b n`, chosen from the levels `T`. -/
noncomputable def chain (α : Omega1.{u}) (T : Omega1.{u} → Set (Omega1.{u} → ℚ))
    (β : Omega1.{u}) (f : Omega1.{u} → ℚ) (a b : ℚ) :
    ℕ → (Omega1.{u} → ℚ)
  | 0 => f
  | n + 1 =>
    if h : ∃ g ∈ T (chainLevel α β (n + 1)), restr (chainLevel α β n) g = chain α T β f a b n ∧
        Below (chainLevel α β (n + 1)) g (chainBound a b (n + 1)) then h.choose else 0

open Classical in
/-- The limit of the chain, a node of level `α`. -/
noncomputable def limitWitness (α : Omega1.{u}) (T : Omega1.{u} → Set (Omega1.{u} → ℚ))
    (β : Omega1.{u}) (f : Omega1.{u} → ℚ) (a b : ℚ) :
    Omega1.{u} → ℚ :=
  fun ξ => if h : ξ < α ∧ ∃ n, ξ < chainLevel α β n then chain α T β f a b (Nat.find h.2) ξ else 0

/-! ### The levels -/

/-- One step of the recursion: the level `α` from the lower levels. -/
noncomputable def treeStep (α : Omega1.{u}) (rec : ∀ β, β < α → Set (Omega1.{u} → ℚ)) :
    Set (Omega1.{u} → ℚ) := by
  classical
  let T : Omega1.{u} → Set (Omega1.{u} → ℚ) := fun β => if h : β < α then rec β h else ∅
  exact if hs : ∃ γ, γ < α ∧ ∀ δ, δ < α → δ ≤ γ then
      {g | ∃ f ∈ T hs.choose, ∃ p : ℚ, Below hs.choose f p ∧ g = extend hs.choose f p}
    else if ∃ δ, δ < α then
      {g | ∃ β, β < α ∧ ∃ f ∈ T β, ∃ a b : ℚ, Below β f a ∧ a < b ∧
        g = limitWitness α T β f a b}
    else {0}

/-- The levels `T_α` of the tree. -/
noncomputable def tree : Omega1.{u} → Set (Omega1.{u} → ℚ) := wellFounded_lt.fix treeStep

lemma tree_eq (α : Omega1.{u}) : tree α = treeStep α (fun β _ => tree β) :=
  wellFounded_lt.fix_eq _ _

/-- The lower levels, as seen from level `α`. -/
noncomputable def treeBelow (α β : Omega1.{u}) : Set (Omega1.{u} → ℚ) :=
  if _ : β < α then tree β else ∅

lemma treeBelow_of_lt {α β : Omega1.{u}} (h : β < α) : treeBelow α β = tree β := by
  simp [treeBelow, h]

lemma tree_of_isMin {α : Omega1.{u}} (hmin : ¬ ∃ δ, δ < α) : tree α = {0} := by
  have hs : ¬ ∃ γ, γ < α ∧ ∀ δ, δ < α → δ ≤ γ := fun ⟨γ, hγ, _⟩ => hmin ⟨γ, hγ⟩
  rw [tree_eq, treeStep]
  simp only [hs, hmin, ↓reduceDIte, ↓reduceIte]

lemma mem_tree_succ {α γ : Omega1.{u}} (hγ : γ < α) (hmax : ∀ δ, δ < α → δ ≤ γ)
    {g : Omega1.{u} → ℚ} :
    g ∈ tree α ↔ ∃ f ∈ tree γ, ∃ p : ℚ, Below γ f p ∧ g = extend γ f p := by
  have hs : ∃ γ, γ < α ∧ ∀ δ, δ < α → δ ≤ γ := ⟨γ, hγ, hmax⟩
  have hc : hs.choose = γ :=
    le_antisymm (hmax _ hs.choose_spec.1) (hs.choose_spec.2 γ hγ)
  rw [tree_eq, treeStep]
  simp only [hs, ↓reduceDIte]
  rw [hc]
  simp only [Set.mem_ofPred_eq, hγ, ↓reduceDIte]

lemma mem_tree_limit {α : Omega1.{u}} (hne : ∃ δ, δ < α) (hs : ¬ ∃ γ, γ < α ∧ ∀ δ, δ < α → δ ≤ γ)
    {g : Omega1.{u} → ℚ} :
    g ∈ tree α ↔ ∃ β, β < α ∧ ∃ f ∈ tree β, ∃ a b : ℚ, Below β f a ∧ a < b ∧
      g = limitWitness α (treeBelow α) β f a b := by
  rw [tree_eq, treeStep]
  simp only [hs, hne, ↓reduceDIte, ↓reduceIte, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨β, hβ, f, hf, a, b, h1, h2, rfl⟩
    refine ⟨β, hβ, f, by simpa [hβ] using hf, a, b, h1, h2, rfl⟩
  · rintro ⟨β, hβ, f, hf, a, b, h1, h2, rfl⟩
    exact ⟨β, hβ, f, by simpa [hβ] using hf, a, b, h1, h2, rfl⟩


/-! ### The invariants -/

/-- The invariants of the level `α`: nodes vanish from `α` on, are strictly increasing and
bounded below `α`; the levels are closed under restriction, have the extension property (9.10),
and are countable. -/
structure Good (α : Omega1.{u}) : Prop where
  restr_self : ∀ f ∈ tree α, restr α f = f
  strictMono : ∀ f ∈ tree α, ∀ ξ η, ξ < η → η < α → f ξ < f η
  bdd : ∀ f ∈ tree α, ∃ q, Below α f q
  closed : ∀ f ∈ tree α, ∀ β, β ≤ α → restr β f ∈ tree β
  ext : ∀ β, β ≤ α → ∀ f ∈ tree β, ∀ a q : ℚ, Below β f a → a < q →
    ∃ g ∈ tree α, restr β g = f ∧ ∃ a', a' < q ∧ Below α g a'
  countable : (tree α).Countable

section Chain

variable {α β : Omega1.{u}} (hα : IsCofinalSeq α (cofSeq α))
include hα

lemma chainLevel_lt (hβ : β < α) (n : ℕ) : chainLevel α β n < α := by
  cases n with
  | zero => exact hβ
  | succ n => exact sup_lt_iff.mpr ⟨hβ, hα.1 n⟩

lemma chainLevel_mono : Monotone (chainLevel α β) := by
  refine monotone_nat_of_le_succ fun n => ?_
  cases n with
  | zero => exact le_sup_left
  | succ n => exact sup_le_sup_left (hα.2.1 n.le_succ) β

lemma exists_lt_chainLevel {ξ : Omega1.{u}} (hξ : ξ < α) : ∃ n, ξ < chainLevel α β n := by
  obtain ⟨n, hn⟩ := hα.2.2 ξ hξ
  exact ⟨n + 1, hn.trans_le le_sup_right⟩

variable {f : Omega1.{u} → ℚ} {a b : ℚ} (hβ : β < α) (hf : f ∈ tree β) (hfa : Below β f a)
  (hab : a < b) (ih : ∀ γ, γ < α → Good γ)
include hβ hf hfa hab ih

/-- The chain through the levels stays in the tree, below the bounds, and each node restricts
to the previous one. -/
lemma chain_spec (n : ℕ) :
    (chain α (treeBelow α) β f a b n ∈ tree (chainLevel α β n) ∧
      Below (chainLevel α β n) (chain α (treeBelow α) β f a b n) (chainBound a b n)) ∧
    restr (chainLevel α β n) (chain α (treeBelow α) β f a b (n + 1)) =
      chain α (treeBelow α) β f a b n := by
  have hex : ∀ n, (chain α (treeBelow α) β f a b n ∈ tree (chainLevel α β n) ∧
      Below (chainLevel α β n) (chain α (treeBelow α) β f a b n) (chainBound a b n)) →
      ∃ g ∈ treeBelow α (chainLevel α β (n + 1)),
        restr (chainLevel α β n) g = chain α (treeBelow α) β f a b n ∧
        Below (chainLevel α β (n + 1)) g (chainBound a b (n + 1)) := by
    rintro n ⟨h1, h2⟩
    obtain ⟨g, hg, hgr, a', ha', hga'⟩ := (ih _ (chainLevel_lt hα hβ (n + 1))).ext _
      (chainLevel_mono hα n.le_succ) _ h1 _ _ h2 (chainBound_lt_succ hab n)
    exact ⟨g, by rwa [treeBelow_of_lt (chainLevel_lt hα hβ (n + 1))], hgr, hga'.mono ha'.le⟩
  have hstep : ∀ n (h : ∃ g ∈ treeBelow α (chainLevel α β (n + 1)),
      restr (chainLevel α β n) g = chain α (treeBelow α) β f a b n ∧
        Below (chainLevel α β (n + 1)) g (chainBound a b (n + 1))),
      chain α (treeBelow α) β f a b (n + 1) = h.choose := fun n h => by
    rw [chain, dite_eq_left h]
  have hP : ∀ n, chain α (treeBelow α) β f a b n ∈ tree (chainLevel α β n) ∧
      Below (chainLevel α β n) (chain α (treeBelow α) β f a b n) (chainBound a b n) := by
    intro n
    induction n with
    | zero => exact ⟨hf, by rw [chainBound_zero]; exact hfa⟩
    | succ n ihn =>
      have h := hex n ihn
      rw [hstep n h]
      obtain ⟨hmem, -, hbelow⟩ := h.choose_spec
      have e := treeBelow_of_lt (chainLevel_lt hα hβ (n + 1))
      exact ⟨e ▸ hmem, hbelow⟩
  refine ⟨hP n, ?_⟩
  have h := hex n (hP n)
  rw [hstep n h]
  exact h.choose_spec.2.1

lemma chain_restr {n m : ℕ} (hnm : n ≤ m) :
    restr (chainLevel α β n) (chain α (treeBelow α) β f a b m) =
      chain α (treeBelow α) β f a b n := by
  induction hnm with
  | refl =>
    exact (ih _ (chainLevel_lt hα hβ n)).restr_self _
      (chain_spec hα hβ hf hfa hab ih n).1.1
  | step hle ihm =>
    rw [← restr_restr (chainLevel_mono hα hle),
      (chain_spec hα hβ hf hfa hab ih _).2, ihm]

lemma limitWitness_apply {ξ : Omega1.{u}} {n : ℕ} (hξ : ξ < chainLevel α β n) :
    limitWitness α (treeBelow α) β f a b ξ = chain α (treeBelow α) β f a b n ξ := by
  classical
  have hξα : ξ < α := hξ.trans (chainLevel_lt hα hβ n)
  have hex : ∃ m, ξ < chainLevel α β m := ⟨n, hξ⟩
  have hlw : limitWitness α (treeBelow α) β f a b ξ =
      chain α (treeBelow α) β f a b (Nat.find hex) ξ := by
    rw [limitWitness, dite_eq_left ⟨hξα, hex⟩]
  rw [hlw, ← chain_restr hα hβ hf hfa hab ih (Nat.find_min' hex hξ),
    restr_of_lt (Nat.find_spec hex)]

lemma restr_limitWitness (n : ℕ) :
    restr (chainLevel α β n) (limitWitness α (treeBelow α) β f a b) =
      chain α (treeBelow α) β f a b n := by
  funext ξ
  by_cases hξ : ξ < chainLevel α β n
  · rw [restr_of_lt hξ, limitWitness_apply hα hβ hf hfa hab ih hξ]
  · rw [restr_of_not_lt hξ, ← (ih _ (chainLevel_lt hα hβ n)).restr_self _
      (chain_spec hα hβ hf hfa hab ih n).1.1, restr_of_not_lt hξ]

end Chain


/-- **Construction 4.3**: every level satisfies the invariants. -/
theorem good (α : Omega1.{u}) : Good α := by
  refine WellFoundedLT.induction α fun α ih => ?_
  by_cases hne : ∃ δ, δ < α
  swap
  · have ht := tree_of_isMin hne
    have hle : ∀ β, β ≤ α → β = α := fun β hβ =>
      hβ.eq_or_lt.resolve_right fun h => hne ⟨β, h⟩
    have h0 : ∀ f ∈ tree α, f = 0 := fun f hf => by rw [ht] at hf; exact hf
    have hr0 : restr α 0 = 0 := by funext ξ; simp [restr]
    refine ⟨fun f hf => by rw [h0 f hf, hr0], fun f _ ξ η _ hη => absurd ⟨η, hη⟩ hne,
      fun f _ => ⟨0, fun ξ hξ => absurd ⟨ξ, hξ⟩ hne⟩, fun f hf β hβ => ?_,
      fun β hβ f hf a q hfa haq => ?_, by rw [ht]; exact Set.countable_singleton 0⟩
    · obtain rfl := hle β hβ
      rw [h0 f hf, hr0, ht]
      rfl
    · obtain rfl := hle β hβ
      exact ⟨f, hf, by rw [h0 f hf, hr0], a, haq, hfa⟩
  by_cases hs : ∃ γ, γ < α ∧ ∀ δ, δ < α → δ ≤ γ
  · obtain ⟨γ, hγ, hmax⟩ := hs
    have hlt : ∀ ξ, ξ < α ↔ ξ ≤ γ := fun ξ => ⟨hmax ξ, fun h => h.trans_lt hγ⟩
    have ihγ := ih γ hγ
    have hmem := fun {g} => mem_tree_succ (g := g) hγ hmax
    have hex_lt : ∀ f p ξ, ξ < γ → extend γ f p ξ = f ξ := fun f p ξ h => by
      simp [extend, h]
    have hex_eq : ∀ f p, extend γ f p γ = p := fun f p => by simp [extend]
    have hex_gt : ∀ f p ξ, γ < ξ → extend γ f p ξ = 0 := fun f p ξ h => by
      simp [extend, not_lt.mpr h.le, h.ne']
    have hrestr_ext : ∀ f p β, β ≤ γ → restr β (extend γ f p) = restr β f := fun f p β hβ => by
      funext ξ
      by_cases h : ξ < β
      · rw [restr_of_lt h, restr_of_lt h, hex_lt _ _ _ (h.trans_le hβ)]
      · rw [restr_of_not_lt h, restr_of_not_lt h]
    have hA : ∀ g ∈ tree α, restr α g = g := by
      intro g hg
      obtain ⟨f, hf, p, hfp, rfl⟩ := hmem.mp hg
      funext ξ
      by_cases h : ξ < α
      · rw [restr_of_lt h]
      · rw [restr_of_not_lt h, hex_gt _ _ _ (not_le.mp fun h' => h ((hlt ξ).mpr h'))]
    refine ⟨hA, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg ξ η hξη hη
      obtain ⟨f, hf, p, hfp, rfl⟩ := hmem.mp hg
      rcases ((hlt η).mp hη).lt_or_eq with h | rfl
      · rw [hex_lt _ _ _ (hξη.trans h), hex_lt _ _ _ h]
        exact ihγ.strictMono f hf ξ η hξη h
      · rw [hex_lt _ _ _ hξη, hex_eq]
        exact hfp ξ hξη
    · intro g hg
      obtain ⟨f, hf, p, hfp, rfl⟩ := hmem.mp hg
      refine ⟨p + 1, fun ξ hξ => ?_⟩
      rcases ((hlt ξ).mp hξ).lt_or_eq with h | rfl
      · rw [hex_lt _ _ _ h]
        linarith [hfp ξ h]
      · rw [hex_eq]
        linarith
    · intro g hg β hβ
      rcases hβ.lt_or_eq with h | rfl
      · obtain ⟨f, hf, p, hfp, rfl⟩ := hmem.mp hg
        rw [hrestr_ext _ _ _ ((hlt β).mp h)]
        exact ihγ.closed f hf β ((hlt β).mp h)
      · rw [hA g hg]
        exact hg
    · intro β hβ f hf a q hfa haq
      rcases hβ.lt_or_eq with h | rfl
      · obtain ⟨h₀, hh₀, hr, a', ha', hba'⟩ := ihγ.ext β ((hlt β).mp h) f hf a q hfa haq
        refine ⟨extend γ h₀ ((a' + q) / 2),
          hmem.mpr ⟨h₀, hh₀, (a' + q) / 2, hba'.mono (by linarith), rfl⟩, ?_,
          ((a' + q) / 2 + q) / 2, by linarith, ?_⟩
        · rw [hrestr_ext _ _ _ ((hlt β).mp h), hr]
        · intro ξ hξ
          rcases ((hlt ξ).mp hξ).lt_or_eq with h' | rfl
          · rw [hex_lt _ _ _ h']
            linarith [hba' ξ h']
          · rw [hex_eq]
            linarith
      · exact ⟨f, hf, hA f hf, a, haq, hfa⟩
    · have hsub : tree α ⊆
          (fun x : (Omega1.{u} → ℚ) × ℚ => extend γ x.1 x.2) '' (tree γ ×ˢ Set.univ) := by
        intro g hg
        obtain ⟨f, hf, p, -, rfl⟩ := hmem.mp hg
        exact ⟨(f, p), ⟨hf, trivial⟩, rfl⟩
      exact ((ihγ.countable.prod Set.countable_univ).image _).mono hsub
  · have hlim : ∀ δ, δ < α → ∃ δ', δ < δ' ∧ δ' < α := fun δ hδ => by
      by_contra h
      push Not at h
      exact hs ⟨δ, hδ, fun δ' hδ' => not_lt.mp fun hlt => not_le.mpr hδ' (h δ' hlt)⟩
    have hcof : IsCofinalSeq α (cofSeq α) := by
      have hex := exists_cofinalSeq hne hlim
      rw [cofSeq, dite_eq_left hex]
      exact hex.choose_spec
    have hmem := fun {g} => mem_tree_limit (α := α) (g := g) hne hs
    have hA : ∀ g ∈ tree α, restr α g = g := by
      intro g hg
      obtain ⟨β, hβ, f, hf, a, b, hfa, hab, rfl⟩ := hmem.mp hg
      funext ξ
      by_cases h : ξ < α
      · rw [restr_of_lt h]
      · rw [restr_of_not_lt h, limitWitness, dite_eq_right fun h' => h h'.1]
    refine ⟨hA, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg ξ η hξη hη
      obtain ⟨β, hβ, f, hf, a, b, hfa, hab, rfl⟩ := hmem.mp hg
      obtain ⟨n, hn⟩ := exists_lt_chainLevel hcof (β := β) hη
      rw [limitWitness_apply hcof hβ hf hfa hab ih (hξη.trans hn),
        limitWitness_apply hcof hβ hf hfa hab ih hn]
      exact (ih _ (chainLevel_lt hcof hβ n)).strictMono _
        (chain_spec hcof hβ hf hfa hab ih n).1.1 ξ η hξη hn
    · intro g hg
      obtain ⟨β, hβ, f, hf, a, b, hfa, hab, rfl⟩ := hmem.mp hg
      refine ⟨b, fun ξ hξ => ?_⟩
      obtain ⟨n, hn⟩ := exists_lt_chainLevel hcof (β := β) hξ
      rw [limitWitness_apply hcof hβ hf hfa hab ih hn]
      exact ((chain_spec hcof hβ hf hfa hab ih n).1.2 ξ hn).trans (chainBound_lt hab n)
    · intro g hg β' hβ'
      rcases hβ'.lt_or_eq with h | rfl
      · obtain ⟨β, hβ, f, hf, a, b, hfa, hab, rfl⟩ := hmem.mp hg
        obtain ⟨n, hn⟩ := exists_lt_chainLevel hcof (β := β) h
        rw [← restr_restr hn.le, restr_limitWitness hcof hβ hf hfa hab ih n]
        exact (ih _ (chainLevel_lt hcof hβ n)).closed _ (chain_spec hcof hβ hf hfa hab ih n).1.1
          β' hn.le
      · rw [hA g hg]
        exact hg
    · intro β hβ f hf a q hfa haq
      rcases hβ.lt_or_eq with h | rfl
      · have hab : a < (a + q) / 2 := by linarith
        refine ⟨limitWitness α (treeBelow α) β f a ((a + q) / 2),
          hmem.mpr ⟨β, h, f, hf, a, _, hfa, hab, rfl⟩, ?_, (a + q) / 2, by linarith, ?_⟩
        · exact restr_limitWitness hcof h hf hfa hab ih 0
        · intro ξ hξ
          obtain ⟨n, hn⟩ := exists_lt_chainLevel hcof (β := β) hξ
          rw [limitWitness_apply hcof h hf hfa hab ih hn]
          exact ((chain_spec hcof h hf hfa hab ih n).1.2 ξ hn).trans (chainBound_lt hab n)
      · exact ⟨f, hf, hA f hf, a, haq, hfa⟩
    · have hsub : tree α ⊆ ⋃ β ∈ Set.Iio α, ⋃ f ∈ tree β, ⋃ a : ℚ, ⋃ b : ℚ,
          {limitWitness α (treeBelow α) β f a b} := by
        intro g hg
        obtain ⟨β, hβ, f, hf, a, b, -, -, rfl⟩ := hmem.mp hg
        simp only [Set.mem_iUnion]
        exact ⟨β, hβ, f, hf, a, b, rfl⟩
      exact Set.Countable.mono hsub ((countable_Iio α).biUnion fun β hβ =>
        (ih β hβ).countable.biUnion fun f _ => Set.countable_iUnion fun a =>
          Set.countable_iUnion fun b => Set.countable_singleton _)


/-! ### The inverse system of levels -/

open CategoryTheory Opposite

/-- The inverse system of the levels `T_α`, with restriction maps. -/
noncomputable def system : (Omega1.{u})ᵒᵖ ⥤ Type u where
  obj α := tree α.unop
  map {α β} h := TypeCat.ofHom fun f =>
    ⟨restr β.unop f.1, (good α.unop).closed f.1 f.2 β.unop (leOfHom h.unop)⟩
  map_id α := by
    ext f x
    exact congrFun ((good α.unop).restr_self f.1 f.2) x
  map_comp {α β γ} h h' := by
    ext f x
    exact congrFun (restr_restr (leOfHom h'.unop) f.1).symm x

lemma system_map_val {a b : Omega1.{u}} (h : a ≤ b) (f : system.obj (op b)) :
    (system.map (homOfLE h).op f).1 = restr a f.1 := rfl

/-- The transition maps of the tree are surjective (every node extends to every higher level). -/
lemma system_map_surjective {a b : Omega1.{u}} (h : a ≤ b) :
    Function.Surjective (system.map (homOfLE h).op) := by
  intro f
  obtain ⟨q, hq⟩ := (good a).bdd f.1 f.2
  obtain ⟨g, hg, hgr, -⟩ := (good b).ext a h f.1 f.2 q (q + 1) hq (lt_add_one q)
  exact ⟨⟨g, hg⟩, Subtype.ext hgr⟩

/-- The levels are countable. -/
lemma countable_system_obj (a : Omega1.{u}) : Countable (system.obj (op a)) :=
  (good a).countable.to_subtype

/-- The least level is `{∅}`. -/
lemma zero_mem_tree_bot : (0 : Omega1.{u} → ℚ) ∈ tree (Omega1.ofOrd 0 (omega_pos 1)) := by
  have hmin : ¬ ∃ δ, δ < Omega1.ofOrd.{u} 0 (omega_pos 1) := by
    rintro ⟨δ, hδ⟩
    have := ord_strictMono hδ
    rw [ord_ofOrd] at this
    exact absurd this (by simp)
  rw [tree_of_isMin hmin]
  rfl

/-- **Construction 4.3**: there is no compatible family of nodes, since it would give a strictly
increasing map `ω₁ → ℚ`. -/
theorem system_no_branch :
    ¬ ∃ s : ∀ i, system.obj (op i), ∀ {a b : Omega1.{u}} (h : a ≤ b),
      system.map (homOfLE h).op (s b) = s a := by
  rintro ⟨s, hs⟩
  choose up hup using Omega1.exists_gt.{u}
  have hval : ∀ {a b : Omega1.{u}} (h : a ≤ b) {ξ}, ξ < a → (s b).1 ξ = (s a).1 ξ := by
    intro a b h ξ hξ
    rw [← hs h, system_map_val, restr_of_lt hξ]
  let B : Omega1.{u} → ℚ := fun ξ => (s (up ξ)).1 ξ
  have hB : ∀ ξ α, ξ < α → (s α).1 ξ = B ξ := fun ξ α hξα => by
    rw [← hval (le_sup_left : α ≤ α ⊔ up ξ) hξα, hval (le_sup_right : up ξ ≤ α ⊔ up ξ) (hup ξ)]
  have hmono : StrictMono B := fun ξ η hξη => by
    rw [← hB ξ (up η) (hξη.trans (hup η)), ← hB η (up η) (hup η)]
    exact (good (up η)).strictMono _ (s (up η)).2 ξ η hξη (hup η)
  exact Omega1.not_countable (hmono.injective.countable)

end Aronszajn

end ExtriangulatedRealization
