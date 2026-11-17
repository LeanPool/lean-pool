/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.GMove


/-!
# Chunks: Lemmas C1 and C2 (`docs/PROOF.md` §4.3)

The chunk-level cost invariant `CInvE`.

* A **unit** of a chunk is a group family or a quiet group: `units s c` counts the groups of `c`
  that are not overflow groups (a family is counted through its splitting member). A chunk-split
  move transfers exactly one unit (fix 3, invariant F).
* **C1**: a splitting chunk `x` that started splitting with size `s₀ ≤ T` satisfies
  `units(x) + (chunkBudget − 1)(t − s₀) ≤ ⌊s₀/g_min⌋ + 1`, where `t ≥ s₀` is its family's size,
    and its
  siblings' sizes differ by at most `u_max = G + k_G`.
* **C2**: a chunk that becomes quiet has size at most `c_max ≤ θ`.

As for groups, `δ c` counts undriven insertions into chunk `c`, and `δu c` the units that the
group phase of such an insertion added to `c`.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Accessors and counts -/

section accessors
variable (s : Core)
/-- The element count stored in a chunk. -/
abbrev cSz (c : Nat) : Nat := (s.C.getX c).size
/-- The current split state of a chunk. -/
abbrev cSt (c : Nat) : St := (s.C.getX c).st
/-- The source chunk recorded by an overflow chunk. -/
abbrev cSrc (c : Nat) : Nat := (s.C.getX c).src
/-- The left sibling recorded by a splitting chunk. -/
abbrev cLl (c : Nat) : Nat := (s.C.getX c).l
/-- The right sibling recorded by a splitting chunk. -/
abbrev cRr (c : Nat) : Nat := (s.C.getX c).r

/-- A chunk of the chunk list (chunks are never freed). -/
def LiveC (c : Nat) : Prop := 1 ≤ c ∧ c < s.C.size
end accessors

instance (s : Core) (g : Nat) : Decidable (LiveG s g) := by unfold LiveG; infer_instance
instance (s : Core) (c : Nat) : Decidable (LiveC s c) := by unfold LiveC; infer_instance

/-- The elements of chunk `c`, in list order. -/
def celts (s : Core) (L : List Nat) (c : Nat) : List Nat := L.filter fun e => gC s (eG s e) = c

/-- The groups of chunk `c` that count as its units: not overflow groups. -/
def UnitG (s : Core) (c g : Nat) : Prop := LiveG s g ∧ gC s g = c ∧ gSt s g ≠ .overflow

instance (s : Core) (c g : Nat) : Decidable (UnitG s c g) := by unfold UnitG; infer_instance

/-- The units of chunk `c`. -/
def units (s : Core) (c : Nat) : Nat := ((Finset.range s.Gs.size).filter (UnitG s c)).card

/-! ### Constants -/

/-- The largest unit: a family. -/
def umax (P : Params) : Nat := P.G + kG P

/-- Units of a chunk of size `s₀`, at most. -/
def unitsOf (P : Params) (s₀ : Nat) : Nat := s₀ / gmin P + 1

/-- `k_C(s₀)`: insertions into a chunk's family until its split ends. -/
def kC (P : Params) (s₀ : Nat) : Nat := unitsOf P s₀ / (P.chunkBudget - 1) + 1

/-- The size of a freshly quiet chunk, at most. -/
def cmax (P : Params) : Nat := (P.T + kC P P.T + umax P + 1) / 2

/-- The parameter conditions for the chunk level (I3, I4). -/
structure CParams (P : Params) : Prop where
  K2 : 2 ≤ P.chunkBudget
  I4 : cmax P ≤ P.theta

/-! ### The invariant -/

/-- The family of a splitting chunk `x`. -/
structure CFamOK (s : Core) (x : Nat) : Prop where
  lLive : LiveC s (cLl s x)
  rLive : LiveC s (cRr s x)
  lAdj : cN s (cLl s x) = x
  rAdj : cN s x = cRr s x
  lSt : cSt s (cLl s x) = .overflow
  lSrc : cSrc s (cLl s x) = x
  rSt : cSt s (cRr s x) = .overflow
  rSrc : cSrc s (cRr s x) = x

/-- Lemma C1's invariant for the family of `x`, which started splitting with size `s₀ x`, at the
sizes and units before the undriven insertions. -/
def C1 (s : Core) (δ δu s₀ : Nat → Nat) (x : Nat) : Prop :=
  s₀ x ≤ s.P.T ∧
    s₀ x ≤ (cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) + (cSz s (cRr s x) - δ (cRr s x)) ∧
    (units s x - δu x) + (s.P.chunkBudget - 1) *
        ((cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) + (cSz s (cRr s x) - δ (cRr s x)) - s₀ x)
      ≤ unitsOf s.P (s₀ x) ∧
    cSz s (cLl s x) - δ (cLl s x) ≤ cSz s (cRr s x) - δ (cRr s x) + umax s.P ∧
    cSz s (cRr s x) - δ (cRr s x) ≤ cSz s (cLl s x) - δ (cLl s x) + umax s.P

theorem unitsOf_mono (P : Params) {a b : Nat} (h : a ≤ b) : unitsOf P a ≤ unitsOf P b := by
  unfold unitsOf; have := Nat.div_le_div_right (c := gmin P) h; omega

/-- C1 bounds the family-size excess by its initial unit budget. -/
theorem C1.excess_le {s : Core} {δ δu s₀ : Nat → Nat} {x : Nat} (h : C1 s δ δu s₀ x)
    (hK : 2 ≤ s.P.chunkBudget) :
    (cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) +
      (cSz s (cRr s x) - δ (cRr s x)) - s₀ x ≤ unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) := by
  have hm : 0 < s.P.chunkBudget - 1 := by omega
  rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]
  exact (Nat.le_add_left _ (units s x - δu x)).trans h.2.2.1

/-- The common family size and balance bounds used by every chunk-drive simulation. -/
theorem C1.drive_bounds {s : Core} {δ δu s₀ : Nat → Nat} {x : Nat} (h : C1 s δ δu s₀ x)
    (hK : 2 ≤ s.P.chunkBudget) (hδs : δ (cLl s x) + δ x + δ (cRr s x) ≤ 1)
    (hδle : δ (cLl s x) ≤ cSz s (cLl s x) ∧ δ x ≤ cSz s x ∧
      δ (cRr s x) ≤ cSz s (cRr s x)) :
    cSz s (cLl s x) + cSz s x + cSz s (cRr s x) ≤ s.P.T + kC s.P s.P.T ∧
    (cSz s (cLl s x) ≤ cSz s (cRr s x) + umax s.P + 1 ∧
      cSz s (cRr s x) ≤ cSz s (cLl s x) + umax s.P + 1) ∧
    cSz s (cLl s x) + cSz s x + cSz s (cRr s x) ≤
      δ (cLl s x) + δ x + δ (cRr s x) + s₀ x +
        unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) := by
  have hq := h.excess_le hK
  have hU := unitsOf_mono s.P h.1
  have hq2 : unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) ≤
      unitsOf s.P s.P.T / (s.P.chunkBudget - 1) := Nat.div_le_div_right hU
  have hk : kC s.P s.P.T = unitsOf s.P s.P.T / (s.P.chunkBudget - 1) + 1 := rfl
  obtain ⟨hT, h1, h2, h3, h4⟩ := h
  omega

/-- The chunk-level invariant, exempting the C1 conditions of the family of `ex`. -/
structure CInvE (s : Core) (L : List Nat) (δ δu s₀ : Nat → Nat) (ex : Nat) : Prop where
  csz : ∀ c, LiveC s c → cSz s c = (celts s L c).length
  cfam : ∀ x, LiveC s x → cSt s x = .splitting → CFamOK s x
  covf : ∀ c, LiveC s c → cSt s c = .overflow →
    LiveC s (cSrc s c) ∧ cSt s (cSrc s c) = .splitting ∧
      (cLl s (cSrc s c) = c ∨ cRr s (cSrc s c) = c)
  gchk : ∀ g, LiveG s g → LiveC s (gC s g) ∧ cSt s (gC s g) ≠ .dead
  c1 : ∀ x, LiveC s x → cSt s x = .splitting → x ≠ ex → C1 s δ δu s₀ x
  δu : ∀ c, δu c ≤ δ c

/-- The chunk-level invariant with no family exempt. -/
abbrev CInv (s : Core) (L : List Nat) (δ δu s₀ : Nat → Nat) : Prop := CInvE s L δ δu s₀ NIL

/-! ### Counting units -/

/-- Unit counts agree when the counted groups agree. -/
theorem units_congr {s s' : Core} {c c' : Nat} (h : ∀ g, UnitG s' c' g ↔ UnitG s c g) :
    units s' c' = units s c := by
  unfold units
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, hg⟩; have := (h g).mp hg; exact ⟨this.1.2.1, this⟩
  · rintro ⟨-, hg⟩; have := (h g).mpr hg; exact ⟨this.1.2.1, this⟩

/-- A unit count after removing one counted group and adding two. -/
theorem units_swap {s s' : Core} {c c' p l r : Nat} (hp : UnitG s c p) (hl : ¬ UnitG s c l)
    (hr : ¬ UnitG s c r) (hlr : l ≠ r) (hl' : UnitG s' c' l) (hr' : UnitG s' c' r)
    (hp' : ¬ UnitG s' c' p)
    (h : ∀ g, g ≠ p → g ≠ l → g ≠ r → (UnitG s' c' g ↔ UnitG s c g)) :
    units s' c' = units s c + 1 := by
  unfold units
  have hS : (Finset.range s'.Gs.size).filter (UnitG s' c') =
      insert l (insert r (((Finset.range s.Gs.size).filter (UnitG s c)).erase p)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_erase]
    by_cases h1 : g = l
    · subst h1; exact ⟨fun _ => Or.inl rfl, fun _ => ⟨hl'.1.2.1, hl'⟩⟩
    · by_cases h2 : g = r
      · subst h2; exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => ⟨hr'.1.2.1, hr'⟩⟩
      · by_cases h3 : g = p
        · subst h3; simp only [h1, h2, false_or, ne_eq, not_true_eq_false, false_and, iff_false]
          exact fun ⟨_, h⟩ => hp' h
        · simp only [h1, h2, h3, false_or, ne_eq, not_false_eq_true, true_and]
          constructor
          · rintro ⟨_, hg⟩; have := (h g h3 h1 h2).mp hg; exact ⟨this.1.2.1, this⟩
          · rintro ⟨_, hg⟩; have := (h g h3 h1 h2).mpr hg; exact ⟨this.1.2.1, this⟩
  rw [hS]
  have hpm : p ∈ (Finset.range s.Gs.size).filter (UnitG s c) := by
    simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hp.1.2.1, hp⟩
  have hrm : r ∉ ((Finset.range s.Gs.size).filter (UnitG s c)).erase p := by
    simp only [Finset.mem_erase, Finset.mem_filter]; exact fun ⟨_, _, h⟩ => hr h
  have hlm : l ∉ insert r (((Finset.range s.Gs.size).filter (UnitG s c)).erase p) := by
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_filter]
    rintro (h | ⟨_, _, h⟩)
    · exact hlr h
    · exact hl h
  rw [Finset.card_insert_of_notMem hlm, Finset.card_insert_of_notMem hrm,
    Finset.card_erase_of_mem hpm]
  have : 0 < ((Finset.range s.Gs.size).filter (UnitG s c)).card := Finset.card_pos.mpr ⟨p, hpm⟩
  omega

end OrderMaintenance.Proof
