/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Runs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring


/-!
# Groups: Lemmas G1, G2 and G4 (`docs/PROOF.md` §4.2)

The group-level cost invariant `GInv`, between operations and inside one, and its preservation
by every step that touches groups or elements. It gives:

* **G1/G2** (sizes): a splitting group `g` with siblings `l`, `r` satisfies
  `|g| + (groupBudget − 1)(t − G) ≤ G` and `||l| − |r|| ≤ 1`, where `t = |l| + |g| + |r| ≥ G`;
    quiet groups
  have fewer than `G` elements, and at least `g_min = ⌊(G−2)/2⌋` unless they hold the sentinel.
* **G4** (element labels): with ghost counters per group (halvings `hv`, pushes `pb`/`pf`),
  every gap within a group is at least `⌊elementSpacing / 2^hv⌋`, and labels stay within
    `pf`/`pb` pushes
  of the centre. The counters are bounded through the group's life, so no element-label guard
  fails.

Ghost counters are not part of the model: the invariant holds for *some* ghost state.

**Undriven insertions.** Inside an operation, the insertion precedes the drive of its family.
`δ g` is the number of insertions into `g` not yet followed by a drive (0 or 1); the size
conditions are stated for the sizes before those insertions.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Accessors and constants -/

section accessors
variable (s : Core)
/-- The element count stored in a group. -/
abbrev gSz (g : Nat) : Nat := (s.Gs.getX g).size
/-- The current split state of a group. -/
abbrev gSt (g : Nat) : St := (s.Gs.getX g).st
/-- The source group recorded by an overflow group. -/
abbrev gSrc (g : Nat) : Nat := (s.Gs.getX g).src
/-- The left sibling recorded by a splitting group. -/
abbrev gLl (g : Nat) : Nat := (s.Gs.getX g).l
/-- The right sibling recorded by a splitting group. -/
abbrev gRr (g : Nat) : Nat := (s.Gs.getX g).r

/-- A live group: in the group list (`INV.mem_glist_iff`). -/
def LiveG (g : Nat) : Prop := g ≠ NIL ∧ g < s.Gs.size ∧ gA s g = true

/-- The size of the family of a splitting group. -/
def famT (g : Nat) : Nat := gSz s (gLl s g) + gSz s g + gSz s (gRr s g)
end accessors

/-- `k_G`: insertions into a family until its split ends (floor form of `PROOF.md`'s `k_G`). -/
def kG (P : Params) : Nat := P.G / (P.groupBudget - 1) + 1

/-- The least size of a freshly quiet group, `⌈(G−3)/2⌉`. -/
def gmin (P : Params) : Nat := (P.G - 2) / 2

/-- The centre of the element label range. -/
def cE (P : Params) : Nat := 1 <<< (P.elementBits - 1)

/-- Halvings a group sees in its life, at most. -/
def UG (P : Params) : Nat := P.G + kG P + (kG P - gmin P)

/-- The parameter conditions for the group level (I1, I2). -/
structure GParams (P : Params) : Prop where
  K2 : 2 ≤ P.groupBudget
  G4 : 4 ≤ P.G
  I1 : P.G + P.G / (P.groupBudget - 1) + 3 < 2 * P.G
  De : 1 ≤ P.elementSpacing
  Be : 1 ≤ P.elementBits
  push : (P.G + kG P) * P.elementSpacing < cE P
  halve : 2 ^ UG P ≤ P.elementSpacing

/-! ### Ghost state -/

/-- Ghost counters per group: halvings, pushes at the back and at the front. -/
structure GGh where
  /-- The number of label halvings charged to each group. -/
  hv : Nat → Nat
  /-- The number of label pushes at the back of each group. -/
  pb : Nat → Nat
  /-- The number of label pushes at the front of each group. -/
  pf : Nat → Nat

/-! ### The invariant -/

/-- The family of a splitting group `g`: its siblings are live, adjacent, overflow nodes with
source `g`, in `g`'s chunk (invariant F). -/
structure FamOK (s : Core) (g : Nat) : Prop where
  lLive : LiveG s (gLl s g)
  rLive : LiveG s (gRr s g)
  lAdj : gN s (gLl s g) = g
  rAdj : gN s g = gRr s g
  lSt : gSt s (gLl s g) = .overflow
  lSrc : gSrc s (gLl s g) = g
  rSt : gSt s (gRr s g) = .overflow
  rSrc : gSrc s (gRr s g) = g
  lC : gC s (gLl s g) = gC s g
  rC : gC s (gRr s g) = gC s g

/-- Lemma G1's invariant for the family of `g`, at the sizes before the undriven insertions. -/
def G1 (s : Core) (δ : Nat → Nat) (g : Nat) : Prop :=
  s.P.G ≤ (gSz s (gLl s g) - δ (gLl s g)) + (gSz s g - δ g) + (gSz s (gRr s g) - δ (gRr s g)) ∧
  (gSz s g - δ g) + (s.P.groupBudget - 1) *
      ((gSz s (gLl s g) - δ (gLl s g)) + (gSz s g - δ g) + (gSz s (gRr s g) - δ (gRr s g)) - s.P.G)
    ≤ s.P.G ∧
  gSz s (gLl s g) - δ (gLl s g) ≤ gSz s (gRr s g) - δ (gRr s g) + 1 ∧
  gSz s (gRr s g) - δ (gRr s g) ≤ gSz s (gLl s g) - δ (gLl s g) + 1

/-- G1 bounds the excess family size by the quotient of its split budget. -/
theorem G1.excess_le {s : Core} {δ : Nat → Nat} {g : Nat} (h : G1 s δ g)
    (hK : 2 ≤ s.P.groupBudget) :
    (gSz s (gLl s g) - δ (gLl s g)) + (gSz s g - δ g) +
      (gSz s (gRr s g) - δ (gRr s g)) - s.P.G ≤ s.P.G / (s.P.groupBudget - 1) := by
  have hm : 0 < s.P.groupBudget - 1 := by omega
  rw [Nat.le_div_iff_mul_le hm, Nat.mul_comm]
  exact (Nat.le_add_left _ (gSz s g - δ g)).trans h.2.1

/-- The common size and balance bounds used by every group-drive simulation. -/
theorem G1.drive_bounds {s : Core} {δ : Nat → Nat} {g : Nat} (h : G1 s δ g)
    (hK : 2 ≤ s.P.groupBudget) (hδs : δ (gLl s g) + δ g + δ (gRr s g) ≤ 1)
    (hδle : δ (gLl s g) ≤ gSz s (gLl s g) ∧ δ g ≤ gSz s g ∧
      δ (gRr s g) ≤ gSz s (gRr s g)) :
    s.P.G ≤ gSz s (gLl s g) + gSz s g + gSz s (gRr s g) ∧
    gSz s (gLl s g) + gSz s g + gSz s (gRr s g) ≤
      s.P.G + s.P.G / (s.P.groupBudget - 1) + 1 ∧
    (gSz s (gLl s g) ≤ gSz s (gRr s g) + 2 ∧
      gSz s (gRr s g) ≤ gSz s (gLl s g) + 2) := by
  have hq := h.excess_le hK
  obtain ⟨h1, h2, h3, h4⟩ := h
  omega

/-- The group-level invariant, exempting the size conditions of the family of `x` (a family
being driven). -/
structure GInvE (s : Core) (L : List Nat) (gh : GGh) (δ : Nat → Nat) (x : Nat) : Prop where
  sz : ∀ g, LiveG s g → gSz s g = (runOf s L g).length
  fam : ∀ g, LiveG s g → gSt s g = .splitting → FamOK s g
  ovf : ∀ g, LiveG s g → gSt s g = .overflow →
    LiveG s (gSrc s g) ∧ gSt s (gSrc s g) = .splitting ∧
      (gLl s (gSrc s g) = g ∨ gRr s (gSrc s g) = g)
  notDead : ∀ g, LiveG s g → gSt s g ≠ .dead
  quiet : ∀ g, LiveG s g → gSt s g = .quiet →
    gSz s g < s.P.G + δ g ∧ 1 ≤ gSz s g ∧ (gmin s.P ≤ gSz s g ∨ s.head ∈ runOf s L g)
  split : ∀ g, LiveG s g → gSt s g = .splitting → g ≠ x → G1 s δ g
  gaps : ∀ g, LiveG s g →
    ((runOf s L g).map (eL s)).IsChain (fun a b => a + s.P.elementSpacing / 2 ^ gh.hv g ≤ b)
  range : ∀ g, LiveG s g → ∀ e ∈ runOf s L g,
    cE s.P ≤ eL s e + gh.pf g * s.P.elementSpacing ∧ eL s e ≤ cE s.P + gh.pb g * s.P.elementSpacing
  ghQ : ∀ g, LiveG s g → gSt s g = .quiet →
    gh.hv g ≤ gSz s g + (kG s.P - gmin s.P) ∧ gh.pb g + gh.pf g ≤ gSz s g
  ghO : ∀ g, LiveG s g → gSt s g = .overflow →
    gh.hv g + s.P.G ≤ famT s (gSrc s g) ∧ gh.pb g + gh.pf g ≤ gSz s g
  ghS : ∀ g, LiveG s g → gSt s g = .splitting →
    gh.hv g ≤ famT s g + (kG s.P - gmin s.P) ∧ gh.pb g + gh.pf g ≤ famT s g

/-- The group-level invariant, with no family exempt. -/
abbrev GInv (s : Core) (L : List Nat) (gh : GGh) (δ : Nat → Nat) : Prop := GInvE s L gh δ NIL

/-! ### Frame: steps that change none of the fields `GInv` reads -/

/-- The fields `GInv` reads are equal. -/
structure GSame (s s' : Core) : Prop where
  Gsize : s'.Gs.size = s.Gs.size
  size : ∀ g, gSz s' g = gSz s g
  st : ∀ g, gSt s' g = gSt s g
  src : ∀ g, gSrc s' g = gSrc s g
  l : ∀ g, gLl s' g = gLl s g
  r : ∀ g, gRr s' g = gRr s g
  next : ∀ g, gN s' g = gN s g
  chk : ∀ g, gC s' g = gC s g
  alive : ∀ g, gA s' g = gA s g
  eG : ∀ e, eG s' e = eG s e
  eL : ∀ e, eL s' e = eL s e
  head : s'.head = s.head
  P : s'.P = s.P

theorem GSame.refl (s : Core) : GSame s s := by
  constructor <;> intros <;> rfl

theorem GSame.trans {s t u : Core} (h1 : GSame s t) (h2 : GSame t u) : GSame s u :=
  ⟨h2.Gsize.trans h1.Gsize, fun g => (h2.size g).trans (h1.size g),
   fun g => (h2.st g).trans (h1.st g), fun g => (h2.src g).trans (h1.src g),
   fun g => (h2.l g).trans (h1.l g), fun g => (h2.r g).trans (h1.r g),
   fun g => (h2.next g).trans (h1.next g), fun g => (h2.chk g).trans (h1.chk g),
   fun g => (h2.alive g).trans (h1.alive g), fun e => (h2.eG e).trans (h1.eG e),
   fun e => (h2.eL e).trans (h1.eL e), h2.head.trans h1.head, h2.P.trans h1.P⟩

instance : IsPre GSame := ⟨GSame.refl, fun _ _ _ => GSame.trans⟩

theorem GSame.liveG {s s' : Core} (h : GSame s s') (g : Nat) : LiveG s' g ↔ LiveG s g := by
  simp only [LiveG, gA,
    h.Gsize]; rw [show (s'.Gs.getX g).alive = (s.Gs.getX g).alive from h.alive g]

theorem GSame.runOf {s s' : Core} (h : GSame s s') (L : List Nat) (g : Nat) :
    runOf s' L g = runOf s L g := by
  unfold OrderMaintenance.Proof.runOf; congr 1; funext e; rw [h.eG]

theorem GSame.famT {s s' : Core} (h : GSame s s') (g : Nat) : famT s' g = famT s g := by
  simp only [OrderMaintenance.Proof.famT, h.size, h.l, h.r]

theorem GSame.famOK {s s' : Core} (h : GSame s s') {g : Nat} (hf : FamOK s g) : FamOK s' g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h.liveG, h.l, h.r, h.next, h.st, h.src, h.chk] <;> assumption

theorem GSame.g1 {s s' : Core} (h : GSame s s') {δ : Nat → Nat} {g : Nat} (hg : G1 s δ g) :
    G1 s' δ g := by
  unfold G1 at *; simp only [h.size, h.l, h.r, h.P]; exact hg

theorem GInvE.of_gsame {s s' : Core} {L : List Nat} {gh : GGh} {δ : Nat → Nat} {x : Nat}
    (hG : GInvE s L gh δ x) (h : GSame s s') : GInvE s' L gh δ x where
  sz g hg := by rw [h.runOf, h.size]; exact hG.sz g ((h.liveG g).mp hg)
  fam g hg hs := h.famOK (hG.fam g ((h.liveG g).mp hg) (h.st g ▸ hs))
  ovf g hg hs := by
    have := hG.ovf g ((h.liveG g).mp hg) (h.st g ▸ hs)
    simp only [h.liveG, h.src, h.st, h.l, h.r]; exact this
  notDead g hg := by rw [h.st]; exact hG.notDead g ((h.liveG g).mp hg)
  quiet g hg hs := by
    rw [h.size, h.P, h.head, h.runOf]; exact hG.quiet g ((h.liveG g).mp hg) (h.st g ▸ hs)
  split g hg hs hx := h.g1 (hG.split g ((h.liveG g).mp hg) (h.st g ▸ hs) hx)
  gaps g hg := by
    have e : eL s' = eL s := funext h.eL
    rw [h.runOf, e, h.P]; exact hG.gaps g ((h.liveG g).mp hg)
  range g hg e he := by
    rw [h.runOf] at he; rw [h.eL, h.P]; exact hG.range g ((h.liveG g).mp hg) e he
  ghQ g hg hs := by rw [h.size, h.P]; exact hG.ghQ g ((h.liveG g).mp hg) (h.st g ▸ hs)
  ghO g hg hs := by
    rw [h.src, h.famT, h.size, h.P]; exact hG.ghO g ((h.liveG g).mp hg) (h.st g ▸ hs)
  ghS g hg hs := by rw [h.famT, h.P]; exact hG.ghS g ((h.liveG g).mp hg) (h.st g ▸ hs)

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Bounds between operations -/

section bounds
variable {s : Core} {L : List Nat} {gh : GGh}

theorem G1.zero {δ : Nat → Nat} {g : Nat} (h : G1 s δ g) (hδ : ∀ b, δ b = 0) :
    s.P.G ≤ famT s g ∧ gSz s g + (s.P.groupBudget - 1) * (famT s g - s.P.G) ≤ s.P.G ∧
      gSz s (gLl s g) ≤ gSz s (gRr s g) + 1 ∧ gSz s (gRr s g) ≤ gSz s (gLl s g) + 1 := by
  unfold G1 at h; simp only [hδ, Nat.sub_zero] at h; exact h

theorem GInv.famT_le (hG : GInv s L gh (fun _ => 0)) (hP : GParams s.P) {g : Nat} (hg : LiveG s g)
    (hs : gSt s g = .splitting) : famT s g ≤ s.P.G + s.P.G / (s.P.groupBudget - 1) := by
  obtain ⟨h1, h2, -, -⟩ := (hG.split g hg hs hg.1).zero fun _ => rfl
  have hK : 0 < s.P.groupBudget - 1 := by have := hP.K2; omega
  have : famT s g - s.P.G ≤ s.P.G / (s.P.groupBudget - 1) := by
    rw [Nat.le_div_iff_mul_le hK]
    have : (s.P.groupBudget - 1) * (famT s g - s.P.G) ≤ s.P.G := by omega
    rw [Nat.mul_comm]; exact this
  omega

theorem GInv.quiet0 (hG : GInv s L gh (fun _ => 0)) {g : Nat} (hg : LiveG s g)
    (hs : gSt s g = .quiet) : gSz s g < s.P.G := by
  have := (hG.quiet g hg hs).1; simpa using this

theorem GInv.size_le (hG : GInv s L gh (fun _ => 0)) (hP : GParams s.P) {g : Nat} (hg : LiveG s g) :
    gSz s g ≤ s.P.G + s.P.G / (s.P.groupBudget - 1) := by
  cases hs : gSt s g with
  | quiet => have := hG.quiet0 hg hs; generalize s.P.G / (s.P.groupBudget - 1) = q; omega
  | splitting => have := hG.famT_le hP hg hs; unfold famT at this; omega
  | overflow =>
    obtain ⟨hp, hps, hlr⟩ := hG.ovf g hg hs
    have := hG.famT_le hP hp hps
    unfold famT at this
    rcases hlr with e | e <;> rw [e] at this <;> omega
  | dead => exact absurd hs (hG.notDead g hg)

theorem GInv.push_le (hG : GInv s L gh (fun _ => 0)) (hP : GParams s.P) {g : Nat} (hg : LiveG s g) :
    gh.pb g + gh.pf g + 1 ≤ s.P.G + kG s.P := by
  unfold kG
  cases hs : gSt s g with
  | quiet =>
    have := (hG.ghQ g hg hs).2; have := hG.quiet0 hg hs
    generalize s.P.G / (s.P.groupBudget - 1) = q; omega
  | splitting => have := (hG.ghS g hg hs).2; have := hG.famT_le hP hg hs; omega
  | overflow => have := (hG.ghO g hg hs).2; have := hG.size_le hP hg; omega
  | dead => exact absurd hs (hG.notDead g hg)

theorem GInv.hv_lt (hG : GInv s L gh (fun _ => 0)) (hP : GParams s.P) {g : Nat} (hg : LiveG s g) :
    gh.hv g + 1 ≤ UG s.P := by
  cases hs : gSt s g with
  | quiet =>
    have h1 := (hG.ghQ g hg hs).1; have h2 := hG.quiet0 hg hs
    simp only [UG, kG] at *; generalize s.P.G / (s.P.groupBudget - 1) = q at *; omega
  | splitting =>
    have h1 := (hG.ghS g hg hs).1; have h2 := hG.famT_le hP hg hs
    simp only [UG, kG] at *; omega
  | overflow =>
    have h1 := (hG.ghO g hg hs).1
    obtain ⟨hp, hps, -⟩ := hG.ovf g hg hs
    have h2 := hG.famT_le hP hp hps
    simp only [UG, kG] at *; omega
  | dead => exact absurd hs (hG.notDead g hg)

end bounds

theorem two_le_div_pow {D U h : Nat} (hD : 2 ^ U ≤ D) (hh : h + 1 ≤ U) : 2 ≤ D / 2 ^ h := by
  rw [Nat.le_div_iff_mul_le (by positivity)]
  calc 2 * 2 ^ h = 2 ^ (h + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ U := Nat.pow_le_pow_right (by norm_num) hh
    _ ≤ D := hD

theorem cE_two (P : Params) (hB : 1 ≤ P.elementBits) : 1 <<< P.elementBits = 2 * cE P := by
  unfold cE; simp only [Nat.shiftLeft_eq, one_mul]
  rw [show P.elementBits = (P.elementBits - 1) + 1 by omega, pow_succ]; simp; ring

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-! ### Transfer of the link structure -/

/-- The group fields other than `size` (and `first`, `last`, `lab`) are equal. -/
structure GLinks (s s' : Core) : Prop where
  Gsize : s'.Gs.size = s.Gs.size
  st : ∀ g, gSt s' g = gSt s g
  src : ∀ g, gSrc s' g = gSrc s g
  l : ∀ g, gLl s' g = gLl s g
  r : ∀ g, gRr s' g = gRr s g
  next : ∀ g, gN s' g = gN s g
  chk : ∀ g, gC s' g = gC s g
  alive : ∀ g, gA s' g = gA s g

theorem GSame.glinks {s s' : Core} (h : GSame s s') : GLinks s s' :=
  ⟨h.Gsize, h.st, h.src, h.l, h.r, h.next, h.chk, h.alive⟩

theorem GLinks.liveG {s s' : Core} (h : GLinks s s') (g : Nat) : LiveG s' g ↔ LiveG s g := by
  simp only [LiveG, gA,
    h.Gsize]; rw [show (s'.Gs.getX g).alive = (s.Gs.getX g).alive from h.alive g]

theorem GLinks.famOK {s s' : Core} (h : GLinks s s') {g : Nat} (hf : FamOK s g) : FamOK s' g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h.liveG, h.l, h.r, h.next, h.st, h.src, h.chk] <;> assumption

theorem GLinks.ovf {s s' : Core} (h : GLinks s s') {g : Nat}
    (hf : LiveG s (gSrc s g) ∧ gSt s (gSrc s g) = .splitting ∧
      (gLl s (gSrc s g) = g ∨ gRr s (gSrc s g) = g)) :
    LiveG s' (gSrc s' g) ∧ gSt s' (gSrc s' g) = .splitting ∧
      (gLl s' (gSrc s' g) = g ∨ gRr s' (gSrc s' g) = g) := by
  simp only [h.liveG, h.src, h.st, h.l, h.r]; exact hf

/-! ### Element insertion -/

theorem insertElem_run' (s : Core) (x hh : Nat) :
    (insertElem x hh).run s =
      if x = gLs s (eG s x) then
        (if eL s x + s.P.elementSpacing ≥ 1 <<< s.P.elementBits ∨ eL s x + s.P.elementSpacing ≤
          eL s x then
          .error (.guard "elem: no room after last") s
        else .ok s.E.size (linkElem s x s.E.size (eL s x + s.P.elementSpacing) hh))
      else
        (if eL s x + 1 ≥ eL s (eN s x) then .error (.guard "elem: no room between") s
        else .ok s.E.size (linkElem s x s.E.size ((eL s x + eL s (eN s x)) / 2) hh)) := by
  simp only [gLs, eG, eL, eN]
  unfold insertElem
  simp only [run_getP_bind, run_getE_bind, run_getG_bind]
  by_cases hl : x = (s.Gs.getX (s.E.getX x).grp).last
  · rw [ite_eq_left (beq_iff_eq.mpr hl), run_bind, run_after, ite_eq_left hl]
    by_cases hg : (s.E.getX x).lab + s.P.elementSpacing ≥ 1 <<< s.P.elementBits ∨
        (s.E.getX x).lab + s.P.elementSpacing ≤ (s.E.getX x).lab
    · rw [ite_eq_left hg, ite_eq_left hg]
    · rw [ite_eq_right hg, ite_eq_right hg]; simp only [run_get_bind, run_modify_bind, run_pure]
  · rw [ite_eq_right (fun h => hl (beq_iff_eq.mp h)), ite_eq_right hl]
    simp only [run_getE_bind]
    rw [run_bind, run_between]
    by_cases hg : (s.E.getX x).lab + 1 ≥ (s.E.getX (s.E.getX x).next).lab
    · rw [ite_eq_left hg, ite_eq_left hg]
    · rw [ite_eq_right hg, ite_eq_right hg]; simp only [run_get_bind, run_modify_bind, run_pure]

section link
variable (s : Core) (x lab hh : Nat)

theorem linkElem_Gs (b : Nat) :
    (linkElem s x s.E.size lab hh).Gs.getX b =
      if eG s x = b ∧ eG s x < s.Gs.size then
        { s.Gs.getX b with last := if (s.Gs.getX b).last = x then s.E.size else (s.Gs.getX b).last,
                           size := (s.Gs.getX b).size + 1 }
      else s.Gs.getX b := by
  simp only [linkElem, Array.getX_modify, eG, beq_iff_eq]

theorem linkElem_glinks : GLinks s (linkElem s x s.E.size lab hh) := by
  refine ⟨by simp [linkElem], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro b <;>
    simp only [gSt, gSrc, gLl, gRr, gN, gC, gA, linkElem_Gs] <;> split <;> rfl

theorem linkElem_gSz (b : Nat) (hg : eG s x < s.Gs.size) :
    gSz (linkElem s x s.E.size lab hh) b = if b = eG s x then gSz s b + 1 else gSz s b := by
  simp only [gSz, linkElem_Gs]
  by_cases hb : b = eG s x
  · subst hb; simp [hg]
  · simp [Ne.symm hb, hb]

theorem linkElem_head : (linkElem s x s.E.size lab hh).head = s.head := rfl
theorem linkElem_P : (linkElem s x s.E.size lab hh).P = s.P := rfl

end link

theorem runOf_link {s : Core} {L : List Nat} {x lab hh : Nat} (hx : x ∈ L) (hy : s.E.size ∉ L)
    (b : Nat) :
    runOf (linkElem s x s.E.size lab hh) (OrderMaintenance.Spec.insertAfterL x s.E.size L) b =
      if b = eG s x then OrderMaintenance.Spec.insertAfterL x s.E.size (runOf s L b) else runOf
        s L b := by
  have hxy : x ≠ s.E.size := fun e => hy (e ▸ hx)
  have hL : L.filter (fun e => decide (eG (linkElem s x s.E.size lab hh) e = b)) =
      L.filter (fun e => decide (eG s e = b)) := by
    refine List.filter_congr fun e he => ?_
    have : e ≠ s.E.size := fun h => hy (h ▸ he)
    rw [linkElem_eG, ite_eq_right this]
  unfold runOf
  rw [filter_insertAfterL, hL]
  · simp only [linkElem_eG, ite_eq_right hxy]
    by_cases hb : b = eG s x
    · subst hb; simp
    · simp [Ne.symm hb, hb]
  · simp [linkElem_eG]

/-- The ghost update of an insertion into group `g`: one more halving or push. -/
structure GhStep (gh gh' : GGh) (g : Nat) : Prop where
  off_hv : ∀ b, b ≠ g → gh'.hv b = gh.hv b
  off_pb : ∀ b, b ≠ g → gh'.pb b = gh.pb b
  off_pf : ∀ b, b ≠ g → gh'.pf b = gh.pf b
  hv_ge : gh.hv g ≤ gh'.hv g
  hv_le : gh'.hv g ≤ gh.hv g + 1
  pb_ge : gh.pb g ≤ gh'.pb g
  pf_ge : gh.pf g ≤ gh'.pf g
  push_le : gh'.pb g + gh'.pf g ≤ gh.pb g + gh.pf g + 1

theorem div_pow_anti (D : Nat) {a b : Nat} (h : a ≤ b) : D / 2 ^ b ≤ D / 2 ^ a :=
  Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) h) (by positivity)

theorem isChain_gap_mono {l : List Nat} {w w' : Nat} (h : l.IsChain (fun a b => a + w ≤ b))
    (hw : w' ≤ w) : l.IsChain (fun a b => a + w' ≤ b) :=
  h.imp fun _ _ hab => by omega

/-- **Linking a new element keeps `GInv`**, given its label's gaps and range. -/
theorem ginv_link {s : Core} {A : Abs} {gh gh' : GGh} (hI : INV s A)
    (hG : GInv s A.elist gh (fun _ => 0)) {x : Nat} (hx : x ∈ A.elist) {lab hh : Nat}
    (hst : GhStep gh gh' (eG s x))
    (hlo : eL s x + s.P.elementSpacing / 2 ^ gh'.hv (eG s x) ≤ lab)
    (hhi : x ≠ gLs s (eG s x) → lab + s.P.elementSpacing / 2 ^ gh'.hv (eG s x) ≤ eL s (eN s x))
    (hr : cE s.P ≤ lab + gh'.pf (eG s x) * s.P.elementSpacing ∧ lab ≤ cE s.P + gh'.pb (eG s x)
      * s.P.elementSpacing) :
    GInv (linkElem s x s.E.size lab hh) (OrderMaintenance.Spec.insertAfterL x s.E.size A.elist) gh'
      (fun b => if b = eG s x then 1 else 0) := by
  generalize hgdef : eG s x = g at hst hlo hhi hr
  have hgl : g ∈ A.glist := hgdef ▸ hI.eG_mem hx
  have hgL : LiveG s g := (hI.mem_glist_iff).mp hgl
  have hgs : eG s x < s.Gs.size := hgdef ▸ hgL.2.1
  have hy : s.E.size ∉ A.elist := fun hm => by have := (hI.eAlloc _).mp hm; omega
  have hxy : x ≠ s.E.size := fun e => hy (e ▸ hx)
  have hxr : x ∈ runOf s A.elist g := mem_runOf.mpr ⟨hx, hgdef⟩
  have hK := linkElem_glinks s x lab hh
  have hLive : ∀ b, LiveG (linkElem s x s.E.size lab hh) b ↔ LiveG s b := hK.liveG
  have hRun : ∀ b, runOf (linkElem s x s.E.size lab hh) (OrderMaintenance.Spec.insertAfterL x
    s.E.size A.elist) b =
      if b = g then OrderMaintenance.Spec.insertAfterL x s.E.size (runOf s A.elist b) else runOf
        s A.elist b := by
    intro b; rw [runOf_link hx hy, hgdef]
  have hSz : ∀ b, gSz (linkElem s x s.E.size lab hh) b = if b = g then gSz s b + 1 else gSz s b
    := by
    intro b; rw [linkElem_gSz s x lab hh b hgs, hgdef]
  have hSzδ : ∀ b, gSz (linkElem s x s.E.size lab hh) b - (if b = g then 1 else 0) = gSz s b := by
    intro b; rw [hSz]; split <;> omega
  have hSzge : ∀ b, gSz s b ≤ gSz (linkElem s x s.E.size lab hh) b := by
    intro b; rw [hSz]; split <;> omega
  have hfam : ∀ p, famT s p ≤ famT (linkElem s x s.E.size lab hh) p := by
    intro p; simp only [famT, hK.l, hK.r]
    have := hSzge (gLl s p); have := hSzge p; have := hSzge (gRr s p); omega
  have hfamg : ∀ p, (gLl s p = g ∨ p = g ∨ gRr s p = g) →
      famT s p + 1 ≤ famT (linkElem s x s.E.size lab hh) p := by
    intro p hp; simp only [famT, hK.l, hK.r]
    have := hSzge (gLl s p); have := hSzge p; have := hSzge (gRr s p)
    rcases hp with e | e | e
    · rw [hSz (gLl s p), ite_eq_left e]; omega
    · rw [hSz p, ite_eq_left e]; omega
    · rw [hSz (gRr s p), ite_eq_left e]; omega
  have hEL : ∀ e, e ≠ s.E.size → eL (linkElem s x s.E.size lab hh) e = eL s e := by
    intro e he; rw [linkElem_eL, ite_eq_right he]
  -- the run of `g`, split at `x`
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hxr
  have hrnd : (runOf s A.elist g).Nodup := hI.eList.nodup.filter _
  have hr1 : x ∉ r1 := by
    rw [hrun] at hrnd; exact fun h => (List.nodup_append.mp hrnd).2.2 x h x (by simp) rfl
  have hyr : ∀ b, s.E.size ∉ runOf s A.elist b := fun b h => hy (mem_runOf.mp h).1
  have hlast : x = gLs s g ↔ r2 = [] := by
    rw [(hI.gEnds g hgl).2, hI.elts_eq hgl, hrun]
    constructor
    · intro e
      cases r2 with
      | nil => rfl
      | cons a t =>
        exfalso
        rw [show r1 ++ x :: a :: t = (r1 ++ [x]) ++ a :: t by simp, getLastD_append_cons] at e
        rw [hrun] at hrnd
        have hm := getLastD_cons_mem a t NIL
        rw [← e] at hm
        exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1 hm
    · rintro rfl; simp
  have hnext : ∀ n ∈ r2.head?, eN s x = n := by
    intro n hn
    have hr2 : r2 ≠ [] := by rintro rfl; simp at hn
    have hnl : (A.elts g).getLast? ≠ some x := by
      rw [hI.elts_eq hgl, hrun]
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hr2
      intro e
      rw [show r1 ++ x :: a :: t = (r1 ++ [x]) ++ a :: t by simp,
        List.getLast?_append_of_ne_nil _ (by simp)] at e
      have hm : x ∈ a :: t := List.mem_of_getLast? e
      rw [hrun] at hrnd
      exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1 hm
    rw [hI.eN_in_run hgl (by rw [hI.elts_eq hgl]; exact hxr) hnl, hI.elts_eq hgl, hrun,
      succOf_mid (hrun ▸ hrnd)]
    cases r2 with
    | nil => simp at hn
    | cons a t => simp at hn; simp [hn]
  have hnewrun : runOf (linkElem s x s.E.size lab hh) (OrderMaintenance.Spec.insertAfterL x
    s.E.size A.elist) g =
      r1 ++ x :: s.E.size :: r2 := by
    rw [hRun, ite_eq_left rfl, hrun, insertAfterL_mid hr1]
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro b hb
    rw [hLive] at hb
    by_cases hbg : b = g
    · subst hbg
      rw [hnewrun, hSz, ite_eq_left rfl, hG.sz b hb, hrun]; simp; omega
    · rw [hSz, ite_eq_right hbg, hRun, ite_eq_right hbg]; exact hG.sz b hb
  · intro b hb hs
    rw [hLive] at hb; rw [hK.st] at hs
    exact hK.famOK (hG.fam b hb hs)
  · intro b hb hs
    rw [hLive] at hb; rw [hK.st] at hs
    exact hK.ovf (hG.ovf b hb hs)
  · intro b hb; rw [hLive] at hb; rw [hK.st]; exact hG.notDead b hb
  · intro b hb hs
    rw [hLive] at hb; rw [hK.st] at hs
    obtain ⟨q1, q2, q3⟩ := hG.quiet b hb hs
    simp only [linkElem_P, linkElem_head]
    refine ⟨?_, le_trans q2 (hSzge b), ?_⟩
    · by_cases hbg : b = g <;> simp only [hSz, hbg, ite_true, ite_false] at q1 ⊢ <;> omega
    · rcases q3 with q3 | q3
      · exact Or.inl (le_trans q3 (hSzge b))
      · right; rw [hRun]; split
        · next e => subst e; exact (OrderMaintenance.Spec.mem_insertAfterL hxr).mpr (Or.inr q3)
        · exact q3
  · intro b hb hs hbx
    rw [hLive] at hb; rw [hK.st] at hs
    have := hG.split b hb hs hbx
    unfold G1 at this ⊢
    simp only [linkElem_P, hK.l, hK.r, hSzδ]
    simpa using this
  · intro b hb
    rw [hLive] at hb
    simp only [linkElem_P]
    by_cases hbg : b = g
    · subst hbg
      rw [hnewrun]
      have hc := isChain_gap_mono (hG.gaps b hb) (div_pow_anti s.P.elementSpacing hst.hv_ge)
      rw [hrun] at hc
      refine isChain_insert' hc (fun z hz => hEL z (fun e => hyr b (e ▸ hrun ▸ hz))) ?_ ?_
      · rw [linkElem_eL, ite_eq_left rfl]; exact hlo
      · intro n hn
        rw [linkElem_eL, ite_eq_left rfl, ← hnext n hn]
        refine hhi fun e => ?_
        rw [hlast.mp e] at hn; simp at hn
    · rw [hRun, ite_eq_right hbg, hst.off_hv b hbg]
      have : (runOf s A.elist b).map (eL (linkElem s x s.E.size lab hh)) =
          (runOf s A.elist b).map (eL s) :=
        List.map_congr_left fun z hz => hEL z (fun e => hyr b (e ▸ hz))
      rw [this]; exact hG.gaps b hb
  · intro b hb e he
    rw [hLive] at hb
    simp only [linkElem_P]
    by_cases hbg : b = g
    · subst hbg
      rw [hnewrun] at he
      by_cases hey : e = s.E.size
      · subst hey; rw [linkElem_eL, ite_eq_left rfl]; exact hr
      · rw [hEL e hey]
        have he' : e ∈ runOf s A.elist b := by
          rw [hrun]; exact (mem_insert_iff.mp he).resolve_left hey
        obtain ⟨h1, h2⟩ := hG.range b hb e he'
        constructor
        · exact le_trans h1 (by have := Nat.mul_le_mul_right s.P.elementSpacing hst.pf_ge; omega)
        · exact le_trans h2 (by have := Nat.mul_le_mul_right s.P.elementSpacing hst.pb_ge; omega)
    · rw [hRun, ite_eq_right hbg] at he
      rw [hEL e (fun h => hyr b (h ▸ he)), hst.off_pb b hbg, hst.off_pf b hbg]
      exact hG.range b hb e he
  · intro b hb hs
    rw [hLive] at hb; rw [hK.st] at hs
    obtain ⟨q1, q2⟩ := hG.ghQ b hb hs
    simp only [linkElem_P]
    by_cases hbg : b = g
    · subst hbg; rw [hSz, ite_eq_left rfl]
      have := hst.hv_le; have := hst.push_le; omega
    · rw [hst.off_hv b hbg, hst.off_pb b hbg, hst.off_pf b hbg]
      exact ⟨le_trans q1 (by have := hSzge b; omega), le_trans q2 (hSzge b)⟩
  · intro b hb hs
    rw [hLive] at hb; rw [hK.st] at hs
    obtain ⟨q1, q2⟩ := hG.ghO b hb hs
    simp only [linkElem_P, hK.src]
    by_cases hbg : b = g
    · subst hbg
      obtain ⟨-, -, hlr⟩ := hG.ovf b hb hs
      have := hfamg (gSrc s b) (by rcases hlr with e | e <;> simp [e])
      rw [hSz, ite_eq_left rfl]
      have := hst.hv_le; have := hst.push_le; omega
    · rw [hst.off_hv b hbg, hst.off_pb b hbg, hst.off_pf b hbg]
      exact ⟨le_trans q1 (hfam _), le_trans q2 (hSzge b)⟩
  · intro b hb hs
    rw [hLive] at hb; rw [hK.st] at hs
    obtain ⟨q1, q2⟩ := hG.ghS b hb hs
    simp only [linkElem_P]
    by_cases hbg : b = g
    · subst hbg
      have := hfamg b (Or.inr (Or.inl rfl))
      have := hst.hv_le; have := hst.push_le; omega
    · rw [hst.off_hv b hbg, hst.off_pb b hbg, hst.off_pf b hbg]
      exact ⟨le_trans q1 (by have := hfam b; omega), le_trans q2 (hfam b)⟩

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- Unless `x` is the last of its group, the element after `x` follows it in the group's run. -/
theorem INV.next_in_run {s : Core} {A : Abs} (hI : INV s A) {x : Nat} (hx : x ∈ A.elist)
    (hl : x ≠ gLs s (eG s x)) :
    ∃ r1 r2, runOf s A.elist (eG s x) = r1 ++ x :: eN s x :: r2 := by
  have hgl := hI.eG_mem hx
  have hxr : x ∈ runOf s A.elist (eG s x) := mem_runOf.mpr ⟨hx, rfl⟩
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hxr
  have hrnd : (runOf s A.elist (eG s x)).Nodup := hI.eList.nodup.filter _
  cases r2 with
  | nil =>
    exfalso; apply hl
    rw [(hI.gEnds _ hgl).2, hI.elts_eq hgl, hrun]; simp
  | cons n t =>
    refine ⟨r1, t, ?_⟩
    have hnl : (A.elts (eG s x)).getLast? ≠ some x := by
      rw [hI.elts_eq hgl, hrun]
      intro e
      rw [show r1 ++ x :: n :: t = (r1 ++ [x]) ++ n :: t by simp,
        List.getLast?_append_of_ne_nil _ (by simp)] at e
      have hm : x ∈ n :: t := List.mem_of_getLast? e
      rw [hrun] at hrnd
      exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1 hm
    rw [hI.eN_in_run hgl (by rw [hI.elts_eq hgl]; exact hxr) hnl, hI.elts_eq hgl, hrun,
      succOf_mid (hrun ▸ hrnd)]
    simp

/-- **Lemma G4 for insertions.** Between operations, element insertion passes its label guard;
the new state satisfies `GInv` with one undriven insertion in `x`'s group. -/
theorem ginv_insertElem {s : Core} {A : Abs} {gh : GGh} (hI : INV s A)
    (hG : GInv s A.elist gh (fun _ => 0)) (hP : GParams s.P) {x : Nat} (hx : x ∈ A.elist)
    (hh : Nat) :
    ∃ lab, (insertElem x hh).run s = .ok s.E.size (linkElem s x s.E.size lab hh) ∧
      ∃ gh', GInv (linkElem s x s.E.size lab hh) (OrderMaintenance.Spec.insertAfterL x s.E.size
        A.elist) gh'
        (fun b => if b = eG s x then 1 else 0) := by
  have hgl := hI.eG_mem hx
  have hgL : LiveG s (eG s x) := hI.mem_glist_iff.mp hgl
  have hxr : x ∈ runOf s A.elist (eG s x) := mem_runOf.mpr ⟨hx, rfl⟩
  have hpush := hG.push_le hP hgL
  have hhv := hG.hv_lt hP hgL
  have hD := hP.De
  have hcE : (s.P.G + kG s.P) * s.P.elementSpacing < cE s.P := hP.push
  obtain ⟨hlo, hhi⟩ := hG.range _ hgL x hxr
  rw [insertElem_run']
  by_cases hl : x = gLs s (eG s x)
  · rw [ite_eq_left hl]
    have hm : (gh.pb (eG s x) + 1) * s.P.elementSpacing ≤ (s.P.G + kG s.P) * s.P.elementSpacing :=
      Nat.mul_le_mul_right _ (by omega)
    have h1 : ¬ (eL s x + s.P.elementSpacing ≥ 1 <<< s.P.elementBits ∨ eL s x +
      s.P.elementSpacing ≤ eL s x) := by
      rw [cE_two _ hP.Be]
      have : (gh.pb (eG s x) + 1) * s.P.elementSpacing = gh.pb (eG s x) * s.P.elementSpacing +
        s.P.elementSpacing := by ring
      omega
    rw [ite_eq_right h1]
    refine ⟨_, rfl, ⟨gh.hv, Function.update gh.pb (eG s x) (gh.pb (eG s x) + 1), gh.pf⟩, ?_⟩
    refine ginv_link hI hG hx ?_ ?_ ?_ ?_
    · refine ⟨fun _ _ => rfl, fun b hb => by simp [hb], fun _ _ => rfl, le_rfl, by simp,
        by simp, le_rfl, by simp; omega⟩
    · simp only; have := Nat.div_le_self s.P.elementSpacing (2 ^ gh.hv (eG s x)); omega
    · intro h; exact absurd hl h
    · simp only [Function.update_self]
      constructor
      · have := Nat.zero_le (gh.pf (eG s x) * s.P.elementSpacing); omega
      · have : (gh.pb (eG s x) + 1) * s.P.elementSpacing = gh.pb (eG s x) * s.P.elementSpacing
        + s.P.elementSpacing := by ring
        omega
  · rw [ite_eq_right hl]
    obtain ⟨r1, r2, hrun⟩ := hI.next_in_run hx hl
    have hgap := isChain_mid (hrun ▸ hG.gaps _ hgL)
    have h2 := two_le_div_pow hP.halve hhv
    have hn : eN s x ∈ runOf s A.elist (eG s x) := by rw [hrun]; simp
    obtain ⟨hlo', hhi'⟩ := hG.range _ hgL _ hn
    rw [ite_eq_right (by omega)]
    refine ⟨_, rfl, ⟨Function.update gh.hv (eG s x) (gh.hv (eG s x) + 1), gh.pb, gh.pf⟩, ?_⟩
    have hw : s.P.elementSpacing / 2 ^ (gh.hv (eG s x) + 1) = s.P.elementSpacing / 2 ^ gh.hv
      (eG s x) / 2 := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    refine ginv_link hI hG hx ?_ ?_ ?_ ?_
    · refine ⟨fun b hb => by simp [hb], fun _ _ => rfl, fun _ _ => rfl, by simp, by simp,
        le_rfl, le_rfl, by dsimp only; omega⟩
    · simp only [Function.update_self, hw]; omega
    · intro _; simp only [Function.update_self, hw]; omega
    · simp only; omega

end OrderMaintenance.Proof
