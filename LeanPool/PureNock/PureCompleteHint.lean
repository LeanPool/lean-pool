/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.PureComplete
public import Mathlib.Tactic.IntervalCases

/-!
# Completeness for the OP₁₁ extension

Mirrors the OP₀–OP₁₀ completeness proof for `nextHint` and `evalN`.
`vcostN` accounts for hint expansion; `runHint_adequate_complete` closes it.
-/

@[expose] public section

namespace Nock
namespace Verb

open Noun

/-- Arithmetic identity for the OP₁₁ dynamic-macro cost accounting (kept top-level so `omega`
    runs in a clean context). -/
theorem op11_arith (A B : Nat) : 1 + A + (1 + 2 + B) = 4 + A + B := by omega

/-! ### Small machine / evalN helpers -/

theorem evalN_atom_none (f : Nat) (s : Noun) (k : Nat) : evalN f s (.atom k) = none := by
  cases f <;> simp [evalN]

theorem evalN_op_ge12_none (f : Nat) (s tail : Noun) (op : Nat) (h : 12 ≤ op) :
    evalN f s (.cell (.atom op) tail) = none := by
  cases f with
  | zero => rfl
  | succ ff =>
      simp only [evalN]
      split <;> first | rfl | omega

theorem inDomainHint_of_inDomain {v : Verb} (h : inDomain v = true) : inDomainHint v = true := by
  simp only [inDomainHint, h, Bool.true_or]

theorem nextHint_none_of_terminal {v : Verb} (h : isTerminal v = true) : nextHint v = none := by
  unfold nextHint; rw [getIndex_none_of_terminal h]

theorem redexHint_eq_reduce_of_hintExpand_none {v : Verb} (h : hintExpand v = none) :
    redexHint v = reduce v := by
  unfold redexHint; rw [h]

theorem EvN_det {a b y1 y2 : Noun} (h1 : Ev a b y1) (h2 : Ev a b y2) : y1 = y2 := by
  obtain ⟨f1, h1⟩ := h1; obtain ⟨f2, h2⟩ := h2
  exact Option.some.inj ((evalN_mono (Nat.le_max_left f1 f2) h1).symm.trans
    (evalN_mono (Nat.le_max_right f1 f2) h2))

/-! ### (b) `den`-definedness descent -/

theorem den_left_defined {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (h : den (f + 1) (Verb.node a l r) = some x) : ∃ y, den f l = some y := by
  cases hl : den f l with
  | some y => exact ⟨y, rfl⟩
  | none =>
      exfalso
      cases a with
      | edit =>
          cases r with
          | leaf k => simp [den] at h
          | node rb nw od => simp [den, hl] at h
      | wut => simp [den] at h
      | _ => simp [den, hl] at h

theorem den_right_defined_of_editOk {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den (f + 1) (Verb.node a l r) = some x) :
    ∃ g y, den g r = some y := by
  cases a with
  | wut => simp [den] at h
  | edit =>
      have hrp : Verb.isPending r = false := editOk_edit_cond hok
      cases r with
      | leaf k => simp [den] at h
      | node rb nw od =>
          have hrb : rb = Action.null := by
            simp only [isPending] at hrp
            cases rb <;> simp_all [Action.isNull]
          subst hrb
          simp only [den] at h
          cases hnw : den f nw with
          | none => rw [hnw] at h; simp at h
          | some n =>
              cases hod : den f od with
              | none => rw [hnw, hod] at h; simp at h
              | some o => exact ⟨f + 1, .cell n o, by simp [den, hnw, hod]⟩
  | null => cases hr : den f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [den, hr]
    at h
  | star => cases hr : den f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [den, hr]
    at h
  | slot => cases hr : den f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [den, hr]
    at h
  | equal => cases hr : den f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [den, hr]
    at h
  | minus => cases hr : den f r with | some y => exact ⟨f, y, hr⟩ | none => exfalso; simp [den, hr]
    at h

theorem enum_den_defined :
    ∀ (v : Verb), editOk v = true → ∀ (c f : Nat) (x : Noun),
      den f v = some x → ∀ p ∈ (enum v c).2, ∃ g y, den g p.2 = some y := by
  intro v
  induction v with
  | leaf k => intro _ c f x _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro hok c f x hden p hp
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := by
        cases f with
        | zero => simp [den] at hden
        | succ n => exact ⟨n, rfl⟩
      have hokl := (editOk_children hok).1
      have hokr := (editOk_children hok).2
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; exact ⟨f + 1, x, hden⟩
      · obtain ⟨yl, hyl⟩ := den_left_defined hden
        exact ihl hokl (c + 1) f yl hyl p hleft
      · obtain ⟨g, yr, hyr⟩ := den_right_defined_of_editOk hok hden
        exact ihr hokr _ g yr hyr p hright

theorem Den_subnode {v : Verb} {x : Noun} (hok : editOk v = true) (hv : Den v x)
    {i : Nat} {sub : Verb} (hmap : map i v = some sub) : ∃ y, Den sub y := by
  obtain ⟨f, hf⟩ := hv
  have hmem : (i, sub) ∈ nodes v := mem_nodes_of_map hmap
  obtain ⟨g, y, hg⟩ := enum_den_defined v hok 0 f x hf (i, sub) hmem
  exact ⟨y, g, hg⟩

/-! ### `den`-definedness helpers at a FIXED fuel -/

theorem den_right_F {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den (f + 1) (Verb.node a l r) = some x) :
    ∃ yr, den (f + 1) r = some yr := by
  cases a with
  | wut => simp [den] at h
  | edit =>
      have hrp : Verb.isPending r = false := editOk_edit_cond hok
      cases r with
      | leaf k => simp [den] at h
      | node rb nw od =>
          have hrb : rb = Action.null := by
            simp only [isPending] at hrp
            cases rb <;> simp_all [Action.isNull]
          subst hrb
          simp only [den] at h
          cases hnw : den f nw with
          | none => rw [hnw] at h; simp at h
          | some n =>
              cases hod : den f od with
              | none => rw [hnw, hod] at h; simp at h
              | some o => exact ⟨.cell n o, by simp [den, hnw, hod]⟩
  | null =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
  | star =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
  | slot =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
  | equal =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h
  | minus =>
      cases hr : den f r with
      | some y => exact ⟨y, den_succ hr⟩
      | none => simp [den, hr] at h

theorem den_children_F {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den F (Verb.node a l r) = some x) :
    (∃ yl, den F l = some yl) ∧ (∃ yr, den F r = some yr) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [den] at h
    | succ n => exact ⟨n, rfl⟩
  refine ⟨?_, den_right_F hok h⟩
  obtain ⟨yl, hyl⟩ := den_left_defined h
  exact ⟨yl, den_succ hyl⟩

theorem den_terminal_val {v : Verb} {F : Nat} {y : Noun}
    (ht : isTerminal v = true) (h : den F v = some y) : y = v.noun :=
  (Den_terminal_iff ht).1 ⟨F, h⟩

theorem den_term_children {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : den F (Verb.node a l r) = some x)
    (htl : isTerminal l = true) (htr : isTerminal r = true) :
    den F l = some l.noun ∧ den F r = some r.noun := by
  obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := den_children_F hok h
  rw [den_terminal_val htl hyl] at hyl
  rw [den_terminal_val htr hyr] at hyr
  exact ⟨hyl, hyr⟩

theorem den_term_split {l r : Verb} {f : Nat} {x : Noun}
    (htl : isTerminal l = true) (htr : isTerminal r = true)
    (h : den (f + 1) (Verb.node .null l r) = some x) :
    den f l = some l.noun ∧ den f r = some r.noun := by
  simp only [den] at h
  cases hl : den f l with
  | none => rw [hl] at h; simp at h
  | some yl =>
      cases hr : den f r with
      | none => rw [hl, hr] at h; simp at h
      | some yr =>
          refine ⟨?_, ?_⟩
          · rw [den_terminal_val htl hl]
          · rw [den_terminal_val htr hr]

theorem den_star_val {A B : Verb} {f : Nat} {a b w : Noun}
    (hA : den f A = some a) (hB : den f B = some b) (he : evalN f a b = some w) :
    den (f + 1) (Verb.node .star A B) = some w := by
  simp only [den, hA, hB]; exact he

theorem den_null_val {A B : Verb} {f : Nat} {a b : Noun}
    (hA : den f A = some a) (hB : den f B = some b) :
    den (f + 1) (Verb.node .null A B) = some (Noun.cell a b) := by
  simp only [den, hA, hB]

theorem den_null_none {A B : Verb} {f : Nat} (hA : den f A = none) :
    den (f + 1) (Verb.node .null A B) = none := by
  simp only [den, hA]

theorem den_null_leaf0 {inner : Verb} {f : Nat} {dv : Noun}
    (h : den (f + 1) (Verb.node .null (Verb.leaf 0) inner) = some dv) :
    ∃ w, dv = Noun.cell (Noun.atom 0) w := by
  simp only [den] at h
  cases hi : den f inner with
  | none => rw [hi] at h; simp at h
  | some iv => rw [hi] at h; exact ⟨iv, (Option.some.inj h).symm⟩

/-! ### (d) The cost measure over `evalN`/`den` -/

/-- Weighted `evalN`-derivation cost: mirrors `evalN` clause-for-clause (same recursive calls),
    each opcode contributing a positive weight (identical to `pcost`, plus an OP₁₁ clause with
    weight `50`). -/
def ncost : Nat → Noun → Noun → Nat
  | 0, _, _ => 0
  | _ + 1, _, .atom _ => 0
  | f + 1, subj, .cell (.cell b c) d =>
      1 + ncost f subj (.cell b c) + ncost f subj d
  | f + 1, subj, .cell (.atom op) tail =>
    match op with
    | 0 => 2
    | 1 => 1
    | 2 =>
        match tail with
        | .cell b c =>
            let inner := match evalN f subj b, evalN f subj c with
                         | some sb, some sc => ncost f sb sc
                         | _, _ => 0
            1 + ncost f subj b + ncost f subj c + inner
        | _ => 0
    | 3 => 2 + ncost f subj tail
    | 4 => 2 + ncost f subj tail
    | 5 =>
        match tail with
        | .cell b c => 2 + ncost f subj b + ncost f subj c
        | _ => 0
    | 6 =>
        match tail with
        | .cell b (.cell c d) =>
            let inner := match evalN f subj b with
                         | some (.atom 0) => ncost f subj c
                         | some (.atom 1) => ncost f subj d
                         | _ => 0
            100 + ncost f subj b + inner
        | _ => 0
    | 7 =>
        match tail with
        | .cell b c =>
            let inner := match evalN f subj b with
                         | some sb => ncost f sb c
                         | _ => 0
            1 + ncost f subj b + inner
        | _ => 0
    | 8 =>
        match tail with
        | .cell b c =>
            let inner := match evalN f subj b with
                         | some sb => ncost f (.cell sb subj) c
                         | _ => 0
            1 + ncost f subj b + inner
        | _ => 0
    | 9 =>
        match tail with
        | .cell (.atom ax) c =>
            let inner := match evalN f subj c with
                         | some core =>
                             match Noun.slot ax core with
                             | some arm => ncost f core arm
                             | _ => 0
                         | _ => 0
            20 + ncost f subj c + inner
        | _ => 0
    | 10 =>
        match tail with
        | .cell (.cell (.atom _) c) d => 2 + ncost f subj c + ncost f subj d
        | _ => 0
    | 11 =>
        match tail with
        | .cell (.cell _ clue) body =>
            let inner := match evalN f subj clue with
                         | some _ => ncost f subj body
                         | _ => 0
            50 + ncost f subj clue + inner
        | .cell (.atom _) body => 50 + ncost f subj body
        | _ => 0
    | _ => 0

/-- Verb cost keyed to `den`/`evalN` (structural in the verb; `F` a fixed lookup-fuel). -/
def vcostN (F : Nat) : Verb → Nat
  | .leaf _ => 0
  | .node a l r =>
      (match a with
       | .star => match den F l, den F r with
                  | some sa, some fo => ncost F sa fo
                  | _, _ => 0
       | .slot => 1
       | .equal => 1
       | .minus => 1
       | .edit => 1
       | .null => 0
       | .wut => 0) + vcostN F l + vcostN F r

theorem ncost_succ {n : Nat} {a b : Noun} {r : Noun}
    (hb : evalN n a b = some r) : ncost (n + 1) a b = ncost n a b := by
  induction n, a, b using evalN.induct generalizing r <;>
    simp only [evalN] at hb <;>
    simp_all only [ncost, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] <;>
    grind only [evalN_succ]

theorem ncost_mono {n m : Nat} {a b r : Noun} (hle : n ≤ m) (hb : evalN n a b = some r) :
    ncost m a b = ncost n a b := by
  induction hle with
  | refl => rfl
  | step hk ih => rw [ncost_succ (evalN_mono hk hb)]; exact ih

theorem ncost_align {n m k : Nat} {a b r : Noun} (h : evalN n a b = some r)
    (hm : n ≤ m) (hk : n ≤ k) : ncost m a b = ncost k a b :=
  (ncost_mono hm h).trans (ncost_mono hk h).symm

theorem vcostN_star_eq {F : Nat} {l r : Verb} : vcostN F (Verb.node .star l r) =
    (match den F l, den F r with | some sa, some fo => ncost F sa fo | _, _ => 0)
      + vcostN F l + vcostN F r := rfl
theorem vcostN_slot_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .slot l r) = 1 + vcostN F l + vcostN F r := rfl
theorem vcostN_equal_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .equal l r) = 1 + vcostN F l + vcostN F r := rfl
theorem vcostN_minus_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .minus l r) = 1 + vcostN F l + vcostN F r := rfl
theorem vcostN_edit_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .edit l r) = 1 + vcostN F l + vcostN F r := rfl
theorem vcostN_null_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .null l r) = vcostN F l + vcostN F r := by
  simp only [vcostN]; omega
theorem vcostN_wut_eq {F : Nat} {l r : Verb} :
    vcostN F (Verb.node .wut l r) = vcostN F l + vcostN F r := by
  simp only [vcostN]; omega

theorem vcostN_terminal : ∀ (v : Verb), isTerminal v = true → ∀ F, vcostN F v = 0 := by
  intro v
  induction v with
  | leaf k => intro _ F; rfl
  | node a l r ihl ihr =>
      intro hterm F
      simp only [isTerminal, Bool.and_eq_true] at hterm
      obtain ⟨⟨hnull, hl⟩, hr⟩ := hterm
      have ha : a = Action.null := by cases a <;> simp_all [Action.isNull]
      subst ha
      simp only [vcostN]; rw [ihl hl F, ihr hr F]

theorem vcostN_star_terminal {F : Nat} {A B : Verb}
    (hA : isTerminal A = true) (hB : isTerminal B = true)
    (hdA : den F A = some A.noun) (hdB : den F B = some B.noun) :
    vcostN F (Verb.node .star A B) = ncost F A.noun B.noun := by
  simp only [vcostN_star_eq, hdA, hdB, vcostN_terminal A hA F, vcostN_terminal B hB F, Nat.add_zero]

theorem vcostN_succ {F : Nat} {v : Verb} {x : Noun}
    (hok : editOk v = true) (hv : den F v = some x) : vcostN (F + 1) v = vcostN F v := by
  induction v generalizing F x with
  | leaf k => rfl
  | node a l r ihl ihr =>
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
        cases F with
        | zero => simp [den] at hv
        | succ n => exact ⟨n, rfl⟩
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := den_children_F hok hv
      have ihl' : vcostN (f + 1 + 1) l = vcostN (f + 1) l := ihl hokl hyl
      have ihr' : vcostN (f + 1 + 1) r = vcostN (f + 1) r := ihr hokr hyr
      cases a with
      | null => simp only [vcostN, ihl', ihr']
      | wut => simp [den] at hv
      | slot => simp only [vcostN, ihl', ihr']
      | equal => simp only [vcostN, ihl', ihr']
      | minus => simp only [vcostN, ihl', ihr']
      | edit => simp only [vcostN, ihl', ihr']
      | star =>
          simp only [den] at hv
          cases hfl : den f l with
          | none => rw [hfl] at hv; simp at hv
          | some sa =>
              cases hfr : den f r with
              | none => rw [hfl, hfr] at hv; simp at hv
              | some fo =>
                  rw [hfl, hfr] at hv
                  have hdl1 : den (f + 1) l = some sa := den_succ hfl
                  have hdr1 : den (f + 1) r = some fo := den_succ hfr
                  have hdl2 : den (f + 1 + 1) l = some sa := den_succ hdl1
                  have hdr2 : den (f + 1 + 1) r = some fo := den_succ hdr1
                  have hev1 : evalN (f + 1) sa fo = some x := evalN_succ hv
                  have hpc : ncost (f + 1 + 1) sa fo = ncost (f + 1) sa fo := ncost_succ hev1
                  simp only [vcostN, hdl1, hdr1, hdl2, hdr2, hpc, ihl', ihr']

theorem vcostN_mono {F G : Nat} {v : Verb} {x : Noun}
    (hle : F ≤ G) (hok : editOk v = true) (hv : den F v = some x) : vcostN G v = vcostN F v := by
  induction hle with
  | refl => rfl
  | @step m h ih => rw [vcostN_succ hok (den_mono h hv)]; exact ih

/-! ### OP₆ strict local decrease (ncost) -/

theorem op6_decreaseN {g : Nat} {L b thn els : Verb} {x : Noun} {rn2 rc : Action}
    (hL : isTerminal L = true) (htc : isTerminal (Verb.node rc thn els) = true)
    (hthn : isTerminal thn = true) (htels : isTerminal els = true)
    (hgc : den g (Verb.node rc thn els) = some (Verb.node rc thn els).noun)
    (hdL : den (g + 1 + 1) L = some L.noun)
    (h4b : den (g + 1 + 1) (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
        = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)))
    (ht4 : isTerminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true)
    (ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true)
    (hvv : evalN (g + 1) L.noun
        (Noun.cell (Noun.atom 6) (Verb.node rn2 b (Verb.node rc thn els)).noun) = some x) :
    vcostN (g + 1 + 1)
        (Verb.node .star L
          (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L
                    (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
      < ncost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by
  have hleaf0 : isTerminal (Verb.leaf 0) = true := rfl
  have h23 : den (g + 1 + 1) (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
      = some (Noun.cell (Noun.atom 2) (Noun.atom 3)) :=
    den_null_val (by simp only [den]) (by simp only [den])
  have hdc : den (g + 1 + 1) (Verb.node rc thn els) = some (Verb.node rc thn els).noun :=
    den_succ (den_succ hgc)
  simp only [noun, evalN] at hvv
  cases hsb : evalN g L.noun b.noun with
  | none => rw [hsb] at hvv; simp at hvv
  | some sbv =>
    rw [hsb] at hvv
    have hEvb : Ev L.noun b.noun sbv := ⟨g, hsb⟩
    have hsb1 : evalN (g + 1) L.noun b.noun = some sbv := evalN_succ hsb
    have eqLb : ncost g L.noun b.noun = ncost (g + 1) L.noun b.noun :=
      ncost_align hsb (Nat.le_refl g) (by omega)
    have hSFinner : ncost (g + 1 + 1) L.noun (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4)
      b.noun))
        = 4 + ncost g L.noun b.noun := by simp only [ncost]; omega
    have hbound : ∀ (branchNoun : Verb),
        (sbv = Noun.atom 0 ∧ branchNoun = thn ∨ sbv = Noun.atom 1 ∧ branchNoun = els) →
        evalN g L.noun branchNoun.noun = some x →
        vcostN (g + 1 + 1)
          (Verb.node .star L
            (Verb.node .star (Verb.node rc thn els)
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                  (Verb.node .null (Verb.leaf 0)
                    (Verb.node .star L
                      (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
        < ncost (g + 1 + 1) L.noun
            (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by
      intro branchNoun hbr hbev
      have eqBr : ncost (g + 1 + 1) L.noun branchNoun.noun = ncost (g + 1) L.noun branchNoun.noun :=
        ncost_align hbev (by omega) (by omega)
      have hRHS : ncost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun
          = 100 + ncost (g + 1) L.noun b.noun + ncost (g + 1) L.noun branchNoun.noun := by
        rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [noun, ncost, hsb1]
      rw [hRHS]
      simp only [vcostN_star_eq, vcostN_null_eq, vcostN_terminal L hL,
        vcostN_terminal (Verb.node rc thn els) htc,
        vcostN_terminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) ht23,
        vcostN_terminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) ht4,
        vcostN_terminal (Verb.leaf 0) hleaf0, hdL, h4b, Nat.add_zero, Nat.zero_add]
      have hc0le : (match den (g + 1 + 1) (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)),
            den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
              (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))
                with
          | some sa, some fo => ncost (g + 1 + 1) sa fo | _, _ => 0) ≤ 2 := by
        rw [h23]
        cases hd0 : den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
            (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))
              with
        | none => simp
        | some dv => obtain ⟨w, rfl⟩ := den_null_leaf0 hd0; simp only [ncost]; omega
      have ha0le : (match den (g + 1 + 1) (Verb.node rc thn els),
            den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                    b)))))) with
          | some sa, some fo => ncost (g + 1 + 1) sa fo | _, _ => 0) ≤ 2 := by
        rw [hdc]
        cases hb0 : den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
            (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                  b)))))) with
        | none => simp
        | some bv => obtain ⟨w, rfl⟩ := den_null_leaf0 hb0; simp only [ncost]; omega
      have hrrle : (match some L.noun,
            den (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                  (Verb.node .null (Verb.leaf 0)
                    (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                      b))))))) with
          | some sa, some fo => ncost (g + 1 + 1) sa fo | _, _ => 0)
          ≤ ncost (g + 1) L.noun branchNoun.noun := by
        cases haa : den (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4)
                    b))))))) with
        | none => simp
        | some aa =>
            simp only
            have hDa0 : Den (Verb.node .star (Verb.node rc thn els)
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                    (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf
                        4) b))))))) aa :=
              ⟨g + 1 + 1, haa⟩
            rw [Den_star] at hDa0
            obtain ⟨cv, b0v, hDc0, hDb0, hEva0⟩ := hDa0
            have : cv = (Verb.node rc thn els).noun := (Den_terminal_iff htc).1 hDc0
            subst this
            rw [Den_null] at hDb0
            obtain ⟨z, c0v, rfl, hDz, hDc0'⟩ := hDb0
            have : z = Noun.atom 0 := Den_leaf.1 hDz
            subst this
            rw [EvN_op0] at hEva0
            obtain ⟨ax, rfl, hslotA⟩ := hEva0
            rw [Den_star] at hDc0'
            obtain ⟨p23, d0v, hD23, hDd0, hEvc0⟩ := hDc0'
            have hp23 : p23 = Noun.cell (Noun.atom 2) (Noun.atom 3) := by
              have := (Den_terminal_iff ht23).1 hD23; simpa only [noun] using this
            subst hp23
            rw [Den_null] at hDd0
            obtain ⟨z2, iv, rfl, hDz2, hDinner⟩ := hDd0
            have : z2 = Noun.atom 0 := Den_leaf.1 hDz2
            subst this
            rw [EvN_op0] at hEvc0
            obtain ⟨ax2, rfl, hslotB⟩ := hEvc0
            rw [Den_star] at hDinner
            obtain ⟨Lv, fv, hDL', hD4, hEvinner⟩ := hDinner
            have : Lv = L.noun := (Den_terminal_iff hL).1 hDL'
            subst this
            have hfv : fv = Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun) := by
              have := (Den_terminal_iff ht4).1 hD4; simpa only [noun] using this
            subst hfv
            rw [EvN_op4] at hEvinner
            obtain ⟨y, hEvy, hlusy⟩ := hEvinner
            rw [EvN_op4] at hEvy
            obtain ⟨y2, hEvy2, hlusy2⟩ := hEvy
            have hy2 : y2 = sbv := EvN_det hEvy2 hEvb
            subst hy2
            rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · have hy : y = Noun.atom 1 := by
                rw [lus_atom] at hlusy2; exact (Option.some.inj hlusy2).symm
              subst hy
              have hax2 : ax2 = 2 := by
                rw [lus_atom] at hlusy; exact (Noun.atom.inj (Option.some.inj hlusy)).symm
              subst hax2
              rw [slot_two] at hslotB
              have hax : ax = 2 := (Noun.atom.inj (Option.some.inj hslotB)).symm
              subst hax
              rw [noun, slot_two] at hslotA
              obtain rfl := Option.some.inj hslotA
              exact eqBr.le
            · have hy : y = Noun.atom 2 := by
                rw [lus_atom] at hlusy2; exact (Option.some.inj hlusy2).symm
              subst hy
              have hax2 : ax2 = 3 := by
                rw [lus_atom] at hlusy; exact (Noun.atom.inj (Option.some.inj hlusy)).symm
              subst hax2
              rw [slot_three] at hslotB
              have hax : ax = 3 := (Noun.atom.inj (Option.some.inj hslotB)).symm
              subst hax
              rw [noun, slot_three] at hslotA
              obtain rfl := Option.some.inj hslotA
              exact eqBr.le
      rw [hSFinner]
      cases evaluatedZero : den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf
                        4) b))))
        <;> cases evaluatedOne : den (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                        (Verb.node .null (Verb.leaf 0)
                          (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null
                            (Verb.leaf 4) b))))))
        <;> cases evaluatedTwo : den (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
                      (Verb.node .null (Verb.leaf 0)
                        (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                          (Verb.node .null (Verb.leaf 0)
                            (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null
                              (Verb.leaf 4) b)))))))
        <;> simp only [hdc, h23, evaluatedZero, evaluatedOne, evaluatedTwo]
          at hc0le ha0le hrrle ⊢
        <;> omega
    cases sbv with
    | cell k1 k2 => simp at hvv
    | atom av =>
        match av, hvv with
        | 0, hvv => exact hbound thn (Or.inl ⟨rfl, rfl⟩) hvv
        | 1, hvv => exact hbound els (Or.inr ⟨rfl, rfl⟩) hvv
        | (k + 2), hvv => simp at hvv

/-! ### (e) `cost_localN` — strict local decrease at a `redexHint` redex -/

private theorem hint_composition_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true)
  (n2 : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : den (g + 1) L = some L.noun) (hdL : den (g + 1 + 1) L
    = some L.noun)
  (hgn2 : den g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 2)
    n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 2).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 2) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨hg1b, hg1c⟩ :=
        den_term_children (editOk_of_terminal hn2t) (den_succ hgn2) htb htc
      have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ hg1b
      have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
      simp only [noun, evalN] at hvv
      cases hb : evalN g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
        cases hc : evalN g L.noun c.noun with
        | none => rw [hb, hc] at hvv; simp at hvv
        | some sc =>
          rw [hb, hc] at hvv
          have hb' : evalN (g + 1) L.noun b.noun = some sb := evalN_succ hb
          have hc' : evalN (g + 1) L.noun c.noun = some sc := evalN_succ hc
          have hd_Lb : den (g + 1 + 1) (Verb.node .star L b) = some sb :=
            den_star_val hfL hg1b hb'
          have hd_Lc : den (g + 1 + 1) (Verb.node .star L c) = some sc :=
            den_star_val hfL hg1c hc'
          have eq_b : ncost (g + 1 + 1) L.noun b.noun = ncost (g + 1) L.noun b.noun :=
            ncost_align hb (by omega) (by omega)
          have eq_c : ncost (g + 1 + 1) L.noun c.noun = ncost (g + 1) L.noun c.noun :=
            ncost_align hc (by omega) (by omega)
          have eq_sbsc : ncost (g + 1 + 1) sb sc = ncost (g + 1) sb sc :=
            ncost_align hvv (by omega) (by omega)
          simp only [vcostN_star_eq, hd_Lb, hd_Lc,
            vcostN_star_terminal hL htb hdL hdb_f1,
            vcostN_star_terminal hL htc hdL hdc_f1]
          simp only [noun, ncost, hb', hc']
          rw [eq_b, eq_c, eq_sbsc]
          omega

private theorem hint_conditional_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true)
  (n2 : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : den (g + 1 + 1) L = some L.noun) (hgn2 : den g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 6) n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 6).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 6) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      have hct : isTerminal c = true := htc
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨hgb, hgcv⟩ :=
        den_term_children (editOk_of_terminal hn2t) hgn2 htb htc
      have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ (den_succ hgb)
      have h4a : den (g + 1) (Verb.node .null (Verb.leaf 4) b)
          = some (Noun.cell (Noun.atom 4) b.noun) :=
        den_null_val (by simp only [den]) hgb
      have h4b : den (g + 1 + 1)
          (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
          = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)) :=
        den_null_val (by simp only [den]) h4a
      have ht4 : isTerminal
          (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true := by
        simp [isTerminal, Action.isNull, htb]
      have ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true := by
        simp [isTerminal, Action.isNull]
      cases c with
      | leaf ck => exfalso; simp only [noun, evalN] at hvv; simp at hvv
      | node rc thn els =>
          have hct2 : isTerminal (Verb.node rc thn els) = true := hct
          rw [isTerminal_node] at hct; simp only [Bool.and_eq_true] at hct
          obtain ⟨⟨hrc, hthn⟩, htels⟩ := hct
          exact op6_decreaseN hL hct2 hthn htels hgcv hdL h4b ht4 ht23 hvv

private theorem hint_arm_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : den (g + 1) L = some L.noun) (hdL : den (g + 1 + 1) L
    = some L.noun)
  (hgn2 : den g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 9)
    n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 9).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 9) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      have hrn2' : rn2 = Action.null := by cases rn2 <;> simp_all [Action.isNull]
      subst hrn2'
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl := Option.some.inj hr
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := by
        cases g with | zero => simp [den] at hgn2 | succ n => exact ⟨n, rfl⟩
      obtain ⟨hhb, hhc⟩ := den_term_split htb htc hgn2
      cases b with
      | node bb bc bd => simp [noun, evalN] at hvv
      | leaf ax0 =>
          simp only [noun, evalN] at hvv
          cases hcor : evalN (g' + 1) L.noun c.noun with
          | none => simp [hcor] at hvv
          | some cor =>
            simp only [hcor] at hvv
            cases harm : Noun.slot ax0 cor with
            | none => simp [harm] at hvv
            | some arm =>
              simp only [harm] at hvv
              have hg2c : den (g' + 1 + 1) c = some c.noun := den_succ (den_succ hhc)
              have hdc_f1 : den (g' + 1 + 1 + 1) c = some c.noun := den_succ hg2c
              have hcor2 : evalN (g' + 2) L.noun c.noun = some cor :=
                evalN_succ hcor
              have hd_core : den (g' + 1 + 1 + 1) (Verb.node .star L c) = some cor :=
                den_star_val hfL hg2c hcor2
              have hb0 : den g' (Verb.leaf 0) = some (Noun.atom 0) := by simp only [den]
              have hb1 : den g' (Verb.leaf 1) = some (Noun.atom 1) := by simp only [den]
              have hf0h : den (g' + 1) (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0))
                  = some (Noun.cell (Noun.atom 0) (Noun.atom ax0)) := den_null_val hb0 hhb
              have hf01 : den (g' + 1) (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                  = some (Noun.cell (Noun.atom 0) (Noun.atom 1)) := den_null_val hb0 hb1
              have hM : den (g' + 1 + 1)
                    (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                      (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0)))
                  = some (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                      (Noun.cell (Noun.atom 0) (Noun.atom ax0))) := den_null_val hf01 hf0h
              have h2 : den (g' + 1 + 1) (Verb.leaf 2) = some (Noun.atom 2) := by
                simp only [den]
              have hform : den (g' + 1 + 1 + 1)
                    (Verb.node .null (Verb.leaf 2)
                      (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                        (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0))))
                  = some (Noun.cell (Noun.atom 2)
                      (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                        (Noun.cell (Noun.atom 0) (Noun.atom ax0)))) := den_null_val h2 hM
              have hformT : isTerminal
                  (Verb.node .null (Verb.leaf 2)
                    (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                      (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0)))) = true := by
                simp [isTerminal, Action.isNull]
              have hev01 : evalN (g' + 2) cor
                  (Noun.cell (Noun.atom 0) (Noun.atom 1)) = some cor := by
                simp only [evalN]; exact slot_one
              have hev0h : evalN (g' + 2) cor
                  (Noun.cell (Noun.atom 0) (Noun.atom ax0)) = some arm := by
                simp only [evalN]; exact harm
              have eq_c1 : ncost (g' + 1 + 1 + 1) L.noun c.noun
                  = ncost (g' + 2) L.noun c.noun := ncost_align hcor (by omega) (by omega)
              have hRHS : ncost (g' + 1 + 1 + 1) L.noun
                  (Verb.node .null (Verb.leaf 9) (Verb.node .null (Verb.leaf ax0) c)).noun
                  = 20 + ncost (g' + 2) L.noun c.noun + ncost (g' + 2) cor arm := by
                simp only [noun, ncost, hcor2, harm]
              rw [hRHS]
              simp only [vcostN_star_eq, hd_core, hform,
                vcostN_star_terminal hL htc hdL hdc_f1, vcostN_terminal _ hformT]
              simp only [ncost, hev01, hev0h]
              change 1 + 2 + 2 + ncost (g' + 2) cor arm
                  + ncost (g' + 1 + 1 + 1) L.noun c.noun + 0
                < 20 + ncost (g' + 2) L.noun c.noun + ncost (g' + 2) cor arm
              rw [eq_c1]
              omega

private theorem hint_edit_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : den (g + 1 + 1) L = some L.noun) (hgn2 : den g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 10) n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 10).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 10) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 hd d =>
      cases hd with
      | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
      | node rhd axv c =>
          have hn2t : isTerminal (Verb.node rn2 (Verb.node rhd axv c) d) = true := htn2
          rw [isTerminal_node] at htn2; simp only [Bool.and_eq_true] at htn2
          obtain ⟨⟨hrn2, hthd⟩, htd⟩ := htn2
          have hhdt : isTerminal (Verb.node rhd axv c) = true := hthd
          rw [isTerminal_node] at hthd; simp only [Bool.and_eq_true] at hthd
          obtain ⟨⟨hrhd, htaxv⟩, htc⟩ := hthd
          simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl := Option.some.inj hr
          obtain ⟨hg1hd, hg1d⟩ :=
            den_term_children (editOk_of_terminal hn2t) (den_succ hgn2) hhdt htd
          obtain ⟨hg1axv, hg1c⟩ :=
            den_term_children (editOk_of_terminal hhdt) hg1hd htaxv htc
          have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
          have hdd_f1 : den (g + 1 + 1) d = some d.noun := den_succ hg1d
          cases axv with
          | node b0 c0 d0 => simp [noun, evalN] at hvv
          | leaf a0 =>
              simp only [noun, evalN] at hvv
              cases hnew : evalN g L.noun c.noun with
              | none => rw [hnew] at hvv; simp at hvv
              | some new =>
                cases hold : evalN g L.noun d.noun with
                | none => rw [hnew, hold] at hvv; simp at hvv
                | some old =>
                    have eq_c : ncost (g + 1 + 1) L.noun c.noun
                        = ncost (g + 1) L.noun c.noun := ncost_align hnew (by omega) (by omega)
                    have eq_d : ncost (g + 1 + 1) L.noun d.noun
                        = ncost (g + 1) L.noun d.noun := ncost_align hold (by omega) (by omega)
                    rw [vcostN_edit_eq, vcostN_null_eq,
                      vcostN_star_terminal hL htc hdL hdc_f1,
                      vcostN_star_terminal hL htd hdL hdd_f1]
                    simp only [vcostN, noun, ncost]
                    rw [eq_c, eq_d]; omega

private theorem hint_opcode_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : den (g + 1 + 1) L = some L.noun) (hgn2 : den g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 11) n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 11).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 11) n2).noun := by
  cases n2 with
  | leaf k =>
      simp [noun, evalN] at hvv
  | node rn2 h2 b2 =>
      have hn2t : isTerminal (Verb.node rn2 h2 b2) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, hth2⟩, htb2⟩ := htn2
      have hgb2 : den g b2 = some b2.noun :=
        (den_term_children (editOk_of_terminal hn2t) hgn2 hth2 htb2).2
      cases h2 with
      | leaf t3 =>
          -- static hint: rr = *[L body]
          have hrr : redexHint (Verb.node .star L
              (Verb.node .null (Verb.leaf 11) (Verb.node rn2 (Verb.leaf t3) b2)))
              = some (Verb.node .star L b2) := by
            simp [redexHint, hintExpand, hL, hn2t, Action.isNull]
          rw [hrr] at hr
          obtain rfl := Option.some.inj hr
          simp only [noun, evalN] at hvv
          have hd2b2 : den (g + 1 + 1) b2 = some b2.noun := den_succ (den_succ hgb2)
          have hLHS : vcostN (g + 1 + 1) (Verb.node .star L b2)
              = ncost (g + 1 + 1) L.noun b2.noun :=
            vcostN_star_terminal hL htb2 hdL hd2b2
          have hRHS : ncost (g + 1 + 1) L.noun
              (Noun.cell (Noun.atom 11) (Noun.cell (Noun.atom t3) b2.noun))
              = 50 + ncost (g + 1) L.noun b2.noun := by simp only [ncost]
          have halign : ncost (g + 1 + 1) L.noun b2.noun = ncost (g + 1) L.noun b2.noun :=
            ncost_align hvv (by omega) (by omega)
          rw [hLHS]
          simp only [noun]
          rw [hRHS, halign]
          omega
      | node r3 t3 clue =>
          -- dynamic hint: rr = *[L (8 clue (7 [0 3] body))]
          have hh2t : isTerminal (Verb.node r3 t3 clue) = true := hth2
          simp only [isTerminal, Bool.and_eq_true] at hth2
          obtain ⟨⟨hr3, ht3⟩, htclue⟩ := hth2
          have hrr : redexHint (Verb.node .star L
              (Verb.node .null (Verb.leaf 11) (Verb.node rn2 (Verb.node r3 t3 clue) b2)))
              = some (Verb.node .star L
                  (Verb.node .null (Verb.leaf 8)
                    (Verb.node .null clue
                      (Verb.node .null (Verb.leaf 7)
                        (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2))))) := by
            simp [redexHint, hintExpand, hL, hn2t, Action.isNull]
          rw [hrr] at hr
          obtain rfl := Option.some.inj hr
          simp only [noun, evalN] at hvv
          cases hclue : evalN g L.noun clue.noun with
          | none => rw [hclue] at hvv; simp at hvv
          | some cv =>
              rw [hclue] at hvv
              obtain ⟨g0, rfl⟩ : ∃ g0, g = g0 + 1 := by
                cases g with
                | zero => simp [evalN] at hclue
                | succ n => exact ⟨n, rfl⟩
              have hclue1 : evalN (g0 + 2) L.noun clue.noun = some cv := evalN_succ hclue
              have hslot3 : evalN (g0 + 1) (Noun.cell cv L.noun)
                  (Noun.cell (Noun.atom 0) (Noun.atom 3)) = some L.noun := by
                simp [evalN, slot_three]
              have hMt : isTerminal
                  (Verb.node .null (Verb.leaf 8)
                    (Verb.node .null clue
                      (Verb.node .null (Verb.leaf 7)
                        (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2)))) = true
                          := by
                simp [isTerminal, Action.isNull, htclue, htb2]
              have hLHSle : vcostN (g0 + 1 + 1 + 1)
                  (Verb.node .star L
                    (Verb.node .null (Verb.leaf 8)
                      (Verb.node .null clue
                        (Verb.node .null (Verb.leaf 7)
                          (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2)))))
                  ≤ ncost (g0 + 1 + 1 + 1) L.noun
                      (Verb.node .null (Verb.leaf 8)
                        (Verb.node .null clue
                          (Verb.node .null (Verb.leaf 7)
                            (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3))
                              b2)))).noun := by
                rw [vcostN_star_eq, vcostN_terminal L hL, vcostN_terminal _ hMt,
                  Nat.add_zero, Nat.add_zero]
                cases hdL3 : den (g0 + 1 + 1 + 1) L with
                | none => simp
                | some sa =>
                    cases hdM : den (g0 + 1 + 1 + 1)
                        (Verb.node .null (Verb.leaf 8)
                          (Verb.node .null clue
                            (Verb.node .null (Verb.leaf 7)
                              (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2))))
                                with
                    | none => simp
                    | some Mv =>
                        have e1 : sa = L.noun := den_terminal_val hL hdL3
                        have e2 : Mv = (Verb.node .null (Verb.leaf 8)
                            (Verb.node .null clue
                              (Verb.node .null (Verb.leaf 7)
                                (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3))
                                  b2)))).noun :=
                          den_terminal_val hMt hdM
                        subst e1; subst e2; simp
              have hLHSval' : ncost (g0 + 1 + 1 + 1) L.noun
                  (Verb.node .null (Verb.leaf 8)
                    (Verb.node .null clue
                      (Verb.node .null (Verb.leaf 7)
                        (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 3)) b2)))).noun
                  = 4 + ncost (g0 + 2) L.noun clue.noun + ncost (g0 + 1) L.noun b2.noun := by
                simp only [noun, ncost, hclue1, hslot3]
                generalize ncost (g0 + 2) L.noun clue.noun = A
                generalize ncost (g0 + 1) L.noun b2.noun = B
                exact op11_arith A B
              have hRHS' : ncost (g0 + 1 + 1 + 1) L.noun
                  (Verb.node .null (Verb.leaf 11) (Verb.node rn2 (Verb.node r3 t3 clue) b2)).noun
                  = 50 + ncost (g0 + 2) L.noun clue.noun + ncost (g0 + 2) L.noun b2.noun := by
                simp only [noun, ncost, hclue1]
              have halign : ncost (g0 + 1) L.noun b2.noun = ncost (g0 + 2) L.noun b2.noun :=
                ncost_align hvv (by omega) (by omega)
              rw [hRHS']
              have key := hLHSval' ▸ hLHSle
              omega

private theorem hint_equality_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2
  : Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hdL : den (g + 1 + 1) L = some L.noun) (hgn2 : den g n2 =
    some n2.noun)
  (hr : (node Action.star L (node Action.null (leaf 5) n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 5).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 5) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
        Option.some.inj hr
      obtain ⟨hg1b, hg1c⟩ :=
        den_term_children (editOk_of_terminal hn2t) (den_succ hgn2) htb htc
      have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ hg1b
      have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
      simp only [noun, evalN] at hvv
      cases hb : evalN g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
        cases hc : evalN g L.noun c.noun with
        | none => rw [hb, hc] at hvv; simp at hvv
        | some sc =>
          have eq_b : ncost (g + 1 + 1) L.noun b.noun = ncost (g + 1) L.noun b.noun :=
            ncost_align hb (by omega) (by omega)
          have eq_c : ncost (g + 1 + 1) L.noun c.noun = ncost (g + 1) L.noun c.noun :=
            ncost_align hc (by omega) (by omega)
          rw [vcostN_equal_eq, vcostN_star_terminal hL htb hdL hdb_f1,
            vcostN_star_terminal hL htc hdL hdc_f1]
          simp only [noun, ncost]
          rw [eq_b, eq_c]; omega

private theorem hint_push_cost_decrease {L rr : Verb} {x : Noun} (hL : L.isTerminal = true) (n2 :
  Verb)
  (htn2 : n2.isTerminal = true) (g : ℕ) (hfL : den (g + 1) L = some L.noun) (hdL : den (g + 1 + 1) L
    = some L.noun)
  (hgn2 : den g n2 = some n2.noun) (hr : (node Action.star L (node Action.null (leaf 8)
    n2)).redexHint = some rr)
  (hvv : evalN (g + 1) L.noun ((atom 8).cell n2.noun) = some x) :
  vcostN (g + 1 + 1) rr < ncost (g + 1 + 1) L.noun (node Action.null (leaf 8) n2).noun := by
  cases n2 with
  | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
  | node rn2 b c =>
      have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
      simp only [isTerminal, Bool.and_eq_true] at htn2
      obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
      simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
        Option.some.inj hr
      obtain ⟨hgb, hgc⟩ :=
        den_term_children (editOk_of_terminal hn2t) hgn2 htb htc
      have hg1b : den (g + 1) b = some b.noun := den_succ hgb
      have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ hg1b
      have hg1c : den (g + 1) c = some c.noun := den_succ hgc
      have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
      simp only [noun, evalN] at hvv
      cases hb : evalN g L.noun b.noun with
      | none => rw [hb] at hvv; simp at hvv
      | some sb =>
          rw [hb] at hvv
          have hb' : evalN (g + 1) L.noun b.noun = some sb := evalN_succ hb
          have eq_Lb : ncost (g + 1 + 1) L.noun b.noun = ncost (g + 1) L.noun b.noun
            :=
            ncost_align hb (by omega) (by omega)
          have eq_sbLc : ncost (g + 1 + 1) (Noun.cell sb L.noun) c.noun
              = ncost (g + 1) (Noun.cell sb L.noun) c.noun := ncost_align hvv (by
                omega) (by omega)
          have hRHS : ncost (g + 1 + 1) L.noun
              (Verb.node .null (Verb.leaf 8) (Verb.node rn2 b c)).noun
              = 1 + ncost (g + 1) L.noun b.noun
                  + ncost (g + 1) (Noun.cell sb L.noun) c.noun := by
            simp only [noun, ncost, hb']
          rw [hRHS]
          have hvcnull : vcostN (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
              = ncost (g + 1 + 1) L.noun b.noun := by
            rw [vcostN_null_eq, vcostN_star_terminal hL htb hdL hdb_f1,
              vcostN_terminal L hL,
              Nat.add_zero]
          cases hgL : den g L with
          | none =>
              have hnone : den (g + 1) (Verb.node .star L b) = none := by
                simp only [den, hgL]
              have hsubjn : den (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
                = none :=
                den_null_none hnone
              rw [vcostN_star_eq]
              simp only [hsubjn, hvcnull, vcostN_terminal c htc]
              rw [eq_Lb]
              omega
          | some vL =>
              have hvL : vL = L.noun := den_terminal_val hL hgL
              subst hvL
              have hd_Lb_g : den (g + 1) (Verb.node .star L b) = some sb :=
                den_star_val hgL hgb hb
              have hd_subj : den (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
                  = some (Noun.cell sb L.noun) := den_null_val hd_Lb_g hfL
              rw [vcostN_star_eq]
              simp only [hd_subj, hdc_f1, hvcnull, vcostN_terminal c htc]
              rw [eq_Lb, eq_sbLc]
              omega

theorem cost_localN {F : Nat} {L R rr : Verb} {x : Noun}
    (hL : isTerminal L = true) (hR : isTerminal R = true)
    (hv : den F (Verb.node .star L R) = some x)
    (hr : redexHint (Verb.node .star L R) = some rr) :
    vcostN F rr < vcostN F (Verb.node .star L R) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [den] at hv
    | succ n => exact ⟨n, rfl⟩
  have hvv := hv
  simp only [den] at hvv
  cases hfL : den f L with
  | none => rw [hfL] at hvv; simp at hvv
  | some sL =>
    cases hfR : den f R with
    | none => rw [hfL, hfR] at hvv; simp at hvv
    | some sR =>
      rw [hfL, hfR] at hvv
      have hsL : sL = L.noun := den_terminal_val hL hfL
      have hsR : sR = R.noun := den_terminal_val hR hfR
      subst hsL; subst hsR
      have hdL : den (f + 1) L = some L.noun := den_succ hfL
      have hvcL : vcostN (f + 1) L = 0 := vcostN_terminal L hL (f + 1)
      have hvcR : vcostN (f + 1) R = 0 := vcostN_terminal R hR (f + 1)
      have hstar : vcostN (f + 1) (Verb.node .star L R) = ncost (f + 1) L.noun R.noun := by
        simp only [vcostN, hdL, den_succ hfR, hvcL, hvcR, Nat.add_zero]
      rw [hstar]
      cases R with
      | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
      | node ra i n2 =>
          have hRt : isTerminal (Verb.node ra i n2) = true := hR
          simp only [isTerminal, Bool.and_eq_true] at hR
          obtain ⟨⟨hra, hti⟩, htn2⟩ := hR
          have hra0 : ra = Action.null := by cases ra <;> simp_all [Action.isNull]
          subst hra0
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := by
            cases f with
            | zero => simp [den] at hfR
            | succ n => exact ⟨n, rfl⟩
          obtain ⟨hgi, hgn2⟩ := den_term_split hti htn2 hfR
          have hdi_f1 : den (g + 1 + 1) i = some i.noun := den_succ (den_succ hgi)
          have hdn2_f1 : den (g + 1 + 1) n2 = some n2.noun := den_succ (den_succ hgn2)
          have hvci : vcostN (g + 1 + 1) i = 0 := vcostN_terminal i hti _
          have hvcn2 : vcostN (g + 1 + 1) n2 = 0 := vcostN_terminal n2 htn2 _
          cases i with
          | node bi ic id =>
              simp only [redexHint, hintExpand, reduce, redex] at hr
              obtain rfl := Option.some.inj hr
              simp only [noun, evalN] at hvv
              cases he1 : evalN g L.noun (Noun.cell ic.noun id.noun) with
              | none => rw [he1] at hvv; simp at hvv
              | some l' =>
                  cases he2 : evalN g L.noun n2.noun with
                  | none => rw [he1, he2] at hvv; simp at hvv
                  | some r' =>
                      have e_i : ncost (g + 1 + 1) L.noun (Noun.cell ic.noun id.noun)
                          = ncost (g + 1) L.noun (Noun.cell ic.noun id.noun) :=
                        ncost_align he1 (by omega) (by omega)
                      have e_n2 : ncost (g + 1 + 1) L.noun n2.noun = ncost (g + 1) L.noun n2.noun :=
                        ncost_align he2 (by omega) (by omega)
                      rw [vcostN_null_eq,
                        vcostN_star_terminal hL hti hdL hdi_f1,
                        vcostN_star_terminal hL htn2 hdL hdn2_f1]
                      simp only [noun, ncost]
                      rw [e_i, e_n2]
                      omega
          | leaf op =>
              have hop : op < 12 := by
                rcases Nat.lt_or_ge op 12 with h | h
                · exact h
                · exfalso
                  simp only [noun] at hvv
                  rw [evalN_op_ge12_none (g + 1) L.noun n2.noun op h] at hvv
                  simp at hvv
              simp only [noun] at hvv
              interval_cases op
              · -- OP0
                simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                  Option.some.inj hr
                rw [vcostN_slot_eq, vcostN_terminal n2 htn2, vcostN_terminal L hL]
                simp only [noun, ncost]; omega
              · -- OP1
                simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                  Option.some.inj hr
                rw [vcostN_terminal n2 htn2]
                simp only [noun, ncost]; omega
              · -- OP2
                exact hint_composition_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP3
                simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                  Option.some.inj hr
                simp only [evalN, Option.map_eq_some_iff] at hvv
                obtain ⟨y, hy, _⟩ := hvv
                have e_n2 : ncost (g + 1 + 1) L.noun n2.noun = ncost (g + 1) L.noun n2.noun :=
                  ncost_align hy (by omega) (by omega)
                rw [vcostN_minus_eq, vcostN_star_terminal hL htn2 hdL hdn2_f1]
                simp only [vcostN, noun, ncost]
                rw [e_n2]; omega
              · -- OP4
                simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                  Option.some.inj hr
                simp only [evalN, Option.bind_eq_some_iff] at hvv
                obtain ⟨y, hy, _⟩ := hvv
                have e_n2 : ncost (g + 1 + 1) L.noun n2.noun = ncost (g + 1) L.noun n2.noun :=
                  ncost_align hy (by omega) (by omega)
                rw [vcostN_minus_eq, vcostN_star_terminal hL htn2 hdL hdn2_f1]
                simp only [vcostN, noun, ncost]
                rw [e_n2]; omega
              · -- OP5
                exact hint_equality_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
              · -- OP6
                exact hint_conditional_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
              · -- OP7
                cases n2 with
                | leaf k => simp [redexHint, hintExpand, reduce, redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    simp only [redexHint, hintExpand, reduce, redex] at hr; obtain rfl :=
                      Option.some.inj hr
                    obtain ⟨hg1b, hg1c⟩ :=
                      den_term_children (editOk_of_terminal hn2t) (den_succ hgn2) htb htc
                    have hdb_f1 : den (g + 1 + 1) b = some b.noun := den_succ hg1b
                    have hdc_f1 : den (g + 1 + 1) c = some c.noun := den_succ hg1c
                    simp only [noun, evalN] at hvv
                    cases hb : evalN g L.noun b.noun with
                    | none => rw [hb] at hvv; simp at hvv
                    | some sb =>
                        rw [hb] at hvv
                        have hb' : evalN (g + 1) L.noun b.noun = some sb := evalN_succ hb
                        have hd_Lb : den (g + 1 + 1) (Verb.node .star L b) = some sb :=
                          den_star_val hfL hg1b hb'
                        have eq_b : ncost (g + 1 + 1) L.noun b.noun = ncost (g + 1) L.noun b.noun :=
                          ncost_align hb (by omega) (by omega)
                        have eq_sbc : ncost (g + 1 + 1) sb c.noun = ncost (g + 1) sb c.noun :=
                          ncost_align hvv (by omega) (by omega)
                        simp only [vcostN_star_eq, hd_Lb, hdc_f1,
                          vcostN_star_terminal hL htb hdL hdb_f1, vcostN_terminal c htc]
                        simp only [noun, ncost, hb']
                        rw [eq_b, eq_sbc]; omega
              · -- OP8
                exact hint_push_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP9
                exact hint_arm_cost_decrease hL n2 htn2 g hfL hdL hgn2 hr hvv
              · -- OP10
                exact hint_edit_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
              · -- OP11 (hint expansion)
                exact hint_opcode_cost_decrease hL n2 htn2 g hdL hgn2 hr hvv
/-! ### (f) step congruence and `cost_stepN` -/

theorem enum_den_F {F : Nat} : ∀ (v : Verb), editOk v = true → ∀ (c : Nat) (x : Noun),
    den F v = some x → ∀ p ∈ (enum v c).2, ∃ y, den F p.2 = some y := by
  intro v
  induction v with
  | leaf k => intro _ c x _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro hok c x hd p hp
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := den_children_F hok hd
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; exact ⟨x, hd⟩
      · exact ihl hokl (c + 1) yl hyl p hleft
      · exact ihr hokr _ yr hyr p hright

theorem den_F_subnode {F : Nat} {v : Verb} {x : Noun} (hok : editOk v = true)
    (hv : den F v = some x) {i : Nat} {sub : Verb} (hmap : map i v = some sub) :
    ∃ y, den F sub = some y :=
  enum_den_F v hok 0 x hv (i, sub) (mem_nodes_of_map hmap)

theorem den_F_swap_eq {F : Nat} {w w' : Verb} (hok : editOk w = true) (hrel : Rel w w')
    {a b : Noun} (ha : den F w = some a) (hb : den F w' = some b) : a = b := by
  have hiff := Rel_den w.noun.size w w' (Nat.le_refl _) hrel hok a
  exact den_det (hiff.1 ⟨F, ha⟩) ⟨F, hb⟩

theorem vcostN_replace_cong (F i : Nat) (sub r₀ : Verb) (hpend : sub.isPending = true)
    (hgraph : ∀ y, Den sub y ↔ Den r₀ y) (hr0 : editOk r₀ = true) :
    ∀ (v : Verb) (c : Nat) (xv xv' : Noun),
      editOk v = true →
      findAt i (enum v c).2 = some sub →
      den F v = some xv →
      den F (replaceAux i r₀ v c).2 = some xv' →
      vcostN F (replaceAux i r₀ v c).2 + vcostN F sub = vcostN F v + vcostN F r₀ := by
  intro v
  induction v with
  | leaf k => intro c xv xv' _ hfind; simp [enum, findAt] at hfind
  | node a l r ihl ihr =>
      intro c xv xv' hok hfind hdv hdv'
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      by_cases hci : c = i
      · subst hci
        have hf : findAt c (enum (Verb.node a l r) c).2 = some (Verb.node a l r) := by
          simp [enum, findAt]
        have hsub : Verb.node a l r = sub := (Option.some.inj (hf.symm.trans hfind))
        have hrepl : (replaceAux c r₀ (Verb.node a l r) c).2 = r₀ := by simp [replaceAux]
        rw [hrepl, ← hsub]
        omega
      · have hine : ¬ (i = c) := fun h => hci h.symm
        have hcL : (replaceAux i r₀ l (c + 1)).1 = (enum l (c + 1)).1 := replaceAux_counter i r₀ l
          (c + 1)
        have hfind' : findAt i (enum l (c + 1)).2 = some sub ∧
              findAt i (enum r (enum l (c + 1)).1).2 = none
            ∨ findAt i (enum l (c + 1)).2 = none ∧
              findAt i (enum r (enum l (c + 1)).1).2 = some sub := by
          simp only [enum, findAt, ite_eq_right hine] at hfind
          rw [findAt_append] at hfind
          cases hl : findAt i (enum l (c + 1)).2 with
          | some s => rw [hl] at hfind; exact Or.inl ⟨hfind, by
              cases hr : findAt i (enum r (enum l (c + 1)).1).2 with
              | none => rfl
              | some s2 =>
                  exfalso
                  have h1 := enum_index_range l (c + 1) (i, s) (findAt_some_mem hl)
                  have h2 := enum_index_range r (enum l (c + 1)).1 (i, s2) (findAt_some_mem hr)
                  omega⟩
          | none => rw [hl] at hfind; exact Or.inr ⟨rfl, hfind⟩
        obtain ⟨⟨xl, hxl⟩, ⟨xr, hxr⟩⟩ := den_children_F hok hdv
        have hok' : editOk (replaceAux i r₀ (Verb.node a l r) c).2 = true := by
          apply editOk_replaceAux i r₀ hr0 (Verb.node a l r) c hok
          intro s hs; have : s = sub := Option.some.inj (hs.symm.trans hfind); rw [this]; exact
            hpend
        simp only [replaceAux, ite_eq_right hci] at hdv' hok' ⊢
        rw [hcL] at hdv' hok' ⊢
        obtain ⟨⟨xl', hxl'⟩, ⟨xr', hxr'⟩⟩ := den_children_F hok' hdv'
        rcases hfind' with ⟨hLsub, hRnone⟩ | ⟨hLnone, hRsub⟩
        · have hrIH := ihl (c + 1) xl xl' hokl hLsub hxl hxl'
          have hreq : (replaceAux i r₀ r (enum l (c + 1)).1).2 = r := replaceAux_notMem i r₀ r _
            hRnone
          rw [hreq] at hxr' ⊢
          have hrelL : Rel l (replaceAux i r₀ l (c + 1)).2 := by
            apply replaceAux_rel i r₀ l (c + 1)
            intro s hs
            have : s = sub := Option.some.inj (hs.symm.trans hLsub)
            rw [this]; exact ⟨hpend, hgraph⟩
          have hlEq : xl = xl' := den_F_swap_eq hokl hrelL hxl hxl'
          cases a <;>
            simp only [vcostN_star_eq, vcostN_null_eq, vcostN_wut_eq, vcostN_slot_eq,
              vcostN_equal_eq,
              vcostN_minus_eq, vcostN_edit_eq, hxl, hxl', hxr, hlEq] <;> omega
        · have hrIH := ihr (enum l (c + 1)).1 xr xr' hokr hRsub hxr hxr'
          have hleq : (replaceAux i r₀ l (c + 1)).2 = l := replaceAux_notMem i r₀ l _ hLnone
          rw [hleq] at hxl' ⊢
          have hrelR : Rel r (replaceAux i r₀ r (enum l (c + 1)).1).2 := by
            apply replaceAux_rel i r₀ r (enum l (c + 1)).1
            intro s hs
            have : s = sub := Option.some.inj (hs.symm.trans hRsub)
            rw [this]; exact ⟨hpend, hgraph⟩
          have hrEq : xr = xr' := den_F_swap_eq hokr hrelR hxr hxr'
          cases a <;>
            simp only [vcostN_star_eq, vcostN_null_eq, vcostN_wut_eq, vcostN_slot_eq,
              vcostN_equal_eq,
              vcostN_minus_eq, vcostN_edit_eq, hxr, hxr', hxl, hrEq] <;> omega

theorem cost_stepN {F : Nat} {v v' : Verb} {x x' : Noun}
    (hwf : editOk v = true) (hv : den F v = some x) (hv' : den F v' = some x')
    (h : nextHint v = some v') : vcostN F v' < vcostN F v := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'eq⟩ := nextHint_eq_some_iff.1 h
  have hgi : getIndex v = some i := getIndex_eq_some_iff.2 hmax
  have hoksub : editOk sub = true := editOk_enum v 0 hwf (i, sub) (mem_nodes_of_map hmap)
  have hokr0 : editOk r₀ = true := editOk_redexHint hred hoksub
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hgraph : ∀ y, Den sub y ↔ Den r₀ y := fun y => denHint_local hdom hred
  obtain ⟨xs, hxs⟩ := den_F_subnode hwf hv hmap
  have hlocal : vcostN F r₀ < vcostN F sub := by
    cases sub with
    | leaf k => simp [isPending] at hpsub
    | node a L R =>
        obtain ⟨hL, hR⟩ := children_terminal_of_getIndex hgi hmap
        cases a with
        | null => simp [isPending, Action.isNull] at hpsub
        | wut => simp [redexHint, hintExpand, reduce] at hred
        | star => exact cost_localN hL hR hxs hred
        | slot =>
            have hEXn : hintExpand (Verb.node .slot L R) = none := by simp [hintExpand]
            rw [redexHint_eq_reduce_of_hintExpand_none hEXn] at hred
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax => rw [reduce] at hred; simp only [noun] at hred
                           exact isTerminal_of_map_ofNoun hred
              | node a2 l2 r2 => rw [reduce] at hred; simp only [noun] at hred; simp at hred
            rw [vcostN_terminal r₀ ht0]
            simp only [vcostN_slot_eq, vcostN_terminal L hL, vcostN_terminal R hR]; omega
        | equal =>
            have hEXn : hintExpand (Verb.node .equal L R) = none := by simp [hintExpand]
            rw [redexHint_eq_reduce_of_hintExpand_none hEXn] at hred
            have ht0 : isTerminal r₀ = true := by
              rw [reduce] at hred; obtain rfl := Option.some.inj hred; exact ofNoun_terminal _
            rw [vcostN_terminal r₀ ht0]
            simp only [vcostN_equal_eq, vcostN_terminal L hL, vcostN_terminal R hR]; omega
        | minus =>
            have hEXn : hintExpand (Verb.node .minus L R) = none := by simp [hintExpand]
            rw [redexHint_eq_reduce_of_hintExpand_none hEXn] at hred
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax =>
                  rw [reduce] at hred; simp only [noun] at hred
                  split at hred
                  · obtain rfl := Option.some.inj hred; exact ofNoun_terminal _
                  · exact isTerminal_of_map_ofNoun hred
                  · simp at hred
              | node a2 l2 r2 => rw [reduce] at hred; simp only [noun] at hred; simp at hred
            rw [vcostN_terminal r₀ ht0]
            simp only [vcostN_minus_eq, vcostN_terminal L hL, vcostN_terminal R hR]; omega
        | edit =>
            have hEXn : hintExpand (Verb.node .edit L R) = none := by simp [hintExpand]
            rw [redexHint_eq_reduce_of_hintExpand_none hEXn] at hred
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax =>
                  cases R with
                  | leaf k => simp [reduce, noun] at hred
                  | node rb nw od =>
                      simp only [reduce, noun] at hred
                      exact isTerminal_of_map_ofNoun hred
              | node a2 l2 r2 => simp [reduce, noun] at hred
            rw [vcostN_terminal r₀ ht0]
            simp only [vcostN_edit_eq, vcostN_terminal L hL, vcostN_terminal R hR]; omega
  have hv'2 : den F (replaceAt i v r₀) = some x' := hv'eq ▸ hv'
  have hcong : vcostN F (replaceAt i v r₀) + vcostN F sub = vcostN F v + vcostN F r₀ :=
    vcostN_replace_cong F i sub r₀ hpsub hgraph hokr0 v 0 x x' hwf hmap hv hv'2
  rw [hv'eq]
  omega

/-! ### (c) `progressN` -/

/-- A `den`-defined, `editOk`, non-terminal verb has a `nextHint` successor. -/
theorem progressN {v : Verb} {x : Noun} (hwf : editOk v = true) (hd : Den v x)
    (hnt : isTerminal v = false) : ∃ v', nextHint v = some v' := by
  have hne : getIndex v ≠ none := by
    intro h; rw [getIndex_none_iff_terminal] at h; rw [h] at hnt; simp at hnt
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨sub, hmap⟩ := map_some_of_getIndex hi
  have hmax : IsMaxPending dfsLt v i := getIndex_eq_some_iff.1 hi
  have hsubp : sub.isPending = true := by
    obtain ⟨w, hw, hwp⟩ := hmax.1
    rw [hmap] at hw
    have heq : sub = w := Option.some.inj hw
    rw [heq]; exact hwp
  cases sub with
  | leaf k => simp [isPending] at hsubp
  | node a L R =>
      obtain ⟨hL, hR⟩ := children_terminal_of_getIndex hi hmap
      obtain ⟨y, hsuby⟩ := Den_subnode hwf hd hmap
      have hstepN : inDomainHint (Verb.node a L R) = true →
          (redexHint (Verb.node a L R)).isSome = true → ∃ v', nextHint v = some v' := by
        intro hdom hred
        cases hrr : redexHint (Verb.node a L R) with
        | none => rw [hrr] at hred; simp at hred
        | some rr =>
            exact ⟨replaceAt i v rr,
              nextHint_eq_some_iff.2 ⟨i, Verb.node a L R, rr, hmax, hmap, hdom, hrr, rfl⟩⟩
      cases a with
      | null => simp [isPending, Action.isNull] at hsubp
      | wut => exact absurd hsuby Den_wut
      | equal =>
          have hdom : inDomain (Verb.node .equal L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          exact hstepN (inDomainHint_of_inDomain hdom) (by simp [redexHint, hintExpand, reduce])
      | slot =>
          obtain ⟨ax, b, hLax, hRb, hslot⟩ := Den_slot.1 hsuby
          have hLn : L.noun = Noun.atom ax := ((Den_terminal_iff hL).1 hLax).symm
          have hbR : b = R.noun := (Den_terminal_iff hR).1 hRb
          subst hbR
          have hdom : inDomain (Verb.node .slot L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          exact hstepN (inDomainHint_of_inDomain hdom)
            (by simp [redexHint, hintExpand, reduce, hLn, hslot])
      | minus =>
          obtain ⟨b, hRb, hcase⟩ := Den_minus.1 hsuby
          have hbR : b = R.noun := (Den_terminal_iff hR).1 hRb
          subst hbR
          have hdom : inDomain (Verb.node .minus L R) = true := by
            simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL, hR]
          rcases hcase with ⟨hL3, _⟩ | ⟨hL4, hlus⟩
          · have hLn : L.noun = Noun.atom 3 := ((Den_terminal_iff hL).1 hL3).symm
            exact hstepN (inDomainHint_of_inDomain hdom)
              (by simp [redexHint, hintExpand, reduce, hLn])
          · have hLn : L.noun = Noun.atom 4 := ((Den_terminal_iff hL).1 hL4).symm
            exact hstepN (inDomainHint_of_inDomain hdom)
              (by simp [redexHint, hintExpand, reduce, hLn, hlus])
      | edit =>
          cases R with
          | leaf k => exact absurd hsuby Den_edit_leaf
          | node rb nw od =>
              simp only [isTerminal, Bool.and_eq_true] at hR
              obtain ⟨⟨hrb, hnw⟩, hod⟩ := hR
              obtain ⟨ax, n, o, hLax, hnwn, hodo, hedit⟩ := Den_edit_node.1 hsuby
              have hLn : L.noun = Noun.atom ax := ((Den_terminal_iff hL).1 hLax).symm
              have hnwn' : n = nw.noun := (Den_terminal_iff hnw).1 hnwn
              have hodo' : o = od.noun := (Den_terminal_iff hod).1 hodo
              subst hnwn'; subst hodo'
              have hdom : inDomain (Verb.node .edit L (Verb.node rb nw od)) = true := by
                simp [inDomain, inOpcodeDomain, opReady, Action.isOperator, hL,
                      isTerminal, hrb, hnw, hod]
              exact hstepN (inDomainHint_of_inDomain hdom)
                (by simp [redexHint, hintExpand, reduce, hLn, hedit])
      | star =>
          obtain ⟨a', b', hLa, hRb, hev⟩ := Den_star.1 hsuby
          have haL : a' = L.noun := (Den_terminal_iff hL).1 hLa
          have hbR : b' = R.noun := (Den_terminal_iff hR).1 hRb
          subst haL; subst hbR
          cases R with
          | leaf k =>
              exfalso; obtain ⟨f, hf⟩ := hev
              simp [noun, evalN_atom_none] at hf
          | node rb fi n2 =>
              simp only [isTerminal, Bool.and_eq_true] at hR
              obtain ⟨⟨hrb, hfi_t⟩, hn2⟩ := hR
              simp only [noun] at hev
              cases fi with
              | node bi ic id =>
                  exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb hfi_t hn2 rfl))
                    (by simp [redexHint, hintExpand, reduce, redex])
              | leaf op =>
                  simp only [noun] at hev
                  have hop : op < 12 := by
                    rcases Nat.lt_or_ge op 12 with h | h
                    · exact h
                    · exfalso
                      obtain ⟨f, hf⟩ := hev
                      rw [evalN_op_ge12_none f L.noun n2.noun op h] at hf
                      exact absurd hf (by simp)
                  interval_cases op
                  · exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                    decide)))
                      (by simp [redexHint, hintExpand, reduce, redex])
                  · exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                    decide)))
                      (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨hb, hc, _, _, hn2eq, _⟩ := EvN_op2.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                    decide)))
                      (by simp [redexHint, hintExpand, reduce, redex])
                  · exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                    decide)))
                      (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨hb, hc, _, _, hn2eq, _⟩ := EvN_op5.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨b, c, d, cv, hn2eq, _⟩ := EvN_op6.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨hb, hc, _, hn2eq, _⟩ := EvN_op7.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨hb, hc, _, hn2eq, _⟩ := EvN_op8.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨ax, c, _, _, hn2eq, _⟩ := EvN_op9.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 c2 d2 =>
                        exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2 (by
                          decide)))
                          (by simp [redexHint, hintExpand, reduce, redex])
                  · obtain ⟨ax, c, d, new, old, hn2eq, _⟩ := EvN_op10.1 hev
                    cases n2 with
                    | leaf k => rw [noun] at hn2eq; exact absurd hn2eq (by simp)
                    | node b2 hdd d2 =>
                        rw [noun] at hn2eq
                        have hhd : hdd.noun = Noun.cell (Noun.atom ax) c := (Noun.cell.inj hn2eq).1
                        cases hdd with
                        | leaf k => rw [noun] at hhd; exact absurd hhd (by simp)
                        | node bhd axv cc =>
                            exact hstepN (inDomainHint_of_inDomain (inDomain_star_of hL hrb rfl hn2
                              (by decide)))
                              (by simp [redexHint, hintExpand, reduce, redex])
                  · -- OP₁₁ hint redex
                    cases n2 with
                    | leaf k =>
                        exfalso; obtain ⟨f, hf⟩ := hev
                        simp only [noun] at hf
                        cases f with
                        | zero => simp [evalN] at hf
                        | succ ff => simp [evalN] at hf
                    | node rn2 h2 b2 =>
                        have hdomN : inDomainHint
                            (Verb.node .star L (Verb.node rb (Verb.leaf 11) (Verb.node rn2 h2 b2)))
                              = true := by
                          rw [inDomainHint]
                          have hhr : isHintRedex
                              (Verb.node .star L (Verb.node rb (Verb.leaf 11) (Verb.node rn2 h2
                                b2))) = true := by
                            simp [isHintRedex, hL, hrb, hn2]
                          rw [hhr]; simp
                        have hredN : (redexHint
                            (Verb.node .star L (Verb.node rb (Verb.leaf 11) (Verb.node rn2 h2
                              b2)))).isSome = true := by
                          cases h2 <;> simp [redexHint, hintExpand, hL, hrb, hn2]
                        exact hstepN hdomN hredN

/-! ### (g) `run_completeN` -/

theorem run_completeN {v : Verb} {x : Noun} (hok : editOk v = true) (hv : Den v x) :
    ∃ N, runHint N v = some x := by
  suffices aux : ∀ (bound F : Nat) (v : Verb) (x : Noun),
      editOk v = true → den F v = some x → vcostN F v < bound → ∃ N, runHint N v = some x by
    obtain ⟨F, hF⟩ := hv
    exact aux (vcostN F v + 1) F v x hok hF (Nat.lt_succ_self _)
  intro bound
  induction bound with
  | zero => intro F v x _ _ hlt; omega
  | succ bound ih =>
      intro F v x hok hF hlt
      by_cases hterm : isTerminal v = true
      · refine ⟨1, ?_⟩
        have hx : x = v.noun := den_terminal_val hterm hF
        subst hx
        simp only [runHint, nextHint_none_of_terminal hterm, result, hterm, ite_true]
      · have hntf : isTerminal v = false := by
          cases hh : isTerminal v with
          | true => exact absurd hh hterm
          | false => rfl
        obtain ⟨v', hnext⟩ := progressN hok ⟨F, hF⟩ hntf
        obtain ⟨F', hF'⟩ := (denHint_step hok hnext).1 ⟨F, hF⟩
        have hokv' : editOk v' = true := editOk_nextHint hnext hok
        have hGv : den (max F F') v = some x := den_mono (Nat.le_max_left _ _) hF
        have hGv' : den (max F F') v' = some x := den_mono (Nat.le_max_right _ _) hF'
        have hvcv : vcostN (max F F') v = vcostN F v := vcostN_mono (Nat.le_max_left _ _) hok hF
        have hvcv' : vcostN (max F F') v' = vcostN F' v' := vcostN_mono (Nat.le_max_right _ _) hokv'
          hF'
        have hdec : vcostN (max F F') v' < vcostN (max F F') v := cost_stepN hok hGv hGv' hnext
        have hlt' : vcostN F' v' < bound := by
          rw [hvcv'] at hdec; rw [hvcv] at hdec; omega
        obtain ⟨N, hN⟩ := ih F' v' x hokv' hF' hlt'
        exact ⟨N + 1, by simp only [runHint, hnext]; exact hN⟩

/-! ### `hintComplete_holds` and OP₁₁ adequacy -/

theorem hintComplete_holds : HintComplete := by
  intro s f r hev
  obtain ⟨g, hg⟩ := (den_iff_evalN s f r).2 hev
  obtain ⟨N, hN⟩ := run_completeN (editOk_program s f) ⟨g, hg⟩
  exact ⟨N, hN⟩

theorem runHint_adequate_complete (s f r : Noun) :
    (∃ fuel, runHintProgram fuel s f = some r) ↔ (∃ fuel, evalN fuel s f = some r) :=
  runHint_adequate hintComplete_holds s f r

end Verb
end Nock
