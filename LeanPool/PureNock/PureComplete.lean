/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.PureAgreement
public import Mathlib.Tactic.IntervalCases

/-!
# Completeness for the derived OP₀–OP₁₀ oracle

`progressP` and the denotation-keyed `vcost`/`pcost` measure show every
successful `evalPaper` evaluation is realized by `runProgram`.
-/

@[expose] public section

namespace Nock
namespace Verb

open Noun

/-! ### Helper: right child of a denP-defined editOk node is denP-defined at the SAME fuel -/

theorem denP_right_F {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP (f + 1) (Verb.node a l r) = some x) :
    ∃ yr, denP (f + 1) r = some yr := by
  cases a with
  | wut => simp [denP] at h
  | edit =>
      have hrp : Verb.isPending r = false := editOk_edit_cond hok
      cases r with
      | leaf k => simp [denP] at h
      | node rb nw od =>
          have hrb : rb = Action.null := by
            simp only [isPending] at hrp
            cases rb <;> simp_all [Action.isNull]
          subst hrb
          simp only [denP] at h
          cases hnw : denP f nw with
          | none => rw [hnw] at h; simp at h
          | some n =>
              cases hod : denP f od with
              | none => rw [hnw, hod] at h; simp at h
              | some o => exact ⟨.cell n o, by simp [denP, hnw, hod]⟩
  | null => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr] at h
  | star => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr] at h
  | slot => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr] at h
  | equal => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr] at h
  | minus => cases hr : denP f r with | some y => exact ⟨y, denP_succ hr⟩ | none => simp [denP, hr] at h

theorem denP_children_F {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP F (Verb.node a l r) = some x) :
    (∃ yl, denP F l = some yl) ∧ (∃ yr, denP F r = some yr) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [denP] at h
    | succ n => exact ⟨n, rfl⟩
  refine ⟨?_, denP_right_F hok h⟩
  obtain ⟨yl, hyl⟩ := denP_left_defined h
  exact ⟨yl, denP_succ hyl⟩

theorem isTerminal_node {a : Action} {l r : Verb} :
    isTerminal (Verb.node a l r) = (a.isNull && isTerminal l && isTerminal r) := rfl

theorem denP_terminal_val {v : Verb} {F : Nat} {y : Noun}
    (ht : isTerminal v = true) (h : denP F v = some y) : y = v.noun :=
  (DenP_terminal_iff ht).1 ⟨F, h⟩

theorem denP_term_children {a : Action} {l r : Verb} {F : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP F (Verb.node a l r) = some x)
    (htl : isTerminal l = true) (htr : isTerminal r = true) :
    denP F l = some l.noun ∧ denP F r = some r.noun := by
  obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := denP_children_F hok h
  rw [denP_terminal_val htl hyl] at hyl
  rw [denP_terminal_val htr hyr] at hyr
  exact ⟨hyl, hyr⟩

theorem denP_term_split {l r : Verb} {f : Nat} {x : Noun}
    (htl : isTerminal l = true) (htr : isTerminal r = true)
    (h : denP (f + 1) (Verb.node .null l r) = some x) :
    denP f l = some l.noun ∧ denP f r = some r.noun := by
  simp only [denP] at h
  cases hl : denP f l with
  | none => rw [hl] at h; simp at h
  | some yl =>
      cases hr : denP f r with
      | none => rw [hl, hr] at h; simp at h
      | some yr =>
          refine ⟨?_, ?_⟩
          · rw [denP_terminal_val htl hl]
          · rw [denP_terminal_val htr hr]

theorem denP_star_val {A B : Verb} {f : Nat} {a b w : Noun}
    (hA : denP f A = some a) (hB : denP f B = some b) (he : evalPaper f a b = some w) :
    denP (f + 1) (Verb.node .star A B) = some w := by
  simp only [denP, hA, hB]; exact he

theorem denP_null_val {A B : Verb} {f : Nat} {a b : Noun}
    (hA : denP f A = some a) (hB : denP f B = some b) :
    denP (f + 1) (Verb.node .null A B) = some (Noun.cell a b) := by
  simp only [denP, hA, hB]

theorem denP_null_none {A B : Verb} {f : Nat} (hA : denP f A = none) :
    denP (f + 1) (Verb.node .null A B) = none := by
  simp only [denP, hA]

theorem isTerminal_of_map_ofNoun {o : Option Noun} {r₀ : Verb}
    (h : o.map ofNoun = some r₀) : isTerminal r₀ = true := by
  rw [Option.map_eq_some_iff] at h; obtain ⟨w, _, rfl⟩ := h; exact ofNoun_terminal w

theorem pcost_align {n m k : Nat} {a b r : Noun} (h : evalPaper n a b = some r)
    (hm : n ≤ m) (hk : n ≤ k) : pcost m a b = pcost k a b :=
  (pcost_mono hm h).trans (pcost_mono hk h).symm

/-! ### Controlled `vcost` node equations (avoid `simp [vcost]` over-unfolding literals) -/

theorem vcost_star_eq {F : Nat} {l r : Verb} : vcost F (Verb.node .star l r) =
    (match denP F l, denP F r with | some sa, some fo => pcost F sa fo | _, _ => 0)
      + vcost F l + vcost F r := rfl
theorem vcost_slot_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .slot l r) = 1 + vcost F l + vcost F r := rfl
theorem vcost_equal_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .equal l r) = 1 + vcost F l + vcost F r := rfl
theorem vcost_minus_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .minus l r) = 1 + vcost F l + vcost F r := rfl
theorem vcost_edit_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .edit l r) = 1 + vcost F l + vcost F r := rfl
theorem vcost_null_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .null l r) = vcost F l + vcost F r := by
  simp only [vcost]; omega
theorem vcost_wut_eq {F : Nat} {l r : Verb} :
    vcost F (Verb.node .wut l r) = vcost F l + vcost F r := by
  simp only [vcost]; omega

/-- `vcost` of a `*`-node with terminal, denP-defined children is the firing `pcost`. -/
theorem vcost_star_terminal {F : Nat} {A B : Verb}
    (hA : isTerminal A = true) (hB : isTerminal B = true)
    (hdA : denP F A = some A.noun) (hdB : denP F B = some B.noun) :
    vcost F (Verb.node .star A B) = pcost F A.noun B.noun := by
  simp only [vcost_star_eq, hdA, hdB, vcost_terminal A hA F, vcost_terminal B hB F, Nat.add_zero]

/-! ### Lemma 1 — `vcost_succ` -/

theorem vcost_succ {F : Nat} {v : Verb} {x : Noun}
    (hok : editOk v = true) (hv : denP F v = some x) : vcost (F + 1) v = vcost F v := by
  induction v generalizing F x with
  | leaf k => rfl
  | node a l r ihl ihr =>
      obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
        cases F with
        | zero => simp [denP] at hv
        | succ n => exact ⟨n, rfl⟩
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := denP_children_F hok hv
      have ihl' : vcost (f + 1 + 1) l = vcost (f + 1) l := ihl hokl hyl
      have ihr' : vcost (f + 1 + 1) r = vcost (f + 1) r := ihr hokr hyr
      cases a with
      | null => simp only [vcost, ihl', ihr']
      | wut => simp [denP] at hv
      | slot => simp only [vcost, ihl', ihr']
      | equal => simp only [vcost, ihl', ihr']
      | minus => simp only [vcost, ihl', ihr']
      | edit => simp only [vcost, ihl', ihr']
      | star =>
          -- unfold star clause; both fuels pick the same denP values sa, fo
          simp only [denP] at hv
          -- hv : (match denP f l, denP f r with ...) = some x
          cases hfl : denP f l with
          | none => rw [hfl] at hv; simp at hv
          | some sa =>
              cases hfr : denP f r with
              | none => rw [hfl, hfr] at hv; simp at hv
              | some fo =>
                  rw [hfl, hfr] at hv
                  -- hv : evalPaper f sa fo = some x
                  have hdl1 : denP (f + 1) l = some sa := denP_succ hfl
                  have hdr1 : denP (f + 1) r = some fo := denP_succ hfr
                  have hdl2 : denP (f + 1 + 1) l = some sa := denP_succ hdl1
                  have hdr2 : denP (f + 1 + 1) r = some fo := denP_succ hdr1
                  have hev1 : evalPaper (f + 1) sa fo = some x := evalPaper_succ hv
                  have hpc : pcost (f + 1 + 1) sa fo = pcost (f + 1) sa fo := pcost_succ hev1
                  simp only [vcost, hdl1, hdr1, hdl2, hdr2, hpc, ihl', ihr']

/-! ### Lemma 2 — `vcost_mono` -/

theorem vcost_mono {F G : Nat} {v : Verb} {x : Noun}
    (hle : F ≤ G) (hok : editOk v = true) (hv : denP F v = some x) : vcost G v = vcost F v := by
  induction hle with
  | refl => rfl
  | @step m h ih => rw [vcost_succ hok (denP_mono h hv)]; exact ih

theorem EvP_det {a b y1 y2 : Noun} (h1 : EvP a b y1) (h2 : EvP a b y2) : y1 = y2 := by
  obtain ⟨f1, h1⟩ := h1; obtain ⟨f2, h2⟩ := h2
  exact Option.some.inj ((evalPaper_mono (Nat.le_max_left f1 f2) h1).symm.trans
    (evalPaper_mono (Nat.le_max_right f1 f2) h2))

theorem denP_null_leaf0 {inner : Verb} {f : Nat} {dv : Noun}
    (h : denP (f + 1) (Verb.node .null (Verb.leaf 0) inner) = some dv) :
    ∃ w, dv = Noun.cell (Noun.atom 0) w := by
  simp only [denP] at h
  cases hi : denP f inner with
  | none => rw [hi] at h; simp at h
  | some iv => rw [hi] at h; exact ⟨iv, (Option.some.inj h).symm⟩

/-- **OP₆ strict local decrease** (if-then-else macro).  The reduct is a 6-level nested `*`-tree;
    its `vcost` is `SF(L,a0) + SF(c,b0) + SF([2,3],d0) + SF(L,[4[4b]])`, where the last is exactly
    `4 + pcost g L b`, the middle two are `≤ 2` (op0), and the first is `0` or the branch cost
    (matching the RHS branch by a full evaluation trace `b → *[L,b]∈{0,1} → +2 → slot → branch`).
    The op₆ weight `100` dominates the macro skeleton (`8`). -/
theorem op6_decrease {g : Nat} {L b thn els : Verb} {x : Noun} {rn2 rc : Action}
    (hL : isTerminal L = true) (htc : isTerminal (Verb.node rc thn els) = true)
    (hthn : isTerminal thn = true) (htels : isTerminal els = true)
    (hgc : denP g (Verb.node rc thn els) = some (Verb.node rc thn els).noun)
    (hdL : denP (g + 1 + 1) L = some L.noun)
    (h4b : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
        = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)))
    (ht4 : isTerminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true)
    (ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true)
    (hvv : evalPaper (g + 1) L.noun
        (Noun.cell (Noun.atom 6) (Verb.node rn2 b (Verb.node rc thn els)).noun) = some x) :
    vcost (g + 1 + 1)
        (Verb.node .star L
          (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L
                    (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
      < pcost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by
  have hleaf0 : isTerminal (Verb.leaf 0) = true := rfl
  have h23 : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
      = some (Noun.cell (Noun.atom 2) (Noun.atom 3)) :=
    denP_null_val (by simp only [denP]) (by simp only [denP])
  have hdc : denP (g + 1 + 1) (Verb.node rc thn els) = some (Verb.node rc thn els).noun :=
    denP_succ (denP_succ hgc)
  -- op₆ evaluation of the guard `b`
  simp only [noun, evalPaper] at hvv
  cases hsb : evalPaper g L.noun b.noun with
  | none => rw [hsb] at hvv; simp at hvv
  | some sbv =>
    rw [hsb] at hvv
    have hEvb : EvP L.noun b.noun sbv := ⟨g, hsb⟩
    have hsb1 : evalPaper (g + 1) L.noun b.noun = some sbv := evalPaper_succ hsb
    have eqLb : pcost g L.noun b.noun = pcost (g + 1) L.noun b.noun :=
      pcost_align hsb (Nat.le_refl g) (by omega)
    -- `[4 [4 b]]` cost is `4 + pcost g L b` (definitional, op4∘op4)
    have hSFinner : pcost (g + 1 + 1) L.noun (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun))
        = 4 + pcost g L.noun b.noun := by simp only [pcost]; omega
    -- The generic argument: whatever branch, the reduct cost < RHS.
    -- key: SF(c,b0) ≤ 2, SF([2,3],d0) ≤ 2, SF(L,a0) is 0 or the branch pcost.
    -- We prove it by decomposing `vcost` and bounding.
    have hbound : ∀ (branchNoun : Verb),
        (sbv = Noun.atom 0 ∧ branchNoun = thn ∨ sbv = Noun.atom 1 ∧ branchNoun = els) →
        evalPaper g L.noun branchNoun.noun = some x →
        vcost (g + 1 + 1)
          (Verb.node .star L
            (Verb.node .star (Verb.node rc thn els)
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                  (Verb.node .null (Verb.leaf 0)
                    (Verb.node .star L
                      (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))))
        < pcost (g + 1 + 1) L.noun
            (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun := by
      intro branchNoun hbr hbev
      -- align the branch cost
      have eqBr : pcost (g + 1 + 1) L.noun branchNoun.noun = pcost (g + 1) L.noun branchNoun.noun :=
        pcost_align hbev (by omega) (by omega)
      -- RHS = 100 + pcost(g+1) L b + pcost(g+1) L branch
      have hRHS : pcost (g + 1 + 1) L.noun
          (Verb.node .null (Verb.leaf 6) (Verb.node rn2 b (Verb.node rc thn els))).noun
          = 100 + pcost (g + 1) L.noun b.noun + pcost (g + 1) L.noun branchNoun.noun := by
        rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [noun, pcost, hsb1]
      rw [hRHS]
      -- decompose vcost of the reduct
      simp only [vcost_star_eq, vcost_null_eq, vcost_terminal L hL,
        vcost_terminal (Verb.node rc thn els) htc,
        vcost_terminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) ht23,
        vcost_terminal (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) ht4,
        vcost_terminal (Verb.leaf 0) hleaf0, hdL, h4b, Nat.add_zero, Nat.zero_add]
      -- SF([2,3],d0) ≤ 2
      have hc0le : (match denP (g + 1 + 1) (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)),
            denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
              (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)))) with
          | some sa, some fo => pcost (g + 1 + 1) sa fo | _, _ => 0) ≤ 2 := by
        rw [h23]
        cases hd0 : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
            (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)))) with
        | none => simp
        | some dv => obtain ⟨w, rfl⟩ := denP_null_leaf0 hd0; simp only [pcost]; omega
      -- SF(c,b0) ≤ 2
      have ha0le : (match denP (g + 1 + 1) (Verb.node rc thn els),
            denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)))))) with
          | some sa, some fo => pcost (g + 1 + 1) sa fo | _, _ => 0) ≤ 2 := by
        rw [hdc]
        cases hb0 : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
            (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)))))) with
        | none => simp
        | some bv => obtain ⟨w, rfl⟩ := denP_null_leaf0 hb0; simp only [pcost]; omega
      -- SF(L,a0) ≤ pcost(g+1) L branch
      have hrrle : (match some L.noun,
            denP (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
              (Verb.node .null (Verb.leaf 0)
                (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                  (Verb.node .null (Verb.leaf 0)
                    (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))) with
          | some sa, some fo => pcost (g + 1 + 1) sa fo | _, _ => 0)
          ≤ pcost (g + 1) L.noun branchNoun.noun := by
        cases haa : denP (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
            (Verb.node .null (Verb.leaf 0)
              (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))) with
        | none => simp
        | some aa =>
            simp only
            -- trace: aa = branchNoun.noun
            have hDa0 : DenP (Verb.node .star (Verb.node rc thn els)
                (Verb.node .null (Verb.leaf 0)
                  (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                    (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))) aa :=
              ⟨g + 1 + 1, haa⟩
            rw [DenP_star] at hDa0
            obtain ⟨cv, b0v, hDc0, hDb0, hEva0⟩ := hDa0
            have : cv = (Verb.node rc thn els).noun := (DenP_terminal_iff htc).1 hDc0
            subst this
            rw [DenP_null] at hDb0
            obtain ⟨z, c0v, rfl, hDz, hDc0'⟩ := hDb0
            have : z = Noun.atom 0 := DenP_leaf.1 hDz
            subst this
            rw [EvP_op0] at hEva0
            obtain ⟨ax, rfl, hslotA⟩ := hEva0
            rw [DenP_star] at hDc0'
            obtain ⟨p23, d0v, hD23, hDd0, hEvc0⟩ := hDc0'
            have hp23 : p23 = Noun.cell (Noun.atom 2) (Noun.atom 3) := by
              have := (DenP_terminal_iff ht23).1 hD23; simpa only [noun] using this
            subst hp23
            rw [DenP_null] at hDd0
            obtain ⟨z2, iv, rfl, hDz2, hDinner⟩ := hDd0
            have : z2 = Noun.atom 0 := DenP_leaf.1 hDz2
            subst this
            rw [EvP_op0] at hEvc0
            obtain ⟨ax2, rfl, hslotB⟩ := hEvc0
            rw [DenP_star] at hDinner
            obtain ⟨Lv, fv, hDL', hD4, hEvinner⟩ := hDinner
            have : Lv = L.noun := (DenP_terminal_iff hL).1 hDL'
            subst this
            have hfv : fv = Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun) := by
              have := (DenP_terminal_iff ht4).1 hD4; simpa only [noun] using this
            subst hfv
            rw [EvP_op4] at hEvinner
            obtain ⟨y, hEvy, hlusy⟩ := hEvinner
            rw [EvP_op4] at hEvy
            obtain ⟨y2, hEvy2, hlusy2⟩ := hEvy
            have hy2 : y2 = sbv := EvP_det hEvy2 hEvb
            subst hy2
            -- Compute each branch.
            rcases hbr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · -- sbv = 0 : y = 1, ax2 = 2, ax = 2, aa = slot 2 c.noun = thn.noun
              have hy : y = Noun.atom 1 := by
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
            · -- sbv = 1 : y = 2, ax2 = 3, ax = 3, aa = slot 3 c.noun = els.noun
              have hy : y = Noun.atom 2 := by
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
      -- combine
      rw [hSFinner]
      cases evaluatedZero : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))
        <;> cases evaluatedOne : denP (g + 1 + 1) (Verb.node .null (Verb.leaf 0)
                      (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                        (Verb.node .null (Verb.leaf 0)
                          (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))))))
        <;> cases evaluatedTwo : denP (g + 1 + 1) (Verb.node .star (Verb.node rc thn els)
                      (Verb.node .null (Verb.leaf 0)
                        (Verb.node .star (Verb.node .null (Verb.leaf 2) (Verb.leaf 3))
                          (Verb.node .null (Verb.leaf 0)
                            (Verb.node .star L (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)))))))
        <;> simp only [hdc, h23, evaluatedZero, evaluatedOne, evaluatedTwo]
          at hc0le ha0le hrrle ⊢
        <;> omega
    -- dispatch on the guard value
    cases sbv with
    | cell k1 k2 => simp at hvv
    | atom av =>
        match av, hvv with
        | 0, hvv => exact hbound thn (Or.inl ⟨rfl, rfl⟩) hvv
        | 1, hvv => exact hbound els (Or.inr ⟨rfl, rfl⟩) hvv
        | (k + 2), hvv => simp at hvv

/-! ### Lemma 3 — `cost_local` (strict local decrease at a `*`-redex) -/

theorem cost_local {F : Nat} {L R rr : Verb} {x : Noun}
    (hL : isTerminal L = true) (hR : isTerminal R = true)
    (hv : denP F (Verb.node .star L R) = some x)
    (hr : reduce (Verb.node .star L R) = some rr) :
    vcost F rr < vcost F (Verb.node .star L R) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := by
    cases F with
    | zero => simp [denP] at hv
    | succ n => exact ⟨n, rfl⟩
  have hvv := hv
  simp only [denP] at hvv
  cases hfL : denP f L with
  | none => rw [hfL] at hvv; simp at hvv
  | some sL =>
    cases hfR : denP f R with
    | none => rw [hfL, hfR] at hvv; simp at hvv
    | some sR =>
      rw [hfL, hfR] at hvv
      have hsL : sL = L.noun := denP_terminal_val hL hfL
      have hsR : sR = R.noun := denP_terminal_val hR hfR
      subst hsL; subst hsR
      have hdL : denP (f + 1) L = some L.noun := denP_succ hfL
      have hvcL : vcost (f + 1) L = 0 := vcost_terminal L hL (f + 1)
      have hvcR : vcost (f + 1) R = 0 := vcost_terminal R hR (f + 1)
      have hstar : vcost (f + 1) (Verb.node .star L R) = pcost (f + 1) L.noun R.noun := by
        simp only [vcost, hdL, denP_succ hfR, hvcL, hvcR, Nat.add_zero]
      rw [hstar]
      cases R with
      | leaf k => simp [reduce, redex] at hr
      | node ra i n2 =>
          have hRt : isTerminal (Verb.node ra i n2) = true := hR
          simp only [isTerminal, Bool.and_eq_true] at hR
          obtain ⟨⟨hra, hti⟩, htn2⟩ := hR
          have hra0 : ra = Action.null := by cases ra <;> simp_all [Action.isNull]
          subst hra0
          obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := by
            cases f with
            | zero => simp [denP] at hfR
            | succ n => exact ⟨n, rfl⟩
          obtain ⟨hgi, hgn2⟩ := denP_term_split hti htn2 hfR
          rw [reduce] at hr
          have hdi_f1 : denP (g + 1 + 1) i = some i.noun := denP_succ (denP_succ hgi)
          have hdn2_f1 : denP (g + 1 + 1) n2 = some n2.noun := denP_succ (denP_succ hgn2)
          have hvci : vcost (g + 1 + 1) i = 0 := vcost_terminal i hti _
          have hvcn2 : vcost (g + 1 + 1) n2 = 0 := vcost_terminal n2 htn2 _
          cases i with
          | node bi ic id =>
              simp only [redex] at hr
              obtain rfl := Option.some.inj hr
              simp only [noun, evalPaper] at hvv
              cases he1 : evalPaper g L.noun (Noun.cell ic.noun id.noun) with
              | none => rw [he1] at hvv; simp at hvv
              | some l' =>
                  cases he2 : evalPaper g L.noun n2.noun with
                  | none => rw [he1, he2] at hvv; simp at hvv
                  | some r' =>
                      have e_i : pcost (g + 1 + 1) L.noun (Noun.cell ic.noun id.noun)
                          = pcost (g + 1) L.noun (Noun.cell ic.noun id.noun) :=
                        pcost_align he1 (by omega) (by omega)
                      have e_n2 : pcost (g + 1 + 1) L.noun n2.noun = pcost (g + 1) L.noun n2.noun :=
                        pcost_align he2 (by omega) (by omega)
                      rw [vcost_null_eq,
                        vcost_star_terminal hL hti hdL hdi_f1,
                        vcost_star_terminal hL htn2 hdL hdn2_f1]
                      simp only [noun, pcost]
                      rw [e_i, e_n2]
                      omega
          | leaf op =>
              have hop : op < 11 := by
                rcases Nat.lt_or_ge op 11 with h | h
                · exact h
                · exfalso
                  simp only [noun] at hvv
                  rw [evalPaper_op_ge11 (g + 1) L.noun n2.noun op h] at hvv
                  simp at hvv
              simp only [noun] at hvv
              interval_cases op
              · -- OP0
                simp only [redex] at hr; obtain rfl := Option.some.inj hr
                rw [vcost_slot_eq, vcost_terminal n2 htn2, vcost_terminal L hL]
                simp only [noun, pcost]; omega
              · -- OP1
                simp only [redex] at hr; obtain rfl := Option.some.inj hr
                rw [vcost_terminal n2 htn2]
                simp only [noun, pcost]; omega
              · -- OP2
                cases n2 with
                | leaf k => simp [redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    simp only [redex] at hr; obtain rfl := Option.some.inj hr
                    obtain ⟨hg1b, hg1c⟩ :=
                      denP_term_children (editOk_of_terminal hn2t) (denP_succ hgn2) htb htc
                    have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ hg1b
                    have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
                    simp only [noun, evalPaper] at hvv
                    cases hb : evalPaper g L.noun b.noun with
                    | none => rw [hb] at hvv; simp at hvv
                    | some sb =>
                      cases hc : evalPaper g L.noun c.noun with
                      | none => rw [hb, hc] at hvv; simp at hvv
                      | some sc =>
                        rw [hb, hc] at hvv
                        have hb' : evalPaper (g + 1) L.noun b.noun = some sb := evalPaper_succ hb
                        have hc' : evalPaper (g + 1) L.noun c.noun = some sc := evalPaper_succ hc
                        have hd_Lb : denP (g + 1 + 1) (Verb.node .star L b) = some sb :=
                          denP_star_val hfL hg1b hb'
                        have hd_Lc : denP (g + 1 + 1) (Verb.node .star L c) = some sc :=
                          denP_star_val hfL hg1c hc'
                        have eq_b : pcost (g + 1 + 1) L.noun b.noun = pcost (g + 1) L.noun b.noun :=
                          pcost_align hb (by omega) (by omega)
                        have eq_c : pcost (g + 1 + 1) L.noun c.noun = pcost (g + 1) L.noun c.noun :=
                          pcost_align hc (by omega) (by omega)
                        have eq_sbsc : pcost (g + 1 + 1) sb sc = pcost (g + 1) sb sc :=
                          pcost_align hvv (by omega) (by omega)
                        simp only [vcost_star_eq, hd_Lb, hd_Lc,
                          vcost_star_terminal hL htb hdL hdb_f1,
                          vcost_star_terminal hL htc hdL hdc_f1]
                        simp only [noun, pcost, hb', hc']
                        rw [eq_b, eq_c, eq_sbsc]
                        omega
              · -- OP3
                simp only [redex] at hr; obtain rfl := Option.some.inj hr
                simp only [evalPaper, Option.map_eq_some_iff] at hvv
                obtain ⟨y, hy, _⟩ := hvv
                have e_n2 : pcost (g + 1 + 1) L.noun n2.noun = pcost (g + 1) L.noun n2.noun :=
                  pcost_align hy (by omega) (by omega)
                rw [vcost_minus_eq, vcost_star_terminal hL htn2 hdL hdn2_f1]
                simp only [vcost, noun, pcost]
                rw [e_n2]; omega
              · -- OP4
                simp only [redex] at hr; obtain rfl := Option.some.inj hr
                simp only [evalPaper, Option.bind_eq_some_iff] at hvv
                obtain ⟨y, hy, _⟩ := hvv
                have e_n2 : pcost (g + 1 + 1) L.noun n2.noun = pcost (g + 1) L.noun n2.noun :=
                  pcost_align hy (by omega) (by omega)
                rw [vcost_minus_eq, vcost_star_terminal hL htn2 hdL hdn2_f1]
                simp only [vcost, noun, pcost]
                rw [e_n2]; omega
              · -- OP5
                cases n2 with
                | leaf k => simp [redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    simp only [redex] at hr; obtain rfl := Option.some.inj hr
                    obtain ⟨hg1b, hg1c⟩ :=
                      denP_term_children (editOk_of_terminal hn2t) (denP_succ hgn2) htb htc
                    have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ hg1b
                    have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
                    simp only [noun, evalPaper] at hvv
                    cases hb : evalPaper g L.noun b.noun with
                    | none => rw [hb] at hvv; simp at hvv
                    | some sb =>
                      cases hc : evalPaper g L.noun c.noun with
                      | none => rw [hb, hc] at hvv; simp at hvv
                      | some sc =>
                        have eq_b : pcost (g + 1 + 1) L.noun b.noun = pcost (g + 1) L.noun b.noun :=
                          pcost_align hb (by omega) (by omega)
                        have eq_c : pcost (g + 1 + 1) L.noun c.noun = pcost (g + 1) L.noun c.noun :=
                          pcost_align hc (by omega) (by omega)
                        rw [vcost_equal_eq, vcost_star_terminal hL htb hdL hdb_f1,
                          vcost_star_terminal hL htc hdL hdc_f1]
                        simp only [noun, pcost]
                        rw [eq_b, eq_c]; omega
              · -- OP6
                cases n2 with
                | leaf k => simp [redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    have hct : isTerminal c = true := htc
                    simp only [redex] at hr; obtain rfl := Option.some.inj hr
                    obtain ⟨hgb, hgcv⟩ :=
                      denP_term_children (editOk_of_terminal hn2t) hgn2 htb htc
                    have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ (denP_succ hgb)
                    -- denP F of the terminal `[4 [4 b]]` cell
                    have h4a : denP (g + 1) (Verb.node .null (Verb.leaf 4) b)
                        = some (Noun.cell (Noun.atom 4) b.noun) :=
                      denP_null_val (by simp only [denP]) hgb
                    have h4b : denP (g + 1 + 1)
                        (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b))
                        = some (Noun.cell (Noun.atom 4) (Noun.cell (Noun.atom 4) b.noun)) :=
                      denP_null_val (by simp only [denP]) h4a
                    have ht4 : isTerminal
                        (Verb.node .null (Verb.leaf 4) (Verb.node .null (Verb.leaf 4) b)) = true := by
                      simp [isTerminal, Action.isNull, htb]
                    have ht23 : isTerminal (Verb.node .null (Verb.leaf 2) (Verb.leaf 3)) = true := by
                      simp [isTerminal, Action.isNull]
                    -- c must be a cell for op6 to fire
                    cases c with
                    | leaf ck => exfalso; simp only [noun, evalPaper] at hvv; simp at hvv
                    | node rc thn els =>
                        have hct2 : isTerminal (Verb.node rc thn els) = true := hct
                        rw [isTerminal_node] at hct; simp only [Bool.and_eq_true] at hct
                        obtain ⟨⟨hrc, hthn⟩, htels⟩ := hct
                        exact op6_decrease hL hct2 hthn htels hgcv hdL h4b ht4 ht23 hvv
              · -- OP7
                cases n2 with
                | leaf k => simp [redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    simp only [redex] at hr; obtain rfl := Option.some.inj hr
                    obtain ⟨hg1b, hg1c⟩ :=
                      denP_term_children (editOk_of_terminal hn2t) (denP_succ hgn2) htb htc
                    have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ hg1b
                    have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
                    simp only [noun, evalPaper] at hvv
                    cases hb : evalPaper g L.noun b.noun with
                    | none => rw [hb] at hvv; simp at hvv
                    | some sb =>
                        rw [hb] at hvv
                        have hb' : evalPaper (g + 1) L.noun b.noun = some sb := evalPaper_succ hb
                        have hd_Lb : denP (g + 1 + 1) (Verb.node .star L b) = some sb :=
                          denP_star_val hfL hg1b hb'
                        have eq_b : pcost (g + 1 + 1) L.noun b.noun = pcost (g + 1) L.noun b.noun :=
                          pcost_align hb (by omega) (by omega)
                        have eq_sbc : pcost (g + 1 + 1) sb c.noun = pcost (g + 1) sb c.noun :=
                          pcost_align hvv (by omega) (by omega)
                        simp only [vcost_star_eq, hd_Lb, hdc_f1,
                          vcost_star_terminal hL htb hdL hdb_f1, vcost_terminal c htc]
                        simp only [noun, pcost, hb']
                        rw [eq_b, eq_sbc]; omega
              · -- OP8
                cases n2 with
                | leaf k => simp [redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    simp only [redex] at hr; obtain rfl := Option.some.inj hr
                    obtain ⟨hgb, hgc⟩ :=
                      denP_term_children (editOk_of_terminal hn2t) hgn2 htb htc
                    have hg1b : denP (g + 1) b = some b.noun := denP_succ hgb
                    have hdb_f1 : denP (g + 1 + 1) b = some b.noun := denP_succ hg1b
                    have hg1c : denP (g + 1) c = some c.noun := denP_succ hgc
                    have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
                    simp only [noun, evalPaper] at hvv
                    cases hb : evalPaper g L.noun b.noun with
                    | none => rw [hb] at hvv; simp at hvv
                    | some sb =>
                        rw [hb] at hvv
                        have hb' : evalPaper (g + 1) L.noun b.noun = some sb := evalPaper_succ hb
                        have eq_Lb : pcost (g + 1 + 1) L.noun b.noun = pcost (g + 1) L.noun b.noun :=
                          pcost_align hb (by omega) (by omega)
                        have eq_sbLc : pcost (g + 1 + 1) (Noun.cell sb L.noun) c.noun
                            = pcost (g + 1) (Noun.cell sb L.noun) c.noun := pcost_align hvv (by omega) (by omega)
                        have hRHS : pcost (g + 1 + 1) L.noun
                            (Verb.node .null (Verb.leaf 8) (Verb.node rn2 b c)).noun
                            = 1 + pcost (g + 1) L.noun b.noun
                                + pcost (g + 1) (Noun.cell sb L.noun) c.noun := by
                          simp only [noun, pcost, hb']
                        rw [hRHS]
                        have hvcnull : vcost (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
                            = pcost (g + 1 + 1) L.noun b.noun := by
                          rw [vcost_null_eq, vcost_star_terminal hL htb hdL hdb_f1, vcost_terminal L hL,
                            Nat.add_zero]
                        cases hgL : denP g L with
                        | none =>
                            have hnone : denP (g + 1) (Verb.node .star L b) = none := by
                              simp only [denP, hgL]
                            have hsubjn : denP (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L) = none :=
                              denP_null_none hnone
                            rw [vcost_star_eq]
                            simp only [hsubjn, hvcnull, vcost_terminal c htc]
                            rw [eq_Lb]
                            omega
                        | some vL =>
                            have hvL : vL = L.noun := denP_terminal_val hL hgL
                            subst hvL
                            have hd_Lb_g : denP (g + 1) (Verb.node .star L b) = some sb :=
                              denP_star_val hgL hgb hb
                            have hd_subj : denP (g + 1 + 1) (Verb.node .null (Verb.node .star L b) L)
                                = some (Noun.cell sb L.noun) := denP_null_val hd_Lb_g hfL
                            rw [vcost_star_eq]
                            simp only [hd_subj, hdc_f1, hvcnull, vcost_terminal c htc]
                            rw [eq_Lb, eq_sbLc]
                            omega
              · -- OP9
                cases n2 with
                | leaf k => simp [redex] at hr
                | node rn2 b c =>
                    have hn2t : isTerminal (Verb.node rn2 b c) = true := htn2
                    simp only [isTerminal, Bool.and_eq_true] at htn2
                    obtain ⟨⟨hrn2, htb⟩, htc⟩ := htn2
                    have hrn2' : rn2 = Action.null := by cases rn2 <;> simp_all [Action.isNull]
                    subst hrn2'
                    simp only [redex] at hr; obtain rfl := Option.some.inj hr
                    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := by
                      cases g with | zero => simp [denP] at hgn2 | succ n => exact ⟨n, rfl⟩
                    obtain ⟨hhb, hhc⟩ := denP_term_split htb htc hgn2
                    cases b with
                    | node bb bc bd => simp [noun, evalPaper] at hvv
                    | leaf ax0 =>
                        simp only [noun, evalPaper] at hvv
                        cases hcor : evalPaper (g' + 1) L.noun c.noun with
                        | none => simp [hcor] at hvv
                        | some cor =>
                          simp only [hcor] at hvv
                          cases harm : Noun.slot ax0 cor with
                          | none => simp [harm] at hvv
                          | some arm =>
                            simp only [harm] at hvv
                            have hg2c : denP (g' + 1 + 1) c = some c.noun := denP_succ (denP_succ hhc)
                            have hdc_f1 : denP (g' + 1 + 1 + 1) c = some c.noun := denP_succ hg2c
                            have hcor2 : evalPaper (g' + 2) L.noun c.noun = some cor :=
                              evalPaper_succ hcor
                            have hd_core : denP (g' + 1 + 1 + 1) (Verb.node .star L c) = some cor :=
                              denP_star_val hfL hg2c hcor2
                            have hb0 : denP g' (Verb.leaf 0) = some (Noun.atom 0) := by simp only [denP]
                            have hb1 : denP g' (Verb.leaf 1) = some (Noun.atom 1) := by simp only [denP]
                            have hf0h : denP (g' + 1) (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0))
                                = some (Noun.cell (Noun.atom 0) (Noun.atom ax0)) := denP_null_val hb0 hhb
                            have hf01 : denP (g' + 1) (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                                = some (Noun.cell (Noun.atom 0) (Noun.atom 1)) := denP_null_val hb0 hb1
                            have hM : denP (g' + 1 + 1)
                                  (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                                    (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0)))
                                = some (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                                    (Noun.cell (Noun.atom 0) (Noun.atom ax0))) := denP_null_val hf01 hf0h
                            have h2 : denP (g' + 1 + 1) (Verb.leaf 2) = some (Noun.atom 2) := by
                              simp only [denP]
                            have hform : denP (g' + 1 + 1 + 1)
                                  (Verb.node .null (Verb.leaf 2)
                                    (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                                      (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0))))
                                = some (Noun.cell (Noun.atom 2)
                                    (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 1))
                                      (Noun.cell (Noun.atom 0) (Noun.atom ax0)))) := denP_null_val h2 hM
                            have hformT : isTerminal
                                (Verb.node .null (Verb.leaf 2)
                                  (Verb.node .null (Verb.node .null (Verb.leaf 0) (Verb.leaf 1))
                                    (Verb.node .null (Verb.leaf 0) (Verb.leaf ax0)))) = true := by
                              simp [isTerminal, Action.isNull]
                            have hev01 : evalPaper (g' + 2) cor
                                (Noun.cell (Noun.atom 0) (Noun.atom 1)) = some cor := by
                              simp only [evalPaper]; exact slot_one
                            have hev0h : evalPaper (g' + 2) cor
                                (Noun.cell (Noun.atom 0) (Noun.atom ax0)) = some arm := by
                              simp only [evalPaper]; exact harm
                            have eq_c1 : pcost (g' + 1 + 1 + 1) L.noun c.noun
                                = pcost (g' + 2) L.noun c.noun := pcost_align hcor (by omega) (by omega)
                            have eq_c2 : pcost (g' + 3) L.noun c.noun
                                = pcost (g' + 2) L.noun c.noun := pcost_align hcor (by omega) (by omega)
                            have hRHS : pcost (g' + 1 + 1 + 1) L.noun
                                (Verb.node .null (Verb.leaf 9) (Verb.node .null (Verb.leaf ax0) c)).noun
                                = 20 + pcost (g' + 2) L.noun c.noun + pcost (g' + 2) cor arm := by
                              simp only [noun, pcost, hcor2, harm]
                            rw [hRHS]
                            simp only [vcost_star_eq, hd_core, hform,
                              vcost_star_terminal hL htc hdL hdc_f1, vcost_terminal _ hformT]
                            simp only [pcost, hev01, hev0h]
                            show 1 + 2 + 2 + pcost (g' + 2) cor arm
                                + pcost (g' + 1 + 1 + 1) L.noun c.noun + 0
                              < 20 + pcost (g' + 2) L.noun c.noun + pcost (g' + 2) cor arm
                            rw [eq_c1]
                            omega
              · -- OP10
                cases n2 with
                | leaf k => simp [redex] at hr
                | node rn2 hd d =>
                    cases hd with
                    | leaf k => simp [redex] at hr
                    | node rhd axv c =>
                        have hn2t : isTerminal (Verb.node rn2 (Verb.node rhd axv c) d) = true := htn2
                        rw [isTerminal_node] at htn2; simp only [Bool.and_eq_true] at htn2
                        obtain ⟨⟨hrn2, hthd⟩, htd⟩ := htn2
                        have hhdt : isTerminal (Verb.node rhd axv c) = true := hthd
                        rw [isTerminal_node] at hthd; simp only [Bool.and_eq_true] at hthd
                        obtain ⟨⟨hrhd, htaxv⟩, htc⟩ := hthd
                        simp only [redex] at hr; obtain rfl := Option.some.inj hr
                        obtain ⟨hg1hd, hg1d⟩ :=
                          denP_term_children (editOk_of_terminal hn2t) (denP_succ hgn2) hhdt htd
                        obtain ⟨hg1axv, hg1c⟩ :=
                          denP_term_children (editOk_of_terminal hhdt) hg1hd htaxv htc
                        have hdc_f1 : denP (g + 1 + 1) c = some c.noun := denP_succ hg1c
                        have hdd_f1 : denP (g + 1 + 1) d = some d.noun := denP_succ hg1d
                        cases axv with
                        | node b0 c0 d0 => simp [noun, evalPaper] at hvv
                        | leaf a0 =>
                            simp only [noun, evalPaper] at hvv
                            cases hnew : evalPaper g L.noun c.noun with
                            | none => rw [hnew] at hvv; simp at hvv
                            | some new =>
                              cases hold : evalPaper g L.noun d.noun with
                              | none => rw [hnew, hold] at hvv; simp at hvv
                              | some old =>
                                  have eq_c : pcost (g + 1 + 1) L.noun c.noun
                                      = pcost (g + 1) L.noun c.noun := pcost_align hnew (by omega) (by omega)
                                  have eq_d : pcost (g + 1 + 1) L.noun d.noun
                                      = pcost (g + 1) L.noun d.noun := pcost_align hold (by omega) (by omega)
                                  rw [vcost_edit_eq, vcost_null_eq,
                                    vcost_star_terminal hL htc hdL hdc_f1,
                                    vcost_star_terminal hL htd hdL hdd_f1]
                                  simp only [vcost, noun, pcost]
                                  rw [eq_c, eq_d]; omega

/-! ### Lemma 4 — step congruence and `cost_stepP` -/

theorem enum_denP_F {F : Nat} : ∀ (v : Verb), editOk v = true → ∀ (c : Nat) (x : Noun),
    denP F v = some x → ∀ p ∈ (enum v c).2, ∃ y, denP F p.2 = some y := by
  intro v
  induction v with
  | leaf k => intro _ c x _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro hok c x hd p hp
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      obtain ⟨⟨yl, hyl⟩, ⟨yr, hyr⟩⟩ := denP_children_F hok hd
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with hroot | hleft | hright
      · subst hroot; exact ⟨x, hd⟩
      · exact ihl hokl (c + 1) yl hyl p hleft
      · exact ihr hokr _ yr hyr p hright

theorem denP_F_subnode {F : Nat} {v : Verb} {x : Noun} (hok : editOk v = true)
    (hv : denP F v = some x) {i : Nat} {sub : Verb} (hmap : map i v = some sub) :
    ∃ y, denP F sub = some y :=
  enum_denP_F v hok 0 x hv (i, sub) (mem_nodes_of_map hmap)

theorem replaceAux_notMem (i : Nat) (r₀ : Verb) : ∀ (v : Verb) (c : Nat),
    findAt i (enum v c).2 = none → (replaceAux i r₀ v c).2 = v := by
  intro v
  induction v with
  | leaf k => intro c _; rfl
  | node a l r ihl ihr =>
      intro c hnone
      have hci : i ≠ c := by
        intro h; subst h; simp [enum, findAt] at hnone
      have hine : ¬ (c = i) := fun h => hci h.symm
      simp only [enum, findAt, if_neg (fun h : i = c => hci h)] at hnone
      rw [findAt_append] at hnone
      have hln : findAt i (enum l (c + 1)).2 = none := by
        cases hl : findAt i (enum l (c + 1)).2 with
        | none => rfl
        | some s => rw [hl] at hnone; simp at hnone
      have hrn : findAt i (enum r (enum l (c + 1)).1).2 = none := by
        rw [hln] at hnone; exact hnone
      have hcL : (replaceAux i r₀ l (c + 1)).1 = (enum l (c + 1)).1 := replaceAux_counter i r₀ l (c + 1)
      simp only [replaceAux, if_neg hine]
      rw [ihl (c + 1) hln, hcL, ihr _ hrn]

theorem denP_F_swap_eq {F : Nat} {w w' : Verb} (hok : editOk w = true) (hrel : RelP w w')
    {a b : Noun} (ha : denP F w = some a) (hb : denP F w' = some b) : a = b := by
  have hiff := Rel_denP w.noun.size w w' (Nat.le_refl _) hrel hok a
  exact denP_det (hiff.1 ⟨F, ha⟩) ⟨F, hb⟩

/-- **Step congruence for `vcost`.**  Swapping the (denotation-preserving, pending) subnode `sub`
    for `r₀` changes `vcost F` by exactly `vcost F r₀ - vcost F sub` (additive form). -/
theorem vcost_replace_cong (F i : Nat) (sub r₀ : Verb) (hpend : sub.isPending = true)
    (hgraph : ∀ y, DenP sub y ↔ DenP r₀ y) (hr0 : editOk r₀ = true) :
    ∀ (v : Verb) (c : Nat) (xv xv' : Noun),
      editOk v = true →
      findAt i (enum v c).2 = some sub →
      denP F v = some xv →
      denP F (replaceAux i r₀ v c).2 = some xv' →
      vcost F (replaceAux i r₀ v c).2 + vcost F sub = vcost F v + vcost F r₀ := by
  intro v
  induction v with
  | leaf k => intro c xv xv' _ hfind; simp [enum, findAt] at hfind
  | node a l r ihl ihr =>
      intro c xv xv' hok hfind hdv hdv'
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      by_cases hci : c = i
      · -- the swapped node itself
        subst hci
        have hf : findAt c (enum (Verb.node a l r) c).2 = some (Verb.node a l r) := by
          simp [enum, findAt]
        have hsub : Verb.node a l r = sub := (Option.some.inj (hf.symm.trans hfind))
        have hrepl : (replaceAux c r₀ (Verb.node a l r) c).2 = r₀ := by simp [replaceAux]
        rw [hrepl, ← hsub]
        omega
      · have hine : ¬ (i = c) := fun h => hci h.symm
        have hcL : (replaceAux i r₀ l (c + 1)).1 = (enum l (c + 1)).1 := replaceAux_counter i r₀ l (c + 1)
        -- locate i in left/right
        have hfind' : findAt i (enum l (c + 1)).2 = some sub ∧
              findAt i (enum r (enum l (c + 1)).1).2 = none
            ∨ findAt i (enum l (c + 1)).2 = none ∧
              findAt i (enum r (enum l (c + 1)).1).2 = some sub := by
          simp only [enum, findAt, if_neg hine] at hfind
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
        -- denP-definedness of children at F (both v and v')
        obtain ⟨⟨xl, hxl⟩, ⟨xr, hxr⟩⟩ := denP_children_F hok hdv
        have hok' : editOk (replaceAux i r₀ (Verb.node a l r) c).2 = true := by
          apply editOk_replaceAux i r₀ hr0 (Verb.node a l r) c hok
          intro s hs; have : s = sub := Option.some.inj (hs.symm.trans hfind); rw [this]; exact hpend
        simp only [replaceAux, if_neg hci] at hdv' hok' ⊢
        rw [hcL] at hdv' hok' ⊢
        obtain ⟨⟨xl', hxl'⟩, ⟨xr', hxr'⟩⟩ := denP_children_F hok' hdv'
        -- head-cost preservation
        rcases hfind' with ⟨hLsub, hRnone⟩ | ⟨hLnone, hRsub⟩
        · -- i in left
          have hrIH := ihl (c + 1) xl xl' hokl hLsub hxl hxl'
          -- right unchanged
          have hreq : (replaceAux i r₀ r (enum l (c + 1)).1).2 = r := replaceAux_notMem i r₀ r _ hRnone
          rw [hreq] at hxr' ⊢
          have hrelL : RelP l (replaceAux i r₀ l (c + 1)).2 := by
            apply replaceAux_relP i r₀ l (c + 1)
            intro s hs
            have : s = sub := Option.some.inj (hs.symm.trans hLsub)
            rw [this]; exact ⟨hpend, hgraph⟩
          have hlEq : xl = xl' := denP_F_swap_eq hokl hrelL hxl hxl'
          cases a <;>
            simp only [vcost_star_eq, vcost_null_eq, vcost_wut_eq, vcost_slot_eq, vcost_equal_eq,
              vcost_minus_eq, vcost_edit_eq, hxl, hxl', hxr, hlEq] <;> omega
        · -- i in right
          have hrIH := ihr (enum l (c + 1)).1 xr xr' hokr hRsub hxr hxr'
          have hleq : (replaceAux i r₀ l (c + 1)).2 = l := replaceAux_notMem i r₀ l _ hLnone
          rw [hleq] at hxl' ⊢
          have hrelR : RelP r (replaceAux i r₀ r (enum l (c + 1)).1).2 := by
            apply replaceAux_relP i r₀ r (enum l (c + 1)).1
            intro s hs
            have : s = sub := Option.some.inj (hs.symm.trans hRsub)
            rw [this]; exact ⟨hpend, hgraph⟩
          have hrEq : xr = xr' := denP_F_swap_eq hokr hrelR hxr hxr'
          cases a <;>
            simp only [vcost_star_eq, vcost_null_eq, vcost_wut_eq, vcost_slot_eq, vcost_equal_eq,
              vcost_minus_eq, vcost_edit_eq, hxr, hxr', hxl, hrEq] <;> omega

/-- **A single machine step strictly decreases `vcost`** (at a common fuel `F`). -/
theorem cost_stepP {F : Nat} {v v' : Verb} {x x' : Noun}
    (hwf : editOk v = true) (hv : denP F v = some x) (hv' : denP F v' = some x')
    (h : next v = some v') : vcost F v' < vcost F v := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'eq⟩ := next_eq_some_iff.1 h
  have hgi : getIndex v = some i := getIndex_eq_some_iff.2 hmax
  have hoksub : editOk sub = true := editOk_enum v 0 hwf (i, sub) (mem_nodes_of_map hmap)
  have hokr0 : editOk r₀ = true := editOk_reduce hred hoksub
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hgraph : ∀ y, DenP sub y ↔ DenP r₀ y := fun y => den_localP hdom hred
  -- denP-definedness of sub at F
  obtain ⟨xs, hxs⟩ := denP_F_subnode hwf hv hmap
  -- strict local decrease at the redex
  have hlocal : vcost F r₀ < vcost F sub := by
    cases sub with
    | leaf k => simp [isPending] at hpsub
    | node a L R =>
        obtain ⟨hL, hR⟩ := children_terminal_of_getIndex hgi hmap
        cases a with
        | null => simp [isPending, Action.isNull] at hpsub
        | wut => simp [reduce] at hred
        | star => exact cost_local hL hR hxs hred
        | slot =>
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax => rw [reduce] at hred; simp only [noun] at hred
                           exact isTerminal_of_map_ofNoun hred
              | node a2 l2 r2 => rw [reduce] at hred; simp only [noun] at hred; simp at hred
            rw [vcost_terminal r₀ ht0]
            simp only [vcost_slot_eq, vcost_terminal L hL, vcost_terminal R hR]; omega
        | equal =>
            have ht0 : isTerminal r₀ = true := by
              rw [reduce] at hred; obtain rfl := Option.some.inj hred; exact ofNoun_terminal _
            rw [vcost_terminal r₀ ht0]
            simp only [vcost_equal_eq, vcost_terminal L hL, vcost_terminal R hR]; omega
        | minus =>
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax =>
                  rw [reduce] at hred; simp only [noun] at hred
                  split at hred
                  · obtain rfl := Option.some.inj hred; exact ofNoun_terminal _
                  · exact isTerminal_of_map_ofNoun hred
                  · simp at hred
              | node a2 l2 r2 => rw [reduce] at hred; simp only [noun] at hred; simp at hred
            rw [vcost_terminal r₀ ht0]
            simp only [vcost_minus_eq, vcost_terminal L hL, vcost_terminal R hR]; omega
        | edit =>
            have ht0 : isTerminal r₀ = true := by
              cases L with
              | leaf ax =>
                  cases R with
                  | leaf k => simp [reduce, noun] at hred
                  | node rb nw od =>
                      simp only [reduce, noun] at hred
                      exact isTerminal_of_map_ofNoun hred
              | node a2 l2 r2 => simp [reduce, noun] at hred
            rw [vcost_terminal r₀ ht0]
            simp only [vcost_edit_eq, vcost_terminal L hL, vcost_terminal R hR]; omega
  -- congruence
  have hv'2 : denP F (replaceAt i v r₀) = some x' := hv'eq ▸ hv'
  have hcong : vcost F (replaceAt i v r₀) + vcost F sub = vcost F v + vcost F r₀ :=
    vcost_replace_cong F i sub r₀ hpsub hgraph hokr0 v 0 x x' hwf hmap hv hv'2
  rw [hv'eq]
  omega

/-! ### Lemma 5 — `run_completeP` -/

theorem run_completeP {v : Verb} {x : Noun} (hok : editOk v = true) (hv : DenP v x) :
    ∃ N, run N v = some x := by
  suffices aux : ∀ (bound F : Nat) (v : Verb) (x : Noun),
      editOk v = true → denP F v = some x → vcost F v < bound → ∃ N, run N v = some x by
    obtain ⟨F, hF⟩ := hv
    exact aux (vcost F v + 1) F v x hok hF (Nat.lt_succ_self _)
  intro bound
  induction bound with
  | zero => intro F v x _ _ hlt; omega
  | succ bound ih =>
      intro F v x hok hF hlt
      by_cases hterm : isTerminal v = true
      · refine ⟨1, ?_⟩
        have hx : x = v.noun := denP_terminal_val hterm hF
        subst hx
        simp only [run, next_none_of_terminal hterm, result, hterm, if_true]
      · have hntf : isTerminal v = false := by
          cases hh : isTerminal v with
          | true => exact absurd hh hterm
          | false => rfl
        obtain ⟨v', hnext⟩ := progressP hok ⟨F, hF⟩ hntf
        obtain ⟨F', hF'⟩ := (den_stepP hok hnext).1 ⟨F, hF⟩
        have hokv' : editOk v' = true := editOk_next hnext hok
        have hGv : denP (max F F') v = some x := denP_mono (Nat.le_max_left _ _) hF
        have hGv' : denP (max F F') v' = some x := denP_mono (Nat.le_max_right _ _) hF'
        have hvcv : vcost (max F F') v = vcost F v := vcost_mono (Nat.le_max_left _ _) hok hF
        have hvcv' : vcost (max F F') v' = vcost F' v' := vcost_mono (Nat.le_max_right _ _) hokv' hF'
        have hdec : vcost (max F F') v' < vcost (max F F') v := cost_stepP hok hGv hGv' hnext
        have hlt' : vcost F' v' < bound := by
          rw [hvcv'] at hdec; rw [hvcv] at hdec; omega
        obtain ⟨N, hN⟩ := ih F' v' x hokv' hF' hlt'
        exact ⟨N + 1, by simp only [run, hnext]; exact hN⟩

/-! ### Lemma 6 — `paperComplete_holds` -/

theorem paperComplete_holds : PaperComplete := by
  intro s f r hev
  obtain ⟨g, hg⟩ := (denP_iff_evalPaper s f r).2 hev
  obtain ⟨N, hN⟩ := run_completeP (editOk_program s f) ⟨g, hg⟩
  exact ⟨N, hN⟩

/-! ### OP₀–OP₁₀ consistency -/

-- main.tex:1052-1083  (`i ∈ [11]` = {0,…,10})
/-- The paper-derived local machine and derived OP₀–OP₁₀ oracle compute the
    same partial function. This is a Lean consistency theorem, not a theorem
    stated in `main.tex`. -/
theorem runProgram_adequate_complete (s f r : Noun) :
    (∃ fuel, runProgram fuel s f = some r) ↔ (∃ fuel, evalPaper fuel s f = some r) :=
  runProgram_adequate paperComplete_holds s f r

end Verb
end Nock
