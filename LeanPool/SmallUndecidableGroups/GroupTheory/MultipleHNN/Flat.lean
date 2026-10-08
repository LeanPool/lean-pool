/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.GroupTheory.MultipleHNN
public import Mathlib.Tactic.Group

/-!
# Flat reduced words for a two-stable-letter HNN extension

This is the simultaneous-letter view of the iterated HNN extension in
`MultipleHNN.lean`.  It is designed for Borisov's Assertion IV: a flat word
records which of the two stable letters occurs at every syllable.  The local
reducedness condition is the ordinary Britton condition whenever two
adjacent syllables use the same stable letter.
-/

@[expose] public section

namespace Undecidability
namespace MultipleHNNFlat

open Function

noncomputable section

variable {G : Type*} [Group G]
variable (A B : Subgroup G) (phi : A ≃* B)

/-- A stable-generator color, orientation, and following base-group coefficient. -/
structure Syllable where
  /-- The label selecting one of the two stable generators. -/
  color : Fin 2
  /-- The orientation of the stable generator, represented by `1` or `-1`. -/
  sign : ℤˣ
  /-- The base-group coefficient following the stable generator. -/
  coeff : G

/-- The condition excluding a Britton pinch between adjacent same-color syllables. -/
def Rel (x y : Syllable (G := G)) : Prop :=
  x.color = y.color →
    x.coeff ∈ HNNExtension.toSubgroup A B x.sign →
      x.sign = y.sign

/-- A flattened HNN word with an initial base coefficient and a reduced syllable chain. -/
structure ReducedWord where
  /-- The initial base-group coefficient of the flattened word. -/
  head : G
  /-- The sequence of stable-generator syllables and their following base coefficients. -/
  toList : List (Syllable (G := G))
  chain : toList.IsChain (Rel A B)

/-- The stable-letter signature of a flat word.  Base coefficients are
discarded, while the color and sign of every stable letter are retained. -/
def signature (w : ReducedWord A B) : List (Fin 2 × ℤˣ) :=
  w.toList.map fun s ↦ (s.color, s.sign)

/-- The same signature read from the nested two-stage normal form: first the
initial block of first stable letters, then each second stable letter and the
following block of first stable letters. -/
def nestedSignature (w : MultipleHNN.ReducedWord A B phi) :
    List (Fin 2 × ℤˣ) :=
  w.head.toList.map (fun p ↦ (0, p.1)) ++
    w.toList.flatMap fun p ↦
      (1, p.1) :: p.2.toList.map (fun q ↦ (0, q.1))

/-- The stable generator in the iterated HNN extension with the selected color. -/
def stableLetter : Fin 2 → MultipleHNN.Extension A B phi
  | 0 => MultipleHNN.firstStable A B phi
  | 1 => MultipleHNN.secondStable A B phi

/-- Evaluate the flattened word in the iterated HNN extension. -/
def eval (w : ReducedWord A B) : MultipleHNN.Extension A B phi :=
  MultipleHNN.baseEmbedding A B phi w.head *
    (w.toList.map fun s ↦
      stableLetter A B phi s.color ^ (s.sign : ℤ) *
        MultipleHNN.baseEmbedding A B phi s.coeff).prod

/-- The inner reduced word containing only the supplied base-group coefficient. -/
def innerEmpty (g : G) : MultipleHNN.InnerReducedWord A B where
  head := g
  toList := []
  chain := List.isChain_nil

/-- The correspondence between the first flat syllables and the front of the nested normal form. -/
def Front (l : List (Syllable (G := G)))
    (w : MultipleHNN.ReducedWord A B phi) : Prop :=
  match l with
  | [] => w.head.toList = [] ∧ w.toList = []
  | s :: _ =>
      if s.color = 0 then
        ∃ a tail, w.head.toList = (s.sign, a) :: tail
      else
        w.head.toList = [] ∧
          ∃ a tail, w.toList = (s.sign, a) :: tail

private structure Collapse (g : G) (l : List (Syllable (G := G))) where
  word : MultipleHNN.ReducedWord A B phi
  head_head : word.head.head = g
  front : Front A B phi l word
  signature_eq : nestedSignature A B phi word =
    l.map fun s ↦ (s.color, s.sign)
  eval_eq : word.eval =
    MultipleHNN.baseEmbedding A B phi g *
      (l.map fun s ↦
        stableLetter A B phi s.color ^ (s.sign : ℤ) *
          MultipleHNN.baseEmbedding A B phi s.coeff).prod
  second_support :
    (∃ s ∈ l, s.color = 1) → word.ContainsSecond

private theorem mapped_toSubgroup_mem_iff (u : ℤˣ) (g : G) :
    MultipleHNN.stageOneOf A B phi g ∈
        HNNExtension.toSubgroup
          (MultipleHNN.MappedA A B phi) (MultipleHNN.MappedB A B phi) u ↔
      g ∈ HNNExtension.toSubgroup A B u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · constructor
    · rintro ⟨x, hx, heq⟩
      have h : x = g := HNNExtension.of_injective phi heq
      simpa [h] using hx
    · intro hg
      exact ⟨g, hg, rfl⟩
  · constructor
    · rintro ⟨x, hx, heq⟩
      have h : x = g := HNNExtension.of_injective phi heq
      simpa [h] using hx
    · intro hg
      exact ⟨g, hg, rfl⟩

private theorem inner_prod_not_mem_mapped_of_nonempty
    (w : MultipleHNN.InnerReducedWord A B) (u : ℤˣ)
    (hne : w.toList ≠ []) :
    w.prod phi ∉ HNNExtension.toSubgroup
      (MultipleHNN.MappedA A B phi) (MultipleHNN.MappedB A B phi) u := by
  intro hmem
  have hbase : w.prod phi ∈
      MonoidHom.range (MultipleHNN.stageOneOf A B phi) := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · rcases hmem with ⟨g, hg, heq⟩
      exact ⟨g, heq⟩
    · rcases hmem with ⟨g, hg, heq⟩
      exact ⟨g, heq⟩
  exact hne (HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    phi w hbase)

private theorem collapse_exists (g : G) (l : List (Syllable (G := G)))
    (hchain : l.IsChain (Rel A B)) :
    Nonempty (Collapse (A := A) (B := B) (phi := phi) g l) := by
  induction l generalizing g with
  | nil =>
      refine ⟨⟨⟨innerEmpty A B g, [], List.isChain_nil⟩, rfl, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩⟩
      · simp [nestedSignature, innerEmpty]
      · simp [MultipleHNN.ReducedWord.eval, MultipleHNN.ReducedWord.toOuter,
          innerEmpty, MultipleHNN.baseEmbedding, MultipleHNN.stageTwoOf,
          MultipleHNN.stageOneOf, HNNExtension.NormalWord.ReducedWord.prod]
      · rintro ⟨s, hs, _⟩
        simp at hs
  | cons s rest ih =>
      have hrest : rest.IsChain (Rel A B) := (List.isChain_cons.1 hchain).2
      rcases ih s.coeff hrest with ⟨c⟩
      by_cases hs : s.color = 0
      · have hinnerChain :
            ((s.sign, c.word.head.head) :: c.word.head.toList).IsChain
              (fun a b ↦ a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1) := by
          cases rest with
          | nil =>
              have hc := c.front
              simp only [Front] at hc
              rw [hc.1]
              simp
          | cons t tail =>
              by_cases ht : t.color = 0
              · rcases (show ∃ a tail',
                    c.word.head.toList = (t.sign, a) :: tail' by
                    simpa [Front, ht] using c.front) with ⟨a, tail', ha⟩
                rw [ha]
                have hcchain :
                    ((t.sign, a) :: tail').IsChain
                      (fun a b ↦ a.2 ∈ HNNExtension.toSubgroup A B a.1 →
                        a.1 = b.1) := by
                  simpa [ha] using c.word.head.chain
                apply List.IsChain.cons hcchain
                intro y hy hmem
                have hy' : (t.sign, a) = y := by simpa using hy
                subst y
                have hp := (List.isChain_cons.1 hchain).1 t (by simp)
                apply hp
                · simp [hs, ht]
                · simpa [c.head_head] using hmem
              · have hc := c.front
                simp only [Front, ht] at hc
                rw [hc.1]
                simp
        let iw : MultipleHNN.InnerReducedWord A B :=
          { head := g
            toList := (s.sign, c.word.head.head) :: c.word.head.toList
            chain := hinnerChain }
        let nw : MultipleHNN.ReducedWord A B phi :=
          { head := iw
            toList := c.word.toList
            chain := c.word.chain }
        refine ⟨⟨nw, rfl, ?_, ?_, ?_, ?_⟩⟩
        · simp [Front, hs, nw, iw]
        · simp only [nestedSignature, nw, iw, List.map_cons]
          change (0, s.sign) :: nestedSignature A B phi c.word =
            (s.color, s.sign) :: rest.map (fun z ↦ (z.color, z.sign))
          rw [c.signature_eq]
          simp [hs]
        · have hstable : stableLetter A B phi s.color =
              MultipleHNN.firstStable A B phi := by
            rw [hs]
            rfl
          have hnweval : nw.eval =
              MultipleHNN.baseEmbedding A B phi g *
                MultipleHNN.firstStable A B phi ^ (s.sign : ℤ) * c.word.eval := by
            simp [MultipleHNN.ReducedWord.eval,
              MultipleHNN.ReducedWord.toOuter,
              HNNExtension.NormalWord.ReducedWord.prod, nw, iw,
              MultipleHNN.baseEmbedding, MultipleHNN.firstStable,
              MultipleHNN.stageTwoOf, MultipleHNN.stageOneOf, mul_assoc]
          rw [hnweval, c.eval_eq]
          simp only [List.map_cons, List.prod_cons, mul_assoc]
          congr 2
          exact congrArg (fun x ↦ x ^ (s.sign : ℤ)) hstable.symm
        · intro hex
          apply c.second_support
          rcases hex with ⟨z, hz, hzcolor⟩
          have hzrest : z ∈ rest := by
            have hz' : z = s ∨ z ∈ rest := by simpa using hz
            rcases hz' with hzs | hz
            · subst z
              omega
            · exact hz
          exact ⟨z, hzrest, hzcolor⟩
      · have hs1 : s.color = 1 := by
          omega
        have houterChain :
            (((s.sign, c.word.head) :: c.word.toList).map
              (fun p ↦ (p.1, p.2.prod phi))).IsChain
              (fun a b ↦
                a.2 ∈ HNNExtension.toSubgroup
                  (MultipleHNN.MappedA A B phi)
                  (MultipleHNN.MappedB A B phi) a.1 → a.1 = b.1) := by
          cases rest with
          | nil =>
              have hc := c.front
              simp only [Front] at hc
              rw [hc.2]
              simp
          | cons t tail =>
              by_cases ht : t.color = 0
              · rcases (show ∃ a tail',
                    c.word.head.toList = (t.sign, a) :: tail' by
                    simpa [Front, ht] using c.front) with ⟨a, tail', ha⟩
                simp only [List.map_cons]
                apply List.IsChain.cons c.word.chain
                intro y hy hmem
                exact False.elim
                  (inner_prod_not_mem_mapped_of_nonempty
                    (A := A) (B := B) (phi := phi) c.word.head s.sign
                    (by simp [ha]) hmem)
              · have ht1 : t.color = 1 := by
                  omega
                rcases (show c.word.head.toList = [] ∧
                    ∃ a tail', c.word.toList = (t.sign, a) :: tail' by
                    simpa [Front, ht] using c.front) with ⟨hhead, a, tail', htail⟩
                rw [htail]
                simp only [List.map_cons]
                have hcchain :
                    ((t.sign, a.prod phi) ::
                      tail'.map (fun p ↦ (p.1, p.2.prod phi))).IsChain
                      (fun a b ↦
                        a.2 ∈ HNNExtension.toSubgroup
                          (MultipleHNN.MappedA A B phi)
                          (MultipleHNN.MappedB A B phi) a.1 → a.1 = b.1) := by
                  simpa [htail] using c.word.chain
                apply List.IsChain.cons hcchain
                intro y hy hmem
                have hy' : (t.sign, a.prod phi) = y := by simpa using hy
                subst y
                have hp := (List.isChain_cons.1 hchain).1 t (by simp)
                apply hp
                · simp [hs1, ht1]
                · have hcMem := (mapped_toSubgroup_mem_iff
                      (A := A) (B := B) (phi := phi)
                      s.sign c.word.head.head).1
                    (by simpa [hhead,
                        HNNExtension.NormalWord.ReducedWord.prod,
                        MultipleHNN.stageOneOf] using hmem)
                  simpa [c.head_head] using hcMem
        let iw : MultipleHNN.InnerReducedWord A B := innerEmpty A B g
        let nw : MultipleHNN.ReducedWord A B phi :=
          { head := iw
            toList := (s.sign, c.word.head) :: c.word.toList
            chain := houterChain }
        refine ⟨⟨nw, rfl, ?_, ?_, ?_, ?_⟩⟩
        · simp [Front, hs, nw, iw, innerEmpty]
        · simp only [nestedSignature, nw, iw, innerEmpty, List.map_nil,
            List.nil_append, List.flatMap_cons]
          change (1, s.sign) :: nestedSignature A B phi c.word =
            (s :: rest).map (fun z ↦ (z.color, z.sign))
          rw [c.signature_eq]
          simp [hs1]
        · have hnweval : nw.eval =
              MultipleHNN.baseEmbedding A B phi g *
                MultipleHNN.secondStable A B phi ^ (s.sign : ℤ) * c.word.eval := by
            simp [MultipleHNN.ReducedWord.eval,
              MultipleHNN.ReducedWord.toOuter,
              HNNExtension.NormalWord.ReducedWord.prod, nw, iw, innerEmpty,
              MultipleHNN.baseEmbedding, MultipleHNN.secondStable,
              MultipleHNN.stageTwoOf, MultipleHNN.stageOneOf, mul_assoc]
          rw [hnweval, c.eval_eq]
          simp only [List.map_cons, List.prod_cons, mul_assoc]
          congr 2
          have hstable : stableLetter A B phi s.color =
              MultipleHNN.secondStable A B phi := by
            rw [hs1]
            rfl
          exact congrArg (fun x ↦ x ^ (s.sign : ℤ)) hstable.symm
        · intro _
          simp [nw, MultipleHNN.ReducedWord.ContainsSecond]

/-- Every flat reduced word has a nested reduced representative with the
same evaluation and exactly the same color/sign signature. -/
theorem exists_nested_with_signature (w : ReducedWord A B) :
    ∃ v : MultipleHNN.ReducedWord A B phi,
      v.eval = eval A B phi w ∧
        nestedSignature A B phi v = signature A B w := by
  rcases collapse_exists (A := A) (B := B) (phi := phi)
    w.head w.toList w.chain with ⟨c⟩
  exact ⟨c.word, by simpa [eval] using c.eval_eq, by
    simpa [signature] using c.signature_eq⟩

/-- Color-sensitive flat Britton lemma.  If a reduced flat word contains the
second stable letter, its value cannot lie in the embedded first HNN stage. -/
theorem eval_not_mem_stageOne_of_contains_color_one
    (w : ReducedWord A B)
    (hcolor : ∃ s ∈ w.toList, s.color = 1) :
    eval A B phi w ∉ MonoidHom.range (MultipleHNN.stageTwoOf A B phi) := by
  rcases collapse_exists (A := A) (B := B) (phi := phi)
    w.head w.toList w.chain with ⟨c⟩
  have hsecond : c.word.ContainsSecond := c.second_support hcolor
  have heval : c.word.eval = eval A B phi w := by
    simpa [eval] using c.eval_eq
  intro hmem
  exact MultipleHNN.ReducedWord.eval_not_mem_stageOne
    (A := A) (B := B) (phi := phi) c.word hsecond
      (by simpa [heval] using hmem)

/-- A nonempty flat reduced word is nontrivial.  This is the simultaneous
two-stable-letter form of Britton's lemma. -/
theorem eval_ne_one (w : ReducedWord A B) (hne : w.toList ≠ []) :
    eval A B phi w ≠ 1 := by
  rcases collapse_exists (A := A) (B := B) (phi := phi)
    w.head w.toList w.chain with ⟨c⟩
  have hstable : c.word.ContainsStable := by
    obtain ⟨s, rest, hl⟩ := List.exists_cons_of_ne_nil hne
    have hc : Front A B phi (s :: rest) c.word := by
      simpa only [hl] using c.front
    by_cases hs : s.color = 0
    · right
      rcases (by simpa only [Front, hs, ite_eq_left] using hc) with ⟨a, tail, ha⟩
      simp [MultipleHNN.ReducedWord.ContainsFirstInHead, ha]
    · left
      rcases (by simpa only [Front, hs, ite_eq_right] using hc) with ⟨hhead, a, tail, ha⟩
      simp [MultipleHNN.ReducedWord.ContainsSecond, ha]
  have hcne := MultipleHNN.ReducedWord.eval_ne_one
    (A := A) (B := B) (phi := phi) c.word hstable
  have heval : c.word.eval = eval A B phi w := by
    simpa [eval] using c.eval_eq
  exact heval ▸ hcne

end

end MultipleHNNFlat
end Undecidability

/-!
# A base-membership form of the flat Britton lemma
-/

namespace Undecidability
namespace MultipleHNNFlat

noncomputable section

variable {G : Type*} [Group G]
variable (A B : Subgroup G) (phi : A ≃* B)

/-- A nonempty flat reduced word cannot lie in the embedded original base.
This strengthens `eval_ne_one` in the form needed for Borisov's subgroup
intersection calculations. -/
theorem eval_not_mem_base (w : ReducedWord A B) (hne : w.toList ≠ []) :
    eval A B phi w ∉
      MonoidHom.range (MultipleHNN.baseEmbedding A B phi) := by
  rintro ⟨g, hg⟩
  let shifted : ReducedWord A B :=
    { head := g⁻¹ * w.head
      toList := w.toList
      chain := w.chain }
  have hshifted : eval A B phi shifted =
      MultipleHNN.baseEmbedding A B phi g⁻¹ * eval A B phi w := by
    simp only [shifted, eval, map_mul, mul_assoc]
  have hone : eval A B phi shifted = 1 := by
    rw [hshifted, ← hg]
    simp
  exact eval_ne_one A B phi shifted hne hone

end

end MultipleHNNFlat
end Undecidability
