/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Model.CStage

/-!
The simulator-specific statement is a classification of one
base-group coefficient.  Notice that it mentions neither `c`, nor `t`, nor
either of the final HNN extensions.
-/

@[expose] public section

namespace Undecidability
namespace BorisovLemma4Pinch

open BorisovCStage

noncomputable section

/-- The reducedness condition relating consecutive stable-letter syllables. -/
abbrev ChainRel (datum : Thue.StandingDatum)
    (_hfree : RankFiveFree datum) :=
  fun a b : ℤˣ × BorisovHNNModel.Gamma3 =>
    a.2 ∈ HNNExtension.toSubgroup (U datum) (V datum) a.1 → a.1 = b.1

private theorem chain_replace_last_coefficient
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
    (u : ℤˣ) (a x : BorisovHNNModel.Gamma3)
    (hchain : (pre ++ [(u, a)]).IsChain (ChainRel datum hfree)) :
    (pre ++ [(u, x)]).IsChain (ChainRel datum hfree) := by
  rw [List.isChain_append] at hchain ⊢
  refine ⟨hchain.1, by simp, ?_⟩
  intro p hp q hq
  have hq' : q = (u, x) := by simpa using hq.symm
  subst q
  have hold := hchain.2.2 p hp (u, a) (by simp)
  exact hold

private theorem combined_chain
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
    (u : ℤˣ) (a x : BorisovHNNModel.Gamma3)
    (v : ℤˣ) (b : BorisovHNNModel.Gamma3)
    (tail : List (ℤˣ × BorisovHNNModel.Gamma3))
    (hleft : (pre ++ [(u, a)]).IsChain (ChainRel datum hfree))
    (hright : ((v, b) :: tail).IsChain (ChainRel datum hfree))
    (hboundary : x ∈ HNNExtension.toSubgroup (U datum) (V datum) u → u = v) :
    (pre ++ (u, x) :: (v, b) :: tail).IsChain (ChainRel datum hfree) := by
  rw [show pre ++ (u, x) :: (v, b) :: tail =
      (pre ++ [(u, x)]) ++ ((v, b) :: tail) by simp]
  apply List.IsChain.append
  · exact chain_replace_last_coefficient datum hfree pre u a x hleft
  · exact hright
  · intro p hp q hq
    have hp' : p = (u, x) := by simpa using hp.symm
    have hq' : q = (v, b) := by simpa using hq.symm
    subst p
    subst q
    exact hboundary

/-- The first genuinely group-theoretic step in Borisov's positive-`c`
induction.  If `P⁻¹ L Q R = 1` and at least one `c` occurs, then both
contexts contain a stable letter and the coefficient across their boundary
is a Britton pinch. -/
theorem lemma4_boundary_pinch
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (P Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree)
    (heq : Lemma4Equation datum hfree P Q L R)
    (hpositive : contextComplexity datum hfree L R ≠ 0) :
    ∃ (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
      (u : ℤˣ) (a : BorisovHNNModel.Gamma3)
      (v : ℤˣ) (b : BorisovHNNModel.Gamma3)
      (tail : List (ℤˣ × BorisovHNNModel.Gamma3)),
      L.word.toList = pre ++ [(u, a)] ∧
      R.word.toList = (v, b) :: tail ∧
      a * positive3 Q * R.word.head ∈
        HNNExtension.toSubgroup (U datum) (V datum) u ∧
      v = -u := by
  have hLne : L.word.toList ≠ [] := by
    intro hLnil
    by_cases hRnil : R.word.toList = []
    · apply hpositive
      simp [contextComplexity, hLnil, hRnil]
    · let combined : CReducedWord datum hfree :=
        { head := (positive3 P)⁻¹ * L.word.head * positive3 Q * R.word.head
          toList := R.word.toList
          chain := R.word.chain }
      have hprod : combined.prod (cEquiv datum hfree) = 1 := by
        simpa [combined, Lemma4Equation, positive2, leftValue, rightValue,
          HNNExtension.NormalWord.ReducedWord.prod, hLnil, of3, map_mul,
          map_inv, mul_assoc] using heq
      have hbase : combined.prod (cEquiv datum hfree) ∈
          MonoidHom.range (of3 datum hfree) := ⟨1, by simp [hprod, of3]⟩
      have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
        (cEquiv datum hfree) combined hbase
      exact hRnil (by simpa [combined] using hnil)
  have hRne : R.word.toList ≠ [] := by
    intro hRnil
    cases hrev : L.word.toList.reverse with
    | nil =>
      apply hLne
      exact List.reverse_eq_nil_iff.mp hrev
    | cons last revPre =>
      let pre := revPre.reverse
      have hLlist : L.word.toList = pre ++ [last] := by
        dsimp [pre]
        rw [← List.reverse_inj]
        simp [hrev]
      let combined : CReducedWord datum hfree :=
        { head := (positive3 P)⁻¹ * L.word.head
          toList := pre ++
            [(last.1, last.2 * positive3 Q * R.word.head)]
          chain := chain_replace_last_coefficient datum hfree pre last.1
            last.2 (last.2 * positive3 Q * R.word.head) (by
              simpa [hLlist] using L.word.chain) }
      have hprod : combined.prod (cEquiv datum hfree) = 1 := by
        simpa [combined, pre, Lemma4Equation, positive2, leftValue, rightValue,
          HNNExtension.NormalWord.ReducedWord.prod, hLlist, hRnil, of3,
          List.map_append, map_mul, map_inv, mul_assoc] using heq
      have hbase : combined.prod (cEquiv datum hfree) ∈
          MonoidHom.range (of3 datum hfree) := ⟨1, by simp [hprod, of3]⟩
      have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
        (cEquiv datum hfree) combined hbase
      have : combined.toList ≠ [] := by simp [combined]
      exact this hnil
  cases hLrev : L.word.toList.reverse with
  | nil =>
    apply (hLne ?_).elim
    exact List.reverse_eq_nil_iff.mp hLrev
  | cons last revPre =>
    rcases last with ⟨u, a⟩
    let pre := revPre.reverse
    have hLlist : L.word.toList = pre ++ [(u, a)] := by
      dsimp [pre]
      rw [← List.reverse_inj]
      simp [hLrev]
    cases hRlist : R.word.toList with
    | nil => exact (hRne hRlist).elim
    | cons first tail =>
      rcases first with ⟨v, b⟩
      let middle := a * positive3 Q * R.word.head
      have hcontra
          (hboundary : middle ∈ HNNExtension.toSubgroup
            (U datum) (V datum) u → u = v) : False := by
        let combined : CReducedWord datum hfree :=
          { head := (positive3 P)⁻¹ * L.word.head
            toList := pre ++ (u, middle) :: (v, b) :: tail
            chain := combined_chain datum hfree pre u a middle v b tail
              (by simpa [hLlist] using L.word.chain)
              (by simpa [hRlist] using R.word.chain) hboundary }
        have hprod : combined.prod (cEquiv datum hfree) = 1 := by
          simpa [combined, middle, Lemma4Equation, positive2, leftValue,
            rightValue, HNNExtension.NormalWord.ReducedWord.prod, hLlist,
            hRlist, of3, List.map_append, map_mul, map_inv, mul_assoc] using heq
        have hbase : combined.prod (cEquiv datum hfree) ∈
            MonoidHom.range (of3 datum hfree) := ⟨1, by simp [hprod, of3]⟩
        have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
          (cEquiv datum hfree) combined hbase
        have : combined.toList ≠ [] := by simp [combined]
        exact this hnil
      have hmem : middle ∈
          HNNExtension.toSubgroup (U datum) (V datum) u := by
        by_contra hm
        exact hcontra (fun hx => (hm hx).elim)
      have hne : u ≠ v := by
        intro huv
        exact hcontra (fun _ => huv)
      refine ⟨pre, u, a, v, b, tail, hLlist, by simp, hmem, ?_⟩
      exact Int.units_ne_iff_eq_neg.mp hne.symm

/-- The boundary pinch with the cyclic context coefficients written as
integer powers.  These are the two cases to which Borisov's Assertion V is
applied: an `A`-pinch rewrites an `F_i`, and a `B`-pinch rewrites an `E_i`. -/
theorem lemma4_boundary_pinch_power_form
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (P Q : List (Fin 2))
    (L : LeftContext datum hfree) (R : RightContext datum hfree)
    (heq : Lemma4Equation datum hfree P Q L R)
    (hpositive : contextComplexity datum hfree L R ≠ 0) :
    ∃ (f r : ℤ)
      (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
      (b : BorisovHNNModel.Gamma3)
      (tail : List (ℤˣ × BorisovHNNModel.Gamma3)),
      (L.word.toList = pre ++ [(1, BorisovHNNModel.d3 ^ f)] ∧
        R.word.toList = (-1, b) :: tail ∧
        R.word.head = BorisovHNNModel.e3 ^ r ∧
        BorisovHNNModel.d3 ^ f * positive3 Q *
            BorisovHNNModel.e3 ^ r ∈ U datum) ∨
      (L.word.toList = pre ++ [(-1, BorisovHNNModel.d3 ^ f)] ∧
        R.word.toList = (1, b) :: tail ∧
        R.word.head = BorisovHNNModel.e3 ^ r ∧
        BorisovHNNModel.d3 ^ f * positive3 Q *
            BorisovHNNModel.e3 ^ r ∈ V datum) := by
  rcases lemma4_boundary_pinch datum hfree P Q L R heq hpositive with
    ⟨pre, u, a, v, b, tail, hL, hR, hmem, hv⟩
  have ha : a ∈ dCyclic := L.coeff_mem (u, a) (by simp [hL])
  have hr : R.word.head ∈ eCyclic := R.head_mem
  rcases Subgroup.mem_closure_singleton.mp ha with ⟨f, hf⟩
  rcases Subgroup.mem_closure_singleton.mp hr with ⟨r, hr⟩
  rcases Int.units_eq_one_or u with rfl | rfl
  · refine ⟨f, r, pre, b, tail, Or.inl ⟨?_, ?_, hr.symm, ?_⟩⟩
    · simpa [hf] using hL
    · simpa [hv] using hR
    · simpa [hf, hr, HNNExtension.toSubgroup_one] using hmem
  · refine ⟨f, r, pre, b, tail, Or.inr ⟨?_, ?_, hr.symm, ?_⟩⟩
    · simpa [hf] using hL
    · simpa [hv] using hR
    · simpa [hf, hr, HNNExtension.toSubgroup_neg_one] using hmem

/-- The group value of a list of signed stable-letter syllables. -/
def listValue
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (l : List (ℤˣ × BorisovHNNModel.Gamma3)) :
    Gamma2 datum hfree :=
  (l.map fun p =>
    (HNNExtension.t : Gamma2 datum hfree) ^ (p.1 : ℤ) *
      of3 datum hfree p.2).prod

/-- The group value of an initial base coefficient followed by the supplied syllables. -/
def prefixValue
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (head : BorisovHNNModel.Gamma3)
    (l : List (ℤˣ × BorisovHNNModel.Gamma3)) :
    Gamma2 datum hfree :=
  of3 datum hfree head * listValue datum hfree l

private theorem prefix_chain
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (L : LeftContext datum hfree)
    (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
    (u : ℤˣ) (a : BorisovHNNModel.Gamma3)
    (hlist : L.word.toList = pre ++ [(u, a)]) :
    pre.IsChain (ChainRel datum hfree) := by
  have hchain : (pre ++ [(u, a)]).IsChain (ChainRel datum hfree) := by
    simpa [hlist] using L.word.chain
  exact (List.isChain_append.mp hchain).1

private theorem prefix_coeff_mem
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (L : LeftContext datum hfree)
    (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
    (u : ℤˣ) (a : BorisovHNNModel.Gamma3)
    (hlist : L.word.toList = pre ++ [(u, a)]) :
    ∀ p ∈ pre, p.2 ∈ dCyclic := by
  intro p hp
  exact L.coeff_mem p (by rw [hlist]; exact List.mem_append_left _ hp)

/-- Absorb one last power of `d` into a reduced left context after deleting
its final stable letter. -/
private theorem exists_left_absorb
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (L : LeftContext datum hfree)
    (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
    (u : ℤˣ) (a x : BorisovHNNModel.Gamma3)
    (hlist : L.word.toList = pre ++ [(u, a)]) (hx : x ∈ dCyclic) :
    ∃ L' : LeftContext datum hfree,
      L'.word.toList.length = pre.length ∧
      leftValue datum hfree L' =
        prefixValue datum hfree L.word.head pre * of3 datum hfree x := by
  have hprechain := prefix_chain datum hfree L pre u a hlist
  have hpremem := prefix_coeff_mem datum hfree L pre u a hlist
  cases hrev : pre.reverse with
  | nil =>
      have hpre : pre = [] := List.reverse_eq_nil_iff.mp hrev
      subst pre
      let L' : LeftContext datum hfree :=
        { word :=
            { head := L.word.head * x
              toList := []
              chain := List.isChain_nil }
          head_mem := dCyclic.mul_mem L.head_mem hx
          coeff_mem := by simp }
      refine ⟨L', by simp [L'], ?_⟩
      simp [L', leftValue, prefixValue, listValue,
        HNNExtension.NormalWord.ReducedWord.prod, of3, map_mul]
  | cons last revRest =>
      rcases last with ⟨w, z⟩
      let rest := revRest.reverse
      have hpre : pre = rest ++ [(w, z)] := by
        dsimp [rest]
        rw [← List.reverse_inj]
        simp [hrev]
      have hrestchain : (rest ++ [(w, z)]).IsChain
          (ChainRel datum hfree) := by simpa [hpre] using hprechain
      let L' : LeftContext datum hfree :=
        { word :=
            { head := L.word.head
              toList := rest ++ [(w, z * x)]
              chain := chain_replace_last_coefficient datum hfree rest w z
                (z * x) hrestchain }
          head_mem := L.head_mem
          coeff_mem := by
            intro p hp
            rw [List.mem_append] at hp
            rcases hp with hp | hp
            · exact hpremem p (by rw [hpre]; exact List.mem_append_left _ hp)
            · have hp' : p = (w, z * x) := by simpa using hp
              subst p
              apply dCyclic.mul_mem
              · exact hpremem (w, z) (by simp [hpre])
              · exact hx }
      refine ⟨L', by simp [L', hpre], ?_⟩
      simp [L', leftValue, prefixValue, listValue,
        HNNExtension.NormalWord.ReducedWord.prod, hpre, List.map_append,
        of3, map_mul, mul_assoc]

/-- Delete the first stable letter of a right context and absorb a power of
`e` into its new head coefficient. -/
private theorem exists_right_absorb
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (R : RightContext datum hfree)
    (v : ℤˣ) (b y : BorisovHNNModel.Gamma3)
    (tail : List (ℤˣ × BorisovHNNModel.Gamma3))
    (hlist : R.word.toList = (v, b) :: tail) (hy : y ∈ eCyclic) :
    ∃ R' : RightContext datum hfree,
      R'.word.toList.length = tail.length ∧
      rightValue datum hfree R' =
        of3 datum hfree y * of3 datum hfree b *
          listValue datum hfree tail := by
  have htailchain : tail.IsChain (ChainRel datum hfree) := by
    have := R.word.chain
    rw [hlist, List.isChain_cons] at this
    exact this.2
  let R' : RightContext datum hfree :=
    { word :=
        { head := y * b
          toList := tail
          chain := htailchain }
      head_mem := eCyclic.mul_mem hy
        (R.coeff_mem (v, b) (by simp [hlist]))
      coeff_mem := by
        intro p hp
        exact R.coeff_mem p (by rw [hlist]; exact List.mem_cons_of_mem _ hp) }
  refine ⟨R', rfl, ?_⟩
  simp [R', rightValue, listValue,
    HNNExtension.NormalWord.ReducedWord.prod, of3, map_mul, mul_assoc]

/-- Borisov's Assertion V in the exact coefficient form consumed by Lemma 4.
An `U`-coefficient is transported by `cEquiv`; a `V`-coefficient is
transported by its inverse.  In both cases the positive middle word changes
by finitely many (in the published proof, at most one) Thue steps. -/
structure PinchClassification (datum : Thue.StandingDatum)
    (hfree : RankFiveFree datum) : Prop where
  source : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (hmem : BorisovHNNModel.d3 ^ f * positive3 Q *
        BorisovHNNModel.e3 ^ r ∈ U datum),
    ∃ (Q' : List (Fin 2)) (f' r' : ℤ),
      ThueEq (Thue.systemOf datum.F datum.E) Q Q' ∧
      ((cEquiv datum hfree
        ⟨BorisovHNNModel.d3 ^ f * positive3 Q *
          BorisovHNNModel.e3 ^ r, hmem⟩ : V datum) :
            BorisovHNNModel.Gamma3) =
        BorisovHNNModel.d3 ^ f' * positive3 Q' *
          BorisovHNNModel.e3 ^ r'
  target : ∀ (Q : List (Fin 2)) (f r : ℤ)
      (hmem : BorisovHNNModel.d3 ^ f * positive3 Q *
        BorisovHNNModel.e3 ^ r ∈ V datum),
    ∃ (Q' : List (Fin 2)) (f' r' : ℤ),
      ThueEq (Thue.systemOf datum.F datum.E) Q Q' ∧
      (((cEquiv datum hfree).symm
        ⟨BorisovHNNModel.d3 ^ f * positive3 Q *
          BorisovHNNModel.e3 ^ r, hmem⟩ : U datum) :
            BorisovHNNModel.Gamma3) =
        BorisovHNNModel.d3 ^ f' * positive3 Q' *
          BorisovHNNModel.e3 ^ r'

private theorem source_pinch_reduces
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (P Q Q' : List (Fin 2)) (f r f' r' : ℤ)
    (L : LeftContext datum hfree) (R : RightContext datum hfree)
    (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
    (b : BorisovHNNModel.Gamma3)
    (tail : List (ℤˣ × BorisovHNNModel.Gamma3))
    (hL : L.word.toList =
      pre ++ [(1, BorisovHNNModel.d3 ^ f)])
    (hR : R.word.toList = (-1, b) :: tail)
    (hRhead : R.word.head = BorisovHNNModel.e3 ^ r)
    (hmem : BorisovHNNModel.d3 ^ f * positive3 Q *
      BorisovHNNModel.e3 ^ r ∈ U datum)
    (htransport :
      ((cEquiv datum hfree
        ⟨BorisovHNNModel.d3 ^ f * positive3 Q *
          BorisovHNNModel.e3 ^ r, hmem⟩ : V datum) :
            BorisovHNNModel.Gamma3) =
        BorisovHNNModel.d3 ^ f' * positive3 Q' *
          BorisovHNNModel.e3 ^ r')
    (heq : Lemma4Equation datum hfree P Q L R) :
    ∃ (L' : LeftContext datum hfree) (R' : RightContext datum hfree),
      Lemma4Equation datum hfree P Q' L' R' ∧
      contextComplexity datum hfree L' R' <
        contextComplexity datum hfree L R := by
  have hdf : BorisovHNNModel.d3 ^ f' ∈ dCyclic := by
    rw [dCyclic, Subgroup.mem_closure_singleton]
    exact ⟨f', rfl⟩
  have her : BorisovHNNModel.e3 ^ r' ∈ eCyclic := by
    rw [eCyclic, Subgroup.mem_closure_singleton]
    exact ⟨r', rfl⟩
  rcases exists_left_absorb datum hfree L pre 1
      (BorisovHNNModel.d3 ^ f)
      (BorisovHNNModel.d3 ^ f') hL hdf with
    ⟨L', hLlen, hLval⟩
  rcases exists_right_absorb datum hfree R (-1) b
      (BorisovHNNModel.e3 ^ r') tail hR her with
    ⟨R', hRlen, hRval⟩
  refine ⟨L', R', ?_, ?_⟩
  · let middle := BorisovHNNModel.d3 ^ f * positive3 Q *
        BorisovHNNModel.e3 ^ r
    have hconj :
        (HNNExtension.t : Gamma2 datum hfree) *
            of3 datum hfree middle * HNNExtension.t⁻¹ =
          of3 datum hfree
            (BorisovHNNModel.d3 ^ f' * positive3 Q' *
              BorisovHNNModel.e3 ^ r') := by
      have h := (HNNExtension.equiv_eq_conj
        (φ := cEquiv datum hfree) ⟨middle, hmem⟩).symm
      simpa [middle, htransport, of3] using h
    have hnorm :
        (positive2 datum hfree P)⁻¹ *
            prefixValue datum hfree L.word.head pre *
            ((HNNExtension.t : Gamma2 datum hfree) *
              of3 datum hfree middle * HNNExtension.t⁻¹) *
            of3 datum hfree b * listValue datum hfree tail = 1 := by
      simpa [middle, Lemma4Equation, positive2, leftValue, rightValue, prefixValue,
        listValue, HNNExtension.NormalWord.ReducedWord.prod, hL, hR,
        List.map_append, hRhead, of3, map_mul, map_inv, mul_assoc] using heq
    rw [hconj] at hnorm
    change (positive2 datum hfree P)⁻¹ * leftValue datum hfree L' *
      positive2 datum hfree Q' * rightValue datum hfree R' = 1
    rw [hLval, hRval]
    simpa [Lemma4Equation, positive2, of3, map_mul, mul_assoc] using hnorm
  · simp only [contextComplexity, hLlen, hRlen]
    have hLlength : L.word.toList.length = pre.length + 1 := by simp [hL]
    have hRlength : R.word.toList.length = tail.length + 1 := by simp [hR]
    omega

private theorem target_pinch_reduces
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (P Q Q' : List (Fin 2)) (f r f' r' : ℤ)
    (L : LeftContext datum hfree) (R : RightContext datum hfree)
    (pre : List (ℤˣ × BorisovHNNModel.Gamma3))
    (b : BorisovHNNModel.Gamma3)
    (tail : List (ℤˣ × BorisovHNNModel.Gamma3))
    (hL : L.word.toList =
      pre ++ [(-1, BorisovHNNModel.d3 ^ f)])
    (hR : R.word.toList = (1, b) :: tail)
    (hRhead : R.word.head = BorisovHNNModel.e3 ^ r)
    (hmem : BorisovHNNModel.d3 ^ f * positive3 Q *
      BorisovHNNModel.e3 ^ r ∈ V datum)
    (htransport :
      (((cEquiv datum hfree).symm
        ⟨BorisovHNNModel.d3 ^ f * positive3 Q *
          BorisovHNNModel.e3 ^ r, hmem⟩ : U datum) :
            BorisovHNNModel.Gamma3) =
        BorisovHNNModel.d3 ^ f' * positive3 Q' *
          BorisovHNNModel.e3 ^ r')
    (heq : Lemma4Equation datum hfree P Q L R) :
    ∃ (L' : LeftContext datum hfree) (R' : RightContext datum hfree),
      Lemma4Equation datum hfree P Q' L' R' ∧
      contextComplexity datum hfree L' R' <
        contextComplexity datum hfree L R := by
  have hdf : BorisovHNNModel.d3 ^ f' ∈ dCyclic := by
    rw [dCyclic, Subgroup.mem_closure_singleton]
    exact ⟨f', rfl⟩
  have her : BorisovHNNModel.e3 ^ r' ∈ eCyclic := by
    rw [eCyclic, Subgroup.mem_closure_singleton]
    exact ⟨r', rfl⟩
  rcases exists_left_absorb datum hfree L pre (-1)
      (BorisovHNNModel.d3 ^ f)
      (BorisovHNNModel.d3 ^ f') hL hdf with
    ⟨L', hLlen, hLval⟩
  rcases exists_right_absorb datum hfree R 1 b
      (BorisovHNNModel.e3 ^ r') tail hR her with
    ⟨R', hRlen, hRval⟩
  refine ⟨L', R', ?_, ?_⟩
  · let middle := BorisovHNNModel.d3 ^ f * positive3 Q *
        BorisovHNNModel.e3 ^ r
    have hconj :
        (HNNExtension.t : Gamma2 datum hfree)⁻¹ *
            of3 datum hfree middle * HNNExtension.t =
          of3 datum hfree
            (BorisovHNNModel.d3 ^ f' * positive3 Q' *
              BorisovHNNModel.e3 ^ r') := by
      have h := (HNNExtension.equiv_symm_eq_conj
        (φ := cEquiv datum hfree) ⟨middle, hmem⟩).symm
      simpa [middle, htransport, of3] using h
    have hnorm :
        (positive2 datum hfree P)⁻¹ *
            prefixValue datum hfree L.word.head pre *
            ((HNNExtension.t : Gamma2 datum hfree)⁻¹ *
              of3 datum hfree middle * HNNExtension.t) *
            of3 datum hfree b * listValue datum hfree tail = 1 := by
      simpa [middle, Lemma4Equation, positive2, leftValue, rightValue,
        prefixValue, listValue, HNNExtension.NormalWord.ReducedWord.prod,
        hL, hR, List.map_append, hRhead, of3, map_mul, map_inv,
        mul_assoc] using heq
    rw [hconj] at hnorm
    change (positive2 datum hfree P)⁻¹ * leftValue datum hfree L' *
      positive2 datum hfree Q' * rightValue datum hfree R' = 1
    rw [hLval, hRval]
    simpa [Lemma4Equation, positive2, of3, map_mul, mul_assoc] using hnorm
  · simp only [contextComplexity, hLlen, hRlen]
    have hLlength : L.word.toList.length = pre.length + 1 := by simp [hL]
    have hRlength : R.word.toList.length = tail.length + 1 := by simp [hR]
    omega

/-- All HNN manipulation in the positive-`c` induction follows formally from
the base-group coefficient classification. -/
theorem pinchReduction_of_classification
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (hclass : PinchClassification datum hfree) :
    PinchReduction datum hfree := by
  intro P Q L R heq
  by_cases hzero : contextComplexity datum hfree L R = 0
  · exact Or.inl hzero
  · right
    rcases lemma4_boundary_pinch_power_form datum hfree P Q L R heq hzero with
      ⟨f, r, pre, b, tail, hsource | htarget⟩
    · rcases hsource with ⟨hL, hR, hRhead, hmem⟩
      rcases hclass.source Q f r hmem with
        ⟨Q', f', r', hQQ', htransport⟩
      rcases source_pinch_reduces datum hfree P Q Q' f r f' r' L R
          pre b tail hL hR hRhead hmem htransport heq with
        ⟨L', R', heq', hlt⟩
      exact ⟨Q', L', R', hQQ', heq', hlt⟩
    · rcases htarget with ⟨hL, hR, hRhead, hmem⟩
      rcases hclass.target Q f r hmem with
        ⟨Q', f', r', hQQ', htransport⟩
      rcases target_pinch_reduces datum hfree P Q Q' f r f' r' L R
          pre b tail hL hR hRhead hmem htransport heq with
        ⟨L', R', heq', hlt⟩
      exact ⟨Q', L', R', hQQ', heq', hlt⟩

/-- Borisov's Lemma 4 derived from `PinchClassification`. -/
theorem borisovLemma4_of_classification
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (hclass : PinchClassification datum hfree) :
    BorisovLemma4 datum hfree :=
  borisovLemma4_of_pinchReduction datum hfree
    (pinchReduction_of_classification datum hfree hclass)

end

end BorisovLemma4Pinch
end Undecidability
