/-
Copyright (c) 2026 Chris Henson and Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson, Lean Pool contributors
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.SymOrbit

/-! # Checking leaf invariance using generators

A group certificate gives a generator and an earlier index for each nonidentity permutation.
Consequently symmetries only need to be checked for those generators.
-/

@[expose] public section

namespace RACert

private theorem generatorStep {t : ℕ} {perms : List (List ℕ × List ℕ)}
    {gens : List (ℕ × List ℕ)} {inv : List ℕ} (h : checkBitGroup t perms gens inv = true)
    {i : ℕ} (hpositive : 0 < i) (hi : i < perms.length) :
    ∃ g ∈ gens, ∃ j < i, ∀ x < t,
      nth 0 (pAt perms i) x = nth 0 (pAt perms g.1) (nth 0 (pAt perms j) x) := by
  simp only [checkBitGroup, Bool.and_eq_true] at h
  obtain ⟨_, _, _, _, hrows, hcover, _⟩ := h
  have hb : (maskOf (gens.flatMap fun g => childrenFrom 0 g.2) ||| 1).testBit i =
      (2 ^ perms.length - 1).testBit i :=
    congrArg (fun mask => mask.testBit i) (Nat.beq_eq.mp hcover)
  rw [Nat.testBit_or, testBit_maskOf, Nat.testBit_two_pow_sub_one, decide_eq_true hi,
    Bool.or_eq_true, decide_eq_true_iff, Nat.testBit_one_eq_true_iff_self_eq_zero] at hb
  rcases hb with hm | hz
  · obtain ⟨g, hg, hchild⟩ := List.mem_flatMap.mp hm
    obtain ⟨j, hj, hindex⟩ := exists_of_mem_childrenFrom hchild
    have hji : j < i := by omega
    have hrow := allZip_spec ([], []) 0 (List.all_eq_true.mp hrows g hg) j (hji.trans hi)
    rw [Bool.and_eq_true, Nat.blt_eq] at hrow
    rw [pAtB_blocks hrow.1, hindex] at hrow
    exact ⟨g, hg, j, hji, eqComp_spec hrow.2⟩
  · omega

private theorem bitAct_comp_of_pointwise {t i j k : ℕ} {perms : List (List ℕ × List ℕ)}
    (hi : checkBitPerm t (pAt perms i) (qAt perms i) = true)
    (hj : checkBitPerm t (pAt perms j) (qAt perms j) = true)
    (hk : checkBitPerm t (pAt perms k) (qAt perms k) = true)
    (h : ∀ x < t, nth 0 (pAt perms i) x =
      nth 0 (pAt perms j) (nth 0 (pAt perms k) x)) (α : ℕ) :
    bitAct t perms i α = bitAct t perms j (bitAct t perms k α) := by
  refine Nat.eq_of_testBit_eq fun y => ?_
  rw [bitAct, bitAct, bitAct, testBit_actBits hi, testBit_actBits hj, testBit_actBits hk]
  by_cases hy : y < t
  · obtain ⟨_, hjlt, _, hjinv⟩ := checkBitPerm_spec hj hy
    obtain ⟨_, hklt, _, hkinv⟩ := checkBitPerm_spec hk hjlt
    obtain ⟨_, _, hiinv, _⟩ := checkBitPerm_spec hi hklt
    rw [h _ hklt, hkinv, hjinv] at hiinv
    rw [hiinv, decide_eq_true hjlt, Bool.true_and]
  · rw [decide_eq_false hy, Bool.false_and, Bool.false_and]

/-- An invariant of all checked generators is an invariant of every listed group element. -/
theorem bitAct_invariant_of_generators {t : ℕ} {perms : List (List ℕ × List ℕ)}
    {gens : List (ℕ × List ℕ)} {inv : List ℕ} {F : ℕ → ℕ}
    (h : checkBitGroup t perms gens inv = true)
    (hgen : ∀ g ∈ gens, g.1 < perms.length ∧ ∀ α < 2 ^ t, F (bitAct t perms g.1 α) = F α) :
    ∀ i < perms.length, ∀ α < 2 ^ t, F (bitAct t perms i α) = F α := by
  have hg := isActGroup_of_check h
  have hperm := (checkBitGroup_spec h).1
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi α hα
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hg.one_act α hα]
    · obtain ⟨g, hm, j, hj, hstep⟩ := generatorStep h hpos hi
      obtain ⟨hIndex, hInvariant⟩ := hgen g hm
      have hj' := hj.trans hi
      rw [bitAct_comp_of_pointwise (hperm i hi) (hperm _ hIndex) (hperm j hj') hstep,
        hInvariant _ (hg.act_lt j hj' α hα), ih j hj hj' α hα]

namespace Problem

/-- Match each generator with a symmetry preserving its action on the high variables. -/
noncomputable def checkGeneratorSymmetries (P : Problem) (b : ℕ)
    (perms : List (List ℕ × List ℕ)) : List (ℕ × List ℕ) → List Sym → Bool
  | [], [] => true
  | g :: gens, s :: syms => Nat.blt g.1 perms.length &&
    (P.checkSym b s (pAt perms g.1, qAt perms g.1) &&
      checkGeneratorSymmetries P b perms gens syms)
  | _, _ => false

private theorem checkGeneratorSymmetries_spec {P : Problem} {b : ℕ}
    {perms : List (List ℕ × List ℕ)} :
    ∀ {gens : List (ℕ × List ℕ)} {syms : List Sym},
      P.checkGeneratorSymmetries b perms gens syms = true →
      ∀ g ∈ gens, g.1 < perms.length ∧
        ∃ s, P.checkSym b s (pAt perms g.1, qAt perms g.1) = true
  | [], _, _, _, hg => by simp at hg
  | _ :: _, [], h, _, _ => by simp [checkGeneratorSymmetries] at h
  | g' :: gens, s :: syms, h, g, hg => by
    rw [checkGeneratorSymmetries, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.mp hg with rfl | hm
    · exact ⟨h.1, s, h.2.1⟩
    · exact checkGeneratorSymmetries_spec h.2.2 g hm

/-- Count with checked generator symmetries and a complete list of orbit representatives. -/
theorem fixCountL_of_orbitGenerators {P : Problem} (hcheck : P.check = true)
    (hrows : P.checkRows = true) {b t hi : ℕ} (hb : Nat.ble b P.V = true)
    (ht : Nat.beq t (P.V - b) = true) (hhi : Nat.beq hi (2 ^ t) = true)
    {syms : List Sym} {perms : List (List ℕ × List ℕ)} {gens : List (ℕ × List ℕ)} {inv : List ℕ}
    (hsyms : P.checkGeneratorSymmetries b perms gens syms = true)
    (hgrp : checkBitGroup t perms gens inv = true) {W : ℕ}
    (hseg : OrbitSeg t perms (P.leaf b) 0 hi hi W) : fixCountL P.s P.n P.perm = W := by
  have hb' := Nat.le_of_ble_eq_true hb
  obtain rfl := Nat.eq_of_beq_eq_true ht
  obtain rfl := Nat.eq_of_beq_eq_true hhi
  have hinv := bitAct_invariant_of_generators (F := P.leaf b) hgrp (fun g hg => by
    obtain ⟨hIndex, s, hs⟩ := checkGeneratorSymmetries_spec hsyms g hg
    exact ⟨hIndex, fun α hα =>
      leaf_actBits hcheck hrows hb' hs ((checkBitGroup_spec hgrp).1 _ hIndex) hα⟩)
  rw [fixCountL_eq_sumLeaves hcheck hrows hb', sumLeaves_eq_sum]
  simp only [Nat.zero_add]
  refine OrbitSeg.sum_eq hgrp (fun e he α hα => ?_) hseg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  simpa only [bitAct, pAt, nth_eq_getElem ([], []) hi] using hinv i hi α hα

end Problem

end RACert
