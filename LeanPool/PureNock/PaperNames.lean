/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import Batteries.Tactic.Alias
public import LeanPool.PureNock.PureComplete
public import LeanPool.PureNock.PureCompleteHint
public import LeanPool.PureNock.NounValidation
public import LeanPool.PureNock.Dyck

/-!
# Pure paper-name aliases

Aliases to labelled objects from the same authorial line as ePrint 2025/1110
(https://eprint.iacr.org/2025/1110). `paper/main.tex` is the bundled draft (different revision/title).
-/

@[expose] public section

namespace NockPure

/-! ## Proper trees and nouns (`main.tex:318–349`) -/

/-- Def:Proper_BT (main.tex:318–327): L_full_BT = {t | size=1 ∨ (left,right ∈ L_full_BT ∧ left ∩ right = ∅)}; L^λ_full_BT = {t ∈ L_full_BT | size=λ}. -/
alias «Def:Proper_BT» := Nock.BTree
/-- Def:tree_nodes (main.tex:329–331): leaf = no children; internal = not a leaf. -/
alias «Def:tree_nodes» := Nock.Noun.internal
/-- Lem:pbt_size (main.tex:333–335): t ∈ L_full_BT^{2λ−1} has λ−1 internal and λ leaf nodes. -/
alias «Lem:pbt_size» := Nock.Noun.pbt_size_of_size
/-- Lem:optimal_dyck (main.tex:340–342): L_dk ≡ L_full_BT; ∀λ, L^{2λ}_dk ≡ L^{2λ+1}_full_BT; |L^{2λ}_dk| = C_λ. -/
alias «Lem:optimal_dyck» := Nock.BTree.dyck_iff_encode
/-- Def:noun (main.tex:347–349): n := (t,dt) ∈ L_dk^{2(λ−1)} × DT(F)^λ := N^λ(F) is a noun of size λ over F. -/
alias «Def:noun» := Nock.Noun

/-! ## Formalizing Nock (`main.tex:1034–1270`) -/

/-- Def:verb (main.tex:1034–1041): verb := (actions,noun) ∈ (X ∪ {*,⊥})^{λ−1} × N^λ(F); terminal iff actions are all ⊥. -/
alias «Def:verb» := Nock.Verb
/-- Algorithm:Opcode_Updates_verb (main.tex:1054–1078): OP_i : D(V) → V ∪ {⊥} for i∈[11], plus cons on cell opcode. -/
alias «Algorithm:Opcode_Updates_verb» := Nock.Verb.redex
/-- Def:NockProgram (main.tex:1090–1099): F = *[subject,formula] with subject,formula terminal; NockProgram^Λ = {F | λ≤Λ}. -/
alias «Def:NockProgram» := Nock.Verb.IsNockProgram
/-- Def:eval_trace (main.tex:1114–1127): T=(t_0,…,t_n) consistent iff t_0=F and ∀i Nock(t_i,t_{i+1})=0; complete/valid/invalid/continuation. -/
alias «Def:eval_trace» := Nock.Verb.Consistent
/-- Def:Nock (main.tex:1130–1135): NockVM^Λ = {F | ∃ complete trace T with t_0=F and λ≤Λ}. -/
alias «Def:Nock» := Nock.Verb.FiniteΛ
/-- Corr:valid_invalid_finite (main.tex:1137–1139): all valid and invalid verbs are finite. -/
alias «Corr:valid_invalid_finite» := Nock.Verb.finite_of_valid_or_invalid
/-- Lem:domain (main.tex:1141–1143): non-null continuation c ⇒ map(c,getIndex(c)) ∈ D(V). -/
alias «Lem:domain» := Nock.Verb.domain
/-- lemma:equiv_continuations (main.tex:1150–1154): NockVM^Λ ≡ FiniteTransitions^Λ. -/
alias «lemma:equiv_continuations» := Nock.Verb.equiv_continuationsΛ
/-- Thm:deterministic_Trace (main.tex:1156–1158): strict map ⇒ ≤1 consistent evaluation trace of size n. -/
alias «Thm:deterministic_Trace» := Nock.Verb.deterministic_Trace_strict
/-- Lem:decomp (main.tex:1210–1213): ∃! λ_L,λ_R>0 with λ=λ_L+λ_R, n_L∈N^{λ_L}, n_R∈N^{λ_R} ⇔ n=cons(n_L,n_R), n∈N^λ. -/
alias «Lem:decomp» := Nock.Noun.decomp
/-- Algorithm:Valid_Noun (main.tex:1244–1260): CheckValidNoun(n₀;T) walks mset via transcript; Accept iff mset empties. -/
alias «Algorithm:Valid_Noun» := Nock.checkValidNoun
/-- Thm:Noun_Validation (main.tex:1268–1269): n∈N^λ(F) ⇔ ∃T. CheckValidNoun(n;T)=Accept ∧ |T|=2λ−1. -/
alias «Thm:Noun_Validation» := Nock.Noun_Validation

/-! ## Appendix A (`main.tex:1514–1666`) -/

/-- Algorithm:Noun_Operators (main.tex:1519–1607): ?,=,+,/,# over nouns (Appendix A). -/
alias «Algorithm:Noun_Operators» := Nock.Verb.reduce
/-- Algorithm:Unroll_Operator (main.tex:1616–1626): −(i,n): i=3 ↦ ?(n); i=4 ↦ +(n); else ⊥. -/
alias «Algorithm:Unroll_Operator» := Nock.Verb.reduce
/-- Algorithm:Transition_Function (main.tex:1637–1662): Nock(T_i,T_{i+1}) checks local OP_i/cons step at getIndex. -/
alias «Algorithm:Transition_Function» := Nock.Verb.NockCheck

end NockPure
