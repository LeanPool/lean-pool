/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import Mathlib.Computability.DFA
import Mathlib.Computability.NFA
import Mathlib.Data.Set.Finite.Range

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Automata for the words used in a linear component

The converse construction needs languages consisting of fixed words followed
by repetitions of other fixed words. We prove regularity of these particular
operations using finite families of continuation languages.

Think of a state as the language of suffixes still to be read. A finite family
that covers every one-letter continuation supplies an NFA; its transition
condition ensures soundness and the cover property ensures completeness.
Mathlib's existing subset construction turns this NFA into a DFA.

Fixed-word and starred-word prefixes are obtained by adding finitely many
suffix states. These are classical existence proofs of automata, not an
executable implementation of a grammar compiler.
-/
open scoped Computability

namespace Parikh
variable {T : Type*}

/-- A finite family of languages covering every one-letter continuation gives
a finite NFA. Transitions are sound language inclusions, and the cover hypothesis
ensures completeness; determinization is Mathlib's existing construction. -/
theorem isRegular_of_finite_language_cover (L : Language T)
    (F : Set (Language T)) (hF : F.Finite) (hL : L ∈ F)
    (hcover : ∀ K ∈ F, ∀ a w, a :: w ∈ K →
      ∃ J ∈ F, w ∈ J ∧ ∀ v ∈ J, a :: v ∈ K) : L.IsRegular := by
  classical
  let : Fintype F := hF.fintype
  let M : NFA T F :=
    { step := fun K a => {J | ∀ v ∈ J.val, a :: v ∈ K.val}
      start := {⟨L, hL⟩}
      accept := {K | [] ∈ K.val} }
  have hcons (K : F) (a : T) (w : List T) :
      a :: w ∈ K.val ↔ ∃ J ∈ M.step K a, w ∈ J.val := by
    constructor
    · intro hw
      obtain ⟨J, hJ, hw, hs⟩ := hcover K.val K.prop a w hw
      exact ⟨⟨J, hJ⟩, hs, hw⟩
    · rintro ⟨J, hs, hw⟩
      exact hs w hw
  have heval (w : List T) (S : Set F) :
      (∃ K ∈ M.evalFrom S w, [] ∈ K.val) ↔ ∃ K ∈ S, w ∈ K.val := by
    induction w generalizing S with
    | nil => rfl
    | cons a w ih =>
      rw [NFA.evalFrom_cons, ih]
      constructor
      · rintro ⟨J, hJ, hw⟩
        obtain ⟨K, hK, hs⟩ := NFA.mem_stepSet.mp hJ
        exact ⟨K, hK, (hcons K a w).mpr ⟨J, hs, hw⟩⟩
      · rintro ⟨K, hK, hw⟩
        obtain ⟨J, hs, hw⟩ := (hcons K a w).mp hw
        exact ⟨J, NFA.mem_stepSet.mpr ⟨K, hK, hs⟩, hw⟩
  have hM : M.accepts = L := by
    ext w
    rw [NFA.mem_accepts]
    change (∃ K, [] ∈ K.val ∧ K ∈ M.evalFrom {⟨L, hL⟩} w) ↔ w ∈ L
    constructor
    · rintro ⟨K, ha, hs⟩
      obtain ⟨J, hJ, hw⟩ := (heval w {⟨L, hL⟩}).mp ⟨K, hs, ha⟩
      have hJ : J = ⟨L, hL⟩ := Set.mem_singleton_iff.mp hJ
      cases hJ
      exact hw
    · intro hw
      obtain ⟨K, hs, ha⟩ := (heval w {⟨L, hL⟩}).mpr
        ⟨⟨L, hL⟩, Set.mem_singleton _, hw⟩
      exact ⟨K, ha, hs⟩
  exact Language.isRegular_iff.mpr
    ⟨Set F, inferInstance, M.toDFA, M.toDFA_correct.trans hM⟩

/-- A one-state rejecting NFA suffices for the empty language. -/
theorem isRegular_zero : (0 : Language T).IsRegular := by
  apply isRegular_of_finite_language_cover _ {0} (Set.finite_singleton _) (by simp)
  intro K hK a w hw
  have hK : K = 0 := Set.mem_singleton_iff.mp hK
  subst K
  exact (Language.notMem_zero _ hw).elim

/-- A one-state accepting NFA with no transitions recognizes epsilon. -/
theorem isRegular_one : (1 : Language T).IsRegular := by
  apply isRegular_of_finite_language_cover _ {1} (Set.finite_singleton _) (by simp)
  intro K hK a w hw
  have hK : K = 1 := Set.mem_singleton_iff.mp hK
  subst K
  simp only [Language.mem_one, List.cons_ne_nil] at hw

/-- Reading the head of a literal prefix leaves its tail as the prefix. -/
theorem mem_word_mul_cons (a b : T) (u x : List T) (L : Language T) :
    a :: x ∈ ({b :: u} : Language T) * L ↔
      a = b ∧ x ∈ ({u} : Language T) * L := by
  simp only [Language.mem_mul]
  change (∃ p, p = b :: u ∧ ∃ v ∈ L, p ++ v = a :: x) ↔
    a = b ∧ ∃ p, p = u ∧ ∃ v ∈ L, p ++ v = x
  simp only [exists_eq_left, List.cons_append, List.cons.injEq]
  constructor
  · rintro ⟨v, hv, hab, hx⟩
    exact ⟨hab.symm, v, hv, hx⟩
  · rintro ⟨hab, v, hv, hx⟩
    exact ⟨v, hv, hab.symm, hx⟩

/-- Prepending one fixed word preserves DFA regularity. The additional NFA
states are the finitely many suffixes of that word. -/
theorem isRegular_word_mul (w : List T) (R : Language T) (hR : R.IsRegular) :
    (({w} : Language T) * R).IsRegular := by
  classical
  obtain ⟨σ, hσ, M, rfl⟩ := hR
  let : Fintype σ := hσ
  let F : Set (Language T) := Set.range M.acceptsFrom ∪
    (fun u => ({u} : Language T) * M.accepts) '' (↑w.tails.toFinset : Set (List T))
  have hF : F.Finite := (Set.finite_range M.acceptsFrom).union
    (w.tails.toFinset.finite_toSet.image _)
  have htail (u : List T) (hu : u <:+ w) : ({u} : Language T) * M.accepts ∈ F := by
    exact Or.inr ⟨u, by simpa using (List.mem_tails u w).mpr hu, rfl⟩
  have hdfa (s : σ) (a : T) (x : List T) (hx : a :: x ∈ M.acceptsFrom s) :
      ∃ J ∈ F, x ∈ J ∧ ∀ v ∈ J, a :: v ∈ M.acceptsFrom s := by
    refine ⟨M.acceptsFrom (M.step s a), Or.inl ⟨_, rfl⟩, ?_, ?_⟩
    · simpa only [DFA.mem_acceptsFrom, DFA.evalFrom_cons] using hx
    · intro v hv
      simpa only [DFA.mem_acceptsFrom, DFA.evalFrom_cons] using hv
  apply isRegular_of_finite_language_cover _ F hF (htail w (List.suffix_refl _))
  intro K hK a x hx
  rcases hK with hK | hK
  · obtain ⟨s, rfl⟩ := hK
    exact hdfa s a x hx
  · obtain ⟨u, hu, rfl⟩ := hK
    have hu : u <:+ w := (List.mem_tails u w).mp (by simpa using hu)
    cases u with
    | nil =>
      change a :: x ∈ (1 : Language T) * M.accepts at hx
      rw [one_mul] at hx
      simpa only [show ({[]} : Language T) = 1 from rfl, one_mul, DFA.accepts] using
        hdfa M.start a x hx
    | cons b u =>
      obtain ⟨hab, hrest⟩ := (mem_word_mul_cons a b u x M.accepts).mp hx
      subst b
      refine ⟨({u} : Language T) * M.accepts,
        htail u ((List.suffix_cons a u).trans hu), hrest, ?_⟩
      intro v hv
      exact (mem_word_mul_cons a a u v M.accepts).mpr ⟨rfl, hv⟩

/-- Prepending any number of copies of one fixed word preserves DFA regularity.
Suffix states return to the same starred prefix; transitions may also enter the
continuation DFA. The empty repeated word is handled without epsilon loops. -/
theorem isRegular_word_star_mul (w : List T) (R : Language T) (hR : R.IsRegular) :
    (({w} : Language T)∗ * R).IsRegular := by
  classical
  cases w with
  | nil =>
    simpa only [show ({[]} : Language T) = 1 from rfl, kstar_one, one_mul] using hR
  | cons b bs =>
    obtain ⟨σ, hσ, M, rfl⟩ := hR
    let : Fintype σ := hσ
    let S : Language T := ({b :: bs} : Language T)∗ * M.accepts
    let F : Set (Language T) := Set.range M.acceptsFrom ∪
      (fun u => ({u} : Language T) * S) '' (↑(b :: bs).tails.toFinset : Set (List T))
    have hF : F.Finite := (Set.finite_range M.acceptsFrom).union
      ((b :: bs).tails.toFinset.finite_toSet.image _)
    have htail (u : List T) (hu : u <:+ b :: bs) : ({u} : Language T) * S ∈ F := by
      exact Or.inr ⟨u, by simpa using (List.mem_tails u (b :: bs)).mpr hu, rfl⟩
    have hdfa (s : σ) (a : T) (x : List T) (hx : a :: x ∈ M.acceptsFrom s) :
        ∃ J ∈ F, x ∈ J ∧ ∀ v ∈ J, a :: v ∈ M.acceptsFrom s := by
      refine ⟨M.acceptsFrom (M.step s a), Or.inl ⟨_, rfl⟩, ?_, ?_⟩
      · simpa only [DFA.mem_acceptsFrom, DFA.evalFrom_cons] using hx
      · intro v hv
        simpa only [DFA.mem_acceptsFrom, DFA.evalFrom_cons] using hv
    have hunfold : S = M.accepts + ({b :: bs} : Language T) * S := by
      dsimp [S]
      conv_lhs => rw [← Language.one_add_self_mul_kstar_eq_kstar ({b :: bs} : Language T)]
      rw [add_mul, one_mul, mul_assoc]
    have hstart : S ∈ F := by
      simpa only [show ({[]} : Language T) = 1 from rfl, one_mul] using
        htail [] List.nil_suffix
    apply isRegular_of_finite_language_cover S F hF hstart
    intro K hK a x hx
    rcases hK with hK | hK
    · obtain ⟨s, rfl⟩ := hK
      exact hdfa s a x hx
    · obtain ⟨u, hu, rfl⟩ := hK
      have hu : u <:+ b :: bs := (List.mem_tails u (b :: bs)).mp (by simpa using hu)
      cases u with
      | nil =>
        change a :: x ∈ (1 : Language T) * S at hx
        rw [one_mul, hunfold, Language.mem_add] at hx
        change ∃ J ∈ F, x ∈ J ∧ ∀ v ∈ J, a :: v ∈ (1 : Language T) * S
        simp only [one_mul]
        rcases hx with hx | hx
        · obtain ⟨J, hJ, hx, hs⟩ := hdfa M.start a x hx
          refine ⟨J, hJ, hx, ?_⟩
          intro v hv
          rw [hunfold, Language.mem_add]
          exact Or.inl (hs v hv)
        · obtain ⟨hab, hrest⟩ := (mem_word_mul_cons a b bs x S).mp hx
          subst b
          refine ⟨({bs} : Language T) * S, htail bs (List.suffix_cons a bs), hrest, ?_⟩
          intro v hv
          rw [hunfold, Language.mem_add]
          exact Or.inr ((mem_word_mul_cons a a bs v S).mpr ⟨rfl, hv⟩)
      | cons c u =>
        obtain ⟨hac, hrest⟩ := (mem_word_mul_cons a c u x S).mp hx
        subst c
        refine ⟨({u} : Language T) * S,
          htail u ((List.suffix_cons a u).trans hu), hrest, ?_⟩
        intro v hv
        exact (mem_word_mul_cons a a u v S).mpr ⟨rfl, hv⟩

end Parikh
