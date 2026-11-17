/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic

/-!
# The `k`-uniform infinite Ramsey theorem

Any finite colouring of the `k`-element `Finset`s of an infinite set has an infinite subset all of
whose `k`-element subsets share a colour. This is stated purely in terms of `Finset V → K`, with
no `SimpleGraph`/`EdgeLabeling` vocabulary at all: pairs (`k = 2`) recover the classical infinite
Ramsey theorem for graphs (`InfiniteRamsey.lean`, which is a thin corollary of this file, not the
other way around), `k = 1` is the ordinary infinite pigeonhole principle, and `k = 0` is trivial
(there is only one `0`-element `Finset`, namely `∅`).

## Main declarations

* `SimpleGraph.ExistsInfiniteMonochromaticKUniform`: the `k`-uniform statement, as a `Prop`
  indexed by `k` so that it can be proved by induction on `k`.
* `SimpleGraph.existsInfiniteMonochromaticKUniform`: the theorem itself, for every `k`.

## Proof sketch

Induction on `k`, via the same thinning idea as the classical `k = 2` proof (recovered here as
`InfiniteRamsey.lean`'s corollary), generalized so a single construction covers every `k` at once.

* Round `n` picks a point `aSeqK n` from the current candidate set `XseqK n`, and needs an
  infinite subset of the rest of `XseqK n` on which `aSeqK n`, together with any `k`-subset of
  that infinite subset, always gets the same colour `cSeqK n`. For pairs, this would be a single
  finite/infinite pigeonhole on the colours of the edges from `aSeqK n`; here it is exactly one
  application of the level-`k` induction hypothesis, applied to the colouring
  `s ↦ C (insert (aSeqK n) s)` of `k`-subsets: pigeonhole for `k`-subsets is precisely what the
  induction hypothesis supplies.
* Assembly: because the chain `XseqK` is decreasing, every `(k + 1)`-subset `s` of the final
  candidate set `H` has a well-defined minimum-index element `aSeqK n0` (extracted via
  `Function.invFun` on the injective sequence `aSeqK`, then `Finset.min'` on the image indices),
  and the rest of `s` is a `k`-subset of `XseqK (n0 + 1)`, so round `n0`'s guarantee determines
  `C s`. A second, ordinary pigeonhole pass on `cSeqK : ℕ → K` then picks out an infinite set of
  rounds sharing one colour, whose image under `aSeqK` is the desired monochromatic set.

## Implementation notes

`ExistsInfiniteMonochromaticKUniform` is stated with `{V K : Type}` (not `Type*`): applying it to
itself as an induction hypothesis, inside its own recursive proof, otherwise triggers universe
metavariable unification failures between the ambient context's universe and the one at which the
hypothesis was quantified. Pinning both to universe `0` avoids the issue; nothing in this
development needs genuine universe polymorphism.

The induction hypothesis `IH : ExistsInfiniteMonochromaticKUniform k` is threaded as an explicit
argument throughout (`chosenPointK C IH X`, etc.) rather than left as a section `variable`: Lean's
auto-bound-variable mechanism only includes a `variable` into a declaration's signature when the
variable is textually mentioned in the declaration's stated type, and `IH` is otherwise used only
inside proof bodies (and inside `noncomputable def` values), so it would silently be dropped from
`exists_step_k`, `chosenPointK`, `chosenColorK`, and `nextInfiniteSetK` if left implicit.

## References

* F. P. Ramsey, *On a problem of formal logic*, Proc. London Math. Soc. (2) 30 (1930), 264-286.

## Tags

ramsey theory, infinite combinatorics, pigeonhole principle
-/

@[expose] public section

namespace SimpleGraph

/-- The `k`-uniform infinite Ramsey statement, as a `Prop` indexed by `k` so it can be proved
by induction: for any finite colour type `K`, any colouring `C` of `Finset V`s, and any infinite
`X0 : Set V`, some colour `col` and infinite `H ⊆ X0` make every `k`-element subset of `H` have
colour `col` under `C`. -/
def ExistsInfiniteMonochromaticKUniform (k : ℕ) : Prop :=
  ∀ {V K : Type} [Finite K] (C : Finset V → K) {X0 : Set V}, X0.Infinite →
    ∃ (col : K) (H : Set V), H ⊆ X0 ∧ H.Infinite ∧
      ∀ s : Finset V, (s : Set V) ⊆ H → s.card = k → C s = col

/-- Base case `k = 0`: the only `0`-element `Finset` is `∅`, so any colour works. -/
theorem existsInfiniteMonochromaticKUniform_zero : ExistsInfiniteMonochromaticKUniform 0 :=
  fun C _ hX0 => ⟨C ∅, _, subset_rfl, hX0, fun s _ hcard => by rw [Finset.card_eq_zero.mp hcard]⟩

section Step

variable {k : ℕ} {V K : Type} [DecidableEq V] [Finite K] (C : Finset V → K)

/-- One round of thinning at level `k + 1`: pick a point `a`, and using the level-`k` induction
hypothesis on the colouring `s ↦ C (insert a s)`, find an infinite remainder on which every
`k`-subset, together with `a`, has the same colour. -/
theorem exists_step_k (IH : ExistsInfiniteMonochromaticKUniform k) (X : Set V) (hX : X.Infinite) :
    ∃ (a : V) (col : K) (X' : Set V), a ∈ X ∧ X' ⊆ X \ {a} ∧ X'.Infinite ∧
      ∀ s : Finset V, (s : Set V) ⊆ X' → s.card = k → C (insert a s) = col :=
  let ⟨a, ha⟩ := hX.nonempty
  let ⟨col, Y, hYsub, hYinf, hYmono⟩ :=
    IH (fun s => C (insert a s)) (hX.sdiff (Set.finite_singleton a))
  ⟨a, col, Y, ha, hYsub, hYinf, hYmono⟩

/-- The point chosen by one round of `exists_step_k`. -/
noncomputable def chosenPointK (IH : ExistsInfiniteMonochromaticKUniform k)
    (X : {S : Set V // S.Infinite}) : V :=
  (exists_step_k C IH X.1 X.2).choose

/-- The colour chosen by one round of `exists_step_k`. -/
noncomputable def chosenColorK (IH : ExistsInfiniteMonochromaticKUniform k)
    (X : {S : Set V // S.Infinite}) : K :=
  (exists_step_k C IH X.1 X.2).choose_spec.choose

/-- The infinite remainder chosen by one round of `exists_step_k`. -/
noncomputable def nextInfiniteSetK (IH : ExistsInfiniteMonochromaticKUniform k)
    (X : {S : Set V // S.Infinite}) : {S : Set V // S.Infinite} :=
  ⟨(exists_step_k C IH X.1 X.2).choose_spec.choose_spec.choose,
    (exists_step_k C IH X.1 X.2).choose_spec.choose_spec.choose_spec.2.2.1⟩

theorem chosenPointK_mem (IH : ExistsInfiniteMonochromaticKUniform k)
    (X : {S : Set V // S.Infinite}) : chosenPointK C IH X ∈ X.1 :=
  (exists_step_k C IH X.1 X.2).choose_spec.choose_spec.choose_spec.1

theorem nextInfiniteSetK_subset (IH : ExistsInfiniteMonochromaticKUniform k)
    (X : {S : Set V // S.Infinite}) :
    (nextInfiniteSetK C IH X : Set V) ⊆ X.1 \ {chosenPointK C IH X} :=
  (exists_step_k C IH X.1 X.2).choose_spec.choose_spec.choose_spec.2.1

theorem mono_of_mem_nextInfiniteSetK (IH : ExistsInfiniteMonochromaticKUniform k)
    (X : {S : Set V // S.Infinite}) {s : Finset V}
    (hs : (s : Set V) ⊆ (nextInfiniteSetK C IH X : Set V)) (hcard : s.card = k) :
    C (insert (chosenPointK C IH X) s) = chosenColorK C IH X :=
  (exists_step_k C IH X.1 X.2).choose_spec.choose_spec.choose_spec.2.2.2 s hs hcard

variable {X0 : Set V} (hX0 : X0.Infinite) (IH : ExistsInfiniteMonochromaticKUniform k)

/-- The decreasing chain of infinite sets built by repeated thinning, starting from `X0`. -/
noncomputable def XseqK (n : ℕ) : {S : Set V // S.Infinite} :=
  match n with
  | 0 => ⟨X0, hX0⟩
  | n + 1 => nextInfiniteSetK C IH (XseqK n)

/-- The point chosen at round `n`. -/
noncomputable def aSeqK (n : ℕ) : V := chosenPointK C IH (XseqK C hX0 IH n)

/-- The colour of every `insert (aSeqK n) s` for `s` a `k`-subset of `XseqK (n + 1)`. -/
noncomputable def cSeqK (n : ℕ) : K := chosenColorK C IH (XseqK C hX0 IH n)

theorem XseqK_succ_subset (n : ℕ) :
    (XseqK C hX0 IH (n + 1) : Set V) ⊆ (XseqK C hX0 IH n : Set V) \ {aSeqK C hX0 IH n} :=
  nextInfiniteSetK_subset C IH (XseqK C hX0 IH n)

theorem aSeqK_mem (n : ℕ) : aSeqK C hX0 IH n ∈ (XseqK C hX0 IH n : Set V) :=
  chosenPointK_mem C IH (XseqK C hX0 IH n)

theorem mono_aSeqK_of_mem_XseqK_succ (n : ℕ) {s : Finset V}
    (hs : (s : Set V) ⊆ (XseqK C hX0 IH (n + 1) : Set V)) (hcard : s.card = k) :
    C (insert (aSeqK C hX0 IH n) s) = cSeqK C hX0 IH n :=
  mono_of_mem_nextInfiniteSetK C IH (XseqK C hX0 IH n) hs hcard

/-- The chain is decreasing. -/
theorem XseqK_antitone {m n : ℕ} (h : m ≤ n) :
    (XseqK C hX0 IH n : Set V) ⊆ (XseqK C hX0 IH m : Set V) := by
  induction n, h using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n hn ih => exact (XseqK_succ_subset C hX0 IH n).trans (Set.sdiff_subset.trans ih)

theorem aSeqK_mem_of_lt {m n : ℕ} (h : m < n) :
    aSeqK C hX0 IH n ∈ (XseqK C hX0 IH (m + 1) : Set V) :=
  XseqK_antitone C hX0 IH h (aSeqK_mem C hX0 IH n)

theorem aSeqK_ne_of_lt {m n : ℕ} (h : m < n) : aSeqK C hX0 IH n ≠ aSeqK C hX0 IH m :=
  (XseqK_succ_subset C hX0 IH m (aSeqK_mem_of_lt C hX0 IH h)).2

/-- `aSeqK` is injective: each round removes the point just chosen from every later remainder. -/
theorem aSeqK_injective : Function.Injective (aSeqK C hX0 IH) :=
  .of_lt_imp_ne fun _ _ h => (aSeqK_ne_of_lt C hX0 IH h).symm

theorem aSeqK_mem_X0 (n : ℕ) : aSeqK C hX0 IH n ∈ X0 :=
  XseqK_antitone C hX0 IH (Nat.zero_le n) (aSeqK_mem C hX0 IH n)

end Step

/-- The inductive step. Given the `k`-uniform statement, the `(k + 1)`-uniform statement holds: a
second pigeonhole pass on `cSeqK` (exactly as in the pairs case) fixes a colour `col`, and any
`(k + 1)`-subset `s` of `H := aSeqK '' (cSeqK ⁻¹' {col})` is monochromatic because its
minimum-index element `aSeqK n0` splits it as `insert (aSeqK n0) (s.erase (aSeqK n0))`, with the
remainder a `k`-subset of `XseqK (n0 + 1)`, so `mono_aSeqK_of_mem_XseqK_succ` applies directly. -/
theorem existsInfiniteMonochromaticKUniform_succ {k : ℕ}
    (IH : ExistsInfiniteMonochromaticKUniform k) : ExistsInfiniteMonochromaticKUniform (k + 1) := by
  intro V K _ C X0 hX0
  classical
  obtain ⟨col, hcol⟩ := Finite.exists_infinite_fiber (cSeqK C hX0 IH)
  rw [Set.infinite_coe_iff] at hcol
  refine ⟨col, aSeqK C hX0 IH '' (cSeqK C hX0 IH ⁻¹' {col}), ?_, ?_, ?_⟩
  · rintro x ⟨n, -, rfl⟩
    exact aSeqK_mem_X0 C hX0 IH n
  · exact hcol.image (aSeqK_injective C hX0 IH).injOn
  · intro s hs hcard
    obtain ⟨t, ht, rfl⟩ := Finset.subset_set_image_iff.mp hs
    have hinj := aSeqK_injective C hX0 IH
    rw [Finset.card_image_of_injective _ hinj] at hcard
    have htne : t.Nonempty := Finset.card_pos.mp (by omega)
    have hn0 := t.min'_mem htne
    -- split off the least index `n0`; the rest lies in `XseqK (n0 + 1)`
    have hmono := mono_aSeqK_of_mem_XseqK_succ C hX0 IH (t.min' htne)
      (s := (t.erase (t.min' htne)).image (aSeqK C hX0 IH)) (fun y hy => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
        exact aSeqK_mem_of_lt C hX0 IH (lt_of_le_of_ne (t.min'_le m (Finset.mem_of_mem_erase hm))
          (Finset.ne_of_mem_erase hm).symm))
      (by rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem hn0]; omega)
    rw [← Finset.image_insert, Finset.insert_erase hn0] at hmono
    exact hmono.trans (ht hn0)



/-- The `k`-uniform infinite Ramsey theorem, for every `k`. Combines the base case (`k = 0`)
and the inductive step (`existsInfiniteMonochromaticKUniform_succ`) by ordinary induction on `k`.
For `k = 2` this specializes (after currying pairs as edges) to `exists_infinite_monochromatic`. -/
theorem existsInfiniteMonochromaticKUniform (k : ℕ) : ExistsInfiniteMonochromaticKUniform k := by
  induction k with
  | zero => exact existsInfiniteMonochromaticKUniform_zero
  | succ k ih => exact existsInfiniteMonochromaticKUniform_succ ih

/-- Worked example: colouring the 2-element subsets of `ℕ` by the parity of their least element,
some colour is attained on every pair drawn from a fixed infinite set of naturals. An instance of
`existsInfiniteMonochromaticKUniform` at `k = 2`. -/
theorem existsInfiniteMonochromaticKUniform_min_parity_example :
    ∃ (col : Bool) (H : Set ℕ), H.Infinite ∧
      ∀ s : Finset ℕ, (s : Set ℕ) ⊆ H → s.card = 2 →
        (if h : s.Nonempty then decide (s.min' h % 2 = 0) else false) = col :=
  let ⟨col, H, _, hH, hmono⟩ := existsInfiniteMonochromaticKUniform 2
    (fun s : Finset ℕ => if h : s.Nonempty then decide (s.min' h % 2 = 0) else false)
    Set.infinite_univ
  ⟨col, H, hH, hmono⟩

end SimpleGraph
