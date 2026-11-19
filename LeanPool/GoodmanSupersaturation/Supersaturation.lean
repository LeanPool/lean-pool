/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

public import LeanPool.GoodmanSupersaturation.Goodman
public import Mathlib.Tactic.Rify

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Supersaturation for cliques in two-colourings

Ramsey's theorem says that every red/blue colouring of a large complete graph has a monochromatic
`K_t`. *Supersaturation* says that it has many: a positive proportion of all `t`-sets.

Two forms are proved, for a graph `G` (red) and its complement `Gᶜ` (blue).

* **Averaging.** If every `m`-set of vertices contains a member of a family `𝓕` of `t`-sets, then
  `C(n, t) ≤ #𝓕 · C(m, t)`. With `𝓕` the monochromatic `t`-cliques and `m` a Ramsey bound for
  `K_t`, there are at least `C(n, t) / C(m, t)` monochromatic `t`-cliques.
* **The Erdős–Szekeres recursion, counted.** Running the Erdős–Szekeres neighbourhood recursion
  while keeping track of counts rather than single cliques: inside any set `S` with
  `x = |S| + 1 - 2 ^ (k + l - 3) > 0`, either `G` has at least `2 ^ (-E(k, l)) x ^ k / k!`
  `k`-cliques or `Gᶜ` has at least `2 ^ (-E(l, k)) x ^ l / l!` `l`-cliques, where
  `E(k, l) = k (l - 2) + C(k + 1, 2) - 1`.

## Main definitions

* `SimpleGraph.supersaturationBound k l x`: `x ^ k 2 ^ (2k + 1) / (k! 2 ^ (kl + C(k + 1, 2)))`.

## Main statements

* `Finset.choose_le_card_mul_choose`: the averaging lemma for set families.
* `SimpleGraph.choose_le_card_cliqueFinset_add_mul_choose`: monochromatic cliques by averaging.
* `SimpleGraph.sum_cliqueCountIn_neighbors_eq`: the rooted double count, `∑ v ∈ S` of the
  `(j - 1)`-cliques in the neighbourhood of `v` is `j` times the `j`-cliques of `S`.
* `SimpleGraph.supersaturation`: the counted Erdős–Szekeres recursion.
* `SimpleGraph.supersaturation_diag`: its diagonal form, counting both colours together.

## Implementation notes

The recursion picks a vertex set of size at least `|S| / 2` all of whose members have blue (or
red) degree at least `(|S| - 1) / 2` in `S`, applies the induction hypothesis inside each blue
neighbourhood, and double counts: each `(l + 1)`-clique arises from exactly `l + 1` rooted
`l`-cliques (`sum_cliqueCountIn_neighbors_eq`).

## References

* [P. Erdős, G. Szekeres, *A combinatorial problem in geometry*][ErdosSzekeres1935]
-/

@[expose] public section

open Finset

/-! ### Averaging -/

/-- **Averaging over `m`-sets.** If every `m`-subset of `s` contains a member of a family `𝓕` of
`t`-subsets of `s`, then `C(|s|, t) ≤ |𝓕| · C(m, t)`. -/
theorem Finset.choose_le_card_mul_choose {α : Type*} {s : Finset α}
    {𝓕 : Finset (Finset α)} {t m : ℕ} (h𝓕 : 𝓕 ⊆ s.powersetCard t) (htm : t ≤ m) (hms : m ≤ #s)
    (hcover : ∀ M ∈ s.powersetCard m, ∃ F ∈ 𝓕, F ⊆ M) :
    (#s).choose t ≤ #𝓕 * m.choose t := by
  classical
  -- every `m`-set lies above some member; each member lies below `C(n - t, m - t)` `m`-sets
  have hdc := card_mul_le_card_mul (fun M F => F ⊆ M) (s := s.powersetCard m) (t := 𝓕)
    (m := 1) (n := (#s - t).choose (m - t))
    (fun M hM => by
      obtain ⟨F, hF, hFM⟩ := hcover M hM
      exact card_pos.mpr ⟨F, mem_filter.mpr ⟨hF, hFM⟩⟩)
    (fun F hF => by
      have hFs := mem_powersetCard.mp (h𝓕 hF)
      calc #(bipartiteBelow (fun M F => F ⊆ M) (s.powersetCard m) F)
          ≤ #((s \ F).powersetCard (m - t)) := by
            refine card_le_card_of_injOn (fun M => M \ F) (fun M hM => ?_) ?_
            · rw [mem_coe, mem_bipartiteBelow, mem_powersetCard] at hM
              rw [mem_coe, mem_powersetCard, card_sdiff_of_subset hM.2, hM.1.2, hFs.2]
              exact ⟨sdiff_subset_sdiff hM.1.1 (Subset.refl F), rfl⟩
            · intro M hM M' hM' hMM'
              rw [mem_coe, mem_bipartiteBelow] at hM hM'
              rw [← sdiff_union_of_subset hM.2, ← sdiff_union_of_subset hM'.2]
              exact congrArg (· ∪ F) hMM'
        _ = (#s - t).choose (m - t) := by rw [card_powersetCard, card_sdiff_of_subset hFs.1, hFs.2])
  rw [card_powersetCard, mul_one] at hdc
  have hpos : 0 < (#s - t).choose (m - t) := Nat.choose_pos (by omega)
  have key : (#s).choose t * (#s - t).choose (m - t) ≤
      #𝓕 * m.choose t * (#s - t).choose (m - t) := by
    rw [← Nat.choose_mul htm]
    calc (#s).choose m * m.choose t ≤ #𝓕 * (#s - t).choose (m - t) * m.choose t :=
          Nat.mul_le_mul_right _ hdc
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right key hpos

namespace SimpleGraph

variable {V : Type*}

/-- **Supersaturation by averaging.** If every `m`-set of vertices of `G` contains a `t`-clique of
`G` or of `Gᶜ`, then `G` and `Gᶜ` have at least `C(n, t) / C(m, t)` `t`-cliques together. -/
theorem choose_le_card_cliqueFinset_add_mul_choose [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t m : ℕ} (htm : t ≤ m) (hm : m ≤ Fintype.card V)
    (h : ∀ M : Finset V, #M = m →
      (∃ K ⊆ M, G.IsNClique t K) ∨ ∃ K ⊆ M, Gᶜ.IsNClique t K) :
    (Fintype.card V).choose t ≤ (#(G.cliqueFinset t) + #(Gᶜ.cliqueFinset t)) * m.choose t := by
  have hsub : G.cliqueFinset t ∪ Gᶜ.cliqueFinset t ⊆ (univ : Finset V).powersetCard t := by
    intro K hK
    rw [mem_powersetCard]
    rcases mem_union.mp hK with hK | hK <;>
      exact ⟨subset_univ _, (mem_cliqueFinset_iff.mp hK).card_eq⟩
  have := Finset.choose_le_card_mul_choose hsub htm (by simpa using hm) fun M hM => by
    rcases h M (mem_powersetCard.mp hM).2 with ⟨K, hKM, hK⟩ | ⟨K, hKM, hK⟩
    · exact ⟨K, mem_union_left _ (mem_cliqueFinset_iff.mpr hK), hKM⟩
    · exact ⟨K, mem_union_right _ (mem_cliqueFinset_iff.mpr hK), hKM⟩
  rw [card_univ] at this
  exact this.trans (Nat.mul_le_mul_right _ (card_union_le _ _))

/-! ### The counted Erdős–Szekeres recursion -/

section Recursion

variable [DecidableEq V]

/-- The supersaturation bound `x ^ k 2 ^ (2k + 1) / (k! 2 ^ (kl + C(k + 1, 2)))`, that is
`2 ^ (-E(k, l)) x ^ k / k!` with `E(k, l) = k (l - 2) + C(k + 1, 2) - 1`. -/
noncomputable def supersaturationBound (k l : ℕ) (x : ℝ) : ℝ :=
  x ^ k * 2 ^ (2 * k + 1) / ((k.factorial : ℝ) * 2 ^ (k * l + (k + 1).choose 2))

private theorem bound_mono (k l : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    supersaturationBound k l x ≤ supersaturationBound k l y := by
  unfold supersaturationBound
  gcongr

private theorem bound_nonneg (k l : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ supersaturationBound k l x := by
  unfold supersaturationBound
  positivity

private theorem bound_succ (k l : ℕ) (x : ℝ) :
    supersaturationBound k (l + 1) x = supersaturationBound k l (x / 2) := by
  unfold supersaturationBound
  rw [show k * (l + 1) = k * l + k by ring, div_pow, pow_add, pow_add]
  field_simp
  ring

private theorem bound_one_le (j : ℕ) (hj : 2 ≤ j) {x : ℝ} (hx : 0 ≤ x) :
    supersaturationBound 1 j x ≤ x := by
  unfold supersaturationBound
  rw [show ((1 : ℕ) + 1).choose 2 = 1 from rfl, Nat.factorial_one, Nat.cast_one, one_mul, pow_one,
    show 2 * 1 + 1 = 3 from rfl, one_mul]
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ 3 ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

private theorem bound_step (a c : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    supersaturationBound (a + 1) (c + 2) x ≤
      x / (2 * ((a : ℝ) + 1)) * supersaturationBound a (c + 2) (x / 2) := by
  have hf : (((a + 1).factorial : ℕ) : ℝ) = ((a : ℝ) + 1) * (a.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hch : (a + 1 + 1).choose 2 = (a + 1).choose 2 + (a + 1) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have key : x / (2 * ((a : ℝ) + 1)) * supersaturationBound a (c + 2) (x / 2) =
      supersaturationBound (a + 1) (c + 2) x * 2 ^ c := by
    unfold supersaturationBound
    rw [hf, hch, show (a + 1) * (c + 2) = a * (c + 2) + (c + 2) by ring, div_pow,
      pow_add, pow_add, pow_add, pow_succ, pow_succ]
    field_simp
    ring
  rw [key]
  have : (1 : ℝ) ≤ 2 ^ c := one_le_pow₀ (by norm_num)
  have := bound_nonneg (a + 1) (c + 2) hx
  nlinarith

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- More cliques inside a larger set. -/
theorem cliqueCountIn_mono {S S' : Finset V} (h : S ⊆ S') (k : ℕ) :
    G.cliqueCountIn S k ≤ G.cliqueCountIn S' k :=
  card_le_card fun T hT => by
    simp only [mem_filter, mem_powersetCard] at hT ⊢
    exact ⟨⟨hT.1.1.trans h, hT.1.2⟩, hT.2⟩

/-- The `1`-cliques inside `S` are its vertices. -/
@[simp] theorem cliqueCountIn_one (S : Finset V) : G.cliqueCountIn S 1 = #S := by
  rw [cliqueCountIn, filter_true_of_mem fun T hT => ?_, card_powersetCard, Nat.choose_one_right]
  obtain ⟨a, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hT).2
  simp

/-- The neighbours of `v` inside `S`. -/
private abbrev nbhd (S : Finset V) (v : V) : Finset V := {w ∈ S | G.Adj v w}

/-- **Rooted double count.** For `1 ≤ j`, summing over `v ∈ S` the number of `(j - 1)`-cliques in
the neighbourhood of `v` in `S` counts each `j`-clique of `S` once per vertex: the sum is
`j` times the number of `j`-cliques in `S`. (At `j = 0` the identity fails under natural
subtraction.) -/
theorem sum_cliqueCountIn_neighbors_eq (S : Finset V) {j : ℕ} (hj : 1 ≤ j) :
    ∑ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1) = j * G.cliqueCountIn S j := by
  set C : Finset (Finset V) := (S.powersetCard j).filter fun T : Finset V => G.IsClique (T : Set V)
    with hC
  have hterm : ∀ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1) =
      ∑ T ∈ C, if v ∈ T then 1 else 0 := by
    intro v hv
    rw [← card_filter, cliqueCountIn]
    refine card_bij (fun U _ => insert v U) (fun U hU => ?_) (fun U hU U' hU' h => ?_)
      fun T hT => ?_
    · rw [mem_filter, mem_powersetCard] at hU
      obtain ⟨⟨hUsub, hUcard⟩, hUcl⟩ := hU
      have hvU : v ∉ U := fun h => G.irrefl (mem_filter.mp (hUsub h)).2
      rw [mem_filter, hC, mem_filter, mem_powersetCard]
      refine ⟨⟨⟨insert_subset hv fun x hx => (mem_filter.mp (hUsub hx)).1, ?_⟩, ?_⟩,
        mem_insert_self _ _⟩
      · rw [card_insert_of_notMem hvU, hUcard]; omega
      · rw [coe_insert]
        exact hUcl.insert fun b hb _ => (mem_filter.mp (hUsub hb)).2
    · have hv1 : v ∉ U := fun h' => G.irrefl
        (mem_filter.mp ((mem_powersetCard.mp (mem_filter.mp hU).1).1 h')).2
      have hv2 : v ∉ U' := fun h' => G.irrefl
        (mem_filter.mp ((mem_powersetCard.mp (mem_filter.mp hU').1).1 h')).2
      have h2 := congrArg (fun A => A.erase v) h
      simpa [erase_insert hv1, erase_insert hv2] using h2
    · rw [mem_filter, hC, mem_filter, mem_powersetCard] at hT
      obtain ⟨⟨⟨hTS, hTcard⟩, hTcl⟩, hvT⟩ := hT
      refine ⟨T.erase v, ?_, insert_erase hvT⟩
      rw [mem_filter, mem_powersetCard, card_erase_of_mem hvT, hTcard]
      refine ⟨⟨fun x hx => ?_, rfl⟩, hTcl.subset (by simp)⟩
      obtain ⟨hxv, hxT⟩ := mem_erase.mp hx
      exact mem_filter.mpr ⟨hTS hxT, hTcl hvT hxT (Ne.symm hxv)⟩
  calc ∑ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1)
      = ∑ v ∈ S, ∑ T ∈ C, if v ∈ T then 1 else 0 := sum_congr rfl hterm
    _ = ∑ T ∈ C, ∑ v ∈ S, if v ∈ T then 1 else 0 := sum_comm
    _ = ∑ _T ∈ C, j := by
        refine sum_congr rfl fun T hT => ?_
        have hT' := mem_powersetCard.mp (mem_filter.mp hT).1
        rw [← card_filter, filter_mem_eq_inter, inter_eq_right.mpr hT'.1, hT'.2]
    _ = j * G.cliqueCountIn S j := by rw [sum_const, smul_eq_mul, mul_comm, hC]; rfl

/-- **Rooted double count**, inequality form of `sum_cliqueCountIn_neighbors_eq`. -/
theorem sum_cliqueCountIn_neighbors_le (S : Finset V) {j : ℕ} (hj : 1 ≤ j) :
    ∑ v ∈ S, G.cliqueCountIn {w ∈ S | G.Adj v w} (j - 1) ≤ j * G.cliqueCountIn S j :=
  (sum_cliqueCountIn_neighbors_eq G S hj).le

/-- At least half of `S` has blue degree at least `(|S| - 1) / 2`, or at least half has red degree
at least `(|S| - 1) / 2`. -/
private theorem exists_half (S : Finset V) :
    (#S : ℝ) / 2 ≤ (#{v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)} : ℝ) ∨
      (#S : ℝ) / 2 ≤ (#{v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd G S v)} : ℝ) := by
  set A := {v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)}
  set B := {v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd G S v)}
  have hsub : S ⊆ A ∪ B := fun v hv => by
    have hd : (#(nbhd G S v) : ℝ) + #(nbhd Gᶜ S v) + 1 = #S := by
      exact_mod_cast degreeWithin_add_degreeWithin_compl G hv
    rw [mem_union]
    by_cases hb : ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)
    · exact .inl (mem_filter.mpr ⟨hv, hb⟩)
    · exact .inr (mem_filter.mpr ⟨hv, by linarith⟩)
  have : (#S : ℝ) ≤ #A + #B := by exact_mod_cast (card_le_card hsub).trans (card_union_le A B)
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  linarith [hcon.1, hcon.2]

/-- The statement proved by induction on `k + l`. -/
private def Claim (V : Type*) [DecidableEq V] (k l : ℕ) : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V), 0 < (#S : ℝ) + 1 - 2 ^ (k + l - 3) →
    supersaturationBound k l ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ G.cliqueCountIn S k ∨
      supersaturationBound l k ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ Gᶜ.cliqueCountIn S l

omit G in
private theorem claim_symm {k l : ℕ} (h : Claim V k l) : Claim V l k := by
  intro G _ S hx
  have hx' : 0 < (#S : ℝ) + 1 - 2 ^ (k + l - 3) := by rwa [Nat.add_comm] at hx
  rw [show l + k - 3 = k + l - 3 by omega]
  rcases h Gᶜ S hx' with h1 | h1
  · exact .inr h1
  · left
    convert h1 using 2
    simp only [cliqueCountIn, compl_compl]

omit G in
private theorem claim_one_left {l : ℕ} (hl : 2 ≤ l) : Claim V 1 l := by
  intro G _ S hx
  left
  rw [cliqueCountIn_one]
  have h1 : (1 : ℝ) ≤ 2 ^ (1 + l - 3) := one_le_pow₀ (by norm_num)
  have := bound_one_le l hl hx.le
  linarith

omit G in
private theorem claim_one_right {k : ℕ} (hk : 2 ≤ k) : Claim V k 1 :=
  claim_symm (claim_one_left hk)

omit G in
private theorem step {c l : ℕ} (IH : Claim V (c + 2) l) (hl : 1 ≤ l)
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hx : 0 < (#S : ℝ) + 1 - 2 ^ (c + 2 + (l + 1) - 3))
    (hgood : (#S : ℝ) / 2 ≤ (#{v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)} : ℝ)) :
    supersaturationBound (c + 2) (l + 1) ((#S : ℝ) + 1 - 2 ^ (c + 2 + (l + 1) - 3)) ≤
        G.cliqueCountIn S (c + 2) ∨
      supersaturationBound (l + 1) (c + 2) ((#S : ℝ) + 1 - 2 ^ (c + 2 + (l + 1) - 3)) ≤
        Gᶜ.cliqueCountIn S (l + 1) := by
  set x : ℝ := (#S : ℝ) + 1 - 2 ^ (c + 2 + (l + 1) - 3) with hxdef
  set good := {v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)} with hgooddef
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hpow : (2 : ℝ) ^ (c + 2 + (l + 1) - 3) = 2 * 2 ^ (c + 2 + l - 3) := by
    rw [show c + 2 + (l + 1) - 3 = (c + 2 + l - 3) + 1 by omega, pow_succ]; ring
  have hx2 : 0 < x / 2 := by linarith
  have hv : ∀ v ∈ good,
      supersaturationBound l (c + 2) (x / 2) ≤ Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l := by
    intro v hvg
    have hdeg := (mem_filter.mp hvg).2
    set W := nbhd Gᶜ S v
    have hxW : x / 2 ≤ (#W : ℝ) + 1 - 2 ^ (c + 2 + l - 3) := by rw [hxdef, hpow]; linarith
    rcases IH G W (by linarith) with h | h
    · exfalso
      have : supersaturationBound (c + 2) (l + 1) x ≤ G.cliqueCountIn S (c + 2) := by
        calc supersaturationBound (c + 2) (l + 1) x
            = supersaturationBound (c + 2) l (x / 2) := bound_succ _ _ _
          _ ≤ supersaturationBound (c + 2) l ((#W : ℝ) + 1 - 2 ^ (c + 2 + l - 3)) :=
              bound_mono _ _ hx2.le hxW
          _ ≤ G.cliqueCountIn W (c + 2) := h
          _ ≤ G.cliqueCountIn S (c + 2) := by
              exact_mod_cast cliqueCountIn_mono G (filter_subset _ _) (c + 2)
      linarith
    · exact (bound_mono _ _ hx2.le hxW).trans h
  set B := supersaturationBound l (c + 2) (x / 2)
  have hB0 : 0 ≤ B := bound_nonneg _ _ hx2.le
  have hsum : (#good : ℝ) * B ≤ ∑ v ∈ good, (Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l : ℝ) := by
    simpa [nsmul_eq_mul] using card_nsmul_le_sum good _ B hv
  have hsub : ∑ v ∈ good, (Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l : ℝ) ≤
      ∑ v ∈ S, (Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
  have hdc : ∑ v ∈ S, (Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l : ℝ) ≤
      ((l : ℝ) + 1) * Gᶜ.cliqueCountIn S (l + 1) := by
    have := sum_cliqueCountIn_neighbors_le Gᶜ S (j := l + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hxm : x ≤ #S := by
    have : (1 : ℝ) ≤ 2 ^ (c + 2 + (l + 1) - 3) := one_le_pow₀ (by norm_num)
    rw [hxdef]; linarith
  have hstep := bound_step (a := l) (c := c) hx.le
  have hcc : x / 2 * B ≤ ((l : ℝ) + 1) * Gᶜ.cliqueCountIn S (l + 1) := by
    have e1 : x / 2 * B ≤ (#S : ℝ) / 2 * B := mul_le_mul_of_nonneg_right (by linarith) hB0
    have e2 : (#S : ℝ) / 2 * B ≤ (#good : ℝ) * B := mul_le_mul_of_nonneg_right hgood hB0
    linarith
  have hfin : supersaturationBound (l + 1) (c + 2) x ≤ Gᶜ.cliqueCountIn S (l + 1) := by
    refine hstep.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

omit G in
private theorem claim_all :
    ∀ n k l : ℕ, 1 ≤ k → 1 ≤ l → 3 ≤ k + l → k + l = n → Claim V k l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k l hk hl h3 hn
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · obtain rfl : k = 1 := by omega
      exact claim_one_left (by omega)
    rcases Nat.lt_or_ge l 2 with hl1 | hl2
    · obtain rfl : l = 1 := by omega
      exact claim_one_right hk2
    obtain ⟨c, rfl⟩ : ∃ c, k = c + 2 := ⟨k - 2, by omega⟩
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have IH1 : Claim V (c + 2) l' := ih _ (by omega) _ _ (by omega) (by omega) (by omega) rfl
    have IH2 : Claim V (c + 1) (l' + 1) := ih _ (by omega) _ _ (by omega) (by omega) (by omega) rfl
    intro G _ S hx
    rcases exists_half G S with hbl | hrd
    · exact step IH1 (by omega) G S hx hbl
    · obtain ⟨c', rfl⟩ : ∃ c', l' = c' + 1 := ⟨l' - 1, by omega⟩
      have e : c' + 2 + (c + 1 + 1) - 3 = c + 2 + (c' + 1 + 1) - 3 := by omega
      have hrd' : (#S : ℝ) / 2 ≤ (#{v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜᶜ S v)} : ℝ) := by
        simpa only [compl_compl] using hrd
      have := step (G := Gᶜ) (claim_symm IH2) (by omega) S (by rw [e]; exact hx) hrd'
      rw [e] at this
      rcases this with h | h
      · exact .inr h
      · left
        convert h using 2
        simp only [cliqueCountIn, compl_compl]

/-- **Supersaturation via the Erdős–Szekeres recursion.** Let `k, l ≥ 1` with `k + l ≥ 3`, and let
`S` be a finite vertex set with `x = |S| + 1 - 2 ^ (k + l - 3) > 0`. Then `G` has at least
`2 ^ (-E(k, l)) x ^ k / k!` `k`-cliques inside `S`, or `Gᶜ` has at least
`2 ^ (-E(l, k)) x ^ l / l!` `l`-cliques inside `S`, where `E(k, l) = k (l - 2) + C(k + 1, 2) - 1`
(see `supersaturationBound`). -/
theorem supersaturation {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (h3 : 3 ≤ k + l) (S : Finset V)
    (hx : 0 < (#S : ℝ) + 1 - 2 ^ (k + l - 3)) :
    supersaturationBound k l ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ G.cliqueCountIn S k ∨
      supersaturationBound l k ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ Gᶜ.cliqueCountIn S l :=
  claim_all (k + l) k l hk hl h3 rfl G S hx

/-- **Diagonal supersaturation.** For `t ≥ 2`, `G` and `Gᶜ` together have at least
`2 ^ (-E(t, t)) x ^ t / t!` `t`-cliques inside `S`, where `x = |S| + 1 - 2 ^ (2t - 3) > 0`. -/
theorem supersaturation_diag {t : ℕ} (ht : 2 ≤ t) (S : Finset V)
    (hx : 0 < (#S : ℝ) + 1 - 2 ^ (t + t - 3)) :
    supersaturationBound t t ((#S : ℝ) + 1 - 2 ^ (t + t - 3)) ≤
      G.cliqueCountIn S t + Gᶜ.cliqueCountIn S t := by
  rcases supersaturation G (by omega) (by omega) (by omega) S hx with h | h
  · have := Nat.cast_nonneg (α := ℝ) (Gᶜ.cliqueCountIn S t); linarith
  · have := Nat.cast_nonneg (α := ℝ) (G.cliqueCountIn S t); linarith

end Recursion

end SimpleGraph
