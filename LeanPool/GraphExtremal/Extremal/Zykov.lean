/-
Copyright (c) 2026 Brian Sanders. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Sanders
-/
module

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
import LeanPool.GraphExtremal.Extremal.WeightShifting
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Zykov's theorem

A graph on `n` vertices with no `(r + 1)`-clique has at most `r.choose s * (n / r) ^ s` cliques of
size `s` (Zykov). For `s = 2` this is Turán's edge bound, and the Turán graph `T(n, r)` attains it
when `r ∣ n` (`SimpleGraph.card_cliqueFinset_turanGraph` in `LexProd.lean`). We prove the weighted
form: for nonnegative vertex weights `p`, the sum over `s`-cliques `S` of `∏ v ∈ S, p v` is at most
`r.choose s * ((∑ p) / r) ^ s`.

## Main definitions

* `SimpleGraph.cliqueWeight G s p`: the sum over `s`-cliques `S` of `∏ v ∈ S, p v`.

## Main statements

* `Finset.sum_powersetCard_prod_le`: Maclaurin's inequality in the form
  `e_s(x) ≤ (#T).choose s * ((∑ i ∈ T, x i) / #T) ^ s` for `x ≥ 0` on `T`, where
  `e_s(x) = ∑ S ∈ T.powersetCard s, ∏ i ∈ S, x i`.
* `SimpleGraph.cliqueWeight_le_choose_mul`: if `G` has no `(r + 1)`-clique and `p ≥ 0`, then
  `G.cliqueWeight s p ≤ r.choose s * ((∑ i, p i) / r) ^ s`.
* `SimpleGraph.card_cliqueFinset_le_choose_mul_div_pow`: **Zykov's theorem**. If `G` has no
  `(r + 1)`-clique, it has at most `r.choose s * (Fintype.card V / r) ^ s` cliques of size `s`.

## Implementation notes

No clique contains two non-adjacent vertices, so `SimpleGraph.cliqueWeight` is affine along every
direction `Pi.single u 1 - Pi.single v 1` with `u, v` non-adjacent
(`SimpleGraph.cliqueWeight_add_smul`). The weight-shifting lemma
`SimpleGraph.exists_isClique_support_le_of_affine` then reduces the bound to weightings supported
on a clique `T` with `#T ≤ r`, where the clique weight is the elementary symmetric polynomial
`e_s` of the weights on `T`. Maclaurin's inequality bounds it, and
`(m.choose s) / m ^ s` increases with `m`.

Maclaurin's inequality is proved by induction on `T`, using
`e_(s+1)(T ∪ {a}) = e_(s+1)(T) + x a * e_s(T)` and Bernoulli's inequality at each step. Mathlib does
not yet have Maclaurin's inequality; this form needs no Newton inequalities.

## References

* [A. A. Zykov, *On some properties of linear complexes*][Zykov1949]
* [T. S. Motzkin, E. G. Straus,
  *Maxima for graphs and a new proof of a theorem of Turán*][MotzkinStraus1965]
* [G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*][HardyLittlewoodPolya1952]
-/

@[expose] public section

open Finset

/-! ### Maclaurin's inequality -/

/-- Bernoulli's inequality as a tangent-line bound: `μ ^ (k + 1)` lies above its tangent at `μ`. -/
private theorem pow_add_mul_sub_le_pow {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (k : ℕ) :
    μ ^ (k + 1) + (k + 1) * μ ^ k * (ν - μ) ≤ ν ^ (k + 1) := by
  have h := pow_add_mul_le_add_pow_of_sq_nonneg hμ (sq_nonneg (ν - μ)) (sq_nonneg (μ + (ν - μ)))
    (by linarith) (k + 1)
  simpa using h

/-- One induction step of Maclaurin's inequality: adjoining a weight `b` to `n` weights with
sum `A`. -/
private theorem choose_mul_pow_step (n s : ℕ) {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) :
    n.choose (s + 1) * (A / n) ^ (s + 1) + b * (n.choose s * (A / n) ^ s) ≤
      (n + 1).choose (s + 1) * ((A + b) / (n + 1 : ℕ)) ^ (s + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · cases s with
    | zero => simpa using hA
    | succ s =>
      rw [Nat.choose_eq_zero_of_lt (by omega : 0 + 1 < s + 1 + 1)]
      simp
  set μ := A / n with hμdef
  set ν := (A + b) / (n + 1 : ℕ) with hνdef
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ : 0 ≤ μ := by positivity
  have hν : 0 ≤ ν := by positivity
  have hnμ : (n : ℝ) * μ = A := by rw [hμdef]; field_simp
  have hnν : ((n : ℝ) + 1) * ν = A + b := by rw [hνdef]; push_cast; field_simp
  have hc : ((n + 1).choose (s + 1) : ℝ) = n.choose s + n.choose (s + 1) := by
    exact_mod_cast Nat.choose_succ_succ' n s
  have hc' : ((n + 1).choose (s + 1) : ℝ) * (s + 1) = (n + 1) * n.choose s := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n s).symm
  calc (n.choose (s + 1) : ℝ) * μ ^ (s + 1) + b * (n.choose s * μ ^ s)
      = (n + 1).choose (s + 1) * (μ ^ (s + 1) + (s + 1) * μ ^ s * (ν - μ)) := by
        linear_combination (-(μ ^ s * ν) + μ ^ (s + 1)) * hc' - (n.choose s * μ ^ s) * hnν +
          (n.choose s * μ ^ s) * hnμ - μ ^ (s + 1) * hc
    _ ≤ (n + 1).choose (s + 1) * ν ^ (s + 1) :=
        mul_le_mul_of_nonneg_left (pow_add_mul_sub_le_pow hμ hν s) (Nat.cast_nonneg _)

/-- **Maclaurin's inequality**, comparing the `s`-th elementary symmetric mean with the arithmetic
mean: for `x ≥ 0` on `T`,
`∑ S ∈ T.powersetCard s, ∏ i ∈ S, x i ≤ (#T).choose s * ((∑ i ∈ T, x i) / #T) ^ s`. -/
theorem Finset.sum_powersetCard_prod_le {ι : Type*} (T : Finset ι) {x : ι → ℝ}
    (hx : ∀ i ∈ T, 0 ≤ x i) (s : ℕ) :
    ∑ S ∈ T.powersetCard s, ∏ i ∈ S, x i ≤ (#T).choose s * ((∑ i ∈ T, x i) / #T) ^ s := by
  classical
  induction T using Finset.induction_on generalizing s with
  | empty =>
    cases s with
    | zero => simp
    | succ s => rw [powersetCard_eq_empty.2 (by simp)]; simp
  | insert a T haT ih =>
    have hxT : ∀ i ∈ T, 0 ≤ x i := fun i hi ↦ hx i (mem_insert_of_mem hi)
    have hxa : 0 ≤ x a := hx a (mem_insert_self a T)
    cases s with
    | zero => simp
    | succ s =>
      have hdisj : Disjoint (T.powersetCard (s + 1)) ((T.powersetCard s).image (insert a)) := by
        refine disjoint_left.2 fun S hS hS' ↦ ?_
        obtain ⟨S', -, rfl⟩ := mem_image.1 hS'
        exact haT ((mem_powersetCard.1 hS).1 (mem_insert_self a S'))
      have hinj : Set.InjOn (insert a) (T.powersetCard s : Set (Finset ι)) := by
        intro S hS S' hS' h
        have haS : a ∉ S := fun ha ↦ haT ((mem_powersetCard.1 hS).1 ha)
        have haS' : a ∉ S' := fun ha ↦ haT ((mem_powersetCard.1 hS').1 ha)
        rw [← erase_insert haS, h, erase_insert haS']
      rw [powersetCard_succ_insert haT, sum_union hdisj, sum_image hinj, card_insert_of_notMem haT,
        sum_insert haT, add_comm (x a)]
      have hprod : ∑ S ∈ T.powersetCard s, ∏ i ∈ insert a S, x i =
          x a * ∑ S ∈ T.powersetCard s, ∏ i ∈ S, x i := by
        rw [mul_sum]
        refine sum_congr rfl fun S hS ↦ prod_insert fun ha ↦ haT ((mem_powersetCard.1 hS).1 ha)
      rw [hprod]
      calc _ ≤ (#T).choose (s + 1) * ((∑ i ∈ T, x i) / #T) ^ (s + 1) +
            x a * ((#T).choose s * ((∑ i ∈ T, x i) / #T) ^ s) :=
          add_le_add (ih hxT (s + 1)) (mul_le_mul_of_nonneg_left (ih hxT s) hxa)
        _ ≤ _ := choose_mul_pow_step _ _ (sum_nonneg hxT) hxa

private theorem prod_range_le_prod_range {f g : ℕ → ℕ} (h : ∀ i, f i ≤ g i) (s : ℕ) :
    ∏ i ∈ range s, f i ≤ ∏ i ∈ range s, g i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [prod_range_succ, prod_range_succ]
    exact Nat.mul_le_mul ih (h s)

/-- `m.choose s * r ^ s ≤ r.choose s * m ^ s` for `m ≤ r`: `m.choose s / m ^ s` increases
with `m`. -/
private theorem choose_mul_pow_le_choose_mul_pow {m r : ℕ} (hmr : m ≤ r) (s : ℕ) :
    m.choose s * r ^ s ≤ r.choose s * m ^ s := by
  have key : m.descFactorial s * r ^ s ≤ r.descFactorial s * m ^ s := by
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    calc (∏ i ∈ range s, (m - i)) * r ^ s = ∏ i ∈ range s, ((m - i) * r) := by
          rw [prod_mul_distrib, prod_const, card_range]
      _ ≤ ∏ i ∈ range s, ((r - i) * m) := prod_range_le_prod_range (fun i ↦ by
          rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm m r]
          exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hmr) _) s
      _ = (∏ i ∈ range s, (r - i)) * m ^ s := by rw [prod_mul_distrib, prod_const, card_range]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    mul_assoc, mul_assoc] at key
  exact Nat.le_of_mul_le_mul_left key (Nat.factorial_pos s)

/-- The Maclaurin bound `m.choose s * (S / m) ^ s` increases with `m`. -/
private theorem choose_mul_div_pow_le {m r : ℕ} (hmr : m ≤ r) (s : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    m.choose s * (S / m) ^ s ≤ r.choose s * (S / r) ^ s := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · cases s with
    | zero => simp
    | succ s => simp only [Nat.choose_zero_succ, Nat.cast_zero, zero_mul]; positivity
  have hr : 0 < r := hm.trans_le hmr
  have key : (m.choose s : ℝ) * r ^ s ≤ r.choose s * m ^ s := by
    exact_mod_cast choose_mul_pow_le_choose_mul_pow hmr s
  have hm' : (0 : ℝ) < m ^ s := by positivity
  have hr' : (0 : ℝ) < r ^ s := by positivity
  rw [div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hm' hr']
  nlinarith [pow_nonneg hS s, key]

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The weighted number of `k`-cliques: the sum over `k`-cliques `s` of `∏ v ∈ s, p v`. -/
noncomputable def cliqueWeight (k : ℕ) (p : V → ℝ) : ℝ :=
  ∑ s ∈ G.cliqueFinset k, ∏ v ∈ s, p v

@[simp]
theorem cliqueWeight_one_eq_card (k : ℕ) :
    G.cliqueWeight k (fun _ ↦ 1) = #(G.cliqueFinset k) := by
  simp [cliqueWeight]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Shifting weight between two non-adjacent vertices changes the product over a clique affinely:
a clique contains at most one of them. -/
private theorem prod_add_smul {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v) {s : Finset V}
    (hs : G.IsClique (s : Set V)) (p : V → ℝ) (t : ℝ) :
    ∏ w ∈ s, (p + t • (Pi.single u 1 - Pi.single v 1 : V → ℝ)) w =
      ∏ w ∈ s, p w + ((if u ∈ s then ∏ w ∈ s.erase u, p w else 0) -
        if v ∈ s then ∏ w ∈ s.erase v, p w else 0) * t := by
  set q := p + t • (Pi.single u 1 - Pi.single v 1 : V → ℝ)
  have hq : ∀ w, w ≠ u → w ≠ v → q w = p w := fun w hwu hwv ↦ by simp [q, hwu, hwv]
  by_cases hu : u ∈ s
  · have hv : v ∉ s := fun hv ↦ hnadj (hs hu hv huv)
    rw [← mul_prod_erase s q hu, ← mul_prod_erase s p hu, prod_congr rfl fun w hw ↦
      hq w (ne_of_mem_erase hw) fun h ↦ hv (h ▸ mem_of_mem_erase hw)]
    simp [q, hu, hv, huv]
    ring
  by_cases hv : v ∈ s
  · rw [← mul_prod_erase s q hv, ← mul_prod_erase s p hv, prod_congr rfl fun w hw ↦
      hq w (fun h ↦ hu (h ▸ mem_of_mem_erase hw)) (ne_of_mem_erase hw)]
    simp [q, hu, hv, huv.symm]
    ring
  simp only [hu, hv, ↓reduceIte, sub_zero, zero_mul, add_zero]
  exact prod_congr rfl fun w hw ↦ hq w (fun h ↦ hu (h ▸ hw)) fun h ↦ hv (h ▸ hw)

/-- Along a direction `Pi.single u 1 - Pi.single v 1` with `u, v` non-adjacent, the weighted
clique count is affine. -/
theorem cliqueWeight_add_smul {u v : V} (hnadj : ¬ G.Adj u v) (k : ℕ) (p : V → ℝ) (t : ℝ) :
    G.cliqueWeight k (p + t • (Pi.single u 1 - Pi.single v 1)) =
      G.cliqueWeight k p + (∑ s ∈ G.cliqueFinset k with u ∈ s, ∏ w ∈ s.erase u, p w -
        ∑ s ∈ G.cliqueFinset k with v ∈ s, ∏ w ∈ s.erase v, p w) * t := by
  rcases eq_or_ne u v with rfl | huv
  · simp
  simp only [cliqueWeight, sum_filter, ← sum_sub_distrib, sum_mul, ← sum_add_distrib]
  exact sum_congr rfl fun s hs ↦
    prod_add_smul G huv hnadj (mem_cliqueFinset_iff.1 hs).isClique p t

/-- **Zykov's theorem, weighted form.** If `G` has no `(r + 1)`-clique, then for nonnegative
weights `p` the weighted number of `s`-cliques is at most `r.choose s * ((∑ i, p i) / r) ^ s`. -/
theorem cliqueWeight_le_choose_mul {r s : ℕ} (hG : G.CliqueFree (r + 1)) {p : V → ℝ}
    (hp : 0 ≤ p) : G.cliqueWeight s p ≤ r.choose s * ((∑ i, p i) / r) ^ s := by
  obtain ⟨q, hq, hsum, -, hcl, hpq⟩ := exists_isClique_support_le_of_affine
    (f := G.cliqueWeight s) (fun _ _ _ hnadj p ↦ ⟨_, cliqueWeight_add_smul G hnadj s p⟩) hp
  refine hpq.trans ?_
  rw [← hsum]
  set T : Finset V := {i | q i ≠ 0}
  have hT : G.IsClique (T : Set V) := hcl.subset fun x hx ↦ by simpa [T] using hx
  have hTr : #T ≤ r := by
    by_contra! h
    obtain ⟨t, hts, htc⟩ := exists_subset_card_eq (show r + 1 ≤ #T by omega)
    exact hG t ⟨hT.subset (by exact_mod_cast hts), htc⟩
  -- on `q`, the clique weight is the elementary symmetric polynomial of the weights on `T`
  have hw : G.cliqueWeight s q = ∑ S ∈ T.powersetCard s, ∏ v ∈ S, q v := by
    refine (sum_subset (fun S hS ↦ ?_) fun S hS hST ↦ ?_).symm
    · obtain ⟨hST, hcard⟩ := mem_powersetCard.1 hS
      exact mem_cliqueFinset_iff.2 ⟨hT.subset (by exact_mod_cast hST), hcard⟩
    · have hsub : ¬ S ⊆ T := fun h ↦
        hST (mem_powersetCard.2 ⟨h, (mem_cliqueFinset_iff.1 hS).card_eq⟩)
      obtain ⟨w, hwS, hwT⟩ := not_subset.1 hsub
      exact prod_eq_zero hwS (by simpa [T] using hwT)
  have hsumT : ∑ i, q i = ∑ i ∈ T, q i := (sum_filter_ne_zero _).symm
  rw [hw, hsumT]
  exact (sum_powersetCard_prod_le T (fun i _ ↦ hq i) s).trans
    (choose_mul_div_pow_le hTr s (sum_nonneg fun i _ ↦ hq i))

/-- **Zykov's theorem.** A graph on `n` vertices with no `(r + 1)`-clique has at most
`r.choose s * (n / r) ^ s` cliques of size `s`. -/
theorem card_cliqueFinset_le_choose_mul_div_pow {r s : ℕ} (hG : G.CliqueFree (r + 1)) :
    (#(G.cliqueFinset s) : ℝ) ≤ r.choose s * (Fintype.card V / r) ^ s := by
  simpa using G.cliqueWeight_le_choose_mul (s := s) hG (p := fun _ ↦ 1) fun _ ↦ zero_le_one

/-- The case `s = r` of `SimpleGraph.cliqueWeight_le_choose_mul`. -/
theorem cliqueWeight_le {k : ℕ} (hG : G.CliqueFree (k + 1)) {p : V → ℝ} (hp : 0 ≤ p) :
    G.cliqueWeight k p ≤ ((∑ i, p i) / k) ^ k := by
  simpa using G.cliqueWeight_le_choose_mul (s := k) hG hp

/-- The case `s = r` of Zykov's theorem: a graph with no `(k + 1)`-clique has at most
`(Fintype.card V / k) ^ k` cliques of size `k`. -/
theorem card_cliqueFinset_le_div_pow {k : ℕ} (hG : G.CliqueFree (k + 1)) :
    (#(G.cliqueFinset k) : ℝ) ≤ (Fintype.card V / k) ^ k := by
  simpa using G.card_cliqueFinset_le_choose_mul_div_pow (s := k) hG

end SimpleGraph
