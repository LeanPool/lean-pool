/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.CuspField
public import LeanPool.HyperellipticCurves.Log.Fold.GenericAtom

import LeanPool.HyperellipticCurves.Log.Fold.CuspWitness

/-!
# The full cuspidal fold: the phase-2 mirror

This file extends the cuspidal fold witness from phase 1 (the `g` stages of
`ChabautyColeman.exists_genCuspChain_witness`) to the **full `2g`-step fold** of
`def:centre-fold`: on the cusp the hyperelliptic involution is `t ↦ -t` (the degree `N`
is odd), so phase 2 is the phase-1 machinery continued at the negated nodes, taken in
**reverse order** (`ChabautyColeman.foldNodes`) — the fold removes the points it added
last first, so it retraces its own phase-1 states backwards (`lem:fold-mirror`). The
phase-2 stages are certified entirely on the cusp:

* `ChabautyColeman.prod_foldNodes_pairing`: the stage-`(g+m)` alphabet factors as the
  **even** polynomial `∏_(i<m) (X² - t_(g-1-i)²)` — each phase-2 node paired with one
  copy of its double — times the stage-`(g-m)` alphabet of the phase-1 chain; the master
  congruence therefore descends to the phase-1 alphabet
  (`ChabautyColeman.congruence_of_even_mul`), and no second chain is needed;
* the value extraction: avoidance and disjointness values of every phase-2 stage come
  from `ChabautyColeman.eval_ne_zero_of_momentDet_ne_zero` against the descended
  congruence and the phase-1 atoms at the generic nodes
  (`ChabautyColeman.genNode_zero_atom_ne_zero`, `ChabautyColeman.genNode_trio_atom_ne_zero`,
  `ChabautyColeman.genNode_tripled_atom_ne_zero`) — no state identification is ever
  needed, except at the final stage;
* `ChabautyColeman.exists_genCuspFold_witness` — **the full-fold witness**: a doubling
  scalar `H₀` such that all `2g` stages of the generic cuspidal fold satisfy the fold
  invariants, all interior avoidance values are nonzero and all composition conditions
  hold; moreover the final state has support `A₀` again (`τ + τ - τ = τ` on the cusp,
  by the uniqueness of the monic moment solution
  `ChabautyColeman.eq_of_det_momentMatrix_ne_zero`).
-/
@[expose] public section

open Polynomial

namespace ChabautyColeman

section FoldNodes

variable {R : Type*} [CommRing R] {g : ℕ}

/-- The node sequence of the full `2g`-step fold: the `g` phase-1 nodes, then their
negatives in reverse order — on the cusp the hyperelliptic involution is `t ↦ -t`, and
the fold removes the points it added last first. -/
def foldNodes (g : ℕ) (t : ℕ → R) : ℕ → R := fun i ↦
  if i < g then t i else -t (g - 1 - (i - g))

theorem foldNodes_of_lt {t : ℕ → R} {i : ℕ} (hi : i < g) : foldNodes g t i = t i :=
  ite_eq_left hi

theorem foldNodes_add (t : ℕ → R) (i : ℕ) : foldNodes g t (g + i) = -t (g - 1 - i) := by
  rw [foldNodes, ite_eq_right (by lia), Nat.add_sub_cancel_left]

/-- **The phase-2 pairing**: the alphabet factors of the full fold at stage `g + m` are
the phase-2 nodes paired with one copy of their doubles — an even polynomial — times the
stage-`(g-m)` alphabet of the phase-1 chain: the fold retraces its own states. -/
theorem prod_foldNodes_pairing (t : ℕ → R) {m : ℕ} (hm : m ≤ g) :
    ∏ i ∈ Finset.range (g + m), (Polynomial.C (foldNodes g t i) - X)
      = (∏ i ∈ Finset.range m, (X ^ 2 - Polynomial.C (t (g - 1 - i) ^ 2)))
        * ∏ i ∈ Finset.range (g - m), (Polynomial.C (t i) - X) := by
  have h1 : ∏ i ∈ Finset.range g, (Polynomial.C (foldNodes g t i) - X)
      = ∏ i ∈ Finset.range g, (Polynomial.C (t i) - X) :=
    Finset.prod_congr rfl fun i hi ↦ by rw [foldNodes_of_lt (Finset.mem_range.mp hi)]
  have h2 : ∏ i ∈ Finset.range m, (Polynomial.C (foldNodes g t (g + i)) - X)
      = ∏ i ∈ Finset.range m, (Polynomial.C (-t (g - 1 - i)) - X) :=
    Finset.prod_congr rfl fun i _ ↦ by rw [foldNodes_add]
  have hsplit := Finset.prod_range_add (fun i ↦ (Polynomial.C (t i) - X)) (g - m) m
  rw [show g - m + m = g by lia] at hsplit
  have hrefl : ∏ i ∈ Finset.range m, (Polynomial.C (t (g - m + i)) - X)
      = ∏ i ∈ Finset.range m, (Polynomial.C (t (g - 1 - i)) - X) := by
    rw [← Finset.prod_range_reflect (fun i ↦ (Polynomial.C (t (g - m + i)) - X)) m]
    exact Finset.prod_congr rfl fun i hi ↦ by
      rw [show g - m + (m - 1 - i) = g - 1 - i by
        have := Finset.mem_range.mp hi; lia]
  rw [Finset.prod_range_add, h1, h2, hsplit, hrefl, mul_assoc, mul_comm,
    ← Finset.prod_mul_distrib]
  refine congrArg (· * _) (Finset.prod_congr rfl fun i _ ↦ ?_)
  rw [map_neg, map_pow]
  ring

/-- The paired phase-2 factors form an even polynomial. -/
theorem prod_sq_sub_comp_neg (t : ℕ → R) (m : ℕ) :
    (∏ i ∈ Finset.range m, (X ^ 2 - Polynomial.C (t i ^ 2))).comp (-X)
      = ∏ i ∈ Finset.range m, (X ^ 2 - Polynomial.C (t i ^ 2)) := by
  rw [prod_comp]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [sub_comp, pow_comp, X_comp, C_comp, neg_sq]

end FoldNodes

section EvenEval

variable {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}

theorem eval_zero_prod_sq_sub_ne_zero {t : ℕ → R} (ht : ∀ i < m, t i ≠ 0) :
    (∏ i ∈ Finset.range m, (X ^ 2 - Polynomial.C (t i ^ 2))).eval 0 ≠ 0 := by
  rw [eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_
  rw [eval_sub, eval_pow, eval_X, eval_C]
  simpa using pow_ne_zero 2 (ht i (Finset.mem_range.mp hi))

end EvenEval

section FoldWitness

variable {k : Type*} [Field k] {g : ℕ}

private theorem d0_cong {F : Type*} [CommRing F] (g : ℕ) (A₀ : F[X]) :
    X ^ (2 * g + 1) ∣ A₀ * ((-1) ^ g * A₀).comp (-X) - A₀.comp (-X) * ((-1) ^ g * A₀) := by
  rw [show A₀ * ((-1) ^ g * A₀).comp (-X) - A₀.comp (-X) * ((-1) ^ g * A₀) = 0 by
    simp only [mul_comp, pow_comp, neg_comp, one_comp]
    ring]
  exact dvd_zero _

private theorem eq_genA₀_of_congr [NeZero (2 : k)]
    {A : (FractionRing (MvPolynomial ℕ k))[X]} (hA : A.Monic) (hAdeg : A.natDegree = g)
    (hcong : X ^ (2 * g + 1) ∣ A * ((-1) ^ g * genA₀ k g).comp (-X)
      - A.comp (-X) * ((-1) ^ g * genA₀ k g)) :
    A = genA₀ k g := by
  have hbase : IsCuspState g (genU₀ k g) (genV₀ k g) (genA₀ k g) :=
    isCuspState_base genNode_sq_injective
  refine eq_of_det_momentMatrix_ne_zero two_ne_zero_fractionRing hA hAdeg hbase.monicA
    hbase.natDegree_A hcong (d0_cong g (genA₀ k g)) ?_
  rw [← momentDet_id,
    show ((-1) ^ g * genA₀ k g : (FractionRing (MvPolynomial ℕ k))[X]).comp (-X)
      = ((-1) ^ g * tupleU (fun i : Fin g ↦ genNode k i)
        * ∏ i ∈ Finset.range 0, (Polynomial.C (genNode k i) - X)).comp (-X) by
      rw [Finset.prod_range_zero, mul_one]; rfl,
    cusp_alphabet_comp_neg (fun m ↦ genNode k m) (Nat.zero_le g)]
  have hmap : ((doublesPoly (fun l ↦ (MvPolynomial.X (0 - 1 - l) : MvPolynomial ℕ k))
        (fun i ↦ MvPolynomial.X (g - 1 - i)) 0 (g - 0)).map
        (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))))
      = doublesPoly (fun l ↦ genNode k (0 - 1 - l)) (fun i ↦ genNode k (g - 1 - i))
          0 (g - 0) := by
    simp only [doublesPoly_map, genNode]
  rw [← hmap]
  exact momentDet_algebraMap_ne_zero _ (momentDet_generic_doubles_ne_zero (Nat.zero_le g))

/-- The scalar sequence of the generic full cuspidal fold: the supplied doubling scalar
`H₀`, then the generic division values along the extended node sequence. -/
noncomputable def genFoldH (k : Type*) [Field k] (g : ℕ)
    (H₀ : FractionRing (MvPolynomial ℕ k)) : ℕ → FractionRing (MvPolynomial ℕ k) :=
  cuspGenH g (genU₀ k g) (genV₀ k g) (genA₀ k g) (foldNodes g (genNode k)) H₀

/-- **The generic full cuspidal fold**: all `2g` single-point additions of
`def:centre-fold` on the cusp — the `g` phase-1 nodes, then their negatives in reverse
order — run with the doubling scalar `H₀` at the initial step and the generic division
scalars beyond. -/
noncomputable def genCuspFold (k : Type*) [Field k] (g : ℕ)
    (H₀ : FractionRing (MvPolynomial ℕ k)) :
    ℕ → (FractionRing (MvPolynomial ℕ k))[X] × (FractionRing (MvPolynomial ℕ k))[X]
      × (FractionRing (MvPolynomial ℕ k))[X] :=
  cuspChain g (genU₀ k g) (genV₀ k g) (genA₀ k g) (foldNodes g (genNode k))
    (genFoldH k g H₀)

/-- The master congruence of the extended chain at stage `g + m`, descended along the
even phase-2 pairing to the stage-`(g - m)` alphabet of the phase-1 chain. -/
private theorem foldChain_congr [NeZero (2 : k)]
    {H₀ : FractionRing (MvPolynomial ℕ k)} {m : ℕ} (hm : m ≤ g)
    (hok : ∀ j < g + m,
      (genCuspFold k g H₀ j).2.2
        * (X - Polynomial.C (foldNodes g (genNode k) j))
        ∣ X ^ (2 * g + 1)
          - ((genCuspFold k g H₀ j).2.1
            + Polynomial.C (genFoldH k g H₀ j)
              * (genCuspFold k g H₀ j).1).comp (X ^ 2))
    (hav : ∀ j < g + m,
      ((genCuspFold k g H₀ j).2.2).eval 0 ≠ 0) :
    X ^ (2 * g + 1) ∣
      (genCuspFold k g H₀ (g + m)).2.2
        * ((-1) ^ g * genA₀ k g
          * ∏ i ∈ Finset.range (g - m), (Polynomial.C (genNode k i) - X)).comp (-X)
      - ((genCuspFold k g H₀ (g + m)).2.2).comp (-X)
        * ((-1) ^ g * genA₀ k g
          * ∏ i ∈ Finset.range (g - m), (Polynomial.C (genNode k i) - X)) := by
  have hTne : ∀ j, foldNodes g (genNode k) j ≠ 0 := fun j ↦ by
    rw [foldNodes]
    split_ifs
    exacts [genNode_ne_zero j, neg_ne_zero.mpr (genNode_ne_zero _)]
  have hbase : IsCuspState g (genU₀ k g) (genV₀ k g) (genA₀ k g) :=
    isCuspState_base genNode_sq_injective
  have h1 := cuspChain_moment_congruence (d₀ := (-1) ^ g * genA₀ k g) (m := g + m)
    hbase hok hav (fun j _ ↦ hTne j)
    (d0_cong g (genA₀ k g))
  rw [prod_foldNodes_pairing (genNode k) hm,
    show (-1) ^ g * genA₀ k g
        * ((∏ i ∈ Finset.range m, (X ^ 2 - Polynomial.C (genNode k (g - 1 - i) ^ 2)))
          * ∏ i ∈ Finset.range (g - m), (Polynomial.C (genNode k i) - X))
      = (∏ i ∈ Finset.range m, (X ^ 2 - Polynomial.C (genNode k (g - 1 - i) ^ 2)))
        * ((-1) ^ g * genA₀ k g
          * ∏ i ∈ Finset.range (g - m), (Polynomial.C (genNode k i) - X))
      by ring] at h1
  exact congruence_of_even_mul
    (eval_zero_prod_sq_sub_ne_zero (t := fun i ↦ genNode k (g - 1 - i))
      fun i _ ↦ genNode_ne_zero _)
    (prod_sq_sub_comp_neg (fun i ↦ genNode k (g - 1 - i)) m) h1

/-- **The phase-2 mirror values**: at stage `g + m` of the extended fold the support
`A_(g+m)` is nonzero at the incoming node `-t_(g-m-1)` and at its negative — the two
values `A_(g-m)(∓t_(g-m-1))` at the last-added node of the retraced phase-1 stage,
certified by the mirror atoms at the generic nodes against the descended congruence. -/
private theorem foldWitness_mirror_vals [NeZero (2 : k)] (hg2 : 2 ≤ g)
    {H₀ : FractionRing (MvPolynomial ℕ k)} {m : ℕ} (hm : m < g)
    (ihok : ∀ j < g + m, (genCuspFold k g H₀ j).2.2
        * (X - Polynomial.C (foldNodes g (genNode k) j))
        ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ j).2.1
          + Polynomial.C (genFoldH k g H₀ j)
            * (genCuspFold k g H₀ j).1).comp (X ^ 2))
    (ihav : ∀ j < g + m, ((genCuspFold k g H₀ j).2.2).eval 0 ≠ 0) :
    ((genCuspFold k g H₀ (g + m)).2.2).eval (foldNodes g (genNode k) (g + m)) ≠ 0
      ∧ ((genCuspFold k g H₀ (g + m)).2.2).eval (-foldNodes g (genNode k) (g + m)) ≠ 0 := by
  have hg : 0 < g := by lia
  have hstate : IsCuspState g (genCuspFold k g H₀ (g + m)).1
      (genCuspFold k g H₀ (g + m)).2.1 (genCuspFold k g H₀ (g + m)).2.2 :=
    isCuspState_cuspChain (isCuspState_base genNode_sq_injective) ihok
  have hdesc := foldChain_congr hm.le ihok ihav
  rw [foldNodes_add, show g - 1 - m = g - m - 1 by lia]
  exact ⟨eval_ne_zero_of_momentDet_ne_zero two_ne_zero_fractionRing hg hstate.monicA
      hstate.natDegree_A hdesc (genNode_tripled_atom_ne_zero hg2 (by lia : 1 ≤ g - m) (by lia)),
    eval_ne_zero_of_momentDet_ne_zero two_ne_zero_fractionRing hg hstate.monicA
      hstate.natDegree_A hdesc (genNode_trio_atom_ne_zero (by lia : 1 ≤ g - m) (by lia))⟩

/-- **The phase-2 disjointness values**: at stage `g + m` of the extended fold the
support evaluates to a nonzero value at the square of the incoming node — the product of
the two mirror values. -/
theorem genCuspFold_eval_sq_ne_zero [NeZero (2 : k)] (hg2 : 2 ≤ g)
    {H₀ : FractionRing (MvPolynomial ℕ k)} {m : ℕ} (hm : m < g)
    (ihok : ∀ j < g + m, (genCuspFold k g H₀ j).2.2
        * (X - Polynomial.C (foldNodes g (genNode k) j))
        ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ j).2.1
          + Polynomial.C (genFoldH k g H₀ j)
            * (genCuspFold k g H₀ j).1).comp (X ^ 2))
    (ihav : ∀ j < g + m, ((genCuspFold k g H₀ j).2.2).eval 0 ≠ 0) :
    ((genCuspFold k g H₀ (g + m)).1).eval (foldNodes g (genNode k) (g + m) ^ 2) ≠ 0 := by
  obtain ⟨hAt, hAmt⟩ := foldWitness_mirror_vals hg2 hm ihok ihav
  have hstate : IsCuspState g (genCuspFold k g H₀ (g + m)).1
      (genCuspFold k g H₀ (g + m)).2.1 (genCuspFold k g H₀ (g + m)).2.2 :=
    isCuspState_cuspChain (isCuspState_base genNode_sq_injective) ihok
  rw [hstate.eval_sq]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hAt hAmt)

/-- One phase-2 step of the extended fold: the composition condition at stage `g + m`. -/
private theorem foldWitness_step [NeZero (2 : k)] (hg2 : 2 ≤ g)
    {H₀ : FractionRing (MvPolynomial ℕ k)} {m : ℕ} (hm1 : m + 1 ≤ g)
    (ihok : ∀ j < g + m, (genCuspFold k g H₀ j).2.2
        * (X - Polynomial.C (foldNodes g (genNode k) j))
        ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ j).2.1
          + Polynomial.C (genFoldH k g H₀ j)
            * (genCuspFold k g H₀ j).1).comp (X ^ 2))
    (ihav : ∀ j < g + m, ((genCuspFold k g H₀ j).2.2).eval 0 ≠ 0) :
    (genCuspFold k g H₀ (g + m)).2.2 * (X - Polynomial.C (foldNodes g (genNode k) (g + m)))
      ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ (g + m)).2.1
        + Polynomial.C (genFoldH k g H₀ (g + m)) * (genCuspFold k g H₀ (g + m)).1).comp
          (X ^ 2) := by
  obtain ⟨hAt, hAmt⟩ := foldWitness_mirror_vals hg2 (by lia) ihok ihav
  have hHval : genFoldH k g H₀ (g + m)
      = (foldNodes g (genNode k) (g + m) ^ (2 * g + 1)
          - ((genCuspFold k g H₀ (g + m)).2.1).eval (foldNodes g (genNode k) (g + m) ^ 2))
        / ((genCuspFold k g H₀ (g + m)).1).eval (foldNodes g (genNode k) (g + m) ^ 2) := by
    obtain ⟨s, hs⟩ : ∃ s, g + m = s + 1 := ⟨g + m - 1, by lia⟩
    rw [hs]
    exact cuspGenH_succ s
  rw [hHval]
  exact cuspStep_cond_of_generic
    (isCuspState_cuspChain (isCuspState_base genNode_sq_injective) ihok) hAt hAmt

/-- The avoidance value at the phase-2 stage `g + m + 1`. -/
private theorem foldWitness_avd [NeZero (2 : k)] (hg2 : 2 ≤ g)
    {H₀ : FractionRing (MvPolynomial ℕ k)} {m : ℕ} (hm1 : m + 1 ≤ g)
    (ihok : ∀ j < g + (m + 1), (genCuspFold k g H₀ j).2.2
        * (X - Polynomial.C (foldNodes g (genNode k) j))
        ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ j).2.1
          + Polynomial.C (genFoldH k g H₀ j)
            * (genCuspFold k g H₀ j).1).comp (X ^ 2))
    (ihav : ∀ j < g + (m + 1), ((genCuspFold k g H₀ j).2.2).eval 0 ≠ 0) :
    ((genCuspFold k g H₀ (g + (m + 1))).2.2).eval 0 ≠ 0 := by
  have hg : 0 < g := by lia
  have hbase : IsCuspState g (genU₀ k g) (genV₀ k g) (genA₀ k g) :=
    isCuspState_base genNode_sq_injective
  have hstate' : IsCuspState g (genCuspFold k g H₀ (g + (m + 1))).1
      (genCuspFold k g H₀ (g + (m + 1))).2.1 (genCuspFold k g H₀ (g + (m + 1))).2.2 :=
    isCuspState_cuspChain hbase ihok
  have hdesc' := foldChain_congr hm1 ihok ihav
  rcases eq_or_ne (m + 1) g with heq | hne
  · rw [show g - (m + 1) = 0 by lia, Finset.prod_range_zero, mul_one] at hdesc'
    rw [eq_genA₀_of_congr hstate'.monicA hstate'.natDegree_A hdesc']
    exact eval_zero_genA₀_ne_zero
  · have h := eval_ne_zero_of_momentDet_ne_zero two_ne_zero_fractionRing hg
      hstate'.monicA hstate'.natDegree_A hdesc' (w := 0) (by
        rw [show (Polynomial.C (0 : FractionRing (MvPolynomial ℕ k)) + X
            : (FractionRing (MvPolynomial ℕ k))[X]) = X by simp]
        exact genNode_zero_atom_ne_zero (by lia : 1 ≤ g - (m + 1)) (by lia))
    rwa [neg_zero] at h

/-- **`thm:cusp-witness` over the function field, the full `2g`-step fold**: there is a
doubling scalar `H₀` such that every stage of the generic full cuspidal fold satisfies
the fold invariants, every interior avoidance value is nonzero and every composition
condition holds — the phase-2 stages by the mirror mechanism of `lem:fold-mirror`.
(The closed-loop identity `τ + τ - τ = τ` on the cusp — the final state has support `A₀`
again — is used internally at the last mirror stage but is not part of the witness
interface: no consumer spends it.) -/
theorem exists_genCuspFold_witness [NeZero (2 : k)] (hg2 : 2 ≤ g) :
    ∃ H₀ : FractionRing (MvPolynomial ℕ k),
      (∀ m ≤ 2 * g,
        (IsCuspState g (genCuspFold k g H₀ m).1 (genCuspFold k g H₀ m).2.1
          (genCuspFold k g H₀ m).2.2)
        ∧ ((genCuspFold k g H₀ m).2.2).eval 0 ≠ 0
        ∧ (m < 2 * g → (genCuspFold k g H₀ m).2.2
            * (X - Polynomial.C (foldNodes g (genNode k) m))
            ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ m).2.1
              + Polynomial.C (genFoldH k g H₀ m)
                * (genCuspFold k g H₀ m).1).comp (X ^ 2))
        ∧ (1 ≤ m → m < 2 * g → ((genCuspFold k g H₀ m).1).eval
            (foldNodes g (genNode k) m ^ 2) ≠ 0)) := by
  have hg : 0 < g := by lia
  obtain ⟨H₀, hwit⟩ := exists_genCuspChain_witness (k := k) hg
  have hH : ∀ j < g, genFoldH k g H₀ j
      = cuspGenH g (genU₀ k g) (genV₀ k g) (genA₀ k g) (genNode k) H₀ j := fun j hj ↦
    cuspGenH_congr j fun i hi ↦ foldNodes_of_lt (by lia)
  have hC : ∀ m ≤ g, genCuspFold k g H₀ m = genCuspChain k g H₀ m := fun m hm ↦
    cuspChain_congr (fun i hi ↦ foldNodes_of_lt (by lia)) fun i hi ↦ hH i (by lia)
  have hok1 : ∀ j < g, (genCuspFold k g H₀ j).2.2
        * (X - Polynomial.C (foldNodes g (genNode k) j))
        ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ j).2.1
          + Polynomial.C (genFoldH k g H₀ j)
            * (genCuspFold k g H₀ j).1).comp (X ^ 2) := fun j hj ↦ by
    rw [hC j hj.le, foldNodes_of_lt hj, hH j hj]
    exact (hwit j hj.le).2.2.1 hj
  have hav1 : ∀ j ≤ g, ((genCuspFold k g H₀ j).2.2).eval 0 ≠ 0 := fun j hj ↦ by
    rw [hC j hj]
    exact (hwit j hj).2.1
  -- the phase-1 disjointness values, from the value clause of the chain witness
  have hval1 : ∀ m, 1 ≤ m → m < g →
      ((genCuspFold k g H₀ m).1).eval (foldNodes g (genNode k) m ^ 2) ≠ 0 := by
    intro m hm1 hmg
    have hstate : IsCuspState g (genCuspFold k g H₀ m).1 (genCuspFold k g H₀ m).2.1
        (genCuspFold k g H₀ m).2.2 :=
      isCuspState_cuspChain (isCuspState_base genNode_sq_injective) fun j hj ↦
        hok1 j (by lia)
    have hA22 : (genCuspFold k g H₀ m).2.2 = (genCuspChain k g H₀ m).2.2 :=
      congrArg (·.2.2) (hC m hmg.le)
    rw [foldNodes_of_lt hmg, hstate.eval_sq]
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero ?_ ?_)
    · have h := (hwit m hmg.le).2.2.2 (-genNode k m) (by
        rw [genA₀]
        exact genNode_pair_atom_ne_zero hm1 hmg)
      rw [neg_neg] at h
      rwa [hA22]
    · have h := (hwit m hmg.le).2.2.2 (genNode k m) (by
        rw [genA₀]
        exact genNode_plus_atom_ne_zero hmg)
      rwa [hA22]
  clear hwit hH hC
  have main : ∀ m, m ≤ g →
      (∀ j < g + m, (genCuspFold k g H₀ j).2.2
        * (X - Polynomial.C (foldNodes g (genNode k) j))
        ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ j).2.1
          + Polynomial.C (genFoldH k g H₀ j)
            * (genCuspFold k g H₀ j).1).comp (X ^ 2))
      ∧ (∀ j ≤ g + m, ((genCuspFold k g H₀ j).2.2).eval 0 ≠ 0) := by
    intro m
    induction m with
    | zero => exact fun _ ↦ ⟨fun j hj ↦ hok1 j (by lia), fun j hj ↦ hav1 j (by lia)⟩
    | succ m ih =>
      intro hm1
      obtain ⟨ihok, ihav⟩ := ih (by lia)
      have hokgm := foldWitness_step hg2 hm1 ihok fun j hj ↦ ihav j (by lia)
      have ihok' : ∀ j < g + (m + 1), (genCuspFold k g H₀ j).2.2
        * (X - Polynomial.C (foldNodes g (genNode k) j))
        ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ j).2.1
          + Polynomial.C (genFoldH k g H₀ j)
            * (genCuspFold k g H₀ j).1).comp (X ^ 2) := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact ihok j h
        · exact hokgm
      have havgm1 := foldWitness_avd hg2 hm1 ihok' fun j hj ↦ ihav j (by lia)
      refine ⟨ihok', fun j hj ↦ ?_⟩
      rcases hj.lt_or_eq with h | rfl
      · exact ihav j (by lia)
      · exact havgm1
  obtain ⟨hokA, havA⟩ := main g le_rfl
  have hbase : IsCuspState g (genU₀ k g) (genV₀ k g) (genA₀ k g) :=
    isCuspState_base genNode_sq_injective
  refine ⟨H₀, fun m hm ↦
    ⟨isCuspState_cuspChain hbase fun j hj ↦ hokA j (by lia),
      havA m (by lia), fun hmlt ↦ hokA m (by lia), fun hm1 hmlt ↦ ?_⟩⟩
  · rcases Nat.lt_or_ge m g with hmg | hmg
    · exact hval1 m hm1 hmg
    · obtain ⟨m', rfl⟩ : ∃ m', m = g + m' := ⟨m - g, by lia⟩
      exact genCuspFold_eval_sq_ne_zero hg2 (by lia)
        (fun j hj ↦ hokA j (by lia)) fun j hj ↦ havA j (by lia)

end FoldWitness

end ChabautyColeman

end
