/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module

public import LeanPool.QECCertificates.GF2.Membership
public import LeanPool.QECCertificates.GF2.Witness
public import LeanPool.QECCertificates.GF2.WeightEnum

/-!
# A checkable certificate for the distance lower bound: handing "no lighter logical operator" to
    the kernel

`GF2/Witness` provides the **two-sided interface** that pins down the distance, but the
lower-bound side still sits at the abstract form "given a per-operator inequality", which
is the part LeanQEC delegates to a SAT solver. This module lands it:

```
is the set of light operators nonempty?
  = over the candidate vectors of "weight ≤ d-1", filter by
    "nonzero ∧ in the kernel ∧ not in the row space" and see whether anything is left
```

Every piece of the predicate is computable (`inKerB` / `inSpanB` from `GF2/Membership`),
and the candidate set is the **weight-bounded enumeration** of `GF2/WeightEnum`: 121
vectors rather than 32768 at $n = 15$. The whole decision is therefore a **closed Boolean
identity** that `by decide` can settle directly, with the kernel doing the computation.
No SAT solver, no `native_decide`, and no custom axiom is needed.

## The two properties of the candidate set (they decide the soundness and the cost of the
    certificate)

* **Coverage** (`mem_lightVecs`): every vector of weight $\le w$ lies in the candidate
  set, so "absent from the candidates" means "does not exist at all". This is the source
  of **soundness**, and it is exactly what `Finset.univ` provides for free.
* **Count** (`length_lightVecs`): the candidate set has exactly
  $\sum_{k\le w}\binom nk$ elements. This is the **cost of the certificate**: for
  fixed $d$ it is a polynomial of degree $d-1$ in $n$, not $2^n$.

## Main results

* `lightSet_card_zero_iff`: `(lightSet M₁ M₂ d).card = 0` is **literally equivalent** to
  the lower-bound statement.
* `le_minWeight_of_lightSet_card_zero`: the **lower-bound certificate**; an empty set
  gives the code distance lower bound `d`.
* `eq_minWeight_of_decide`: the **checkable certificate form of the exact distance**,
  with the lower bound by `decide` and an explicit witness for the upper bound; the two
  sides pinch to "the code distance is exactly $d$".
* `lightCand_length_le`: the **certificate complexity**, the candidate space being at
  most $\sum_{k<d}\binom nk$.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## The set of light operators -/

/-- The predicate "undetectable nontrivial operator of weight less than `d`".

The three pieces together are exactly what the lower bound has to rule out: nonzero,
commuting with every check, yet not an element of the check row space. Each piece is
computable, so the kernel can reduce the whole predicate; the weight bound is carried by
the candidate set itself, `lightVecs n (d-1)`.

Marked `abbrev` rather than `def`: `def` is semireducible, so the instance search for
`DecidablePred` does not unfold it and `Finset.filter` fails to synthesize a decidable
predicate. -/
abbrev IsLightUndetectable {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (v : Vec n) : Prop :=
  0 < hammingNorm v ∧ inKerB M₁ v = true ∧ inSpanB (List.ofFn fun i => M₂ i) v = false

/-- **The candidate set for the lower-bound certificate**: among the vectors of weight
$\le d-1$, those that commute with the checks yet do not lie in the row space.

The candidates come from `lightVecs n (d-1)`, a **weight-bounded enumeration** rather
than the full space; the $2^n$ version over `Finset.univ` already takes three minutes at
$n = 15$. The bound $d-1$ on the weight is justified because the lower bound only has to
rule out operators of weight $< d$ (`wtRec_eq_hammingNorm` + `Nat.lt_iff_le_pred`). -/
def lightCand {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (d : ℕ) : List (Vec n) :=
  (lightVecs n (d - 1)).filter (fun v => decide (IsLightUndetectable M₁ M₂ v))

/-- **The set of light operators**: the `Finset` form of the candidate set, in which
`card = 0` means "there is no lighter logical operator". -/
def lightSet {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    (d : ℕ) : Finset (Vec n) :=
  (lightCand M₁ M₂ d).toFinset

/-- Membership characterization, expanding `lightSet` into the candidate set and the
predicate. -/
theorem mem_lightSet {m₁ m₂ : ℕ}
    {M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)}
    {d : ℕ} {v : Vec n} :
    v ∈ lightSet M₁ M₂ d ↔ v ∈ lightCand M₁ M₂ d :=
  List.mem_toFinset

theorem mem_lightCand {m₁ m₂ : ℕ}
    {M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)} {M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)}
    {d : ℕ} {v : Vec n} :
    v ∈ lightCand M₁ M₂ d ↔ v ∈ lightVecs n (d - 1) ∧ IsLightUndetectable M₁ M₂ v := by
  rw [lightCand, List.mem_filter, decide_eq_true_eq]

/-! ## The lower-bound certificate -/

/-- **The lower-bound certificate, checkable form**: an empty set of light operators
implies that the code distance is at least `d`.

The proof is contraposition, coverage and translation. If an undetectable operator of
weight below `d` existed, its weight would be nonzero, since otherwise it would lie in
the row space and contradict undetectability, and a weight $\le d-1$ places it in the
weight-bounded enumeration (`mem_lightVecs`; **the soundness of this certificate rests
entirely on that coverage theorem**). The lemmas `inKerB_iff` and `inSpanB_eq_false_iff`
then translate it into the two certificates of the decision layer, and `mem_lightCand`
puts it back into the set, contradicting emptiness. -/
theorem lowerHyp_of_lightSet_card_zero {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (h : (lightSet M₁ M₂ d).card = 0) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.certificateRowSpace → d ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < d := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.certificateRowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs n (d - 1) := by
    refine mem_lightVecs n (d - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ lightCand M₁ M₂ d := by
    rw [mem_lightCand]
    exact ⟨hcov, hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanB_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  have hmem' : E ∈ lightSet M₁ M₂ d := mem_lightSet.mpr hmem
  rw [Finset.card_eq_zero] at h
  rw [h] at hmem'
  simp at hmem'

/-- **The lower-bound theorem, checkable certificate form**: an empty `lightSet` gives the
distance lower bound. -/
theorem le_minWeight_of_lightSet_card_zero {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (h : (lightSet M₁ M₂ d).card = 0) :
    d ≤ minWeightKernelOutsideRowSpace M₁ M₂ :=
  le_minWeight_of_lower M₁ M₂ hd (lowerHyp_of_lightSet_card_zero M₁ M₂ h)

/-! ## The List-form lower-bound entry point (for large candidate sets)

`lightSet` is the `Finset` form of the candidate list, and the deduplication inside
`List.toFinset` compares elements pairwise, at cost $O(N^2)$. On instances such as
$n=24,\ d=4$, with 2325 candidates each a 24-bit vector, **the deduplication itself
dominates the whole `decide`**. The three results below have the same mathematical content
as the `lightSet` family above, with the hypothesis replaced by `lightCand M₁ M₂ d = []`,
so that no part of the `Finset` path enters the reduction.
Small instances ($n\le18$) go through either way; once the candidate count reaches the
thousands, the List form is an order of magnitude apart.
-/

/-- **The lower-bound certificate, List form**: an empty candidate list implies that the
code distance is at least `d`. -/
theorem lowerHyp_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (h : lightCand M₁ M₂ d = []) :
    ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.certificateRowSpace → d ≤ hammingNorm E := by
  intro E hker hnot
  by_contra hlt
  have hlt' : hammingNorm E < d := not_le.mp hlt
  have hne : E ≠ 0 := fun h0 => hnot (h0 ▸ M₂.certificateRowSpace.zero_mem)
  have hpos : 0 < hammingNorm E := Nat.pos_of_ne_zero fun h0 => hne (hammingNorm_eq_zero.mp h0)
  have hcov : E ∈ lightVecs n (d - 1) := by
    refine mem_lightVecs n (d - 1) E ?_
    rw [wtRec_eq_hammingNorm]
    omega
  have hmem : E ∈ lightCand M₁ M₂ d := by
    rw [mem_lightCand]
    exact ⟨hcov, hpos, (inKerB_iff M₁ E).mpr hker,
      (inSpanB_eq_false_iff (List.ofFn fun i => M₂ i) E).mpr
        (by rwa [Matrix.rowSpace_eq_spanL_ofFn] at hnot)⟩
  rw [h] at hmem
  simp at hmem

/-- **The lower-bound theorem, List form**. -/
theorem le_minWeight_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d₀ : ℕ} (hd : d₀ ≤ n) (h : lightCand M₁ M₂ d₀ = []) :
    d₀ ≤ minWeightKernelOutsideRowSpace M₁ M₂ :=
  le_minWeight_of_lower M₁ M₂ hd (lowerHyp_of_lightCand_nil M₁ M₂ h)

/-- **The exact distance, List form**: the same shape as `eq_minWeight_of_decide` with the
lower-bound hypothesis replaced by an empty candidate list; used for instances with large
candidate sets. -/
theorem eq_minWeight_of_lightCand_nil {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (hlow : lightCand M₁ M₂ d = []) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace) (hw : hammingNorm E =
      d) :
    minWeightKernelOutsideRowSpace M₁ M₂ = d :=
  eq_minWeight_of_bounds M₁ M₂ hd hker hnot hw (lowerHyp_of_lightCand_nil M₁ M₂ hlow)

/-- **The exact distance, checkable certificate form**: the lower bound by `decide` and an
explicit witness for the upper bound pinch to an equality.

This is the uniform proof template for the case matrix of this library. For a code, only
four things have to be supplied: (i) two parity-check matrices, (ii) an explicit low-weight
logical operator `E`, (iii) three closed assertions the kernel can compute, namely that
`E` is in the kernel, that `E` is not in the row space, and that `hammingNorm E = d`, and
(iv) an empty `lightSet`. **No step refers to an external solver or to a custom axiom.** -/
theorem eq_minWeight_of_decide {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : d ≤ n) (hlow : (lightSet M₁ M₂ d).card = 0) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace) (hw : hammingNorm E =
      d) :
    minWeightKernelOutsideRowSpace M₁ M₂ = d :=
  eq_minWeight_of_bounds M₁ M₂ hd hker hnot hw
    (lowerHyp_of_lightSet_card_zero M₁ M₂ hlow)

/-! ## Certificate complexity -/

/-- **The size of the candidate space for the lower-bound certificate**: at most
$\sum_{k<d}\binom nk$.

This is the visible content of the certificate-complexity statement for the distance
decision: the candidate set is a weight-bounded enumeration, not $2^n$, and the
**enumeration length is exactly given by binomial coefficients** (`length_lightVecs`). For
fixed $d$ this is a polynomial of degree $d-1$ in $n$: 121 candidates at $n = 15, d = 3$,
against $32768$ for the full space. -/
theorem lightCand_length_le {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : 1 ≤ d) :
    (lightCand M₁ M₂ d).length ≤ ∑ k ∈ Finset.range d, n.choose k := by
  refine (List.length_filter_le _ _).trans ?_
  rw [length_lightVecs, show d - 1 + 1 = d from by omega]

/-- The same statement in `Finset` form. -/
theorem lightSet_card_le {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {d : ℕ} (hd : 1 ≤ d) :
    (lightSet M₁ M₂ d).card ≤ ∑ k ∈ Finset.range d, n.choose k :=
  (List.toFinset_card_le _).trans (lightCand_length_le M₁ M₂ hd)

/-! ## Convenience lemmas for the case matrix -/

/-- Kernel membership from a computable decision; the case matrix writes
`(mem_ker_of_inKerB .. (by decide))`. -/
theorem mem_ker_of_inKerB {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2)) {v : Vec n}
    (h : inKerB M v = true) : v ∈ LinearMap.ker M.toLin' :=
  (inKerB_iff M v).mp h

/-- **The dual witness route**: `w ∈ ker H` together with `w ⬝ᵥ E = 1` implies
`E ∉ certificateRowSpace H`.

An order of magnitude cheaper than `not_mem_rowSpace_of_inSpanB_false`: both assertions are
row-by-row pairings and **row reduction is not needed**. For wide matrices, say the toric
code at $n = 18$, this is not an optimization but the difference between usable and
unusable, since `inSpanB` runs `rowReduce` internally and the kernel reduction cost of
`rowReduce` on an 18-wide matrix would exhaust the heartbeat budget of `by decide`. -/
theorem not_mem_rowSpace_of_dualCheck {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    {E w : Vec n} (hk : inKerB H w = true) (hp : w ⬝ᵥ E = 1) : E ∉ H.certificateRowSpace :=
  DualWitness.not_mem_rowSpace ⟨w, (inKerB_iff H w).mp hk, hp⟩

/-- Non-membership in the row space, from a computable decision; the case matrix writes
`(not_mem_rowSpace_of_inSpanB_false .. (by decide))`.

**Note**: this lemma runs `rowReduce` internally and is expensive on wide matrices; for
those, use `not_mem_rowSpace_of_dualCheck`, the dual witness route, instead. -/
theorem not_mem_rowSpace_of_inSpanB_false {m : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    {v : Vec n} (h : inSpanB (List.ofFn fun i => M i) v = false) : v ∉ M.certificateRowSpace := by
  rw [Matrix.rowSpace_eq_spanL_ofFn]
  exact (inSpanB_eq_false_iff _ v).mp h

end QECCertificates
