/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module
public import LeanPool.QECCertificates.GF2.RankCertificate

/-!
# Dual-witness certificates and the exact-distance pair of theorems

Certifying a code distance is two-sided. The **lower bound** says that no lighter logical
operator exists, which calls for enumeration or reduction over low-weight operators; the
**upper bound** says that here is one, which needs only a concrete artefact. This module
turns the upper-bound side into an **independently checkable certificate** and joins it
with the LeanQEC distance definition into a closed assertion that the distance is exactly
$d$.

## Dual witnesses

To prove that an operator `E` is **not** in the parity-check row space one need not
enumerate: it suffices to exhibit a vector `w` that commutes with every check and
anticommutes with `E`, that is
  `w ∈ ker H` and `w ⬝ᵥ E = 1`.

This is a certificate-shaped wrapper around LeanQEC's
`not_mem_rowspace_iff_exists_mem_ker`: **the certificate has two entries and each is
checkable on its own**, and completeness (`E ∉ certificateRowSpace` implies such a `w` exists) is
given by that theorem.

## The two-matrix form

The table below (`M₁` supplies the kernel and `M₂` the row space) covers all three classes
of code in this package:

| Code class | `M₁` | `M₂` | weight = |
|---|---|---|---|
| classical linear code | the parity-check matrix `H` | the empty matrix | weight of a nonzero
    codeword |
| CSS code | one side's checks | the other side's checks | weight of an X-type or Z-type logical
    operator |
| general stabilizer code | the **symplectic transpose** of the generators | the generators
    themselves | Pauli weight (the two halves together) |

The last class works because the symplectic inner product is `⟨g, v⟩ = (J g) ⬝ᵥ v` (the
matrix `J` swaps the `Z` half with the `X` half), so commuting with all generators is the
same as lying in the row orthogonal complement of `J`, that is, in `ker J`.

## Main results

* `DualWitness`: the dual-witness certificate structure, with
  `DualWitness.not_mem_rowSpace` as the conclusion the kernel checks.
* `exists_dualWitness_iff`: **the certificate is complete**: `E ∉ certificateRowSpace` is equivalent
  to the existence of a dual witness.
* `minWeight_le_of_witness`: **the upper-bound theorem**: one concrete artefact gives an
  upper bound on the code distance.
* `le_minWeight_of_lower`: **the lower-bound theorem**: a per-operator lower bound gives a
  lower bound on the code distance.
* `eq_minWeight_of_bounds`: **the exact distance**: the two sides together give a distance
  exactly equal to $d$.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## Dual witnesses -/

/-- **Dual witness**: orthogonal to (commuting with) every row of the parity-check matrix
`H`, while pairing to 1 with `E`.

Two entries, each checkable on its own: the first says that it commutes with every check
and the second that it anticommutes with `E`. Together they prove that `E` is not an
element of the stabilizer group, which is the smallest certificate for the judgement that
`E` is a logical operator. -/
structure DualWitness {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (E : Vec n) where
  /-- The witness vector. -/
  w : Vec n
  /-- Orthogonal to every check row. -/
  mem_ker : w ∈ LinearMap.ker H.toLin'
  /-- Pairs to 1 with the target operator (that is, anticommutes over GF(2)). -/
  pairing : w ⬝ᵥ E = 1

/-- **Certificate soundness**: holding a dual witness proves that `E` is not in the
parity-check row space, hence that it is a logical operator. -/
theorem DualWitness.not_mem_rowSpace {m : ℕ} {H : Matrix (Fin m) (Fin n) (ZMod 2)} {E : Vec n}
    (hw : DualWitness H E) : E ∉ H.certificateRowSpace :=
  (not_mem_rowspace_iff_exists_mem_ker H E).mpr ⟨hw.w, hw.mem_ker, hw.pairing⟩

/-- **Certificate completeness**: `E` is not in the row space if and only if a dual
witness exists.

Completeness is LeanQEC's `not_mem_rowspace_iff_exists_mem_ker`; this package wraps its
existential output in the shape of a checkable certificate. -/
theorem exists_dualWitness_iff {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (E : Vec n) :
    (∃ _ : DualWitness H E, True) ↔ E ∉ H.certificateRowSpace := by
  constructor
  · rintro ⟨hw, -⟩; exact hw.not_mem_rowSpace
  · intro hE
    obtain ⟨w, hker, hpair⟩ := (not_mem_rowspace_iff_exists_mem_ker H E).mp hE
    exact ⟨⟨w, hker, hpair⟩, trivial⟩

/-! ## The two-sided characterization of the code distance -/

/-- The set of undetectable nontrivial operators: orthogonal to every row of `M₁` but not
an element of the row space of `M₂`.

`ker M₁ \ certificateRowSpace M₂` is exactly the space of logical operators modulo stabilizers:
operators that are not detected and are yet not elements of the stabilizer group, so they
really do flip the logic. The `@[reducible]` marker lets instance search unfold this
definition for the `Set.toFinset` uses below. -/
@[reducible] def undetectableSet {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) : Set (Vec n) :=
  (↑(LinearMap.ker M₁.toLin') : Set (Vec n)) \ (↑M₂.certificateRowSpace : Set (Vec n))

/-- **The code distance**: LeanQEC's `minWeightKernelOutsideRowSpace` (the least weight of
an undetectable nontrivial operator, taking the value `n + 1` when the set is empty),
specialized to the diagonal case in which the parity-check matrix and the row space are
one and the same.

It is **literally the same** as the upstream definition, so the conclusions of this module
feed straight back into the LeanQEC distance reduction chain. For the general
two-matrix case, use `minWeightKernelOutsideRowSpace` directly. -/
noncomputable abbrev codeDistance {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  minWeightKernelOutsideRowSpace H H

/-- An undetectable nontrivial operator of weight `d₀` puts `d₀` among the values over
which the minimum is taken. -/
lemma mem_image_hammingNorm_of_witness {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {E : Vec n} {d₀ : ℕ} (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace)
    (hw : hammingNorm E = d₀) :
    d₀ ∈ Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset := by
  rw [Finset.mem_image]
  exact ⟨E, by rw [Set.mem_toFinset]; exact ⟨hker, hnot⟩, hw⟩

/-- **The upper-bound theorem**: if an undetectable nontrivial operator of weight `d₀`
exists, then the code distance is at most `d₀`.

This is the witness upper bound: the certificate is a concrete low-weight logical
operator, and the kernel only has to check the three assertions `E ∈ ker M₁`,
`E ∉ certificateRowSpace M₂` and `hammingNorm E = d₀`. -/
theorem minWeight_le_of_witness {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2))
    {E : Vec n} {d₀ : ℕ} (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace)
    (hw : hammingNorm E = d₀) :
    minWeightKernelOutsideRowSpace M₁ M₂ ≤ d₀ := by
  have hmem := mem_image_hammingNorm_of_witness M₁ M₂ hker hnot hw
  have hle : Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset)
      ≤ (d₀ : WithTop ℕ) := Finset.min_le hmem
  unfold minWeightKernelOutsideRowSpace
  change (match Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) with
    | none => n + 1
    | some a => a) ≤ d₀
  split
  · rename_i htop
    have hempty : Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset = ∅ :=
      Finset.min_eq_top.mp
        (show (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset).min = ⊤ from htop)
    rw [hempty] at hmem
    simp at hmem
  · rename_i a ha
    rw [ha] at hle
    exact WithTop.coe_le_coe.mp hle

/-- **The lower-bound theorem**: if every undetectable nontrivial operator has weight at
least `d₀`, then the code distance is at least `d₀`.

The lower-bound side admits no short certificate unless there is a structural argument,
which is why LeanQEC reduces to SAT and UNSAT; this theorem provides the common interface
at which a lower-bound result and an upper-bound witness meet. For a computable
certificate on the lower-bound side see `QECCertificates.GF2.LowerBound`. -/
theorem le_minWeight_of_lower {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {d₀ : ℕ}
    (hd : d₀ ≤ n)
    (h : ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.certificateRowSpace → d₀ ≤ hammingNorm E) :
    d₀ ≤ minWeightKernelOutsideRowSpace M₁ M₂ := by
  unfold minWeightKernelOutsideRowSpace
  change d₀ ≤ (match Finset.min (Finset.image hammingNorm (undetectableSet M₁ M₂).toFinset) with
    | none => n + 1
    | some a => a)
  split
  · exact Nat.le_trans hd (Nat.le_succ n)
  · rename_i a ha
    have hmem := Finset.mem_of_min ha
    rw [Finset.mem_image] at hmem
    obtain ⟨E, hE, hEw⟩ := hmem
    rw [Set.mem_toFinset] at hE
    rw [← hEw]
    exact h E hE.1 hE.2

/-- **The exact distance (the two sides together)**: equal lower and upper bounds give a
distance exactly equal to $d$.

This is the formal skeleton of an exact-distance assertion: the lower bound is proved in
the kernel (or reduced through SAT and LRAT) and the upper bound is supplied by a concrete
low-weight logical operator. -/
theorem eq_minWeight_of_bounds {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {d₀ : ℕ}
    (hd : d₀ ≤ n) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace) (hw : hammingNorm E =
      d₀)
    (hlower : ∀ F, F ∈ LinearMap.ker M₁.toLin' → F ∉ M₂.certificateRowSpace → d₀ ≤ hammingNorm F) :
    minWeightKernelOutsideRowSpace M₁ M₂ = d₀ :=
  le_antisymm (minWeight_le_of_witness M₁ M₂ hker hnot hw) (le_minWeight_of_lower M₁ M₂ hd hlower)

end QECCertificates
