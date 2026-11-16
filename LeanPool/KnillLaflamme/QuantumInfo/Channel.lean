/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite-dimensional quantum channels (Kraus form)

A **quantum channel** `Φ : Matrix n n ℂ → Matrix m m ℂ` in **Kraus form**: a finite family
of Kraus operators `Kᵢ : Matrix m n ℂ` with the **trace-preserving** constraint
`∑ᵢ Kᵢᴴ Kᵢ = 1`, acting by `Φ(ρ) = ∑ᵢ Kᵢ ρ Kᵢᴴ`.

This file establishes the type and the core properties: the action is linear,
**trace-preserving** (`apply_trace`), **positive** (`apply_posSemidef`), and
**Hermiticity-preserving** (`apply_isHermitian`) — so a channel maps density operators to density
operators. Complete positivity is not stated here: every map in Kraus form is completely positive,
and nothing in this repository needs the statement.

The Kraus index `ι` is an arbitrary `Fintype`.

*Provenance:* copied from csd-lean4 (`zblore/csd-lean4`, commit `db586e88`), file
`CsdLean4/Mathlib/QuantumInfo/Channel.lean`. It imports only Mathlib, so no import changed. The
code is unchanged. The comments were edited for this repository to remove csd-lean4's internal
notes and references to files that are not here. The adjoint lemmas and `Channel.id` are not used
by the theorem.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace QuantumInfo

/-- A finite-dimensional **quantum channel** in Kraus form: Kraus operators `kraus i` with
the trace-preserving (TP) constraint `∑ᵢ (kraus i)ᴴ (kraus i) = 1`. The action is
`apply ρ = ∑ᵢ (kraus i) ρ (kraus i)ᴴ`. -/
structure Channel (n m ι : Type*) [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n] where
  /-- The Kraus operators `Kᵢ : ℂⁿ → ℂᵐ`. -/
  kraus : ι → Matrix m n ℂ
  /-- Trace preservation: `∑ᵢ Kᵢᴴ Kᵢ = 1`. -/
  tp : (∑ i : ι, (kraus i)ᴴ * (kraus i) : Matrix n n ℂ) = 1

namespace Channel

variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n]

/-- The action of a channel on an operator: `Φ(ρ) = ∑ᵢ Kᵢ ρ Kᵢᴴ`. -/
noncomputable def apply (Φ : Channel n m ι) (ρ : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ i : ι, Φ.kraus i * ρ * (Φ.kraus i)ᴴ

/-- The channel action, unfolded to its Kraus sum. **Not `@[simp]`**: as a head unfolder it would
rewrite every `Φ.apply ρ` before more specific closed forms such as `id_apply` could fire. Use it
explicitly when the sum is what you want. -/
lemma apply_def (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    Φ.apply ρ = ∑ i : ι, Φ.kraus i * ρ * (Φ.kraus i)ᴴ := rfl

/-- The channel action is additive. -/
lemma apply_add (Φ : Channel n m ι) (ρ σ : Matrix n n ℂ) :
    Φ.apply (ρ + σ) = Φ.apply ρ + Φ.apply σ := by
  simp only [apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

/-- The channel action commutes with scalar multiplication. -/
lemma apply_smul (Φ : Channel n m ι) (c : ℂ) (ρ : Matrix n n ℂ) :
    Φ.apply (c • ρ) = c • Φ.apply ρ := by
  simp only [apply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- **Trace preservation.** `Tr(Φ ρ) = Tr ρ` — the defining TP property, from
`∑ᵢ Kᵢᴴ Kᵢ = 1` and trace cyclicity. -/
lemma apply_trace (Φ : Channel n m ι) (ρ : Matrix n n ℂ) :
    (Φ.apply ρ).trace = ρ.trace := by
  simp only [apply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (Φ.kraus _) ρ (Φ.kraus _)ᴴ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, Φ.tp, Matrix.one_mul]

/-- **Positivity.** A channel maps positive-semidefinite operators to positive-semidefinite
operators: each `Kᵢ ρ Kᵢᴴ` is PSD, and PSD is closed under finite sums. -/
lemma apply_posSemidef (Φ : Channel n m ι) {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (Φ.apply ρ).PosSemidef := by
  rw [apply]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero (fun i _ => ?_)
  exact hρ.mul_mul_conjTranspose_same (Φ.kraus i)

/-- A channel preserves Hermiticity. -/
lemma apply_isHermitian (Φ : Channel n m ι) {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    (Φ.apply ρ).IsHermitian := by
  unfold Matrix.IsHermitian apply
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hρ.eq, Matrix.mul_assoc]

/-- The channel action is **subtractive** (linearity in the input). -/
lemma apply_sub (Φ : Channel n m ι) (ρ σ : Matrix n n ℂ) :
    Φ.apply (ρ - σ) = Φ.apply ρ - Φ.apply σ := by
  simp only [apply, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

/-! ## The channel adjoint (Heisenberg dual)

For `Φ(ρ) = ∑ᵢ Kᵢ ρ Kᵢᴴ` the **adjoint** (dual / Heisenberg) map is `Φ†(P) = ∑ᵢ Kᵢᴴ P Kᵢ`,
characterised by the trace duality `Tr(P · Φ ρ) = Tr(Φ† P · ρ)`. The TP constraint
`∑ᵢ Kᵢᴴ Kᵢ = 1` makes `Φ†` **unital** (`Φ† 1 = 1`); together with positivity this gives
`0 ≤ Φ† P ≤ I` whenever `0 ≤ P ≤ I`. -/

/-- The **adjoint** (Heisenberg dual) of a channel: `Φ†(P) = ∑ᵢ Kᵢᴴ P Kᵢ`. -/
noncomputable def adjoint (Φ : Channel n m ι) (P : Matrix m m ℂ) : Matrix n n ℂ :=
  ∑ i : ι, (Φ.kraus i)ᴴ * P * (Φ.kraus i)

@[simp] lemma adjoint_def (Φ : Channel n m ι) (P : Matrix m m ℂ) :
    Φ.adjoint P = ∑ i : ι, (Φ.kraus i)ᴴ * P * (Φ.kraus i) := rfl

/-- **The adjoint is unital:** `Φ† 1 = 1`, directly from the TP constraint `∑ᵢ Kᵢᴴ Kᵢ = 1`. -/
lemma adjoint_unital [DecidableEq m] (Φ : Channel n m ι) : Φ.adjoint 1 = 1 := by
  rw [adjoint]
  simp only [Matrix.mul_one]
  exact Φ.tp

/-- **The adjoint preserves positive-semidefiniteness:** each `Kᵢᴴ P Kᵢ` is PSD and PSD is
closed under finite sums. -/
lemma adjoint_posSemidef (Φ : Channel n m ι) {P : Matrix m m ℂ} (hP : P.PosSemidef) :
    (Φ.adjoint P).PosSemidef := by
  rw [adjoint]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero (fun i _ => ?_)
  exact hP.conjTranspose_mul_mul_same (Φ.kraus i)

/-- The adjoint is **subtractive** (linearity in `P`). -/
lemma adjoint_sub (Φ : Channel n m ι) (P Q : Matrix m m ℂ) :
    Φ.adjoint (P - Q) = Φ.adjoint P - Φ.adjoint Q := by
  simp only [adjoint, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

/-- The adjoint is **additive** (linearity in `P`). -/
lemma adjoint_add (Φ : Channel n m ι) (P Q : Matrix m m ℂ) :
    Φ.adjoint (P + Q) = Φ.adjoint P + Φ.adjoint Q := by
  simp only [adjoint, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

/-- **`0 ≤ P ≤ I ⟹ 0 ≤ Φ† P ≤ I`** (the upper half): unitality +
subtractivity give `1 − Φ† P = Φ† (1 − P)`, PSD by `adjoint_posSemidef`. -/
lemma adjoint_le_one [DecidableEq m] (Φ : Channel n m ι) {P : Matrix m m ℂ}
    (_hP : P.PosSemidef) (hP' : ((1 : Matrix m m ℂ) - P).PosSemidef) :
    ((1 : Matrix n n ℂ) - Φ.adjoint P).PosSemidef := by
  rw [← Φ.adjoint_unital, ← Φ.adjoint_sub]
  exact Φ.adjoint_posSemidef hP'

/-- **Adjoint (trace) duality:** `Tr(P · Φ ρ) = Tr(Φ† P · ρ)`. The defining property of the
adjoint, via trace cyclicity rotating `Kᵢᴴ` to the front of each summand. -/
lemma adjoint_trace_mul (Φ : Channel n m ι) (P : Matrix m m ℂ) (ρ : Matrix n n ℂ) :
    (P * Φ.apply ρ).trace = (Φ.adjoint P * ρ).trace := by
  rw [apply, Finset.mul_sum, Matrix.trace_sum, adjoint, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Tr(P · (Kᵢ ρ) · Kᵢᴴ) = Tr(Kᵢᴴ · P · (Kᵢ ρ)): rotate Kᵢᴴ to the front (cyclicity).
  rw [show P * (Φ.kraus i * ρ * (Φ.kraus i)ᴴ) = P * (Φ.kraus i * ρ) * (Φ.kraus i)ᴴ by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    Matrix.trace_mul_cycle P (Φ.kraus i * ρ) (Φ.kraus i)ᴴ,
    show (Φ.kraus i)ᴴ * P * (Φ.kraus i) * ρ
        = (Φ.kraus i)ᴴ * P * (Φ.kraus i * ρ) by rw [Matrix.mul_assoc]]

/-- The **identity channel** (a single Kraus operator `1`). -/
def id (n : Type*) [Fintype n] [DecidableEq n] : Channel n n PUnit where
  kraus _ := 1
  tp := by simp

@[simp] lemma id_apply (n : Type*) [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) :
    (Channel.id n).apply ρ = ρ := by
  simp [apply, Channel.id]

end Channel
end QuantumInfo
