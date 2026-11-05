/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.SequenceLaw
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.Sigma

/-!
# Finite

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Finite infrared cutoff increments

This module contains only the finite part of the infrared construction.  The
lower-infinite cutoff is not defined here: `finiteLowerCutoff m q` is the
honest truncation over `(m - q, m]` and will later be sent to the lower
infinite limit on the full-measure carrier.
-/

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The canonical sample carrier for the integer-indexed shell sequence. -/
abbrev ShellSeq (d : ℕ) :=
  ℤ → Algsuperdiff.Frozen.Assumptions.ShellField d

/-- The regular coefficient-field realization of one shell coordinate. -/
def shellReg (omega : ShellSeq d) (n : ℤ) : RegCoeffField d :=
  Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell (omega n)

/-- One shell coordinate, realized as a regular coefficient field, is
measurable on the canonical sequence carrier. -/
theorem measurable_shellReg (n : ℤ) :
    Measurable (fun omega : ShellSeq d => shellReg omega n) :=
  Algsuperdiff.Frozen.Assumptions.ShellField.measurable_forgetShell.comp
    (measurable_pi_apply n)

/-- The finite stream increment `\mathbf{k}_m-\mathbf{k}_n`, namely the
literal sum of shells with indices in `(n,m]`. -/
def finiteShellIncrement (omega : ShellSeq d) (n m : ℤ) : RegCoeffField d :=
  ∑ k ∈ Finset.Ioc n m, shellReg omega k

/-- Matrix-valued evaluation formula for a finite stream increment. -/
@[simp]
theorem finiteShellIncrement_apply (omega : ShellSeq d) (n m : ℤ) (x : Vec d) :
    finiteShellIncrement omega n m x =
      ∑ k ∈ Finset.Ioc n m, shellReg omega k x := by
  simp [finiteShellIncrement, RegCoeffField.finset_sum_apply]

/-- Entrywise evaluation formula for a finite stream increment. -/
@[simp]
theorem finiteShellIncrement_apply_entry (omega : ShellSeq d) (n m : ℤ)
    (x : Vec d) (i j : Fin d) :
    finiteShellIncrement omega n m x i j =
      ∑ k ∈ Finset.Ioc n m, omega k x i j := by
  rw [finiteShellIncrement_apply]
  simp only [Matrix.sum_apply]
  rfl

/-- Finite stream increments are measurable as regular coefficient fields. -/
theorem measurable_finiteShellIncrement (n m : ℤ) :
    Measurable (fun omega : ShellSeq d => finiteShellIncrement omega n m) := by
  unfold finiteShellIncrement
  exact Finset.measurable_sum _ fun k _ => measurable_shellReg k

/-- Every finite stream increment is antisymmetric. -/
theorem finiteShellIncrement_skew (omega : ShellSeq d) (n m : ℤ) (x : Vec d) :
    (finiteShellIncrement omega n m x).transpose = -finiteShellIncrement omega n m x := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, finiteShellIncrement_apply_entry]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact Algsuperdiff.Frozen.Assumptions.ShellField.skew_entry (omega k) x j i

/-- The finite lower truncation of the manuscript cutoff at scale `m`: the
sum over `(m-q,m]`.  It is finite data, not a lower-infinite replacement. -/
def finiteLowerCutoff (m : ℤ) (q : ℕ) (omega : ShellSeq d) : RegCoeffField d :=
  finiteShellIncrement omega (m - (q : ℤ)) m

/-- Matrix-valued evaluation formula for the finite lower truncation. -/
@[simp]
theorem finiteLowerCutoff_apply (m : ℤ) (q : ℕ) (omega : ShellSeq d) (x : Vec d) :
    finiteLowerCutoff m q omega x =
      ∑ k ∈ Finset.Ioc (m - (q : ℤ)) m, shellReg omega k x := by
  simp [finiteLowerCutoff]

/-- Entrywise evaluation formula for the finite lower truncation. -/
@[simp]
theorem finiteLowerCutoff_apply_entry (m : ℤ) (q : ℕ) (omega : ShellSeq d)
    (x : Vec d) (i j : Fin d) :
    finiteLowerCutoff m q omega x i j =
      ∑ k ∈ Finset.Ioc (m - (q : ℤ)) m, omega k x i j := by
  simp [finiteLowerCutoff]

/-- Finite lower truncations are measurable as regular coefficient fields. -/
theorem measurable_finiteLowerCutoff (m : ℤ) (q : ℕ) :
    Measurable (fun omega : ShellSeq d => finiteLowerCutoff m q omega) :=
  measurable_finiteShellIncrement (m - (q : ℤ)) m

/-- Reindexing `(m-q,m]` in descending order. -/
private theorem ioc_eq_range_desc (m : ℤ) (q : ℕ) :
    Finset.Ioc (m - (q : ℤ)) m =
      (Finset.range q).map ⟨fun r : ℕ => m - (r : ℤ), by
        intro a b hab
        have hab' : (a : ℤ) = (b : ℤ) := by
          linarith
        exact_mod_cast hab'⟩ := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hk : 0 ≤ m - k := by omega
    have htoNat : ((m - k).toNat : ℤ) = m - k := Int.toNat_of_nonneg hk
    refine ⟨(m - k).toNat, ?_, ?_⟩
    · have h2 : ((m - k).toNat : ℤ) < (q : ℤ) := by omega
      exact_mod_cast h2
    · change m - ((m - k).toNat : ℤ) = k
      rw [htoNat]
      ring
  · rintro ⟨r, hr, rfl⟩
    have hr' : (r : ℤ) < (q : ℤ) := by exact_mod_cast hr
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := by exact_mod_cast Nat.zero_le r
    change m - (q : ℤ) < m - (r : ℤ) ∧ m - (r : ℤ) ≤ m
    constructor
    · linarith
    · linarith

/-- The finite lower cutoff is the descending partial sum
`\sum_{r < q} \mathbf j_{m-r}`. -/
theorem finiteLowerCutoff_eq_sum_range_desc (m : ℤ) (q : ℕ) (omega : ShellSeq d) :
    finiteLowerCutoff m q omega =
      ∑ r ∈ Finset.range q, shellReg omega (m - (r : ℤ)) := by
  rw [finiteLowerCutoff, finiteShellIncrement, ioc_eq_range_desc, Finset.sum_map]
  rfl

/-- Entrywise descending-partial-sum formula for the finite lower cutoff. -/
theorem finiteLowerCutoff_apply_entry_eq_sum_range_desc (m : ℤ) (q : ℕ)
    (omega : ShellSeq d) (x : Vec d) (i j : Fin d) :
    finiteLowerCutoff m q omega x i j =
      ∑ r ∈ Finset.range q, omega (m - (r : ℤ)) x i j := by
  rw [finiteLowerCutoff_apply_entry, ioc_eq_range_desc, Finset.sum_map]
  rfl

end

end Algsuperdiff.Section3.Cutoff
