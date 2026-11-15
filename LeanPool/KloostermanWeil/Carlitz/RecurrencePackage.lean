/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.GeneratingIdentity


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# The Carlitz spectral recurrence

Derives the quadratic recurrence and its first terms. See Carlitz (1969) and the
two-root formulation in Harcos (2015), introduction (2).
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open PowerSeries
open KloostermanWeil.Dickson

/-- Normalization of the degree-one Carlitz sum. -/
theorem carlitzK1_eq_primeKloosterman
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    Kseq p t 1 = KloostermanWeil.kloostermanSumPrime p t 1 := by
  rw [Kseq_succ, Kext_one_eq_kloostermanSumPrime]

/-- Carlitz three-term recurrence in prime-modulus normalization. -/
theorem carlitz_recurrence
    (p : ℕ) [Fact p.Prime] {t : Fp p} (ht : t ≠ 0) :
    ∀ n : ℕ, 1 ≤ n →
      Kseq p t (n + 2) +
        Kseq p t 1 * Kseq p t (n + 1) +
        (p : ℂ) * Kseq p t n = 0 := by
  exact recurrence_of_generating_identity
    (Kseq p t) (p : ℂ) (carlitz_generating_identity p ht)

/-- Spectral-root representation of the Carlitz recurrence. -/
theorem carlitz_spectral_roots
    (p : ℕ) [Fact p.Prime] {t : Fp p} (ht : t ≠ 0) :
    ∃ α β : ℂ,
      α + β = -Kseq p t 1 ∧
      α * β = (p : ℂ) ∧
      ∀ n : ℕ, 1 ≤ n →
        Kseq p t n = -(α ^ n + β ^ n) := by
  exact exists_spectral_roots_of_generating_identity
    (Kseq p t) (p : ℂ) (carlitz_generating_identity p ht)



/-- Recurrence expressed in strictly positive extension degrees. -/
theorem carlitz_recurrence_Kext
    (p : ℕ) [Fact p.Prime] {t : Fp p} (ht : t ≠ 0) (r : ℕ) :
    Kext p (r + 3) t +
      Kext p 1 t * Kext p (r + 2) t +
      (p : ℂ) * Kext p (r + 1) t = 0 := by
  have h := carlitz_recurrence p ht (r + 1) (by omega)
  simpa [Kseq_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Spectral-root representation in positive extension degrees. -/
theorem carlitz_spectral_roots_Kext
    (p : ℕ) [Fact p.Prime] {t : Fp p} (ht : t ≠ 0) :
    ∃ α β : ℂ,
      α + β = -Kext p 1 t ∧
      α * β = (p : ℂ) ∧
      ∀ r : ℕ,
        Kext p (r + 1) t = -(α ^ (r + 1) + β ^ (r + 1)) := by
  obtain ⟨α, β, hsum, hprod, hpow⟩ :=
    carlitz_spectral_roots p ht
  refine ⟨α, β, ?_, hprod, ?_⟩
  · simpa [Kseq_succ] using hsum
  · intro r
    simpa [Kseq_succ] using hpow (r + 1) (by omega)


end KloostermanWeil.Carlitz
