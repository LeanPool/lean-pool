/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Defs

/-!
# Formal statements of Theorem 1.1 and Corollary 1.2

The main result of the manuscript and its corollary, as `Prop`-valued definitions stated
separately from their proofs, which are in `FreeField/MainTheorems.lean` (`theorem_1_1`,
`corollary_1_2`).

The statements quantify over every vacuum Weyl system `V : FreeFieldVacuum m H` in every
Hilbert space `H : Type`; by uniqueness of the GNS representation all such systems are
unitarily equivalent, and the Fock representation is one of them.  The existence of a
`FreeFieldVacuum` for every mass `m > 0` (non-vacuity of these statements) is proved in
`FreeField/Existence.lean` (`freeFieldVacuum_exists`).
-/

@[expose] public section

namespace VacuumBellSeparation

/-- **Theorem 1.1 (separation threshold).**  There is a finite constant `C_* > 2`,
independent of `m` and `R`, such that for all `m, R > 0` and `L ≥ C_* R`, the vacuum Bell
correlation `β_m(R, L)` of `𝔄_m(D_R)` and `𝔄_m(D_R + (0, L𝐞₁))` equals `1`. -/
def Theorem_1_1 : Prop :=
  ∃ Cstar : ℝ, 2 < Cstar ∧
    ∀ m R L : ℝ, 0 < m → 0 < R → Cstar * R ≤ L →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (V : FreeFieldVacuum m H), freeFieldBell V R L = 1

/-- **Corollary 1.2 (fixed bounded regions).**  For every `m > 0`, any two bounded regions
`O₁, O₂` and any spacelike vector `a`, the vacuum Bell correlation of `𝔄_m(O₁)` and
`𝔄_m(O₂ + t a)` equals `1` for all sufficiently large `t`. -/
def Corollary_1_2 : Prop :=
  ∀ m : ℝ, 0 < m → ∀ O₁ O₂ : Set Spacetime, Bornology.IsBounded O₁ → Bornology.IsBounded O₂ →
    ∀ a : Spacetime, a.1 ^ 2 < ‖a.2‖ ^ 2 →
      ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
        ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
          (V : FreeFieldVacuum m H),
          bellCorrelation (vectorState V.vacuum V.vacuum_norm) (localAlgebra V O₁)
            (localAlgebra V ((fun x => x + t • a) '' O₂)) = 1

/-- **Lemma 2.1 (dilation)**, in the realization-independent form: for all `m, R, L > 0`, the
Bell correlation `β_m(R, L)` of any vacuum system of mass `m` equals `β_{mR}(1, L/R)` of any
vacuum system of mass `mR`.  (This also contains the independence of `β` from the chosen
vacuum system, i.e. GNS uniqueness.) -/
def Lemma_2_1 : Prop :=
  ∀ m R L : ℝ, 0 < m → 0 < R → 0 < L →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (V : FreeFieldVacuum m H)
      (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (V' : FreeFieldVacuum (m * R) H'),
      freeFieldBell V R L = freeFieldBell V' 1 (L / R)

/-- Non-vacuity: a vacuum Weyl system of the free field of every mass `m > 0`
exists (the Fock vacuum representation). -/
def FreeFieldVacuumExists : Prop :=
  ∀ m : ℝ, 0 < m → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H), Nonempty (FreeFieldVacuum m H)

end VacuumBellSeparation
