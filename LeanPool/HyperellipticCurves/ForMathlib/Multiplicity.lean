/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.Ideal
public import Mathlib.RingTheory.ChainOfDivisors
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# General facts about `emultiplicity` of ideals

Mathlib-gap lemmas about `emultiplicity` for ideals: invariance under a ring automorphism, and,
in a Dedekind domain, the multiplicity of one maximal ideal in another (`0` for distinct maximal
ideals) and of a proper nonzero ideal in itself (`1`).
-/

@[expose] public section

namespace Ideal

/-- `emultiplicity` of ideals is invariant under a ring automorphism. -/
theorem emultiplicity_map_ringEquiv {R : Type*} [CommRing R] (σ : R ≃+* R) (I J : Ideal R) :
    emultiplicity (Ideal.map σ I) (Ideal.map σ J) = emultiplicity I J := by
  exact emultiplicity_map_eq (Ideal.mapMulEquiv σ)

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Distinct maximal ideals of a Dedekind domain do not divide one another. -/
theorem emultiplicity_eq_zero_of_isMaximal_of_ne {P Q : Ideal R} (hP : P.IsMaximal)
    (hQ : Q.IsMaximal) (hne : Q ≠ P) : emultiplicity P Q = 0 :=
  emultiplicity_eq_zero.mpr fun hdvd ↦ hne (hQ.eq_of_le hP.ne_top (Ideal.dvd_iff_le.mp hdvd))

/-- A proper nonzero ideal of a Dedekind domain occurs in itself with multiplicity one. -/
theorem emultiplicity_self_of_ne_top {P : Ideal R} (hP : P ≠ ⊤) (h0 : P ≠ ⊥) :
    emultiplicity P P = 1 :=
  (finiteMultiplicity hP h0).emultiplicity_self

end Ideal

end
