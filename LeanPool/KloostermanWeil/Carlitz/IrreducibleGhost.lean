/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.RelevantIrreducibles


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Irreducible-class ghost sums

Expresses the extension sum using irreducible polynomial classes, in the Carlitz
(1969) recurrence framework.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial

noncomputable def irredGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) : ℂ := by
  classical
  letI : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  letI := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  letI : Fintype (RelevantIrred p n) :=
    Fintype.ofEquiv
      (ConjRootClass (Fp p) (Ext p n))
      (classRelevantEquiv p n)
  exact ∑ P : RelevantIrred p n,
    (P.1.natDegree : ℂ) *
      KloostermanWeil.Dickson.etaPoly p t P.1 ^
        (n / P.1.natDegree)

lemma minpoly_zero_class_eq_X
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    (0 : ConjRootClass (Fp p) (Ext p n)).minpoly =
      (X : Polynomial (Fp p)) := by
  change minpoly (Fp p) (0 : Ext p n) = X
  simp

theorem classGhost_eq_irredGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) :
    classGhost p n t = irredGhost p n t := by
  classical
  let : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  let := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  let e := classRelevantEquiv p n
  let : Fintype (RelevantIrred p n) :=
    Fintype.ofEquiv
      (ConjRootClass (Fp p) (Ext p n)) e
  unfold classGhost irredGhost
  refine Fintype.sum_equiv e
    (fun c : ConjRootClass (Fp p) (Ext p n) =>
      if c = 0 then (0 : ℂ)
      else (c.minpoly.natDegree : ℂ) *
        KloostermanWeil.Dickson.etaPoly p t c.minpoly ^
          (n / c.minpoly.natDegree))
    (fun P : RelevantIrred p n =>
      (P.1.natDegree : ℂ) *
        KloostermanWeil.Dickson.etaPoly p t P.1 ^
          (n / P.1.natDegree)) ?_
  intro c
  change
    (if c = 0 then (0 : ℂ)
      else (c.minpoly.natDegree : ℂ) *
        KloostermanWeil.Dickson.etaPoly p t c.minpoly ^
          (n / c.minpoly.natDegree)) =
      (c.minpoly.natDegree : ℂ) *
        KloostermanWeil.Dickson.etaPoly p t c.minpoly ^
          (n / c.minpoly.natDegree)
  by_cases hc : c = 0
  · subst c
    rw [ite_eq_left rfl, minpoly_zero_class_eq_X p n]
    simp [KloostermanWeil.Dickson.etaPoly, NeZero.ne n]
  · rw [ite_eq_right hc]

theorem Kext_eq_irredGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) :
    Kext p n t = irredGhost p n t := by
  rw [Kext_eq_classGhost, classGhost_eq_irredGhost]


end KloostermanWeil.Carlitz
