/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.ClassValue
public import LeanPool.KloostermanWeil.Carlitz.ConjugateDecomposition
public import Mathlib.FieldTheory.Separable


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Conjugacy-class ghost sums

Conjugate polynomial classes and ghost sums used in the Carlitz recurrence. The
extension-sum method is from Carlitz (1969); the class decomposition is formalized
here.
-/

@[expose] public section

namespace KloostermanWeil.Carlitz

open Polynomial

lemma conjCarrier_card_eq_minpoly_natDegree
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    (c : ConjRootClass (Fp p) (Ext p n))
    [Fintype c.carrier] :
    Fintype.card c.carrier = c.minpoly.natDegree := by
  let e : c.carrier ≃ c.minpoly.rootSet (Ext p n) := {
    toFun x := ⟨x.1, by
      rw [c.rootSet_minpoly_eq_carrier]
      exact x.2⟩
    invFun x := ⟨x.1, by
      rw [← c.rootSet_minpoly_eq_carrier]
      exact x.2⟩
    left_inv x := by apply Subtype.ext; rfl
    right_inv x := by apply Subtype.ext; rfl
  }
  calc
    Fintype.card c.carrier =
        Fintype.card (c.minpoly.rootSet (Ext p n)) :=
      Fintype.card_congr e
    _ = c.minpoly.natDegree :=
      Polynomial.card_rootSet_eq_natDegree
        c.separable_minpoly c.splits_minpoly

lemma minpoly_eq_class_minpoly
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    {c : ConjRootClass (Fp p) (Ext p n)}
    (y : c.carrier) :
    minpoly (Fp p) (y : Ext p n) = c.minpoly := by
  have hy : ConjRootClass.mk (Fp p) (y : Ext p n) = c :=
    ConjRootClass.mem_carrier.mp y.2
  calc
    minpoly (Fp p) (y : Ext p n) =
        (ConjRootClass.mk (Fp p) (y : Ext p n)).minpoly := by
      symm
      exact ConjRootClass.minpoly_mk (K := Fp p) (y : Ext p n)
    _ = c.minpoly := congrArg ConjRootClass.minpoly hy

lemma relative_finrank_eq_total_div_classDegree
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    {c : ConjRootClass (Fp p) (Ext p n)}
    (y : c.carrier) :
    Module.finrank
        (IntermediateField.adjoin (Fp p) ({(y : Ext p n)} : Set (Ext p n)))
        (Ext p n) =
      n / c.minpoly.natDegree := by
  let M :=
    IntermediateField.adjoin (Fp p) ({(y : Ext p n)} : Set (Ext p n))
  have hyint : IsIntegral (Fp p) (y : Ext p n) :=
    IsIntegral.of_finite (Fp p) (y : Ext p n)
  have hbase :
      Module.finrank (Fp p) M = c.minpoly.natDegree := by
    calc
      Module.finrank (Fp p) M =
          (minpoly (Fp p) (y : Ext p n)).natDegree :=
        IntermediateField.adjoin.finrank hyint
      _ = c.minpoly.natDegree := by
        rw [minpoly_eq_class_minpoly p n y]
  have htotal :
      Module.finrank (Fp p) (Ext p n) = n :=
    GaloisField.finrank p (NeZero.ne n)
  have hdegpos : 0 < c.minpoly.natDegree := by
    rw [← minpoly_eq_class_minpoly p n y]
    exact minpoly.natDegree_pos hyint
  have hbase0 : Module.finrank (Fp p) M ≠ 0 := by
    rw [hbase]
    exact hdegpos.ne'
  have hcancel :=
    Module.finrank_div_finrank_cancel_left
      (Fp p) M (Ext p n) hbase0
  calc
    Module.finrank M (Ext p n) =
        Module.finrank (Fp p) (Ext p n) /
          Module.finrank (Fp p) M := hcancel.symm
    _ = n / c.minpoly.natDegree := by
      rw [htotal, hbase]



noncomputable def classGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) : ℂ := by
  classical
  letI : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  letI := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  exact ∑ c : ConjRootClass (Fp p) (Ext p n),
    if c = 0 then 0
    else (c.minpoly.natDegree : ℂ) *
      KloostermanWeil.Dickson.etaPoly p t c.minpoly ^
        (n / c.minpoly.natDegree)

theorem Kext_eq_classGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) :
    Kext p n t = classGhost p n t := by
  classical
  let := Fintype.ofFinite (Ext p n)
  let : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  let := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  unfold Kext classGhost
  rw [sum_eq_sum_conjRootClass
    (F := Fp p) (L := Ext p n) (M := ℂ)]
  apply Fintype.sum_congr
  intro c
  by_cases hc : c = 0
  · subst c
    rw [ite_eq_left rfl]
    apply Fintype.sum_eq_zero
    intro y
    have hy0 : (y : Ext p n) = 0 :=
      (ConjRootClass.mk_eq_zero_iff (K := Fp p) (y : Ext p n)).mp y.2
    simp [hy0]
  · rw [ite_eq_right hc]
    calc
      (∑ y : c.carrier,
          if (y : Ext p n) = 0 then 0
          else psiExt p n
            ((y : Ext p n) +
              algebraMap (Fp p) (Ext p n) t * (y : Ext p n)⁻¹)) =
        ∑ _y : c.carrier,
          KloostermanWeil.Dickson.etaPoly p t c.minpoly ^
            (n / c.minpoly.natDegree) := by
          apply Fintype.sum_congr
          intro y
          have hyne : (y : Ext p n) ≠ 0 := by
            intro hy0
            have hyc :
                ConjRootClass.mk (Fp p) (y : Ext p n) = c :=
              ConjRootClass.mem_carrier.mp y.2
            rw [hy0, ConjRootClass.mk_zero] at hyc
            exact hc hyc.symm
          rw [ite_eq_right hyne]
          rw [psiExt_carlitz_arg_eq_etaPoly_pow p n t hyne]
          rw [minpoly_eq_class_minpoly p n y]
          rw [relative_finrank_eq_total_div_classDegree p n y]
      _ =
        (c.minpoly.natDegree : ℂ) *
          KloostermanWeil.Dickson.etaPoly p t c.minpoly ^
            (n / c.minpoly.natDegree) := by
          rw [← conjCarrier_card_eq_minpoly_natDegree p n c]
          simp [nsmul_eq_mul]


end KloostermanWeil.Carlitz
