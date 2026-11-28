/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.AssociatedTrace
public import LeanPool.MathFin.Models.ModelFree.SVI.RealIrreducibles
public import LeanPool.MathFin.Models.ModelFree.SVI.RealRootSignature
public import LeanPool.MathFin.Models.ModelFree.SVI.TraceSignature
public import LeanPool.MathFin.Models.ModelFree.SVI.QuotientProduct
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

/-! # Hermite's trace-form identity

Part of the SVI polynomial-sign certificate (#174).

For `f ≠ 0`, the signature of the weighted trace form on `ℝ[X]/(f)` is the sum of `sign (q c)`
over the distinct real roots `c` of `f` (`weightedTraceForm_signature`), with no squarefreeness
assumed. `hermite_signature` is the same identity for the sign-variation test of the Hermite matrix
`hermite f q f.natDegree`.

## Main results

* `weightedTraceForm_signature`: for `f ≠ 0`, the signature of the weighted trace form on
  `ℝ[X]/(f)` is `∑ c ∈ f.roots.toFinset, sign (q.eval c)`, the sum over distinct real roots.
* `hermite_signature`: for `f ≠ 0`, `signatureTest (hermite f q f.natDegree)` equals the same sum.

## Tags

Hermite quadratic form, real root counting, trace form signature, Sylvester inertia, SVI, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Polynomial

private theorem unit_trace_signature (f q : ℝ[X]) (hf : IsUnit f) :
    formSignature (weightedTraceForm f q).toQuadraticMap = 0 := by
  have hf0 := hf.ne_zero
  let : FiniteDimensional ℝ (AdjoinRoot f) :=
      Module.Finite.of_basis (AdjoinRoot.powerBasis hf0).basis
  have hd : Module.finrank ℝ (AdjoinRoot f) = 0 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim]
    exact natDegree_eq_zero_of_isUnit hf
  have hp := sigPos_le_finrank (weightedTraceForm f q).toQuadraticMap
  have hn := sigPos_le_finrank (-(weightedTraceForm f q).toQuadraticMap)
  rw [hd] at hp hn
  simp [formSignature, ← sigPos_neg, Nat.eq_zero_of_le_zero hp, Nat.eq_zero_of_le_zero hn]

/-- A unit polynomial has no roots. -/
theorem roots_eq_zero_of_isUnit (f : ℝ[X]) (hf : IsUnit f) : f.roots = 0 := by
  apply Multiset.card_eq_zero.mp
  exact Nat.eq_zero_of_le_zero ((card_roots' f).trans_eq (natDegree_eq_zero_of_isUnit hf))

private theorem positiveQuadratic_roots (a b : ℝ) (hb : b ≠ 0) :
    (positiveQuadratic a b).roots = 0 := by
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro c hc
  have h := (mem_roots (by intro h; have := positiveQuadratic_degree a b; simp [h] at this)).mp hc
  have he : (c-a)^2+b^2 = 0 := by simpa [IsRoot, positiveQuadratic] using h
  nlinarith [sq_nonneg (c-a), sq_pos_of_ne_zero hb]

/-- Hermite's trace-form identity, with distinct real roots and without any
squarefreeness hypothesis. -/
theorem weightedTraceForm_signature (f q : ℝ[X]) (hf : f ≠ 0) :
    formSignature (weightedTraceForm f q).toQuadraticMap =
      ∑ c ∈ f.roots.toFinset, sign (q.eval c) := by
  classical
  induction f using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact (hf rfl).elim
  | @h1 f hu => simp [unit_trace_signature f q hu, roots_eq_zero_of_isUnit f hu]
  | @hpr p r hp =>
    by_cases hr : r = 0
    · subst r
      simp only [pow_zero, roots_one]
      exact unit_trace_signature 1 q isUnit_one
    have hrp : 0 < r := Nat.pos_of_ne_zero hr
    have ha := (associated_normalize p).pow_pow (n := r)
    rw [weightedTraceForm_associated_signature _ _ q ha, ha.roots_eq]
    have hi : Irreducible (normalize p) :=
        (associated_normalize p).irreducible_iff.mp hp.irreducible
    rcases monic_real_irreducible_cases (normalize p) (monic_normalize hp.ne_zero) hi with
      ⟨c, hc⟩ | ⟨a,b,hb,hp⟩
    · rw [hc, weightedTraceForm_realRoot_signature c r hrp q]
      simp [roots_pow, roots_X_sub_C, hr]
    · rw [hp, weightedTraceForm_quadratic_signature a b hb r hrp q]
      simp [roots_pow, positiveQuadratic_roots a b hb]
  | @hcp f g hc ihf ihg =>
    have hf0 : f ≠ 0 := left_ne_zero_of_mul hf
    have hg0 : g ≠ 0 := right_ne_zero_of_mul hf
    rw [weightedTraceForm_prod_signature f g q hf0 hg0 hc.isCoprime, ihf hf0, ihg hg0,
      roots_mul hf, Multiset.toFinset_add]
    symm
    apply Finset.sum_union
    apply Finset.disjoint_left.mpr
    intro c hcf hcg
    have hcf := (mem_roots hf0).mp (Multiset.mem_toFinset.mp hcf)
    have hcg := (mem_roots hg0).mp (Multiset.mem_toFinset.mp hcg)
    obtain ⟨u,v,huv⟩ := hc.isCoprime
    have hh := congrArg (eval c) huv
    simp [hcf.eq_zero, hcg.eq_zero] at hh

/-- Concrete companion-matrix form of the distinct-root identity. -/
theorem hermite_signature (f q : ℝ[X]) (hf : f ≠ 0) :
    signatureTest (hermite f q f.natDegree) =
      ∑ c ∈ f.roots.toFinset, sign (q.eval c) := by
  rw [hermite_signature_eq_trace_signature f q hf, weightedTraceForm_signature f q hf]

end SVI
end MathFin
