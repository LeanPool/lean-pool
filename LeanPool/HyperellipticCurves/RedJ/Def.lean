/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.BaseChange
public import LeanPool.HyperellipticCurves.RedJ.RedIdealPrincipal
public import LeanPool.HyperellipticCurves.RedJ.Tower

import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# The reduction map on the Jacobian (`def:redJ`)

For a complete DVR `O` with algebraically closed residue field of characteristic `≠ 2` and
fraction field `K` of characteristic `0`, we define the reduction map
`ChabautyColeman.redJ : J(K) → J(κ_bar)` on the class-group Jacobian of `y² = f(x)`: represent
a class over a finite splitting extension `L` by a split-supported ideal
(`ChabautyColeman.SplitSupported`) and reduce it to the fixed residue curve
(`ChabautyColeman.redIdealBar`). The defining relation is `ChabautyColeman.IsRedJPair`;
totality is `ChabautyColeman.exists_isRedJPair` (Mumford representatives split over the
splitting field of `u`).

This file also glues the principal-kill (`ChabautyColeman.isPrincipal_redIdeal_span`) over
the tower (`ChabautyColeman.isPrincipal_redIdealBar_span`), providing the engine invocation
with the adic topology on `O_L` — the analytic input to `thm:redJ-hom`.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

/-- The maximal ideal of a rational point is split-supported. -/
theorem splitSupported_pointIdeal {F : Type*} [Field F] {g : F[X]} {x y : F}
    (hxy : y ^ 2 = g.eval x) : SplitSupported (pointIdeal g x y) := fun _ hQ _ hle ↦
  ⟨x, y, hxy, ((pointIdeal_isMaximal hxy).eq_of_le hQ.ne_top hle).symm⟩

section Base

variable {K : Type*} [Field K]

/-- Every nonzero polynomial over `K` splits over a finite intermediate field of the
algebraic closure. -/
theorem exists_intermediateField_splits_base (u : K[X]) :
    ∃ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L ∧
      (u.map (algebraMap K L)).Splits :=
  ⟨_, finiteDimensional_adjoin_rootSet u, splits_map_adjoin_rootSet u⟩

end Base

section RedJDef

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type u} [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
  {f : O[X]}
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- **Split principal ideals reduce to principal ideals over the tower**: the glue of
`ChabautyColeman.isPrincipal_redIdeal_span` through `redIdealBar`, providing the adic
topology on `O_L` for the engine. -/
theorem isPrincipal_redIdealBar_span (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    {w : HypRing L ((f.map (algebraMap O K)).map (algebraMap K L))} (hw : w ≠ 0)
    (hsplit : (w.re ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L) * w.im ^ 2).Splits)
    (hsq : ∀ x : L, IsIntegral O x →
      (w.re ^ 2 - (f.map (algebraMap O K)).map (algebraMap K L) * w.im ^ 2).eval x = 0 →
        ∃ b : L, b ^ 2 = ((f.map (algebraMap O K)).map (algebraMap K L)).eval x) :
    (redIdealBar f L (Ideal.span {w})).IsPrincipal := by
  -- the engine's topological pack on `O_L`
  let : WithIdeal (integralClosure O L) := ⟨maximalIdeal (integralClosure O L)⟩
  have hadic : Fact (IsAdic (maximalIdeal (integralClosure O L))) := ⟨rfl⟩
  have hcompl : IsAdicComplete (maximalIdeal (integralClosure O L)) (integralClosure O L) :=
    integralClosure_isAdicComplete_maximalIdeal O K L
  obtain ⟨hcs, ht2⟩ := ((Fact.out :
    IsAdic (maximalIdeal (integralClosure O L))).isAdicComplete_iff).mp hcompl
  have : CompleteSpace (integralClosure O L) := hcs
  have : T2Space (integralClosure O L) := ht2
  -- transport the element and its hypotheses through the index change
  set w' := toClosureIndex f L w with hw'def
  have hre : w'.re = w.re := by rw [hw'def, re_toClosureIndex]
  have him : w'.im = w.im := by rw [hw'def, im_toClosureIndex]
  have hprin : (redIdeal (f.map (algebraMap O (integralClosure O L)))
      (Ideal.span {w'})).IsPrincipal := by
    refine isPrincipal_redIdeal_span (hf.map _) ?_ ?_ ?_ ?_ ?_
    · rwa [hf.natDegree_map]
    · exact isUnit_two_of_neZero_residue
    · intro h0
      obtain ⟨h1, h2⟩ := QuadraticAlgebra.eq_zero_iff.mp h0
      rw [hre] at h1
      rw [him] at h2
      exact hw (QuadraticAlgebra.eq_zero_iff.mpr ⟨h1, h2⟩)
    · rw [hre, him, ← map_algebraMap_integralClosure_eq f L]
      exact hsplit
    · intro x hx h0
      rw [hre, him, ← map_algebraMap_integralClosure_eq f L] at h0
      obtain ⟨b, hb⟩ := hsq x (isIntegral_trans x hx) h0
      exact ⟨b, by rwa [← map_algebraMap_integralClosure_eq f L]⟩
  obtain ⟨a, ha⟩ := hprin.principal
  refine ⟨fromClosureResidue f L a, ?_⟩
  rw [redIdealBar, Ideal.map_span, Set.image_singleton, ← hw'def, ha,
    Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]

open nonZeroDivisors in
/-- The graph of the reduction map on the Jacobian: `r` is a reduction of `c` if some
split-supported representative ideal of `c` over a finite extension has reduction of
class `r`. -/
def IsRedJPair (c : HypJac K (f.map (algebraMap O K)))
    (r : HypJac (ResidueField O) (f.map (residue O))) : Prop :=
  ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
    (I : (Ideal (HypRing L ((f.map (algebraMap O K)).map (algebraMap K L))))⁰),
      SplitSupported I.1 ∧
      HypJac.map (f.map (algebraMap O K)) c = ClassGroup.mk0 I ∧
      r = ClassGroup.mk0 ⟨redIdealBar f L I.1,
        mem_nonZeroDivisors_of_ne_zero (redIdealBar_ne_zero f L _)⟩

open nonZeroDivisors in
/-- **Totality of the reduction relation**: every class has a split-supported Mumford
representative over the splitting field of `u`. -/
theorem exists_isRedJPair (c : HypJac K (f.map (algebraMap O K))) :
    ∃ r, IsRedJPair c r := by
  classical
  obtain ⟨I₀, hI₀⟩ := ClassGroup.mk0_surjective c
  obtain ⟨u, v, hu, hdvd, hmum⟩ := exists_mk0_eq_mk0_mumfordIdeal
    (f.map (algebraMap O K)) I₀.1 I₀.2
  obtain ⟨L, hL, hsplit⟩ := exists_intermediateField_splits_base u
  have hu' := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hu
  have hdvd' : u.map (algebraMap K L) ∣ (v.map (algebraMap K L)) ^ 2
      - (f.map (algebraMap O K)).map (algebraMap K L) := by
    have h := Polynomial.map_dvd (algebraMap K L) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_pow] at h
  set M := mumfordIdeal ((f.map (algebraMap O K)).map (algebraMap K L))
    (u.map (algebraMap K L)) (v.map (algebraMap K L))
  have hM0 : M ≠ 0 :=
    mumfordIdeal_ne_zero ((f.map (algebraMap O K)).map (algebraMap K L)) hu' _
  refine ⟨ClassGroup.mk0 ⟨redIdealBar f L M, mem_nonZeroDivisors_of_ne_zero
      (redIdealBar_ne_zero f L M)⟩, L, hL, ⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩,
    splitSupported_mumfordIdeal hu' hdvd' hsplit, ?_, rfl⟩
  rw [hI₀.symm, hmum, HypJac.map_mk0]
  exact congrArg ClassGroup.mk0 (Subtype.ext (mumfordIdeal_map (f.map (algebraMap O K)) u v))

/-- **The reduction map on the Jacobian** (`def:redJ`): the value of the reduction
relation, via a choice of split-supported representative. Well-definedness (independence
of all choices) is `ChabautyColeman.isRedJPair_unique`. -/
noncomputable def redJ (c : HypJac K (f.map (algebraMap O K))) :
    HypJac (ResidueField O) (f.map (residue O)) :=
  (exists_isRedJPair c).choose

theorem isRedJPair_redJ (c : HypJac K (f.map (algebraMap O K))) : IsRedJPair c (redJ c) :=
  (exists_isRedJPair c).choose_spec

end RedJDef

end ChabautyColeman

end
