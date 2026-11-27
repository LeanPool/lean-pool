/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceTomitaPolar
public import LeanPool.VacuumBellSeparation.FreeField.SourceModularOperator

/-!
# The maximal adjoint graph of the physical antilinear Tomita operator

For a conjugate-linear S and a conjugate-first inner product, the adjoint
relation is ⟨Sx,y⟩=⟨S*y,x⟩. We use that universal relation as the definition
of its full graph. The resulting coordinate equation and the full graph
of S*S are proved on the actual physical domain, without inverse notation.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory ContinuousLinearMap Gaussian.HilbertComplexification
open scoped InnerProductSpace ComplexConjugate

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
variable (hU : Bornology.IsBounded U) (hopen : IsOpen U) (hne : U.Nonempty)

/-- Full antilinear adjoint relation, quantified over every actual domain vector. -/
def sourceTomitaAdjointGraph :
    Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)) :=
  {p | ∀ x : (sourceTomita hm U hU).domain,
    inner ℂ (sourceTomita hm U hU x) p.1 = inner ℂ p.2 (x : Lp ℂ 2 (oneParticleMeasure m))}

include hopen hne in
/-- Density makes the universal adjoint relation single-valued. -/
theorem sourceTomitaAdjointGraph_unique {y z w : Lp ℂ 2 (oneParticleMeasure m)}
    (hz : (y, z) ∈ sourceTomitaAdjointGraph hm U hU)
    (hw : (y, w) ∈ sourceTomitaAdjointGraph hm U hU) : z = w := by
  apply (sourceTomita_dense_domain hm U hU hopen hne).eq_of_inner_left ℂ
  intro x hx
  exact (hz ⟨x, hx⟩).symm.trans (hw ⟨x, hx⟩)

private theorem sourceConjugation_inner_swap (x y : ComplexSourceHilbert hm U) :
    inner ℂ (conjugation x) y = inner ℂ (conjugation y) x := by
  calc
    _ = conj (inner ℂ x (conjugation y)) := by
      simpa only [conjugation_conjugation] using sourceConjugation_inner x (conjugation y)
    _ = _ := inner_conj_symm _ _

/-- The full adjoint graph is exactly the weak bounded-root equation. -/
theorem sourceTomitaAdjointGraph_polar_iff (y z : ComplexSourceHilbert hm U) :
    (sourcePolarUnitary hm U hU hopen hne y,
      sourcePolarUnitary hm U hU hopen hne z) ∈ sourceTomitaAdjointGraph hm U hU ↔
        conjugateSourceGramRoot hm U (conjugation y) = sourceGramRoot hm U z := by
  constructor
  · intro h
    apply ext_inner_right ℂ
    intro v
    have hh := h (sourceRangeEquiv hm U hU v)
    rw [sourceTomita_polar_action hm U hU hopen hne, sourceRangeEquiv_apply,
      ← sourcePolarUnitary_sqrt_gram hm U hU hopen hne,
      LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map] at hh
    calc
      _ = inner ℂ (conjugation y) (conjugateSourceGramRoot hm U v) :=
        (CFC.sqrt_nonneg (conjugateSourceGram hm U)).isSelfAdjoint.isSymmetric _ _
      _ = inner ℂ (conjugation (conjugateSourceGramRoot hm U v)) y :=
        sourceConjugation_inner_swap hm U _ _
      _ = inner ℂ z (sourceGramRoot hm U v) := hh
      _ = _ := ((CFC.sqrt_nonneg (sourceGram hm U)).isSelfAdjoint.isSymmetric _ _).symm
  · intro heq x
    let v := (sourceRangeEquiv hm U hU).symm x
    have hx : x = sourceRangeEquiv hm U hU v :=
      (sourceRangeEquiv hm U hU).apply_symm_apply x |>.symm
    rw [hx, sourceTomita_polar_action hm U hU hopen hne, sourceRangeEquiv_apply,
      ← sourcePolarUnitary_sqrt_gram hm U hU hopen hne,
      LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
    calc
      _ = inner ℂ (conjugation y) (conjugateSourceGramRoot hm U v) :=
        sourceConjugation_inner_swap hm U _ _
      _ = inner ℂ (conjugateSourceGramRoot hm U (conjugation y)) v :=
        ((CFC.sqrt_nonneg (conjugateSourceGram hm U)).isSelfAdjoint.isSymmetric _ _).symm
      _ = inner ℂ (sourceGramRoot hm U z) v := by rw [heq]
      _ = _ := (CFC.sqrt_nonneg (sourceGram hm U)).isSelfAdjoint.isSymmetric _ _

/-- Maximal graph composition S*S, with the actual intermediate-domain condition. -/
def sourceTomitaModularGraph :
    Set (Lp ℂ 2 (oneParticleMeasure m) × Lp ℂ 2 (oneParticleMeasure m)) :=
  {p | ∃ hx : p.1 ∈ (sourceTomita hm U hU).domain,
    (sourceTomita hm U hU ⟨p.1, hx⟩, p.2) ∈ sourceTomitaAdjointGraph hm U hU}

/-- The literal S*S graph has domain U(range G) and value U(Gbar z) at U(Gz). -/
theorem sourceTomitaModularGraph_polar_iff (x y : ComplexSourceHilbert hm U) :
    (sourcePolarUnitary hm U hU hopen hne x,
      sourcePolarUnitary hm U hU hopen hne y) ∈ sourceTomitaModularGraph hm U hU ↔
        ∃ z, sourceGram hm U z = x ∧ conjugateSourceGram hm U z = y := by
  let A := sourceGramRoot hm U
  let B := conjugateSourceGramRoot hm U
  have hA (v : ComplexSourceHilbert hm U) : A (A v) = sourceGram hm U v :=
    congrArg (fun Q : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U => Q v)
      (CFC.sqrt_mul_sqrt_self _ (nonneg_iff_isPositive.mpr (sourceGram_isPositive hm U)))
  have hB (v : ComplexSourceHilbert hm U) : B (B v) = conjugateSourceGram hm U v :=
    congrArg (fun Q : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U => Q v)
      (CFC.sqrt_mul_sqrt_self _ (conjugateSourceGram_nonneg hm U))
  have hc (v : ComplexSourceHilbert hm U) : A (B v) = B (A v) :=
    congrArg (fun Q : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U => Q v)
      (sourceGramRoot_commute_conjugateSourceGramRoot hm U).eq
  have hsum (v : ComplexSourceHilbert hm U) : A (A v) + B (B v) = (2 : ℂ) • v := by
    simpa only [add_apply, mul_apply_eq_comp, ofNat_apply, two_smul] using
      congrArg (fun Q : ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U => Q v)
        (sourceGramRoot_sq_add_conjugateSourceGramRoot_sq hm U)
  constructor
  · rintro ⟨hx, hs⟩
    have hxcopy := hx
    obtain ⟨v, hv⟩ := hxcopy
    have hvx : A v = x := (sourcePolarUnitary hm U hU hopen hne).injective
      ((sourcePolarUnitary_sqrt_gram hm U hU hopen hne v).trans hv)
    have hsub : (⟨sourcePolarUnitary hm U hU hopen hne x, hx⟩ :
        (sourceTomita hm U hU).domain) = sourceRangeEquiv hm U hU v := Subtype.ext hv.symm
    rw [hsub, sourceTomita_polar_action hm U hU hopen hne,
      sourceTomitaAdjointGraph_polar_iff hm U hU hopen hne, conjugation_conjugation] at hs
    have heq : B (B v) = A y := hs
    let w := (1 / 2 : ℂ) • (A v + y)
    have hw : A w = v := by
      dsimp [w]
      rw [map_smul, map_add, ← heq, hsum]
      norm_num [smul_smul]
    refine ⟨w, ?_, ?_⟩
    · rw [← hA, hw, hvx]
    · rw [← hB]
      apply sourceGramRoot_injective hm U hU
      change A (B (B w)) = A y
      rw [hc, hc, hw, heq]
  · rintro ⟨z, rfl, rfl⟩
    have hphys : sourcePolarUnitary hm U hU hopen hne (sourceGram hm U z) =
        complexSourceMap hm U (A z) := by
      rw [← hA]
      exact sourcePolarUnitary_sqrt_gram hm U hU hopen hne (A z)
    refine ⟨⟨A z, hphys.symm⟩, ?_⟩
    have hsub : (⟨sourcePolarUnitary hm U hU hopen hne (sourceGram hm U z),
        ⟨A z, hphys.symm⟩⟩ : (sourceTomita hm U hU).domain) =
          sourceRangeEquiv hm U hU (A z) := Subtype.ext hphys
    rw [hsub, sourceTomita_polar_action hm U hU hopen hne,
      sourceTomitaAdjointGraph_polar_iff hm U hU hopen hne, conjugation_conjugation]
    change B (B (A z)) = A (conjugateSourceGram hm U z)
    rw [← hB, hc, hc]

end VacuumBellSeparation
