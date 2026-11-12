/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOdometerTheorem
public import LeanPool.ApollonianSuperharmonic.IntegerSuperharmonicClosedness
public import LeanPool.ApollonianSuperharmonic.PositiveDefiniteRepresentativeGap
public import LeanPool.ApollonianSuperharmonic.PositiveTracePackingDichotomy
public import LeanPool.ApollonianSuperharmonic.SuperharmonicDownwardClosure
public import LeanPool.ApollonianSuperharmonic.TraceNonpositivePackingApproximation

-- [TABLET NODE: IntegerSuperharmonicCharacterization]

/-!
# IntegerSuperharmonicCharacterization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem IntegerSuperharmonicCharacterization
    (A : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm) :
    (Exists fun g : IntegerLatticeFunction =>
      IntegerSuperharmonicRepresentative A g) <->
      Or (Exists fun C : BandCircle =>
          (CircleMatrix C - A).PosSemidef)
        (Matrix.trace A <= 0) := by
-- BODY
  constructor
  · rintro ⟨g, hg⟩
    by_cases htrace : Matrix.trace A <= 0
    · exact Or.inr htrace
    · have htrace_pos : 0 < Matrix.trace A := lt_of_not_ge htrace
      rcases PositiveTracePackingDichotomy A hA htrace_pos with hpsd | hpd
      · exact Or.inl hpsd
      · exfalso
        rcases hpd with ⟨C, hgap⟩
        rcases BandOdometerTheorem C with ⟨h, hh, hcocycle, hmax⟩
        rcases PositiveDefiniteRepresentativeGap A C g h hg hh hgap with
          ⟨hdiv, c, hdom⟩
        let f : IntegerLatticeFunction := fun x => g x + c
        have hfdom : forall x, h x <= f x := hdom
        have hflap : forall x, FourNeighborLaplacian f x <= 1 := by
          intro x
          have hgx := hg.2.2 x
          dsimp [f, FourNeighborLaplacian] at hgx ⊢
          omega
        rcases hmax f hfdom hflap with ⟨B, hB⟩
        rcases hdiv ((B : Real) - (c : Real) + 1) with ⟨R, hR⟩
        obtain ⟨N, hN⟩ := exists_nat_ge (max R 1)
        let x : GaussianInt := ⟨N, 0⟩
        have hxlarge : R <= (x.re : Real) ^ 2 + (x.im : Real) ^ 2 := by
          have hRN : R <= (N : Real) := le_trans (le_max_left _ _) hN
          have hN1 : (1 : Real) <= N := le_trans (le_max_right _ _) hN
          have hNsq : (N : Real) <= (N : Real) ^ 2 := by nlinarith
          simpa [x] using le_trans hRN hNsq
        have hgrowth := hR x hxlarge
        have hnonneg : 0 <= f x - h x := by
          exact sub_nonneg.mpr (hfdom x)
        have hbound := hB x
        have hbound_int : ((f x - h x).natAbs : Int) <= B := by
          exact_mod_cast hbound
        rw [Int.natAbs_of_nonneg hnonneg] at hbound_int
        have hbound' : (f x : Real) - (h x : Real) <= B := by
          exact_mod_cast hbound_int
        simp only [f, Int.cast_add] at hbound'
        linarith
  · rintro (⟨C, hgap⟩ | htrace)
    · rcases BandOdometerTheorem C with ⟨g, hg, hcocycle, hmax⟩
      exact SuperharmonicDownwardClosure A (CircleMatrix C) hA ⟨g, hg⟩ hgap
    · rcases TraceNonpositivePackingApproximation A hA htrace with
        ⟨Aseq, hconv, Cseq, hgap⟩
      apply IntegerSuperharmonicClosedness Aseq A hconv
      intro n
      rcases BandOdometerTheorem (Cseq n) with ⟨g, hg, hcocycle, hmax⟩
      have hDsymm : (CircleMatrix (Cseq n) - Aseq n).IsSymm := by
        change (CircleMatrix (Cseq n) - Aseq n).transpose =
          CircleMatrix (Cseq n) - Aseq n
        simpa [Matrix.IsHermitian] using (hgap n).1
      have hAn : (Aseq n).IsSymm := by
        change (Aseq n).transpose = Aseq n
        change (CircleMatrix (Cseq n)).transpose - (Aseq n).transpose =
          CircleMatrix (Cseq n) - Aseq n at hDsymm
        rw [hg.1] at hDsymm
        ext i j
        have hij := congrFun (congrFun hDsymm i) j
        simp only [Matrix.sub_apply] at hij
        linarith
      exact SuperharmonicDownwardClosure
        (Aseq n) (CircleMatrix (Cseq n)) hAn ⟨g, hg⟩ (hgap n)

end ApollonianSuperharmonic

end
