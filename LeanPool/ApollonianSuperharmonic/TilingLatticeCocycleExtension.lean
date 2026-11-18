/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.QuadraticCocycleSubgroup

public import LeanPool.ApollonianSuperharmonic.CircleMatrixIncomingVector
public import LeanPool.ApollonianSuperharmonic.TilingLatticeBasis
public import LeanPool.ApollonianSuperharmonic.IntegerLatticeFunction
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

-- [TABLET NODE: TilingLatticeCocycleExtension]

/-!
# TilingLatticeCocycleExtension

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TilingLatticeCocycleExtension (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hC : q 0 = C.1.1) (g : IntegerLatticeFunction)
    (hgen : ∀ j : Fin 3, ∀ x,
      g (x + BandVectors.1 (q j.succ) (q 0)) = g x +
        x.re * (BandVectors.2 (q j.succ) (q 0)).re +
        x.im * (BandVectors.2 (q j.succ) (q 0)).im +
        g (BandVectors.1 (q j.succ) (q 0))) :
    ∀ v, v ∈ TilingLattice C → ∃ a : GaussianInt,
      Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
        ![(a.re : ℝ), (a.im : ℝ)] ∧
      ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v := by
-- BODY
  classical
  intro w hw
  let a := BandVectors.1 (q 1) (q 0)
  let b := BandVectors.1 (q 2) (q 0)
  have basis := TilingLatticeBasis C q hq hC
  dsimp at basis
  obtain ⟨ha, hb, hcoords, hu, hv, hL, hLcoords, hfund⟩ := basis
  obtain ⟨mn, hmn⟩ := hcoords ⟨w, hw⟩
  have hgenA := hgen ⟨0, by decide⟩
  have hgenB := hgen ⟨1, by decide⟩
  have hmatA := CircleMatrixIncomingVector C q hq.1 hC ⟨0, by decide⟩
  have hmatB := CircleMatrixIncomingVector C q hq.1 hC ⟨1, by decide⟩
  have gzero : g 0 = 0 := by
    have h := hgenA 0
    simpa using congrArg (fun z : ℤ => z - g a) h
  let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
  have generators : ({a, b} : Set GaussianInt) ⊆
      quadraticCocycleSubgroup (CircleMatrix C) g gzero := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact ⟨BandVectors.2 (q 1) (q 0), hmatA, hgenA⟩
    · obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨BandVectors.2 (q 2) (q 0), hmatB, hgenB⟩
  have hwK : w ∈ K := by
    rw [show w = (mn.1 : GaussianInt) * a + (mn.2 : GaussianInt) * b by simpa [a, b] using
        hmn.1.symm]
    have aa : a ∈ K := AddSubgroup.subset_closure (by simp)
    have bb : b ∈ K := AddSubgroup.subset_closure (by simp)
    exact K.add_mem (by simpa [smul_eq_mul] using K.zsmul_mem aa mn.1)
      (by simpa [smul_eq_mul] using K.zsmul_mem bb mn.2)
  exact ((AddSubgroup.closure_le
    (quadraticCocycleSubgroup (CircleMatrix C) g gzero)).mpr generators) hwK

end ApollonianSuperharmonic

end
