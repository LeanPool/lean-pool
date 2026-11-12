/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleMatrixIncomingVector
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureGeneratorCocycles
public import LeanPool.ApollonianSuperharmonic.TilingLatticeBasis

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
  have cocycle : ∀ z : GaussianInt, z ∈ K → ∃ c : GaussianInt,
      Matrix.mulVec (CircleMatrix C) ![(z.re : ℝ), (z.im : ℝ)] =
        ![(c.re : ℝ), (c.im : ℝ)] ∧
      ∀ x, g (x + z) = g x + x.re * c.re + x.im * c.im + g z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · refine ⟨BandVectors.2 (q 1) (q 0), hmatA, ?_⟩
          exact hgenA
        · refine ⟨BandVectors.2 (q 2) (q 0), hmatB, ?_⟩
          exact hgenB
    | zero =>
        refine ⟨0, ?_, ?_⟩
        · ext i
          fin_cases i <;> simp [Matrix.mulVec]
        · intro x
          simp [gzero]
    | add z y hz hy iz iy =>
        rcases iz with ⟨c, hc, hz⟩
        rcases iy with ⟨d, hd, hy⟩
        refine ⟨c + d, ?_, ?_⟩
        · rw [show ![((z + y).re : ℝ), ((z + y).im : ℝ)] =
              ![(z.re : ℝ), (z.im : ℝ)] + ![(y.re : ℝ), (y.im : ℝ)] by
                ext i; fin_cases i <;> simp]
          have hcr := congrFun hc 0
          have hci := congrFun hc 1
          have hdr := congrFun hd 0
          have hdi := congrFun hd 1
          ext i
          fin_cases i
          · simp [Matrix.mulVec] at hcr hdr ⊢
            nlinarith [hcr, hdr]
          · simp [Matrix.mulVec] at hci hdi ⊢
            nlinarith [hci, hdi]
        · intro x
          rw [show x + (z + y) = (x + z) + y by abel]
          rw [hy, hz]
          have hyz := hy z
          rw [hyz]
          simp
          ring_nf
    | neg z hz iz =>
        rcases iz with ⟨c, hc, hz⟩
        refine ⟨-c, ?_, ?_⟩
        · have hlin : Matrix.mulVec (CircleMatrix C) ![(-z.re : ℝ), (-z.im : ℝ)] =
              - Matrix.mulVec (CircleMatrix C) ![(z.re : ℝ), (z.im : ℝ)] := by
            ext i
            fin_cases i <;> simp [Matrix.mulVec] <;> ring
          have hzre : ((-z).re : ℝ) = -(z.re : ℝ) := by
            simp []
          have hzim : ((-z).im : ℝ) = -(z.im : ℝ) := by
            simp []
          have hcre : ((-c).re : ℝ) = -(c.re : ℝ) := by
            simp []
          have hcim : ((-c).im : ℝ) = -(c.im : ℝ) := by
            simp []
          rw [hzre, hzim, hcre, hcim]
          rw [hlin, hc]
          simp
        · intro x
          have h := hz (x - z)
          have hconst := hz (-z)
          have hback : g 0 = g (-z) + (-z).re * c.re + (-z).im * c.im + g z := by
            simpa using hconst
          rw [gzero] at hback
          have gzneg : g (-z) = z.re * c.re + z.im * c.im - g z := by
            simp at hback
            linarith [hback]
          change g (x - z) = _
          rw [gzneg]
          rw [show ((-c).re : ℤ) = -c.re by simp [],
            show ((-c).im : ℤ) = -c.im by simp []]
          simp at h
          ring_nf at h ⊢
          linarith [h]
  have hwK : w ∈ K := by
    rw [show w = (mn.1 : GaussianInt) * a + (mn.2 : GaussianInt) * b by simpa [a, b] using
        hmn.1.symm]
    have aa : a ∈ K := AddSubgroup.subset_closure (by simp)
    have bb : b ∈ K := AddSubgroup.subset_closure (by simp)
    exact K.add_mem (by simpa [smul_eq_mul] using K.zsmul_mem aa mn.1)
      (by simpa [smul_eq_mul] using K.zsmul_mem bb mn.2)
  obtain ⟨c, hc, hformula⟩ := cocycle w hwK
  exact ⟨c, hc, hformula⟩

end ApollonianSuperharmonic

end
