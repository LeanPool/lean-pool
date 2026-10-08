/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleCompatibleSlope

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleGlobalSlope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# One global slope from the Liouville finite-excess family

The exact finite realizations supplied by the fixed-cube excess theorem all
represent the same global gradient.  Their inner-cube gradient classes are
therefore compatible, so the independently compactness-selected slopes agree.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

private theorem cubeSolution_transport_grad
    {d : ℕ} (a : Book.Ch02.TriadicCoeffFamily d)
    {m m' : ℤ} (h : m = m')
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    (show Book.Ch03.CubeSolution (originCube d m') a from h ▸ u).toH1.grad =
      u.toH1.grad := by
  subst m'
  rfl

private theorem finiteAffineGradientExcess_transport
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k : ℤ) {m m' : ℤ} (h : m = m')
    (u : Book.Ch03.CubeSolution (originCube d m) a) :
    finiteAffineGradientExcess a k m'
        (show Book.Ch03.CubeSolution (originCube d m') a from h ▸ u) =
      finiteAffineGradientExcess a k m u := by
  subst m'
  rfl

/-- A single slope represents the global Liouville gradient on every centered
cube beyond the good-tail base. -/
theorem exists_common_jointSlope_of_liouvilleFixedCubeExcess
    {d : ℕ} [NeZero d] {s : ℝ}
    {a : Book.Ch02.TriadicCoeffFamily d} {delta c : ℝ} {n : ℤ}
    (hthreshold : c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c → ScalarIdentityGoodTail a s delta n →
        ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          euclideanNorm e ≤ 2 * euclideanNorm
            (cubeAverageVec (originCube d (q : ℤ))
              (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad))
    (hcoercive : ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
      (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
      euclideanNorm e ≤ 2 * euclideanNorm
        (localGradientClassAverage
          ((show LocalGradientL2 d q from
              constantGradientOnOriginCube e (q : ℤ)) +
            (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)))
    (hdelta : delta ∈ Set.Ioc (0 : ℝ) c)
    (hgood : ScalarIdentityGoodTail a s delta n)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (u : ∀ p : ℕ,
      Book.Ch03.CubeSolution (originCube d ((p : ℤ) - 2)) a)
    (Dv : Vec d → Vec d) (huGrad : ∀ p, (u p).toH1.grad = Dv)
    (hexcess : ∀ k : ℤ, n ≤ k →
      Tendsto
        (fun p : ℕ => finiteAffineGradientExcess a k ((p : ℤ) - 2) (u p))
        atTop (nhds 0)) :
    ∃ e : Vec d, ∀ q : ℕ, n.toNat ≤ q →
      (finiteCubeSolutionRestriction a (by omega) (u (q + 4))).toH1.gradToHilbertVectorL2 =
        (jointAffineFullGradientLinearMap a hCauchy q) e := by
  let g : ∀ q : ℕ, LocalGradientL2 d q := fun q =>
    (finiteCubeSolutionRestriction a (by omega) (u (q + 4))).toH1.gradToHilbertVectorL2
  have hgRep : ∀ q : ℕ, g q =ᵐ[volumeMeasureOn (localGradientCube d q)]
      fun x => HilbertVec.ofVec (Dv x) := by
    intro q
    have hcoe :=
      (finiteCubeSolutionRestriction a (n := (q : ℤ)) (by omega) (u (q +
        4))).toH1.coeFn_gradToHilbertVectorL2
    rw [finiteCubeSolutionRestriction_grad, huGrad (q + 4)] at hcoe
    exact hcoe
  have hcompat : ∀ {q r : ℕ} (hqr : q ≤ r),
      localGradientRestrict hqr (g r) = g q := by
    intro q r hqr
    apply (localGradientRestrict_eq_iff_ae hqr (g r) (g q)).2
    have hmu : volumeMeasureOn (localGradientCube d q) ≤
        volumeMeasureOn (localGradientCube d r) :=
      Measure.restrict_mono_set volume (localGradientCube_mono hqr)
    exact (hgRep r).filter_mono (ae_mono hmu) |>.trans (hgRep q).symm
  have hslope : ∀ q : ℕ, n ≤ (q : ℤ) → ∃ e : Vec d,
      g q = (jointAffineFullGradientLinearMap a hCauchy q) e := by
    intro q hnq
    let uq : ∀ j : ℕ,
      Book.Ch03.CubeSolution (originCube d ((q + j + 2 : ℕ) : ℤ)) a :=
      fun j => by
        have hm : ((q + j + 4 : ℕ) : ℤ) - 2 =
            ((q + j + 2 : ℕ) : ℤ) := by omega
        exact hm ▸ u (q + j + 4)
    have huqGrad : ∀ j, (uq j).toH1.grad = Dv := by
      intro j
      rw [cubeSolution_transport_grad]
      exact huGrad (q + j + 4)
    have hexcessq : Tendsto
        (fun j => finiteAffineGradientExcess a (q : ℤ)
          ((q + j + 2 : ℕ) : ℤ) (uq j))
        atTop (nhds 0) := by
      have hsub := (hexcess (q : ℤ) hnq).comp
        (tendsto_add_atTop_nat (q + 4))
      convert hsub using 1
      funext j
      simp only [Function.comp_apply]
      rw [show j + (q + 4) = q + j + 4 by omega]
      have houter : ((q + j + 4 : ℕ) : ℤ) - 2 =
          ((q + j + 2 : ℕ) : ℤ) := by omega
      exact finiteAffineGradientExcess_transport a (q : ℤ) houter
        (u (q + j + 4))
    obtain ⟨e, he⟩ := exists_jointSlope_of_fixedCubeExcess
      hthreshold hdelta hgood hCauchy q hnq uq Dv huqGrad hexcessq
    refine ⟨e, ?_⟩
    have hcoe0 :=
      (finiteCubeSolutionRestriction a (n := (q : ℤ)) (by omega) (uq
        0)).toH1.coeFn_gradToHilbertVectorL2
    rw [finiteCubeSolutionRestriction_grad, huqGrad 0] at hcoe0
    have hgq : g q =
        (finiteCubeSolutionRestriction a (n := (q : ℤ)) (by omega) (uq
          0)).toH1.gradToHilbertVectorL2 := by
      apply MeasureTheory.Lp.ext
      exact (hgRep q).trans hcoe0.symm
    exact hgq.trans he
  obtain ⟨e, he⟩ := exists_common_jointSlope_of_compatible_localGradients
    hcoercive hCauchy g hcompat hslope
  exact ⟨e, by simpa only [g] using! he⟩

end

end HighContrast
end HCPolySupport
