/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentitySuccessorConstants

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentitySuccessorTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open Set
open scoped BigOperators

noncomputable section

open FiniteLipschitzCoreInternal

private theorem weakError_le_one_of_interval
    {d : ℕ} [NeZero d] {a : Book.Ch03.CoeffFamily d}
    {s delta : ℝ} {n m j : ℤ}
    (hdelta : delta ≤ 1)
    (htail : ScalarIdentityGoodTailOnInterval a s delta n m)
    (hj : j ∈ Finset.Icc n m) :
    scalarIdentityWeakError a s j ≤ 1 := by
  have hsingle : scalarIdentityWeakError a s j ≤
      ∑ k ∈ Finset.Icc n m, scalarIdentityWeakError a s k :=
    Finset.single_le_sum (fun k _ ↦ scalarIdentityWeakError_nonneg a s k) hj
  exact hsingle.trans (htail.trans hdelta)

private theorem goodMax_subinterval_of_interval
    {d : ℕ} [NeZero d] {a : Book.Ch03.CoeffFamily d}
    {s delta : ℝ} {n q top m : ℤ}
    (hdelta : delta ≤ 1) (hnq : n ≤ q) (htopm : top ≤ m)
    (htail : ScalarIdentityGoodTailOnInterval a s delta n m) :
    ScalarIdentityGoodMaxOnInterval a s 1 q top := by
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  exact weakError_le_one_of_interval hdelta htail
    (Finset.mem_Icc.mpr ⟨hnq.trans hj'.1, hj'.2.trans htopm⟩)

private theorem goodTail_subinterval_of_interval
    {d : ℕ} [NeZero d] {a : Book.Ch03.CoeffFamily d}
    {s delta delta' : ℝ} {n q top m : ℤ}
    (hdelta : delta ≤ delta') (hnq : n ≤ q) (htopm : top ≤ m)
    (htail : ScalarIdentityGoodTailOnInterval a s delta n m) :
    ScalarIdentityGoodTailOnInterval a s delta' q top := by
  have hsubset : Finset.Icc q top ⊆ Finset.Icc n m := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨hnq.trans hj'.1, hj'.2.trans htopm⟩
  calc
    ∑ j ∈ Finset.Icc q top, scalarIdentityWeakError a s j ≤
        ∑ j ∈ Finset.Icc n m, scalarIdentityWeakError a s j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j _ _ ↦ scalarIdentityWeakError_nonneg a s j)
    _ ≤ delta := htail
    _ ≤ delta' := hdelta

private theorem successorTerminal_of_recurrence
    {d : ℕ} [NeZero d] {a : Book.Ch03.CoeffFamily d}
    {m q : ℤ} {e : Vec d} {s Crec : ℝ}
    (hCrec : 1 ≤ Crec) (hqm : q ≤ m - 1 - 2)
    (hrec : ∀ h ∈ Finset.Icc q (m - 1 - 2),
      finiteCenteredCubeSolutionEnergy a (m - 1 - 2)
          (successorInnerRestriction a m e) h ≤
        Crec * finiteCenteredCubeSolutionEnergy a (m - 1 - 2)
            (successorInnerRestriction a m e) (m - 1 - 2) +
          Crec * ∑ j ∈ Finset.Ioc h (m - 1 - 2),
            scalarIdentityWeakError a s j *
              finiteCenteredCubeSolutionEnergy a (m - 1 - 2)
                (successorInnerRestriction a m e) j)
    (hsmall : ScalarIdentityGoodTailOnInterval a s
      (2 * Crec)⁻¹ q (m - 1 - 2)) :
    finiteCenteredCubeSolutionEnergy a (m - 1 - 2)
        (successorInnerRestriction a m e) q ≤
      2 * Crec * finiteCenteredCubeSolutionEnergy a (m - 1 - 2)
        (successorInnerRestriction a m e) (m - 1 - 2) := by
  let v := successorInnerRestriction a m e
  exact finiteCenteredEnergy_le_of_identityGoodTail
    hCrec hqm v hrec hsmall q (Finset.mem_Icc.mpr ⟨le_rfl, hqm⟩)


private theorem finiteCenteredCubeSolutionEnergy_self
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) :
    finiteCenteredCubeSolutionEnergy a m u m =
      Book.Ch03.h1EnergyNormOnCube (originCube d m) a u.toH1 := by
  change finiteLipschitzEnergyRow a m u m = _
  exact finiteLipschitzEnergyRow_self a m u

theorem identityGaugeSuccessorEnergy_le
    (d : ℕ) [NeZero d] (g : ℝ)
    (geom : RoundedGenerationAnalyticGeometry d)
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hdual : PrintOrderRoundedReferenceDualRegularityAtGeneration
      d g geom.generation)
    (aGauge : CoeffSpace d) (hI : (symmPart (1 : Mat d)).PosDef)
    (aIdentity : Book.Ch03.CoeffFamily d)
    (hIdentity : ∀ Q : TriadicCube d,
      (aIdentity.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace (1 : Mat d) hI aGauge).1 :
          CoeffField d))
    (delta : ℝ) (n q m : ℤ) (e : Vec d)
    (hdelta : delta ∈ Ioc (0 : ℝ)
      (identitySuccessorSmallness d g geom hg hdual))
    (hnq : n ≤ q) (hqm : q ≤ m - 1 - 2)
    (hgood : ScalarIdentityGoodTailOnInterval aIdentity
      (printCertificateOrder g) delta n (m + 1)) :
    finiteCenteredCubeSolutionEnergy aIdentity (m - 1 - 2)
        (successorInnerRestriction aIdentity m e) q ≤
      identitySuccessorEnergyConstant d g geom hg hdual *
        (scalarIdentityWeakError aIdentity (printCertificateOrder g) m +
          scalarIdentityWeakError aIdentity
            (printCertificateOrder g) (m + 1)) *
        euclideanNorm e := by
  let Clocal := identitySuccessorLocalConstant d g geom hg
  let Crec := identitySuccessorRecurrenceConstant d g geom hg hdual
  let s := printCertificateOrder g
  have hCrec := (identitySuccessorRecurrenceConstant_spec
    d g geom hg hdual).1
  have hdeltaOne : delta ≤ 1 :=
    hdelta.2.trans
      ((min_le_left (1 / 2 : ℝ) (2 * Crec)⁻¹).trans (by norm_num))
  have hdeltaRec : delta ≤ (2 * Crec)⁻¹ :=
    hdelta.2.trans (min_le_right (1 / 2 : ℝ) (2 * Crec)⁻¹)
  have hlocal := (identitySuccessorLocalConstant_spec d g geom hg).2
    aGauge hI aIdentity hIdentity m e
    (weakError_le_one_of_interval hdeltaOne hgood
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    (weakError_le_one_of_interval hdeltaOne hgood
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    (weakError_le_one_of_interval hdeltaOne hgood
      (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
  have hmax := goodMax_subinterval_of_interval hdeltaOne hnq
    (by omega : m - 1 - 2 ≤ m + 1) hgood
  have hrec := (identitySuccessorRecurrenceConstant_spec
    d g geom hg hdual).2 aGauge hI aIdentity hIdentity q m e hqm hmax
  have hsmall := goodTail_subinterval_of_interval hdeltaRec hnq
    (by omega : m - 1 - 2 ≤ m + 1) hgood
  have hterminal := successorTerminal_of_recurrence
    (a := aIdentity) (m := m) (q := q) (e := e) (s := s)
    (Crec := Crec) hCrec hqm hrec hsmall
  have htop := finiteCenteredCubeSolutionEnergy_self aIdentity
    (m - 1 - 2) (successorInnerRestriction aIdentity m e)
  have hbound := terminal_bound_of_top hCrec hterminal htop hlocal
  simpa only [identitySuccessorEnergyConstant, Clocal, Crec, s] using hbound

end

end HighContrast
end HCPolySupport
