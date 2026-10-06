/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardFamilyClauses
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardDataTolerance
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderNormalizedReferencePowerTail

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardNormalizedSupply

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The normalized-gauge supply, from the certificate's own block row

The stationary corrector family clause reduces to `RootNormalizedSupply`.  This module
supplies it from the **same physical block row that `hhomogenized` consumes**,
through the available converter
`exists_shiftedNormalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow`.

Three things make the reduction work, and each is worth naming.

* **The gauge matches.**  The converter's reference family satisfies
  `(aRef.coeffOn Q).toCoeffField = affineCoefficient (Selection.normalizedRoot (symmPart abar)) _
  ↑↑(normalizedCenteredCoeff a abar hS)`,
  which is **definitionally** `gaugeCoeff a abar hS` — the two sides are the
  same `affineCoefficient` application, so the identification is `rfl` — hence
  almost everywhere
  `⇑(normalizedSample abar hS a).1`.  This is exactly the identity the *identity*-gauge
  demand cannot have.
* **No smallness on the certificate's `delta` is needed.**  The converter
  returns a *power* tail, and `ScalarIdentityPowerTail.rebase` trades reference
  scale for amplitude: pushing the base scale out drives the amplitude below any
  prescribed tolerance.  That is why the identity-gauge row was stated
  `∀ eps > 0` and why nothing here demands `delta` below a private constant.
* **The translates are covered by the certificate itself.**  `hquenched`
  produces the row on a set `OmegaEnd` with
  `∀ z, translateCoeff z ⁻¹' OmegaEnd = OmegaEnd`, so a certified sample and all
  of its integer translates carry the row.  No per-`z` certificate is assumed.

The one exponent condition is `rho < 2 * s`, where `s` is the good-tail order
the supply itself chooses.  `s` is not a
frozen constant: it is carried by the block-row
supply and consumed only here, because the corrector datum records its order as
a *field* rather than an index.  At the certificate's `rho = (1 + 3 g) / 4` a
per-`g` order `s := (1 + g) / 4` satisfies both `0 < s < 1/2` and `rho < 2 * s`
for every `g ∈ [0, 1)`, so the admitted range is the whole of `[0,1)`; the
frozen order would have forced `g < 1/6`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## Trading reference scale for amplitude -/

/-- **A power tail is a good tail at every prescribed tolerance.**  Rebasing to
a larger reference scale divides the amplitude by a positive power, and the
geometric sum of the rebased tail is below any `eps > 0` once the base is far
enough out. -/
theorem exists_goodTail_of_powerTail [NeZero d]
    {aFin : Book.Ch02.TriadicCoeffFamily d} {s A kappa x eps : ℝ}
    (h : ScalarIdentityPowerTail aFin s A kappa x)
    (hA : 0 ≤ A) (hkappa : 0 < kappa) (hx : 1 ≤ x) (heps : 0 < eps) :
    ∃ n : ℤ, ScalarIdentityGoodTail aFin s eps n := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hpow : (3 : ℝ) ^ (-kappa) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.mpr hkappa)
  have hc : (0 : ℝ) < 1 - (3 : ℝ) ^ (-kappa) := by linarith only [hpow]
  have htend : Filter.Tendsto (fun t : ℝ => A * t ^ (-kappa)) Filter.atTop
      (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hkappa).const_mul A
  have hev : ∀ᶠ t : ℝ in Filter.atTop,
      A * t ^ (-kappa) ≤ eps * (1 - (3 : ℝ) ^ (-kappa)) :=
    htend.eventually_le_const (by positivity)
  obtain ⟨t, hle, ht1⟩ := (hev.and (Filter.eventually_ge_atTop (1 : ℝ))).exists
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hxy : x ≤ x * t := le_mul_of_one_le_right hx0.le ht1
  have hy : (0 : ℝ) < x * t := mul_pos hx0 ht0
  have hreb := h.rebase hx0 hy hxy
  have hratio : x * t / x = t := by field_simp
  rw [hratio] at hreb
  have hone : (1 : ℝ) ≤ x * t := le_trans hx hxy
  have hAmp : 0 ≤ A * t ^ (-kappa) :=
    mul_nonneg hA (Real.rpow_nonneg ht0.le _)
  refine ⟨(Quenched.triadicCeilingIndex (x * t) : ℤ),
    (hreb.goodTail hAmp hkappa hone).mono ?_⟩
  rw [div_le_iff₀ hc]
  exact hle

/-! ## The certificate-side block row -/

/-- **The certificate-side input, in the shape `hquenched` produces it.**  A
certified sample lies in a translation-invariant set on which the physical block
row at the comparison matrix `abar` holds, with the row exponent below twice the
private order.

Every field is on `RootAssembly`'s own binder surface: `Omega` is `OmegaEnd`
together with its `∀ z, translateCoeff z ⁻¹' OmegaEnd = OmegaEnd`; `rho` is
`(1 + 3 g) / 4`; `kappa`, `delta`, `S`, `X` are the interface's; `1 ≤ X b` and
`S b ≤ X b` are `hquenched`'s own `(∀ a, 1 ≤ X a)` and `(∀ a, S a ≤ X a)`; and
the row itself is the hypothesis `hhomogenized` consumes, at the same
`Book.Ch02.constantBlockMatrix abar`.  Nothing new is introduced.

The good-tail order `s` is *supplied here*
together with the row, subject only to the corrector cone `0 < s < 1/2` and the
window `rho < 2 * s`.  It is not a global constant, so the provider may choose
it after the contrast exponent `g` — and nothing downstream of the supply ever
sees it. -/
@[expose]
def RootBlockRowSupply (d : ℕ) [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop) : Prop :=
  ∀ (abar : Mat d), (symmPart abar).PosDef →
    ∀ (a : CoeffSpace d) (x : ℝ), GoodScale abar a x →
      ∃ (Omega : Set (CoeffSpace d)) (s rho kappa delta : ℝ)
        (S X : CoeffSpace d → ℝ),
        a ∈ Omega ∧
        (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Omega = Omega) ∧
        0 < s ∧ s < 1 / 2 ∧
        0 < rho ∧ rho ≤ 1 ∧ rho < 2 * s ∧
        0 < kappa ∧ 0 ≤ delta ∧
        ∀ b ∈ Omega, 1 ≤ X b ∧ S b ≤ X b ∧
          Quenched.HasAllLaterPhysicalBlockRow rho kappa delta
            (Book.Ch02.constantBlockMatrix abar) S X b

/-! ## The supply -/

/-- **The normalized-gauge datum, from the block row.**  The single input
`correctorFamilyHole_of_normalizedSupply`
needs is produced by the certificate's own row, in the certificate's own
gauge. -/
theorem rootNormalizedSupply_of_blockRow [NeZero d]
    {GoodScale : Mat d → CoeffSpace d → ℝ → Prop}
    (hblock : RootBlockRowSupply d GoodScale) :
    RootNormalizedSupply d GoodScale := by
  intro abar hS a x hgood z
  obtain ⟨Omega, s, rho, kappa, delta, S, X, haOmega, hinv, hs0, hs2, hrho0,
    hrho1, hgap, hkappa, hdelta, hrow⟩ := hblock abar hS a x hgood
  have hz : translateCoeff z a ∈ Omega := by
    have hpre : a ∈ translateCoeff z ⁻¹' Omega := by rw [hinv z]; exact haOmega
    exact hpre
  obtain ⟨hXone, hburn, hrowz⟩ := hrow _ hz
  obtain ⟨aRef, L, hcoeffRef, hpower⟩ :=
    exists_shiftedNormalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow
      (translateCoeff z a) abar hS s rho kappa delta S X
      hrho0 hrho1 hgap hkappa hdelta hrowz hXone hburn
  have hbase : (1 : ℝ) ≤
      (3 : ℝ) ^ ((Quenched.triadicCeilingIndex (X (translateCoeff z a)) + L : ℕ) : ℤ) := by
    rw [zpow_natCast]
    exact one_le_pow₀ (by norm_num)
  obtain ⟨n, hgoodTail⟩ := exists_goodTail_of_powerTail hpower
    (Real.sqrt_nonneg delta) (by positivity) hbase
    (rootCorrectorSupplyTolerance_pos d s hs0 hs2)
  have hgauge : ∀ q : ℕ,
      (aRef.coeffOn (originCube d (q : ℤ))).toCoeffField =
        gaugeCoeff (translateCoeff z a) abar hS :=
    fun q => hcoeffRef (originCube d (q : ℤ))
  /- The converter's identity is *pointwise* and holds on
  **every** triadic cube, and the datum keeps it in a.e. form.  This one field is what makes the
  selected datum's family a.e.
  equal to the certificate's exact-gauge family, and hence what discharges the
  corrector-family hypotheses of the decay, Liouville and C¹ clauses. -/
  have hcoeffAll : ∀ Q : TriadicCube d,
      (aRef.coeffOn Q).toCoeffField =ᵐ[volume]
        fun y ↦ (normalizedSample abar hS (translateCoeff z a)).1 y := by
    intro Q
    rw [hcoeffRef Q]
    exact (normalizedSample_ae abar hS (translateCoeff z a)).symm
  have hcoeff : ∀ q : ℕ,
      Book.Ch03.publicCoeffField (originCube d (q : ℤ)) aRef
        =ᵐ[volume.restrict (localGradientCube d q)]
          fun y ↦ (normalizedSample abar hS (translateCoeff z a)).1 y := by
    intro q
    have h1 := Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      (originCube d (q : ℤ)) aRef
    rw [hgauge q] at h1
    have h2 : Book.Ch03.publicCoeffField (originCube d (q : ℤ)) aRef
        =ᵐ[volume.restrict (localGradientCube d q)]
          gaugeCoeff (translateCoeff z a) abar hS := h1
    exact h2.trans (ae_restrict_of_ae
      (normalizedSample_ae abar hS (translateCoeff z a)).symm)
  have hmem : rootCorrectorSupplyTolerance d s hs0 hs2 ∈
      Ioc (0 : ℝ) (rootCorrectorTolerance d s hs0 hs2) :=
    ⟨rootCorrectorSupplyTolerance_pos d s hs0 hs2,
      (min_le_left _ _).trans (min_le_left _ _)⟩
  have hmemData : rootCorrectorSupplyTolerance d s hs0 hs2 ∈
      Ioc (0 : ℝ) (rootCorrectorDataTolerance d s hs0 hs2) :=
    ⟨rootCorrectorSupplyTolerance_pos d s hs0 hs2,
      (min_le_left _ _).trans (min_le_right _ _)⟩
  have hmemRow : rootCorrectorSupplyTolerance d s hs0 hs2 ∈
      Ioc (0 : ℝ) (rootCorrectorWeakRowTolerance d s hs0 hs2) :=
    ⟨rootCorrectorSupplyTolerance_pos d s hs0 hs2, min_le_right _ _⟩
  refine rootCorrectorEvent_of_goodTail hs0 hs2 aRef
    (rootCorrectorSupplyTolerance d s hs0 hs2) n
    hmem hgoodTail hcoeff hcoeffAll ?_ ?_
  · intro hC e
    obtain ⟨C, hC0, hValue⟩ :=
      ((rootCorrectorData_spec d s hs0 hs2).2 aRef
        (rootCorrectorSupplyTolerance d s hs0 hs2) n
        hmemData hgoodTail hC e).2
    exact ⟨n.toNat, C, hC0, hValue⟩
  · intro hC e
    obtain ⟨N, hN0, hRow⟩ :=
      (rootCorrectorWeakRow_spec d s hs0 hs2).2 aRef
        (rootCorrectorSupplyTolerance d s hs0 hs2) n
        hmemRow hgoodTail hC e
    exact ⟨n.toNat, N, hN0, hRow⟩

/-! ## The hole, from the certificate's row alone -/

/-- **the stationary corrector family clause of the root assembly, from the certificate's own
block row.**  This composes the inhabitant with the supply: no
gauge change, no per-`z` certificate, no smallness beyond the exponent window
`rho < 2 * s` at the supply's own order `s`. -/
theorem correctorFamilyHole_of_blockRow (d : ℕ) [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop)
    (hblock : RootBlockRowSupply d GoodScale) :
    ∀ abar : Mat d, (symmPart abar).PosDef →
      ∃ (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
        (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
        RootPushCorrectorFamilyPredicate d abar Phi gradPhi ∧
        (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
          gradPhi (c • e + e') a
            =ᵐ[volume] fun x => c • gradPhi e a x + gradPhi e' a x) ∧
        (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
          gradPhi e (translateCoeff z a)
            =ᵐ[volume] fun x => gradPhi e a (x + Source.AKL.intTranslation z)) ∧
        ∀ (a : CoeffSpace d) (x : ℝ), GoodScale abar a x →
          ∀ e : Vec d,
            HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
              IsWeakSolutionOn (fun y => a.1 y) Set.univ
                (fun y => e + gradPhi e a y) :=
  correctorFamilyHole_of_normalizedSupply d GoodScale
    (rootNormalizedSupply_of_blockRow hblock)

end

end Root
end HighContrast
end HCPolySupport
