/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Count.InfRational
public import LeanPool.HyperellipticCurves.Count.WeierstrassRational
public import LeanPool.HyperellipticCurves.Log.Trace.TraceKz
public import LeanPool.HyperellipticCurves.Log.Trace.TraceKzInf
public import LeanPool.HyperellipticCurves.Log.Trace.TraceKzWeierstrass

import LeanPool.HyperellipticCurves.Log.Trace.TraceChain

/-!
# The per-disk bounds with the `hW`-identification discharged

The three chart instances of blueprint `thm:disk-bound` — generic, Weierstrass and infinity
centre — with the `hW` slot (the identification of the disk expansion of `h·dx/y` with the
`ω′`-combination, clause (c) of blueprint `thm:omega-prime-global`) discharged by the
trace-form capstones, each run **per disk** over `Frac(K⟦z⟧)`
(`LeanPool.HyperellipticCurves.Log.Trace.TraceKz`,
`LeanPool.HyperellipticCurves.Log.Trace.TraceKzWeierstrass`,
`LeanPool.HyperellipticCurves.Log.Trace.TraceKzInf`). What remains in each case is the
disk-independent
trace-form coordinate identity `hmap` (blueprint `lem:normalize`) and the per-disk
genericity pack of the respective chart — no function-field pack enters anywhere.

## Main statements

* `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_tracePoly`: the bound at a generic
  centre.
* `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_tracePoly_weierstrass`: at a
  Weierstrass centre.
* `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_tracePoly_inf`: at the centre at
  infinity.

Blueprint nodes: `thm:disk-bound`, `thm:omega-prime-global` (clause (c)), `thm:main-count`.
-/

@[expose] public section

open Polynomial IsLocalRing
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries

namespace ChabautyColeman

section DiskAssembled

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O]
  [IsAlgClosed (ResidueField O)] [Invertible (2 : O)] {C : HyperellipticCurve O} [C.IsOdd]
  {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  {π : O} {p e : ℕ} (cs : Fin uτ.natDegree → FractionRing O)
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]

/-- **The per-disk bound at a generic centre, `hW` discharged** (blueprint `thm:disk-bound`
composed with clause (c) of `thm:omega-prime-global`): the identification of the disk
expansion of `h·dx/y` with the `ω′`-combination is supplied by
`ChabautyColeman.map_omegaExpansionGeneric_eq_sum_smul_omegaPrime`, run per disk over
`Frac(K⟦z⟧)`, so what remains of the `hW` slot is the trace-form coordinate identity `hmap`
(disk-independent, blueprint `lem:normalize`) together with the per-disk genericity: `y_Q` a
unit, the fold avoidance bundle, and the Weierstrass avoidance of the reduced per-disk
configuration. -/
theorem encard_inter_residueDisk_le_ordPoint_tracePoly {h : O[X]} (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric C.f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = C.f.eval a) (hfa : IsUnit (C.f.eval a)) (hyQ : yQ ^ 2 = C.f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - C.f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < C.f.natDegree)
    (hcerts : IsPipelineCerts (C.f.map PowerSeries.C) (phiConfig C.f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (ha : ∀ i, uτ.eval (aτ i) = 0) (hbv : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m', (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j, i ≠ j → IsUnit (aτ i - aτ j))
    (hd : IsFtauFoldCerts Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)))
    {G : PowerSeries (FractionRing O)}
    (hG : G = ∑ i, cs i • antideriv (omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (phiZeta C.f a b xQ yQ m m₀ uτ vτ d s)) i))
    (hann : ∀ c, lambda hu rfl hv hw hbez cs C.monic_f C.natDegree_pos hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c = 0)
    (hh : h.map (residue O) ≠ 0)
    -- the per-disk genericity pack
    (hyQu : IsUnit yQ)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (havr : IsPipelineAvoid (C.f.map (residue O))
      ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
        (d.map (seriesResidue O)))
    -- the trace-form coordinates of the annihilating differential (`lem:normalize`)
    (hmap : h.map (algebraMap O (FractionRing O)) = ∑ i, cs i •
      tracePoly (uτ.map (algebraMap O (FractionRing O)))
        (c₂.map (algebraMap O (FractionRing O)))
        (Fin.cast (hu.natDegree_map (algebraMap O (FractionRing O))).symm i))
    (hord :
      ordAffine (C.f.map (residue O)) (h.map (residue O)) (residue O a) (residue O b) + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.affine (residue O a) (residue O b)
        (onCurve_map _ hb))).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h.map (residue O))
          (.affine (residue O a) (residue O b) (onCurve_map _ hb)) :=
  have h2 : IsUnit (2 : O) := isUnit_of_invertible 2
  have hfdegO : C.f.natDegree = 2 * uτ.natDegree + 1 :=
    (C.monic_f.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg
  encard_inter_residueDisk_le_ordPoint cs hsep hm hm₀ hb hfa hyQ hu hv hw hbez
    hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hh
    (map_omegaExpansionGeneric_eq_sum_smul_omegaPrime hroot hcc ha hbv hsplit hunit hd
      hram.maximalIdeal_eq hram.ne_zero_of_charZero_fractionRing C.monic_f hsep hm hm₀ hb hfa h2
      hyQ hfdegO hcerts hyQu havF
      (isPipelineAvoid_phi_of_residue hu hcerts havr) hmap)
    hord hrat

/-- **The per-disk bound at a Weierstrass centre, `hW` discharged**: the Weierstrass mirror
of `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_tracePoly`, with the `hW` slot
supplied by `ChabautyColeman.map_omegaExpansionWeierstrass_eq_sum_smul_omegaPrime_tracePoly`,
run per disk over `Frac(K⟦z⟧)`, from the trace-form coordinate identity `hmap` and the
per-disk genericity: `y_Q` a unit, the fold avoidance bundle, and the Weierstrass avoidance
of the reduced per-disk configuration (its second reduction step crosses the singular
constant block). -/
theorem encard_inter_residueDisk_le_ordPoint_tracePoly_weierstrass {h : O[X]} {ω : O}
    (hω : C.f.eval ω = 0) (hωu : IsUnit (C.f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries C.monic_f C.natDegree_pos hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = C.f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - C.f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < C.f.natDegree)
    (hcerts : IsPipelineCerts (C.f.map PowerSeries.C)
      (wConfig C.monic_f C.natDegree_pos hω hωu xQ yQ m₀ m uτ vτ) d uτ.natDegree)
    (hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (ha : ∀ i, uτ.eval (aτ i) = 0) (hbv : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m', (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j, i ≠ j → IsUnit (aτ i - aτ j))
    (hd : IsFtauFoldCerts Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)))
    {G : PowerSeries (FractionRing O)}
    (hG : G = ∑ i, cs i • antideriv (omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (wZeta C.monic_f C.natDegree_pos hω hωu xQ yQ m m₀ uτ vτ d s)) i))
    (hann : ∀ c, lambda hu rfl hv hw hbez cs C.monic_f C.natDegree_pos hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c = 0)
    (hh : h.map (residue O) ≠ 0)
    -- the per-disk genericity pack of the Weierstrass identification
    (hyQu : IsUnit yQ)
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (havr : IsPipelineAvoid (C.f.map (residue O))
      ((diskCenterConfig ω 0 xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
        (d.map (seriesResidue O)))
    (hmap : h.map (algebraMap O (FractionRing O)) = ∑ i, cs i •
      tracePoly (uτ.map (algebraMap O (FractionRing O)))
        (c₂.map (algebraMap O (FractionRing O)))
        (Fin.cast (hu.natDegree_map (algebraMap O (FractionRing O))).symm i))
    (hord : ordAffine (C.f.map (residue O)) (h.map (residue O)) (residue O ω) 0 + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.affine (residue O ω) 0
        (onCurve_map_of_root _ hω))).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h.map (residue O))
          (.affine (residue O ω) 0
            (onCurve_map_of_root _ hω)) :=
  have hfdegO : C.f.natDegree = 2 * uτ.natDegree + 1 :=
    (C.monic_f.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg
  encard_inter_residueDisk_le_ordPoint_weierstrass cs hω hωu hsep hm hm₀ hyQ hu hv
    hw hbez hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hh
    (map_omegaExpansionWeierstrass_eq_sum_smul_omegaPrime_tracePoly hroot hcc ha hbv hsplit
      hunit hd hram.maximalIdeal_eq hram.ne_zero_of_charZero_fractionRing C.monic_f
      C.natDegree_pos hω hωu hsep hm hm₀ hyQ hfdegO hcerts hyQu havF
      (isPipelineAvoid_w_of_residue C.monic_f C.natDegree_pos hω hωu hu hcerts havr) hmap)
    hord hrat

/-- **The per-disk bound at the infinity centre, `hW` discharged**: the infinity mirror of
`ChabautyColeman.encard_inter_residueDisk_le_ordPoint_tracePoly`, with the `hW` slot
supplied by `ChabautyColeman.map_omegaExpansionInf_eq_sum_smul_omegaPrime_tracePoly`, run
per disk over `Frac(K⟦z⟧)`, from the trace-form coordinate identity `hmap`, the reduced
closed datum `(infU, V)` and the fold avoidance bundle — no genericity beyond the `τ`-pack
enters at the infinity centre. -/
theorem encard_inter_residueDisk_le_ordPoint_tracePoly_inf {h : O[X]}
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - C.f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hvτ : vτ.natDegree < uτ.natDegree)
    {V : (O⟦X⟧)[X]}
    (hV : Polynomial.C PowerSeries.X * V = -(infV C.monic_f uτ vτ %ₘ infU C.monic_f uτ vτ))
    (hVdeg : V.degree < (infU C.monic_f uτ vτ).degree)
    (hVdvd : infU C.monic_f uτ vτ ∣ V ^ 2 - C.f.map PowerSeries.C)
    (hfdeg : (C.f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (ha : ∀ i, uτ.eval (aτ i) = 0) (hbv : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m', (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j, i ≠ j → IsUnit (aτ i - aτ j))
    (hd : IsFtauFoldCerts Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hf₀ : C₀.f.map (algebraMap K₀ (FractionRing O)) = C.f.map (algebraMap O (FractionRing O)))
    {G : PowerSeries (FractionRing O)}
    (hG : G = ∑ i, cs i • antideriv (omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (infZeta C.monic_f uτ vτ s)) i))
    (hann : ∀ c, lambda hu rfl hv hw hbez cs C.monic_f C.natDegree_pos hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c = 0)
    (hh : h.map (residue O) ≠ 0)
    (hhdeg : (h.map (residue O)).natDegree ≤ genus C.f - 1)
    -- the per-disk genericity pack of the infinity identification
    (havF : IsFtauFoldAvoid Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hmap : h.map (algebraMap O (FractionRing O)) = ∑ i, cs i •
      tracePoly (uτ.map (algebraMap O (FractionRing O)))
        (c₂.map (algebraMap O (FractionRing O)))
        (Fin.cast (hu.natDegree_map (algebraMap O (FractionRing O))).symm i))
    (hord : ordInf (C.f.map (residue O)) (h.map (residue O)) + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.infinity : CurvePoint (ResidueField O) (C.f.map (residue O)))).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h.map (residue O)) .infinity :=
  have hgdeg : C.f.natDegree = 2 * uτ.natDegree + 1 :=
    (C.monic_f.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg
  encard_inter_residueDisk_le_ordPoint_inf cs hu hv hw hbez hvτ hgdeg hV hVdeg
    hVdvd hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hh hhdeg
    (map_omegaExpansionInf_eq_sum_smul_omegaPrime_tracePoly hroot hcc ha hbv hsplit hunit
      hd hram.maximalIdeal_eq hram.ne_zero_of_charZero_fractionRing C.monic_f hvτ hgdeg hV hVdeg
      hVdvd havF hmap)
    hord hrat

end DiskAssembled

end ChabautyColeman

end
