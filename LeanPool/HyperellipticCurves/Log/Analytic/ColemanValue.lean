/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Analytic.ColemanIntegral
public import LeanPool.HyperellipticCurves.Log.Charts.DiskIdentification

/-!
# The Coleman integral value of `Lam` (numerical clause (b))

This file assembles numerical clause (b) of `thm:omega-prime-global`: for a same-disk
difference `c = [P_{z₀}] - [P₀]` (realized in `ker redJ`), the abelian logarithm value
`Lam c i` is the Coleman integral of `ω′_i` from the disk center to `z₀`.

The class itself is `ChabautyColeman.diskDiffClass`, the difference of the disk point at
parameter `z₀` and the centre.

`ChabautyColeman.hasSum_Lam_antiderivOmegaPrime` states this as a convergent `p`-adic sum over
`K = FractionRing O`: the image of `Lam c i` is `∑_k coeff_k(antideriv ω′) · (f z₀)^k`, where
`ω′ = ChabautyColeman.omegaPrime` of the translated formal group law `ChabautyColeman.ftauFoldFGL`
along the `φ_Q`-chart `ChabautyColeman.phiZeta`. It is built from four ingredients:

* `ChabautyColeman.hasSum_algebraMap_Lam` — the endpoint value (`Lam` as the `F_τ`-logarithm at
  the chart coordinates of `c + τ`, a convergent `K`-sum);
* `ChabautyColeman.J1_equiv_polydisk_diskPointDiff` — those chart coordinates *are* `ζ(z₀)`
  (the geometric identification of `LeanPool.HyperellipticCurves.Log.Charts.DiskIdentification`);
* `ChabautyColeman.hasSum_coeff_subst_log` — the Fubini reindexing turning the multi-index
  endpoint sum into the single-index series of the substituted logarithm;
* `ChabautyColeman.subst_log_eq_antideriv` — that substituted logarithm is the antiderivative
  of `ω′`.
-/

@[expose] public section

open Polynomial IsLocalRing MvPowerSeries
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries

namespace ChabautyColeman

section ColemanValue

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O] [CharZero (FractionRing O)]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  {π : O} {p e : ℕ}

/-- **The Coleman value of `Lam`, given the chart coordinates of the class**: for any family
`ζ` of chart coordinates vanishing at the centre and any kernel class whose polydisk
coordinates are the values `ζ(z₀)`, the image of `Lam c i` is the value at `z₀` of the
antiderivative of `ω′_i`. Assembled from `ChabautyColeman.hasSum_algebraMap_Lam` (endpoint
value), `ChabautyColeman.hasSum_coeff_subst_log` (the Fubini reindexing) and
`ChabautyColeman.subst_log_eq_antideriv`; the three charts differ only in the identification
`hJ` of the polydisk coordinates. -/
theorem hasSum_Lam_antiderivOmegaPrime_of_polydisk (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (ha : ∀ i, uτ.eval (aτ i) = 0) (hbv : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m', (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j, i ≠ j → IsUnit (aτ i - aτ j))
    (hd : IsFtauFoldCerts Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    {ζ : Fin uτ.natDegree → O⟦X⟧} (hζ0 : ∀ s, PowerSeries.constantCoeff (ζ s) = 0)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker)
    (hJ : (reductionKernelEquivPolydisk hu rfl hv hw hbez hf hdeg hfdeg hsq c).1
      = fun j ↦ PSeries.eval z₀ (ζ j)) (i : Fin uτ.natDegree) :
    HasSum (fun k : ℕ ↦ PowerSeries.coeff k (antideriv (omegaPrime
          (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv hd hram hsplit hunit)
          (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (ζ s)) i))
        * algebraMap O (FractionRing O) z₀ ^ k)
      (algebraMap O (FractionRing O)
        (Lam hu rfl hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe c i)) := by
  have hLam := hasSum_algebraMap_Lam hu rfl hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
      hsplit hunit hd hram hpe c i
  rw [hJ] at hLam
  have hFub := hasSum_coeff_subst_log
    (ftauFoldFGL hu rfl hv hw hbez hf
      ((hf.natDegree_map (algebraMap O (FractionRing O))).symm.trans hfdeg) hroot hcc ha hbv
      hd hram.maximalIdeal_eq hram.ne_zero_of_charZero_fractionRing hsplit hunit) hram hpe
      hζ0 hz₀ i hLam
  rw [← subst_log_eq_antideriv (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv
      hd hram hsplit hunit)
    (fun s ↦ by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hζ0 s, map_zero]) i]
  exact hFub

/-- The same-disk difference `[P_z] - [P₀]` on the residue disk with centre `P₀ = (a, b)`,
as an element of `J¹ = ker(redJ)`: the disk point at parameter `z ∈ 𝔪` is
`(a + z, b·η(z))` and its class is multiplied by the class of `ιP₀ = (a, -b)`. Membership
in the kernel is `ChabautyColeman.redJ_diskPointDiff_eq_one` — the two points reduce to the
same residue point. -/
noncomputable def diskDiffClass (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    {z : O} (hz : z ∈ maximalIdeal O) :
    (redJHom (K := FractionRing O) (f := f) hf hdeg).ker :=
  ⟨aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) (a + z))
      (algebraMap O (FractionRing O) (PSeries.eval z (PowerSeries.C b * diskSeriesGeneric f a)))
    * aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) a)
      (algebraMap O (FractionRing O) (-b)),
    MonoidHom.mem_ker.mpr (redJ_diskPointDiff_eq_one hf hdeg hb hfa h2 hz)⟩

/-- **Numerical clause (b) of `thm:omega-prime-global` for `Lam`**: for the same-disk difference
`c = [P_{z₀}] - [P₀]` (realized in `ker redJ`), the image of `Lam c i` in `K = FractionRing O`
is the convergent `p`-adic Coleman integral of `ω′_i` from the disk center to `z₀` — i.e. the
value at `z₀` of the antiderivative of the pulled-back invariant differential
`omegaPrime (F_τ) (φ_Q-chart)`. Assembled from `ChabautyColeman.hasSum_algebraMap_Lam`
(endpoint value), `ChabautyColeman.J1_equiv_polydisk_diskPointDiff` (chart-coordinate
identification `ζ(z₀)`), `ChabautyColeman.hasSum_coeff_subst_log` (the Fubini reindexing) and
`ChabautyColeman.subst_log_eq_antideriv`. -/
theorem hasSum_Lam_antiderivOmegaPrime (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (ha : ∀ i, uτ.eval (aτ i) = 0) (hbv : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m', (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j, i ≠ j → IsUnit (aτ i - aτ j))
    (hd : IsFtauFoldCerts Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) (i : Fin uτ.natDegree) :
    HasSum (fun k : ℕ ↦ PowerSeries.coeff k (antideriv (omegaPrime
          (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv hd hram hsplit hunit)
          (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
            (phiZeta f a b xQ yQ m m₀ uτ vτ d s)) i))
        * algebraMap O (FractionRing O) z₀ ^ k)
      (algebraMap O (FractionRing O) (Lam hu rfl hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe
          (diskDiffClass hf hdeg hb hfa h2 hz₀) i)) := by
  have hζ0 : ∀ s, PowerSeries.constantCoeff (phiZeta f a b xQ yQ m m₀ uτ vτ d s) = 0 :=
    fun s ↦ constantCoeff_phiZeta hf hsep hm hm₀ hb hfa h2 hyQ hu hv ⟨w, hw⟩ hgτ hcerts s
  have hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (phiZeta f a b xQ yQ m m₀ uτ vτ d j) ∈ maximalIdeal O := fun j ↦
    PSeries.eval_mem_maximalIdeal_of_constantCoeff_eq_zero hz₀ (hζ0 j)
  exact hasSum_Lam_antiderivOmegaPrime_of_polydisk hf hdeg hu hv hw hbez hfdeg hsq hroot hcc
    ha hbv hsplit hunit hd hram hpe hζ0 hz₀ _
    (J1_equiv_polydisk_diskPointDiff hf hdeg hsep hm hm₀ hb hfa h2 hyQ hu hv hw
      hbez hgτ hcerts hfdeg hsq hz₀ hζ) i

end ColemanValue

end ChabautyColeman

end
