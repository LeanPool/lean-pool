/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Analytic.ColemanValue
public import LeanPool.HyperellipticCurves.Log.Charts.WeierstrassIdentification

/-!
# The Coleman integral on a Weierstrass residue disk (chart coverage)

`ChabautyColeman.hasSum_Lam_antiderivOmegaPrime_weierstrass` is numerical clause (b) of
`thm:omega-prime-global` at a Weierstrass centre: for the same-disk difference
`ChabautyColeman.diskDiffClassW`, `[P_{z₀}] - [P₀]` — with `P_{z₀} = (W(z₀), z₀)` the moving
disk point and `P₀ = (ω, 0)` the 2-torsion centre — the value of `Lam` in the fraction field
is the convergent `p`-adic integral of the pulled-back invariant differential along the
Weierstrass disk chart
coordinates `ChabautyColeman.wZeta`. The proof is the generic one with the Weierstrass
geometric identifications of `LeanPool.HyperellipticCurves.Log.Charts.WeierstrassIdentification`
substituted;
the analytic layers (`ChabautyColeman.hasSum_algebraMap_Lam`, the Fubini reindexing, and the formal
antiderivative identity) are chart-independent.
-/

@[expose] public section

open Polynomial IsLocalRing MvPowerSeries
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries

namespace ChabautyColeman

section WeierstrassColemanValue

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O] [CharZero (FractionRing O)]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  {π : O} {p e : ℕ}

/-- The same-disk difference `[P_z] - [P₀]` on the Weierstrass residue disk with the
2-torsion centre `P₀ = (ω, 0)`, as an element of `J¹ = ker(redJ)`: the disk point at
parameter `z ∈ 𝔪` is `(W(z), z)`. Membership in the kernel is
`ChabautyColeman.redJ_diskPointDiff_eq_one_weierstrass`. -/
noncomputable def diskDiffClassW (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    {z : O} (hz : z ∈ maximalIdeal O) :
    (redJHom (K := FractionRing O) (f := f) hf hdeg).ker :=
  ⟨aj (f.map (algebraMap O (FractionRing O)))
      (algebraMap O (FractionRing O) (PSeries.eval z (weierstrassSeries hf hdeg hω hωu)))
      (algebraMap O (FractionRing O) z)
    * aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) ω)
      (algebraMap O (FractionRing O) (-(0 : O))),
    MonoidHom.mem_ker.mpr (redJ_diskPointDiff_eq_one_weierstrass hf hdeg hω hωu hz)⟩

/-- **Numerical clause (b) at a Weierstrass centre**: for the same-disk difference
`c = [P_{z₀}] - [P₀]` — with `P_{z₀} = (W(z₀), z₀)` and `P₀ = (ω, 0)` the 2-torsion
centre — the image of `Lam c i` in `K = FractionRing O` is the convergent `p`-adic Coleman
integral of `ω′_i` from the disk centre to `z₀`, i.e. the value at `z₀` of the
antiderivative of the pulled-back invariant differential along the Weierstrass disk chart
coordinates `wZeta`. -/
theorem hasSum_Lam_antiderivOmegaPrime_weierstrass (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
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
            (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d s)) i))
        * algebraMap O (FractionRing O) z₀ ^ k)
      (algebraMap O (FractionRing O) (Lam hu rfl hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe
          (diskDiffClassW hf hdeg hω hωu hz₀) i)) := by
  have hζ0 : ∀ s, PowerSeries.constantCoeff (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d s) = 0 :=
    fun s ↦ constantCoeff_wZeta hf hdeg hω hωu hsep hm hm₀ hyQ hu hv ⟨w, hw⟩ hgτ hcerts s
  have hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j) ∈ maximalIdeal O := fun j ↦
    PSeries.eval_mem_maximalIdeal_of_constantCoeff_eq_zero hz₀ (hζ0 j)
  exact hasSum_Lam_antiderivOmegaPrime_of_polydisk hf hdeg hu hv hw hbez hfdeg hsq hroot hcc
    ha hbv hsplit hunit hd hram hpe hζ0 hz₀ _
    (J1_equiv_polydisk_diskPointDiff_weierstrass hf hdeg hω hωu hsep hm hm₀ hyQ
      hu hv hw hbez hgτ hcerts hfdeg hsq hz₀ hζ) i

end WeierstrassColemanValue

end ChabautyColeman

end
