/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Analytic.Lambda
public import LeanPool.HyperellipticCurves.Log.Charts.WeierstrassValue

/-!
# The glue identity on a Weierstrass residue disk (chart coverage)

The mirrors of `LeanPool.HyperellipticCurves.Log.Analytic.Lambda`'s glue chain at a Weierstrass
centre
`P₀ = (ω, 0)`, for the same-disk difference `ChabautyColeman.diskDiffClassW`
(`LeanPool.HyperellipticCurves.Log.Charts.WeierstrassValue`):

* `ChabautyColeman.hasSum_lambdaOne_diskDiffClass_weierstrass`: on it, `λ_ω` is the
  convergent value of the antiderivative of the disk expansion of `ω = ∑ cs_i·ω′_i`;
* `ChabautyColeman.mapBase_aj_div_eq_diskDiffClassW`: the base change of a difference of
  two `K₀`-rational points of the disk is the same-disk difference — the 2-torsion base
  point cancels;
* `ChabautyColeman.lambda_glue_weierstrass`: the glue identity (blueprint `thm:glue`) —
  `λ_ω` of the difference of two classes is the difference of the antiderivative values at
  their parameters.
-/

@[expose] public section

open Polynomial IsLocalRing MvPowerSeries
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries

namespace ChabautyColeman

section WeierstrassGlue

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
  {π : O} {p e : ℕ} (cs : Fin uτ.natDegree → FractionRing O)

/-- **Clause (b) for `λ` at a Weierstrass centre**: on a same-disk difference the value of
`λ_ω` is the convergent `p`-adic value at `z` of the antiderivative of the disk expansion of
`ω = ∑_i cs_i·ω′_i` along the Weierstrass chart coordinates. -/
theorem hasSum_lambdaOne_diskDiffClass_weierstrass (hf : f.Monic) (hdeg : 0 < f.natDegree)
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
    {z : O} (hz : z ∈ maximalIdeal O) :
    HasSum (fun k : ℕ ↦ (∑ i, cs i * PowerSeries.coeff k (antideriv (omegaPrime
          (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv hd hram hsplit hunit)
          (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
            (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d s)) i)))
        * algebraMap O (FractionRing O) z ^ k)
      (lambdaOne hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe
        (diskDiffClassW hf hdeg hω hωu hz)) := by
  simpa only [lambdaOne] using hasSum_sum_mul_coeff cs fun i ↦
    hasSum_Lam_antiderivOmegaPrime_weierstrass hf hdeg hω hωu hsep hm hm₀ hyQ hu hv hw hbez
      hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hz i

variable {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)]
  {f₀ : K₀[X]} [Fact (Odd f₀.natDegree)]

/-- **The base change of a difference of two rational points of one Weierstrass disk is the
same-disk difference**; the base point `ιP₀ = (ω, 0)` cancels. -/
theorem mapBase_aj_div_eq_diskDiffClassW [CharZero K₀] [Fact (Squarefree f₀)]
    (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    (hf₀ : f₀.map (algebraMap K₀ (FractionRing O)) = f.map (algebraMap O (FractionRing O)))
    {z z' : O} (hz : z ∈ maximalIdeal O) (hz' : z' ∈ maximalIdeal O) {x x' y y' : K₀}
    (hx : algebraMap K₀ (FractionRing O) x
      = algebraMap O (FractionRing O) (PSeries.eval z (weierstrassSeries hf hdeg hω hωu)))
    (hy : algebraMap K₀ (FractionRing O) y = algebraMap O (FractionRing O) z)
    (hx' : algebraMap K₀ (FractionRing O) x'
      = algebraMap O (FractionRing O) (PSeries.eval z' (weierstrassSeries hf hdeg hω hωu)))
    (hy' : algebraMap K₀ (FractionRing O) y' = algebraMap O (FractionRing O) z') :
    mapBase K₀ f₀ hf₀ (aj f₀ x' y' * (aj f₀ x y)⁻¹)
      = (diskDiffClassW hf hdeg hω hωu hz' : HypJac _ _)
        * (diskDiffClassW hf hdeg hω hωu hz : HypJac _ _)⁻¹ := by
  rw [map_mul, map_inv, mapBase_aj, mapBase_aj, hx, hy, hx', hy', diskDiffClassW, diskDiffClassW]
  group

/-- **The glue identity at a Weierstrass centre** (blueprint `thm:glue`, chart coverage):
for two points of one Weierstrass residue disk, the value of `λ_ω` on the difference of
their classes is the difference of the values of the disk antiderivative at their
parameters. -/
theorem lambda_glue_weierstrass (hf : f.Monic) (hdeg : 0 < f.natDegree)
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
    (hf₀ : f₀.map (algebraMap K₀ (FractionRing O)) = f.map (algebraMap O (FractionRing O)))
    {G : PowerSeries (FractionRing O)}
    (hG : G = ∑ i, cs i • antideriv (omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d s)) i))
    {z z' : O} (hz : z ∈ maximalIdeal O) (hz' : z' ∈ maximalIdeal O)
    {c : J1 K₀ f₀ hf hdeg hf₀}
    (hc : mapBase K₀ f₀ hf₀ ↑c = (diskDiffClassW hf hdeg hω hωu hz' : HypJac _ _)
      * (diskDiffClassW hf hdeg hω hωu hz : HypJac _ _)⁻¹)
    {A A' : FractionRing O}
    (hA : HasSum (fun k : ℕ ↦ PowerSeries.coeff k G * algebraMap O (FractionRing O) z ^ k) A)
    (hA' : HasSum (fun k : ℕ ↦ PowerSeries.coeff k G * algebraMap O (FractionRing O) z' ^ k) A') :
    lambda hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c = A' - A := by
  simp only [hG, map_sum, PowerSeries.coeff_smul, smul_eq_mul] at hA hA'
  have hval := hasSum_lambdaOne_diskDiffClass_weierstrass cs hf hdeg hω hωu hsep hm hm₀ hyQ
    hu hv hw hbez hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hz
  have hval' := hasSum_lambdaOne_diskDiffClass_weierstrass cs hf hdeg hω hωu hsep hm hm₀ hyQ
    hu hv hw hbez hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hz'
  have hsub : (⟨mapBase K₀ f₀ hf₀ ↑c, c.2⟩ :
        (redJHom (K := FractionRing O) (f := f) hf hdeg).ker)
      = diskDiffClassW hf hdeg hω hωu hz' * (diskDiffClassW hf hdeg hω hωu hz)⁻¹ :=
    Subtype.ext (by simpa using hc)
  rw [lambda, hsub, lambdaOne_mul hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe,
    lambdaOne_inv hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe,
    hval.unique hA, hval'.unique hA']
  ring

end WeierstrassGlue

end ChabautyColeman

end
