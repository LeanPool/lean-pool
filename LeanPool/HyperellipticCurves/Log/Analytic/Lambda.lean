/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Analytic.ColemanValue
public import LeanPool.HyperellipticCurves.RedJ.J1

/-!
# The pairing `λ` on the Jacobian, and the glue identity

The endgame of the abelian-logarithm chapter: blueprint `def:lambda` and `thm:glue`.

`ChabautyColeman.lambdaOne` pairs a regular differential — given by its coordinates `cs` in
the `ω′`-basis — with a class in the kernel of reduction over the completed field.
`ChabautyColeman.lambda` reads it on `J¹ = ker(J(K₀) → J(κ_bar))`, the classes over the
arithmetic base field whose base change reduces trivially. It is additive and linear in the
differential; no extension beyond `J¹` is needed, since the counting chapter pairs only
same-disk difference classes, which lie in `J¹`.

`ChabautyColeman.lambda_glue` is the identity the counting chapter runs on: for two points of
one residue disk, `λ_ω` of the difference of their classes is the difference of the values of
the disk antiderivative. Its analytic content is
`ChabautyColeman.hasSum_lambdaOne_diskDiffClass` — clause (b) of `thm:omega-prime-global`
summed against the coordinates `cs`, resting on
`ChabautyColeman.hasSum_Lam_antiderivOmegaPrime`.

Blueprint nodes: `def:lambda`, `thm:glue`.
-/

@[expose] public section

open Polynomial IsLocalRing MvPowerSeries
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries

namespace ChabautyColeman

universe u

section Lambda

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  {π : O} {p e : ℕ} (cs : Fin n → FractionRing O)
  (hf : f.Monic) (hdeg : 0 < f.natDegree)
  (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
  (hsq : Squarefree (u.map (residue O))) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
  (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
  (ha : ∀ i, u.eval (a i) = 0) (hbv : ∀ i, v.eval (a i) = b i)
  (hsplit : u = ∏ m, (Polynomial.X - Polynomial.C (a m)))
  (hunit : ∀ i j, i ≠ j → IsUnit (a i - a j))
  (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
  (hram : IsUniformizer π p e) (hpe : e + 1 < p)
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)]
  {f₀ : K₀[X]} [Fact (Odd f₀.natDegree)]
  (hf₀ : f₀.map (algebraMap K₀ (FractionRing O)) = f.map (algebraMap O (FractionRing O)))

/-- `λ` on the inverse of a kernel class (blueprint `def:lambda1`). -/
theorem lambdaOne_inv (c : (redJHom (K := FractionRing O) (f := f) hf hdeg).ker) :
    lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe c⁻¹
      = -lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe c := by
  have h := lambdaOne_mul hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
      hsplit hunit hd hram hpe c c⁻¹
  rw [mul_inv_cancel, lambdaOne_one hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
      hsplit hunit hd hram hpe] at h
  linear_combination -h

/-- **The pairing `λ` on the kernel of reduction** (blueprint `def:lambda`): the value of
`ChabautyColeman.lambdaOne` at the base change of a class in
`J¹ = ker(J(K₀) → J(K) → J(κ_bar))`. Restricting to `J¹` costs nothing downstream: the classes
the counting chapter pairs are same-disk differences of rational points, which lie in `J¹`,
and the rank of `J¹` is bounded by the rank of `J(K₀)`, so the rank hypothesis still
produces an annihilating differential. -/
noncomputable def lambda (c : J1 K₀ f₀ hf hdeg hf₀) : FractionRing O :=
  lambdaOne hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe
    ⟨mapBase K₀ f₀ hf₀ ↑c, c.2⟩

/-- **`λ` is a homomorphism on `J¹`** (blueprint `thm:glue`, first half):
the class group is written multiplicatively and `λ` is additive. -/
theorem lambda_mul (c c' : J1 K₀ f₀ hf hdeg hf₀) :
    lambda hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ (c * c')
      = lambda hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe hf₀ c
        + lambda hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
            hsplit hunit hd hram hpe hf₀ c' := by
  have hsub : (⟨mapBase K₀ f₀ hf₀ ↑(c * c'), (c * c').2⟩ :
        (redJHom (K := FractionRing O) (f := f) hf hdeg).ker)
      = ⟨mapBase K₀ f₀ hf₀ ↑c, c.2⟩ * ⟨mapBase K₀ f₀ hf₀ ↑c', c'.2⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])
  rw [lambda, lambda, lambda, hsub,
    lambdaOne_mul hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe]

/-- **`λ` is additive in the differential** (blueprint `thm:glue`: `λ` is `ℚ_p`-linear as a
map `RegDiff → Hom(J¹, ℚ_p)`), in the `ω′`-coordinates of the differential. -/
theorem lambda_add_left (cs' : Fin n → FractionRing O) (c : J1 K₀ f₀ hf hdeg hf₀) :
    lambda hu hne hv hw hbez (cs + cs') hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c
      = lambda hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe hf₀ c
        + lambda hu hne hv hw hbez cs' hf hdeg hfdeg hsq hroot hcc ha hbv
            hsplit hunit hd hram hpe hf₀ c := by
  rw [lambda, lambda, lambda,
    lambdaOne_add_left hu hne hv hw hbez cs cs' hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe]

/-- **`λ` is homogeneous in the differential** (blueprint `thm:glue`). -/
theorem lambda_smul_left (r : FractionRing O) (c : J1 K₀ f₀ hf hdeg hf₀) :
    lambda hu hne hv hw hbez (r • cs) hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c
      = r * lambda hu hne hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
          hsplit hunit hd hram hpe hf₀ c := by
  rw [lambda, lambda, lambdaOne_smul_left hu hne hv hw hbez r cs hf hdeg hfdeg hsq
      hroot hcc ha hbv hsplit hunit hd hram hpe]

end Lambda

section Glue

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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
  {π : O} {p e : ℕ} (cs : Fin uτ.natDegree → FractionRing O)

/-- **Clause (b) for `λ`**: on a same-disk difference the value of `λ_ω` is the convergent
`p`-adic value at `z` of the antiderivative of the disk expansion of
`ω = ∑_i cs_i·ω′_i`, i.e. the Coleman integral `∫_{P₀}^{P_z} ω`. This is
`ChabautyColeman.hasSum_Lam_antiderivOmegaPrime` scaled by the coordinates `cs` and summed
over the basis. -/
theorem hasSum_lambdaOne_diskDiffClass (hf : f.Monic) (hdeg : 0 < f.natDegree)
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
    {z : O} (hz : z ∈ maximalIdeal O) :
    HasSum (fun k : ℕ ↦ (∑ i, cs i * PowerSeries.coeff k (antideriv (omegaPrime
          (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv hd hram hsplit hunit)
          (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
            (phiZeta f a b xQ yQ m m₀ uτ vτ d s)) i)))
        * algebraMap O (FractionRing O) z ^ k)
      (lambdaOne hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe
        (diskDiffClass hf hdeg hb hfa h2 hz)) := by
  simpa only [lambdaOne] using hasSum_sum_mul_coeff cs fun i ↦
    hasSum_Lam_antiderivOmegaPrime hf hdeg hsep hm hm₀ hb hfa h2 hyQ hu hv hw hbez hgτ hcerts
      hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hz i

variable {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)]
  {f₀ : K₀[X]} [Fact (Odd f₀.natDegree)]

/-- **The base change of a difference of two rational points of one disk is the same-disk
difference**. This discharges the hypothesis `hc` of `ChabautyColeman.lambda_glue` for the
class of a difference of two `K₀`-rational points whose coordinates are those of the disk
points at the parameters `z` and `z'`; the base point `ιP₀` of
`ChabautyColeman.diskDiffClass` cancels. -/
theorem mapBase_aj_div_eq_diskDiffClass [CharZero K₀] [Fact (Squarefree f₀)]
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a))
    (h2 : IsUnit (2 : O))
    (hf₀ : f₀.map (algebraMap K₀ (FractionRing O)) = f.map (algebraMap O (FractionRing O)))
    {z z' : O} (hz : z ∈ maximalIdeal O) (hz' : z' ∈ maximalIdeal O) {x x' y y' : K₀}
    (hx : algebraMap K₀ (FractionRing O) x = algebraMap O (FractionRing O) (a + z))
    (hy : algebraMap K₀ (FractionRing O) y = algebraMap O (FractionRing O)
      (PSeries.eval z (PowerSeries.C b * diskSeriesGeneric f a)))
    (hx' : algebraMap K₀ (FractionRing O) x' = algebraMap O (FractionRing O) (a + z'))
    (hy' : algebraMap K₀ (FractionRing O) y' = algebraMap O (FractionRing O)
      (PSeries.eval z' (PowerSeries.C b * diskSeriesGeneric f a))) :
    mapBase K₀ f₀ hf₀ (aj f₀ x' y' * (aj f₀ x y)⁻¹)
      = (diskDiffClass hf hdeg hb hfa h2 hz' : HypJac _ _)
        * (diskDiffClass hf hdeg hb hfa h2 hz : HypJac _ _)⁻¹ := by
  rw [map_mul, map_inv, mapBase_aj, mapBase_aj, hx, hy, hx', hy', diskDiffClass, diskDiffClass]
  group

/-- **The glue identity** (blueprint `thm:glue`): for two points of one residue disk, the
value of `λ_ω` on the difference of their classes is the difference of the values of the
disk antiderivative `G^ω_D` at their parameters.

The two identifications that connect this to the blueprint statement are hypotheses, in the
certificate-passing style of `ChabautyColeman.lambdaOne_rational_values`
(`upstream HyperellipticCurves.Archive.RationalValues`):

* `hG` says that `G` is the antiderivative of the disk expansion of `ω = ∑_i cs_i·ω′_i`
  (which for a regular `ω` written in the `ω′`-basis is `G^ω_D` of blueprint
  `def:disk-antider`);
* `hc` says that the class `c` over the arithmetic base field base-changes to the same-disk
  difference of the two disk points (for a `ℚ_p`-rational point of the disk this is the
  disk parametrization of `lem:disk-decomp`, together with
  `ChabautyColeman.HypJac.map_aj`).

Given those, the identity itself is `ChabautyColeman.hasSum_lambdaOne_diskDiffClass` at the
two parameters, uniqueness of sums, and additivity of `λ`. -/
theorem lambda_glue (hf : f.Monic) (hdeg : 0 < f.natDegree)
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
    (hf₀ : f₀.map (algebraMap K₀ (FractionRing O)) = f.map (algebraMap O (FractionRing O)))
    {G : PowerSeries (FractionRing O)}
    (hG : G = ∑ i, cs i • antideriv (omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (phiZeta f a b xQ yQ m m₀ uτ vτ d s)) i))
    {z z' : O} (hz : z ∈ maximalIdeal O) (hz' : z' ∈ maximalIdeal O)
    {c : J1 K₀ f₀ hf hdeg hf₀}
    (hc : mapBase K₀ f₀ hf₀ ↑c = (diskDiffClass hf hdeg hb hfa h2 hz' : HypJac _ _)
      * (diskDiffClass hf hdeg hb hfa h2 hz : HypJac _ _)⁻¹)
    {A A' : FractionRing O}
    (hA : HasSum (fun k : ℕ ↦ PowerSeries.coeff k G * algebraMap O (FractionRing O) z ^ k) A)
    (hA' : HasSum (fun k : ℕ ↦ PowerSeries.coeff k G * algebraMap O (FractionRing O) z' ^ k) A') :
    lambda hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c = A' - A := by
  simp only [hG, map_sum, PowerSeries.coeff_smul, smul_eq_mul] at hA hA'
  have hval := hasSum_lambdaOne_diskDiffClass cs hf hdeg hsep hm hm₀ hb hfa h2 hyQ hu hv hw
    hbez hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hz
  have hval' := hasSum_lambdaOne_diskDiffClass cs hf hdeg hsep hm hm₀ hb hfa h2 hyQ hu hv hw
    hbez hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hz'
  have hsub : (⟨mapBase K₀ f₀ hf₀ ↑c, c.2⟩ :
        (redJHom (K := FractionRing O) (f := f) hf hdeg).ker)
      = diskDiffClass hf hdeg hb hfa h2 hz' * (diskDiffClass hf hdeg hb hfa h2 hz)⁻¹ :=
    Subtype.ext (by simpa using hc)
  rw [lambda, hsub, lambdaOne_mul hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe,
    lambdaOne_inv hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe,
    hval.unique hA, hval'.unique hA']
  ring

end Glue

end ChabautyColeman

end
