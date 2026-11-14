/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Count.DiskBound
public import LeanPool.HyperellipticCurves.Curve.Basic
public import LeanPool.HyperellipticCurves.Disks.OrdMatchIntrinsic
public import LeanPool.HyperellipticCurves.Log.Analytic.Lambda

/-!
# The per-disk bound for rational points

Blueprint `thm:disk-bound`, assembled: `ChabautyColeman.encard_le_of_lambda_eq_zero` bounds
by `1 + ord` the number of points of a residue disk that are rational over the arithmetic
base field `K₀`, given a differential annihilating the Jacobian.

The two hypotheses that `ChabautyColeman.disk_count_le` left open are supplied here from the
`K₀`-rationality of the points, which enters as the two coordinate identities `hx`, `hy`:

* *distinctness of the parameters* — the coordinates of a point are those of the parametrized
  disk point at its parameter, so equal parameters give equal coordinates, hence equal points;
* *constancy of the Coleman integral* — this is blueprint `thm:glue`
  (`ChabautyColeman.lambda_glue`, applied to the difference class of the two points via
  `ChabautyColeman.mapBase_aj_div_eq_diskDiffClass`) composed with the annihilating property
  of the differential (blueprint `thm:annihilator`,
  `ChabautyColeman.exists_annihilator_tracePoly`), which makes both `λ_ω`-values zero.

`ChabautyColeman.encard_inter_residueDisk_le` restates the bound in the shape blueprint
`thm:main-count` sums over the disks: for `S ∩ ResidueDisk (ā, b_bar)` with `S` a set of
`K₀`-rational
points. The abstract parameter interface of `encard_le_of_lambda_eq_zero` is discharged by
the disk parametrization (blueprint `lem:disk-param`,
`ChabautyColeman.diskPointGeneric_surjective`): the parameters, the coordinate identities,
the injectivity, and the value of the Coleman integral (via
`ChabautyColeman.exists_forall_hasSum_antideriv`) are all produced, leaving only the
rationality of the coordinates as a hypothesis.

Blueprint node: `thm:disk-bound`.
-/

@[expose] public section

open Polynomial IsLocalRing MvPowerSeries
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries

namespace ChabautyColeman

section DiskRational

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
  {π : O} {p e ord : ℕ} {W : O⟦X⟧} (cs : Fin uτ.natDegree → FractionRing O)
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]

/-- **The per-disk bound** (blueprint `thm:disk-bound`): a set `S` of points of one residue
disk that are rational over the arithmetic base field `K₀` has at most `1 + ord` elements,
where `ord` is any index with a unit coefficient in the disk expansion `W` of the
differential `ω = ∑_i cs_i·ω′_i` (for `ord = ord_P_bar(ω_bar)` this is the sharpest bound) and
`p > ord + e + 1`.

The hypotheses fall into four groups: the certificate data of `ChabautyColeman.lambda_glue`
(everything up to `hG`, which says that `G` is the antiderivative of the disk expansion of
`ω`); the annihilating property `hann` of `ω`, which blueprint `thm:annihilator`
(`ChabautyColeman.exists_annihilator_tracePoly`) provides under the rank hypothesis; the
normalization of `ω` — `hW` says that its disk expansion is the *integral* series `W`
(blueprint `lem:normalize`), and `hmu`, `hord` that `W` has a unit coefficient in degree
`ord < p - 2`; and the rational points themselves, given by their parameters `ζ` in the
maximal ideal and their coordinates `x`, `y` over `K₀` — `hx` and `hy` say that those are
the coordinates of the
parametrized disk point at `ζ P` (blueprint `lem:disk-param`), and `hinjζ` that a point of
`S` is determined by its parameter. -/
theorem encard_le_of_lambda_eq_zero (hsep : IsUnit (xQ - a))
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
    (hW : W.map (algebraMap O (FractionRing O)) = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (phiZeta C.f a b xQ yQ m m₀ uτ vτ d s)) i)
    (hord : ord + e + 1 < p) (hmu : IsUnit (PowerSeries.coeff ord W))
    {α : Type*} {S : Set α} {ζ : α → O} {x y : α → K₀} {A : α → FractionRing O}
    (hζ : ∀ P ∈ S, ζ P ∈ maximalIdeal O) (hinjζ : Set.InjOn ζ S)
    (hx : ∀ P ∈ S, algebraMap K₀ (FractionRing O) (x P) = algebraMap O (FractionRing O) (a + ζ P))
    (hy : ∀ P ∈ S, algebraMap K₀ (FractionRing O) (y P) = algebraMap O (FractionRing O)
      (PSeries.eval (ζ P) (PowerSeries.C b * diskSeriesGeneric C.f a)))
    (hA : ∀ P ∈ S, HasSum (fun k : ℕ ↦ PowerSeries.coeff k G
      * algebraMap O (FractionRing O) (ζ P) ^ k) (A P)) :
    S.encard ≤ 1 + ord := by
  have h2 : IsUnit (2 : O) := isUnit_of_invertible 2
  -- the integral `G` is the antiderivative of the disk expansion `W`, which is integral
  have hGW : G = antideriv (W.map (algebraMap O (FractionRing O))) := by
    rw [hG, hW, antideriv_sum_smul]
  refine disk_count_le hram hord hmu hGW ζ hζ hinjζ hA fun P hP Q hQ ↦ ?_
  -- the two values differ by `λ_ω` of the difference of the two classes, which vanishes
  have hc := mapBase_aj_div_eq_diskDiffClass C.monic_f C.natDegree_pos hb hfa h2 hf₀ (hζ P hP)
    (hζ Q hQ) (hx P hP) (hy P hP) (hx Q hQ) (hy Q hQ)
  have h := lambda_glue cs C.monic_f C.natDegree_pos hsep hm hm₀ hb hfa h2 hyQ hu hv hw hbez hgτ
    hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG (hζ P hP) (hζ Q hQ)
    (c := ⟨_, mem_J1_of_mapBase_eq_div hc⟩) hc (hA P hP) (hA Q hQ)
  rw [hann] at h
  linear_combination h

/-- **The per-disk bound on a generic residue disk, for rational points**
(blueprint `thm:disk-bound` in the shape blueprint `thm:main-count` sums): the points of a residue
disk with centre `(ā, b_bar)`, `b_bar ≠ 0`, that are rational over the arithmetic base field `K₀`
number at most `1 + ord`. The disk parametrization supplies the parameters, coordinates and
convergence data of `ChabautyColeman.encard_le_of_lambda_eq_zero`; the rationality of the
points enters as `hrat`, and `hinjζ` is free because the disk parametrization is
injective. -/
theorem encard_inter_residueDisk_le (hsep : IsUnit (xQ - a))
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
    (hW : W.map (algebraMap O (FractionRing O)) = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (phiZeta C.f a b xQ yQ m m₀ uτ vτ d s)) i)
    (hord : ord + e + 1 < p) (hmu : IsUnit (PowerSeries.coeff ord W))
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.affine (residue O a) (residue O b)
        (onCurve_map _ hb))).encard ≤ 1 + ord := by
  have h2 : IsUnit (2 : O) := isUnit_of_invertible 2
  set D := S ∩ ResidueDisk (K := FractionRing O)
    (.affine (residue O a) (residue O b) (onCurve_map _ hb))
  -- every point of the disk is the parametrized point at a unique parameter in `𝔪`
  have hpar : ∀ P ∈ D, ∃ z, ∃ hz : z ∈ maximalIdeal O,
      diskPointGeneric C.f hb hfa h2 hz = P := fun P hP ↦ by
    obtain ⟨z, hz⟩ := diskPointGeneric_surjective hb hfa h2 (mem_residueDisk.mp hP.2)
    exact ⟨z.1, z.2, hz⟩
  choose! ζ hζm hζP using hpar
  -- the `K₀`-coordinates of the points
  have hrat' : ∀ P ∈ D, ∃ x₀ y₀ : K₀,
      P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀ := fun P hP ↦ hrat P hP.1
  choose! x y hx hy using hrat'
  -- the coordinate identities of `lem:disk-param`
  have hxeq : ∀ P ∈ D, algebraMap K₀ (FractionRing O) (x P)
      = algebraMap O (FractionRing O) (a + ζ P) := fun P hP ↦ by
    have h := congrArg CurvePoint.xCoord (hζP P hP)
    simp only [xCoord_diskPointGeneric] at h
    rw [← hx P hP]
    exact h.symm
  have hyeq : ∀ P ∈ D, algebraMap K₀ (FractionRing O) (y P) = algebraMap O (FractionRing O)
      (PSeries.eval (ζ P) (PowerSeries.C b * diskSeriesGeneric C.f a)) := fun P hP ↦ by
    have h := congrArg CurvePoint.yCoord (hζP P hP)
    simp only [yCoord_diskPointGeneric] at h
    rw [← hy P hP, PSeries.eval_mul (hζm P hP), PSeries.eval_C]
    exact h.symm
  -- a point of the disk is determined by its parameter
  have hinjζ : Set.InjOn ζ D := fun P hP Q hQ h ↦ by
    rw [← hζP P hP, ← hζP Q hQ, diskPointGeneric_congr hb hfa h2 (hζm P hP) (hζm Q hQ) h]
  -- the value of the Coleman integral: the substituted antiderivative converges on `𝔪`
  have hGW : G = antideriv (W.map (algebraMap O (FractionRing O))) := by
    rw [hG, hW, antideriv_sum_smul]
  obtain ⟨A₀, hA₀⟩ := exists_forall_hasSum_antideriv hram hpe W hGW
  exact encard_le_of_lambda_eq_zero cs hsep hm hm₀ hb hfa hyQ hu hv hw hbez hgτ
    hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hW hord hmu
    (S := D) (ζ := ζ) (x := x) (y := y) (A := fun P ↦ A₀ (ζ P))
    hζm hinjζ hxeq hyeq fun P hP ↦ hA₀ (ζ P) (hζm P hP)

/-- **The per-disk bound at the intrinsic order** (blueprint `thm:disk-bound` composed with
`lem:ord-match`): with `W` the disk expansion of `ω = h·dx/y` at the generic centre `(ā, b_bar)`,
the index with a unit coefficient *is* `m_P_bar = ord_P_bar(ω_bar)` — the shape blueprint
`thm:main-count`
sums via `ChabautyColeman.ratPoints_encard_le`. The identification of the expansion of
`h·dx/y` with the `ω′`-combination stays as the hypothesis `hW` (blueprint
`thm:omega-prime-global`, clause (c)). -/
theorem encard_inter_residueDisk_le_ordPoint {h : O[X]} (hsep : IsUnit (xQ - a))
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
    (hW : (omegaExpansionGeneric C.f h a b).map (algebraMap O (FractionRing O))
      = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (phiZeta C.f a b xQ yQ m m₀ uτ vτ d s)) i)
    (hord :
      ordAffine (C.f.map (residue O)) (h.map (residue O)) (residue O a) (residue O b) + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.affine (residue O a) (residue O b)
        (onCurve_map _ hb))).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h.map (residue O))
          (.affine (residue O a) (residue O b)
            (onCurve_map _ hb)) := by
  have hkey := encard_inter_residueDisk_le cs hsep hm hm₀ hb hfa hyQ hu hv hw hbez
    hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hW hord
    (isUnit_coeff_ordAffine_omegaExpansionGeneric hb hfa hh) hrat
  rwa [ordPoint_affine]

end DiskRational

end ChabautyColeman

end
