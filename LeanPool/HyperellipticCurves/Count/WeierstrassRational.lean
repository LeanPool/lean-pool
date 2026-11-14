/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Count.DiskRational
public import LeanPool.HyperellipticCurves.Log.Charts.WeierstrassGlue

/-!
# The per-disk bound on a Weierstrass residue disk (chart coverage)

`ChabautyColeman.encard_le_of_lambda_eq_zero_weierstrass` is the mirror of
`ChabautyColeman.encard_le_of_lambda_eq_zero` at a Weierstrass centre `P₀ = (ω, 0)`: a set
of `K₀`-rational points of the disk has at most `1 + ord` elements, where `ord` is any index
with a unit coefficient in the disk expansion `W` of the differential. The disk parameter is
the `y`-coordinate itself, the coordinates of a point of the disk are
`(W(ζ P), ζ P)`, and the constancy of the Coleman integral comes from
`ChabautyColeman.lambda_glue_weierstrass` and the annihilator.

`ChabautyColeman.encard_inter_residueDisk_le_weierstrass` restates the bound in the shape
blueprint `thm:main-count` sums: for `S ∩ ResidueDisk (ω_bar, 0)` with `S` a set of `K₀`-rational
points, the parametrization (`ChabautyColeman.diskPointWeierstrass_surjective`, identified
with the series parametrization by `ChabautyColeman.weierstrassRoot_eq_eval_weierstrassSeries`)
producing all inputs; and `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_weierstrass`
instantiates the index at the intrinsic order `ordPoint` via
`ChabautyColeman.isUnit_coeff_ordAffine_omegaExpansionWeierstrass`, leaving only the
identification `hW` of the expansion of `h·dx/y` with the `ω′`-combination.
-/

@[expose] public section

open Polynomial IsLocalRing MvPowerSeries
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology
open scoped PowerSeries

namespace ChabautyColeman

section WeierstrassDiskRational

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O]
  [IsAlgClosed (ResidueField O)] [Invertible (2 : O)] {C : HyperellipticCurve O} [C.IsOdd]
  {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  {π : O} {p e ord : ℕ} {W : O⟦X⟧} (cs : Fin uτ.natDegree → FractionRing O)
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]

/-- **The per-disk bound at a Weierstrass centre** (blueprint `thm:disk-bound`, chart
coverage): a set `S` of points of one Weierstrass residue disk that are rational over the
arithmetic base field `K₀` has at most `1 + ord` elements, where `ord` is any index with a
unit coefficient in the disk expansion `W` of the differential `ω = ∑_i cs_i·ω′_i` and
`p > ord + e + 1`. The disk parameter is the `y`-coordinate, so the parameter map is injective
as soon as the points are determined by their coordinates. -/
theorem encard_le_of_lambda_eq_zero_weierstrass
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
    (hW : W.map (algebraMap O (FractionRing O)) = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (wZeta C.monic_f C.natDegree_pos hω hωu xQ yQ m m₀ uτ vτ d s)) i)
    (hord : ord + e + 1 < p) (hmu : IsUnit (PowerSeries.coeff ord W))
    {α : Type*} {S : Set α} {ζ : α → O} {x y : α → K₀} {A : α → FractionRing O}
    (hζ : ∀ P ∈ S, ζ P ∈ maximalIdeal O) (hinjζ : Set.InjOn ζ S)
    (hx : ∀ P ∈ S, algebraMap K₀ (FractionRing O) (x P) = algebraMap O (FractionRing O)
      (PSeries.eval (ζ P) (weierstrassSeries C.monic_f C.natDegree_pos hω hωu)))
    (hy : ∀ P ∈ S, algebraMap K₀ (FractionRing O) (y P) = algebraMap O (FractionRing O) (ζ P))
    (hA : ∀ P ∈ S, HasSum (fun k : ℕ ↦ PowerSeries.coeff k G
      * algebraMap O (FractionRing O) (ζ P) ^ k) (A P)) :
    S.encard ≤ 1 + ord := by
  -- the integral `G` is the antiderivative of the disk expansion `W`, which is integral
  have hGW : G = antideriv (W.map (algebraMap O (FractionRing O))) := by
    rw [hG, hW, antideriv_sum_smul]
  refine disk_count_le hram hord hmu hGW ζ hζ hinjζ hA fun P hP Q hQ ↦ ?_
  -- the two values differ by `λ_ω` of the difference of the two classes, which vanishes
  have hc := mapBase_aj_div_eq_diskDiffClassW C.monic_f C.natDegree_pos hω hωu hf₀ (hζ P hP)
    (hζ Q hQ) (hx P hP) (hy P hP) (hx Q hQ) (hy Q hQ)
  have h := lambda_glue_weierstrass cs C.monic_f C.natDegree_pos hω hωu hsep hm hm₀ hyQ hu hv hw
    hbez hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG (hζ P hP) (hζ Q hQ)
    (c := ⟨_, mem_J1_of_mapBase_eq_div hc⟩) hc (hA P hP) (hA Q hQ)
  rw [hann] at h
  linear_combination h

end WeierstrassDiskRational

section WeierstrassDiskWrappers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O]
  [IsAlgClosed (ResidueField O)] [Invertible (2 : O)] {C : HyperellipticCurve O} [C.IsOdd]
  {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  {π : O} {p e ord : ℕ} {W : O⟦X⟧} (cs : Fin uτ.natDegree → FractionRing O)
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]

/-- **The per-disk bound on a Weierstrass residue disk, for rational points**: the points of
the disk with centre `(ω_bar, 0)` that are rational over `K₀` number at most `1 + ord`. The disk
parametrization supplies the parameters (the `y`-coordinates), coordinates and convergence
data; only the rationality of the coordinates remains as a hypothesis. -/
theorem encard_inter_residueDisk_le_weierstrass
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
    (hW : W.map (algebraMap O (FractionRing O)) = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (wZeta C.monic_f C.natDegree_pos hω hωu xQ yQ m m₀ uτ vτ d s)) i)
    (hord : ord + e + 1 < p) (hmu : IsUnit (PowerSeries.coeff ord W))
        {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.affine (residue O ω) 0
        (onCurve_map_of_root _ hω))).encard
      ≤ 1 + ord := by
  classical
  set D := S ∩ ResidueDisk (K := FractionRing O)
    (.affine (residue O ω) 0 (onCurve_map_of_root _ hω))
  have hpar : ∀ P ∈ D, ∃ z, ∃ hz : z ∈ maximalIdeal O,
      diskPointWeierstrass C.monic_f C.natDegree_pos hω hωu hz = P := fun P hP ↦ by
    obtain ⟨z, hz⟩ := diskPointWeierstrass_surjective C.monic_f C.natDegree_pos hω hωu
      (mem_residueDisk.mp hP.2)
    exact ⟨z.1, z.2, hz⟩
  choose! ζ hζm hζP using hpar
  have hrat' : ∀ P ∈ D, ∃ x₀ y₀ : K₀,
      P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀ := fun P hP ↦ hrat P hP.1
  choose! x y hx hy using hrat'
  have hxeq : ∀ P ∈ D, algebraMap K₀ (FractionRing O) (x P)
      = algebraMap O (FractionRing O)
        (PSeries.eval (ζ P) (weierstrassSeries C.monic_f C.natDegree_pos hω hωu)) := fun P hP ↦ by
    have h := congrArg CurvePoint.xCoord (hζP P hP)
    simp only [xCoord_diskPointWeierstrass] at h
    rw [← hx P hP,
      ← weierstrassRoot_eq_eval_weierstrassSeries C.monic_f C.natDegree_pos hω hωu (hζm P hP)]
    exact h.symm
  have hyeq : ∀ P ∈ D, algebraMap K₀ (FractionRing O) (y P)
      = algebraMap O (FractionRing O) (ζ P) := fun P hP ↦ by
    have h := congrArg CurvePoint.yCoord (hζP P hP)
    simp only [yCoord_diskPointWeierstrass] at h
    rw [← hy P hP]
    exact h.symm
  have hinjζ : Set.InjOn ζ D := fun P hP Q hQ h ↦ by
    rw [← hζP P hP, ← hζP Q hQ,
      diskPointWeierstrass_congr C.monic_f C.natDegree_pos hω hωu (hζm P hP) (hζm Q hQ) h]
  have hGW : G = antideriv (W.map (algebraMap O (FractionRing O))) := by
    rw [hG, hW, antideriv_sum_smul]
  obtain ⟨A₀, hA₀⟩ := exists_forall_hasSum_antideriv hram hpe W hGW
  exact encard_le_of_lambda_eq_zero_weierstrass cs hω hωu hsep hm hm₀ hyQ hu hv hw
    hbez hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hW hord hmu
    (S := D) (ζ := ζ) (x := x) (y := y) (A := fun P ↦ A₀ (ζ P))
    hζm hinjζ hxeq hyeq fun P hP ↦ hA₀ (ζ P) (hζm P hP)

/-- **The per-disk bound at the intrinsic order, Weierstrass centre**: with `W` the disk
expansion of `ω = h·dx/y` at the centre `(ω_bar, 0)`, the index with a unit coefficient is
`m_P_bar = ord_P_bar(ω_bar)` — the shape blueprint `thm:main-count` sums. What stays as the
hypothesis `hW`
is the identification of the expansion of `h·dx/y` with the `ω′`-combination. -/
theorem encard_inter_residueDisk_le_ordPoint_weierstrass {h : O[X]}
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
    (hW : (omegaExpansionWeierstrass h C.monic_f C.natDegree_pos hω hωu).map
      (algebraMap O (FractionRing O)) = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O))
        (wZeta C.monic_f C.natDegree_pos hω hωu xQ yQ m m₀ uτ vτ d s)) i)
    (hord : ordAffine (C.f.map (residue O)) (h.map (residue O)) (residue O ω) 0 + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, ∃ x₀ y₀ : K₀, P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.affine (residue O ω) 0
        (onCurve_map_of_root _ hω))).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h.map (residue O))
          (.affine (residue O ω) 0
            (onCurve_map_of_root _ hω)) := by
  have hkey := encard_inter_residueDisk_le_weierstrass cs hω hωu hsep hm hm₀ hyQ hu hv
    hw hbez hgτ hcerts hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hW hord
    (isUnit_coeff_ordAffine_omegaExpansionWeierstrass C.monic_f C.natDegree_pos hω hωu hh
      (NeZero.ne (2 : ResidueField O))) hrat
  rwa [ordPoint_affine]

end WeierstrassDiskWrappers

end ChabautyColeman

end
