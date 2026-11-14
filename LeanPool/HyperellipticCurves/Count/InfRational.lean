/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Count.DiskRational
public import LeanPool.HyperellipticCurves.Log.Charts.InfGlue

/-!
# The per-disk bound on the infinity residue disk (chart coverage)

The infinity-chart analogue of `LeanPool.HyperellipticCurves.Count.WeierstrassRational`: the
per-disk bound
of blueprint `thm:disk-bound` for the residue disk of `∞_bar`, in the shape `thm:main-count` sums.

* `ChabautyColeman.encard_le_of_lambda_eq_zero_inf`: the core bound. Since the disk centre
  `∞` is the Abel–Jacobi base point, every value of the integral vanishes — at `∞` because
  the antiderivative vanishes at `0`, at the rational affine points by the single-point glue
  identity (`ChabautyColeman.lambda_glue_inf`) and the annihilating property of `ω`;
* `ChabautyColeman.encard_inter_residueDisk_le_inf`: the bound for the intersection of a set
  of `K₀`-rational points with the disk of `∞_bar`, via the parametrization
  `ChabautyColeman.diskPointInf`;
* `ChabautyColeman.encard_inter_residueDisk_le_ordPoint_inf`: the same at the intrinsic
  order index `ord_∞_bar(ω_bar) = 2g - 2 - 2·deg h_bar` (`ChabautyColeman.ordPoint` at `∞`), up to
  the identification `hW` of the disk expansion of `h·dx/y` with the `ω′`-combination.

Blueprint nodes: `thm:disk-bound`/`thm:main-count` (infinity chart).
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section InfDiskRational

open ChabautyColeman.FractionTopology

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O]
  [IsAlgClosed (ResidueField O)] [Invertible (2 : O)] {C : HyperellipticCurve O} [C.IsOdd]
  {uτ vτ w c₁ c₂ : O[X]}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  {π : O} {p e ord : ℕ} {W : O⟦X⟧} (cs : Fin uτ.natDegree → FractionRing O)
  {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)] [CharZero K₀]
  {C₀ : HyperellipticCurve K₀} [C₀.IsOdd]

/-- **The per-disk bound at the infinity centre** (blueprint `thm:disk-bound`, chart
coverage): a set `S` of points of the infinity residue disk whose affine members are
rational over the arithmetic base field `K₀` has at most `1 + ord` elements. Since the disk
centre `∞` is the Abel–Jacobi base point, the glue is single-point: every value `A P` of
the integral vanishes (at `∞` because the antiderivative vanishes at `0`, elsewhere by the
annihilating property of `ω`). -/
theorem encard_le_of_lambda_eq_zero_inf
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - C.f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hgdeg : C.f.natDegree = 2 * uτ.natDegree + 1)
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
    (hW : W.map (algebraMap O (FractionRing O)) = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (infZeta C.monic_f uτ vτ s)) i)
    (hord : ord + e + 1 < p) (hmu : IsUnit (PowerSeries.coeff ord W))
    {α : Type*} {S : Set α} {ζ : α → O} {A : α → FractionRing O}
    (hζ : ∀ P ∈ S, ζ P ∈ maximalIdeal O) (hinjζ : Set.InjOn ζ S)
    (hrat : ∀ P ∈ S, ζ P ≠ 0 → ∃ x y : K₀,
      algebraMap K₀ (FractionRing O) x
          = (algebraMap O (FractionRing O) (PSeries.eval (ζ P) (infSeries C.monic_f)))⁻¹
        ∧ algebraMap K₀ (FractionRing O) y
          = (algebraMap O (FractionRing O) (ζ P))⁻¹
            * (algebraMap O (FractionRing O) (PSeries.eval (ζ P) (infSeries C.monic_f)))⁻¹
              ^ uτ.natDegree)
    (hA : ∀ P ∈ S, HasSum (fun k : ℕ ↦ PowerSeries.coeff k G
      * algebraMap O (FractionRing O) (ζ P) ^ k) (A P)) :
    S.encard ≤ 1 + ord := by
  have hG0 : PowerSeries.constantCoeff G = 0 := by simp [hG]
  have hA0 : ∀ P ∈ S, A P = 0 := by
    intro P hP
    rcases eq_or_ne (ζ P) 0 with h0 | h0
    · have h := hA P hP
      rw [h0, map_zero] at h
      have h1 : HasSum (fun k : ℕ ↦ PowerSeries.coeff k G * (0 : FractionRing O) ^ k)
          (PowerSeries.coeff 0 G * (0 : FractionRing O) ^ 0) :=
        hasSum_single 0 fun b hb ↦ by rw [zero_pow hb, mul_zero]
      rw [h.unique h1, pow_zero, mul_one,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hG0]
    · obtain ⟨x, y, hx, hy⟩ := hrat P hP h0
      have hc := mapBase_aj_eq_diskDiffClassInf C.monic_f C.natDegree_pos hgdeg hf₀ (hζ P hP) h0
        hx hy
      have hglue := lambda_glue_inf cs C.monic_f C.natDegree_pos hu hv hw hbez hvτ hgdeg hV hVdeg
        hVdvd hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG (hζ P hP) h0
        (c := ⟨_, mem_J1_of_mapBase_eq hc⟩) hc (hA P hP)
      rw [hann] at hglue
      exact hglue.symm
  have hGW : G = antideriv (W.map (algebraMap O (FractionRing O))) := by
    rw [hG, hW, antideriv_sum_smul]
  exact disk_count_le hram hord hmu hGW ζ hζ hinjζ (A := A) hA
    fun P hP Q hQ ↦ by rw [hA0 P hP, hA0 Q hQ]

/-- **The per-disk bound on the infinity residue disk, for rational points**: the points of
the disk with centre `∞_bar` that are rational over `K₀` number at most `1 + ord`. The disk
parametrization supplies parameters and coordinates; only the rationality of the affine
coordinates remains as a hypothesis. -/
theorem encard_inter_residueDisk_le_inf
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - C.f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hgdeg : C.f.natDegree = 2 * uτ.natDegree + 1)
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
    (hW : W.map (algebraMap O (FractionRing O)) = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (infZeta C.monic_f uτ vτ s)) i)
    (hord : ord + e + 1 < p) (hmu : IsUnit (PowerSeries.coeff ord W))
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀,
      P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.infinity :
        CurvePoint (ResidueField O) (C.f.map (residue O)))).encard ≤ 1 + ord := by
  classical
  have hodd : Odd C.f.natDegree := C.odd_natDegree_f
  have hgen : genus C.f = uτ.natDegree := genus_eq_of_natDegree hgdeg
  set D := S ∩ ResidueDisk (K := FractionRing O)
    (.infinity : CurvePoint (ResidueField O) (C.f.map (residue O)))
  have hpar : ∀ P ∈ D, ∃ z, ∃ hz : z ∈ maximalIdeal O,
      diskPointInf C.f C.monic_f hodd hz = P := fun P hP ↦ by
    obtain ⟨z, hz⟩ := diskPointInf_surjective C.f C.monic_f hodd (mem_residueDisk.mp hP.2)
    exact ⟨z.1, z.2, hz⟩
  choose! ζ hζm hζP using hpar
  have hinjζ : Set.InjOn ζ D := fun P hP Q hQ h ↦ by
    rw [← hζP P hP, ← hζP Q hQ, diskPointInf_congr C.monic_f hodd (hζm P hP) (hζm Q hQ) h]
  have hratζ : ∀ P ∈ D, ζ P ≠ 0 → ∃ x y : K₀,
      algebraMap K₀ (FractionRing O) x
          = (algebraMap O (FractionRing O) (PSeries.eval (ζ P) (infSeries C.monic_f)))⁻¹
        ∧ algebraMap K₀ (FractionRing O) y
          = (algebraMap O (FractionRing O) (ζ P))⁻¹
            * (algebraMap O (FractionRing O) (PSeries.eval (ζ P) (infSeries C.monic_f)))⁻¹
              ^ uτ.natDegree := by
    intro P hP h0
    have hPa : diskPointInf (K := FractionRing O) C.f C.monic_f hodd (hζm P hP)
        = .affine ((algebraMap O (FractionRing O) (infRoot C.f C.monic_f (hζm P hP)))⁻¹)
          ((algebraMap O (FractionRing O) (infRoot C.f C.monic_f (hζm P hP)) ^ genus C.f
            * algebraMap O (FractionRing O) (ζ P))⁻¹)
          (infRoot_onCurve C.f C.monic_f hodd (hζm P hP) h0) := diskPointInf_of_ne_zero _ _ _ _ h0
    have hPfull := (hζP P hP).symm.trans hPa
    have hPne : P ≠ .infinity := by rw [hPfull]; nofun
    obtain ⟨x₀, y₀, hx₀, hy₀⟩ := hrat P hP.1 hPne
    have hxc := congrArg CurvePoint.xCoord hPfull
    have hyc := congrArg CurvePoint.yCoord hPfull
    rw [CurvePoint.xCoord_affine, infRoot_eq_eval_infSeries C.monic_f (hζm P hP)] at hxc
    rw [CurvePoint.yCoord_affine, infRoot_eq_eval_infSeries C.monic_f (hζm P hP)] at hyc
    refine ⟨x₀, y₀, ?_, ?_⟩
    · rw [← hx₀, hxc]
    · rw [← hy₀, hyc, hgen, mul_inv, ← inv_pow, mul_comm]
  have hGW : G = antideriv (W.map (algebraMap O (FractionRing O))) := by
    rw [hG, hW, antideriv_sum_smul]
  obtain ⟨A₀, hA₀⟩ := exists_forall_hasSum_antideriv hram hpe W hGW
  exact encard_le_of_lambda_eq_zero_inf cs hu hv hw hbez hvτ hgdeg hV hVdeg hVdvd
    hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hW hord hmu (S := D) (ζ := ζ)
    (A := fun P ↦ A₀ (ζ P)) hζm hinjζ hratζ fun P hP ↦ hA₀ (ζ P) (hζm P hP)

/-- **The per-disk bound at the intrinsic order, infinity centre**: with `W` the disk
expansion of `ω = h·dx/y` at `∞`, the index with a unit coefficient is
`m_∞_bar = ord_∞_bar(ω_bar) = 2g - 2 - 2·deg h_bar` — the shape blueprint `thm:main-count` sums.
What stays as
the hypothesis `hW` is the identification of the expansion of `h·dx/y` with the
`ω′`-combination. -/
theorem encard_inter_residueDisk_le_ordPoint_inf {h : O[X]}
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - C.f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hgdeg : C.f.natDegree = 2 * uτ.natDegree + 1)
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
    (hW : (omegaExpansionInf h C.monic_f).map (algebraMap O (FractionRing O))
      = ∑ i, cs i • omegaPrime
      (ftauFoldFGLFrac hu rfl hv hw hbez C.monic_f hfdeg hroot hcc ha hbv hd hram hsplit hunit)
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (infZeta C.monic_f uτ vτ s)) i)
    (hord : ordInf (C.f.map (residue O)) (h.map (residue O)) + e + 1 < p)
    {S : Set (CurvePoint (FractionRing O) (C.f.map (algebraMap O (FractionRing O))))}
    (hrat : ∀ P ∈ S, P ≠ .infinity → ∃ x₀ y₀ : K₀,
      P.xCoord = algebraMap K₀ (FractionRing O) x₀
        ∧ P.yCoord = algebraMap K₀ (FractionRing O) y₀) :
    (S ∩ ResidueDisk (.infinity :
        CurvePoint (ResidueField O) (C.f.map (residue O)))).encard
      ≤ 1 + ordPoint (C.f.map (residue O)) (h.map (residue O)) .infinity := by
  have hkey := encard_inter_residueDisk_le_inf cs hu hv hw hbez hvτ hgdeg hV hVdeg
    hVdvd hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hf₀ hG hann hW hord
    (isUnit_coeff_ordInf_omegaExpansionInf C.monic_f hh hhdeg (NeZero.ne (2 : ResidueField O)))
    hrat
  rwa [ordPoint_infinity]

end InfDiskRational

end ChabautyColeman
