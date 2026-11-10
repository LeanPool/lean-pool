/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Charts.PhiChart
public import LeanPool.HyperellipticCurves.Log.Ftau.ChartMem

/-!
# Identifying the disk-point difference with a chart coordinate (geometric step of (b))

The numerical form of `thm:omega-prime-global`(b) needs the same-disk difference class
`c := [P_{z₀}] - [P₀]` — for a disk point `z₀`, the class of the disk point `P_{z₀}` minus
the disk center `P₀` — to be identified, as a kernel element of `redJHom`, with the polydisk
point `ζ(z₀) = ` (`phiZeta` evaluated at `z₀`), i.e. its chart coordinates. This file builds
that identification.

Reduction side: `ChabautyColeman.redJ_diskPointDiff_eq_one` — the class `[P_{z₀}] · [ιP₀]`
(`ιP₀` the hyperelliptic involute of the center) reduces to `1`, since `P_{z₀}` and `P₀` have
the same reduction (both reduce to the disk center over the residue field). This realizes `c`
as an element of `(redJHom …).ker`. The helper `ChabautyColeman.aj_eq_mk0_mumfordIdeal`
identifies the Mumford-ideal point classes of `ChabautyColeman.mk0_phiPipeline_eval` with
values of the Abel–Jacobi map `ChabautyColeman.aj`.

Chart identification (section `PipelineChart`): the evaluated disk pipeline datum is identified
*directly* with the chart datum at coordinates `ζ(z₀)_j = eval z₀ (phiZeta j)`. The `u`-parts agree
by `ChabautyColeman.map_evalRingHom_eq_add_chartCoords` (both equal `uτ + ∑ C(ζ_j) X^j`) and
`ChabautyColeman.chartU_map_evalRingHom`; the `v`-parts agree by square-root uniqueness
`ChabautyColeman.eq_of_dvd_sq_sub_of_residue_bezout`
(`ChabautyColeman.map_evalRingHom_eq_chartV_map`), using that both reduce to `v_bar` over the
residue
field (`ChabautyColeman.phiPipeline_map_constantCoeff`,
`ChabautyColeman.chartV_map_constantCoeff`). Feeding these into
`ChabautyColeman.mk0_phiPipeline_eval` gives `chartClass(ζ(z₀)) = ([P_{z₀}] + [ιP₀]) · [τ]`
(`ChabautyColeman.chartClass_eq_diskPointDiff_mul_tauClass`), whence
`(J1_equiv_polydisk c).1 = ζ(z₀)` through `ChabautyColeman.polydiskToKer`
(`ChabautyColeman.J1_equiv_polydisk_diskPointDiff`).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

/-- The Abel–Jacobi class of an affine point as a Mumford-ideal class (linear `u = X - x₀`,
constant `v = C y₀`). Identifies the point classes appearing in
`ChabautyColeman.mk0_phiPipeline_eval` with values of `ChabautyColeman.aj`. -/
theorem aj_eq_mk0_mumfordIdeal {K : Type*} [Field K] (fK : K[X]) [NeZero (2 : K)]
    [Fact (Odd fK.natDegree)] [Fact (Squarefree fK)] (x₀ y₀ : K) :
    aj fK x₀ y₀ = ClassGroup.mk0 ⟨mumfordIdeal fK (X - C x₀) (C y₀),
      mumfordIdeal_mem_nonZeroDivisors fK (monic_X_sub_C x₀).ne_zero (C y₀)⟩ :=
  congrArg ClassGroup.mk0 (Subtype.ext (pointIdeal_eq_mumfordIdeal fK x₀ y₀))

section DiskIdent

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {f : O[X]} {a b : O}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- **The same-disk point difference is in the kernel of reduction**: the class
`[P_{z₀}] · [ιP₀]` — with `P_{z₀} = (a+z₀, yz)` the disk point and `ιP₀ = (a,-b)` the
hyperelliptic involute of the disk center — reduces to `1`, because `P_{z₀}` and `P₀` reduce
to the same point over the residue field. This realizes `[P_{z₀}] - [P₀]` as an element of the
kernel of `redJHom`. -/
theorem redJ_diskPointDiff_eq_one (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    redJ (aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) (a + z₀))
          (algebraMap O (FractionRing O)
            (PSeries.eval z₀ (PowerSeries.C b * diskSeriesGeneric f a)))
        * aj (f.map (algebraMap O (FractionRing O)))
          (algebraMap O (FractionRing O) a)
          (algebraMap O (FractionRing O) (-b))) = 1 := by
  set φ := algebraMap O (FractionRing O)
  have hyz : PSeries.eval z₀ (PowerSeries.C b * diskSeriesGeneric f a)
      = b * PSeries.eval z₀ (diskSeriesGeneric f a) := by
    rw [PSeries.eval_mul hz₀, PSeries.eval_C]
  have hab1 : φ (PSeries.eval z₀ (PowerSeries.C b * diskSeriesGeneric f a)) ^ 2
      = (f.map φ).eval (φ (a + z₀)) := by
    rw [hyz]
    exact onCurve_map _ (generic_onCurve f hb hfa h2 hz₀)
  have hab2 : φ (-b) ^ 2 = (f.map φ).eval (φ a) := by
    rw [map_neg, neg_sq, ← map_pow, hb, eval_map_apply]
  rw [redJ_mul hf hdeg, redJ_aj hf hdeg hab1, redJ_aj hf hdeg hab2]
  rw [show residue O (a + z₀) = residue O a by
      rw [map_add, show residue O z₀ = 0 from (residue_eq_zero_iff _).mpr hz₀, add_zero],
    show residue O (PSeries.eval z₀ (PowerSeries.C b * diskSeriesGeneric f a))
        = residue O b by rw [hyz, residue_b_mul_eval a b hz₀], map_neg]
  have hbar : residue O b ^ 2 = (f.map (residue O)).eval (residue O a) := onCurve_map _ hb
  rw [aj_inv (f.map (residue O)) hbar, mul_inv_cancel]

end DiskIdent

section PipelineChart

open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O]
  {f : O[X]} {a b xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]}
  {d : CantorCertData O⟦X⟧}

/-- The disk pipeline over `O⟦z⟧` returns a reduced datum: `phiPipeline.1` is monic, divides
`phiPipeline.2 ^ 2 - f`, and dominates `phiPipeline.2` in degree. -/
theorem phiPipeline_monic_dvd_degree_lt (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ) (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree) :
    (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.Monic
      ∧ (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1
        ∣ (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2 ^ 2 - f.map PowerSeries.C
      ∧ (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2.degree
        < (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.degree := by
  have hu₁ : (phiU₁ a xQ (O := O)).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hu₃ : (phiU₃ a xQ (O := O)).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₁ : phiU₁ a xQ ∣ phiV₁ f a b m ^ 2 - f.map PowerSeries.C :=
    movingPair_dvd hsep hm hb hfa h2 hyQ
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧)
      ∣ (vτ.map PowerSeries.C) ^ 2 - f.map PowerSeries.C := map_dvd_sq_sub _ hdvdτ
  have hsep' : IsUnit (a - xQ) := neg_sub xQ a ▸ hsep.neg
  have hd₃O : (X - C xQ) * (X - C a) ∣ pairV xQ yQ m₀ ^ 2 - f :=
    pair_dvd hsep' hm₀ hyQ (by rwa [neg_pow_two])
  have hd₃ : phiU₃ a xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - f.map PowerSeries.C := map_dvd_sq_sub _ hd₃O
  exact cantorPipeline_monic_dvd_degree_lt hu₁ hd₁ hu₂ hd₂ hu₃ hd₃ hcerts

variable [IsDiscreteValuationRing O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- A monic polynomial of the center's degree, evaluated at a disk point `z₀`, is the chart
polynomial at the coordinates `ζ(z₀)_j = eval z₀ (chartCoords j)`. -/
theorem map_evalRingHom_eq_add_chartCoords {U : Polynomial O⟦X⟧} (huτ : uτ.Monic)
    (hUm : U.Monic) (hUdeg : U.natDegree = uτ.natDegree) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    U.map (PSeries.evalRingHom hz₀)
      = uτ + ∑ j : Fin uτ.natDegree,
          C (PSeries.eval z₀ (chartCoords PowerSeries.C uτ U j)) * X ^ (j : ℕ) := by
  nth_rw 1 [eq_add_chartCoords (φ := PowerSeries.C) huτ hUm hUdeg]
  rw [Polynomial.map_add, Polynomial.map_map]
  congr 1
  · rw [PSeries.evalRingHom_comp_C, Polynomial.map_id]
  · rw [Polynomial.map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      PSeries.evalRingHom_apply]

/-- Residues of a `z₀`-evaluated single-variable polynomial agree with those of its center.
The `O⟦z⟧` analogue of `ChabautyColeman.map_residue_eval_eq`. -/
theorem PSeries.map_residue_eval_eq {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) (P : Polynomial O⟦X⟧) :
    (P.map (PSeries.evalRingHom hz₀)).map (residue O)
      = (P.map (PowerSeries.constantCoeff : O⟦X⟧ →+* O)).map (residue O) := by
  ext k
  simp only [Polynomial.coeff_map, PSeries.evalRingHom_apply]
  have hmem := PSeries.eval_sub_constantCoeff_mem hz₀ (P.coeff k)
  have h0 : residue O (PSeries.eval z₀ (P.coeff k) - PowerSeries.constantCoeff (P.coeff k)) = 0 :=
    (residue_eq_zero_iff _).mpr hmem
  rwa [map_sub, sub_eq_zero] at h0

variable {w c₁ c₂ : O[X]}

/-- The square root `V` belonging to a monic `U` of the center's degree, evaluated at a disk
point `z₀`, is the evaluated chart square root at the coordinates `ζ(z₀)` of `U`: both are
square roots of `f` modulo the common `u`-part with the same reduction `v_bar`, and such a square
root is unique. -/
theorem map_evalRingHom_eq_chartV_map {U V : Polynomial O⟦X⟧} (hu : uτ.Monic)
    (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hUm : U.Monic)
    (hUdeg : U.natDegree = uτ.natDegree) (hVdvd : U ∣ V ^ 2 - f.map PowerSeries.C)
    (hVdeg : V.degree < U.degree)
    (hVres : V.map (PowerSeries.constantCoeff : O⟦X⟧ →+* O) = vτ)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    (hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (chartCoords PowerSeries.C uτ U j) ∈ maximalIdeal O) :
    V.map (PSeries.evalRingHom hz₀)
      = (chartV hu (le_refl uτ.natDegree) hv hw hbez).map
          (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hζ)) := by
  set ev := MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hζ)
  set Uc := (chartU uτ uτ.natDegree).map ev with hUc
  set W := V.map (PSeries.evalRingHom hz₀) with hW
  have hUeq : Uc = U.map (PSeries.evalRingHom hz₀) := by
    rw [hUc, chartU_map_evalRingHom hζ, map_evalRingHom_eq_add_chartCoords hu hUm hUdeg hz₀]
  have hUdvdW : Uc ∣ W ^ 2 - f := by
    rw [hUeq, hW]
    have h := map_dvd (Polynomial.mapRingHom (PSeries.evalRingHom hz₀)) hVdvd
    simp only [coe_mapRingHom, Polynomial.map_sub, Polynomial.map_pow] at h
    rwa [PSeries.map_C_map_evalRingHom hz₀ f] at h
  have hdegU : Uc.degree = U.degree := by
    rw [hUeq]; exact hUm.degree_map _
  have hdW : W.degree < Uc.degree := by
    rw [hW, hdegU]
    exact Polynomial.degree_map_le.trans_lt hVdeg
  have hWres : W.map (residue O) = vτ.map (residue O) := by
    rw [hW, PSeries.map_residue_eval_eq hz₀, hVres]
  exact (chartV_map_evalRingHom_eq hu rfl hv hw hbez hζ hUdvdW hdW hWres).symm

variable [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The disk chart class at `ζ(z₀)` is the same-disk difference class**: evaluating the
chart at the coordinates `ζ(z₀)_j = eval z₀ (phiZeta j)` gives the class
`([P_{z₀}] + [ιP₀]) · [τ]`. -/
theorem chartClass_eq_diskPointDiff_mul_tauClass (hf : f.Monic) (hsep : IsUnit (xQ - a))
    (hm : m * (PowerSeries.C xQ - (PowerSeries.C a + PowerSeries.X))
      = PowerSeries.C (-yQ) - PowerSeries.C b * diskSeriesGeneric f a)
    (hm₀ : m₀ * (a - xQ) = -b - yQ)
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d
      uτ.natDegree)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    (hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (phiZeta f a b xQ yQ m m₀ uτ vτ d j) ∈ maximalIdeal O) :
    chartClass hu rfl hv hw hbez hζ
      = aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) (a + z₀))
          (algebraMap O (FractionRing O)
            (PSeries.eval z₀ (PowerSeries.C b * diskSeriesGeneric f a)))
        * aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) a)
          (algebraMap O (FractionRing O) (-b))
        * tauClass (f := f) (v := vτ) hu := by
  set φ := algebraMap O (FractionRing O)
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  obtain ⟨hPmonic, hPdvd, hPdeg⟩ :=
    phiPipeline_monic_dvd_degree_lt hsep hm hm₀ hb hfa h2 hyQ hu hdvdτ hcerts
  have hUeq' : (chartU uτ uτ.natDegree).map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hζ))
      = (phiPipeline f a b xQ yQ m m₀ uτ vτ d).1.map (PSeries.evalRingHom hz₀) := by
    rw [chartU_map_evalRingHom hζ,
      map_evalRingHom_eq_add_chartCoords hu hPmonic hcerts.hdeg hz₀]
    rfl
  have hVeq' : (chartV hu (le_refl uτ.natDegree) hv hw hbez).map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hζ))
      = (phiPipeline f a b xQ yQ m m₀ uτ vτ d).2.map (PSeries.evalRingHom hz₀) :=
    (map_evalRingHom_eq_chartV_map hu hv hw hbez hPmonic hcerts.hdeg hPdvd hPdeg
      (phiPipeline_map_constantCoeff hf hsep hm hm₀ hb hfa h2 hyQ hu hv hdvdτ hgτ hcerts).2
      hz₀ hζ).symm
  rw [chartClass_eq hu rfl hv hw hbez hζ (congrArg (Polynomial.map φ) hUeq')
      (congrArg (Polynomial.map φ) hVeq') ((hPmonic.map _).map _).ne_zero,
    mk0_phiPipeline_eval hsep hm hm₀ hb hfa h2 hyQ hu hdvdτ hcerts hPmonic hz₀,
    aj_eq_mk0_mumfordIdeal, aj_eq_mk0_mumfordIdeal]
  simp only [map_neg, tauClass]

variable [IsAdicComplete (maximalIdeal O) O] [CharZero (FractionRing O)]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- **The polydisk coordinates of the same-disk difference class are `ζ(z₀)`**: under
`thm:J1-index`'s bijection, the kernel class `[P_{z₀}] + [ιP₀]` corresponds to the polydisk
point `ζ(z₀)_j = eval z₀ (phiZeta j)`. -/
theorem J1_equiv_polydisk_diskPointDiff (hf : f.Monic) (hdeg : 0 < f.natDegree)
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
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    (hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (phiZeta f a b xQ yQ m m₀ uτ vτ d j) ∈ maximalIdeal O) :
    (J1_equiv_polydisk hu rfl hv hw hbez hf hdeg hfdeg hsq
        ⟨aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) (a + z₀))
            (algebraMap O (FractionRing O)
              (PSeries.eval z₀ (PowerSeries.C b * diskSeriesGeneric f a)))
          * aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) a)
            (algebraMap O (FractionRing O) (-b)),
          MonoidHom.mem_ker.mpr (redJ_diskPointDiff_eq_one hf hdeg hb hfa h2 hz₀)⟩).1
      = fun j ↦ PSeries.eval z₀ (phiZeta f a b xQ yQ m m₀ uτ vτ d j) := by
  suffices h : J1_equiv_polydisk hu rfl hv hw hbez hf hdeg hfdeg hsq _
      = ⟨fun j ↦ PSeries.eval z₀ (phiZeta f a b xQ yQ m m₀ uτ vτ d j), hζ⟩ from
    congrArg Subtype.val h
  rw [J1_equiv_polydisk, Equiv.symm_apply_eq, Equiv.ofBijective_apply]
  refine Subtype.ext ?_
  change _ = chartClass hu rfl hv hw hbez hζ * (tauClass (f := f) (v := vτ) hu)⁻¹
  rw [chartClass_eq_diskPointDiff_mul_tauClass hf hsep hm hm₀ hb hfa h2 hyQ hu hv hw hbez
    hgτ hcerts hz₀ hζ, mul_inv_cancel_right]

end PipelineChart

end ChabautyColeman

end
