/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Analytic.ColemanValue
public import LeanPool.HyperellipticCurves.Log.Analytic.Lambda
public import LeanPool.HyperellipticCurves.Log.Charts.InfIdentification

/-!
# The infinity-disk glue chain: chart coordinates, Coleman value, glue identity

The infinity-chart analogues of `LeanPool.HyperellipticCurves.Log.Charts.WeierstrassIdentification`
(chart
layer), `LeanPool.HyperellipticCurves.Log.Charts.WeierstrassValue` and
`LeanPool.HyperellipticCurves.Log.Charts.WeierstrassGlue` (analytic layer), for the scaled
infinity-disk data
of `LeanPool.HyperellipticCurves.Log.Charts.InfChart`.

* `ChabautyColeman.map_constantCoeff_infVred`: **the centre of the reduced `v`-part is
  `vτ`** — proven by passing to `O⟦z⟧/(z²)`, where `û ↦ 0` collapses the pipeline to
  `v_check ↦ uτ + z·vτ`, `U ↦ uτ + 2z·vτ`;
* `ChabautyColeman.chartClass_eq_diskPointDiff_mul_tauClass_inf` /
  `ChabautyColeman.J1_equiv_polydisk_diskPointDiff_inf`: the chart class at `ζ(z₀)` is
  `[P_{z₀} - ∞]·[τ]`, and under `thm:J1-index`'s bijection the kernel class `[P_{z₀} - ∞]`
  corresponds to the polydisk point `ζ(z₀)`;
* `ChabautyColeman.diskDiffClassInf`, `ChabautyColeman.hasSum_Lam_antiderivOmegaPrime_inf`,
  `ChabautyColeman.hasSum_lambdaOne_diskDiffClass_inf`,
  `ChabautyColeman.mapBase_aj_eq_diskDiffClassInf`, `ChabautyColeman.lambda_glue_inf`:
  the analytic layer — since the disk centre `∞` is the Abel–Jacobi base point, the glue
  identity is *single-point*: `λ_ω([P_z - ∞]) = G(z)` with `G` the antiderivative of the
  disk expansion.

Blueprint node: `thm:glue` (infinity chart) / `lem:global-generic` environment.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section InfCenterV

variable {O : Type*} [CommRing O] [IsDomain O] {f uτ vτ : O[X]}

/-- **The centre of the reduced `v`-part is the `τ`-datum**: `V(0) = vτ` for the unscaled
reduced `v`-part `V` of the infinity-disk pipeline. The proof passes to `O⟦z⟧/(z²)`, where
`û ↦ 0` collapses everything: `v_check ↦ uτ + z·vτ` and `U ↦ uτ + 2z·vτ`, so
`v_check mod U ↦ -z·vτ`, and `z`-cancellation pins the constant coefficient. -/
theorem map_constantCoeff_infVred (hf : f.Monic) (huτ : uτ.Monic)
    (hvτ : vτ.natDegree < uτ.natDegree) (hdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hdvdτ : uτ ∣ vτ ^ 2 - f) (hvτd : vτ.degree < uτ.degree)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ)) :
    V.map (PowerSeries.constantCoeff (R := O)) = vτ := by
  set I : Ideal O⟦X⟧ := Ideal.span {(PowerSeries.X : O⟦X⟧) ^ 2} with hI
  set π : O⟦X⟧ →+* O⟦X⟧ ⧸ I := Ideal.Quotient.mk I with hπ
  set φ₂ : O →+* O⟦X⟧ ⧸ I := π.comp PowerSeries.C with hφ₂
  have hπu : π (infSeries hf) = 0 := by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
    exact Dvd.intro _ (infSeries_eq hf).symm
  have hπz2 : π PowerSeries.X ^ 2 = 0 := by
    rw [← map_pow, hπ, Ideal.Quotient.eq_zero_iff_mem, hI]
    exact Ideal.mem_span_singleton_self _
  have hπaeval (p : O[X]) : π (aeval (infSeries hf) p) = φ₂ (p.coeff 0) := by
    rw [aeval_def, Polynomial.hom_eval₂, hπu, eval₂_at_zero, hφ₂]
    rfl
  -- the collapsed data
  have hπc : π (infC hf uτ vτ) = 1 := by
    have hA := congrArg π (aeval_infSeries_reverse_mul_infTauInv hf huτ)
    rw [map_mul, map_one, hπaeval, coeff_zero_reverse, huτ.leadingCoeff, map_one,
      one_mul] at hA
    rw [infC, map_mul, map_sub, map_one, map_mul, map_mul, hπu, mul_zero, zero_mul,
      sub_zero, one_mul, hA]
  have hmapmap₂ (p : O[X]) : (p.map (PowerSeries.C : O →+* O⟦X⟧)).map π = p.map φ₂ := by
    rw [Polynomial.map_map, hφ₂]
  have hπv : (infV hf uτ vτ).map π = C (π PowerSeries.X) * vτ.map φ₂ + uτ.map φ₂ := by
    rw [infV, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C,
      hπc, C_1, one_mul, hmapmap₂, hmapmap₂]
  have hπD : π (aeval (infSeries hf) f.reverse) = 1 := by
    rw [hπaeval, coeff_zero_reverse, hf.leadingCoeff, map_one]
  -- the collapsed master factorization
  have hfac := congrArg (Polynomial.map π) (infV_sq_sub_factor hf huτ hvτ hdeg hdvdτ)
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_pow, map_C,
    show (C (π PowerSeries.X) : (O⟦X⟧ ⧸ I)[X]) ^ 2 = C (π PowerSeries.X ^ 2) by
      rw [map_pow],
    hπz2, C_0, zero_mul, sub_zero,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, Polynomial.map_X,
    hπu, C_0, zero_mul, sub_zero, one_mul, hπv, hmapmap₂] at hfac
  have hItop : I ≠ ⊤ := hI ▸ Ideal.span_singleton_ne_top fun hu ↦ by
    have h2 := PowerSeries.isUnit_iff_constantCoeff.mp hu
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow two_ne_zero] at h2
    exact not_isUnit_zero h2
  have : Nontrivial (O⟦X⟧ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hC2 : (C (2 * π PowerSeries.X) : (O⟦X⟧ ⧸ I)[X]) = 2 * C (π PowerSeries.X) := by
    rw [map_mul, map_ofNat]
  -- identify the collapsed `U`
  have hπU : (infU hf uτ vτ).map π
      = uτ.map φ₂ + C (2 * π PowerSeries.X) * vτ.map φ₂ := by
    have hπQ : (infU hf uτ vτ).map π = (infQ hf uτ vτ).map π := by
      rw [infU, Polynomial.map_mul, map_C, hπD, C_1, one_mul]
    have hz2C : (C (π PowerSeries.X) : (O⟦X⟧ ⧸ I)[X]) ^ 2 = 0 := by rw [← map_pow, hπz2, C_0]
    have hcancel : uτ.map φ₂ * ((infQ hf uτ vτ).map π)
        = uτ.map φ₂ * (uτ.map φ₂ + C (2 * π PowerSeries.X) * vτ.map φ₂) := by
      rw [← hfac, hC2]
      linear_combination (vτ.map φ₂ : (O⟦X⟧ ⧸ I)[X]) ^ 2 * hz2C
    rw [hπQ]
    exact (huτ.map φ₂).isRegular.left hcancel
  -- the collapsed remainder
  have hVπ := congrArg (Polynomial.map π) hV
  rw [Polynomial.map_mul, map_C, Polynomial.map_neg,
    map_modByMonic π (infU_monic hf huτ hvτ hdeg hdvdτ), hπv, hπU] at hVπ
  have hUm₂ : (uτ.map φ₂ + C (2 * π PowerSeries.X) * vτ.map φ₂).Monic := by
    rw [← hπU]
    exact (infU_monic hf huτ hvτ hdeg hdvdτ).map π
  have hUdeg₂ : (uτ.map φ₂ + C (2 * π PowerSeries.X) * vτ.map φ₂).degree = uτ.degree := by
    rw [← hπU, Polynomial.degree_eq_natDegree ((infU_monic hf huτ hvτ hdeg hdvdτ).map π).ne_zero,
      ((infU_monic hf huτ hvτ hdeg hdvdτ).natDegree_map π),
      natDegree_infU hf huτ hvτ hdeg hdvdτ,
      Polynomial.degree_eq_natDegree huτ.ne_zero]
  have hdegv₂ : (C (-(π PowerSeries.X)) * vτ.map φ₂).degree
      < (uτ.map φ₂ + C (2 * π PowerSeries.X) * vτ.map φ₂).degree := by
    rw [hUdeg₂]
    refine lt_of_le_of_lt (le_trans (degree_mul_le _ _) ?_) hvτd
    refine le_trans (add_le_add degree_C_le degree_map_le) ?_
    exact (zero_add _).le
  have hmod : (C (π PowerSeries.X) * vτ.map φ₂ + uτ.map φ₂)
        %ₘ (uτ.map φ₂ + C (2 * π PowerSeries.X) * vτ.map φ₂)
      = C (-(π PowerSeries.X)) * vτ.map φ₂ := by
    have hsplit : C (π PowerSeries.X) * vτ.map φ₂ + uτ.map φ₂
        = C (-(π PowerSeries.X)) * vτ.map φ₂
          + (uτ.map φ₂ + C (2 * π PowerSeries.X) * vτ.map φ₂) * 1 := by
      rw [map_neg, hC2]
      ring
    rw [hsplit, add_modByMonic, mul_one, modByMonic_self hUm₂, add_zero,
      (modByMonic_eq_self_iff hUm₂).mpr hdegv₂]
  rw [hmod, map_neg, neg_mul, neg_neg] at hVπ
  -- cancel `z` against the ideal `(z²)`
  have hcoeff (i : ℕ) : PowerSeries.constantCoeff (V.coeff i) = vτ.coeff i := by
    have h := congrArg (fun p ↦ Polynomial.coeff p i) hVπ
    simp only [coeff_C_mul, coeff_map] at h
    have h2 : π (PowerSeries.X * (V.coeff i - PowerSeries.C (vτ.coeff i))) = 0 := by
      rw [map_mul, map_sub, mul_sub, h, hφ₂, RingHom.comp_apply, sub_self]
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton, sq] at h2
    obtain ⟨b, hb⟩ := h2
    rw [mul_assoc] at hb
    have h3 : V.coeff i - PowerSeries.C (vτ.coeff i) = PowerSeries.X * b :=
      mul_left_cancel₀ PowerSeries.X_ne_zero hb
    have h4 := congrArg PowerSeries.constantCoeff h3
    rwa [map_sub, map_mul, PowerSeries.constantCoeff_X, zero_mul,
      PowerSeries.constantCoeff_C, sub_eq_zero] at h4
  ext i
  rw [coeff_map, hcoeff]

end InfCenterV

section InfChartEval

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {f uτ vτ : O[X]}

variable {w c₁ c₂ : O[X]}

variable [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The disk chart class at `ζ(z₀)` is the disk-point class, infinity centre**:
evaluating the chart at the coordinates `ζ(z₀)_j = eval z₀ (infZeta j)` gives the class
`[P_{z₀} - ∞] · [τ]`. -/
theorem chartClass_eq_diskPointDiff_mul_tauClass_inf (hf : f.Monic)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) (hz₀0 : z₀ ≠ 0)
    (hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (infZeta hf uτ vτ j) ∈ maximalIdeal O) :
    chartClass hu rfl hv hw hbez hζ
      = aj (f.map (algebraMap O (FractionRing O)))
          (algebraMap O (FractionRing O) (PSeries.eval z₀ (infSeries hf)))⁻¹
          ((algebraMap O (FractionRing O) z₀)⁻¹
            * (algebraMap O (FractionRing O) (PSeries.eval z₀ (infSeries hf)))⁻¹
              ^ uτ.natDegree)
        * tauClass (f := f) (v := vτ) hu := by
  set φ := algebraMap O (FractionRing O)
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  have hUm : (infU hf uτ vτ).Monic := infU_monic hf hu hvτ hdeg hdvdτ
  have hUdeg := natDegree_infU hf hu hvτ hdeg hdvdτ
  have hUeq' : (chartU uτ uτ.natDegree).map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hζ))
      = (infU hf uτ vτ).map (PSeries.evalRingHom hz₀) := by
    rw [chartU_map_evalRingHom hζ, map_evalRingHom_eq_add_chartCoords hu hUm hUdeg hz₀]
    rfl
  have hVeq' : (chartV hu (le_refl uτ.natDegree) hv hw hbez).map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hζ))
      = V.map (PSeries.evalRingHom hz₀) :=
    (map_evalRingHom_eq_chartV_map hu hv hw hbez hUm hUdeg hVdvd hVdeg
      (map_constantCoeff_infVred hf hu hvτ hdeg hdvdτ hv hV) hz₀ hζ).symm
  rw [chartClass_eq hu rfl hv hw hbez hζ (congrArg (Polynomial.map φ) hUeq')
      (congrArg (Polynomial.map φ) hVeq') ((hUm.map _).map _).ne_zero,
    mk0_infU_eval hf hu hvτ hdeg hdvdτ hV hz₀ hz₀0, aj_eq_mk0_mumfordIdeal]
  simp only [tauClass]

variable [IsAdicComplete (maximalIdeal O) O] [CharZero (FractionRing O)]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- **The polydisk coordinates of the disk-point class at the infinity centre are
`ζ(z₀)`**: under `thm:J1-index`'s bijection, the kernel class `[P_{z₀} - ∞]` corresponds to
the polydisk point `ζ(z₀)_j = eval z₀ (infZeta j)`. -/
theorem J1_equiv_polydisk_diskPointDiff_inf (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hgdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) (hz₀0 : z₀ ≠ 0)
    (hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (infZeta hf uτ vτ j) ∈ maximalIdeal O) :
    (reductionKernelEquivPolydisk hu rfl hv hw hbez hf hdeg hfdeg hsq
        ⟨aj (f.map (algebraMap O (FractionRing O)))
            (algebraMap O (FractionRing O) (PSeries.eval z₀ (infSeries hf)))⁻¹
            ((algebraMap O (FractionRing O) z₀)⁻¹
              * (algebraMap O (FractionRing O) (PSeries.eval z₀ (infSeries hf)))⁻¹
                ^ uτ.natDegree),
          MonoidHom.mem_ker.mpr
            (redJ_diskPointDiff_eq_one_inf hf hdeg hgdeg hz₀ hz₀0)⟩).1
      = fun j ↦ PSeries.eval z₀ (infZeta hf uτ vτ j) := by
  suffices h : reductionKernelEquivPolydisk hu rfl hv hw hbez hf hdeg hfdeg hsq _
      = ⟨fun j ↦ PSeries.eval z₀ (infZeta hf uτ vτ j), hζ⟩ from
    congrArg Subtype.val h
  rw [reductionKernelEquivPolydisk, Equiv.symm_apply_eq, Equiv.ofBijective_apply]
  refine Subtype.ext ?_
  change _ = chartClass hu rfl hv hw hbez hζ * (tauClass (f := f) (v := vτ) hu)⁻¹
  rw [chartClass_eq_diskPointDiff_mul_tauClass_inf hf hu hv hw hbez hvτ hgdeg hV hVdeg
    hVdvd hz₀ hz₀0 hζ, mul_inv_cancel_right]

end InfChartEval

section InfGlue

open MvPowerSeries ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsAdicComplete (maximalIdeal O) O] [CharZero (FractionRing O)]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {f uτ vτ w c₁ c₂ : O[X]}
  {Aτ : Fin uτ.natDegree → MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O}
  {aτ bτ : Fin uτ.natDegree → O}
  {dF : FoldCertData (MvPowerSeries (Fin uτ.natDegree ⊕ Fin uτ.natDegree) O) uτ.natDegree}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  {π : O} {p e : ℕ} (cs : Fin uτ.natDegree → FractionRing O)

/-- The class `[P_z - ∞]` of the infinity-disk point at parameter `z ∈ 𝔪`, `z ≠ 0`, as an
element of `J¹ = ker(redJ)` (the disk centre is `∞` itself, so the same-disk difference is
the point's own class); membership in the kernel is
`ChabautyColeman.redJ_diskPointDiff_eq_one_inf`. -/
noncomputable def diskDiffClassInf (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hgdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {z : O} (hz : z ∈ maximalIdeal O) (hz0 : z ≠ 0) :
    (redJHom (K := FractionRing O) (f := f) hf hdeg).ker :=
  ⟨aj (f.map (algebraMap O (FractionRing O)))
      (algebraMap O (FractionRing O) (PSeries.eval z (infSeries hf)))⁻¹
      ((algebraMap O (FractionRing O) z)⁻¹
        * (algebraMap O (FractionRing O) (PSeries.eval z (infSeries hf)))⁻¹
          ^ uτ.natDegree),
    MonoidHom.mem_ker.mpr (redJ_diskPointDiff_eq_one_inf hf hdeg hgdeg hz hz0)⟩

/-- **Numerical clause (b) at the infinity centre**: on the disk-point class `[P_z - ∞]`
the image of `Lam` in `K = FractionRing O` is the convergent `p`-adic Coleman integral of
`ω′_i` from `∞` to `z`, the value at `z` of the antiderivative of the pulled-back invariant
differential along the infinity chart coordinates `infZeta`. -/
theorem hasSum_Lam_antiderivOmegaPrime_inf (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hgdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {V : (O⟦X⟧)[X]} (hV : Polynomial.C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (ha : ∀ i, uτ.eval (aτ i) = 0) (hbv : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m', (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j, i ≠ j → IsUnit (aτ i - aτ j))
    (hd : IsFtauFoldCerts Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) (hz₀0 : z₀ ≠ 0) (i : Fin uτ.natDegree) :
    HasSum (fun k : ℕ ↦ PowerSeries.coeff k
        (antideriv (omegaPrime
          (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv hd hram hsplit hunit)
          (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (infZeta hf uτ vτ s)) i))
        * algebraMap O (FractionRing O) z₀ ^ k)
      (algebraMap O (FractionRing O)
        (Lam hu rfl hv hw hbez hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe
          (diskDiffClassInf hf hdeg hgdeg hz₀ hz₀0) i)) := by
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  have hζ0 : ∀ s, PowerSeries.constantCoeff (infZeta hf uτ vτ s) = 0 :=
    constantCoeff_infZeta hf hu hvτ hgdeg hdvdτ
  have hζ (j : Fin uτ.natDegree) : PSeries.eval z₀ (infZeta hf uτ vτ j) ∈ maximalIdeal O :=
    PSeries.eval_mem_maximalIdeal_of_constantCoeff_eq_zero hz₀ (hζ0 j)
  refine hasSum_Lam_antiderivOmegaPrime_of_polydisk hf hdeg hu hv hw hbez hfdeg hsq hroot hcc
    ha hbv hsplit hunit hd hram hpe hζ0 hz₀ (diskDiffClassInf hf hdeg hgdeg hz₀ hz₀0) ?_ i
  rw [show ((diskDiffClassInf hf hdeg hgdeg hz₀ hz₀0 :
      (redJHom (K := FractionRing O) (f := f) hf hdeg).ker)) = ⟨_, _⟩ from rfl]
  exact J1_equiv_polydisk_diskPointDiff_inf hf hdeg hu hv hw hbez hvτ hgdeg hV hVdeg hVdvd
    hfdeg hsq hz₀ hz₀0 hζ

/-- **Clause (b) for `λ` at the infinity centre**: on the disk-point class the value of
`λ_ω` is the convergent `p`-adic value at `z` of the antiderivative of the disk expansion
of `ω = ∑_i cs_i·ω′_i` along the infinity chart coordinates. -/
theorem hasSum_lambdaOne_diskDiffClass_inf (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hgdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {V : (O⟦X⟧)[X]} (hV : Polynomial.C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    (hroot : ∀ i, (ftauUY uτ uτ.natDegree).eval (Aτ i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (Aτ i) = aτ i)
    (ha : ∀ i, uτ.eval (aτ i) = 0) (hbv : ∀ i, vτ.eval (aτ i) = bτ i)
    (hsplit : uτ = ∏ m', (Polynomial.X - Polynomial.C (aτ m')))
    (hunit : ∀ i j, i ≠ j → IsUnit (aτ i - aτ j))
    (hd : IsFtauFoldCerts Aτ aτ bτ hu (rfl : uτ.natDegree = uτ.natDegree) hv hw hbez dF)
    (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    {z : O} (hz : z ∈ maximalIdeal O) (hz0 : z ≠ 0) :
    HasSum (fun k : ℕ ↦ (∑ i, cs i * PowerSeries.coeff k
        (antideriv (omegaPrime
          (ftauFoldFGLFrac hu rfl hv hw hbez hf hfdeg hroot hcc ha hbv hd hram hsplit hunit)
          (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (infZeta hf uτ vτ s)) i)))
        * algebraMap O (FractionRing O) z ^ k)
      (lambdaOne hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe
        (diskDiffClassInf hf hdeg hgdeg hz hz0)) := by
  simpa only [lambdaOne] using hasSum_sum_mul_coeff cs fun i ↦
    hasSum_Lam_antiderivOmegaPrime_inf hf hdeg hu hv hw hbez hvτ hgdeg hV hVdeg hVdvd hfdeg
      hsq hroot hcc ha hbv hsplit hunit hd hram hpe hz hz0 i

variable {K₀ : Type*} [Field K₀] [Algebra K₀ (FractionRing O)]
  {f₀ : K₀[X]} [Fact (Odd f₀.natDegree)]

/-- **The base change of a rational point of the infinity disk is the disk-point class**:
the disk centre `∞` is the Abel–Jacobi base point, so no cancellation is needed. -/
theorem mapBase_aj_eq_diskDiffClassInf [CharZero K₀] [Fact (Squarefree f₀)]
    (hf : f.Monic) (hdeg : 0 < f.natDegree) (hgdeg : f.natDegree = 2 * uτ.natDegree + 1)
    (hf₀ : f₀.map (algebraMap K₀ (FractionRing O)) = f.map (algebraMap O (FractionRing O)))
    {z : O} (hz : z ∈ maximalIdeal O) (hz0 : z ≠ 0) {x y : K₀}
    (hx : algebraMap K₀ (FractionRing O) x
      = (algebraMap O (FractionRing O) (PSeries.eval z (infSeries hf)))⁻¹)
    (hy : algebraMap K₀ (FractionRing O) y
      = (algebraMap O (FractionRing O) z)⁻¹
        * (algebraMap O (FractionRing O) (PSeries.eval z (infSeries hf)))⁻¹
          ^ uτ.natDegree) :
    mapBase K₀ f₀ hf₀ (aj f₀ x y)
      = (diskDiffClassInf hf hdeg hgdeg hz hz0 : HypJac _ _) := by
  rw [mapBase_aj, hx, hy, diskDiffClassInf]

/-- **The glue identity at the infinity centre** (blueprint `thm:glue`, chart coverage):
for a rational point of the infinity residue disk, the value of `λ_ω` on its class is the
value of the disk antiderivative at its parameter (the base point `∞` is the disk centre,
so no difference is needed). -/
theorem lambda_glue_inf (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1)
    (hvτ : vτ.natDegree < uτ.natDegree) (hgdeg : f.natDegree = 2 * uτ.natDegree + 1)
    {V : (O⟦X⟧)[X]} (hV : Polynomial.C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    (hVdeg : V.degree < (infU hf uτ vτ).degree)
    (hVdvd : infU hf uτ vτ ∣ V ^ 2 - f.map PowerSeries.C)
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
      (fun s ↦ PowerSeries.map (algebraMap O (FractionRing O)) (infZeta hf uτ vτ s)) i))
    {z : O} (hz : z ∈ maximalIdeal O) (hz0 : z ≠ 0)
    {c : J1 K₀ f₀ hf hdeg hf₀}
    (hc : mapBase K₀ f₀ hf₀ ↑c = (diskDiffClassInf hf hdeg hgdeg hz hz0 : HypJac _ _))
    {A : FractionRing O}
    (hA : HasSum (fun k : ℕ ↦ PowerSeries.coeff k G
      * algebraMap O (FractionRing O) z ^ k) A) :
    lambda hu rfl hv hw hbez cs hf hdeg hfdeg hsq hroot hcc ha hbv
        hsplit hunit hd hram hpe hf₀ c = A := by
  simp only [hG, map_sum, PowerSeries.coeff_smul, smul_eq_mul] at hA
  have hval := hasSum_lambdaOne_diskDiffClass_inf cs hf hdeg hu hv hw hbez hvτ hgdeg hV
    hVdeg hVdvd hfdeg hsq hroot hcc ha hbv hsplit hunit hd hram hpe hz hz0
  have hsub : (⟨mapBase K₀ f₀ hf₀ ↑c, c.2⟩ :
        (redJHom (K := FractionRing O) (f := f) hf hdeg).ker)
      = diskDiffClassInf hf hdeg hgdeg hz hz0 :=
    Subtype.ext (by simpa using hc)
  rw [lambda, hsub, hval.unique hA]

end InfGlue

end ChabautyColeman
