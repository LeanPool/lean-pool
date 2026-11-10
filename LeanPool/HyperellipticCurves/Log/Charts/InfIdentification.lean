/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.ChartsInf
public import LeanPool.HyperellipticCurves.Log.Charts.DiskIdentification
public import LeanPool.HyperellipticCurves.Log.Charts.InfChart

/-!
# Pointwise identification of the infinity-disk pipeline (chart coverage)

The infinity-chart analogues of `LeanPool.HyperellipticCurves.Log.Charts.WeierstrassIdentification`:
evaluating the scaled infinity-disk data of `LeanPool.HyperellipticCurves.Log.Charts.InfChart` at a
point
`z₀` of the maximal ideal.

* `ChabautyColeman.infRoot_eq_eval_infSeries`: the two disk parametrizations agree — the
  Hensel root `infRoot` at parameter `z₀` is the evaluation of `infSeries`;
* `ChabautyColeman.mk0_mumfordIdeal_of_scaled_factor`: **abstract scaled reduction** — over
  any field, a scaled composed square root `v_check = z₀·vτ + c·uτ` with factorization
  `v_check² - z₀²·f = (1 - u·X)·uτ·Q` and interpolation `v_check(1/u) = 1/uᵍ` represents, after the
  monic normalization `U = D·Q` and unscaling `V = -(v_check mod U)/z₀`, the class
  `[(x - 1/u, 1/(uᵍ·z₀))]·[(uτ, vτ)]`;
* `ChabautyColeman.mk0_map_infU`: the same statement for the infinity-disk datum transported
  by an arbitrary ring map out of `O⟦z⟧`, which is what both consumers instantiate;
* `ChabautyColeman.mk0_infU_eval`: **the pipeline computes `[P_{z₀} - ∞] + [τ]` pointwise**
  (the instantiation over the fraction field at `z₀ ≠ 0`);
* `ChabautyColeman.redJ_diskPointDiff_eq_one_inf`: the disk point's class lies in the
  kernel of reduction — its `x`-coordinate is non-integral
  (`ChabautyColeman.not_isIntegral_inv_algebraMap`), so the point reduces to the centre
  `∞_bar`.

Blueprint node: `thm:glue` (infinity chart) / `lem:global-generic` environment.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section InfEval

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {f : O[X]}

/-- Evaluation at a maximal-ideal point commutes with polynomial evaluation at a series. -/
theorem eval_aeval (p : O[X]) (u : O⟦X⟧) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    PSeries.evalRingHom hz₀ (aeval u p) = p.eval (PSeries.evalRingHom hz₀ u) := by
  rw [aeval_def, Polynomial.hom_eval₂]
  congr 1
  ext x
  rw [RingHom.comp_apply, RingHom.id_apply, PowerSeries.algebraMap_eq,
    PSeries.evalRingHom_apply hz₀ (PowerSeries.C x), PSeries.eval_C]

/-- The evaluated infinity coordinate series solves the infinity-chart equation. -/
theorem eval_infSeries_eq (hf : f.Monic) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    PSeries.eval z₀ (infSeries hf)
      = z₀ ^ 2 * (reverse f).eval (PSeries.eval z₀ (infSeries hf)) := by
  have h := congrArg (PSeries.evalRingHom hz₀) (infSeries_eq hf)
  rw [map_mul, map_pow, eval_aeval] at h
  simpa only [PSeries.evalRingHom_apply, PSeries.eval_X] using h

theorem eval_infSeries_mem (hf : f.Monic) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    PSeries.eval z₀ (infSeries hf) ∈ maximalIdeal O :=
  PSeries.eval_mem_maximalIdeal_of_constantCoeff_eq_zero hz₀ (constantCoeff_infSeries hf)

end InfEval

section InfEvalDVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {f : O[X]}

/-- **The two infinity-disk parametrizations agree**: the Hensel root `infRoot` at
parameter `z₀` is the evaluation of the infinity coordinate series. -/
theorem infRoot_eq_eval_infSeries (hf : f.Monic) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    infRoot f hf hz₀ = PSeries.eval z₀ (infSeries hf) :=
  (eq_infRoot_of_solve hf (eval_infSeries_mem hf hz₀) hz₀ (eval_infSeries_eq hf hz₀)).symm

end InfEvalDVR

section InfEvalNeZero

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {f : O[X]}

theorem eval_infSeries_ne_zero (hf : f.Monic) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    (hz₀0 : z₀ ≠ 0) : PSeries.eval z₀ (infSeries hf) ≠ 0 := by
  intro h0
  have h := eval_infSeries_eq hf hz₀
  rw [h0, ← coeff_zero_eq_eval_zero, coeff_zero_reverse, hf.leadingCoeff, mul_one] at h
  exact hz₀0 (pow_eq_zero_iff two_ne_zero |>.mp h.symm)

end InfEvalNeZero

section ScaledReduction

open nonZeroDivisors

variable {K : Type*} [Field K] {fK : K[X]} [NeZero (2 : K)]
  [Fact (Odd fK.natDegree)] [Fact (Squarefree fK)]

/-- **Class-level correctness of a scaled composition-reduction**: abstract form of the
pointwise infinity-disk pipeline over a field. Data: a `τ`-datum `(uτ, vτ)`, a scaled
composed square root `v_check = z₀·vτ + c·uτ` interpolating `1/u^g` at the point `x = 1/u`, a
factorization `v_check² - z₀²·f = (1 - u·X)·uτ·Q`, and the monic normalization `U = D·Q` with
reduced `v`-part `V = -(v_check mod U)/z₀`. Then `[(U, V)] = [(x - 1/u, y)]·[(uτ, vτ)]` with
`y = 1/(uᵍ·z₀)`. -/
theorem mk0_mumfordIdeal_of_scaled_factor {uτK vτK vchK UK VK QK : K[X]}
    {uK z₀K DK cK : K} {g : ℕ}
    (huK0 : uK ≠ 0) (hz₀K0 : z₀K ≠ 0) (hDK0 : DK ≠ 0)
    (huτm : uτK.Monic) (hUKm : UK.Monic)
    (hvch : vchK = C z₀K * vτK + C cK * uτK)
    (hfac : vchK ^ 2 - C z₀K ^ 2 * fK = (1 - C uK * X) * uτK * QK)
    (hUQ : UK = C DK * QK)
    (hvx : vchK.eval uK⁻¹ = uK⁻¹ ^ g)
    (huτx : uτK.eval uK⁻¹ ≠ 0) (hdvdτK : uτK ∣ vτK ^ 2 - fK)
    (hVK : C z₀K * VK = -(vchK %ₘ UK)) :
    ClassGroup.mk0 ⟨mumfordIdeal fK UK VK,
        mumfordIdeal_mem_nonZeroDivisors _ hUKm.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal fK (X - C uK⁻¹) (C (z₀K⁻¹ * uK⁻¹ ^ g)),
          mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal fK uτK vτK,
            mumfordIdeal_mem_nonZeroDivisors _ huτm.ne_zero _⟩ := by
  classical
  set xK : K := uK⁻¹ with hxKdef
  set yKv : K := z₀K⁻¹ * xK ^ g with hyKvdef
  have hQK : QK = C DK⁻¹ * UK := by
    rw [hUQ, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hDK0, C_1, one_mul]
  have haz : (C z₀K⁻¹ : K[X]) ^ 2 * C z₀K ^ 2 = 1 := by
    rw [← mul_pow, ← Polynomial.C_mul, inv_mul_cancel₀ hz₀K0, C_1, one_pow]
  have hu1 : (C xK : K[X]) * C uK = 1 := by
    rw [← Polynomial.C_mul, hxKdef, inv_mul_cancel₀ huK0, C_1]
  have hD1 : (C DK⁻¹ : K[X]) * C DK = 1 := by rw [← Polynomial.C_mul, inv_mul_cancel₀ hDK0, C_1]
  have hz1 : (C z₀K⁻¹ : K[X]) * C z₀K = 1 := by rw [← Polynomial.C_mul, inv_mul_cancel₀ hz₀K0, C_1]
  set wK : K[X] := -C uK * C z₀K⁻¹ ^ 2 * C DK⁻¹ * UK with hwKdef
  have honcurve : (C z₀K⁻¹ * vchK) ^ 2 - fK = ((X - C xK) * uτK) * wK := by
    rw [hwKdef]
    linear_combination (C z₀K⁻¹ : K[X]) ^ 2 * hfac + fK * haz
      - uτK * QK * C z₀K⁻¹ ^ 2 * hu1
      + uτK * QK * C z₀K⁻¹ ^ 2 * (X - C xK) * C uK * hD1
      - (X - C xK) * uτK * (-C uK * C z₀K⁻¹ ^ 2 * C DK⁻¹) * hUQ
  have hvcx : (C z₀K⁻¹ * vchK).eval xK = yKv := by rw [eval_mul, eval_C, hxKdef, hvx, hyKvdef]
  have hyy : yKv ^ 2 = fK.eval xK := by
    have h := congrArg (Polynomial.eval xK) honcurve
    rw [eval_sub, eval_pow, hvcx, eval_mul, eval_mul, eval_sub, eval_X, eval_C, sub_self,
      zero_mul, zero_mul, sub_eq_zero] at h
    exact h
  -- Bézout certificate for the composition
  have hcop : IsCoprime (X - C xK) uτK :=
    (isCoprime_X_sub_C_of_eval_ne_zero (hxKdef ▸ huτx)).symm
  obtain ⟨s₁, s₂, hs⟩ := id hcop
  have hbez : s₁ * (X - C xK) + s₂ * uτK + 0 * (C yKv + vτK) = 1 := by linear_combination hs
  have hd₁ : (X - C xK) ∣ (C yKv) ^ 2 - fK := by
    refine dvd_iff_isRoot.mpr ?_
    rw [IsRoot, eval_sub, eval_pow, eval_C, hyy, sub_self]
  have hd₂ : uτK ∣ vτK ^ 2 - fK := hdvdτK
  have hmul := mk0_mumfordIdeal_mul_of_bezout (f := fK) hbez hd₁ hd₂
    (monic_X_sub_C _).ne_zero huτm.ne_zero
  -- the composed interpolant agrees with `v_c` modulo the composed `u`
  obtain ⟨w₁, hw₁⟩ := hd₁
  obtain ⟨w₂, hw₂⟩ := hd₂
  have hvc1 : (X - C xK) ∣ C z₀K⁻¹ * vchK - C yKv :=
    dvd_iff_isRoot.mpr (by rw [IsRoot, eval_sub, hvcx, eval_C, sub_self])
  have hvc2 : uτK ∣ C z₀K⁻¹ * vchK - vτK := by
    refine ⟨C (z₀K⁻¹ * cK), ?_⟩
    rw [hvch, map_mul]
    linear_combination vτK * hz1
  have hcv1 := cantorV_sub_left fK hbez hw₁
  have hcv2 := cantorV_sub_right fK hbez hw₂
  have hdiff : (X - C xK) * uτK
      ∣ cantorV fK (X - C xK) (C yKv) uτK vτK s₁ s₂ 0 - C z₀K⁻¹ * vchK :=
    hcop.mul_dvd
      (by
        have := dvd_sub ⟨_, hcv1⟩ hvc1
        rwa [sub_sub_sub_cancel_right] at this)
      (by
        have := dvd_sub ⟨_, hcv2⟩ hvc2
        rwa [sub_sub_sub_cancel_right] at this)
  have hidealc := mumfordIdeal_eq_of_dvd_sub fK hdiff
  -- the reduction step
  have hwK0 : wK ≠ 0 := by
    rw [hwKdef]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) hUKm.ne_zero
    · rw [Ne, neg_eq_zero, C_eq_zero]; exact huK0
    · rw [Ne, pow_eq_zero_iff two_ne_zero, C_eq_zero]; exact inv_ne_zero hz₀K0
    · rw [Ne, C_eq_zero]; exact inv_ne_zero hDK0
  have hred := mk0_mumfordIdeal_eq_mk0_cofactor_neg fK
    (mul_ne_zero (monic_X_sub_C _).ne_zero huτm.ne_zero) hwK0 honcurve
  -- identify the reduced datum with `(U, V)`
  have hmodrw : vchK %ₘ UK = -(C z₀K * VK) := by linear_combination hVK
  have hsplit := modByMonic_add_div vchK UK
  have hVdiff : -(C z₀K⁻¹ * vchK) = VK + UK * (-C z₀K⁻¹ * (vchK /ₘ UK)) := by
    linear_combination C z₀K⁻¹ * hsplit - C z₀K⁻¹ * hmodrw + VK * hz1
  have hidr : mumfordIdeal fK wK (-(C z₀K⁻¹ * vchK)) = mumfordIdeal fK UK VK := by
    have hC : (-C uK * C z₀K⁻¹ ^ 2 * C DK⁻¹ : K[X]) = C (-uK * z₀K⁻¹ ^ 2 * DK⁻¹) := by
      rw [← Polynomial.C_neg, ← Polynomial.C_pow, ← Polynomial.C_mul, ← Polynomial.C_mul]
    have hc0 : (-uK * z₀K⁻¹ ^ 2 * DK⁻¹ : K) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr huK0)
        (pow_ne_zero 2 (inv_ne_zero hz₀K0))) (inv_ne_zero hDK0)
    rw [hwKdef, hC, mumfordIdeal_C_mul fK hc0, hVdiff]
    exact mumfordIdeal_add_mul fK UK VK _
  calc ClassGroup.mk0 ⟨mumfordIdeal fK UK VK,
        mumfordIdeal_mem_nonZeroDivisors _ hUKm.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal fK ((X - C xK) * uτK) (C z₀K⁻¹ * vchK),
          mumfordIdeal_mem_nonZeroDivisors _
            (mul_ne_zero (monic_X_sub_C _).ne_zero huτm.ne_zero) _⟩ := by
        rw [hred]
        exact (congrArg ClassGroup.mk0 (Subtype.ext hidr)).symm
    _ = ClassGroup.mk0 ⟨mumfordIdeal fK ((X - C xK) * uτK)
          (cantorV fK (X - C xK) (C yKv) uτK vτK s₁ s₂ 0),
          mumfordIdeal_mem_nonZeroDivisors _
            (mul_ne_zero (monic_X_sub_C _).ne_zero huτm.ne_zero) _⟩ :=
        (congrArg ClassGroup.mk0 (Subtype.ext hidealc)).symm
    _ = _ := by rw [← hmul]

end ScaledReduction

section ScaledInstantiation

open nonZeroDivisors

variable {O : Type*} [CommRing O] [IsDomain O] {f uτ vτ : O[X]}

/-- **The scaled reduction transported out of `O⟦z⟧`**: the infinity-disk datum `(infU, V)`
mapped by a ring map `ρ` into a field represents `[P] + [τ]`, where `P` is the point
`(1/ρ(û), 1/(ρ(û)ᵍ·ρ(z)))`. Both consumers — evaluation at a disk parameter and transport to
the function field — are this lemma at their own `ρ`; the base map `χ` is passed as the
identity `hχ` so that each keeps its own spelling of it. -/
theorem mk0_map_infU {L : Type*} [Field L] [NeZero (2 : L)] {ρ : O⟦X⟧ →+* L} {χ : O →+* L}
    (hχ : ρ.comp (PowerSeries.C : O →+* O⟦X⟧) = χ)
    [Fact (Odd (f.map χ).natDegree)] [Fact (Squarefree (f.map χ))]
    (hf : f.Monic) (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    {z u : L} (hz : ρ PowerSeries.X = z) (hu : ρ (infSeries hf) = u)
    (hz0 : z ≠ 0) (hu0 : u ≠ 0) :
    ClassGroup.mk0 ⟨mumfordIdeal (f.map χ) ((infU hf uτ vτ).map ρ) (V.map ρ),
        mumfordIdeal_mem_nonZeroDivisors _
          (((infU_monic hf huτ hvτ hdeg hdvdτ).map ρ).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map χ) (X - C u⁻¹)
          (C (z⁻¹ * u⁻¹ ^ uτ.natDegree)),
          mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal (f.map χ) (uτ.map χ) (vτ.map χ),
            mumfordIdeal_mem_nonZeroDivisors _ ((huτ.map χ).ne_zero) _⟩ := by
  subst hz
  subst hu
  set g := uτ.natDegree with hgdef
  set u := ρ (infSeries hf) with hudef
  have hmapmap (p : O[X]) : (p.map (PowerSeries.C : O →+* O⟦X⟧)).map ρ = p.map χ := by
    rw [Polynomial.map_map, hχ]
  have hDK0 : ρ (aeval (infSeries hf) f.reverse) ≠ 0 := by
    obtain ⟨hlc, -⟩ := infQ_leadingCoeff_natDegree hf huτ hvτ hdeg hdvdτ
    have h := congrArg ρ hlc
    rw [map_mul, map_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hvch : (infV hf uτ vτ).map ρ
      = C (ρ PowerSeries.X) * vτ.map χ + C (ρ (infC hf uτ vτ)) * uτ.map χ := by
    rw [infV, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C,
      hmapmap, hmapmap]
  have hfacK := congrArg (Polynomial.map ρ) (infV_sq_sub_factor hf huτ hvτ hdeg hdvdτ)
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_pow, map_C, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_mul, map_C, Polynomial.map_X, hmapmap,
    hmapmap] at hfacK
  have hUQ : (infU hf uτ vτ).map ρ
      = C (ρ (aeval (infSeries hf) f.reverse)) * (infQ hf uτ vτ).map ρ := by
    rw [infU, Polynomial.map_mul, map_C]
  have haevalρ (p : (O⟦X⟧)[X]) (w : O⟦X⟧) : ρ (aeval w p) = (p.map ρ).eval (ρ w) := by
    rw [coe_aeval_eq_eval, eval_map_apply]
  let : Invertible u⁻¹ := ⟨u, mul_inv_cancel₀ hu0, inv_mul_cancel₀ hu0⟩
  have hvchx : ((infV hf uτ vτ).map ρ).eval u⁻¹ = u⁻¹ ^ g := by
    have h := congrArg ρ (aeval_reflect_infV hf huτ hvτ)
    rw [haevalρ, ← reflect_map, map_one, ← hudef] at h
    have h2 := eval₂_reflect_mul_pow (RingHom.id L) u⁻¹ g ((infV hf uτ vτ).map ρ)
      (le_trans natDegree_map_le (natDegree_infV_le hf hvτ.le))
    rw [eval₂_id, eval₂_id, show (⅟u⁻¹ : L) = u from rfl, h, one_mul] at h2
    exact h2.symm
  have huτx : (uτ.map χ).eval u⁻¹ ≠ 0 := by
    have hA := congrArg ρ (aeval_infSeries_reverse_mul_infTauInv hf huτ)
    rw [map_mul, map_one] at hA
    have hA0 : ρ (aeval (infSeries hf) uτ.reverse) ≠ 0 := left_ne_zero_of_mul_eq_one hA
    have hAv : ρ (aeval (infSeries hf) uτ.reverse) = (reflect g (uτ.map χ)).eval u := by
      have h1 : (aeval (infSeries hf) uτ.reverse : O⟦X⟧)
          = (uτ.reverse.map PowerSeries.C : (O⟦X⟧)[X]).eval (infSeries hf) := by
        rw [aeval_def, eval_map, ← PowerSeries.algebraMap_eq]
      rw [h1, ← eval_map_apply, hmapmap, ← hudef, Polynomial.reverse, ← reflect_map, ← hgdef]
    have h2 := eval₂_reflect_mul_pow (RingHom.id L) u⁻¹ g (uτ.map χ) natDegree_map_le
    rw [eval₂_id, eval₂_id, show (⅟u⁻¹ : L) = u from rfl] at h2
    intro h0
    rw [h0] at h2
    refine hA0 ?_
    rw [hAv]
    exact (mul_eq_zero.mp h2).resolve_right (pow_ne_zero g (inv_ne_zero hu0))
  have hVK : C (ρ PowerSeries.X) * V.map ρ
      = -(((infV hf uτ vτ).map ρ) %ₘ ((infU hf uτ vτ).map ρ)) := by
    have h := congrArg (Polynomial.map ρ) hV
    rwa [Polynomial.map_mul, map_C, Polynomial.map_neg,
      map_modByMonic ρ (infU_monic hf huτ hvτ hdeg hdvdτ)] at h
  exact mk0_mumfordIdeal_of_scaled_factor (fK := f.map χ) hu0 hz0 hDK0
    (huτ.map χ) ((infU_monic hf huτ hvτ hdeg hdvdτ).map ρ) hvch hfacK hUQ hvchx huτx
    (map_dvd_sq_sub χ hdvdτ) hVK

end ScaledInstantiation

section InfPointwiseClass

open nonZeroDivisors

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {f uτ vτ : O[X]}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The infinity-disk pipeline computes `[P_z - ∞] + [τ]` pointwise**: evaluating the
reduced datum `(U, V)` at a nonzero point `z₀` of the maximal ideal produces a reduced
Mumford datum representing the class `(P_{z₀}) - (∞) + [τ]` over the fraction field, where
`P_{z₀} = (1/û(z₀), 1/(û(z₀)ᵍ·z₀))` is the infinity-disk point. -/
theorem mk0_infU_eval (hf : f.Monic) (huτ : uτ.Monic) (hvτ : vτ.natDegree < uτ.natDegree)
    (hdeg : f.natDegree = 2 * uτ.natDegree + 1) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    {V : (O⟦X⟧)[X]} (hV : C PowerSeries.X * V = -(infV hf uτ vτ %ₘ infU hf uτ vτ))
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) (hz₀0 : z₀ ≠ 0) :
    ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
        (((infU hf uτ vτ).map (PSeries.evalRingHom hz₀)).map (algebraMap O (FractionRing O)))
        ((V.map (PSeries.evalRingHom hz₀)).map (algebraMap O (FractionRing O))),
        mumfordIdeal_mem_nonZeroDivisors _
          ((((infU_monic hf huτ hvτ hdeg hdvdτ).map _).map _).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
          (X - C (algebraMap O (FractionRing O) (PSeries.eval z₀ (infSeries hf)))⁻¹)
          (C ((algebraMap O (FractionRing O) z₀)⁻¹
              * (algebraMap O (FractionRing O) (PSeries.eval z₀ (infSeries hf)))⁻¹
                ^ uτ.natDegree)),
          mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (uτ.map (algebraMap O (FractionRing O)))
            (vτ.map (algebraMap O (FractionRing O))),
            mumfordIdeal_mem_nonZeroDivisors _ ((huτ.map _).ne_zero) _⟩ := by
  classical
  set K := FractionRing O
  set φK : O →+* K := algebraMap O K
  set ε : O⟦X⟧ →+* O := PSeries.evalRingHom hz₀
  set ρ : O⟦X⟧ →+* K := φK.comp ε with hρdef
  have hinjK : Function.Injective φK := IsFractionRing.injective O K
  have hεapp (x : O⟦X⟧) : ε x = PSeries.eval z₀ x :=
    congrFun (PSeries.coe_evalRingHom hz₀) x
  have hρC (x : O) : ρ (PowerSeries.C x) = φK x := by
    rw [hρdef, RingHom.comp_apply, hεapp, PSeries.eval_C]
  have hρX : ρ PowerSeries.X = φK z₀ := by rw [hρdef, RingHom.comp_apply, hεapp, PSeries.eval_X]
  set g := uτ.natDegree
  set uK : K := ρ (infSeries hf) with huKdef
  have huKeval : uK = φK (PSeries.eval z₀ (infSeries hf)) := by
    rw [huKdef, hρdef, RingHom.comp_apply, hεapp]
  have huK0 : uK ≠ 0 := by
    rw [huKeval, Ne, map_eq_zero_iff φK hinjK]
    exact eval_infSeries_ne_zero hf hz₀ hz₀0
  have hz₀K0 : φK z₀ ≠ 0 := by rwa [Ne, map_eq_zero_iff φK hinjK]
  -- the scaled reduction, instantiated along `ρ`
  have hkey := mk0_map_infU (RingHom.ext hρC) hf huτ hvτ hdeg hdvdτ hV hρX huKdef.symm
    hz₀K0 huK0
  have hgoalL : (((infU hf uτ vτ).map ε).map φK) = (infU hf uτ vτ).map ρ := by
    rw [Polynomial.map_map, hρdef]
  have hgoalV : ((V.map ε).map φK) = V.map ρ := by rw [Polynomial.map_map, hρdef]
  calc ClassGroup.mk0 ⟨mumfordIdeal (f.map φK) (((infU hf uτ vτ).map ε).map φK)
        ((V.map ε).map φK), mumfordIdeal_mem_nonZeroDivisors _
          ((((infU_monic hf huτ hvτ hdeg hdvdτ).map _).map _).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map φK) ((infU hf uτ vτ).map ρ) (V.map ρ),
          mumfordIdeal_mem_nonZeroDivisors _
            (((infU_monic hf huτ hvτ hdeg hdvdτ).map ρ).ne_zero) _⟩ := by
        have hid1 : mumfordIdeal (f.map φK) (((infU hf uτ vτ).map ε).map φK)
            ((V.map ε).map φK) = mumfordIdeal (f.map φK) ((infU hf uτ vτ).map ρ) (V.map ρ) := by
          rw [hgoalL, hgoalV]
        exact congrArg ClassGroup.mk0 (Subtype.ext hid1)
    _ = _ := by
        rw [hkey]
        have hid2 : mumfordIdeal (f.map φK) (X - C uK⁻¹) (C ((φK z₀)⁻¹ * uK⁻¹ ^ g))
            = mumfordIdeal (f.map φK)
              (X - C (φK (PSeries.eval z₀ (infSeries hf)))⁻¹)
              (C ((φK z₀)⁻¹ * (φK (PSeries.eval z₀ (infSeries hf)))⁻¹ ^ uτ.natDegree)) := by
          rw [huKeval]
        exact congrArg (· * _) (congrArg ClassGroup.mk0 (Subtype.ext hid2))

end InfPointwiseClass

section NotIntegral

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsIntegrallyClosed O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- The inverse of a nonzero maximal-ideal element is not integral (over the integrally
closed `O`). -/
theorem not_isIntegral_inv_algebraMap {m : O} (hm : m ∈ maximalIdeal O) (hm0 : m ≠ 0) :
    ¬IsIntegral O ((algebraMap O K m)⁻¹) := by
  intro h
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  have hφm : algebraMap O K m ≠ 0 := by rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
  have h1 : algebraMap O K (c * m) = algebraMap O K 1 := by
    rw [map_mul, hc, inv_mul_cancel₀ hφm, map_one]
  have h2 : IsUnit m := isUnit_iff_exists_inv.mpr
    ⟨c, by rw [mul_comm]; exact IsFractionRing.injective O K h1⟩
  exact (mem_maximalIdeal m).mp hm h2

end NotIntegral

section InfRedJ

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O] {f : O[X]}

/-- The infinity-disk point at parameter `z₀ ≠ 0`, in coordinates from the coordinate
series, lies on the curve. -/
theorem inv_eval_infSeries_onCurve (hf : f.Monic) {g : ℕ}
    (hgdeg : f.natDegree = 2 * g + 1) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) (hz₀0 : z₀ ≠ 0) :
    ((algebraMap O K z₀)⁻¹
        * (algebraMap O K (PSeries.eval z₀ (infSeries hf)))⁻¹ ^ g) ^ 2
      = (f.map (algebraMap O K)).eval
          (algebraMap O K (PSeries.eval z₀ (infSeries hf)))⁻¹ := by
  have hodd : Odd f.natDegree := by rw [hgdeg]; exact odd_two_mul_add_one g
  have hg : genus f = g := genus_eq_of_natDegree hgdeg
  have h := infRoot_onCurve (K := K) f hf hodd hz₀ hz₀0
  rwa [infRoot_eq_eval_infSeries hf hz₀, hg, mul_inv, ← inv_pow, mul_comm] at h

variable [IsAdicComplete (maximalIdeal O) O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- **The same-disk point difference at the infinity centre is in the kernel of
reduction**: the class of the infinity-disk point `P_{z₀}` reduces to `1` — its
`x`-coordinate is non-integral, so the point reduces to `∞_bar`, the disk centre. -/
theorem redJ_diskPointDiff_eq_one_inf (hf : f.Monic) (hdeg : 0 < f.natDegree) {g : ℕ}
    (hgdeg : f.natDegree = 2 * g + 1) {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) (hz₀0 : z₀ ≠ 0) :
    redJ (aj (f.map (algebraMap O (FractionRing O)))
        (algebraMap O (FractionRing O) (PSeries.eval z₀ (infSeries hf)))⁻¹
        ((algebraMap O (FractionRing O) z₀)⁻¹
          * (algebraMap O (FractionRing O) (PSeries.eval z₀ (infSeries hf)))⁻¹ ^ g)) = 1 :=
  redJ_aj_of_not_isIntegral hf hdeg (inv_eval_infSeries_onCurve hf hgdeg hz₀ hz₀0)
    (not_isIntegral_inv_algebraMap (eval_infSeries_mem hf hz₀)
      (eval_infSeries_ne_zero hf hz₀ hz₀0))

end InfRedJ

end ChabautyColeman
