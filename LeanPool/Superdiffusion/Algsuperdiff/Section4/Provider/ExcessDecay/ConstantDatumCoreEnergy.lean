/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ConstantDatumCorrector
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryOuterCaccioppoli
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorDatum

/-!
# ConstantDatumCoreEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior Caccioppoli energy through a constant-datum comparison

The interior specialization of `l.coarse.grained.Caccioppoli.RHS` used by the
proved interior lane
(`CaccioppoliInteriorDatum.exists_interiorCaccioppoliEnergy_subConst`) applies
CoarseGraining's boundary theorem to `u - c` and pays CoarseGraining's own
force leg `t^{-8} λ_{t,1}^{-1} [g]²`.  This module runs the *comparison* form
instead:

```text
  E_core(∇u) = E_core(∇(u-c))
      ≤ 2 E_core(∇((u-c) - ρ)) + 2 E_core(∇ρ)
      ≤ 2 P (λ_{t,1} 3^{-2m} ‖(u-c) - ρ‖²_{L²(Q)}) + 2 · 18^d · E_Q(∇ρ) ,
```

where `ρ` is the cube's own zero-trace corrector at the *same* force `g`.  The
difference `(u-c) - ρ` solves the **homogeneous** equation, so CoarseGraining's
force leg disappears from the Caccioppoli application altogether; the force
reappears only through the two corrector bounds of `ConstantDatumCorrector`,
both of which carry `λ_{t,2}^{-1}` explicitly and only `t^{-3}`.  Splitting the
`L²` object and inserting them gives the display of
`exists_constantDatumCoreEnergy` below:

```text
  E_core(∇u) ≤ K ( P λ_{t,1} ( 3^{-2m} ‖u - c‖²_{L²(Q)}
                              + (t^{-3} λ_{t,2}^{-1} [g]_{B^{2t}(Q)})² )
                  + t^{-3} λ_{t,2}^{-1} [g]²_{B^{2t}(Q)} ) .
```

The comparison object is `c + ρ`, i.e. the Dirichlet solution with the **constant
datum** `c`; the two `∇h` legs of the printed boundary display vanish for it,
which is why no boundary-gradient term appears.  Nothing here uses the good
event: the display is deterministic and keeps `λ_{t,1}`, `λ_{t,2}` separate.

## What this buys (disclosed)

Against the proved interior display, the force envelope improves from `t^{-8}`
to `t^{-6}` *provided* the caller can pay `λ_{t,1} λ_{t,2}^{-2} ≲ σ^{-1}` —
which is exactly what the frozen theorem's good event gives.  Nothing is gained
deterministically: with only CoarseGraining's generic ellipticity comparison
the two displays agree.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; `e.energy.bound.interior`.
* CoarseGraining, `Book/Ch03/Theorems/CoarseCaccioppoli/*`,
  `Book/Ch03/Theorems/CoarsePoincare.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The `L²` split -/

/-- `(A + B)² ≤ 2A² + 2B²`, in the form the split needs. -/
private theorem sq_le_two_add_two {C A B : ℝ} (hC : 0 ≤ C) (h : C ≤ A + B) :
    C ^ (2 : ℕ) ≤ 2 * A ^ (2 : ℕ) + 2 * B ^ (2 : ℕ) := by
  have h1 : C ^ (2 : ℕ) ≤ (A + B) ^ (2 : ℕ) := pow_le_pow_left₀ hC h 2
  have h2 : (0 : ℝ) ≤ (A - B) ^ (2 : ℕ) := sq_nonneg _
  have h3 : (A + B) ^ (2 : ℕ) = A ^ (2 : ℕ) + 2 * (A * B) + B ^ (2 : ℕ) := by ring
  have h4 : (A - B) ^ (2 : ℕ) = A ^ (2 : ℕ) - 2 * (A * B) + B ^ (2 : ℕ) := by ring
  linarith only [h1, h2, h3, h4]

/-- The normalized `L²` triangle inequality on the open cube, in the squared
form the Caccioppoli display consumes. -/
theorem normalizedL2SqOnSet_sub_le_two_add_two (Q : TriadicCube d)
    {f h : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    normalizedL2SqOnSet (openCubeSet Q) (fun y => f y - h y) ≤
      2 * normalizedL2SqOnSet (openCubeSet Q) f +
        2 * normalizedL2SqOnSet (openCubeSet Q) h := by
  have hsub : MemLp (fun y => f y - h y) 2 (normalizedCubeMeasure Q) := hf.sub hh
  have hle : eLpNorm (fun y => f y - h y) 2 (normalizedCubeMeasure Q) ≤
      eLpNorm f 2 (normalizedCubeMeasure Q) + eLpNorm h 2 (normalizedCubeMeasure Q) :=
    MeasureTheory.eLpNorm_sub_le (by norm_num)
  have hne : eLpNorm f 2 (normalizedCubeMeasure Q) +
      eLpNorm h 2 (normalizedCubeMeasure Q) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hf.eLpNorm_lt_top.ne, hh.eLpNorm_lt_top.ne⟩
  have htri : cubeLpNorm Q 2 (fun y => f y - h y) ≤
      cubeLpNorm Q 2 f + cubeLpNorm Q 2 h := by
    have hmono := ENNReal.toReal_mono hne hle
    rw [ENNReal.toReal_add hf.eLpNorm_lt_top.ne hh.eLpNorm_lt_top.ne] at hmono
    exact hmono
  rw [normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _ hsub,
    normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _ hf,
    normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _ hh]
  exact sq_le_two_add_two (cubeLpNorm_nonneg Q 2 _) htri

/-! ## 2. The composition, on abstract reals -/

/-- The arithmetic of the comparison composition: the Minkowski split, the
`L²` split, the core-volume ratio and the two corrector bounds, folded into one
constant.  Abstract in every quantity, so no analytic content hides here. -/
private theorem constantDatum_core_arith
    {Ecore D Ev EQ Lsub P lam S X Lv F2 G KE KL Kd K : ℝ}
    (h2 : Ecore ≤ 2 * D + 2 * Ev) (h3 : D ≤ P * (lam * S * Lsub))
    (h4 : Lsub ≤ 2 * X + 2 * Lv) (h5 : Ev ≤ Kd * EQ) (h6 : EQ ≤ KE * G)
    (h7 : S * Lv ≤ KL * F2)
    (hP : 0 ≤ P) (hlam : 0 ≤ lam) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hF2 : 0 ≤ F2) (hG : 0 ≤ G) (hKd : 0 ≤ Kd)
    (hK4 : 4 ≤ K) (hKKL : 4 * KL ≤ K) (hKKE : 2 * Kd * KE ≤ K) :
    Ecore ≤ K * (P * lam * (S * X + F2) + G) := by
  have hPlam : 0 ≤ P * lam := mul_nonneg hP hlam
  have hstep3 : D ≤ P * (lam * S * (2 * X + 2 * Lv)) :=
    h3.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h4 (mul_nonneg hlam hS)) hP)
  have hexp : P * (lam * S * (2 * X + 2 * Lv)) =
      2 * (P * lam) * (S * X) + 2 * (P * lam) * (S * Lv) := by ring
  have hstep7 : 2 * (P * lam) * (S * Lv) ≤ 2 * (P * lam) * (KL * F2) := by
    have hnn : (0 : ℝ) ≤ 2 * (P * lam) := by linarith only [hPlam]
    have h := mul_le_mul_of_nonneg_left h7 hnn
    linarith only [h]
  have hD : D ≤ 2 * (P * lam) * (S * X) + 2 * (P * lam) * (KL * F2) := by
    rw [hexp] at hstep3
    linarith only [hstep3, hstep7]
  have hEv : Ev ≤ Kd * (KE * G) := h5.trans (mul_le_mul_of_nonneg_left h6 hKd)
  have hA1 : 0 ≤ P * lam * (S * X) := mul_nonneg hPlam (mul_nonneg hS hX)
  have hA2 : 0 ≤ P * lam * F2 := mul_nonneg hPlam hF2
  have hc1 : 4 * (P * lam * (S * X)) ≤ K * (P * lam * (S * X)) :=
    mul_le_mul_of_nonneg_right hK4 hA1
  have hc2 : 4 * KL * (P * lam * F2) ≤ K * (P * lam * F2) :=
    mul_le_mul_of_nonneg_right hKKL hA2
  have hc3 : 2 * Kd * KE * G ≤ K * G := mul_le_mul_of_nonneg_right hKKE hG
  have htarget : K * (P * lam * (S * X + F2) + G) =
      K * (P * lam * (S * X)) + K * (P * lam * F2) + K * G := by ring
  linarith only [h2, hD, hEv, hc1, hc2, hc3, htarget]

/-! ## 3. The constant-datum core-energy display -/

variable [NeZero d]

/-- **The interior Caccioppoli energy through the constant-datum comparison.**

See the module docstring for the display.  The comparison solution is `c + ρ`
with `ρ` the cube's own zero-trace corrector; the boundary-gradient legs of the
printed display vanish because the datum is constant, and the Caccioppoli force
leg vanishes because the difference solves the homogeneous equation. -/
theorem exists_constantDatumCoreEnergy (d : ℕ) [NeZero d] :
    ∃ C₁ K : ℝ, 0 < C₁ ∧ 0 < K ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t c : ℝ} {x : Vec d}
        {g : Vec d → Vec d} (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))),
        IsForcedEquation Q a u g → 0 < t → t ≤ 1 / 4 →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        ForceBesovRegularity Q (2 * t) g →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u ≤
            K * (caccioppoliWithRHSPrefactor C₁ Q a (1 / 4) t * Ch02.lambdaS Q t a *
                  (Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                      normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - c) +
                    (Real.rpow t (-3 : ℝ) *
                        Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
                        scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^
                      (2 : ℕ)) +
                Real.rpow t (-3 : ℝ) *
                  Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ (2 : ℕ)) := by
  obtain ⟨C₁, hC₁, hcacc⟩ := exists_boundaryCaccioppoliEnergy_ofLocalizedDifference d
  obtain ⟨KE, hKE, hEnergy⟩ := exists_correctorParentEnergy_le d
  obtain ⟨KL, hKL, hL2⟩ := exists_correctorParentL2_forceScale d
  refine ⟨C₁, 4 * KL + 2 * (18 : ℝ) ^ d * KE + 4, hC₁, by positivity, ?_⟩
  intro Q a t c x g u hu ht ht4 hpatch hg
  have ht2 : t < 1 / 2 := by linarith only [ht4]
  have hgCube : MemVectorL2 (cubeSet Q) g := memVectorL2_cubeSet_of_forceBesovRegularity hg
  set rho : ZeroTraceDirichletCorrectorData Q (publicCoeffField Q a) g :=
    constantDatumCorrector Q a hgCube with hrho
  set v : H1Function (Ch02.cubeDomain Q : Set (Vec d)) :=
    (boundaryForcedCaccioppoliCorrectorOpenH10 (Q := Q) (a := a) rho).toH1Function with hv
  set uc : H1Function (Ch02.cubeDomain Q : Set (Vec d)) := u - constantDatumH1 Q c with huc
  have hucgrad : uc.grad = u.grad := sub_constantDatumH1_grad Q u c
  have hucfun : uc.toFun = fun y => u.toFun y - c := sub_constantDatumH1_toFun Q u c
  have hucEq : IsForcedEquation Q a uc g := by
    intro phi
    rw [hucgrad]
    exact hu phi
  have hvEq : IsForcedEquation Q a v g :=
    (boundaryForcedCaccioppoliCorrectorForcedCubeSolution (Q := Q) (a := a) rho).weakSolution
  have hx : x ∈ openCubeSet Q := hpatch (mem_openCubeAtScale_self x (Q.scale - 1))
  have hdiff : Ch01.LocalizedZeroTraceFunctionOn (Ch02.cubeDomain Q : Set (Vec d))
      (openCubeAtScale x (Q.scale - 1)) (fun y => uc.toFun y - v.toFun y) :=
    localizedZeroTraceFunctionOn_of_memH1
      (by
        rw [Ch02.cubeDomain_coe]
        exact isOpenBoundedConvexDomain_openCubeSet Q)
      (by
        rw [Ch02.cubeDomain_coe]
        exact hpatch)
      ⟨uc - v, H1Function.sub_toFun uc v⟩
  have hcaccbound := hcacc (s := 1 / 4) uc v hucEq hvEq hdiff (by norm_num) (by norm_num) ht
    (by linarith only [ht2]) (by linarith only [ht4]) hx
  have hsplit := localizedCoeffEnergyValue_core_le_two_mul_sub_add (x := x) (a := a) uc v
  have hcore := localizedCoeffEnergyValue_core_le_eighteen_pow_mul_parent (a := a) hx v
  have hEv := hEnergy rho ht ht2 hg
  have hLv := hL2 rho ht ht4 hg
  -- the `L²` split
  have hmemU : MemLp (fun y => u.toFun y - c) 2 (normalizedCubeMeasure Q) := by
    let : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
      ⟨normalizedCubeMeasure_apply_univ Q⟩
    exact (memLp_two_normalizedCubeMeasure_of_h1 Q u).sub (memLp_const c)
  have hmemV : MemLp v.toFun 2 (normalizedCubeMeasure Q) :=
    memLp_two_normalizedCubeMeasure_of_h1 Q v
  have hL2split : normalizedL2SqOnSet (openCubeSet Q) (fun y => uc.toFun y - v.toFun y) ≤
      2 * normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - c) +
        2 * normalizedL2SqOnSet (openCubeSet Q) v.toFun := by
    rw [hucfun]
    exact normalizedL2SqOnSet_sub_le_two_add_two Q hmemU hmemV
  -- the energy of `u` is the energy of `u - c`
  have hEqEnergy : localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) uc =
      localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u :=
    localizedCoeffEnergyValue_congr_grad (caccioppoliCoreSet Q x) (a.coeffOn Q) hucgrad
  rw [← hEqEnergy]
  -- nonnegativity data
  have hPnn : 0 ≤ caccioppoliWithRHSPrefactor C₁ Q a (1 / 4) t :=
    caccioppoliWithRHSPrefactor_nonneg hC₁.le (by norm_num) ht (by linarith only [ht4])
  have hlamnn : 0 ≤ Ch02.lambdaS Q t a := by
    have h := Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 1)
    exact h.le
  have hSnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hXnn : 0 ≤ normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - c) :=
    normalizedL2SqOnSet_nonneg _ _ (measurableSet_openCubeSet Q)
  have hGnn : (0 : ℝ) ≤ Real.rpow t (-3 : ℝ) *
      Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ (2 : ℕ) := by
    have hlam2 : (0 : ℝ) ≤ Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) :=
      Real.rpow_nonneg (Ch02.lambdaSq_finite_pos Q a ht (by norm_num : (1 : ℝ) ≤ 2)).le _
    have ht3 : (0 : ℝ) ≤ Real.rpow t (-3 : ℝ) := Real.rpow_nonneg ht.le _
    have hb : (0 : ℝ) ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ (2 : ℕ) :=
      pow_two_nonneg _
    exact mul_nonneg (mul_nonneg ht3 hlam2) hb
  have hF2nn : (0 : ℝ) ≤ (Real.rpow t (-3 : ℝ) *
      Real.rpow (Ch02.lambdaSq Q t (.finite 2) a) (-1 : ℝ) *
      scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g) ^ (2 : ℕ) :=
    pow_two_nonneg _
  have h18 : (0 : ℝ) ≤ (18 : ℝ) ^ d := by positivity
  have hp1 : (0 : ℝ) ≤ 4 * KL := by positivity
  have hp2 : (0 : ℝ) ≤ 2 * (18 : ℝ) ^ d * KE := by positivity
  exact constantDatum_core_arith hsplit hcaccbound hL2split hcore hEv hLv hPnn hlamnn
    hSnn hXnn hF2nn hGnn h18 (by linarith only [hp1, hp2]) (by linarith only [hp2])
    (by linarith only [hp1])

end

end Algsuperdiff.Section4.Provider.ExcessDecay
