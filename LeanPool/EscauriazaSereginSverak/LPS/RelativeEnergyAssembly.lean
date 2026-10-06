/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ComparisonGronwall
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinWeakSlices
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossLimitTerms
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossIdentity

/-!
# Relative energy from cross testing

The a.e. energy equality of the distinguished field combines with the
competitor's energy inequality and the relative cross identity to give the
integral inequality used in Gronwall's lemma.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Interval
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The squared distance of two velocity slices. -/
@[expose] def lpsComparisonDistanceSq (u v : ParabolicPoint → Vec3) (t : ℝ) : ℝ :=
  ∫ x : Vec3, ∑ k : Fin 3, (v (x,t) k - u (x,t) k) ^ 2

/-- The relative convection density for two velocity fields and their
specified gradients. -/
@[expose] def lpsRelativeConvection (u v : ParabolicPoint → Vec3)
    (Du Dv : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) : ℝ :=
  ∑ k : Fin 3, u z k * ∑ j : Fin 3,
    (v z j - u z j) * (Dv z k j - Du z k j)

/-- The squared difference of two specified gradients. -/
@[expose] def lpsRelativeGradientSq (Du Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) : ℝ :=
  ∑ k : Fin 3, ∑ j : Fin 3, (Dv z k j - Du z k j) ^ 2

/-- The squared gradient difference expands into the two dissipation terms
and their cross pairing on every time slab. -/
theorem lps_relative_gradient_expansion
    {T : ℝ} {a b : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T b v Dv pv) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        lpsRelativeGradientSq Du Dv z) =
        ((∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j) -
          2 * (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)) +
        (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j) := by
  let μT : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
  have hDu2 := serrinWeak_gradient_memLp_two hU
  have hDv2 := serrinWeak_gradient_memLp_two hV
  have hDiff2 : MemLp (fun z : ParabolicPoint => Dv z - Du z) 2 μT := hDv2.sub hDu2
  have hG (f g : ParabolicPoint → Fin 3 → Vec3)
      (hf : MemLp f 2 μT) (hg : MemLp g 2 μT) :
      Integrable (fun z : ParabolicPoint =>
        ∑ k : Fin 3, ∑ j : Fin 3, f z k j * g z k j) μT := by
    refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => ?_
    exact memLp_one_iff_integrable.mp (((hf.eval k).eval j).mul (r := 1) ((hg.eval k).eval j))
  have hGvv := hG Dv Dv hDv2 hDv2
  have hGuu := hG Du Du hDu2 hDu2
  have hGuv := hG Du Dv hDu2 hDv2
  have hGdd := hG (fun z => Dv z - Du z) (fun z => Dv z - Du z) hDiff2 hDiff2
  have hGdd' : Integrable (fun z : ParabolicPoint => lpsRelativeGradientSq Du Dv z) μT :=
    hGdd.congr (Eventually.of_forall fun z => by
      simp only [lpsRelativeGradientSq, Pi.sub_apply, sq])
  have hGvv' : Integrable (fun z : ParabolicPoint =>
      ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j) μT := hGvv
  have hGuu' : Integrable (fun z : ParabolicPoint =>
      ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j) μT := hGuu
  have hGuv' : Integrable (fun z : ParabolicPoint =>
      ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j) μT := hGuv
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [] with t ht
  have hle := serrin_slab_restrict_le ht.2.le
  have hGddt := hGdd'.mono_measure hle
  have hGvvt := hGvv'.mono_measure hle
  have hGuut := hGuu'.mono_measure hle
  have hGuvt := hGuv'.mono_measure hle
  have h2uv : Integrable (fun z : ParabolicPoint =>
      2 * ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := hGuvt.const_mul 2
  have hA : Integrable (fun z : ParabolicPoint =>
      (∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j) -
        2 * ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) := hGvvt.sub h2uv
  calc
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        lpsRelativeGradientSq Du Dv z) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ((∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j) -
          2 * ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j) +
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j := by
      congr 1
      funext z
      simp only [lpsRelativeGradientSq, Fin.sum_univ_three]
      ring_nf
    _ = _ := by
      rw [integral_add hA hGuut, integral_sub hGvvt h2uv, integral_const_mul]

/-- A fixed-time relative-convection estimate integrates to its space-time
counterpart on almost every initial slab. -/
theorem lps_relative_convection_bound_integrated
    {T K : ℝ} {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3} {m : ℝ → ℝ}
    (hSliceBound : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x, τ)) ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x, τ)) +
          K * (m τ * lpsComparisonDistanceSq u v τ))
    (hC : Integrable (lpsRelativeConvection u v Du Dv)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hD : Integrable (lpsRelativeGradientSq Du Dv)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hmE : IntegrableOn (fun τ => m τ * lpsComparisonDistanceSq u v τ) (Ioo 0 T)) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        lpsRelativeConvection u v Du Dv z) ≤
        (1 / 2 : ℝ) *
          (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            lpsRelativeGradientSq Du Dv z) +
          K * ∫ τ in (0 : ℝ)..t,
            m τ * lpsComparisonDistanceSq u v τ := by
  have hSliceOnOpen := (ae_restrict_iff' measurableSet_Ioo).mp hSliceBound
  rw [ae_restrict_iff' measurableSet_Ioo] at hSliceBound ⊢
  filter_upwards [hSliceBound] with t hbound ht
  have ht0 : 0 ≤ t := ht.1.le
  have hCshort := hC.mono_measure (serrin_slab_restrict_le ht.2.le)
  have hDshort := hD.mono_measure (serrin_slab_restrict_le ht.2.le)
  have hCshortTime := serrin_intervalIntegrable_of_slab ht0 hCshort
  have hDshortTime := serrin_intervalIntegrable_of_slab ht0 hDshort
  have hmEt : IntervalIntegrable
      (fun τ => m τ * lpsComparisonDistanceSq u v τ) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
    exact hmE.mono_set fun τ hτ => ⟨hτ.1, lt_of_le_of_lt hτ.2 ht.2⟩
  have hboundIcc : ∀ᵐ τ ∂(volume.restrict (Icc 0 t)),
      (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x,τ)) ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x,τ)) +
          K * (m τ * lpsComparisonDistanceSq u v τ) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hSliceOnOpen, Measure.ae_ne volume (0 : ℝ)] with τ hτ hτ0 hτI
    exact hτ ⟨lt_of_le_of_ne hτI.1 (Ne.symm hτ0),
      lt_of_le_of_lt hτI.2 ht.2⟩
  have hmono := intervalIntegral.integral_mono_ae_restrict ht0 hCshortTime
    ((hDshortTime.const_mul (1 / 2 : ℝ)).add (hmEt.const_mul K)) hboundIcc
  have hCslab := serrin_intervalIntegral_eq_slab ht0 hCshort
  have hDslab := serrin_intervalIntegral_eq_slab ht0 hDshort
  rw [intervalIntegral.integral_add (hDshortTime.const_mul (1 / 2 : ℝ))
      (hmEt.const_mul K), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hCslab, hDslab] at hmono
  exact hmono

/-- A relative cross identity, the distinguished energy equality, the
competitor energy inequality, and an integrated relative-convection bound
imply the comparison inequality at almost every time. The energy equality is
an explicit hypothesis so it can be supplied by `lps_serrin_energy_equality`.
-/
theorem lps_relative_energy_inequality_from_identities
    {T K : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ} {m : ℝ → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hEnergyEquality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j)
    (hEnergyInequality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j)
    (hRelativeCross : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -(∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            lpsRelativeConvection u v Du Dv z) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)
    (hConvectionBound : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        lpsRelativeConvection u v Du Dv z) ≤
        (1 / 2 : ℝ) *
          (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            lpsRelativeGradientSq Du Dv z) +
          K * ∫ τ in (0 : ℝ)..t,
            m τ * lpsComparisonDistanceSq u v τ) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t ≤
        2 * K * ∫ τ in (0 : ℝ)..t,
          m τ * lpsComparisonDistanceSq u v τ := by
  have hSliceEnergy : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t =
        (∫ x : Vec3, ∑ k : Fin 3, v (x,t) k * v (x,t) k) -
          2 * (∫ x : Vec3, ∑ k : Fin 3, v (x,t) k * u (x,t) k) +
          (∫ x : Vec3, ∑ k : Fin 3, u (x,t) k * u (x,t) k) := by
    filter_upwards [serrinWeak_slices_ae hU, serrinWeak_slices_ae hV]
      with t hu hv
    rcases hu with ⟨hu2, -, -, -, -⟩
    rcases hv with ⟨hv2, -, -, -, -⟩
    have hdiff2 : MemLp (fun x : Vec3 => v (x,t) - u (x,t)) 2 volume := hv2.sub hu2
    have hV2 : Integrable (fun x : Vec3 =>
        ∑ k : Fin 3, v (x,t) k * v (x,t) k) volume := by
      refine integrable_finsetSum _ fun k _ => ?_
      exact (hv2.eval k).integrable_mul (hv2.eval k)
    have hU2 : Integrable (fun x : Vec3 =>
        ∑ k : Fin 3, u (x,t) k * u (x,t) k) volume := by
      refine integrable_finsetSum _ fun k _ => ?_
      exact (hu2.eval k).integrable_mul (hu2.eval k)
    have hVU : Integrable (fun x : Vec3 =>
        ∑ k : Fin 3, v (x,t) k * u (x,t) k) volume := by
      refine integrable_finsetSum _ fun k _ => ?_
      exact (hv2.eval k).integrable_mul (hu2.eval k)
    have hDiff : Integrable (fun x : Vec3 =>
        ∑ k : Fin 3, (v (x,t) k - u (x,t) k) ^ 2) volume := by
      refine integrable_finsetSum _ fun k _ => ?_
      exact (hdiff2.eval k).integrable_mul (hdiff2.eval k) |>.congr
        (Eventually.of_forall fun x => by simp [sq])
    have hTwoVU : Integrable (fun x : Vec3 =>
        2 * ∑ k : Fin 3, v (x,t) k * u (x,t) k) volume := hVU.const_mul 2
    have hA : Integrable (fun x : Vec3 =>
        (∑ k : Fin 3, v (x,t) k * v (x,t) k) -
          2 * ∑ k : Fin 3, v (x,t) k * u (x,t) k) volume := hV2.sub hTwoVU
    calc
      lpsComparisonDistanceSq u v t =
          ∫ x : Vec3,
            ((∑ k : Fin 3, v (x,t) k * v (x,t) k) -
              2 * ∑ k : Fin 3, v (x,t) k * u (x,t) k) +
                ∑ k : Fin 3, u (x,t) k * u (x,t) k := by
        unfold lpsComparisonDistanceSq
        congr 1
        funext x
        simp only [Fin.sum_univ_three, sq]
        ring_nf
      _ = (∫ x : Vec3, ∑ k : Fin 3, v (x,t) k * v (x,t) k) -
            2 * (∫ x : Vec3, ∑ k : Fin 3, v (x,t) k * u (x,t) k) +
              (∫ x : Vec3, ∑ k : Fin 3, u (x,t) k * u (x,t) k) := by
        rw [integral_add hA hU2, integral_sub hV2 hTwoVU, integral_const_mul]
  have hGradientExpansion := lps_relative_gradient_expansion hU hV
  filter_upwards [hSliceEnergy, hEnergyEquality, hEnergyInequality,
      hRelativeCross, hGradientExpansion, hConvectionBound]
    with t hS hUE hVE hX hG hC
  rw [hS]
  let A : ℝ := ∫ x : Vec3, ∑ k : Fin 3, a x k * a x k
  let V0 : ℝ := ∫ x : Vec3, ∑ k : Fin 3, v (x,t) k * v (x,t) k
  let U0 : ℝ := ∫ x : Vec3, ∑ k : Fin 3, u (x,t) k * u (x,t) k
  let P0 : ℝ := ∫ x : Vec3, ∑ k : Fin 3, v (x,t) k * u (x,t) k
  let GV : ℝ := ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
    ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j
  let GU : ℝ := ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
    ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j
  let GX : ℝ := ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
    ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j
  let GC : ℝ := ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
    lpsRelativeConvection u v Du Dv z
  let GD : ℝ := ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
    lpsRelativeGradientSq Du Dv z
  let GI : ℝ := ∫ τ in (0 : ℝ)..t, m τ * lpsComparisonDistanceSq u v τ
  have hUE' : U0 - A = -2 * GU := hUE
  have hVE' : V0 ≤ A - 2 * GV := hVE
  have hX' : P0 - A = -GC - 2 * GX := by linarith only [hX]
  have hG' : GD = (GV - 2 * GX) + GU := by
    exact hG
  have hC' : GC ≤ (1 / 2 : ℝ) * GD + K * GI := by
    simpa only [GC, GD, GI] using hC
  have hEq : V0 - 2 * P0 + U0 = (V0 - A) + (U0 - A) - 2 * (P0 - A) := by ring
  have hIneq : (V0 - A) + (U0 - A) - 2 * (P0 - A) ≤
      (-2 * GV) + (-2 * GU) - 2 * (-GC - 2 * GX) := by
    rw [hUE', hX']
    linarith only [hVE']
  have hEq2 : (-2 * GV) + (-2 * GU) - 2 * (-GC - 2 * GX) =
      2 * GC - 2 * GD := by
    rw [hG']
    ring
  have hstep : V0 - 2 * P0 + U0 ≤ 2 * GC - 2 * GD :=
    hEq ▸ hIneq.trans_eq hEq2
  have hGDnonneg : 0 ≤ GD := by
    dsimp [GD, lpsRelativeGradientSq]
    exact integral_nonneg fun z => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _
  have hstep2 : 2 * GC - 2 * GD ≤ 2 * K * GI := by
    linarith only [hC', hGDnonneg]
  dsimp [V0, P0, U0, GC, GD, GI] at hstep hstep2
  exact hstep.trans hstep2

/-- The relative-energy inequality implies uniqueness when its coefficient and
energy product satisfy the hypotheses of integral Gronwall. -/
theorem lps_relative_energy_grow_zero
    {T K : ℝ} {u v : ParabolicPoint → Vec3} {m : ℝ → ℝ}
    (hT : 0 < T) (hK : 0 ≤ K)
    (hm : IntegrableOn m (Ioo 0 T))
    (hmNonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ m t)
    (hENonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      0 ≤ lpsComparisonDistanceSq u v t)
    (hmE : IntegrableOn (fun t => m t * lpsComparisonDistanceSq u v t) (Ioo 0 T))
    (hmENonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      0 ≤ m t * lpsComparisonDistanceSq u v t)
    (hineq : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t ≤
        2 * K * ∫ s in (0 : ℝ)..t, m s * lpsComparisonDistanceSq u v s) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), lpsComparisonDistanceSq u v t = 0 := by
  exact lps_comparison_grow_zero hT (by positivity) hm hmNonneg hENonneg hmE
    hmENonneg hineq

/-- The distinguished energy equality and the relative cross-testing inputs
imply that the two weak fields agree almost everywhere. -/
theorem lps_relative_energy_zero_from_identities
    {T K : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ} {m : ℝ → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hK : 0 ≤ K)
    (hEnergyEquality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j)
    (hEnergyInequality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j)
    (hRelativeCross : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -(∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            lpsRelativeConvection u v Du Dv z) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)
    (hConvectionBound : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        lpsRelativeConvection u v Du Dv z) ≤
        (1 / 2 : ℝ) *
          (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            lpsRelativeGradientSq Du Dv z) +
          K * ∫ τ in (0 : ℝ)..t,
            m τ * lpsComparisonDistanceSq u v τ)
    (hm : IntegrableOn m (Ioo 0 T))
    (hmNonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ m t)
    (hmE : IntegrableOn
      (fun t => m t * lpsComparisonDistanceSq u v t) (Ioo 0 T)) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t = 0 := by
  have hineq := lps_relative_energy_inequality_from_identities hU hV
    hEnergyEquality hEnergyInequality hRelativeCross hConvectionBound
  have hEnonneg : ∀ t, 0 ≤ lpsComparisonDistanceSq u v t := by
    intro t
    unfold lpsComparisonDistanceSq
    exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hmEnonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      0 ≤ m t * lpsComparisonDistanceSq u v t := by
    filter_upwards [hmNonneg] with t ht
    exact mul_nonneg ht (hEnonneg t)
  exact lps_relative_energy_grow_zero hU.pos hK hm hmNonneg
    (Filter.Eventually.of_forall hEnonneg) hmE hmEnonneg hineq

/-- Fixed-time comparison bounds, the relative cross identity, and the
distinguished energy equality imply almost-everywhere uniqueness. -/
theorem lps_relative_energy_zero_from_slice_bound
    {T K : ℝ} {a : Vec3 → Vec3}
    {u v : ParabolicPoint → Vec3}
    {Du Dv : ParabolicPoint → Fin 3 → Vec3}
    {pu pv : ParabolicPoint → ℝ} {m : ℝ → ℝ}
    (hU : IsSerrinWeakSolution T a u Du pu)
    (hV : IsSerrinWeakSolution T a v Dv pv)
    (hK : 0 ≤ K)
    (hEnergyEquality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, u (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Du z k j)
    (hEnergyInequality : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * v (x, t) k) ≤
        (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Dv z k j * Dv z k j)
    (hRelativeCross : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, ∑ k : Fin 3, v (x, t) k * u (x, t) k) -
          (∫ x : Vec3, ∑ k : Fin 3, a x k * a x k) =
        -(∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            lpsRelativeConvection u v Du Dv z) -
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
            ∑ k : Fin 3, ∑ j : Fin 3, Du z k j * Dv z k j)
    (hSliceBound : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      (∫ x : Vec3, lpsRelativeConvection u v Du Dv (x, τ)) ≤
        (1 / 2 : ℝ) *
          (∫ x : Vec3, lpsRelativeGradientSq Du Dv (x, τ)) +
          K * (m τ * lpsComparisonDistanceSq u v τ))
    (hC : Integrable (lpsRelativeConvection u v Du Dv)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hD : Integrable (lpsRelativeGradientSq Du Dv)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hm : IntegrableOn m (Ioo 0 T))
    (hmNonneg : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ m t)
    (hmE : IntegrableOn
      (fun t => m t * lpsComparisonDistanceSq u v t) (Ioo 0 T)) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      lpsComparisonDistanceSq u v t = 0 := by
  have hConvectionBound := lps_relative_convection_bound_integrated hSliceBound hC hD hmE
  exact lps_relative_energy_zero_from_identities hU hV hK hEnergyEquality
    hEnergyInequality hRelativeCross hConvectionBound hm hmNonneg hmE

end ESS

end
