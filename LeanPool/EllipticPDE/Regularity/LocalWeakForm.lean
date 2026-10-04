/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.DifferentiatedEquation


/-!
# Localising the bilinear pairing to plain integrals

The weak formulation a solution satisfies pairs `H1amb Ω` vectors through the bounded bilinear
form `Op.fullBilin`. Every localised step of interior regularity instead works with plain
integrals over a compact `V ⊆ Ω` against a test function supported in `V`, on
`Lp ℝ 2 (volume.restrict V)` classes. This file is the bridge between the two.

The derivation is mechanical. A test function supported in `V` has its graph in `H₀¹(Ω)`, so the
weak formulation applies to it; `EllipticCoeff.bilin_apply` and
`FullEllipticOp.lowerBilin_apply` expand the pairing into inner products; `inner_actL_eq` and
`inner_mulCoeffL_eq` turn each of those into an integral over `Ω`; each integrand has a factor
vanishing off `tsupport v ⊆ V`, so the integral shrinks to `V`; and the restriction of the
whole-space extension of each coordinate agrees with that coordinate on `V`.

The localised identity is the hypothesis `hLoc` of `differentiated_weakForm` and
`differentiated_weakForm_div`, which nothing discharged before. Discharging it makes the
differentiated-equation identity of Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1, Theorem 2, reachable from the weak formulation itself.

## Main declarations

* `localWeakForm_of_fullBilin`: the localised plain-integral weak identity on `V`.
* `differentiated_weakForm_of_weakSolution`: the differentiated-equation identity, with every
  hypothesis except the weak `ℓ`-derivative of the datum discharged from the weak formulation
  and the interior `H²` estimate.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Localised plain-integral weak identity -/

/-- **Localised weak formulation (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 2).** A weak solution `u ∈ H₀¹(Ω)` of `L u = f`, stated through the bilinear pairing
`Op.fullBilin` over all of `Ω`, satisfies the plain-integral identity `∑_{i,j} ∫_V a_{ij}(∂ᵢu)
∂ⱼv + ∑_i ∫_V b_i (∂ᵢu) v + ∫_V c u v = ∫_V f v` on any measurable `V ⊆ Ω`, for every test
function `v` with `tsupport v ⊆ V`, with each coordinate read as the `V`-restriction of its
whole-space extension by zero. This is the shape the differentiated-equation identity takes as
its hypothesis `hLoc`. -/
theorem localWeakForm_of_fullBilin (Op : FullEllipticOp d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    {V : Set (EuclideanSpace ℝ (Fin d))} (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω)
    (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
    (v : EuclideanSpace ℝ (Fin d) → ℝ) (hvc : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvcs : HasCompactSupport v) (hvV : tsupport v ⊆ V) :
    (∑ i : Fin d, ∑ j : Fin d, ∫ x in V, Op.a x i j
        * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * partialD j v x)
      + (∑ i : Fin d, ∫ x in V, Op.b x i
        * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * v x)
      + (∫ x in V, Op.c x
        * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)) x : ℝ) * v x)
      = ∫ x in V, (restrictL2 (Ω := V) (extendL2 hΩm f) x : ℝ) * v x := by
  classical
  have hv : IsTestFn Ω v := ⟨hvc, hvcs, hvV.trans hVΩ⟩
  have hvmem : hv.testGraph ∈ H01 Ω :=
    (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨v, hv, rfl⟩)
  -- The `V`-restriction of the whole-space extension agrees with the class itself on `V`.
  have hres : ∀ g : L2D Ω,
      (restrictL2 (Ω := V) (extendL2 hΩm g) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict V] (g : EuclideanSpace ℝ (Fin d) → ℝ) := by
    intro g
    filter_upwards [coeFn_restrictL2 (Ω := V) (extendL2 hΩm g),
      ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hVm] with x h1 h2 h3
    rw [h1, h2, Set.indicator_of_mem (hVΩ h3)]
  -- An integrand vanishing off `V` sees the same integral over `Ω` and over `V`.
  have hshrink : ∀ F : EuclideanSpace ℝ (Fin d) → ℝ, (∀ x, x ∉ V → F x = 0) →
      ∫ x in Ω, F x = ∫ x in V, F x := by
    intro F hF
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hF x (fun hc => hx (hVΩ hc))),
      setIntegral_eq_integral_of_forall_compl_eq_zero hF]
  -- The two coordinate representatives of the test-function graph.
  have hgrad : ∀ j : Fin d, (hv.testGraph j.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] partialD j v := by
    intro j
    rw [IsTestFn.testGraph_succ]
    exact (hv.memLp_partialD j).coeFn_toLp
  have hfun : (hv.testGraph 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] v := by
    rw [IsTestFn.testGraph_zero]
    exact hv.mem_lp.coeFn_toLp
  -- Principal block, one entry at a time.
  have hprin : ∀ i j : Fin d,
      ⟪Op.toEllipticCoeff.actL i j ((u : H1amb Ω) i.succ), hv.testGraph j.succ⟫
        = ∫ x in V, Op.a x i j
            * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ)
            * partialD j v x := by
    intro i j
    have hstep : ⟪Op.toEllipticCoeff.actL i j ((u : H1amb Ω) i.succ), hv.testGraph j.succ⟫
        = ∫ x in Ω, Op.a x i j * ((u : H1amb Ω) i.succ x : ℝ) * partialD j v x := by
      rw [Op.toEllipticCoeff.inner_actL_eq i j]
      refine integral_congr_ae ?_
      filter_upwards [hgrad j] with x hx
      rw [hx]
    have hvanish : ∀ x, x ∉ V →
        Op.a x i j * ((u : H1amb Ω) i.succ x : ℝ) * partialD j v x = 0 := by
      intro x hx
      rw [show partialD j v x = 0 from image_eq_zero_of_notMem_tsupport
        (fun hc => hx (hvV (tsupport_partialD_subset j v hc))), mul_zero]
    rw [hstep, hshrink _ hvanish]
    refine integral_congr_ae ?_
    filter_upwards [hres ((u : H1amb Ω) i.succ)] with x hx
    rw [hx]
  -- Transport block.
  have htrans : ∀ i : Fin d,
      ⟪Op.bAct i ((u : H1amb Ω) i.succ), hv.testGraph 0⟫
        = ∫ x in V, Op.b x i
            * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ) * v x := by
    intro i
    have hstep : ⟪Op.bAct i ((u : H1amb Ω) i.succ), hv.testGraph 0⟫
        = ∫ x in Ω, Op.b x i * ((u : H1amb Ω) i.succ x : ℝ) * v x := by
      rw [show ⟪Op.bAct i ((u : H1amb Ω) i.succ), hv.testGraph 0⟫
          = ∫ x in Ω, Op.b x i * ((u : H1amb Ω) i.succ x : ℝ) * (hv.testGraph 0 x : ℝ) from
        inner_mulCoeffL_eq _ _ _ _]
      refine integral_congr_ae ?_
      filter_upwards [hfun] with x hx
      rw [hx]
    have hvanish : ∀ x, x ∉ V →
        Op.b x i * ((u : H1amb Ω) i.succ x : ℝ) * v x = 0 := by
      intro x hx
      rw [show v x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hvV hc)), mul_zero]
    rw [hstep, hshrink _ hvanish]
    refine integral_congr_ae ?_
    filter_upwards [hres ((u : H1amb Ω) i.succ)] with x hx
    rw [hx]
  -- Zeroth-order block.
  have hzero : ⟪Op.cAct ((u : H1amb Ω) 0), hv.testGraph 0⟫
      = ∫ x in V, Op.c x
          * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)) x : ℝ) * v x := by
    have hstep : ⟪Op.cAct ((u : H1amb Ω) 0), hv.testGraph 0⟫
        = ∫ x in Ω, Op.c x * ((u : H1amb Ω) 0 x : ℝ) * v x := by
      rw [show ⟪Op.cAct ((u : H1amb Ω) 0), hv.testGraph 0⟫
          = ∫ x in Ω, Op.c x * ((u : H1amb Ω) 0 x : ℝ) * (hv.testGraph 0 x : ℝ) from
        inner_mulCoeffL_eq _ _ _ _]
      refine integral_congr_ae ?_
      filter_upwards [hfun] with x hx
      rw [hx]
    have hvanish : ∀ x, x ∉ V → Op.c x * ((u : H1amb Ω) 0 x : ℝ) * v x = 0 := by
      intro x hx
      rw [show v x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hvV hc)), mul_zero]
    rw [hstep, hshrink _ hvanish]
    refine integral_congr_ae ?_
    filter_upwards [hres ((u : H1amb Ω) 0)] with x hx
    rw [hx]
  -- The datum side.
  have hdat : (∫ x in Ω, (f x : ℝ) * (hv.testGraph 0 x : ℝ))
      = ∫ x in V, (restrictL2 (Ω := V) (extendL2 hΩm f) x : ℝ) * v x := by
    have hstep : (∫ x in Ω, (f x : ℝ) * (hv.testGraph 0 x : ℝ))
        = ∫ x in Ω, (f x : ℝ) * v x := by
      refine integral_congr_ae ?_
      filter_upwards [hfun] with x hx
      rw [hx]
    have hvanish : ∀ x, x ∉ V → (f x : ℝ) * v x = 0 := by
      intro x hx
      rw [show v x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hvV hc)), mul_zero]
    rw [hstep, hshrink _ hvanish]
    refine integral_congr_ae ?_
    filter_upwards [hres f] with x hx
    rw [hx]
  -- Assemble.
  have hkey := hu ⟨hv.testGraph, hvmem⟩
  rw [FullEllipticOp.fullBilin_apply, EllipticCoeff.bilin_apply,
    FullEllipticOp.lowerBilin_apply] at hkey
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hprin i j)),
    Finset.sum_congr rfl (fun i _ => htrans i), hzero, hdat] at hkey
  linarith [hkey]

/-! ### Differentiated-equation identity from the weak formulation -/

/-- **Differentiated-equation identity for a weak solution (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2).** For a weak solution `u ∈ H₀¹(Ω)` of `L u = f` with
`C²` principal coefficients and `C¹` lower-order coefficients, and any compact `V ⋐ Ω`, the
second weak derivatives of `u` on `V` exist and are bounded by the data, and for every direction
`ℓ` in which the datum has a weak derivative `Df`, the pair `(∂_ℓ∂ᵢu, Df)` satisfies Evans'
equation (34) against every test function supported in `V`.

Every hypothesis of `differentiated_weakForm` other than the weak `ℓ`-derivative of `f` is
discharged here: the second derivatives come from `interior_H2_estimate`, the first
derivatives from `hasWeakDeriv_extendL2_of_mem_H01`, and the localised weak identity from
`localWeakForm_of_fullBilin`. The weak derivative of `f` cannot be dropped, since Evans (26)
assumes `f ∈ H^m(U)` and his datum (36) contains `D^α f`. -/
theorem differentiated_weakForm_of_weakSolution {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsC2Coeff Op.toEllipticCoeff) (ℓ : Fin (n + 1))
    (hb : ∀ i, ContDiff ℝ 1 (fun x => Op.b x i)) (hc : ContDiff ℝ 1 Op.c)
    (Mdb : Fin (n + 1) → ℝ)
    (hbdM : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      |partialD ℓ (fun y => Op.b y i) x| ≤ Mdb i)
    (Mdc : ℝ)
    (hcdM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      |partialD ℓ Op.c x| ≤ Mdc)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (Df : Lp ℝ 2 (volume.restrict V)),
      HasWeakDerivOn V ℓ (restrictL2 (Ω := V) (extendL2 hΩm f)) Df →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ D2 : Fin (n + 1) → Fin (n + 1) → Lp ℝ 2 (volume.restrict V),
        (∀ k i, HasWeakDerivOn V k
            (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) (D2 k i))
        ∧ (∀ k i, ‖D2 k i‖
              + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
              + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
            ≤ C * (‖f‖ + ‖(u : H1amb Ω) 0‖))
        ∧ ∀ φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
            HasCompactSupport φ → tsupport φ ⊆ V →
          (∑ i, ∑ j, ∫ x in V, Op.a x i j * (D2 ℓ i x : ℝ) * partialD j φ x)
          = (∫ x in V, (Df x : ℝ) * φ x)
            - (∑ i, ∫ x in V, (partialD ℓ (fun y => Op.b y i) x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ)
                + Op.b x i * (D2 ℓ i x : ℝ)) * φ x)
            - (∫ x in V, (partialD ℓ Op.c x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)) x : ℝ)
                + Op.c x
                  * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)) x : ℝ)) * φ x)
            + (∑ i, ∑ j, ∫ x in V,
                (partialD j (partialD ℓ (fun y => Op.a y i j)) x
                    * (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) x : ℝ)
                  + partialD ℓ (fun y => Op.a y i j) x * (D2 j i x : ℝ)) * φ x) := by
  classical
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  obtain ⟨C, hC0, hest⟩ :=
    interior_H2_estimate Op hΩm hΩo hA.toIsC1Coeff.toIsLipCoeff hVc hVΩ
  refine ⟨C, hC0, fun u f Df hf_Df hu => ?_⟩
  choose D2 hD2w hD2n using hest u f hu
  refine ⟨D2, hD2w, hD2n, fun φ hφc hφcs hφV => ?_⟩
  exact differentiated_weakForm hVm Op hA ℓ hb hc Mdb hbdM Mdc hcdM
    (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
    (fun i => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)))
    D2 (restrictL2 (Ω := V) (extendL2 hΩm f)) Df
    (fun i => hasWeakDerivOn_of_hasWeakDeriv i (hasWeakDeriv_extendL2_of_mem_H01 hΩm i u.2))
    (fun i => hD2w ℓ i) (fun i j => hD2w j i) hf_Df
    (fun w hwc hwcs hwV => localWeakForm_of_fullBilin Op hΩm hVm hVΩ u f hu w hwc hwcs hwV)
    hφc hφcs hφV

end EllipticPdes.Regularity
