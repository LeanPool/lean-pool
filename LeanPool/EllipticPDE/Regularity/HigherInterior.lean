/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.WeakFormDense
public import LeanPool.EllipticPDE.Regularity.CutoffCommutator
public import LeanPool.EllipticPDE.Regularity.CollarIdentify
public import LeanPool.EllipticPDE.Regularity.CutoffDatum


/-!
# Higher interior regularity for H₀¹ weak solutions

James Guo, *Partial Differential Equations* (Course Lecture Notes), Theorem VIII.3.2
(*Higher Interior Regularity*, p. 65) gives the weak-coefficient version. The formalization
below treats `H₀¹` weak solutions `u` of `L u = f`, with globally defined coefficients and a
separate globally Lipschitz hypothesis on the principal-coefficient representatives. With
`a_{ij} ∈ W^{k+1,∞}`, `b_i, c ∈ W^{k,∞}` and `f ∈ H^k`, the solution lies in `H^{k+2}_loc`
with

`‖u‖_{H^{k+2}(V)} ≤ C (‖f‖_{H^k(Ω)} + ‖u‖_{L²(Ω)})` for every `V ⋐ Ω`,

the constant depending on the data and the pair `V ⋐ Ω` and on neither `u` nor `f`. Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 (p. 332) is the same statement
with `C^{k+1}` coefficients, which `IsCkCoeff.toIsWkInftyCoeff` shows to be the stronger
hypothesis. The theorem below asks Guo's weak-derivative orders together with the separate
pointwise `IsLipCoeff` bundle for the base case.

## Shape of the induction

`InteriorRegularityAt Op Ω k` packages the conclusion at order `k`, and the theorem is an
induction on `k` over that predicate.

* Order `0` is `interior_H2_estimate` with its `(k, i)`-indexed second derivatives assembled
  into a `HasIteratedWeakDerivOn` family of order `2`.
* The step differentiates the equation once. Where `u` solves `L u = f`, the derivative `∂_l u`
  solves `L (∂_l u) = ∂_l f + R_l`, with `R_l` collecting the terms in which the differentiation
  lands on a coefficient rather than on `u`. Those terms pair one derivative of a coefficient
  against derivatives of `u` of order at most two, so `R_l` sits in `H^{k-1}` once the
  order-`k-1` conclusion is available for `u` itself. Applying the induction hypothesis to `∂_l
  u` on an intermediate `V ⋐ W ⋐ Ω` gives `∂_l u ∈ H^{k+1}(V)`, which is `u ∈ H^{k+2}(V)`.

The differentiated equation is already available as
`EllipticPdes.Regularity.differentiated_weakForm_div`, and the admissibility of the test
function it needs as `interior_cutoffGrad_mem_H01`.

## Main declarations

* `InteriorRegularityAt`: the order-`k` conclusion, as a predicate, so that the induction has
  something to be an induction over.
* `interiorRegularityAt_zero`: the base case.
* `exists_cutoffDeriv_weakForm`: the differentiated equation, as a weak formulation for the
  cutoff derivative, which is what the induction hypothesis consumes.
* `interiorRegularityAt_succ`: the induction step.
* `higher_interior_regularity`: the theorem.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Order-`k` interior conclusion.** For every compact `V ⋐ Ω` there is a constant,
quantified before the solution and the datum, bounding every weak derivative of `u` of order at
most `k + 2` on `V` by `‖f‖_{H^k} + ‖u‖_{L²}`. The datum's `H^k` norm enters through a bound
`M` on its own iterated family, which `IteratedL2Bound.norm_le` shows to dominate `‖f‖`. -/
def InteriorRegularityAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (k : ℕ) : Prop :=
  ∀ {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}, IsCompact V → V ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω k f), IteratedL2Bound hfk M →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ hu : HasIteratedWeakDerivOn V (k + 2)
          (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))),
        IteratedL2Bound hu (C * (M + ‖(u : H1amb Ω) 0‖))

/-- **Base case: order zero is the interior `H²` estimate.** The estimate
`interior_H2_estimate` returns, for each direction pair `(k, i)`, a weak `k`-derivative of
`∂ᵢu` on `V` together with its bound. Assembling those into a `HasIteratedWeakDerivOn` family
of order `2` is a matter of naming: the empty list is `u`, a singleton `[i]` is `∂ᵢu`, a pair
`[k, i]` is the returned `wki`, and longer lists are unconstrained because `D_step` is asked
only of lists shorter than `2`.

The first-order step, which the `H²` estimate does not itself provide, is
`hasWeakDeriv_extendL2_of_mem_H01`: the ambient encoding's coordinate `i.succ` is the weak
`i`-derivative of coordinate `0` on the whole space, and `hasWeakDerivOn_of_hasWeakDeriv`
localises it to `V`.

No constant is spent. The `H²` estimate bounds the sum of the three norms, so each of them is
bounded on its own, and `IteratedL2Bound.norm_le` supplies `‖f‖ ≤ M`. -/
theorem interiorRegularityAt_zero (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff) :
    InteriorRegularityAt Op hΩm 0 := by
  classical
  intro V hVc hVΩ
  obtain ⟨C, hC0, hC⟩ := interior_H2_estimate Op hΩm hΩo hA hVc hVΩ
  refine ⟨C, hC0, fun u f M hfk hM hu => ?_⟩
  choose W hW hWb using hC u f hu
  -- The family: the empty list is `u`, a singleton is a first derivative, a pair is the
  -- second derivative the `H²` estimate returned. Longer lists are never asked about.
  refine ⟨⟨fun α =>
      match α with
      | [] => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))
      | [i] => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))
      | [k, i] => W k i
      | _ => 0, rfl, ?_⟩, ?_⟩
  · rintro m (_ | ⟨i, _ | ⟨j, rest⟩⟩) hα
    · exact hasWeakDerivOn_of_hasWeakDeriv m (hasWeakDeriv_extendL2_of_mem_H01 hΩm m u.2)
    · exact hW m i
    · simp at hα
  -- Each of the three norms is dominated by the sum the `H²` estimate bounds.
  · have hfM : ‖f‖ ≤ M := hM.norm_le
    have hshift : C * (‖f‖ + ‖(u : H1amb Ω) 0‖) ≤ C * (M + ‖(u : H1amb Ω) 0‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    rintro (_ | ⟨i, _ | ⟨j, rest⟩⟩) hα
    · refine le_trans ?_ hshift
      have h := hWb 0 0
      have h1 := norm_nonneg (W 0 0)
      have h2 := norm_nonneg (restrictL2 (Ω := V)
        (extendL2 hΩm ((u : H1amb Ω) (0 : Fin (n + 1)).succ)))
      linarith
    · refine le_trans ?_ hshift
      have h := hWb 0 i
      have h1 := norm_nonneg (W 0 i)
      have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
      linarith
    · rcases rest with _ | ⟨p, rest'⟩
      · refine le_trans ?_ hshift
        have h := hWb i j
        have h1 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) j.succ)))
        have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
        linarith
      · simp at hα

private theorem cutoff_mixed_weakDeriv_comm {N : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hNm : MeasurableSet N) {k : ℕ} {g : L2D N}
    (HuN : HasIteratedWeakDerivOn N (k + 1 + 1) g)
    {ϑ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hϑ : IsTestFn N ϑ)
    (ℓ : Fin (n + 1)) : ∀ i : Fin (n + 1),
      (fun x => ϑ x * (HuN.D [i, ℓ] x : ℝ))
        =ᵐ[volume.restrict N] fun x => ϑ x * (HuN.D [ℓ, i] x : ℝ) := by
  intro i
  have h := mulTest_mixed_weakDeriv_comm hNm hϑ
    (HuN.D_step i [] (Nat.succ_pos _)) (HuN.D_step ℓ [] (Nat.succ_pos _))
    (HuN.D_step ℓ [i] (Nat.succ_lt_succ (Nat.succ_pos k)))
    (HuN.D_step i [ℓ] (Nat.succ_lt_succ (Nat.succ_pos k)))
  filter_upwards [mulTest_coeFn hϑ (HuN.D [ℓ, i]), mulTest_coeFn hϑ (HuN.D [i, ℓ])]
    with x h1 h2
  rw [← h2, ← h, h1]

private theorem cutoffDatumPairing_eq_blocks {N : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hNm : MeasurableSet N) {k : ℕ} (Op : FullEllipticOp (n + 1))
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    {ξ ϑ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hξ : IsTestFn N ξ) (hϑ : IsTestFn N ϑ)
    (hϑ_eqOn : Set.EqOn ϑ 1 (tsupport ξ)) {uN fN Df : L2D N}
    (HuN : HasIteratedWeakDerivOn N (k + 2) uN) (ℓ : Fin (n + 1))
    (hfDf : HasWeakDerivOn N ℓ fN Df)
    (hLoc : ∀ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
      HasCompactSupport v → tsupport v ⊆ N →
      (∑ i, ∑ j, ∫ x in N, Op.a x i j * (HuN.D [i] x : ℝ) * partialD j v x)
        + (∑ i, ∫ x in N, Op.b x i * (HuN.D [i] x : ℝ) * v x)
        + (∫ x in N, Op.c x * (HuN.D [] x : ℝ) * v x)
        = ∫ x in N, (fN x : ℝ) * v x)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hvc : ContDiff ℝ (⊤ : ℕ∞) v) :
    (∑ i, ∑ j, ∫ x in N, Op.a x i j * (HuN.D [i, ℓ] x : ℝ) * partialD j (fun y => ξ y * v y) x)
        - (∑ i, ∑ j, ∫ x in N, partialD j ξ x * (Op.a x i j * (HuN.D [i, ℓ] x : ℝ)) * v x)
        - (∑ i, ∑ j, ∫ x in N, partialD j (partialD i ξ) x * (Op.a x i j * (HuN.D [ℓ] x : ℝ)) * v x)
        - (∑ i, ∑ j, ∫ x in N,
            partialD i ξ x * (hA.D [j] i j x * (HuN.D [ℓ] x : ℝ)) * v x)
        - (∑ i, ∑ j, ∫ x in N, partialD i ξ x * (Op.a x i j * (HuN.D [j, ℓ] x : ℝ)) * v x)
        + (∑ i, ∫ x in N, partialD i ξ x * (Op.b x i * (HuN.D [ℓ] x : ℝ)) * v x)
        + (∑ i, ∫ x in N, ξ x * (Op.b x i * (HuN.D [i, ℓ] x : ℝ)) * v x)
        + ∫ x in N, ξ x * (Op.c x * (HuN.D [ℓ] x : ℝ)) * v x = cutoffDatumPairing Op hA hbc ξ ℓ uN
          Df HuN v := by
  classical
  dsimp only [cutoffDatumPairing]
  -- The mixed second derivative, swapped into the order the equation names.
  have hsymm := cutoff_mixed_weakDeriv_comm hNm HuN hϑ ℓ
  have hψ : ∀ j : Fin (n + 1), ∀ x, ϑ x * partialD j (fun y => ξ y * v y) x
      = partialD j (fun y => ξ y * v y) x := fun j =>
    mul_eq_self_of_eqOn_one hϑ_eqOn
      ((tsupport_partialD_subset j _).trans tsupport_mul_subset_left)
  conv_lhs =>
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      setIntegral_weight_mul_congr_of_cutoff_ae (hsymm i) (fun x => Op.a x i j) (hψ j)))]
  have hdiffeq := differentiated_weakForm_wkInfty Op hA hbc ℓ (HuN.D [])
    (fun i => HuN.D [i]) (fun m i => HuN.D [m, i])
    fN
    Df
    (fun i => HuN.D_step ℓ [i] (Nat.succ_lt_succ (Nat.succ_pos k)))
    (fun i j => HuN.D_step j [i] (Nat.succ_lt_succ (Nat.succ_pos k)))
    (HuN.D_step ℓ [] (Nat.succ_pos _)) hfDf hLoc
    (hξ.1.mul hvc) hξ.2.1.mul_right (tsupport_mul_subset_left.trans hξ.2.2)
  conv_lhs => rw [hdiffeq]
  rw [show (∫ x in N, (Df x : ℝ) * (ξ x * v x))
        = ∫ x in N, ξ x * ((1 : ℝ)
            * (Df x : ℝ)) * v x from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)]
  rw [Finset.sum_congr rfl (fun i _ =>
      setIntegral_add_weight_mul_cutoff ((hbc.bReg i).measurable_D_singleton ℓ)
        ((hbc.bReg i).ae_abs_D_singleton_le ℓ) (hbc.bReg i).measurable_self
        (hbc.bReg i).ae_abs_le (HuN.D [i]) (HuN.D [ℓ, i]) hξ.1 hξ.2.1 hvc)]
  rw [setIntegral_add_weight_mul_cutoff (hbc.cReg.measurable_D_singleton ℓ)
      (hbc.cReg.ae_abs_D_singleton_le ℓ) hbc.cReg.measurable_self hbc.cReg.ae_abs_le
      (HuN.D []) (HuN.D [ℓ]) hξ.1 hξ.2.1 hvc]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      setIntegral_add_weight_mul_cutoff (hA.D_meas i j [j, ℓ] (Nat.le_add_left 2 k))
        (hA.ess_bdd i j [j, ℓ] (Nat.le_add_left 2 k))
        (hA.D_meas i j [ℓ] (Nat.le_add_left 1 (k + 1)))
        (hA.ess_bdd i j [ℓ] (Nat.le_add_left 1 (k + 1))) (HuN.D [i]) (HuN.D [j, i])
        hξ.1 hξ.2.1 hvc))]
  simp only [HuN.D_nil, Finset.sum_add_distrib]
  ring

private theorem cutoff_derivative_weakForm (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (T : CutoffTower Ω V)
    (N : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) (hξNt : IsTestFn N T.ξ)
    (ϑ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hϑ : IsTestFn N ϑ)
    (hϑ_eqOn : Set.EqOn ϑ 1 (tsupport T.ξ)) (u : H01 Ω) (f : L2D Ω)
    (hfk : HasIteratedWeakDerivOn Ω (k + 1) f)
    (hu : ∀ w : H01 Ω, Op.fullBilin Ω u w =
      ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) (ℓ : Fin (n + 1))
    (HuN : HasIteratedWeakDerivOn N (k + 2)
      (restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) 0))))
    (hDu : ∀ i, HuN.D [i] = restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) i.succ)))
    (Uamb : H1amb Ω) (hUmem : Uamb ∈ H01 Ω)
    (hU0 : Uamb 0 = mulTest T.hξ ((u : H1amb Ω) ℓ.succ))
    (hgrad : ∀ i, extendL2 hΩm (Uamb i.succ) = extendL2 hNm
      (mulTest (isTestFn_partialD hξNt i)
          (restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)))
        + mulTest hξNt (HuN.D [i, ℓ]))) (F : L2D Ω)
    (hFpair : ∀ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
      HasCompactSupport v → (∫ x in Ω, (F x : ℝ) * v x) =
        cutoffDatumPairing Op hA hbc T.ξ ℓ
          (restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) 0)))
          (restrictL2 (Ω := N) (extendL2 hΩm (hfk.D [ℓ]))) HuN v) (w : H01 Ω) :
    Op.fullBilin Ω ⟨Uamb, hUmem⟩ w = ∫ x in Ω, (F x : ℝ) * ((w : H1amb Ω) 0 x : ℝ) := by
  classical
  refine weakForm_of_testFn Op ⟨Uamb, hUmem⟩ F (fun v hv => ?_) w
  have hgrad' : ∀ i : Fin (n + 1), extendL2 hΩm (Uamb i.succ)
      = extendL2 hNm (mulTest (isTestFn_partialD hξNt i) (HuN.D [ℓ])
        + mulTest hξNt (HuN.D [i, ℓ])) := by
    intro i
    rw [hDu ℓ]
    exact hgrad i
  have hU0N : extendL2 hΩm (Uamb 0) = extendL2 hNm (mulTest hξNt (HuN.D [ℓ])) := by
    as_aux_lemma =>
      rw [hU0, hDu ℓ]
      exact extendL2_mulTest_eq hΩm hNm hNΩ T.hξ hξNt ((u : H1amb Ω) ℓ.succ)
  have hD2 : ∀ i : Fin (n + 1), HasWeakDerivOn N i (HuN.D [ℓ]) (HuN.D [i, ℓ]) :=
    fun i => HuN.D_step i [ℓ] (Nat.succ_lt_succ (Nat.succ_pos k))
  rw [fullBilin_testGraph_eq Op ⟨Uamb, hUmem⟩ hv,
    setIntegral_blocks_eq Op hΩm hNm hξNt hA hbc (p := HuN.D [ℓ])
      (D2 := fun i => HuN.D [i, ℓ]) hgrad' hU0N hD2 hv.1,
    hFpair v hv.1 hv.2.1]
  have hfDf : HasWeakDerivOn N ℓ (restrictL2 (Ω := N) (extendL2 hΩm f))
      (restrictL2 (Ω := N) (extendL2 hΩm (hfk.D [ℓ]))) := by
    have h := hfk.D_step ℓ [] (Nat.succ_pos k)
    rw [hfk.D_nil] at h
    exact h.restrict hΩm hNm hNΩ
  have hLoc : ∀ v' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v' →
      HasCompactSupport v' → tsupport v' ⊆ N →
      (∑ i, ∑ j, ∫ x in N, Op.a x i j * (HuN.D [i] x : ℝ) * partialD j v' x)
        + (∑ i, ∫ x in N, Op.b x i * (HuN.D [i] x : ℝ) * v' x)
        + (∫ x in N, Op.c x * (HuN.D [] x : ℝ) * v' x)
        = ∫ x in N, (restrictL2 (Ω := N) (extendL2 hΩm f) x : ℝ) * v' x := by
    intro v' h1 h2 h3
    simp only [hDu, HuN.D_nil]
    exact localWeakForm_of_fullBilin Op hΩm hNm hNΩ u f hu v' h1 h2 h3
  exact cutoffDatumPairing_eq_blocks hNm Op hA hbc hξNt hϑ hϑ_eqOn HuN ℓ hfDf hLoc hv.1

private theorem cutoffDatum_bound {KD C₁ Cξ M uNorm : ℝ}
    (hKD : 0 ≤ KD) (hC₁ : 0 ≤ C₁) (hCξ : 0 ≤ Cξ) (hM : 0 ≤ M) (hu : 0 ≤ uNorm) :
    KD * (C₁ * (M + uNorm) + M) ≤ (KD * (C₁ + 1) + Cξ * C₁) * (M + uNorm) := by
  have h1 : C₁ * (M + uNorm) + M ≤ (C₁ + 1) * (M + uNorm) := by
    linarith only [hu]
  calc KD * (C₁ * (M + uNorm) + M) ≤ KD * ((C₁ + 1) * (M + uNorm)) :=
        mul_le_mul_of_nonneg_left h1 hKD
    _ = KD * (C₁ + 1) * (M + uNorm) := by ring
    _ ≤ (KD * (C₁ + 1) + Cξ * C₁) * (M + uNorm) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hCξ hC₁))
          (add_nonneg hM hu)

/-- **Differentiated equation as a weak formulation for a cutoff derivative.** For a weak
solution `u` of `L u = f` and each direction `ℓ`, there is an element `U ∈ H₀¹(Ω)` agreeing with
`∂_ℓ u` on `V`, a datum `F ∈ L²(Ω)` with `k` weak derivatives, and a weak formulation `B[U, w] =
⟪F, w⟫` for every `w ∈ H₀¹(Ω)`, with both `‖U‖` and the `H^k` bound on `F` controlled by the
data.

This is Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2, step 3 in the
shape the induction consumes, and it is where the analytic content of the step sits.

`U` is `ξ · ∂_ℓ u` for the middle cutoff of a tower for `V ⋐ Ω`, which
`EllipticPdes.Regularity.interior_cutoffGrad_mem_H01` places in `H₀¹(Ω)` and
`EllipticPdes.Regularity.restrictL2_extendL2_mulTest_xi` makes invisible on `V`. `F` collects
`∂_ℓ f`, the terms of `EllipticPdes.Regularity.differentiated_weakForm_wkInfty` in which the
differentiation lands on a coefficient, and the commutator with `ξ`. Each of those is a
`W^{k,∞}` weight against a derivative of `u` of order at most two, so
`EllipticPdes.Regularity.exists_iteratedWeakDeriv_mul` and
`EllipticPdes.Regularity.HasIteratedWeakDerivOn.sum` assemble the family and its bound, and
`EllipticPdes.Regularity.weakForm_of_testFn` extends the identity from test functions to
`H₀¹(Ω)`.

## Order-`k` conclusion as a hypothesis

`F` pairs second derivatives of `u` against first derivatives of the coefficients, so `F ∈ H^k`
asks for `u ∈ H^{k+2}` on a neighbourhood of `tsupport ξ`, which is the order-`k` conclusion at
that compact set. Evans reaches for it at the same point: the datum (36) of §6.3.1, Theorem 2
contains `D²u`, and its `H^k` bound is read off the inductive hypothesis rather than off the
solution's membership of `H₀¹(Ω)`. Passing `hk` here rather than deriving it is what keeps the
step an induction. -/
theorem exists_cutoffDeriv_weakForm (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    (hk : InteriorRegularityAt Op hΩm k)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω (k + 1) f), IteratedL2Bound hfk M →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ ℓ : Fin (n + 1), ∃ (U : H01 Ω) (F : L2D Ω) (hFk : HasIteratedWeakDerivOn Ω k F),
        restrictL2 (Ω := V) (extendL2 hΩm ((U : H1amb Ω) 0))
            = restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ))
          ∧ (∀ w : H01 Ω, Op.fullBilin Ω U w
              = ∫ x in Ω, (F x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
          ∧ IteratedL2Bound hFk (C * (M + ‖(u : H1amb Ω) 0‖))
          ∧ ‖(U : H1amb Ω) 0‖ ≤ C * (M + ‖(u : H1amb Ω) 0‖) := by
  classical
  -- The cutoff tower for `V ⋐ Ω`, and an open collar around its middle cutoff.
  obtain ⟨T⟩ : Nonempty (CutoffTower Ω V) :=
    ⟨cutoffTowerOfIsCompactSubsetIsOpen hVc hΩo hVΩ⟩
  let collar := T.exists_isOpen_collar
  let N := collar.choose
  have hNo := collar.choose_spec.1
  have hξN := collar.choose_spec.2.1
  have hNW := collar.choose_spec.2.2.1
  have hθN := collar.choose_spec.2.2.2
  have hWm : MeasurableSet (tsupport T.θ) := T.hθ.2.1.isClosed.measurableSet
  have hWΩ : tsupport T.θ ⊆ Ω := T.hθ.2.2
  have hNm : MeasurableSet N := hNo.measurableSet
  have hNΩ : N ⊆ Ω := hNW.trans hWΩ
  have hξNt : IsTestFn N T.ξ := ⟨T.hξ.1, T.hξ.2.1, hξN⟩
  have hθWt : IsTestFn (tsupport T.θ) T.θ := ⟨T.hθ.1, T.hθ.2.1, subset_rfl⟩
  -- A fourth cutoff, identically one near the middle cutoff and supported in the collar. The
  -- symmetry of the mixed second derivatives is only available after a cutoff, and this is the
  -- one that is invisible against everything the datum pairs with.
  let innerCutoff := exists_isTestFn_one_nhdsSet_of_isCompact T.hξ.2.1 hNo hξN
  let ϑ := innerCutoff.choose
  have hϑ := innerCutoff.choose_spec.1
  have hϑ_one := innerCutoff.choose_spec.2.1
  have _hϑ_Icc := innerCutoff.choose_spec.2.2
  have hϑ_eqOn : Set.EqOn ϑ 1 (tsupport T.ξ) := fun x hx => hϑ_one.self_of_nhdsSet x hx
  -- The datum, and the inductive hypothesis at the outer support of the tower.
  let datumEstimate := exists_cutoffDatum Op hNm hNΩ hA hbc hξNt
  let KD := datumEstimate.choose
  have hKD0 := datumEstimate.choose_spec.1
  have hDat := datumEstimate.choose_spec.2
  let interiorEstimate := hk T.hθ.2.1 hWΩ
  let C₁ := interiorEstimate.choose
  have hC₁0 := interiorEstimate.choose_spec.1
  have hIH := interiorEstimate.choose_spec.2
  let cutoffBound := exists_abs_bound hξNt
  let Cξ := cutoffBound.choose
  have hCξ := cutoffBound.choose_spec
  have hCξ0 : (0 : ℝ) ≤ Cξ := le_trans (abs_nonneg (T.ξ 0)) (hCξ 0)
  refine ⟨KD * (C₁ + 1) + Cξ * C₁,
    add_nonneg (mul_nonneg hKD0 (add_nonneg hC₁0 zero_le_one)) (mul_nonneg hCξ0 hC₁0),
    fun u f M hfk hM hu ℓ => ?_⟩
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg f) hM.norm_le
  have hu00 : (0 : ℝ) ≤ ‖(u : H1amb Ω) 0‖ := norm_nonneg _
  -- The solution's derivatives to order `k + 2` on the outer support, then on the collar.
  let lowerDatum : HasIteratedWeakDerivOn Ω k f := hfk.mono (Nat.le_succ k)
  have lowerDatum_bound : IteratedL2Bound lowerDatum M :=
    fun α hα => hM α (hα.trans (Nat.le_succ k))
  let interiorDerivatives := hIH u f M lowerDatum lowerDatum_bound hu
  let HuW := interiorDerivatives.choose
  have hHuW := interiorDerivatives.choose_spec
  let collarDerivatives := exists_collarFamily hΩm hWm hNm hNW hθWt hθN
    (fun i => hasWeakDeriv_extendL2_of_mem_H01 hΩm i u.2) HuW hHuW
  let HuN := collarDerivatives.choose
  have hHuNbd := collarDerivatives.choose_spec.1
  have hDu := collarDerivatives.choose_spec.2
  -- The cut-off derivative, and the closed form of its gradient.
  let cutoffGradient := interior_cutoffGrad_mem_H01 Op hΩm hA1 T u f hu ℓ
  let Uamb := cutoffGradient.choose
  have hUmem := cutoffGradient.choose_spec.1
  have hU0 := cutoffGradient.choose_spec.2.1
  have hUgrad := cutoffGradient.choose_spec.2.2
  have hDgℓ : ∀ i : Fin (n + 1),
      HasWeakDerivOn N i (restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)))
        (HuN.D [i, ℓ]) := by
    intro i
    have h := HuN.D_step i [ℓ] (Nat.succ_lt_succ (Nat.succ_pos k))
    rwa [hDu ℓ] at h
  have hgrad : ∀ i : Fin (n + 1), extendL2 hΩm (Uamb i.succ)
      = extendL2 hNm (mulTest (isTestFn_partialD hξNt i)
          (restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)))
        + mulTest hξNt (HuN.D [i, ℓ])) :=
    fun i => extendL2_cutoffGrad_eq hΩm hNm hNΩ T.hξ hξNt ((u : H1amb Ω) ℓ.succ) hUgrad hDgℓ i
  -- The datum's own derivative, cut down to the collar.
  let restrictedDatum := exists_restrictFamily hΩm hNm hNΩ (hfk.deriv ℓ) (hM.deriv ℓ)
  let HDfN := restrictedDatum.choose
  have hDfNbd := restrictedDatum.choose_spec
  -- One bound serving the solution's derivatives and the datum's alike.
  have hMu : (0 : ℝ) ≤ M + ‖(u : H1amb Ω) 0‖ := add_nonneg hM0 hu00
  have hC₁Mu : (0 : ℝ) ≤ C₁ * (M + ‖(u : H1amb Ω) 0‖) := mul_nonneg hC₁0 hMu
  have hle1 : C₁ * (M + ‖(u : H1amb Ω) 0‖) ≤ C₁ * (M + ‖(u : H1amb Ω) 0‖) + M :=
    le_add_of_nonneg_right hM0
  have hle2 : M ≤ C₁ * (M + ‖(u : H1amb Ω) 0‖) + M := le_add_of_nonneg_left hC₁Mu
  let differentiatedDatum := hDat ℓ _ _ HuN HDfN
    (C₁ * (M + ‖(u : H1amb Ω) 0‖) + M) (hHuNbd.mono_const hle1) (hDfNbd.mono_const hle2)
  let F := differentiatedDatum.choose
  let HF := differentiatedDatum.choose_spec.choose
  have hFbd := differentiatedDatum.choose_spec.choose_spec.1
  have hFpair := differentiatedDatum.choose_spec.choose_spec.2
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  have hDℓnorm : ‖HuN.D [ℓ]‖ ≤ C₁ * (M + ‖(u : H1amb Ω) 0‖) :=
    hHuNbd [ℓ] (Nat.succ_le_succ (Nat.zero_le _))
  refine ⟨⟨Uamb, hUmem⟩, F, HF, ?_, ?_, ?_, ?_⟩
  · as_aux_lemma =>
      -- The cutoff is invisible on the base set, so nothing is lost there.
      change restrictL2 (Ω := V) (extendL2 hΩm (Uamb 0)) = _
      rw [hU0]
      exact restrictL2_extendL2_mulTest_xi hΩm hVm hVΩ T ((u : H1amb Ω) ℓ.succ)
  · as_aux_lemma =>
      exact cutoff_derivative_weakForm Op hΩm hA hbc T N hNm hNΩ hξNt ϑ hϑ hϑ_eqOn
        u f hfk hu ℓ HuN hDu Uamb hUmem hU0 hgrad F hFpair
  · exact hFbd.mono_const (cutoffDatum_bound hKD0 hC₁0 hCξ0 hM0 hu00)
  · as_aux_lemma =>
      -- The cut-off derivative's norm, read on the collar where the cutoff lives.
      change ‖Uamb 0‖ ≤ _
      rw [hU0]
      have hag : (mulTest T.hξ ((u : H1amb Ω) ℓ.succ) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
          =ᵐ[volume.restrict Ω] fun x => T.ξ x
            * ((restrictL2 (Ω := Ω) (extendL2 hNm (HuN.D [ℓ]))) x : ℝ) := by
        have hres : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))), x ∈ N →
            (HuN.D [ℓ] x : ℝ) = (extendL2 hΩm ((u : H1amb Ω) ℓ.succ) x : ℝ) := by
          rw [hDu ℓ]
          exact (ae_restrict_iff' hNm).mp
            (coeFn_restrictL2 (Ω := N) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ)))
        filter_upwards [mulTest_coeFn T.hξ ((u : H1amb Ω) ℓ.succ),
          coeFn_restrictL2 (Ω := Ω) (extendL2 hNm (HuN.D [ℓ])),
          ae_restrict_of_ae (coeFn_extendL2 hNm (HuN.D [ℓ])),
          ae_restrict_of_ae (coeFn_extendL2 hΩm ((u : H1amb Ω) ℓ.succ)),
          ae_restrict_of_ae hres, ae_restrict_mem hΩm] with x h1 h2 h3 h4 h5 h6
        rw [h1, h2, h3]
        by_cases hxN : x ∈ N
        · rw [Set.indicator_of_mem hxN, h5 hxN, h4, Set.indicator_of_mem h6]
        · rw [Set.indicator_of_notMem hxN, mul_zero,
            show T.ξ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hxN (hξN hc)),
            zero_mul]
      have hstep : ‖restrictL2 (Ω := Ω) (extendL2 hNm (HuN.D [ℓ]))‖ ≤ ‖HuN.D [ℓ]‖ :=
        le_trans (norm_restrictL2_le _) (le_of_eq (norm_extendL2 hNm (HuN.D [ℓ])))
      calc ‖mulTest T.hξ ((u : H1amb Ω) ℓ.succ)‖
          ≤ Cξ * ‖restrictL2 (Ω := Ω) (extendL2 hNm (HuN.D [ℓ]))‖ :=
            norm_le_of_ae_mul T.hξ.continuous.measurable (Filter.Eventually.of_forall hCξ) hag
        _ ≤ Cξ * ‖HuN.D [ℓ]‖ := mul_le_mul_of_nonneg_left hstep hCξ0
        _ ≤ Cξ * (C₁ * (M + ‖(u : H1amb Ω) 0‖)) := mul_le_mul_of_nonneg_left hDℓnorm hCξ0
        _ = Cξ * C₁ * (M + ‖(u : H1amb Ω) 0‖) := by ring
        _ ≤ (KD * (C₁ + 1) + Cξ * C₁) * (M + ‖(u : H1amb Ω) 0‖) :=
            mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left (mul_nonneg hKD0 (add_nonneg hC₁0 zero_le_one))) hMu

/-- **Induction step.** Differentiating the equation once raises the order-`k` conclusion to
order `k + 1`, under one more order of regularity on every coefficient.

`∂_ℓ u` lies outside `H₀¹(Ω)`: it is a first derivative of an `H₀¹` function and lies only in
`H¹_loc`, so `InteriorRegularityAt`, which quantifies over `H01 Ω`, cannot be applied to it.
`exists_cutoffDeriv_weakForm` supplies the cutoff that can be, together with its datum, and
this step is what remains once that is in hand.

The induction hypothesis returns `k + 2` weak derivatives of the cutoff derivative on `V`,
which `HasIteratedWeakDerivOn.congr` reads as `k + 2` weak derivatives of `∂_ℓ u` itself,
the cutoff being `1` there. Reassembling over `ℓ` through `HasIteratedWeakDerivOn.ofDeriv`
gives `u ∈ H^{k + 3}(V)`.

The constant is `2 C₁ C₀ + 1`, with `C₀` from the datum and `C₁` from the induction
hypothesis. The two summands of `C₀ (M + ‖u‖) + ‖U‖` are each at most `C₀ (M + ‖u‖)`, which
is where the factor of two comes from, and the `+ 1` covers `‖u‖` itself, which the order-zero
entry of the assembled family needs and which no derivative bound supplies. -/
theorem interiorRegularityAt_succ (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2))
    (hbc : IsWkInftyLower Op (k + 1)) (hk : InteriorRegularityAt Op hΩm k) :
    InteriorRegularityAt Op hΩm (k + 1) := by
  classical
  intro V hVc hVΩ
  obtain ⟨C₀, hC₀0, hdat⟩ := exists_cutoffDeriv_weakForm Op hΩm hΩo hA1 hA hbc hk hVc hVΩ
  obtain ⟨C₁, hC₁0, hIH⟩ := hk hVc hVΩ
  refine ⟨2 * C₁ * C₀ + 1, by nlinarith [mul_nonneg hC₁0 hC₀0], fun u f M hfk hM hu => ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM.norm_le
  have hu00 : (0 : ℝ) ≤ ‖(u : H1amb Ω) 0‖ := norm_nonneg _
  -- Each first derivative of `u` has `k + 2` weak derivatives on `V`, read off the induction
  -- hypothesis applied to the cutoff derivative and transported along `ξ ≡ 1`.
  have hstep : ∀ ℓ : Fin (n + 1), ∃ H : HasIteratedWeakDerivOn V (k + 2)
      (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) ℓ.succ))),
      IteratedL2Bound H ((2 * C₁ * C₀ + 1) * (M + ‖(u : H1amb Ω) 0‖)) := by
    intro ℓ
    obtain ⟨U, F, hFk, hres, hUweak, hFbd, hU0⟩ := hdat u f M hfk hM hu ℓ
    obtain ⟨HU, hHU⟩ := hIH U F (C₀ * (M + ‖(u : H1amb Ω) 0‖)) hFk hFbd hUweak
    exact ⟨HU.congr hres, hHU.congr.mono_const (by nlinarith)⟩
  choose H hH using hstep
  refine ⟨HasIteratedWeakDerivOn.ofDeriv
    (fun ℓ => hasWeakDerivOn_of_hasWeakDeriv ℓ
      (hasWeakDeriv_extendL2_of_mem_H01 hΩm ℓ u.2)) H, IteratedL2Bound.ofDeriv ?_ hH⟩
  refine le_trans (norm_restrictL2_le _) ?_
  rw [norm_extendL2]
  have hprod : (0 : ℝ) ≤ 2 * C₁ * C₀ * (M + ‖(u : H1amb Ω) 0‖) :=
    mul_nonneg (mul_nonneg (by linarith) hC₀0) (by linarith)
  nlinarith [hprod]

/-- **Higher interior regularity (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1, Theorem 2, p. 332; a variant of James Guo, *Partial Differential Equations*
(Course Lecture Notes), Theorem VIII.3.2, p. 65).** Evans states the result for
`C^{m+1}` coefficients; the weak
coefficient derivative hypotheses follow Guo's statement. This formalization additionally
requires the specified principal-coefficient representatives to be globally Lipschitz for the
base case, and quantifies over `H₀¹` weak solutions. The pointwise Lipschitz hypothesis is
retained separately from the weak-derivative bundles.

With `W^{k+1,∞}` principal coefficients, `W^{k,∞}` lower-order coefficients and an `H^k` datum,
weak derivatives of every order up to `k + 2` exist on each compact `V ⋐ Ω`. Their L² bounds
use a constant quantified before the solution, datum and datum bound.

At `k = 0`, `interiorRegularityAt_zero` uses the pointwise `IsLipCoeff` hypothesis alone.
The step to order `k + 1` differentiates the equation once: its datum pairs second derivatives
of each `a_{ij}` and first derivatives of `b_i, c` against derivatives of `u` of order at most
two, so an `H^k` datum asks `a_{ij} ∈ W^{k+2,∞}` and `b_i, c ∈ W^{k+1,∞}`
(`exists_cutoffDatum`), and the induction hypothesis at order `k` asks no more. -/
theorem higher_interior_regularity (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsLipCoeff Op.toEllipticCoeff) (k : ℕ)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1))
    (hbc : IsWkInftyLower Op k) :
    InteriorRegularityAt Op hΩm k := by
  induction k with
  | zero => exact interiorRegularityAt_zero Op hΩm hΩo hA1
  | succ j ih =>
    exact interiorRegularityAt_succ (k := j) Op hΩm hΩo hA1 hA hbc
      (ih (hA.mono (by omega)) (hbc.mono (by omega)))

end EllipticPdes.Regularity
