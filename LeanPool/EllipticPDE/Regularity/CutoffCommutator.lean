/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.L2Pairing
public import LeanPool.EllipticPDE.Regularity.CutoffGradFormula


/-!
# Commutator of the bilinear form with a cutoff

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 differentiates the equation
without cutting off, because his interior `H²` theorem asks only `u ∈ H¹(U)`. The interior `H²`
estimate here quantifies its solution over `H₀¹(Ω)`, and `∂_ℓu` has no boundary condition, so
the induction runs on `ξ·∂_ℓu` and pays a commutator.

This file computes it. Each block of `Op.fullBilin` is expanded on the cut-off element, one
entry at a time, and every term either matches the differentiated equation tested against `ξv`
or becomes an `L²` pairing against `v`.

## Principal entry

`∂ᵢ(ξ·∂_ℓu)` is `(∂ᵢξ)(∂_ℓu) + ξ(∂ᵢ∂_ℓu)`, so the entry splits in two.

* The term with `ξ` keeps its derivative on the solution. Writing `ξ∂ⱼv = ∂ⱼ(ξv) - (∂ⱼξ)v` turns
  it into the differentiated equation tested against `ξv`, plus a pairing.
* The term with `∂ᵢξ` keeps its derivative on the test function, and has to be integrated by
  parts. It is admissible because `∂ᵢξ` is supported in `W`, which is
  `EllipticPdes.Regularity.setIntegral_mul_mulTest_partialD`.

Nothing here is specific to the operator: the coefficient enters as a bounded measurable weight
and the second derivative of the solution enters as a weak derivative on `W`. The entries are
supplied as classes with their defining almost-everywhere descriptions, so the caller names its
own and no product is constructed twice.

## Main declarations

* `mul_eq_self_of_eqOn_one`: a cutoff that is one where a weight lives is invisible.
* `setIntegral_principal_entry`: one entry of the principal block, expanded.
* `setIntegral_principal_entry_coeff`: the same at the operator's coefficient, in the shape the
  datum pairs against.
* `setIntegral_lower_entry`: one entry of a block with no derivative on the test function.
* `setIntegral_blocks_eq`: all three blocks, as the shapes the datum names.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Open collar the identifications use -/

/-- **Open collar around the middle cutoff.** There is an open `N` with
`tsupport ξ ⊆ N ⊆ tsupport θ` on which `θ` is identically `1`.

Every identification the induction step makes holds only after a cutoff, and `N` is where the
cutoff is invisible. Running the differentiated equation on `N` rather than on the compact
`tsupport θ` is what lets the inductive hypothesis's own family supply every derivative: the
first derivatives it names agree with the ambient element's gradient coordinates almost
everywhere on `N`, which is enough for both to be weak derivatives of one class there. -/
theorem CutoffTower.exists_isOpen_collar {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (T : CutoffTower Ω V) :
    ∃ N : Set (EuclideanSpace ℝ (Fin d)), IsOpen N ∧ tsupport T.ξ ⊆ N ∧ N ⊆ tsupport T.θ ∧
      Set.EqOn T.θ 1 N := by
  obtain ⟨N, hNo, hξN, hNθ⟩ := mem_nhdsSet_iff_exists.1 T.hθ_one
  refine ⟨N, hNo, hξN, ?_, fun x hx => hNθ hx⟩
  intro x hx
  refine subset_tsupport T.θ ?_
  rw [Function.mem_support, hNθ hx]
  exact one_ne_zero

/-- **Invisibility of a cutoff that is one where the weight lives.** Every identification
the induction step makes holds only after a cutoff, and every weight it pairs against is
supported where that cutoff is identically one, so the cutoff never reaches the conclusion. -/
theorem mul_eq_self_of_eqOn_one {χ : EuclideanSpace ℝ (Fin d) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin d))} (hχ : Set.EqOn χ 1 S)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : tsupport ψ ⊆ S) (x : EuclideanSpace ℝ (Fin d)) :
    χ x * ψ x = ψ x := by
  by_cases hx : x ∈ tsupport ψ
  · rw [hχ (hψ hx)]
    simp
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- **One entry of the principal block of the cut-off element.** With `Uamb` an ambient element
whose `i`-th gradient coordinate is `(∂ᵢξ)·p + ξ·(∂ᵢp)`, the entry
`∫_Ω a·(∂ᵢ(ξp))·∂ⱼv` splits into the differentiated equation's principal term tested against
`ξv`, a pairing coming from `ξ∂ⱼv = ∂ⱼ(ξv) - (∂ⱼξ)v`, and the integration by parts of the term
in which the derivative landed on the cutoff.

`Aip` is the class of `a·p`, `dAip` its weak `j`-derivative on `W`, and `Aig` the class of
`a·∂ᵢp`. Only `dAip` needs the coefficient to be differentiable, and it enters as a hypothesis
rather than as a construction, so this statement is free of every coefficient bundle. -/
theorem setIntegral_principal_entry {Ω W : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W)
    {ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hξW : IsTestFn W ξ)
    (a : EuclideanSpace ℝ (Fin d) → ℝ) {Uamb : H1amb Ω} {p Dgi : L2D W} (i j : Fin d)
    (hgrad : extendL2 hΩm (Uamb i.succ)
      = extendL2 hWm (mulTest (isTestFn_partialD hξW i) p + mulTest hξW Dgi))
    (Aip : L2D W) (hAip : Aip =ᵐ[volume.restrict W] fun x => a x * (p x : ℝ))
    (dAip : L2D W) (hdAip : HasWeakDerivOn W j Aip dAip)
    (Aig : L2D W) (hAig : Aig =ᵐ[volume.restrict W] fun x => a x * (Dgi x : ℝ))
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hvc : ContDiff ℝ (⊤ : ℕ∞) v) :
    (∫ x in Ω, a x * ((Uamb i.succ) x : ℝ) * partialD j v x)
      = (∫ x in W, (Aig x : ℝ) * partialD j (fun y => ξ y * v y) x)
        - (∫ x in W, (Aig x : ℝ) * (partialD j ξ x * v x))
        - ∫ x in W, (partialD j (partialD i ξ) x * (Aip x : ℝ)
            + partialD i ξ x * (dAip x : ℝ)) * v x := by
  -- The entry, moved down to `W` through the gradient formula.
  have e0 : (∫ x in Ω, a x * ((Uamb i.succ) x : ℝ) * partialD j v x)
      = ∫ x in W, a x
          * ((mulTest (isTestFn_partialD hξW i) p + mulTest hξW Dgi) x : ℝ) * partialD j v x := by
    rw [← integral_extendL2_mul_mul hΩm (Uamb i.succ) a (partialD j v), hgrad,
      integral_extendL2_mul_mul hWm _ a (partialD j v)]
  -- The two summands of the gradient, each with its own cutoff.
  have hQ : (fun x => a x
        * ((mulTest (isTestFn_partialD hξW i) p + mulTest hξW Dgi) x : ℝ) * partialD j v x)
      =ᵐ[volume.restrict W] fun x => (Aip x : ℝ) * (partialD i ξ x * partialD j v x)
        + (Aig x : ℝ) * (ξ x * partialD j v x) := by
    filter_upwards [Lp.coeFn_add (mulTest (isTestFn_partialD hξW i) p) (mulTest hξW Dgi),
      mulTest_coeFn (isTestFn_partialD hξW i) p, mulTest_coeFn hξW Dgi, hAip, hAig]
      with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, h4, h5]
    ring
  have e1 : (∫ x in W, a x
        * ((mulTest (isTestFn_partialD hξW i) p + mulTest hξW Dgi) x : ℝ) * partialD j v x)
      = (∫ x in W, (Aip x : ℝ) * (partialD i ξ x * partialD j v x))
        + ∫ x in W, (Aig x : ℝ) * (ξ x * partialD j v x) := by
    rw [integral_congr_ae hQ]
    exact integral_add
      (integrable_mul_testFn Aip ((contDiff_partialD hξW.1 i).mul (contDiff_partialD hvc j))
        (hξW.hasCompactSupport_partialD i).mul_right)
      (integrable_mul_testFn Aig (hξW.1.mul (contDiff_partialD hvc j)) hξW.2.1.mul_right)
  rw [e0, e1, setIntegral_mul_mulTest_partialD (isTestFn_partialD hξW i) hdAip hvc,
    setIntegral_mul_cutoff_partialD_split Aig hξW.1 hξW.2.1 hvc j]
  ring

/-- **One entry of the principal block in the shape the datum pairs against.** The general
entry is instantiated at the operator's coefficient, its weak derivative is supplied by the
`W^{k,∞}` bundle through the Leibniz rule, and the three integrals it returns are split into the
five the datum names.

The first is the differentiated equation's principal term tested against `ξv`, with the second
derivative in the order the gradient of the cut-off derivative produces it. The other four are
pairings, and each is one of the datum's shapes. -/
theorem setIntegral_principal_entry_coeff (Op : FullEllipticOp d)
    {Ω N : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω) (hNm : MeasurableSet N)
    {ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hξN : IsTestFn N ξ) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1)) {Uamb : H1amb Ω} {p : L2D N}
    {D2 : Fin d → L2D N} (i j : Fin d)
    (hgrad : extendL2 hΩm (Uamb i.succ)
      = extendL2 hNm (mulTest (isTestFn_partialD hξN i) p + mulTest hξN (D2 i)))
    (hpD : ∀ m, HasWeakDerivOn N m p (D2 m))
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hvc : ContDiff ℝ (⊤ : ℕ∞) v) :
    (∫ x in Ω, Op.a x i j * ((Uamb i.succ) x : ℝ) * partialD j v x)
      = (∫ x in N, Op.a x i j * (D2 i x : ℝ) * partialD j (fun y => ξ y * v y) x)
        - (∫ x in N, partialD j ξ x * (Op.a x i j * (D2 i x : ℝ)) * v x)
        - (∫ x in N, partialD j (partialD i ξ) x * (Op.a x i j * (p x : ℝ)) * v x)
        - (∫ x in N, partialD i ξ x * (hA.D [j] i j x * (p x : ℝ)) * v x)
        - ∫ x in N, partialD i ξ x * (Op.a x i j * (D2 j x : ℝ)) * v x := by
  classical
  -- The coefficient against the derivative, and its own weak derivative by the Leibniz rule.
  have hAip := Op.toEllipticCoeff.actL_coeFn (Ω := N) i j p
  have hAig := Op.toEllipticCoeff.actL_coeFn (Ω := N) i j (D2 i)
  have hAjd := Op.toEllipticCoeff.actL_coeFn (Ω := N) i j (D2 j)
  have hmul : (mulL2 ((hA.entry i j).measurable_D_singleton j)
        ((hA.entry i j).ae_abs_D_singleton_le j) p : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict N] fun x => hA.D [j] i j x * (p x : ℝ) :=
    mulL2_coeFn ((hA.entry i j).measurable_D_singleton j)
      ((hA.entry i j).ae_abs_D_singleton_le j) p
  have hdag : (mulL2 ((hA.entry i j).measurable_D_singleton j)
        ((hA.entry i j).ae_abs_D_singleton_le j) p + Op.toEllipticCoeff.actL i j (D2 j))
      =ᵐ[volume.restrict N] fun x =>
        hA.D [j] i j x * (p x : ℝ) + Op.a x i j * (D2 j x : ℝ) := by
    filter_upwards [Lp.coeFn_add (mulL2 ((hA.entry i j).measurable_D_singleton j)
        ((hA.entry i j).ae_abs_D_singleton_le j) p) (Op.toEllipticCoeff.actL i j (D2 j)),
      hmul, hAjd] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  have hdAip : HasWeakDerivOn N j (Op.toEllipticCoeff.actL i j p)
      (mulL2 ((hA.entry i j).measurable_D_singleton j)
        ((hA.entry i j).ae_abs_D_singleton_le j) p + Op.toEllipticCoeff.actL i j (D2 j)) :=
    HasWeakDerivOn.mul_isWkInfty_left j (hpD j) (hA.entry i j).measurable_self
      ((hA.entry i j).measurable_D_singleton j) ((hA.entry i j).hasWeakPartial_D j)
      (hA.entry i j).ae_abs_le ((hA.entry i j).ae_abs_D_singleton_le j) _ hAip _ hdag
  rw [setIntegral_principal_entry hΩm hNm hξN (fun x => Op.a x i j) i j hgrad
    (Op.toEllipticCoeff.actL i j p) hAip _ hdAip (Op.toEllipticCoeff.actL i j (D2 i)) hAig hvc]
  -- The three integrals the general entry returns, rewritten as the five the datum names.
  have e1 : (∫ x in N, (Op.toEllipticCoeff.actL i j (D2 i) x : ℝ)
        * partialD j (fun y => ξ y * v y) x)
      = ∫ x in N, Op.a x i j * (D2 i x : ℝ) * partialD j (fun y => ξ y * v y) x := by
    refine integral_congr_ae ?_
    filter_upwards [hAig] with x hx
    rw [hx]
  have e2 : (∫ x in N, (Op.toEllipticCoeff.actL i j (D2 i) x : ℝ) * (partialD j ξ x * v x))
      = ∫ x in N, partialD j ξ x * (Op.a x i j * (D2 i x : ℝ)) * v x := by
    refine integral_congr_ae ?_
    filter_upwards [hAig] with x hx
    rw [hx]
    ring
  -- The last integral is three pairings.
  have hi1 : Integrable (fun x => (Op.toEllipticCoeff.actL i j p x : ℝ)
      * (partialD j (partialD i ξ) x * v x)) (volume.restrict N) :=
    integrable_mul_testFn _ ((contDiff_partialD (contDiff_partialD hξN.1 i) j).mul hvc)
      ((hξN.hasCompactSupport_partialD i).fderiv_apply (𝕜 := ℝ)
        (EuclideanSpace.single j 1)).mul_right
  have hi2 : Integrable (fun x => (mulL2 ((hA.entry i j).measurable_D_singleton j)
        ((hA.entry i j).ae_abs_D_singleton_le j) p x : ℝ) * (partialD i ξ x * v x))
      (volume.restrict N) :=
    integrable_mul_testFn _ ((contDiff_partialD hξN.1 i).mul hvc)
      (hξN.hasCompactSupport_partialD i).mul_right
  have hi3 : Integrable (fun x => (Op.toEllipticCoeff.actL i j (D2 j) x : ℝ)
      * (partialD i ξ x * v x)) (volume.restrict N) :=
    integrable_mul_testFn _ ((contDiff_partialD hξN.1 i).mul hvc)
      (hξN.hasCompactSupport_partialD i).mul_right
  have hi1' : Integrable
      (fun x => partialD j (partialD i ξ) x * (Op.a x i j * (p x : ℝ)) * v x)
      (volume.restrict N) := by
    refine hi1.congr ?_
    filter_upwards [hAip] with x hx
    rw [hx]
    ring
  have hi2' : Integrable
      (fun x => partialD i ξ x * (hA.D [j] i j x * (p x : ℝ)) * v x)
      (volume.restrict N) := by
    refine hi2.congr ?_
    filter_upwards [hmul] with x hx
    rw [hx]
    ring
  have hi3' : Integrable
      (fun x => partialD i ξ x * (Op.a x i j * (D2 j x : ℝ)) * v x) (volume.restrict N) := by
    refine hi3.congr ?_
    filter_upwards [hAjd] with x hx
    rw [hx]
    ring
  have e3 : (∫ x in N, (partialD j (partialD i ξ) x * (Op.toEllipticCoeff.actL i j p x : ℝ)
        + partialD i ξ x * ((mulL2 ((hA.entry i j).measurable_D_singleton j)
            ((hA.entry i j).ae_abs_D_singleton_le j) p
          + Op.toEllipticCoeff.actL i j (D2 j)) x : ℝ)) * v x)
      = (∫ x in N, partialD j (partialD i ξ) x * (Op.a x i j * (p x : ℝ)) * v x)
        + (∫ x in N, partialD i ξ x * (hA.D [j] i j x * (p x : ℝ)) * v x)
        + ∫ x in N, partialD i ξ x * (Op.a x i j * (D2 j x : ℝ)) * v x := by
    have hcong : (fun x => (partialD j (partialD i ξ) x
          * (Op.toEllipticCoeff.actL i j p x : ℝ)
          + partialD i ξ x * ((mulL2 ((hA.entry i j).measurable_D_singleton j)
              ((hA.entry i j).ae_abs_D_singleton_le j) p
            + Op.toEllipticCoeff.actL i j (D2 j)) x : ℝ)) * v x)
        =ᵐ[volume.restrict N] fun x =>
          (partialD j (partialD i ξ) x * (Op.a x i j * (p x : ℝ)) * v x
            + partialD i ξ x * (hA.D [j] i j x * (p x : ℝ)) * v x)
            + partialD i ξ x * (Op.a x i j * (D2 j x : ℝ)) * v x := by
      filter_upwards [hAip, hdag] with x h1 h2
      rw [h1, h2]
      ring
    have hi12 : Integrable
        (fun x => partialD j (partialD i ξ) x * (Op.a x i j * (p x : ℝ)) * v x
          + partialD i ξ x * (hA.D [j] i j x * (p x : ℝ)) * v x)
        (volume.restrict N) := hi1'.add hi2'
    rw [integral_congr_ae hcong, integral_add hi12 hi3', integral_add hi1' hi2']
  rw [e1, e2, e3]
  ring

/-- **One entry of a block with no derivative on the test function.** The transport and
zeroth-order blocks need no integration by parts: the entry is already an `L²` pairing, and
only the gradient formula and the move down to `W` are used. -/
theorem setIntegral_lower_entry {Ω W : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (F : L2D Ω) (G : L2D W)
    (hFG : extendL2 hΩm F = extendL2 hWm G) (a : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x in Ω, a x * (F x : ℝ) * v x) = ∫ x in W, a x * (G x : ℝ) * v x := by
  rw [← integral_extendL2_mul_mul hΩm F a v, hFG, integral_extendL2_mul_mul hWm G a v]

/-- **Three blocks of the bilinear form on the cut-off element.** Summing the principal
entry over both directions and adding the transport and zeroth-order blocks, which need no
integration by parts, gives the whole pairing as eight sums, each of them a shape the datum of
the induction step names.

The first sum is the differentiated equation's principal term tested against `ξv`, with the
second derivative in the order the gradient produces it. Everything else is a pairing against
`v`. -/
theorem setIntegral_blocks_eq (Op : FullEllipticOp d)
    {Ω N : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω) (hNm : MeasurableSet N)
    {ξ : EuclideanSpace ℝ (Fin d) → ℝ} (hξN : IsTestFn N ξ) {k m : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1)) (hbc : IsWkInftyLower Op m)
    {Uamb : H1amb Ω} {p : L2D N} {D2 : Fin d → L2D N}
    (hgrad : ∀ i : Fin d, extendL2 hΩm (Uamb i.succ)
      = extendL2 hNm (mulTest (isTestFn_partialD hξN i) p + mulTest hξN (D2 i)))
    (hU0N : extendL2 hΩm (Uamb 0) = extendL2 hNm (mulTest hξN p))
    (hpD : ∀ i : Fin d, HasWeakDerivOn N i p (D2 i))
    {v : EuclideanSpace ℝ (Fin d) → ℝ} (hvc : ContDiff ℝ (⊤ : ℕ∞) v) :
    (∑ i, ∑ j, ∫ x in Ω, Op.a x i j * ((Uamb i.succ) x : ℝ) * partialD j v x)
        + (∑ i, ∫ x in Ω, Op.b x i * ((Uamb i.succ) x : ℝ) * v x)
        + (∫ x in Ω, Op.c x * ((Uamb 0) x : ℝ) * v x)
      = (∑ i, ∑ j, ∫ x in N, Op.a x i j * (D2 i x : ℝ) * partialD j (fun y => ξ y * v y) x)
        - (∑ i, ∑ j, ∫ x in N, partialD j ξ x * (Op.a x i j * (D2 i x : ℝ)) * v x)
        - (∑ i, ∑ j, ∫ x in N, partialD j (partialD i ξ) x * (Op.a x i j * (p x : ℝ)) * v x)
        - (∑ i, ∑ j, ∫ x in N,
            partialD i ξ x * (hA.D [j] i j x * (p x : ℝ)) * v x)
        - (∑ i, ∑ j, ∫ x in N, partialD i ξ x * (Op.a x i j * (D2 j x : ℝ)) * v x)
        + (∑ i, ∫ x in N, partialD i ξ x * (Op.b x i * (p x : ℝ)) * v x)
        + (∑ i, ∫ x in N, ξ x * (Op.b x i * (D2 i x : ℝ)) * v x)
        + ∫ x in N, ξ x * (Op.c x * (p x : ℝ)) * v x := by
  classical
  -- The transport block, entry by entry.
  have htrans : ∀ i : Fin d, (∫ x in Ω, Op.b x i * ((Uamb i.succ) x : ℝ) * v x)
      = (∫ x in N, partialD i ξ x * (Op.b x i * (p x : ℝ)) * v x)
        + ∫ x in N, ξ x * (Op.b x i * (D2 i x : ℝ)) * v x := by
    intro i
    rw [setIntegral_lower_entry hΩm hNm (Uamb i.succ) _ (hgrad i) (fun x => Op.b x i) v]
    have hi1 : Integrable (fun x => partialD i ξ x * (Op.b x i * (p x : ℝ)) * v x)
        (volume.restrict N) := by
      refine (integrable_mul_testFn (mulL2 (hbc.bReg i).measurable_self
        (hbc.bReg i).ae_abs_le p) ((contDiff_partialD hξN.1 i).mul hvc)
        (hξN.hasCompactSupport_partialD i).mul_right).congr ?_
      filter_upwards [mulL2_coeFn (hbc.bReg i).measurable_self (hbc.bReg i).ae_abs_le p] with x hx
      rw [hx]
      ring
    have hi2 : Integrable (fun x => ξ x * (Op.b x i * (D2 i x : ℝ)) * v x)
        (volume.restrict N) := by
      refine (integrable_mul_testFn (mulL2 (hbc.bReg i).measurable_self
        (hbc.bReg i).ae_abs_le (D2 i)) (hξN.1.mul hvc) hξN.2.1.mul_right).congr ?_
      filter_upwards [mulL2_coeFn (hbc.bReg i).measurable_self (hbc.bReg i).ae_abs_le (D2 i)]
        with x hx
      rw [hx]
      ring
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add (mulTest (isTestFn_partialD hξN i) p) (mulTest hξN (D2 i)),
      mulTest_coeFn (isTestFn_partialD hξN i) p, mulTest_coeFn hξN (D2 i)] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    ring
  -- The zeroth-order block.
  have hzero : (∫ x in Ω, Op.c x * ((Uamb 0) x : ℝ) * v x)
      = ∫ x in N, ξ x * (Op.c x * (p x : ℝ)) * v x := by
    rw [setIntegral_lower_entry hΩm hNm (Uamb 0) _ hU0N Op.c v]
    refine integral_congr_ae ?_
    filter_upwards [mulTest_coeFn hξN p] with x hx
    rw [hx]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      setIntegral_principal_entry_coeff Op hΩm hNm hξN hA (p := p) (D2 := D2) i j
        (hgrad i) hpD hvc)),
    Finset.sum_congr rfl (fun i _ => htrans i), hzero]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring


end EllipticPdes.Regularity
