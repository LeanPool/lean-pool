/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Witt cancellation: the reduction to the hyperbolic case

**Witt cancellation over LG rings** (`GN 6.5`; cf. `GPR 11.27`) is the capstone result of Layer 0
and the reason this project builds quadratic-form regularity theory in the first place (see the
overview, "Results of independent interest").

## The target statement

Over an LG ring `R`, for `q₁, q₂` **nonsingular** and `q₃` **regular**:
```
-- theorem QuadraticForm.cancel (hLG : IsLGRing R) {q₁ : QuadraticForm R M₁} ...
--     (h₁ : q₁.IsGPRNonsingular) (h₂ : q₂.IsGPRNonsingular) (h₃ : q₃.IsGPRRegular)
--     (h : Nonempty (IsometryEquiv (q₁.prod q₃) (q₂.prod q₃))) :
--     Nonempty (IsometryEquiv q₁ q₂)
```
The hypothesis asymmetry is load-bearing, not a simplification we can drop: cancellation is
**false** if `q₃` is merely nonsingular rather than regular (counterexample: Elman–Karpenko–
Merkurjev, p. 49 — see overview trap 5). `GPR 11.27` is the weaker all-regular
version (GPR's "quadratic space" means regular throughout); `GN 6.5` subsumes it.

## What is proved here

`QuadraticForm.isometryEquiv_prod_dualProd_of_isometryEquiv_prod`: cancelling a **regular** form
`q₃` reduces to cancelling a **hyperbolic** one. Adding `-q₃` to both sides of
`q₁ ⊥ q₃ ≅ q₂ ⊥ q₃` and reassociating turns it into

  `q₁ ⊥ (q₃ ⊥ -q₃) ≅ q₂ ⊥ (q₃ ⊥ -q₃)`,

and `q₃ ⊥ -q₃` is hyperbolic (`QuadraticForm.isometryEquivDualProd`, `Baeza I (4.7)`,
`QuadraticForm/Hyperbolic.lean`). This is the same first move `GN` makes at the start of the proof
of 6.5, and it is where regularity of `q₃` — as opposed to non-singularity — is consumed: the
comparison map `q ⊥ -q → h` is bijective exactly when the polar map of `q` is.

Note that this reduction needs no LG hypothesis at all.

## Where the theorem itself is

`QuadraticForm.cancel` — the statement displayed above — and `QuadraticForm.cancel_dualProd` are
in `QuadraticForm/WittCancellation.lean`, which imports this file. `GN 6.5`'s hypothesis that `q₁`
be non-singular is not carried, since it is implied by the others: `q₂ ⊥ q₃` is non-singular, so
`q₁ ⊥ q₃` is too, and non-singularity passes to summands
(`QuadraticForm.IsGPRNonsingular.of_prod_left`).

The route is Dias's, following Baeza's direct proof in III §4, which Baeza labels "Second proof
(after Knebusch)" and traces to Knebusch's *Isometrien über semi-lokalen Ringen*. It is
deliberately *not* `GN`'s own cohomological proof via reductive group schemes and
`SO(q)`-torsors, per overview §8. Its four steps are all formalized, and they combine into
**cancellation of a single hyperbolic plane**
(`QuadraticForm.isometryEquiv_of_isometryEquiv_plane_prod_of_isLGRing`):

1. **Siegel–Eichler transvections and dilations**, and the unit case of `Dias II.6.2`:
   *if the `u`-coefficient of `i` is a unit then some self-isometry carries the standard hyperbolic
   pair `(u, v)` to `(i, j)`*. Over an arbitrary commutative ring, no hypothesis on `2` —
   `QuadraticForm/HyperbolicPair.lean`,
   `QuadraticMap.IsHyperbolicPair.exists_isometryEquiv_of_isUnit`.
2. **`Dias II.6.1`**, the LG step and the only place the LG axiom is used: given `i = ((α, β), m)`
   in `plane ⊥ q₀`, produce `y ∈ M₀` making `α - q₀(y, m) - β q₀(y)` — the new `u`-coefficient
   after applying `E(u, (0, y))` — a **unit**. `QuadraticForm/PlaneTransitivity.lean`,
   `QuadraticForm.exists_isUnit_sub_polar_sub_smul`. The residue-field case analysis uses
   `exists_isHyperbolicPair_of_radical_eq_bot` (the non-singular field form of `GPR 11.17`) and
   `exists_apply_ne_zero_of_radical_eq_bot` (from `GPR 11.26`); globally, the LG axiom is applied
   to `QuadraticForm.eichlerMvPolynomial` written in the standard basis of a presentation
   `Rⁿ ↠ M₀`, so `M₀` never has to be free.
3. **`Dias II.6.2`** in general — `QuadraticForm.exists_isometryEquiv_of_isHyperbolicPair`. Baeza
   and Dias assume the complement `M₀` nonzero at every residue field (`Baeza III (2.3)`'s rank
   hypothesis, Dias's `V₀ ≠ 0`); that hypothesis is *not* assumed here. Where `M₀` dies the switch
   is needed, and `QuadraticForm.switchIdem` supplies it on exactly that locus — clopen, cut out by
   `Module.rankIdempotent R M₀ 0` — as a single isometry over `R`, with no product decomposition of
   `R`. This matters for step 5: the last plane to be cancelled has bare `q₂` as its complement,
   and `M₂ = 0` is a case `GN 6.5` has to cover.
4. **`Dias II.6.4`**, cancellation of a plane given step 3 — `QuadraticForm/PlaneCancellation.lean`,
   `QuadraticForm.isometryEquiv_of_isometryEquiv_plane_prod`. This step needs no regularity of `q₁`
   or `q₂` at all: membership in the second summand is detected by orthogonality to the pair.
5. **From one plane to `dualProd R N`** — `QuadraticForm/WittCancellation.lean`. Choose `N'` with
   `N × N' ≅ Rⁿ`, add `dualProd R N'` to both sides, and use
   `dualProd R (M × N) ≅ dualProd R M ⊥ dualProd R N` with `dualProd R R ≅ plane R` to
   reduce to `n` planes, then induct. This needs `N` neither free nor of constant rank, so it
   avoids `GN 2.6(b)` and the rank decomposition. The intermediate forms
   `dualProd R (Rᵏ) ⊥ q₂` are non-singular by `GN (C.8.3)`
   (`QuadraticForm.IsGPRRegular.prod_isGPRNonsingular`) — which is why the hyperbolic summand is
   kept on the left, where a *regular* form is what that lemma wants.

The prerequisites this file used to list are all in place: `LGRing/` is complete through
`GPR 11.22` (semilocal ⇒ LG), `GN 2.6(a)` and `GN 2.6(b)`, the representation lemma `GPR 11.26`
holds in full generality, and the rank decomposition `GPR Exc. 9.31` is available.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.11, 11.27.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, §6 (`6.1`, `6.5`).
* [Baeza] R. Baeza, *Quadratic Forms over Semilocal Rings*, Lecture Notes in Mathematics **655**,
  Springer, 1978, I (4.7), III §4, and Corollary III.4.3.
* [Dias] I. Dias, *Formas Quadráticas Sobre LG-Anéis*, Ph.D. thesis, Universidade Estadual de
  Campinas, 1988, II.6.1–II.6.4.
* [Knebusch] M. Knebusch, *Isometrien über semi-lokalen Ringen*, Mathematische Zeitschrift
  **108** (1969), 255–268. Baeza III §4 cites this as `[K]₂` for the direct proof.
* [EKM] R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic
  Forms*, AMS Colloquium Publications **56**, 2008, p. 49: the counterexample bounding the
  hypothesis on `q₃`.
-/

@[expose] public section

universe u v₁ v₂ v₃

variable {R : Type u} [CommRing R]
variable {M₁ : Type v₁} [AddCommGroup M₁] [Module R M₁]
variable {M₂ : Type v₂} [AddCommGroup M₂] [Module R M₂]
variable {M₃ : Type v₃} [AddCommGroup M₃] [Module R M₃]

/-- **Cancelling a regular form reduces to cancelling a hyperbolic one.**

From `q₁ ⊥ q₃ ≅ q₂ ⊥ q₃` with `q₃` regular, add `-q₃` to both sides and reassociate: since
`q₃ ⊥ -q₃` is hyperbolic (`QuadraticForm.isometryEquivDualProd`), the result is
`q₁ ⊥ h ≅ q₂ ⊥ h` with `h` the hyperbolic form of `M₃`.

This is the opening move of `GN`'s proof of 6.5, and it needs no LG hypothesis. Regularity of
`q₃` — rather than mere non-singularity — is consumed here and nowhere else. -/
theorem QuadraticForm.isometryEquiv_prod_dualProd_of_isometryEquiv_prod
    [Module.Finite R M₃] [Module.Projective R M₃] {q₁ : QuadraticForm R M₁}
    {q₂ : QuadraticForm R M₂} {q₃ : QuadraticForm R M₃}
    (h₃ : QuadraticForm.IsGPRRegular q₃)
    (h : Nonempty (QuadraticMap.IsometryEquiv (q₁.prod q₃) (q₂.prod q₃))) :
    Nonempty (QuadraticMap.IsometryEquiv (q₁.prod (QuadraticForm.dualProd R M₃))
      (q₂.prod (QuadraticForm.dualProd R M₃))) := by
  obtain ⟨e⟩ := h
  refine ⟨?_⟩
  -- `q₁ ⊥ h ≅ q₁ ⊥ (q₃ ⊥ -q₃) ≅ (q₁ ⊥ q₃) ⊥ -q₃`
  -- `≅ (q₂ ⊥ q₃) ⊥ -q₃ ≅ q₂ ⊥ (q₃ ⊥ -q₃) ≅ q₂ ⊥ h`
  refine ((QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl q₁)
    (QuadraticForm.isometryEquivDualProd q₃ h₃).symm).trans ?_).trans
    (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl q₂)
      (QuadraticForm.isometryEquivDualProd q₃ h₃))
  refine (QuadraticMap.IsometryEquiv.prodAssoc q₁ q₃ (-q₃)).symm.trans ?_
  exact (QuadraticMap.IsometryEquiv.prod e (QuadraticMap.IsometryEquiv.refl (-q₃))).trans
    (QuadraticMap.IsometryEquiv.prodAssoc q₂ q₃ (-q₃))
