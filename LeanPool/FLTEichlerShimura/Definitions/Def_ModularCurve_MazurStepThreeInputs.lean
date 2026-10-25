/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node ModularCurve_MazurStepThreeInputs
(e3e6892f-f171-5eae-9a79-bf709f2cab60) by Claude (2026-09-05).

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_Eisenstein
public import LeanPool.FLTEichlerShimura.Definitions.Def_EllipticCurve_ZeroComponentAt

/-!
# Named inputs for Mazur's step three over X0​(p)

Definition: `ModularCurve_MazurStepThreeInputs` (`e3e6892f-f171-5eae-9a79-bf709f2cab60`), by Claude,
2026-09-05.

Fix a prime-to-be $p$ with `NeZero p`, and let `JZero p` be the degree-zero divisor class group
$\mathrm{Pic}^0$ of the geometric modular function field `modularFunctionFieldBar p` over
$\overline{\mathbb Q}$. Throughout, the Hecke-module structure is an explicit binder `inst : Module
HeckeAlg (JZero p)` rather than an instance, `HeckeAlg` being the polynomial ring $\mathbb Z[T_\ell
: \ell \text{ prime}]$. First come the carriers: `eisensteinKernelSubmodule p inst` is
$\gamma\cdot\top$, where $\gamma$ is the ideal `eisensteinKernel` attached to `eisensteinIdeal p`
(the kernel of $T_\ell \mapsto 1$ for $\ell \mid p$, $T_\ell \mapsto 1+\ell$ otherwise);
`EisensteinQuotient p inst` is the quotient of `JZero p` by it, `eisensteinQuotientMk` the quotient
map, and `eisensteinQuotientRational` the image of the set of $x$ with $\sigma\cdot x - x \in
\gamma\cdot\top$ for all $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, i.e. the
"rational part" of the quotient. The theorem `eisensteinQuotientInvariantsFiniteAt_iff` records, by
`Iff.rfl`, that the project's predicate `EisensteinQuotientInvariantsFiniteAt` is exactly finiteness
of this set. `CuspidalClassSurvives` says the class of $(\bar 0)-(\bar\infty)$ does not lie in
$\gamma\cdot\top$. Next, `jBar p` and `jpBar p` are the coefficientwise images in
`modularFunctionFieldBar p` of the $q$-expansions $j(q)$ and $j(q^p)$, and `placeDiff p x y` is the
divisor $(x)-(y)$.

`MazurQuotientSpecialization p inst` asserts: for every prime $\ell \neq p$ and every valuation
subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $A$, there are an abelian group $T$
and an additive map $s$ from the Eisenstein quotient such that (i) $s$ is injective on the
prime-to-$\ell$ torsion of `eisensteinQuotientRational`, (ii) if $\ell \neq 2$, also on its
$\ell$-power torsion, and (iii) $s$ annihilates the class of $(x)-(\bar\infty)$, resp. $(x)-(\bar
0)$, for every place $x$ fixed by the arithmetic Galois action with $\mathrm{ord}_x(\,\bar j - j_1)
> 0$, $\mathrm{ord}_x(\,\bar j_p - j_2) > 0$ and $v_A(j_1) > 1$, under $v_A(j_2) = v_A(j_1)^p$,
resp. $v_A(j_2)^p = v_A(j_1)$ (the relevant divisors being assumed of degree zero).

Finally, `jInt W` is $c_4^3/\Delta$ computed with Lean's total division (so $0$ when $\Delta = 0$;
every use assumes $\Delta \neq 0$), and `JQuot` is the type of functions assigning to each integral
Weierstrass curve $W$ and each $\overline{\mathbb Q}$-point of $W_{\mathbb Q}$ an element of
$\overline{\mathbb Q}$ — an abstract stand-in for the $j$-invariant of the quotient, with no
identification built in. For such a `jQuot`, `ModuliPointExists` says that for $p$ prime, $W$ with
$\Delta \neq 0$ and $q \nmid c_4$ for every prime $q \mid \Delta$, and every Galois-fixed point $Q$
of exact order $p$, there is a degree-one place of `modularFunctionFieldBar p`, fixed by the
arithmetic Galois action, at which both $\bar j - \mathrm{jInt}\,W$ and $\bar j_p -
\mathrm{jQuot}\,W\,Q$ have positive order. `TateCuspCriterion` says that in the same situation, at a
prime $\ell \neq p$ with $\ell \mid \Delta$, $\ell \nmid c_4$ and $A$ over $\ell$, one has
$v_A(\mathrm{jInt}\,W) > 1$, and that $Q$ lies in the zero component at $A$ (in the sense of the
project's `InZeroComponentAt`: $Q = 0$, or $Q = (x,y)$ with $x \notin A$, or $x,y \in A$ with
nonsingular reduction) implies $v_A(\mathrm{jQuot}\,W\,Q) = v_A(\mathrm{jInt}\,W)^p$, while failure
of that condition implies $v_A(\mathrm{jQuot}\,W\,Q)^p = v_A(\mathrm{jInt}\,W)$; these are two
one-directional implications, not stated as equivalences.

**Relation to Mathlib.** Weierstrass curves, their invariants $c_4,\Delta$, affine points and
`ValuationSubring` are Mathlib's; the curve-theoretic framework used here (places, divisors,
$\mathrm{Pic}^0$, the modular function field as a subfield of Laurent series, the Hecke algebra and
the Eisenstein ideal) is the project's own, as are `InZeroComponentAt` and `LiesOverPrime`.

**Where it is used.** These predicates isolate, as propositions carrying no proof, the inputs from
Mazur's study of the Eisenstein ideal and from Tate uniformisation that are consumed by the
reduction proving [`MazurStepThree p`](../def/ModularCurve_MazurStepThree.html#L8): the finiteness
of the rational part of the Eisenstein quotient, survival of the cuspidal class (which fails for $p
\le 7$ and $p = 13$), the specialisation map with its injectivity and cusp-killing clauses,
existence of the moduli point attached to a pair $(W, \langle Q\rangle)$, and the Tate-curve
computation of the quotient $j$-invariant's valuation.

<!-- Generated by add_prove2me_provenance.py -->
-/

@[expose] public section publicSection

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable (p : ℕ) [NeZero p]

/-- The submodule generated by the action of the Eisenstein kernel on the level-`p` divisor-class
group. -/
def eisensteinKernelSubmodule (inst : Module HeckeAlg (JZero p)) :
    letI := inst; Submodule HeckeAlg (JZero p) :=
  letI := inst
  eisensteinKernel (JZero p) (eisensteinIdeal p) • (⊤ : Submodule HeckeAlg (JZero p))

/-- The quotient of the divisor-class group by its Eisenstein-kernel submodule. -/
abbrev EisensteinQuotient (inst : Module HeckeAlg (JZero p)) : Type :=
  letI := inst
  JZero p ⧸ eisensteinKernelSubmodule p inst

/-- The additive projection to the Eisenstein quotient. -/
def eisensteinQuotientMk (inst : Module HeckeAlg (JZero p)) :
    JZero p →+ EisensteinQuotient p inst :=
  letI := inst
  (eisensteinKernelSubmodule p inst).mkQ.toAddMonoidHom

/-- The image in the Eisenstein quotient of classes whose Galois differences lie in the
Eisenstein-kernel submodule. -/
def eisensteinQuotientRational (inst : Module HeckeAlg (JZero p)) :
    Set (EisensteinQuotient p inst) :=
  letI := inst
  eisensteinQuotientMk p inst ''
    {x : JZero p | ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ • x - x ∈ eisensteinKernelSubmodule p inst}

omit [NeZero p] in
theorem eisensteinQuotientInvariantsFiniteAt_iff (inst : Module HeckeAlg (JZero p)) :
    EisensteinQuotientInvariantsFiniteAt p inst ↔ (eisensteinQuotientRational p inst).Finite :=
  Iff.rfl

/-- The cuspidal class does not belong to the Eisenstein-kernel submodule. -/
def CuspidalClassSurvives (inst : Module HeckeAlg (JZero p)) : Prop :=
  letI := inst
  cuspidalClass p ∉ eisensteinKernelSubmodule p inst

/-- The expansion `j(q)` viewed in the algebraic-closure full modular function field. -/
abbrev jBar : modularFunctionFieldBar p :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩

/-- The expansion `j(q^p)` viewed in the algebraic-closure full modular function field. -/
abbrev jpBar : modularFunctionFieldBar p :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩

/-- The divisor consisting of the first place minus the second place. -/
def placeDiff (x y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
  Finsupp.single x 1 - Finsupp.single y 1

/-- Specialization maps on the Eisenstein quotient detect rational torsion and kill the
prescribed cusp differences under the corresponding valuation relations. -/
def MazurQuotientSpecialization (inst : Module HeckeAlg (JZero p)) : Prop :=
  letI := inst
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∃ (T : Type) (_ : AddCommGroup T) (s : EisensteinQuotient p inst →+ T),
        (∀ z ∈ eisensteinQuotientRational p inst,
            (∃ m : ℕ, ¬ ℓ ∣ m ∧ m • z = 0) → s z = 0 → z = 0) ∧
        (ℓ ≠ 2 → ∀ z ∈ eisensteinQuotientRational p inst,
            (∃ k : ℕ, ℓ ^ k • z = 0) → s z = 0 → z = 0) ∧
        (∀ (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
            (j₁ j₂ : AlgebraicClosure ℚ)
            (hinf : placeDiff p x (cuspInftyBar p) ∈ Divisor.degZero)
            (hzero : placeDiff p x (cuspZeroBar p) ∈ Divisor.degZero),
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
              arithmeticGalois (modularFunctionFieldFull p) σ • x = x) →
          0 < x.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₁) →
          0 < x.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₂) →
          1 < A.valuation j₁ →
            (A.valuation j₂ = A.valuation j₁ ^ p →
              s (eisensteinQuotientMk p inst
                (Pic0.mk ⟨placeDiff p x (cuspInftyBar p), hinf⟩)) = 0) ∧
            (A.valuation j₂ ^ p = A.valuation j₁ →
              s (eisensteinQuotientMk p inst
                (Pic0.mk ⟨placeDiff p x (cuspZeroBar p), hzero⟩)) = 0))

end ModularCurve

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

variable (p : ℕ) [NeZero p]

/-- The ratio `c₄³ / Δ` of an integral Weierstrass equation, valued in the algebraic closure of
the rationals. -/
def jInt (W : WeierstrassCurve ℤ) : AlgebraicClosure ℚ :=
  ((W.c₄ : ℤ) : AlgebraicClosure ℚ) ^ 3 / ((W.Δ : ℤ) : AlgebraicClosure ℚ)

/-- The type of functions assigning an algebraic number to an integral Weierstrass curve and a
point over the algebraic closure. -/
abbrev JQuot : Type :=
  (W : WeierstrassCurve ℤ) → ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →
    AlgebraicClosure ℚ

/-- Every rational point of order `p` on the specified semistable integral curve determines a
rational degree-one modular-curve place with the prescribed two `j`-values. -/
def ModuliPointExists (jQuot : JQuot) : Prop :=
  p.Prime →
  ∀ (W : WeierstrassCurve ℤ), W.Δ ≠ 0 →
    (∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → ¬ (q : ℤ) ∣ W.c₄) →
    ∀ (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) →
      addOrderOf Q = p →
      ∃ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p),
        x.deg = 1 ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            arithmeticGalois (modularFunctionFieldFull p) σ • x = x) ∧
        0 < x.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (jInt W)) ∧
        0 < x.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p)
              (jQuot W Q))

/-- At the indicated multiplicative primes, valuations of the two `j`-values distinguish whether
the torsion point lies in the identity component. -/
def TateCuspCriterion (jQuot : JQuot) : Prop :=
  p.Prime →
  ∀ (W : WeierstrassCurve ℤ), W.Δ ≠ 0 →
    ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → (ℓ : ℤ) ∣ W.Δ → ¬ (ℓ : ℤ) ∣ W.c₄ →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
    ∀ (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) →
      addOrderOf Q = p →
        1 < A.valuation (jInt W) ∧
        (W.InZeroComponentAt A Q → A.valuation (jQuot W Q) = A.valuation (jInt W) ^ p) ∧
        (¬ W.InZeroComponentAt A Q → A.valuation (jQuot W Q) ^ p = A.valuation (jInt W))

end ModularCurve

end


end publicSection
