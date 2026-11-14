/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Alternative
public import LeanPool.CompositionAlgebrasOverRings.Composition.BaseChange
public import LeanPool.CompositionAlgebrasOverRings.Composition.Basic
public import LeanPool.CompositionAlgebrasOverRings.Composition.CayleyDickson
public import LeanPool.CompositionAlgebrasOverRings.Composition.CayleyDicksonIff
public import LeanPool.CompositionAlgebrasOverRings.Composition.ComplexQuaternion
public import LeanPool.CompositionAlgebrasOverRings.Composition.Defs
public import LeanPool.CompositionAlgebrasOverRings.Composition.Doubling
public import LeanPool.CompositionAlgebrasOverRings.Composition.Examples
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Basic
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Euclidean
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Finite
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.FractionField
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Real
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.SepClosed
public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.SurjectiveNorm
public import LeanPool.CompositionAlgebrasOverRings.Composition.Inseparable
public import LeanPool.CompositionAlgebrasOverRings.Composition.InseparableAnisotropic
public import LeanPool.CompositionAlgebrasOverRings.Composition.NormClassification
public import LeanPool.CompositionAlgebrasOverRings.Composition.NormEquivalence
public import LeanPool.CompositionAlgebrasOverRings.Composition.Octonion
public import LeanPool.CompositionAlgebrasOverRings.Composition.QuadraticEtale
public import LeanPool.CompositionAlgebrasOverRings.Composition.QuadraticSubalgebra
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankDichotomy
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankOneTwoFourEight
public import LeanPool.CompositionAlgebrasOverRings.Composition.RankTwoSubalgebra
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Capstone
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Classification
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Defs
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Hyperbolic
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Orientation
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.OrientedRankEight
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Peirce
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.RankEight
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.RankTwo
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Reducedness
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Split
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Splitness
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.TwistedMatrix
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.TwistedZorn
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Zorn
public import LeanPool.CompositionAlgebrasOverRings.Composition.Sedenion
public import LeanPool.CompositionAlgebrasOverRings.Composition.Tower
public import LeanPool.CompositionAlgebrasOverRings.Conic.BaseChange
public import LeanPool.CompositionAlgebrasOverRings.Conic.BaseChangeMultiplicative
public import LeanPool.CompositionAlgebrasOverRings.Conic.Basic
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDickson
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonAlternative
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonAssociative
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonConverse
public import LeanPool.CompositionAlgebrasOverRings.Conic.CayleyDicksonMultiplicative
public import LeanPool.CompositionAlgebrasOverRings.Conic.Defs
public import LeanPool.CompositionAlgebrasOverRings.Conic.Division
public import LeanPool.CompositionAlgebrasOverRings.Conic.Doubling
public import LeanPool.CompositionAlgebrasOverRings.Conic.Kirmse
public import LeanPool.CompositionAlgebrasOverRings.Conic.Multiplicative
public import LeanPool.CompositionAlgebrasOverRings.Conic.Projective
public import LeanPool.CompositionAlgebrasOverRings.Conic.QuadraticAlgebra
public import LeanPool.CompositionAlgebrasOverRings.Conic.Recognition
public import LeanPool.CompositionAlgebrasOverRings.Conic.Subalgebra
public import LeanPool.CompositionAlgebrasOverRings.Conic.TraceDefectCounterexample
public import LeanPool.CompositionAlgebrasOverRings.LGRing.ConstantRank
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Defs
public import LeanPool.CompositionAlgebrasOverRings.LGRing.DirectLimit
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Examples
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Jacobson
public import LeanPool.CompositionAlgebrasOverRings.LGRing.NonExamples
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Products
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Semilocal
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Unimodular
public import LeanPool.CompositionAlgebrasOverRings.LGRing.ValueIdeal
public import LeanPool.CompositionAlgebrasOverRings.LGRing.ZeroDimensional
public import LeanPool.CompositionAlgebrasOverRings.Module.AlternatingBaseChange
public import LeanPool.CompositionAlgebrasOverRings.Module.ExteriorPower
public import LeanPool.CompositionAlgebrasOverRings.Module.IdempotentDecomposition
public import LeanPool.CompositionAlgebrasOverRings.Module.IdempotentFactor
public import LeanPool.CompositionAlgebrasOverRings.Module.Invertible
public import LeanPool.CompositionAlgebrasOverRings.Module.RankDecomposition
public import LeanPool.CompositionAlgebrasOverRings.Module.SelfAnnihilating
public import LeanPool.CompositionAlgebrasOverRings.Module.Unimodular
public import LeanPool.CompositionAlgebrasOverRings.Module.VectorProduct
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Artin
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Defs
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Moufang
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.Peirce
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Alternative.PowerAssociative
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Associator
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Division
public import LeanPool.CompositionAlgebrasOverRings.Nonassociative.Subalgebra
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.BaseChangeProjective
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Cancellation
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.FiniteField
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Hyperbolic
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.HyperbolicPair
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Isotropic
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.NonsingularOverFields
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.OrthogonalComplement
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.PlaneCancellation
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.PlaneSplitting
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.PlaneTransitivity
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Polynomial
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Real
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Representation
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.WittCancellation

/-!
# Composition Algebras over Commutative Rings

Source: doi:10.1017/9781009426862
Authors: Skip Garibaldi
Status: verified
Main declarations: `ConicAlgebra.IsComposition.rankAtStalk_classification`, `QuadraticForm.cancel`
Tags: nonassociative-algebra, composition-algebras, octonions, quadratic-forms, lg-rings
MSC: 17A75, 17D05, 11E81, 11E08, 13C10
-/

@[expose] public section

/-!
# Composition algebras over commutative rings

This project develops the theory of **composition algebras over a commutative ring**, following
Garibaldi–Petersson–Racine, *Albert Algebras over Commutative Rings* (`GPR`), Part I: conic
algebras, Cayley–Dickson doubling, composition algebras, reduced composition algebras, and the
classification over special classes of fields. Two results needed along the way are of
independent interest and are proved in full: **Witt cancellation for quadratic forms** and
**Artin's theorem on alternative rings**.

The proofs that are classical over fields work, almost unchanged, over **LG rings** — commutative
rings over which finitely generated projective modules behave like vector spaces — so that is the
generality used. The objects themselves are defined over an arbitrary commutative ring.

A result-by-result record of what is proved, indexed by its number in `GPR`, `GN`, `EKM` and
`Dias`, is `RESULTS.md` in the source repository (`skipgaribaldi/CompositionAlgebras-lean`, tag
`v1.0`). Docstrings in this project cite the sections below as "overview §N" and "overview trap N".

## Layout

The directories form layers. A file imports mathlib, TauCeti, and directories of strictly lower
layer only, so that the general-purpose layers stay liftable:

| Layer | Directory | Contents |
|---|---|---|
| 0 | `Module/` | commutative algebra: idempotents, rank decomposition, unimodular elements |
| 0 | `Nonassociative/` | associator, nucleus, alternative rings, Moufang, Artin's theorem |
| 1 | `LGRing/` | LG rings: examples, non-examples, constant-rank projectives are free |
| 2 | `QuadraticForm/` | base change without `2`, regularity, isotropy, Witt cancellation |
| 3 | `Conic/` | conic algebras, conjugation, Cayley–Dickson doubling |
| 4 | `Composition/` | composition algebras, the tower, ranks 1, 2, 4, 8, reduced algebras |

## Why LG rings

A commutative ring `R` is an **LG ring** if a polynomial over `R` represents a unit as soon as it
represents a unit over every residue field `R ⧸ 𝔪`. LG rings include all fields, all semilocal
rings, all zero-dimensional rings and the ring of all algebraic integers; they do not include `ℤ`
or `R[t]` for a domain `R`. Two facts drive everything:

1. over an LG ring, a finitely generated projective module of constant rank is free;
2. quadratic forms over an LG ring cancel: `q₁ ⊥ q₃ ≅ q₂ ⊥ q₃ ⇒ q₁ ≅ q₂` for `q₁, q₂`
   nonsingular and `q₃` regular (`GN 6.5`).

## Results of independent interest

* **Witt cancellation** over LG rings, with the field case as an instance, proved by the
  elementary Dias–Baeza–Knebusch route through hyperbolic planes and Siegel–Eichler transvections.
* **Artin's theorem**: a ring is alternative if and only if every subring generated by two elements
  is associative; with the alternating associator and the three Moufang identities.
* **LG rings** with their examples and non-examples, and freeness of constant-rank projectives.
* **The rank decomposition** of a finitely generated projective module (`GPR Exc. 9.31`).
* **Invertible modules are line bundles** (`Module.invertible_iff_isLocallyFreeRankOne`).
* **Isotropy over a finite field**: a quadratic form in at least three variables over a finite
  field has a nonzero null vector, via Chevalley–Warning.

## Conventions

These conventions keep the development consistent; docstrings refer to them by number.

**§0. mathlib and TauCeti are canonical.** Nothing they define is redefined here. Where a notion
must differ from mathlib's, the divergence is documented with a `⚠` paragraph saying what mathlib's
notion is, what ours is, and where they agree.

**§2. Hypotheses are unbundled, minimal and honest.** Every result carries exactly the hypotheses
its proof consumes. Three axes stay separate: algebra structure (`[NonAssocRing A]`,
`[IsAlternative A]`), norm regularity (`IsGPRNonsingular`, `IsGPRRegular`, ...) and module
regularity (`Module.Finite`, `Module.Projective`, constant rank). Objects are defined over a
general `CommRing`; `IsLGRing k` and `[Field K]` appear only on theorems, and the field case is the
LG theorem applied to `isLGRing_of_field`.

**§3. Import discipline.** See *Layout*: no file imports a directory of the same or a higher
layer, apart from its own.

**§5. No `sorry`, no `native_decide`.** Every result uses only the standard axioms.

**§6. Mandatory warnings.** Each is documented where it applies and may not be simplified away.
* (a) **Polar, never `associated`.** Norm, trace and conjugation go through the un-halved
  `QuadraticMap.polar`. `QuadraticMap.associated` needs `Invertible 2` and would make every
  characteristic-two example unstatable.
* (b) **Regularity words are source-specific.** mathlib's `LinearMap.BilinForm.Nondegenerate` is
  injectivity into the dual, `GPR`'s "weakly regular". `GPR`'s non-degenerate, non-singular and
  regular are `QuadraticForm.IsGPRNondegenerate`, `IsGPRNonsingular` and `IsGPRRegular`; `EKM`'s
  ladder is `IsEKMNondegenerate`. No bare `IsNondegenerate`, `IsRegular` or `IsNonsingular`.
* (c) **`GPR` isotropy is unimodular, mathlib's is nonzero.** `GPR`'s notion is
  `QuadraticMap.IsGPRIsotropic`, never `¬ QuadraticMap.Anisotropic`; they agree over fields and
  over PIDs (`GPR 22.19`) but not in general.
* (d) **The Cayley–Dickson scalar is arbitrary**: `μ : k`, not `μ : kˣ`. Unit hypotheses go on
  theorems; otherwise the sedenions could not be stated.
* (e) **Conjugation is an anti-homomorphism only with a module hypothesis.** Over a ring,
  `conj (x y) = (conj y) (conj x)` needs the algebra projective (`GPR 16.14(b)`, `GPR 17.6`), even
  when it is associative; see trap 6.

**§8. Working with the literature.** `GPR` and `GN` are the sources of record, cited by number.
`GN` is cited by its published numbering (European Journal of Mathematics **11** (2025), article
42), not the arXiv preprint's: preprint 1.6 is published 2.6, preprint 5.5 is published 6.5, and
preprint 2.15 is published Example 3.15. The `GPR` pre-publication text uses the same numbering as
the published book. Where a result is false in greater generality, its docstring says so and cites
the counterexample. Proofs avoid disproportionate machinery: Witt cancellation follows the
elementary Dias–Baeza–Knebusch route rather than `GN`'s cohomological Cancellation Principle, and
of `GN Example 3.15` only the final paragraph is in scope.

## Design decisions

1. **Two named algebra notions, `ConicAlgebra` and `IsComposition`.** Everything between them is
   a hypothesis. There is no `PreCompositionAlgebra`: `GPR 19.7(a)` shows that notion is not
   stable under base change, with `GPR 19.4` as the counterexample.
2. **Three independent axes, never bundled** (§2).
3. **`GPR`'s regularity notions, named after their source** (§6(b)). Over a ring they are not
   linearly ordered; `QuadraticForm/Regularity.lean` has the separating examples.
4. **Polar, never `associated`** (§6(a)).
5. **`μ : k` arbitrary in Cayley–Dickson** (§6(d)).
6. **Recover mathlib's objects, don't duplicate them**, asymmetrically where the mathematics is
   asymmetric (trap 3).
7. **Work over `CommRing` by default** (§2).

## Boundaries and traps

Six places where the obvious thing is wrong.

1. **Regularity words are source-specific** (§6(b)). For finite-dimensional forms over a field of
   characteristic not two the notions agree; in characteristic two they separate already over a
   field (`x²` over `𝔽₂` is non-degenerate and non-singular but not weakly regular), and over rings
   further (`x²` over `𝔽₂[ε]/(ε²)` is non-singular with `ε` in its radical).
2. **Isotropy is unimodular** (§6(c)). `GPR 22.19` lists the two notions as separate conditions,
   (ii) and (iii), because over a general ring they are.
3. **`QuaternionAlgebra` is a free rank-four presentation, not "the rank-four composition
   algebras".** It is too wide (its norm need not be non-singular) and too narrow (it only
   produces free modules). The correct statements are asymmetric: a `QuaternionAlgebra` with
   non-singular norm is a rank-four composition algebra, and over an LG ring every
   constant-rank-four composition algebra is a `QuaternionAlgebra`. The specific identification of
   `Cay₄ ℝ (-1) (-1)` with `ℍ[ℝ]` is unaffected.
4. **The norm does not determine the algebra over a general ring.** Gille (Canad. Math. Bull.
   **57** (2014), 303–309) gives non-isomorphic octonion algebras with isometric norms, so the LG
   hypothesis in the norm classification cannot be dropped.
5. **Witt cancellation needs `q₃` regular**, not merely nonsingular; otherwise it is false
   (Elman–Karpenko–Merkurjev, p. 49, cited at the end of `GN §6`).
6. **Alternativity does not make conjugation an anti-homomorphism over a ring.** The field proof
   does not generalize: `Conic/TraceDefectCounterexample.lean` gives an associative conic algebra
   over `ℤ/4` where it fails, a small variant of McCrimmon's `GPR Exc. 17.8`. `GPR` itself warns
   against this in `GPR 17.4`.

## References

* [GPR] S. Garibaldi, H. P. Petersson, M. Racine, *Albert Algebras over Commutative Rings*,
  Cambridge University Press, New Mathematical Monographs **48**, 2024.
* [GN] P. Gille, E. Neher, *Group schemes over LG-rings and applications to cancellation theorems
  and Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42.
* [EKM] R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic
  Forms*, AMS Colloquium Publications **56**, 2008.
* [Dias] I. Dias, *Formas Quadráticas Sobre LG-Anéis*, Ph.D. thesis, Universidade Estadual de
  Campinas, 1988.
* R. Baeza, *Quadratic Forms over Semilocal Rings*, Lecture Notes in Mathematics **655**, 1978.
* R. D. Schafer, *An Introduction to Nonassociative Algebras*.
* P. Gille, *Octonion algebras over rings are not determined by their norms*, Canad. Math. Bull.
  **57** (2014), 303–309.
-/
