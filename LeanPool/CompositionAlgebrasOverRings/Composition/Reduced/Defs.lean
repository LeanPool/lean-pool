/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Split
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Isotropic
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.PlaneSplitting

/-!
# Elementary idempotents and reduced composition algebras (`GPR 22.6–22.9`)

An **elementary idempotent** of a conic algebra (`GPR Exc. 16.23`) is an element `c` with

  `n(c) = 0`  and  `t(c) = 1`.

The degree-two identity then makes it an idempotent for free, `c² = t(c)c - n(c)1 = c`, and its
conjugate `conj c = 1 - c` is a second elementary idempotent orthogonal to it. Elementary
idempotents are what "reduced" means in practice: a composition algebra of rank `> 1` is reduced in
the sense of `GPR 22.6` exactly when it has one (`GPR 22.7`).

This file proves the part of **`GPR 22.9`** that needs no Peirce decomposition: for a conic algebra
`C`, being reduced, containing a split quadratic étale subalgebra, and — under the two hypotheses
the proof actually consumes — having isotropic norm, are all the same condition.

## The three conditions

* **(i)** `C` has an elementary idempotent (`ConicAlgebra.HasElementaryIdempotent`).
* **(ii)** `C` contains a split quadratic étale subalgebra
  (`ConicAlgebra.HasSplitEtaleSubalgebra`), spelled concretely as an injective, unital,
  multiplicative norm-preserving `k`-linear map `k × k → A`, with `k × k` carrying the conic
  structure `ConicAlgebra.splitEtale` of `GPR 21.19(b)`.
* **(iii)** the norm is isotropic in `GPR`'s sense — a **unimodular** null vector
  (`QuadraticMap.IsGPRIsotropic`), not merely a nonzero one; see overview §6(c).

`(i) ↔ (ii)` holds in **every** conic algebra, with no regularity, no projectivity, no
multiplicativity and no hypothesis on `2`: both directions are a direct computation with `c` and
`conj c`. `(i) → (iii)` is likewise free — the trace is a functional taking the value `1` at `c`,
which is exactly unimodularity (`GPR 9.13`). Only `(iii) → (i)` costs anything, and what it
costs is `GPR`'s own argument: regularity of the norm and multiplicativity.

## Main definitions

* `ConicAlgebra.IsElementaryIdempotent` : `n(c) = 0` and `t(c) = 1` (`GPR Exc. 16.23`).
* `ConicAlgebra.HasElementaryIdempotent`, `ConicAlgebra.HasSplitEtaleSubalgebra` : conditions (i)
  and (ii) of `GPR 22.9`.
* `ConicAlgebra.elementaryIdempotentEmbedding` : the map `(a, b) ↦ a c + b (conj c)`.

## Main results

* `ConicAlgebra.hasSplitEtaleSubalgebra_iff_hasElementaryIdempotent` : **`GPR 22.9` (i) ↔ (ii)**.
* `ConicAlgebra.hasElementaryIdempotent_iff_isGPRIsotropic` : **`GPR 22.9` (i) ↔ (iii)**, for a
  regular multiplicative norm.
* `ConicAlgebra.IsElementaryIdempotent.isHyperbolicPair` : `(c, conj c)` is a hyperbolic pair of the
  norm, and `ConicAlgebra.IsElementaryIdempotent.isometryEquivPlaneProd` splits the plane
  `k c ⊕ k (conj c)` off orthogonally. The full hyperbolic presentation is in
  `Composition/Reduced/Hyperbolic.lean`.

## Implementation notes

⚠ **"Reduced" is not defined here, and `HasElementaryIdempotent` is not it.** `GPR 22.6` defines a
composition algebra to be *reduced* if it contains an **absolutely primitive** idempotent, and
`GPR 22.7` proves that in rank `> 1` those are exactly the elementary ones. The two notions really
do differ in rank one: `1 ∈ k` is absolutely primitive, so `k` is reduced, while an elementary
idempotent of `k` would need `c² = 0` and `2c = 1`, which `ℝ` does not supply. Absolute
primitivity quantifies over all base changes and nothing downstream needs it, so this file states
the
elementary-idempotent condition under its own name and records the discrepancy rather than
overloading `GPR`'s word.

Clause (iv) of `GPR 22.9` — that the norm is hyperbolic — is completed in
`Composition/Reduced/Hyperbolic.lean`. What is proved here is the hypothesis-free first step: the
plane `k c ⊕ k (conj c)` splits off orthogonally
(`IsElementaryIdempotent.isometryEquivPlaneProd`).

**Why (ii) is not stated with a `NonAssocSubalgebra`.** The content of "contains a split quadratic
étale subalgebra" is the *map* from `k × k`, since that is what carries the norm, and phrasing it
as a submodule with induced structure would need the restricted conic algebra of
`Conic/Subalgebra.lean` plus an isomorphism anyway. The injective unital multiplicative isometry is
the same data, presented once.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 9.13,
  Exc. 16.23, 21.19, 22.6, 22.7, 22.9.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A]

/-- `c` is an **elementary idempotent** of the conic algebra `C` (`GPR Exc. 16.23`): its norm
vanishes and its trace is `1`.

Idempotency is a consequence, not a hypothesis: the degree-two identity gives
`c² = t(c) c - n(c) 1 = c` (`ConicAlgebra.IsElementaryIdempotent.mul_self`). Nothing here needs
regularity, projectivity, multiplicativity or an assumption on `2`. -/
structure IsElementaryIdempotent (C : ConicAlgebra k A) (c : A) : Prop where
  /-- The norm of an elementary idempotent vanishes. -/
  norm_eq_zero : C.norm c = 0
  /-- The trace of an elementary idempotent is `1`. -/
  trace_eq_one : C.trace c = 1

namespace IsElementaryIdempotent

variable {C : ConicAlgebra k A} {c : A}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- An elementary idempotent is an idempotent, by the degree-two identity. -/
theorem mul_self (hc : C.IsElementaryIdempotent c) : c * c = c := by
  rw [C.mul_self_eq c, hc.norm_eq_zero, hc.trace_eq_one, one_smul, zero_smul, sub_zero]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The conjugate of an elementary idempotent is `1 - c`. -/
theorem conj_eq (hc : C.IsElementaryIdempotent c) : C.conj c = 1 - c := by
  rw [ConicAlgebra.conj_apply, hc.trace_eq_one, one_smul]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The conjugate of an elementary idempotent is again one: `conj c = 1 - c` is the complementary
idempotent. -/
theorem conj (hc : C.IsElementaryIdempotent c) : C.IsElementaryIdempotent (C.conj c) where
  norm_eq_zero := by rw [ConicAlgebra.norm_conj, hc.norm_eq_zero]
  trace_eq_one := by rw [ConicAlgebra.trace_conj, hc.trace_eq_one]

omit [IsScalarTower k A A] in
/-- The two complementary idempotents are orthogonal: `c (conj c) = 0`. (Not a `simp` lemma:
`ConicAlgebra.mul_conj_self` already rewrites the left-hand side to `n(c) • 1`.) -/
theorem mul_conj (hc : C.IsElementaryIdempotent c) : c * C.conj c = 0 := by
  rw [ConicAlgebra.mul_conj_self, hc.norm_eq_zero, zero_smul]

omit [SMulCommClass k A A] in
/-- The two complementary idempotents are orthogonal: `(conj c) c = 0`. -/
theorem conj_mul (hc : C.IsElementaryIdempotent c) : C.conj c * c = 0 := by
  rw [ConicAlgebra.conj_mul_self, hc.norm_eq_zero, zero_smul]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- `c + conj c = 1`. -/
theorem add_conj_eq_one (hc : C.IsElementaryIdempotent c) : c + C.conj c = 1 := by
  rw [ConicAlgebra.add_conj, hc.trace_eq_one, one_smul]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **`(c, conj c)` is a hyperbolic pair**: both are null and `n(c, conj c) = 1`. This is what makes
the norm of a reduced algebra hyperbolic (`GPR 22.9(iv)`). -/
theorem polar_conj (hc : C.IsElementaryIdempotent c) :
    QuadraticMap.polar C.norm c (C.conj c) = 1 := by
  have h := C.norm_add c (C.conj c)
  rw [hc.add_conj_eq_one, C.norm_one, hc.norm_eq_zero, hc.conj.norm_eq_zero] at h
  simpa using h.symm

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **`(c, conj c)` is a hyperbolic pair of the norm**, in the sense of
`QuadraticMap.IsHyperbolicPair`. This is what connects a reduced algebra to the hyperbolic-form
machinery: by `QuadraticMap.IsHyperbolicPair.isometryEquivPlaneProd` the plane `k c ⊕ k (conj c)`
splits off the norm orthogonally. -/
theorem isHyperbolicPair (hc : C.IsElementaryIdempotent c) :
    QuadraticMap.IsHyperbolicPair C.norm c (C.conj c) where
  apply_left := hc.norm_eq_zero
  apply_right := hc.conj.norm_eq_zero
  polar_eq_one := hc.polar_conj

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- An elementary idempotent is **unimodular** (`GPR 9.13`): the trace is a functional taking the
value `1` on it. -/
theorem isUnimodular (hc : C.IsElementaryIdempotent c) : Module.IsUnimodular k c :=
  Module.isUnimodular_of_apply_eq_one (f := C.trace) hc.trace_eq_one

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- **`GPR 22.9`, (i) ⇒ (iii)**: an elementary idempotent is a unimodular null vector, so the norm
is isotropic in `GPR`'s sense. No hypotheses. -/
theorem isGPRIsotropic (hc : C.IsElementaryIdempotent c) : C.norm.IsGPRIsotropic :=
  ⟨c, hc.isUnimodular, hc.norm_eq_zero⟩

end IsElementaryIdempotent

/-- `C` **has an elementary idempotent**. For a composition algebra of rank `> 1` this is `GPR`'s
*reduced* (`GPR 22.6`, via `GPR 22.7`); in rank one the two conditions differ, which is why this
one carries its own name — see the module docstring. -/
def HasElementaryIdempotent (C : ConicAlgebra k A) : Prop := ∃ c : A, C.IsElementaryIdempotent c

/-! ### The split quadratic étale subalgebra `k c ⊕ k (conj c)` -/

variable (C : ConicAlgebra k A)

/-- The map `k × k → A`, `(a, b) ↦ a c + b (conj c)`, whose image is the subalgebra
`k c ⊕ k (conj c)` of `GPR 22.9`'s proof of (i) ⇒ (ii). It is unital, multiplicative and an
isometry from the split quadratic étale norm exactly when `c` is an elementary idempotent. -/
def elementaryIdempotentEmbedding (c : A) : (k × k) →ₗ[k] A :=
  (LinearMap.toSpanSingleton k A c).comp (LinearMap.fst k k k) +
    (LinearMap.toSpanSingleton k A (C.conj c)).comp (LinearMap.snd k k k)

variable {C}

omit [SMulCommClass k A A] [IsScalarTower k A A] in
@[simp] theorem elementaryIdempotentEmbedding_apply (c : A) (x : k × k) :
    C.elementaryIdempotentEmbedding c x = x.1 • c + x.2 • C.conj c := rfl

namespace IsElementaryIdempotent

variable {c : A} (hc : C.IsElementaryIdempotent c)
include hc

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The embedding is unital: `c + conj c = 1`. (Not a `simp` lemma:
`elementaryIdempotentEmbedding_apply` already rewrites the left-hand side.) -/
theorem elementaryIdempotentEmbedding_one :
    C.elementaryIdempotentEmbedding c 1 = 1 := by
  simpa using hc.add_conj_eq_one

theorem elementaryIdempotentEmbedding_mul (x y : k × k) :
    C.elementaryIdempotentEmbedding c (x * y) =
      C.elementaryIdempotentEmbedding c x * C.elementaryIdempotentEmbedding c y := by
  simp only [elementaryIdempotentEmbedding_apply, Prod.fst_mul, Prod.snd_mul, add_mul, mul_add,
    smul_mul_smul_comm, hc.mul_self, hc.conj.mul_self, hc.mul_conj, hc.conj_mul, smul_zero,
    add_zero, zero_add]

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The embedding carries the split quadratic étale norm `(a, b) ↦ ab` of `GPR 21.19(b)` to the
norm of `C`. -/
theorem norm_elementaryIdempotentEmbedding (x : k × k) :
    C.norm (C.elementaryIdempotentEmbedding c x) = QuadraticForm.plane k x := by
  rw [elementaryIdempotentEmbedding_apply, C.norm_add, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, hc.polar_conj, QuadraticMap.map_smul, QuadraticMap.map_smul,
    hc.norm_eq_zero, hc.conj.norm_eq_zero, QuadraticForm.plane_apply]
  simp

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The coefficient `a` is recovered from `a c + b (conj c)` by pairing with `conj c`, which is what
makes the embedding injective — with no regularity hypothesis on `C`. -/
theorem polar_elementaryIdempotentEmbedding_conj (x : k × k) :
    QuadraticMap.polar C.norm (C.elementaryIdempotentEmbedding c x) (C.conj c) = x.1 := by
  rw [elementaryIdempotentEmbedding_apply, QuadraticMap.polar_add_left,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, hc.polar_conj,
    QuadraticMap.polar_self, hc.conj.norm_eq_zero]
  ring

omit [SMulCommClass k A A] [IsScalarTower k A A] in
/-- The coefficient `b` is recovered from `a c + b (conj c)` by pairing with `c`. -/
theorem polar_elementaryIdempotentEmbedding_self (x : k × k) :
    QuadraticMap.polar C.norm (C.elementaryIdempotentEmbedding c x) c = x.2 := by
  have hcc : QuadraticMap.polar C.norm (C.conj c) c = 1 := by
    rw [QuadraticMap.polar_comm]; exact hc.polar_conj
  rw [elementaryIdempotentEmbedding_apply, QuadraticMap.polar_add_left,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_self, hcc,
    hc.norm_eq_zero]
  simp

omit [SMulCommClass k A A] [IsScalarTower k A A] in
theorem injective_elementaryIdempotentEmbedding :
    Function.Injective (C.elementaryIdempotentEmbedding c) := by
  intro x y hxy
  refine Prod.ext ?_ ?_
  · rw [← hc.polar_elementaryIdempotentEmbedding_conj x,
      ← hc.polar_elementaryIdempotentEmbedding_conj y, hxy]
  · rw [← hc.polar_elementaryIdempotentEmbedding_self x,
      ← hc.polar_elementaryIdempotentEmbedding_self y, hxy]

end IsElementaryIdempotent

/-- `C` **contains a split quadratic étale subalgebra** (`GPR 22.9`(ii)): there is an injective
`k`-linear map from `k × k` which preserves the unit and the multiplication and carries the split
quadratic étale norm of `GPR 21.19(b)` to the norm of `C`.

Presented as a map rather than as a submodule with induced structure: the map is the same data and
carries the norm along with it. -/
def HasSplitEtaleSubalgebra (C : ConicAlgebra k A) : Prop :=
  ∃ f : (k × k) →ₗ[k] A,
    Function.Injective f ∧ f 1 = 1 ∧ (∀ x y : k × k, f (x * y) = f x * f y) ∧
      ∀ x : k × k, C.norm (f x) = QuadraticForm.plane k x

/-- **`GPR 22.9`, (i) ⇔ (ii)**, in an arbitrary conic algebra: `C` has an elementary idempotent
if and only if it contains a split quadratic étale subalgebra.

Forwards, the subalgebra is `k c ⊕ k (conj c)`. Backwards, the image of `(1, 0)` is an elementary
idempotent: it has norm `1 * 0 = 0`, and its trace is `n(1, ·)` computed in `k × k`, namely
`1 * 0 + 1 * 1 = 1`. Neither direction uses regularity, projectivity, multiplicativity of the norm
of `C`, or any hypothesis on `2`. -/
theorem hasSplitEtaleSubalgebra_iff_hasElementaryIdempotent {C : ConicAlgebra k A} :
    C.HasSplitEtaleSubalgebra ↔ C.HasElementaryIdempotent := by
  constructor
  · rintro ⟨f, -, hf1, -, hfn⟩
    refine ⟨f (1, 0), ⟨by simpa using hfn (1, 0), ?_⟩⟩
    have hpolar : QuadraticMap.polar C.norm (f 1) (f (1, 0)) =
        QuadraticMap.polar (QuadraticForm.plane k) 1 (1, 0) := by
      rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hfn, hfn, hfn]
    rw [ConicAlgebra.trace_apply, ← hf1, hpolar, QuadraticForm.polar_plane_one]
    simp
  · rintro ⟨c, hc⟩
    exact ⟨C.elementaryIdempotentEmbedding c, hc.injective_elementaryIdempotentEmbedding,
      hc.elementaryIdempotentEmbedding_one, hc.elementaryIdempotentEmbedding_mul,
      hc.norm_elementaryIdempotentEmbedding⟩

/-! ### Isotropy produces an idempotent

This is the one implication of `GPR 22.9` with hypotheses, and they are exactly the two
`GPR`'s proof uses: the norm must be **regular** — so that a functional can be realized as
`n(v, ·)` — and it must be **multiplicative** — so that `n(uv) = n(u)n(v) = 0`. -/

omit [SMulCommClass k A A] in
/-- **`GPR 22.9`, (iii) ⇒ (i)**: a regular multiplicative norm with a unimodular null vector
produces an elementary idempotent.

Given a unimodular null `u`, unimodularity gives a functional `l` with `l(u) = 1`; precomposing
with the conjugation and inverting the polar map produces `v` with `n(v, conj u) = 1`.
Norm-associativity (`GPR 16.5`) turns that into `t(uv) = 1`, while multiplicativity gives
`n(uv) = n(u) n(v) = 0`. So `c = uv` is elementary. -/
theorem exists_isElementaryIdempotent_of_isGPRIsotropic {C : ConicAlgebra k A}
    (hreg : C.norm.IsGPRRegular) (hmul : C.IsMultiplicative)
    (hiso : C.norm.IsGPRIsotropic) : C.HasElementaryIdempotent := by
  obtain ⟨u, hu, hnu⟩ := hiso
  obtain ⟨l, hl⟩ := Module.isUnimodular_iff.mp hu
  obtain ⟨v, hv⟩ := hreg.2 (l.comp C.conj)
  refine ⟨u * v, ⟨by rw [hmul u v, hnu, zero_mul], ?_⟩⟩
  have hpolar : QuadraticMap.polar C.norm v (C.conj u) = 1 := by
    have := congrArg (fun f : Module.Dual k A ↦ f (C.conj u)) hv
    simpa [QuadraticMap.polarBilin_apply_apply, hl] using this
  rw [ConicAlgebra.trace_apply, QuadraticMap.polar_comm, hmul.polar_mul_left u v 1, mul_one,
    hpolar]

omit [SMulCommClass k A A] in
/-- **`GPR 22.9`, (i) ⇔ (iii)** for a regular multiplicative norm: `C` has an elementary
idempotent if and only if its norm is isotropic in `GPR`'s sense (a *unimodular* null vector,
overview §6(c)).

For a composition algebra of rank `> 1` the hypotheses are automatic: multiplicativity is part of
the definition, and regularity of the norm is `GPR 19.11`. -/
theorem hasElementaryIdempotent_iff_isGPRIsotropic {C : ConicAlgebra k A}
    (hreg : C.norm.IsGPRRegular) (hmul : C.IsMultiplicative) :
    C.HasElementaryIdempotent ↔ C.norm.IsGPRIsotropic :=
  ⟨fun ⟨_, hc⟩ ↦ hc.isGPRIsotropic,
    exists_isElementaryIdempotent_of_isGPRIsotropic hreg hmul⟩

/-- **`GPR 22.9`, (ii) ⇔ (iii)** for a regular multiplicative norm. -/
theorem hasSplitEtaleSubalgebra_iff_isGPRIsotropic {C : ConicAlgebra k A}
    (hreg : C.norm.IsGPRRegular) (hmul : C.IsMultiplicative) :
    C.HasSplitEtaleSubalgebra ↔ C.norm.IsGPRIsotropic :=
  hasSplitEtaleSubalgebra_iff_hasElementaryIdempotent.trans
    (hasElementaryIdempotent_iff_isGPRIsotropic hreg hmul)

/-! ### The norm splits off a hyperbolic plane

`GPR 22.9`(iv) says the norm of a reduced composition algebra is hyperbolic. What follows from the
pair `(c, conj c)` alone, with no Peirce decomposition and no hypothesis whatever on `C`, is that it
splits off *one* hyperbolic plane. `Composition/Reduced/Hyperbolic.lean` uses the Peirce
decomposition and regularity to identify the entire norm with a hyperbolic form. -/

/-- **Towards `GPR 22.9`(iv)**: an elementary idempotent splits a hyperbolic plane off the norm,

  `n ≅ ⟨plane⟩ ⊥ n|_{(k c ⊕ k (conj c))ᗮ}`.

The plane is `k c ⊕ k (conj c)`, and the restriction of `n` to it is regular by
`QuadraticMap.IsHyperbolicPair.isGPRRegular_comp_planeSubmodule_subtype` — so no regularity of `n`
itself, no projectivity, and no hypothesis on `2` is needed. The ingredients for full hyperbolicity
from `GPR Exc. 19.35` are developed in `Composition/Reduced/Peirce.lean`. -/
noncomputable def IsElementaryIdempotent.isometryEquivPlaneProd {C : ConicAlgebra k A} {c : A}
    (hc : C.IsElementaryIdempotent c) :
    ((QuadraticForm.plane k).prod (C.norm.comp (C.norm.polarOrthogonal
      (QuadraticMap.IsHyperbolicPair.planeSubmodule c (C.conj c))).subtype)).IsometryEquiv
      C.norm :=
  hc.isHyperbolicPair.isometryEquivPlaneProd

/-! ### The split algebras are reduced (`GPR 22.16`)

Each split model of `GPR 21.19` of rank `> 1` carries a visible elementary idempotent — the
"first diagonal entry" in each case. By `GPR 22.9` this makes each of their norms isotropic and
exhibits a split quadratic étale subalgebra in each. No hypothesis on the base ring. -/

section SplitModels

variable (k : Type u) [CommRing k]

/-- **`k × k` is reduced**: `(1, 0)` is an elementary idempotent. -/
theorem hasElementaryIdempotent_splitEtale : (splitEtale k).HasElementaryIdempotent :=
  ⟨(1, 0), ⟨by simp, by simp⟩⟩

/-- **`Mat₂(k)` is reduced**: the matrix unit `e₁₁` is an elementary idempotent — it has
determinant `0` and trace `1`. -/
theorem hasElementaryIdempotent_splitQuaternion :
    (splitQuaternion k).HasElementaryIdempotent :=
  ⟨!![1, 0; 0, 0], ⟨by simp, by simp [Matrix.trace_fin_two]⟩⟩

/-- **`Zor(k)` is reduced**: the Zorn vector matrix `[[1, 0], [0, 0]]` is an elementary
idempotent. -/
theorem hasElementaryIdempotent_zor : (zor k).HasElementaryIdempotent :=
  ⟨((1, 0), (0, 0)), ⟨(zorNorm_apply (((1, 0), (0, 0)) : Zor k)).trans (by simp),
    (trace_zor_apply (((1, 0), (0, 0)) : Zor k)).trans (by simp)⟩⟩

end SplitModels

end ConicAlgebra
