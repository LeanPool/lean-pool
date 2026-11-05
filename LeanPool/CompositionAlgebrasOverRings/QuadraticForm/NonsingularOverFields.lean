/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Non-singular quadratic forms over fields: `EKM Lemma 7.16` and `GPR Exercise 11.37`

Over a field, the base-change-stable regularity condition `QuadraticForm.IsGPRNonsingular` admits
a finite, checkable characterisation: `Q` is non-singular iff its radical vanishes *and* the
radical of its polar form is at most a line. That is `EKM Lemma 7.16`, and `GPR Exercise 11.37`
with one extra rung. This file proves both, and the part of `GPR Exc. 11.37`'s Remark (1) that
describes what the two cases look like.

## Relation to mathlib

Both mathlib notions from `Mathlib/LinearAlgebra/QuadraticForm/Radical.lean` are used directly;
this development defines no competing radical or non-degeneracy predicate.

* `QuadraticMap.radical` — the submodule of vectors on which both `Q` and its polar form vanish —
  is *the* radical throughout, including in `QuadraticForm/Regularity.lean`, where the whole
  regularity ladder (`IsGPRNondegenerate`, `IsGPRNonsingular`, `IsEKMNondegenerate`) is phrased
  as `radical … = ⊥`.
* `QuadraticMap.Nondegenerate` *is* `EKM`'s condition (3), taken as mathlib's definition. Our
  `QuadraticForm.IsEKMNondegenerate` formalizes `EKM`'s condition (1) instead, since that is the
  one that reads verbatim as a base-change statement, and `IsGPRNonsingular` is its ring-level
  generalisation, which mathlib has no name for. `EKM 7.16` is exactly the assertion that
  condition (1) and mathlib's predicate agree; that is
  `QuadraticForm.isEKMNondegenerate_iff_nondegenerate` below.

⚠ Do not read mathlib's `QuadraticMap.Nondegenerate` as GPR's "non-degenerate": it is strictly
stronger, and over a field it is GPR's **non-singular** rung. GPR's "non-degenerate" is the bare
`radical Q = ⊥`, i.e. `QuadraticForm.IsGPRNondegenerate`.

## Main results

* `QuadraticForm.finrank_le_one_of_anisotropic_of_isAlgClosed` : over an algebraically closed
  field an anisotropic quadratic form has dimension at most `1`. Proved in every characteristic
  by finding a root of `Q(e) t² + b(e, f) t + Q(f)`, so it applies in the characteristic-`2` case
  that mathlib's `QuadraticForm/AlgClosed.lean` (which assumes `Invertible (2 : K)`) does not
  cover.
* `QuadraticForm.finrank_ker_polarBilin_baseChangeOfProjective` : the radical of the polar form
  commutes with base change, hence has the same dimension. Flatness of `L` over `F`, via
  mathlib's `LinearMap.tensorKerEquiv`.
* `QuadraticForm.isGPRNonsingular_iff_nondegenerate`,
  `QuadraticForm.isEKMNondegenerate_iff_nondegenerate` : **`EKM Lemma 7.16`**, as the equivalence
  of conditions (1) and (3), and its restatement for `IsEKMNondegenerate`.
* `QuadraticForm.isGPRNonsingular_tfae` : **`GPR Exercise 11.37`**, all four conditions.
* `QuadraticForm.isGPRNonsingular_of_isAlgClosed` : `GPR Exc. 11.37` (iii) ⇒ (i) for an arbitrary
  algebraically closed `K`, which is what makes the "for some `K`" reading of (iii) legitimate.
* `QuadraticForm.isGPRRegular_xor_finrank_ker_polarBilin_eq_one`,
  `QuadraticForm.ringChar_eq_two_of_finrank_ker_polarBilin_eq_one`,
  `QuadraticForm.exists_isometryEquiv_rankOne_prod` : **`GPR Exc. 11.37`, Remark (1)** — see below.

## `GPR Exc. 11.37`, Remark (1), and what is missing

Remark (1) says that for finite-dimensional `V`, condition (ii) holds iff *exactly one* of

(a) `char F = 2`, `dim V` is odd, and `Q ≅ ⟨α⟩ ⊥ Q₀` with `Q₀` regular and `α ∈ Fˣ`;
(b) `Q` is regular

holds. Everything here is proved except **the parity clause "`dim V` is odd" in (a)**:

* the dichotomy — the polar radical of a non-degenerate form is either `0` (case (b)) or a line
  (case (a)), exclusively — is `isGPRRegular_xor_finrank_ker_polarBilin_eq_one`;
* `char F = 2` in case (a) is `ringChar_eq_two_of_finrank_ker_polarBilin_eq_one`;
* the decomposition in case (a) is `exists_isometryEquiv_rankOne_prod`, and needs no
  orthogonalisation: the generator `u` of the polar radical is orthogonal to everything already,
  so *any* complement of `F u` splits `Q` orthogonally.

The missing clause is not about quadratic forms at all. In characteristic `2` the polar form is
alternating, and "`dim V` odd" is the statement that an alternating bilinear form on a
finite-dimensional space has `dim V ≡ dim (rad b) (mod 2)` — equivalently that a non-degenerate
alternating form forces even dimension, the symplectic-basis theorem. mathlib has neither that
nor the Pfaffian, and proving it means the usual induction: split off a hyperbolic plane
`span {v, w}` with `b v w = 1`, pass to `{x | b v x = 0 ∧ b w x = 0}`, and induct. That is a
self-contained piece of bilinear algebra, better placed in a file of its own (or upstreamed)
than bolted on here. It is not attempted in this file.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-! ## Part A: isotropy over an algebraically closed field -/

section AlgClosed

variable {K : Type*} [Field K] [IsAlgClosed K]
  {W : Type*} [AddCommGroup W] [Module K W]

theorem QuadraticForm.exists_ne_zero_eq_zero_of_isAlgClosed (Q : QuadraticForm K W)
    {e f : W} (he : e ≠ 0) (hf : ∀ t : K, t • e + f ≠ 0) :
    ∃ w, w ≠ 0 ∧ Q w = 0 := by
  by_cases hQe : Q e = 0
  · exact ⟨e, he, hQe⟩
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_root
      (Polynomial.C (Q e) * Polynomial.X ^ 2
        + Polynomial.C (QuadraticMap.polar Q e f) * Polynomial.X + Polynomial.C (Q f))
      (by rw [Polynomial.degree_quadratic hQe]; decide)
    refine ⟨t • e + f, hf t, ?_⟩
    have hroot : Q e * t ^ 2 + QuadraticMap.polar Q e f * t + Q f = 0 := by
      simpa using ht
    rw [QuadraticMap.map_add (⇑Q) (t • e) f, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, smul_eq_mul, smul_eq_mul]
    rw [← hroot]; ring

theorem QuadraticForm.finrank_le_one_of_anisotropic_of_isAlgClosed [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : Q.Anisotropic) : Module.finrank K W ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  set b := Module.finBasis K W with hb
  set i₀ : Fin (Module.finrank K W) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (Module.finrank K W) := ⟨1, hlt⟩ with hi₁
  have hne : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  obtain ⟨x, hx, hQx⟩ := Q.exists_ne_zero_eq_zero_of_isAlgClosed (b.ne_zero i₀) (f := b i₁)
    (fun t ht ↦ by
      have := congrArg (fun y ↦ b.repr y i₁) ht
      simp [Module.Basis.repr_self, hne] at this)
  exact hx (hQ x hQx)

end AlgClosed

/-! ## Part B: base change of the radical of the polar form -/

section PolarKernel

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
  [Module.Finite F V] [Module.Projective F V]
  {L : Type*} [Field L] [Algebra F L]

/-- The polar form of a base-changed quadratic form has the same kernel as the base change of
the polar form as a plain linear map: the two differ by the dual-comparison isomorphism of
`GPR 9.15`, which is injective. -/
theorem QuadraticForm.ker_polarBilin_baseChangeOfProjective (Q : QuadraticForm F V) :
    LinearMap.ker (QuadraticMap.polarBilin (Q.baseChangeOfProjective L)) =
      LinearMap.ker (LinearMap.baseChange L
        (QuadraticMap.polarBilin Q : V →ₗ[F] Module.Dual F V)) := by
  rw [QuadraticForm.polarBilin_baseChangeOfProjective,
    LinearMap.BilinForm.baseChange_eq_comp_dualBaseChange]
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective
      (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := F) (M := V) (A := L)).injective)

/-- **The radical of the polar form is compatible with base change.** Its dimension is unchanged:
`L` is flat over the field `F`, so `L ⊗[F] ker b ≃ ker b_L` (`LinearMap.tensorKerEquiv`). -/
theorem QuadraticForm.finrank_ker_polarBilin_baseChangeOfProjective (Q : QuadraticForm F V) :
    Module.finrank L (LinearMap.ker (QuadraticMap.polarBilin (Q.baseChangeOfProjective L))) =
      Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) := by
  rw [QuadraticForm.ker_polarBilin_baseChangeOfProjective]
  have e : L ⊗[F] (LinearMap.ker (QuadraticMap.polarBilin Q)) ≃ₗ[L]
      LinearMap.ker (LinearMap.baseChange L
        (QuadraticMap.polarBilin Q : V →ₗ[F] Module.Dual F V)) :=
    LinearMap.tensorKerEquiv (R := F) L L _
  rw [← e.finrank_eq, Module.finrank_baseChange]

/-- A vector killed by the polar form stays killed after base change. -/
theorem QuadraticForm.one_tmul_mem_ker_polarBilin_baseChangeOfProjective (Q : QuadraticForm F V)
    {u : V} (hu : u ∈ LinearMap.ker (QuadraticMap.polarBilin Q)) :
    (1 : L) ⊗ₜ[F] u ∈
      LinearMap.ker (QuadraticMap.polarBilin (Q.baseChangeOfProjective L)) := by
  rw [QuadraticForm.ker_polarBilin_baseChangeOfProjective, LinearMap.mem_ker,
    LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hu, TensorProduct.tmul_zero]

end PolarKernel

/-! ## Part C: the two substantive implications -/

section TFAE

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

omit [FiniteDimensional F V] in
/-- A nonzero vector stays nonzero in `L ⊗[F] V`: apply a functional separating it from `0`. -/
theorem QuadraticForm.one_tmul_ne_zero {L : Type*} [Field L] [Algebra F L] {u : V} (hu : u ≠ 0) :
    (1 : L) ⊗ₜ[F] u ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F V, φ u ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hu ((Module.forall_dual_apply_eq_zero_iff F u).mp hcon)
  intro hzero
  have h1 := congrArg (TensorProduct.rid F L ∘ LinearMap.baseChange L φ) hzero
  simp only [Function.comp_apply, LinearMap.baseChange_tmul, TensorProduct.rid_tmul,
    map_zero] at h1
  exact hφ ((injective_iff_map_eq_zero _).mp (algebraMap F L).injective _
    (by simpa [Algebra.smul_def] using h1))

/-- **`EKM 7.16`, (3) ⇒ (1); `GPR Exc. 11.37`, (ii) ⇒ (i).** If the radical of `Q` vanishes and the
radical of its polar form has dimension at most `1`, then `Q` is non-singular.

If `dim (rad b_Q) = 0` the polar radical stays `0` after base change and there is nothing to
kill. If `dim (rad b_Q) = 1`, say `rad b_Q = F u`, then `Q u ≠ 0` (else `u` would lie in the
radical of `Q`), and after base change `rad b_{Q_L} = L (1 ⊗ u)`; an element `a ⊗ u` of the
radical of `Q_L` has `0 = Q_L (a ⊗ u) = Q(u) a²`, forcing `a = 0`. -/
theorem QuadraticForm.isGPRNonsingular_of_radical_eq_bot_of_finrank_ker_le_one
    (Q : QuadraticForm F V) (hrad : Q.radical = ⊥)
    (hdim : Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) ≤ 1) :
    Q.IsGPRNonsingular := by
  intro L _ _
  have : Module.Finite L (L ⊗[F] V) := Module.Finite.base_change F L V
  refine ((Q.baseChangeOfProjective L).radical.eq_bot_iff).mpr fun x hx ↦ ?_
  set QL := Q.baseChangeOfProjective L with hQL
  have hxker : x ∈ LinearMap.ker (QuadraticMap.polarBilin QL) := LinearMap.mem_ker.mpr hx.2
  have hdimL : Module.finrank L (LinearMap.ker (QuadraticMap.polarBilin QL)) ≤ 1 := by
    rw [hQL, QuadraticForm.finrank_ker_polarBilin_baseChangeOfProjective]; exact hdim
  rcases Nat.eq_zero_or_pos (Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)))
    with h0 | h1
  · -- The polar radical is already zero over `F`, hence over `L`.
    have : LinearMap.ker (QuadraticMap.polarBilin QL) = ⊥ := by
      rw [← Submodule.finrank_eq_zero, hQL,
        QuadraticForm.finrank_ker_polarBilin_baseChangeOfProjective]
      exact h0
    rw [this] at hxker
    simpa using hxker
  · -- The polar radical is a line `F u`, and `Q u ≠ 0`.
    have hone : Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) = 1 :=
      le_antisymm hdim h1
    obtain ⟨u, hu, hune⟩ : ∃ u ∈ LinearMap.ker (QuadraticMap.polarBilin Q), u ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      rw [(LinearMap.ker (QuadraticMap.polarBilin Q)).eq_bot_iff.mpr hcon,
        finrank_bot] at hone
      exact one_ne_zero hone.symm
    have hQu : Q u ≠ 0 := fun hQu0 ↦ hune (by
      have : u ∈ Q.radical := ⟨hQu0, LinearMap.mem_ker.mp hu⟩
      rwa [hrad, Submodule.mem_bot] at this)
    -- `rad b_{Q_L}` is the line spanned by `1 ⊗ u`.
    have htmul := Q.one_tmul_mem_ker_polarBilin_baseChangeOfProjective (L := L) hu
    have hspan : LinearMap.ker (QuadraticMap.polarBilin QL) = L ∙ ((1 : L) ⊗ₜ[F] u) := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · rw [Submodule.span_le, Set.singleton_subset_iff]; exact htmul
      · rw [finrank_span_singleton (QuadraticForm.one_tmul_ne_zero hune)]
        refine (le_antisymm hdimL ?_).symm
        rw [hQL, QuadraticForm.finrank_ker_polarBilin_baseChangeOfProjective, hone]
    rw [hspan, Submodule.mem_span_singleton] at hxker
    obtain ⟨a, rfl⟩ := hxker
    have hxa : a • ((1 : L) ⊗ₜ[F] u) = a ⊗ₜ[F] u := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hxa] at hx ⊢
    have hQ0 : QL (a ⊗ₜ[F] u) = 0 := hx.1
    rw [hQL, QuadraticForm.baseChangeOfProjective_tmul, Algebra.smul_def] at hQ0
    have ha : a = 0 := by
      rcases mul_eq_zero.mp hQ0 with h | h
      · exact absurd ((injective_iff_map_eq_zero _).mp (algebraMap F L).injective _ h) hQu
      · exact mul_self_eq_zero.mp h
    rw [ha, TensorProduct.zero_tmul]

/-- Half of **`EKM 7.16`, (2) ⇒ (3); `GPR Exc. 11.37`, (iii) ⇒ (ii)**: the radical of `Q` already
vanishes as soon as it vanishes after *one* base change, algebraically closed or not.
`(rad Q)_K ⊆ rad Q_K`, and `1 ⊗ u = 0` forces `u = 0`. -/
theorem QuadraticForm.radical_eq_bot_of_radical_baseChangeOfProjective_eq_bot
    {K : Type*} [Field K] [Algebra F K] (Q : QuadraticForm F V)
    (hK : (Q.baseChangeOfProjective K).radical = ⊥) : Q.radical = ⊥ := by
  rw [(Q.radical).eq_bot_iff]
  intro u hu
  have hmem : (1 : K) ⊗ₜ[F] u ∈ (Q.baseChangeOfProjective K).radical := by
    refine ⟨?_, ?_⟩
    · rw [QuadraticForm.baseChangeOfProjective_tmul, hu.1, zero_smul]
    · exact LinearMap.mem_ker.mp
        (Q.one_tmul_mem_ker_polarBilin_baseChangeOfProjective (L := K)
          (LinearMap.mem_ker.mpr hu.2))
  rw [hK, Submodule.mem_bot] at hmem
  by_contra hune
  exact QuadraticForm.one_tmul_ne_zero hune hmem

/-- The other half of **`EKM 7.16`, (2) ⇒ (3); `GPR Exc. 11.37`, (iii) ⇒ (ii)**: over an
algebraically closed `K`, vanishing of `rad Q_K` bounds the dimension of the polar radical by `1`.

`Q_K` restricted to `rad b_{Q_K}` is anisotropic — an isotropic vector there would lie in
`rad Q_K` — and over an algebraically closed field an anisotropic form has dimension at most one
(`QuadraticForm.finrank_le_one_of_anisotropic_of_isAlgClosed`). The dimension then descends to
`F` because the polar radical commutes with base change. -/
theorem QuadraticForm.finrank_ker_polarBilin_le_one_of_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K] [Algebra F K] (Q : QuadraticForm F V)
    (hK : (Q.baseChangeOfProjective K).radical = ⊥) :
    Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) ≤ 1 := by
  have : Module.Finite K (K ⊗[F] V) := Module.Finite.base_change F K V
  rw [← QuadraticForm.finrank_ker_polarBilin_baseChangeOfProjective (L := K) Q]
  refine QuadraticForm.finrank_le_one_of_anisotropic_of_isAlgClosed
    ((Q.baseChangeOfProjective K).comp
      (LinearMap.ker (QuadraticMap.polarBilin (Q.baseChangeOfProjective K))).subtype) ?_
  intro w hw
  have hmem : (w : K ⊗[F] V) ∈ (Q.baseChangeOfProjective K).radical :=
    ⟨hw, LinearMap.mem_ker.mp w.2⟩
  rw [hK, Submodule.mem_bot] at hmem
  exact Subtype.ext hmem

/-- **`GPR Exc. 11.37`, (iii) ⇒ (i).** A single algebraically closed base change suffices: if
`rad Q_K = 0` for one algebraically closed `K ⊇ F`, then `Q` is non-singular. -/
theorem QuadraticForm.isGPRNonsingular_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    [Algebra F K] (Q : QuadraticForm F V) (hK : (Q.baseChangeOfProjective K).radical = ⊥) :
    Q.IsGPRNonsingular :=
  Q.isGPRNonsingular_of_radical_eq_bot_of_finrank_ker_le_one
    (Q.radical_eq_bot_of_radical_baseChangeOfProjective_eq_bot hK)
    (Q.finrank_ker_polarBilin_le_one_of_isAlgClosed hK)

/-- **`EKM Lemma 7.16`, (1) ↔ (3); `GPR Exercise 11.37`, (i) ↔ (ii).** `Q` is non-singular
exactly when its radical vanishes and the radical of its polar form is at most a line.

The right-hand side is mathlib's `QuadraticMap.Nondegenerate`, which is `EKM`'s condition (3)
taken as the definition. So this identifies our base-change-stable `IsGPRNonsingular` — and
therefore `QuadraticForm.IsEKMNondegenerate` — with mathlib's predicate. -/
theorem QuadraticForm.isGPRNonsingular_iff_nondegenerate (Q : QuadraticForm F V) :
    Q.IsGPRNonsingular.{u, v, u} ↔ QuadraticMap.Nondegenerate (Q := Q) := by
  constructor
  · intro h
    have hK := h (AlgebraicClosure F)
    refine ⟨Q.radical_eq_bot_of_radical_baseChangeOfProjective_eq_bot hK, ?_⟩
    rw [← Module.finrank_eq_rank, Nat.cast_le_one]
    exact Q.finrank_ker_polarBilin_le_one_of_isAlgClosed hK
  · rintro ⟨h1, h2⟩
    refine Q.isGPRNonsingular_of_radical_eq_bot_of_finrank_ker_le_one h1 ?_
    rwa [← Module.finrank_eq_rank, Nat.cast_le_one] at h2

/-- **`EKM Definition 7.17` is mathlib's `QuadraticMap.Nondegenerate`.** `EKM` defines
non-degeneracy by condition (1) of `Lemma 7.16` — the reading `QuadraticForm.IsEKMNondegenerate`
formalizes — while mathlib takes condition (3). `EKM 7.16` says they agree. -/
theorem QuadraticForm.isEKMNondegenerate_iff_nondegenerate (Q : QuadraticForm F V) :
    QuadraticForm.IsEKMNondegenerate.{u, v, u} Q ↔ QuadraticMap.Nondegenerate (Q := Q) :=
  Q.isGPRNonsingular_iff_nondegenerate

/-- **`GPR Exercise 11.37`.** For a quadratic form over a field, on a finite-dimensional space,
the following are equivalent:

(i) `Q` is non-singular;
(ii) `Q` is non-degenerate and the radical of its polar form has dimension at most `1`;
(iii) `Q_K` is non-degenerate for *some* algebraically closed `K ⊇ F`;
(iv) `Q_K` is non-degenerate for *every* algebraically closed `K ⊇ F`.

Condition (ii) is `QuadraticMap.Nondegenerate`, so this is `EKM Lemma 7.16` with the extra
rung (iv). Condition (iii) is stated at the canonical choice `AlgebraicClosure F`; that this
really captures "some" is `QuadraticForm.isGPRNonsingular_of_isAlgClosed`, which accepts any
algebraically closed `K`. -/
theorem QuadraticForm.isGPRNonsingular_tfae (Q : QuadraticForm F V) :
    List.TFAE
      [Q.IsGPRNonsingular.{u, v, u},
        Q.radical = ⊥ ∧ Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) ≤ 1,
        (Q.baseChangeOfProjective (AlgebraicClosure F)).radical = ⊥,
        ∀ (K : Type u) [Field K] [Algebra F K] [IsAlgClosed K],
          (Q.baseChangeOfProjective K).radical = ⊥] := by
  tfae_have 1 → 4 := fun h K _ _ _ ↦ h K
  tfae_have 4 → 3 := fun h ↦ h (AlgebraicClosure F)
  tfae_have 3 → 2 := fun h ↦
    ⟨Q.radical_eq_bot_of_radical_baseChangeOfProjective_eq_bot h,
      Q.finrank_ker_polarBilin_le_one_of_isAlgClosed h⟩
  tfae_have 2 → 1 := fun h ↦
    Q.isGPRNonsingular_of_radical_eq_bot_of_finrank_ker_le_one h.1 h.2
  tfae_finish

end TFAE

/-! ## Part D: `GPR Exc. 11.37`, Remark (1) -/

section Remark

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- Over a finite-dimensional space regularity is exactly vanishing of the polar radical:
`polarBilin Q` is injective iff bijective, `V` and `Module.Dual F V` having equal dimension. -/
theorem QuadraticForm.isGPRRegular_iff_ker_polarBilin_eq_bot (Q : QuadraticForm F V) :
    Q.IsGPRRegular ↔ LinearMap.ker (QuadraticMap.polarBilin Q) = ⊥ := by
  constructor
  · exact fun h ↦ LinearMap.ker_eq_bot.mpr h.1
  · intro h
    have hinj := LinearMap.ker_eq_bot.mp h
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp hinj⟩

/-- Regularity in terms of the dimension of the polar radical. -/
theorem QuadraticForm.isGPRRegular_iff_finrank_ker_polarBilin_eq_zero (Q : QuadraticForm F V) :
    Q.IsGPRRegular ↔ Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) = 0 := by
  rw [QuadraticForm.isGPRRegular_iff_ker_polarBilin_eq_bot, ← Submodule.finrank_eq_zero]

/-- **Remark (1), the dichotomy.** For a non-degenerate `Q` on a finite-dimensional space, the
polar radical is either `0` — the regular case, (b) — or a line, case (a). The two are mutually
exclusive, so *exactly* one holds. -/
theorem QuadraticForm.isGPRRegular_xor_finrank_ker_polarBilin_eq_one (Q : QuadraticForm F V)
    (hnd : QuadraticMap.Nondegenerate (Q := Q)) :
    Xor Q.IsGPRRegular (Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) = 1) := by
  have hle : Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) ≤ 1 := by
    have := hnd.rank_rad_polar_le
    rwa [← Module.finrank_eq_rank, Nat.cast_le_one] at this
  rw [QuadraticForm.isGPRRegular_iff_finrank_ker_polarBilin_eq_zero]
  rcases Nat.lt_or_ge (Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q))) 1 with h | h
  · exact Or.inl ⟨Nat.lt_one_iff.mp h, by omega⟩
  · exact Or.inr ⟨le_antisymm hle h, by omega⟩

/-- **Remark (1), case (a) forces characteristic `2`.** If `2` is invertible then a non-degenerate
form is automatically regular, by `GN (C.8.2)`'s non-base-changed half
(`QuadraticForm.radical_eq_bot_iff_injective_polarBilin`): with `2` invertible the extra
`Q m = 0` clause in the radical is redundant, so `radical Q = ⊥` already says `polarBilin Q` is
injective. -/
theorem QuadraticForm.isGPRRegular_of_radical_eq_bot_of_invertible_two [Invertible (2 : F)]
    (Q : QuadraticForm F V) (hrad : Q.radical = ⊥) : Q.IsGPRRegular := by
  rw [QuadraticForm.isGPRRegular_iff_ker_polarBilin_eq_bot, LinearMap.ker_eq_bot]
  exact (QuadraticForm.radical_eq_bot_iff_injective_polarBilin Q).mp hrad

/-- **Remark (1), case (a) forces characteristic `2`**, stated as `(2 : F) = 0`. -/
theorem QuadraticForm.two_eq_zero_of_finrank_ker_polarBilin_eq_one (Q : QuadraticForm F V)
    (hrad : Q.radical = ⊥)
    (hdim : Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) = 1) :
    (2 : F) = 0 := by
  by_contra h2
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hreg := Q.isGPRRegular_of_radical_eq_bot_of_invertible_two hrad
  rw [QuadraticForm.isGPRRegular_iff_finrank_ker_polarBilin_eq_zero, hdim] at hreg
  exact one_ne_zero hreg

/-- The same conclusion as `ringChar F = 2`, matching `GPR`'s phrasing "char `F` = 2". -/
theorem QuadraticForm.ringChar_eq_two_of_finrank_ker_polarBilin_eq_one (Q : QuadraticForm F V)
    (hrad : Q.radical = ⊥)
    (hdim : Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) = 1) :
    ringChar F = 2 := by
  have h2 : ((2 : ℕ) : F) = 0 := by
    push_cast
    exact Q.two_eq_zero_of_finrank_ker_polarBilin_eq_one hrad hdim
  rcases (Nat.prime_two.eq_one_or_self_of_dvd _ (ringChar.dvd h2)) with h | h
  · exact absurd h (CharP.ringChar_ne_one)
  · exact h

/-- **Remark (1), case (a): the orthogonal decomposition `q = q₀ ⊥ ⟨α⟩`.**

If the polar radical of a non-degenerate `Q` is the line `F u`, then `α := Q u ≠ 0` and `Q` splits
as `⟨α⟩ ⊥ Q|W` for *any* complement `W` of `F u`, with `Q|W` regular.

No orthogonalisation is needed: `u` is in the radical of the polar form, so `polar Q u w = 0`
already holds for every `w`, making the decomposition orthogonal automatically. `Q|W` is regular
because a vector of `W` killed by `Q|W` is killed by all of `Q`'s polar form — it is orthogonal to
`u` for free — hence lies in `F u ⊓ W = 0`. -/
theorem QuadraticForm.exists_isometryEquiv_rankOne_prod (Q : QuadraticForm F V)
    (hrad : Q.radical = ⊥)
    (hdim : Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) = 1) :
    ∃ (W : Submodule F V) (α : F), α ≠ 0 ∧
      QuadraticForm.IsGPRRegular (Q.comp W.subtype) ∧
      Nonempty (QuadraticMap.IsometryEquiv
        (QuadraticMap.prod (QuadraticForm.rankOne α) (Q.comp W.subtype)) Q) := by
  -- A generator `u` of the polar radical, and `α = Q u ≠ 0`.
  obtain ⟨u, hu, hune⟩ : ∃ u ∈ LinearMap.ker (QuadraticMap.polarBilin Q), u ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    rw [(LinearMap.ker (QuadraticMap.polarBilin Q)).eq_bot_iff.mpr hcon, finrank_bot] at hdim
    exact zero_ne_one hdim
  have hpolar : ∀ w, QuadraticMap.polar Q u w = 0 := fun w ↦ by
    have h := DFunLike.congr_fun (LinearMap.mem_ker.mp hu) w
    rwa [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] at h
  have hQu : Q u ≠ 0 := fun h ↦ hune (by
    have : u ∈ Q.radical := ⟨h, LinearMap.mem_ker.mp hu⟩
    rwa [hrad, Submodule.mem_bot] at this)
  have hker : LinearMap.ker (QuadraticMap.polarBilin Q) = F ∙ u := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hu
    · rw [finrank_span_singleton hune, hdim]
  -- Any complement `W` of the line `F u` works.
  obtain ⟨W, hW⟩ := (F ∙ u).exists_isCompl
  have hinf : (F ∙ u) ⊓ W = ⊥ := hW.inf_eq_bot
  refine ⟨W, Q u, hQu, ?_, ?_⟩
  · -- `Q|W` is regular.
    rw [QuadraticForm.isGPRRegular_iff_ker_polarBilin_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have hwW : ∀ w' : W, QuadraticMap.polar Q w (w' : V) = 0 := fun w' ↦ by
      have h := DFunLike.congr_fun (LinearMap.mem_ker.mp hw) w'
      rwa [QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply] at h
    have hall : (w : V) ∈ LinearMap.ker (QuadraticMap.polarBilin Q) := by
      refine LinearMap.mem_ker.mpr (LinearMap.ext fun v ↦ ?_)
      obtain ⟨x, hx, y, hy, rfl⟩ :=
        Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top : v ∈ _)
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_right, QuadraticMap.polar_comm Q (w : V) u, hpolar,
        smul_zero, zero_add, hwW ⟨y, hy⟩, LinearMap.zero_apply]
    rw [hker] at hall
    have hbot : (w : V) ∈ (F ∙ u) ⊓ W := Submodule.mem_inf.mpr ⟨hall, w.2⟩
    rw [hinf, Submodule.mem_bot] at hbot
    exact Submodule.coe_eq_zero.mp hbot
  · -- The isometry `⟨α⟩ ⊥ Q|W ≃ Q`, via `(a, w) ↦ a • u + w`.
    set f : F × W →ₗ[F] V := (LinearMap.toSpanSingleton F V u).coprod W.subtype with hf
    have hbij : Function.Bijective f := by
      constructor
      · rw [injective_iff_map_eq_zero]
        rintro ⟨a, w⟩ hzero
        have hmem : a • u ∈ (F ∙ u) ⊓ W := by
          refine ⟨Submodule.mem_span_singleton.mpr ⟨a, rfl⟩, ?_⟩
          have : a • u = -(w : V) := by
            rw [eq_neg_iff_add_eq_zero]; simpa [hf, LinearMap.toSpanSingleton_apply] using hzero
          rw [this]
          exact Submodule.neg_mem _ w.2
        rw [hinf, Submodule.mem_bot] at hmem
        have hw : (w : V) = 0 := by
          have := hzero
          simp only [hf, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
            Submodule.coe_subtype, hmem, zero_add] at this
          exact this
        exact Prod.ext ((smul_eq_zero.mp hmem).resolve_right hune) (Submodule.coe_eq_zero.mp hw)
      · intro v
        obtain ⟨x, hx, y, hy, rfl⟩ :=
          Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top : v ∈ _)
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        exact ⟨(a, ⟨y, hy⟩), by simp [hf, LinearMap.toSpanSingleton_apply]⟩
    refine ⟨⟨LinearEquiv.ofBijective f hbij, ?_⟩⟩
    rintro ⟨a, w⟩
    change Q (f (a, w)) = _
    rw [hf]
    simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply, Submodule.coe_subtype,
      QuadraticMap.prod_apply, QuadraticForm.rankOne_apply, QuadraticMap.comp_apply]
    rw [QuadraticMap.map_add (⇑Q) (a • u) (w : V), QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, hpolar, smul_zero, add_zero, smul_eq_mul]
    ring

/-- **`GPR Exc. 11.37`, Remark (1)**, assembled — *except* for the parity clause "`dim V` is odd" in
case (a), which is not proved here (see the module docstring).

For a non-degenerate `Q` on a finite-dimensional space over a field, exactly one of:

(b) `Q` is regular; or
(a) the radical of the polar form is a line, `char F = 2`, and `Q ≅ ⟨α⟩ ⊥ Q₀` for some `α ≠ 0`
    and some regular `Q₀` on a complement of that line.

`GPR` states case (a) with "`dim V` is odd" in place of the clause "the polar radical is a line".
The two are equivalent given the parity theorem for alternating forms; the version here uses the
polar-radical clause, which is what actually drives the proof and what makes the dichotomy
exclusive. -/
theorem QuadraticForm.isGPRRegular_xor_charTwo_rankOne_decomposition (Q : QuadraticForm F V)
    (hnd : QuadraticMap.Nondegenerate (Q := Q)) :
    Xor Q.IsGPRRegular
      (Module.finrank F (LinearMap.ker (QuadraticMap.polarBilin Q)) = 1 ∧ ringChar F = 2 ∧
        ∃ (W : Submodule F V) (α : F), α ≠ 0 ∧
          QuadraticForm.IsGPRRegular (Q.comp W.subtype) ∧
          Nonempty (QuadraticMap.IsometryEquiv
            (QuadraticMap.prod (QuadraticForm.rankOne α) (Q.comp W.subtype)) Q)) := by
  rcases Q.isGPRRegular_xor_finrank_ker_polarBilin_eq_one hnd with
    ⟨hreg, hne⟩ | ⟨hone, hnreg⟩
  · exact Or.inl ⟨hreg, fun h ↦ hne h.1⟩
  · refine Or.inr ⟨⟨hone, Q.ringChar_eq_two_of_finrank_ker_polarBilin_eq_one hnd.1 hone,
      Q.exists_isometryEquiv_rankOne_prod hnd.1 hone⟩, hnreg⟩

end Remark
