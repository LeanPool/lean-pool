/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import LeanPool.CompositionAlgebrasOverRings.Module.Unimodular
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Hyperbolic
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.HyperbolicPair
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Regularity

/-!
# GPR-sense isotropy

Defines `QuadraticMap.IsGPRIsotropic`: `Q` is isotropic iff it has a **unimodular** null vector
(`GPR 11.17`), not merely a nonzero one.

⚠ **This is not mathlib's `QuadraticMap.Anisotropic`.** `¬ Q.Anisotropic` unfolds to "there is a
*nonzero* `x` with `Q x = 0`". GPR's isotropy demands a *unimodular* null vector — strictly stronger
over a general ring, since unimodularity (mathlib's `Module.IsUnimodular`: some functional takes the
value `1` at `u`, equivalently `R·u` is a free rank-1 direct summand, `GPR 9.13`) asks
for more than `u ≠ 0`. The two notions coincide over a field, and `GPR Exc. 12.38(c)` shows they
also coincide for finitely generated projective (that is, finite free) modules over a PID (the
module hypothesis is needed: the zero form on the `ℤ`-module `ℤ/2` has a nonzero null vector but no
unimodular element); in general they do not, and the reduced-composition-algebra layer (`GPR 22.9`
ff.) needs the GPR notion specifically. See overview §6(c).

The name carries its source, as for the regularity ladder (`QuadraticForm.IsGPRNondegenerate`,
`IsGPRNonsingular`, `IsGPRRegular` in `QuadraticForm/Regularity.lean`): there is no bare
`IsIsotropic` here, precisely because "isotropic" means two different things in mathlib and in
`GPR` and a bare name would hide which one is meant.

## Main definitions

* `QuadraticMap.IsGPRIsotropic` : `Q` has a unimodular null vector.

## `GPR 11.17`: isotropic vectors extend to hyperbolic pairs

`GPR 11.17` proves that for a *quadratic space* — a **regular** form in the sense of
`QuadraticForm.IsGPRRegular` — a vector is isotropic exactly when it is the first member of a
hyperbolic pair. That is `QuadraticForm.isGPRIsotropic_iff_exists_isHyperbolicPair` below, with
`exists_isHyperbolicPair_of_isUnimodular` for the substantive direction: regularity solves
`l = q(·, w)` for the functional `l` witnessing unimodularity, and then `-q(w) • u + w` completes
`u` to a pair.

⚠ Over a field, **non-singularity is enough and regularity is not necessary**: a non-singular form
of odd rank in characteristic 2 is not regular (`QuadraticForm.rankOne`), yet its isotropic vectors
still extend. So `exists_isHyperbolicPair_of_radical_eq_bot` is *not* a special case of `GPR 11.17`;
it is the version the Witt-cancellation chain consumes at each residue field, where the forms being
cancelled are only assumed non-singular (`GN 6.5`, not `GPR 11.27`).

## Main results

* `QuadraticMap.IsGPRIsotropic.not_anisotropic` : over a nontrivial ring, GPR-isotropic implies
  not mathlib-anisotropic. (This is the direction that always holds.)
* `QuadraticMap.IsGPRIsotropic.map_isometryEquiv` : isotropy transports along an isometry
  equivalence.
* `QuadraticForm.isGPRIsotropic_dualProd` : the hyperbolic form `dualProd R M` is isotropic
  whenever `M` contains a unimodular element.
* `QuadraticMap.isGPRIsotropic_iff_not_anisotropic` : over a **field**, the two notions coincide —
  every nonzero vector is unimodular (`Module.isUnimodular_of_ne_zero`), so the extra strength GPR's
  definition carries over a general ring disappears entirely over a field.

`GPR Exc. 12.38(c)` — that the two notions already coincide for a finitely generated projective,
hence finite free, module over a **PID**, more generally than a field — is proved below by
generating the ideal of the coordinates of a nonzero vector. A generator divides every coordinate;
dividing by it gives a primitive, hence unimodular, vector. Homogeneity and the domain hypothesis
preserve the null-vector equation.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 9.13,
  11.17, Exc. 12.38, 22.19.
* [GN] Gille, Neher, *Group schemes over LG-rings…*, European Journal of Mathematics **11** (2025),
  article 42, 6.5.
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- `Q` is **isotropic** in the GPR sense: it has a *unimodular* null vector (`GPR 11.17`). -/
def QuadraticMap.IsGPRIsotropic (Q : QuadraticMap R M N) : Prop :=
  ∃ u : M, Module.IsUnimodular R u ∧ Q u = 0

namespace QuadraticMap.IsGPRIsotropic

/-- GPR-sense isotropy transports along an isometry equivalence. The null vector is carried by
the underlying linear equivalence, which also preserves unimodularity. -/
theorem map_isometryEquiv {Q₁ : QuadraticMap R M N} {M' : Type*} [AddCommGroup M'] [Module R M']
    {Q₂ : QuadraticMap R M' N} (h : Q₁.IsGPRIsotropic) (e : Q₁.IsometryEquiv Q₂) :
    Q₂.IsGPRIsotropic := by
  obtain ⟨u, hu, hQu⟩ := h
  exact ⟨e u, hu.map e.toLinearEquiv, by rw [e.map_app, hQu]⟩

theorem not_anisotropic [Nontrivial R] {Q : QuadraticMap R M N} (h : Q.IsGPRIsotropic) :
    ¬ Q.Anisotropic := by
  obtain ⟨u, hu, hQu⟩ := h
  intro hA
  obtain rfl := hA u hQu
  obtain ⟨l, hl⟩ := Module.isUnimodular_iff.mp hu
  rw [map_zero] at hl
  exact zero_ne_one hl

end QuadraticMap.IsGPRIsotropic

/-- Over a field, a not-anisotropic quadratic map is GPR-isotropic: the nonzero null vector mathlib
gives you is automatically unimodular. -/
theorem QuadraticMap.isGPRIsotropic_of_not_anisotropic {K : Type u} [Field K] {M : Type v}
    [AddCommGroup M] [Module K M] {N : Type w} [AddCommGroup N] [Module K N]
    {Q : QuadraticMap K M N} (h : ¬ Q.Anisotropic) : Q.IsGPRIsotropic := by
  obtain ⟨x, hx, hQx⟩ := (QuadraticMap.not_anisotropic_iff_exists Q).mp h
  exact ⟨x, Module.isUnimodular_of_ne_zero hx, hQx⟩

/-- Over a field, GPR-sense isotropy and mathlib's `¬ Anisotropic` are the same notion. -/
theorem QuadraticMap.isGPRIsotropic_iff_not_anisotropic {K : Type u} [Field K] {M : Type v}
    [AddCommGroup M] [Module K M] {N : Type w} [AddCommGroup N] [Module K N]
    {Q : QuadraticMap K M N} : Q.IsGPRIsotropic ↔ ¬ Q.Anisotropic :=
  ⟨fun h ↦ h.not_anisotropic, QuadraticMap.isGPRIsotropic_of_not_anisotropic⟩

/-! ### `GPR Exc. 12.38(c)`: isotropy over a PID -/

private theorem exists_smul_isUnimodular_of_ne_zero_of_pid
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    {x : M} (hx : x ≠ 0) :
    ∃ d : R, d ≠ 0 ∧ ∃ u : M, Module.IsUnimodular R u ∧ x = d • u := by
  classical
  let : Module.IsTorsionFree R M := inferInstance
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := M)
  let f : Fin n → R := fun i ↦ b.equivFun x i
  let I : Ideal R := Ideal.span (Set.range f)
  obtain ⟨d, hdI⟩ := (IsPrincipalIdealRing.principal I).principal
  have hdiv (i : Fin n) : d ∣ f i := by
    rw [← Ideal.mem_span_singleton]
    have hfi : f i ∈ I := Ideal.subset_span (Set.mem_range_self i)
    rwa [hdI] at hfi
  choose g hg using hdiv
  let u : M := b.equivFun.symm g
  have hxu : x = d • u := by
    apply b.equivFun.injective
    funext i
    simp only [map_smul, b.equivFun.apply_symm_apply, Pi.smul_apply, smul_eq_mul, u]
    change f i = d * g i
    exact hg i
  have hd : d ≠ 0 := by
    intro hd
    apply hx
    rw [hxu, hd, zero_smul]
  have hdmem : d ∈ Ideal.span (Set.range f) := by
    change d ∈ I
    rw [hdI]
    exact Ideal.mem_span_singleton_self d
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hdmem
  have hsum : ∑ i, g i * a i = 1 := by
    apply mul_left_cancel₀ hd
    calc
      d * (∑ i, g i * a i) = ∑ i, a i * f i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hg i]
        ring
      _ = d := ha
      _ = d * 1 := by rw [mul_one]
  let l : Module.Dual R M := b.constr R a
  have hlu : l u = 1 := by
    rw [Module.Basis.constr_apply_fintype]
    simp only [u, b.equivFun.apply_symm_apply, smul_eq_mul]
    exact hsum
  exact ⟨d, hd, u, Module.isUnimodular_of_apply_eq_one (f := l) hlu, hxu⟩

/-- **`GPR Exc. 12.38(c)`**, for quadratic forms and with its trivial converse: over a PID, a
quadratic form has a unimodular null vector if and only if it has a nonzero null vector. The module
is only assumed finitely generated projective, which over a PID means finite free. `GPR 22.19`
applies this to the norm of a composition algebra (its conditions (ii) and (iii)). -/
theorem QuadraticMap.isGPRIsotropic_iff_not_anisotropic_of_pid
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    {Q : QuadraticForm R M} : Q.IsGPRIsotropic ↔ ¬ Q.Anisotropic := by
  refine ⟨fun h ↦ h.not_anisotropic, fun h ↦ ?_⟩
  obtain ⟨x, hx, hQx⟩ := (QuadraticMap.not_anisotropic_iff_exists Q).mp h
  obtain ⟨d, hd, u, hu, hxu⟩ :=
    exists_smul_isUnimodular_of_ne_zero_of_pid (R := R) (M := M) hx
  refine ⟨u, hu, ?_⟩
  have hzero : d ^ 2 * Q u = 0 := by
    simpa only [hxu, QuadraticMap.map_smul, smul_eq_mul, pow_two] using hQx
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hd)

/-! ### `GPR 11.17`: isotropic vectors and hyperbolic pairs -/

namespace QuadraticForm

open _root_.QuadraticMap (polar polar_comm polar_smul_right IsHyperbolicPair
  isHyperbolicPair_neg_smul_add)

variable {Q : QuadraticForm R M}

/-- The hyperbolic form `dualProd R M` is GPR-isotropic as soon as `M` contains a unimodular
element `m`. The null vector is `(0, m)`; a functional taking `m` to `1` extends across the product
by the second projection. -/
theorem isGPRIsotropic_dualProd {m : M} (hm : Module.IsUnimodular R m) :
    (dualProd R M).IsGPRIsotropic := by
  obtain ⟨l, hl⟩ := Module.isUnimodular_iff.mp hm
  refine ⟨(0, m), Module.isUnimodular_of_apply_eq_one
    (f := l.comp (LinearMap.snd R (Module.Dual R M) M)) ?_, ?_⟩
  · simpa only [LinearMap.comp_apply, LinearMap.snd_apply] using hl
  · simp only [dualProd_apply, LinearMap.zero_apply]

/-- **`GPR 11.17`, `(i) ⇒ (ii)`.** In a **regular** quadratic module an isotropic vector — a
unimodular `u` with `q u = 0` — extends to a hyperbolic pair.

Regularity is used exactly once, to solve `l = q(·, w)` for the functional `l` with `l u = 1`
supplied by unimodularity (`GPR 9.13`); then `GPR`'s formula `v = -q(w) • u + w` finishes the job
(`QuadraticMap.isHyperbolicPair_neg_smul_add`). -/
theorem exists_isHyperbolicPair_of_isUnimodular (hQ : Q.IsGPRRegular) {u : M}
    (hu : Module.IsUnimodular R u) (hqu : Q u = 0) : ∃ v : M, IsHyperbolicPair Q u v := by
  obtain ⟨l, hl⟩ := Module.isUnimodular_iff.mp hu
  obtain ⟨w, hw⟩ := hQ.2 l
  have huw : polar Q u w = 1 := by
    have h := DFunLike.congr_fun hw u
    rw [QuadraticMap.polarBilin_apply_apply, hl] at h
    rw [polar_comm]
    exact h
  exact ⟨_, isHyperbolicPair_neg_smul_add hqu huw⟩

/-- **`GPR 11.17`, `(ii) ⇒ (i)`.** The first member of a hyperbolic pair is isotropic in the GPR
sense: it is unimodular, since `q(·, v)` sends it to `1`. No hypothesis on `Q`. -/
theorem isUnimodular_of_isHyperbolicPair {u v : M} (h : IsHyperbolicPair Q u v) :
    Module.IsUnimodular R u :=
  Module.isUnimodular_of_apply_eq_one (f := QuadraticMap.polarBilin Q v) <| by
    rw [QuadraticMap.polarBilin_apply_apply, polar_comm]
    exact h.polar_eq_one

/-- **`GPR 11.17`.** A regular quadratic module is isotropic in the GPR sense exactly when it
contains a hyperbolic pair. -/
theorem isGPRIsotropic_iff_exists_isHyperbolicPair (hQ : Q.IsGPRRegular) :
    Q.IsGPRIsotropic ↔ ∃ u v : M, IsHyperbolicPair Q u v := by
  constructor
  · rintro ⟨u, hu, hqu⟩
    obtain ⟨v, hv⟩ := exists_isHyperbolicPair_of_isUnimodular hQ hu hqu
    exact ⟨u, v, hv⟩
  · rintro ⟨u, v, huv⟩
    exact ⟨u, isUnimodular_of_isHyperbolicPair huv, huv.apply_left⟩

/-- **The non-singular analogue of `GPR 11.17` over a field.** A nonzero null vector of a form with
vanishing radical extends to a hyperbolic pair.

⚠ This is not an instance of `GPR 11.17`: over a field of characteristic 2 a non-singular form of
odd rank has a *degenerate* polar form, so it is not regular, and `GPR 11.17` does not apply. What
replaces regularity is that `u ∉ radical Q` while `Q u = 0`, which forces `q(u, ·) ≠ 0` directly.
This is the form of the statement that the Witt-cancellation chain uses at each residue field
(`Dias II.6.1`), where the forms being cancelled are only non-singular. -/
theorem exists_isHyperbolicPair_of_radical_eq_bot {F : Type*} [Field F] {V : Type*}
    [AddCommGroup V] [Module F V] {q : QuadraticForm F V} (hq : q.radical = ⊥) {u : V}
    (hu : u ≠ 0) (hqu : q u = 0) : ∃ v : V, IsHyperbolicPair q u v := by
  have hpol : ∃ x : V, polar q u x ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hu ?_
    have hmem : u ∈ q.radical :=
      ⟨hqu, LinearMap.ext fun x ↦ by rw [QuadraticMap.polarBilin_apply_apply, hc x,
        LinearMap.zero_apply]⟩
    rwa [hq, Submodule.mem_bot] at hmem
  obtain ⟨x, hx⟩ := hpol
  have huw : polar q u ((polar q u x)⁻¹ • x) = 1 := by
    rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hx]
  exact ⟨_, isHyperbolicPair_neg_smul_add hqu huw⟩

end QuadraticForm
