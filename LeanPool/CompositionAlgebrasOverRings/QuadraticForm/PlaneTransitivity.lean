/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Module.RankDecomposition
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Isotropic
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.PlaneCancellation
public import LeanPool.CompositionAlgebrasOverRings.QuadraticForm.Representation

/-!
# `Dias II.6.1`–`II.6.2`: transitivity on hyperbolic pairs

Not the Witt *extension* theorem — nothing here extends an isometry between submodules to the whole
module. What is proved is the single statement Witt cancellation needs: **the isometry group of
`plane ⊥ q` acts transitively on hyperbolic pairs**. `Dias II.6.1` is the step of it that uses the
LG axiom, and the only one in the whole chain that does.

Work in `plane ⊥ q₀` on `(R × R) × M₀`, with standard hyperbolic pair `u = ((1,0), 0)`,
`v = ((0,1), 0)`. A vector is `i = ((α, β), m)`, and applying the Siegel–Eichler transvection
`E(u, (0, y))` to it gives

  `E(u, (0, y)) i = ((α - b(y, m) - β * q₀ y, β), m + β • y)`,

so the `u`-coefficient changes from `α` to `α - b(y, m) - β·q₀(y)`. `Dias II.6.1` says that over an
LG ring one can choose `y` making that a **unit**, after which
`QuadraticMap.IsHyperbolicPair.exists_isometryEquiv_of_isUnit` finishes the job.

## The residue-field core

Over a field, with `q₀` non-singular, `α β + q₀ m = 0` (isotropy of `i`) and `α ≠ 0`, `β ≠ 0` or
`q₀(m, ·) ≠ 0` (a consequence of unimodularity of `i`), the value `α - b(y, m) - β q₀ y` is
nonzero for a suitable `y`:

* `α ≠ 0` — take `y = 0`;
* `α = 0` and `m ≠ 0` — then `q₀ m = 0`, so `m` is a nonzero isotropic vector and extends to a
  hyperbolic pair `(m, y)` (`exists_isHyperbolicPair_of_radical_eq_bot`); the value is `-1`;
* `α = 0` and `m = 0` — then `β ≠ 0` (the third disjunct is vacuous when `m = 0`), and any `y`
  with `q₀ y ≠ 0`
  (`QuadraticForm.exists_apply_ne_zero_of_radical_eq_bot`) gives the value `-β q₀ y`.

The last case needs `M₀ ⊗ κ(𝔪) ≠ 0` — Baeza's rank hypothesis in `Baeza III (2.3)`, Dias's
`V₀ ≠ 0`. Both sources assume it globally. Here it is needed only at those maximal ideals where
`α` is not *already* a unit, since where it is, `y = 0` works and the residue-field core is never
called. That is what lets the hypothesis be dispensed with entirely.

## The locus where `M₀` vanishes

Where `M₀ ⊗ κ(𝔪) = 0` the form `plane ⊥ q₀` reduces to the plane at `𝔪`, and there the hyperbolic
pair `(u, v)` and the pair `(β • v, β⁻¹ • u)` are exchanged by the **switch**, which is not a
product of transvections and dilations — it has the opposite Dickson invariant. No amount of
Eichler theory reaches it.

The locus is clopen: it is cut out by `Module.rankIdempotent R M₀ 0`
(`Module/RankDecomposition.lean`), which annihilates `M₀` and reduces to `1` on the locus. Rather
than splitting `R` into a product of rings, `QuadraticForm.switchIdem` performs the switch on the
locus and the identity off it — one isometry, defined over `R`. Applying it first makes the
`u`-coefficient a unit at exactly the maximal ideals where `M₀` dies, so `Dias II.6.1` can be run
with no hypothesis on the support of `M₀` at all.

## Main results

* `QuadraticForm.exists_ne_zero_sub_polar_sub_smul` : the residue-field core, above.
* `QuadraticForm.exists_isUnit_sub_polar_sub_smul` : **`Dias II.6.1`**, the LG step.
* `QuadraticForm.switchIdem` : the partial switch.
* `QuadraticForm.exists_isometryEquiv_of_isHyperbolicPair` : **`Dias II.6.2`** — the isometry group
  of `plane ⊥ q` is transitive on hyperbolic pairs.
* `QuadraticForm.isometryEquiv_of_isometryEquiv_plane_prod_of_isLGRing` : cancellation of one
  hyperbolic plane. `QuadraticForm/WittCancellation.lean` passes from this to `GN 6.5`.

## References

* I. Dias, *Formas Quadráticas Sobre LG-Anéis*, Ph.D. thesis, Universidade Estadual de Campinas,
  1988, II.6.1, II.6.2.
* R. Baeza, *Quadratic Forms over Semilocal Rings*, Lecture Notes in Math. **655**, Springer 1978,
  III, (2.3).
-/

@[expose] public section

universe u v v₁

namespace QuadraticForm

open _root_.QuadraticMap (polar polar_comm polar_zero_left polar_zero_right polar_comp_apply
  IsHyperbolicPair)

/-- **The residue-field core of `Dias II.6.1`.** Let `q` be a quadratic form with vanishing radical
on a nonzero vector space over a field, let `a * b + q w = 0`, and suppose one of `a`, `b`,
`q(w, ·)` is nonzero. Then some `y` makes `a - q(y, w) - b * q y` nonzero.

This is the value taken by the `u`-coefficient of `E(u, (0, y)) i` for `i = ((a, b), w)`; the three
cases are those listed in the module docstring. Non-singularity of `q` enters twice: to extend an
isotropic vector to a hyperbolic pair, and to guarantee that `q` is not identically zero. -/
theorem exists_ne_zero_sub_polar_sub_smul {F : Type u} [Field F] {W : Type v} [AddCommGroup W]
    [Module F W] [Nontrivial W] {q : QuadraticForm F W} (hq : q.radical = ⊥) {a b : F} {w : W}
    (hiso : a * b + q w = 0) (hnz : a ≠ 0 ∨ b ≠ 0 ∨ ∃ z : W, polar q w z ≠ 0) :
    ∃ y : W, a - polar q y w - b * q y ≠ 0 := by
  by_cases ha : a ≠ 0
  · exact ⟨0, by simpa using ha⟩
  push Not at ha
  subst ha
  have hqw : q w = 0 := by linear_combination hiso
  by_cases hw : w = 0
  · subst hw
    have hb : b ≠ 0 := by
      rcases hnz with h | h | ⟨z, hz⟩
      · exact absurd rfl h
      · exact h
      · exact absurd (QuadraticMap.polar_zero_left q z) hz
    obtain ⟨y, hy⟩ := q.exists_apply_ne_zero_of_radical_eq_bot hq
    refine ⟨y, ?_⟩
    simpa using mul_ne_zero hb hy
  · obtain ⟨y, hy⟩ := exists_isHyperbolicPair_of_radical_eq_bot hq hw hqw
    refine ⟨y, ?_⟩
    rw [polar_comm, hy.polar_eq_one, hy.apply_right]
    simp

/-! ### The polynomial of `Dias II.6.1`

The function `y ↦ α - b(y, m) - β * q y` is an inhomogeneous quadratic polynomial function. On a
free module it is computed by an explicit `MvPolynomial`, in the same way `GPR 11.8`
(`QuadraticForm.toMvPolynomial`) computes `q` itself: a constant term, a linear term from the polar
form, and `-β` times the polynomial of `q`. -/

section Polynomial

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M] {n : ℕ}

/-- The polar form evaluated on a finite linear combination. -/
theorem polar_sum_smul_left {S : Type*} [CommRing S] {P : Type*} [AddCommGroup P] [Module S P]
    {ι : Type*} [Fintype ι] (Q : QuadraticForm S P) (f : ι → S) (g : ι → P) (w : P) :
    polar Q (∑ i, f i • g i) w = ∑ i, f i * polar Q (g i) w := by
  simp only [← QuadraticMap.polarBilin_apply_apply]
  rw [map_sum]
  simp [LinearMap.sum_apply, smul_eq_mul]

variable (α β : R) (q : QuadraticForm R M) (m : M) (bm : Module.Basis (Fin n) R M)

/-- The polynomial computing `y ↦ α - b(y, m) - β * q y` in the basis `bm`. -/
noncomputable def eichlerMvPolynomial : MvPolynomial (Fin n) R :=
  MvPolynomial.C α - (∑ i, MvPolynomial.C (polar q (bm i) m) * MvPolynomial.X i) -
    MvPolynomial.C β * QuadraticForm.toMvPolynomial q bm

variable {α β q m bm}

/-- The defining property of `eichlerMvPolynomial`, over `R` itself. -/
theorem aeval_eichlerMvPolynomial_self (t : Fin n → R) :
    MvPolynomial.aeval t (eichlerMvPolynomial α β q m bm) =
      α - polar q (∑ i, t i • bm i) m - β * q (∑ i, t i • bm i) := by
  rw [eichlerMvPolynomial, map_sub, map_sub, map_mul, map_sum,
    QuadraticForm.aeval_toMvPolynomial_self, polar_sum_smul_left]
  simp only [MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_mul, Algebra.algebraMap_self_apply]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦ mul_comm (polar q (bm i) m) (t i)]

/-- The polar form of a base-changed form on a pair of pure tensors. -/
theorem polar_baseChangeOfProjective_tmul (S : Type*) [CommRing S] [Algebra R S]
    (Q : QuadraticForm R M) (x y : M) :
    polar (Q.baseChangeOfProjective S) ((1 : S) ⊗ₜ[R] x) ((1 : S) ⊗ₜ[R] y) =
      algebraMap R S (polar Q x y) := by
  have h := QuadraticForm.polarBilin_baseChangeOfProjective (A := S) Q
  have h2 := DFunLike.congr_fun (DFunLike.congr_fun h ((1 : S) ⊗ₜ[R] x)) ((1 : S) ⊗ₜ[R] y)
  simpa [Algebra.smul_def] using h2

/-- The defining property of `eichlerMvPolynomial` after base change: `GPR 11.8` for the
inhomogeneous polynomial. -/
theorem aeval_eichlerMvPolynomial (S : Type*) [CommRing S] [Algebra R S] (s : Fin n → S) :
    MvPolynomial.aeval s (eichlerMvPolynomial α β q m bm) =
      algebraMap R S α -
        polar (q.baseChangeOfProjective S) (∑ i, s i • ((1 : S) ⊗ₜ[R] bm i))
          ((1 : S) ⊗ₜ[R] m) -
        algebraMap R S β *
          (q.baseChangeOfProjective S) (∑ i, s i • ((1 : S) ⊗ₜ[R] bm i)) := by
  rw [eichlerMvPolynomial, map_sub, map_sub, map_mul, map_sum,
    QuadraticForm.aeval_toMvPolynomial, polar_sum_smul_left]
  simp only [MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_mul,
    polar_baseChangeOfProjective_tmul S q _ m]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) ↦
    mul_comm (algebraMap R S (polar q (bm i) m)) (s i)]

end Polynomial


/-! ### `Dias II.6.1` over an LG ring -/

section LG

open scoped TensorProduct

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **`Dias II.6.1`.** Over an LG ring, for `q` non-singular on a finitely generated projective
module, and `α β m` with `α β + q m = 0` whose reductions never vanish simultaneously, some `y`
makes `α - q(y, m) - β * q y` a **unit**.

Applied to `i = ((α, β), m)` in `plane ⊥ q`, this says the Siegel–Eichler transvection `E(u, (0,y))`
can be chosen to make the `u`-coefficient of `i` a unit — the hypothesis of
`QuadraticMap.IsHyperbolicPair.exists_isometryEquiv_of_isUnit`.

The LG axiom is applied to `QuadraticForm.eichlerMvPolynomial` written in the standard basis of a
presentation `Rⁿ ↠ M`; as in `QuadraticForm/Representation.lean`, pulling back along the
presentation is what removes any need for `M` to be free.

`hM` is what replaces Baeza's rank hypothesis and Dias's `V₀ ≠ 0`: `M` need only be nonzero at
those residue fields where `α` itself is not already a unit. Where it is, `y = 0` works and the
residue-field core is not called at all. Full support (`Module.HasFullSupport`) implies `hM`, but
is strictly stronger — it fails for `M = 0`, which the cancellation theorem has to cover. -/
theorem exists_isUnit_sub_polar_sub_smul (hLG : IsLGRing R) [Module.Finite R M]
    [Module.Projective R M] {q : QuadraticForm R M} (hq : q.IsGPRNonsingular.{u, v, u})
    {α β : R} {m : M} (hiso : α * β + q m = 0)
    (hnz : ∀ 𝔪 : Ideal R,
      𝔪.IsMaximal → α ∉ 𝔪 ∨ β ∉ 𝔪 ∨ ∃ n : M, polar q m n ∉ 𝔪)
    (hM : ∀ 𝔪 : Ideal R,
      𝔪.IsMaximal → α ∉ 𝔪 ∨ Nontrivial ((R ⧸ 𝔪) ⊗[R] M)) :
    ∃ y : M, IsUnit (α - polar q y m - β * q y) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨m', rfl⟩ := hπ m
  set bm : Module.Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n) with hbm
  set q' : QuadraticForm R (Fin n → R) := q.comp π with hq'
  have hrep : (eichlerMvPolynomial α β q' m' bm).RepresentsUnit R := by
    refine (hLG n _).mpr fun 𝔪 _ ↦ ?_
    let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    -- where `α` is already a unit, `y = 0` does the job and `M` is not needed at all
    rcases hM 𝔪 ‹_› with hα | hnt
    · refine ⟨0, ?_⟩
      rw [QuadraticForm.aeval_eichlerMvPolynomial]
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, polar_zero_left, map_zero,
        mul_zero, sub_zero]
      rw [Ideal.Quotient.algebraMap_eq]
      exact isUnit_iff_ne_zero.mpr fun hc ↦ hα (Ideal.Quotient.eq_zero_iff_mem.mp hc)
    have := hnt
    -- the residue-field witness
    have hisoF : algebraMap R (R ⧸ 𝔪) α * algebraMap R (R ⧸ 𝔪) β +
        (q.baseChangeOfProjective (R ⧸ 𝔪)) ((1 : R ⧸ 𝔪) ⊗ₜ[R] π m') = 0 := by
      rw [QuadraticForm.baseChangeOfProjective_tmul, mul_one, Algebra.smul_def, mul_one,
        ← map_mul, ← map_add, hiso, map_zero]
    have hnzF : algebraMap R (R ⧸ 𝔪) α ≠ 0 ∨ algebraMap R (R ⧸ 𝔪) β ≠ 0 ∨
        ∃ z : (R ⧸ 𝔪) ⊗[R] M,
          polar (q.baseChangeOfProjective (R ⧸ 𝔪))
            ((1 : R ⧸ 𝔪) ⊗ₜ[R] π m') z ≠ 0 := by
      have hmk : ∀ r : R, algebraMap R (R ⧸ 𝔪) r = 0 ↔ r ∈ 𝔪 := fun r ↦
        Ideal.Quotient.eq_zero_iff_mem
      rcases hnz 𝔪 ‹_› with h | h | ⟨n, hn⟩
      · exact Or.inl fun hc ↦ h ((hmk α).mp hc)
      · exact Or.inr (Or.inl fun hc ↦ h ((hmk β).mp hc))
      · refine Or.inr (Or.inr ⟨(1 : R ⧸ 𝔪) ⊗ₜ[R] n, ?_⟩)
        rw [QuadraticForm.polar_baseChangeOfProjective_tmul]
        exact fun hc ↦ hn ((hmk _).mp hc)
    obtain ⟨yF, hyF⟩ :=
      QuadraticForm.exists_ne_zero_sub_polar_sub_smul (hq (R ⧸ 𝔪)) hisoF hnzF
    obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective (R ⧸ 𝔪) hπ yF
    set b' := Algebra.TensorProduct.basis (R ⧸ 𝔪) bm with hb'
    refine ⟨fun i ↦ b'.repr x i, ?_⟩
    have hx : ∑ i, b'.repr x i • ((1 : R ⧸ 𝔪) ⊗ₜ[R] bm i) = x := by
      simpa [hb', Algebra.TensorProduct.basis_apply] using b'.sum_repr x
    rw [QuadraticForm.aeval_eichlerMvPolynomial, hx, hq',
      QuadraticForm.baseChangeOfProjective_comp, polar_comp_apply, QuadraticMap.comp_apply,
      LinearMap.baseChange_tmul]
    exact hyF.isUnit
  obtain ⟨t, ht⟩ := hrep
  rw [QuadraticForm.aeval_eichlerMvPolynomial_self] at ht
  have hsum : ∑ i, t i • bm i = t := by
    simpa [hbm] using (Pi.basisFun R (Fin n)).sum_repr t
  rw [hsum, hq', polar_comp_apply, QuadraticMap.comp_apply] at ht
  exact ⟨π t, ht⟩

end LG


/-! ### `Dias II.6.2` and cancellation of a plane -/

section Cancellation

open scoped TensorProduct

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-! #### The partial switch

The switch `(x, y) ↦ (y, x)` of the plane is an isometry that no product of transvections and
dilations can equal — it has the opposite Dickson invariant. An idempotent `ε` lets it be applied
on the clopen piece `D(ε)` of `Spec R` and not on the complement, still as a single global
isometry: `(x, y) ↦ (εy + (1-ε)x, εx + (1-ε)y)`. This is the one move outside the Eichler group
that the argument needs, and it is exactly what handles the locus where `M` vanishes. -/

/-- The **partial switch** of the plane: the switch on `D(ε)`, the identity on `D(1 - ε)`. -/
def switchIdemPlaneMap (ε : R) : (R × R) →ₗ[R] (R × R) :=
  LinearMap.prod (ε • LinearMap.snd R R R + (1 - ε) • LinearMap.fst R R R)
    (ε • LinearMap.fst R R R + (1 - ε) • LinearMap.snd R R R)

@[simp] theorem switchIdemPlaneMap_apply (ε : R) (x : R × R) :
    switchIdemPlaneMap ε x = (ε * x.2 + (1 - ε) * x.1, ε * x.1 + (1 - ε) * x.2) := rfl

/-- The partial switch of `plane ⊥ q`, acting on the plane and fixing `M`. -/
def switchIdemMap (ε : R) (M : Type v) [AddCommGroup M] [Module R M] :
    ((R × R) × M) →ₗ[R] ((R × R) × M) :=
  (switchIdemPlaneMap ε).prodMap LinearMap.id

@[simp] theorem switchIdemMap_apply (ε : R) (x : (R × R) × M) :
    switchIdemMap ε M x =
      ((ε * x.1.2 + (1 - ε) * x.1.1, ε * x.1.1 + (1 - ε) * x.1.2), x.2) := rfl

/-- The partial switch is an involution, because `ε` is idempotent. -/
theorem switchIdemMap_switchIdemMap {ε : R} (hε : IsIdempotentElem ε) (x : (R × R) × M) :
    switchIdemMap ε M (switchIdemMap ε M x) = x := by
  have hεε : ε * ε = ε := hε.eq
  refine Prod.ext (Prod.ext ?_ ?_) rfl <;> simp only [switchIdemMap_apply]
  · linear_combination (2 * (x.1.1 - x.1.2)) * hεε
  · linear_combination (2 * (x.1.2 - x.1.1)) * hεε

/-- The partial switch preserves `plane ⊥ q`: on the plane the product `x * y` is `ε` times the
switched product plus `1 - ε` times the original, and `ε(1 - ε) = 0`. -/
theorem apply_switchIdemMap {ε : R} (hε : IsIdempotentElem ε) (q : QuadraticForm R M)
    (x : (R × R) × M) : ((plane R).prod q) (switchIdemMap ε M x) = ((plane R).prod q) x := by
  have hεε : ε * ε = ε := hε.eq
  simp only [switchIdemMap_apply, QuadraticMap.prod_apply, plane_apply]
  linear_combination (-(x.1.1 - x.1.2) ^ 2) * hεε

/-- The **partial switch** as a self-isometry of `plane ⊥ q`. -/
noncomputable def switchIdem {ε : R} (hε : IsIdempotentElem ε) (q : QuadraticForm R M) :
    ((plane R).prod q).IsometryEquiv ((plane R).prod q) where
  __ := LinearEquiv.ofBijective (switchIdemMap ε M)
    (Function.bijective_iff_has_inverse.2
      ⟨switchIdemMap ε M, switchIdemMap_switchIdemMap hε, switchIdemMap_switchIdemMap hε⟩)
  map_app' := apply_switchIdemMap hε q

@[simp] theorem switchIdem_apply {ε : R} (hε : IsIdempotentElem ε) (q : QuadraticForm R M)
    (x : (R × R) × M) :
    switchIdem hε q x = ((ε * x.1.2 + (1 - ε) * x.1.1, ε * x.1.1 + (1 - ε) * x.1.2), x.2) := rfl

theorem switchIdem_switchIdem {ε : R} (hε : IsIdempotentElem ε) (q : QuadraticForm R M)
    (x : (R × R) × M) : switchIdem hε q (switchIdem hε q x) = x :=
  switchIdemMap_switchIdemMap hε x

/-- **`Dias II.6.2`, the case where the `u`-coefficient is a unit where `M` vanishes.** Over an LG
ring, if `q` is non-singular on a finitely generated projective module and `α` is a unit at every
residue field where `M` dies, then the hyperbolic pair `(((α, β), m), j)` is the image of the
standard one under a self-isometry.

The proof is `Dias II.6.1` (`exists_isUnit_sub_polar_sub_smul`) followed by the unit case
(`QuadraticMap.IsHyperbolicPair.exists_isometryEquiv_of_isUnit`): the transvection `E(u, (0, y))`
moves the given pair to one whose `u`-coefficient is a unit, and the unit case moves the standard
pair to *that*; composing with `E(u, (0, y))⁻¹` finishes.

`exists_isometryEquiv_of_isHyperbolicPair` removes the hypothesis `hM` by a partial switch. -/
theorem exists_isometryEquiv_of_isHyperbolicPair_of_notMem (hLG : IsLGRing R) [Module.Finite R M]
    [Module.Projective R M] {q : QuadraticForm R M} (hq : q.IsGPRNonsingular.{u, v, u})
    (α β : R) (m : M) (j : (R × R) × M)
    (hij : IsHyperbolicPair ((plane R).prod q) ((α, β), m) j)
    (hM : ∀ 𝔪 : Ideal R,
      𝔪.IsMaximal → α ∉ 𝔪 ∨ Nontrivial ((R ⧸ 𝔪) ⊗[R] M)) :
    ∃ σ : ((plane R).prod q).IsometryEquiv ((plane R).prod q),
      σ ((1, 0), 0) = ((α, β), m) ∧ σ ((0, 1), 0) = j := by
  set Q : QuadraticForm R ((R × R) × M) := (plane R).prod q with hQ
  have huv : IsHyperbolicPair Q ((1, 0), 0) ((0, 1), 0) := isHyperbolicPair_plane_prod q
  -- the coefficient of `i` is isotropic data
  have hiso : α * β + q m = 0 := by
    have := hij.apply_left
    rwa [hQ, QuadraticMap.prod_apply, plane_apply] at this
  -- unimodularity of `i`, read off from `q(i, j) = 1`
  have hnz : ∀ 𝔪 : Ideal R,
      𝔪.IsMaximal → α ∉ 𝔪 ∨ β ∉ 𝔪 ∨ ∃ n : M, polar q m n ∉ 𝔪 := by
    intro 𝔪 h𝔪
    by_cases hα : α ∈ 𝔪
    · by_cases hβ : β ∈ 𝔪
      · refine Or.inr (Or.inr ⟨j.2, fun hc ↦ h𝔪.ne_top ?_⟩)
        have hone := hij.polar_eq_one
        rw [hQ, QuadraticMap.polar_prod, polar_plane] at hone
        refine Ideal.eq_top_of_isUnit_mem 𝔪 ?_ isUnit_one
        rw [← hone]
        exact Ideal.add_mem _
          (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hα) (Ideal.mul_mem_right _ _ hβ)) hc
      · exact Or.inr (Or.inl hβ)
    · exact Or.inl hα
  obtain ⟨y, hy⟩ := QuadraticForm.exists_isUnit_sub_polar_sub_smul hLG hq hiso hnz hM
  obtain ⟨a, ha⟩ := hy
  -- the transvection `E(u, (0, y))`
  have hzu : polar Q (((1 : R), (0 : R)), (0 : M)) ((0, 0), y) = 0 := by
    rw [hQ, QuadraticMap.polar_prod, polar_plane]; simp
  set E := QuadraticMap.eichler huv.apply_left hzu with hE
  have hEi :
      E ((α, β), m) =
        ((0, 0), m + β • y) + (a : R) • ((1, 0), 0) + β • ((0, 1), 0) := by
    have hp₁ : polar Q ((1, 0), 0) ((α, β), m) = β := by
      rw [hQ, QuadraticMap.polar_prod, polar_plane]; simp
    have hp₂ : polar Q ((0, 0), y) ((α, β), m) = polar q y m := by
      rw [hQ, QuadraticMap.polar_prod, polar_plane]; simp
    have hp₃ : Q ((0, 0), y) = q y := by rw [hQ, QuadraticMap.prod_apply, plane_apply]; simp
    rw [hE, QuadraticMap.eichler_apply, hp₁, hp₂, hp₃]
    refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp
    linear_combination -ha
  obtain ⟨σ', hσ'u, hσ'v⟩ :=
    (huv.exists_isometryEquiv_of_isUnit (hij.map E) (a := a) (b := β)
      (z := ((0, 0), m + β • y))
      (by rw [hQ, QuadraticMap.polar_prod, polar_plane]; simp)
      (by rw [hQ, QuadraticMap.polar_prod, polar_plane]; simp)
      (by rw [← hEi]))
  refine ⟨σ'.trans E.symm, ?_, ?_⟩
  · change E.symm (σ' ((1, 0), 0)) = _
    rw [hσ'u, E.symm_apply_apply]
  · change E.symm (σ' ((0, 1), 0)) = _
    rw [hσ'v, E.symm_apply_apply]

/-- **`Dias II.6.2`.** Over an LG ring, if `q` is non-singular on a finitely generated projective
module, then every hyperbolic pair of `plane ⊥ q` is the image of the standard hyperbolic pair
under a self-isometry. **No hypothesis on the support of `M`.**

Where `M ⊗ κ(𝔪)` vanishes the plane is everything, and there the pair `(u, v)` reaches the pair
`(β • v, β⁻¹ • u)` only through the switch — not a product of transvections and dilations. The
partial switch `switchIdem` supplies exactly that, on exactly that locus: with
`ε₀ = Module.rankIdempotent R M 0` and `i = ((α, β), m)`, `j = ((γ, δ), n)`, the element

  `ε := ε₀ * (β * γ)`

is idempotent, because `ε₀` annihilates `M` and hence kills `q m`, `q n` and `q(m, n)`, leaving
`α β = 0`, `γ δ = 0`, `α δ + β γ = 1` — the relations that make `β γ` idempotent on the vanishing
locus. Applying `switchIdem ε` first turns the `u`-coefficient into `ε β + (1 - ε) α`, which is a
unit at every maximal ideal where `M` dies: there either `β γ` or `α δ` is `1`. That is the
hypothesis `exists_isometryEquiv_of_isHyperbolicPair_of_notMem` needs. -/
theorem exists_isometryEquiv_of_isHyperbolicPair (hLG : IsLGRing R) [Module.Finite R M]
    [Module.Projective R M] {q : QuadraticForm R M} (hq : q.IsGPRNonsingular.{u, v, u})
    (i j : (R × R) × M) (hij : IsHyperbolicPair ((plane R).prod q) i j) :
    ∃ σ : ((plane R).prod q).IsometryEquiv ((plane R).prod q),
      σ ((1, 0), 0) = i ∧ σ ((0, 1), 0) = j := by
  obtain ⟨⟨α, β⟩, m⟩ := i
  obtain ⟨⟨γ, δ⟩, n⟩ := j
  -- the three identities defining a hyperbolic pair, in coordinates
  have hi : α * β + q m = 0 := by
    have h := hij.apply_left; rwa [QuadraticMap.prod_apply, plane_apply] at h
  have hj : γ * δ + q n = 0 := by
    have h := hij.apply_right; rwa [QuadraticMap.prod_apply, plane_apply] at h
  have hone : α * δ + β * γ + polar q m n = 1 := by
    have h := hij.polar_eq_one; rwa [QuadraticMap.polar_prod, polar_plane] at h
  -- the rank-zero idempotent annihilates `M`, hence kills every value of `q` and of its polar
  set e := Module.rankIdempotent R M 0 with he
  have hee : e * e = e := (Module.isIdempotentElem_rankIdempotent R M 0).eq
  have hesmul : ∀ x : M, e • x = 0 := Module.rankIdempotent_zero_smul R M
  have heq : ∀ x : M, e * q x = 0 := fun x ↦ by
    have h := q.map_smul e x
    rw [hesmul x, QuadraticMap.map_zero, hee] at h
    exact h.symm
  have hepolar : ∀ x y : M, e * polar q x y = 0 := fun x y ↦ by
    have h := QuadraticMap.polar_smul_left (Q := q) e x y
    rw [hesmul x, polar_zero_left, smul_eq_mul] at h
    exact h.symm
  -- the idempotent cutting out the locus where the switch is needed
  set ε := e * (β * γ) with hεdef
  have hε : IsIdempotentElem ε := by
    change ε * ε = ε
    rw [hεdef]
    linear_combination (β * γ) ^ 2 * hee + (e * β * γ) * hone - (β * γ) * hepolar m n -
      (e * γ * δ) * hi + (e * q m) * hj - (q n) * heq m
  set S := switchIdem hε q with hS
  -- after the partial switch the `u`-coefficient is a unit wherever `M` dies
  have hM : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal →
      ε * β + (1 - ε) * α ∉ 𝔪 ∨ Nontrivial ((R ⧸ 𝔪) ⊗[R] M) := by
    intro 𝔪 h𝔪
    rcases subsingleton_or_nontrivial ((R ⧸ 𝔪) ⊗[R] M) with hsub | hnt
    swap
    · exact Or.inr hnt
    refine Or.inl ?_
    have hprime := h𝔪.isPrime
    -- `M` dies at `𝔪`, so `ε₀` is a unit there and `q(m, n) ∈ 𝔪`
    have hemem : e ∉ 𝔪 := Module.notMem_rankIdempotent_zero R M 𝔪 hsub
    have hp : polar q m n ∈ 𝔪 :=
      (hprime.mem_or_mem (hepolar m n ▸ 𝔪.zero_mem)).resolve_left hemem
    rcases hprime.mem_or_mem (show ε * (1 - ε) ∈ 𝔪 by
      rw [hε.mul_one_sub_self]; exact 𝔪.zero_mem) with hεm | hεm
    · -- `ε ≡ 0`: the coefficient is `α`, and `α δ = 1` at `𝔪`
      have hα : α ∉ 𝔪 := by
        intro hαmem
        refine h𝔪.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
        rw [← hone]
        exact 𝔪.add_mem (𝔪.add_mem (Ideal.mul_mem_right _ _ hαmem)
          ((hprime.mem_or_mem hεm).resolve_left hemem)) hp
      intro hc
      refine hα ?_
      rw [show α = ε * β + (1 - ε) * α - ε * β + ε * α by ring]
      exact 𝔪.add_mem (𝔪.sub_mem hc (Ideal.mul_mem_right _ _ hεm))
        (Ideal.mul_mem_right _ _ hεm)
    · -- `ε ≡ 1`: the coefficient is `β`, and `β γ = 1` at `𝔪`
      have hβ : β ∉ 𝔪 := by
        intro hβmem
        refine h𝔪.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
        have hεmem : ε ∈ 𝔪 :=
          hεdef ▸ Ideal.mul_mem_left _ e (Ideal.mul_mem_right _ _ hβmem)
        simpa using 𝔪.add_mem hεmem hεm
      intro hc
      refine hβ ?_
      rw [show β = ε * β + (1 - ε) * α + (1 - ε) * β - (1 - ε) * α by ring]
      exact 𝔪.sub_mem (𝔪.add_mem hc (Ideal.mul_mem_right _ _ hεm))
        (Ideal.mul_mem_right _ _ hεm)
  obtain ⟨σ', hσ'u, hσ'v⟩ := exists_isometryEquiv_of_isHyperbolicPair_of_notMem hLG hq
    (ε * β + (1 - ε) * α) (ε * α + (1 - ε) * β) m (S ((γ, δ), n)) (hij.map S) hM
  have hSi : S ((α, β), m) = ((ε * β + (1 - ε) * α, ε * α + (1 - ε) * β), m) := rfl
  refine ⟨σ'.trans S, ?_, ?_⟩
  · change S (σ' ((1, 0), 0)) = _
    rw [hσ'u, ← hSi, hS, switchIdem_switchIdem]
  · change S (σ' ((0, 1), 0)) = _
    rw [hσ'v, hS, switchIdem_switchIdem]

/-- **Cancellation of a hyperbolic plane over an LG ring.** For `q₂` non-singular on a finitely
generated projective module, `plane ⊥ q₁ ≅ plane ⊥ q₂` implies `q₁ ≅ q₂`.

This is `Dias II.6.4` for one plane: `Dias II.6.2` supplies the transitivity that
`QuadraticForm.isometryEquiv_of_isometryEquiv_plane_prod` consumes. Note `q₁` carries no
hypotheses at all, and `q₂` only non-singularity — in particular `M` may vanish, or vanish on
part of `Spec R`. -/
theorem isometryEquiv_of_isometryEquiv_plane_prod_of_isLGRing (hLG : IsLGRing R)
    {M₁ : Type v₁} [AddCommGroup M₁] [Module R M₁] [Module.Finite R M]
    [Module.Projective R M]
    {q₁ : QuadraticForm R M₁} {q₂ : QuadraticForm R M}
    (hq₂ : q₂.IsGPRNonsingular.{u, v, u})
    (h : Nonempty (((plane R).prod q₁).IsometryEquiv ((plane R).prod q₂))) :
    Nonempty (q₁.IsometryEquiv q₂) :=
  QuadraticForm.isometryEquiv_of_isometryEquiv_plane_prod
    (fun i j hij ↦ exists_isometryEquiv_of_isHyperbolicPair hLG hq₂ i j hij) h

end Cancellation

end QuadraticForm
