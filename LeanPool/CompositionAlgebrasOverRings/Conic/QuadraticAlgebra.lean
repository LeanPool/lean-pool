/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Conic.Projective
public import LeanPool.CompositionAlgebrasOverRings.Module.Invertible
public import LeanPool.CompositionAlgebrasOverRings.Module.Unimodular
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Support

/-!
# Quadratic algebras are conic (`GPR 16.4`)

`GPR 16.4` calls a `k`-algebra **quadratic** if it is unital and projective of rank `2` as a
`k`-module, and shows that a quadratic algebra is conic. This file proves that, for a unital
algebra that is finitely generated projective of constant rank `2` over an arbitrary commutative
ring, with no hypothesis on `2`.

## The construction

`GPR` deduces conicness from the Cayley–Hamilton theorem, with norm `det(Lₓ)`; that needs a
determinant for projective modules. The argument here is global instead.

* **`1` is unimodular** (`ConicAlgebra.isUnimodular_one_of_rankAtStalk_ne_zero`, as in `GPR 16.4`).
  Otherwise every functional sends `1` into some maximal ideal `𝔪`, so `1 ∈ 𝔪 R`, hence `R = 𝔪 R`,
  and Nakayama makes `R` vanish at `𝔪` — but its rank there is `2`.
* So `R = k·1 ⊕ L` with `L` projective of rank one (`LinearMap.equivProdKerOfApplyEqOne`). For
  `a, b ∈ L` write `a b = ν(a, b)·1 + μ(a, b)` with `μ(a, b) ∈ L`.
* On a module of rank one every endomorphism is a scalar: with a finite dual basis `(fⱼ, lⱼ)` of
  `L`, put `α(a) = Σⱼ fⱼ(μ(a, lⱼ))`. The rank-one identity `φ(x) y = φ(y) x`
  (`Module.IsLocallyFreeRankOne.isRankOnePairing`) gives `μ(a, a) = α(a) a`.
* Then `n(λ·1 + a) = λ² + λ α(a) - ν(a, a)` is a quadratic form with `n(1) = 1`, its trace is
  `t(λ·1 + a) = 2λ + α(a)`, and `x² = t(x) x - n(x)·1`.

By `ConicAlgebra.norm_eq_of_projective` (`GPR 16.16`) the conic norm is then unique, so the
choice made here is immaterial.

## Main results

* `ConicAlgebra.isUnimodular_one_of_rankAtStalk_ne_zero` : `1` is unimodular in a unital finitely
  generated projective algebra whose rank vanishes nowhere.
* `ConicAlgebra.nonempty_of_rankAtStalk_eq_two` : **`GPR 16.4`**, a quadratic algebra carries a
  conic structure.
* `ConicAlgebra.ofRankTwo` : a chosen conic structure on a quadratic algebra; by `GPR 16.16` it is
  the only one.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 9.17, 16.4, 16.16.
-/

@[expose] public section

universe u v

namespace ConicAlgebra

variable {k : Type u} {R : Type v} [CommRing k] [NonAssocRing R] [Module k R]
  [SMulCommClass k R R] [IsScalarTower k R R] [Module.Finite k R] [Module.Projective k R]

omit [IsScalarTower k R R] in
/-- **`1` is unimodular** in a unital finitely generated projective algebra whose rank vanishes at
no prime (`GPR 16.4`, via `GPR 9.17`). If no functional takes `1` to a unit, the values at `1`
lie in a maximal ideal `𝔪`; the dual basis then puts `1`, and hence every `x = x · 1`, in `𝔪 R`,
and Nakayama kills `R` at `𝔪`. -/
theorem isUnimodular_one_of_rankAtStalk_ne_zero
    (hR : ∀ p : PrimeSpectrum k, Module.rankAtStalk (R := k) R p ≠ 0) :
    Module.IsUnimodular k (1 : R) := by
  let I : Ideal k := LinearMap.range (Module.Dual.eval k R 1)
  by_contra hne
  have hI : I ≠ ⊤ := fun h ↦ hne <| by
    obtain ⟨φ, hφ⟩ : (1 : k) ∈ I := h ▸ Submodule.mem_top
    exact Module.isUnimodular_of_apply_eq_one hφ
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs⟩ := ‹Module.Projective k R›.out
  -- The dual basis puts `1` in `𝔪 R`.
  have h1 : (1 : R) ∈ m • (⊤ : Submodule k R) := by
    rw [← hs 1, Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem_smul (hIm ⟨Finsupp.lapply j ∘ₗ s, rfl⟩) trivial
  -- Hence every `x = x · 1` is in `𝔪 R`.
  have htop : (⊤ : Submodule k R) ≤ m • ⊤ := fun x _ ↦ by
    have hx := Submodule.mem_map_of_mem (f := LinearMap.mulLeft k x) h1
    rw [Submodule.map_smul'', LinearMap.mulLeft_apply, mul_one] at hx
    exact Submodule.smul_mono le_rfl le_top hx
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
    (Module.finite_def.mp inferInstance) htop
  have hrm : r ∉ m := fun h ↦ hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by
    simpa using m.sub_mem h hr1))
  refine hR ⟨m, hm.isPrime⟩ ((Module.rankAtStalk_eq_zero_iff_notMem_support _).mpr ?_)
  rw [Module.mem_support_iff_of_finite]
  exact fun h ↦ hrm (h (Module.mem_annihilator.mpr fun x ↦ hr x trivial))

/-- **`GPR 16.4`: a quadratic algebra is conic.** A unital algebra that is finitely generated
projective of constant rank `2` over a commutative ring carries a conic structure. See the module
docstring for the construction: `R = k·1 ⊕ L` with `L` of rank one, and the norm of `λ·1 + a` is
`λ² + λ α(a) - ν(a, a)`, where `a² = ν(a, a)·1 + α(a) a`. -/
theorem nonempty_of_rankAtStalk_eq_two (hR : Module.rankAtStalk (R := k) R = fun _ ↦ 2) :
    Nonempty (ConicAlgebra k R) := by
  obtain ⟨l, hl⟩ := Module.isUnimodular_iff.mp
    (isUnimodular_one_of_rankAtStalk_ne_zero (R := R) fun p ↦ by rw [hR]; norm_num)
  -- The splitting `R = k·1 ⊕ L`.
  let L := LinearMap.ker l
  let π : R →ₗ[k] L :=
    (LinearMap.id - (LinearMap.toSpanSingleton k R 1) ∘ₗ l).codRestrict L fun x ↦
      LinearMap.mem_ker.mpr (by simp [LinearMap.toSpanSingleton_apply, hl])
  have hπ (x : R) : (π x : R) = x - l x • (1 : R) := by
    simp [π, LinearMap.toSpanSingleton_apply]
  have hdecomp (x : R) : x = l x • (1 : R) + (π x : R) := by rw [hπ]; abel
  have hπL (y : L) : π y = y := Subtype.ext (by
    rw [hπ, LinearMap.mem_ker.mp y.2, zero_smul, sub_zero])
  have hπ1 : π 1 = 0 := Subtype.ext (by rw [hπ, hl, one_smul, sub_self]; rfl)
  have : Module.Finite k L := Module.Finite.of_surjective π fun y ↦ ⟨y, hπL y⟩
  have : Module.Projective k L :=
    Module.Projective.of_split (M := R) L.subtype π (LinearMap.ext hπL)
  -- `L` has rank one.
  let e : R ≃ₗ[k] k × L := LinearMap.equivProdKerOfApplyEqOne l 1 hl
  have hLrank : Module.rankAtStalk (R := k) L = 1 := by
    funext p
    have : Nontrivial k := ⟨⟨0, 1, fun h ↦ p.isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr (h ▸ p.asIdeal.zero_mem))⟩⟩
    have h := congrFun hR p
    rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod, Pi.add_apply,
      Module.rankAtStalk_self, Pi.one_apply] at h
    rw [Pi.one_apply]
    omega
  -- On a module of rank one, `φ(x) y = φ(y) x`.
  have hpair := (show Module.IsLocallyFreeRankOne k L from
    ⟨inferInstance, inferInstance, hLrank⟩).isRankOnePairing
  have hrk (φ : Module.Dual k L) (x y : L) : φ x • y = φ y • x := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
    intro ψ
    rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hpair φ ψ x y, sub_self]
  -- A finite dual basis of `L`.
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' k L
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hexp (a : L) : a = ∑ j, g a j • f (Pi.single j 1) := by
    conv_lhs => rw [← LinearMap.id_apply (R := k) a, ← hg, LinearMap.comp_apply,
      pi_eq_sum_univ (g a)]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 2
    funext i
    simp [Pi.single_apply, eq_comm]
  -- The two components of multiplication on `L`, and the scalar `α`.
  let mulL : L →ₗ[k] L →ₗ[k] R := (LinearMap.mul k R).compl₁₂ L.subtype L.subtype
  let μ : L →ₗ[k] L →ₗ[k] L := mulL.compr₂ π
  let ν : L →ₗ[k] L →ₗ[k] k := mulL.compr₂ l
  have hmulL (a b : L) : (a : R) * b = ν a b • (1 : R) + (μ a b : R) := hdecomp _
  let α : L →ₗ[k] k := ∑ j, (LinearMap.proj j ∘ₗ g) ∘ₗ μ.flip (f (Pi.single j 1))
  have hμ (a : L) : μ a a = α a • a := by
    rw [show μ a a = μ a (∑ j, g a j • f (Pi.single j 1)) from congrArg (μ a) (hexp a)]
    simp only [map_sum, map_smul, α, LinearMap.sum_apply, Finset.sum_smul, LinearMap.comp_apply,
      LinearMap.flip_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact hrk (LinearMap.proj j ∘ₗ g) a (μ a (f (Pi.single j 1)))
  -- The norm.
  let B : LinearMap.BilinMap k R k :=
    (LinearMap.mul k k).compl₁₂ l l + (LinearMap.mul k k).compl₁₂ l (α ∘ₗ π) -
      ν.compl₁₂ π π
  have hB (x y : R) : B x y = l x * l y + l x * α (π y) - ν (π x) (π y) := rfl
  let N : QuadraticForm k R := B.toQuadraticMap
  have hN (x : R) : N x = l x * l x + l x * α (π x) - ν (π x) (π x) := rfl
  have hpolar (x : R) : QuadraticMap.polar N 1 x = 2 * l x + α (π x) := by
    rw [LinearMap.BilinMap.polar_toQuadraticMap, hB, hB, hπ1, hl]
    simp only [map_zero, LinearMap.zero_apply, mul_one, one_mul, mul_zero, sub_zero]
    ring
  refine ⟨{ norm := N, norm_one := ?_, mul_self := fun x ↦ ?_ }⟩
  · rw [hN, hπ1, hl]
    simp
  · rw [hpolar, hN]
    set c := l x
    set a := π x
    have hx : x = c • (1 : R) + (a : R) := hdecomp x
    rw [hx]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hmulL, hμ,
      Submodule.coe_smul]
    module

/-- A chosen conic structure on a quadratic algebra (`GPR 16.4`). By `GPR 16.16` it is the only
one (`ConicAlgebra.eq_ofRankTwo`). -/
noncomputable def ofRankTwo (hR : Module.rankAtStalk (R := k) R = fun _ ↦ 2) :
    ConicAlgebra k R :=
  Classical.choice (nonempty_of_rankAtStalk_eq_two hR)

/-- Every conic structure on a quadratic algebra is the chosen one: conic norms on a finitely
generated projective algebra are unique (`GPR 16.16`). -/
theorem eq_ofRankTwo (hR : Module.rankAtStalk (R := k) R = fun _ ↦ 2) (C : ConicAlgebra k R) :
    C = ofRankTwo hR :=
  ConicAlgebra.ext (norm_eq_of_projective C (ofRankTwo hR))

end ConicAlgebra
