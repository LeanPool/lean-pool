/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node ModularCurve.coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
(d98e6416-da3e-517f-9bda-a6513d150a13) by Claude (2026-09-05).

Proof based on Prove2Me submission 5ba11f28-d12e-5cbd-82f6-1c2dfb1f7451
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_AtkinLehner
public import Mathlib.Analysis.Complex.Periodic

import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_coeffMap_qExpand
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_coeffEmb_qExpand
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_PhiGen_exists_galoisPerm
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_PhiGen_mem_range_coeffEmb_qExpand_of_mem_inter
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_PhiGen_conj_injective
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_mem_range_qExpand_of_qTwist_eq
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_hasSum_jq_qParam
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_exists_perm_gamma0_cosetReps
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Fricke involution sends the ∞-expansion to the 0-expansion

Theorem statement: `ModularCurve.coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant`
(`d98e6416-da3e-517f-9bda-a6513d150a13`), by Claude, 2026-09-05.

Proof: submission `5ba11f28-d12e-5cbd-82f6-1c2dfb1f7451`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $\ell$ be a prime, let $f,g$ be Laurent series over $\mathbb{Q}$, and let
$F\colon\mathfrak{H}\to\mathbb{C}$ be a function on the upper half-plane. Assume: (hF) for every
$\tau$, the family $m\mapsto f_m\,q_1(\tau)^m$ indexed by $m\in\mathbb{Z}$, where $f_m$ is the
$m$-th coefficient of $f$ mapped into $\mathbb{C}$ and $q_h(\tau)=e^{2\pi i\tau/h}$ is Mathlib's
`Function.Periodic.qParam`, is summable with sum $F(\tau)$; (hG) for every $\tau$, the family
$m\mapsto g_m\,q_\ell(\tau)^m$ is summable with sum $F(S\cdot\tau)$, where $S$ is the standard
involution in $\mathrm{SL}_2(\mathbb{Z})$; (hinv) $F(\gamma\cdot\tau)=F(\tau)$ for all
$\gamma\in\Gamma_0(\ell)$ and all $\tau$; and (hf) $f$ lies in `modularFunctionFieldFull ℓ`, the
intermediate field of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set of series
$q\mapsto$ `qExpand ℚ d jq` for the nonzero divisors $d$ of $\ell$. The conclusion is that applying
`frickeInvolutionFull ℓ` to the element $\langle f,\mathrm{hf}\rangle$ and taking the underlying
Laurent series yields exactly $g$. Here `frickeInvolutionFull ℓ` is, by definition, a chosen
$\mathbb{Q}$-algebra automorphism $\sigma$ of `modularFunctionFieldFull ℓ` satisfying
`IsFrickeAutFull ℓ σ` — that is, $\sigma(\mathtt{qExpand}\ \mathbb{Q}\ a\
\mathtt{jq})=\mathtt{qExpand}\ \mathbb{Q}\ b\ \mathtt{jq}$ whenever $ab=\ell$ with $a,b$ nonzero —
if such a $\sigma$ exists, and the identity automorphism otherwise; existence for primes is supplied
by
[`ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime`]
(thm.html#ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime).

This is the $q$-expansion form of the statement that the Fricke involution $w_\ell$ on the function
field of $X_0(\ell)$ interchanges the cusps $\infty$ and $0$: a $\Gamma_0(\ell)$-invariant function
with expansion $f$ at $\infty$ (period $1$) and expansion $g$ at $0$ (period $\ell$) has
$w_\ell(f)=g$. It is used to identify the Fricke image of modular unit series and to place the
resulting series in the modular function field, via
[`ModularCurve.coe_frickeInvolutionFull_modularUnitSeries`]
(thm.html#ModularCurve.coe_frickeInvolutionFull_modularUnitSeries)
and
[`ModularCurve.sharpUnitSeries_mem_modularFunctionField`]
(thm.html#ModularCurve.sharpUnitSeries_mem_modularFunctionField).

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection


namespace P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective \
  qExpand_one_apply qExpand_qExpand jq jqN modularFunctionField jq_mem jqN_mem \
  modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full qTwist qTwist_coeff \
  qTwist_one_apply qTwist_qTwist qTwist_qExpand PhiGen.conj PhiGen.conj_zero PhiGen.conj_succ \
  coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff coeffMap_coeffEmb coeffMap_qExpand \
  coeffEmb_qExpand PhiGen.exists_galoisPerm PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq \
  PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter PhiGen.conj_injective \
  mem_range_qExpand_of_qTwist_eq hasSum_jq_qParam E4_cube_div_discriminant_smul \
  hasSum_qParam_mul_laurent hasSum_qParam_heckeMatrix_smul hasSum_qParam_heckeDiagMatrix_smul \
  mem_adjoin_jq_of_hasSum_of_slash_invariant exists_perm_gamma0_cosetReps \
  exists_sl2_heckeDiagMatrix_smul_eq laurent_qParam_coeff_unique IsFrickeAutFull \
  frickeInvolutionFull jq_mem_full isFrickeAutFull_frickeInvolutionFull_prime"
p2m_open "ModularCurve"

namespace QExpN

section Generic

variable {L L' : Type*} [CommRing L] [CommRing L'] {n : ℕ}

def interpPoly (H Y : Fin n → L) : L[X] :=
  ∑ i, C (H i) * ∏ m ∈ Finset.univ.erase i, (X - C (Y m))

def conjPoly (H : Fin n → L) : L[X] := ∏ i, (X - C (H i))

omit [CommRing L'] in
lemma prod_erase_perm (e : Equiv.Perm (Fin n)) (G : Fin n → L[X]) (i : Fin n) :
    ∏ m ∈ Finset.univ.erase i, G (e m) = ∏ m ∈ Finset.univ.erase (e i), G m := by
  refine Finset.prod_equiv e (fun m => ?_) (fun m _ => rfl)
  simp [e.injective.eq_iff]

lemma interpPoly_map (φ : L →+* L') (H Y : Fin n → L) :
    (interpPoly H Y).map φ = interpPoly (φ ∘ H) (φ ∘ Y) := by
  simp only [interpPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Function.comp_apply]

lemma conjPoly_map (φ : L →+* L') (H : Fin n → L) : (conjPoly H).map φ = conjPoly (φ ∘ H) := by
  simp only [conjPoly, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Function.comp_apply]

omit [CommRing L'] in
lemma interpPoly_perm (e : Equiv.Perm (Fin n)) (H Y : Fin n → L) :
    interpPoly (H ∘ e) (Y ∘ e) = interpPoly H Y := by
  unfold interpPoly
  simp only [Function.comp_apply]
  rw [← Equiv.sum_comp e (fun j => C (H j) * ∏ m ∈ Finset.univ.erase j, (X - C (Y m)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prod_erase_perm e (fun m => X - C (Y m)) i]

omit [CommRing L'] in
lemma conjPoly_perm (e : Equiv.Perm (Fin n)) (H : Fin n → L) : conjPoly (H ∘ e) = conjPoly H := by
  unfold conjPoly
  simp only [Function.comp_apply]
  exact Equiv.prod_comp e (fun j => X - C (H j))

omit [CommRing L'] in
lemma interpPoly_eval (H Y : Fin n → L) (i₀ : Fin n) :
    (interpPoly H Y).eval (Y i₀) = H i₀ * ∏ m ∈ Finset.univ.erase i₀, (Y i₀ - Y m) := by
  unfold interpPoly
  rw [Polynomial.eval_finsetSum, Finset.sum_eq_single i₀]
  · simp [Polynomial.eval_prod]
  · intro i _ hi
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := i₀) (by simp [Ne.symm hi]) ?_)
    simp
  · intro h; exact absurd (Finset.mem_univ i₀) h

omit [CommRing L'] in
lemma conjPoly_eval (H : Fin n → L) (i₀ : Fin n) : (conjPoly H).eval (H i₀) = 0 := by
  unfold conjPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp)

omit [CommRing L'] in
lemma conjPoly_monic (H : Fin n → L) : (conjPoly H).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (H i)

omit [CommRing L'] in
lemma conjPoly_natDegree [Nontrivial L] [NoZeroDivisors L] (H : Fin n → L) :
    (conjPoly H).natDegree = n := by
  unfold conjPoly
  rw [Polynomial.natDegree_prod _ _ fun i _ => Polynomial.X_sub_C_ne_zero (H i)]
  simp

lemma eval_eq_sum_coeff {p : L[X]} {N : ℕ} (hN : p.natDegree < N) (x : L) :
    p.eval x = ∑ k ∈ Finset.range N, p.coeff k * x ^ k := by
  rw [Polynomial.eval_eq_sum_range' hN]

end Generic

section Slots

variable {K : Type} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
  (hζ : IsPrimitiveRoot (ζ : K) ℓ)

def slotH (f g : LaurentSeries ℚ) : Fin (ℓ + 1) → LaurentSeries K :=
  Fin.cases (coeffEmb K (qExpand ℚ ℓ f)) (fun b : Fin ℓ => qTwist (ζ ^ (b : ℕ)) (coeffEmb K g))

@[scoped simp] lemma slotH_zero (f g : LaurentSeries ℚ) :
    slotH ℓ ζ f g 0 = coeffEmb K (qExpand ℚ ℓ f) := by
  simp [slotH]

@[scoped simp] lemma slotH_succ (f g : LaurentSeries ℚ) (b : Fin ℓ) :
    slotH ℓ ζ f g b.succ = qTwist (ζ ^ (b : ℕ)) (coeffEmb K g) := by
  simp [slotH]

def liftPerm (e : Equiv.Perm (Fin ℓ)) :
    Equiv.Perm (Fin (ℓ + 1)) := Equiv.Perm.decomposeFin.symm (0, e)

omit hℓ in
@[scoped simp] lemma liftPerm_zero (e : Equiv.Perm (Fin ℓ)) : liftPerm ℓ e 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero 0 e

omit hℓ in
@[scoped simp] lemma liftPerm_succ (e : Equiv.Perm (Fin ℓ)) (b : Fin ℓ) :
    liftPerm ℓ e b.succ = (e b).succ := by
  rw [liftPerm, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]

lemma coeffMap_qTwist {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (u : Rˣ)
    (x : LaurentSeries R) :
    coeffMap φ (qTwist u x) = qTwist (Units.map (φ : R →* S) u) (coeffMap φ x) := by
  ext k
  simp only [coeffMap_coeff, qTwist_coeff, map_mul]
  congr 1
  rw [← map_zpow (Units.map (φ : R →* S)) u k, Units.coe_map]
  rfl

omit hℓ [Algebra ℚ K] in
lemma units_map_zeta_pow (σ : K →+* K) (e : Equiv.Perm (Fin ℓ))
    (he : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ)) (b : Fin ℓ) :
    Units.map (σ : K →* K) (ζ ^ (b : ℕ)) = ζ ^ ((e b : Fin ℓ) : ℕ) := by
  ext
  rw [Units.coe_map, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  exact he b

lemma coeffMap_slotH (f g : LaurentSeries ℚ) (σ : K ≃ₐ[ℚ] K) (e : Equiv.Perm (Fin ℓ))
    (he : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ)) (i : Fin (ℓ + 1)) :
    coeffMap (σ : K →+* K) (slotH ℓ ζ f g i) = slotH ℓ ζ f g (liftPerm ℓ e i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [liftPerm_zero, slotH_zero, coeffMap_coeffEmb]
  · rw [liftPerm_succ, slotH_succ, slotH_succ, coeffMap_qTwist, coeffMap_coeffEmb,
      units_map_zeta_pow ℓ ζ (σ : K →+* K) e (fun b => he b) b]

lemma coeffMap_conj (σ : K ≃ₐ[ℚ] K) (e : Equiv.Perm (Fin ℓ))
    (he : ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ)) (i : Fin (ℓ + 1)) :
    coeffMap (σ : K →+* K) (PhiGen.conj ℓ ζ i) = PhiGen.conj ℓ ζ (liftPerm ℓ e i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [liftPerm_zero, PhiGen.conj_zero, coeffMap_qExpand, coeffMap_coeffEmb]
  · rw [liftPerm_succ, PhiGen.conj_succ, PhiGen.conj_succ, coeffMap_qTwist, coeffMap_coeffEmb,
      units_map_zeta_pow ℓ ζ (σ : K →+* K) e (fun b => he b) b]

include hζ in
omit hℓ [Algebra ℚ K] in
lemma zeta_pow_ell : ζ ^ ℓ = 1 := by
  ext; rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]

include hζ in
omit [Algebra ℚ K] in
lemma zeta_mul_zeta_pow (b : Fin ℓ) : ζ * ζ ^ (b : ℕ) = ζ ^ (((b + 1 : Fin ℓ)) : ℕ) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  rw [← pow_succ', Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  conv_lhs => rw [← Nat.div_add_mod ((b : ℕ) + 1) ℓ, pow_add, pow_mul, zeta_pow_ell ℓ ζ hζ, one_pow,
    one_mul]

include hζ in
lemma qTwist_slotH (f g : LaurentSeries ℚ) (i : Fin (ℓ + 1)) :
    qTwist ζ (slotH ℓ ζ f g i) = slotH ℓ ζ f g (liftPerm ℓ (Equiv.addRight (1 : Fin ℓ)) i) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [liftPerm_zero, slotH_zero, coeffEmb_qExpand, qTwist_qExpand, zpow_natCast, zeta_pow_ell ℓ ζ
      hζ,
      qTwist_one_apply]
  · rw [liftPerm_succ, slotH_succ, slotH_succ, qTwist_qTwist, Equiv.coe_addRight, zeta_mul_zeta_pow
      ℓ ζ hζ]

include hζ in
lemma qTwist_conj (i : Fin (ℓ + 1)) :
    qTwist ζ (PhiGen.conj ℓ ζ i) = PhiGen.conj ℓ ζ (liftPerm ℓ (Equiv.addRight (1 : Fin ℓ)) i) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine Fin.cases ?_ (fun b => ?_) i
  · rw [liftPerm_zero, PhiGen.conj_zero, qTwist_qExpand]
    congr 1
    rw [show ((ℓ * ℓ : ℕ) : ℤ) = ((ℓ * ℓ : ℕ) : ℤ) from rfl, zpow_natCast, pow_mul, zeta_pow_ell ℓ ζ
      hζ, one_pow,
      qTwist_one_apply]
  · rw [liftPerm_succ, PhiGen.conj_succ, PhiGen.conj_succ, qTwist_qTwist, Equiv.coe_addRight,
      zeta_mul_zeta_pow ℓ ζ hζ]

def interpK (f g : LaurentSeries ℚ) :
    (LaurentSeries K)[X] := interpPoly (slotH ℓ ζ f g) (PhiGen.conj ℓ ζ)

def conjK (f g : LaurentSeries ℚ) : (LaurentSeries K)[X] := conjPoly (slotH ℓ ζ f g)

variable [IsGalois ℚ K] [FiniteDimensional ℚ K]

include hζ in
theorem exists_interpK_coeff_eq (f g : LaurentSeries ℚ) (k : ℕ) :
    ∃ ξ : LaurentSeries ℚ, (interpK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ ξ) := by
  refine PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter ?_ ?_
  · refine mem_range_qExpand_of_qTwist_eq ℓ ζ hζ _ ?_
    rw [← Polynomial.coeff_map, interpK, interpPoly_map]
    have h1 : (⇑(qTwist ζ) ∘ slotH ℓ ζ f g) = slotH ℓ ζ f g ∘ liftPerm ℓ (Equiv.addRight (1 : Fin
      ℓ)) :=
      funext fun i => qTwist_slotH ℓ ζ hζ f g i
    have h2 : (⇑(qTwist ζ) ∘ PhiGen.conj ℓ ζ) = PhiGen.conj ℓ ζ ∘ liftPerm ℓ (Equiv.addRight (1 :
      Fin ℓ)) :=
      funext fun i => qTwist_conj ℓ ζ hζ i
    rw [h1, h2, interpPoly_perm]
  · refine PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq
      (fun c hc => (IsGalois.mem_range_algebraMap_iff_fixed c).mpr hc) fun σ => ?_
    obtain ⟨e, he⟩ := PhiGen.exists_galoisPerm hζ (σ : K →+* K)
    rw [← Polynomial.coeff_map, interpK, interpPoly_map]
    have h1 : (⇑(coeffMap (σ : K →+* K)) ∘ slotH ℓ ζ f g) = slotH ℓ ζ f g ∘ liftPerm ℓ e :=
      funext fun i => coeffMap_slotH ℓ ζ f g σ e he i
    have h2 : (⇑(coeffMap (σ : K →+* K)) ∘ PhiGen.conj ℓ ζ) = PhiGen.conj ℓ ζ ∘ liftPerm ℓ e :=
      funext fun i => coeffMap_conj ℓ ζ σ e he i
    rw [h1, h2, interpPoly_perm]

include hζ in
theorem exists_conjK_coeff_eq (f g : LaurentSeries ℚ) (k : ℕ) :
    ∃ π : LaurentSeries ℚ, (conjK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ π) := by
  refine PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter ?_ ?_
  · refine mem_range_qExpand_of_qTwist_eq ℓ ζ hζ _ ?_
    rw [← Polynomial.coeff_map, conjK, conjPoly_map]
    have h1 : (⇑(qTwist ζ) ∘ slotH ℓ ζ f g) = slotH ℓ ζ f g ∘ liftPerm ℓ (Equiv.addRight (1 : Fin
      ℓ)) :=
      funext fun i => qTwist_slotH ℓ ζ hζ f g i
    rw [h1, conjPoly_perm]
  · refine PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq
      (fun c hc => (IsGalois.mem_range_algebraMap_iff_fixed c).mpr hc) fun σ => ?_
    obtain ⟨e, he⟩ := PhiGen.exists_galoisPerm hζ (σ : K →+* K)
    rw [← Polynomial.coeff_map, conjK, conjPoly_map]
    have h1 : (⇑(coeffMap (σ : K →+* K)) ∘ slotH ℓ ζ f g) = slotH ℓ ζ f g ∘ liftPerm ℓ e :=
      funext fun i => coeffMap_slotH ℓ ζ f g σ e he i
    rw [h1, conjPoly_perm]

end Slots

def RealL (h : ℝ) (A : LaurentSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ)

namespace RealL

variable {h : ℝ} {A B : LaurentSeries ℂ} {F G : ℍ → ℂ}

lemma add (hA : RealL h A F) (hB : RealL h B G) : RealL h (A + B) (F + G) := fun τ => by
  simpa [add_mul] using (hA τ).add (hB τ)

lemma neg (hA : RealL h A F) : RealL h (-A) (-F) := fun τ => by
  simpa [neg_mul] using (hA τ).neg

lemma sub (hA : RealL h A F) (hB : RealL h B G) : RealL h (A - B) (F - G) := fun τ => by
  simpa [sub_mul] using (hA τ).sub (hB τ)

lemma mul (hh : 0 < h) (hA : RealL h A F) (hB : RealL h B G) : RealL h (A * B) (F * G) := fun τ =>
  hasSum_qParam_mul_laurent h hh A B F G hA hB τ

lemma single (h : ℝ) (a : ℂ) (n : ℤ) :
    RealL h (HahnSeries.single n a) (fun τ => a * 𝕢 h (τ : ℂ) ^ n) := fun τ => by
  refine (hasSum_ite_eq n (a * 𝕢 h (τ : ℂ) ^ n)).congr_fun fun m => ?_
  by_cases hm : m = n
  · subst hm; simp
  · simp [HahnSeries.coeff_single_of_ne hm, hm]

lemma C (h : ℝ) (a : ℂ) : RealL h (HahnSeries.C a) (fun _ => a) := by
  simpa using single h a 0

lemma one (h : ℝ) : RealL h 1 1 := by
  simpa [Pi.one_def] using C h 1

lemma zero (h : ℝ) : RealL h 0 0 := fun τ => by simp [hasSum_zero]

lemma congr {A' : LaurentSeries ℂ} {F' : ℍ → ℂ} (hA : RealL h A F) (h1 : A = A')
    (h2 : ∀ τ, F τ = F' τ) :
    RealL h A' F' := fun τ => by rw [← h1, ← h2]; exact hA τ

lemma sum {ι : Type} (s : Finset ι) {A : ι → LaurentSeries ℂ} {F : ι → ℍ → ℂ}
    (hAF : ∀ i ∈ s, RealL h (A i) (F i)) : RealL h (∑ i ∈ s, A i) (fun τ => ∑ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Pi.zero_def] using zero h
  | insert a s ha ih =>
    have h1 :=
      (hAF a (Finset.mem_insert_self a s)).add (ih fun i hi => hAF i (Finset.mem_insert_of_mem hi))
    refine h1.congr (Finset.sum_insert ha).symm fun τ => ?_
    simp [Finset.sum_insert ha]

lemma prod (hh : 0 < h) {ι : Type} (s : Finset ι) {A : ι → LaurentSeries ℂ} {F : ι → ℍ → ℂ}
    (hAF : ∀ i ∈ s, RealL h (A i) (F i)) : RealL h (∏ i ∈ s, A i) (fun τ => ∏ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Pi.one_def] using one h
  | insert a s ha ih =>
    have h1 :=
      (hAF a (Finset.mem_insert_self a s)).mul hh (ih fun i hi => hAF i (Finset.mem_insert_of_mem
        hi))
    refine h1.congr (Finset.prod_insert ha).symm fun τ => ?_
    simp [Finset.prod_insert ha]

lemma coeff_prod_X_sub_C (hh : 0 < h) {ι : Type} (s : Finset ι) {a : ι → LaurentSeries ℂ}
    {α : ι → ℍ → ℂ} (haα : ∀ i ∈ s, RealL h (a i) (α i)) (k : ℕ) :
    RealL h ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff k)
      (fun τ => (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))).coeff k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    by_cases hk : k = 0
    · subst hk; simpa [Pi.one_def] using one h
    · simpa [hk, Pi.zero_def] using zero h
  | insert b s hb ih =>
    have ih' := fun k => ih (fun i hi => haα i (Finset.mem_insert_of_mem hi)) k
    have hb' := haα b (Finset.mem_insert_self b s)
    have hA : (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (a i))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))) * (Polynomial.X - Polynomial.C (a b)) :=
      (Finset.prod_insert hb).trans (mul_comm (G := Polynomial (LaurentSeries ℂ)) _ _)
    have hfun : ∀ τ : ℍ, (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (α i τ))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))) * (Polynomial.X - Polynomial.C (α b τ)) :=
      fun τ => (Finset.prod_insert hb).trans (mul_comm (G := Polynomial ℂ) _ _)
    cases k with
    | zero =>
      refine ((ih' 0).mul hh hb').neg.congr ?_ fun τ => ?_
      · rw [hA, Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
          Polynomial.coeff_C_zero, zero_sub]
        exact (mul_neg (α := LaurentSeries ℂ) _ _).symm
      · simp only [hfun τ, Polynomial.mul_coeff_zero, Pi.neg_apply, Pi.mul_apply,
          Polynomial.coeff_sub,
          Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
    | succ k =>
      refine ((ih' k).sub ((ih' (k + 1)).mul hh hb')).congr ?_ fun τ => ?_
      · rw [hA, Polynomial.coeff_mul_X_sub_C]
      · simp only [hfun τ, Polynomial.coeff_mul_X_sub_C, Pi.sub_apply, Pi.mul_apply]

lemma interpPoly_coeff (hh : 0 < h) {n : ℕ} {Hs Ys : Fin n → LaurentSeries ℂ} {η υ : Fin n → ℍ → ℂ}
    (hH : ∀ i, RealL h (Hs i) (η i)) (hY : ∀ i, RealL h (Ys i) (υ i)) (k : ℕ) :
    RealL h ((interpPoly Hs Ys).coeff k)
      (fun τ => (interpPoly (fun i => η i τ) (fun i => υ i τ)).coeff k) := by
  unfold interpPoly
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      RealL h ((Polynomial.C (Hs i) * ∏ m ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (Ys
        m))).coeff k)
        (fun τ => (Polynomial.C (η i τ) *
          ∏ m ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (υ m τ))).coeff k) := by
    intro i _
    refine ((hH i).mul hh (coeff_prod_X_sub_C hh (Finset.univ.erase i) (fun m _ => hY m) k)).congr
      ?_ fun τ => ?_
    · rw [Polynomial.coeff_C_mul]
    · simp only [Pi.mul_apply, Polynomial.coeff_C_mul]
  refine (sum Finset.univ h1).congr ?_ fun τ => ?_
  · rw [Polynomial.finsetSum_coeff]
  · simp only [Polynomial.finsetSum_coeff]

lemma conjPoly_coeff (hh : 0 < h) {n : ℕ} {Hs : Fin n → LaurentSeries ℂ} {η : Fin n → ℍ → ℂ}
    (hH : ∀ i, RealL h (Hs i) (η i)) (k : ℕ) :
    RealL h ((conjPoly Hs).coeff k) (fun τ => (conjPoly fun i => η i τ).coeff k) :=
  coeff_prod_X_sub_C hh Finset.univ (fun i _ => hH i) k

end RealL

section Periods

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

lemma realL_one_of_realL_qExpand (x : LaurentSeries ℂ) (F : ℍ → ℂ) (hx : RealL ℓ (qExpand ℂ ℓ x) F)
    :
    RealL 1 x F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hℓ.out.ne_zero)
  have h := hx τ
  rw [← hinj.hasSum_iff] at h
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

lemma realL_qExpand_of_realL_one (x : LaurentSeries ℂ) (F : ℍ → ℂ) (hx : RealL 1 x F) :
    RealL ℓ (qExpand ℂ ℓ x) F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hℓ.out.ne_zero)
  rw [← hinj.hasSum_iff]
  · refine (hx τ).congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

def expRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / ℓ)

lemma isPrimitiveRoot_expRoot : IsPrimitiveRoot (expRoot ℓ) ℓ :=
  Complex.isPrimitiveRoot_exp ℓ hℓ.out.ne_zero

omit hℓ in
lemma expRoot_pow_zpow (b : ℕ) (m : ℤ) :
    (expRoot ℓ ^ b) ^ m = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
  rw [expRoot, ← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  congr 1
  ring

omit hℓ in
lemma qParam_T_pow_smul (b : ℕ) (τ : ℍ) :
    𝕢 ℓ (((ModularGroup.T ^ b • τ : ℍ)) : ℂ) = expRoot ℓ ^ b * 𝕢 ℓ (τ : ℂ) := by
  have h := modular_T_zpow_smul τ (b : ℤ)
  rw [zpow_natCast] at h
  rw [h, coe_vadd, expRoot, ← Complex.exp_nat_mul]
  simp only [Periodic.qParam, Complex.ofReal_natCast, Int.cast_natCast]
  rw [← Complex.exp_add]
  congr 1
  ring

omit hℓ in
lemma realL_twist (A : LaurentSeries ℂ) (G : ℍ → ℂ) (hA : RealL ℓ A G) (b : ℕ) (B : LaurentSeries ℂ)
    (hB : ∀ m : ℤ, B.coeff m = (expRoot ℓ ^ b) ^ m * A.coeff m) :
    RealL ℓ B (fun τ => G (ModularGroup.T ^ b • τ)) := by
  intro τ
  have h := hA (ModularGroup.T ^ b • τ)
  refine h.congr_fun fun m => ?_
  rw [hB m, qParam_T_pow_smul, mul_zpow]
  ring

end Periods

section Analytic

variable {K : Type} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
  (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* ℂ) (hσ : σ (ζ : K) = expRoot ℓ)

def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

def jtN (τ : ℍ) : ℂ := jt (ModularForm.heckeDiagMatrix ℓ • τ)

abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

omit hℓ in
lemma coeffMap_sigma_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap σ (coeffEmb K x) = coeffMap castC x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeffMap_coeff, eq_ratCast, map_ratCast]
  rfl

def cosetRep (i : Fin (ℓ + 1)) : SL(2, ℤ) :=
  Fin.cases (1 : SL(2, ℤ)) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i

omit hℓ in
@[scoped simp] lemma cosetRep_zero : cosetRep ℓ 0 = 1 := by simp [cosetRep]
omit hℓ in
@[scoped simp] lemma cosetRep_succ (b : Fin ℓ) :
    cosetRep ℓ b.succ = ModularGroup.S * ModularGroup.T ^ (b : ℕ) := by
  simp [cosetRep]

def slotF (F : ℍ → ℂ) (i : Fin (ℓ + 1)) (τ : ℍ) : ℂ := F (cosetRep ℓ i • τ)

def slotJ (i : Fin (ℓ + 1)) (τ : ℍ) : ℂ := jtN ℓ (cosetRep ℓ i • τ)

variable (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S •
    τ)))

include hF in
omit hℓ in
lemma realL_fC : RealL 1 (coeffMap castC f) F := fun τ => hF τ

include hG in
omit hℓ in
lemma realL_gC : RealL ℓ (coeffMap castC g) (fun τ => F (ModularGroup.S • τ)) := fun τ => hG τ

include hF hG hσ in
lemma realL_slotH (i : Fin (ℓ + 1)) :
    RealL ℓ (coeffMap σ (slotH ℓ ζ f g i)) (slotF ℓ F i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · have h := realL_qExpand_of_realL_one ℓ _ _ (realL_fC f F hF)
    refine h.congr ?_ fun τ => ?_
    · rw [slotH_zero, coeffMap_sigma_coeffEmb, coeffMap_qExpand]
    · simp [slotF]
  · have h :=
      realL_twist ℓ _ _ (realL_gC ℓ g F hG) (b : ℕ) (coeffMap σ (slotH ℓ ζ f g b.succ)) fun m => by
      rw [slotH_succ, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀,
        Units.val_pow_eq_pow_val, map_pow, hσ, coeffEmb_coeff, eq_ratCast, map_ratCast,
        coeffMap_coeff]
      rfl
    refine h.congr rfl fun τ => ?_
    simp only [slotF, cosetRep_succ, mul_smul]

lemma coeffMap_conj_zero_eq :
    coeffMap σ (PhiGen.conj ℓ ζ 0) = qExpand ℂ (ℓ * ℓ) (coeffMap castC jq) := by
  rw [PhiGen.conj_zero, coeffMap_qExpand, coeffMap_sigma_coeffEmb]

omit hℓ in
lemma realL_jqC : RealL 1 (coeffMap castC jq) jt := fun τ => hasSum_jq_qParam τ

omit hℓ in
lemma heckeDiag_smul_S_T_pow_smul [NeZero ℓ] (b : ℕ) (τ : ℍ) :
    ModularForm.heckeDiagMatrix ℓ • (ModularGroup.S * ModularGroup.T ^ b) • τ =
      ModularGroup.S • ModularForm.heckeMatrix ℓ b • τ := by
  have hT : ((ModularGroup.T ^ b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (b : ℤ); 0, 1] :=
    by
    have := ModularGroup.coe_T_zpow (b : ℤ)
    rwa [zpow_natCast] at this
  set g : SL(2, ℤ) := ModularGroup.S * ModularGroup.T ^ b with hg
  have hg' : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, (b : ℤ)] := by
    rw [hg, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, hT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h00 : g 0 0 = 0 := congrFun (congrFun hg' 0) 0
  have h01 : g 0 1 = -1 := congrFun (congrFun hg' 0) 1
  have h10 : g 1 0 = 1 := congrFun (congrFun hg' 1) 0
  have h11 : g 1 1 = b := congrFun (congrFun hg' 1) 1
  clear_value g
  have hmat : ModularForm.heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ g =
      Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeMatrix ℓ b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ),
        ModularForm.val_heckeMatrix (NeZero.ne ℓ), ModularGroup.coe_S, h00, h01, h10, h11]
  have h1 : ModularForm.heckeDiagMatrix ℓ • g • τ =
      (ModularForm.heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ g) • τ := by
    rw [mul_smul]; rfl
  have h2 : ModularGroup.S • ModularForm.heckeMatrix ℓ b • τ =
      (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeMatrix ℓ b) • τ := by
    rw [mul_smul]; rfl
  rw [h1, h2, hmat]

include hσ in
lemma realL_conj (i : Fin (ℓ + 1)) : RealL ℓ (coeffMap σ (PhiGen.conj ℓ ζ i)) (slotJ ℓ i) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  refine Fin.cases ?_ (fun b => ?_) i
  · intro τ
    have h := hasSum_qParam_heckeDiagMatrix_smul ℓ (coeffMap castC jq) jt realL_jqC τ
    rw [coeffMap_conj_zero_eq]
    simpa [slotJ, jtN] using h
  · intro τ
    have h := hasSum_qParam_heckeMatrix_smul ℓ (b : ℕ) (coeffMap castC jq) jt realL_jqC τ
    have hval : slotJ ℓ b.succ τ = jt (ModularForm.heckeMatrix ℓ (b : ℕ) • τ) := by
      rw [slotJ, jtN, cosetRep_succ, heckeDiag_smul_S_T_pow_smul]
      exact E4_cube_div_discriminant_smul ModularGroup.S _
    rw [hval]
    refine h.congr_fun fun m => ?_
    congr 1
    rw [PhiGen.conj_succ, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val,
      map_zpow₀,
      Units.val_pow_eq_pow_val, map_pow, hσ, expRoot_pow_zpow, coeffEmb_coeff, eq_ratCast,
      map_ratCast,
      coeffMap_coeff]
    rfl

def interpFun (k : ℕ) (τ : ℍ) :
    ℂ := (interpPoly (fun i => slotF ℓ F i τ) (fun i => slotJ ℓ i τ)).coeff k

def conjFun (k : ℕ) (τ : ℍ) : ℂ := (conjPoly fun i => slotF ℓ F i τ).coeff k

variable (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

omit hℓ in
lemma jtN_smul [NeZero ℓ] (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 ℓ) (τ : ℍ) :
    jtN ℓ (γ • τ) = jtN ℓ τ := by
  obtain ⟨γ', hγ', -⟩ := exists_sl2_heckeDiagMatrix_smul_eq ℓ γ hγ
  rw [jtN, jtN, hγ' τ]
  exact E4_cube_div_discriminant_smul γ' _

include hinv in
lemma slots_smul (γ : SL(2, ℤ)) : ∃ e : Equiv.Perm (Fin (ℓ + 1)),
    (∀ i τ, slotF ℓ F i (γ • τ) = slotF ℓ F (e i) τ) ∧ (∀ i τ, slotJ ℓ i (γ • τ) = slotJ ℓ (e i) τ)
      := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  obtain ⟨e, he⟩ := exists_perm_gamma0_cosetReps ℓ γ
  have key : ∀ (i : Fin (ℓ + 1)) (τ : ℍ),
      cosetRep ℓ i • γ • τ = (cosetRep ℓ i * γ * (cosetRep ℓ (e i))⁻¹) • cosetRep ℓ (e i) • τ := by
    intro i τ
    simp only [smul_smul, inv_mul_cancel_right]
  have he' : ∀ i, cosetRep ℓ i * γ * (cosetRep ℓ (e i))⁻¹ ∈ CongruenceSubgroup.Gamma0 ℓ := he
  refine ⟨e, fun i τ => ?_, fun i τ => ?_⟩
  · rw [slotF, slotF, key, hinv _ (he' i)]
  · rw [slotJ, slotJ, key, jtN_smul ℓ _ (he' i)]

include hinv in
lemma interpFun_smul (k : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) :
    interpFun ℓ F k (γ • τ) = interpFun ℓ F k τ := by
  obtain ⟨e, h1, h2⟩ := slots_smul ℓ F hinv γ
  unfold interpFun
  have hH : (fun i => slotF ℓ F i (γ • τ)) = (fun i => slotF ℓ F i τ) ∘ e := funext fun i => h1 i τ
  have hY : (fun i => slotJ ℓ i (γ • τ)) = (fun i => slotJ ℓ i τ) ∘ e := funext fun i => h2 i τ
  rw [hH, hY, interpPoly_perm]

include hinv in
lemma conjFun_smul (k : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) : conjFun ℓ F k (γ • τ) = conjFun ℓ F k τ := by
  obtain ⟨e, h1, -⟩ := slots_smul ℓ F hinv γ
  unfold conjFun
  have hH : (fun i => slotF ℓ F i (γ • τ)) = (fun i => slotF ℓ F i τ) ∘ e := funext fun i => h1 i τ
  rw [hH, conjPoly_perm]

include hF hG hσ hinv in
lemma mem_adjoin_of_interpK_coeff_eq (k : ℕ) (ξ : LaurentSeries ℚ)
    (hξ : (interpK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ ξ)) : ξ ∈ Algebra.adjoin ℚ {jq} := by
  have h1 : RealL ℓ (coeffMap σ ((interpK ℓ ζ f g).coeff k)) (interpFun ℓ F k) := by
    have h := RealL.interpPoly_coeff (h := (ℓ : ℝ)) (by exact_mod_cast hℓ.out.pos)
      (fun i => realL_slotH ℓ ζ σ hσ f g F hF hG i) (fun i => realL_conj ℓ ζ σ hσ i) k
    refine h.congr ?_ fun τ => rfl
    rw [← Polynomial.coeff_map, interpK, interpPoly_map]
    rfl
  rw [hξ, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h1
  have h2 := realL_one_of_realL_qExpand ℓ _ _ h1
  exact mem_adjoin_jq_of_hasSum_of_slash_invariant ξ (interpFun ℓ F k) h2
    (fun γ τ => interpFun_smul ℓ F hinv k γ τ)

include hF hG hσ hinv in
lemma mem_adjoin_of_conjK_coeff_eq (k : ℕ) (π : LaurentSeries ℚ)
    (hπ : (conjK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ π)) : π ∈ Algebra.adjoin ℚ {jq} := by
  have h1 : RealL ℓ (coeffMap σ ((conjK ℓ ζ f g).coeff k)) (conjFun ℓ F k) := by
    have h := RealL.conjPoly_coeff (h := (ℓ : ℝ)) (by exact_mod_cast hℓ.out.pos)
      (fun i => realL_slotH ℓ ζ σ hσ f g F hF hG i) k
    refine h.congr ?_ fun τ => rfl
    rw [← Polynomial.coeff_map, conjK, conjPoly_map]
    rfl
  rw [hπ, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h1
  have h2 := realL_one_of_realL_qExpand ℓ _ _ h1
  exact mem_adjoin_jq_of_hasSum_of_slash_invariant π (conjFun ℓ F k) h2
    (fun γ τ => conjFun_smul ℓ F hinv k γ τ)

end Analytic

section Assembly

variable {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K] [FiniteDimensional ℚ K]
  (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* ℂ)
  (hσ : σ (ζ : K) = expRoot ℓ)
  (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S •
    τ)))
  (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

def iota : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ ℓ)

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma iota_apply (x : LaurentSeries ℚ) : iota (K := K) ℓ x = coeffEmb K (qExpand ℚ ℓ x) := rfl

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma coeffEmb_injective' :
    Function.Injective (coeffEmb K : LaurentSeries ℚ → LaurentSeries K) := by
  intro x y h
  ext m
  have hm := congrArg (fun z : LaurentSeries K => z.coeff m) h
  simp only [coeffEmb_coeff] at hm
  exact (algebraMap ℚ K).injective hm

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma iota_injective : Function.Injective (iota (K := K) ℓ) :=
  coeffEmb_injective'.comp (qExpand_injective (R := ℚ) ℓ)

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma iota_eq_slotH_zero : iota ℓ f = slotH ℓ ζ f g 0 := by
  rw [iota_apply, slotH_zero]

omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma iota_jqN : iota (K := K) ℓ (jqN ℓ) = PhiGen.conj ℓ ζ 0 := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  rw [iota_apply, jqN, qExpand_qExpand, PhiGen.conj_zero, coeffEmb_qExpand]

def dHat :
    LaurentSeries K := ∏ m ∈ Finset.univ.erase (0 : Fin (ℓ + 1)), (PhiGen.conj ℓ ζ 0 - PhiGen.conj ℓ
      ζ m)

include hζ in
omit [IsGalois ℚ K] [FiniteDimensional ℚ K] in
lemma dHat_ne_zero : dHat ℓ ζ ≠ 0 := by
  rw [dHat, Finset.prod_ne_zero_iff]
  intro m hm h0
  exact (Finset.ne_of_mem_erase hm) ((PhiGen.conj_injective ℓ ζ hζ (sub_eq_zero.mp h0)).symm)

include hζ in
lemma exists_sum_eq_mul_dHat (hmem : ∀ (k : ℕ) (ξ : LaurentSeries ℚ),
      (interpK ℓ ζ f g).coeff k = coeffEmb K (qExpand ℚ ℓ ξ) → ξ ∈ Algebra.adjoin ℚ {jq}) :
    ∃ x : LaurentSeries ℚ, x ∈ modularFunctionField ℓ ∧ iota ℓ x = iota ℓ f * dHat ℓ ζ := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  choose ξ hξ using fun k => exists_interpK_coeff_eq ℓ ζ hζ f g k
  have hadj : Algebra.adjoin ℚ {jq} ≤ (modularFunctionField ℓ).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (jq_mem ℓ))
  refine ⟨∑ k ∈ Finset.range ((interpK ℓ ζ f g).natDegree + 1), ξ k * jqN ℓ ^ k, ?_, ?_⟩
  · refine sum_mem fun k _ => mul_mem (hadj (hmem k (ξ k) (hξ k))) (pow_mem (jqN_mem ℓ) k)
  · rw [map_sum]
    simp only [map_mul, map_pow, iota_jqN ℓ ζ, iota_apply, ← hξ]
    rw [← Polynomial.eval_eq_sum_range, interpK, interpPoly_eval, ← slotH_zero ℓ ζ f g, dHat]

include hζ hσ hF hG hinv in
theorem mem_modularFunctionField_of_data : f ∈ modularFunctionField ℓ := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  obtain ⟨x, hx, hιx⟩ := exists_sum_eq_mul_dHat ℓ ζ hζ f g
    (fun k ξ h => mem_adjoin_of_interpK_coeff_eq ℓ ζ σ hσ f g F hF hG hinv k ξ h)
  have h1F : ∀ τ : ℍ, HasSum (fun m : ℤ => (((1 : LaurentSeries ℚ).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^
    m)
      ((fun _ : ℍ => (1 : ℂ)) τ) := by
    intro τ
    have h := RealL.one 1 τ
    rw [← map_one (coeffMap castC)] at h
    exact h
  have h1G : ∀ τ : ℍ, HasSum (fun m : ℤ => (((1 : LaurentSeries ℚ).coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^
    m)
      ((fun _ : ℍ => (1 : ℂ)) (ModularGroup.S • τ)) := by
    intro τ
    have h := RealL.one (ℓ : ℝ) τ
    rw [← map_one (coeffMap castC)] at h
    exact h
  obtain ⟨d, hd, hιd⟩ := exists_sum_eq_mul_dHat ℓ ζ hζ 1 1
    (fun k ξ h => mem_adjoin_of_interpK_coeff_eq ℓ ζ σ hσ 1 1 (fun _ => 1) h1F h1G (fun _ _ _ =>
      rfl) k ξ h)
  rw [map_one, one_mul] at hιd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact dHat_ne_zero ℓ ζ hζ (by rw [map_zero] at hιd; exact hιd.symm)
  have hfd : f * d = x := iota_injective (K := K) ℓ (by rw [map_mul, hιd, hιx])
  have hf : f = x * d⁻¹ := by rw [← hfd, mul_inv_cancel_right₀ hd0]
  rw [hf]
  exact mul_mem hx (inv_mem hd)

include hζ hσ hF hG hinv in
theorem isIntegral_of_data : IsIntegral (Algebra.adjoin ℚ {jq}) f := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  choose π hπ using fun k => exists_conjK_coeff_eq ℓ ζ hζ f g k
  have hπmem : ∀ k, π k ∈ Algebra.adjoin ℚ {jq} := fun k =>
    mem_adjoin_of_conjK_coeff_eq ℓ ζ σ hσ f g F hF hG hinv k (π k) (hπ k)
  have hdeg : (conjK ℓ ζ f g).natDegree = ℓ + 1 := conjPoly_natDegree _
  have hmon : (conjK ℓ ζ f g).Monic := conjPoly_monic _
  let p : Polynomial (Algebra.adjoin ℚ {jq}) :=
    ∑ k ∈ Finset.range (ℓ + 2),
      Polynomial.C (⟨π k, hπmem k⟩ : Algebra.adjoin ℚ {jq}) * (Polynomial.X : Polynomial
        (Algebra.adjoin ℚ {jq})) ^ k
  have hcoeffp : ∀ n, p.coeff n = if n < ℓ + 2 then (⟨π n, hπmem n⟩ : Algebra.adjoin ℚ {jq}) else 0
    :=
    by
    intro n
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hmapmap : (p.map (algebraMap (Algebra.adjoin ℚ {jq}) (LaurentSeries ℚ))).map (iota ℓ) = conjK
    ℓ ζ f g :=
    by
    rw [Polynomial.map_map]
    simp only [p, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X,
      RingHom.comp_apply]
    have hk : ∀ k, (iota (K := K) ℓ) ((algebraMap (Algebra.adjoin ℚ {jq}) (LaurentSeries ℚ)) ⟨π k,
      hπmem k⟩) =
        (conjK ℓ ζ f g).coeff k :=
      fun k => (hπ k).symm
    simp only [hk]
    exact (Polynomial.as_sum_range_C_mul_X_pow' _ (by rw [hdeg]; omega)).symm
  refine ⟨p, ?_, ?_⟩
  · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one (ℓ + 1) ?_ ?_
    · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk =>
        (Polynomial.natDegree_C_mul_X_pow_le _ k).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp
          hk))
    · rw [hcoeffp, ite_eq_left (by omega)]
      refine Subtype.ext ?_
      apply iota_injective (K := K) ℓ
      rw [iota_apply, ← hπ (ℓ + 1), ← hdeg, hmon.coeff_natDegree]
      exact (map_one (iota (K := K) ℓ)).symm
  · rw [Polynomial.eval₂_eq_eval_map]
    apply iota_injective (K := K) ℓ
    rw [map_zero]
    change (iota ℓ) (Polynomial.eval₂ (RingHom.id _) f
      ((p.map (algebraMap (Algebra.adjoin ℚ {jq}) (LaurentSeries ℚ))))) = 0
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_eq_eval_map, ← Polynomial.map_map, Polynomial.map_id,
      hmapmap,
      iota_eq_slotH_zero ℓ ζ f g, conjK]
    exact conjPoly_eval _ 0

end Assembly

section Main

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

def sigma (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) :
    CyclotomicField ℓ ℚ →+* ℂ :=
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  ((hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)).symm
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩).toRingHom

lemma sigma_zeta (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) :
    sigma ℓ ζ hζ (ζ : CyclotomicField ℓ ℚ) = expRoot ℓ := by
  let : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have := CyclotomicField.isCyclotomicExtension ℓ ℚ
  let e := hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)
  let r : primitiveRoots ℓ ℂ :=
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩
  have h := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe hζ ℂ
    (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos) (e.symm r)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

variable (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S •
    τ)))
  (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

include hF hG hinv in
theorem mem_modularFunctionField : f ∈ modularFunctionField ℓ := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  exact mem_modularFunctionField_of_data ℓ hzu.unit hζ (sigma ℓ hzu.unit hζ) (sigma_zeta ℓ hzu.unit
    hζ)
    f g F hF hG hinv

include hF hG hinv in
theorem isIntegral_adjoin_jq : IsIntegral (Algebra.adjoin ℚ {jq}) f := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  exact isIntegral_of_data ℓ hzu.unit hζ (sigma ℓ hzu.unit hζ) (sigma_zeta ℓ hzu.unit hζ) f g F hF
    hG hinv

end Main

section FrickeTransport

lemma natDegree_interpPoly_lt {L : Type*} [CommRing L] {n : ℕ} (H Y : Fin (n + 1) → L) :
    (interpPoly H Y).natDegree < n + 1 := by
  unfold interpPoly
  refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun m _ => Polynomial.natDegree_X_sub_C_le (Y m)).trans ?_
  simp [Finset.card_erase_of_mem (Finset.mem_univ i)]

variable {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K] [FiniteDimensional ℚ K]
  (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* ℂ)
  (hσ : σ (ζ : K) = expRoot ℓ)
  (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S •
    τ)))
  (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

lemma realL_jtN_S : RealL ℓ (coeffMap castC jq) (fun τ => jtN ℓ (ModularGroup.S • τ)) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  intro τ
  have hpt : ModularForm.heckeDiagMatrix ℓ • ModularGroup.S • τ = ModularGroup.S •
    ModularForm.heckeMatrix ℓ 0 • τ :=
    by
    have h := heckeDiag_smul_S_T_pow_smul ℓ 0 τ
    rwa [pow_zero, mul_one] at h
  have h := hasSum_qParam_heckeMatrix_smul ℓ 0 (coeffMap castC jq) jt realL_jqC τ
  have hval : jtN ℓ (ModularGroup.S • τ) = jt (ModularForm.heckeMatrix ℓ 0 • τ) := by
    simp only [jtN]
    rw [hpt]
    exact E4_cube_div_discriminant_smul ModularGroup.S _
  change HasSum _ (jtN ℓ (ModularGroup.S • τ))
  rw [hval]
  refine h.congr_fun fun m => ?_
  simp

lemma realL_sum_qExpand_mul_jq_pow (n : ℕ) (ξ : ℕ → LaurentSeries ℚ) (Ξ : ℕ → ℍ → ℂ)
    (hξ : ∀ k, RealL 1 (coeffMap castC (ξ k)) (Ξ k))
    (hΞ : ∀ k (γ : SL(2, ℤ)) τ, Ξ k (γ • τ) = Ξ k τ) :
    RealL ℓ (coeffMap castC (∑ k ∈ Finset.range n, qExpand ℚ ℓ (ξ k) * jq ^ k))
      (fun τ => ∑ k ∈ Finset.range n, Ξ k (ModularGroup.S • τ) * jtN ℓ (ModularGroup.S • τ) ^ k)
        := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.out.pos
  have hk : ∀ k ∈ Finset.range n, RealL ℓ (coeffMap castC (qExpand ℚ ℓ (ξ k) * jq ^ k))
      (fun τ => Ξ k (ModularGroup.S • τ) * jtN ℓ (ModularGroup.S • τ) ^ k) := by
    intro k _
    have h1 : RealL ℓ (coeffMap castC (qExpand ℚ ℓ (ξ k))) (fun τ => Ξ k (ModularGroup.S • τ)) := by
      have h := realL_qExpand_of_realL_one ℓ _ _ (hξ k)
      refine h.congr (coeffMap_qExpand _ _ _).symm fun τ => (hΞ k ModularGroup.S τ).symm
    have h2 : RealL ℓ (coeffMap castC (jq ^ k)) (fun τ => jtN ℓ (ModularGroup.S • τ) ^ k) := by
      have h := RealL.prod hℓpos (Finset.range k) (fun _ _ => realL_jtN_S ℓ)
      refine h.congr ?_ fun τ => ?_
      · rw [Finset.prod_const, Finset.card_range, map_pow]
      · simp [Finset.prod_const, Finset.card_range]
    exact (h1.mul hℓpos h2).congr (map_mul _ _ _).symm fun τ => rfl
  exact (RealL.sum (Finset.range n) hk).congr (map_sum _ _ _).symm fun τ => rfl

lemma coeffMap_castC_injective :
    Function.Injective (coeffMap castC : LaurentSeries ℚ → LaurentSeries ℂ) := by
  intro x y h
  ext m
  have hm := congrArg (fun z : LaurentSeries ℂ => z.coeff m) h
  simp only [coeffMap_coeff] at hm
  exact castC.injective hm

def embW (w : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ) :
    modularFunctionFieldFull ℓ →+* LaurentSeries ℚ :=
  (algebraMap (modularFunctionFieldFull ℓ) (LaurentSeries ℚ)).comp (w : modularFunctionFieldFull ℓ
    →+* modularFunctionFieldFull ℓ)

omit hℓ in
lemma embW_apply (w : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ)
    (x : modularFunctionFieldFull ℓ) :
    embW ℓ w x = ((w x : modularFunctionFieldFull ℓ) : LaurentSeries ℚ) := rfl

lemma embW_of_mem_adjoin (w : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ)
    (hw : IsFrickeAutFull ℓ w) (ξ : LaurentSeries ℚ) (hξ : ξ ∈ Algebra.adjoin ℚ {jq})
    (hξ' : ξ ∈ modularFunctionFieldFull ℓ) : embW ℓ w ⟨ξ, hξ'⟩ = qExpand ℚ ℓ ξ := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  revert hξ'
  induction hξ using Algebra.adjoin_induction with
  | mem x hx =>
    intro hξ'
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h := hw 1 ℓ (one_mul ℓ) inferInstance inferInstance
    have h1 : (⟨qExpand ℚ 1 jq, jqd_mem_full ℓ (Dvd.intro ℓ (one_mul ℓ))⟩ : modularFunctionFieldFull
      ℓ) =
        ⟨jq, hξ'⟩ := Subtype.ext (qExpand_one_apply jq)
    rw [h1] at h
    rw [embW_apply, h]
  | algebraMap r =>
    intro hξ'
    have hR : qExpand ℚ ℓ (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℚ (LaurentSeries ℚ) r :=
      RingHom.congr_fun (RingHom.ext_rat ((qExpand ℚ ℓ).comp (algebraMap ℚ (LaurentSeries ℚ)))
        (algebraMap ℚ (LaurentSeries ℚ))) r
    let χ : ℚ →+* modularFunctionFieldFull ℓ := (algebraMap ℚ (LaurentSeries ℚ)).codRestrict
      (modularFunctionFieldFull ℓ) (fun x => IntermediateField.algebraMap_mem _ x)
    have hχ : χ = algebraMap ℚ (modularFunctionFieldFull ℓ) := RingHom.ext_rat _ _
    have he : (⟨algebraMap ℚ (LaurentSeries ℚ) r, hξ'⟩ : modularFunctionFieldFull ℓ) =
        algebraMap ℚ (modularFunctionFieldFull ℓ) r := by
      rw [← hχ]; rfl
    have hval : ((algebraMap ℚ (modularFunctionFieldFull ℓ) r : modularFunctionFieldFull ℓ) :
      LaurentSeries ℚ) =
        algebraMap ℚ (LaurentSeries ℚ) r := by
      rw [← he]
    rw [hR, he, embW_apply, AlgEquiv.commutes, hval]
  | add x y hx hy ihx ihy =>
    intro hξ'
    have hx' : x ∈ modularFunctionFieldFull ℓ :=
      (Algebra.adjoin_le (S := (modularFunctionFieldFull ℓ).toSubalgebra)
      (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))) hx
    have hy' : y ∈ modularFunctionFieldFull ℓ :=
      (Algebra.adjoin_le (S := (modularFunctionFieldFull ℓ).toSubalgebra)
      (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))) hy
    have : (⟨x + y, hξ'⟩ : modularFunctionFieldFull ℓ) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [this, map_add, map_add, ihx hx', ihy hy']
  | mul x y hx hy ihx ihy =>
    intro hξ'
    have hx' : x ∈ modularFunctionFieldFull ℓ :=
      (Algebra.adjoin_le (S := (modularFunctionFieldFull ℓ).toSubalgebra)
      (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))) hx
    have hy' : y ∈ modularFunctionFieldFull ℓ :=
      (Algebra.adjoin_le (S := (modularFunctionFieldFull ℓ).toSubalgebra)
      (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))) hy
    have : (⟨x * y, hξ'⟩ : modularFunctionFieldFull ℓ) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
    rw [this, map_mul, map_mul, ihx hx', ihy hy']

include hζ hσ hF hG hinv in
theorem fricke_transport (w : modularFunctionFieldFull ℓ ≃ₐ[ℚ] modularFunctionFieldFull ℓ)
    (hw : IsFrickeAutFull ℓ w) (hf : f ∈ modularFunctionFieldFull ℓ) :
    ((w ⟨f, hf⟩ : modularFunctionFieldFull ℓ) : LaurentSeries ℚ) = g := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.out.pos
  have hadj : Algebra.adjoin ℚ {jq} ≤ (modularFunctionFieldFull ℓ).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr (jq_mem_full ℓ))
  have hFle := modularFunctionField_le_full ℓ
  choose ξ hξ using fun k => exists_interpK_coeff_eq ℓ ζ hζ f g k
  have h1F : ∀ τ : ℍ, HasSum (fun m : ℤ => (((1 : LaurentSeries ℚ).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^
    m)
      ((fun _ : ℍ => (1 : ℂ)) τ) := by
    intro τ; have h := RealL.one 1 τ; rw [← map_one (coeffMap castC)] at h; exact h
  have h1G : ∀ τ : ℍ, HasSum (fun m : ℤ => (((1 : LaurentSeries ℚ).coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^
    m)
      ((fun _ : ℍ => (1 : ℂ)) (ModularGroup.S • τ)) := by
    intro τ; have h := RealL.one (ℓ : ℝ) τ; rw [← map_one (coeffMap castC)] at h; exact h
  have h1inv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, (fun _ : ℍ => (1 : ℂ)) (γ • τ) = (fun _ :
    ℍ => (1 : ℂ)) τ :=
    fun _ _ _ => rfl
  choose ξ1 hξ1 using fun k => exists_interpK_coeff_eq ℓ ζ hζ (1 : LaurentSeries ℚ) 1 k
  have hξmem : ∀ k, ξ k ∈ Algebra.adjoin ℚ {jq} := fun k =>
    mem_adjoin_of_interpK_coeff_eq ℓ ζ σ hσ f g F hF hG hinv k (ξ k) (hξ k)
  have hξ1mem : ∀ k, ξ1 k ∈ Algebra.adjoin ℚ {jq} := fun k =>
    mem_adjoin_of_interpK_coeff_eq ℓ ζ σ hσ 1 1 (fun _ => 1) h1F h1G h1inv k (ξ1 k) (hξ1 k)
  have hreal : ∀ k, RealL 1 (coeffMap castC (ξ k)) (interpFun ℓ F k) := by
    intro k
    have h := RealL.interpPoly_coeff (h := (ℓ : ℝ)) hℓpos
      (fun i => realL_slotH ℓ ζ σ hσ f g F hF hG i) (fun i => realL_conj ℓ ζ σ hσ i) k
    have h' : RealL ℓ (coeffMap σ ((interpK ℓ ζ f g).coeff k)) (interpFun ℓ F k) := by
      refine h.congr ?_ fun τ => rfl
      rw [← Polynomial.coeff_map, interpK, interpPoly_map]; rfl
    rw [hξ k, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h'
    exact realL_one_of_realL_qExpand ℓ _ _ h'
  have hreal1 : ∀ k, RealL 1 (coeffMap castC (ξ1 k)) (interpFun ℓ (fun _ => (1 : ℂ)) k) := by
    intro k
    have h := RealL.interpPoly_coeff (h := (ℓ : ℝ)) hℓpos
      (fun i => realL_slotH ℓ ζ σ hσ 1 1 (fun _ => (1 : ℂ)) h1F h1G i) (fun i => realL_conj ℓ ζ σ hσ
        i) k
    have h' : RealL ℓ (coeffMap σ ((interpK ℓ ζ (1 : LaurentSeries ℚ) 1).coeff k)) (interpFun ℓ (fun
      _ => (1 : ℂ)) k) :=
      by
      refine h.congr ?_ fun τ => rfl
      rw [← Polynomial.coeff_map, interpK, interpPoly_map]; rfl
    rw [hξ1 k, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h'
    exact realL_one_of_realL_qExpand ℓ _ _ h'
  set x : LaurentSeries ℚ := ∑ k ∈ Finset.range (ℓ + 1), ξ k * jqN ℓ ^ k with hx
  set d : LaurentSeries ℚ := ∑ k ∈ Finset.range (ℓ + 1), ξ1 k * jqN ℓ ^ k with hd
  set x' : LaurentSeries ℚ := ∑ k ∈ Finset.range (ℓ + 1), qExpand ℚ ℓ (ξ k) * jq ^ k with hx'
  set d' : LaurentSeries ℚ := ∑ k ∈ Finset.range (ℓ + 1), qExpand ℚ ℓ (ξ1 k) * jq ^ k with hd'
  have hxmem : x ∈ modularFunctionFieldFull ℓ :=
    sum_mem fun k _ => mul_mem (hadj (hξmem k)) (pow_mem (hFle (jqN_mem ℓ)) k)
  have hdmem : d ∈ modularFunctionFieldFull ℓ :=
    sum_mem fun k _ => mul_mem (hadj (hξ1mem k)) (pow_mem (hFle (jqN_mem ℓ)) k)
  have hιx : iota (K := K) ℓ x = iota ℓ f * dHat ℓ ζ := by
    have hdeg : (interpK ℓ ζ f g).natDegree < ℓ + 1 := natDegree_interpPoly_lt _ _
    rw [hx, map_sum]
    simp only [map_mul, map_pow, iota_jqN ℓ ζ, iota_apply, ← hξ]
    rw [← Polynomial.eval_eq_sum_range' hdeg, interpK, interpPoly_eval, ← slotH_zero ℓ ζ f g, dHat]
  have hιd : iota (K := K) ℓ d = dHat ℓ ζ := by
    have hdeg : (interpK ℓ ζ (1 : LaurentSeries ℚ) 1).natDegree < ℓ + 1 :=
      natDegree_interpPoly_lt _ _
    rw [hd, map_sum]
    simp only [map_mul, map_pow, iota_jqN ℓ ζ, iota_apply, ← hξ1]
    rw [← Polynomial.eval_eq_sum_range' hdeg, interpK, interpPoly_eval, dHat, slotH_zero, map_one,
      map_one, one_mul]
  have hd0 : d ≠ 0 := by
    intro h0; exact dHat_ne_zero ℓ ζ hζ (by rw [h0, map_zero] at hιd; exact hιd.symm)
  have hfd : f * d = x := iota_injective (K := K) ℓ (by rw [map_mul, hιd, hιx])
  have hwx : embW ℓ w ⟨x, hxmem⟩ = x' := by
    have : (⟨x, hxmem⟩ : modularFunctionFieldFull ℓ) =
        ∑ k ∈ Finset.range (ℓ + 1), ⟨ξ k, hadj (hξmem k)⟩ * ⟨jqN ℓ, hFle (jqN_mem ℓ)⟩ ^ k := by
      apply Subtype.ext
      simp only [hx]
      push_cast
      rfl
    rw [this, map_sum, hx']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, embW_of_mem_adjoin ℓ w hw (ξ k) (hξmem k)]
    congr 1
    have h := hw ℓ 1 (mul_one ℓ) inferInstance inferInstance
    have h1 : (⟨qExpand ℚ 1 jq, jqd_mem_full ℓ (Dvd.intro_left ℓ (mul_one ℓ))⟩ :
      modularFunctionFieldFull ℓ) =
        ⟨jq, jq_mem_full ℓ⟩ := Subtype.ext (qExpand_one_apply jq)
    have h2 : (⟨qExpand ℚ ℓ jq, jqd_mem_full ℓ (Dvd.intro 1 (mul_one ℓ))⟩ : modularFunctionFieldFull
      ℓ) =
        ⟨jqN ℓ, hFle (jqN_mem ℓ)⟩ := Subtype.ext rfl
    rw [h1, h2] at h
    rw [embW_apply, h]
  have hwd : embW ℓ w ⟨d, hdmem⟩ = d' := by
    have : (⟨d, hdmem⟩ : modularFunctionFieldFull ℓ) =
        ∑ k ∈ Finset.range (ℓ + 1), ⟨ξ1 k, hadj (hξ1mem k)⟩ * ⟨jqN ℓ, hFle (jqN_mem ℓ)⟩ ^ k := by
      apply Subtype.ext
      simp only [hd]
      push_cast
      rfl
    rw [this, map_sum, hd']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_pow, embW_of_mem_adjoin ℓ w hw (ξ1 k) (hξ1mem k)]
    congr 1
    have h := hw ℓ 1 (mul_one ℓ) inferInstance inferInstance
    have h1 : (⟨qExpand ℚ 1 jq, jqd_mem_full ℓ (Dvd.intro_left ℓ (mul_one ℓ))⟩ :
      modularFunctionFieldFull ℓ) =
        ⟨jq, jq_mem_full ℓ⟩ := Subtype.ext (qExpand_one_apply jq)
    have h2 : (⟨qExpand ℚ ℓ jq, jqd_mem_full ℓ (Dvd.intro 1 (mul_one ℓ))⟩ : modularFunctionFieldFull
      ℓ) =
        ⟨jqN ℓ, hFle (jqN_mem ℓ)⟩ := Subtype.ext rfl
    rw [h1, h2] at h
    rw [embW_apply, h]
  have hXpt : ∀ (Φ : ℍ → ℂ) (τ : ℍ), ∑ k ∈ Finset.range (ℓ + 1), interpFun ℓ Φ k τ * jtN ℓ τ ^ k =
      Φ τ * ∏ m ∈ Finset.univ.erase (0 : Fin (ℓ + 1)), (slotJ ℓ 0 τ - slotJ ℓ m τ) := by
    intro Φ τ
    have h1 := interpPoly_eval (fun i => slotF ℓ Φ i τ) (fun i => slotJ ℓ i τ) 0
    have h2 := Polynomial.eval_eq_sum_range'
      (natDegree_interpPoly_lt (fun i => slotF ℓ Φ i τ) (fun i => slotJ ℓ i τ)) ((fun i => slotJ ℓ i
        τ) 0)
    simp only [] at h1 h2
    have h0 : slotJ ℓ 0 τ = jtN ℓ τ := by simp [slotJ]
    have hF0 : slotF ℓ Φ 0 τ = Φ τ := by simp [slotF]
    simp only [interpFun]
    rw [← h0, ← h2, h1, hF0]
  have hrx' : RealL ℓ (coeffMap castC x') (fun τ => F (ModularGroup.S • τ) *
      ∏ m ∈ Finset.univ.erase (0 : Fin (ℓ + 1)), (slotJ ℓ 0 (ModularGroup.S • τ) - slotJ ℓ m
        (ModularGroup.S • τ))) := by
    have h := realL_sum_qExpand_mul_jq_pow ℓ (ℓ + 1) ξ (fun k => interpFun ℓ F k) hreal
      (fun k γ τ => interpFun_smul ℓ F hinv k γ τ)
    exact h.congr rfl fun τ => hXpt F (ModularGroup.S • τ)
  have hrd' : RealL ℓ (coeffMap castC d') (fun τ =>
      ∏ m ∈ Finset.univ.erase (0 : Fin (ℓ + 1)), (slotJ ℓ 0 (ModularGroup.S • τ) - slotJ ℓ m
        (ModularGroup.S • τ))) := by
    have h :=
      realL_sum_qExpand_mul_jq_pow ℓ (ℓ + 1) ξ1 (fun k => interpFun ℓ (fun _ => (1 : ℂ)) k) hreal1
      (fun k γ τ => interpFun_smul ℓ (fun _ => (1 : ℂ)) h1inv k γ τ)
    refine h.congr rfl fun τ => ?_
    rw [hXpt (fun _ => (1 : ℂ)) (ModularGroup.S • τ), one_mul]
  have hrg : RealL ℓ (coeffMap castC g) (fun τ => F (ModularGroup.S • τ)) := fun τ => hG τ
  have hx'gd : x' = g * d' := by
    apply coeffMap_castC_injective
    rw [map_mul]
    exact laurent_qParam_coeff_unique ℓ hℓpos _ _ _ hrx' (hrg.mul hℓpos hrd')
  have hd'0 : d' ≠ 0 := by
    rw [← hwd, embW_apply]
    intro h0
    apply hd0
    have : (w ⟨d, hdmem⟩ : modularFunctionFieldFull ℓ) = 0 := Subtype.ext h0
    have := w.injective (this.trans (map_zero w).symm)
    exact congrArg Subtype.val this
  have hprod : (⟨f, hf⟩ : modularFunctionFieldFull ℓ) * ⟨d, hdmem⟩ = ⟨x, hxmem⟩ := Subtype.ext hfd
  have key : embW ℓ w ⟨f, hf⟩ * d' = g * d' := by
    rw [← hx'gd, ← hwx, ← hprod, map_mul, hwd]
  have := mul_right_cancel₀ hd'0 key
  rwa [embW_apply] at this

end FrickeTransport

end QExpN
end ModularCurve
end

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ) (hF :
  ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ :
  ℂ) ^ m) (F τ)) (hG : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) *
  Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ))) (hinv : ∀ γ ∈
  CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) (hf : f ∈
  ModularCurve.modularFunctionFieldFull ℓ) :
    ((ModularCurve.frickeInvolutionFull ℓ ⟨f, hf⟩ : ModularCurve.modularFunctionFieldFull ℓ) :
      LaurentSeries ℚ) = g := by
  have hℓ : Fact (Nat.Prime ℓ) := inferInstance
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  exact ModularCurve.QExpN.fricke_transport ℓ hzu.unit hζ (ModularCurve.QExpN.sigma ℓ hzu.unit hζ)
    (ModularCurve.QExpN.sigma_zeta ℓ hzu.unit hζ) f g F hF hG hinv
      (ModularCurve.frickeInvolutionFull ℓ)
    (ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime ℓ) hf

end S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
end P2MW
export P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant (solution)

end privateSection

public section publicSection

theorem ModularCurve.coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant (ℓ : ℕ) [Fact
  (Nat.Prime ℓ)] (f g : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ) (hF : ∀ τ : UpperHalfPlane, HasSum
  (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (hG : ∀ τ :
  UpperHalfPlane, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * Function.Periodic.qParam ℓ (τ : ℂ) ^
  m) (F (ModularGroup.S • τ))) (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ
  • τ) = F τ) (hf : f ∈ ModularCurve.modularFunctionFieldFull ℓ) :
    ((ModularCurve.frickeInvolutionFull ℓ ⟨f, hf⟩ : ModularCurve.modularFunctionFieldFull ℓ) :
      LaurentSeries ℚ) = g :=
  solution ℓ f g F hF hG hinv hf

end publicSection
