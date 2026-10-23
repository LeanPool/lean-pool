/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/

/-
Based on Prove2Me node
ModularCurve.exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace
(7c8c2611-3f75-5f50-8620-bbc353cafd33) by Claude (2026-09-05).

Proof based on Prove2Me submission e35b7e94-2177-503f-ad53-6879f6d8eed9
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_Repartitions
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_GenusNumerics
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_MazurStepThreeInputs

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_card_eq_natCard_moduliPoint_j_eq_of_EMD
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_dedekindPsi_pos
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_emd_holds
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_natCard_ord_jBar_eq_one_eq_nuThree
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ord_jBar_dvd_three
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ord_jBar_sub_1728_dvd_two
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# A weight-2m divisor on X₀(N)_ℚ̄ with integrality

Theorem statement:
`ModularCurve.exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace`
(`7c8c2611-3f75-5f50-8620-bbc353cafd33`), by Claude, 2026-09-05.

Proof: submission `e35b7e94-2177-503f-ad53-6879f6d8eed9`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $N\ge 1$ (a natural number with `NeZero N`) and let $m$ be a natural number with $1\le m$. Write
$\bar F_N$ for [`ModularCurve.modularFunctionFieldBar
N`](def/ModularCurve_ArithmeticGalois.html#L111), the intermediate field of $\overline{\mathbb
Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of
`modularFunctionFieldFull N`, itself the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by
the divisor expansions attached to $N$, and write $\bar\jmath=$ `jBar N` for the element of $\bar
F_N$ given by the $q$-expansion of $j$. Put $g=$ `genusFormula N`
$=1+\psi(N)/12-\nu_2/4-\nu_3/3-\nu_\infty/2$, where $\psi(N)=\sum_{d\mid N,\ d\
\text{squarefree}}N/d$, $\nu_2=\#\{x\in\mathbb Z/N:x^2+1=0\}$, $\nu_3=\#\{x\in\mathbb
Z/N:x^2+x+1=0\}$ and $\nu_\infty=$ `cuspCount N` $=\sum_{d\mid N}\varphi(\gcd(d,N/d))$. The
assertion is that there exists a divisor $D$ on $\bar F_N$ over $\overline{\mathbb Q}$, i.e. a
finitely supported integer-valued function on the places of $\bar F_N/\overline{\mathbb Q}$
(valuation subrings containing $\overline{\mathbb Q}$, proper, and principal ideal rings), such
that, first, with $\deg D=\sum_v D(v)\deg v$,
$$\deg D+1-g=(2m-1)(g-1)+\lfloor m/2\rfloor\,\nu_2+\lfloor 2m/3\rfloor\,\nu_3+(m-1)\,\nu_\infty$$
(the floors being natural-number divisions $m/2$ and $2m/3$), and, secondly, every $x$ in the
Riemann–Roch space of $D$, that is every $x\in\bar F_N$ whose adic valuation at each place $v$ is at
most $\exp(D(v))$, satisfies two integrality conditions:
$x^6\,\bar\jmath^{\,4m}(\bar\jmath-1728)^{3m}$ is integral over $\overline{\mathbb Q}[\bar\jmath]$,
and $x^{2\psi(N)}\,\bar\jmath^{\,m\psi(N)+1}(\bar\jmath-1728)^{m\psi(N)}$ is integral over
$\overline{\mathbb Q}[\bar\jmath^{-1}]$, where $1728$ denotes its image under the structure map
$\overline{\mathbb Q}\to\bar F_N$.

This packages the divisor-theoretic input to the dimension formula for cusp forms of weight $2m$ on
$\Gamma_0(N)$: a divisor whose Riemann–Roch defect is exactly the classical dimension expression,
together with growth bounds at the places above $j=0$, $j=1728$ and the cusps in the form of
integrality over $\overline{\mathbb Q}[\bar\jmath]$ and $\overline{\mathbb Q}[\bar\jmath^{-1}]$. It
is used in the proof of
[`CuspForm.dimFormula_le_finrank_gamma0`](thm.html#CuspForm.dimFormula_le_finrank_gamma0).

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace.lean

<!-- Generated by add_prove2me_provenance.py -->
-/


section privateSection


namespace P2MW.S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace


namespace ModularCurve
p2m_export "ModularCurve" "jBar modularFunctionFieldBar jq coeff_jq_neg_one dedekindPsi coeffEmb \
  coeffEmb_coeff nuTwo nuThree cuspCount genusFormula EMD ModuliPoint ModuliPoint.j \
  sum_ord_jBar_sub_eq_dedekindPsi deg_eq_one_modularFunctionFieldBar \
  jCoordinate_spec_modularFunctionFieldBar sum_neg_ord_jBar_eq_dedekindPsi ord_jBar_dvd_three \
  ord_jBar_sub_1728_dvd_two card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg \
  natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo natCard_ord_jBar_eq_one_eq_nuThree \
  card_eq_natCard_moduliPoint_j_eq_of_EMD emd_holds transcendental_coeffEmb_jq \
  isCurveOver_modularFunctionFieldBar finiteDimensional_adjoin_coeffEmb_jq_of_neZero \
  dedekindPsi_pos"
namespace LDivDegree
p2m_open "ModularCurve"

p2m_open "ModularCurve \
  P2MW.S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace.ModularCu\
  rve AlgebraicCurve"

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) {c : K} : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h1 : v.ord (-f) = v.ord (-1) + v.ord f := by
    rw [← v.ord_mul (by norm_num) hf, neg_one_mul]
  have h2 : v.ord ((-1 : F)) = 0 := by
    have := v.ord_zpow (-1 : F) 2
    norm_num at this
    linarith
  rw [h1, h2, zero_add]

end Generic

theorem int_eq_of_pos_of_dvd_two {e : ℤ} (he : 0 < e) (hd : e ∣ 2) : e = 1 ∨ e = 2 := by
  have hle := Int.le_of_dvd (by norm_num) hd
  interval_cases e
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem int_eq_of_pos_of_dvd_three {e : ℤ} (he : 0 < e) (hd : e ∣ 3) : e = 1 ∨ e = 3 := by
  have hle := Int.le_of_dvd (by norm_num) hd
  interval_cases e
  · exact Or.inl rfl
  · exfalso; norm_num at hd
  · exact Or.inr rfl

variable (N : ℕ) [NeZero N] (m : ℕ)

local notation "ℚb" => AlgebraicClosure ℚ
local notation "𝔽" => ModularCurve.modularFunctionFieldBar N

theorem jBar_sub_algebraMap_ne_zero (c : ℚb) : jBar N - algebraMap ℚb 𝔽 c ≠ 0 := by
  intro h
  have htr := transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  apply htr
  have : (jBar N : 𝔽) = algebraMap ℚb 𝔽 c := sub_eq_zero.mp h
  change IsAlgebraic ℚb (jBar N)
  rw [this]
  exact isAlgebraic_algebraMap c

theorem jBar_ne_zero : (jBar N : 𝔽) ≠ 0 := by
  have h := jBar_sub_algebraMap_ne_zero N 0
  rwa [map_zero, sub_zero] at h

theorem ord_sub_nonneg {v : Place ℚb 𝔽} (hv : 0 ≤ v.ord (jBar N)) (c : ℚb) :
    0 ≤ v.ord (jBar N - algebraMap ℚb 𝔽 c) := by
  rw [← v.mem_iff_ord_nonneg (jBar_sub_algebraMap_ne_zero N c)]
  exact sub_mem ((v.mem_iff_ord_nonneg (jBar_ne_zero N)).mpr hv) (v.algebraMap_mem' c)

theorem ord_eq_zero_of_pos_1728 {v : Place ℚb 𝔽} (hv : 0 < v.ord (jBar N - algebraMap ℚb 𝔽 1728)) :
    v.ord (jBar N) = 0 := by
  have h1728 : v.ord (algebraMap ℚb 𝔽 1728) = 0 := ord_algebraMap v
  have hne : (algebraMap ℚb 𝔽 1728) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚb 𝔽).injective]; norm_num
  rcases lt_trichotomy (v.ord (jBar N)) 0 with hlt | heq | hgt
  · have h : v.ord (jBar N + (-(algebraMap ℚb 𝔽 1728))) = v.ord (jBar N) :=
      v.ord_add_eq_of_lt (jBar_ne_zero N) (neg_ne_zero.mpr hne) (by rw [ord_neg, h1728]; exact hlt)
    rw [← sub_eq_add_neg] at h
    omega
  · exact heq
  · have h : v.ord (-(algebraMap ℚb 𝔽 1728) + jBar N) = v.ord (-(algebraMap ℚb 𝔽 1728)) :=
      v.ord_add_eq_of_lt (neg_ne_zero.mpr hne) (jBar_ne_zero N) (by rw [ord_neg, h1728]; exact hgt)
    rw [neg_add_eq_sub, ord_neg, h1728] at h
    omega

theorem ord_1728_eq_zero_of_pos {v : Place ℚb 𝔽} (hv : 0 < v.ord (jBar N)) :
    v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 0 := by
  have h1728 : v.ord (algebraMap ℚb 𝔽 1728) = 0 := ord_algebraMap v
  have hne : (algebraMap ℚb 𝔽 1728) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚb 𝔽).injective]; norm_num
  have h : v.ord (-(algebraMap ℚb 𝔽 1728) + jBar N) = v.ord (-(algebraMap ℚb 𝔽 1728)) :=
    v.ord_add_eq_of_lt (neg_ne_zero.mpr hne) (jBar_ne_zero N) (by rw [ord_neg, h1728]; exact hv)
  rw [neg_add_eq_sub, ord_neg, h1728] at h
  exact h

noncomputable def recipe (v : Place ℚb 𝔽) : ℤ :=
  if v.ord (jBar N) < 0 then (m : ℤ) * v.ord (jBar N) - 1
  else (m : ℤ) * v.ord (jBar N - algebraMap ℚb 𝔽 1728) / 2 + 2 * (m : ℤ) * v.ord (jBar N) / 3

theorem recipe_of_neg {v : Place ℚb 𝔽} (h : v.ord (jBar N) < 0) :
    recipe N m v = (m : ℤ) * v.ord (jBar N) - 1 := ite_eq_left h

theorem recipe_of_nonneg {v : Place ℚb 𝔽} (h : 0 ≤ v.ord (jBar N)) :
    recipe N m v = (m : ℤ) * v.ord (jBar N - algebraMap ℚb 𝔽 1728) / 2 + 2 * (m : ℤ) * v.ord (jBar
      N) / 3 :=
  ite_eq_right (not_lt.mpr h)

theorem recipe_of_pos {v : Place ℚb 𝔽} (h : 0 < v.ord (jBar N)) :
    recipe N m v = 2 * (m : ℤ) * v.ord (jBar N) / 3 := by
  rw [recipe_of_nonneg N m h.le, ord_1728_eq_zero_of_pos N h, mul_zero, Int.zero_ediv, zero_add]

theorem recipe_of_pos_1728 {v : Place ℚb 𝔽} (h : 0 < v.ord (jBar N - algebraMap ℚb 𝔽 1728)) :
    recipe N m v = (m : ℤ) * v.ord (jBar N - algebraMap ℚb 𝔽 1728) / 2 := by
  have h0 := ord_eq_zero_of_pos_1728 N h
  rw [recipe_of_nonneg N m h0.ge, h0, mul_zero, Int.zero_ediv, add_zero]

theorem recipe_eq_zero {v : Place ℚb 𝔽} (h0 : v.ord (jBar N) = 0)
    (h1 : ¬ 0 < v.ord (jBar N - algebraMap ℚb 𝔽 1728)) : recipe N m v = 0 := by
  have hge := ord_sub_nonneg N h0.ge (1728 : ℚb)
  have he : v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 0 := by omega
  rw [recipe_of_nonneg N m h0.ge, h0, he]
  simp

theorem exists_weightDivisor :
    ∃ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ((D.degree : ℚ) + 1 - ModularCurve.genusFormula N =
        (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) *
          (ModularCurve.nuTwo N : ℚ)
          + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) *
            (ModularCurve.cuspCount N : ℚ)) ∧
      (∀ v, 0 ≤ v.ord (jBar N) →
        D v ≤ (m : ℤ) * v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          1728) / 2
          + 2 * (m : ℤ) * v.ord (jBar N) / 3) ∧
      (∀ v, v.ord (jBar N) < 0 → D v ≤ (m : ℤ) * v.ord (jBar N) - 1) := by
  classical
  have hdeg : ∀ w : Place ℚb 𝔽, w.deg = 1 := deg_eq_one_modularFunctionFieldBar N
  obtain ⟨-, hfinc, hfinI⟩ := jCoordinate_spec_modularFunctionFieldBar N
  set S0 : Finset (Place ℚb 𝔽) := (hfinc 0).toFinset with hS0def
  set S1 : Finset (Place ℚb 𝔽) := (hfinc 1728).toFinset with hS1def
  set Sinf : Finset (Place ℚb 𝔽) := hfinI.toFinset with hSIdef
  have hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord (jBar N) := fun v => by
    rw [hS0def, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, map_zero, sub_zero]
  have hS1 : ∀ v, v ∈ S1 ↔ 0 < v.ord (jBar N - algebraMap ℚb 𝔽 1728) :=
    fun v => by rw [hS1def, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hSI : ∀ v, v ∈ Sinf ↔ v.ord (jBar N) < 0 := fun v => by
    rw [hSIdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  set S := S0 ∪ S1 ∪ Sinf with hSdef
  have hS : ∀ v, v ∈ S ↔ v ∈ S0 ∨ v ∈ S1 ∨ v ∈ Sinf := fun v => by
    simp only [hSdef, Finset.mem_union, or_assoc]
  have hoff : ∀ v, v ∉ S → recipe N m v = 0 := by
    intro v hv
    rw [hS] at hv
    push Not at hv
    obtain ⟨hv0, hv1, hvI⟩ := hv
    rw [hS0] at hv0; rw [hS1] at hv1; rw [hSI] at hvI
    exact recipe_eq_zero N m (by omega) hv1
  let D : Divisor ℚb 𝔽 := Finsupp.onFinset S (recipe N m) (fun v hv => by
    by_contra h
    exact hv (hoff v h))
  have hD : ∀ v, D v = recipe N m v := fun v => Finsupp.onFinset_apply
  refine ⟨D, ?_, fun v hv => ?_, fun v hv => ?_⟩
  rotate_left
  · rw [hD, recipe_of_nonneg N m hv]
  · rw [hD, recipe_of_neg N m hv]
  have hdisj01 : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro v hv0 hv1
    rw [hS0] at hv0; rw [hS1] at hv1
    have := ord_eq_zero_of_pos_1728 N hv1
    omega
  have hdisj0I : Disjoint (S0 ∪ S1) Sinf := by
    rw [Finset.disjoint_left]
    intro v hv hvI
    rw [hSI] at hvI
    rcases Finset.mem_union.mp hv with hv0 | hv1
    · rw [hS0] at hv0; omega
    · rw [hS1] at hv1
      have := ord_eq_zero_of_pos_1728 N hv1
      omega
  have hdegsum : D.degree = ∑ v ∈ S, recipe N m v := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    have hsupp : D.support ⊆ S := Finsupp.support_onFinset_subset
    rw [Finset.sum_subset hsupp (fun v _ hv => by
      have : D v = 0 := by simpa [Finsupp.mem_support_iff] using hv
      rw [this]; simp)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one, hD]
  have hsplit : ∑ v ∈ S, recipe N m v
      = ∑ v ∈ S0, recipe N m v + ∑ v ∈ S1, recipe N m v + ∑ v ∈ Sinf, recipe N m v := by
    rw [hSdef, Finset.sum_union hdisj0I, Finset.sum_union hdisj01]
  have hsum0 : 3 * ∑ v ∈ S0, recipe N m v
      = 3 * ((2 * m / 3 : ℕ) : ℤ) * ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ)
        + 2 * (m : ℤ) * ((dedekindPsi N : ℤ) - ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ))
          := by
    have hψ₀ : ∑ v ∈ S0, v.ord (jBar N) = (dedekindPsi N : ℤ) := by
      have h :=
        sum_ord_jBar_sub_eq_dedekindPsi N 0 hdeg S0 (fun v => by rw [hS0, map_zero, sub_zero])
      simpa [map_zero, sub_zero] using h
    have hcase : ∀ v ∈ S0, (v.ord (jBar N) = 1 ∧ recipe N m v = ((2 * m / 3 : ℕ) : ℤ)) ∨
        (v.ord (jBar N) = 3 ∧ recipe N m v = 2 * (m : ℤ)) := by
      intro v hv
      have hpos := (hS0 v).1 hv
      have hdvd := ord_jBar_dvd_three N v hpos
      rw [recipe_of_pos N m hpos]
      rcases int_eq_of_pos_of_dvd_three hpos hdvd with h1 | h3
      · left; refine ⟨h1, ?_⟩; rw [h1]; push_cast; omega
      · right; refine ⟨h3, ?_⟩; rw [h3]; omega
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not S0 (fun v => v.ord (jBar N) = 1)]
    rw [← Finset.sum_filter_add_sum_filter_not S0 (fun v => v.ord (jBar N) = 1)] at hψ₀
    have hA : ∑ v ∈ S0.filter (fun v => v.ord (jBar N) = 1), 3 * recipe N m v
        = 3 * ((2 * m / 3 : ℕ) : ℤ) * ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => 3 * ((2 * m / 3 : ℕ) : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul]; ring
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨-, hr⟩ | ⟨h3, -⟩
        · rw [hr]
        · omega
    have hB : ∑ v ∈ S0.filter (fun v => ¬ v.ord (jBar N) = 1), 3 * recipe N m v
        = 6 * (m : ℤ) * ((S0.filter fun v => ¬ v.ord (jBar N) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => 6 * (m : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul]; ring
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨h1', -⟩ | ⟨-, hr⟩
        · exact absurd h1' h1
        · rw [hr]; ring
    have hψA : ∑ v ∈ S0.filter (fun v => v.ord (jBar N) = 1), v.ord (jBar N)
        = ((S0.filter fun v => v.ord (jBar N) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun v hv => (Finset.mem_filter.mp hv).2)]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hψB : ∑ v ∈ S0.filter (fun v => ¬ v.ord (jBar N) = 1), v.ord (jBar N)
        = 3 * ((S0.filter fun v => ¬ v.ord (jBar N) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (3 : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨h1', -⟩ | ⟨h3, -⟩
        · exact absurd h1' h1
        · exact h3
    rw [hA, hB]
    rw [hψA, hψB] at hψ₀
    linear_combination (2 * (m : ℤ)) * hψ₀
  have hsum1 : 2 * ∑ v ∈ S1, recipe N m v
      = 2 * ((m / 2 : ℕ) : ℤ) * ((S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card
        : ℤ)
        + (m : ℤ) * ((dedekindPsi N : ℤ) - ((S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽
          1728) = 1).card : ℤ)) := by
    have hψ₁ : ∑ v ∈ S1, v.ord (jBar N - algebraMap ℚb 𝔽 1728) = (dedekindPsi N : ℤ) :=
      sum_ord_jBar_sub_eq_dedekindPsi N 1728 hdeg S1 hS1
    have hcase : ∀ v ∈ S1, (v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1 ∧ recipe N m v = ((m / 2 : ℕ)
      : ℤ)) ∨
        (v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 2 ∧ recipe N m v = (m : ℤ)) := by
      intro v hv
      have hpos := (hS1 v).1 hv
      have hdvd := ord_jBar_sub_1728_dvd_two N v hpos
      rw [recipe_of_pos_1728 N m hpos]
      rcases int_eq_of_pos_of_dvd_two hpos hdvd with h1 | h2
      · left; refine ⟨h1, ?_⟩; rw [h1]; push_cast; omega
      · right; refine ⟨h2, ?_⟩; rw [h2]; omega
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not S1 (fun v => v.ord (jBar N -
      algebraMap ℚb 𝔽 1728) = 1)]
    rw [← Finset.sum_filter_add_sum_filter_not S1 (fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) =
      1)] at hψ₁
    have hA : ∑ v ∈ S1.filter (fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1), 2 * recipe N m v
        = 2 * ((m / 2 : ℕ) : ℤ) * ((S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) =
          1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => 2 * ((m / 2 : ℕ) : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul]; ring
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨-, hr⟩ | ⟨h2, -⟩
        · rw [hr]
        · omega
    have hB : ∑ v ∈ S1.filter (fun v => ¬ v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1), 2 * recipe N m
      v
        = 2 * (m : ℤ) * ((S1.filter fun v => ¬ v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ)
          := by
      rw [Finset.sum_congr rfl (g := fun _ => 2 * (m : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul]; ring
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨h1', -⟩ | ⟨-, hr⟩
        · exact absurd h1' h1
        · rw [hr]
    have hψA : ∑ v ∈ S1.filter (fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1), v.ord (jBar N -
      algebraMap ℚb 𝔽 1728)
        = ((S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ)) (fun v hv => (Finset.mem_filter.mp hv).2)]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hψB : ∑ v ∈ S1.filter (fun v => ¬ v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1), v.ord (jBar N
      - algebraMap ℚb 𝔽 1728)
        = 2 * ((S1.filter fun v => ¬ v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card : ℤ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (2 : ℤ)) (fun v hv => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      · obtain ⟨hv, h1⟩ := Finset.mem_filter.mp hv
        rcases hcase v hv with ⟨h1', -⟩ | ⟨h2, -⟩
        · exact absurd h1' h1
        · exact h2
    rw [hA, hB]
    rw [hψA, hψB] at hψ₁
    linear_combination (m : ℤ) * hψ₁
  have hsumI : ∑ v ∈ Sinf, recipe N m v = -(m : ℤ) * (dedekindPsi N : ℤ) - (Sinf.card : ℤ) := by
    have hψinf : ∑ v ∈ Sinf, -v.ord (jBar N) = (dedekindPsi N : ℤ) :=
      sum_neg_ord_jBar_eq_dedekindPsi N Sinf hSI
    rw [Finset.sum_congr rfl (g := fun v => -(m : ℤ) * (-v.ord (jBar N)) + (-1))
      (fun v hv => by rw [recipe_of_neg N m ((hSI v).1 hv)]; ring)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hψinf, Finset.sum_const, nsmul_eq_mul, mul_neg,
      mul_one]
    ring
  have hNC : ∀ (P : Place ℚb 𝔽 → Prop) (T : Finset (Place ℚb 𝔽)),
      (∀ v, v ∈ T ↔ P v) → Nat.card {v // P v} = T.card := by
    intro P T hT
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun v => (hT v).symm) : {v // P v} ≃ {v // v ∈ T}),
      Nat.card_eq_fintype_card, Fintype.card_coe]
  have h1728 : (jBar N - 1728 : 𝔽) = jBar N - algebraMap ℚb 𝔽 1728 := by rw [map_ofNat]
  have hε₂ : (S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1).card = nuTwo N := by
    have h2 : ∀ v : Place ℚb 𝔽, 0 < v.ord (jBar N - 1728) → v.ord (jBar N - 1728) ∣ 2 :=
      fun v hv => by
      rw [h1728] at hv ⊢
      exact ord_jBar_sub_1728_dvd_two N v hv
    have hcount : Nat.card {v : Place ℚb 𝔽 // 0 < v.ord (jBar N - 1728)}
        = Nat.card {x : ModuliPoint N ℚb // ModuliPoint.j x = (1728 : ℚb)} := by
      rw [← card_eq_natCard_moduliPoint_j_eq_of_EMD N 1728 (emd_holds N 1728) S1 hS1]
      exact hNC _ S1 (fun v => by rw [hS1, h1728])
    have h := natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo N h2 hcount
    rwa [hNC _ (S1.filter fun v => v.ord (jBar N - algebraMap ℚb 𝔽 1728) = 1)
      (fun v => by
        rw [Finset.mem_filter, hS1, h1728]
        exact ⟨fun hv => hv.2, fun hv => ⟨by rw [hv]; exact one_pos, hv⟩⟩)] at h
  have hε₃ : (S0.filter fun v => v.ord (jBar N) = 1).card = nuThree N := by
    have h3 : ∀ v : Place ℚb 𝔽, 0 < v.ord (jBar N) → v.ord (jBar N) ∣ 3 :=
      fun v hv => ord_jBar_dvd_three N v hv
    have hcount : Nat.card {v : Place ℚb 𝔽 // 0 < v.ord (jBar N)}
        = Nat.card {x : ModuliPoint N ℚb // ModuliPoint.j x = (0 : ℚb)} := by
      rw [← card_eq_natCard_moduliPoint_j_eq_of_EMD N 0 (emd_holds N 0) S0 (fun v => by rw [hS0,
        map_zero, sub_zero])]
      exact hNC _ S0 (fun v => by rw [hS0])
    have h := natCard_ord_jBar_eq_one_eq_nuThree N h3 hcount
    rwa [hNC _ (S0.filter fun v => v.ord (jBar N) = 1)
      (fun v => by
        rw [Finset.mem_filter, hS0]
        exact ⟨fun hv => hv.2, fun hv => ⟨by rw [hv]; exact one_pos, hv⟩⟩)] at h
  have hcard : Sinf.card = cuspCount N :=
    card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg N Sinf hSI
  rw [hε₃] at hsum0
  rw [hε₂] at hsum1
  rw [hcard] at hsumI
  set A0 : ℤ := ∑ v ∈ S0, recipe N m v with hA0
  set A1 : ℤ := ∑ v ∈ S1, recipe N m v with hA1
  set AI : ℤ := ∑ v ∈ Sinf, recipe N m v with hAI
  have c0 : (3 : ℚ) * (A0 : ℚ) = 3 * ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ)
      + 2 * (m : ℚ) * ((dedekindPsi N : ℚ) - (nuThree N : ℚ)) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hsum0
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast] using h
  have c1 : (2 : ℚ) * (A1 : ℚ) = 2 * ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
      + (m : ℚ) * ((dedekindPsi N : ℚ) - (nuTwo N : ℚ)) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hsum1
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast] using h
  have cI : (AI : ℚ) = -(m : ℚ) * (dedekindPsi N : ℚ) - (cuspCount N : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) hsumI
    simpa only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_ofNat,
      Int.cast_natCast] using h
  have eD : (D.degree : ℚ) = (A0 : ℚ) + (A1 : ℚ) + (AI : ℚ) := by
    rw [hdegsum, hsplit]; push_cast; ring
  unfold genusFormula
  linear_combination eD + (1 / 3 : ℚ) * c0 + (1 / 2 : ℚ) * c1 + cI

end ModularCurve.LDivDegree

p2m_open "ModularCurve \
  P2MW.S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace.ModularCu\
  rve AlgebraicCurve"


noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jBar modularFunctionFieldBar jq coeff_jq_neg_one dedekindPsi coeffEmb \
  coeffEmb_coeff nuTwo nuThree cuspCount genusFormula EMD ModuliPoint ModuliPoint.j \
  sum_ord_jBar_sub_eq_dedekindPsi deg_eq_one_modularFunctionFieldBar \
  jCoordinate_spec_modularFunctionFieldBar sum_neg_ord_jBar_eq_dedekindPsi ord_jBar_dvd_three \
  ord_jBar_sub_1728_dvd_two card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg \
  natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo natCard_ord_jBar_eq_one_eq_nuThree \
  card_eq_natCard_moduliPoint_j_eq_of_EMD emd_holds transcendental_coeffEmb_jq \
  isCurveOver_modularFunctionFieldBar finiteDimensional_adjoin_coeffEmb_jq_of_neZero \
  dedekindPsi_pos"
namespace LDivIntegral
p2m_open "ModularCurve"

variable (N : ℕ) [NeZero N]

theorem jBar_ne_zero : (jBar N : modularFunctionFieldBar N) ≠ 0 := by
  intro h
  have h2 : (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1) = 0 := by
    have h1 : ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
      rw [h]; rfl
    have : (coeffEmb (AlgebraicClosure ℚ) jq) = 0 := h1
    rw [this]; rfl
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h2
  exact one_ne_zero h2

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pow' (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

theorem ord_algebraMap (v : Place K F) {c : K} : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h1 : v.ord (-f) = v.ord (-1) + v.ord f := by
    rw [← v.ord_mul (by norm_num) hf, neg_one_mul]
  have h2 : v.ord ((-1 : F)) = 0 := by
    have := v.ord_zpow (-1 : F) 2
    norm_num at this
    linarith
  rw [h1, h2, zero_add]

theorem six_mul_ediv_two_le (n : ℤ) : 6 * (n / 2) ≤ 3 * n := by
  have := Int.ediv_mul_le n (by norm_num : (2 : ℤ) ≠ 0)
  linarith

theorem six_mul_ediv_three_le (n : ℤ) : 6 * (n / 3) ≤ 2 * n := by
  have := Int.ediv_mul_le n (by norm_num : (3 : ℤ) ≠ 0)
  linarith

theorem two_mul_ediv_two_le (n : ℤ) : 2 * (n / 2) ≤ n := by
  have := Int.ediv_mul_le n (by norm_num : (2 : ℤ) ≠ 0)
  linarith

end Generic

theorem isIntegral_pair_of_mem_riemannRochSpace (m : ℕ)
    (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hDfin : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ v.ord (jBar N) →
      Dv v ≤ (m : ℤ) * v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        1728) / 2
        + 2 * (m : ℤ) * v.ord (jBar N) / 3)
    (hDcusp : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord (jBar N) < 0 →
      Dv v ≤ (m : ℤ) * v.ord (jBar N) - 1)
    (x : modularFunctionFieldBar N) (hx : x ∈ riemannRochSpace Dv) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))
        (x ^ 6 * jBar N ^ (4 * m)
          * (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728) ^ (3 * m)) ∧
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar
        N)))
        (x ^ (2 * dedekindPsi N) * jBar N ^ (m * dedekindPsi N + 1)
          * (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1728) ^ (m *
            dedekindPsi N)) := by
  classical
  have hCO := ModularCurve.isCurveOver_modularFunctionFieldBar N
  have hFD : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
        (modularFunctionFieldBar N) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  have hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    IsCurveOver.hasPrincipalDivisors
  set J : modularFunctionFieldBar N := jBar N with hJdef
  set ψ : ℕ := dedekindPsi N with hψdef
  set c1728 : modularFunctionFieldBar N := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar
    N) 1728
    with hc
  have hψpos : 0 < ψ := ModularCurve.dedekindPsi_pos N (NeZero.ne N)
  have hJ0 : J ≠ 0 := jBar_ne_zero N
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨?_, ?_⟩
    · rw [zero_pow (by norm_num), zero_mul, zero_mul]; exact isIntegral_zero
    · rw [zero_pow (by omega), zero_mul, zero_mul]; exact isIntegral_zero
  have hxord : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), -Dv v ≤ v.ord x := by
    intro v
    rcases (mem_riemannRochSpace_iff.mp hx) v with h | h
    · exact absurd h hx0
    · exact h
  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (F := modularFunctionFieldBar N) J hJ0
  let S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    Dj.support.filter (fun v => v.ord J < 0)
  have hS : ∀ v, v ∈ S ↔ v.ord J < 0 := by
    intro v
    simp only [S, Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
    intro hv
    rw [hDj v]
    exact hv.ne
  have hsum : ∑ v ∈ S, -v.ord J = (ψ : ℤ) := by
    have := ModularCurve.sum_neg_ord_jBar_eq_dedekindPsi N S hS
    exact_mod_cast this
  have hwidth : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord J < 0 → -v.ord J
    ≤ (ψ : ℤ) :=
    by
    intro v hv
    rw [← hsum]
    exact Finset.single_le_sum (f := fun w => -w.ord J)
      (fun w hw => by have := (hS w).mp hw; change (0 : ℤ) ≤ -w.ord J; omega) ((hS v).mpr hv)
  have hpole : ∃ v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v₀.ord J < 0 := by
    by_contra hno
    push Not at hno
    have hSe : S = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      exact absurd ((hS v).mp hv) (not_lt.mpr (hno v))
    rw [hSe, Finset.sum_empty] at hsum
    have h' : (ψ : ℤ) = 0 := hsum.symm
    omega
  obtain ⟨v₀, hv₀⟩ := hpole
  have htr : Transcendental (AlgebraicClosure ℚ) J := by
    intro halg
    have hint : IsIntegral (AlgebraicClosure ℚ) J := halg.isIntegral
    have hint' : IsIntegral v₀.toValuationSubring J := hint.tower_top
    have hmem : J ∈ v₀.toValuationSubring := by
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v₀.toValuationSubring)
        (K := modularFunctionFieldBar N)).mp hint'
      rw [← hy]
      exact y.2
    have := v₀.ord_nonneg_of_mem hmem
    omega
  have h1728ne : (1728 : AlgebraicClosure ℚ) ≠ 0 := by norm_num
  have hJne1728 : J - c1728 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have := ord_algebraMap v₀ (c := (1728 : AlgebraicClosure ℚ))
    rw [hc] at h
    rw [← h] at this
    omega
  have hordJsub_of_neg : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord J < 0 →
      v.ord (J - c1728) = v.ord J := by
    intro v hv
    have hc0 : v.ord (-c1728) = 0 := by rw [ord_neg]; exact ord_algebraMap v
    have := v.ord_add_eq_of_lt (f := J) (g := -c1728) hJ0
      (neg_ne_zero.mpr (by rw [hc, Ne, map_eq_zero]; norm_num)) (by rw [hc0]; exact hv)
    rwa [← sub_eq_add_neg] at this
  have hordJsub_nonneg : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ v.ord J →
      0 ≤ v.ord (J - c1728) := by
    intro v hv
    have hJmem : J ∈ v.toValuationSubring := (v.mem_iff_ord_nonneg hJ0).mpr hv
    exact v.ord_nonneg_of_mem (sub_mem hJmem (v.algebraMap_mem' _))
  refine ⟨?_, ?_⟩
  · refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar N) J _ ?_
    intro v hvJ
    have ha := hordJsub_nonneg v hvJ
    have hD := hDfin v hvJ
    have hxv := hxord v
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), ord_pow', ord_pow', ord_pow']
    have h2 := six_mul_ediv_two_le ((m : ℤ) * v.ord (J - c1728))
    have h3 := six_mul_ediv_three_le (2 * (m : ℤ) * v.ord J)
    push_cast
    nlinarith
  · have htr' : Transcendental (AlgebraicClosure ℚ) J⁻¹ := by
      intro halg
      exact htr (by simpa using halg.inv)
    have hadj : IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set (modularFunctionFieldBar
      N))
        = IntermediateField.adjoin (AlgebraicClosure ℚ) ({J} : Set (modularFunctionFieldBar N))
          := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) J)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have h1 := IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) (J⁻¹)
        have h2 : (J⁻¹)⁻¹ ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set
          (modularFunctionFieldBar N)) :=
          inv_mem h1
        rwa [inv_inv] at h2
    have : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({J⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) := by
      rw [hadj]; exact hFD
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar N) J⁻¹ _ ?_
    intro v hvJinv
    rw [v.ord_inv] at hvJinv
    have hvJ : v.ord J ≤ 0 := by omega
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), ord_pow', ord_pow', ord_pow']
    have hxv := hxord v
    rcases hvJ.lt_or_eq with hneg | hzero
    · have hw := hwidth v hneg
      have hD := hDcusp v hneg
      rw [hordJsub_of_neg v hneg]
      have hψ1 : (1 : ℤ) ≤ ψ := by exact_mod_cast hψpos
      push_cast
      have hx1 : 1 - (m : ℤ) * v.ord J ≤ v.ord x := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℤ) ≤ 2 * (ψ : ℤ))]
    · have ha := hordJsub_nonneg v hzero.ge
      have hD := hDfin v hzero.ge
      rw [hzero, mul_zero, Int.zero_ediv, add_zero] at hD
      have h2 := two_mul_ediv_two_le ((m : ℤ) * v.ord (J - c1728))
      rw [hzero]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (show -( (m : ℤ) * v.ord (J - c1728) / 2) ≤ v.ord x by
        linarith)
        (by positivity : (0 : ℤ) ≤ 2 * (ψ : ℤ))]

end ModularCurve.LDivIntegral

end

theorem solution (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ((D.degree : ℚ) + 1 - ModularCurve.genusFormula N =
        (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) *
          (ModularCurve.nuTwo N : ℚ)
          + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) *
            (ModularCurve.cuspCount N : ℚ)) ∧
      ∀ x : ↥(ModularCurve.modularFunctionFieldBar N), x ∈ AlgebraicCurve.riemannRochSpace D →
        IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({ModularCurve.jBar N} : Set
          ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ 6 * ModularCurve.jBar N ^ (4 * m) * (ModularCurve.jBar N - algebraMap
              (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (3 * m)) ∧
          IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.jBar N)⁻¹} : Set
            ↥(ModularCurve.modularFunctionFieldBar N)))
              (x ^ (2 * ModularCurve.dedekindPsi N) * ModularCurve.jBar N ^ (m *
                ModularCurve.dedekindPsi N + 1) *
              (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ)
                ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (m * ModularCurve.dedekindPsi N))
                := by
  have hm_copy := hm
  clear hm_copy
  obtain ⟨D, hdeg, hDfin, hDcusp⟩ := ModularCurve.LDivDegree.exists_weightDivisor N m
  exact ⟨D, hdeg, fun x hx =>
    ModularCurve.LDivIntegral.isIntegral_pair_of_mem_riemannRochSpace N m D hDfin hDcusp x hx⟩

end S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace
end P2MW
export P2MW.S_ModularCurve_exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace
  (solution)

end privateSection

public section publicSection


open ModularCurve AlgebraicCurve
theorem ModularCurve.exists_divisor_degree_weight_and_isIntegral_of_mem_riemannRochSpace (N : ℕ)
    [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    ∃ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ((D.degree : ℚ) + 1 - ModularCurve.genusFormula N =
        (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + ((m / 2 : ℕ) : ℚ) *
          (ModularCurve.nuTwo N : ℚ)
          + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + ((m : ℚ) - 1) *
            (ModularCurve.cuspCount N : ℚ)) ∧
      ∀ x : ↥(ModularCurve.modularFunctionFieldBar N), x ∈ AlgebraicCurve.riemannRochSpace D →
        IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({ModularCurve.jBar N} : Set
          ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ 6 * ModularCurve.jBar N ^ (4 * m) * (ModularCurve.jBar N - algebraMap
              (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (3 * m)) ∧
          IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.jBar N)⁻¹} : Set
            ↥(ModularCurve.modularFunctionFieldBar N)))
            (x ^ (2 * ModularCurve.dedekindPsi N) * ModularCurve.jBar N ^ (m *
              ModularCurve.dedekindPsi N + 1) *
              (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ)
                ↥(ModularCurve.modularFunctionFieldBar N) 1728) ^ (m * ModularCurve.dedekindPsi N))
                :=
  solution N m hm

end publicSection
