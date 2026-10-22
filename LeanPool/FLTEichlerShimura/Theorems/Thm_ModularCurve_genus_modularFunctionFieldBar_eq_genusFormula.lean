/-
Based on Prove2Me node ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula
(db11f309-8d92-554c-9c92-76fbdde0c34f) by Claude (2026-09-05).

Proof based on Prove2Me submission 1e0413be-2860-50e9-8736-e2fdfd92fd40
by Claude (2026-09-05); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_CanonicalDivisor
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_ArithmeticGalois
public import LeanPool.FLTEichlerShimura.Definitions.Def_ModularCurve_GenusNumerics

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ordDiff_D_eq_ord_sub_one
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_twelve_mul_eq_of_sum_ordDiff_eq
import LeanPool.FLTEichlerShimura.Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_card_eq_natCard_moduliPoint_j_eq_of_EMD
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_emd_holds
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_jCoordinate_spec_modularFunctionFieldBar
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_natCard_ord_jBar_eq_one_eq_nuThree
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ord_jBar_dvd_three
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ord_jBar_sub_1728_dvd_two
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import LeanPool.FLTEichlerShimura.Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import LeanPool.FLTEichlerShimura.Definitions.Def_P2M_Util

/-!
# Genus of the modular function field equals 1+ψ/12-ν₂/4-ν₃/3-c_∞/2

Theorem statement: `ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula`
(`db11f309-8d92-554c-9c92-76fbdde0c34f`), by Claude, 2026-09-05.

Proof: submission `1e0413be-2860-50e9-8736-e2fdfd92fd40`, by Claude, 2026-09-05 (ACCEPTED); locally
adapted.

Let $N$ be a nonzero natural number and let $F_N$ denote the field
[`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), that is the
intermediate field of $\overline{\mathbb Q}((q))$ generated over $K = \overline{\mathbb Q} =$
`AlgebraicClosure ℚ` by the image, under the coefficient embedding of $\mathbb Q((q))$ into
$\overline{\mathbb Q}((q))$, of the field `modularFunctionFieldFull N` obtained by adjoining to
$\mathbb Q$ inside $\mathbb Q((q))$ the family `divisorExpansions N`. Assume `HasCanonicalDivisor`
for the extension $K \subseteq F_N$: for every nonzero Kähler differential $\omega \in
\Omega_{F_N/K}$ the function $v \mapsto v.\mathrm{ordDifferential}\,\omega$ on the places of $F_N$
over $K$ is finitely supported, hence is a divisor. Then the natural number
[`AlgebraicCurve.genus`](def/AlgebraicCurve_CanonicalDivisor.html#L33) of $K \subseteq F_N$ —
computed as $(\deg D + 2).\mathrm{toNat}$ divided by $2$ in $\mathbb N$, for $D$ the canonical
divisor attached to some nonzero differential, and $0$ if none exists — equals, after casting to
$\mathbb Q$, the rational number $$1 + \frac{\psi(N)}{12} - \frac{\nu_2(N)}{4} - \frac{\nu_3(N)}{3}
- \frac{c_\infty(N)}{2},$$ where $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, $\nu_2(N) =
\#\{x \in \mathbb Z/N : x^2+1 = 0\}$, $\nu_3(N) = \#\{x \in \mathbb Z/N : x^2+x+1 = 0\}$ and
$c_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$. In particular this rational number is a
nonnegative integer.

This is the classical genus formula for the modular curve $X_0(N)$, here expressed through the
divisor-theoretic genus of its function field over $\overline{\mathbb Q}$, with $\psi(N) =
[\mathrm{SL}_2(\mathbb Z):\Gamma_0(N)]$, $\nu_2$ and $\nu_3$ counting elliptic points of orders $2$
and $3$, and $c_\infty$ the number of cusps. It feeds the comparison between the genus and the
dimension of the space of weight-two cusp forms for $\Gamma_0(N)$, used in
[`CuspForm.dimFormula_le_finrank_gamma0`](thm.html#CuspForm.dimFormula_le_finrank_gamma0) and
[`CuspForm.genusFormula_le_finrank_gamma0_weight_two`]
(thm.html#CuspForm.genusFormula_le_finrank_gamma0_weight_two).

## Explanation of the source proof

Proof transplanted from the FLT repository:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula.lean

<!-- Generated by add_prove2me_provenance.py -->
-/

set_option maxHeartbeats 6400000

section privateSection


namespace P2MW.S_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula


open ModularCurve AlgebraicCurve IntermediateField

theorem solution (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F :=
      ↥(ModularCurve.modularFunctionFieldBar N))] :
    (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℚ)
      = ModularCurve.genusFormula N := by
  classical
  set F := ↥(modularFunctionFieldBar N) with hF
  set j : ↥(modularFunctionFieldBar N) := jBar N with hj
  have hjdef : j = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        ↥(modularFunctionFieldBar N)) := rfl
  have h1728 : (j - 1728 : ↥(modularFunctionFieldBar N))
      = j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728 := by
    rw [map_ofNat]
  have : CharZero ↥(modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    isCurveOver_modularFunctionFieldBar N
  have : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    IsCurveOver.hasPrincipalDivisors
  have : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    essFiniteType_modularFunctionFieldBar N
  have hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set
    ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) := finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  have : CharZero ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set
    ↥(modularFunctionFieldBar N))) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have : PerfectField ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set
    ↥(modularFunctionFieldBar N))) :=
    PerfectField.ofCharZero
  have : Algebra.IsIntegral ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set
    ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) := Algebra.IsIntegral.of_finite _ _
  have : Algebra.IsSeparable ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set
    ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) := Algebra.IsSeparable.of_integral _ _
  have htr : Transcendental (AlgebraicClosure ℚ) j :=
    transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  have hdeg : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), w.deg = 1 :=
    deg_eq_one_modularFunctionFieldBar N
  obtain ⟨hval, hfinc, hfinI⟩ := jCoordinate_spec_modularFunctionFieldBar N
  set S0 : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := (hfinc 0).toFinset
    with hS0def
  set S1 : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := (hfinc 1728).toFinset
    with hS1def
  set Sinf : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := hfinI.toFinset with
    hSIdef
  have hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord j := fun v => by
    rw [hS0def, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, map_zero, sub_zero]
  have hS1 : ∀ v, v ∈ S1 ↔ 0 < v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar
    N) 1728) :=
    fun v => by rw [hS1def, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hSI : ∀ v, v ∈ Sinf ↔ v.ord j < 0 := fun v => by
    rw [hSIdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hDj1728 : KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j
      = KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)
          (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  have h₀ : ∀ v ∈ S0, v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ)
    ↥(modularFunctionFieldBar N) j) = v.ord j - 1
      ∧ 0 < v.ord j ∧ v.ord j ∣ 3 := fun v hv => by
    have hpos := (hS0 v).1 hv
    exact ⟨AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one j v hpos.ne', hpos, ord_jBar_dvd_three N v
      hpos⟩
  have h₁ : ∀ v ∈ S1,
      v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j)
        = v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) - 1
      ∧ 0 < v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728)
      ∧ v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) ∣ 2 := fun v
        hv => by
    have hpos := (hS1 v).1 hv
    refine ⟨?_, hpos, ord_jBar_sub_1728_dvd_two N v hpos⟩
    rw [hDj1728]
    exact AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one j v hpos.ne'
  have hinf : ∀ v ∈ Sinf, v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ)
    ↥(modularFunctionFieldBar N) j) = v.ord j - 1
      ∧ v.ord j < 0 := fun v hv => by
    have hneg := (hSI v).1 hv
    exact ⟨AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one j v hneg.ne, hneg⟩
  have hψ₀ : ∑ v ∈ S0, v.ord j = (dedekindPsi N : ℤ) := by
    have h := sum_ord_jBar_sub_eq_dedekindPsi N 0 hdeg S0 (fun v => by rw [hS0, map_zero, sub_zero])
    simpa [map_zero, sub_zero] using h
  have hψ₁ : ∑ v ∈ S1, v.ord (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728)
    = (dedekindPsi N : ℤ) :=
    sum_ord_jBar_sub_eq_dedekindPsi N 1728 hdeg S1 hS1
  have hψinf : ∑ v ∈ Sinf, -v.ord j = (dedekindPsi N : ℤ) :=
    sum_neg_ord_jBar_eq_dedekindPsi N Sinf hSI
  set S := S0 ∪ S1 ∪ Sinf with hSdef
  have hS : ∀ v, v ∈ S ↔ v ∈ S0 ∨ v ∈ S1 ∨ v ∈ Sinf := fun v => by
    simp only [hSdef, Finset.mem_union, or_assoc]
  have hDj : KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental (AlgebraicClosure ℚ) j htr
  have hoff : ∀ v, v ∉ S → v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ)
    ↥(modularFunctionFieldBar N) j) = 0 :=
    by
    intro v hv
    rw [hS] at hv
    push Not at hv
    obtain ⟨hv0, hv1, hvI⟩ := hv
    have hnonneg : 0 ≤ v.ord j := by
      by_contra h
      exact hvI ((hSI v).2 (lt_of_not_ge h))
    obtain ⟨c, hcpos, -⟩ := hval v hnonneg
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv0
      rw [hS0]
      simpa [map_zero, sub_zero] using hcpos
    have hc1728 : c ≠ 1728 := by
      rintro rfl
      exact hv1 ((hS1 v).2 hcpos)
    have hone := ord_jBar_sub_eq_one_of_ne_zero_of_ne N v c hc0 hc1728 hcpos
    have hD : KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j
        = KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)
            (j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c) := by
      rw [map_sub, Derivation.map_algebraMap, sub_zero]
    rw [hD, AlgebraicCurve.Place.ordDiff_D_eq_ord_sub_one j v (by
      rw [hone]; exact one_ne_zero), hone]
    norm_num
  have hcan : ∑ v ∈ S, v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ)
    ↥(modularFunctionFieldBar N) j)
      = 2 * (genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) - 2 := by
    rw [← degree_canonicalDivisorOf_modularFunctionFieldBar N hDj]
    set Kd := canonicalDivisorOf hDj with hKd
    have hseam : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        v.ordDiff (KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) j) = Kd v
          := fun v => by
      rw [hKd, canonicalDivisorOf_apply, AlgebraicCurve.Place.ordDiff_eq_ordDifferential]
    have hsupp : Kd.support ⊆ S := by
      intro v hv
      by_contra hvS
      rw [Finsupp.mem_support_iff] at hv
      exact hv ((hseam v).symm.trans (hoff v hvS))
    have hdegsum : Divisor.degree Kd = ∑ v ∈ Kd.support, Kd v := by
      rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [AddMonoidHom.mulRight_apply, hdeg v, Nat.cast_one, mul_one]
    rw [hdegsum, Finset.sum_subset hsupp (fun v _ hv => by
      simpa [Finsupp.mem_support_iff] using hv)]
    exact Finset.sum_congr rfl (fun v _ => hseam v)
  have hHE := AlgebraicCurve.twelve_mul_eq_of_sum_ordDiff_eq j S0 S1 Sinf (dedekindPsi N)
    (genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) h₀ h₁ hinf hψ₀ hψ₁ hψinf S hS hcan
  have hNC : ∀ (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) → Prop)
      (T : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))),
      (∀ v, v ∈ T ↔ P v) → Nat.card {v // P v} = T.card := by
    intro P T hT
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun v => (hT v).symm) : {v // P v} ≃ {v // v ∈ T}),
      Nat.card_eq_fintype_card, Fintype.card_coe]
  have hε₂ : (S1.filter fun v => v.ord (j - algebraMap (AlgebraicClosure ℚ)
    ↥(modularFunctionFieldBar N) 1728) = 1).card
      = nuTwo N := by
    have h2 : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        0 < v.ord (jBar N - 1728) → v.ord (jBar N - 1728) ∣ 2 := fun v hv => by
      rw [← hj, h1728] at hv ⊢
      exact ord_jBar_sub_1728_dvd_two N v hv
    have hcount : Nat.card {v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) // 0 < v.ord
      (jBar N - 1728)}
        = Nat.card {x : ModuliPoint N (AlgebraicClosure ℚ) // ModuliPoint.j x = (1728 :
          AlgebraicClosure ℚ)} := by
      rw [← card_eq_natCard_moduliPoint_j_eq_of_EMD N 1728 (emd_holds N 1728) S1 hS1]
      exact hNC _ S1 (fun v => by rw [hS1, ← hj, h1728])
    have h := natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo N h2 hcount
    rwa [hNC _ (S1.filter fun v => v.ord (j - algebraMap (AlgebraicClosure ℚ)
      ↥(modularFunctionFieldBar N) 1728) = 1)
      (fun v => by
        rw [Finset.mem_filter, hS1, ← hj, h1728]
        exact ⟨fun hv => hv.2, fun hv => ⟨by rw [hv]; exact one_pos, hv⟩⟩)] at h
  have hε₃ : (S0.filter fun v => v.ord j = 1).card = nuThree N := by
    have h3 : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        0 < v.ord (jBar N) → v.ord (jBar N) ∣ 3 := fun v hv => ord_jBar_dvd_three N v hv
    have hcount : Nat.card {v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) // 0 < v.ord
      (jBar N)}
        = Nat.card {x : ModuliPoint N (AlgebraicClosure ℚ) // ModuliPoint.j x = (0 :
          AlgebraicClosure ℚ)} := by
      rw [← card_eq_natCard_moduliPoint_j_eq_of_EMD N 0 (emd_holds N 0) S0 (fun v => by rw [hS0, hj,
        map_zero, sub_zero])]
      exact hNC _ S0 (fun v => by rw [hS0, hj])
    have h := natCard_ord_jBar_eq_one_eq_nuThree N h3 hcount
    rwa [hNC _ (S0.filter fun v => v.ord j = 1)
      (fun v => by
        rw [Finset.mem_filter, hS0, hj]
        exact ⟨fun hv => hv.2, fun hv => ⟨by rw [hv]; exact one_pos, hv⟩⟩)] at h
  have hcard : Sinf.card = cuspCount N :=
    card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg N Sinf hSI
  rw [hε₂, hε₃, hcard] at hHE
  have key : (12 : ℚ) * (genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℚ)
      = 12 + (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ) - 6 * (cuspCount N : ℚ)
        := by
    exact_mod_cast hHE
  unfold genusFormula
  linarith [key]

end S_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula
end P2MW
export P2MW.S_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula (solution)

end privateSection

public section publicSection

theorem ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F :=
      ↥(ModularCurve.modularFunctionFieldBar N))] :
    (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℚ)
      = ModularCurve.genusFormula N :=
  solution N

end publicSection
