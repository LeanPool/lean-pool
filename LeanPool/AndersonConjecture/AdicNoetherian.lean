/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import LeanPool.AndersonConjecture.AdicKerEval
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.CategoryTheory.Category.Init
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.Tactic.Positivity.Finset

/-!
# Adic Completion of a Noetherian Local Ring is Noetherian

For a Noetherian local ring (R, M), the M-adic completion R-hat
is Noetherian. The key facts are that R-hat / M-hat^n is
isomorphic to R / M^n for each n, and that the completion is
M-adically complete, so the Noetherian property lifts by
successive approximation (Atiyah--Macdonald, Prop. 10.11).
-/

@[expose] public section

open AdicCompletion

open scoped Pointwise

variable {R : Type*} [CommRing R]

/-! ### Part 1: ker(evalₐ I n) = (map f I)ⁿ -/

section KernelEvalₐ

variable (I : Ideal R)

/- `(map f I)ⁿ ⊆ ker(evalₐ I n)`: elements from I^n evaluate to zero. -/
include R in
lemma map_pow_le_ker_evalₐ (n : ℕ) :
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) ≤
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  change (evalₐ I n) (of I R r) = 0
  rw [evalₐ_of]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/- `ker(evalₐ M n) = M̂ⁿ` for Noetherian local R. -/
include R in
lemma ker_evalₐ_eq [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (evalₐ (IsLocalRing.maximalIdeal R) n).toRingHom =
    Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
      (IsLocalRing.maximalIdeal R) ^ n := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hx
    exact mem_map_pow_of_evalₐ_eq_zero R n x hx
  · rw [← Ideal.map_pow]
    exact map_pow_le_ker_evalₐ (IsLocalRing.maximalIdeal R) n

/- Evaluations are stable along Cauchy sequences. -/
include R in
lemma eval_cauchy_stable (f : ℕ → AdicCompletion I R)
    (hf : ∀ {m n : ℕ}, m ≤ n →
      SModEq (I ^ m • (⊤ : Submodule R (AdicCompletion I R))) (f m) (f n))
    {k n : ℕ} (hkn : k ≤ n) :
    evalₐ I k (f n) = evalₐ I k (f k) := by
  have hmem := hf hkn
  rw [SModEq.sub_mem, Ideal.smul_top_eq_map] at hmem
  have := map_pow_le_ker_evalₐ I k hmem
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, sub_eq_zero] at this
  exact this.symm

/- `factorPow ∘ evalₐ n = evalₐ m` for m ≤ n. -/
include R in
lemma factorPow_comp_evalₐ_noeth {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x := by
  apply induction_on I R
    (p := fun x => Ideal.Quotient.factorPow I hmn (evalₐ I n x) = evalₐ I m x) x
  intro a
  simp only [evalₐ_mk]
  have hfactor : Ideal.Quotient.factorPow I hmn (Ideal.Quotient.mk (I ^ n) (a.1 n)) =
      Ideal.Quotient.mk (I ^ m) (a.1 n) := by
    simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [hfactor]
  have hcauchy := a.2 hmn
  rw [SModEq.sub_mem] at hcauchy
  have hmem : a.1 m - a.1 n ∈ (I ^ m : Ideal R) := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hcauchy
  rw [Ideal.Quotient.eq]
  rwa [show a.1 n - a.1 m = -(a.1 m - a.1 n) from by ring, neg_mem_iff]

end KernelEvalₐ

/-! ### Part 2: R̂/M̂ⁿ ≅ R/Mⁿ -/

section QuotientIso

variable [IsLocalRing R] [IsNoetherianRing R]

/-- `R̂ / M̂ⁿ ≅ R / Mⁿ` as rings. -/
noncomputable def quotientPowEquiv (n : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
      (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
        (IsLocalRing.maximalIdeal R)) ^ n ≃+*
    R ⧸ (IsLocalRing.maximalIdeal R) ^ n := by
  have hker := ker_evalₐ_eq (R := R) n
  have hsurj := surjective_evalₐ (IsLocalRing.maximalIdeal R) n
  exact (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective hsurj)

end QuotientIso

/-! ### Part 3: IsPrecomplete M (AdicCompletion M R) -/

section Precomplete

variable [IsLocalRing R] [IsNoetherianRing R]

/-- The adic completion of a Noetherian local ring is M-adically precomplete. -/
instance adicCompletion_isPrecomplete :
    IsPrecomplete (IsLocalRing.maximalIdeal R)
      (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (AdicCompletion.isAdicComplete (M := R)
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing).toIsPrecomplete

end Precomplete

/-! ### Part 4: Main theorem — IsNoetherianRing R̂ -/

section Main

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Generic helper: build a recursive sequence with proof-carrying data.
This is a standalone `def` so its elaboration budget is independent. -/
noncomputable def buildAdicSeq {α : Type*} {P : ℕ → α → Prop}
    (base : { a // P 0 a })
    (step : ∀ K, { a // P K a } → { a // P (K + 1) a }) :
    ∀ K, { a // P K a } :=
  fun K => Nat.rec base (fun K prev => step K prev) K

/- Auxiliary: M * FN(n) ≤ FN(n+1) for the leading-term filtration FN. -/
omit [IsLocalRing R] [IsNoetherianRing R] in
lemma filtration_smul_le
    (Mi : Ideal R) (J : Ideal (AdicCompletion Mi R))
    (FN : ℕ → Ideal R)
    (hFN_def : ∀ n, FN n = Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J))
    (n : ℕ) :
    Mi * FN n ≤ FN (n + 1) := by
  rw [Ideal.mul_le]
  intro m hm r hr_mem
  rw [hFN_def] at hr_mem
  obtain ⟨hr_pow, hr_comap⟩ := hr_mem
  rw [hFN_def]
  refine ⟨?_, ?_⟩
  · rw [pow_succ']
    exact Ideal.mul_mem_mul hm hr_pow
  · obtain ⟨y, hyJ, hyr⟩ := (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1))).mp hr_comap
    have hmyJ : of Mi R m * y ∈ J := J.mul_mem_left _ hyJ
    apply (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1 + 1))).mpr
    refine ⟨of Mi R m * y, hmyJ, ?_⟩
    have hlhs : evalₐ Mi (n + 1 + 1) (of Mi R m * y) =
        Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m * evalₐ Mi (n + 1 + 1) y := by
      simp [map_mul, evalₐ_of]
    rw [hlhs]
    have hfp_y : Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))
        (evalₐ Mi (n + 1 + 1) y) = evalₐ Mi (n + 1) y :=
      factorPow_comp_evalₐ_noeth Mi (Nat.le_succ (n + 1)) y
    have hfp_r : Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))
        (Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r) =
        Ideal.Quotient.mk (Mi ^ (n + 1)) r := by
      simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    have hdiff_quot : evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r ∈
        RingHom.ker (Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1))) := by
      rw [RingHom.mem_ker, map_sub, hfp_y, hfp_r, hyr, sub_self]
    rw [show Ideal.Quotient.factorPow Mi (Nat.le_succ (n + 1)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) from rfl,
      Ideal.Quotient.factor_ker] at hdiff_quot
    obtain ⟨s, hs, hseq⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hdiff_quot
    suffices h0 : Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m *
        (evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r) = 0 by
      have := h0
      rw [mul_sub] at this
      rw [show Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) m *
          Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r =
          Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) (m * r) from by rw [← map_mul]] at this
      exact sub_eq_zero.mp this
    have hseq' : Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) s =
        evalₐ Mi (n + 1 + 1) y - Ideal.Quotient.mk (Mi ^ (n + 1 + 1)) r := hseq
    rw [← hseq', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    rw [show n + 1 + 1 = (n + 1).succ from rfl, pow_succ']
    exact Ideal.mul_mem_mul hm hs

/- Auxiliary: the shared coefficient-matching step for a single smul generator. -/
omit [IsLocalRing R] [IsNoetherianRing R] in
lemma evalₐ_mk_smul_eq
    (Mi : Ideal R) (n0 K : ℕ) (m s : R) (hm : m ∈ (Mi ^ K : Ideal R))
    (δ_s : AdicCompletion Mi R)
    (hδ_s_eq : evalₐ Mi (n0 + 1) δ_s = Ideal.Quotient.mk (Mi ^ (n0 + 1)) s) :
    Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) m * evalₐ Mi (n0 + K + 1) δ_s =
      Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) (m • s) := by
  have hdiff_ker : evalₐ Mi (n0 + K + 1) δ_s -
      Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) s ∈
      RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (show n0 + 1 ≤ n0 + K + 1 by omega))) := by
    rw [RingHom.mem_ker, map_sub,
      show Ideal.Quotient.factor _ (evalₐ Mi (n0 + K + 1) δ_s) =
        evalₐ Mi (n0 + 1) δ_s from factorPow_comp_evalₐ_noeth Mi (by omega) δ_s,
      hδ_s_eq, Ideal.Quotient.factor_mk, sub_self]
  rw [Ideal.Quotient.factor_ker] at hdiff_ker
  have hmk_kills : Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) m *
      (evalₐ Mi (n0 + K + 1) δ_s -
        Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) s) = 0 := by
    obtain ⟨q, hq_mem, hq_eq⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hdiff_ker
    rw [← hq_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_pow_right (by omega)
      (show m * q ∈ Mi ^ (K + (n0 + 1)) by
         rw [pow_add]
         exact Ideal.mul_mem_mul hm hq_mem)
  rw [mul_sub] at hmk_kills
  rw [sub_eq_zero.mp hmk_kills, show m • s = m * s from rfl, ← map_mul]

/- Auxiliary: lift elements of Mi^K • FN(n0) to I₀ with evalₐ compatibility. -/
omit [IsLocalRing R] [IsNoetherianRing R] in lemma smul_lift_of_filtration
    (Mi : Ideal R)
    (n0 K : ℕ)
    (FN_n0 : Ideal R)
    (S_F : Finset R) (hS_F : Ideal.span ↑S_F = FN_n0)
    (I₀ : Ideal (AdicCompletion Mi R))
    (hlift_span : ∀ t : R, t ∈ (Ideal.span ↑S_F : Ideal R) →
        ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
        evalₐ Mi (n0 + 1) δ = Ideal.Quotient.mk (Mi ^ (n0 + 1)) t)
    (r' : R) (hr' : r' ∈ (Mi ^ K • (FN_n0 : Submodule R R) : Submodule R R)) :
    ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
      evalₐ Mi (n0 + K + 1) δ =
      Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) r' := by
  refine Submodule.smul_induction_on hr' ?_ ?_
  · intro m hm s hs
    have hs_span : s ∈ (Ideal.span ↑S_F : Ideal R) :=
      hS_F ▸ hs
    obtain ⟨δ_s, hδ_s_I, hδ_s_eq⟩ := hlift_span s hs_span
    refine ⟨of Mi R m * δ_s, I₀.mul_mem_left _ hδ_s_I, ?_⟩
    rw [map_mul, evalₐ_of]
    exact evalₐ_mk_smul_eq R Mi n0 K m s hm δ_s hδ_s_eq
  · intro a b ⟨δa, hδaI, hδaeq⟩ ⟨δb, hδbI, hδbeq⟩
    exact ⟨δa + δb, I₀.add_mem hδaI hδbI, by rw [map_add, hδaeq, hδbeq, map_add]⟩

/- Auxiliary: per-generator coefficient decomposition for r' ∈ Mi^K • FN_n0. -/
omit [IsLocalRing R] [IsNoetherianRing R] in
lemma coeff_decomp_of_smul
    (Mi : Ideal R)
    (n0 K : ℕ)
    (FN_n0 : Ideal R)
    (S_F : Finset R) (hS_F : Ideal.span ↑S_F = FN_n0)
    (genS : Finset (AdicCompletion Mi R))
    (I₀ : Ideal (AdicCompletion Mi R))
    (hI₀_eq : I₀ = Ideal.span (↑genS : Set (AdicCompletion Mi R)))
    (hlift_span : ∀ t : R, t ∈ (Ideal.span ↑S_F : Ideal R) →
        ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
        evalₐ Mi (n0 + 1) δ = Ideal.Quotient.mk (Mi ^ (n0 + 1)) t)
    (r' : R) (hr' : r' ∈ (Mi ^ K • (FN_n0 : Submodule R R) : Submodule R R)) :
    ∃ (c : AdicCompletion Mi R → AdicCompletion Mi R),
      (∀ g, g ∈ genS → c g ∈ (Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi) ^ K) ∧
      evalₐ Mi (n0 + K + 1) (Finset.sum genS (fun g => c g * g)) =
      Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) r' := by
  refine Submodule.smul_induction_on hr' ?_ ?_
  · intro m hm s hs
    obtain ⟨δ_s, hδ_s_I, hδ_s_eq⟩ := hlift_span s (hS_F ▸ hs)
    have hδ_s_span : δ_s ∈ Ideal.span (↑genS : Set (AdicCompletion Mi R)) :=
      hI₀_eq ▸ hδ_s_I
    obtain ⟨f, _, hf_sum⟩ := Submodule.mem_span_finset.mp hδ_s_span
    refine ⟨fun g => of Mi R m * f g,
      fun g _ => Ideal.mul_mem_right (f g) _
        (by
           rw [← Ideal.map_pow]
           exact Ideal.mem_map_of_mem _ hm), ?_⟩
    have hsum_eq : Finset.sum genS (fun g => (of Mi R m * f g) * g) = of Mi R m * δ_s := by
      rw [← hf_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    rw [hsum_eq, map_mul, evalₐ_of]
    exact evalₐ_mk_smul_eq R Mi n0 K m s hm δ_s hδ_s_eq
  · intro a b ⟨ca, hcaM, hcaeq⟩ ⟨cb, hcbM, hcbeq⟩
    refine ⟨fun g => ca g + cb g,
      fun g hg => ((Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi) ^ K).add_mem
        (hcaM g hg) (hcbM g hg), ?_⟩
    have hexp : Finset.sum genS (fun g => (ca g + cb g) * g) =
        Finset.sum genS (fun g => ca g * g) + Finset.sum genS (fun g => cb g * g) := by
      simp only [add_mul, Finset.sum_add_distrib]
    rw [hexp, map_add, hcaeq, hcbeq, map_add]

/- Auxiliary: extract a representative r ∈ Mi^K • FN_n0 from e ∈ Mhat^(n0+K) ∩ J. -/
omit [IsLocalRing R] [IsNoetherianRing R] in
lemma extract_filtration_rep
    (Mi : Ideal R) (J : Ideal (AdicCompletion Mi R))
    (FN : ℕ → Ideal R) (n0 K : ℕ)
    (hFN_def : ∀ n, FN n = Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J))
    (FN_n0_sub : Submodule R R)
    (hn0_pow : ∀ K, Mi ^ K • FN_n0_sub = (fun n => (FN n : Submodule R R)) (n0 + K))
    (Mhat : Ideal (AdicCompletion Mi R))
    (hker_eq : ∀ N, RingHom.ker (evalₐ Mi N).toRingHom = Mhat ^ N)
    (e : AdicCompletion Mi R) (he : e ∈ Mhat ^ (n0 + K)) (heJ : e ∈ J) :
    ∃ r : R, r ∈ (Mi ^ K • FN_n0_sub : Submodule R R) ∧
      evalₐ Mi (n0 + K + 1) e = Ideal.Quotient.mk (Mi ^ (n0 + K + 1)) r := by
  have he_ker : evalₐ Mi (n0 + K) e = 0 := by
    have : e ∈ RingHom.ker (evalₐ Mi (n0 + K)).toRingHom := hker_eq _ ▸ he
    rwa [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
  have he_factor : Ideal.Quotient.factorPow Mi (Nat.le_succ (n0 + K))
      (evalₐ Mi (n0 + K + 1) e) = 0 :=
    (factorPow_comp_evalₐ_noeth Mi (Nat.le_succ (n0 + K)) e).trans he_ker
  have he_in_map : evalₐ Mi (n0 + K + 1) e ∈
      Ideal.map (Ideal.Quotient.mk (Mi ^ (n0 + K + 1))) (Mi ^ (n0 + K)) := by
    have hfp : Ideal.Quotient.factorPow Mi (Nat.le_succ (n0 + K)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n0 + K))) := rfl
    rw [hfp] at he_factor
    rwa [← Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.le_succ (n0 + K))),
      RingHom.mem_ker]
  obtain ⟨r, hr_pow, hr_eq⟩ := (Ideal.mem_map_iff_of_surjective _
    Ideal.Quotient.mk_surjective).mp he_in_map
  have hr_FN : r ∈ FN (n0 + K) := by
    rw [hFN_def]
    exact ⟨hr_pow, Ideal.mem_comap.mpr (hr_eq ▸ Ideal.mem_map_of_mem _ heJ)⟩
  refine ⟨r, ?_, hr_eq.symm⟩
  simpa only [hn0_pow] using hr_FN

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Membership in `M̂ᴷ` is membership in `Mᴷ • ⊤` for the adic completion. -/
private theorem mem_map_pow_iff_mem_pow_smul_top (Mi : Ideal R) (K : ℕ)
    (z : AdicCompletion Mi R) :
    z ∈ Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi ^ K ↔
      z ∈ Mi ^ K • (⊤ : Submodule R (AdicCompletion Mi R)) := by
  rw [Ideal.smul_top_eq_map, ← Ideal.map_pow, Submodule.restrictScalars_mem]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- A sequence whose consecutive differences lie in `M̂ᴷ` is adically Cauchy. -/
private theorem smodEq_of_consecutive_differences (Mi : Ideal R)
    (f : ℕ → AdicCompletion Mi R)
    (hf : ∀ K, f (K + 1) - f K ∈ Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi ^ K)
    {m n : ℕ} (hmn : m ≤ n) :
    f m ≡ f n [SMOD (Mi ^ m • (⊤ : Submodule R (AdicCompletion Mi R)))] := by
  rw [SModEq.sub_mem, ← mem_map_pow_iff_mem_pow_smul_top R Mi]
  set Mhat := Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction d with
  | zero => simp [sub_self, (Mhat ^ m).zero_mem]
  | succ d ih =>
    rw [show m + (d + 1) = (m + d) + 1 from by omega]
    have hsplit : f m - f ((m + d) + 1) =
        (f m - f (m + d)) + -(f ((m + d) + 1) - f (m + d)) := by abel
    rw [hsplit]
    exact (Mhat ^ m).add_mem (ih (Nat.le_add_right m d))
      ((Mhat ^ m).neg_mem (Ideal.pow_le_pow_right (Nat.le_add_right m d) (hf (m + d))))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Lifts to `I₀` of the generators of `span S` give lifts of every element of `span S`. -/
private theorem lift_span_of_generators (Mi : Ideal R) (n : ℕ) (S : Finset R)
    (I₀ : Ideal (AdicCompletion Mi R))
    (hgen : ∀ r ∈ S, ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
      evalₐ Mi n δ = Ideal.Quotient.mk (Mi ^ n) r)
    (t : R) (ht : t ∈ (Ideal.span ↑S : Ideal R)) :
    ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧ evalₐ Mi n δ = Ideal.Quotient.mk (Mi ^ n) t := by
  refine Submodule.closure_induction
    (p := fun t _ => ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
      evalₐ Mi n δ = Ideal.Quotient.mk (Mi ^ n) t)
    ?_ ?_ ?_ ht
  · exact ⟨0, I₀.zero_mem, by simp⟩
  · intro _ _ _ _ ⟨δ1, hδ1I, hδ1eq⟩ ⟨δ2, hδ2I, hδ2eq⟩
    exact ⟨δ1 + δ2, I₀.add_mem hδ1I hδ2I, by rw [map_add, hδ1eq, hδ2eq, map_add]⟩
  · intro c s hs_mem
    obtain ⟨δ, hδI, hδeq⟩ := hgen s (Finset.mem_coe.mp hs_mem)
    exact ⟨of Mi R c * δ, I₀.mul_mem_left _ hδI, by
      simp only [map_mul, evalₐ_of, hδeq, smul_eq_mul]⟩

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- If `I₀` has the same image as `J` modulo `M̂ⁿ`, then `J ≤ I₀ ⊔ M̂ⁿ`. -/
private theorem mem_sup_pow_of_map_evalₐ_le (Mi : Ideal R)
    (J I₀ : Ideal (AdicCompletion Mi R)) (n : ℕ)
    (hker : RingHom.ker (evalₐ Mi n).toRingHom =
      Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi ^ n)
    (hle : Ideal.map (evalₐ Mi n).toRingHom J ≤ Ideal.map (evalₐ Mi n).toRingHom I₀)
    (x : AdicCompletion Mi R) (hx : x ∈ J) :
    x ∈ I₀ ⊔ Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi ^ n := by
  obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _
    (surjective_evalₐ Mi n)).mp (hle (Ideal.mem_map_of_mem _ hx))
  refine Submodule.mem_sup.mpr ⟨y, hy, x - y, ?_, by abel⟩
  rw [← hker, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    map_sub, sub_eq_zero]
  exact hyx.symm

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Successive approximation (Atiyah–Macdonald Prop. 10.11 / Matsumura Thm. 8.1): if every
`e ∈ J ∩ M̂^(n0 + K)` can be corrected modulo `M̂^(n0 + K + 1)` by a combination of `genS`
with coefficients in `M̂ᴷ`, then every `z ∈ J ∩ M̂^n0` is a combination of `genS`. -/
private theorem exists_coefficients_of_successive_approximation (Mi : Ideal R)
    (hprec : IsPrecomplete Mi (AdicCompletion Mi R))
    (J : Ideal (AdicCompletion Mi R)) (genS : Finset (AdicCompletion Mi R)) (n0 : ℕ)
    (hstep_coeff : ∀ K (e : AdicCompletion Mi R),
      e ∈ Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi ^ (n0 + K) → e ∈ J →
      ∃ c : AdicCompletion Mi R → AdicCompletion Mi R,
        (∀ g, g ∈ genS → c g ∈ Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi ^ K) ∧
        e - Finset.sum genS (fun g => c g * g) ∈
          Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi ^ (n0 + (K + 1)))
    (hsum_J : ∀ d : AdicCompletion Mi R → AdicCompletion Mi R,
      Finset.sum genS (fun g => d g * g) ∈ J)
    (z : AdicCompletion Mi R)
    (hz : z ∈ Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi ^ n0) (hzJ : z ∈ J) :
    ∃ c : AdicCompletion Mi R → AdicCompletion Mi R,
      z = Finset.sum genS (fun g => c g * g) := by
  classical
  set Mhat := Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi
  let sumG (f : AdicCompletion Mi R → AdicCompletion Mi R) :=
    Finset.sum genS (fun g => f g * g)
  -- Build the recursive coefficient sequence via `buildAdicSeq`.
  let CSDPred (K : ℕ) (c : AdicCompletion Mi R → AdicCompletion Mi R) :=
    (z - sumG c) ∈ Mhat ^ (n0 + K) ∧ (z - sumG c) ∈ J
  have hsum_zero : sumG (fun _ => (0 : AdicCompletion Mi R)) = 0 := by
    simp only [sumG, zero_mul, Finset.sum_const_zero]
  have csd0 : { c // CSDPred 0 c } := ⟨fun _ => 0, by
    constructor
    · simpa only [hsum_zero, sub_zero, Nat.add_zero] using hz
    · show z - sumG (fun _ => 0) ∈ _
      rw [hsum_zero, sub_zero]
      exact hzJ⟩
  let csdS : ∀ K, { c // CSDPred K c } → { c // CSDPred (K + 1) c } :=
    fun K ⟨c_K, hMK, hJK⟩ =>
    let d := (hstep_coeff K _ hMK hJK).choose
    let hd := (hstep_coeff K _ hMK hJK).choose_spec
    ⟨fun g => c_K g + d g, by
      have hsplit : Finset.sum genS (fun g => (c_K g + d g) * g) =
          sumG c_K + sumG d := by
        simp only [sumG, add_mul, Finset.sum_add_distrib]
      have hrw : z - Finset.sum genS (fun g => (c_K g + d g) * g) =
          (z - sumG c_K) - sumG d := by
        rw [hsplit]
        abel
      exact ⟨by rw [hrw]
                exact hd.2,
        by rw [hrw]
           exact J.sub_mem hJK (hsum_J d)⟩⟩
  let csdAll := buildAdicSeq csd0 csdS
  let pc : ℕ → AdicCompletion Mi R → AdicCompletion Mi R := fun K => (csdAll K).1
  -- Per-step bound: pc(K+1)(g) - pc(K)(g) ∈ Mhat^K
  have hpc_diff : ∀ K g, g ∈ genS →
      pc (K + 1) g - pc K g ∈ Mhat ^ K := by
    intro K g hg
    have hcs := hstep_coeff K _ (csdAll K).2.1 (csdAll K).2.2
    have hcsBound : ∀ g, g ∈ genS → hcs.choose g ∈ Mhat ^ K := hcs.choose_spec.1
    change (csdS K (csdAll K)).val g - (csdAll K).val g ∈ Mhat ^ K
    have key : ∀ (dat : { c // CSDPred K c }),
        (csdS K dat).val g - dat.val g =
        (hstep_coeff K _ dat.2.1 dat.2.2).choose g := by
      intro ⟨c_K, _, _⟩
      simp only [csdS, add_sub_cancel_left]
    rw [key]
    exact hcsBound g hg
  -- Per-generator limits via IsPrecomplete
  have hpc_lim : ∀ g, g ∈ genS →
      ∃ cg, ∀ n,
        pc n g ≡ cg [SMOD (Mi ^ n • ⊤ :
          Submodule R (AdicCompletion Mi R))] :=
    fun g hg => IsPrecomplete.prec hprec
      (smodEq_of_consecutive_differences R Mi (fun K => pc K g) (fun K => hpc_diff K g hg))
  let cLim : AdicCompletion Mi R → AdicCompletion Mi R :=
    fun g => if hg : g ∈ genS then (hpc_lim g hg).choose else 0
  have hcLim_spec : ∀ g, g ∈ genS → ∀ n,
      pc n g ≡ cLim g [SMOD (Mi ^ n • ⊤ : Submodule R (AdicCompletion Mi R))] := by
    intro g hg n
    simpa only [cLim, dite_eq_left hg] using (hpc_lim g hg).choose_spec n
  -- z = ∑ cLim(g) * g by Hausdorff
  refine ⟨cLim, ?_⟩
  apply (IsHausdorff.eq_iff_smodEq (I := Mi) (M := AdicCompletion Mi R)).mpr
  intro n
  rw [SModEq.sub_mem, ← mem_map_pow_iff_mem_pow_smul_top R Mi]
  have hsplit : z - Finset.sum genS (fun g => cLim g * g) =
      (z - Finset.sum genS (fun g => pc n g * g)) +
        Finset.sum genS (fun g => (pc n g - cLim g) * g) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  apply (Mhat ^ n).add_mem
  · exact Ideal.pow_le_pow_right (Nat.le_add_left n n0) (csdAll n).2.1
  · exact Ideal.sum_mem _ (fun g hg => Ideal.mul_mem_right _ _
      (by
         rw [mem_map_pow_iff_mem_pow_smul_top R Mi]
         exact SModEq.sub_mem.mp (hcLim_spec g hg n)))

/-- Every ideal of the adic completion of a Noetherian local ring is finitely generated. -/
private theorem adicCompletion_ideal_fg :
    ∀ J : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R), J.FG := by
  set Mi := IsLocalRing.maximalIdeal R
  intro J
  have hJ_img_fg : forall n, (Ideal.map (evalₐ Mi n).toRingHom J).FG := fun n =>
    (isNoetherianRing_iff_ideal_fg _).mp (Ideal.Quotient.isNoetherianRing _)
      (Ideal.map (evalₐ Mi n).toRingHom J)
  -- Leading-term filtration: FN(n) = M^n ∩ comap(mk(M^{n+1}), eval(n+1)(J))
  set FN : Nat -> Ideal R := fun n =>
    Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J)
  have hFN_def : ∀ n, FN n = Mi ^ n ⊓ Ideal.comap (Ideal.Quotient.mk (Mi ^ (n + 1)))
      (Ideal.map (evalₐ Mi (n + 1)).toRingHom J) := fun n => rfl
  have hFN_le : forall n, FN n ≤ Mi ^ n := fun n => inf_le_left
  have hFN_mono_sub : forall n, FN (n + 1) ≤ FN n := by
    intro n r ⟨hr1, hr2⟩
    refine ⟨Ideal.pow_le_pow_right (Nat.le_succ n) hr1, ?_⟩
    change Ideal.Quotient.mk (Mi ^ (n + 1)) r ∈ Ideal.map (evalₐ Mi (n + 1)).toRingHom J
    obtain ⟨y, hyJ, hyr⟩ := (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1 + 1))).mp hr2
    refine (Ideal.mem_map_iff_of_surjective _
      (surjective_evalₐ Mi (n + 1))).mpr ⟨y, hyJ, ?_⟩
    rw [← factorPow_comp_evalₐ_noeth Mi (Nat.le_succ (n + 1)) y]
    simp only [hyr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  have hFN_smul_sub : forall n, Mi * FN n ≤ FN (n + 1) :=
    filtration_smul_le R Mi J FN hFN_def
  -- Build the Ideal.Filtration and prove stability
  have hFN_smul_R : forall n, Mi • (FN n : Submodule R R) ≤ (FN (n + 1) : Submodule R R) :=
    hFN_smul_sub
  set F_filt : Mi.Filtration R :=
    { N := fun n => (FN n : Submodule R R)
      mono := fun n => hFN_mono_sub n
      smul_le := hFN_smul_R }
  have hF_le : F_filt ≤ Mi.stableFiltration ⊤ := by
    intro n x hx
    change x ∈ Mi ^ n • (⊤ : Submodule R R)
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mem_map_of_mem _ (hFN_le n hx)
  have : Module.Finite R R := Module.Finite.self R
  have hF_stable : F_filt.Stable := (Ideal.stableFiltration_stable Mi ⊤).of_le hF_le
  -- Stability: ∃ n0, FN(n0+k) = M^k * FN(n0)
  obtain ⟨n0, hn0_pow⟩ := hF_stable.exists_pow_smul_eq
  obtain ⟨S_F, hS_F⟩ : (FN n0).FG := IsNoetherian.noetherian _
  obtain ⟨S_J, hS_J⟩ := hJ_img_fg n0
  have hS_J_lift : forall a, a ∈ S_J -> ∃ x : AdicCompletion Mi R, x ∈ J ∧
      evalₐ Mi n0 x = a := by
    intro a ha
    exact (Ideal.mem_map_iff_of_surjective _ (surjective_evalₐ Mi n0)).mp
      (hS_J ▸ Ideal.subset_span ha)
  have hS_F_lift : forall r, r ∈ S_F -> ∃ x : AdicCompletion Mi R, x ∈ J ∧
      evalₐ Mi (n0 + 1) x = Ideal.Quotient.mk (Mi ^ (n0 + 1)) r := by
    intro r hr
    have hmem : r ∈ FN n0 := hS_F ▸ Ideal.subset_span hr
    exact (Ideal.mem_map_iff_of_surjective _ (surjective_evalₐ Mi (n0 + 1))).mp hmem.2
  choose lJ hlJ_mem hlJ_eq using hS_J_lift
  choose lF hlF_mem hlF_eq using hS_F_lift
  classical
  set genJ := S_J.image (fun a => if h : a ∈ S_J then lJ a h else 0)
  set genF := S_F.image (fun r => if h : r ∈ S_F then lF r h else 0)
  set I₀ := Ideal.span (↑(genJ ∪ genF) : Set (AdicCompletion Mi R))
  have hI0_le_J : I₀ ≤ J := by
    rw [Ideal.span_le]
    intro z hz
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hz
    rcases hz with hz | hz
    · rw [Finset.mem_image] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      simpa only [dite_eq_left ha, SetLike.mem_coe] using hlJ_mem a ha
    · rw [Finset.mem_image] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      simpa only [dite_eq_left hr, SetLike.mem_coe] using hlF_mem r hr
  refine ⟨genJ ∪ genF, le_antisymm hI0_le_J ?_⟩
  -- HARD DIRECTION: J ≤ Ideal.span ↑(genJ ∪ genF), by successive approximation
  -- (Atiyah-Macdonald Prop 10.11 / Matsumura Thm 8.1) and Hausdorffness.
  set Mhat := Ideal.map (algebraMap R (AdicCompletion Mi R)) Mi
  have hker_eq : ∀ N, RingHom.ker (evalₐ Mi N).toRingHom = Mhat ^ N :=
    fun N => ker_evalₐ_eq N
  have hgenJ_sub : ∀ a ∈ S_J, (if h : a ∈ S_J then lJ a h else 0) ∈ I₀ := by
    intro a ha
    exact Ideal.subset_span (Finset.mem_coe.mpr
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)))
  have hgenF_sub : ∀ r ∈ S_F, (if h : r ∈ S_F then lF r h else 0) ∈ I₀ := by
    intro r hr
    exact Ideal.subset_span (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)))
  have hlift_span : ∀ t : R, t ∈ (Ideal.span ↑S_F : Ideal R) →
      ∃ δ : AdicCompletion Mi R, δ ∈ I₀ ∧
      evalₐ Mi (n0 + 1) δ = Ideal.Quotient.mk (Mi ^ (n0 + 1)) t :=
    lift_span_of_generators R Mi (n0 + 1) S_F I₀ fun r hr =>
      ⟨_, hgenF_sub r hr, by simpa only [dite_eq_left hr] using hlF_eq r hr⟩
  -- Base approximation: J ≤ I₀ ⊔ Mhat^n0, since I₀ and J have the same image mod Mhat^n0.
  have hI0_surj : Ideal.map (evalₐ Mi n0).toRingHom I₀ = Ideal.span ↑S_J := by
    apply le_antisymm
    · rw [Ideal.map_span]
      apply Ideal.span_le.mpr
      intro a ha
      simp only [Set.mem_image, Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha
      obtain ⟨g, hg, rfl⟩ := ha
      rcases hg with hg | hg
      · rw [Finset.mem_image] at hg
        obtain ⟨a, ha, rfl⟩ := hg
        rw [dite_eq_left ha, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        rw [hlJ_eq a ha]
        exact Ideal.subset_span ha
      · rw [Finset.mem_image] at hg
        obtain ⟨r, hr, rfl⟩ := hg
        rw [dite_eq_left hr, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        have hr_pow : r ∈ Mi ^ n0 := hFN_le n0 (hS_F ▸ Ideal.subset_span hr)
        have : (evalₐ Mi n0) (lF r hr) =
          Ideal.Quotient.factorPow Mi (Nat.le_succ n0) (evalₐ Mi (n0 + 1) (lF r hr)) :=
          (factorPow_comp_evalₐ_noeth Mi (Nat.le_succ n0) (lF r hr)).symm
        rw [this, hlF_eq r hr]
        have hfp_eq : Ideal.Quotient.factorPow Mi (Nat.le_succ n0) =
          Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n0)) := rfl
        rw [hfp_eq, Ideal.Quotient.factor_mk,
          Ideal.Quotient.eq_zero_iff_mem.mpr hr_pow]
        exact Ideal.zero_mem _
    · apply Ideal.span_le.mpr
      intro a ha
      have ha_fin : a ∈ S_J := ha
      exact (Ideal.mem_map_iff_of_surjective _ (surjective_evalₐ Mi n0)).mpr
        ⟨if h : a ∈ S_J then lJ a h else 0, hgenJ_sub a ha_fin, by
          simpa only [dite_eq_left ha_fin] using hlJ_eq a ha_fin⟩
  have hzero : ∀ x ∈ J, x ∈ I₀ ⊔ Mhat ^ n0 :=
    mem_sup_pow_of_map_evalₐ_le R Mi J I₀ n0 (hker_eq n0) (hI0_surj.trans hS_J).ge
  -- Correction step: errors in J ∩ Mhat^(n0+K) are fixed by generator combinations.
  have hstep_coeff : ∀ K (e : AdicCompletion Mi R), e ∈ Mhat ^ (n0 + K) → e ∈ J →
      ∃ (c : AdicCompletion Mi R → AdicCompletion Mi R),
        (∀ g, g ∈ genJ ∪ genF → c g ∈ Mhat ^ K) ∧
        e - Finset.sum (genJ ∪ genF) (fun g => c g * g) ∈ Mhat ^ (n0 + (K + 1)) := by
    intro K e he heJ
    obtain ⟨r, hr_in_smul, hr_eq⟩ := extract_filtration_rep R Mi J FN n0 K
      hFN_def (F_filt.N n0) (fun K => (hn0_pow K).symm) Mhat hker_eq e he heJ
    obtain ⟨c, hcM, hceq⟩ := coeff_decomp_of_smul R Mi n0 K (FN n0) S_F hS_F
      (genJ ∪ genF) I₀ rfl hlift_span r hr_in_smul
    exact ⟨c, hcM, by
      rw [show n0 + (K + 1) = n0 + K + 1 from by omega, ← hker_eq,
        RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        map_sub, hceq, ← hr_eq, sub_self]⟩
  have hsum_in_I₀ : ∀ (d : AdicCompletion Mi R → AdicCompletion Mi R),
      Finset.sum (genJ ∪ genF) (fun g => d g * g) ∈ I₀ :=
    fun d => Ideal.sum_mem _ (fun g hg =>
      I₀.mul_mem_left (d g) (Ideal.subset_span (Finset.mem_coe.mpr hg)))
  intro x hx
  obtain ⟨y₀, hy₀, e₀, he₀, hxye₀⟩ := Submodule.mem_sup.mp (hzero x hx)
  have he₀sub : x - y₀ ∈ Mhat ^ n0 := by
    rwa [eq_sub_of_add_eq' hxye₀] at he₀
  obtain ⟨c, hc⟩ := exists_coefficients_of_successive_approximation R Mi
    (adicCompletion_isPrecomplete (R := R)) J (genJ ∪ genF) n0 hstep_coeff
    (fun d => hI0_le_J (hsum_in_I₀ d)) (x - y₀) he₀sub (J.sub_mem hx (hI0_le_J hy₀))
  rw [← sub_add_cancel x y₀, hc]
  exact I₀.add_mem (hsum_in_I₀ c) hy₀

/-- The adic completion of a Noetherian local ring is Noetherian. -/
instance adicCompletion_isNoetherianRing :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (isNoetherianRing_iff_ideal_fg _).mpr (adicCompletion_ideal_fg R)

end Main
