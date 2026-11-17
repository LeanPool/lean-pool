/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Roy.Subquot
public import LeanPool.RoyStrongSix.Roy.Support
public import LeanPool.RoyStrongSix.Roy.Theorem1
public import LeanPool.RoyStrongSix.Thm1.Quot
public import LeanPool.RoyStrongSix.Thm1.QuotMap

/-!
# Reductions for Theorem 1: Step R and the trivial cases

* `theorem1_of_basic : BasicT1 → WaldschmidtTheorem1` (Step R). `BasicT1` has the weaker right-hand
  side `d₁/(d − dim V)`. To get Roy's right-hand side `(d₁ − dim(Y ∩ Ω))/(d − dim V)`, first
  quotient
  by `ℂ·(Y ∩ Ω)`. This is a `ℚ`-rational subspace of the torus factor contained in `V`, of dimension
  `u = dim_ℚ(Y ∩ Ω)`. It lowers `d₁` and `dim V` by `u` and leaves `d − dim V` unchanged.
* `basic_of_core : CoreT1 → BasicT1`. `CoreT1` assumes `1 ≤ dim V` and `d₀ ≤ dim V`.
  * If `dim V = 0`, take `s = id`.
  * If `dim V < d₀`, take `s` = the quotient by `(span of the Qbar-parts of Y) × ℂ^{d₁}`. Then
    `s(Y) = 0`, the left side is `0`, and `s(W) ⊆ s(V) ≠ ⊤` because `dim pr₀(V) < d₀`.
-/

@[expose] public section

namespace LeanPool

open Module Submodule
open StrongSix.Roy

namespace StrongSix.Thm1

variable {d0 d1 : ℕ}

/-- The left side of Theorem 1's inequality, for a map `s`. -/
noncomputable def lhs {d0' d1' : ℕ} (Y : Submodule ℚ (E d0 d1)) (W : Submodule ℂ (E d0 d1))
    (s : E d0 d1 →ₗ[ℂ] E d0' d1') : ℚ :=
  ((d1' : ℚ) - finrank ℚ ↥(Y.map (s.restrictScalars ℚ) ⊓ Omega d0' d1') +
      finrank ℚ ↥(Y.map (s.restrictScalars ℚ))) / ((d0' + d1' : ℚ) - finrank ℂ ↥(W.map s))

/-- The conclusion of Theorem 1, with right-hand side `rhs`. -/
def T1Concl (d0 d1 : ℕ) (Y : Submodule ℚ (E d0 d1)) (W : Submodule ℂ (E d0 d1)) (rhs : ℚ) :
    Prop :=
  ∃ (d0' d1' : ℕ) (s : E d0 d1 →ₗ[ℂ] E d0' d1'), Function.Surjective s ∧
    (∀ u : Fin d0 → ℂ, AlgVec u → ∃ u', AlgVec u' ∧ s (u, 0) = (u', 0)) ∧
    (∀ v : Fin d1 → ℂ, RatVec v → ∃ v', RatVec v' ∧ s (0, v) = (0, v')) ∧
    W.map s ≠ ⊤ ∧ lhs Y W s ≤ rhs

/-- The hypotheses of Theorem 1. -/
structure Hyps (d0 d1 : ℕ) (Y : Submodule ℚ (E d0 d1)) (W V : Submodule ℂ (E d0 d1)) : Prop where
  fin : FiniteDimensional ℚ Y
  pts : ∀ p ∈ Y, AlgVec p.1 ∧ ∀ j, p.2 j ∈ logAlg
  rat : RationalOverQbar W
  YV : ∀ p ∈ Y, p ∈ V
  WV : W ≤ V
  Vne : V ≠ ⊤

/-- Theorem 1 with the weaker right-hand side `d₁/(d − dim V)`. -/
def BasicT1 : Prop :=
  ∀ (d0 d1 : ℕ) (Y : Submodule ℚ (E d0 d1)) (W V : Submodule ℂ (E d0 d1)), Hyps d0 d1 Y W V →
    T1Concl d0 d1 Y W ((d1 : ℚ) / ((d0 + d1 : ℚ) - finrank ℂ ↥V))

/-- `BasicT1` in the transcendence regime `1 ≤ dim V`, `d₀ ≤ dim V`. -/
def CoreT1 : Prop :=
  ∀ (d0 d1 : ℕ) (Y : Submodule ℚ (E d0 d1)) (W V : Submodule ℂ (E d0 d1)), Hyps d0 d1 Y W V →
    1 ≤ finrank ℂ ↥V → d0 ≤ finrank ℂ ↥V →
    T1Concl d0 d1 Y W ((d1 : ℚ) / ((d0 + d1 : ℚ) - finrank ℂ ↥V))

theorem finrank_E (a b : ℕ) : finrank ℂ (E a b) = a + b := by
  simp [E, Module.finrank_prod]

theorem finrank_lt_of_ne_top {a b : ℕ} {V : Submodule ℂ (E a b)} (h : V ≠ ⊤) :
    finrank ℂ ↥V < a + b := by
  rw [← finrank_E a b]; exact Submodule.finrank_lt h

theorem ne_top_of_finrank_lt {a b : ℕ} {V : Submodule ℂ (E a b)} (h : finrank ℂ ↥V < a + b) :
    V ≠ ⊤ := by
  rintro rfl
  rw [finrank_top, finrank_E] at h
  exact lt_irrefl _ h

/-! ### Rational matrices preserve algebraic and logarithmic vectors -/

theorem presQ_alg {n k : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ)) (hf : PresF ℚ f)
    {x : Fin n → ℂ} (hx : AlgVec x) : AlgVec (f x) := fun j =>
  presQ_preserves f hf algSub (x := x) (fun i => hx i) j

theorem presQ_log {n k : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ)) (hf : PresF ℚ f)
    {x : Fin n → ℂ} (hx : ∀ i, x i ∈ logAlg) (j : Fin k) : f x j ∈ logAlg :=
  presQ_preserves f hf logAlgSub (x := x) hx j

theorem presQ_rat {n k : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ)) (hf : PresF ℚ f)
    {x : Fin n → ℂ} (hx : RatVec x) : RatVec (f x) :=
  ratVec_iff.mpr (hf x (ratVec_iff.mp hx))

/-! ### Step R -/

/-- `ι(r) = (0, 2πi r)`. -/
noncomputable def ιΩ (d0 d1 : ℕ) : (Fin d1 → ℚ) →ₗ[ℚ] E d0 d1 := (μ d0 d1) ∘ₗ inclF ℚ d1

theorem ιΩ_injective : Function.Injective (ιΩ d0 d1) :=
  (μ_injective d0 d1).comp inclF_injective

theorem inf_Omega_eq (Y : Submodule ℚ (E d0 d1)) :
    Y ⊓ Omega d0 d1 = (Y.comap (ιΩ d0 d1)).map (ιΩ d0 d1) := by
  ext p
  rw [Omega_eq_map, mem_inf, mem_map, mem_map]
  constructor
  · rintro ⟨hpY, x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := exists_inclF hx
    exact ⟨r, hpY, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨hr, inclF ℚ d1 r, inclF_mem_Fpts r, rfl⟩

theorem finrank_inf_Omega (Y : Submodule ℚ (E d0 d1)) :
    finrank ℚ ↥(Y ⊓ Omega d0 d1) = finrank ℚ ↥(Y.comap (ιΩ d0 d1)) := by
  rw [inf_Omega_eq]
  exact ((Submodule.equivMapOfInjective _ ιΩ_injective _).finrank_eq).symm

/-- **Step R.** -/
theorem theorem1_of_basic (hB : BasicT1) : WaldschmidtTheorem1 := by
  intro d0 d1 Y W V hfin hpts hrat hYV hWV hVne
  set R : Submodule ℚ (Fin d1 → ℚ) := Y.comap (ιΩ d0 d1) with hR
  set u := finrank ℚ R with hu
  set q : E d0 d1 →ₗ[ℂ] E d0 (d1 - u) := LinearMap.prodMap LinearMap.id (qC R) with hq
  have hqC := qC_presF R
  have hq_apply : ∀ p : E d0 d1, q p = (p.1, qC R p.2) := fun p => rfl
  -- the kernel of `q` lies in `V`
  have hker : LinearMap.ker q = (⊥ : Submodule ℂ (Fin d0 → ℂ)).prod (LinearMap.ker (qC R)) := by
    rw [hq, LinearMap.ker_prodMap, LinearMap.ker_id]
  have hkerV : LinearMap.ker q ≤ V := by
    rw [hker]
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have ha' : a = 0 := by simpa using ha
    subst ha'
    rw [ker_qC] at hb
    have hgen : span ℂ ((R.map (inclF ℚ d1) : Submodule ℚ _) : Set (Fin d1 → ℂ)) ≤
        V.comap (LinearMap.inr ℂ (Fin d0 → ℂ) (Fin d1 → ℂ)) := by
      rw [span_le]
      rintro _ ⟨r, hr, rfl⟩
      change ((0 : Fin d0 → ℂ), inclF ℚ d1 r) ∈ V
      have h1 : ιΩ d0 d1 r ∈ V := hYV _ hr
      have h2 : ((0 : Fin d0 → ℂ), inclF ℚ d1 r) = ω⁻¹ • ιΩ d0 d1 r := by
        simp [ιΩ, μ_apply, smul_smul, inv_mul_cancel₀ ω_ne_zero]
      rw [h2]; exact V.smul_mem _ h1
    exact hgen hb
  have hfk : finrank ℂ ↥(LinearMap.ker q) = u := by
    rw [hker, finrank_prod_sub, finrank_bot, zero_add, finrank_ker_qC]
  have hn := finrank_lt_of_ne_top hVne
  have huV : u ≤ finrank ℂ ↥V := by
    rw [← hfk]; exact Submodule.finrank_mono hkerV
  have hud1 : u ≤ d1 := by
    have := finrank_inf_Omega Y
    have h2 : finrank ℚ ↥R ≤ d1 := by
      have := Submodule.finrank_le R; simpa using this
    omega
  have hVq : finrank ℂ ↥(V.map q) = finrank ℂ ↥V - u := by
    have h := finrank_map_add_inf_ker q V
    rw [inf_eq_right.mpr hkerV, hfk] at h
    omega
  -- the quotient data satisfies the hypotheses
  have hqalg : ∀ x : E d0 d1, AlgVec x.1 → AlgVec x.2 → AlgVec (q x).1 ∧ AlgVec (q x).2 :=
    fun x h1 h2 => ⟨h1, presQ_alg _ hqC h2⟩
  have H : Hyps d0 (d1 - u) (Y.map (q.restrictScalars ℚ)) (W.map q) (V.map q) := by
    refine ⟨inferInstance, ?_, rationalOverQbar_map q hqalg hrat, ?_, Submodule.map_mono hWV, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨h1, h2⟩ := hpts y hy
      exact ⟨h1, presQ_log _ hqC h2⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact Submodule.mem_map_of_mem (hYV y hy)
    · apply ne_top_of_finrank_lt
      rw [hVq]; omega
  obtain ⟨d0', d1', s, hs, ha, hr, hW, hlhs⟩ := hB _ _ _ _ _ H
  have hqs : Function.Surjective q := by
    rintro ⟨a, b⟩
    obtain ⟨b', rfl⟩ := qC_surjective R b
    exact ⟨(a, b'), rfl⟩
  refine ⟨d0', d1', s ∘ₗ q, hs.comp hqs, fun x hx => ?_, fun v hv => ?_, ?_, ?_⟩
  · obtain ⟨x', hx', he⟩ := ha x hx
    refine ⟨x', hx', ?_⟩
    rw [LinearMap.comp_apply, hq_apply, map_zero]; exact he
  · obtain ⟨v', hv', he⟩ := hr (qC R v) (presQ_rat _ hqC hv)
    exact ⟨v', hv', by rw [LinearMap.comp_apply, hq_apply]; exact he⟩
  · rw [Submodule.map_comp]; exact hW
  · have e1 : Y.map ((s ∘ₗ q).restrictScalars ℚ) =
        (Y.map (q.restrictScalars ℚ)).map (s.restrictScalars ℚ) := by
      rw [LinearMap.restrictScalars_comp, Submodule.map_comp]
    have e2 : W.map (s ∘ₗ q) = (W.map q).map s := Submodule.map_comp _ _ _
    have hl : lhs Y W (s ∘ₗ q) = lhs (Y.map (q.restrictScalars ℚ)) (W.map q) s := by
      unfold lhs; rw [e1, e2]
    change lhs Y W (s ∘ₗ q) ≤ _
    rw [hl]
    refine hlhs.trans (le_of_eq ?_)
    rw [hVq, finrank_inf_Omega, ← hR, ← hu]
    rw [Nat.cast_sub hud1, Nat.cast_sub huV]
    ring

/-! ### The trivial cases -/

theorem finrank_bot_inf {a b : ℕ} (Ω : Submodule ℚ (E a b)) :
    finrank ℚ ↥((⊥ : Submodule ℚ (E a b)) ⊓ Ω) = 0 :=
  Nat.eq_zero_of_le_zero ((Submodule.finrank_mono inf_le_left).trans (finrank_bot ℚ _).le)

/-- `dim V = 0`: `s = id`. -/
theorem basic_dim_zero {Y : Submodule ℚ (E d0 d1)} {W V : Submodule ℂ (E d0 d1)}
    (H : Hyps d0 d1 Y W V) (h0 : finrank ℂ ↥V = 0) :
    T1Concl d0 d1 Y W ((d1 : ℚ) / ((d0 + d1 : ℚ) - finrank ℂ ↥V)) := by
  have hV : V = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hW : W = ⊥ := eq_bot_iff.mpr (hV ▸ H.WV)
  have hY : Y = ⊥ := by
    rw [eq_bot_iff]; intro p hp
    have := H.YV p hp
    rw [hV, mem_bot] at this
    exact (mem_bot ℚ).mpr this
  refine ⟨d0, d1, LinearMap.id, Function.surjective_id, fun u hu => ⟨u, hu, rfl⟩,
    fun v hv => ⟨v, hv, rfl⟩, ?_, ?_⟩
  · rw [Submodule.map_id, hW]
    intro h
    exact H.Vne (by rw [hV, h])
  · apply le_of_eq
    have e1 : Y.map ((LinearMap.id : E d0 d1 →ₗ[ℂ] E d0 d1).restrictScalars ℚ) = ⊥ := by
      rw [hY]; exact Submodule.map_bot _
    have e2 : W.map (LinearMap.id : E d0 d1 →ₗ[ℂ] E d0 d1) = ⊥ := by rw [Submodule.map_id, hW]
    unfold lhs
    rw [e1, e2, h0, finrank_bot_inf]
    simp

/-- `dim V < d₀`: quotient by `(Qbar-span of the additive parts of Y) × ℂ^{d₁}`. -/
theorem basic_small {Y : Submodule ℚ (E d0 d1)} {W V : Submodule ℂ (E d0 d1)}
    (H : Hyps d0 d1 Y W V) (hlt : finrank ℂ ↥V < d0) :
    T1Concl d0 d1 Y W ((d1 : ℚ) / ((d0 + d1 : ℚ) - finrank ℂ ↥V)) := by
  set h0 : Submodule Qb (Fin d0 → Qb) := span Qb {x | ∃ y ∈ Y, incl d0 x = y.1} with hh0
  set U0 : Submodule ℚ (Fin d1 → ℚ) := ⊥
  set s := sMap h0 U0 with hs
  have hd1' : finrank ℚ ↥U0 = 0 := finrank_bot ℚ _
  have hsY : ∀ y ∈ Y, s y = 0 := by
    intro y hy
    obtain ⟨x, hx⟩ := exists_incl_of_algVec (H.pts y hy).1
    have hxh : x ∈ h0 := subset_span ⟨y, hy, hx⟩
    apply Prod.ext
    · change PsiC h0 y.1 = 0
      rw [← hx, PsiC_incl,
        show psiK h0 x = 0 by rw [← LinearMap.mem_ker, ker_psiK]; exact hxh, map_zero]
    · funext k
      exact absurd k.2 (by omega)
  have hYs : Y.map (s.restrictScalars ℚ) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_bot ℚ).mpr (hsY y hy)
  -- the dimension count
  set A : Submodule ℂ (Fin d0 → ℂ) := span ℂ ((h0.map (incl d0) : Submodule Qb _) : Set _) with hA
  have hAf : finrank ℂ ↥A = finrank Qb ↥h0 := by
    rw [hA, finrank_span_of_le_Fpts _ (by rintro _ ⟨x, -, rfl⟩; exact algVec_iff.mp (algVec_incl
      x))]
    exact ((Submodule.equivMapOfInjective _ (incl_injective d0) h0).finrank_eq).symm
  set V0 : Submodule ℂ (Fin d0 → ℂ) := V.map (LinearMap.fst ℂ _ _) with hV0def
  have hAV : A ≤ V0 := by
    have : h0 ≤ (V0.restrictScalars Qb).comap (incl d0) := by
      rw [hh0, span_le]
      rintro x ⟨y, hy, hx⟩
      change incl d0 x ∈ V0
      rw [hx]; exact ⟨y, H.YV y hy, rfl⟩
    rw [hA, span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact this hx
  have hAker : A ≤ LinearMap.ker (PsiC h0) := by
    rw [hA, span_le]
    rintro _ ⟨x, hx, rfl⟩
    change PsiC h0 (incl d0 x) = 0
    rw [PsiC_incl, show psiK h0 x = 0 by rw [← LinearMap.mem_ker, ker_psiK]; exact hx, map_zero]
  have hV0le : finrank ℂ ↥V0 ≤ finrank ℂ ↥V := Submodule.finrank_map_le _ _
  have hPV0 : finrank ℂ ↥(V0.map (PsiC h0)) + finrank Qb ↥h0 ≤ finrank ℂ ↥V0 := by
    have h := finrank_map_add_inf_ker (PsiC h0) V0
    have : finrank ℂ ↥A ≤ finrank ℂ ↥(V0 ⊓ LinearMap.ker (PsiC h0)) :=
      Submodule.finrank_mono (le_inf hAV hAker)
    omega
  -- `s(V) ≅ Ψ(pr₀ V)`, since the second factor of the target is zero-dimensional
  have hsV : finrank ℂ ↥(V.map s) = finrank ℂ ↥(V0.map (PsiC h0)) := by
    have hfst : Function.Injective
        (LinearMap.fst ℂ (Fin (d0 - finrank Qb h0) → ℂ) (Fin (finrank ℚ ↥U0) → ℂ)) := by
      intro a b hab
      refine Prod.ext hab (funext fun k => absurd k.2 (by omega))
    rw [(Submodule.equivMapOfInjective _ hfst (V.map s)).finrank_eq, hV0def, ← Submodule.map_comp,
      ← Submodule.map_comp]
    rfl
  have hfin : finrank ℂ ↥(W.map s) < (d0 - finrank Qb h0) + finrank ℚ ↥U0 := by
    have := Submodule.finrank_mono (Submodule.map_mono (f := s) H.WV)
    omega
  refine ⟨_, _, s, sMap_surjective h0 U0, sMap_alg h0 U0, sMap_rat h0 U0,
    ne_top_of_finrank_lt hfin, ?_⟩
  have hn := finrank_lt_of_ne_top H.Vne
  have hden : (0 : ℚ) < (d0 + d1 : ℚ) - finrank ℂ ↥V := by
    have : (finrank ℂ ↥V : ℚ) < d0 + d1 := by exact_mod_cast hn
    linarith
  have hc : ((finrank ℚ ↥U0 : ℕ) : ℚ) = 0 := by exact_mod_cast hd1'
  unfold lhs
  rw [hYs, hc]
  rw [finrank_bot_inf, finrank_bot]
  simp only [Nat.cast_zero, sub_zero, add_zero, zero_div]
  exact div_nonneg (Nat.cast_nonneg _) hden.le

/-- **The trivial cases.** -/
theorem basic_of_core (hC : CoreT1) : BasicT1 := by
  intro d0 d1 Y W V H
  by_cases h0 : finrank ℂ ↥V = 0
  · exact basic_dim_zero H h0
  by_cases hlt : finrank ℂ ↥V < d0
  · exact basic_small H hlt
  · exact hC d0 d1 Y W V H (by omega) (by omega)

/-- **Theorem 1 from its core case.** -/
theorem theorem1_of_core (hC : CoreT1) : WaldschmidtTheorem1 :=
  theorem1_of_basic (basic_of_core hC)

end StrongSix.Thm1

end LeanPool
