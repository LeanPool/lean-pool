/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Roy.Instance

/-!
# The core contradiction for the strong six exponentials theorem

See `StrongSix.Roy.Instance` for the setup. This is the specialization of Roy's proof of his
Theorem 4 (case `d' = d`, with `d = 2`, `dim U = 1`, `dim_Qbar Z = 3`) to the matrix `(xᵢ yⱼ)`.
-/

@[expose] public section

namespace LeanPool

open Module Submodule

noncomputable section

namespace StrongSix.Roy

variable {m : ℕ} (ω : Fin m → ℂ)

theorem isAlgebraic_finsum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, IsAlgebraic ℚ (f i)) : IsAlgebraic ℚ (∑ i ∈ s, f i) :=
  Submodule.sum_mem algSub h

/-- Independent algebraic scalars preserve rational independence of a product family. -/
theorem linearIndependent_scaled_products (hωalg : ∀ k, IsAlgebraic ℚ (ω k))
    (hωind : LinearIndependent ℚ ω) {x : Fin 2 → ℂ} (hx0 : x ≠ 0)
    {y : Fin 3 → ℂ} (hy : QbarIndep y) :
    LinearIndependent ℚ (fun p : Fin m × Fin 3 => (ω p.1 * y p.2) • x) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  -- `(∑ g(k,j) ω_k y_j) x = 0`, so `∑_j (∑_k g(k,j) ω_k) y_j = 0`
  have h1 : (∑ q : Fin m × Fin 3, (g q : ℂ) * (ω q.1 * y q.2)) • x = 0 := by
    rw [Finset.sum_smul]
    rw [← hg]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Rat.cast_smul_eq_qsmul ℂ, smul_smul]
  have h2 : ∑ q : Fin m × Fin 3, (g q : ℂ) * (ω q.1 * y q.2) = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hx0
  have h3 : ∑ j : Fin 3, (∑ k : Fin m, (g (k, j) : ℂ) * ω k) * y j = 0 := by
    rw [← h2, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have h4 := hy (fun j => ∑ k : Fin m, (g (k, j) : ℂ) * ω k)
    (fun j => isAlgebraic_finsum _ _ fun k _ => (isAlgebraic_algebraMap (g (k, j))).mul (hωalg
      k)) h3
  have h5 := Fintype.linearIndependent_iff.mp hωind (fun k => g (k, p.2)) (by
    have := h4 p.2
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Rat.smul_def]) p.1
  exact h5

/-- The coefficient map has a kernel defined over the algebraic numbers. -/
theorem rationalOverQbar_ker_phiω (hωalg : ∀ k, IsAlgebraic ℚ (ω k)) :
    RationalOverQbar (LinearMap.ker (phiω ω)) := by
  set φ := phiω ω with hφdef
  let φt := φ.comp (eqv 2 (m * 2)).toLinearMap
  have hPres : PresF Qb φt := by
    intro z hz i
    rw [mem_range_Qb]
    have hz' := (eqv_fpts z).mp hz
    change IsAlgebraic ℚ (φ (eqv 2 (m * 2) z) i)
    rw [hφdef, phiω_apply]
    refine (hz'.1 i).add ?_
    exact isAlgebraic_finsum _ _ fun k _ => (hωalg k).mul (hz'.2 _)
  obtain ⟨A, hA, hker⟩ := isRat_ker φt hPres
  refine rationalOverQbar_of_comap hA ?_
  rw [← hker]
  rfl

theorem strong_six_core (hT1 : WaldschmidtTheorem1) (hm : 1 ≤ m)
    (hωalg : ∀ k, IsAlgebraic ℚ (ω k)) (hωind : LinearIndependent ℚ ω)
    {x : Fin 2 → ℂ} (hx : QbarIndep x) {y : Fin 3 → ℂ} (hy : QbarIndep y)
    (lift : Fin m × Fin 3 → E 2 (m * 2))
    (hliftalg : ∀ p, AlgVec (lift p).1 ∧ ∀ i, (lift p).2 i ∈ logAlg)
    (hlift : ∀ p, phiω ω (lift p) = (ω p.1 * y p.2) • x) : False := by
  classical
  set φ := phiω ω with hφdef
  -- `x ≠ 0`
  have hx0 : x ≠ 0 := by
    intro h
    have := hx ![1, 0] (by intro i; fin_cases i <;> simp [isAlgebraic_one, isAlgebraic_zero])
      (by simp [h])
    simpa using this 0
  set U : Submodule ℂ (Fin 2 → ℂ) := span ℂ {x} with hU
  set W : Submodule ℂ (E 2 (m * 2)) := LinearMap.ker φ with hWdef
  set V : Submodule ℂ (E 2 (m * 2)) := U.comap φ with hVdef
  set Y : Submodule ℚ (E 2 (m * 2)) := span ℚ (Set.range lift) with hYdef
  have hYfin : FiniteDimensional ℚ Y := FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hYgood : Y ≤ goodSub 2 (m * 2) := by
    rw [span_le]
    rintro _ ⟨p, rfl⟩
    exact ⟨fun i => (hliftalg p).1 i, fun j => (hliftalg p).2 j⟩
  have hYalg : ∀ p ∈ Y, AlgVec p.1 ∧ ∀ j, p.2 j ∈ logAlg := fun p hp =>
    ⟨fun i => (hYgood hp).1 i, fun j => (hYgood hp).2 j⟩
  have hYV : ∀ p ∈ Y, p ∈ V := by
    have : Y ≤ V.restrictScalars ℚ := by
      rw [span_le]
      rintro _ ⟨p, rfl⟩
      change φ (lift p) ∈ U
      rw [hlift]; exact U.smul_mem _ (mem_span_singleton_self x)
    exact fun p hp => this hp
  have hWV : W ≤ V := LinearMap.ker_le_comap φ
  -- `W = ker φ` is rational over `Qbar`
  have hWrat : RationalOverQbar W := rationalOverQbar_ker_phiω ω hωalg
  let M : Amb := ⟨2, m * 2, Y, W, V, hYfin, hYV, hWV⟩
  let X0 : M.Ob := ⟨(rbot 2 (m * 2), rtop 2 (m * 2)), ⟨bot_le, bot_le⟩⟩
  -- dimensions
  have hφs := phiω_surjective ω
  have hdimE : finrank ℂ (E 2 (m * 2)) = 2 + m * 2 := Amb.finrank_E 2 (m * 2)
  have hdimW : finrank ℂ W = m * 2 := by
    have h : finrank ℂ ↥(LinearMap.range φ) + finrank ℂ W = finrank ℂ (E 2 (m * 2)) :=
      LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.mpr hφs, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, hdimE] at h
    omega
  have hdimU : finrank ℂ U = 1 := finrank_span_singleton hx0
  have hdimV : finrank ℂ V = m * 2 + 1 := by
    have := finrank_map_add_inf_ker φ V
    rw [Submodule.map_comap_eq_of_surjective hφs, inf_eq_right.mpr hWV, hdimU, hdimW] at this
    omega
  have hr0 : Amb.r X0 = 2 + m * 2 := by
    change finrank ℂ (rtop 2 (m * 2)).sub - finrank ℂ (rbot 2 (m * 2)).sub = _
    rw [rtop_sub, rbot_sub, finrank_top, finrank_bot, hdimE]; rfl
  have hd10 : Amb.d1f X0 = m * 2 := by
    change finrank ℂ (⊤ : Submodule ℂ (Fin (m * 2) → ℂ)) - finrank ℂ (⊥ : Submodule ℂ _) = _
    rw [finrank_top, finrank_bot, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; rfl
  have hvd0 : Amb.vd X0 = m * 2 + 1 := by
    change finrank ℂ ↥(V ⊓ (rtop 2 (m * 2)).sub) - finrank ℂ ↥(V ⊓ (rbot 2 (m * 2)).sub) = _
    rw [rtop_sub, rbot_sub, inf_top_eq, inf_bot_eq, finrank_bot, hdimV]; rfl
  have hwd0 : Amb.wd X0 = m * 2 := by
    change finrank ℂ ↥(W ⊓ (rtop 2 (m * 2)).sub) - finrank ℂ ↥(W ⊓ (rbot 2 (m * 2)).sub) = _
    rw [rtop_sub, rbot_sub, inf_top_eq, inf_bot_eq, finrank_bot, hdimW]; rfl
  have hb0 : Amb.b X0 = 1 := by unfold Amb.b; rw [hr0, hvd0]; omega
  have hdd0 : Amb.d X0 = 1 := by unfold Amb.d; rw [hvd0, hwd0]; omega
  have hc0 : Amb.c X0 = finrank ℚ Y := by
    change finrank ℚ ↥(Y ⊓ (rtop 2 (m * 2)).sub.restrictScalars ℚ) -
      finrank ℚ ↥(Y ⊓ (rbot 2 (m * 2)).sub.restrictScalars ℚ) = _
    rw [rtop_sub, rbot_sub, Submodule.restrictScalars_top, Submodule.restrictScalars_bot,
      inf_top_eq, inf_bot_eq, finrank_bot]; rfl
  -- `dim_ℚ Y ≥ 3m`
  have hY3 : m * 3 ≤ finrank ℚ Y := by
    have hmap : Y.map (φ.restrictScalars ℚ) =
        span ℚ (Set.range fun p : Fin m × Fin 3 => (ω p.1 * y p.2) • x) := by
      rw [hYdef, Submodule.map_span, ← Set.range_comp]
      have hf : (⇑(φ.restrictScalars ℚ) ∘ lift) = fun p : Fin m × Fin 3 => (ω p.1 * y p.2) • x :=
        funext fun p => hlift p
      rw [hf]
    have hind := linearIndependent_scaled_products ω hωalg hωind hx0 hy
    have := Submodule.finrank_map_le (φ.restrictScalars ℚ) Y
    rw [hmap, finrank_span_eq_card hind, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin] at this
    exact this
  -- the no-kernel condition and the minimality of the identity
  have halgU : ∀ u : Fin 2 → ℂ, AlgVec u → u ∈ U → u = 0 := fun u hu hux =>
    alg_in_line hx hu hux
  have hS0 : ∀ S0 : Submodule ℂ (Fin 2 → ℂ), IsRat Qb S0 → S0 ≤ U → S0 = ⊥ := by
    intro S0 hS0 hle
    rw [span_ptsOf hS0, eq_bot_iff, span_le]
    intro u hu
    exact halgU u (algVec_iff.mpr hu.2) (hle hu.1)
  have hS1 : ∀ S1 : Submodule ℂ (Fin (m * 2) → ℂ), IsRat ℚ S1 →
      (∀ q ∈ S1, φ (0, q) ∈ U) → S1 = ⊥ := by
    intro S1 hS1 hle
    rw [span_ptsOf hS1, eq_bot_iff, span_le]
    intro q hq
    obtain ⟨hqS, hqF⟩ := hq
    choose c hc using hqF
    have hz : φ (0, q) = 0 := by
      refine halgU _ ?_ (hle q hqS)
      intro i
      rw [hφdef, phiω_apply]
      simp only [Pi.zero_apply, zero_add]
      exact isAlgebraic_finsum _ _ fun k _ => (hωalg k).mul (by
        rw [← hc]
        exact isAlgebraic_algebraMap _)
    change q = 0
    funext l
    obtain ⟨⟨k, i⟩, rfl⟩ := finProdFinEquiv.surjective l
    have hi := congrFun hz i
    rw [hφdef, phiω_apply] at hi
    simp only [Pi.zero_apply, zero_add] at hi
    have := Fintype.linearIndependent_iff.mp hωind (fun k' => c (finProdFinEquiv (k', i))) (by
      rw [← hi]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [Rat.smul_def, ← hc, mul_comm]; rfl) k
    rw [Pi.zero_apply, ← hc, this, map_zero]
  have hE1 : ∀ X', M.sys.Cok X0 X' → Amb.b X' ≠ 0 →
      (Amb.d1f X0 : ℚ) / Amb.b X0 ≤ (Amb.d1f X' : ℚ) / Amb.b X' := by
    intro X' hC hb'
    -- `b X' ≠ 0` forces `φ(S) ≤ U`
    have hT' : X'.1.2 = rtop 2 (m * 2) := hC.1.symm
    have hle : ∀ s ∈ X'.1.1.sub, φ s ∈ U := by
      by_contra hcon
      push Not at hcon
      obtain ⟨s, hs, hsU⟩ := hcon
      apply hb'
      have hsup : V ⊔ X'.1.1.sub = ⊤ := by
        have hmap : (V ⊔ X'.1.1.sub).map φ = ⊤ := by
          rw [Submodule.map_sup, Submodule.map_comap_eq_of_surjective hφs]
          apply Submodule.eq_top_of_finrank_eq
          have hlt : U < U ⊔ X'.1.1.sub.map φ :=
            lt_of_le_of_ne le_sup_left (fun h => hsU (h ▸ mem_sup_right (mem_map_of_mem hs)))
          have := Submodule.finrank_lt_finrank_of_lt hlt
          have hle2 := Submodule.finrank_le (U ⊔ X'.1.1.sub.map φ)
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle2 ⊢
          omega
        have := Submodule.comap_map_eq φ (V ⊔ X'.1.1.sub)
        rw [hmap, Submodule.comap_top, sup_assoc, sup_comm _ (LinearMap.ker φ), ← sup_assoc,
          sup_eq_left.mpr hWV] at this
        exact this.symm
      have e1 : finrank ℂ ↥(V ⊔ X'.1.1.sub) + finrank ℂ ↥(V ⊓ X'.1.1.sub) =
          finrank ℂ V + finrank ℂ X'.1.1.sub := Submodule.finrank_sup_add_finrank_inf_eq V _
      rw [hsup, finrank_top] at e1
      have g1 : finrank ℂ X'.1.1.sub ≤ finrank ℂ (E 2 (m * 2)) := Submodule.finrank_le _
      have g2 : finrank ℂ ↥(V ⊓ X'.1.1.sub) ≤ finrank ℂ V :=
        Submodule.finrank_mono inf_le_left
      have hbX : Amb.b X' = (finrank ℂ X'.1.2.sub - finrank ℂ X'.1.1.sub) -
          (finrank ℂ ↥(V ⊓ X'.1.2.sub) - finrank ℂ ↥(V ⊓ X'.1.1.sub)) := rfl
      rw [hbX, hT', rtop_sub, finrank_top, inf_top_eq]
      have key : finrank ℂ (E 2 (m * 2)) - finrank ℂ X'.1.1.sub -
          (finrank ℂ V - finrank ℂ ↥(V ⊓ X'.1.1.sub)) = 0 := by omega
      exact key
    -- hence `S = 0`
    have h0 : X'.1.1.S0 = ⊥ := hS0 _ X'.1.1.h0 (fun u hu => by
      have := hle (u, 0) ⟨hu, X'.1.1.S1.zero_mem⟩
      rw [hφdef, show phiω ω (u, 0) = u by funext i; rw [phiω_apply]; simp] at this
      exact this)
    have h1 : X'.1.1.S1 = ⊥ := hS1 _ X'.1.1.h1 (fun q hq => hle (0, q) ⟨X'.1.1.S0.zero_mem, hq⟩)
    have hX : X' = X0 := by
      apply Subtype.ext
      ext1
      · exact RSub.ext h0 h1
      · exact hT'
    rw [hX]
  have hnoker : ¬ ∃ Xs, M.sys.Ker Xs X0 ∧ Amb.d1f Xs = 0 ∧ Amb.b Xs = 0 ∧ Amb.r Xs ≠ 0 := by
    rintro ⟨Xs, hK, hd1s, hbs, hrs⟩
    have hS : Xs.1.1 = rbot 2 (m * 2) := hK.1
    have hT1z : Xs.1.2.S1 = ⊥ := by
      have h : finrank ℂ Xs.1.2.S1 - finrank ℂ Xs.1.1.S1 = 0 := hd1s
      rw [hS] at h
      have h' : finrank ℂ Xs.1.2.S1 - finrank ℂ (⊥ : Submodule ℂ (Fin (m * 2) → ℂ)) = 0 := h
      rw [finrank_bot] at h'
      exact Submodule.finrank_eq_zero.mp (by omega)
    have hTV : Xs.1.2.sub ≤ V := by
      have h : (finrank ℂ Xs.1.2.sub - finrank ℂ Xs.1.1.sub) -
          (finrank ℂ ↥(V ⊓ Xs.1.2.sub) - finrank ℂ ↥(V ⊓ Xs.1.1.sub)) = 0 := hbs
      rw [hS, rbot_sub, finrank_bot, inf_bot_eq, finrank_bot, Nat.sub_zero, Nat.sub_zero] at h
      have hle : finrank ℂ ↥(V ⊓ Xs.1.2.sub) ≤ finrank ℂ Xs.1.2.sub :=
        Submodule.finrank_mono inf_le_right
      have heq : V ⊓ Xs.1.2.sub = Xs.1.2.sub :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (Nat.sub_eq_zero_iff_le.mp h)
      exact heq ▸ inf_le_left
    have hT0 : Xs.1.2.S0 = ⊥ := hS0 _ Xs.1.2.h0 (fun u hu => by
      have := hTV (show ((u, 0) : E 2 (m * 2)) ∈ Xs.1.2.sub from ⟨hu, Xs.1.2.S1.zero_mem⟩)
      change u ∈ U
      have e : phiω ω (u, 0) = u := by funext i; rw [phiω_apply]; simp
      rw [← e]; exact this)
    apply hrs
    unfold Amb.r
    rw [hS, rbot_sub, finrank_bot]
    change finrank ℂ ↥(Xs.1.2.S0.prod Xs.1.2.S1) - 0 = 0
    rw [hT0, hT1z, Submodule.prod_bot, finrank_bot]
  -- apply Roy's Theorem 2bis
  have hineq := theorem2bis_identity (S := M.sys) Amb.hyp Amb.d1f_add
    (Amb.stmt1_of_theorem1 hT1 hYalg hWrat) Amb.prop3 Amb.a_le_d1f X0
    (by rw [hb0]; exact one_ne_zero) hE1 hnoker
  rw [hd10, hc0, hb0, hdd0] at hineq
  push_cast at hineq
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)] at hineq
  have : ((m * 3 : ℕ) : ℚ) ≤ (finrank ℚ Y : ℚ) := by exact_mod_cast hY3
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast hm
  push_cast at this
  nlinarith

end StrongSix.Roy

end

end LeanPool
