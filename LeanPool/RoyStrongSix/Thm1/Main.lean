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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Roy.Final
public import LeanPool.RoyStrongSix.Thm1.Core6

/-!
# The multiplicity estimate implies Waldschmidt's Theorem 1 (and strong six)

* `core_of_multEst : MultEst Qb → CoreT1`. Fix the data and a large base `β`, and look at the
  interpolation matrix. Either its columns are dependent: then `obstruction` and
  `concl_of_obstruction` give the conclusion. Or a maximal minor is non-zero: then Liouville
  (`liouville_det`) against Laurent's bound (`interpDet_bound`) contradicts `growth_core`.
* `theorem1_of_multEst : MultEst Qb → WaldschmidtTheorem1`.
* `strongSix_of_multEst : MultEst Qb → StrongSixExponentials`.
-/

@[expose] public section

namespace LeanPool

open Module Submodule _root_.MvPolynomial NumberField
open StrongSix.Roy

namespace StrongSix.Thm1

/-- The interpolation space has enough monomials for the analytic determinant bound. -/
theorem card_mono_ge_power (X : Params.Exps) {d0 d1 n β : ℕ} (hn : 1 ≤ n)
    (hβ2 : 2 ≤ β) (hd0β : d0 ≤ β) (hd1β : d1 ≤ β) (hx1 : 1 ≤ X.x1)
    (hm : n * X.θ + 2 * n + (d0 + d1) + 1 ≤ d0 * X.Q + d1 * X.x1) :
    2 * (β ^ (n * X.θ + 2)) ^ n ≤
      Fintype.card (Mono d0 d1 (β ^ (n * X.Q)) (β ^ (n * X.x1))) := by
  classical
  set L0 := β ^ (n * X.Q) with hL0def
  set L1 := β ^ (n * X.x1) with hL1def
  set M := β ^ (n * X.θ + 2) with hMdef
  set N := Fintype.card (Mono d0 d1 L0 L1)
  set d := d0 + d1 with hd
  change 2 * M ^ n ≤ N
  have hQ1 : 1 ≤ n * X.Q := Nat.mul_pos (by omega) (by
    have := X.K_pos; unfold Params.Exps.Q; positivity)
  have hx1' : 1 ≤ n * X.x1 := Nat.mul_pos (by omega) (by omega)
  set A0 := β ^ (n * X.Q - 1) with hA0
  set B0 := β ^ (n * X.x1 - 1) with hB0
  have hLA : L0 = β * A0 := by
    rw [hL0def, hA0, ← pow_succ', Nat.sub_add_cancel hQ1]
  have hLB : L1 = β * B0 := by
    rw [hL1def, hB0, ← pow_succ', Nat.sub_add_cancel hx1']
  have hcard := card_Mono_ge (d0 := d0) (d1 := d1) (L0 := L0) (L1 := L1) (A := A0) (B := B0)
    (by rw [hLA]; exact Nat.mul_le_mul_right A0 hd0β)
    (by rw [hLB]; exact Nat.mul_le_mul_right B0 hd1β)
    (by rw [hLA]; exact Nat.le_mul_of_pos_left A0 (show 0 < β by omega))
    (by rw [hLB]; exact Nat.le_mul_of_pos_left B0 (show 0 < β by omega))
  have hlow : A0 ^ d0 * B0 ^ d1 ≤ N :=
    le_trans (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_succ _) _)
      (Nat.pow_le_pow_left (Nat.le_succ _) _)) hcard
  have hpow : A0 ^ d0 * B0 ^ d1 = β ^ ((n * X.Q - 1) * d0 + (n * X.x1 - 1) * d1) := by
    rw [hA0, hB0, ← pow_mul, ← pow_mul, ← pow_add]
  -- the exponent inequality
  have hexp : (n * X.θ + 2) * n + 1 ≤ (n * X.Q - 1) * d0 + (n * X.x1 - 1) * d1 := by
    have h1 := Nat.mul_le_mul_left n hm
    have e1 : n * (n * X.θ + 2 * n + d + 1) = n * (n * X.θ) + 2 * (n * n) + n * d + n := by ring
    have e2 : n * (d0 * X.Q + d1 * X.x1) = n * X.Q * d0 + n * X.x1 * d1 := by ring
    have e3 : (n * X.θ + 2) * n = n * (n * X.θ) + 2 * n := by ring
    have f1 : (n * X.Q - 1) * d0 + d0 = n * X.Q * d0 := by
      rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hQ1)]
    have f2 : (n * X.x1 - 1) * d1 + d1 = n * X.x1 * d1 := by
      rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hx1')]
    have g1 : n ≤ n * n := Nat.le_mul_self n
    have g2 : d ≤ n * d := Nat.le_mul_of_pos_left _ (by omega)
    omega
  calc 2 * M ^ n = 2 * β ^ ((n * X.θ + 2) * n) := by rw [hMdef, ← pow_mul]
    _ ≤ β * β ^ ((n * X.θ + 2) * n) := Nat.mul_le_mul_right _ hβ2
    _ = β ^ ((n * X.θ + 2) * n + 1) := by rw [pow_succ']
    _ ≤ β ^ ((n * X.Q - 1) * d0 + (n * X.x1 - 1) * d1) := Nat.pow_le_pow_right (by omega) hexp
    _ = A0 ^ d0 * B0 ^ d1 := hpow.symm
    _ ≤ N := hlow

/-- The entry majorant is at least one for positive degree bounds. -/
theorem one_le_analytic_entry_bound {Hd H0 H1 : ℝ} {L0 L1 TJ ℓ S : ℕ}
    (hHd : 1 ≤ Hd) (hH0' : 0 ≤ H0) (hH1' : 0 ≤ H1) (hL01 : 1 ≤ L0) :
    1 ≤ (Hd * ((L0 : ℝ) + L1)) ^ TJ * (1 + 2 * ((ℓ : ℝ) * S * H0)) ^ L0 *
      (Real.exp (2 * ((ℓ : ℝ) * S * H1))) ^ L1 := by
  have h1 : (1 : ℝ) ≤ Hd * (L0 + L1) := by
    have : (1 : ℝ) ≤ L0 := by exact_mod_cast hL01
    nlinarith [Nat.cast_nonneg (α := ℝ) L1]
  have h2 : (1 : ℝ) ≤ 1 + 2 * (ℓ * S * H0) := by
    have : (0 : ℝ) ≤ ℓ * S * H0 := by positivity
    linarith
  have h3 : (1 : ℝ) ≤ Real.exp (2 * (ℓ * S * H1)) := Real.one_le_exp (by positivity)
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1)
    (one_le_pow₀ h2)) (one_le_pow₀ h3)

/-- The entry majorant is at least one for positive degree bounds. -/
theorem one_le_arithmetic_entry_bound {Hd : ℝ} {L0 L1 TJ ℓ S : ℕ}
    (hHd : 1 ≤ Hd) (hL01 : 1 ≤ L0) :
    1 ≤ (Hd * ((L0 : ℝ) + L1)) ^ TJ * (1 + (ℓ : ℝ) * S * Hd) ^ L0 *
      (Hd ^ (ℓ * S)) ^ L1 := by
  have h1 : (1 : ℝ) ≤ Hd * (L0 + L1) := by
    have : (1 : ℝ) ≤ L0 := by exact_mod_cast hL01
    nlinarith [Nat.cast_nonneg (α := ℝ) L1]
  have h2 : (1 : ℝ) ≤ 1 + ℓ * S * Hd := by
    have : (0 : ℝ) ≤ ℓ * S * Hd := by positivity
    linarith
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1)
    (one_le_pow₀ h2)) (one_le_pow₀ (one_le_pow₀ hHd))

/-- The chosen powers satisfy the inequalities used in the logarithmic growth comparison. -/
theorem interpolation_growth_bounds (X : Params.Exps) (d0 d1 n β : ℕ)
    (hβ1 : 1 ≤ β) (hqp : X.q ≤ X.p) :
    let T := β ^ (n * X.θ)
    let L0 := β ^ (n * X.Q)
    let L1 := β ^ (n * X.x1)
    let TJ := (d0 + d1) * T + 1
    let S := (d0 + d1) * β ^ (n * X.σ)
    let N := Fintype.card (Mono d0 d1 L0 L1)
    (1 : ℝ) ≤ T ∧ (L0 : ℝ) = (β : ℝ) ^ (n * X.Q) ∧ (L0 : ℝ) ≤ T ∧ L1 ≤ L0 ∧
      (TJ : ℝ) ≤ ((d0 + d1 : ℕ) + 1) * T ∧
      (S : ℝ) ≤ (d0 + d1 : ℕ) * (β : ℝ) ^ (n * X.σ) ∧
      (L1 : ℝ) * S ≤ (d0 + d1 : ℕ) * T ∧
      (N : ℝ) ≤ (2 * (β : ℝ) ^ (n * X.Q)) ^ (d0 + d1) := by
  classical
  dsimp only
  set T := β ^ (n * X.θ) with hTdef
  set L0 := β ^ (n * X.Q) with hL0def
  set L1 := β ^ (n * X.x1) with hL1def
  set S' := β ^ (n * X.σ) with hS'def
  set TJ := (d0 + d1) * T + 1 with hTJdef
  set S := (d0 + d1) * S' with hSdef
  set N := Fintype.card (Mono d0 d1 L0 L1)
  set d := d0 + d1 with hd
  set a := n * X.Q with ha
  set b := n * X.σ with hb
  have hT1 : 1 ≤ T := Nat.one_le_pow _ _ hβ1
  have hL01 : 1 ≤ L0 := Nat.one_le_pow _ _ hβ1
  have hx1Q : X.x1 ≤ X.Q := by have := X.x1_add_sigma hqp; omega
  have hQθ : X.Q ≤ X.θ := by unfold Params.Exps.θ; omega
  have hb1 : (1 : ℝ) ≤ β := by exact_mod_cast hβ1
  have hT1' : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have haθ : n * X.Q ≤ n * X.θ := Nat.mul_le_mul_left _ hQθ
  have hL0eq : (L0 : ℝ) = (β : ℝ) ^ a := by rw [hL0def, ha]; push_cast; rfl
  have hL0T : (L0 : ℝ) ≤ T := by exact_mod_cast Nat.pow_le_pow_right (by omega) haθ
  have hL1L0 : L1 ≤ L0 := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hx1Q)
  have hTJ : (TJ : ℝ) ≤ (d + 1) * T := by
    have : TJ ≤ (d + 1) * T := by rw [hTJdef]; nlinarith
    exact_mod_cast this
  have hS : (S : ℝ) ≤ d * (β : ℝ) ^ b := by
    rw [hSdef, hS'def, hb, hd]; push_cast; exact le_refl _
  have hL1S : (L1 : ℝ) * S ≤ d * T := by
    have e : L1 * S = d * L0 := by
      change β ^ (n * X.x1) * (d * β ^ (n * X.σ)) = d * β ^ (n * X.Q)
      rw [mul_comm d, ← mul_assoc, ← pow_add, ← Nat.mul_add, X.x1_add_sigma hqp]
      ring
    have : L1 * S ≤ d * T := by
      rw [e]; exact Nat.mul_le_mul_left _ (by exact_mod_cast hL0T)
    exact_mod_cast this
  have hNle : (N : ℝ) ≤ (2 * (β : ℝ) ^ a) ^ d := by
    have h1 := card_Mono_le (d0 := d0) (d1 := d1) L0 L1
    have h2 : (L0 + 1) ^ d0 * (L1 + 1) ^ d1 ≤ (2 * L0) ^ d0 * (2 * L0) ^ d1 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_left (by omega) _)
    have h3 : N ≤ (2 * L0) ^ d := by rw [hd, pow_add]; exact h1.trans h2
    have h4 : (N : ℝ) ≤ ((2 * L0) ^ d : ℕ) := by exact_mod_cast h3
    have h5 : (((2 * L0) ^ d : ℕ) : ℝ) = (2 * (β : ℝ) ^ a) ^ d := by push_cast; rw [hL0eq]
    exact h4.trans h5.le
  exact ⟨hT1', hL0eq, hL0T, hL1L0, hTJ, hS, hL1S, hNle⟩

/-- **The core of Theorem 1.** -/
theorem core_of_multEst (hM : MultEst Qb) : CoreT1 := by
  intro d0 d1 Y W V H hn1 hd0n
  classical
  obtain ⟨C, hC⟩ := obstruction hM d0 d1
  obtain ⟨ℓ, η, hηY, hηmem, ⟨D⟩, t, wb, hwb⟩ := exists_data H
  have hVlt := finrank_lt_of_ne_top H.Vne
  -- exponents
  set n := finrank ℂ ↥V with hn
  set X : Params.Exps := ⟨d1, d0 + d1 - n, n, d0 + d1⟩ with hX
  have hXp : X.p = d1 := rfl
  have hXq : X.q = d0 + d1 - n := rfl
  have hXn : X.n = n := rfl
  have hXd : X.d = d0 + d1 := rfl
  have hq : 1 ≤ X.q := by rw [hXq]; omega
  have hqp : X.q ≤ X.p := by rw [hXq, hXp]; omega
  have hpd : X.p ≤ X.d := by rw [hXp, hXd]; omega
  have hnd : X.n + X.q = X.d := by rw [hXn, hXq, hXd]; omega
  have hmargin := X.margin hq hqp hpd hnd
  have hx1 := X.one_le_x1 hqp hn1
  have hx1Q : X.x1 ≤ X.Q := by have := X.x1_add_sigma hqp; omega
  have hQθ : X.Q ≤ X.θ := by unfold Params.Exps.θ; omega
  -- points and directions lie in `V`
  have hηV : ∀ i, η i ∈ V := fun i => H.YV _ (hηmem i)
  have hwV : ∀ j, inclL d0 d1 (wb j) ∈ V := fun j => by
    have : wb j ∈ WK W := by rw [hwb]; exact subset_span ⟨j, rfl⟩
    exact H.WV this
  -- the number field and its constants
  obtain ⟨K, hfin, hle, hmem⟩ := exists_nf D wb
  have : FiniteDimensional ℚ K := hfin
  have : NumberField K := ⟨⟩
  obtain ⟨δ, Hd, hδ1, hHd, hδa, hδα, hδw1, hδw2, hHa, hHα, hHw1, hHw2⟩ :=
    exists_den_house D wb K hmem
  set H0 : ℝ := 1 + ∑ i, ∑ k, ‖(η i).1 k‖ with hH0def
  set H1 : ℝ := 1 + ∑ i, ∑ j, ‖(η i).2 j‖ with hH1def
  have hH0 : ∀ i k, ‖(η i).1 k‖ ≤ H0 := fun i k => by
    have h1 := Finset.single_le_sum (fun k _ => norm_nonneg ((η i).1 k)) (Finset.mem_univ k)
    have h2 := Finset.single_le_sum (f := fun i => ∑ k, ‖(η i).1 k‖)
      (fun i _ => Finset.sum_nonneg fun k _ => norm_nonneg ((η i).1 k)) (Finset.mem_univ i)
    linarith
  have hH1 : ∀ i j, ‖(η i).2 j‖ ≤ H1 := fun i j => by
    have h1 := Finset.single_le_sum (fun j _ => norm_nonneg ((η i).2 j)) (Finset.mem_univ j)
    have h2 := Finset.single_le_sum (f := fun i => ∑ j, ‖(η i).2 j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg ((η i).2 j)) (Finset.mem_univ i)
    linarith
  have hH0' : 0 ≤ H0 := by positivity
  have hH1' : 0 ≤ H1 := by positivity
  set k := finrank ℚ K with hkdef
  have hk : 1 ≤ k := Module.finrank_pos
  -- the constant of the growth comparison
  set d := d0 + d1 with hd
  set a := n * X.Q with ha
  set b := n * X.σ with hb
  set Ctot : ℝ := k * (d * (Real.log 2 + a)) +
    ((d + 1) * (Real.log (2 * Hd) + a) + (Real.log (1 + 2 * ℓ * H0 * d) + b) + 2 * ℓ * d * H1) +
    k * (Real.log δ * (d + 2 + ℓ * d)) +
    k * ((d + 1) * (Real.log (2 * Hd) + a) + (Real.log (1 + ℓ * Hd * d) + b) + ℓ * d * Real.log Hd)
    with hCtot
  obtain ⟨β₀, hβ₀⟩ := growth_core d Ctot
  -- the base
  set β : ℕ := max β₀ (max (⌈C⌉₊ + 1) (d + 2)) with hβdef
  have hββ₀ : β₀ ≤ β := le_max_left _ _
  have hβC : C < β := by
    have h1 : ⌈C⌉₊ + 1 ≤ β := le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : C ≤ ⌈C⌉₊ := Nat.le_ceil C
    have h3 : ((⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ β := by exact_mod_cast h1
    push_cast at h3; linarith
  have hβd : d + 2 ≤ β := le_trans (le_max_right _ _) (le_max_right _ _)
  have hβ1 : 1 ≤ β := by omega
  have hβ2 : 2 ≤ β := by omega
  -- the parameters
  set T : ℕ := β ^ (n * X.θ) with hTdef
  set L0 : ℕ := β ^ (n * X.Q) with hL0def
  set L1 : ℕ := β ^ (n * X.x1) with hL1def
  set S' : ℕ := β ^ (n * X.σ) with hS'def
  set TJ : ℕ := (d0 + d1) * T + 1 with hTJdef
  set S : ℕ := (d0 + d1) * S' with hSdef
  have hT1 : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
  have hL01 : 1 ≤ L0 := Nat.one_le_pow _ _ (by omega)
  have hL11 : 1 ≤ L1 := Nat.one_le_pow _ _ (by omega)
  set A := interpMatrix D wb TJ S L0 L1 with hA
  rcases dichotomy A with ⟨c, hc0, hc⟩ | ⟨sel, hsel⟩
  · -- dependent columns: the obstruction branch
    obtain ⟨P, hP, hbid, hvan⟩ := vanishing_of_kernel D wb W hwb c hc0 hc
    obtain ⟨h0, U, hndg, hineq⟩ := hC W H.rat η D P T L0 L1 S' hP hbid hT1 hL01 hL11
      (fun s hs => hvan s hs)
    exact concl_of_obstruction H η hηY X hXp hXd hXn hXq hqp hn1 hβC hβ1 h0 U hndg hineq
  · -- a non-zero maximal minor: contradiction
    exfalso
    set N := Fintype.card (Mono d0 d1 L0 L1) with hNdef
    let eM : Fin N ≃ Mono d0 d1 L0 L1 := (Fintype.equivFin _).symm
    let f : Fin N → (Fin n → ℂ) → ℂ := fun l => fC V (eM l)
    let J : Fin N → Jet n := fun ν => jetOf V wb hηV hwV (sel (eM ν))
    -- the minor over `Qbar`, and over `K`
    set B : Matrix (Fin N) (Fin N) Qb := (A.submatrix sel id).submatrix eM eM with hBdef
    have hBdet : B.det ≠ 0 := by rw [hBdef, Matrix.det_submatrix_equiv_self]; exact hsel
    set BK : Matrix (Fin N) (Fin N) K :=
      ((KMatrix D wb K hmem TJ S L0 L1).submatrix sel id).submatrix eM eM with hBKdef
    have hmapB : (ιK K hle).mapMatrix BK = B := by
      refine Matrix.ext fun ν l => ?_
      exact KMatrix_map D wb K hmem hle _ _
    have hBKdet : BK.det ≠ 0 := by
      intro h; apply hBdet; rw [← hmapB, ← RingHom.map_det, h, map_zero]
    -- the analytic value
    have hΨ : Ψ f J 1 = algebraMap K ℂ BK.det := by
      have h1 : Ψ f J 1 = ((algebraMap Qb ℂ).mapMatrix B).det := by
        unfold Ψ; congr 1; refine Matrix.ext fun ν l => ?_; exact entry_one V D wb hηV hwV _ _
      rw [h1, ← RingHom.map_det, ← hmapB, ← RingHom.map_det]
      rfl
    -- Liouville
    set E : ℕ := δ ^ TJ * δ ^ L0 * (δ ^ (ℓ * S)) ^ L1 with hEdef
    set Hent : ℝ := (Hd * (L0 + L1)) ^ TJ * (1 + ℓ * S * Hd) ^ L0 * (Hd ^ (ℓ * S)) ^ L1 with
      hHentdef
    have hbounds := fun ν l => KMatrix_bounds D wb K hmem δ hHd hδa hδα hδw1 hδw2 hHa hHα hHw1 hHw2
      (TJ := TJ) (S := S) hL01 (sel (eM ν)) (eM l)
    have hE0 : E ≠ 0 := by rw [hEdef]; positivity
    have hlow := liouville_det (algebraMap K ℂ) BK E (fun i j => (hbounds i j).1)
      (fun i j => (hbounds i j).2) hBKdet hE0
    -- Laurent
    set Bent : ℝ := (Hd * (L0 + L1)) ^ TJ * (1 + 2 * (ℓ * S * H0)) ^ L0 *
      (Real.exp (2 * (ℓ * S * H1))) ^ L1 with hBentdef
    set M : ℕ := β ^ (n * X.θ + 2) with hMdef
    have hup := interpDet_bound hn1 (f := f) (fun l => contDiff_fC V (eM l)) J M (R := 2) (B :=
      Bent)
      (by norm_num)
      (fun ν l z hz => entry_bound V D wb K hmem hηV hwV δ hHd hδw1 hδw2 hHw1 hHw2 hH0' hH1' hH0 hH1
        hL01 (sel (eM ν)) (eM l) z hz)
    rw [hΨ] at hup
    -- the logarithmic inequality
    have hN1 : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨⟨(0, 0), by simp⟩⟩
    have hBent1 : 1 ≤ Bent := one_le_analytic_entry_bound hHd hH0' hH1' hL01
    have hE1 : (1 : ℝ) ≤ E := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hE0
    have hHent1 : 1 ≤ Hent := one_le_arithmetic_entry_bound hHd hL01
    have hts : ∑ ν, (J ν).t ≤ N * TJ := by
      calc ∑ ν, (J ν).t ≤ ∑ _ν : Fin N, TJ := Finset.sum_le_sum fun ν _ =>
            (Row.word_length (sel (eM ν))).le.trans' (by simp [J, jetOf, Row.word])
        _ = N * TJ := by simp
    have hMN : 2 * M ^ n ≤ N := by
      apply card_mono_ge_power X hn1 hβ2 (by omega) (by omega) hx1
      have margin := hmargin
      rw [hXn, hXd, hXp] at margin
      have e : d0 + d1 - d1 = d0 := by omega
      rw [e] at margin
      simpa [hd, mul_comm] using margin
    have hlog := log_ineq hN1 hk hBent1 hE1 hHent1 hMN hts hup (by rw [← hkdef] at hlow; exact hlow)
    -- the growth comparison
    obtain ⟨hT1', hL0eq, hL0T, hL1L0, hTJ, hS, hL1S, hNle⟩ :=
      interpolation_growth_bounds X d0 d1 n β hβ1 hqp
    have hlN := log_N_le hβ1 (T := (T : ℝ)) hT1' hN1 hNle
    have hlB := log_B_le hβ1 hT1' hL0eq hL0T hL1L0 hL01 hTJ hS hL1S (ℓ := ℓ) hHd hH0' hH1'
    have hlE := log_E_le hβ1 hT1' hL0T hTJ hL1S (ℓ := ℓ) hδ1
    have hlH := log_H_le hβ1 hT1' hL0eq hL0T hL1L0 hL01 hTJ hS hL1S (ℓ := ℓ) hHd
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hRHS : (k : ℝ) * Real.log N + Real.log Bent + k * Real.log E + k * Real.log Hent ≤
        Ctot * T * (1 + Real.log β) := by
      calc
        _ ≤ (k : ℝ) * (d * (Real.log 2 + a) * T * (1 + Real.log β)) +
            (((d + 1) * (Real.log (2 * Hd) + a) +
              (Real.log (1 + 2 * ℓ * H0 * d) + b) + 2 * ℓ * d * H1) *
              T * (1 + Real.log β)) +
            k * (Real.log δ * (d + 2 + ℓ * d) * T * (1 + Real.log β)) +
            k * (((d + 1) * (Real.log (2 * Hd) + a) +
              (Real.log (1 + ℓ * Hd * d) + b) + ℓ * d * Real.log Hd) *
              T * (1 + Real.log β)) :=
          add_le_add (add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hlN hk0) hlB)
            (mul_le_mul_of_nonneg_left hlE hk0)) (mul_le_mul_of_nonneg_left hlH hk0)
        _ = _ := by rw [hCtot]; ring
    have hfin := hβ₀ β hββ₀ (T : ℝ) _ hT1' hRHS
    have hMr : ((M : ℕ) : ℝ) = (T : ℝ) * (β : ℝ) ^ 2 := by
      rw [hMdef, hTdef]; push_cast; rw [pow_add]
    have hTJr : ((TJ : ℕ) : ℝ) = d * T + 1 := by rw [hTJdef, hd]; push_cast; ring
    rw [hMr, hTJr] at hlog
    linarith

/-- **The multiplicity estimate implies Waldschmidt's Theorem 1.** -/
theorem theorem1_of_multEst (hM : MultEst Qb) : WaldschmidtTheorem1 :=
  theorem1_of_core (core_of_multEst hM)

/-- **The multiplicity estimate implies Roy's strong six exponentials theorem.** -/
theorem strongSix_of_multEst (hM : MultEst Qb) : StrongSixExponentials :=
  strongSix_of_theorem1 (theorem1_of_multEst hM)

end StrongSix.Thm1

end LeanPool
