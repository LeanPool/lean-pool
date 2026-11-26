/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Sphere
public import LeanPool.SplitCliqueGap.GapExtremal.GraphPadding
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Exact-order exponent estimates for split graphs

The cap construction combines the host padding theorem with a quantitative choice of seed.

-/

@[expose] public section

namespace GapExtremal

open Finset

/-! ### From a padded family to every order -/

/-- **From a padded family to all orders exactly.** -/
theorem exponent_of_family_exact {M a K : ℕ} (hM : 2 ≤ M) (ha : 1 ≤ a) (hK : 0 < K)
    (V : ℕ → ℕ → Type) [∀ j k, Fintype (V j k)] [∀ j k, DecidableEq (V j k)]
    (G : ∀ j k, SimpleGraph (V j k)) (b : ℕ → ℕ) (hb : ∀ j, b j ≤ K * M ^ j)
    (hcard : ∀ j k, Fintype.card (V j k) = b j + k) (hsplit : ∀ j k, IsSplit (G j k))
    (hconn : ∀ j k, (G j k).Connected)
    (hgap : ∀ j k, (a : ℝ) ^ j * (M : ℝ) ^ j / 3 ≤ gap (G j k)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, K * M ≤ n →
      ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
        Fintype.card V' = n ∧ IsSplit G' ∧ G'.Connected ∧
        c * (n : ℝ) ^ (1 + Real.log a / Real.log M) ≤ gap G' := by
  refine ⟨((K : ℝ) * M) ^ (-(1 + Real.log a / Real.log M)) / 3, by positivity, fun n hn => ?_⟩
  obtain ⟨j, hsize, hscale⟩ := exponent_budget hM ha hK hn
  have hbn : b j ≤ n := (hb j).trans hsize
  refine ⟨V j (n - b j), inferInstance, inferInstance, G j (n - b j), ?_, hsplit _ _, hconn _ _,
    hscale.trans (hgap j _)⟩
  rw [hcard]
  omega

/-! ### The padded positioned construction -/

section PPad

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]
variable {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
variable {U : Type*} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

instance instDecEqPadIdx (k : ℕ) : DecidableEq (PHostIdx F W P U ⊕ Fin k) :=
  @instDecidableEqSum _ _ instDecEqPHostIdx inferInstance

instance instDecEqSumPadIdx (k : ℕ) : DecidableEq (V ⊕ (PHostIdx F W P U ⊕ Fin k)) :=
  @instDecidableEqSum _ _ inferInstance (instDecEqPadIdx k)

/-- **Cor. 16.4, padded.** -/
theorem pgap_ge_third_pad (D : PData F W V P) {C : Finset W} (hC : IsSCap (actCol D) (C : Set W))
    (hC0 : C.Nonempty) (S : SepFam F C U)
    (hsame : ∀ v v', D.base v = D.base v' → ∀ i j, D.σ i = D.pos v → D.σ j = D.pos v' →
      ¬ H12.graph.Adj i j) (x0 : V) (k : ℕ) :
    ((C.card * Fintype.card W : ℕ) : ℝ) / 3 ≤ gap (hostGraph (padN (ppalette D C S) x0 k)) := by
  have h := gap_ge ((phostHyp (S := S) hC0 hsame).pad x0 k) (8 * (pblocks D C).card)
    (fun T hT => pI_le_s D hC hT) (presPack (D := D) (C := C))
  have hv := pvalue (D := D) (C := C)
  have hb : ((pblocks D C).card : ℝ) ≤ C.card * Fintype.card W := by
    exact_mod_cast card_pblocks_le D
  push_cast at h ⊢
  linarith

end PPad

/-! ### Exact-order transfer for S-caps -/

section Single

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

/-- The padded one-layer graph of `A^j`. -/
abbrev SVk (F U : Type) (j k : ℕ) :=
  (F × (Fin j → U)) ⊕ (PHostIdx F (Fin j → U) F U ⊕ Fin k)

omit [DecidableEq F] [DecidableEq U] in
/-- **TP-cond for S-caps, exact order, connected.** -/
theorem tp_single_s_exact (σ : Fin 6 ↪ F) {A : Finset U} (hA : IsSCap (Set.range σ) (A : Set U))
    (hA0 : A.Nonempty) {e : U} (he : e ≠ 0) (hM : 2 ≤ Fintype.card U) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      3 * (Fintype.card F + 1) ^ 4 * Fintype.card U * Fintype.card U ≤ n →
      ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
        Fintype.card V' = n ∧ IsSplit G' ∧ G'.Connected ∧
        c * (n : ℝ) ^ (1 + Real.log A.card / Real.log (Fintype.card U)) ≤ gap G' := by
  classical
  set M := Fintype.card U
  have hcapne : ∀ j, (capPow A j).Nonempty := fun j => by
    obtain ⟨a0, ha0⟩ := hA0
    exact ⟨fun _ => a0, by simp [capPow, ha0]⟩
  refine exponent_of_family_exact hM hA0.card_pos (by positivity) (SVk F U)
    (fun j k => hostGraph (padN (ppalette (single (W := Fin j → U) σ) (capPow A j) (prodSep A he j))
      ((0 : F), (0 : Fin j → U)) k))
    (fun j => Fintype.card (SV F U j)) (fun j => card_SV_le j)
    (fun j k => card_pad k) (fun j k => isSplit_hostGraph _)
    (fun j k => connected_hostGraph _ ((0 : F), (0 : Fin j → U)) (padN_nonempty _ _ _)) (fun j k
      => ?_)
  have h := pgap_ge_third_pad (single (W := Fin j → U) σ) (isSCap_capPow hA j) (hcapne j)
    (prodSep A he j) (single_same σ) ((0 : F), (0 : Fin j → U)) k
  rw [card_capPow] at h
  have hW : Fintype.card (Fin j → U) = M ^ j := by simp [M]
  rw [hW] at h
  push_cast at h
  exact h

end Single

/-- **Theorem 17.0, exact form.** For every large `n` there is a connected split graph of order
exactly `n`
with `cp − cp* ≥ c n^{2 − ε}`. -/
theorem exponent_two_exact {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
        Fintype.card V' = n ∧ IsSplit G' ∧ G'.Connected ∧ c * (n : ℝ) ^ (2 - ε) ≤ gap G' := by
  have hl10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  -- a large prime
  obtain ⟨p, hpM, hpp⟩ := Nat.exists_infinite_primes (⌈Real.exp (2 * Real.log 10 / ε)⌉₊ + 11)
  have : Fact p.Prime := ⟨hpp⟩
  have hp11 : 11 ≤ p := by omega
  have hp5 : 5 < p := by omega
  set K := (p - 1) / 10 with hKdef
  have hK : 10 * K < p := by
    have := Nat.div_mul_le_self (p - 1) 10
    rw [hKdef]; omega
  have hK1 : 1 ≤ K := by rw [hKdef]; exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hpK : p ≤ 10 * (K + 1) := by
    have h1 := Nat.div_add_mod (p - 1) 10
    have h2 := Nat.mod_lt (p - 1) (show 0 < 10 by norm_num)
    rw [hKdef]; omega
  have hpr : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  set L := Real.log p with hLdef
  have hL : 0 < L := Real.log_pos hpr
  have hLbig : 2 * Real.log 10 / ε ≤ L := by
    have h1 : Real.exp (2 * Real.log 10 / ε) ≤ p := by
      have := Nat.le_ceil (Real.exp (2 * Real.log 10 / ε))
      have h2 : ((⌈Real.exp (2 * Real.log 10 / ε)⌉₊ : ℕ) : ℝ) ≤ p := by exact_mod_cast (by omega :
        _ ≤ p)
      linarith
    rw [hLdef, ← Real.log_exp (2 * Real.log 10 / ε)]
    exact Real.log_le_log (Real.exp_pos _) h1
  have hlog10 : Real.log 10 / L ≤ ε / 2 := by
    rw [div_le_iff₀ hL]
    have := mul_le_mul_of_nonneg_left hLbig hε.le
    rw [mul_div_cancel₀ _ hε.ne'] at this
    linarith
  have hKlog : L ≤ Real.log 10 + Real.log (K + 1) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpK)
  -- choose `N` with `log (N R' + 1) ≤ (ε/2) N L`
  set R' := K ^ 2 + 1 with hR'def
  have hR'pos : (0 : ℝ) < R' := by positivity
  have hε2 : 0 < ε / 2 := by positivity
  set a : ℝ := L / R'
  have ha : a ≠ 0 := by positivity
  have ht := Real.tendsto_pow_log_div_mul_add_atTop a (-a) 1 ha
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 ht).2 (ε / 2) hε2)
  set N : ℕ := ⌈X⌉₊ + 1 with hNdef
  have hN : 0 < N := by omega
  have hxN : X ≤ (N : ℝ) * R' + 1 := by
    have h1 := Nat.le_ceil X
    have h2 : (⌈X⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈X⌉₊ ≤ N by omega)
    have h3 : (N : ℝ) ≤ N * R' := by
      have : (1 : ℝ) ≤ R' := by exact_mod_cast (show 1 ≤ R' by omega)
      nlinarith
    linarith
  have hlogN : Real.log ((N : ℝ) * R' + 1) ≤ ε / 2 * (N * L) := by
    have := (hX _ hxN).le
    simp only [pow_one] at this
    have hden : a * ((N : ℝ) * R' + 1) + -a = N * L := by
      simp only [a]; field_simp; ring
    rw [hden, div_le_iff₀ (by positivity)] at this
    linarith
  -- the seed
  obtain ⟨r, hr⟩ := exists_large_sphere K N (R := R') (by omega)
  set A := seed p K N r with hAdef
  have hAcard : A.card = (sphere K N r).card := card_sphereSeed (by omega)
  have hApos : 0 < A.card := by
    rw [hAcard]
    by_contra h0
    push Not at h0
    have : (sphere K N r).card = 0 := by omega
    rw [this, mul_zero] at hr
    have : 0 < (K + 1) ^ N := by positivity
    omega
  have hcardU : Fintype.card (Fin N → ZMod p) = p ^ N := by simp
  have hM : 2 ≤ Fintype.card (Fin N → ZMod p) := by
    rw [hcardU]
    calc 2 ≤ p ^ 1 := by simp; omega
      _ ≤ p ^ N := Nat.pow_le_pow_right (by omega) hN
  have he : (fun _ => (1 : ZMod p) : Fin N → ZMod p) ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hN⟩
    simp at this
  obtain ⟨c, hc, h⟩ := tp_single_s_exact (colσ hp5) (isSCap_seed (N := N) (r := r) hK hp5)
    (Finset.card_pos.mp hApos) he hM
  refine ⟨c, hc, 3 * (Fintype.card (ZMod p) + 1) ^ 4 * Fintype.card (Fin N → ZMod p) *
    Fintype.card (Fin N → ZMod p), fun n hn => ?_⟩
  obtain ⟨V', i1, i2, G', hcard, hsplit, hconn, hgap⟩ := h n hn
  refine ⟨V', i1, i2, G', hcard, hsplit, hconn, le_trans ?_ hgap⟩
  have hn1 : (1 : ℝ) ≤ n := by
    have h0 : 0 < 3 * (Fintype.card (ZMod p) + 1) ^ 4 * Fintype.card (Fin N → ZMod p) *
        Fintype.card (Fin N → ZMod p) := by positivity
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hlogU : Real.log (Fintype.card (Fin N → ZMod p) : ℝ) = N * L := by
    rw [hcardU]; push_cast
    rw [Real.log_pow]
  have hrate : 1 - ε ≤ Real.log A.card / Real.log (Fintype.card (Fin N → ZMod p) : ℝ) := by
    rw [hlogU]
    have hA : ((K + 1 : ℕ) : ℝ) ^ N ≤ ((N : ℝ) * R' + 1) * A.card := by
      rw [hAcard]; exact_mod_cast hr
    have hlog : (N : ℝ) * Real.log (K + 1) ≤ Real.log ((N : ℝ) * R' + 1) + Real.log A.card := by
      have hK0 : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
      rw [← Real.log_mul (by positivity) (by exact_mod_cast hApos.ne')]
      have := Real.log_le_log (by positivity) hA
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hNL : (0 : ℝ) < N * L := by positivity
    rw [le_div_iff₀ hNL]
    -- `log 10 ≤ (ε/2) L`
    have h10 : Real.log 10 ≤ ε / 2 * L := by
      rw [div_le_iff₀ hL] at hlog10; linarith
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    nlinarith
  have hexp := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith :
    2 - ε ≤ 1 + Real.log A.card / Real.log (Fintype.card (Fin N → ZMod p) : ℝ))
  exact mul_le_mul_of_nonneg_left hexp hc.le

end GapExtremal
