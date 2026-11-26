/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.ExponentTwo
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Exact order and connectivity (ledger L1.2)

Hosts whose palette is a single core vertex are pendant leaves. Padding a host family (`padN`):
* gives every empty palette the vertex `x₀`;
* adds `k` new hosts with palette `{x₀}`.

The bridge hypotheses `HostHyp` survive (`HostHyp.pad`), so the lower bound of `gap_ge` is
unchanged. The graph
stays split, becomes connected (`connected_hostGraph`), and its order grows by exactly `k`. With
`exponent_of_family_exact` this gives the final statements for split **connected** graphs of order
**exactly**
`n`:
* `tp_single_s_exact`;
* **`exponent_two_exact`**.
-/

@[expose] public section

namespace GapExtremal

open Finset

/-! ### Padding a host family -/

section Pad

variable {V : Type*} [Fintype V] [DecidableEq V] {H : Type*} [Fintype H] [DecidableEq H]

/-- Padded palettes: empty palettes become `{x₀}`, and `k` new hosts with palette `{x₀}`. -/
def padN (N : H → Finset V) (x0 : V) (k : ℕ) : H ⊕ Fin k → Finset V
  | .inl h => if N h = ∅ then {x0} else N h
  | .inr _ => {x0}

omit [DecidableEq H] [Fintype H] [Fintype V] in
theorem padN_nonempty (N : H → Finset V) (x0 : V) (k : ℕ) (h : H ⊕ Fin k) : (padN N x0 k
  h).Nonempty := by
  rcases h with h | i
  · simp only [padN]
    split_ifs with h0
    · exact Finset.singleton_nonempty _
    · exact Finset.nonempty_iff_ne_empty.mpr h0
  · exact Finset.singleton_nonempty _

omit [DecidableEq H] [Fintype H] [Fintype V] in
theorem HostHyp.pad {B : SimpleGraph V} {N : H → Finset V} {φ : V → V → H}
    (hH : HostHyp B N φ) (x0 : V) (k : ℕ) :
    HostHyp B (padN N x0 k) (fun x y => Sum.inl (φ x y)) where
  indep := by
    rintro (h | i) x hx y hy hxy
    · simp only [padN] at hx hy
      split_ifs at hx hy with h0
      · rw [Finset.mem_singleton] at hx hy
        subst hx; subst hy
        exact B.loopless.irrefl _ hxy
      · exact hH.indep h x hx y hy hxy
    · simp only [padN, Finset.mem_singleton] at hx hy
      subst hx; subst hy
      exact B.loopless.irrefl _ hxy
  cover := by
    intro x y hne hadj
    obtain ⟨hx, hy⟩ := hH.cover x y hne hadj
    have h0 : N (φ x y) ≠ ∅ := Finset.ne_empty_of_mem hx
    simp only [padN, ite_eq_right h0]
    exact ⟨hx, hy⟩
  symm := fun x y => by rw [hH.symm x y]
  inj := fun x y y' h1 h2 h3 h4 h => hH.inj x y y' h1 h2 h3 h4 (Sum.inl_injective h)

omit [DecidableEq H] [DecidableEq V] in
theorem card_pad (k : ℕ) :
    Fintype.card (V ⊕ (H ⊕ Fin k)) = Fintype.card (V ⊕ H) + k := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

omit [DecidableEq V] [Fintype V] in
/-- A host graph with a nonempty core and nonempty palettes is connected. -/
theorem connected_hostGraph {H' : Type*} (N : H' → Finset V) (x0 : V)
    (hN : ∀ h, (N h).Nonempty) :
    (hostGraph N).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have hcore : ∀ y : V, (hostGraph N).Reachable (.inl x0) (.inl y) := fun y => by
    by_cases hy : x0 = y
    · rw [hy]
    · exact SimpleGraph.Adj.reachable ((hostGraph_inl_inl N _ _).mpr hy)
  refine ⟨.inl x0, ?_⟩
  rintro (y | h)
  · exact hcore y
  · obtain ⟨y, hy⟩ := hN h
    exact (hcore y).trans (SimpleGraph.Adj.reachable ((hostGraph_inl_inr N _ _).mpr hy))

end Pad

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
  set α := 1 + Real.log a / Real.log M
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hα : 0 ≤ α := by
    have h1 : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
    have h2 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
    positivity
  refine ⟨((K : ℝ) * M) ^ (-α) / 3, by positivity, fun n hn => ?_⟩
  set j := Nat.log M (n / K) with hj
  have hMj : M ^ j ≤ n / K := Nat.pow_log_le_self M (by
    have : 1 ≤ n / K := (Nat.le_div_iff_mul_le hK).mpr (by
      have := Nat.mul_le_mul_left K (show 1 ≤ M by omega); nlinarith)
    omega)
  have hlt : n / K < M ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) _
  have hbn : b j ≤ n := by
    calc b j ≤ K * M ^ j := hb j
      _ ≤ K * (n / K) := Nat.mul_le_mul_left K hMj
      _ ≤ n := Nat.mul_div_le n K
  refine ⟨V j (n - b j), inferInstance, inferInstance, G j (n - b j), ?_, hsplit _ _, hconn _ _, ?_⟩
  · rw [hcard]; omega
  · have hn' : (n : ℝ) / (K * M) ≤ (M : ℝ) ^ j := by
      have h1 : n < K * (n / K) + K := by
        have := Nat.div_add_mod n K
        have := Nat.mod_lt n hK
        omega
      have h2 : n < K * M ^ (j + 1) := by
        calc n < K * (n / K) + K := h1
          _ = K * (n / K + 1) := by ring
          _ ≤ K * M ^ (j + 1) := Nat.mul_le_mul_left K hlt
      rw [div_le_iff₀ (by positivity)]
      have : (n : ℝ) < K * M ^ (j + 1) := by exact_mod_cast h2
      rw [pow_succ] at this
      nlinarith
    have hpow := pow_rpow_alpha ha hM j
    have hmono : ((n : ℝ) / (K * M)) ^ α ≤ ((M : ℝ) ^ j) ^ α :=
      Real.rpow_le_rpow (by positivity) hn' hα
    have hsplit' : ((n : ℝ) / (K * M)) ^ α = ((K : ℝ) * M) ^ (-α) * (n : ℝ) ^ α := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
      ring
    refine le_trans ?_ (hgap j _)
    calc ((K : ℝ) * M) ^ (-α) / 3 * (n : ℝ) ^ α = ((n : ℝ) / (K * M)) ^ α / 3 := by
          rw [hsplit']; ring
      _ ≤ ((M : ℝ) ^ j) ^ α / 3 := by linarith
      _ = (a : ℝ) ^ j * (M : ℝ) ^ j / 3 := by rw [hpow]

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

omit [DecidableEq F] [Field F] [AddCommGroup U] [Module F U] [DecidableEq U] in
theorem card_SV_le [Nonempty U] (j : ℕ) :
    Fintype.card (SV F U j) ≤ 3 * (Fintype.card F + 1) ^ 4 * Fintype.card U * Fintype.card U ^ j
      := by
  set M := Fintype.card U
  set q := Fintype.card F
  have hc := pcard_vertices (F := F) (W := Fin j → U) (V := F × (Fin j → U)) (P := F) (U := U)
  rw [hc]
  simp only [Fintype.card_prod, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Sym2.card]
  set X := M ^ j
  set C2 := (q + 1).choose 2 with hC2
  have hsym : C2 ≤ (q + 1) ^ 2 := by
    rw [hC2, Nat.choose_two_right, sq]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hq4 : (q + 1) ^ 2 ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have f1 : q ≤ (q + 1) ^ 4 := le_trans (by nlinarith) hq4
  have f2 : q * q * C2 ≤ (q + 1) ^ 4 := by
    calc q * q * C2 ≤ q * q * (q + 1) ^ 2 := Nat.mul_le_mul_left _ hsym
      _ ≤ (q + 1) ^ 2 * (q + 1) ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)
      _ = (q + 1) ^ 4 := by ring
  have f3 : q * C2 ≤ (q + 1) ^ 4 := by
    calc q * C2 ≤ (q + 1) * (q + 1) ^ 2 := Nat.mul_le_mul (by omega) hsym
      _ ≤ (q + 1) ^ 4 := by
        calc (q + 1) * (q + 1) ^ 2 = (q + 1) ^ 3 := by ring
          _ ≤ (q + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hM1 : 1 ≤ M := Fintype.card_pos
  have hX : X ≤ M * X := Nat.le_mul_of_pos_left _ (by omega)
  have e1 : q * X ≤ (q + 1) ^ 4 * (M * X) := Nat.mul_le_mul f1 hX
  have e2 : q * X * (M * q * C2) = (q * q * C2) * (M * X) := by ring
  have e3 : q * X * C2 = (q * C2) * X := by ring
  have e4 : (q * C2) * X ≤ (q + 1) ^ 4 * (M * X) := Nat.mul_le_mul f3 hX
  have e5 : (q * q * C2) * (M * X) ≤ (q + 1) ^ 4 * (M * X) := Nat.mul_le_mul_right _ f2
  calc q * X + q * X * (M * q * C2) + q * X * C2
      ≤ (q + 1) ^ 4 * (M * X) + (q + 1) ^ 4 * (M * X) + (q + 1) ^ 4 * (M * X) := by
        rw [e2, e3]; exact Nat.add_le_add (Nat.add_le_add e1 e5) e4
    _ = 3 * (q + 1) ^ 4 * M * X := by ring

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
