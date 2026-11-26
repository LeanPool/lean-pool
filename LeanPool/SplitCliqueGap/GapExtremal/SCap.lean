/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Single
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# S-caps suffice (ledger §17, L17.1)

The cap hypothesis enters the positioned construction only through `tri_geom` and `one_geom`, and
there the
coefficients of the linear dependence are differences of *active* colours. So it suffices that the
seed `A` be an
**S-cap** for the set `S` of active colours: no three distinct `a, b, c ∈ A` and `s₁, s₂, s₃ ∈ S`
with `s₁ ≠ s₂` and
`(s₂ - s₁) a + (s₃ - s₂) b + (s₁ - s₃) c = 0`.

This file re-runs the chain `pblockHyp → pI_le → pgap_ge_third → tp_single` under that weaker
hypothesis
(`tp_single_s`). The original cap chain is left untouched.
-/

@[expose] public section

namespace GapExtremal

open Finset

/-! ### S-caps -/

section SCapDef

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- `A` is an `S`-cap: no colour relation `(s₂ - s₁) a + (s₃ - s₂) b + (s₁ - s₃) c = 0` with `s₁ ≠
s₂` among three
distinct points of `A`. -/
def IsSCap (S : Set K) (A : Set V) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A → a ≠ b → a ≠ c → b ≠ c →
    ∀ ⦃s₁⦄, s₁ ∈ S → ∀ ⦃s₂⦄, s₂ ∈ S → ∀ ⦃s₃⦄, s₃ ∈ S → s₁ ≠ s₂ →
      (s₂ - s₁) • a + (s₃ - s₂) • b + (s₁ - s₃) • c ≠ 0

/-- A colour relation with `s₂ = s₃` forces `a = c`. -/
theorem rel_eq23 {s₁ s₂ : K} (h12 : s₁ ≠ s₂) {a b c : V}
    (h : (s₂ - s₁) • a + (s₂ - s₂) • b + (s₁ - s₂) • c = 0) : a = c := by
  have : (s₂ - s₁) • (a - c) = 0 := by
    rw [smul_sub]
    have e : (s₁ - s₂) • c = -((s₂ - s₁) • c) := by rw [← neg_smul, neg_sub]
    rw [sub_self, zero_smul, add_zero, e] at h
    simpa [sub_eq_add_neg] using h
  rcases smul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm h12
  · exact sub_eq_zero.mp h0

/-- A colour relation with `s₁ = s₃` forces `a = b`. -/
theorem rel_eq13 {s₁ s₂ : K} (h12 : s₁ ≠ s₂) {a b c : V}
    (h : (s₂ - s₁) • a + (s₁ - s₂) • b + (s₁ - s₁) • c = 0) : a = b := by
  have : (s₂ - s₁) • (a - b) = 0 := by
    rw [smul_sub]
    have e : (s₁ - s₂) • b = -((s₂ - s₁) • b) := by rw [← neg_smul, neg_sub]
    rw [sub_self, zero_smul, add_zero, e] at h
    simpa [sub_eq_add_neg] using h
  rcases smul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm h12
  · exact sub_eq_zero.mp h0

/-- S-caps are closed under powers. -/
theorem IsSCap.pi {ι : Type*} {S : Set K} {A : Set V} (hA : IsSCap S A) :
    IsSCap S (Set.pi Set.univ (fun _ : ι => A)) := by
  intro a ha b hb c hc hab hac hbc s₁ h1 s₂ h2 s₃ h3 h12 hrel
  have hcoord : ∀ i, (s₂ - s₁) • a i + (s₃ - s₂) • b i + (s₁ - s₃) • c i = 0 := fun i => by
    simpa using congrFun hrel i
  by_cases h23 : s₂ = s₃
  · subst h23
    exact hac (funext fun i => rel_eq23 h12 (hcoord i))
  by_cases h13 : s₁ = s₃
  · subst h13
    exact hab (funext fun i => rel_eq13 h12 (hcoord i))
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
    by_contra h; push Not at h; exact hab (funext h)
  have hai := ha i (Set.mem_univ i)
  have hbi := hb i (Set.mem_univ i)
  have hci := hc i (Set.mem_univ i)
  by_cases hac' : a i = c i
  · -- then `(s₂ - s₃) (a i - b i) = 0`
    have e := hcoord i
    rw [← hac'] at e
    have : (s₂ - s₃) • (a i - b i) = 0 := by
      have : (s₂ - s₁) • a i + (s₃ - s₂) • b i + (s₁ - s₃) • a i = (s₂ - s₃) • (a i - b i) := by
        simp only [smul_sub, sub_smul]; abel
      rw [← this]; exact e
    rcases smul_eq_zero.mp this with h0 | h0
    · exact h23 (sub_eq_zero.mp h0)
    · exact hi (sub_eq_zero.mp h0)
  by_cases hbc' : b i = c i
  · have e := hcoord i
    rw [← hbc'] at e
    have : (s₂ - s₁) • (a i - b i) = 0 := by
      have : (s₂ - s₁) • a i + (s₃ - s₂) • b i + (s₁ - s₃) • b i = (s₂ - s₁) • (a i - b i) := by
        simp only [smul_sub, sub_smul]; abel
      rw [← this]; exact e
    rcases smul_eq_zero.mp this with h0 | h0
    · exact h12 (sub_eq_zero.mp h0).symm
    · exact hi (sub_eq_zero.mp h0)
  exact hA hai hbi hci hi hac' hbc' h1 h2 h3 h12 (hcoord i)

end SCapDef

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]

/-! ### Geometry under an S-cap -/

section Geom

variable {S : Set F} {C : Finset W} (hC : IsSCap S (C : Set W))
include hC

omit [Fintype W] in
/-- `tri_geom` under an S-cap, for points of active colours. -/
theorem tri_geom_s {x y z : F × W} {a b c : W} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) (hxy : x ≠ y)
    (hxS : x.1 ∈ S) (hyS : y.1 ∈ S) (hzS : z.1 ∈ S)
    (h1 : y - x = (y.1 - x.1) • u a) (h2 : z - y = (z.1 - y.1) • u b)
    (h3 : z - x = (z.1 - x.1) • u c) : ∃ d ∈ C, ∃ p : F × W, x ∈ line p d ∧ y ∈ line p d
      ∧ z ∈ line p d := by
  have hα : y.1 - x.1 ≠ 0 := by
    intro h0; rw [h0, zero_smul, sub_eq_zero] at h1; exact hxy h1.symm
  by_cases hab : a = b
  · subst hab
    refine ⟨a, ha, x, self_mem_line x a, mem_line_of_sub h1, ?_⟩
    refine mem_line.mpr ⟨(y.1 - x.1) + (z.1 - y.1), ?_⟩
    rw [add_smul, ← h1, ← h2]; abel
  by_cases hac : a = c
  · subst hac
    exact ⟨a, ha, x, self_mem_line x a, mem_line_of_sub h1, mem_line_of_sub h3⟩
  by_cases hbc : b = c
  · subst hbc
    refine ⟨b, hb, z, ?_, ?_, self_mem_line z b⟩
    · refine mem_line.mpr ⟨-(z.1 - x.1), ?_⟩
      rw [neg_smul, ← h3]; abel
    · refine mem_line.mpr ⟨-(z.1 - y.1), ?_⟩
      rw [neg_smul, ← h2]; abel
  exfalso
  have e1 := snd_eq_of_sub h1
  have e2 := snd_eq_of_sub h2
  have e3 := snd_eq_of_sub h3
  refine hC ha hb hc hab hac hbc hxS hyS hzS (fun h0 => hα (sub_eq_zero.mpr h0.symm)) ?_
  rw [show x.1 - z.1 = -(z.1 - x.1) by ring, ← e1, ← e2, neg_smul, ← e3]; abel

omit [Fintype W] in
/-- `one_geom` under an S-cap, for points of active colours. -/
theorem one_geom_s {x0 : F × W} {c0 : W} (hc0 : c0 ∈ C) {z y y' : F × W} (hz : z ∉ line x0 c0)
    (hy : y ∈ line x0 c0) (hy' : y' ∈ line x0 c0) (hzS : z.1 ∈ S) (hyS : y.1 ∈ S) (hy'S : y'.1 ∈ S)
    {d e' : W} (hd : d ∈ C) (he : e' ∈ C)
    (hzy : y - z = (y.1 - z.1) • u d) (hzy' : y' - z = (y'.1 - z.1) • u e') : y = y' := by
  by_contra hne
  have hyy := sub_of_mem_line hy hy'
  have hγ : y'.1 - y.1 ≠ 0 := fun h0 =>
    hne (fst_injOn_line x0 c0 hy hy' (sub_eq_zero.mp h0).symm)
  by_cases hdc : d = c0
  · subst hdc
    apply hz
    rw [← line_eq_of_mem hy]
    refine mem_line.mpr ⟨-(y.1 - z.1), ?_⟩
    rw [neg_smul, ← hzy]; abel
  by_cases hec : e' = c0
  · subst hec
    apply hz
    rw [← line_eq_of_mem hy']
    refine mem_line.mpr ⟨-(y'.1 - z.1), ?_⟩
    rw [neg_smul, ← hzy']; abel
  by_cases hde : d = e'
  · subst hde
    have : (y'.1 - y.1) • (u d : F × W) = (y'.1 - y.1) • u c0 := by
      rw [← hyy]
      have : y' - y = (y' - z) - (y - z) := by abel
      rw [this, hzy, hzy', ← sub_smul]
      congr 1; ring
    exact hdc ((par_eq this).2 hγ)
  by_cases hzy1 : y'.1 = z.1
  · have : y' = z := by
      rw [hzy1, sub_self, zero_smul, sub_eq_zero] at hzy'
      exact hzy'
    exact hz (this ▸ hy')
  have e1 := snd_eq_of_sub hzy
  have e2 := snd_eq_of_sub hzy'
  have e3 := snd_eq_of_sub hyy
  -- colours `s₁ = z.1`, `s₂ = y'.1`, `s₃ = y.1`; points `e'`, `c0`, `d`
  refine hC he hc0 hd hec (Ne.symm hde) (Ne.symm hdc) hzS hy'S hyS (Ne.symm hzy1) ?_
  have : (y.1 - y'.1) • c0 = -((y'.1 - y.1) • c0) := by rw [← neg_smul, neg_sub]
  have hd' : (z.1 - y.1) • d = -((y.1 - z.1) • d) := by rw [← neg_smul, neg_sub]
  rw [hd', this, ← e2, ← e1, ← e3]; abel

end Geom

section PChain

/-! ### The positioned chain under an S-cap -/

variable {V P : Type*} [Fintype V] [DecidableEq V] [DecidableEq P]
variable (D : PData F W V P) {C : Finset W}

/-- Active colours of a positioned core. -/
def actCol : Set F := Set.range fun i => D.col (D.σ i)

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype V]
    [Fintype W] in
theorem fst_mem_actCol {v : V} (h : ∃ i, D.σ i = D.pos v) : (D.base v).1 ∈ actCol D := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rw [D.base_fst]; exact congrArg D.col hi⟩

variable (hC : IsSCap (actCol D) (C : Set W))
include hC

theorem pblockHyp_s : BlockHyp2 (PB D C) (pblocks D C) where
  edge := by
    intro v v' h
    obtain ⟨hv, hv'⟩ := PB_adj_pos D h
    obtain ⟨-, ⟨c, hc, hdir⟩, -⟩ := h
    refine ⟨pblock D (D.base v) c, pblock_mem D hc _, ?_, ?_⟩
    · exact (mem_pblock D).mpr ⟨self_mem_line _ _, hv⟩
    · exact (mem_pblock D).mpr ⟨mem_line_of_sub hdir, hv'⟩
  tri := by
    intro a b x hab hbx hax
    have pa := (PB_adj_pos D hab).1
    have pb := (PB_adj_pos D hab).2
    have px := (PB_adj_pos D hbx).2
    obtain ⟨hne, ⟨c1, hc1, h1⟩, -⟩ := hab
    obtain ⟨-, ⟨c2, hc2, h2⟩, -⟩ := hbx
    obtain ⟨-, ⟨c3, hc3, h3⟩, -⟩ := hax
    obtain ⟨d, hd, p, ha, hb, hx⟩ := tri_geom_s hC hc1 hc2 hc3 hne (fst_mem_actCol D pa)
      (fst_mem_actCol D pb) (fst_mem_actCol D px) h1 h2 h3
    refine ⟨pblock D p d, pblock_mem D hd p, ?_, ?_, ?_⟩
    · exact (mem_pblock D).mpr ⟨ha, pa⟩
    · exact (mem_pblock D).mpr ⟨hb, pb⟩
    · exact (mem_pblock D).mpr ⟨hx, px⟩
  two := by
    intro ℓ hℓ z hz y hy y' hy' y'' hy'' h1 h2 h3
    obtain ⟨⟨c0, w0⟩, hp, rfl⟩ := Finset.mem_image.mp hℓ
    have hc0 : c0 ∈ C := (Finset.mem_product.mp hp).1
    rw [mem_pblock] at hy hy' hy''
    have pz := (PB_adj_pos D h1).1
    have hzl : D.base z ∉ line ((0 : F), w0) c0 := fun hzl =>
      hz ((mem_pblock D).mpr ⟨hzl, pz⟩)
    obtain ⟨-, ⟨d1, hd1, e1⟩, -⟩ := h1
    obtain ⟨-, ⟨d2, hd2, e2⟩, -⟩ := h2
    obtain ⟨-, ⟨d3, hd3, e3⟩, -⟩ := h3
    have b12 := one_geom_s hC hc0 hzl hy.1 hy'.1 (fst_mem_actCol D pz) (fst_mem_actCol D hy.2)
      (fst_mem_actCol D hy'.2) hd1 hd2 e1 e2
    have b13 := one_geom_s hC hc0 hzl hy.1 hy''.1 (fst_mem_actCol D pz) (fst_mem_actCol D hy.2)
      (fst_mem_actCol D hy''.2) hd1 hd3 e1 e3
    exact D.fib y y' y'' b12 b13
  nonadj := by
    intro ℓ hℓ z hz y hy y' hy' h1 h2 hyy
    obtain ⟨⟨c0, w0⟩, hp, rfl⟩ := Finset.mem_image.mp hℓ
    have hc0 : c0 ∈ C := (Finset.mem_product.mp hp).1
    rw [mem_pblock] at hy hy'
    have pz := (PB_adj_pos D h1).1
    have hzl : D.base z ∉ line ((0 : F), w0) c0 := fun hzl =>
      hz ((mem_pblock D).mpr ⟨hzl, pz⟩)
    obtain ⟨-, ⟨d1, hd1, e1⟩, -⟩ := h1
    obtain ⟨-, ⟨d2, hd2, e2⟩, -⟩ := h2
    exact hyy.1 (one_geom_s hC hc0 hzl hy.1 hy'.1 (fst_mem_actCol D pz) (fst_mem_actCol D hy.2)
      (fst_mem_actCol D hy'.2) hd1 hd2 e1 e2)

/-- **`I(B) ≤ 8 · #blocks`** under an S-cap. -/
theorem pI_le_s {T : Finset (Finset V)} (hT : IsPack T) :
    ∑ Q ∈ T, w (PB D C) Q ≤ 8 * (pblocks D C).card := by
  refine global_bound2 (pblockHyp_s D hC) 8 ?_ hT
  intro ℓ hℓ T' hT'sub hT'
  obtain ⟨⟨c0, w0⟩, -, rfl⟩ := Finset.mem_image.mp hℓ
  have hinj : Set.InjOn D.pos (pblock D ((0 : F), w0) c0 : Set V) := by
    intro v hv v' hv' h
    rw [Finset.mem_coe, mem_pblock] at hv hv'
    apply D.inj v v' _ h
    apply fst_injOn_line _ _ hv.1 hv'.1
    rw [D.base_fst, D.base_fst, h]
  have := block_local (B := PB D C) D.pos D.σ hinj
    (fun v _ v' _ h => by
      obtain ⟨-, -, i, j, hi, hj, hij⟩ := h
      exact ⟨i, j, hi, hj, hij⟩) T' hT'sub hT'
  simpa using this

omit hC in
theorem pgap_ge_third_s [Fintype P] {U : Type*} [AddCommGroup U] [Module F U] [Fintype U]
  [DecidableEq U]
    (hC : IsSCap (actCol D) (C : Set W)) (hC0 : C.Nonempty) (S : SepFam F C U)
    (hsame : ∀ v v', D.base v = D.base v' → ∀ i j, D.σ i = D.pos v → D.σ j = D.pos v' →
      ¬ H12.graph.Adj i j) :
    ((C.card * Fintype.card W : ℕ) : ℝ) / 3 ≤ gap (hostGraph (ppalette D C S)) := by
  have h := gap_ge (phostHyp (S := S) hC0 hsame) (8 * (pblocks D C).card)
    (fun T hT => pI_le_s D hC hT) (presPack (D := D) (C := C))
  have hv := pvalue (D := D) (C := C)
  have hb : ((pblocks D C).card : ℝ) ≤ C.card * Fintype.card W := by
    exact_mod_cast card_pblocks_le D
  push_cast at h ⊢
  linarith


end PChain

section Single

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

omit [DecidableEq F] [DecidableEq U] [Fintype F] [Fintype U] in
theorem isSCap_capPow {S : Set F} {A : Finset U} (hA : IsSCap S (A : Set U)) (j : ℕ) :
    IsSCap S (capPow A j : Set (Fin j → U)) := by
  rw [coe_capPow]; exact hA.pi

omit [DecidableEq F] [Fintype F] in
theorem actCol_single {W : Type} [AddCommGroup W] [Module F W] (σ : Fin 6 ↪ F) :
    actCol (single (W := W) σ) = Set.range σ := rfl

omit [DecidableEq F] [DecidableEq U] in
/-- **TP-cond for S-caps** (ledger §17): the exponent `1 + log |A| / log |U|` for every S-cap `A`,
`S` the
active colours `range σ`. -/
theorem tp_single_s (σ : Fin 6 ↪ F) {A : Finset U} (hA : IsSCap (Set.range σ) (A : Set U)) (hA0 :
  A.Nonempty) {e : U}
    (he : e ≠ 0) (hM : 2 ≤ Fintype.card U) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      3 * (Fintype.card F + 1) ^ 4 * Fintype.card U * Fintype.card U ≤ n →
      ∃ (V' : Type) (_ : Fintype V') (_ : DecidableEq V') (G' : SimpleGraph V'),
        Fintype.card V' ≤ n ∧ IsSplit G' ∧
        c * (n : ℝ) ^ (1 + Real.log A.card / Real.log (Fintype.card U)) ≤ gap G' := by
  classical
  set M := Fintype.card U
  have hcapne : ∀ j, (capPow A j).Nonempty := fun j => by
    obtain ⟨a0, ha0⟩ := hA0
    exact ⟨fun _ => a0, by simp [capPow, ha0]⟩
  refine exponent_of_family hM hA0.card_pos (by positivity) (SV F U)
    (fun j => hostGraph (ppalette (single (W := Fin j → U) σ) (capPow A j) (prodSep A he j)))
    (fun j => ?_) (fun j => isSplit_hostGraph _) (fun j => ?_)
  · exact card_SV_le j
  · have h := pgap_ge_third_s (single (W := Fin j → U) σ) (isSCap_capPow hA j) (hcapne j)
      (prodSep A he j) (single_same σ)
    rw [card_capPow] at h
    have hW : Fintype.card (Fin j → U) = M ^ j := by simp [M]
    rw [hW] at h
    push_cast at h
    exact h


end Single

end GapExtremal
