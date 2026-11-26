/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Source
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Abel

/-!
# Concrete hosts (ledger §8, L2.2, L8.1–L8.2)

Hosts are indexed by `(F × W) × F × F` (exterior directions: representative, fibre value, label)
and by
`(F × W) × Sym2 F` (selected directions: representative, colour pair).

* `rep d`: a canonical generator of the line `F ∙ d`; `rep (-d) = rep d`.
* `sepFun r`: for an exterior direction `r`, a functional vanishing on `r` and on no `u c` (L2.2,
from SEP).
* `lab r`: a functional not vanishing on `r` (labels, so that no division by 2 is needed).
* `hostHyp`: the hypotheses of the bridge hold.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]

/-! ### Canonical representatives of directions -/

open Classical in
/-- A chosen nonzero vector of a submodule (or `0`). -/
noncomputable def repOf (S : Submodule F (F × W)) : F × W :=
  if h : ∃ v ∈ S, v ≠ 0 then h.choose else 0

/-- Canonical generator of the line spanned by `d`. -/
noncomputable def rep (d : F × W) : F × W := repOf (F ∙ d)

theorem rep_spec {d : F × W} (hd : d ≠ 0) : rep d ≠ 0 ∧ ∃ s : F, s ≠ 0 ∧ rep d = s • d := by
  classical
  have hex : ∃ v ∈ (F ∙ d), v ≠ 0 := ⟨d, Submodule.mem_span_singleton_self d, hd⟩
  have hr : rep d = hex.choose := by unfold rep repOf; rw [dite_eq_left hex]
  obtain ⟨hmem, hne⟩ := hex.choose_spec
  rw [← hr] at hmem hne
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨hne, s, fun h0 => hne (by rw [← hs, h0, zero_smul]), hs.symm⟩

theorem rep_smul {t : F} (ht : t ≠ 0) (d : F × W) : rep (t • d) = rep d := by
  unfold rep
  rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 t ht)]

theorem rep_neg (d : F × W) : rep (-d) = rep d := by
  rw [← neg_one_smul F d, rep_smul (neg_ne_zero.mpr one_ne_zero)]

/-- `d = (rep d) / s` for some nonzero `s`. -/
theorem eq_smul_rep {d : F × W} (hd : d ≠ 0) : ∃ a : F, a ≠ 0 ∧ d = a • rep d := by
  obtain ⟨-, s, hs, h⟩ := rep_spec hd
  exact ⟨s⁻¹, inv_ne_zero hs, by rw [h, smul_smul, inv_mul_cancel₀ hs, one_smul]⟩

/-! ### Selected and exterior directions -/

variable (C : Finset W) (σ : Fin 6 ↪ F)

/-- A direction parallel to some `u c`, `c ∈ C`. -/
def Par (d : F × W) : Prop := ∃ c ∈ C, ∃ t : F, d = t • u c

/-- An exterior direction. -/
def Ext (d : F × W) : Prop := d ≠ 0 ∧ ¬ Par C d

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
theorem exists_sepFun (hS : IsSep F (C : Set W)) {r : F × W} (hr : Ext C r) :
    ∃ L : (F × W) →ₗ[F] F, L r = 0 ∧ ∀ c ∈ C, L (u c) ≠ 0 := by
  by_cases h1 : r.1 = 0
  · refine ⟨LinearMap.fst F F W, by simpa using h1, fun c _ => by simp [u]⟩
  · set z := r.1⁻¹ • r.2
    have hz : z ∉ (C : Set W) := by
      intro hz
      apply hr.2
      refine ⟨z, hz, r.1, ?_⟩
      ext
      · simp [u]
      · simp [u, z, smul_smul, mul_inv_cancel₀ h1]
    obtain ⟨l, b, hl, hlC⟩ := hS z hz
    refine ⟨l.comp (LinearMap.snd F F W) - b • LinearMap.fst F F W, ?_, ?_⟩
    · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.snd_apply,
        LinearMap.smul_apply, LinearMap.fst_apply, smul_eq_mul]
      have : l r.2 = r.1 * l z := by simp [z, ← mul_assoc, mul_inv_cancel₀ h1]
      rw [this, hl]; ring
    · intro c hc
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.snd_apply,
        LinearMap.smul_apply, LinearMap.fst_apply, smul_eq_mul, u, mul_one]
      exact sub_ne_zero.mpr (hlC c (by exact_mod_cast hc))

open Classical in
/-- The separating functional of an exterior direction (L2.2). -/
noncomputable def sepFun (hS : IsSep F (C : Set W)) (r : F × W) : (F × W) →ₗ[F] F :=
  if h : Ext C r then (exists_sepFun C hS h).choose else 0

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
theorem sepFun_spec (hS : IsSep F (C : Set W)) {r : F × W} (hr : Ext C r) :
    sepFun C hS r r = 0 ∧ ∀ c ∈ C, sepFun C hS r (u c) ≠ 0 := by
  classical
  unfold sepFun
  rw [dite_eq_left hr]
  exact (exists_sepFun C hS hr).choose_spec

open Classical in
/-- A label functional, nonzero on `r ≠ 0`. -/
noncomputable def lab (r : F × W) : (F × W) →ₗ[F] F :=
  if h : r ≠ 0 then (Module.Projective.exists_dual_ne_zero F h).choose else 0

omit [Fintype F] [Fintype W] in
theorem lab_spec {r : F × W} (hr : r ≠ 0) : lab r r ≠ 0 := by
  classical
  unfold lab
  rw [dite_eq_left hr]
  exact (Module.Projective.exists_dual_ne_zero F hr).choose_spec

/-! ### Hosts, palettes and the assignment -/

/-- Host indices. -/
abbrev HostIdx (F W : Type*) := ((F × W) × F × F) ⊕ ((F × W) × Sym2 F)

/-- Colour pairs that are not edges of `H12`. -/
def GoodS (s : Sym2 F) : Prop := ∀ i j : Fin 6, s = s(σ i, σ j) → ¬ H12.graph.Adj i j

open Classical in
/-- The palettes. -/
noncomputable def palette (hS : IsSep F (C : Set W)) : HostIdx F W → Finset (F × W)
  | .inl ⟨r, b, _⟩ => if Ext C r then univ.filter (fun z => sepFun C hS r z = b) else ∅
  | .inr ⟨_, s⟩ => if GoodS σ s then univ.filter (fun z => z.1 ∈ s) else ∅

/-- A pair with a selected direction. -/
def Sel (x y : F × W) : Prop := ∃ c ∈ C, y - x = (y.1 - x.1) • u c

open Classical in
/-- The assignment of marked pairs to hosts. -/
noncomputable def assign (hS : IsSep F (C : Set W)) (x y : F × W) : HostIdx F W :=
  if Sel C x y then .inr (rep (y - x), s(x.1, y.1))
  else .inl (rep (y - x), sepFun C hS (rep (y - x)) x, lab (rep (y - x)) (x + y))

variable {C σ}

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
theorem sel_symm {x y : F × W} : Sel C x y ↔ Sel C y x := by
  constructor <;> rintro ⟨c, hc, h⟩ <;> refine ⟨c, hc, ?_⟩ <;>
    · rw [← neg_sub, h, ← neg_smul, neg_sub]

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
theorem sel_fst_ne {x y : F × W} (hxy : x ≠ y) (h : Sel C x y) : x.1 ≠ y.1 := by
  obtain ⟨c, -, h⟩ := h
  intro h1
  rw [h1, sub_self, zero_smul, sub_eq_zero] at h
  exact hxy h.symm

theorem ext_of_not_sel {x y : F × W} (hxy : x ≠ y) (h : ¬ Sel C x y) : Ext C (rep (y - x)) := by
  have hd : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  refine ⟨(rep_spec hd).1, ?_⟩
  rintro ⟨c, hc, t, ht⟩
  obtain ⟨a, -, ha⟩ := eq_smul_rep hd
  apply h
  refine ⟨c, hc, ?_⟩
  have e : y - x = (a * t) • u c := by rw [ha, ht, smul_smul]
  have e1 : y.1 - x.1 = a * t := by simpa [u] using congrArg Prod.fst e
  rw [e1, ← e]

theorem rep_fst_ne_of_sel {x y : F × W} (hxy : x ≠ y) (h : Sel C x y) : (rep (y - x)).1 ≠ 0 := by
  have hd : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  obtain ⟨-, s, hs, hr⟩ := rep_spec hd
  rw [hr]
  simp only [Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
  exact mul_ne_zero hs (sub_ne_zero.mpr (sel_fst_ne hxy h).symm)

theorem sepFun_eq_of_ext (hS : IsSep F (C : Set W)) {x y : F × W} (hxy : x ≠ y)
    (hext : Ext C (rep (y - x))) : sepFun C hS (rep (y - x)) y = sepFun C hS (rep (y - x)) x := by
  obtain ⟨a, -, ha⟩ := eq_smul_rep (sub_ne_zero.mpr hxy.symm)
  generalize rep (y - x) = r at ha hext ⊢
  have hy : y = x + a • r := by rw [← ha]; abel
  rw [hy, map_add, map_smul, (sepFun_spec C hS hext).1, smul_zero, add_zero]

variable (hS : IsSep F (C : Set W))

theorem hostHyp : HostHyp (Bgr C σ) (palette C σ hS) (assign C hS) where
  indep := by
    rintro (⟨r, b, l⟩ | ⟨r, s⟩) z hz z' hz' hadj
    · simp only [palette] at hz hz'
      split_ifs at hz hz' with hr
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
        obtain ⟨c, hc, hdir⟩ := hadj.2.1
        have h0 : sepFun C hS r (z' - z) = 0 := by rw [map_sub, hz, hz', sub_self]
        rw [hdir, map_smul, smul_eq_mul] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · rw [h, zero_smul, sub_eq_zero] at hdir
          exact hadj.1 hdir.symm
        · exact (sepFun_spec C hS hr).2 c hc h
      · simp at hz
    · simp only [palette] at hz hz'
      split_ifs at hz hz' with hs
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
        obtain ⟨i, j, hi, hj, hij⟩ := hadj.2.2
        have hne := Bgr_fst_ne hadj
        have : s = s(z.1, z'.1) := (Sym2.mem_and_mem_iff hne).mp ⟨hz, hz'⟩
        exact hs i j (by rw [this, hi, hj]) hij
      · simp at hz
  cover := by
    intro x y hxy hnadj
    by_cases hsel : Sel C x y
    · simp only [assign, ite_eq_left hsel, palette]
      have hgood : GoodS σ s(x.1, y.1) := by
        intro i j hs hij
        apply hnadj
        obtain ⟨c, hc, hdir⟩ := hsel
        refine ⟨hxy, ⟨c, hc, hdir⟩, ?_⟩
        rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨i, j, h1.symm, h2.symm, hij⟩
        · exact ⟨j, i, h1.symm, h2.symm, hij.symm⟩
      rw [ite_eq_left hgood]
      simp
    · have hext := ext_of_not_sel hxy hsel
      simp only [assign, ite_eq_right hsel, palette, ite_eq_left hext, Finset.mem_filter,
        Finset.mem_univ,
        true_and]
      exact sepFun_eq_of_ext hS hxy hext
  symm := by
    intro x y
    by_cases hxy : x = y
    · rw [hxy]
    by_cases hsel : Sel C x y
    · have hsel' : Sel C y x := sel_symm.mp hsel
      simp only [assign, ite_eq_left hsel, ite_eq_left hsel']
      rw [← neg_sub x y, rep_neg, Sym2.eq_swap]
    · have hsel' : ¬ Sel C y x := fun h => hsel (sel_symm.mpr h)
      simp only [assign, ite_eq_right hsel, ite_eq_right hsel']
      have hext := ext_of_not_sel hxy hsel
      have hxyv := sepFun_eq_of_ext hS hxy hext
      rw [show x - y = -(y - x) by abel, rep_neg, add_comm x y, hxyv]
  inj := by
    intro x y y' hxy hn hxy' hn' heq
    by_cases hs : Sel C x y <;> by_cases hs' : Sel C x y'
    · simp only [assign, ite_eq_left hs, ite_eq_left hs', Sum.inr.injEq, Prod.mk.injEq] at heq
      obtain ⟨hr, hsym⟩ := heq
      have h1 : y.1 = y'.1 := by
        rcases Sym2.eq_iff.mp hsym with ⟨-, h⟩ | ⟨h, h'⟩
        · exact h
        · exact absurd h'.symm (sel_fst_ne hxy hs)
      obtain ⟨a, -, ha⟩ := eq_smul_rep (sub_ne_zero.mpr hxy.symm)
      obtain ⟨a', -, ha'⟩ := eq_smul_rep (sub_ne_zero.mpr hxy'.symm)
      have hfst := rep_fst_ne_of_sel hxy' hs'
      rw [hr] at ha
      generalize rep (y' - x) = r at ha ha' hfst
      have e1 : y.1 - x.1 = a * r.1 := by simpa using congrArg Prod.fst ha
      have e2 : y'.1 - x.1 = a' * r.1 := by simpa using congrArg Prod.fst ha'
      have haa : a = a' := mul_right_cancel₀ hfst (by rw [← e1, ← e2, h1])
      have : y - x = y' - x := by rw [ha, ha', haa]
      exact sub_left_inj.mp this
    · simp [assign, ite_eq_left hs, ite_eq_right hs'] at heq
    · simp [assign, ite_eq_right hs, ite_eq_left hs'] at heq
    · simp only [assign, ite_eq_right hs, ite_eq_right hs', Sum.inl.injEq, Prod.mk.injEq] at heq
      obtain ⟨hr, -, hl⟩ := heq
      obtain ⟨a, -, ha⟩ := eq_smul_rep (sub_ne_zero.mpr hxy.symm)
      obtain ⟨a', -, ha'⟩ := eq_smul_rep (sub_ne_zero.mpr hxy'.symm)
      have hr0 : rep (y' - x) ≠ 0 := (rep_spec (sub_ne_zero.mpr hxy'.symm)).1
      rw [hr] at ha hl
      generalize rep (y' - x) = r at ha ha' hl hr0
      have hy : y = x + a • r := by rw [← ha]; abel
      have hy' : y' = x + a' • r := by rw [← ha']; abel
      rw [hy, hy'] at hl
      simp only [map_add, map_smul, smul_eq_mul] at hl
      have haa : a = a' := mul_right_cancel₀ (lab_spec hr0) (by linear_combination hl)
      rw [hy, hy', haa]

end GapExtremal
