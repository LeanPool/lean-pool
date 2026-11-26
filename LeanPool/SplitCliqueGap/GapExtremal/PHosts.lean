/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.PSource
public import LeanPool.SplitCliqueGap.GapExtremal.Hosts
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Abel

/-!
# Hosts on a positioned core (ledger §16.1, §16.3)

Exterior directions are separated by linear maps `sep r : F × W →ₗ U` (`sep r r = 0`, `sep r (u c)
≠ 0`), not
necessarily hyperplanes (no SEP). Hosts:

* `inl (r, β, λ, s)`: base fibre `sep r = β`, positions in `s`; marked pairs with exterior
difference;
* `inr (r, s)`: positions in `s` (a non-adjacent label pair); marked pairs with selected or zero
difference
  (twins).
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]
variable {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
variable {U : Type*} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

variable (F) in
/-- A separating family for the exterior directions of `C`. -/
structure SepFam (C : Finset W) (U : Type*) [AddCommGroup U] [Module F U] where
  /-- The linear functional separating the specified exterior direction from core directions. -/
  sep : F × W → (F × W) →ₗ[F] U
  sep_self : ∀ r, Ext C r → sep r r = 0
  sep_u : ∀ r, Ext C r → ∀ c ∈ C, sep r (u c) ≠ 0

/-- Host indices. -/
abbrev PHostIdx (F W P U : Type*) := ((F × W) × U × F × Sym2 P) ⊕ ((F × W) × Sym2 P)

instance instDecEqPHostIdx : DecidableEq (PHostIdx F W P U) :=
  @instDecidableEqSum _ _ (fun a b => instDecidableEqProd a b) (fun a b => instDecidableEqProd a b)

instance instDecEqSumPHostIdx : DecidableEq (V ⊕ PHostIdx F W P U) :=
  @instDecidableEqSum _ _ inferInstance instDecEqPHostIdx

variable (D : PData F W V P) (C : Finset W) (S : SepFam F C U)

/-- Position pairs carrying no `H12` edge. -/
def GoodP (s : Sym2 P) : Prop := ∀ i j : Fin 6, s = s(D.σ i, D.σ j) → ¬ H12.graph.Adj i j

open Classical in
/-- The palettes. -/
noncomputable def ppalette : PHostIdx F W P U → Finset V
  | .inl ⟨r, β, _, s⟩ =>
      if Ext C r then univ.filter (fun v => S.sep r (D.base v) = β ∧ D.pos v ∈ s) else ∅
  | .inr ⟨_, s⟩ => if GoodP D s then univ.filter (fun v => D.pos v ∈ s) else ∅

/-- Selected (or zero) base difference. -/
def PSel (v v' : V) : Prop :=
  ∃ c ∈ C, D.base v' - D.base v = ((D.base v').1 - (D.base v).1) • u c

open Classical in
/-- The assignment. -/
noncomputable def passign (v v' : V) : PHostIdx F W P U :=
  if PSel D C v v' then .inr (rep (D.base v' - D.base v), s(D.pos v, D.pos v'))
  else .inl (rep (D.base v' - D.base v), S.sep (rep (D.base v' - D.base v)) (D.base v),
    lab (rep (D.base v' - D.base v)) (D.base v + D.base v'), s(D.pos v, D.pos v'))

variable {D C S}

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype P]
    [Fintype V] [Fintype W] in
theorem psel_symm {v v' : V} : PSel D C v v' ↔ PSel D C v' v := by
  constructor <;> rintro ⟨c, hc, h⟩ <;> refine ⟨c, hc, ?_⟩ <;>
    · rw [← neg_sub, h, ← neg_smul, neg_sub]

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype P]
    [Fintype V] [Fintype W] in
theorem psel_of_base_eq (hC0 : C.Nonempty) {v v' : V} (h : D.base v = D.base v') : PSel D C v v'
  := by
  obtain ⟨c, hc⟩ := hC0
  exact ⟨c, hc, by rw [h, sub_self, sub_self, zero_smul]⟩

omit [DecidableEq P] [DecidableEq V] [Fintype P] [Fintype V] in
theorem ext_of_not_psel {v v' : V} (hb : D.base v ≠ D.base v') (h : ¬ PSel D C v v') :
    Ext C (rep (D.base v' - D.base v)) := by
  have hd : D.base v' - D.base v ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  refine ⟨(rep_spec hd).1, ?_⟩
  rintro ⟨c, hc, t, ht⟩
  obtain ⟨a, -, ha⟩ := eq_smul_rep hd
  apply h
  refine ⟨c, hc, ?_⟩
  have e : D.base v' - D.base v = (a * t) • u c := by rw [ha, ht, smul_smul]
  have e1 : (D.base v').1 - (D.base v).1 = a * t := by simpa [u] using congrArg Prod.fst e
  rw [e1, ← e]

omit [DecidableEq P] [DecidableEq U] [DecidableEq V] [Fintype P] [Fintype U] [Fintype V] in
theorem sep_eq_of_ext {v v' : V} (hb : D.base v ≠ D.base v')
    (hext : Ext C (rep (D.base v' - D.base v))) :
    S.sep (rep (D.base v' - D.base v)) (D.base v') = S.sep (rep (D.base v' - D.base v)) (D.base v)
      := by
  obtain ⟨a, -, ha⟩ := eq_smul_rep (sub_ne_zero.mpr (Ne.symm hb))
  generalize rep (D.base v' - D.base v) = r at ha hext ⊢
  have hy : D.base v' = D.base v + a • r := by rw [← ha]; abel
  rw [hy, map_add, map_smul, S.sep_self r hext, smul_zero, add_zero]

omit [DecidableEq F] [DecidableEq U] [Fintype F] [Fintype U] in
theorem smul_ne_zero_of {t : F} {x : U} (ht : t ≠ 0) (hx : x ≠ 0) : t • x ≠ 0 := by
  intro h
  apply hx
  have := congrArg (fun y => t⁻¹ • y) h
  simpa [smul_smul, inv_mul_cancel₀ ht] using this

omit [DecidableEq V] [Fintype P] [Fintype U] in
/-- **Host hypotheses** on a positioned core. -/
theorem phostHyp (hC0 : C.Nonempty)
    (hsame : ∀ v v', D.base v = D.base v' → ∀ i j, D.σ i = D.pos v → D.σ j = D.pos v' →
      ¬ H12.graph.Adj i j) :
    HostHyp (PB D C) (ppalette D C S) (passign D C S) where
  indep := by
    rintro (⟨r, b, l, s⟩ | ⟨r, s⟩) z hz z' hz' hadj
    · simp only [ppalette] at hz hz'
      split_ifs at hz hz' with hr
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
        obtain ⟨hne, ⟨c, hc, hdir⟩, -⟩ := hadj
        have h0 : S.sep r (D.base z' - D.base z) = 0 := by rw [map_sub, hz.1, hz'.1, sub_self]
        rw [hdir, map_smul] at h0
        by_cases ht : (D.base z').1 - (D.base z).1 = 0
        · rw [ht, zero_smul, sub_eq_zero] at hdir
          exact hne hdir.symm
        · exact smul_ne_zero_of ht (S.sep_u r hr c hc) h0
      · simp at hz
    · simp only [ppalette] at hz hz'
      split_ifs at hz hz' with hs
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
        obtain ⟨-, -, i, j, hi, hj, hij⟩ := hadj
        have hne : D.pos z ≠ D.pos z' := by
          intro h
          exact hij.ne (D.σ.injective (by rw [hi, hj, h]))
        have : s = s(D.pos z, D.pos z') := (Sym2.mem_and_mem_iff hne).mp ⟨hz, hz'⟩
        exact hs i j (by rw [this, hi, hj]) hij
      · simp at hz
  cover := by
    intro v v' hvv hnadj
    by_cases hsel : PSel D C v v'
    · simp only [passign, ite_eq_left hsel, ppalette]
      have hgood : GoodP D s(D.pos v, D.pos v') := by
        intro i j hs hij
        rcases Sym2.eq_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · by_cases hb : D.base v = D.base v'
          · exact hsame v v' hb i j h1.symm h2.symm hij
          · exact hnadj ⟨hb, hsel, i, j, h1.symm, h2.symm, hij⟩
        · by_cases hb : D.base v = D.base v'
          · exact hsame v v' hb j i h1.symm h2.symm hij.symm
          · exact hnadj ⟨hb, hsel, j, i, h1.symm, h2.symm, hij.symm⟩
      rw [ite_eq_left hgood]
      simp
    · have hb : D.base v ≠ D.base v' := fun h => hsel (psel_of_base_eq hC0 h)
      have hext := ext_of_not_psel hb hsel
      simp only [passign, ite_eq_right hsel, ppalette, ite_eq_left hext, Finset.mem_filter,
        Finset.mem_univ,
        true_and]
      constructor <;> simp [sep_eq_of_ext (S := S) hb hext]
  symm := by
    intro v v'
    by_cases hvv : v = v'
    · rw [hvv]
    by_cases hsel : PSel D C v v'
    · have hsel' : PSel D C v' v := psel_symm.mp hsel
      simp only [passign, ite_eq_left hsel, ite_eq_left hsel']
      rw [← neg_sub (D.base v) (D.base v'), rep_neg, Sym2.eq_swap]
    · have hsel' : ¬ PSel D C v' v := fun h => hsel (psel_symm.mpr h)
      simp only [passign, ite_eq_right hsel, ite_eq_right hsel']
      have hb : D.base v ≠ D.base v' := fun h => hsel (psel_of_base_eq hC0 h)
      have hext := ext_of_not_psel hb hsel
      have hsv := sep_eq_of_ext (S := S) hb hext
      rw [show D.base v - D.base v' = -(D.base v' - D.base v) by abel, rep_neg,
        add_comm (D.base v) (D.base v'), hsv, Sym2.eq_swap]
  inj := by
    intro v v' v'' hvv hn hvv' hn' heq
    by_cases hs : PSel D C v v' <;> by_cases hs' : PSel D C v v''
    · simp only [passign, ite_eq_left hs, ite_eq_left hs', Sum.inr.injEq, Prod.mk.injEq] at heq
      obtain ⟨hr, hsym⟩ := heq
      have hpos : D.pos v' = D.pos v'' := Sym2.congr_right.mp hsym
      apply D.inj v' v'' _ hpos
      -- equal bases
      by_cases h0 : D.base v' - D.base v = 0
      · have h0' : D.base v'' - D.base v = 0 := by
          by_contra hne
          have := (rep_spec hne).1
          rw [← hr, h0] at this
          apply this
          simp [rep, repOf]
        rw [sub_eq_zero] at h0 h0'
        rw [h0, h0']
      · have h0' : D.base v'' - D.base v ≠ 0 := by
          intro hz
          have := (rep_spec h0).1
          rw [hr, hz] at this
          apply this
          simp [rep, repOf]
        obtain ⟨a, -, ha⟩ := eq_smul_rep h0
        obtain ⟨a', -, ha'⟩ := eq_smul_rep h0'
        rw [hr] at ha
        have hcol : (D.base v').1 = (D.base v'').1 := by rw [D.base_fst, D.base_fst, hpos]
        have hfst : (rep (D.base v'' - D.base v)).1 ≠ 0 := by
          obtain ⟨c, -, hdir⟩ := hs'
          obtain ⟨-, s, hs0, hrs⟩ := rep_spec h0'
          rw [hrs]
          simp only [Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
          refine mul_ne_zero hs0 fun h1 => h0' ?_
          rw [hdir, h1, zero_smul]
        generalize rep (D.base v'' - D.base v) = r at ha ha' hfst
        have e1 : (D.base v').1 - (D.base v).1 = a * r.1 := by simpa using congrArg Prod.fst ha
        have e2 : (D.base v'').1 - (D.base v).1 = a' * r.1 := by simpa using congrArg Prod.fst ha'
        have haa : a = a' := mul_right_cancel₀ hfst (by rw [← e1, ← e2, hcol])
        have : D.base v' - D.base v = D.base v'' - D.base v := by rw [ha, ha', haa]
        exact sub_left_inj.mp this
    · simp [passign, ite_eq_left hs, ite_eq_right hs'] at heq
    · simp [passign, ite_eq_right hs, ite_eq_left hs'] at heq
    · simp only [passign, ite_eq_right hs, ite_eq_right hs', Sum.inl.injEq, Prod.mk.injEq] at heq
      obtain ⟨hr, -, hl, hsym⟩ := heq
      have hpos : D.pos v' = D.pos v'' := Sym2.congr_right.mp hsym
      apply D.inj v' v'' _ hpos
      have hb : D.base v ≠ D.base v' := fun h => hs (psel_of_base_eq hC0 h)
      have hb' : D.base v ≠ D.base v'' := fun h => hs' (psel_of_base_eq hC0 h)
      obtain ⟨a, -, ha⟩ := eq_smul_rep (sub_ne_zero.mpr (Ne.symm hb))
      obtain ⟨a', -, ha'⟩ := eq_smul_rep (sub_ne_zero.mpr (Ne.symm hb'))
      have hr0 : rep (D.base v'' - D.base v) ≠ 0 := (rep_spec (sub_ne_zero.mpr (Ne.symm hb'))).1
      rw [hr] at ha hl
      generalize rep (D.base v'' - D.base v) = r at ha ha' hl hr0
      have hy : D.base v' = D.base v + a • r := by rw [← ha]; abel
      have hy' : D.base v'' = D.base v + a' • r := by rw [← ha']; abel
      rw [hy, hy'] at hl
      simp only [map_add, map_smul, smul_eq_mul] at hl
      have haa : a = a' := mul_right_cancel₀ (lab_spec hr0) (by linear_combination hl)
      rw [hy, hy', haa]

end GapExtremal
