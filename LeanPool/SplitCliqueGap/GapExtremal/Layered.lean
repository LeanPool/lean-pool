/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.PMain
public import LeanPool.SplitCliqueGap.GapExtremal.Exponent
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Product caps need no SEP, and the two-layer core over `F₅` (ledger §16.1, §16.3)

* `prodSep`: for `C = A^j` (any cap `A ⊆ U`, no separability) a separating family with values in `U`
  (fix the coordinates of one block where `z ∉ A`).
* `layered`: the positioned core `V = (F₅ × W) ⊕ W`; the twin `inr w` doubles the colour-0 point
`(0, w)`;
  labels `0, 1, 2, 3, 4, 5` sit at `0, 1, twin, 2, 3, 4`.
-/

@[expose] public section

namespace GapExtremal

open Finset

/-! ### Separating maps for product caps -/

section ProdSep

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

omit [DecidableEq F] [DecidableEq U] [Fintype F] [Fintype U] in
theorem ext_bad {A : Finset U} {j : ℕ} {r : F × (Fin j → U)} (hr : Ext (capPow A j) r)
    (h1 : r.1 ≠ 0) : ∃ i, (r.1⁻¹ • r.2) i ∉ A := by
  by_contra h
  push Not at h
  apply hr.2
  refine ⟨r.1⁻¹ • r.2, ?_, r.1, ?_⟩
  · simp only [capPow, Fintype.mem_piFinset]; exact h
  · ext
    · simp [u]
    · simp [u, smul_smul, mul_inv_cancel₀ h1]

open Classical in
/-- The separating map of a direction for a product cap. -/
noncomputable def prodSepMap (A : Finset U) (e : U) (j : ℕ) (r : F × (Fin j → U)) :
    (F × (Fin j → U)) →ₗ[F] U :=
  if h : r.1 ≠ 0 ∧ ∃ i, (r.1⁻¹ • r.2) i ∉ A then
    (LinearMap.proj h.2.choose).comp (LinearMap.snd F F (Fin j → U)) -
      (LinearMap.fst F F (Fin j → U)).smulRight ((r.1⁻¹ • r.2) h.2.choose)
  else (LinearMap.fst F F (Fin j → U)).smulRight e

/-- **L16.1.** Product caps have a separating family (no SEP needed). -/
noncomputable def prodSep (A : Finset U) {e : U} (he : e ≠ 0) (j : ℕ) : SepFam F (capPow A j) U
  where
  sep := prodSepMap A e j
  sep_self := by
    intro r hr
    unfold prodSepMap
    split_ifs with h
    · simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.proj_apply,
        LinearMap.smulRight_apply, LinearMap.fst_apply, Pi.smul_apply, smul_smul,
        mul_inv_cancel₀ h.1, one_smul, sub_self]
    · have h1 : r.1 = 0 := by
        by_contra h1
        exact h ⟨h1, ext_bad hr h1⟩
      simp [h1]
  sep_u := by
    intro r hr c hc
    unfold prodSepMap
    split_ifs with h
    · have hci : c h.2.choose ∈ A := by
        simp only [capPow, Fintype.mem_piFinset] at hc; exact hc _
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.snd_apply,
        LinearMap.proj_apply,
        LinearMap.smulRight_apply, LinearMap.fst_apply, u, one_smul]
      intro h0
      rw [sub_eq_zero] at h0
      exact h.2.choose_spec (h0 ▸ hci)
    · simpa [u] using he

end ProdSep

/-! ### The two-layer core over `F₅` -/

section Layered

/-- The five-element field used in the layered construction. -/
abbrev F5 := ZMod 5

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Pin the additive group of `ZMod 5` to the ring structure (otherwise instance search may pick the
`IsSimpleAddGroup` route, which is not reducibly compatible with the module instances). -/
instance (priority := 10000) addCommGroupF5 : AddCommGroup (ZMod 5) := Ring.toAddCommGroup

/-- Label positions: `0 ↦ 0, 1 ↦ 1, 2 ↦ twin, 3 ↦ 2, 4 ↦ 3, 5 ↦ 4`. -/
def σL : Fin 6 ↪ Option F5 :=
  ⟨![some 0, some 1, none, some 2, some 3, some 4], by decide⟩

/-- The colour of a layer, with colour zero assigned to the outer layer. -/
def colL (o : Option F5) : F5 := o.getD 0

variable {W : Type} [AddCommGroup W] [Module F5 W] [Fintype W] [DecidableEq W]

/-- The two-layer positioned core. -/
def layered : PData F5 W ((F5 × W) ⊕ W) (Option F5) where
  base := Sum.elim id fun w => ((0 : F5), w)
  pos := Sum.elim (fun y => some y.1) fun _ => none
  col := colL
  σ := σL
  base_fst := by rintro (y | w) <;> rfl
  inj := by
    rintro (y | w) (y' | w') hb hp
    · simpa using hb
    · simp at hp
    · simp at hp
    · simp only [Sum.elim_inr, Prod.mk.injEq, true_and] at hb; rw [hb]
  fib := by
    rintro (y | w) (y' | w') (y'' | w'') h₁ h₂ <;>
      first
      | exact Or.inl (congrArg Sum.inl h₁)
      | exact Or.inl (congrArg Sum.inr (congrArg Prod.snd h₁))
      | exact Or.inr (Or.inl (congrArg Sum.inl h₂))
      | exact Or.inr (Or.inl (congrArg Sum.inr (congrArg Prod.snd h₂)))
      | exact Or.inr (Or.inr (congrArg Sum.inl (h₁.symm.trans h₂)))
      | exact Or.inr (Or.inr (congrArg Sum.inr (congrArg Prod.snd (h₁.symm.trans h₂))))
  rl y i := if σL i = none then Sum.inr y.2 else Sum.inl y
  rl_base := by
    intro y i hy
    split_ifs with h
    · simp only [Sum.elim_inr]
      rw [h] at hy
      ext
      · exact hy.symm
      · rfl
    · rfl
  rl_pos := by
    intro y i hy
    split_ifs with h
    · simp [h]
    · simp only [Sum.elim_inl]
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp h
      rw [ha] at hy ⊢
      simp only [colL, Option.getD_some] at hy
      rw [hy]
  colσ := by decide

omit [DecidableEq W] [Fintype W] in
theorem layered_same :
    ∀ v v' : (F5 × W) ⊕ W, (layered (W := W)).base v = (layered (W := W)).base v' →
      ∀ i j, σL i = (layered (W := W)).pos v → σL j = (layered (W := W)).pos v' →
        ¬ H12.graph.Adj i j := by
  have key : ∀ i j : Fin 6, σL i = σL j → ¬ H12.graph.Adj i j := by decide
  have key2 : ∀ i j : Fin 6, σL i = some 0 → σL j = none → ¬ H12.graph.Adj i j := by decide
  have key3 : ∀ i j : Fin 6, σL i = none → σL j = some 0 → ¬ H12.graph.Adj i j := by decide
  rintro (y | w) (y' | w') hb i j hi hj
  · simp only [layered, Sum.elim_inl, id] at hb hi hj
    exact key i j (by rw [hi, hj, hb])
  · simp only [layered, Sum.elim_inl, Sum.elim_inr, id] at hb hi hj
    exact key2 i j (by rw [hi, hb]) hj
  · simp only [layered, Sum.elim_inl, Sum.elim_inr, id] at hb hi hj
    exact key3 i j hi (by rw [hj, ← hb])
  · simp only [layered, Sum.elim_inr] at hi hj
    exact key i j (by rw [hi, hj])

end Layered

end GapExtremal
