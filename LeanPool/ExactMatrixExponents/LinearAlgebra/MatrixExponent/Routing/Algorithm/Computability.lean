/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector
public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Algorithm.Code
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Shift
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Formula
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.Control.Decor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Routing.GeometryControl
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.VectorSort
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transport.System

/-!
# Straight-line word programs with indexed loads

Data are single bits, bounded unsigned words, pairs, and dyadic
arrays. Pairs and arrays are immutable and can be shared by address.
A program is independent of its input. Tabulation writes a fresh
array in increasing index order, with the program for each index
included in the instruction count. A literal, including a static
index, occupies one word. Boolean gates have four-bit truth tables.

The rules give the denotation and charge of a program simultaneously.
The width bounds apply to arithmetic operands and literals. To address
storage one may take the maximum of this width and the binary length
of the input and the allocated words. There is no unit-cost primitive
for evaluating large tables, searching, or sorting.
-/

@[expose] public section

section
/- # Bounds for near-linear word programs -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Algorithm

theorem budget_mono (h w : ℕ) {c d : ℕ} (hc : c ≤ d) :
    2 ^ h * (100 + w) ^ c ≤ 2 ^ h * (100 + w) ^ d :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hc)

theorem budget_step (h w c : ℕ) :
    100 * (2 ^ h * (100 + w) ^ c) ≤ 2 ^ h * (100 + w) ^ (c + 1) := by
  rw [pow_succ, ← mul_assoc (2 ^ h), mul_comm 100]
  exact Nat.mul_le_mul_left _ (by omega)

theorem budget_base (h w c : ℕ) : 2 ^ h ≤ 2 ^ h * (100 + w) ^ c := by
  simpa using budget_mono h w (Nat.zero_le c)

theorem budget_width (h c : ℕ) :
    2 ^ h * (100 + (3 * h + 10)) ^ c ≤ 2 ^ h * (100 + h) ^ (2 * c) := by
  rw [pow_mul]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by ring_nf; omega) _)

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Algorithm
end

section
/- # Code tabulation and bounds on advice and working memory -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Algorithm
open Coloring

namespace Code
variable {w h : ℕ} {A D : Type}

theorem tabulate_eq (hh : h ≤ w) (f : B h → Code w A D) : tabulate hh f = tab hh f := by
  unfold tabulate
  apply congrArg (tab hh)
  funext i
  exact Vector.getElem_ofFn i.isLt

/-- The time allowance covers both the program words and the scratch
allocation, including the extra words of all tabulations. -/
theorem advice_scratch (c : Code w A D) : c.advice + c.scratch ≤ c.time := by
  change charge 8 1 c + charge 8 1 c ≤ charge 16 4 c
  rw [← two_mul]
  induction c <;> try {simp only [charge]; omega}
  case tab hh f ih =>
    simp only [charge, mul_add, Finset.mul_sum]
    apply Nat.add_le_add le_rfl
    apply Finset.sum_le_sum
    intro i _
    have := ih i
    omega

end Code

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Algorithm
end

/-
# Compiling local observations

The list of group elements and the table on their coincidences are
fixed before the height or the permutation is given.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Root
open Coloring

private theorem Local.table {G : Type} [Group G] {q : ℕ} {f : Root G → B q} (hf : Local f) :
    ∃ (t : ℕ) (g : B t → G) (b : (B t → B t → Bool) → B q),
      ∀ r, b (fun i j => r.see (g i) (g j)) = f r := by
  classical
  obtain ⟨E, hE⟩ := hf
  let e := encode ↥E
  let g := Function.extend e (fun i : ↥E => i.val) (fun _ => 1)
  have hg (x : G) (hx : x ∈ E) : g (e ⟨x, hx⟩) = x :=
    e.injective.extend_apply _ _ _
  let obs (r : Root G) i j := r.see (g i) (g j)
  have same (r s : Root G) (he : obs r = obs s) : f r = f s := by
    apply hE
    intro i hi j hj
    simpa only [obs, hg] using congrFun (congrFun he (e ⟨i, hi⟩)) (e ⟨j, hj⟩)
  let b z := if h : ∃ r, obs r = z then f h.choose else 0
  refine ⟨_, g, b, fun r => ?_⟩
  have ex : ∃ s, obs s = obs r := ⟨r, rfl⟩
  change b (obs r) = _
  simp only [b, dite_eq_left ex]
  exact same _ _ ex.choose_spec

theorem Local.compile {F : Type} [Field F] {m q : ℕ} {T : Routes F m}
    {V : Type*} {f : Root (controllers F T.embed) → V} (hf : Local f) (e : V ↪ B q) :
    ∃ c k₀ : ℕ, ∀ h ≥ k₀, ∃ v,
      Cheap F (h + 1) (h + 1) (Perm h) (.vec (h + 1) (.addr q)) v c ∧
      ∀ π : Equiv.Perm (B h), ∀ i, v π i = e (f (@Root.mk _ _ (B (h + 1)) (T.action h π) i)) := by
  obtain ⟨t, g, b, hb⟩ := (hf.map e).table
  obtain ⟨c, hc⟩ := T.controllers_net t g
  obtain ⟨k, hk⟩ := Cheap.equalityTable F t q
  refine ⟨max c 30 + 1, max (2 ^ t) k, fun h hh => ?_⟩
  obtain ⟨v, hv, he⟩ := hc h (by omega)
  have net := hv.comp (hk (h + 1) (h + 1) le_rfl (by omega) b)
  refine ⟨_, net, fun π i => ?_⟩
  let r := @Root.mk _ _ (B (h + 1)) (T.action h π) i
  refine Eq.trans ?_ (hb r)
  apply congrArg b
  funext j l
  rw [Bool.eq_iff_iff]
  simp only [see, decide_eq_true_eq, he]
  rfl

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Root
end

/-
# Compiling local functions of marked sites

The permutation determines the addresses. Compare them and gather the
marks there before applying the fixed local table.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Decor
open Coloring

private abbrev pattern (t : ℕ) := B t → B t → Bool

private abbrev frame (t q : ℕ) :=
  Format.pair (.addr (Fintype.card (pattern t))) (.vec t (.addr q))

private def observe {G : Type} [Group G] {t q : ℕ} (g : B t → G) (r : Decor G q) :
    (frame t q).obj :=
  (encode (pattern t) (fun i j => r.toRoot.see (g i) (g j)), fun i => r.mark (r.toRoot.label (g i)))

private theorem Local.table {G : Type} [Group G] {q l : ℕ} {V : Type*} {f : Decor G q → V}
    (hf : Local f) (enc : V ↪ B l) :
    ∃ (t : ℕ) (g : B t → G) (b : (frame t q).obj → B l),
      ∀ r, b (observe g r) = enc (f r) := by
  classical
  obtain ⟨E, hE⟩ := hf
  let e := encode ↥E
  let g := Function.extend e (fun i : ↥E => i.val) (fun _ => 1)
  have hg (x : G) (hx : x ∈ E) : g (e ⟨x, hx⟩) = x :=
    e.injective.extend_apply _ _ _
  have same (r s : Decor G q) (he : observe g r = observe g s) : f r = f s := by
    apply hE
    · intro i hi j hj
      have hp := (encode _).injective (congrArg Prod.fst he)
      simpa only [hg] using congrFun (congrFun hp (e ⟨i, hi⟩)) (e ⟨j, hj⟩)
    · intro i hi
      simpa only [observe, hg] using congrFun (congrArg Prod.snd he) (e ⟨i, hi⟩)
  let b z := if h : ∃ r, observe g r = z then enc (f h.choose) else 0
  refine ⟨_, g, b, fun r => ?_⟩
  have ex : ∃ s, observe g s = observe g r := ⟨r, rfl⟩
  simp only [b, dite_eq_left ex]
  exact congrArg enc (same _ _ ex.choose_spec)

theorem Local.compile {F : Type} [Field F] {m l q : ℕ} {T : Routes F m}
    {V : Type*} {f : Decor (controllers F T.embed) q → V} (hf : Local f) (e : V ↪ B l) :
    ∃ c k₀ : ℕ, ∀ h ≥ k₀, ∃ v,
      Cheap F (h + 1) (h + 1) (.pair (Perm h) (.vec (h + 1) (.addr q))) (.vec (h
        + 1) (.addr l)) v c ∧
      ∀ π : Equiv.Perm (B h), ∀ z i,
        v (π, z) i = e (f ⟨@Root.mk _ _ (B (h + 1)) (T.action h π) i, z⟩) := by
  obtain ⟨t, g, b, hb⟩ := hf.table e
  obtain ⟨c, hc⟩ := T.controllers_net t g
  obtain ⟨k, hk⟩ := Cheap.equalityTable F t (Fintype.card (pattern t))
  let Y := frame t q
  let cost := 2 * Y.width + (Format.addr l).width
    + Install.localCost Y.width * (Format.addr l).width
  refine ⟨c + 50, 2 ^ t + k + q + cost, fun h hh => ?_⟩
  have ht := Nat.two_pow_pos t
  let X := Format.pair (Perm h) (.vec (h + 1) (.addr q))
  have hw : X.width ≤ 2 ^ (h + 1) * (100 + (h + 1)) ^ 2 := by
    simp only [X, Format.width_pair, Format.width_vec, Format.width_addr]
    have hu := Nat.mul_le_mul_left (2 ^ (h + 1)) (show q ≤ h by omega)
    ring_nf at hu ⊢
    omega
  have input := Cheap.id F hw
  obtain ⟨v, hv, he⟩ := hc h (by omega)
  have addr := input.fst.comp hv
  have eqs := addr.comp (hk (h + 1) (h + 1) le_rfl (by omega) (encode (pattern t)))
  have marks := (input.snd.pair addr).comp (Cheap.neighbors F (.addr q) (h + 1) (h + 1) t
    le_rfl (by rw [Format.width_addr]; omega) (by omega))
  have tab : Cheap F 0 (h + 1) Y (.addr l) b 1 :=
    Cheap.fixed F b (show cost ≤ h + 1 by omega)
  have net := (eqs.pair marks).zip.comp (Cheap.map _ (fun _ => tab))
  refine ⟨_, net.mono (by omega), fun π z i => ?_⟩
  let r : Decor (controllers F T.embed) q := ⟨@Root.mk _ _ (B (h + 1)) (T.action h π) i, z⟩
  refine Eq.trans ?_ (hb r)
  apply congrArg b
  apply Prod.ext
  · apply congrArg (encode (pattern t))
    funext j l
    rw [Bool.eq_iff_iff]
    simp only [Root.see, decide_eq_true_eq, Function.comp_apply, id_eq, he]
    rfl
  · funext j
    exact congrArg z (he π j i)

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Decor
end

section
/-
# Dispatching to an action chosen at each site

A local decision names a member of a fixed list of actions. To
materialize one address bit the circuit needs only the encoded decision
and the corresponding bit of each candidate address.
-/

namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Decor
open Coloring

/-- Indexes the plan by the coordinates of `B l × (B p → Bool × Bool × B k × B p)`. -/
abbrev Plan (l p k : ℕ) := B l × (B p → Bool × Bool × B k × B p)

/-- The indexed operation `(x.1, fun j => let t := x.2 j; (t.1, t.2.1, a t.2.2.1, t.2.2.2))`. -/
def resolve {l p k h : ℕ} (x : Plan l p k) (a : B k → B (h + 1)) :
    B l × (B p → (Transport.Command h p).obj) :=
  (x.1, fun j => let t := x.2 j; (t.1, t.2.1, a t.2.2.1, t.2.2.2))

private abbrev Row (h p l : ℕ) := Format.pair (.addr l) (.vec p (Transport.Command h p))
private abbrev Source (h k s : ℕ) := Format.pair (.vec (h + 1) (.addr s)) (.vec k (Perm (h + 1)))

variable {l p k h s : ℕ}

private theorem resolve_bit (z : (Row h p l).pins) :
    ∃ d : slots (word (h + 1)), ∀ (x : Plan l p k) (a b : B k → B (h + 1)),
      (∀ i, (Format.addr (h + 1)).code (a i) d = (Format.addr (h + 1)).code (b i) d) →
      (Row h p l).code (resolve x a) z = (Row h p l).code (resolve x b) z := by
  rcases z with z | ⟨j, z | z | z | z⟩
  · exact ⟨.inl (), fun _ _ _ _ => rfl⟩
  · exact ⟨.inl (), fun _ _ _ _ => rfl⟩
  · exact ⟨.inl (), fun _ _ _ _ => rfl⟩
  · exact ⟨z, fun x a b he => he ((x.2 j).2.2.1)⟩
  · exact ⟨.inl (), fun _ _ _ _ => rfl⟩

private def select (g : B s → Plan l p k) (x : (Source h k s).obj) :
    (Transport.Controls h p (.addr l)).obj :=
  fun i => resolve (g (x.1 i)) (fun j => x.2 j i)

private theorem select_depends (g : B s → Plan l p k) :
    Install.Depends ((Transport.Controls h p (.addr l)).code ∘ select g ∘
      (Source h k s).code.symm) (s + 2 ^ k) := by
  classical
  rintro ⟨i, z⟩
  obtain ⟨d, hd⟩ := resolve_bit (k := k) z
  let key (u : slots (word s)) : (Source h k s).pins := .inl (i, u)
  let val (u : B k) : (Source h k s).pins := .inr (u, i, d)
  refine ⟨Finset.univ.image key ∪ Finset.univ.image val, ?_, fun x y he => ?_⟩
  · apply (Finset.card_union_le _ _).trans
    have hl := Finset.card_image_le (s := Finset.univ) (f := key)
    have hr := Finset.card_image_le (s := Finset.univ) (f := val)
    simpa only [Finset.card_univ, card_slots, wd_word, Fintype.card_fin] using Nat.add_le_add hl hr
  · let a := (Source h k s).code.symm x
    let b := (Source h k s).code.symm y
    have hl : a.1 i = b.1 i := by
      apply congrArg (Control.decode s)
      funext u
      exact he (key u) (by simp)
    have hr (j : B k) : (Format.addr (h + 1)).code (a.2 j i) d =
        (Format.addr (h + 1)).code (b.2 j i) d := by
      change (Source h k s).code a (val j) = (Source h k s).code b (val j)
      simp only [a, b, Equiv.apply_symm_apply]
      exact he (val j) (by simp)
    change (Row h p l).code (resolve (g (a.1 i)) (fun j => a.2 j i)) z =
      (Row h p l).code (resolve (g (b.1 i)) (fun j => b.2 j i)) z
    rw [hl]
    exact hd _ _ _ hr

private theorem cheap_select (F : Type) [Field F] (g : B s → Plan l p k) :
    ∃ k₀ : ℕ, ∀ h ≥ k₀, Cheap F (h + 1) (h + 1) (Source h k s)
      (Transport.Controls h p (.addr l)) (select g) 5 := by
  let C := Install.localCost (s + 2 ^ k)
  refine ⟨max s (max l (max p (max (2 ^ k) (max (2 ^ p) C)))), fun h hb => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hb
  obtain ⟨hs, hl, hp, hk, hr, hc⟩ := hb
  refine ⟨_, (select_depends (h := h) g).bnet F, ?_⟩
  change (Source h k s).width + (Transport.Controls h p (.addr l)).width +
    ((Source h k s).width + C * (Transport.Controls h p (.addr l)).width) ≤ _
  simp only [Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit, Format.width_addr (h + 1)]
  calc
    _ = 2 ^ (h + 1) * (2 * (s + 2 ^ k * (h + 1)) + (C + 1) * (l + 2 ^ p * (2 + (h + 1) + p)))
      := by ring
    _ ≤ 2 ^ (h + 1) * (2 * (h + h * (h + 1)) + (h + 1) * (h + h * (2 + (h + 1) + h))) := by gcongr
    _ ≤ _ := by gcongr; ring_nf; omega

theorem Local.dispatch {F : Type} [Field F] {m q : ℕ} {T : Routes F m}
    {f : Decor (controllers F T.embed) q → Plan l p k} (hf : Local f)
    (w : B k → controllers F T.embed) :
    ∃ c k₀ : ℕ, ∀ h ≥ k₀, ∃ v,
      Cheap F (h + 1) (h + 1) (.pair (Perm h) (.vec (h
        + 1) (.addr q))) (Transport.Controls h p (.addr l)) v c ∧
      ∀ π : Equiv.Perm (B h), ∀ z i,
        v (π, z) i = resolve (f ⟨@Root.mk _ _ (B (h + 1)) (T.action h π) i, z⟩)
          (fun j => (T.action h π).smul (w j) i) := by
  let e := encode (Plan l p k)
  let g := Function.invFun e
  obtain ⟨c, h₀, hl⟩ := hf.compile e
  obtain ⟨c', hr⟩ := T.controllers_net k w
  obtain ⟨h₁, hs⟩ := cheap_select F g
  refine ⟨c + c' + 10, max h₀ (max h₁ (2 ^ k)), fun h hh => ?_⟩
  obtain ⟨u, hu, eu⟩ := hl h (by omega)
  obtain ⟨v, hv, ev⟩ := hr h (by omega)
  let X := Format.pair (Perm h) (.vec (h + 1) (.addr q))
  have hx : X.width ≤ 2 ^ (h + 1) * (100 + (h + 1)) ^ c := by
    obtain ⟨_, _, hw⟩ := hu
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hw)
  have addresses := (Cheap.id F hx).fst.comp hv
  have net := (hu.pair addresses).comp (hs h (by omega))
  refine ⟨_, net.mono (by omega), fun π z i => ?_⟩
  change resolve (g (u (π, z) i)) (fun j => v π j i) = _
  rw [eu, show ∀ x, g (e x) = x from Function.leftInverse_invFun e.injective]
  exact congrArg _ (funext fun j => ev π j i)

end MatrixMultiplicationAllFields.MatrixExponent.Routing.Decor
end
