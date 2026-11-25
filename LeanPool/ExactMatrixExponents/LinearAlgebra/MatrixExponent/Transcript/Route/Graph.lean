/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Tagged.SortBack
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.VectorSort
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Install.Weight
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.RAM.Calls
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Cost
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Shaving.Defs

/-! # Verifying a deterministic controller on two named tapes -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Coloring

open Install
variable {F : Type} [Field F] {A D : Format} {f : A.obj → D.obj} {j k c : ℕ}

open scoped Classical in
/-- Returns `1` when `f (A.code.symm (z ∘ Sum.inl)) = D.code.symm (z ∘ Sum.inr)` holds, and `0`
otherwise. -/
def graph (F : Type) [Field F] (A D : Format) (f : A.obj → D.obj)
    (z : A.pins ⊕ D.pins → Bool) : F :=
  if f (A.code.symm (z ∘ Sum.inl)) = D.code.symm (z ∘ Sum.inr) then 1 else 0

open scoped Classical in
theorem Cheap.weight (h : Cheap F j k A D f c) :
    Weight F (graph F A D f) (2 ^ j * (100 + k) ^ c) := by
  obtain ⟨m, hf, hm⟩ := h
  let a := word A.width
  let b := word D.width
  let i : A.pins ≃ slots a := Fintype.equivOfCardEq (by simp [a, Format.width])
  let l : D.pins ≃ slots b := Fintype.equivOfCardEq (by simp [b, Format.width])
  obtain ⟨v, hv, hf⟩ := hf a b i l
  have hb : wd b = D.width := wd_word _
  apply Weight.of_layout (a := .pair a b) (i.sumCongr l)
  refine ⟨v + wd b, by omega, ?_⟩
  have hu (k : Val a → Val b → F) (hk : Net F a b k v) :
      Net F (.pair a b) .unit (fun x _ => k x.1 x.2) (v + wd b) := by
    have both := (hk.par (Tagged.cap b)).pre (.assoc a b b)
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
      (both.post (.swap _ _)).trace
  convert hu _ hf using 1
  funext z _
  have he (u : D.obj) : u = D.code.symm (bits b z.2 ∘ l) ↔
      (bits b).symm (D.code u ∘ l.symm) = z.2 := by
    rw [Equiv.eq_symm_apply, Equiv.symm_apply_eq]
    simp only [funext_iff, Function.comp_apply]
    exact ⟨fun h t => by simpa using h (l.symm t), fun h t => by simpa using h (l t)⟩
  change (if f (A.code.symm (bits a z.1 ∘ i)) = D.code.symm (bits b z.2 ∘ l) then (1 : F) else 0)
    = _
  simp only [he, Function.comp_apply]

end MatrixMultiplicationAllFields.MatrixExponent.Coloring
end

/-
# Reading routed stations through a dictionary

Each station occupies exactly one installed seat. The other seats
are either dormant or encode withdrawn scalar factors.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript

variable {F : Type} [Field F] {x y : Wire} {d U : ℕ} {T J : Type}

open scoped Classical in
/-- The data for the dispatch construction, including `place`, `label`, `correct`, `size`,
`extra`. -/
structure Dispatch (D : Dictionary F d) (U : ℕ) (G : Diagram F x y)
    (T : Type) (width : J → ℕ) extends Route G T where
  /-- The `Dispatch` component of type `Selector G.V J`. -/
  place : Selector G.V J
  /-- The label at each coordinate of type `G.V → Fin d → Bool`. -/
  label : G.V → Fin d → Bool
  correct : ∀ v, D.table (label v) = G.table v
  size : ∀ v, d + G.arity v ≤ U ∧ d + G.arity v ≤ 2 ^ (width (place.write v))
  /-- The `Dispatch` component of type `(s : J) → (RAM.token (width s)).obj`. -/
  extra : (s : J) → (RAM.token (width s)).obj

namespace Dispatch
variable {D : Dictionary F d} {G : Diagram F x y} {width : J → ℕ}
  (P : Dispatch D U G T width)

open scoped Classical in
/-- The value specified by `query (P.label v) (G.table v) (Sum.elim (exterior a b) q ∘ P.tap
v)`. -/
def request (a : Val x) (b : Val y) (q : T → Bool) (v : G.V) : List Bool :=
  query (P.label v) (G.table v) (Sum.elim (exterior a b) q ∘ P.tap v)

open scoped Classical in
/-- The indexed operation `(P.place.read s).elim (P.extra s) (fun v => RAM.encodeToken _
(P.request a b q v))`. -/
def emit (a : Val x) (b : Val y) (q : T → Bool) (s : J) : (RAM.token (width s)).obj :=
  (P.place.read s).elim (P.extra s) (fun v => RAM.encodeToken _ (P.request a b q v))

open scoped Classical in
/-- Returns `RAM.tokenValue U D.eval (width s) (P.extra s)` when `P.place.read s = none` holds,
and `1` otherwise. -/
def factor (s : J) : F :=
  if P.place.read s = none then RAM.tokenValue U D.eval (width s) (P.extra s) else 1

variable [Fintype J]

open scoped Classical in
/-- The product of `P.factor s` indexed by `s`. -/
def scalar : F := ∏ s, P.factor s

open scoped Classical in
theorem product (a : Val x) (b : Val y) (q : T → Bool) :
    (∏ s, RAM.tokenValue U D.eval (width s) (P.emit a b q s)) =
      P.scalar * ∏ v, P.toRoute.vertex a b q v := by
  have he (s : J) : RAM.tokenValue U D.eval (width s) (P.emit a b q s) =
      P.factor s * ∏ v, if s = P.place.write v then P.toRoute.vertex a b q v else 1 := by
    simp_rw [← P.place.valid]
    unfold emit factor
    cases h : P.place.read s with
    | none => simp
    | some v =>
      have hl : (P.request a b q v).length = d + G.arity v := query_length _ _ _
      have hv := P.size v
      rw [← (P.place.valid _ _).mp h] at hv
      simp only [Option.elim_some, reduceCtorEq, ite_false, one_mul, Option.some.injEq,
        Finset.prod_ite_eq, Finset.mem_univ, ite_true]
      rw [RAM.tokenValue_encode _ _ _ (hl.le.trans hv.1) (hl.le.trans hv.2)]
      exact D.eval_query _ _ (P.correct v) _
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp only [scalar, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

end Dispatch
end MatrixMultiplicationAllFields.MatrixExponent.Transcript
end

/-
# Contracting a selected family

Control bits include intermediate deterministic decisions. A valid
selector has only one encoding. Payload bits may include paths and
padding; each internal edge retains exactly one independent bit.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript

variable {F : Type} [Field F] {x y : Wire} {d U : ℕ} {T J I C : Type}
  {width : J → ℕ} {D : Dictionary F d} {G : I → Diagram F x y}

namespace Dispatch

variable (S : Selector I C) (P : ∀ i, Dispatch D U (G i) T width)

open scoped Classical in
/-- The condition `∃ i, S.read c = some i ∧ (P i).copies.Agrees (exterior a b) t` on the
specified data. -/
def authorized (a : Val x) (b : Val y) (c : C) (t : T → Bool) : Prop :=
  ∃ i, S.read c = some i ∧ (P i).copies.Agrees (exterior a b) t

open scoped Classical in
/-- Multiplicity is checked on both levels, first the internal wires
of a summand and then the index of the summand. -/
theorem sum [Fintype I] [Fintype C] [Fintype T] [Fintype J] (a : Val x) (b : Val y)
    (ok : C → (T → Bool) → Prop)
    (calls : C → (T → Bool) → (s : J) → (RAM.token (width s)).obj)
    (allowed : ∀ c t, ok c t ↔ authorized S P a b c t)
    (reads : ∀ i t, (P i).copies.Agrees (exterior a b) t →
      calls (S.write i) t = (P i).emit a b t) :
    (∑ c, ∑ t, if ok c t then ∏ s, RAM.tokenValue U D.eval (width s) (calls c t s) else 0) =
      ∑ i, (P i).scalar * (G i).eval a b := by
  rw [← S.sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  cases h : S.read c with
  | none =>
    have he (t) : ¬ok c t := by simp [allowed, authorized, h]
    simp [he]
  | some i =>
    have he (t) : ok c t ↔ (P i).copies.Agrees (exterior a b) t := by
      simp only [allowed, authorized, h, Option.some.injEq, exists_eq_left']
    simp only [Option.elim_some]
    rw [← (P i).toRoute.contract, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases hx : ok c t
    · rw [ite_eq_left hx, (S.valid _ _).mp h, reads _ _ ((he _).mp hx), product]
      simp only [Route.value, ite_eq_left ((he _).mp hx)]
    · rw [ite_eq_right hx, Route.value, ite_eq_right (mt (he _).mpr hx), mul_zero]

end Dispatch
end MatrixMultiplicationAllFields.MatrixExponent.Transcript
end

/- # Labeled networks for a selected family of routed diagrams -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM

open Filter

open scoped Classical in
theorem labeled {K : Type} [Field K] {a b : Wire} {f : Val a → Val b → K}
    {W : List Bool → K} {U s : ℕ} (h : Wide K (8 * (U + 1)) (labels U W) a b f s) :
    Labeled f (ceiling U + 1) s (8 * (U + 1)) := by
  let L := (Finset.range (ceiling U + 1)).image (label U W)
  have he : (↑L : Set (Table K)) = labels U W := by
    ext
    simp [L, labels]
  exact ⟨L, Finset.card_image_le.trans_eq (Finset.card_range _), he.symm ▸ h⟩

end MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM
end
