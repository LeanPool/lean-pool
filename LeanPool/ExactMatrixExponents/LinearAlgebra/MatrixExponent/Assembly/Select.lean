/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector
public import Mathlib.Data.Fintype.EquivFin
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Diagram.Pad
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Shaving.Defs
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Seats

/-!
# Long host names and short block records

A host's list of neighbor names is shared between blocks. An
occurrence sees only indices in this list and indices of remote
ports. This avoids charging a global address at every occurrence.
-/

@[expose] public section

section

namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Fmt

open Coloring

/-- The value specified by `.vec m (.pair (.vec d (.addr m)) (.vec h A))`. -/
abbrev rows (m d h : ℕ) (A : Format) : Format :=
  .vec m (.pair (.vec d (.addr m)) (.vec h A))

/-- Candidate outgoing stubs at one occurrence. The extra field can
carry a colony key. The block is implicit in the enclosing row. -/
abbrev occ (d _h e k ℓ : ℕ) : Format :=
  .pair (.addr ℓ) (.vec e (.pair .bit (.pair (.addr d) (.addr k))))

theorem width_rows (m d h : ℕ) (A : Format) :
    (rows m d h A).width = 2 ^ m * (2 ^ d * m + 2 ^ h * A.width) := by
  simp [rows]

theorem width_occ (d h e k ℓ : ℕ) :
    (occ d h e k ℓ).width = ℓ + 2 ^ e * (1 + (d + k)) := by
  simp [occ]

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Fmt
end

/-
# Networks between typed records

Sequential composition contracts the *entire* intermediate record.
Its two layouts may differ by arbitrary renaming of bit positions.
The gate budget is additive.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly

open Coloring

variable {F : Type} [Field F] {A B C D : Format} {u m n : ℕ} {L : Set (Table F)}

open scoped Classical in
instance finiteObj (A : Format) : Finite A.obj := Finite.of_injective A.code A.code.injective

open scoped Classical in
/-- Reindexes two finite types using equality of cardinalities. -/
def names (A : Format) : A.pins ≃ slots (word A.width)
    := Fintype.equivOfCardEq (by simp [Format.width])

open scoped Classical in
/-- Reindexes `Val a` and `A.obj` by an equivalence. -/
def view (A : Format) {a : Wire} (i : A.pins ≃ slots a) : Val a ≃ A.obj :=
  (bits a).trans ((i.symm.arrowCongr (.refl Bool)).trans A.code.symm)

open scoped Classical in
theorem view_apply (A : Format) {a : Wire} (i : A.pins ≃ slots a) (x : Val a) :
    view A i x = A.code.symm (bits a x ∘ i) := rfl

open scoped Classical in
/-- The defining condition `∀ (a b : Wire) (i : A.pins ≃ slots a) (j : B.pins ≃ slots b), ∃ s ≤
m, Wide F u L a b (fun x y => f (view A i x) (view B j y)) s`. -/
def Kernel (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (A B : Format) (f : A.obj → B.obj → F) (m : ℕ) : Prop :=
  ∀ (a b : Wire) (i : A.pins ≃ slots a) (j : B.pins ≃ slots b),
    ∃ s ≤ m, Wide F u L a b (fun x y => f (view A i x) (view B j y)) s

open scoped Classical in
/-- Requires `Kernel F u L A B (fun x y => if f x = y then 1 else 0) m`. -/
def Map (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (A B : Format) (f : A.obj → B.obj) (m : ℕ) : Prop :=
  Kernel F u L A B (fun x y => if f x = y then 1 else 0) m

namespace Kernel
variable {f : A.obj → B.obj → F}

open scoped Classical in
theorem mono (h : Kernel F u L A B f m) (hm : m ≤ n) : Kernel F u L A B f n := by
  intro a b i j
  obtain ⟨s, hs, h⟩ := h a b i j
  exact ⟨s, hs.trans hm, h⟩

open scoped Classical in
theorem widen {v : ℕ} {L' : Set (Table F)} (h : Kernel F u L A B f m)
    (hu : u ≤ v) (hl : L ⊆ L') : Kernel F v L' A B f m := by
  intro a b i j
  obtain ⟨s, hs, h⟩ := h a b i j
  exact ⟨s, hs, h.mono hu hl⟩

open scoped Classical in
theorem of_layout {a b : Wire} (i : A.pins ≃ slots a) (j : B.pins ≃ slots b)
    (h : ∃ s ≤ m, Wide F u L a b (fun x y => f (view A i x) (view B j y)) s) :
    Kernel F u L A B f m := by
  intro c d k l
  obtain ⟨s, hs, hw⟩ := h
  refine ⟨s, hs, ?_⟩
  have hp := (hw.pre (rewire_reindex (i.symm.trans k))).post (rewire_reindex (j.symm.trans l))
  simpa [view_apply, reindex, Function.comp_def] using hp

open scoped Classical in
theorem comp [Fintype B.obj] {g : B.obj → C.obj → F}
    (h : Kernel F u L A B f m) (k : Kernel F u L B C g n) :
    Kernel F u L A C (fun x z => ∑ y, f x y * g y z) (m + n) := by
  intro a c i l
  obtain ⟨s, hs, h⟩ := h a _ i (names B)
  obtain ⟨t, ht, k⟩ := k _ c (names B) l
  refine ⟨s + t, Nat.add_le_add hs ht, ?_⟩
  have he (x : Val a) (z : Val c) :=
    (view B (names B)).sum_comp (fun y => f (view A i x) y * g y (view C l z))
  simpa only [he] using h.comp k

open scoped Classical in
theorem par {g : C.obj → D.obj → F} (h : Kernel F u L A B f m) (k : Kernel F u L C D g n) :
    Kernel F u L (.pair A C) (.pair B D) (fun x y => f x.1 y.1 * g x.2 y.2) (m + n) := by
  obtain ⟨s, hs, h⟩ := h _ _ (names A) (names B)
  obtain ⟨t, ht, k⟩ := k _ _ (names C) (names D)
  exact of_layout (a := .pair _ _) (b := .pair _ _)
    ((names A).sumCongr (names C)) ((names B).sumCongr (names D))
    ⟨_, Nat.add_le_add hs ht, h.par k⟩

end Kernel

namespace Map
variable {f : A.obj → B.obj}

open scoped Classical in
theorem mono (h : Map F u L A B f m) (hm : m ≤ n) : Map F u L A B f n := Kernel.mono h hm

open scoped Classical in
theorem then_kernel {g : B.obj → C.obj → F} (h : Map F u L A B f m)
    (k : Kernel F u L B C g n) : Kernel F u L A C (fun x y => g (f x) y) (m + n) := by
  let _ := Fintype.ofFinite B.obj
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using Kernel.comp h k

open scoped Classical in
theorem comp {g : B.obj → C.obj} (h : Map F u L A B f m) (k : Map F u L B C g n) :
    Map F u L A C (g ∘ f) (m + n) := h.then_kernel k

open scoped Classical in
theorem par {g : C.obj → D.obj} (h : Map F u L A B f m) (k : Map F u L C D g n) :
    Map F u L (.pair A C) (.pair B D) (Prod.map f g) (m + n) := by
  unfold Map
  simpa only [Prod.ext_iff, Prod.map_fst, Prod.map_snd, ite_and, ite_mul, one_mul, zero_mul]
    using Kernel.par h k

open scoped Classical in
theorem of_layout {a b : Wire} (i : A.pins ≃ slots a) (j : B.pins ≃ slots b)
    {g : Val a → Val b} (h : DWide F u L a b g m) (he : ∀ x, view B j (g x) = f (view A i x)) :
    Map F u L A B f m := by
  apply Kernel.of_layout i j
  obtain ⟨s, hs, hw⟩ := h
  refine ⟨s, hs, ?_⟩
  simpa only [← he, Equiv.apply_eq_iff_eq] using hw

open scoped Classical in
theorem circuit (hu : 3 ≤ u) (h : Circuit F A B f m) : Map F u L A B f (4 * m) := by
  apply of_layout (names A) (names B) (DWide.of_dnet hu (h _ _ (names A) (names B)))
  intro x
  exact (view B (names B)).apply_symm_apply _

end Map
end MatrixMultiplicationAllFields.MatrixExponent.Assembly
end

/-
# Composing encoded expansions

A state can carry its host, allocation and proof invariants. Only
the bit record crosses a stage boundary. It may contain payloads
in the stage's own ordering. Distinct terms with the same record
retain their field multiplicities.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly

open Coloring

universe v

open scoped Classical in
/-- The data for the snapshot construction, including `state`, `eval`, `port`, `encode`. -/
structure Snapshot (F : Type) (x y : Wire) where
  /-- The `Snapshot` component of type `Type v`. -/
  state : Type v
  /-- The evaluation operation of type `state → Val x → Val y → F`. -/
  eval : state → Val x → Val y → F
  /-- The `Snapshot` component of type `Format`. -/
  port : Format
  /-- The `Snapshot` component of type `state → Val x → Val y → port.obj`. -/
  encode : state → Val x → Val y → port.obj

variable {F : Type} [Field F] {x y : Wire} {u m n : ℕ} {L : Set (Table F)}
  {X Y Z : Snapshot.{v} F x y}

open scoped Classical in
/-- The expands of type `Prop` for the given inputs. -/
def Expands (X Y : Snapshot.{v} F x y) (f : X.port.obj → Y.port.obj → F) : Prop :=
  ∀ s : X.state, ∃ (I : Type) (_ : Fintype I) (q : I → Y.state) (c : I → F),
    (∀ a b, X.eval s a b = ∑ i, c i * Y.eval (q i) a b) ∧
    ∀ a b r, f (X.encode s a b) r = ∑ i, if Y.encode (q i) a b = r then c i else 0

open scoped Classical in
/-- The condition `∃ f, Kernel F u L X.port Y.port f m ∧ Expands X Y f` on the specified data. -/
def Transforms (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (X Y : Snapshot.{v} F x y) (m : ℕ) : Prop :=
  ∃ f, Kernel F u L X.port Y.port f m ∧ Expands X Y f

open scoped Classical in
/-- Contracting against a snapshot sums over actual branches, including
when encodings collide. -/
private theorem contract {I R : Type} [Fintype I] [Fintype R] (q : I → R) (c : I → F) (f : R → F) :
    (∑ r, (∑ i, if q i = r then c i else 0) * f r) = ∑ i, c i * f (q i) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

open scoped Classical in
theorem Expands.comp [Fintype Y.port.obj] {f g} (h : Expands X Y f) (k : Expands Y Z g) :
    Expands X Z (fun a b => ∑ y, f a y * g y b) := by
  intro s
  obtain ⟨I, _, q, c, hq, he⟩ := h s
  choose J fJ r d hr hd using fun i => k (q i)
  let _ : ∀ i, Fintype (J i) := fJ
  refine ⟨Σ i, J i, inferInstance, fun v => r v.1 v.2, fun v => c v.1 * d v.1 v.2, ?_, ?_⟩
  · intro a b
    simp only [hq, hr, Finset.mul_sum, Fintype.sum_sigma, mul_assoc]
  · intro a b t
    simp only [he]
    rw [contract, Fintype.sum_sigma]
    simp only [hd, Finset.mul_sum, mul_ite, mul_zero]

namespace Transforms

open scoped Classical in
theorem mono (h : Transforms F u L X Y m) (hm : m ≤ n) : Transforms F u L X Y n :=
  let ⟨f, hf, he⟩ := h
  ⟨f, hf.mono hm, he⟩

open scoped Classical in
theorem widen {v : ℕ} {L' : Set (Table F)} (h : Transforms F u L X Y m) (hu : u ≤ v)
    (hs : L ⊆ L') : Transforms F v L' X Y m :=
  let ⟨f, hf, he⟩ := h
  ⟨f, hf.widen hu hs, he⟩

open scoped Classical in
theorem comp (h : Transforms F u L X Y m) (k : Transforms F u L Y Z n) :
    Transforms F u L X Z (m + n) := by
  let _ := Fintype.ofFinite Y.port.obj
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨g, hg, hg'⟩ := k
  exact ⟨_, hf.comp hg, he.comp hg'⟩

open scoped Classical in
theorem of_map (f : X.port.obj → Y.port.obj) (q : X.state → Y.state)
    (hm : Map F u L X.port Y.port f m)
    (he : ∀ s, X.eval s = Y.eval (q s))
    (hc : ∀ s a b, f (X.encode s a b) = Y.encode (q s) a b) :
    Transforms F u L X Y m := by
  refine ⟨_, hm, fun s => ⟨Unit, inferInstance, fun _ => q s, fun _ => 1, ?_, ?_⟩⟩
  · intro a b
    simp only [he, Fintype.sum_unique, one_mul]
  · intro a b r
    simp only [hc, Fintype.sum_unique]

open scoped Classical in
theorem refl (hu : 3 ≤ u) (X : Snapshot.{v} F x y) :
    Transforms F u L X X (4 * X.port.width) :=
  of_map id id (Map.circuit hu (Circuit.id F _)) (fun _ => rfl) (fun _ _ _ => rfl)

end Transforms

open scoped Classical in
/-- The condition `∃ k : X.port.obj → F, Kernel F u L X.port (.wire .unit) (fun a _ => k a) m ∧
∀ s a b, k (X.encode s a b) = X.eval s a b` on the specified data. -/
def Finishes (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (X : Snapshot.{v} F x y) (m : ℕ) : Prop :=
  ∃ k : X.port.obj → F, Kernel F u L X.port (.wire .unit) (fun a _ => k a) m ∧
    ∀ s a b, k (X.encode s a b) = X.eval s a b

open scoped Classical in
theorem Transforms.finish (h : Transforms F u L X Y m) (k : Finishes F u L Y n) :
    Finishes F u L X (m + n) := by
  let _ := Fintype.ofFinite Y.port.obj
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨g, hg, hg'⟩ := k
  refine ⟨fun x => ∑ y, f x y * g y, hf.comp hg, fun s a b => ?_⟩
  obtain ⟨I, _, q, c, hq, hh⟩ := he s
  simp only [hh, contract, hg', hq]

end MatrixMultiplicationAllFields.MatrixExponent.Assembly
end

/-
# Realizing local factors on shared tapes

Copying a tape is paid once per actual read, even if the tape is
much larger than any individual factor.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Kernel

open Coloring Transcript

variable {F : Type} [Field F] {A B C : Format} {u m : ℕ} {L : Set (Table F)}

open scoped Classical in
theorem of_weight (hu : 3 ≤ u) {f : ((A.pins ⊕ B.pins) → Bool) → F}
    (h : WideWeight F u L f m) :
    Kernel F u L A B (fun x y => f (Sum.elim (A.code x) (B.code y))) (m + 4 * B.width) := by
  intro a b i j
  obtain ⟨s, hs, k⟩ := h (.pair a b) (i.sumCongr j)
  obtain ⟨t, ht, hc⟩ := (Net.cup F b).includeWide (L := L) hu
  have hw := (((k.par hc).pre (.unit' _)).post ((Rewire.unit' _).comp (.swap _ _))).trace
  have hb := (Fintype.card_congr j).trans (card_slots b)
  refine ⟨s + t, Nat.add_le_add hs (by rw [Format.width, hb]; exact ht), ?_⟩
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hw
  convert hw using 1
  funext x y
  simp only [view_apply, Equiv.apply_symm_apply]
  apply congrArg f
  funext p
  cases p <;> rfl

open scoped Classical in
theorem factors {I Y : Type} [Fintype I] [Fintype Y] {Z : I → Type} [∀ i, Finite (Z i)]
    (k : (i : I) → (Z i → Bool) → F) (r : (i : I) → Z i → (A.pins ⊕ B.pins) ⊕ Y)
    (cost : I → ℕ) (hu : 3 ≤ u) (h : ∀ i, WideWeight F u L (k i) (cost i)) :
    Kernel F u L A B (fun x y => weightedSum k r (Sum.elim (A.code x) (B.code y)))
      (8 * (A.width + B.width + Fintype.card Y) + 9 * (∑ i, cost i) + 4 * B.width) := by
  let : ∀ i, Fintype (Z i) := fun i => Fintype.ofFinite (Z i)
  simpa only [Fintype.card_sum] using of_weight hu (wide_sum k r cost hu h)

open scoped Classical in
private theorem free (a : Wire) : Net F .unit a (fun _ _ => 1) (wd a) := by
  induction a with
  | bit => exact .table _ _ _ (by decide)
  | unit => exact .empty
  | pair a b h k => simpa only [wd, one_mul] using (h.par k).pre (.unit' _)

open scoped Classical in
theorem sum_hidden [Fintype C.obj] {f : (A.obj × C.obj) → B.obj → F}
    (hu : 3 ≤ u) (h : Kernel F u L (.pair A C) B f m) :
    Kernel F u L A B (fun a b => ∑ c, f (a, c) b) (m + 4 * C.width) := by
  intro a b i j
  let c := word C.width
  obtain ⟨s, hs, hk⟩ := h (.pair a c) b (i.sumCongr (names C)) j
  obtain ⟨t, ht, hf⟩ := (free (F := F) c).includeWide (L := L) hu
  have hw := ((hk.par hf).pre (.unit' _)).trace
  refine ⟨s + t, Nat.add_le_add hs (by simpa [c] using ht), ?_⟩
  simp only [mul_one] at hw
  convert hw using 1
  funext x y
  exact ((view C (names C)).sum_comp (fun z => f (view A i x, z) (view B j y))).symm

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Kernel
end

/-
# One selector word per branch of an exact expansion

The menu can depend on the entire preceding state. Only the exposed
selector format must stay fixed across the possible preceding states.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly
open Coloring Transcript

universe v
variable {F : Type} [Field F] {x y : Wire} {u m n : ℕ} {L : Set (Table F)}
  {X Y : Snapshot.{v} F x y} {C : Format}

open scoped Classical in
/-- The data for the selected construction, including `choice`, `[finite`, `index`, `next`,
`scalar`. -/
structure Selected (X Y : Snapshot.{v} F x y) (C : Format) where
  /-- The `Selected` component of type `X.state → Type`. -/
  choice : X.state → Type
  [finite : ∀ s, Fintype (choice s)]
  /-- The identification of the indices of type `∀ s, Selector (choice s) C.obj`. -/
  index : ∀ s, Selector (choice s) C.obj
  /-- The successor of each choice of type `∀ s, choice s → Y.state`. -/
  next : ∀ s, choice s → Y.state
  /-- The scalar prefactor of type `∀ s, choice s → F`. -/
  scalar : ∀ s, choice s → F
  expands : ∀ s a b, X.eval s a b = ∑ i, scalar s i * Y.eval (next s i) a b

attribute [instance] Selected.finite

open scoped Classical in
theorem Transforms.of_selector (hu : 3 ≤ u) (R : Selected X Y C)
    {k : X.port.obj × C.obj → Y.port.obj → F}
    (hk : Kernel F u L (.pair X.port C) Y.port k m)
    (he : ∀ s a b c t, k (X.encode s a b, c) t = ((R.index s).read c).elim 0
      (fun i => if Y.encode (R.next s i) a b = t then R.scalar s i else 0)) :
    Transforms F u L X Y (m + 4 * C.width) := by
  let _ := Fintype.ofFinite C.obj
  refine ⟨_, Kernel.sum_hidden hu hk, fun s =>
    ⟨R.choice s, inferInstance, R.next s, R.scalar s, R.expands s, fun a b t => ?_⟩⟩
  simp only [he, Selector.sum]

open scoped Classical in
/-- The computation can reject invalid words by zero weight. -/
theorem Transforms.of_guard (hu : 3 ≤ u) (R : Selected X Y C)
    (out : X.port.obj × C.obj → Y.port.obj) (weight : X.port.obj × C.obj → F)
    (hk : Kernel F u L (.pair X.port C) Y.port (fun v t => if out v = t then weight v else 0) m)
    (hw : ∀ s a b c, weight (X.encode s a b, c) = ((R.index s).read c).elim 0 (R.scalar s))
    (ho : ∀ s a b i, out (X.encode s a b, (R.index s).write i) = Y.encode (R.next s i) a b) :
    Transforms F u L X Y (m + 4 * C.width) := by
  refine Transforms.of_selector hu R hk fun s a b c t => ?_
  rw [hw]
  cases h : (R.index s).read c with
  | none => simp
  | some i =>
    rw [(R.index s).valid _ _ |>.mp h, ho]
    rfl

open scoped Classical in
theorem Finishes.start (hu : 3 ≤ u) (s : X.state)
    (h : Map F u L (.wire (.pair x y)) X.port (fun p => X.encode s p.1 p.2) m)
    (hf : Finishes F u L X n) :
    ∃ v ≤ m + n + 4 * wd y, Wide F u L x y (X.eval s) v := by
  obtain ⟨k, hk, he⟩ := hf
  obtain ⟨v, hv, hv'⟩ := h.then_kernel hk (.pair x y) .unit (.refl _) (.refl _)
  have viewId (z : Val (.pair x y)) : view (.wire (.pair x y)) (.refl _) z = z :=
    (bits _).symm_apply_apply z
  simp only [viewId, he] at hv'
  obtain ⟨w, hw, hcup⟩ := (Net.cup F y).includeWide (L := L) hu
  have hfin := (((hv'.par hcup).pre (.unit' _)).post ((Rewire.unit' _).comp (.swap _ _))).trace
  refine ⟨v + w, Nat.add_le_add hv hw, ?_⟩
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hfin

open scoped Classical in
/-- Stage budgets add even when ports, layouts and reachable states
change from round to round. -/
theorem Finishes.stages (X : ℕ → Snapshot.{v} F x y) (cost : ℕ → ℕ) (j : ℕ)
    (steps : ∀ i < j, Transforms F u L (X i) (X (i + 1)) (cost i))
    (stop : Finishes F u L (X j) m) :
    Finishes F u L (X 0) ((∑ i ∈ Finset.range j, cost i) + m) := by
  induction j generalizing m with
  | zero => simpa using stop
  | succ j ih =>
    rw [Finset.sum_range_succ, add_assoc]
    exact ih (fun i hi => steps i (Nat.lt_succ_of_lt hi)) ((steps j (by omega)).finish stop)

end MatrixMultiplicationAllFields.MatrixExponent.Assembly
end
