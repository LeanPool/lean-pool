/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.EncodedList
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.RecursionEvaluation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Evaluation existence for the encoded-list codes

`EncodedList` defines the codes that act on an encoded list; this file proves
that the five public operations below have a value in an arbitrary model, given
the evaluations required by their arguments.  Their public conclusions assert
only existence: nothing here decodes an arbitrary model element as a list or
identifies its semantic list contents.  Exact private evaluations of the head,
tail and iterated tail are used internally to establish that existence.

Cons needs no induction: its eager conditional has two polynomial branches.
Option bind also needs no induction once the continuation is supplied at the
payload; because its conditional is eager, that evaluation is required even at
zero.  Thus `𝐏𝐀⁻` suffices for both public existence theorems.  The indexed
entry, the length and the appended list rest on the iterated tail, whose
termination is a `𝐏𝐀` statement.

The iterated tail is `codePrec` with the list as base and one tail as step, so
`eval_codePrec_exists_of_total` gives it a value at every index.  A separate
Sigma-one induction proves that, for `i ≤ l`, an iterated-tail value `z` satisfies
`z + i ≤ l`; hence the value at index `l` is zero.  The length minimization
therefore terminates, by the Sigma-one least-number principle applied to the
indices whose iterated tail is zero.

The head, tail and iterated tail lemmas stay private; the file exposes only the
five existence statements the evaluator layers consume.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open HierarchySymbol

variable {M : Type*} [ORingStructure M]

/-!
### The pairing and cons layers -/

/-- Cantor pairing has a value at any two values, without an induction
assumption: the two branches of the eager conditional are polynomials. -/
private theorem eval_codePair_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A B : Code k) (a b : M)
    (v : Fin k → M) (hA : Semiformula.Evalb (a :> v) (code A))
    (hB : Semiformula.Evalb (b :> v) (code B)) :
    ∃ p : M, Semiformula.Evalb (p :> v) (code (codePair A B)) :=
  by
  have hhigh : Semiformula.Evalb ((b * b + a) :> v) (code (codeAdd (codeMul B B) A)) :=
    (eval_codeAdd_iff _ _ _ _).mpr
      ⟨b * b, a, (eval_codeMul_iff _ _ _ _).mpr ⟨b, b, hB, hB, rfl⟩, hA, rfl⟩
  have hlow :
    Semiformula.Evalb ((a * a + a + b) :> v) (code (codeAdd (codeAdd (codeMul A A) A) B)) :=
    (eval_codeAdd_iff _ _ _ _).mpr
      ⟨a * a + a, b,
        (eval_codeAdd_iff _ _ _ _).mpr
          ⟨a * a, a, (eval_codeMul_iff _ _ _ _).mpr ⟨a, a, hA, hA, rfl⟩, hA, rfl⟩,
        hB, rfl⟩
  simp only [codePair]
  by_cases hab : a < b
  · exact
      ⟨b * b + a,
        eval_codeIfPos_of _ _ _ 1 (b * b + a) (a * a + a + b) (b * b + a) v
          ((eval_codeLt_iff _ _ _ _).mpr ⟨a, b, hA, hB, Or.inl ⟨hab, rfl⟩⟩) hhigh hlow
          (Or.inl ⟨by simp, rfl⟩)⟩
  · exact
      ⟨a * a + a + b,
        eval_codeIfPos_of _ _ _ 0 (b * b + a) (a * a + a + b) (a * a + a + b) v
          ((eval_codeLt_iff _ _ _ _).mpr ⟨a, b, hA, hB, Or.inr ⟨hab, rfl⟩⟩) hhigh hlow
          (Or.inr ⟨rfl, rfl⟩)⟩

/-!
### Head and tail -/

/-- The encoded head has a value at any value of its argument. -/
private theorem eval_codeListHeadOptional_exists [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (d : Code k) (x : M)
    (v : Fin k → M) (hd : Semiformula.Evalb (x :> v) (code d)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeListHeadOptional d)) :=
  by
  have hone : Semiformula.Evalb ((1 : M) :> v) (code (codeConst (n := k) 1)) := by
    rw [eval_codeConst_iff]; simp
  have hsub := eval_codeSub d (codeConst 1) x 1 v hd hone
  have hsucc :
    Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pi₁ (x - 1) + 1) :> v)
      (code (codeSucc (codeUnpair₁ (codeSub d (codeConst 1))))) :=
    (eval_codeSucc_iff _ _ _).mpr
      ⟨_, eval_codeUnpair₁ (codeSub d (codeConst 1)) (x - 1) v hsub, rfl⟩
  have hzero : Semiformula.Evalb ((0 : M) :> v) (code (Code.zero k)) :=
    (eval_zero_iff _ _).mpr rfl
  simp only [codeListHeadOptional]
  by_cases hx : 0 < x
  · exact
      ⟨_,
        eval_codeIfPos_of _ _ _ x _ 0 (FFL.FirstOrder.Arithmetic.pi₁ (x - 1) + 1) v hd hsucc
          hzero (Or.inl ⟨hx, rfl⟩)⟩
  · exact
      ⟨0,
        eval_codeIfPos_of _ _ _ x _ 0 0 v hd hsucc hzero
          (Or.inr ⟨le_antisymm (not_lt.mp hx) (by simp), rfl⟩)⟩

/-- The encoded tail at a value, with its value displayed as the second Cantor
component of the predecessor. -/
private theorem eval_codeListTail_value [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] {k : ℕ} (d : Code k) (x : M)
    (v : Fin k → M) (hd : Semiformula.Evalb (x :> v) (code d)) :
    Semiformula.Evalb ((FFL.FirstOrder.Arithmetic.pi₂ (x - 1)) :> v) (code (codeListTail d)) :=
  by
  have hone : Semiformula.Evalb ((1 : M) :> v) (code (codeConst (n := k) 1)) := by
    rw [eval_codeConst_iff]; simp
  exact eval_codeUnpair₂ _ _ v (eval_codeSub d (codeConst 1) x 1 v hd hone)

/-!
### The iterated-tail recursion -/

/-- The iterated-tail recursion that `codeListDrop` applies to its index and
its list. -/
private def dropCore : Code 2 :=
  codePrec (Code.proj (0 : Fin 1)) (codeListTail (Code.proj (1 : Fin 3)))

/-- `codeListDrop` applies `dropCore` to its two arguments. -/
private theorem codeListDrop_eq_dropCore {n : ℕ} (dlist didx : Code n) :
    codeListDrop dlist didx = dropCore.comp ![didx, dlist] :=
  rfl

/-- The iterated tail has a value at every index and every list value.  The
base is the list itself and the step is one tail, total at every value. -/
private theorem eval_dropCore_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (i l : M) :
    ∃ z : M, Semiformula.Evalb (z :> ![i, l]) (code dropCore) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  exact
    eval_codePrec_exists_of_total (Code.proj (0 : Fin 1)) (codeListTail (Code.proj (1 : Fin 3)))
      i ![l] ⟨l, (eval_proj_iff _ _ _).mpr (by simp)⟩
      (fun j _ z =>
        ⟨_,
          eval_codeListTail_value (Code.proj (1 : Fin 3)) z (j :> z :> ![l])
            ((eval_proj_iff _ _ _).mpr (by simp))⟩)

/-- The iterated tail at evaluated list and index codes. -/
private theorem eval_codeListDrop_exists [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {n : ℕ} (dlist didx : Code n) (l i : M)
    (v : Fin n → M) (hlist : Semiformula.Evalb (l :> v) (code dlist))
    (hidx : Semiformula.Evalb (i :> v) (code didx)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeListDrop dlist didx)) :=
  by
  obtain ⟨z, hz⟩ := eval_dropCore_exists i l
  refine ⟨z, ?_⟩
  rw [codeListDrop_eq_dropCore, eval_comp_iff]
  refine ⟨![i, l], hz, ?_⟩
  intro j
  refine Fin.cases ?_ ?_ j
  · simpa using hidx
  · intro j1
    refine Fin.cases ?_ (fun j2 => Fin.elim0 j2) j1
    simpa using hlist

/-!
### Sigma-one definability of a literal code graph -/

open HierarchySymbol in
/-- Varying the first argument of the graph formula of a code, with the output
and the remaining arguments fixed as parameters, is a Sigma-one condition. -/
private theorem definable_code_head_slot {m : ℕ} (A : Code (m + 1)) (out : M)
    (par : Fin m → M) :
    Σ-[1].DefinablePred (fun c : M => Semiformula.Evalb (out :> c :> par) (code A)) :=
  by
  refine
    ⟨HierarchySymbol.Semiformula.mkSigma
        ((Rew.embSubsts
            ((&out : Semiterm ℒₒᵣ M 1) :>
              (#0 : Semiterm ℒₒᵣ M 1) :> fun j => (&(par j) : Semiterm ℒₒᵣ M 1))) ▹
          (code A))
        (Hierarchy.rew _ (code_sigma_one A)),
      ?_⟩
  intro w
  simp only [HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_embSubsts]
  have hv :
    (Semiterm.val w id ∘
        ((&out : Semiterm ℒₒᵣ M 1) :>
          (#0 : Semiterm ℒₒᵣ M 1) :> fun j => (&(par j) : Semiterm ℒₒᵣ M 1))) =
      (out :> w 0 :> par) :=
    by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j1
      refine Fin.cases ?_ ?_ j1
      · simp
      · intro j2; simp
  rw [hv]

open HierarchySymbol in
/-- Varying the output and the first argument of the graph formula of a code,
with the remaining arguments fixed as parameters, is a Sigma-one condition. -/
private theorem definable_code_out_head_slot {m : ℕ} (A : Code (m + 1)) (par : Fin m → M) :
    Σ-[1].Definable (fun w : Fin 2 → M => Semiformula.Evalb (w 0 :> w 1 :> par) (code A)) :=
  by
  refine
    ⟨HierarchySymbol.Semiformula.mkSigma
        ((Rew.embSubsts
            ((#0 : Semiterm ℒₒᵣ M 2) :>
              (#1 : Semiterm ℒₒᵣ M 2) :> fun j => (&(par j) : Semiterm ℒₒᵣ M 2))) ▹
          (code A))
        (Hierarchy.rew _ (code_sigma_one A)),
      ?_⟩
  intro w
  simp only [HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_embSubsts]
  have hv :
    (Semiterm.val w id ∘
        ((#0 : Semiterm ℒₒᵣ M 2) :>
          (#1 : Semiterm ℒₒᵣ M 2) :> fun j => (&(par j) : Semiterm ℒₒᵣ M 2))) =
      (w 0 :> w 1 :> par) :=
    by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j1
      refine Fin.cases ?_ ?_ j1
      · simp
      · intro j2; simp
  rw [hv]

/-!
### The iterated tail decreases -/

/-- At every index up to the list value, the iterated tail has a value whose
sum with the index is bounded by the list value.

The bound is what makes the minimization inside `codeListLength` terminate at an
arbitrary element of the model, well formed or not. -/
private theorem dropCore_bound [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (l : M) :
    ∀ i : M, (∃ z : M, Semiformula.Evalb (z :> ![i, l]) (code dropCore) ∧ z + i ≤ l) ∨ l < i :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hgraph :
    Σ-[1].Definable
      (fun w : Fin 2 → M =>
        Semiformula.Evalb (w 0 :> ![w 1, l]) (code dropCore) ∧ w 0 + w 1 ≤ l) :=
    HierarchySymbol.Definable.and (definable_code_out_head_slot dropCore ![l]) (by definability)
  have hdef :
    Σ-[1].DefinablePred
      (fun i : M =>
        (∃ z : M, Semiformula.Evalb (z :> ![i, l]) (code dropCore) ∧ z + i ≤ l) ∨ l < i) :=
    HierarchySymbol.Definable.or
      (HierarchySymbol.Definable.exs (hgraph.of_iff (by intro w; simp))) (by definability)
  refine InductionOnHierarchy.succ_induction Σ 1 hdef ?_ ?_
  · obtain ⟨z, hz⟩ := eval_dropCore_exists 0 l
    have hzl : z = l :=
      (eval_proj_iff _ _ _).mp
        (eval_codePrec_zero (Code.proj (0 : Fin 1)) (codeListTail (Code.proj (1 : Fin 3))) z
          ![l] hz)
    exact Or.inl ⟨z, hz, by rw [hzl]; simp⟩
  · intro i IH
    by_cases hli : l < i + 1
    · exact Or.inr hli
    · have hil : i + 1 ≤ l := not_lt.mp hli
      obtain ⟨z, hz, hzi⟩ :=
        IH.resolve_right (not_lt.mpr (le_of_lt (lt_of_lt_of_le (by simp) hil)))
      obtain ⟨z', hz'⟩ := eval_dropCore_exists (i + 1) l
      obtain ⟨w, hw, hstep⟩ :=
        eval_codePrec_succ (Code.proj (0 : Fin 1)) (codeListTail (Code.proj (1 : Fin 3))) i z'
          ![l] hz'
      have hwz : w = z := eval_unique hw hz
      have htail :=
        eval_codeListTail_value (Code.proj (1 : Fin 3)) z (i :> z :> ![l])
          ((eval_proj_iff _ _ _).mpr (by simp))
      have hz'val : z' = FFL.FirstOrder.Arithmetic.pi₂ (z - 1) :=
        by
        rw [hwz] at hstep
        exact eval_unique hstep htail
      refine Or.inl ⟨z', hz', ?_⟩
      rcases eq_or_ne z 0 with hz0 | hz0
      · have : z' = 0 := by
          rw [hz'val, hz0]
          exact
            le_antisymm (by simpa using FFL.FirstOrder.Arithmetic.pi₂_le_self ((0 : M) - 1))
              (by simp)
        rw [this, zero_add]
        exact hil
      · have hone : 1 ≤ z := FFL.FirstOrder.Arithmetic.ne_zero_iff_one_le.mp hz0
        have hz'le : z' + 1 ≤ z :=
          by
          have h1 : z' ≤ z - 1 := by
            rw [hz'val]
            exact FFL.FirstOrder.Arithmetic.pi₂_le_self _
          calc
            z' + 1 ≤ (z - 1) + 1 := by simpa using h1
            _ = z := FFL.FirstOrder.Arithmetic.sub_add_self_of_le hone
        calc
          z' + (i + 1) = (z' + 1) + i := by simp [add_comm, add_left_comm]
          _ ≤ z + i := by simpa using hz'le
          _ ≤ l := hzi

/-- The iterated tail at the list value itself is zero. -/
private theorem eval_dropCore_zero_at_value [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (l : M) :
    Semiformula.Evalb ((0 : M) :> ![l, l]) (code dropCore) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨z, hz, hzl⟩ := (dropCore_bound l l).resolve_right (_root_.lt_irrefl l)
  have hz0 : z = 0 := by
    have h1 : z + l = l := le_antisymm hzl le_add_self
    exact add_right_cancel (b := l) (by simpa using h1)
  rwa [hz0] at hz

/-!
### Local unfolding equations

Rewriting with the definitions of `EncodedList` directly would make this module
generate their equation lemmas, moving ownership of those constants away from
the modules that already generate them.  These `rfl` equations keep the
unfolding local. -/

/-- `codeListLength` written out. -/
private theorem codeListLength_eq {n : ℕ} (dlist : Code n) :
    codeListLength dlist =
      codeRfindPos (codeInv (codeListDrop (codeLift dlist) (codeHead (n := n)))) :=
  rfl

/-- `codeOptionBind` written out. -/
private theorem codeOptionBind_eq {n : ℕ} (dopt : Code n) (dk : Code (n + 1)) :
    codeOptionBind dopt dk =
      codeIfPos dopt (codeBind (codeSub dopt (Code.one n)) dk) (Code.zero n) :=
  rfl

/-!
### Evaluation existence for the encoded-list constructors -/

/-- The encoded cons cell has a value at any head and tail values. -/
theorem eval_codeListCons_exists_of_values [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (A B : Code k) (a b : M)
    (v : Fin k → M) (hA : Semiformula.Evalb (a :> v) (code A))
    (hB : Semiformula.Evalb (b :> v) (code B)) :
    ∃ c : M, Semiformula.Evalb (c :> v) (code (codeListCons A B)) :=
  by
  obtain ⟨p, hp⟩ := eval_codePair_exists A B a b v hA hB
  exact ⟨p + 1, (eval_codeSucc_iff _ _ _).mpr ⟨p, hp, rfl⟩⟩

/-- The length minimization terminates at any list value.

Nothing is asserted about the value found: for an arbitrary element of the model
it is the least index whose iterated tail is zero, which agrees with the number
of entries only on an actual encoded list. -/
theorem eval_codeListLength_exists_of_value [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (dlist : Code k) (l : M)
    (v : Fin k → M) (hlist : Semiformula.Evalb (l :> v) (code dlist)) :
    ∃ n : M, Semiformula.Evalb (n :> v) (code (codeListLength dlist)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hdrop :
    ∀ t : M,
      ∃ z : M,
        Semiformula.Evalb (z :> t :> v)
          (code (codeListDrop (codeLift dlist) (codeHead (n := k)))) :=
    fun t =>
    eval_codeListDrop_exists (codeLift dlist) (codeHead (n := k)) l t (t :> v)
      ((eval_codeLift_iff _ _ _ _).mpr hlist) ((eval_codeHead_iff _ _).mpr rfl)
  have hzeroL :
    Semiformula.Evalb ((0 : M) :> l :> v)
      (code (codeListDrop (codeLift dlist) (codeHead (n := k)))) :=
    by
    rw [codeListDrop_eq_dropCore, eval_comp_iff]
    refine ⟨![l, l], eval_dropCore_zero_at_value l, ?_⟩
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa using (eval_codeHead_iff (k := k) l (l :> v)).mpr rfl
    · intro j1
      refine Fin.cases ?_ (fun j2 => Fin.elim0 j2) j1
      simpa using (eval_codeLift_iff dlist l l v).mpr hlist
  have hdef :
    Σ-[1].DefinablePred
      (fun t : M =>
        Semiformula.Evalb ((0 : M) :> t :> v)
          (code (codeListDrop (codeLift dlist) (codeHead (n := k))))) :=
    definable_code_head_slot _ (0 : M) v
  obtain ⟨t₀, ht₀, hmin⟩ := InductionOnHierarchy.least_number Σ 1 hdef hzeroL
  refine ⟨t₀, ?_⟩
  rw [codeListLength_eq, eval_codeRfindPos_iff]
  refine ⟨⟨1, by simp, (eval_codeInv_iff _ _ _).mpr ⟨0, ht₀, Or.inl ⟨rfl, rfl⟩⟩⟩, ?_⟩
  intro t ht
  obtain ⟨z, hz⟩ := hdrop t
  exact (eval_codeInv_iff _ _ _).mpr ⟨z, hz, Or.inr ⟨fun h0 => hmin t ht (h0 ▸ hz), rfl⟩⟩

/-- The indexed entry has a value at any list and index values: the iterated
tail terminates, and the encoded head is eager. -/
theorem eval_codeListGetOptional_exists_of_values [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (dlist didx : Code k)
    (l i : M) (v : Fin k → M) (hlist : Semiformula.Evalb (l :> v) (code dlist))
    (hidx : Semiformula.Evalb (i :> v) (code didx)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeListGetOptional dlist didx)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨z, hz⟩ := eval_codeListDrop_exists dlist didx l i v hlist hidx
  exact eval_codeListHeadOptional_exists (codeListDrop dlist didx) z v hz

/-- Bind on an encoded option has a value once the continuation has one at the
payload of the supplied option value.

The continuation premise is needed even when the option value is zero: the
conditional evaluates both branches. -/
theorem eval_codeOptionBind_exists_of_value [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {k : ℕ} (dopt : Code k)
    (dk : Code (k + 1)) (o : M) (v : Fin k → M) (hopt : Semiformula.Evalb (o :> v) (code dopt))
    (hk : ∃ y : M, Semiformula.Evalb (y :> (o - 1) :> v) (code dk)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeOptionBind dopt dk)) :=
  by
  obtain ⟨y, hy⟩ := hk
  have hone : Semiformula.Evalb ((1 : M) :> v) (code (Code.one k)) := (eval_one_iff _ _).mpr rfl
  have hbind : Semiformula.Evalb (y :> v) (code (codeBind (codeSub dopt (Code.one k)) dk)) :=
    (eval_codeBind_iff _ _ _ _).mpr ⟨o - 1, eval_codeSub dopt (Code.one k) o 1 v hopt hone, hy⟩
  have hzero : Semiformula.Evalb ((0 : M) :> v) (code (Code.zero k)) :=
    (eval_zero_iff _ _).mpr rfl
  rw [codeOptionBind_eq]
  by_cases ho : 0 < o
  · exact ⟨y, eval_codeIfPos_of _ _ _ o y 0 y v hopt hbind hzero (Or.inl ⟨ho, rfl⟩)⟩
  · exact
      ⟨0,
        eval_codeIfPos_of _ _ _ o y 0 0 v hopt hbind hzero
          (Or.inr ⟨le_antisymm (not_lt.mp ho) (by simp), rfl⟩)⟩

/-- Appending one entry has a value at any list and entry values.

The bound of the rebuilding recursion is the value of `codeListLength`, and its
step is total at every index up to and including that bound. -/
theorem eval_codeListSnoc_exists_of_values [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] {k : ℕ} (dlist dx : Code k) (l x : M)
    (v : Fin k → M) (hlist : Semiformula.Evalb (l :> v) (code dlist))
    (hx : Semiformula.Evalb (x :> v) (code dx)) :
    ∃ s : M, Semiformula.Evalb (s :> v) (code (codeListSnoc dlist dx)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨n, hn⟩ := eval_codeListLength_exists_of_value dlist l v hlist
  have hbase :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeListCons dx (codeListNil (n := k)))) :=
    eval_codeListCons_exists_of_values dx (codeListNil (n := k)) x 0 v hx
      ((eval_zero_iff _ _).mpr rfl)
  have hstep :
    ∀ i : M,
      i ≤ n →
        ∀ z : M,
          ∃ w : M,
            Semiformula.Evalb (w :> i :> z :> v)
              (code
                (codeListCons
                  (codeSub
                    (codeListGetOptional (codeLift (codeLift dlist))
                      (codeSub (codeListLength (codeLift (codeLift dlist)))
                        (codeSucc (Code.proj (0 : Fin (k + 2))))))
                    (codeConst 1))
                  (Code.proj (1 : Fin (k + 2))))) :=
    by
    intro i _ z
    have hlist2 : Semiformula.Evalb (l :> i :> z :> v) (code (codeLift (codeLift dlist))) :=
      (eval_codeLift_iff (codeLift dlist) l i (z :> v)).mpr
        ((eval_codeLift_iff dlist l z v).mpr hlist)
    obtain ⟨n', hn'⟩ :=
      eval_codeListLength_exists_of_value (codeLift (codeLift dlist)) l (i :> z :> v) hlist2
    have hsucc :
      Semiformula.Evalb ((i + 1) :> i :> z :> v)
        (code (codeSucc (Code.proj (0 : Fin (k + 2))))) :=
      (eval_codeSucc_iff _ _ _).mpr ⟨i, (eval_proj_iff _ _ _).mpr rfl, rfl⟩
    have hrev := eval_codeSub _ _ n' (i + 1) (i :> z :> v) hn' hsucc
    obtain ⟨g, hg⟩ :=
      eval_codeListGetOptional_exists_of_values (codeLift (codeLift dlist)) _ l (n' - (i + 1))
        (i :> z :> v) hlist2 hrev
    have hone : Semiformula.Evalb ((1 : M) :> i :> z :> v) (code (codeConst (n := k + 2) 1)) :=
      by rw [eval_codeConst_iff]; simp
    exact
      eval_codeListCons_exists_of_values _ _ (g - 1) z (i :> z :> v)
        (eval_codeSub _ _ g 1 (i :> z :> v) hg hone) ((eval_proj_iff _ _ _).mpr rfl)
  obtain ⟨s, hs⟩ := eval_codePrec_exists_of_total _ _ n v hbase hstep
  refine ⟨s, ?_⟩
  rw [codeListSnoc_eq_bind, eval_codeBind_iff]
  exact ⟨n, hn, hs⟩

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
