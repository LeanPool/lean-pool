/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Side
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.SymOrbit
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.WPop

/-!
# Eliminating independent variables

Some variables never occur together in the associativity condition of a quadruple (for instance
the variables `a ≤ a * a` of the symmetric atoms `a`). Given the other variables, the conditions
on such variables are independent of each other, so the number of their admissible values is a
product, and they need not be dimensions of the truth tables.

`leafE P b m qm ow α` computes `P.leaf (b + m) α` with tables of `2 ^ b` bits: the variables
`b, …, b + m - 1` are eliminated. The quadruples not depending on them (`qm`) give the table of
admissible assignments of the first `b` variables. For the `i`-th eliminated variable, the
quadruples `ow[i]` depending on it are evaluated for both of its values, which gives the tables
of assignments for which it is forced (`F`) or free (`R`). The tables `E j` of the assignments
with exactly `j` free variables are maintained by `stepE0`, and the result is
`∑ j, 2 ^ j * popcount (E j)` (`wtotF`).
-/

@[expose] public section

namespace RACert

/-- Membership in a list of numbers, as a Boolean. -/
def elemN (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => Nat.beq x y || elemN x ys

theorem elemN_spec {x : ℕ} : ∀ {l : List ℕ}, elemN x l = true → x ∈ l
  | y :: ys, h => by
    rw [elemN, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with h | h
    · rw [h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (elemN_spec h)
  | [], h => by simp [elemN] at h

/-- Counting assignments is summing an indicator over their codes. -/
theorem card_filter_fun_eq_sum (b : ℕ) (f : (Fin b → Bool) → Bool) :
    (Finset.univ.filter fun w : Fin b → Bool => f w = true).card =
      ∑ β ∈ Finset.range (2 ^ b), (f fun i : Fin b => β.testBit i).toNat := by
  let x : ℕ := Nat.ofBits fun p : Fin (2 ^ b) => f fun i : Fin b => p.val.testBit i
  have hx : x < 2 ^ 2 ^ b := Nat.ofBits_lt_two_pow _
  have hbit : ∀ p < 2 ^ b, x.testBit p = f fun i : Fin b => p.testBit i := fun p hp =>
    Nat.testBit_ofBits_lt _ p hp
  rw [← popcount_eq_card_filter_fun hx f hbit, popcount_eq hx, Finset.card_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hbit p (Finset.mem_range.mp hp)]
  cases f fun i : Fin b => p.testBit i <;> rfl

/-- Splitting the low variables of an assignment. -/
theorem joinN_split {b m α β ζ : ℕ} (hβ : β < 2 ^ b) (hζ : ζ < 2 ^ m) :
    joinN (b + m) α (β + 2 ^ b * ζ) = joinN b (ζ + 2 ^ m * α) β := by
  funext j
  simp only [joinN]
  rw [testBit_add_two_pow_mul hβ]
  by_cases hj : j < b
  · have hj' : j < b + m := by omega
    simp only [hj, hj', ite_true]
  · rw [testBit_add_two_pow_mul hζ]
    by_cases hj' : j < b + m
    · have : j - b < m := by omega
      simp only [hj, hj', this, ite_true, ite_false]
    · have : ¬ j - b < m := by omega
      simp only [hj, hj', this, ite_false]
      congr 1
      omega

/-- The value `0` or `2 ^ i` of the eliminated variables for the tag `o`: `0` for a quadruple
depending on none of them, `i + 1` for a quadruple depending on the `i`-th. -/
def pOf : ℕ → ℕ
  | 0 => 0
  | i + 1 => Nat.pow 2 i

/-- The masks of the entry `e` select no eliminated variable other than the one of the tag `o`. -/
def ownOK (m o : ℕ) (e : ℕ × ℕ × ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.lor e.2.1 e.2.2) (Nat.xor (Nat.sub (Nat.pow 2 m) 1) (pOf o))) 0

/-- The values of the eliminated variables relevant for the tag `o`. -/
def restr (o ζ : ℕ) : ℕ :=
  match o with
  | 0 => 0
  | i + 1 => bif ζ.testBit i then 2 ^ i else 0

theorem restr_lt {m o ζ : ℕ} (ho : o ≤ m) : restr o ζ < 2 ^ m := by
  match o with
  | 0 => exact Nat.pow_pos (by decide)
  | i + 1 =>
    rw [restr]
    cases ζ.testBit i
    · exact Nat.pow_pos (by decide)
    · exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem land_restr {m o ζ α : ℕ} {e : ℕ × ℕ × ℕ} (ho : o ≤ m) (hζ : ζ < 2 ^ m)
    (h : ownOK m o e = true) :
    Nat.land (ζ + 2 ^ m * α) e.2.1 = Nat.land (restr o ζ + 2 ^ m * α) e.2.1 ∧
      Nat.land (ζ + 2 ^ m * α) e.2.2 = Nat.land (restr o ζ + 2 ^ m * α) e.2.2 := by
  rw [ownOK, Nat.beq_eq] at h
  have key : ∀ j, (e.2.1.testBit j = true ∨ e.2.2.testBit j = true) →
      (ζ + 2 ^ m * α).testBit j = (restr o ζ + 2 ^ m * α).testBit j := by
    intro j hj
    have h1 := congrArg (fun x => Nat.testBit x j) h
    simp only [testBit_land, testBit_lor, testBit_xor, Nat.zero_testBit] at h1
    have hor : (e.2.1.testBit j || e.2.2.testBit j) = true := by
      rcases hj with hj | hj <;> simp [hj]
    rw [hor, Bool.true_and] at h1
    have hm : (Nat.sub (Nat.pow 2 m) 1).testBit j = decide (j < m) :=
      Nat.testBit_two_pow_sub_one m j
    rw [hm] at h1
    rw [testBit_add_two_pow_mul hζ, testBit_add_two_pow_mul (restr_lt ho)]
    match o with
    | 0 =>
      have : ¬ j < m := by simpa [pOf] using h1
      simp only [this, ite_false]
    | i + 1 =>
      have hp : (pOf (i + 1)).testBit j = decide (i = j) := Nat.testBit_two_pow
      rw [hp] at h1
      by_cases hjm : j < m
      · have hij : i = j := by simpa [hjm] using h1
        subst hij
        simp only [hjm, ite_true, restr]
        cases hb : ζ.testBit i
        · simp
        · simp
      · simp only [hjm, ite_false]
  constructor
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_land, testBit_land]
    cases hb : e.2.1.testBit j
    · simp
    · rw [key j (Or.inl hb)]
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_land, testBit_land]
    cases hb : e.2.2.testBit j
    · simp
    · rw [key j (Or.inr hb)]

/-- A binary tree of quadruples with their two sides; every inner node carries masks of the high
variables of its two subtrees. -/
inductive QTree where
  | leaf (x : ℕ) (sl sr : Side)
  | node (ml : ℕ) (l : QTree) (mr : ℕ) (r : QTree)

namespace QTree

/-- The high variables on which the tree is evaluated. -/
def mask : QTree → ℕ
  | leaf _ sl sr => Nat.lor sl.1 sr.1
  | node ml _ mr _ => Nat.lor ml mr

/-- The masks of the inner nodes contain the masks of their subtrees. -/
def wf : QTree → Bool
  | leaf _ _ _ => true
  | node ml l mr r =>
    Nat.beq (Nat.land ml l.mask) l.mask && Nat.beq (Nat.land mr r.mask) r.mask && l.wf && r.wf

/-- The quadruples of the tree, with the masks of their two sides. -/
def entries : QTree → List (ℕ × ℕ × ℕ)
  | leaf x sl sr => [(x, sl.1, sr.1)]
  | node _ l _ r => l.entries ++ r.entries

end QTree

namespace Problem

variable (P : Problem)

/-- The two sides of the condition of the quadruple with code `x` are the same pair of rows, so
that the condition holds for every assignment. -/
noncomputable def trivQuad (x : ℕ) : Bool :=
  (listBeq (nth [] (nth [] P.cls (cvN P.s (x / P.k / P.k / P.k % P.k))) (x % P.k))
        (nth [] (nth [] P.cls (x / P.k / P.k / P.k % P.k)) (x / P.k / P.k % P.k)) &&
      listBeq (nth [] (nth [] P.cls (x / P.k / P.k % P.k)) (x / P.k % P.k))
        (nth [] (nth [] P.cls (x % P.k)) (cvN P.s (x / P.k % P.k)))) ||
    (listBeq (nth [] (nth [] P.cls (cvN P.s (x / P.k / P.k / P.k % P.k))) (x % P.k))
        (nth [] (nth [] P.cls (x % P.k)) (cvN P.s (x / P.k % P.k))) &&
      listBeq (nth [] (nth [] P.cls (x / P.k / P.k % P.k)) (x / P.k % P.k))
        (nth [] (nth [] P.cls (x / P.k / P.k / P.k % P.k)) (x / P.k / P.k % P.k)))

variable {P}

theorem dotB_tbl_congr {v : ℕ → Bool} {a b c d a' b' c' d' : ℕ}
    (h₁ : nth [] (nth [] P.cls a) b = nth [] (nth [] P.cls a') b')
    (h₂ : nth [] (nth [] P.cls c) d = nth [] (nth [] P.cls c') d') :
    dotB P.k (P.tbl v) a b c d = dotB P.k (P.tbl v) a' b' c' d' := by
  simp only [dotB, tbl, clsAt, h₁, h₂]

theorem quadAt_of_trivQuad {x : ℕ} (h : P.trivQuad x = true) (v : ℕ → Bool) :
    P.quadAt v x = true := by
  rw [trivQuad, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rw [quadAt, quadB, beq_iff_eq]
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact dotB_tbl_congr (listBeq_eq h₁) (listBeq_eq h₂)
  · rw [dotB_symm (X := P.tbl v) (x / P.k / P.k / P.k % P.k)]
    exact dotB_tbl_congr (listBeq_eq h₁) (listBeq_eq h₂)

/-- Every condition holds in a model, whether its quadruple is listed or not. -/
theorem quadAt_of_phi (hcheck : P.check = true) {v : ℕ → Bool} (hv : P.phi v = true) (x : ℕ) :
    P.quadAt v x = true := by
  have hk := numAtoms_pos P.s P.n
  have hm : ∀ y, y % P.k < P.k := fun y => Nat.mod_lt _ hk
  exact quadB_of_phi hcheck hv (hm _) (hm _) (hm _) (hm _)

/-- The condition of the entry `q = (x, m₁, m₂)` only depends on the high variables selected by
its masks. -/
def MaskDep (P : Problem) (b : ℕ) (q : ℕ × ℕ × ℕ) : Prop :=
  ∀ α₁ α₂ β, β < 2 ^ b → Nat.land α₁ q.2.1 = Nat.land α₂ q.2.1 →
    Nat.land α₁ q.2.2 = Nat.land α₂ q.2.2 →
    P.quadAt (joinN b α₁ β) q.1 = P.quadAt (joinN b α₂ β) q.1

theorem maskDep_of_cov (hrows : P.checkRows = true) {b : ℕ} {e : ℕ × ℕ × ℕ}
    (hcov : P.coversQuad b e = true) : MaskDep P b e := by
  intro α₁ α₂ β hβ h₁ h₂
  obtain ⟨a₁, a₂⟩ := dotR_land (α := α₁) hcov
  obtain ⟨c₁, c₂⟩ := dotR_land (α := α₂) hcov
  have hq : P.quadD (top b) (ones b) b (krowsOf b α₁ P.cls) e.1 0 =
      P.quadD (top b) (ones b) b (krowsOf b α₂ P.cls) e.1 0 := by
    rw [quadD_eq_dotR, quadD_eq_dotR, ← a₁, ← a₂, ← c₁, ← c₂, h₁, h₂]
  have s₁ := (quadD_spec hrows (α := α₁) hβ e.1 (top_pos b)).2
  have s₂ := (quadD_spec hrows (α := α₂) hβ e.1 (top_pos b)).2
  rw [hq, s₂] at s₁
  simpa using s₁.symm

/-- The condition of an entry with tag `o` only depends on the eliminated variable of `o`. -/
theorem quadAt_restr {b m o ζ α β : ℕ} (hβ : β < 2 ^ b)
    (ho : o ≤ m) (hζ : ζ < 2 ^ m) {e : ℕ × ℕ × ℕ} (hdep : MaskDep P b e)
    (hown : ownOK m o e = true) :
    P.quadAt (joinN b (ζ + 2 ^ m * α) β) e.1 =
      P.quadAt (joinN b (restr o ζ + 2 ^ m * α) β) e.1 := by
  obtain ⟨h₁, h₂⟩ := land_restr (α := α) ho hζ hown
  exact hdep _ _ β hβ h₁ h₂

theorem dotB_eq_zip (hrows : P.checkRows = true) (v : ℕ → Bool) {a₁ b₁ a₂ b₂ : ℕ}
    (ha₁ : a₁ < P.k) (hb₁ : b₁ < P.k) (ha₂ : a₂ < P.k) (hb₂ : b₂ < P.k) :
    dotB P.k (P.tbl v) a₁ b₁ a₂ b₂ =
      ((nth [] (nth [] P.cls a₁) b₁).zip (nth [] (nth [] P.cls a₂) b₂)).any
        fun p => litB v p.1 && litB v p.2 := by
  rw [zip_any_eq_range (litB v) P.k _ _ (checkRows_spec hrows ha₁ hb₁)
    (checkRows_spec hrows ha₂ hb₂)]
  rfl

variable (P)

/-- The sides `sl`, `sr` are the classifications of the two sides of the condition of the
quadruple with code `x`. -/
noncomputable def checkLeaf (b x : ℕ) (sl sr : Side) : Bool :=
  Nat.ble b 64 &&
    (checkSide b sl
        (nth [] (nth [] P.cls (cvN P.s (x / P.k / P.k / P.k % P.k))) (x % P.k))
        (nth [] (nth [] P.cls (x / P.k / P.k % P.k)) (x / P.k % P.k)) &&
      checkSide b sr
        (nth [] (nth [] P.cls (x / P.k / P.k / P.k % P.k)) (x / P.k / P.k % P.k))
        (nth [] (nth [] P.cls (x % P.k)) (cvN P.s (x / P.k % P.k))))

/-- All leaves of the tree are valid. -/
noncomputable def leavesOK (b : ℕ) : QTree → Bool
  | .leaf x sl sr => P.checkLeaf b x sl sr
  | .node _ l _ r => leavesOK b l && leavesOK b r

variable {P}

/-- The condition of a quadruple in terms of its two classified sides. -/
theorem quadAt_eq_sides (hrows : P.checkRows = true) {b x : ℕ} {sl sr : Side}
    (h : P.checkLeaf b x sl sr = true) (α β : ℕ) :
    sideWF b sl = true ∧ sideWF b sr = true ∧
      P.quadAt (joinN b α β) x = (sideSem sl.2 α β == sideSem sr.2 α β) := by
  have hk := numAtoms_pos P.s P.n
  have hm : ∀ y, y % P.k < P.k := fun y => Nat.mod_lt _ hk
  rw [checkLeaf, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨hb, hl, hr⟩ := h
  obtain ⟨wl, el⟩ := checkSide_spec hl
  obtain ⟨wr, er⟩ := checkSide_spec hr
  refine ⟨wl, wr, ?_⟩
  rw [el, er, classify_sem hb, classify_sem hb, quadAt, quadB,
    dotB_eq_zip hrows _ (cvN_lt (hm (x / P.k / P.k / P.k))) (hm x) (hm (x / P.k / P.k))
      (hm (x / P.k)),
    dotB_eq_zip hrows _ (hm (x / P.k / P.k / P.k)) (hm (x / P.k / P.k)) (hm x)
      (cvN_lt (hm (x / P.k)))]

theorem maskDep_of_leaf (hrows : P.checkRows = true) {b x : ℕ} {sl sr : Side}
    (h : P.checkLeaf b x sl sr = true) : MaskDep P b (x, sl.1, sr.1) := by
  intro α₁ α₂ β _ h₁ h₂
  obtain ⟨wl, wr, e₁⟩ := quadAt_eq_sides hrows h α₁ β
  obtain ⟨-, -, e₂⟩ := quadAt_eq_sides hrows h α₂ β
  change P.quadAt (joinN b α₁ β) x = P.quadAt (joinN b α₂ β) x
  rw [e₁, e₂, sideSem_congr wl h₁, sideSem_congr wr h₂]

theorem maskDep_of_leavesOK (hrows : P.checkRows = true) {b : ℕ} : ∀ (t : QTree),
    P.leavesOK b t = true → ∀ q ∈ t.entries, MaskDep P b q
  | .leaf x sl sr, h, q, hq => by
    rw [QTree.entries, List.mem_singleton] at hq
    rw [hq]
    exact maskDep_of_leaf hrows h
  | .node _ l _ r, h, q, hq => by
    rw [leavesOK, Bool.and_eq_true] at h
    rw [QTree.entries, List.mem_append] at hq
    rcases hq with hq | hq
    · exact maskDep_of_leavesOK hrows l h.1 q hq
    · exact maskDep_of_leavesOK hrows r h.2 q hq

/-- A leaf with eliminated variables as a sum over the tables of the remaining low variables. -/
theorem leaf_split (hrows : P.checkRows = true) {b m α : ℕ} (hα : α < 2 ^ (P.V - (b + m))) :
    P.leaf (b + m) α = ∑ β ∈ Finset.range (2 ^ b), ∑ ζ ∈ Finset.range (2 ^ m),
      (P.phi (joinN b (ζ + 2 ^ m * α) β)).toNat := by
  rw [leaf_eq hrows hα, card_filter_fun_eq_sum (b + m) fun w => P.phi (join (b + m) α w),
    sum_range_two_pow_add, Finset.sum_comm]
  refine Finset.sum_congr rfl fun β hβ => Finset.sum_congr rfl fun ζ hζ => ?_
  rw [join_testBit, joinN_split (Finset.mem_range.mp hβ) (Finset.mem_range.mp hζ)]

/-- The violations of a condition with sides `L`, `R`, as an optional table. -/
noncomputable def neqO (on : ℕ) (L R : SVal) : Option ℕ :=
  SVal.rec (motive := fun _ => Option ℕ)
    (SVal.rec (motive := fun _ => Option ℕ) none (some on) (fun e => some (Nat.xor on e)) R)
    (SVal.rec (motive := fun _ => Option ℕ) (some on) none (fun e => some e) R)
    (fun e => SVal.rec (motive := fun _ => Option ℕ) (some (Nat.xor on e)) (some e)
      (fun e' => bif Nat.beq e e' then none else some (Nat.xor e e')) R) L

theorem neqO_spec {b β : ℕ} {L R : SVal} (hL : L.lt b) (hR : R.lt b) (hβ : β < 2 ^ b) :
    optV (neqO (ones b) L R) < top b ∧
      (optV (neqO (ones b) L R)).testBit β = (L.sem β ^^ R.sem β) := by
  have hon : (ones b).testBit β = true := by rw [testBit_ones]; simpa using hβ
  have hT := top_pos b
  have ho := ones_lt_top b
  cases L with
  | top =>
    cases R with
    | top => exact ⟨hT, by simp [neqO, optV, SVal.sem]⟩
    | zero => exact ⟨ho, by simp [neqO, optV, SVal.sem, hon]⟩
    | tab e =>
      exact ⟨xor_lt (ones_lt b) hR, by
        change (Nat.xor (ones b) e).testBit β = _
        rw [testBit_xor, hon]
        rfl⟩
  | zero =>
    cases R with
    | top => exact ⟨ho, by simp [neqO, optV, SVal.sem, hon]⟩
    | zero => exact ⟨hT, by simp [neqO, optV, SVal.sem]⟩
    | tab e => exact ⟨hR, by simp [neqO, optV, SVal.sem]⟩
  | tab e =>
    cases R with
    | top =>
      exact ⟨xor_lt (ones_lt b) hL, by
        change (Nat.xor (ones b) e).testBit β = _
        rw [testBit_xor, hon]
        simp [SVal.sem]⟩
    | zero => exact ⟨hL, by simp [neqO, optV, SVal.sem]⟩
    | tab e' =>
      change optV (bif Nat.beq e e' then none else some (Nat.xor e e')) < top b ∧
        (optV (bif Nat.beq e e' then none else some (Nat.xor e e'))).testBit β = _
      by_cases h : e = e'
      · rw [beq_true h, h]
        exact ⟨hT, by simp [optV, SVal.sem]⟩
      · rw [beq_false h]
        exact ⟨xor_lt hL hR, testBit_xor _ _ _⟩

/-- Disjunction of two optional tables. -/
noncomputable def orO2 (X Y : Option ℕ) : Option ℕ :=
  Option.rec (motive := fun _ => Option ℕ)
    (Option.rec (motive := fun _ => Option ℕ) none (fun ex => some ex) X)
    (fun ey => Option.rec (motive := fun _ => Option ℕ) (some ey)
      (fun ex => some (Nat.lor ex ey)) X) Y

theorem orO2_spec {b : ℕ} {X Y : Option ℕ} (hX : optV X < top b) (hY : optV Y < top b)
    (β : ℕ) : optV (orO2 X Y) < top b ∧
      (optV (orO2 X Y)).testBit β = ((optV X).testBit β || (optV Y).testBit β) := by
  cases X with
  | none =>
    cases Y with
    | none => exact ⟨hX, by simp [orO2, optV]⟩
    | some ey => exact ⟨hY, by simp [orO2, optV]⟩
  | some ex =>
    cases Y with
    | none => exact ⟨hX, by simp [orO2, optV]⟩
    | some ey => exact ⟨lor_lt hX hY, testBit_lor _ _ _⟩

/-- The violations of the quadruples of a tree, the high variables being given by `ρ`, as an
optional table. Every subtree is evaluated on the high variables selected by its mask only,
given as a literal, so that the kernel evaluates it once for all leaves of a declaration
agreeing on these. -/
noncomputable def violO (b on : ℕ) (t : QTree) : ℕ → Option ℕ :=
  QTree.rec (motive := fun _ => ℕ → Option ℕ)
    (fun _ sl sr ρ =>
      forceL (Nat.land ρ sl.1) fun r₁ => forceL (Nat.land ρ sr.1) fun r₂ =>
        neqO on (sideO b sl r₁) (sideO b sr r₂))
    (fun ml _ mr _ ihl ihr ρ =>
      forceL (Nat.land ρ ml) fun ρl => forceL (Nat.land ρ mr) fun ρr => orO2 (ihl ρl) (ihr ρr)) t

theorem violO_leaf (b on x : ℕ) (sl sr : Side) (ρ : ℕ) : violO b on (.leaf x sl sr) ρ =
    neqO on (sideO b sl (Nat.land ρ sl.1)) (sideO b sr (Nat.land ρ sr.1)) := rfl

theorem violO_node (b on ml mr ρ : ℕ) (l r : QTree) : violO b on (.node ml l mr r) ρ =
    orO2 (violO b on l (Nat.land ρ ml)) (violO b on r (Nat.land ρ mr)) := rfl

/-- The weights `E` multiplied by the number of admissible values of a variable which is forced
at the positions `F` and free at the positions `R`; the first table has no predecessor. -/
noncomputable def stepE0 (F R : ℕ) (E : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun e es _ => Nat.land e F :: stepE F R es e) E

theorem wsum_stepE0 {F R β : ℕ} (h : ¬ (F.testBit β = true ∧ R.testBit β = true)) :
    ∀ E : List ℕ, wsum β (stepE0 F R E) =
      ((F.testBit β).toNat + 2 * (R.testBit β).toNat) * wsum β E
  | [] => by simp [stepE0, wsum_nil]
  | e :: es => by
    change wsum β (Nat.land e F :: stepE F R es e) = _
    rw [wsum_cons, wsum_stepE h, wsum_cons, testBit_land]
    cases e.testBit β <;> cases hF : F.testBit β <;> cases hR : R.testBit β <;>
      simp [hF, hR] at h ⊢

theorem stepE0_lt {N F R : ℕ} : ∀ {E : List ℕ}, (∀ e ∈ E, e < 2 ^ N) →
    ∀ e ∈ stepE0 F R E, e < 2 ^ N
  | [], _, e, he => by simp [stepE0] at he
  | x :: xs, hE, e, he => by
    change e ∈ Nat.land x F :: stepE F R xs x at he
    rw [List.mem_cons] at he
    rcases he with he | he
    · rw [he]
      exact land_lt_left (hE x List.mem_cons_self)
    · exact stepE_lt (fun y hy => hE y (List.mem_cons_of_mem _ hy)) (hE x List.mem_cons_self)
        e he

/-- Case distinction on the violations `B₀`, `B₁` of the conditions on an eliminated variable
for its two values: the continuation `k` receives the tables of the positions at which the
variable is forced and free; `k0` is the result if the variable is free everywhere. -/
noncomputable def frK {γ : Type} (on : ℕ) (B₀ B₁ : Option ℕ) (k0 : γ) (k : ℕ → ℕ → γ) : γ :=
  Option.rec (motive := fun _ => γ)
    (Option.rec (motive := fun _ => γ) k0 (fun e₁ => k e₁ (Nat.xor on e₁)) B₁)
    (fun e₀ => Option.rec (motive := fun _ => γ) (k e₀ (Nat.xor on e₀))
      (fun e₁ => k (Nat.xor e₀ e₁) (Nat.xor on (Nat.lor e₀ e₁))) B₁) B₀

/-- The weights `E` multiplied by the number of admissible values of an eliminated variable. -/
noncomputable def frL (on : ℕ) (B₀ B₁ : Option ℕ) (E : List ℕ) : List ℕ :=
  frK on B₀ B₁ (0 :: E) (fun F R => stepE0 F R E)

theorem frK_map {γ : Type} (on : ℕ) (B₀ B₁ : Option ℕ) (E : List ℕ) (f : List ℕ → γ) :
    frK on B₀ B₁ (f (0 :: E)) (fun F R => f (stepE0 F R E)) = f (frL on B₀ B₁ E) := by
  cases B₀ <;> cases B₁ <;> rfl

theorem frL_spec {b β : ℕ} (hβ : β < 2 ^ b) {B₀ B₁ : Option ℕ} (h₀ : optV B₀ < top b)
    (h₁ : optV B₁ < top b) {E : List ℕ} (hE : ∀ e ∈ E, e < 2 ^ 2 ^ b) :
    (∀ e ∈ frL (ones b) B₀ B₁ E, e < 2 ^ 2 ^ b) ∧
      wsum β (frL (ones b) B₀ B₁ E) =
        ((!(optV B₀).testBit β).toNat + (!(optV B₁).testBit β).toNat) * wsum β E := by
  have hon : (ones b).testBit β = true := by rw [testBit_ones]; simpa using hβ
  cases B₀ with
  | none =>
    cases B₁ with
    | none =>
      refine ⟨?_, ?_⟩
      · intro e he
        change e ∈ 0 :: E at he
        rw [List.mem_cons] at he
        rcases he with he | he
        · rw [he]
          exact Nat.pow_pos (by decide)
        · exact hE e he
      · change wsum β (0 :: E) = _
        rw [wsum_cons]
        simp [optV]
    | some e₁ =>
      refine ⟨stepE0_lt hE, ?_⟩
      change wsum β (stepE0 e₁ (Nat.xor (ones b) e₁) E) = _
      rw [wsum_stepE0 (by rw [testBit_xor, hon]; cases e₁.testBit β <;> simp), testBit_xor, hon]
      cases h1 : e₁.testBit β <;> simp [optV, h1]
  | some e₀ =>
    cases B₁ with
    | none =>
      refine ⟨stepE0_lt hE, ?_⟩
      change wsum β (stepE0 e₀ (Nat.xor (ones b) e₀) E) = _
      rw [wsum_stepE0 (by rw [testBit_xor, hon]; cases e₀.testBit β <;> simp), testBit_xor, hon]
      cases h0 : e₀.testBit β <;> simp [optV, h0]
    | some e₁ =>
      refine ⟨stepE0_lt hE, ?_⟩
      change wsum β (stepE0 (Nat.xor e₀ e₁) (Nat.xor (ones b) (Nat.lor e₀ e₁)) E) = _
      rw [wsum_stepE0 (by
        rw [testBit_xor, testBit_xor, testBit_lor, hon]
        cases e₀.testBit β <;> cases e₁.testBit β <;> simp), testBit_xor, testBit_xor,
        testBit_lor, hon]
      cases h0 : e₀.testBit β <;> cases h1 : e₁.testBit β <;> simp [optV, h0, h1]

variable (P)

/-- The tree `t` is valid for the tag `o`. -/
noncomputable def checkTree (b m o : ℕ) (t : QTree) : Bool :=
  t.wf && (P.leavesOK b t && t.entries.all (ownOK m o))

/-- The trees `ow` are valid for the eliminated variables `i, i + 1, …, m - 1`. -/
noncomputable def checkOw (b m : ℕ) : ℕ → List QTree → Bool
  | i, [] => Nat.beq i m
  | i, t :: ow => P.checkTree b m (i + 1) t && checkOw b m (i + 1) ow

/-- The certificate for the elimination of the variables `b, …, b + m - 1`: the tree `qt` lists
quadruples not depending on them, the `i`-th tree of `ow` lists quadruples depending on the
`i`-th only, and every other quadruple of the problem has a trivial condition. -/
noncomputable def checkElim (b m : ℕ) (qt : QTree) (ow : List QTree) : Bool :=
  P.checkTree b m 0 qt && (P.checkOw b m 0 ow &&
    P.quads.all fun x => P.trivQuad x ||
      elemN x ((qt.entries ++ (ow.map QTree.entries).flatten).map Prod.fst))

/-- Multiply the weights `E` by the numbers of admissible values of the eliminated variables of
the trees `ow`; `p` is the power of two of the first of them. -/
noncomputable def elimK (b on α : ℕ) (ow : List QTree) : ℕ → List ℕ → (List ℕ → ℕ) → ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ → (List ℕ → ℕ) → ℕ) (fun _ E k => k E)
    (fun t _ ih p E k =>
      forceL (Nat.land α t.mask) fun r₀ =>
        forceL (Nat.land (Nat.add p α) t.mask) fun r₁ =>
          frK on (violO b on t r₀) (violO b on t r₁) (ih (Nat.add p p) (0 :: E) k)
            (fun F R => ih (Nat.add p p) (stepE0 F R E) k)) ow

/-- The weights passed on by `elimK`. -/
noncomputable def elimL (b on α : ℕ) : List QTree → ℕ → List ℕ → List ℕ
  | [], _, E => E
  | t :: ow, p, E =>
    elimL b on α ow (p + p)
      (frL on (violO b on t (Nat.land α t.mask)) (violO b on t (Nat.land (p + α) t.mask)) E)

theorem elimK_eq (b on α : ℕ) (ow : List QTree) (p : ℕ) (E : List ℕ) (k : List ℕ → ℕ) :
    elimK b on α ow p E k = k (elimL b on α ow p E) := by
  induction ow generalizing p E with
  | nil => rfl
  | cons t ow ih =>
    change frK on (violO b on t (Nat.land α t.mask)) (violO b on t (Nat.land (Nat.add p α) t.mask))
      (elimK b on α ow (Nat.add p p) (0 :: E) k)
      (fun F R => elimK b on α ow (Nat.add p p) (stepE0 F R E) k) = _
    rw [ih, show (fun F R => elimK b on α ow (Nat.add p p) (stepE0 F R E) k) =
      fun F R => k (elimL b on α ow (Nat.add p p) (stepE0 F R E)) from
        funext fun F => funext fun R => ih _ _]
    exact frK_map on _ _ E fun L => k (elimL b on α ow (Nat.add p p) L)

/-- The table of the positions not violating the conditions with violations `B`. -/
noncomputable def gOf (on : ℕ) (B : Option ℕ) : ℕ :=
  Option.rec (motive := fun _ => ℕ) on (fun e => Nat.xor on e) B

theorem gOf_eq (on : ℕ) (B : Option ℕ) : gOf on B = Nat.xor on (optV B) := by
  cases B with
  | none => exact (Nat.xor_zero on).symm
  | some e => rfl

/-- The number of models whose variables `b + m, …` are given by `α`, computed with tables of
`2 ^ b` bits by eliminating the variables `b, …, b + m - 1`. -/
noncomputable def leafE (b m : ℕ) (qt : QTree) (ow : List QTree) (α : ℕ) : ℕ :=
  forceL (Nat.mul (Nat.pow 2 m) α) fun α₀ =>
    elimK b (ones b) α₀ ow 1 [gOf (ones b) (violO b (ones b) qt α₀)] fun E => wtotF b E

variable {P}

/-- All conditions of the entries hold when the eliminated variables are given by `c`. -/
noncomputable def blkOK (P : Problem) (b m α β c : ℕ) (blk : List (ℕ × ℕ × ℕ)) : Bool :=
  blk.all fun e => P.quadAt (joinN b (c + 2 ^ m * α) β) e.1

/-- The product of the numbers of admissible values of the eliminated variables. -/
noncomputable def prodOw (P : Problem) (b m α β : ℕ) : ℕ → List QTree → ℕ
  | _, [] => 1
  | i, t :: ow =>
    ((blkOK P b m α β 0 t.entries).toNat + (blkOK P b m α β (2 ^ i) t.entries).toNat) *
      prodOw P b m α β (i + 1) ow

theorem badS_zero (q : ℕ) : badS 0 q = q := by
  unfold badS
  by_cases h : q = 0
  · rw [beq_true h, h]
    rfl
  · rw [beq_false h]
    rfl

theorem land_lor_left (a c : ℕ) : Nat.land (Nat.lor a c) a = a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_land, testBit_lor]
  cases a.testBit j <;> simp

theorem land_lor_right (a c : ℕ) : Nat.land (Nat.lor a c) c = c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_land, testBit_lor]
  cases c.testBit j <;> simp

theorem land_land_self (x M : ℕ) : Nat.land (Nat.land x M) M = Nat.land x M := by
  change (x &&& M) &&& M = x &&& M
  rw [Nat.and_assoc, Nat.and_self]

theorem violO_spec (hrows : P.checkRows = true) {b α β : ℕ} (hβ : β < 2 ^ b) :
    ∀ (t : QTree), t.wf = true → P.leavesOK b t = true →
      ∀ ρ, Nat.land ρ t.mask = Nat.land α t.mask →
      optV (violO b (ones b) t ρ) < top b ∧ (optV (violO b (ones b) t ρ)).testBit β =
        t.entries.any fun q => !P.quadAt (joinN b α β) q.1
  | .leaf x sl sr, _, hleaf, ρ, hρ => by
    obtain ⟨wl, wr, hq⟩ := quadAt_eq_sides hrows hleaf α β
    obtain ⟨l1, l2⟩ := sideO_spec wl hβ (Nat.land ρ sl.1)
    obtain ⟨r1, r2⟩ := sideO_spec wr hβ (Nat.land ρ sr.1)
    obtain ⟨n1, n2⟩ := neqO_spec l1 r1 hβ
    have el : sideSem sl.2 (Nat.land ρ sl.1) β = sideSem sl.2 α β :=
      sideSem_congr wl ((land_land_self ρ sl.1).trans
        (land_of_sub hρ (land_lor_left sl.1 sr.1))) β
    have er : sideSem sr.2 (Nat.land ρ sr.1) β = sideSem sr.2 α β :=
      sideSem_congr wr ((land_land_self ρ sr.1).trans
        (land_of_sub hρ (land_lor_right sl.1 sr.1))) β
    rw [violO_leaf]
    refine ⟨n1, ?_⟩
    rw [n2, l2, r2, el, er, QTree.entries, List.any_cons, List.any_nil, Bool.or_false, hq]
    cases sideSem sl.2 α β <;> cases sideSem sr.2 α β <;> rfl
  | .node ml l mr r, hwf, hleaf, ρ, hρ => by
    rw [QTree.wf, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq,
      Nat.beq_eq] at hwf
    obtain ⟨⟨⟨hl, hr⟩, hwl⟩, hwr⟩ := hwf
    rw [leavesOK, Bool.and_eq_true] at hleaf
    have hρl : Nat.land (Nat.land ρ ml) l.mask = Nat.land α l.mask := by
      have h1 : Nat.land ρ ml = Nat.land α ml := land_of_sub hρ (land_lor_left ml mr)
      change (ρ &&& ml) &&& l.mask = α &&& l.mask
      rw [show ρ &&& ml = α &&& ml from h1, Nat.and_assoc]
      exact congrArg (α &&& ·) hl
    have hρr : Nat.land (Nat.land ρ mr) r.mask = Nat.land α r.mask := by
      have h1 : Nat.land ρ mr = Nat.land α mr := land_of_sub hρ (land_lor_right ml mr)
      change (ρ &&& mr) &&& r.mask = α &&& r.mask
      rw [show ρ &&& mr = α &&& mr from h1, Nat.and_assoc]
      exact congrArg (α &&& ·) hr
    obtain ⟨a1, a2⟩ := violO_spec hrows hβ l hwl hleaf.1 _ hρl
    obtain ⟨c1, c2⟩ := violO_spec hrows hβ r hwr hleaf.2 _ hρr
    obtain ⟨g1, g2⟩ := orO2_spec a1 c1 β
    rw [violO_node]
    refine ⟨g1, ?_⟩
    rw [g2, a2, c2, QTree.entries, List.any_append]

theorem violO_bit (hrows : P.checkRows = true) {b m o α β c : ℕ} (hβ : β < 2 ^ b) {t : QTree}
    (h : P.checkTree b m o t = true) {ρ : ℕ}
    (hρ : Nat.land ρ t.mask = Nat.land (c + 2 ^ m * α) t.mask) :
    optV (violO b (ones b) t ρ) < top b ∧
      (optV (violO b (ones b) t ρ)).testBit β = !blkOK P b m α β c t.entries := by
  rw [checkTree, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := violO_spec hrows (α := c + 2 ^ m * α) hβ t h.1 h.2.1 ρ hρ
  refine ⟨h1, ?_⟩
  rw [h2, blkOK, Bool.eq_iff_iff]
  simp [List.any_eq_true]

theorem elimL_spec (hrows : P.checkRows = true) {b m α β : ℕ} (hβ : β < 2 ^ b) :
    ∀ {ow : List QTree} {i : ℕ} {E : List ℕ}, P.checkOw b m i ow = true →
      (∀ e ∈ E, e < 2 ^ 2 ^ b) →
      (∀ e ∈ elimL b (ones b) (2 ^ m * α) ow (2 ^ i) E, e < 2 ^ 2 ^ b) ∧
        wsum β (elimL b (ones b) (2 ^ m * α) ow (2 ^ i) E) =
          wsum β E * prodOw P b m α β i ow
  | [], i, E, _, hE => ⟨hE, by rw [elimL, prodOw, Nat.mul_one]⟩
  | t :: ow, i, E, h, hE => by
    rw [checkOw, Bool.and_eq_true] at h
    obtain ⟨hb0, hq0⟩ := violO_bit hrows (α := α) (c := 0) hβ h.1
      (ρ := Nat.land (2 ^ m * α) t.mask) (by rw [Nat.zero_add]; exact land_land_self _ _)
    obtain ⟨hb1, hq1⟩ := violO_bit hrows (α := α) (c := 2 ^ i) hβ h.1
      (ρ := Nat.land (2 ^ i + 2 ^ m * α) t.mask) (land_land_self _ _)
    obtain ⟨hE', hw⟩ := frL_spec hβ hb0 hb1 hE
    have hpp : 2 ^ i + 2 ^ i = 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
    obtain ⟨g1, g2⟩ := elimL_spec hrows hβ h.2 hE'
    rw [elimL, hpp]
    refine ⟨g1, ?_⟩
    rw [g2, hw, hq0, hq1, prodOw, Bool.not_not, Bool.not_not]
    ring

/-- A tree with one constant condition, as a default value. -/
def QTree.triv : QTree := .leaf 0 (0, [], []) (0, [], [])

/-- The admissible values of the `j`-th eliminated variable. -/
noncomputable def owQ (P : Problem) (b m α β : ℕ) (ow : List QTree) (j : ℕ) (c : Bool) : Bool :=
  blkOK P b m α β (bif c then 2 ^ j else 0) (nth QTree.triv ow j).entries

theorem prodOw_eq (b m α β : ℕ) : ∀ (ow : List QTree) (i : ℕ),
    prodOw P b m α β i ow = ∏ j ∈ Finset.range ow.length,
      ((blkOK P b m α β 0 (nth QTree.triv ow j).entries).toNat +
        (blkOK P b m α β (2 ^ (i + j)) (nth QTree.triv ow j).entries).toNat)
  | [], i => rfl
  | t :: ow, i => by
    rw [prodOw, prodOw_eq b m α β ow (i + 1), List.length_cons, Finset.prod_range_succ']
    simp only [nth_cons_zero, nth_cons_succ, Nat.add_zero]
    rw [Nat.mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show i + 1 + j = i + (j + 1) by omega]

theorem cnt_eq_prod (Q : ℕ → Bool → Bool) (m : ℕ) :
    cnt Q m = ∏ j ∈ Finset.range m, ((Q j false).toNat + (Q j true).toNat) := by
  induction m with
  | zero => rw [cnt_zero, Finset.prod_range_zero]
  | succ m ih => rw [cnt_succ, ih, Finset.prod_range_succ]

theorem checkOw_length {b m : ℕ} : ∀ {ow : List QTree} {i : ℕ},
    P.checkOw b m i ow = true → i + ow.length = m
  | [], i, h => by
    rw [checkOw, Nat.beq_eq] at h
    simpa using h
  | t :: ow, i, h => by
    rw [checkOw, Bool.and_eq_true] at h
    have := checkOw_length h.2
    rw [List.length_cons]
    omega

theorem checkOw_nth {b m : ℕ} : ∀ {ow : List QTree} {i : ℕ},
    P.checkOw b m i ow = true →
      ∀ j < ow.length, P.checkTree b m (i + j + 1) (nth QTree.triv ow j) = true
  | [], _, _, j, hj => by simp at hj
  | t :: ow, i, h, j, hj => by
    rw [checkOw, Bool.and_eq_true] at h
    match j with
    | 0 => exact h.1
    | j + 1 =>
      have := checkOw_nth h.2 j (by simpa using hj)
      rw [nth_cons_succ, show i + (j + 1) + 1 = i + 1 + j + 1 by omega]
      exact this

/-- The models with given remaining variables, in terms of the eliminated variables. -/
theorem phi_iff_elim (hcheck : P.check = true) (hrows : P.checkRows = true) {b m : ℕ}
    {qt : QTree} {ow : List QTree} (hel : P.checkElim b m qt ow = true) {α β ζ : ℕ}
    (hβ : β < 2 ^ b) (hζ : ζ < 2 ^ m) :
    P.phi (joinN b (ζ + 2 ^ m * α) β) = true ↔
      blkOK P b m α β 0 qt.entries = true ∧
        ∀ j < m, owQ P b m α β ow j (ζ.testBit j) = true := by
  rw [checkElim, Bool.and_eq_true, Bool.and_eq_true] at hel
  obtain ⟨hqm, how, hquads⟩ := hel
  have hlen := checkOw_length how
  rw [Nat.zero_add] at hlen
  rw [checkTree, Bool.and_eq_true, Bool.and_eq_true] at hqm
  -- the conditions of the entries, transported to the restricted assignments
  have hq : ∀ q ∈ qt.entries, P.quadAt (joinN b (ζ + 2 ^ m * α) β) q.1 =
      P.quadAt (joinN b (0 + 2 ^ m * α) β) q.1 := by
    intro q hq
    exact quadAt_restr hβ (Nat.zero_le m) hζ (maskDep_of_leavesOK hrows qt hqm.2.1 q hq)
      (List.all_eq_true.mp hqm.2.2 q hq)
  have ho : ∀ j < m, ∀ q ∈ (nth QTree.triv ow j).entries,
      P.quadAt (joinN b (ζ + 2 ^ m * α) β) q.1 =
        P.quadAt (joinN b ((bif ζ.testBit j then 2 ^ j else 0) + 2 ^ m * α) β) q.1 := by
    intro j hj q hq
    have h1 := checkOw_nth how j (by omega)
    rw [Nat.zero_add, checkTree, Bool.and_eq_true, Bool.and_eq_true] at h1
    exact quadAt_restr hβ (show j + 1 ≤ m by omega) hζ
      (maskDep_of_leavesOK hrows _ h1.2.1 q hq) (List.all_eq_true.mp h1.2.2 q hq)
  constructor
  · intro hphi
    have hall := quadAt_of_phi hcheck hphi
    refine ⟨?_, fun j hj => ?_⟩
    · rw [blkOK, List.all_eq_true]
      intro q hq'
      rw [← hq q hq']
      exact hall q.1
    · rw [owQ, blkOK, List.all_eq_true]
      intro q hq'
      rw [← ho j hj q hq']
      exact hall q.1
  · rintro ⟨hG, hQ⟩
    rw [phi, List.all_eq_true]
    intro x hx
    have hx' := List.all_eq_true.mp hquads x hx
    rw [Bool.or_eq_true] at hx'
    rcases hx' with ht | hmem
    · exact quadAt_of_trivQuad ht _
    · have hmem' := elemN_spec hmem
      rw [List.mem_map] at hmem'
      obtain ⟨q, hq', rfl⟩ := hmem'
      rw [List.mem_append] at hq'
      rcases hq' with hq' | hq'
      · rw [hq q hq']
        rw [blkOK, List.all_eq_true] at hG
        exact hG q hq'
      · rw [List.mem_flatten] at hq'
        obtain ⟨blk, hblk, hq'⟩ := hq'
        rw [List.mem_map] at hblk
        obtain ⟨t, ht, rfl⟩ := hblk
        obtain ⟨j, hj, rfl⟩ : ∃ j, j < ow.length ∧ nth QTree.triv ow j = t := by
          obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem ht
          exact ⟨j, hj, by rw [nth_eq_getD, List.getD_eq_getElem _ _ hj, hjeq]⟩
        have hjm : j < m := by omega
        rw [ho j hjm q hq']
        have := hQ j hjm
        rw [owQ, blkOK, List.all_eq_true] at this
        exact this q hq'

theorem leafE_eq_leaf (hcheck : P.check = true) (hrows : P.checkRows = true) {b m : ℕ}
    {qt : QTree} {ow : List QTree} (hel : P.checkElim b m qt ow = true) {α : ℕ}
    (hα : α < 2 ^ (P.V - (b + m))) : leafE b m qt ow α = P.leaf (b + m) α := by
  have hel' := hel
  rw [checkElim, Bool.and_eq_true, Bool.and_eq_true] at hel'
  obtain ⟨hqm, how, -⟩ := hel'
  have hlen := checkOw_length how
  rw [Nat.zero_add] at hlen
  have hbad : ∀ β < 2 ^ b, _ := fun β hβ =>
    violO_bit hrows (α := α) (c := 0) hβ hqm (ρ := 2 ^ m * α) (by rw [Nat.zero_add])
  have h0 := (hbad 0 (Nat.pow_pos (by decide))).1
  have hE0 : ∀ e ∈ [Nat.xor (ones b) (optV (violO b (ones b) qt (2 ^ m * α)))],
      e < 2 ^ 2 ^ b := by
    intro e he
    rw [List.mem_singleton] at he
    rw [he]
    exact xor_lt (ones_lt b) h0
  rw [leaf_split hrows hα, leafE, forceL_eq, elimK_eq]
  change wtotF b (elimL b (ones b) (2 ^ m * α) ow (2 ^ 0)
    [gOf (ones b) (violO b (ones b) qt (2 ^ m * α))]) = _
  rw [gOf_eq, wtotF_eq (elimL_spec hrows (α := α) (β := 0) (Nat.pow_pos (by decide)) how hE0).1]
  refine Finset.sum_congr rfl fun β hβ' => ?_
  have hβ := Finset.mem_range.mp hβ'
  rw [(elimL_spec hrows (α := α) hβ how hE0).2, wsum_cons, wsum_nil, testBit_xor, testBit_ones,
    (hbad β hβ).2, prodOw_eq, hlen]
  simp only [Nat.zero_add]
  have hprod : (∏ j ∈ Finset.range m, ((blkOK P b m α β 0 (nth QTree.triv ow j).entries).toNat +
      (blkOK P b m α β (2 ^ j) (nth QTree.triv ow j).entries).toNat)) =
      cnt (owQ P b m α β ow) m := by
    rw [cnt_eq_prod]
    rfl
  rw [hprod]
  -- the indicator of the models, summed over the eliminated variables
  have hsum : ∑ ζ ∈ Finset.range (2 ^ m), (P.phi (joinN b (ζ + 2 ^ m * α) β)).toNat =
      (blkOK P b m α β 0 qt.entries).toNat * cnt (owQ P b m α β ow) m := by
    rw [cnt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    have hiff := phi_iff_elim hcheck hrows hel (α := α) hβ (Finset.mem_range.mp hζ)
    by_cases hG : blkOK P b m α β 0 qt.entries = true
    · by_cases hQ : ∀ j < m, owQ P b m α β ow j (ζ.testBit j) = true
      · rw [hiff.mpr ⟨hG, hQ⟩, hG, ite_eq_left_of_eq_true _ _ (eq_true hQ)]
        rfl
      · have : P.phi (joinN b (ζ + 2 ^ m * α) β) = false := by
          rw [Bool.eq_false_iff]
          exact fun h => hQ (hiff.mp h).2
        rw [this, ite_eq_right_of_eq_false _ _ (eq_false hQ)]
        rfl
    · have : P.phi (joinN b (ζ + 2 ^ m * α) β) = false := by
        rw [Bool.eq_false_iff]
        exact fun h => hG (hiff.mp h).1
      rw [this, Bool.eq_false_iff.mpr hG]
      simp
  rw [hsum]
  congr 1
  simp only [hβ, decide_true, Bool.true_xor, Bool.not_not, Nat.mul_zero, Nat.add_zero]

/-- The entries of `flat` have valid masks and do not depend on the eliminated variables. -/
noncomputable def checkFlat (P : Problem) (b m : ℕ) (flat : List (ℕ × ℕ × ℕ)) : Bool :=
  flat.all fun q => P.coversQuad b q && ownOK m 0 q

/-- A leaf vanishes when the two sides of a condition not depending on the eliminated variables
are opposite constants. -/
theorem leaf_deadE (hcheck : P.check = true) (hrows : P.checkRows = true) {b m α : ℕ}
    {e : ℕ × ℕ × ℕ} (hcov : P.coversQuad b e = true) (hown : ownOK m 0 e = true)
    (hα : α < 2 ^ (P.V - (b + m))) (hdead : P.deadR b (Nat.mul (Nat.pow 2 m) α) e = true) :
    P.leaf (b + m) α = 0 := by
  have hk := numAtoms_pos P.s P.n
  have hm : ∀ y, y % P.k < P.k := fun y => Nat.mod_lt _ hk
  rw [leaf_split hrows hα]
  refine Finset.sum_eq_zero fun β hβ' => Finset.sum_eq_zero fun ζ hζ' => ?_
  have hβ := Finset.mem_range.mp hβ'
  have hζ := Finset.mem_range.mp hζ'
  cases hphi : P.phi (joinN b (ζ + 2 ^ m * α) β)
  · rfl
  · exfalso
    have hq := quadAt_of_phi hcheck hphi e.1
    rw [quadAt_restr hβ (Nat.zero_le m) hζ (maskDep_of_cov hrows hcov) hown] at hq
    change P.quadAt (joinN b (0 + 2 ^ m * α) β) e.1 = true at hq
    rw [Nat.zero_add] at hq
    obtain ⟨e1, e2⟩ := dotR_land (α := 2 ^ m * α) hcov
    change forceB (Nat.land (2 ^ m * α) e.2.1) (fun r₁ => forceB (Nat.land (2 ^ m * α) e.2.2)
      fun r₂ => deadLR (top b) (P.dotRL b e.1 r₁) (P.dotRR b e.1 r₂)) = true at hdead
    rw [forceB_eq, forceB_eq, e1, e2] at hdead
    obtain ⟨-, hL⟩ := dotD_rows_spec hrows (α := 2 ^ m * α) hβ
      (cvN_lt (hm (e.1 / P.k / P.k / P.k))) (hm e.1) (hm (e.1 / P.k / P.k)) (hm (e.1 / P.k))
    obtain ⟨-, hR⟩ := dotD_rows_spec hrows (α := 2 ^ m * α) hβ (hm (e.1 / P.k / P.k / P.k))
      (hm (e.1 / P.k / P.k)) (hm e.1) (cvN_lt (hm (e.1 / P.k)))
    rw [quadAt, quadB, beq_iff_eq, ← hL, ← hR] at hq
    have hT := top_pos b
    rw [deadLR, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq,
      Nat.beq_eq, Nat.beq_eq] at hdead
    rcases hdead with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [dotRL_eq] at h1
      rw [dotRR_eq] at h2
      rw [h1, h2, sem_top, sem_zero hT] at hq
      exact Bool.noConfusion hq
    · rw [dotRL_eq] at h1
      rw [dotRR_eq] at h2
      rw [h1, h2, sem_top, sem_zero hT] at hq
      exact Bool.noConfusion hq

/-- Check the weighted sum `W` of the leaves of a list of orbit minima `(α, orbit size)`. A
minimum with evidence `i + 1` is checked to have a vanishing leaf because of the `i`-th entry of
`flat` (which must not depend on the eliminated variables); the leaf of a minimum with evidence
`0`, or beyond the end of the list of evidence, is evaluated. -/
noncomputable def sumEvE (P : Problem) (b m : ℕ) (qt : QTree) (ow : List QTree)
    (flat : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → Bool
  | [], _, acc, W => Nat.beq acc W
  | e :: seg, [], acc, W =>
    Nat.blt e.1 (2 ^ (P.V - (b + m))) &&
      forceL (Nat.add acc (Nat.mul e.2 (leafE b m qt ow e.1))) fun acc' =>
        sumEvE P b m qt ow flat seg [] acc' W
  | e :: seg, 0 :: ev, acc, W =>
    Nat.blt e.1 (2 ^ (P.V - (b + m))) &&
      forceL (Nat.add acc (Nat.mul e.2 (leafE b m qt ow e.1))) fun acc' =>
        sumEvE P b m qt ow flat seg ev acc' W
  | e :: seg, (i + 1) :: ev, acc, W =>
    Nat.blt e.1 (2 ^ (P.V - (b + m))) && (Nat.blt i flat.length &&
      (P.deadR b (Nat.mul (Nat.pow 2 m) e.1) (nth (0, 0, 0) flat i) &&
        sumEvE P b m qt ow flat seg ev acc W))

theorem sumEvE_spec (hcheck : P.check = true) (hrows : P.checkRows = true) {b m : ℕ}
    {qt : QTree} {ow : List QTree} (hel : P.checkElim b m qt ow = true)
    {flat : List (ℕ × ℕ × ℕ)} (hflat : P.checkFlat b m flat = true) :
    ∀ {seg : List (ℕ × ℕ)} {ev : List ℕ} {acc W : ℕ},
      P.sumEvE b m qt ow flat seg ev acc W = true →
      acc + (seg.map fun e => e.2 * P.leaf (b + m) e.1).sum = W
  | [], _, acc, W, h => by
    rw [sumEvE, Nat.beq_eq] at h
    simpa using h
  | e :: seg, [], acc, W, h => by
    rw [sumEvE, Bool.and_eq_true, Nat.blt_eq, forceL_eq] at h
    have ih := sumEvE_spec hcheck hrows hel hflat h.2
    rw [leafE_eq_leaf hcheck hrows hel h.1] at ih
    rw [List.map_cons, List.sum_cons, ← Nat.add_assoc]
    exact ih
  | e :: seg, 0 :: ev, acc, W, h => by
    rw [sumEvE, Bool.and_eq_true, Nat.blt_eq, forceL_eq] at h
    have ih := sumEvE_spec hcheck hrows hel hflat h.2
    rw [leafE_eq_leaf hcheck hrows hel h.1] at ih
    rw [List.map_cons, List.sum_cons, ← Nat.add_assoc]
    exact ih
  | e :: seg, (i + 1) :: ev, acc, W, h => by
    rw [sumEvE, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq,
      Nat.blt_eq] at h
    have ih := sumEvE_spec hcheck hrows hel hflat h.2.2.2
    have hc := List.all_eq_true.mp hflat _ (nth_mem (0, 0, 0) h.2.1)
    rw [Bool.and_eq_true] at hc
    rw [List.map_cons, List.sum_cons, leaf_deadE hcheck hrows hc.1 hc.2 h.1 h.2.2.1, Nat.mul_zero,
      Nat.zero_add]
    exact ih

/-- The form used by generated certificates. -/
theorem sumEvE_sum (hcheck : P.check = true) (hrows : P.checkRows = true) {b m : ℕ}
    {qt : QTree} {ow : List QTree} (hel : P.checkElim b m qt ow = true)
    {flat : List (ℕ × ℕ × ℕ)} (hflat : P.checkFlat b m flat = true) {seg : List (ℕ × ℕ)}
    {ev : List ℕ} {W : ℕ} (h : P.sumEvE b m qt ow flat seg ev 0 W = true) :
    SegSum (P.leaf (b + m)) seg W := by
  have := sumEvE_spec hcheck hrows hel hflat h
  rwa [Nat.zero_add] at this

end Problem

end RACert
