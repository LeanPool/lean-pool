/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Towers.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Group.Finsupp

/-!
# Towers of abelian groups: `lim`, `lim¹` and the Mittag-Leffler condition

For a tower `G : ℕᵒᵖ ⥤ AddCommGrpCat`:

* `Tower.IsCompatible G x`: `x ∈ ∏ G_m` is a compatible family, i.e. an element of `lim G`;
* `Tower.LimVanishes G`: `lim G = 0`;
* `Tower.LimOneVanishes G`: `lim¹ G = 0`, i.e. `1 - shift : ∏ G_m → ∏ G_m` is surjective;
* `Tower.MittagLeffler G`: the images of the transition maps into each level stabilise.

Main results:

* Paper, Lemma 3.2 (`lem:ML-const`) [Stacks, Tags 070C, 0H9K, 07KW]: for a pro-isomorphism
  `u : cst U ⟶ G`, the tower `G` is Mittag-Leffler (`IsProIso.mittagLeffler`), `u` induces a
  bijection from `U` to `lim G` (`IsProIso.existsUnique_eq`), and `lim¹ G = 0`
  (`IsProIso.limOneVanishes`);
* Paper, Lemma 4.1 (`lem:ML`) [Stacks, Tag 091C]: `G` is pro-zero if and only if `lim` and
  `lim¹` vanish on `G` and on the countable direct sum `sumTower G` of copies of `G`
  (`isProZero_iff_lim`).
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe v

namespace RigidDescent

namespace Tower

variable {G : ℕᵒᵖ ⥤ AddCommGrpCat.{v}}

/-! ### Elementwise transition maps -/

@[simp]
lemma t_t_apply {m m' m'' : ℕ} (h : m ≤ m') (h' : m' ≤ m'') (x : G.obj (op m'')) :
    Tower.t G h (Tower.t G h' x) = Tower.t G (h.trans h') x :=
  (CategoryTheory.comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom (t_comp G h h') x)

lemma t_refl_apply (m : ℕ) (x : G.obj (op m)) : Tower.t G (le_refl m) x = x :=
  (ConcreteCategory.congr_hom (t_refl G m) x).trans (CategoryTheory.id_apply _)

lemma app_t_apply {U : AddCommGrpCat.{v}} (u : (Functor.const ℕᵒᵖ).obj U ⟶ G) {m m' : ℕ}
    (h : m ≤ m') (z : U) : Tower.t G h (u.app (op m') z) = u.app (op m) z :=
  (CategoryTheory.comp_apply _ _ _).symm.trans (ConcreteCategory.congr_hom (app_t u h) z)

lemma t_naturality_apply {G' : ℕᵒᵖ ⥤ AddCommGrpCat.{v}} (α : G ⟶ G') {m m' : ℕ} (h : m ≤ m')
    (x : G.obj (op m')) : α.app (op m) (Tower.t G h x) = Tower.t G' h (α.app (op m') x) :=
  (CategoryTheory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom (t_naturality α h) x).trans (CategoryTheory.comp_apply _ _ _))

lemma t_apply_eq_of_le {m m' : ℕ} (h : m ≤ m') (x : G.obj (op m')) {m₁ : ℕ} (h₁ : m ≤ m₁)
    (h₁' : m₁ ≤ m') : Tower.t G h x = Tower.t G h₁ (Tower.t G h₁' x) := by
  rw [t_t_apply]

/-! ### `lim`, `lim¹` and Mittag-Leffler -/

variable (G) in
/-- `x ∈ ∏ G_m` is compatible with the transition maps, i.e. it is an element of `lim G`. -/
def IsCompatible (x : ∀ m, G.obj (op m)) : Prop :=
  ∀ m, Tower.t G (Nat.le_succ m) (x (m + 1)) = x m

variable (G) in
/-- `lim G = 0`. -/
def LimVanishes : Prop :=
  ∀ x : ∀ m, G.obj (op m), IsCompatible G x → ∀ m, x m = 0

variable (G) in
/-- `lim¹ G = 0`: the map `1 - shift : ∏ G_m → ∏ G_m` is surjective, where `lim¹` is the
cokernel of `1 - shift` (Paper, Conventions). -/
def LimOneVanishes : Prop :=
  ∀ a : ∀ m, G.obj (op m), ∃ b : ∀ m, G.obj (op m),
    ∀ m, b m - Tower.t G (Nat.le_succ m) (b (m + 1)) = a m

variable (G) in
/-- The Mittag-Leffler condition: for every `m` there is `m' ≥ m` such that the image of
`G_{m''} → G_m` is the image of `G_{m'} → G_m` for every `m'' ≥ m'`. -/
def MittagLeffler : Prop :=
  ∀ m, ∃ (m' : ℕ) (h : m ≤ m'), ∀ (m'' : ℕ) (h' : m' ≤ m'') (x : G.obj (op m')),
    ∃ y : G.obj (op m''), Tower.t G (h.trans h') y = Tower.t G h x

lemma IsCompatible.t_apply {x : ∀ m, G.obj (op m)} (hx : IsCompatible G x) {m m' : ℕ}
    (h : m ≤ m') : Tower.t G h (x m') = x m := by
  induction m', h using Nat.le_induction with
  | base => exact t_refl_apply _ _
  | succ n hmn ih => rw [← ih, ← hx n, t_t_apply]

/-- Unrolling `β_l = t(β_{l+1})` on `[p, q)`. -/
lemma eq_t_of_succ (β : ∀ l, G.obj (op l)) {p q : ℕ} (hpq : p ≤ q)
    (hβ : ∀ l, p ≤ l → l < q → β l = Tower.t G (Nat.le_succ l) (β (l + 1))) :
    β p = Tower.t G hpq (β q) := by
  induction q, hpq using Nat.le_induction with
  | base => exact (t_refl_apply _ _).symm
  | succ n hpn ih =>
    rw [ih (fun l hl hln => hβ l hl (by omega)), hβ n hpn (by omega), t_t_apply]

/-- If every element of `I_l` lifts to `I_{l+1}`, every element of `I_m` is the `m`-th
component of a compatible family. -/
lemma exists_isCompatible_of_lift (I : ∀ l, Set (G.obj (op l)))
    (hI : ∀ l z, z ∈ I l → ∃ z', z' ∈ I (l + 1) ∧ Tower.t G (Nat.le_succ l) z' = z)
    {m : ℕ} (y : G.obj (op m)) (hy : y ∈ I m) :
    ∃ x : ∀ l, G.obj (op l), IsCompatible G x ∧ x m = y := by
  choose g hg hg' using hI
  let f : ∀ i : ℕ, {w : G.obj (op (m + i)) // w ∈ I (m + i)} := fun i =>
    Nat.rec (motive := fun i => {w : G.obj (op (m + i)) // w ∈ I (m + i)}) ⟨y, hy⟩
      (fun i w => ⟨g (m + i) w.1 w.2, hg _ _ _⟩) i
  have hf : ∀ i, Tower.t G (Nat.le_succ (m + i)) (f (i + 1)).1 = (f i).1 := fun i => hg' _ _ _
  have hfy : ∀ i, Tower.t G (Nat.le_add_right m i) (f i).1 = y := by
    intro i
    induction i with
    | zero => exact t_refl_apply _ _
    | succ i ih =>
      rw [← ih, ← hf i, t_t_apply]
  refine ⟨fun l => Tower.t G (Nat.le_add_left l m) (f l).1, fun l => ?_, hfy m⟩
  dsimp only
  rw [t_t_apply, ← hf l, t_t_apply]

end Tower

open Tower

variable {G : ℕᵒᵖ ⥤ AddCommGrpCat.{v}} {U : AddCommGrpCat.{v}}
  {u : (Functor.const ℕᵒᵖ).obj U ⟶ G}

/-! ### Lemma 3.2 -/

/-- Paper, Lemma 3.2 (`lem:ML-const`) [Stacks, Tag 070C]: a tower of abelian groups that is
pro-isomorphic to a constant tower is Mittag-Leffler. -/
theorem IsProIso.mittagLeffler (hu : IsProIso u) : MittagLeffler G := by
  obtain ⟨k, v, -, H⟩ := hu
  intro m
  obtain ⟨k', hk, hm, e⟩ := H m
  refine ⟨k', hm, fun m'' h' x => ⟨u.app (op m'') (v (Tower.t G hk x)), ?_⟩⟩
  have := ConcreteCategory.congr_hom e x
  simp only [CategoryTheory.comp_apply] at this
  rw [app_t_apply]
  exact this

/-- Paper, Lemma 3.2 (`lem:ML-const`): a pro-isomorphism `u : cst U ⟶ G` induces
`lim G ≅ U`: every compatible family is `(u_m z)_m` for a unique `z ∈ U`. -/
theorem IsProIso.existsUnique_eq (hu : IsProIso u) {x : ∀ m, G.obj (op m)}
    (hx : IsCompatible G x) : ∃! z : U, ∀ m, u.app (op m) z = x m := by
  obtain ⟨k, v, hv, H⟩ := hu
  refine ⟨v (x k), fun m => ?_, fun z hz => ?_⟩
  · obtain ⟨k', hk, hm, e⟩ := H m
    have := ConcreteCategory.congr_hom e (x k')
    simp only [CategoryTheory.comp_apply] at this
    rwa [hx.t_apply hk, hx.t_apply hm] at this
  · have := ConcreteCategory.congr_hom hv z
    simp only [CategoryTheory.comp_apply] at this
    rw [← hz k]
    exact this.symm

/-- Paper, Lemma 3.2 (`lem:ML-const`) [Stacks, Tag 07KW]: if `u : cst U ⟶ G` is a
pro-isomorphism, then `lim¹ G = 0`. -/
theorem IsProIso.limOneVanishes (hu : IsProIso u) : LimOneVanishes G := by
  classical
  obtain ⟨k, v, N, -, H⟩ := hu.exists_data
  intro a
  let c : ℕ → U := fun j => if h : k ≤ j then v (Tower.t G h (a j)) else 0
  let P : ℕ → ℕ := fun m => max (N m) k
  have hc : ∀ m j (hm : m ≤ j), P m ≤ j → u.app (op m) (c j) = Tower.t G hm (a j) := by
    intro m j hm hj
    have hk : k ≤ j := le_trans (le_max_right _ _) hj
    have e := ConcreteCategory.congr_hom (H m j hk hm (le_trans (le_max_left _ _) hj)) (a j)
    simp only [CategoryTheory.comp_apply] at e
    simp only [c, hk, ↓reduceDIte]
    exact e
  let d : ∀ m, ℕ → G.obj (op m) := fun m i =>
    Tower.t G (Nat.le_add_right m i) (a (m + i)) - u.app (op m) (c (m + i))
  have hd0 : ∀ m i, P m ≤ i → d m i = 0 := fun m i hi => by
    simp only [d]
    rw [hc m (m + i) (Nat.le_add_right m i) (le_trans hi (Nat.le_add_left i m)), sub_self]
  have hdt : ∀ m i, Tower.t G (Nat.le_succ m) (d (m + 1) i) = d m (i + 1) := by
    intro m i
    simp only [d, map_sub, t_t_apply, app_t_apply]
    have key : ∀ j j' (h : m ≤ j) (h' : m ≤ j'), j = j' →
        Tower.t G h (a j) - u.app (op m) (c j) = Tower.t G h' (a j') - u.app (op m) (c j') := by
      rintro j _ h h' rfl
      rfl
    exact key _ _ _ _ (by omega)
  let S : ∀ m, ℕ → G.obj (op m) := fun m L => ∑ i ∈ Finset.range L, d m i
  have hS : ∀ m L, P m ≤ L → S m L = S m (P m) := by
    intro m L hL
    refine (Finset.sum_subset (Finset.range_mono hL) fun i _ hi => hd0 m i ?_).symm
    simpa using hi
  let C : ℕ → U := fun m => ∑ j ∈ Finset.range m, c j
  refine ⟨fun m => S m (P m) - u.app (op m) (C m), fun m => ?_⟩
  obtain ⟨L, hL₁, hL₂⟩ : ∃ L, P m ≤ L ∧ P (m + 1) ≤ L :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have h1 : S m (L + 1) = d m 0 + ∑ i ∈ Finset.range L, d m (i + 1) := by
    simp only [S]
    rw [Finset.sum_range_succ', add_comm]
  have h2 : Tower.t G (Nat.le_succ m) (S (m + 1) L) = ∑ i ∈ Finset.range L, d m (i + 1) := by
    simp only [S, map_sum, hdt]
  have h3 : Tower.t G (Nat.le_succ m) (u.app (op (m + 1)) (C (m + 1))) =
      u.app (op m) (C m) + u.app (op m) (c m) := by
    rw [app_t_apply]
    simp only [C, Finset.sum_range_succ, map_add]
  have h4 : d m 0 = a m - u.app (op m) (c m) := by
    change Tower.t G (le_refl m) (a m) - u.app (op m) (c m) = _
    rw [t_refl_apply]
  change S m (P m) - u.app (op m) (C m) -
    Tower.t G (Nat.le_succ m) (S (m + 1) (P (m + 1)) - u.app (op (m + 1)) (C (m + 1))) = a m
  rw [← hS m (L + 1) (by omega), ← hS (m + 1) L hL₂, map_sub, h1, h2, h3, h4]
  abel

/-- Paper, Lemma 3.2 (`lem:ML-const`) for pro-constant towers. -/
theorem IsProConstant.mittagLeffler (h : IsProConstant G) : MittagLeffler G :=
  let ⟨_, _, hu⟩ := h
  hu.mittagLeffler

/-- Paper, Lemma 3.2 (`lem:ML-const`) for pro-constant towers. -/
theorem IsProConstant.limOneVanishes (h : IsProConstant G) : LimOneVanishes G :=
  let ⟨_, _, hu⟩ := h
  hu.limOneVanishes

/-! ### Invariance under isomorphism -/

lemma LimVanishes.of_iso {G' : ℕᵒᵖ ⥤ AddCommGrpCat.{v}} (h : LimVanishes G) (e : G ≅ G') :
    LimVanishes G' := by
  intro x' hx' m
  have hx : IsCompatible G fun m => e.inv.app (op m) (x' m) := fun m => by
    dsimp only
    rw [← t_naturality_apply, hx']
  have h₁ := ConcreteCategory.congr_hom (e.inv_hom_id_app (op m)) (x' m)
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h₁
  rw [← h₁, h _ hx m, map_zero]

lemma LimOneVanishes.of_iso {G' : ℕᵒᵖ ⥤ AddCommGrpCat.{v}} (h : LimOneVanishes G)
    (e : G ≅ G') : LimOneVanishes G' := by
  intro a'
  obtain ⟨b, hb⟩ := h fun m => e.inv.app (op m) (a' m)
  refine ⟨fun m => e.hom.app (op m) (b m), fun m => ?_⟩
  have h₁ := ConcreteCategory.congr_hom (e.inv_hom_id_app (op m)) (a' m)
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h₁
  rw [← t_naturality_apply, ← map_sub, hb, h₁]

/-! ### Lemma 4.1 -/

variable (G) in
/-- The countable direct sum `{G_m^{(ℕ)}}_m` of copies of a tower `G`. -/
noncomputable def sumTower : ℕᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj m := AddCommGrpCat.of (ℕ →₀ G.obj m)
  map f := AddCommGrpCat.ofHom (Finsupp.mapRange.addMonoidHom (G.map f).hom)
  map_id m := by
    ext x n
    simp
  map_comp f g := by
    ext x n
    simp

variable (G) in
/-- The projection of `sumTower G` onto the `n`-th copy. -/
noncomputable def sumTowerEval (n : ℕ) : sumTower G ⟶ G where
  app m := AddCommGrpCat.ofHom (Finsupp.applyAddHom n)
  naturality m m' f := by
    ext x
    rfl

variable (G) in
/-- The inclusion of the `n`-th copy at level `l`. -/
noncomputable def sumTowerSingle (n l : ℕ) : G.obj (op l) ⟶ (sumTower G).obj (op l) :=
  AddCommGrpCat.ofHom (Finsupp.singleAddHom n)

lemma sumTowerEval_single (n l l' : ℕ) (y : G.obj (op l')) :
    (sumTowerEval G n).app (op l') (sumTowerSingle G l l' y) = if l = n then y else 0 := by
  change (Finsupp.single l y : ℕ →₀ G.obj (op l')) n = _
  rw [Finsupp.single_apply]

lemma IsProZero.sum (h : IsProZero G) : IsProZero (sumTower G) := by
  intro m
  obtain ⟨m', hm, e⟩ := h m
  refine ⟨m', hm, ?_⟩
  ext x
  have hx : Tower.t (sumTower G) hm x = 0 := by
    refine Finsupp.ext fun n => ?_
    have := t_naturality_apply (sumTowerEval G n) hm x
    rw [e] at this
    exact this.trans rfl
  rw [hx]
  rfl

lemma IsProZero.limVanishes (h : IsProZero G) : LimVanishes G := by
  intro x hx m
  obtain ⟨m', hm, e⟩ := h m
  rw [← hx.t_apply hm, e]
  rfl

/-- Emmanouil's criterion [Stacks, Tag 0CQA]: if `lim¹` vanishes on the countable direct sum
of copies of `G`, then `G` is Mittag-Leffler. -/
theorem mittagLeffler_of_limOneVanishes_sumTower (h : LimOneVanishes (sumTower G)) :
    MittagLeffler G := by
  classical
  by_contra hML
  simp only [MittagLeffler, not_forall, not_exists] at hML
  obtain ⟨m, hm⟩ := hML
  choose M hM x hx using hm
  let a : ∀ l, (sumTower G).obj (op l) := fun l =>
    sumTowerSingle G l l (if hl : m ≤ l then x l hl else 0)
  obtain ⟨b, hb⟩ := h a
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset
    ((b m : ℕ →₀ G.obj (op m)).support ∪ Finset.range m)
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hn
  obtain ⟨hbm, hnm⟩ := hn
  let β : ∀ l, G.obj (op l) := fun l => (sumTowerEval G n).app (op l) (b l)
  have hβ : ∀ l, β l - Tower.t G (Nat.le_succ l) (β (l + 1)) =
      (sumTowerEval G n).app (op l) (a l) := by
    intro l
    simp only [β]
    rw [← t_naturality_apply, ← map_sub, hb]
  have ha : ∀ l, l ≠ n → (sumTowerEval G n).app (op l) (a l) = 0 := by
    intro l hl
    simp only [a]
    simp only [sumTowerEval_single, hl, ↓reduceIte]
  have han : (sumTowerEval G n).app (op n) (a n) = x n hnm := by
    simp only [a]
    simp only [sumTowerEval_single, hnm, ↓reduceIte, ↓reduceDIte]
  have hstep : ∀ l, l ≠ n → β l = Tower.t G (Nat.le_succ l) (β (l + 1)) := fun l hl =>
    sub_eq_zero.1 ((hβ l).trans (ha l hl))
  have hβm : β m = 0 := Finsupp.notMem_support_iff.1 hbm
  set q := max (M n hnm) (n + 1)
  have e₁ : β m = Tower.t G hnm (β n) :=
    eq_t_of_succ β hnm fun l _ hl => hstep l (by omega)
  have e₂ : β (n + 1) = Tower.t G (le_max_right (M n hnm) (n + 1)) (β q) :=
    eq_t_of_succ β _ fun l hl _ => hstep l (by omega)
  have e₃ : β n = x n hnm + Tower.t G (Nat.le_succ n) (β (n + 1)) := by
    rw [← han, ← hβ n, sub_add_cancel]
  apply hx n hnm (Tower.t G (le_max_left (M n hnm) (n + 1)) (-β q))
  rw [hβm, e₃, e₂, map_add, t_t_apply, t_t_apply] at e₁
  rw [t_t_apply, map_neg]
  exact (eq_neg_of_add_eq_zero_left e₁.symm).symm

/-- [Stacks, Tag 091C]: a Mittag-Leffler tower with `lim G = 0` is pro-zero. -/
theorem isProZero_of_mittagLeffler (hML : MittagLeffler G) (h0 : LimVanishes G) :
    IsProZero G := by
  choose μ hμ hML using hML
  let I : ∀ l, Set (G.obj (op l)) := fun l => Set.range (Tower.t G (hμ l))
  have hI : ∀ l z, z ∈ I l → ∃ z', z' ∈ I (l + 1) ∧ Tower.t G (Nat.le_succ l) z' = z := by
    rintro l _ ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := hML l (max (μ (l + 1)) (μ l)) (le_max_right _ _) w
    refine ⟨Tower.t G (le_trans (hμ (l + 1)) (le_max_left _ _)) y,
      ⟨Tower.t G (le_max_left _ _) y, by rw [t_t_apply]⟩, ?_⟩
    rw [t_t_apply]
    exact hy
  intro m
  refine ⟨μ m, hμ m, ?_⟩
  ext w
  obtain ⟨x, hx, hxm⟩ := exists_isCompatible_of_lift I hI (Tower.t G (hμ m) w) ⟨w, rfl⟩
  rw [← hxm, h0 x hx m]
  rfl

/-- Paper, Lemma 4.1 (`lem:ML`) [Stacks, Tag 091C]: a tower of abelian groups is pro-zero if
and only if `lim` and `lim¹` vanish on it and on the countable direct sum of copies of it. -/
theorem isProZero_iff_lim :
    IsProZero G ↔ LimVanishes G ∧ LimOneVanishes G ∧ LimVanishes (sumTower G) ∧
      LimOneVanishes (sumTower G) := by
  constructor
  · intro h
    exact ⟨h.limVanishes, h.isProConstant.limOneVanishes, h.sum.limVanishes,
      h.sum.isProConstant.limOneVanishes⟩
  · rintro ⟨h0, -, -, h1⟩
    exact isProZero_of_mittagLeffler (mittagLeffler_of_limOneVanishes_sumTower h1) h0

end RigidDescent
