/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Intervals.Peeling

/-!
# Good representations are finite direct sums of intervals

Every `E`-good representation of `I_*` is isomorphic to a finite direct sum of the interval
representations `Y`, `A e`, `P e` with `e ∈ E`. Together with `IsGood.of_shortExact` this gives
Lemma 2.1, Step 2: extensions of objects of `B_E` lie in `B_E`.

The proof splits off one interval at a time. If `M(*) ≠ 0`, a nonzero `v ∈ M(*)` survives up to
a largest endpoint `d ∈ E` (or dies at once), and `P d` (or `Y`) splits off; otherwise a nonzero
`v ∈ M(0)` gives a summand `A d`. Induction on `dim M(*) + dim M(0)` concludes.
The splitting strategy follows the earlier
[linear-quiver development by Enomoto](https://github.com/haruhisa-enomoto/pretorsion-image-closed).
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

/-- Labels whose index lies in a finite set `E` (the label `Y` always does). -/
def LabelIn (E : Finset I) : IntervalCat k I → Prop
  | Y => True
  | A i => i ∈ E
  | P i => i ∈ E

section IntervalsGood

variable (E : Finset I)

lemma intervalRep_smap_apply (U : Set (WithBot I)) [U.OrdConnected] {s t : WithBot I}
    (h : s ≤ t) (f : (intervalRep U : Rep k I).obj s) (x : {_x : Unit // t ∈ U}) (hs : s ∈ U) :
    smap (intervalRep U : Rep k I) h f x = f ⟨(), hs⟩ :=
  (intervalRep_map_apply (k := k) h f x).trans (dite_eq_left hs)

instance (U : Set (WithBot I)) [U.OrdConnected] (t : WithBot I) :
    FiniteDimensional k ((intervalRep U : Rep k I).obj t) :=
  inferInstanceAs (FiniteDimensional k ({_x : Unit // t ∈ U} → k))

lemma intervalRep_subsingleton {U : Set (WithBot I)} [U.OrdConnected] {t : WithBot I}
    (ht : t ∉ U) : Subsingleton ((intervalRep U : Rep k I).obj t) :=
  ⟨fun _ _ => funext fun x => absurd x.2 ht⟩

/-- An interval whose trace on `I` is `{t ≤ e}` with `e ∈ E` is good. -/
lemma isGood_intervalRep_of_trace (U : Set (WithBot I)) [U.OrdConnected] (e : I) (he : e ∈ E)
    (hU : ∀ t : I, (t : WithBot I) ∈ U ↔ t ≤ e) : IsGood E (intervalRep U : Rep k I) where
  finite t := inferInstance
  surj {s t} h g := by
    by_cases ht : t ≤ e
    · refine ⟨fun _ => g ⟨(), (hU t).mpr ht⟩, funext fun x => ?_⟩
      exact intervalRep_smap_apply U _ _ x ((hU s).mpr (h.trans ht))
    · have := intervalRep_subsingleton (k := k) (fun h' => ht ((hU t).mp h'))
      exact ⟨0, Subsingleton.elim _ _⟩
  inj {s t} h hE f g hfg := by
    by_cases hs : s ≤ e
    · have ht : t ≤ e := le_of_not_gt fun het => hE e he ⟨hs, het⟩
      have hs' := (hU s).mpr hs
      apply intervalRep_obj_ext hs'
      have := congrFun hfg ⟨(), (hU t).mpr ht⟩
      rwa [intervalRep_smap_apply U _ _ _ hs', intervalRep_smap_apply U _ _ _ hs'] at this
    · have := intervalRep_subsingleton (k := k) (fun h' => hs ((hU s).mp h'))
      exact Subsingleton.elim _ _
  zero t ht := intervalRep_subsingleton (fun h' => absurd ((hU t).mp h') (not_le.mpr (ht e he)))

lemma isGood_rep (l : IntervalCat k I) (hl : LabelIn E l) : IsGood E (l.rep k) := by
  rcases l with _ | i | i
  · change IsGood E (intervalRep (Y (I := I)).support)
    exact
      { finite := fun t => inferInstance
        surj := fun {s t} h g => by
          have := intervalRep_subsingleton (k := k) (U := (Y (I := I)).support) (t := t)
            (IntervalLabel.coe_not_mem_Y t)
          exact ⟨0, Subsingleton.elim _ _⟩
        inj := fun {s t} h _ f g _ => by
          have := intervalRep_subsingleton (k := k) (U := (Y (I := I)).support) (t := s)
            (IntervalLabel.coe_not_mem_Y s)
          exact Subsingleton.elim _ _
        zero := fun t _ => intervalRep_subsingleton (IntervalLabel.coe_not_mem_Y t) }
  · exact isGood_intervalRep_of_trace E _ i hl (fun t => IntervalLabel.coe_mem_A)
  · exact isGood_intervalRep_of_trace E _ i hl (fun t => IntervalLabel.coe_mem_P)

/-- Conversely, a good interval whose trace on `I` is `{t ≤ i}` has `i ∈ E`. -/
lemma mem_of_isGood_intervalRep (U : Set (WithBot I)) [U.OrdConnected] (i : I)
    (hU : ∀ t : I, (t : WithBot I) ∈ U ↔ t ≤ i) (hg : IsGood E (intervalRep U : Rep k I)) :
    i ∈ E := by
  by_contra hi
  have hiU : (i : WithBot I) ∈ U := (hU i).mpr le_rfl
  have hne : (fun _ => (1 : k) : (intervalRep U : Rep k I).obj (i : WithBot I)) ≠
      (fun _ => 0) := fun h => one_ne_zero (congrFun h ⟨(), hiU⟩)
  by_cases hup : ∃ e ∈ E, i < e
  · let F := E.filter (fun e => i < e)
    have hF : F.Nonempty := by
      obtain ⟨e, he, hie⟩ := hup
      exact ⟨e, Finset.mem_filter.mpr ⟨he, hie⟩⟩
    let e₀ := F.min' hF
    have he₀ : i < e₀ := (Finset.mem_filter.mp (F.min'_mem hF)).2
    have hinj := hg.inj he₀.le (fun e he ⟨h₁, h₂⟩ => by
      rcases h₁.lt_or_eq with h₁ | rfl
      · exact absurd (F.min'_le e (Finset.mem_filter.mpr ⟨he, h₁⟩)) (not_le.mpr h₂)
      · exact hi he)
    have : Subsingleton ((intervalRep U : Rep k I).obj (e₀ : WithBot I)) :=
      intervalRep_subsingleton (fun h => absurd ((hU e₀).mp h) (not_le.mpr he₀))
    exact hne (hinj (Subsingleton.elim _ _))
  · have hlt : ∀ e ∈ E, e < i := fun e he =>
      lt_of_le_of_ne (le_of_not_gt fun h => hup ⟨e, he, h⟩) fun h => hi (h ▸ he)
    exact hne (@Subsingleton.elim _ (hg.zero i hlt) _ _)

/-- A good interval has its label in `E`. -/
lemma labelIn_of_isGood (l : IntervalCat k I) (hl : IsGood E (l.rep k)) : LabelIn E l := by
  rcases l with _ | i | i
  · trivial
  · exact mem_of_isGood_intervalRep E _ i (fun t => IntervalLabel.coe_mem_A) hl
  · exact mem_of_isGood_intervalRep E _ i (fun t => IntervalLabel.coe_mem_P) hl

end IntervalsGood

/-! ### Splitting off one interval -/

section Peel

variable [WellFoundedLT I] [Nonempty I] (E : Finset I)

/-- The least element `0` of `I`. -/
noncomputable def leastI : I :=
  (wellFounded_lt (α := I)).min Set.univ Set.univ_nonempty

lemma leastI_le (t : I) : leastI ≤ t :=
  not_lt.mp ((wellFounded_lt (α := I)).not_lt_min Set.univ (Set.mem_univ t))

lemma bot_lt_leastI : (⊥ : WithBot I) < (leastI : I) := WithBot.bot_lt_coe _

lemma exists_functional {V : Type*} [AddCommGroup V] [Module k V] {w : V} (hw : w ≠ 0) :
    ∃ μ : V →ₗ[k] k, μ w = 1 := by
  have : ¬ ∀ φ : Module.Dual k V, φ w = 0 := fun h =>
    hw ((Module.forall_dual_apply_eq_zero_iff k w).mp h)
  simp only [not_forall] at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨(φ w)⁻¹ • φ, by simp [hφ]⟩

variable {E}

omit [WellFoundedLT I] [Nonempty I] in
/-- A nonzero vector of a good representation survives up to some endpoint. -/
lemma IsGood.survive {M : Rep k I} (hM : IsGood E M) {t : I} (w : M.obj (t : WithBot I))
    (hw : w ≠ 0) : ∃ e ∈ E, ∃ h : t ≤ e, smap M (WithBot.coe_le_coe.mpr h) w ≠ 0 := by
  classical
  by_cases hall : ∀ e ∈ E, e < t
  · have := hM.zero t hall
    exact absurd (Subsingleton.elim w 0) hw
  · simp only [not_forall, not_lt] at hall
    have hne : (E.filter (fun e => t ≤ e)).Nonempty :=
      let ⟨e, he, hte⟩ := hall
      ⟨e, Finset.mem_filter.mpr ⟨he, hte⟩⟩
    have he₀ := Finset.mem_filter.mp ((E.filter (fun e => t ≤ e)).min'_mem hne)
    refine ⟨_, he₀.1, he₀.2, fun h0 => hw (hM.inj he₀.2 ?_ (h0.trans (map_zero _).symm))⟩
    intro e he ⟨hte, hee⟩
    exact absurd ((E.filter (fun e => t ≤ e)).min'_le e (Finset.mem_filter.mpr ⟨he, hte⟩))
      (not_le.mpr hee)

/-- A vector which survives to `0 ∈ I` survives exactly up to a largest endpoint `d ∈ E`. -/
lemma IsGood.lastSurvivor {M : Rep k I} (hM : IsGood E M) {a : WithBot I}
    (ha : a ≤ (leastI : I)) (v : M.obj a) (hv : smap M ha v ≠ 0) :
    ∃ d ∈ E, ∃ had : a ≤ (d : WithBot I), smap M had v ≠ 0 ∧
      ∀ (t : I) (h : a ≤ (t : WithBot I)), d < t → smap M h v = 0 := by
  classical
  have hae : ∀ e : I, a ≤ (e : WithBot I) := fun e =>
    ha.trans (WithBot.coe_le_coe.mpr (leastI_le e))
  let S := E.filter (fun e => smap M (hae e) v ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨e, he, hle, hne⟩ := hM.survive _ hv
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
    rwa [smap_comp] at hne
  have hd := Finset.mem_filter.mp (S.max'_mem hS)
  refine ⟨S.max' hS, hd.1, hae _, hd.2, fun t h hdt => ?_⟩
  by_contra hne
  obtain ⟨e, he, hte, hne'⟩ := hM.survive _ hne
  rw [smap_comp] at hne'
  have : e ≤ S.max' hS := S.le_max' e (Finset.mem_filter.mpr ⟨he, hne'⟩)
  exact absurd (lt_of_lt_of_le hdt hte) (not_lt.mpr this)

/-- A good representation which is nonzero at `*` or at `0` has an interval direct summand. -/
theorem IsGood.exists_summand {M : Rep k I} (hM : IsGood E M)
    (hne : Nontrivial (M.obj ⊥) ∨ Nontrivial (M.obj (leastI : I))) :
    ∃ (l : IntervalCat k I) (_ : LabelIn E l) (ι : l.rep k ⟶ M) (r : M ⟶ l.rep k), ι ≫ r = 𝟙 _ := by
  by_cases hbot : Nontrivial (M.obj ⊥)
  · obtain ⟨v, hv⟩ := exists_ne (0 : M.obj ⊥)
    by_cases hv0 : smap M (bot_le : (⊥ : WithBot I) ≤ (leastI : I)) v = 0
    · obtain ⟨μ, hμ⟩ := exists_functional (k := k) hv
      have hdie : ∀ t (h : ⊥ ≤ t), t ∉ Set.Iic (⊥ : WithBot I) → smap M h v = 0 := by
        intro t h ht
        have htb : t ≠ ⊥ := by rintro rfl; exact ht (Set.mem_Iic.mpr le_rfl)
        obtain ⟨t', rfl⟩ := WithBot.ne_bot_iff_exists.mp htb
        rw [← smap_comp M (bot_le : (⊥ : WithBot I) ≤ (leastI : I))
          (WithBot.coe_le_coe.mpr (leastI_le t')), hv0, map_zero]
      refine ⟨Y, trivial, fromVec M _ ⊥ v (fun t _ => bot_le) hdie,
        toInt M _ ⊥ μ (fun t ht => ht) (fun s t h hs ht => absurd (h.trans ht) hs), ?_⟩
      exact fromVec_comp_toInt M _ ⊥ ⊥ v _ hdie μ _ _ le_rfl (by rw [smap_self, hμ])
    · obtain ⟨d, hd, had, hsurv, hdead⟩ := hM.lastSurvivor bot_le v hv0
      obtain ⟨μ, hμ⟩ := exists_functional (k := k) hsurv
      have hdie : ∀ t (h : ⊥ ≤ t), t ∉ Set.Iic (d : WithBot I) → smap M h v = 0 := by
        intro t h ht
        have htb : t ≠ ⊥ := by rintro rfl; exact ht (Set.mem_Iic.mpr bot_le)
        obtain ⟨t', rfl⟩ := WithBot.ne_bot_iff_exists.mp htb
        exact hdead t' h (WithBot.coe_lt_coe.mp (not_le.mp ht))
      refine ⟨P d, hd, fromVec M _ ⊥ v (fun t _ => bot_le) hdie,
        toInt M _ (d : WithBot I) μ (fun t ht => ht)
          (fun s t h hs ht => absurd (h.trans ht) hs), ?_⟩
      exact fromVec_comp_toInt M _ ⊥ _ v _ hdie μ _ _ had hμ
  · have hbot' : Subsingleton (M.obj ⊥) := not_nontrivial_iff_subsingleton.mp hbot
    have h0 : Nontrivial (M.obj (leastI : I)) := hne.resolve_left hbot
    obtain ⟨v, hv⟩ := exists_ne (0 : M.obj (leastI : I))
    obtain ⟨d, hd, had, hsurv, hdead⟩ := hM.lastSurvivor le_rfl v (by rwa [smap_self])
    obtain ⟨μ, hμ⟩ := exists_functional (k := k) hsurv
    have hdie : ∀ t (h : ((leastI : I) : WithBot I) ≤ t), t ∉ Set.Ioc ⊥ (d : WithBot I) →
        smap M h v = 0 := by
      intro t h ht
      have htb : t ≠ ⊥ := by
        rintro rfl
        exact absurd h (not_le.mpr bot_lt_leastI)
      obtain ⟨t', rfl⟩ := WithBot.ne_bot_iff_exists.mp htb
      refine hdead t' h
        (WithBot.coe_lt_coe.mp (not_le.mp fun hle => ht ⟨WithBot.bot_lt_coe t', hle⟩))
    have hUa : ∀ t ∈ Set.Ioc ⊥ (d : WithBot I), ((leastI : I) : WithBot I) ≤ t := by
      intro t ht
      have htb : t ≠ ⊥ := ne_of_gt ht.1
      obtain ⟨t', rfl⟩ := WithBot.ne_bot_iff_exists.mp htb
      exact WithBot.coe_le_coe.mpr (leastI_le t')
    have hzero : ∀ s t (h : s ≤ t), s ∉ Set.Ioc ⊥ (d : WithBot I) → t ∈ Set.Ioc ⊥ (d : WithBot I) →
        ∀ m, smap M h m = 0 := by
      intro s t h hs ht m
      have : s = ⊥ := by
        by_contra hne'
        exact hs ⟨bot_lt_iff_ne_bot.mpr hne', h.trans ht.2⟩
      subst this
      rw [Subsingleton.elim m 0, map_zero]
    refine ⟨A d, hd, fromVec M _ _ v hUa hdie, toInt M _ (d : WithBot I) μ (fun t ht => ht.2) hzero,
      ?_⟩
    exact fromVec_comp_toInt M _ _ _ v hUa hdie μ _ hzero had hμ

end Peel

/-! ### Splitting identities and dimensions -/

section Split

variable {X M : Rep k I} (ι : X ⟶ M) (r : M ⟶ X) (h : ι ≫ r = 𝟙 X)

/-- The projection onto the kernel of a retraction. -/
noncomputable def kerProj : M ⟶ kernel r :=
  kernel.lift r (𝟙 M - r ≫ ι) (by
    rw [Preadditive.sub_comp, Category.assoc, h, Category.comp_id, Category.id_comp, sub_self])

include h in
lemma ι_kerProj : ι ≫ kerProj ι r h = 0 := by
  apply (cancel_mono (kernel.ι r)).mp
  rw [Category.assoc, kerProj, kernel.lift_ι, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, h, Category.id_comp, sub_self, zero_comp]

lemma kernelι_kerProj : kernel.ι r ≫ kerProj ι r h = 𝟙 _ := by
  apply (cancel_mono (kernel.ι r)).mp
  rw [Category.assoc, kerProj, kernel.lift_ι, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, kernel.condition, zero_comp, sub_zero, Category.id_comp]

lemma retract_add_kerProj : r ≫ ι + kerProj ι r h ≫ kernel.ι r = 𝟙 M := by
  rw [kerProj, kernel.lift_ι, add_sub_cancel]

lemma app_apply_of_eq {A B : Rep k I} {f g : A ⟶ B} (hfg : f = g) (t : WithBot I) (x : A.obj t) :
    (f.app t).hom x = (g.app t).hom x := by rw [hfg]

/-- Pointwise, `M(t) ≃ X(t) × (ker r)(t)`. -/
noncomputable def splitEquiv (t : WithBot I) : M.obj t ≃ₗ[k] X.obj t × (kernel r).obj t where
  toFun m := ((r.app t).hom m, ((kerProj ι r h).app t).hom m)
  map_add' m m' := by simp
  map_smul' c m := by simp
  invFun p := (ι.app t).hom p.1 + ((kernel.ι r).app t).hom p.2
  left_inv m := by
    have := app_apply_of_eq (retract_add_kerProj ι r h) t m
    simpa using this
  right_inv p := by
    obtain ⟨x, y⟩ := p
    have h1 := app_apply_of_eq h t x
    have h2 := app_apply_of_eq (ι_kerProj ι r h) t x
    have h3 := app_apply_of_eq (kernel.condition r) t y
    have h4 := app_apply_of_eq (kernelι_kerProj ι r h) t y
    simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, NatTrans.id_app,
      ModuleCat.hom_id, LinearMap.id_apply, NatTrans.app_zero, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h1 h2 h3 h4
    simp [map_add, h1, h2, h3, h4]

include h in
lemma finrank_split (t : WithBot I) [FiniteDimensional k (M.obj t)] :
    Module.finrank k (M.obj t) =
      Module.finrank k (X.obj t) + Module.finrank k ((kernel r).obj t) := by
  have e := splitEquiv ι r h t
  have : FiniteDimensional k (X.obj t × (kernel r).obj t) := LinearEquiv.finiteDimensional e
  have : FiniteDimensional k (X.obj t) := Module.Finite.of_surjective
    (LinearMap.fst k (X.obj t) ((kernel r).obj t)) LinearMap.fst_surjective
  have : FiniteDimensional k ((kernel r).obj t) := Module.Finite.of_surjective
    (LinearMap.snd k (X.obj t) ((kernel r).obj t)) LinearMap.snd_surjective
  rw [e.finrank_eq, Module.finrank_prod]

include h in
lemma IsGood.kernel_of_retract {E : Finset I} (hM : IsGood E M) : IsGood E (kernel r) :=
  hM.of_retract _ (kernel.ι r) (kerProj ι r h) (kernelι_kerProj ι r h)

end Split

section Decompose

variable [WellFoundedLT I] [Nonempty I] {E : Finset I}

/-- The measure `dim M(*) + dim M(0)`. -/
noncomputable def measure (M : Rep k I) : ℕ :=
  Module.finrank k (M.obj ⊥) + Module.finrank k (M.obj (leastI : I))

omit [WellFoundedLT I] [Nonempty I] in
lemma finrank_intervalRep (U : Set (WithBot I)) [U.OrdConnected] {t : WithBot I} (ht : t ∈ U) :
    Module.finrank k ((intervalRep U : Rep k I).obj t) = 1 := by
  classical
  change Module.finrank k ({_x : Unit // t ∈ U} → k) = 1
  rw [Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_eq_one_iff.mpr ⟨⟨(), ht⟩, fun x => Subtype.ext rfl⟩

lemma one_le_measure_rep (l : IntervalCat k I) (hl : LabelIn E l) : 1 ≤ measure (l.rep k) := by
  rcases l with _ | d | d
  · have := finrank_intervalRep (k := k) (Y (I := I)).support (t := ⊥) (Set.mem_Iic.mpr le_rfl)
    unfold measure
    change 1 ≤ Module.finrank k ((intervalRep (Y (I := I)).support : Rep k I).obj ⊥) + _
    omega
  · have := finrank_intervalRep (k := k) (A d).support (t := (leastI : I))
      ⟨bot_lt_leastI, WithBot.coe_le_coe.mpr (leastI_le d)⟩
    unfold measure
    change 1 ≤ _ + Module.finrank k ((intervalRep (A d).support : Rep k I).obj (leastI : I))
    omega
  · have := finrank_intervalRep (k := k) (P d).support (t := ⊥)
      (Set.mem_Iic.mpr bot_le)
    unfold measure
    change 1 ≤ Module.finrank k ((intervalRep (P d).support : Rep k I).obj ⊥) + _
    omega

/-- Adjoining one summand to a finite biproduct. -/
noncomputable def isoBiprodBiproduct {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] [HasBinaryBiproducts C] {ι : Type*} [Fintype ι] (X : C) (f : ι → C) :
    X ⊞ (⨁ f) ≅ ⨁ (fun o : Option ι => o.elim X f) := by
  classical
  let b : Bicone (fun o : Option ι => o.elim X f) :=
    { pt := X ⊞ (⨁ f)
      π := fun o => match o with
        | none => biprod.fst
        | some i => biprod.snd ≫ biproduct.π f i
      ι := fun o => match o with
        | none => biprod.inl
        | some i => biproduct.ι f i ≫ biprod.inr
      ι_π := fun o o' => by
        rcases o with _ | i <;> rcases o' with _ | i'
        · refine (biprod.inl_fst (X := X) (Y := ⨁ f)).trans ?_
          rw [dite_eq_left (rfl : (none : Option ι) = none)]
          rfl
        · have : (biprod.inl : X ⟶ X ⊞ ⨁ f) ≫ biprod.snd ≫ biproduct.π f i' = 0 := by
            rw [← Category.assoc, biprod.inl_snd, zero_comp]
          refine this.trans ?_
          rw [dite_eq_right (fun (h : (none : Option ι) = some i') =>
            Option.some_ne_none i' h.symm)]
          rfl
        · have : (biproduct.ι f i ≫ (biprod.inr : ⨁ f ⟶ X ⊞ ⨁ f)) ≫ biprod.fst = 0 := by
            rw [Category.assoc, biprod.inr_fst, comp_zero]
          refine this.trans ?_
          rw [dite_eq_right (Option.some_ne_none i)]
          rfl
        · have : (biproduct.ι f i ≫ (biprod.inr : ⨁ f ⟶ X ⊞ ⨁ f)) ≫ biprod.snd ≫
              biproduct.π f i' = if h : i = i' then eqToHom (congrArg f h) else 0 := by
            rw [Category.assoc, biprod.inr_snd_assoc, biproduct.ι_π]
          refine this.trans ?_
          by_cases h : i = i'
          · subst h
            rw [dite_eq_left rfl, dite_eq_left rfl]
            rfl
          · rw [dite_eq_right h, dite_eq_right (fun h' => h (Option.some_injective _ h'))]
            rfl }
  have key : ∑ i, b.π (some i) ≫ b.ι (some i) = (biprod.snd : X ⊞ (⨁ f) ⟶ ⨁ f) ≫ biprod.inr := by
    change ∑ i, ((biprod.snd : X ⊞ (⨁ f) ⟶ ⨁ f) ≫ biproduct.π f i) ≫
      (biproduct.ι f i ≫ (biprod.inr : ⨁ f ⟶ X ⊞ (⨁ f))) = _
    have : ∀ i, ((biprod.snd : X ⊞ (⨁ f) ⟶ ⨁ f) ≫ biproduct.π f i) ≫
        (biproduct.ι f i ≫ (biprod.inr : ⨁ f ⟶ X ⊞ (⨁ f))) =
        (biprod.snd : X ⊞ (⨁ f) ⟶ ⨁ f) ≫ (biproduct.π f i ≫ biproduct.ι f i) ≫ biprod.inr :=
      fun i => by simp only [Category.assoc]
    rw [Finset.sum_congr rfl (fun i _ => this i), ← Preadditive.comp_sum, ← Preadditive.sum_comp,
      biproduct.total, Category.id_comp]
  have hb : b.IsBilimit := isBilimitOfTotal b (by
    rw [Fintype.sum_option, key]
    exact (biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ ⨁ f)))
  exact biproduct.uniqueUpToIso _ hb

end Decompose

/-! ### The decomposition -/

section DecomposeMain

variable [WellFoundedLT I] [Nonempty I] {E : Finset I}

lemma IsGood.isZero_of_measure {M : Rep k I} (hM : IsGood E M) (h : measure M = 0) : IsZero M := by
  have h1 : Module.finrank k (M.obj ⊥) = 0 := by unfold measure at h; omega
  have h2 : Module.finrank k (M.obj (leastI : I)) = 0 := by unfold measure at h; omega
  have := hM.finite ⊥
  have := hM.finite (leastI : I)
  have s1 : Subsingleton (M.obj ⊥) := Module.finrank_zero_iff.mp h1
  have s2 : Subsingleton (M.obj (leastI : I)) := Module.finrank_zero_iff.mp h2
  refine Functor.isZero _ (fun t => ?_)
  induction t using WithBot.recBotCoe with
  | bot => exact ModuleCat.isZero_of_subsingleton _
  | coe t =>
    have : Subsingleton (M.obj (t : WithBot I)) := (hM.surj (leastI_le t)).subsingleton
    exact ModuleCat.isZero_of_subsingleton _

lemma isZero_biproduct_empty {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
    {ι : Type*} [IsEmpty ι] (f : ι → C) : IsZero (⨁ f) :=
  ⟨fun _ => ⟨⟨0⟩, fun _ => biproduct.hom_ext' _ _ (fun i => isEmptyElim i)⟩,
    fun _ => ⟨⟨0⟩, fun _ => biproduct.hom_ext _ _ (fun i => isEmptyElim i)⟩⟩

/-- **Lemma 2.1, Step 2 (decomposition).** Every `E`-good representation is isomorphic to a
finite direct sum of interval representations with labels in `E`. -/
theorem IsGood.decompose : ∀ (n : ℕ) (M : Rep k I), IsGood E M → measure M ≤ n →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → IntervalCat k I), (∀ i, LabelIn E (L i)) ∧
      Nonempty (M ≅ ⨁ fun i => (L i).rep k) := by
  intro n
  induction n with
  | zero =>
    intro M hM hn
    refine ⟨Empty, inferInstance, isEmptyElim, isEmptyElim, ⟨?_⟩⟩
    exact (hM.isZero_of_measure (by omega)).iso (isZero_biproduct_empty _)
  | succ n ih =>
    intro M hM hn
    by_cases hz : measure M = 0
    · exact ⟨Empty, inferInstance, isEmptyElim, isEmptyElim,
        ⟨(hM.isZero_of_measure hz).iso (isZero_biproduct_empty _)⟩⟩
    have := hM.finite ⊥
    have := hM.finite (leastI : I)
    have hne : Nontrivial (M.obj ⊥) ∨ Nontrivial (M.obj (leastI : I)) := by
      by_contra hc
      simp only [not_or, not_nontrivial_iff_subsingleton] at hc
      obtain ⟨h1, h2⟩ := hc
      apply hz
      unfold measure
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
    obtain ⟨l, hl, ι, r, h⟩ := hM.exists_summand hne
    have hK := hM.kernel_of_retract ι r h
    have hmeas : measure M = measure (l.rep k) + measure (Limits.kernel r) := by
      unfold measure
      rw [finrank_split ι r h ⊥, finrank_split ι r h (leastI : I)]
      ring
    have := one_le_measure_rep l hl
    obtain ⟨ι', _, L, hL, ⟨e⟩⟩ := ih (Limits.kernel r) hK (by omega)
    refine ⟨Option ι', inferInstance, fun o => o.elim l L, ?_, ⟨?_⟩⟩
    · rintro (_ | i)
      exacts [hl, hL i]
    · exact isoBiprodKernel ι r h ≪≫ biprod.mapIso (Iso.refl _) e ≪≫
        isoBiprodBiproduct (l.rep k) (fun i => (L i).rep k) ≪≫
        eqToIso (congrArg (fun F => ⨁ F) (funext fun o => by cases o <;> rfl))

end DecomposeMain

end ExtriangulatedRealization
