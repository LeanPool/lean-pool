/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.FreeCover

/-!
# Local cocycles from functions on the sides

Let `W` be a finite paired family of words and let `g` be a function on the discs such that on each
pair of pasted sides
the difference of `g` is constant (`SideConst`). Take `A` copies of the discs. Paste the copy `s` of
a point `a` to the
copy `s + g b - g a` of `b` when `a` and `b` are pasted. The group `A` acts freely on this space,
with quotient the
space presented by `W`. So we get a local cocycle with primitive `g` (`exists_cocycle`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

universe u

/-- On each pair of pasted sides the difference of `g` is constant. -/
def SideConst {A : Type} [AddGroup A] (W : ℕ → List Letter) (g : ℕ × ℂ → A) : Prop :=
  ∀ i p j q k e e', (W i)[p]? = some (k, e) → (W j)[q]? = some (k, e') → (i, p) ≠ (j, q) →
    ∃ c, ∀ u ∈ Icc (0 : ℝ) 1, g (spt W j q (flp e e' u)) = c + g (spt W i p u)

variable {W : ℕ → List Letter} {A : Type} [AddGroup A] {g : ℕ × ℂ → A}

/-- The relation on the copies of the discs. -/
def covRel (W : ℕ → List Letter) (g : ℕ × ℂ → A) (x y : Dsk W × A) : Prop :=
  PRel W x.1.1 y.1.1 ∧ -g x.1.1 + x.2 = -g y.1.1 + y.2

/-- The relation on the copies of the discs, as a setoid. -/
def covSetoid (W : ℕ → List Letter) (g : ℕ × ℂ → A) : Setoid (Dsk W × A) :=
  ⟨covRel W g, ⟨fun _ => ⟨.refl _, rfl⟩, fun h => ⟨.symm _ _ h.1, h.2.symm⟩,
    fun h h' => ⟨.trans _ _ _ h.1 h'.1, h.2.trans h'.2⟩⟩⟩

theorem isClosed_covRel [TopologicalSpace A] [DiscreteTopology A] [Finite A] (hW : FinW W)
  (hP : IsPaired W)
    (hg : SideConst W g) : IsClosed {p : (Dsk W × A) × (Dsk W × A) | covRel W g p.1 p.2} := by
  classical
  have hS := finite_sides hW
  let Ix : Set ((ℕ × ℕ) × (ℕ × ℕ) × Bool × Bool) :=
    {d | ∃ k, (W d.1.1)[d.1.2]? = some (k, d.2.2.1) ∧ (W d.2.1.1)[d.2.1.2]? = some (k, d.2.2.2)
      ∧ d.1 ≠ d.2.1}
  have hIx : Ix.Finite := by
    refine ((hS.prod (hS.prod (finite_univ (α := Bool × Bool)))).image
      fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2)).subset ?_
    rintro ⟨x, y, e, e'⟩ ⟨k, h1, h2, -⟩
    exact ⟨(x, y, e, e'), ⟨⟨_, h1⟩, ⟨_, h2⟩, mem_univ _⟩, rfl⟩
  have hc : ∀ d : (ℕ × ℕ) × (ℕ × ℕ) × Bool × Bool, ∃ c : A, d ∈ Ix → ∀ u ∈ Icc (0 : ℝ) 1,
      g (spt W d.2.1.1 d.2.1.2 (flp d.2.2.1 d.2.2.2 u)) = c + g (spt W d.1.1 d.1.2 u) := by
    intro d
    by_cases hd : d ∈ Ix
    · obtain ⟨k, h1, h2, h3⟩ := hd
      obtain ⟨c, hc⟩ := hg _ _ _ _ k _ _ h1 h2 h3
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using hc
  let E : (ℕ × ℕ) × (ℕ × ℕ) × Bool × Bool → Set ((ℕ × ℂ) × (ℕ × ℂ)) := fun d =>
    (fun u => (spt W d.1.1 d.1.2 u, spt W d.2.1.1 d.2.1.2 (flp d.2.2.1 d.2.2.2 u))) '' Icc (0 : ℝ) 1
  have hE : ∀ d, IsClosed (E d) := by
    intro d
    refine (isCompact_Icc.image ?_).isClosed
    have h1 : ∀ i p, Continuous (spt W i p) := fun i p => by
      unfold spt
      have := continuous_per (W i).length
      fun_prop
    have h2 : Continuous (flp d.2.2.1 d.2.2.2) := by
      unfold flp
      split_ifs <;> fun_prop
    exact (h1 _ _).prodMk ((h1 _ _).comp h2)
  let R1 : Set ((Dsk W × A) × (Dsk W × A)) := {p | p.1 = p.2}
  let R2 : Set ((Dsk W × A) × (Dsk W × A)) :=
    ⋃ d ∈ Ix, {p | (p.1.1.1, p.2.1.1) ∈ E d ∧ p.2.2 - p.1.2 = c d}
  let R3 : Set ((Dsk W × A) × (Dsk W × A)) :=
    {p | p.1.1.1 ∈ crn W ∧ p.2.1.1 ∈ crn W ∧ covRel W g p.1 p.2}
  have hR2 : IsClosed R2 := by
    refine hIx.isClosed_biUnion fun d _ => ?_
    change IsClosed ({p : (Dsk W × A) × (Dsk W × A) | (p.1.1.1, p.2.1.1) ∈ E d} ∩
      {p : (Dsk W × A) × (Dsk W × A) | p.2.2 - p.1.2 = c d})
    apply IsClosed.inter
    · have h1 : Continuous fun p : (Dsk W × A) × (Dsk W × A) => (p.1.1.1, p.2.1.1) := by fun_prop
      exact (hE d).preimage h1
    · have h1 : Continuous fun p : (Dsk W × A) × (Dsk W × A) => (p.1.2, p.2.2) := by fun_prop
      exact (isClosed_discrete {x : A × A | x.2 - x.1 = c d}).preimage h1
  have hR3 : R3.Finite := by
    have hinj : InjOn (fun p : (Dsk W × A) × (Dsk W × A) => ((p.1.1.1, p.2.1.1), p.1.2, p.2.2)) R3
      := by
      rintro ⟨⟨a, s⟩, ⟨b, t⟩⟩ _ ⟨⟨a', s'⟩, ⟨b', t'⟩⟩ _ he
      simp only [Prod.mk.injEq] at he
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := he
      rw [Subtype.ext h1, Subtype.ext h2, h3, h4]
    refine Set.Finite.of_finite_image (((finite_crn hW).prod (finite_crn hW)).prod (toFinite
      (univ : Set (A × A))) |>.subset ?_) hinj
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨hp.1, hp.2.1⟩, mem_univ _⟩
  have hsym : ∀ x y, Stp W x y → Stp W y x := fun _ _ h => h.symm
  have hstepmem : ∀ p : (Dsk W × A) × (Dsk W × A), Stp W p.1.1.1 p.2.1.1 → covRel W g p.1 p.2
    → p ∈ R2 := by
    rintro ⟨⟨⟨a, ha⟩, s⟩, ⟨⟨b, hb⟩, t⟩⟩ hs hr
    obtain ⟨i, j, p, q, k, e, e', u, h1, h2, h3, hu, ha', hb'⟩ := stp_iff.mp hs
    simp only at ha' hb'
    subst ha' hb'
    have hd : ((i, p), (j, q), e, e') ∈ Ix := ⟨k, h1, h2, h3⟩
    refine mem_biUnion hd ⟨⟨u, hu, rfl⟩, ?_⟩
    have h4 := hc _ hd u hu
    have h5 : -g (spt W i p u) + s = -g (spt W j q (flp e e' u)) + t := hr.2
    simp only at h4
    change t - s = _
    rw [h4, neg_add_rev, add_assoc] at h5
    rw [add_left_cancel h5, sub_eq_add_neg, neg_add_rev, neg_neg, add_neg_cancel_left]
  have e : {p : (Dsk W × A) × (Dsk W × A) | covRel W g p.1 p.2} = R1 ∪ R2 ∪ R3 := by
    ext ⟨x, y⟩
    constructor
    · intro hr
      have hr' : covRel W g x y := hr
      by_cases ha : x.1.1 ∈ crn W
      · by_cases hb : y.1.1 ∈ crn W
        · exact .inr ⟨ha, hb, hr'⟩
        · rcases prel_of_not_crn hP y.1.2 hb (.symm _ _ hr'.1) with h | h
          · refine .inl (.inl (Prod.ext (Subtype.ext h) ?_))
            have h2 := hr'.2
            rw [h] at h2
            exact add_left_cancel h2
          · exact .inl (.inr (hstepmem (x, y) (hsym _ _ h) hr'))
      · rcases prel_of_not_crn hP x.1.2 ha hr'.1 with h | h
        · refine .inl (.inl (Prod.ext (Subtype.ext h.symm) ?_))
          have h2 := hr'.2
          rw [h] at h2
          exact add_left_cancel h2
        · exact .inl (.inr (hstepmem (x, y) h hr'))
    · rintro ((h | h) | h)
      · have h' : x = y := h
        subst h'
        exact ⟨.refl _, rfl⟩
      · obtain ⟨d, hd, ⟨u, hu, he⟩, h3⟩ := mem_iUnion₂.mp h
        obtain ⟨h1, h2⟩ := Prod.mk.inj he
        obtain ⟨k, hk1, hk2, hk3⟩ := hd
        have hs : Stp W x.1.1 y.1.1 := by
          rw [← h1, ← h2]
          exact stp_iff.mpr ⟨_, _, _, _, k, _, _, u, hk1, hk2, hk3, hu, rfl, rfl⟩
        refine ⟨.rel _ _ hs, ?_⟩
        have h4 := hc d ⟨k, hk1, hk2, hk3⟩ u hu
        rw [h1, h2] at h4
        have h5 : y.2 - x.2 = c d := h3
        change -g x.1.1 + x.2 = -g y.1.1 + y.2
        rw [h4, ← h5]
        simp only [sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc, neg_add_cancel, add_zero]
      · exact h.2.2
  rw [e]
  exact (isClosed_eq continuous_fst continuous_snd |>.union hR2).union hR3.isClosed

theorem finite_freeSides (hW : FinW W) : {x : ℕ × ℕ | x.2 < (W x.1).length
  ∧ FreeSide W x.1 x.2}.Finite := by
  refine (finite_sides hW).subset ?_
  rintro ⟨i, p⟩ ⟨h1, -⟩
  exact ⟨(W i)[p]'h1, List.getElem?_eq_getElem h1⟩

/-- A function on the sides gives a local cocycle with this function as a primitive. If the function
is constant on each
free side, then the local cocycle vanishes on the boundary. -/
theorem exists_cocycle {Y : Type u} [TopologicalSpace Y] [T2Space Y] [Finite A] {f : ℕ × ℂ → Y}
  (hW : FinW W)
    (hP : IsPaired W) (hf : Presents W f) (hg : SideConst W g) (h0 : W 0 ≠ []) :
    ∃ φ : Y → Y → A, IsCoc φ ∧ IsPrim φ (fun z => f (0, z)) (fun z => g (0, z)) ∧
      ((∀ i p, p < (W i).length → FreeSide W i p → ∃ c, ∀ u ∈ Icc (0 : ℝ) 1, g (spt W i p u) = c)
        → BdTriv φ) := by
  classical
  let _ : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hcD := compactSpace_dsk hW
  have ht : T2Space (Quotient (covSetoid W g)) :=
    t2Space_quotient_of_isClosed (covSetoid W g) (isClosed_covRel hW hP hg)
  let Z := Quotient (covSetoid W g)
  let mk : Dsk W × A → Z := Quotient.mk (covSetoid W g)
  have hmk : Continuous mk := continuous_quotient_mk'
  have hsound : ∀ {x y : Dsk W × A}, PRel W x.1.1 y.1.1 → -g x.1.1 + x.2 = -g y.1.1 + y.2 → mk x
    = mk y :=
    fun h1 h2 => Quotient.sound ⟨h1, h2⟩
  have hexact : ∀ {x y : Dsk W × A}, mk x = mk y → PRel W x.1.1 y.1.1 ∧ -g x.1.1 + x.2
    = -g y.1.1 + y.2 :=
    fun h => Quotient.exact h
  let τ : A → Z → Z := fun s => Quotient.lift (fun x => mk (x.1, x.2 + s)) (fun x y h => hsound h.1
    (by
    have h2 : -g x.1.1 + x.2 = -g y.1.1 + y.2 := h.2
    simp only
    rw [← add_assoc, h2, add_assoc]))
  have hτmk : ∀ s x, τ s (mk x) = mk (x.1, x.2 + s) := fun _ _ => rfl
  have hτc : ∀ s, Continuous (τ s) := fun s =>
    Continuous.quotient_lift (hmk.comp (by fun_prop)) _
  have hexZ : ∀ z : Z, ∃ x, mk x = z := fun z => Quotient.exists_rep z
  have hτ0 : ∀ z, τ 0 z = z := by
    intro z
    obtain ⟨x, rfl⟩ := hexZ z
    rw [hτmk, add_zero]
  have hτa : ∀ s t z, τ s (τ t z) = τ (t + s) z := by
    intro s t z
    obtain ⟨x, rfl⟩ := hexZ z
    rw [hτmk, hτmk, hτmk, add_assoc]
  have hfree : ∀ s z, τ s z = z → s = 0 := by
    intro s z he
    obtain ⟨x, rfl⟩ := hexZ z
    rw [hτmk] at he
    have h1 := (hexact he).2
    simp only at h1
    exact add_eq_left.mp (add_left_cancel h1)
  let q : Z → Y := Quotient.lift (fun x => f x.1.1) (fun x y h => (hf.2.2 _ x.1.2 _ y.1.2).mpr h.1)
  have hqmk : ∀ x, q (mk x) = f x.1.1 := fun _ => rfl
  have hfc : Continuous fun x : Dsk W => f x.1 := hf.1.comp_continuous continuous_subtype_val fun x
    => x.2
  have hq : Continuous q := Continuous.quotient_lift (hfc.comp continuous_fst) _
  have hlift : ∀ y : Y, ∃ a : Dsk W, f a.1 = y := fun y => by
    have h1 : y ∈ f '' Dsk W := by
      rw [hf.2.1]
      exact mem_univ y
    obtain ⟨a, ha, rfl⟩ := h1
    exact ⟨⟨a, ha⟩, rfl⟩
  have hs : Function.Surjective q := fun y => by
    obtain ⟨a, rfl⟩ := hlift y
    exact ⟨mk (a, 0), rfl⟩
  have hfib : ∀ z z', q z = q z' → ∃ s, z' = τ s z := by
    intro z z' he
    obtain ⟨x, rfl⟩ := hexZ z
    obtain ⟨y, rfl⟩ := hexZ z'
    have h1 : PRel W x.1.1 y.1.1 := (hf.2.2 _ x.1.2 _ y.1.2).mp he
    refine ⟨-x.2 + (g x.1.1 + (-g y.1.1 + y.2)), ?_⟩
    rw [hτmk]
    refine hsound (.symm _ _ h1) ?_
    simp only [add_neg_cancel_left, neg_add_cancel_left]
  have hfib' : ∀ s z, q (τ s z) = q z := by
    intro s z
    obtain ⟨x, rfl⟩ := hexZ z
    rfl
  choose l hl using hlift
  let σ : Y → Z := fun y => mk (l y, g (l y).1)
  have hσ : ∀ y, q (σ y) = y := fun y => hl y
  have hσf : ∀ a : Dsk W, σ (f a.1) = mk (a, g a.1) := fun a =>
    hsound ((hf.2.2 _ (l (f a.1)).2 _ a.2).mp (hl _)) (by simp)
  obtain ⟨φ, V, hV, hφ, hφs, hinv⟩ := cocycle_of_cover τ hτc hτ0 hτa hfree q hq hs hfib hfib' σ hσ
  have hba : ∀ z ∈ closedBall (0 : ℂ) 1, ((0 : ℕ), z) ∈ Dsk W := fun z hz => ⟨h0, by simpa using hz⟩
  have hprim : IsPrim φ (fun z => f (0, z)) (fun z => g (0, z)) := by
    let P : ℂ → Z := fun z => if h : z ∈ closedBall (0 : ℂ) 1 then mk (⟨(0, z), hba z h⟩, 0) else
      mk (⟨(0, 0), hba 0 (by simp)⟩, 0)
    have hP : ∀ z (h : z ∈ closedBall (0 : ℂ) 1), P z = mk (⟨(0, z), hba z h⟩, 0) := fun z h => by
      simp only [P, h, dite_eq_left]
    have hPc : ContinuousOn P (closedBall 0 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have e : (closedBall (0 : ℂ) 1).domRestrict P = mk ∘ fun z : closedBall (0 : ℂ) 1 =>
        (⟨(0, z.1), hba z.1 z.2⟩, 0) := by
        funext z
        exact hP z.1 z.2
      rw [e]
      refine hmk.comp (Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_const)
      fun_prop
    obtain ⟨ε, hε, h1⟩ := exists_eps (isCompact_closedBall 0 1) hPc hV
    refine ⟨ε, hε, fun a ha b hb hab => ?_⟩
    have h2 := hinv (g (0, b)) _ _ (h1 a ha b hb hab)
    rw [hP a ha, hP b hb, hτmk, hτmk] at h2
    have e1 := hσf ⟨(0, a), hba a ha⟩
    have e2 := hσf ⟨(0, b), hba b hb⟩
    simp only at e1 e2
    refine hφs _ _ _ ?_
    rw [e1, e2, hτmk]
    simp only [zero_add] at h2 ⊢
    have e3 : g (0, a) + (-g (0, a) + g (0, b)) = g (0, b) := add_neg_cancel_left _ _
    rw [e3]
    exact h2
  refine ⟨φ, hφ, hprim, fun hconst => ?_⟩
  have hbd := (surface_of_presents hW hP hf).2
  have hconst' : ∀ d : ℕ × ℕ, ∃ c, d ∈ {x : ℕ × ℕ | x.2 < (W x.1).length ∧ FreeSide W x.1 x.2} →
      ∀ u ∈ Icc (0 : ℝ) 1, g (spt W d.1 d.2 u) = c := by
    intro d
    by_cases hd : d ∈ {x : ℕ × ℕ | x.2 < (W x.1).length ∧ FreeSide W x.1 x.2}
    · obtain ⟨c, hc⟩ := hconst _ _ hd.1 hd.2
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using hconst'
  have hm : ∀ d ∈ {x : ℕ × ℕ | x.2 < (W x.1).length ∧ FreeSide W x.1 x.2}, ∀ u, spt W d.1 d.2 u ∈
    Dsk W := by
    intro d hd u
    refine ⟨fun he => ?_, (norm_per _ _).le⟩
    have h1 := hd.1
    simp only [spt] at he
    rw [he] at h1
    simp at h1
  let K : Set Z := ⋃ d ∈ {x : ℕ × ℕ | x.2 < (W x.1).length ∧ FreeSide W x.1 x.2},
    (fun u : ℝ => if h : spt W d.1 d.2 u ∈ Dsk W then mk (⟨_, h⟩, c d) else mk (l (f
      (0, 0)), 0)) '' Icc (0 : ℝ) 1
  have hmemK : ∀ d (hd : d ∈ {x : ℕ × ℕ | x.2 < (W x.1).length ∧ FreeSide W x.1 x.2}), ∀ u ∈ Icc
    (0 : ℝ) 1,
      mk (⟨_, hm d hd u⟩, g (spt W d.1 d.2 u)) ∈ K := by
    intro d hd u hu
    refine mem_biUnion hd ⟨u, hu, ?_⟩
    simp only [hm d hd u, dite_eq_left, hc d hd u hu]
  have hKform : ∀ z ∈ K, ∃ a : Dsk W, z = mk (a, g a.1) := by
    intro z hz
    obtain ⟨d, hd, u, hu, rfl⟩ := mem_iUnion₂.mp hz
    refine ⟨⟨_, hm d hd u⟩, ?_⟩
    simp only [hm d hd u, dite_eq_left, hc d hd u hu]
  have hK : IsCompact K := by
    refine (finite_freeSides hW).isCompact_biUnion fun d hd => ?_
    refine isCompact_Icc.image_of_continuousOn ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have e : (Icc (0 : ℝ) 1).domRestrict (fun u : ℝ => if h : spt W d.1 d.2 u ∈ Dsk W then mk
      (⟨_, h⟩, c d)
        else mk (l (f (0, 0)), 0)) = mk ∘ fun u : Icc (0 : ℝ) 1 => (⟨_, hm d hd u.1⟩, c d) := by
      funext u
      simp only [Set.domRestrict_apply, hm d hd u.1, dite_eq_left, Function.comp]
    rw [e]
    refine hmk.comp (Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_const)
    unfold spt
    have := continuous_per (W d.1).length
    fun_prop
  have hne : Nonempty Z := ⟨mk (l (f (0, 0)), 0)⟩
  have hinj : InjOn q K := by
    intro z hz z' hz' he
    obtain ⟨a, rfl⟩ := hKform z hz
    obtain ⟨b, rfl⟩ := hKform z' hz'
    exact hsound ((hf.2.2 _ a.2 _ b.2).mp he) (by simp)
  obtain ⟨q', hq', hql⟩ := exists_inv_of_compactOn hK hq.continuousOn hinj
  have hσK : ∀ x ∈ bd Y, σ x ∈ K := by
    intro x hx
    rw [hbd] at hx
    obtain ⟨a, ⟨i, p, u, hp, hfr, hu, rfl⟩, rfl⟩ := hx
    have hd : (i, p) ∈ {x : ℕ × ℕ | x.2 < (W x.1).length ∧ FreeSide W x.1 x.2} := ⟨hp, hfr⟩
    have h1 := hσf ⟨_, hm (i, p) hd u⟩
    simp only at h1
    rw [h1]
    exact hmemK _ hd u hu
  have hσc : ContinuousOn σ (bd Y) := by
    have hsub : bd Y ⊆ q '' K := fun x hx => ⟨σ x, hσK x hx, hσ x⟩
    refine (hq'.mono hsub).congr fun x hx => ?_
    have h1 := hql (hσK x hx)
    rw [hσ] at h1
    exact h1.symm
  have hcl : IsClosed (bd Y) := isClosed_bd Y
  refine ⟨0, {p | p.1 ∈ bd Y → p.2 ∈ bd Y → (σ p.1, σ p.2) ∈ V}, fun y => ?_,
    fun x hx y hy hxy => ?_⟩
  · by_cases hy : y ∈ bd Y
    · have h1 : ContinuousWithinAt (fun p : Y × Y => (σ p.1, σ p.2)) (bd Y ×ˢ bd Y) (y, y) := by
        have h2 := hσc.prodMap hσc
        exact h2 (y, y) ⟨hy, hy⟩
      have h3 := h1 (hV (σ y))
      obtain ⟨u, hu, hus⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h3
      refine Filter.mem_of_superset hu fun p hp h4 h5 => ?_
      exact hus ⟨hp, h4, h5⟩
    · have h1 : (bd Y)ᶜ ×ˢ (univ : Set Y) ∈ 𝓝 (y, y) := (hcl.isOpen_compl.prod
      isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩
      refine Filter.mem_of_superset h1 fun p hp h4 => ?_
      exact absurd h4 hp.1
  · have h1 := hφs x y 0 (by rw [hτ0]; exact hxy hx hy)
    simp [h1]

end GraphMinor.Surface
