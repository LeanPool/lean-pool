/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Relativized
public import LeanPool.DescriptiveCounting.OrderedComposition

/-!
# Composition of relativized first-order reductions

Transitivity of `P ≤ʳᶠᵒ[≤] Q` (`DescriptiveComplexity.RelOrderedFOReduction.trans`), the
relativized analogue of `DescriptiveComplexity.OrderedFOReduction.trans`. This is the one
piece the hardness rewiring for relativized reductions needs
that does not reduce to `DescriptiveComplexity.OrderedFOReduction.toRel`.

The plain composition of `DescriptiveComplexity.Composition` pulls the outer relation
formulas back through the inner interpretation with quantifiers ranging over
the *whole* inner universe `Tag × A^dim`. On the definable subset that is
wrong: an outer quantifier must range over the *in-domain* points only. The
fix is a **guarded pullback** `DescriptiveComplexity.RelFOInterpretation.pullRel`, which
conjoins each quantifier block with the inner domain formula, and whose
pullback theorem `DescriptiveComplexity.RelFOInterpretation.realize_pullRel` carries an
“environment is in-domain” hypothesis. The composite domain formula is then
the conjunction of the inner domains (one per outer coordinate) with the
pulled-back outer domain, and the two decompose in exactly the way
`realize_pullRel` needs.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure BoundedFormula

variable {L₁ L₂ L₃ : Language.{0, 0}}

/-! ### Guarded pullback of a formula through a relativized interpretation -/

section PullRel

variable {Tag : Type} {d : ℕ} {β : Type}

/-- The in-domain environment of the relativized interpreted structure induced
by tags `τ`, coordinates `v`, and a proof `hv` that each variable's coordinates
satisfy its tag's domain formula. -/
def RelFOInterpretation.liftEnvRel (I : RelFOInterpretation L₁ L₂ Tag d) {A : Type}
    [L₁.Structure A] {γ : Type} (τ : γ → Tag) (v : γ × Fin d → A)
    (hv : ∀ b, (I.domFormula (τ b)).Realize fun j => v (b, j)) (b : γ) : I.MapRel A :=
  ⟨(τ b, fun j => v (b, j)), hv b⟩

open Classical in
/-- Guarded pullback of an `L₂`-formula through the relativized interpretation
`I`: as `DescriptiveComplexity.FOInterpretation.pull`, but each quantifier block is guarded
by the domain formula of its tag, so that it ranges over the definable subset
`I.MapRel A` rather than all of `Tag × A^dim`. -/
noncomputable def RelFOInterpretation.pullRel (I : RelFOInterpretation L₁ L₂ Tag d)
    [L₂.IsRelational] [Finite Tag] :
    ∀ {n : ℕ}, L₂.BoundedFormula β n → ((β ⊕ Fin n) → Tag) → L₁.Formula ((β ⊕ Fin n) × Fin d)
  | _, .falsum, _ => ⊥
  | _, .equal t₁ t₂, τ =>
      if τ t₁.varOf = τ t₂.varOf then
        Formula.iInf fun j : Fin d =>
          Term.equal (Term.var (t₁.varOf, j)) (Term.var (t₂.varOf, j))
      else ⊥
  | _, .rel R ts, τ =>
      (I.relFormula R fun i => τ (ts i).varOf).relabel fun p => ((ts p.1).varOf, p.2)
  | _, .imp φ ψ, τ =>
      (RelFOInterpretation.pullRel I φ τ).imp (RelFOInterpretation.pullRel I ψ τ)
  | _, .all φ, τ =>
      Formula.iInf fun t : Tag =>
        (((I.domFormula t).relabel Sum.inr).imp
          ((RelFOInterpretation.pullRel I φ (extendTag τ t)).relabel splitLast)).iAlls (Fin d)

variable (I : RelFOInterpretation L₁ L₂ Tag d) [L₂.IsRelational] [Finite Tag] {A : Type}
  [L₁.Structure A]

theorem RelFOInterpretation.realize_pullRel {n : ℕ} (φ : L₂.BoundedFormula β n)
    (τ : (β ⊕ Fin n) → Tag) (v : ((β ⊕ Fin n) × Fin d) → A)
    (hv : ∀ b, (I.domFormula (τ b)).Realize fun j => v (b, j)) :
    (I.pullRel φ τ).Realize v ↔
      φ.Realize (M := I.MapRel A) (I.liftEnvRel τ v hv ∘ Sum.inl)
        (I.liftEnvRel τ v hv ∘ Sum.inr) := by
  induction φ with
  | falsum =>
    simp only [RelFOInterpretation.pullRel, Formula.realize_bot, false_iff]
    exact fun h => h
  | equal t₁ t₂ =>
    have hRHS : (BoundedFormula.equal t₁ t₂).Realize (M := I.MapRel A)
        (I.liftEnvRel τ v hv ∘ Sum.inl) (I.liftEnvRel τ v hv ∘ Sum.inr) ↔
        I.liftEnvRel τ v hv t₁.varOf = I.liftEnvRel τ v hv t₂.varOf := by
      rw [show (BoundedFormula.equal t₁ t₂).Realize (M := I.MapRel A)
          (I.liftEnvRel τ v hv ∘ Sum.inl) (I.liftEnvRel τ v hv ∘ Sum.inr) ↔
          t₁.realize (Sum.elim (I.liftEnvRel τ v hv ∘ Sum.inl) (I.liftEnvRel τ v hv ∘ Sum.inr)) =
            t₂.realize (Sum.elim (I.liftEnvRel τ v hv ∘ Sum.inl)
              (I.liftEnvRel τ v hv ∘ Sum.inr)) from Iff.rfl]
      simp [Sum.elim_comp_inl_inr]
    rw [hRHS]
    simp only [RelFOInterpretation.pullRel]
    split_ifs with h
    · rw [Formula.realize_iInf]
      simp only [Formula.realize_equal, Term.realize_var]
      constructor
      · intro hj
        apply Subtype.ext
        exact Prod.ext_iff.mpr ⟨h, funext hj⟩
      · intro hpq j
        exact congrFun (congrArg Prod.snd (congrArg Subtype.val hpq)) j
    · simp only [Formula.realize_bot, false_iff]
      exact fun hpq => h (congrArg Prod.fst (congrArg Subtype.val hpq))
  | rel R ts =>
    have hRHS : (BoundedFormula.rel R ts).Realize (M := I.MapRel A)
        (I.liftEnvRel τ v hv ∘ Sum.inl) (I.liftEnvRel τ v hv ∘ Sum.inr) ↔
        RelMap (M := I.MapRel A) R fun i => I.liftEnvRel τ v hv (ts i).varOf := by
      rw [show (BoundedFormula.rel R ts).Realize (M := I.MapRel A)
          (I.liftEnvRel τ v hv ∘ Sum.inl) (I.liftEnvRel τ v hv ∘ Sum.inr) ↔
          RelMap (M := I.MapRel A) R fun i =>
            (ts i).realize (Sum.elim (I.liftEnvRel τ v hv ∘ Sum.inl)
              (I.liftEnvRel τ v hv ∘ Sum.inr)) from Iff.rfl]
      simp [Sum.elim_comp_inl_inr]
    rw [hRHS, RelFOInterpretation.relMap_mapRel]
    simp only [RelFOInterpretation.pullRel, Formula.realize_relabel]
    exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    rw [RelFOInterpretation.pullRel]
    simp only [Formula.realize_imp, BoundedFormula.realize_imp]
    rw [ihφ τ v hv, ihψ τ v hv]
  | all φ ih =>
    simp only [RelFOInterpretation.pullRel, Formula.realize_iInf, Formula.realize_iAlls,
      Formula.realize_imp, Formula.realize_relabel, BoundedFormula.realize_all]
    have hE₁ : ∀ (t : Tag) (w : Fin d → A)
        (hw : ∀ b, (I.domFormula (extendTag τ t b)).Realize
          fun j => (Sum.elim v w ∘ splitLast) (b, j)),
        I.liftEnvRel (extendTag τ t) (Sum.elim v w ∘ splitLast) hw ∘ Sum.inl =
          I.liftEnvRel τ v hv ∘ Sum.inl := by
      intro t w hw
      funext b
      apply Subtype.ext
      rfl
    have hlast : ∀ {m : ℕ} (g : Fin m → I.MapRel A) (a : I.MapRel A),
        Fin.snoc (α := fun _ => I.MapRel A) g a (Fin.last m) = a := fun g a => by simp
    have hcs : ∀ {m : ℕ} (g : Fin m → I.MapRel A) (a : I.MapRel A) (i' : Fin m),
        Fin.snoc (α := fun _ => I.MapRel A) g a i'.castSucc = g i' := fun g a i' => by simp
    have hE₂ : ∀ (t : Tag) (w : Fin d → A)
        (hw : ∀ b, (I.domFormula (extendTag τ t b)).Realize
          fun j => (Sum.elim v w ∘ splitLast) (b, j))
        (hq : (I.domFormula t).Realize w),
        I.liftEnvRel (extendTag τ t) (Sum.elim v w ∘ splitLast) hw ∘ Sum.inr =
          Fin.snoc (I.liftEnvRel τ v hv ∘ Sum.inr) ⟨(t, w), hq⟩ := by
      intro t w hw hq
      funext i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Eq.trans ?_ (hlast _ _).symm
        apply Subtype.ext
        change ((extendTag τ t (Sum.inr (Fin.last _)),
          fun j => (Sum.elim v w ∘ splitLast) (Sum.inr (Fin.last _), j)) : Tag × (Fin d → A)) =
          (t, w)
        unfold extendTag
        congr 1
        · simp
        · funext j
          simp [splitLast]
      · refine Eq.trans ?_ (hcs _ _ _).symm
        apply Subtype.ext
        change ((extendTag τ t (Sum.inr i'.castSucc),
          fun j => (Sum.elim v w ∘ splitLast) (Sum.inr i'.castSucc, j)) : Tag × (Fin d → A)) =
          (τ (Sum.inr i'), fun j => v (Sum.inr i', j))
        unfold extendTag
        congr 1
        · simp
        · funext j
          simp [splitLast]
    constructor
    · intro h q
      obtain ⟨⟨t, w⟩, hq⟩ := q
      have hw : ∀ b, (I.domFormula (extendTag τ t b)).Realize
          fun j => (Sum.elim v w ∘ splitLast) (b, j) := by
        rintro (b | i)
        · exact hv (Sum.inl b)
        · refine Fin.lastCases ?_ (fun i' => ?_) i
          · have : (fun j => (Sum.elim v w ∘ splitLast) (Sum.inr (Fin.last _), j)) = w := by
              funext j; simp [splitLast]
            rw [show extendTag τ t (Sum.inr (Fin.last _)) = t by simp [extendTag], this]
            exact hq
          · have : (fun j => (Sum.elim v w ∘ splitLast) (Sum.inr i'.castSucc, j)) =
                (fun j => v (Sum.inr i', j)) := by funext j; simp [splitLast]
            rw [show extendTag τ t (Sum.inr i'.castSucc) = τ (Sum.inr i') by simp [extendTag],
              this]
            exact hv (Sum.inr i')
      have := (ih (extendTag τ t) (Sum.elim v w ∘ splitLast) hw).mp (h t w hq)
      rwa [hE₁ t w hw, hE₂ t w hw hq] at this
    · intro h t w hq
      have hw : ∀ b, (I.domFormula (extendTag τ t b)).Realize
          fun j => (Sum.elim v w ∘ splitLast) (b, j) := by
        rintro (b | i)
        · exact hv (Sum.inl b)
        · refine Fin.lastCases ?_ (fun i' => ?_) i
          · have : (fun j => (Sum.elim v w ∘ splitLast) (Sum.inr (Fin.last _), j)) = w := by
              funext j; simp [splitLast]
            rw [show extendTag τ t (Sum.inr (Fin.last _)) = t by simp [extendTag], this]
            exact hq
          · have : (fun j => (Sum.elim v w ∘ splitLast) (Sum.inr i'.castSucc, j)) =
                (fun j => v (Sum.inr i', j)) := by funext j; simp [splitLast]
            rw [show extendTag τ t (Sum.inr i'.castSucc) = τ (Sum.inr i') by simp [extendTag],
              this]
            exact hv (Sum.inr i')
      refine (ih (extendTag τ t) (Sum.elim v w ∘ splitLast) hw).mpr ?_
      rw [hE₁ t w hw, hE₂ t w hw hq]
      exact h ⟨(t, w), hq⟩

end PullRel

/-! ### Composition of relativized interpretations -/

section Comp

variable {Tag₁ Tag₂ : Type} {d₁ d₂ : ℕ}
variable [L₂.IsRelational] [L₃.IsRelational] [Finite Tag₁]
variable (J : RelFOInterpretation L₂ L₃ Tag₂ d₂) (I : RelFOInterpretation L₁ L₂ Tag₁ d₁)

/-- The relabeling of the composite's coordinates onto a `d₂ × d₁` matrix. -/
def compRelabel {n : ℕ} :
    (((Fin n × Fin d₂) ⊕ Fin 0) × Fin d₁) → (Fin n × Fin (d₂ * d₁))
  | (.inl p, j) => (p.1, finProdFinEquiv (p.2, j))
  | (.inr z, _) => z.elim0

/-- The relabeling of the composite domain formula's coordinates. -/
def compDomRelabel :
    (((Fin d₂ ⊕ Fin 0) × Fin d₁)) → Fin (d₂ * d₁)
  | (.inl k, j) => finProdFinEquiv (k, j)
  | (.inr z, _) => z.elim0

/-- The composite of two relativized interpretations: like
`DescriptiveComplexity.FOInterpretation.comp`, but the relation formulas are pulled back with
the **guarded** pullback, and the domain formula asks each outer coordinate's
inner tuple to be in the inner domain and the outer tuple (of inner points) to
be in the outer domain. -/
noncomputable def RelFOInterpretation.compRel :
    RelFOInterpretation L₁ L₃ (Tag₂ × (Fin d₂ → Tag₁)) (d₂ * d₁) where
  relFormula {_n} R T :=
    (I.pullRel (J.relFormula R fun i => (T i).1)
        (Sum.elim (fun p => (T p.1).2 p.2) Fin.elim0)).relabel compRelabel
  domFormula := fun T =>
    (Formula.iInf fun k : Fin d₂ =>
        (I.domFormula (T.2 k)).relabel fun j => finProdFinEquiv (k, j)) ⊓
      (I.pullRel (J.domFormula T.1) (Sum.elim T.2 Fin.elim0)).relabel compDomRelabel

variable {A : Type} [L₁.Structure A]

omit [L₃.IsRelational] in
/-- The composite domain decomposes: each outer coordinate is in the inner
domain, and – given that – the outer tuple of inner points is in the outer
domain. -/
theorem RelFOInterpretation.realize_compRel_domFormula (T : Tag₂ × (Fin d₂ → Tag₁))
    (coords : Fin (d₂ * d₁) → A) :
    ((J.compRel I).domFormula T).Realize coords ↔
      ∃ h : ∀ k, (I.domFormula (T.2 k)).Realize fun j => coords (finProdFinEquiv (k, j)),
        (J.domFormula T.1).Realize (M := I.MapRel A)
          fun k => ⟨(T.2 k, fun j => coords (finProdFinEquiv (k, j))), h k⟩ := by
  rw [RelFOInterpretation.compRel]
  simp only [Formula.realize_inf, Formula.realize_iInf, Formula.realize_relabel]
  have hv : ∀ (h1 : ∀ k, (I.domFormula (T.2 k)).Realize fun j => coords (finProdFinEquiv (k, j))),
      ∀ b, (I.domFormula ((Sum.elim T.2 Fin.elim0) b)).Realize
        fun j => coords (compDomRelabel (b, j)) := by
    intro h1 b
    rcases b with k | z
    · exact h1 k
    · exact z.elim0
  have henv : ∀ (h1 : ∀ k,
        (I.domFormula (T.2 k)).Realize fun j => coords (finProdFinEquiv (k, j))),
      (I.liftEnvRel (Sum.elim T.2 Fin.elim0) (fun p => coords (compDomRelabel p)) (hv h1)
          ∘ Sum.inl) =
        fun k => (⟨(T.2 k, fun j => coords (finProdFinEquiv (k, j))), h1 k⟩ : I.MapRel A) := by
    intro h1; funext k; apply Subtype.ext; rfl
  have henv2 : ∀ (h1 : ∀ k,
        (I.domFormula (T.2 k)).Realize fun j => coords (finProdFinEquiv (k, j))),
      (I.liftEnvRel (Sum.elim T.2 Fin.elim0) (fun p => coords (compDomRelabel p)) (hv h1)
          ∘ Sum.inr) = (default : Fin 0 → I.MapRel A) :=
    fun h1 => funext fun i => i.elim0
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => h1 k, ?_⟩
    have key := (I.realize_pullRel (J.domFormula T.1) (Sum.elim T.2 Fin.elim0)
      (fun p => coords (compDomRelabel p)) (hv (fun k => h1 k))).mp h2
    rw [henv (fun k => h1 k), henv2 (fun k => h1 k)] at key
    exact key
  · rintro ⟨hinner, h2⟩
    refine ⟨fun k => hinner k, ?_⟩
    refine (I.realize_pullRel (J.domFormula T.1) (Sum.elim T.2 Fin.elim0)
      (fun p => coords (compDomRelabel p)) (hv hinner)).mpr ?_
    rw [henv hinner, henv2 hinner]
    exact h2

/-- The universe of the composite relativized interpretation is equivalent to
the twice-interpreted universe, as subtypes. -/
noncomputable def RelFOInterpretation.compEquivRel :
    (J.compRel I).MapRel A ≃ J.MapRel (I.MapRel A) where
  toFun x :=
    let h := (J.realize_compRel_domFormula I x.1.1 x.1.2).mp x.2
    ⟨(x.1.1.1, fun k => ⟨(x.1.1.2 k, fun j => x.1.2 (finProdFinEquiv (k, j))), h.choose k⟩),
      h.choose_spec⟩
  invFun y :=
    ⟨((y.1.1, fun k => (y.1.2 k).1.1),
        fun m => (y.1.2 (finProdFinEquiv.symm m).1).1.2 (finProdFinEquiv.symm m).2), by
      refine (J.realize_compRel_domFormula I _ _).mpr ?_
      have hcoord : ∀ (k : Fin d₂) (j : Fin d₁),
          (fun m => (y.1.2 (finProdFinEquiv.symm m).1).1.2 (finProdFinEquiv.symm m).2)
            (finProdFinEquiv (k, j)) = (y.1.2 k).1.2 j := by
        intro k j; simp only [Equiv.symm_apply_apply]
      have hinner : ∀ k, (I.domFormula (y.1.2 k).1.1).Realize
          (fun j => (fun m => (y.1.2 (finProdFinEquiv.symm m).1).1.2 (finProdFinEquiv.symm m).2)
            (finProdFinEquiv (k, j))) :=
        fun k => by rw [funext (hcoord k)]; exact (y.1.2 k).2
      refine ⟨hinner, ?_⟩
      have henv : (fun k => (⟨((y.1.2 k).1.1,
          fun j => (fun m => (y.1.2 (finProdFinEquiv.symm m).1).1.2 (finProdFinEquiv.symm m).2)
            (finProdFinEquiv (k, j))), hinner k⟩ : I.MapRel A)) = y.1.2 :=
        funext fun k => Subtype.ext (Prod.ext rfl (funext (hcoord k)))
      rw [henv]; exact y.2⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨⟨⟨t, tg⟩, w⟩, hx⟩ := x
    refine Prod.ext (Prod.ext rfl rfl) (funext fun m => ?_)
    change w (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)) = w m
    rw [show ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2) =
      finProdFinEquiv.symm m from rfl, Equiv.apply_symm_apply]
  right_inv y := by
    apply Subtype.ext
    obtain ⟨⟨t, u⟩, hy⟩ := y
    refine Prod.ext rfl (funext fun k => ?_)
    apply Subtype.ext
    refine Prod.ext rfl (funext fun j => ?_)
    change (u (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).1.2
        (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2 = (u k).1.2 j
    rw [Equiv.symm_apply_apply]

theorem RelFOInterpretation.relMap_compRel {n : ℕ} (R : L₃.Relations n)
    (x : Fin n → (J.compRel I).MapRel A) :
    RelMap (M := (J.compRel I).MapRel A) R x ↔
      RelMap (M := J.MapRel (I.MapRel A)) R (J.compEquivRel I ∘ x) := by
  rw [RelFOInterpretation.relMap_mapRel, RelFOInterpretation.relMap_mapRel]
  simp only [RelFOInterpretation.compRel, Formula.realize_relabel]
  rw [I.realize_pullRel (J.relFormula R fun i => (x i).1.1.1)
    (Sum.elim (fun p => (x p.1).1.1.2 p.2) Fin.elim0)
    ((fun p => (x p.1).1.2 p.2) ∘ compRelabel) (by
      rintro (p | z)
      · exact ((J.realize_compRel_domFormula I (x p.1).1.1 (x p.1).1.2).mp (x p.1).2).choose p.2
      · exact z.elim0)]
  refine iff_of_eq ?_
  congr 1
  funext i
  exact i.elim0

/-- The universe equivalence of the composite relativized interpretation is an
`L₃`-isomorphism. -/
noncomputable def RelFOInterpretation.compLEquivRel :
    (J.compRel I).MapRel A ≃[L₃] J.MapRel (I.MapRel A) where
  toEquiv := J.compEquivRel I
  map_fun' := fun f => isEmptyElim f
  map_rel' := fun R x => (J.relMap_compRel I R x).symm

end Comp

/-! ### Extending a relativized interpretation with the lexicographic order -/

section OrdExtend

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational]
variable {T : Type} [LinearOrder T] {d : ℕ}

/-- Extension of a relativized interpretation over an ordered base to one whose
target carries the order vocabulary, interpreted by the lexicographic order on
tagged tuples. The domain formula is unchanged. -/
noncomputable def RelFOInterpretation.ordExtendRel
    (I : RelFOInterpretation (L₁.sum Language.order) L₂ T d) :
    RelFOInterpretation (L₁.sum Language.order) (L₂.sum Language.order) T d where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl r => I.relFormula r
    | _, Sum.inr .le => fun t => lexLeF L₁ d (t 0) (t 1)
  domFormula := I.domFormula

variable (I : RelFOInterpretation (L₁.sum Language.order) L₂ T d)
variable (A : Type) [L₁.Structure A] [LinearOrder A]

/-- The lexicographic linear order on the relativized interpreted universe,
restricted from the tagged-tuple order along `Subtype.val`. -/
@[instance_reducible]
noncomputable def RelFOInterpretation.mapRelLinearOrder : LinearOrder (I.MapRel A) :=
  letI := tagTupleOrder (Tag := T) (d := d) (A := A)
  LinearOrder.lift' (Subtype.val : I.MapRel A → T × (Fin d → A)) Subtype.val_injective

/-- The order-extended relativized interpretation produces exactly the original
relativized interpreted structure equipped with the lexicographic order. -/
noncomputable def RelFOInterpretation.ordExtendRelLEquiv :
    @Language.Equiv (L₂.sum Language.order) (I.ordExtendRel.MapRel A) (I.MapRel A)
      (RelFOInterpretation.mapRelStructure I.ordExtendRel A)
      (letI := I.mapRelLinearOrder A; sumOrderStructure L₂ (I.MapRel A)) :=
  letI := I.mapRelLinearOrder A
  { toEquiv := Equiv.refl _
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      cases R with
      | inl r => exact Iff.rfl
      | inr r =>
        cases r with
        | le =>
          exact ((realize_lexLeF (L := L₁) (A := A) (Tag := T) (d := d)
              (t₁ := (x 0).1.1) (t₂ := (x 1).1.1) (v := fun p => (x p.1).1.2 p.2)).trans
            (tagTupleLe_iff_le (x 0).1 (x 1).1)).symm }

end OrdExtend

/-! ### Transitivity of relativized ordered reductions -/

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂} {R : DecisionProblem L₃}

/-- **Transitivity of relativized ordered FO reductions**: if `P ≤ʳᶠᵒ[≤] Q` and
`Q ≤ʳᶠᵒ[≤] R`, then `P ≤ʳᶠᵒ[≤] R`. The intermediate definable structure is
ordered by the lexicographic order on tagged tuples, restricted to the domain. -/
noncomputable def RelOrderedFOReduction.trans (g : P ≤ʳᶠᵒ[≤] Q) (f : Q ≤ʳᶠᵒ[≤] R) :
    P ≤ʳᶠᵒ[≤] R :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toRelInterpretation := f.toRelInterpretation.compRel g.toRelInterpretation.ordExtendRel
    dom_nonempty := fun A _ _ _ _ => by
      let := g.toRelInterpretation.mapRelLinearOrder A
      have : Finite (g.toRelInterpretation.MapRel A) := g.toRelInterpretation.mapRel_finite A
      have : Nonempty (g.toRelInterpretation.MapRel A) := g.mapRel_nonempty A
      have e1 := g.toRelInterpretation.ordExtendRelLEquiv A
      have e2 := f.toRelInterpretation.mapRelLEquiv e1
      have e3 := f.toRelInterpretation.compLEquivRel g.toRelInterpretation.ordExtendRel (A := A)
      obtain ⟨y⟩ := f.mapRel_nonempty (g.toRelInterpretation.MapRel A)
      obtain ⟨⟨t, w⟩, hw⟩ := (e2.comp e3).symm y
      exact ⟨t, w, hw⟩
    correct := fun A _ _ _ _ => by
      let := g.toRelInterpretation.mapRelLinearOrder A
      have : Finite (g.toRelInterpretation.MapRel A) := g.toRelInterpretation.mapRel_finite A
      have : Nonempty (g.toRelInterpretation.MapRel A) := g.mapRel_nonempty A
      have h1 := g.correct A
      have h2 := f.correct (g.toRelInterpretation.MapRel A)
      have e1 := g.toRelInterpretation.ordExtendRelLEquiv A
      have e2 := f.toRelInterpretation.mapRelLEquiv e1
      have e3 := f.toRelInterpretation.compLEquivRel g.toRelInterpretation.ordExtendRel (A := A)
      exact (h1.trans h2).trans (R.iso_invariant (e2.comp e3)).symm }

/-- `Trans` instance for relativized ordered FO reductions. -/
noncomputable instance :
    Trans (α := DecisionProblem L₁) (β := DecisionProblem L₂) (γ := DecisionProblem L₃)
      RelOrderedFOReduction RelOrderedFOReduction RelOrderedFOReduction where
  trans g f := g.trans f

end Trans

end DescriptiveComplexity
