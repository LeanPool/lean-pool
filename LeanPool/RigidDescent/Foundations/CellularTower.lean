/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.Telescope

/-!
# Cellular towers

Let `H : Tᵒᵖ ⥤ AddCommGrpCat` be additive, cohomological (`IsCohomological`) and send
coproducts to products (`SendsCoproductsToProducts`), and let `g : κ → T` be a family of
compact objects. We kill maps from the `g k` one stage at a time:

* `X₀ = ∐` over pairs `(k, h ∈ H(g k))` of `g k`, with `u₀ ∈ H(X₀)` restricting to `h` on the
  summand `(k, h)`;
* `Xₙ₊₁` is the cone of `∐_{(k, b)} g k ⟶ Xₙ`, over the maps `b : g k ⟶ Xₙ` with
  `b^* uₙ = 0`, and `uₙ₊₁ ∈ H(Xₙ₊₁)` lifts `uₙ`;
* `X∞` is the telescope, and `u∞ ∈ H(X∞)` lifts the compatible family `(uₙ)`.

Then `a ↦ a^* u∞` is a bijection `Hom(g k, X∞) ≅ H(g k)` for every `k`
(`CellularTower.bijective`): it is surjective at stage `0`; and if `a^* u∞ = 0`, then `a`
factors through some `Xₙ` (`Telescope.exists_factor`), by a map that is killed at stage
`n + 1`.

This is the common core of Neeman's theorem (`Foundations/Neeman.lean`, for
`H = Hom(-, X)`) and of Brown representability (`Foundations/Brown.lean`).
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T]

section Predicates

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]

/-- A functor `H : Tᵒᵖ ⥤ AddCommGrpCat` is *cohomological* if for every distinguished triangle
`X₁ → X₂ → X₃ → X₁⟦1⟧` the sequence `H(X₃) → H(X₂) → H(X₁)` is exact in the middle. -/
def IsCohomological (H : Tᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ Tr ∈ distTriang T, ∀ y : H.obj (op Tr.obj₂), H.map Tr.mor₁.op y = 0 →
    ∃ z : H.obj (op Tr.obj₃), H.map Tr.mor₂.op z = y

end Predicates

variable [HasCoproducts.{v} T]

/-- A functor `H : Tᵒᵖ ⥤ AddCommGrpCat` *sends coproducts to products*: for every family
`Y : J → T`, `J : Type v`, the map `H(∐ Y) → ∏ H(Yⱼ)` is bijective. -/
def SendsCoproductsToProducts (H : Tᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ (J : Type v) (Y : J → T),
    Function.Bijective fun (a : H.obj (op (∐ Y))) (j : J) => H.map (Sigma.ι Y j).op a

omit [Preadditive T] in
/-- `H` sends coproducts indexed by `v`-small types to products. -/
lemma SendsCoproductsToProducts.bijective_of_small {H : Tᵒᵖ ⥤ AddCommGrpCat.{v}}
    (hH : SendsCoproductsToProducts H) {J : Type*} [Small.{v} J] (Y : J → T)
    [HasCoproduct Y] :
    Function.Bijective fun (a : H.obj (op (∐ Y))) (j : J) => H.map (Sigma.ι Y j).op a := by
  let e := equivShrink.{v} J
  let Y' : Shrink.{v} J → T := fun j' => Y (e.symm j')
  let φ : ∐ Y ⟶ ∐ Y' := Sigma.desc fun j =>
    eqToHom (congrArg Y (e.symm_apply_apply j).symm) ≫ Sigma.ι Y' (e j)
  let ψ : ∐ Y' ⟶ ∐ Y := Sigma.desc fun j' => Sigma.ι Y (e.symm j')
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    ext j
    simp only [φ, ψ, Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc,
      Category.comp_id]
    exact Sigma.eqToHom_comp_ι Y (e.symm_apply_apply j)
  have hψ : ∀ (a : H.obj (op (∐ Y))) (j' : Shrink.{v} J),
      H.map (Sigma.ι Y' j').op (H.map ψ.op a) = H.map (Sigma.ι Y (e.symm j')).op a := by
    intro a j'
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Sigma.ι_comp_desc]
  have hφ : ∀ a, H.map φ.op (H.map ψ.op a) = a := by
    intro a
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hφψ, op_id,
      CategoryTheory.Functor.map_id, AddCommGrpCat.id_apply]
  have heq : ∀ (b : ∀ j, H.obj (op (Y j))) {j₁ j₂ : J} (hj : j₁ = j₂),
      H.map (eqToHom (congrArg Y hj)).op (b j₂) = b j₁ := by
    rintro b _ _ rfl
    simp
  obtain ⟨hinj, hsurj⟩ := hH (Shrink.{v} J) Y'
  constructor
  · intro a b hab
    have : H.map ψ.op a = H.map ψ.op b := hinj (funext fun j' => by
      simp only [hψ]
      exact congrFun hab (e.symm j'))
    rw [← hφ a, ← hφ b, this]
  · intro b
    obtain ⟨a', ha'⟩ := hsurj fun j' => b (e.symm j')
    refine ⟨H.map φ.op a', funext fun j => ?_⟩
    dsimp only
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Sigma.ι_comp_desc,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    have := congrFun ha' (e j)
    dsimp only at this
    rw [this]
    exact heq b (e.symm_apply_apply j).symm

section Yoneda

/-- `Hom(-, X)` sends coproducts to products. -/
lemma sendsCoproductsToProducts_preadditiveYoneda (X : T) :
    SendsCoproductsToProducts (preadditiveYoneda.obj X) := by
  intro J Y
  constructor
  · intro a b hab
    exact Sigma.hom_ext _ _ fun j => congrFun hab j
  · intro b
    exact ⟨Sigma.desc b, funext fun j => Sigma.ι_comp_desc b j⟩

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]

omit [HasCoproducts.{v} T] in
/-- `Hom(-, X)` is cohomological. -/
lemma isCohomological_preadditiveYoneda (X : T) :
    IsCohomological (preadditiveYoneda.obj X) :=
  fun Tr hTr y hy => Triangle.yoneda_exact₂ Tr hTr y hy |>.imp fun _ hz => hz.symm

end Yoneda

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]

variable {H : Tᵒᵖ ⥤ AddCommGrpCat.{v}}

/-- For cohomological `H` sending coproducts to products, a compatible family of elements
`uₙ ∈ H(Xₙ)` lifts to the telescope. -/
lemma Telescope.exists_lift [H.Additive] (hH : IsCohomological H)
    (hHc : SendsCoproductsToProducts H) {X : ℕ → T} {x : ∀ n, X n ⟶ X (n + 1)}
    (t : Telescope X x) (u : ∀ n, H.obj (op (X n)))
    (hu : ∀ n, H.map (x n).op (u (n + 1)) = u n) :
    ∃ w : H.obj (op t.obj), ∀ n, H.map (t.ι n).op w = u n := by
  obtain ⟨hinj, hsurj⟩ := hHc.bijective_of_small X
  obtain ⟨lifted, hlifted⟩ := hsurj u
  have h0 : H.map (𝟙 (∐ X) - telescopeShift X x).op lifted = 0 := hinj (funext fun n => by
    have h1 := congrFun hlifted n
    have h2 := congrFun hlifted (n + 1)
    dsimp only at h1 h2 ⊢
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Preadditive.comp_sub,
      Category.comp_id, ι_telescopeShift, op_sub, Functor.map_sub]
    simp [h1, h2, hu])
  obtain ⟨w, hw⟩ := hH _ t.distinguished lifted h0
  refine ⟨w, fun n => ?_⟩
  have := congrFun hlifted n
  dsimp only at this hw
  rw [← this, ← hw, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-! ### The tower -/

variable (H) {κ : Type v} (g : κ → T)

/-- A stage of the tower: an object `X` with an element `u ∈ H(X)`. -/
structure CellStage where
  /-- The object. -/
  X : T
  /-- The element. -/
  u : H.obj (op X)

/-- The maps from the `g k` killed by `u`. -/
def CellStage.Killed (s : CellStage H) : Type v :=
  Σ k : κ, {b : g k ⟶ s.X // H.map b.op s.u = 0}

/-- The next stage: the cone of `∐_{(k, b)} g k ⟶ X` over the killed maps, with a lift of
`u`. -/
structure CellStep (s : CellStage H) where
  /-- The next object. -/
  X' : T
  /-- The map to it. -/
  x : s.X ⟶ X'
  /-- The third map of the triangle. -/
  δ : X' ⟶ (∐ fun t : s.Killed H g => g t.1)⟦(1 : ℤ)⟧
  distinguished : Triangle.mk (Sigma.desc fun t : s.Killed H g => t.2.1) x δ ∈ distTriang T
  /-- The lift of `u`. -/
  u' : H.obj (op X')
  hu' : H.map x.op u' = s.u

variable {H g}

lemma CellStep.nonempty (hH : IsCohomological H)
    (hHc : SendsCoproductsToProducts H) (s : CellStage H) : Nonempty (CellStep H g s) := by
  obtain ⟨X', x, δ, hT⟩ := distinguished_cocone_triangle (Sigma.desc fun t : s.Killed H g => t.2.1)
  have h0 : H.map (Sigma.desc fun t : s.Killed H g => t.2.1).op s.u = 0 :=
    (hHc _ _).1 (funext fun t => by
      dsimp only
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Sigma.ι_comp_desc,
        t.2.2]
      exact (map_zero _).symm)
  obtain ⟨u', hu'⟩ := hH _ hT s.u h0
  exact ⟨⟨X', x, δ, hT, u', hu'⟩⟩

/-- The output of the construction: a sequence `X₀ → X₁ → ⋯` with telescope `X∞` and
`u∞ ∈ H(X∞)` such that `a ↦ a^* u∞` is a bijection `Hom(g k, X∞) ≅ H(g k)` for every `k`.
`X₀` is a coproduct of objects `g k`, and each `Xₙ₊₁` is the cone of a map from such a
coproduct to `Xₙ`. -/
structure CellularTower (H : Tᵒᵖ ⥤ AddCommGrpCat.{v}) (g : κ → T) where
  /-- The stages. -/
  X : ℕ → T
  /-- The maps between them. -/
  x : ∀ n, X n ⟶ X (n + 1)
  /-- The telescope. -/
  tel : Telescope X x
  /-- The element `u∞`. -/
  u : H.obj (op tel.obj)
  bijective : ∀ k, Function.Bijective fun a : g k ⟶ tel.obj => H.map a.op u
  zero : ∃ (J : Type v) (j : J → κ), Nonempty (X 0 ≅ ∐ fun i => g (j i))
  succ : ∀ n, ∃ (J : Type v) (j : J → κ) (f : (∐ fun i => g (j i)) ⟶ X n)
    (δ : X (n + 1) ⟶ (∐ fun i => g (j i))⟦(1 : ℤ)⟧), Triangle.mk f (x n) δ ∈ distTriang T

/-- Cellular towers exist. -/
theorem CellularTower.nonempty [H.Additive] (hH : IsCohomological H)
    (hHc : SendsCoproductsToProducts H) (hg : ∀ k, IsCompactObj (g k)) :
    Nonempty (CellularTower H g) := by
  classical
  -- stage `0`
  let S₀ := Σ k : κ, H.obj (op (g k))
  obtain ⟨u₀, hu₀⟩ := (hHc S₀ fun t => g t.1).2 fun t => t.2
  let step : ∀ s : CellStage H, CellStep H g s :=
    fun s => Classical.choice (CellStep.nonempty hH hHc s)
  let stage : ℕ → CellStage H := fun n => Nat.rec ⟨∐ fun t : S₀ => g t.1, u₀⟩
    (fun _ s => ⟨(step s).X', (step s).u'⟩) n
  let X : ℕ → T := fun n => (stage n).X
  let x : ∀ n, X n ⟶ X (n + 1) := fun n => (step (stage n)).x
  let tel := telescope X x
  obtain ⟨w, hw⟩ := tel.exists_lift hH hHc (fun n => (stage n).u)
    (fun n => (step (stage n)).hu')
  refine ⟨⟨X, x, tel, w, fun k => ⟨?_, ?_⟩, ⟨S₀, fun t => t.1, ⟨Iso.refl _⟩⟩,
    fun n => ⟨(stage n).Killed H g, fun t => t.1, Sigma.desc fun t => t.2.1,
      (step (stage n)).δ, (step (stage n)).distinguished⟩⟩⟩
  · -- injectivity
    have key : ∀ a : g k ⟶ tel.obj, H.map a.op w = 0 → a = 0 := by
      intro a ha
      obtain ⟨n, a', rfl⟩ := tel.exists_factor (hg k) a
      have ha' : H.map a'.op (stage n).u = 0 := by
        rw [← hw n, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
        exact ha
      have hz : a' ≫ x n = 0 := by
        have := comp_distTriang_mor_zero₁₂ _ (step (stage n)).distinguished
        dsimp at this
        have h := Sigma.ι (fun t : (stage n).Killed H g => g t.1) ⟨k, a', ha'⟩ ≫= this
        simpa using h
      rw [← tel.x_comp_ι n, ← Category.assoc, hz, Limits.zero_comp]
    intro a b hab
    rw [← sub_eq_zero]
    apply key
    dsimp only at hab
    simp [hab]
  · -- surjectivity
    intro h
    refine ⟨Sigma.ι (fun t : S₀ => g t.1) ⟨k, h⟩ ≫ tel.ι 0, ?_⟩
    dsimp only
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hw 0]
    exact congrFun hu₀ ⟨k, h⟩

end RigidDescent
