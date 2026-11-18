/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import LeanPool.TruthTableRigidity.Prop31
public import Mathlib.Topology.Baire.BaireMeasurable

/-!
# Baire measurable functions and Baire category on Cantor space

Topological preliminaries for the Baire measurable case (Section 4 of the note):

* `BaireMeasurableFun F`: preimages of open sets have the Baire property;
* a Baire measurable `F` is continuous on a dense `Gδ` set (Kechris 8.38);
* uniformization on a dense `Gδ` subset (Lemma 2.4, relative version);
* removing the parameters (Lemma 4.4);
* translations and shears of `2^ω × 2^ω` preserve comeager sets.
-/

@[expose] public section

open Filter Topology

namespace TT

open OAI.TuringRigidity

/-- `F : 2^ω → 2^ω` is *Baire measurable*: the preimage of every open set has the Baire
property. -/
def BaireMeasurableFun (F : Oracle → Oracle) : Prop :=
  ∀ U : Set Oracle, IsOpen U → BaireMeasurableSet (F ⁻¹' U)

theorem BaireMeasurableFun.of_continuous {F : Oracle → Oracle} (hF : Continuous F) :
    BaireMeasurableFun F := fun _ hU => (hU.preimage hF).baireMeasurableSet

/-- Every Borel measurable function is Baire measurable. -/
theorem BaireMeasurableFun.of_measurable {F : Oracle → Oracle} (hF : Measurable F) :
    BaireMeasurableFun F := fun _ hU => (hF hU.measurableSet).baireMeasurableSet

/-- A Baire measurable function is continuous on a dense `Gδ` set. -/
theorem BaireMeasurableFun.exists_continuousOn {F : Oracle → Oracle}
    (hF : BaireMeasurableFun F) : ∃ D : Set Oracle, IsGδ D ∧ Dense D ∧ ContinuousOn F D := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis Oracle
  have hu : ∀ s ∈ b, ∃ u : Set Oracle, IsOpen u ∧ F ⁻¹' s =ᵇ u := fun s hs =>
    (hF s (hb.isOpen hs)).residualEq_isOpen
  choose! u hu1 hu2 using hu
  have hR : {x | ∀ s ∈ b, (x ∈ F ⁻¹' s ↔ x ∈ u s)} ∈ residual Oracle := by
    have := (eventually_countable_ball (l := residual Oracle) hbc
      (p := fun x s _ => (x ∈ F ⁻¹' s ↔ x ∈ u s))).mpr
      (fun s hs => (hu2 s hs).mem_iff)
    exact this
  obtain ⟨D, hDR, hDG, hDd⟩ := mem_residual.mp hR
  refine ⟨D, hDG, hDd, fun x hx => ?_⟩
  rw [ContinuousWithinAt, hb.nhds_hasBasis.tendsto_right_iff]
  rintro s ⟨hs, hFx⟩
  have hxu : x ∈ u s := ((hDR hx) s hs).mp hFx
  rw [eventually_nhdsWithin_iff]
  filter_upwards [(hu1 s hs).mem_nhds hxu] with z hz hzD
  exact ((hDR hzD) s hs).mpr hz

/-! ### Removing the parameters (Lemma 4.4) -/

theorem exists_box_subset {U : Set (Oracle × Oracle)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ γ δ : List Bool, Ncyl γ ×ˢ Ncyl δ ⊆ U := by
  obtain ⟨⟨x, y⟩, hxy⟩ := hne
  obtain ⟨k, hk⟩ := exists_cyl_prod_subset hU hxy
  exact ⟨pre x k, pre y k, by rw [Ncyl_pre, Ncyl_pre]; exact hk⟩

/-- **Lemma 4.4.** If `A ≤tt X ⊕ G ⊕ H` for comeager many `(G, H)` in a nonempty open set,
then `A ≤tt X`. -/
theorem remove_parameters {U : Set (Oracle × Oracle)} (hU : IsOpen U) (hne : U.Nonempty)
    {A X : Oracle}
    (h : ∀ᶠ p in residual (Oracle × Oracle), p ∈ U → TTReducible A (ojoin X (ojoin p.1 p.2))) :
    TTReducible A X := by
  obtain ⟨E, hEh, hEG, hEd⟩ := mem_residual.mp h
  let K (Φ : {Φ : Oracle → Oracle // IsTTFunctional Φ}) : Set (Oracle × Oracle) :=
    {p | A = Φ.1 (ojoin X (ojoin p.1 p.2))}
  have hcont : Continuous fun p : Oracle × Oracle => ojoin X (ojoin p.1 p.2) :=
    continuous_ojoin.comp (continuous_const.prodMk continuous_ojoin)
  have hclosed : ∀ Φ, IsClosed (K Φ) := fun Φ =>
    isClosed_eq continuous_const (Φ.2.continuous.comp hcont)
  have hcover : ∀ p ∈ E, p ∈ U → ∃ Φ, p ∈ K Φ := by
    intro p hpE hpU
    obtain ⟨Φ, hΦ, hp⟩ := hEh hpE hpU
    exact ⟨⟨Φ, hΦ⟩, hp.symm⟩
  have : Nonempty {Φ : Oracle → Oracle // IsTTFunctional Φ} := ⟨⟨id, isTTFunctional_id⟩⟩
  obtain ⟨Φ, V, -, hV, hVne, hVK⟩ :=
    exists_open_subset_of_closed_cover hEG hEd hU hne hclosed hcover
  obtain ⟨γ, δ, hγδ⟩ := exists_box_subset hV hVne
  have hmem : (prep γ zzero, prep δ zzero) ∈ V := hγδ ⟨prep_mem γ zzero, prep_mem δ zzero⟩
  have hEq : A = Φ.1 (ojoin X (ojoin (prep γ zzero) (prep δ zzero))) := hVK hmem
  exact ⟨fun Z => Φ.1 (ojoin Z (ojoin (prep γ zzero) (prep δ zzero))),
    Φ.2.comp (isTTFunctional_id.join (isTTFunctional_const
      (ojoin_ttReducible (ttComputable_prep γ) (ttComputable_prep δ)))), hEq.symm⟩

/-! ### Comeager sets and countable sets -/

/-- In Cantor space the complement of a point is dense. -/
theorem dense_compl_singleton_oracle (x : Oracle) : Dense ({x}ᶜ : Set Oracle) := by
  rw [dense_iff_inter_open]
  intro U hU ⟨y, hy⟩
  obtain ⟨k, hk⟩ := exists_cyl_subset hU hy
  by_cases hxy : y = x
  · refine ⟨Function.update y k (!y k), hk fun i hi => ?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]
    · intro h
      have := congrFun h k
      rw [Function.update_self, hxy] at this
      simp at this
  · exact ⟨y, hy, hxy⟩

/-- Removing a countable set from a comeager subset of Cantor space leaves a comeager set. -/
theorem diff_countable_mem_residual {D S : Set Oracle} (hD : D ∈ residual Oracle)
    (hS : S.Countable) : D \ S ∈ residual Oracle := by
  have h : ∀ x ∈ S, ({x}ᶜ : Set Oracle) ∈ residual Oracle := fun x _ =>
    residual_of_dense_open isClosed_singleton.isOpen_compl (dense_compl_singleton_oracle x)
  have h2 : (⋂ x ∈ S, ({x}ᶜ : Set Oracle)) ∈ residual Oracle :=
    (countable_bInter_mem hS).mpr h
  filter_upwards [hD, h2] with z hzD hz
  refine ⟨hzD, fun hzS => ?_⟩
  have := Set.mem_iInter₂.mp hz z hzS
  exact this rfl

/-- The preimage of a comeager set under a continuous open map is comeager. -/
theorem preimage_mem_residual {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hc : Continuous f) (ho : IsOpenMap f) {s : Set Y} (hs : s ∈ residual Y) :
    f ⁻¹' s ∈ residual X :=
  tendsto_residual_of_isOpenMap hc ho hs

/-! ### Translations and shears -/

theorem zaddO_znegO_cancel (x c : Oracle) : zaddO (zaddO x c) (znegO c) = x := by
  have : ∀ a b : Z2, (a + b) + -b = a := fun a b => by abel
  exact this x c

theorem zaddO_cancel_znegO (x c : Oracle) : zaddO (zaddO x (znegO c)) c = x := by
  have : ∀ a b : Z2, (a + -b) + b = a := fun a b => by abel
  exact this x c

theorem continuous_zaddO_const_right (c : Oracle) : Continuous fun x => zaddO x c := by
  have hp : Continuous fun x : Oracle => (x, c) :=
    (continuous_id : Continuous (id : Oracle → Oracle)).prodMk
      (continuous_const : Continuous fun _ : Oracle => c)
  have hcomp : Continuous ((fun p : Oracle × Oracle => zaddO p.1 p.2) ∘
      (fun x : Oracle => (x, c))) :=
    continuous_zaddO.comp (f := fun x : Oracle => (x, c)) hp
  exact hcomp.congr (g := fun x : Oracle => zaddO x c) (fun _ => rfl)

/-- Translation `x ↦ x + c` is a homeomorphism of Cantor space. -/
def translHomeo (c : Oracle) : Oracle ≃ₜ Oracle where
  toFun x := zaddO x c
  invFun x := zaddO x (znegO c)
  left_inv x := zaddO_znegO_cancel x c
  right_inv x := zaddO_cancel_znegO x c
  continuous_toFun := continuous_zaddO_const_right c
  continuous_invFun := continuous_zaddO_const_right (znegO c)

/-- Negation is a homeomorphism of Cantor space. -/
def negHomeo : Oracle ≃ₜ Oracle where
  toFun := znegO
  invFun := znegO
  left_inv x := (neg_neg (Z2.of x) :)
  right_inv x := (neg_neg (Z2.of x) :)
  continuous_toFun := continuous_znegO
  continuous_invFun := continuous_znegO

/-- The shear `(G, H) ↦ (G + g H, H)` is a homeomorphism of `2^ω × 2^ω`. -/
def shearHomeo (g : Oracle → Oracle) (hg : Continuous g) : (Oracle × Oracle) ≃ₜ (Oracle × Oracle)
  where
  toFun p := (zaddO p.1 (g p.2), p.2)
  invFun p := (zaddO p.1 (znegO (g p.2)), p.2)
  left_inv p := by simp only [zaddO_znegO_cancel]
  right_inv p := by simp only [zaddO_cancel_znegO]
  continuous_toFun :=
    (continuous_zaddO.comp (continuous_fst.prodMk (hg.comp continuous_snd))).prodMk continuous_snd
  continuous_invFun :=
    (continuous_zaddO.comp (continuous_fst.prodMk
      (continuous_znegO.comp (hg.comp continuous_snd)))).prodMk continuous_snd

theorem isOpenMap_shear_fst (g : Oracle → Oracle) (hg : Continuous g) :
    IsOpenMap fun p : Oracle × Oracle => zaddO p.1 (g p.2) :=
  isOpenMap_fst.comp (shearHomeo g hg).isOpenMap

/-- Translating both coordinates preserves comeager sets of pairs. -/
theorem translate_mem_residual (c₁ c₂ : Oracle) {s : Set (Oracle × Oracle)}
    (hs : s ∈ residual (Oracle × Oracle)) :
    (fun p : Oracle × Oracle => (zaddO p.1 c₁, zaddO p.2 c₂)) ⁻¹' s ∈
      residual (Oracle × Oracle) := by
  let h := (translHomeo c₁).prodCongr (translHomeo c₂)
  change h ⁻¹' s ∈ residual _
  exact preimage_mem_residual h.continuous h.isOpenMap hs

/-! ### Countable subgroups -/

theorem countable_addSubgroup_closure (S : Set Z2) (hS : S.Countable) :
    (AddSubgroup.closure S : Set Z2).Countable := by
  have := hS.to_subtype
  let f : List (Bool × S) → Z2 := fun l => (l.map fun p => if p.1 then (p.2 : Z2) else -p.2).sum
  have hflip : ∀ l : List (Bool × S), f (l.map fun p => (!p.1, p.2)) = -f l := by
    intro l
    induction l with
    | nil => simp [f]
    | cons p l ih =>
      simp only [f, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, neg_add]
      cases p.1 <;> simp
  refine (Set.countable_range f).mono ?_
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx => exact ⟨[(true, ⟨x, hx⟩)], by simp [f]⟩
  | zero => exact ⟨[], by simp [f]⟩
  | add x y _ _ hx hy =>
    obtain ⟨l₁, rfl⟩ := hx
    obtain ⟨l₂, rfl⟩ := hy
    exact ⟨l₁ ++ l₂, by simp [f]⟩
  | neg x _ hx =>
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l.map fun p => (!p.1, p.2), hflip l⟩

end TT
