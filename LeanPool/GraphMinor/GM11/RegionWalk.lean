/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.HubWalk
public import LeanPool.GraphMinor.GM11.SplitEdge

/-!
# A walk around a region

`exists_steps` reads off from the collar of a region, in a drawing whose edges have been split, the
walk
around the region in the first drawing. `exists_runs_walk` turns a list of steps into a walk with
`RunsAlongOn`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A list of steps along a curve is a walk that the curve runs along. -/
theorem exists_runs_walk (D : Drawing S) {m : ℕ} {w : ℕ → S} {e : ℕ → Set S} {x : ℕ → ℝ} {φ : ℝ → S}
    (hlink : ∀ j < m, D.toGraph.IsLink (e j) (w j) (w (j + 1))) (hx : ∀ j < m, x j < x (j + 1))
    (hstart : ∀ j ≤ m, φ (x j) = w j) (hinj : ∀ j < m, InjOn φ (Ioo (x j) (x (j + 1))))
    (him : ∀ j < m, φ '' Ioo (x j) (x (j + 1)) = e j) (hV : w m ∈ D.V) {z : S} (hz : w m = z) :
    ∀ d ≤ m, ∃ W : GraphWalk D.toGraph (w (m - d)) z, RunsAlongOn D φ (x (m - d)) (x m) W ∧
      W.edges = (List.range' (m - d) d).map e := by
  subst hz
  intro d
  induction d with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    exact ⟨.nil hV, ⟨rfl, hstart m le_rfl⟩, by simp [GraphWalk.edges]⟩
  | succ d ih =>
    intro hd
    obtain ⟨W, hW, hedges⟩ := ih (by omega)
    have hj : m - (d + 1) < m := by omega
    have hs : m - (d + 1) + 1 = m - d := by omega
    have hl := hlink _ hj
    rw [hs] at hl
    refine ⟨.cons hl W, ?_, ?_⟩
    · refine ⟨x (m - d), ?_, hstart _ (by omega), ?_, ?_, hW⟩
      · have := hx _ hj
        rwa [hs] at this
      · have := hinj _ hj
        rwa [hs] at this
      · have := him _ hj
        rwa [hs] at this
    · simp only [GraphWalk.edges, hedges]
      rw [show d + 1 = (d + 1) by rfl, List.range'_succ, List.map_cons, hs]

namespace IsHubCollar

variable {Γ Γ' H : Drawing S} {r : Set S} {n : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S}
  {h : C(Circle × I, S)}

/-- The open arc of a step is its edge. -/
theorem image_Ioo (hc : IsHubCollar Γ Γ' H r n v a s P ε h) (i : ℕ) : ε i '' Ioo 0 1 = a i := by
  have hE := Γ.closure_diff_V (hc.edge i)
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [← hE]
    refine ⟨hc.ε_range i ▸ mem_range_self u, fun hV => ?_⟩
    have hm : ε i u ∈ closure (a i) ∩ Γ.V := ⟨hc.ε_range i ▸ mem_range_self u, hV⟩
    rw [hc.cap] at hm
    rcases hm with h₁ | h₁
    · have := hc.ε_inj i (h₁.trans (hc.ε_zero i).symm)
      exact hu.1.ne' this
    · have := hc.ε_inj i ((mem_singleton_iff.mp h₁).trans (hc.ε_one i).symm)
      exact hu.2.ne this
  · intro hy
    have hcl : y ∈ range (ε i) := hc.ε_range i ▸ subset_closure hy
    obtain ⟨u, rfl⟩ := hcl
    have hnV := ((hc.edge i).2.1 hy).2
    refine ⟨u, ⟨?_, ?_⟩, rfl⟩
    · refine unitInterval.pos_iff_ne_zero.mpr fun h₀ => hnV ?_
      rw [h₀, hc.ε_zero]
      exact hc.vertex i
    · refine lt_of_le_of_ne (unitInterval.le_one u) fun h₁ => hnV ?_
      rw [h₁, hc.ε_one]
      exact hc.vertex _

/-- The curve at the bottom of the collar, on the `i`-th step. -/
theorem curve_eq (hc : IsHubCollar Γ Γ' H r n v a s P ε h) {i : ℕ} (hi : i < n) (u : I) :
    collarCurve h ((i + u.1) / n) = ε i u :=
  hc.bottom i hi u

end IsHubCollar

/-- The data of `exists_split`. -/
structure SplitData (D D₂ : Drawing S) (A B : Set S → Set S) (m x y : Set S → S) : Prop where
  U_eq : D₂.U = D.U
  V_eq : D₂.V = D.V ∪ m '' D.E
  A_mem : ∀ e ∈ D.E, A e ∈ D₂.E
  B_mem : ∀ e ∈ D.E, B e ∈ D₂.E
  mid : ∀ e ∈ D.E, m e ∈ e
  mid_A : ∀ e ∈ D.E, m e ∉ A e
  mid_B : ∀ e ∈ D.E, m e ∉ B e
  disj : ∀ e ∈ D.E, Disjoint (A e) (B e)
  union : ∀ e ∈ D.E, e = A e ∪ {m e} ∪ B e
  x_mem : ∀ e ∈ D.E, x e ∈ D.V
  y_mem : ∀ e ∈ D.E, y e ∈ D.V
  cap : ∀ e ∈ D.E, closure e ∩ D.V = {x e, y e}
  cap_A : ∀ e ∈ D.E, closure (A e) ∩ D₂.V = {x e, m e}
  cap_B : ∀ e ∈ D.E, closure (B e) ∩ D₂.V = {m e, y e}
  all : ∀ g ∈ D₂.E, ∃ e ∈ D.E, g = A e ∨ g = B e

variable {D D₂ : Drawing S} {A B : Set S → Set S} {m x y : Set S → S}

namespace SplitData

theorem mid_notMem (hd : SplitData D D₂ A B m x y) {e : Set S} (he : e ∈ D.E) : m e ∉ D.V :=
  (he.2.1 (hd.mid e he)).2

theorem mid_V₂ (hd : SplitData D D₂ A B m x y) {e : Set S} (he : e ∈ D.E) : m e ∈ D₂.V :=
  hd.V_eq ▸ Or.inr ⟨e, he, rfl⟩

theorem V_sub (hd : SplitData D D₂ A B m x y) {z : S} (hz : z ∈ D.V) : z ∈ D₂.V :=
  hd.V_eq ▸ Or.inl hz

theorem A_sub (hd : SplitData D D₂ A B m x y) {e : Set S} (he : e ∈ D.E) : A e ⊆ e := fun _ h => by
  rw [hd.union e he]
  exact Or.inl (Or.inl h)

theorem B_sub (hd : SplitData D D₂ A B m x y) {e : Set S} (he : e ∈ D.E) : B e ⊆ e := fun _ h => by
  rw [hd.union e he]
  exact Or.inr h

/-- Two edges of the first drawing with a point in common are equal. -/
theorem edge_of_piece (hd : SplitData D D₂ A B m x y) {e f : Set S} (he : e ∈ D.E) (hf : f ∈ D.E)
    (h : (A e = A f ∨ A e = B f ∨ B e = A f ∨ B e = B f)) : e = f := by
  have hsame : ∀ {g₁ g₂ : Set S}, g₁ ∈ D₂.E → g₁ = g₂ → g₁ ⊆ e → g₂ ⊆ f → e = f := by
    rintro g₁ _ hg rfl h₁ h₂
    obtain ⟨z, hz⟩ := hg.1
    exact D.edge_eq_of_mem he hf (h₁ hz) (h₂ hz)
  rcases h with h | h | h | h
  · exact hsame (hd.A_mem e he) h (hd.A_sub he) (hd.A_sub hf)
  · exact hsame (hd.A_mem e he) h (hd.A_sub he) (hd.B_sub hf)
  · exact hsame (hd.B_mem e he) h (hd.B_sub he) (hd.A_sub hf)
  · exact hsame (hd.B_mem e he) h (hd.B_sub he) (hd.B_sub hf)

theorem mid_inj (hd : SplitData D D₂ A B m x y) {e f : Set S} (he : e ∈ D.E) (hf : f ∈ D.E)
    (h : m e = m f) : e = f :=
  D.edge_eq_of_mem he hf (hd.mid e he) (h ▸ hd.mid f hf)

theorem ne_AB (hd : SplitData D D₂ A B m x y) {e : Set S} (he : e ∈ D.E) : A e ≠ B e := by
  intro h
  obtain ⟨z, hz⟩ := (hd.A_mem e he).1
  exact disjoint_left.mp (hd.disj e he) hz (h ▸ hz)

/-- No edge of the second drawing is a loop. -/
theorem noLoop (hd : SplitData D D₂ A B m x y) :
    ∀ g ∈ D₂.E, ∃ a b, a ≠ b ∧ closure g ∩ D₂.V = {a, b} := by
  intro g hg
  obtain ⟨e, he, rfl | rfl⟩ := hd.all g hg
  · refine ⟨x e, m e, fun h => hd.mid_notMem he ?_, hd.cap_A e he⟩
    rw [← h]
    exact hd.x_mem e he
  · refine ⟨m e, y e, fun h => hd.mid_notMem he ?_, hd.cap_B e he⟩
    rw [h]
    exact hd.y_mem e he

end SplitData

variable [T2Space S] [ConnectedSpace S] {Γ' H : Drawing S} {r : Set S} {n : ℕ} {v : ℕ → S}
  {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}

/-- The steps of the collar, two at a time, are the edges of the first drawing. -/
theorem exists_steps (hd : SplitData D D₂ A B m x y)
    (hrad : PreRad (PaintingOrDrawing.drawing D₂) Γ') (hS : IsClosedSurface S)
    (hmax : RadMax (PaintingOrDrawing.drawing D₂) Γ') (hE : D₂.E.Nonempty)
    (hc : IsHubCollar D₂ Γ' (radialUnion hrad) r n v a s P ε h) (hv0 : v 0 ∈ D.V) :
    ∃ p, n = 2 * p ∧ ∃ F : ℕ → Set S, ∀ j, F j ∈ D.E ∧ v (2 * j + 1) = m (F j) ∧
      ((a (2 * j) = A (F j) ∧ a (2 * j + 1) = B (F j) ∧ x (F j) = v (2 * j) ∧
          y (F j) = v (2 * j + 2)) ∨
        (a (2 * j) = B (F j) ∧ a (2 * j + 1) = A (F j) ∧ y (F j) = v (2 * j) ∧
          x (F j) = v (2 * j + 2))) := by
  classical
  have hstep : ∀ i, v i ∈ D.V → ∃ e ∈ D.E, v (i + 1) = m e ∧ (a i = A e ∨ a i = B e) := by
    intro i hi
    obtain ⟨e, he, hg⟩ := hd.all _ (hc.edge i)
    refine ⟨e, he, ?_, hg⟩
    have hcap := hc.cap i
    rcases hg with hg | hg
    · rw [hg, hd.cap_A e he] at hcap
      have hm : m e ∈ ({v i, v (i + 1)} : Set S) := hcap ▸ (by simp)
      rcases hm with h₁ | h₁
      · exact (hd.mid_notMem he (h₁ ▸ hi)).elim
      · exact (mem_singleton_iff.mp h₁).symm
    · rw [hg, hd.cap_B e he] at hcap
      have hm : m e ∈ ({v i, v (i + 1)} : Set S) := hcap ▸ (by simp)
      rcases hm with h₁ | h₁
      · exact (hd.mid_notMem he (h₁ ▸ hi)).elim
      · exact (mem_singleton_iff.mp h₁).symm
  have hback : ∀ e ∈ D.E, ∀ i, v i = m e → v (i + 1) ∈ D.V ∧ (a i = A e ∨ a i = B e) := by
    intro e he i hi
    obtain ⟨f, hf, hg⟩ := hd.all _ (hc.edge i)
    have hcap := hc.cap i
    rcases hg with hg | hg
    · rw [hg, hd.cap_A f hf] at hcap
      have hm : v i ∈ ({x f, m f} : Set S) := hcap ▸ (by simp)
      rcases hm with h₁ | h₁
      · exact (hd.mid_notMem he (hi ▸ h₁ ▸ hd.x_mem f hf)).elim
      · have hef : e = f := hd.mid_inj he hf (hi.symm.trans (mem_singleton_iff.mp h₁))
        subst hef
        have h₂ : x e ∈ ({v i, v (i + 1)} : Set S) := hcap ▸ (by simp)
        rcases h₂ with h₂ | h₂
        · exact (hd.mid_notMem he (hi ▸ h₂ ▸ hd.x_mem e he)).elim
        · exact ⟨(mem_singleton_iff.mp h₂) ▸ hd.x_mem e he, Or.inl hg⟩
    · rw [hg, hd.cap_B f hf] at hcap
      have hm : v i ∈ ({m f, y f} : Set S) := hcap ▸ (by simp)
      rcases hm with h₁ | h₁
      · have hef : e = f := hd.mid_inj he hf (hi.symm.trans h₁)
        subst hef
        have h₂ : y e ∈ ({v i, v (i + 1)} : Set S) := hcap ▸ (by simp)
        rcases h₂ with h₂ | h₂
        · exact (hd.mid_notMem he (hi ▸ h₂ ▸ hd.y_mem e he)).elim
        · exact ⟨(mem_singleton_iff.mp h₂) ▸ hd.y_mem e he, Or.inr hg⟩
      · exact (hd.mid_notMem he (hi ▸ (mem_singleton_iff.mp h₁) ▸ hd.y_mem f hf)).elim
  have hodd : ∀ j, v (2 * j) ∈ D.V := by
    intro j
    induction j with
    | zero => exact hv0
    | succ j ih =>
      obtain ⟨e, he, h₁, -⟩ := hstep _ ih
      exact (hback e he _ h₁).1
  have hn : Even n := by
    by_contra hodd'
    obtain ⟨q, hq⟩ := Nat.not_even_iff_odd.mp hodd'
    obtain ⟨e, he, h₁, -⟩ := hstep (2 * q) (hodd q)
    have h₂ := hc.per_v 0
    rw [zero_add, hq] at h₂
    exact hd.mid_notMem he (h₁ ▸ h₂ ▸ hv0)
  obtain ⟨p, hp⟩ := hn
  refine ⟨p, by omega, ?_⟩
  have key : ∀ j, ∃ e, e ∈ D.E ∧ v (2 * j + 1) = m e ∧
      ((a (2 * j) = A e ∧ a (2 * j + 1) = B e ∧ x e = v (2 * j) ∧ y e = v (2 * j + 2)) ∨
        (a (2 * j) = B e ∧ a (2 * j + 1) = A e ∧ y e = v (2 * j) ∧ x e = v (2 * j + 2))) := by
    intro j
    obtain ⟨e, he, h₁, hg⟩ := hstep _ (hodd j)
    obtain ⟨-, hg'⟩ := hback e he _ h₁
    have hAcl : m e ∈ closure (A e) := by
      have : m e ∈ closure (A e) ∩ D₂.V := by rw [hd.cap_A e he]; simp
      exact this.1
    have hBcl : m e ∈ closure (B e) := by
      have : m e ∈ closure (B e) ∩ D₂.V := by rw [hd.cap_B e he]; simp
      exact this.1
    have hE₂ : D₂.E.Nonempty := hE
    refine ⟨e, he, h₁, ?_⟩
    have hcap₁ := hc.cap (2 * j)
    have hcap₂ := hc.cap (2 * j + 1)
    rw [h₁] at hcap₁ hcap₂
    rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega] at hcap₂
    rcases hg with hg | hg
    · have hne : a (2 * j + 1) ≠ a (2 * j) := collar_turn hrad hS hmax hE hd.noLoop hc (2 * j)
        (hd.B_mem e he) (h₁ ▸ hBcl) (by rw [hg]; exact (hd.ne_AB he).symm)
      have hb : a (2 * j + 1) = B e := by
        rcases hg' with h₂ | h₂
        · exact (hne (h₂.trans hg.symm)).elim
        · exact h₂
      refine Or.inl ⟨hg, hb, ?_, ?_⟩
      · rw [hg, hd.cap_A e he] at hcap₁
        have : x e ∈ ({v (2 * j), m e} : Set S) := hcap₁ ▸ (by simp)
        rcases this with h₃ | h₃
        · exact h₃
        · exact (hd.mid_notMem he (mem_singleton_iff.mp h₃ ▸ hd.x_mem e he)).elim
      · rw [hb, hd.cap_B e he] at hcap₂
        have : y e ∈ ({m e, v (2 * j + 2)} : Set S) := hcap₂ ▸ (by simp)
        rcases this with h₃ | h₃
        · exact (hd.mid_notMem he (h₃ ▸ hd.y_mem e he)).elim
        · exact mem_singleton_iff.mp h₃
    · have hne : a (2 * j + 1) ≠ a (2 * j) := collar_turn hrad hS hmax hE hd.noLoop hc (2 * j)
        (hd.A_mem e he) (h₁ ▸ hAcl) (by rw [hg]; exact hd.ne_AB he)
      have hb : a (2 * j + 1) = A e := by
        rcases hg' with h₂ | h₂
        · exact h₂
        · exact (hne (h₂.trans hg.symm)).elim
      refine Or.inr ⟨hg, hb, ?_, ?_⟩
      · rw [hg, hd.cap_B e he] at hcap₁
        have : y e ∈ ({v (2 * j), m e} : Set S) := hcap₁ ▸ (by simp)
        rcases this with h₃ | h₃
        · exact h₃
        · exact (hd.mid_notMem he (mem_singleton_iff.mp h₃ ▸ hd.y_mem e he)).elim
      · rw [hb, hd.cap_A e he] at hcap₂
        have : x e ∈ ({m e, v (2 * j + 2)} : Set S) := hcap₂ ▸ (by simp)
        rcases this with h₃ | h₃
        · exact (hd.mid_notMem he (h₃ ▸ hd.x_mem e he)).elim
        · exact mem_singleton_iff.mp h₃
  choose F hF using key
  exact ⟨F, fun j => ⟨(hF j).1, (hF j).2.1, (hF j).2.2⟩⟩

omit [T2Space S] [ConnectedSpace S] in
/-- **The walk around a region**, from the steps of `exists_steps`. -/
theorem exists_collar_walk (hd : SplitData D D₂ A B m x y)
    (hc : IsHubCollar D₂ Γ' H r n v a s P ε h) (hc₀ : v 0 ∈ D.V) {p : ℕ} (hnp : n = 2 * p)
    {F : ℕ → Set S} (hF : ∀ j, F j ∈ D.E ∧ v (2 * j + 1) = m (F j) ∧
      ((a (2 * j) = A (F j) ∧ a (2 * j + 1) = B (F j) ∧ x (F j) = v (2 * j) ∧
          y (F j) = v (2 * j + 2)) ∨
        (a (2 * j) = B (F j) ∧ a (2 * j + 1) = A (F j) ∧ y (F j) = v (2 * j) ∧
          x (F j) = v (2 * j + 2)))) :
    ∃ W : GraphWalk D.toGraph (v 0) (v 0), RunsAlongOn D (collarCurve h) 0 1 W ∧
      W.edges = (List.range' 0 p).map F := by
  have hn := hc.pos
  have hpp : 0 < p := by omega
  have hcn : (0 : ℝ) < n := by exact_mod_cast hn
  have hcp : (0 : ℝ) < p := by exact_mod_cast hpp
  have hnr : (n : ℝ) = 2 * p := by exact_mod_cast hnp
  let φ := collarCurve h
  have hφ : ∀ i, i < n → ∀ u : I, φ ((i + u.1) / n) = ε i u := fun i hi u => hc.curve_eq hi u
  have hzero : ∀ j : ℕ, j < p → φ (j / p) = v (2 * j) := by
    intro j hj
    have := hφ (2 * j) (by omega) 0
    rw [hc.ε_zero] at this
    rw [← this]
    congr 1
    rw [hnr]
    simp only [Icc.coe_zero, add_zero]
    push_cast
    field_simp
  have hmid : ∀ j, j < p → φ ((2 * j + 1) / n) = v (2 * j + 1) := by
    intro j hj
    have := hφ (2 * j + 1) (by omega) 0
    rw [hc.ε_zero] at this
    rw [← this]
    congr 1
    push_cast
    simp
  have hone : φ 1 = v 0 := by
    have h₀ := hzero 0 hpp
    simp only [Nat.cast_zero, zero_div, mul_zero] at h₀
    rw [← h₀]
    simp [φ, collarCurve, Circle.exp_two_pi]
  have hend : v (2 * p) = v 0 := by
    have := hc.per_v 0
    rwa [zero_add, hnp] at this
  have hL : ∀ j, j < p → ∀ u : I, φ ((2 * j + u.1) / n) = ε (2 * j) u := fun j hj u => by
    have := hφ (2 * j) (by omega) u
    rwa [show (((2 * j : ℕ) : ℝ) + u.1) = 2 * j + u.1 by push_cast; ring] at this
  have hR : ∀ j, j < p → ∀ u : I, φ ((2 * j + 1 + u.1) / n) = ε (2 * j + 1) u := fun j hj u => by
    have := hφ (2 * j + 1) (by omega) u
    rwa [show (((2 * j + 1 : ℕ) : ℝ) + u.1) = 2 * j + 1 + u.1 by push_cast; ring] at this
  have hL' : ∀ j, j < p → ∀ u ∈ Ioo (0 : I) 1, ε (2 * j) u ∈ a (2 * j) := fun j _ u hu =>
    hc.image_Ioo _ ▸ mem_image_of_mem _ hu
  have hR' : ∀ j, j < p → ∀ u ∈ Ioo (0 : I) 1, ε (2 * j + 1) u ∈ a (2 * j + 1) := fun j _ u hu =>
    hc.image_Ioo _ ▸ mem_image_of_mem _ hu
  have hsplit : ∀ j, F j = a (2 * j) ∪ {m (F j)} ∪ a (2 * j + 1) ∧ Disjoint (a (2 * j)) (a
    (2 * j + 1)) ∧
      m (F j) ∉ a (2 * j) ∧ m (F j) ∉ a (2 * j + 1) := by
    intro j
    obtain ⟨he, -, h₁⟩ := hF j
    rcases h₁ with ⟨h₁, h₂, -, -⟩ | ⟨h₁, h₂, -, -⟩
    · rw [h₁, h₂]
      exact ⟨hd.union _ he, hd.disj _ he, hd.mid_A _ he, hd.mid_B _ he⟩
    · rw [h₁, h₂]
      refine ⟨?_, (hd.disj _ he).symm, hd.mid_B _ he, hd.mid_A _ he⟩
      conv_lhs => rw [hd.union _ he]
      ext z
      simp only [mem_union, mem_singleton_iff]
      tauto
  -- The three parts of the open interval of a step.
  have htri : ∀ (j : ℕ) (t : ℝ), (j : ℝ) / p < t → t < ((j + 1 : ℕ) : ℝ) / p →
      (∃ u ∈ Ioo (0 : I) 1, t = (2 * j + u.1) / n) ∨ t = (2 * j + 1) / n ∨
        ∃ u ∈ Ioo (0 : I) 1, t = (2 * j + 1 + u.1) / n := by
    intro j t h₁ h₂
    rw [div_lt_iff₀ hcp] at h₁
    rw [lt_div_iff₀ hcp] at h₂
    push_cast at h₂
    have hval : t * n = 2 * (t * p) := by rw [hnr]; ring
    have hdiv : ∀ {c : ℝ}, t * n = c → t = c / n := fun h => by
      rw [← h]
      field_simp
    rcases lt_trichotomy (t * n) (2 * j + 1) with h₃ | h₃ | h₃
    · refine Or.inl ⟨⟨t * n - 2 * j, by linarith, by linarith⟩, ⟨?_, ?_⟩, hdiv (by simp)⟩
      · change (0 : ℝ) < t * n - 2 * j
        linarith
      · change t * n - 2 * j < 1
        linarith
    · exact Or.inr (Or.inl (hdiv h₃))
    · refine Or.inr (Or.inr ⟨⟨t * n - (2 * j + 1), by linarith, by linarith⟩, ⟨?_, ?_⟩,
        hdiv (by simp)⟩)
      · change (0 : ℝ) < t * n - (2 * j + 1)
        linarith
      · change t * n - (2 * j + 1) < 1
        linarith
  have hrange₁ : ∀ j : ℕ, (j : ℝ) / p < (2 * j + 1) / n ∧ ((2 * j + 1 : ℝ) / n <
    ((j + 1 : ℕ) : ℝ) / p) := by
    intro j
    rw [hnr]
    push_cast
    constructor
    · rw [div_lt_div_iff₀ hcp (by positivity)]
      nlinarith
    · rw [div_lt_div_iff₀ (by positivity) hcp]
      nlinarith
  have hrangeL : ∀ (j : ℕ) (u : I), 0 < u → (j : ℝ) / p < (2 * j + u.1) / n ∧
      ((2 * j + u.1 : ℝ) / n < (2 * j + 1) / n ∨ u = 1) := by
    intro j u hu
    have hu₀ : (0 : ℝ) < u.1 := hu
    constructor
    · rw [hnr, div_lt_div_iff₀ hcp (by positivity)]
      nlinarith
    · by_cases h₁ : u = 1
      · exact Or.inr h₁
      · refine Or.inl ?_
        have : u.1 < 1 := lt_of_le_of_ne u.2.2 fun h => h₁ (Subtype.ext h)
        exact (div_lt_div_iff_of_pos_right hcn).mpr (by linarith)
  have hrangeR : ∀ (j : ℕ) (u : I), u < 1 → (2 * j + 1 : ℝ) / n ≤ (2 * j + 1 + u.1) / n ∧
      ((2 * j + 1 + u.1 : ℝ) / n < ((j + 1 : ℕ) : ℝ) / p) := by
    intro j u hu
    have hu₁ : u.1 < 1 := hu
    constructor
    · exact (div_le_div_iff_of_pos_right hcn).mpr (by linarith [u.2.1])
    · push_cast
      rw [hnr, div_lt_div_iff₀ (by positivity) hcp]
      nlinarith
  refine (fun (key : ∃ W : GraphWalk D.toGraph (v (2 * (p - p))) (v 0),
      RunsAlongOn D φ (((p - p : ℕ) : ℝ) / p) ((p : ℝ) / p) W ∧
        W.edges = (List.range' (p - p) p).map F) => ?_)
    (exists_runs_walk (m := p) (w := fun j => v (2 * j)) (e := F)
    (x := fun j => (j : ℝ) / p) (φ := φ) D (z := v 0) ?_ ?_ ?_ ?_ ?_ ?_ hend p le_rfl)
  · revert key
    rw [Nat.sub_self]
    rintro ⟨W, hW, hedges⟩
    refine ⟨W, ?_, hedges⟩
    have h₁ : ((p : ℝ) / p) = 1 := div_self hcp.ne'
    rw [h₁, Nat.cast_zero, zero_div] at hW
    exact hW
  · intro j _
    obtain ⟨he, -, h₁⟩ := hF j
    refine ⟨he, ?_, ?_, ?_⟩
    · rcases h₁ with ⟨-, -, h₂, -⟩ | ⟨-, -, h₂, -⟩
      · exact h₂ ▸ hd.x_mem _ he
      · exact h₂ ▸ hd.y_mem _ he
    · rcases h₁ with ⟨-, -, -, h₂⟩ | ⟨-, -, -, h₂⟩
      · rw [show 2 * (j + 1) = 2 * j + 2 by ring]
        exact h₂ ▸ hd.y_mem _ he
      · rw [show 2 * (j + 1) = 2 * j + 2 by ring]
        exact h₂ ▸ hd.x_mem _ he
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, hd.cap _ he]
      rcases h₁ with ⟨-, -, h₂, h₃⟩ | ⟨-, -, h₂, h₃⟩
      · rw [h₂, h₃]
      · rw [h₂, h₃, pair_comm]
  · intro j _
    exact (div_lt_div_iff_of_pos_right hcp).mpr (by push_cast; linarith)
  · intro j hj
    rcases hj.lt_or_eq with h₁ | rfl
    · exact hzero j h₁
    · rw [div_self hcp.ne', hone, hend]
  · intro j hj t ht t' ht' heq
    obtain ⟨hs, hdisj, hma, hmb⟩ := hsplit j
    have hms := (hF j).2.1
    rcases htri j t ht.1 ht.2 with ⟨u, hu, rfl⟩ | rfl | ⟨u, hu, rfl⟩ <;>
      rcases htri j t' ht'.1 ht'.2 with ⟨u', hu', rfl⟩ | rfl | ⟨u', hu', rfl⟩
    · rw [hL j hj, hL j hj] at heq
      rw [hc.ε_inj _ heq]
    · rw [hL j hj, hmid j hj, hms] at heq
      exact (hma (heq ▸ hL' j hj u hu)).elim
    · rw [hL j hj, hR j hj] at heq
      exact (disjoint_left.mp hdisj (hL' j hj u hu) (heq ▸ hR' j hj u' hu')).elim
    · rw [hL j hj, hmid j hj, hms] at heq
      exact (hma (heq ▸ hL' j hj u' hu')).elim
    · rfl
    · rw [hR j hj, hmid j hj, hms] at heq
      exact (hmb (heq ▸ hR' j hj u' hu')).elim
    · rw [hR j hj, hL j hj] at heq
      exact (disjoint_left.mp hdisj (hL' j hj u' hu') (heq ▸ hR' j hj u hu)).elim
    · rw [hR j hj, hmid j hj, hms] at heq
      exact (hmb (heq ▸ hR' j hj u hu)).elim
    · rw [hR j hj, hR j hj] at heq
      rw [hc.ε_inj _ heq]
  · intro j hj
    obtain ⟨hs, hdisj, hma, hmb⟩ := hsplit j
    have hms := (hF j).2.1
    apply subset_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      rw [hs]
      rcases htri j t ht.1 ht.2 with ⟨u, hu, rfl⟩ | rfl | ⟨u, hu, rfl⟩
      · rw [hL j hj]
        exact Or.inl (Or.inl (hL' j hj u hu))
      · rw [hmid j hj, hms]
        exact Or.inl (Or.inr rfl)
      · rw [hR j hj]
        exact Or.inr (hR' j hj u hu)
    · intro z hz
      rw [hs] at hz
      rcases hz with (hz | hz) | hz
      · rw [← hc.image_Ioo] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        obtain ⟨h₁, h₂⟩ := hrangeL j u hu.1
        refine ⟨_, ⟨h₁, ?_⟩, hL j hj u⟩
        rcases h₂ with h₂ | h₂
        · exact h₂.trans (hrange₁ j).2
        · exact (hu.2.ne h₂).elim
      · rw [mem_singleton_iff.mp hz, ← hms, ← hmid j hj]
        exact mem_image_of_mem _ (hrange₁ j)
      · rw [← hc.image_Ioo] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        obtain ⟨h₁, h₂⟩ := hrangeR j u hu.2
        exact ⟨_, ⟨(hrange₁ j).1.trans_le h₁, h₂⟩, hR j hj u⟩
  · rw [hend]
    exact hc₀

end GraphMinor.GM11
