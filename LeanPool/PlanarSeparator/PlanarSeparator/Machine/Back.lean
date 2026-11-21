/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.CycleRun
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.RootPath
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.InMark
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Label

/-!
# The separator program: the back half

From the stellar subdivision in memory (the reversals `A` at `[0, 3 m)`, the tree marks at
`[3 m, 6 m)`, the face weights at `[6 m, 7 m)`) and the levels, the parent darts, the face
representatives and the thin levels in place, the back half of the program

* runs the cycle search (`CycleSearch.cycleSep`) and copies its outcome to `r127 … r129`;
* marks the root paths of the dart `a` and the corners of the last triangle (`rootPaths`);
* finds the side of `a` (`sideOf`) and marks the faces inside the cycle (`inLoop`);
* labels the vertices, groups the pieces and prints the parts (`outPhase`).

`back_exec` states the outcome numerically, relative to a plane map `M` with spanning tree `T`
coded by the memory (`CycleSearch.Coded`): the outcome of the cycle search (`CycleOut`), the
search of the dual tree (`SB`), the inside marks `im`, and the output (`outList`) of the labels
`labN` with the separator marks `smN`.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset CycleSearch

/-- The outcome of the cycle search, copied to `r127` (mode), `r128` (`δ`), `r129` (`a`). -/
def copyOut : Stmt := block [.copyN 127 61, .copyN 128 50, .copyN 129 53]

/-- **The back half of the separator program.** -/
def back : Stmt :=
  .seq cycleSep (.seq copyOut (.seq rootPaths (.seq sideOf (.seq inLoop outPhase))))

open Classical in
/-- The separator mark of a vertex `x`, numerically: on the root path of `a` or of its reversal
`Aa`, or in mode `1` a corner of the triangle `δ`. -/
noncomputable def smN (tl rv fr pr L : ℕ → ℕ) (mode δ a Aa : ℕ) (x : ℕ) : ℕ :=
  if AncN tl rv pr L (uN tl rv fr a) x ∨ AncN tl rv pr L (uN tl rv fr Aa) x ∨
    (0 < mode ∧ (x = tl (δ / 3) ∨ x = tl (rv (δ / 3)))) then 1 else 0

theorem copyOut_wr {r : ℕ} (h1 : r ≠ 127) (h2 : r ≠ 128) (h3 : r ≠ 129) : copyOut.wr r = false := by
  simp [copyOut, block, Stmt.wr, Instr.wr]; omega

section proofs

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 3 * ∑ v ∈ range n, w v + 2 * n + 3 * m + 10 ≤ W)
include hN hIn hW

open Classical in
/-- **The back half of the separator program.** -/
theorem back_exec {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]
    {M : Map D Q} {T : M.SpTree} {cd : D ≃ Fin (3 * m)} (hm2 : 2 ≤ m)
    (L pr fr : ℕ → ℕ) (l₁ j j' : ℕ) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hR : CRegs m c)
    (hC : Coded M T m cd (fun x => c.nmem x) (fun x => c.nmem (3 * m + x)))
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (fw : M.Face → ℕ)
    (hFw : ∀ x, c.nmem (6 * m + (cd x : ℕ) / 3) = fw (M.face x))
    (hfwW : 11 * m + 3 * ∑ G, fw G + 4 ≤ W)
    (hfr : ∀ q < m, 1 ≤ fr q ∧ fr q ≤ m) (hfrm : ∀ q < m, c.nmem (11 * m + q) = fr q)
    (hpar : ∀ v < n, v ≠ 0 → pr v < m ∧ tl (pr v) = v ∧ L (parN tl rv pr v) + 1 = L v)
    (hL0 : L 0 = 0) (hprm : ∀ v < n, c.nmem (13 * m + n + v) = pr v)
    (hLm : ∀ v < n, c.nmem (13 * m + v) = L v) (hLn : ∀ v < n, L v < n)
    (h122 : c.nreg 122 = ∑ v ∈ range n, w v) (h123 : c.nreg 123 = l₁) (h125 : c.nreg 125 = j)
    (h126 : c.nreg 126 = j') (hl₁ : l₁ ≤ n) (hj : j ≤ n) (hj' : j' ≤ n)
    (hz7 : ∀ f < m, c.nmem (7 * m + f) = 0) (hz12 : ∀ G < m, c.nmem (12 * m + G) = 0)
    (hzs : ∀ v < n, c.nmem (13 * m + 4 * n + v) = 0)
    (hzp : ∀ i < 4, c.nmem (13 * m + 10 * n + 4 + i) = 0) :
    ∃ c' k, Exec P W back c c' k ∧ k ≤ 224 * m + 90 * n + 300 ∧
      ∃ (mode δ a : ℕ) (c₁ : Config) (im : ℕ → ℕ),
        CycleOut M T fw cd mode δ a ∧
        SB m (fun x => c.nmem x) (fun x => c.nmem (3 * m + x)) (fun f => c.nmem (6 * m + f)) W
          c.output c₁ ∧ c₁.nreg 11 = m ∧ im 0 = 0 ∧
        (∀ G < m, G ≠ 0 → im G =
          if G = (if c.nmem (3 * m + a) ≠ 0 then 0
            else if IsPd c₁.nmem m a then a / 3 else c.nmem a / 3) then 1
          else im (c.nmem (pd m c₁.nmem G) / 3)) ∧
        c'.output = c.output ++ outList n (∑ v ∈ range n, w v) w (fun v =>
          labN l₁ j j' (if c.nmem (3 * m + a) ≠ 0 then 0 else if IsPd c₁.nmem m a then 0 else 1)
            (L v)
            (smN tl rv fr pr L mode δ a (c.nmem a) v) (im (ofs v))) := by
  have hW' := hW; unfold memTop at hW'
  have hm1 : 1 ≤ m := by omega
  -- the cycle search
  obtain ⟨c₂, k₂, e₂, hk₂, ho₂, hout, hm₂, hr₂, hR₂, c₁, hS, hall, hpdm⟩ :=
    cycleSep_run (P := P) (W := W) (Fw := fun f => c.nmem (6 * m + f))
      hC hM hT3 hm2 fw hFw hfwW
      c hc hR ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ (fun f hf => hz7 f hf)
  generalize hmo : c₂.nreg 61 = mode at hout
  generalize hδ : c₂.nreg 50 = δ at hout
  generalize ha : c₂.nreg 53 = a at hout
  have haδ : a < 3 * m ∧ (0 < mode → δ < 3 * m) := by
    rcases hout with ⟨h0, a', ha', -⟩ | ⟨h1, δ', a', hδ', ha', -⟩
    · exact ⟨by rw [← ha']; exact (cd a').2, fun h => absurd h (by omega)⟩
    · exact ⟨by rw [← ha']; exact (cd a').2, fun _ => by rw [← hδ']; exact (cd δ').2⟩
  have hAa : c.nmem a < 3 * m := hC.tri.A_lt a haδ.1
  -- the copy
  obtain ⟨c₃, k₃, e₃, h127, h128, h129, hr₃, hm₃, ho₃, rfl⟩ : ∃ c₃ k₃, Exec P W copyOut c₂ c₃ k₃ ∧
      c₃.nreg 127 = mode ∧ c₃.nreg 128 = δ ∧ c₃.nreg 129 = a ∧
      (∀ r, r ≠ 127 → r ≠ 128 → r ≠ 129 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧
      c₃.output = c₂.output ∧ k₃ = 3 := by
    have hw₂ := e₂.wb_right
    unfold copyOut
    exec_block
    refine ⟨by config_simp; exact hmo, by config_simp; exact hδ, by config_simp; exact ha,
      fun r h1 h2 h3 => by simp only [upd_apply, h1, h2, h3, ↓reduceIte], rfl, rfl, rfl⟩
  have hr₃' : ∀ r, 100 ≤ r → r ≠ 127 → r ≠ 128 → r ≠ 129 → c₃.nreg r = c.nreg r :=
    fun r h0 h1 h2 h3 => (hr₃ r h1 h2 h3).trans (hr₂ r (by omega))
  have hL₃ : Lay n m c₃ := hL.of fun r h1 h2 => hr₃' r h1 (by omega) (by omega) (by omega)
  have hm₃' : ∀ x, (x < 7 * m ∨ 11 * m ≤ x) → c₃.nmem x = c.nmem x := fun x hx => by
    rw [hm₃]; exact hm₂ x hx
  -- the root paths
  obtain ⟨c₄, k₄, e₄, hk₄, ho₄, hr₄, hf₄, hmk₄⟩ := rootPaths_exec hN hIn
    (by unfold memTop; omega) fr pr L hfr hpar hL0 c₃ e₃.wb_right hL₃
    (fun q hq => (hm₃' _ (Or.inr (by omega))).trans (hfrm q hq))
    (fun v hv => (hm₃' _ (Or.inr (by omega))).trans (hprm v hv))
    (fun v hv => (hm₃' _ (Or.inr (by omega))).trans (hLm v hv)) hLn
    (by rw [h129]; exact haδ.1) (by rw [h129, hm₃' _ (Or.inl (by omega))]; exact hAa)
    (by rw [h127, h128]; exact haδ.2)
  rw [h129, h127, h128, hm₃' _ (Or.inl (by omega))] at hmk₄
  have hR₄ : ∀ r, 100 ≤ r → r ≠ 127 → r ≠ 128 → r ≠ 129 → c₄.nreg r = c.nreg r :=
    fun r h0 h1 h2 h3 => (hr₄ r h0).trans (hr₃' r h0 h1 h2 h3)
  have hL₄ : Lay n m c₄ := hL₃.of fun r h1 _ => hr₄ r h1
  have hm₄' : ∀ x, (x < 7 * m ∨ 11 * m ≤ x) → ¬ (13 * m + 4 * n ≤ x ∧ x < 13 * m + 5 * n) →
      c₄.nmem x = c.nmem x := fun x h1 h2 => (hf₄ x h2).trans (hm₃' x h1)
  have h8₄ : c₄.nreg 8 = 8 * m := by
    rw [e₄.nreg_of_wr (by decide), hr₃ 8 (by omega) (by omega) (by omega)]
    exact hR₂.2.2.2.2.2.2.2.2.1
  have h129₄ : c₄.nreg 129 = a := by rw [hr₄ 129 (by omega), h129]
  have hpd₄ : c₄.nmem (8 * m + a / 3) = c₁.nmem (8 * m + a / 3) := by
    rw [hf₄ _ (by omega), hm₃, hpdm _ (by omega) (by omega)]
  have hIs : IsPd c₄.nmem m a ↔ IsPd c₁.nmem m a := by unfold IsPd; rw [hpd₄]
  have hA₄ : c₄.nmem a = c.nmem a := hm₄' a (Or.inl (by omega)) (by omega)
  -- the side
  have hT₄ : c₄.nmem (3 * m + a) = c.nmem (3 * m + a) := hm₄' _ (Or.inl (by omega)) (by omega)
  obtain ⟨c₅, k₅, e₅, hk₅, hm₅, ho₅, hr₅, h130, h131⟩ := sideOf_exec (P := P)
    (by unfold memTop; omega) c₄ e₄.wb_right hL₄ h8₄ (by rw [h129₄]; exact haδ.1)
  rw [h129₄, hA₄, hT₄] at h130
  rw [h129₄, hT₄] at h131
  have h130' : c₅.nreg 130 = (if c.nmem (3 * m + a) ≠ 0 then 0
      else if IsPd c₁.nmem m a then a / 3 else c.nmem a / 3) := by
    rw [h130]; by_cases hp : IsPd c₁.nmem m a
    · rw [ite_eq_left hp, ite_eq_left (hIs.2 hp)]
    · rw [ite_eq_right hp, ite_eq_right (fun h => hp (hIs.1 h))]
  have h131' : c₅.nreg 131 = (if c.nmem (3 * m + a) ≠ 0 then 0
      else if IsPd c₁.nmem m a then 0 else 1) := by
    rw [h131]; by_cases hp : IsPd c₁.nmem m a
    · rw [ite_eq_left hp, ite_eq_left (hIs.2 hp)]
    · rw [ite_eq_right hp, ite_eq_right (fun h => hp (hIs.1 h))]
  have hR₅ : ∀ r, 100 ≤ r → r ≠ 127 → r ≠ 128 → r ≠ 129 → r ≠ 130 → r ≠ 131 →
      c₅.nreg r = c.nreg r := fun r h0 h1 h2 h3 h4 h5 =>
    (hr₅ r (by omega) (by omega) (by omega) (by omega) (by omega) h4 h5).trans
      (hR₄ r h0 h1 h2 h3)
  have hL₅ : Lay n m c₅ := hL₄.of fun r h1 h2 =>
    hr₅ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hsideW : sideOf.wr 8 = false ∧ sideOf.wr 9 = false := by decide
  have h8₅ : c₅.nreg 8 = 8 * m := by rw [e₅.nreg_of_wr hsideW.1, h8₄]
  have h9₅ : c₅.nreg 9 = 9 * m := by
    rw [e₅.nreg_of_wr hsideW.2, e₄.nreg_of_wr (by decide), hr₃ 9 (by omega) (by omega) (by omega)]
    exact hR₂.2.2.2.2.2.2.2.2.2.1
  -- the inside marks
  have hq := hS.q_lt
  rw [hall] at hq
  obtain ⟨c₆, k₆, e₆, hk₆, ho₆, hr₆, hf₆, h12₆, him₆⟩ := inLoop_exec (P := P) hm1
    (by unfold memTop; omega) (qu m c₁.nmem) (pd m c₁.nmem) (fun x => c.nmem x) _ hq
    (fun i hi j hj e => hS.q_inj i (by omega) j (by omega) e) hS.q0.2
    (fun G hG => hS.exists_pos hall hG)
    (fun i h1 h2 => by
      obtain ⟨p1, p2, -, i', hi', p3⟩ := hS.pd_ok i h1 (by omega)
      exact ⟨p2, hC.tri.A_lt _ p2, i', hi', p3⟩)
    c₅ e₅.wb_right hL₅ h8₅ h9₅ h130'
    (fun i hi => by rw [hm₅, hf₄ _ (by omega), hm₃, hpdm _ (by omega) (by omega)]; rfl)
    (fun G hG => by rw [hm₅, hf₄ _ (by omega), hm₃, hpdm _ (by omega) (by omega)]; rfl)
    (fun x hx => by rw [hm₅]; exact hm₄' x (Or.inl (by omega)) (by omega))
    (fun G hG => by rw [hm₅, hm₄' _ (Or.inr (by omega)) (by omega)]; exact hz12 G hG)
  have hR₆ : ∀ r, 100 ≤ r → r ≠ 127 → r ≠ 128 → r ≠ 129 → r ≠ 130 → r ≠ 131 →
      c₆.nreg r = c.nreg r := fun r h0 h1 h2 h3 h4 h5 =>
    (hr₆ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hR₅ r h0 h1 h2 h3 h4 h5)
  have hL₆ : Lay n m c₆ := hL₅.of fun r h1 h2 =>
    hr₆ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hm₆' : ∀ x, (x < 7 * m ∨ 11 * m ≤ x) → ¬ (13 * m + 4 * n ≤ x ∧ x < 13 * m + 5 * n) →
      ¬ (12 * m ≤ x ∧ x < 13 * m) → c₆.nmem x = c.nmem x := fun x h1 h2 h3 => by
    rw [hf₆ x h3, hm₅]; exact hm₄' x h1 h2
  -- the labels and the output
  obtain ⟨c₇, k₇, e₇, hk₇, ho₇⟩ := outPhase_exec hN hIn hW L
    (smN tl rv fr pr L mode δ a (c.nmem a)) (fun x => c₆.nmem (12 * m + x)) l₁ j j' _ c₆
    e₆.wb_right hL₆ (fun v hv => by
      rw [hm₆' _ (Or.inr (by omega)) (by omega) (by omega)]; exact hLm v hv)
    (fun v hv => (hLn v hv).le)
    (fun v hv => by
      rw [hf₆ _ (by omega), hm₅, hmk₄ v hv, hm₃' _ (Or.inr (by omega)), hzs v hv]; rfl)
    (fun x _ => rfl)
    (by rw [hR₆ 122 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h122])
    (by rw [hR₆ 123 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h123])
    (by rw [hR₆ 125 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h125])
    (by rw [hR₆ 126 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h126])
    (by rw [hr₆ 131 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h131'])
    hl₁ hj hj'
    (fun i hi => by rw [hm₆' _ (Or.inr (by omega)) (by omega) (by omega)]; exact hzp i hi)
  refine ⟨c₇, k₂ + (3 + (k₄ + (k₅ + (k₆ + k₇)))),
    .seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))), by omega, mode, δ, a, c₁,
    fun x => c₆.nmem (12 * m + x), hout, hS, hall, by simpa using h12₆, fun G hG hG0 => ?_, ?_⟩
  · exact him₆ G hG hG0
  · rw [ho₇, ho₆, ho₅, ho₄, ho₃, ho₂]

end proofs

end SepProg

end PlanarSeparator
