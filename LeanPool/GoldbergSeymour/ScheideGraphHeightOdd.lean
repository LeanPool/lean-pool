/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.AdjacentEdges
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.IsProperEdgeColoring
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.PresentColors
public import LeanPool.GoldbergSeymour.ScheideGraphHeight
public import LeanPool.GoldbergSeymour.ScheideNormalisation
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Scheide Graph Height Odd

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_branch_188.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (alpha beta : Fin k) (_ : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl
        (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl
        (T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (T' :
        TreeSequence G e0) (_ : NormalGlobalMaximumTriple G k e0 phi T'), alpha ∈ MissingColors G
        phi (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ)))) →
    ∀ (m : ℕ) (f : E) (c : PartialEdgeColoring E m) (S : TreeSequence G f) (M :
        NormalGlobalMaximumTriple G m f c S), IsProperEdgeColoring G c →
    let path : (TwoColorIncidenceGraph G c M.alpha M.beta).Walk (Sum.inl (S.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ S.positive⟩ : Fin (S.length + (1 : ℕ))))) (Sum.inl (S.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ S.length⟩ : Fin (S.length + (1 : ℕ))))) := M.closingPath; path.length =
        (2 : ℕ) * (M.height - (1 : ℕ)) → (
    ∀ i ≤ path.length, (i % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), path.getVert i = Sum.inl v) ∧ (i % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), path.getVert i = Sum.inr e)) → (
    ∀ i < M.height - (1 : ℕ),
    ∃ (e : E), path.getVert ((2 : ℕ) * i + (1 : ℕ)) = Sum.inr e ∧ (c e = some M.alpha ∨ c e = some
        M.beta)) →
    ∀ (i : ℕ), (i < M.height - (1 : ℕ) → (i % (2 : ℕ) = (0 : ℕ) →
    ∃ (e : E), path.getVert ((2 : ℕ) * i + (1 : ℕ)) = Sum.inr e ∧ c e = some M.alpha) ∧ (i % (2 :
        ℕ) = (1 : ℕ) →
    ∃ (e : E), path.getVert ((2 : ℕ) * i + (1 : ℕ)) = Sum.inr e ∧ c e = some M.beta)) → i + (1 :
        ℕ) < M.height - (1 : ℕ) → ((i + (1 : ℕ)) % (2 : ℕ) = (0 : ℕ) →
    ∃ (e : E), path.getVert ((2 : ℕ) * (i + (1 : ℕ)) + (1 : ℕ)) = Sum.inr e ∧ c e = some M.alpha)
        ∧ ((i + (1 : ℕ)) % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), path.getVert ((2 : ℕ) * (i + (1 : ℕ)) + (1 : ℕ)) = Sum.inr e ∧ c e = some M.beta)
  := by
  classical
  intro V E _ _ _ G k e0 phi T alpha beta path0 T' N ha m f c S M hproper path hpathlen hshape
      hcolored i ih hi
  have hold : i < M.height - 1 := by omega
  have hprev := ih hold
  have hcur := hcolored (i + 1) hi
  constructor
  · intro heven
    obtain ⟨e, he, hc⟩ := hprev.2 (by omega)
    obtain ⟨f, hf, hfcol⟩ := hcur
    have hdiff : e ≠ f := by
      intro hef
      subst f
      have hinj : Function.Injective path.support.get :=
        (SimpleGraph.Walk.isPath_iff_injective_get_support path).mp M.closingPath_isPath
      have hia : 2 * i + 1 < path.support.length := by
        simp only [path.length_support]
        rw [hpathlen]
        omega
      have hib : 2 * (i + 1) + 1 < path.support.length := by
        simp only [path.length_support]
        rw [hpathlen]
        omega
      let a : Fin path.support.length := ⟨2 * i + 1, hia⟩
      let b : Fin path.support.length := ⟨2 * (i + 1) + 1, hib⟩
      have hab : a = b := by
        apply hinj
        have ha' := congrFun path.getVert_comp_val_eq_get_support a
        have hb' := congrFun path.getVert_comp_val_eq_get_support b
        rw [← ha', ← hb']
        exact he.trans hf.symm
      have habval : 2 * i + 1 = 2 * (i + 1) + 1 := by
        simpa [a, b] using congrArg Fin.val hab
      omega
    have hv : ∃ v, path.getVert (2 * i + 2) = Sum.inl v := (hshape (2 * i + 2)
        (by rw [hpathlen]; omega)).1 (by omega)
    obtain ⟨v, hv⟩ := hv
    have ha := path.adj_getVert_succ (i := 2 * i + 1) (by rw [hpathlen]; omega)
    have hb' := path.adj_getVert_succ (i := 2 * i + 2) (by rw [hpathlen]; omega)
    rw [he, hv] at ha
    have hf' : path.getVert (2 * i + 2 + 1) = Sum.inr f := by
      have hidx : 2 * i + 2 + 1 = 2 * (i + 1) + 1 := by omega
      rw [hidx]
      exact hf
    rw [hv, hf'] at hb'
    have hb'' : (TwoColorIncidenceGraph G c M.alpha M.beta).Adj (Sum.inl v)
        (path.getVert (2 * (i + 1) + 1)) := by
      have hidx : 2 * i + 2 + 1 = 2 * (i + 1) + 1 := by omega
      rw [← hf] at hb'
      convert hb' using 1
    have haInfo : Incident G v e ∧ (c e = some M.alpha ∨ c e = some M.beta) := by
      simpa [TwoColorIncidenceGraph] using ha
    rw [hf] at hb''
    have hbInfo : Incident G v f ∧ (c f = some M.alpha ∨ c f = some M.beta) := by
      simpa [TwoColorIncidenceGraph] using hb''
    have hne : ∀ {q : Fin m}, c e = some q → c f ≠ some q := by
      intro q hq
      exact hproper (c := q) hdiff ⟨v, haInfo.1, hbInfo.1⟩ hq
    have bad : c f = some M.alpha := hfcol.resolve_right (by
      intro hfb
      exact (hne hc) hfb)
    exact ⟨f, hf, bad⟩
  · intro hodd
    obtain ⟨e, he, hc⟩ := hprev.1 (by omega)
    obtain ⟨f, hf, hfcol⟩ := hcur
    have hdiff : e ≠ f := by
      intro hef
      subst f
      have hinj : Function.Injective path.support.get :=
        (SimpleGraph.Walk.isPath_iff_injective_get_support path).mp M.closingPath_isPath
      have hia : 2 * i + 1 < path.support.length := by
        simp only [path.length_support]
        rw [hpathlen]
        omega
      have hib : 2 * (i + 1) + 1 < path.support.length := by
        simp only [path.length_support]
        rw [hpathlen]
        omega
      let a : Fin path.support.length := ⟨2 * i + 1, hia⟩
      let b : Fin path.support.length := ⟨2 * (i + 1) + 1, hib⟩
      have hab : a = b := by
        apply hinj
        have ha' := congrFun path.getVert_comp_val_eq_get_support a
        have hb' := congrFun path.getVert_comp_val_eq_get_support b
        rw [← ha', ← hb']
        exact he.trans hf.symm
      have habval : 2 * i + 1 = 2 * (i + 1) + 1 := by
        simpa [a, b] using congrArg Fin.val hab
      omega
    obtain ⟨v, hv⟩ := (hshape (2 * i + 2) (by rw [hpathlen]; omega)).1 (by omega)
    have ha := path.adj_getVert_succ (i := 2 * i + 1) (by rw [hpathlen]; omega)
    have hb' := path.adj_getVert_succ (i := 2 * i + 2) (by rw [hpathlen]; omega)
    rw [he, hv] at ha
    have hf' : path.getVert (2 * i + 2 + 1) = Sum.inr f := by
      have hidx : 2 * i + 2 + 1 = 2 * (i + 1) + 1 := by omega
      rw [hidx]
      exact hf
    rw [hv, hf'] at hb'
    have hb'' : (TwoColorIncidenceGraph G c M.alpha M.beta).Adj (Sum.inl v)
        (path.getVert (2 * (i + 1) + 1)) := by
      have hidx : 2 * i + 2 + 1 = 2 * (i + 1) + 1 := by omega
      rw [← hf] at hb'
      convert hb' using 1
    have haInfo : Incident G v e ∧ (c e = some M.alpha ∨ c e = some M.beta) := by
      simpa [TwoColorIncidenceGraph] using ha
    rw [hf] at hb''
    have hbInfo : Incident G v f ∧ (c f = some M.alpha ∨ c f = some M.beta) := by
      simpa [TwoColorIncidenceGraph] using hb''
    have bad : c f = some M.beta := hfcol.resolve_left (by
      intro hfa
      exact (hproper (c := M.alpha) hdiff ⟨v, haInfo.1, hbInfo.1⟩ hc) hfa)
    exact ⟨f, hf, bad⟩

theorem ScheideGraphHeightOdd {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    3 ≤ ScheideGraphHeight G ∧ Odd (ScheideGraphHeight G) := by
  classical
  obtain ⟨alpha, beta, path0, T', N, ha, hb, hpath0, hcomp, hNa, hNb, hNh⟩ :=
    ScheideNormalisation G k e0 phi T hglobal
  have hcard : T'.length + 1 ≤ Fintype.card V := by
    simpa using Fintype.card_le_of_injective T'.vertex T'.vertex_injective
  have hNcard : N.height < Fintype.card V + 1 := by
    exact lt_of_le_of_lt N.height_upper (by omega)
  let heights := (Finset.range (Fintype.card V + 1)).filter (fun p =>
    ∃ (m : ℕ) (f : E) (c : PartialEdgeColoring E m)
      (S : TreeSequence G f),
      ∃ M : NormalGlobalMaximumTriple G m f c S, M.height = p)
  have hmem : N.height ∈ heights := by
    simp only [Finset.mem_filter, Finset.mem_range.mpr hNcard, true_and, heights]
    exact ⟨k, e0, phi, T', N, rfl⟩
  unfold ScheideGraphHeight
  dsimp [heights] at hmem ⊢
  let witness := (insert 0 ((Finset.range (Fintype.card V + 1)).filter (fun p =>
    ∃ (m : ℕ) (f : E) (c : PartialEdgeColoring E m)
      (S : TreeSequence G f),
      ∃ M : NormalGlobalMaximumTriple G m f c S, M.height = p))).max'
      (by simp [])
  have hw : witness ∈ insert 0 ((Finset.range (Fintype.card V + 1)).filter (fun p =>
    ∃ (m : ℕ) (f : E) (c : PartialEdgeColoring E m)
      (S : TreeSequence G f),
      ∃ M : NormalGlobalMaximumTriple G m f c S, M.height = p)) :=
    Finset.max'_mem _ _
  have hle : N.height ≤ witness := by
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem hmem
  rcases Finset.mem_insert.mp hw with hz | hz
  · exfalso
    omega
  · rcases Finset.mem_filter.mp hz with ⟨_, ⟨m, f, c, S, M, hM⟩⟩
    have hm : M.height = witness := hM
    have hproper : IsProperEdgeColoring G c := M.global.1.2.2.2.1
    let path := M.closingPath
    have hpathlen : path.length = 2 * (M.height - 1) := by
      simpa [path] using M.closingPath_length
    have hshape : ∀ i ≤ path.length,
        (i % 2 = 0 → ∃ v, path.getVert i = Sum.inl v) ∧
        (i % 2 = 1 → ∃ e, path.getVert i = Sum.inr e) := by
      intro i
      induction i with
      | zero =>
          intro hi
          constructor <;> intro hpar
          · exact ⟨S.vertex ⟨1, Nat.succ_lt_succ S.positive⟩, by
              simpa [path] using path.getVert_zero⟩
          · omega
      | succ i ih =>
          intro hi
          have hil : i < path.length := by omega
          have hadj := path.adj_getVert_succ hil
          have hs := ih (by omega)
          constructor
          · intro heven
            obtain ⟨e, he⟩ := hs.2 (by omega)
            cases hn : path.getVert (i + 1) with
            | inl v => exact ⟨v, rfl⟩
            | inr e' =>
                rw [he, hn] at hadj
                simp [TwoColorIncidenceGraph] at hadj
          · intro hodd
            obtain ⟨v, hv⟩ := hs.1 (by omega)
            cases hn : path.getVert (i + 1) with
            | inl v' =>
                rw [hv, hn] at hadj
                simp [TwoColorIncidenceGraph] at hadj
            | inr e => exact ⟨e, rfl⟩
    have hcolored : ∀ i < M.height - 1, ∃ e,
        path.getVert (2 * i + 1) = Sum.inr e ∧
          (c e = some M.alpha ∨ c e = some M.beta) := by
      intro i hi
      have hlen : 2 * i + 1 ≤ path.length := by
        rw [hpathlen]
        omega
      obtain ⟨e, he⟩ := (hshape (2 * i + 1) hlen).2 (by omega)
      obtain ⟨v, hv⟩ := (hshape (2 * i) (by omega)).1 (by omega)
      have hadj := path.adj_getVert_succ (by omega : 2 * i < path.length)
      rw [hv, he] at hadj
      simp only [TwoColorIncidenceGraph] at hadj
      exact ⟨e, he, hadj.2⟩
    have hlow := M.height_lower
    have hfirst : ∃ e, path.getVert 1 = Sum.inr e ∧ c e = some M.alpha := by
      obtain ⟨e, he, hc⟩ := hcolored 0 (by omega)
      have hv : path.getVert 0 = Sum.inl (S.vertex ⟨1, Nat.succ_lt_succ S.positive⟩) := by
        simpa [path] using path.getVert_zero
      have hadj := path.adj_getVert_succ (i := 0) (by rw [hpathlen]; omega)
      rw [hv, he] at hadj
      simp only [TwoColorIncidenceGraph] at hadj
      have hnot : c e ≠ some M.beta := by
        intro heβ
        have hp : M.beta ∈ PresentColors G c (S.vertex ⟨1, Nat.succ_lt_succ S.positive⟩) := by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨e, hadj.1, heβ⟩
        have hm := M.beta_missing
        have hnotmem : M.beta ∉ PresentColors G c (S.vertex ⟨1, Nat.succ_lt_succ S.positive⟩) := by
          simpa [MissingColors] using hm
        exact hnotmem hp
      exact ⟨e, he, hc.resolve_right hnot⟩
    have hlast : ∃ e, path.getVert (path.length - 1) = Sum.inr e ∧ c e = some M.beta := by
      have hmpos : 0 < M.height - 1 := by
        have hlow := M.height_lower
        omega
      obtain ⟨e, he, hc⟩ := hcolored (M.height - 2) (by omega)
      have hv : path.getVert path.length = Sum.inl (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩) := by
        simpa [path] using path.getVert_length
      have hepos : 2 * (M.height - 2) + 1 = path.length - 1 := by
        rw [hpathlen]
        omega
      have hadj := path.adj_getVert_succ (i := path.length - 1) (by rw [hpathlen]; omega)
      have hnext : path.length - 1 + 1 = path.length := by rw [hpathlen]; omega
      rw [hepos] at he
      have hnext : path.length - 1 + 1 = path.length := by rw [hpathlen]; omega
      rw [hnext] at hadj
      rw [hv, he] at hadj
      simp only [TwoColorIncidenceGraph, Fin.zero_eta] at hadj
      have hnot : c e ≠ some M.alpha := by
        intro heα
        have hp : M.alpha ∈ PresentColors G c (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩) := by
          change M.alpha ∈ (Finset.univ.filter (fun q =>
            ∃ g, Incident G (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩) g ∧ c g = some q))
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, e, hadj.1, heα⟩
        have hm := M.alpha_missing
        have hnotmem : M.alpha ∉ PresentColors G c (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩) := by
          simpa [MissingColors] using hm
        exact hnotmem hp
      exact ⟨e, he, hc.resolve_left hnot⟩
    have hnecolor : M.alpha ≠ M.beta := by
      intro hab
      obtain ⟨e, he, hc⟩ := hfirst
      have hv : path.getVert 0 = Sum.inl (S.vertex ⟨1, Nat.succ_lt_succ S.positive⟩) := by
        simpa [path] using path.getVert_zero
      have hadj := path.adj_getVert_succ (i := 0) (by rw [hpathlen]; omega)
      rw [hv, he] at hadj
      simp only [TwoColorIncidenceGraph] at hadj
      have hp : M.beta ∈ PresentColors G c (S.vertex ⟨1, Nat.succ_lt_succ S.positive⟩) := by
        simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨e, hadj.1, hab ▸ hc⟩
      have hnotmem : M.beta ∉ PresentColors G c (S.vertex ⟨1, Nat.succ_lt_succ S.positive⟩) := by
        simpa [MissingColors] using M.beta_missing
      exact hnotmem hp
    have hflip : ∀ i < M.height - 1,
        (i % 2 = 0 → ∃ e, path.getVert (2 * i + 1) = Sum.inr e ∧ c e = some M.alpha) ∧
        (i % 2 = 1 → ∃ e, path.getVert (2 * i + 1) = Sum.inr e ∧ c e = some M.beta) := by
      intro i
      induction i with
      | zero =>
          intro hi
          exact ⟨fun _ => hfirst, fun h => by omega⟩
      | succ i ih =>
          exact @helper_branch_188 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
              (@e0) (@phi) (@T) (@alpha) (@beta) (@path0) (@T') (@N) (@ha) (@m) (@f) (@c) (@S)
              (@M) (@hproper) (@hpathlen) (@hshape) (@hcolored) (@i) (@ih)
    have hlastIndex : 2 * (M.height - 2) + 1 = path.length - 1 := by
      rw [hpathlen]
      omega
    obtain ⟨el, hel, hcl⟩ := hlast
    have hpar : (M.height - 2) % 2 = 1 := by
      by_contra hn
      have heven : (M.height - 2) % 2 = 0 := by omega
      obtain ⟨ea, hea, hca⟩ := (hflip (M.height - 2) (by omega)).1 heven
      have heq : ea = el := by
        apply Sum.inr.inj
        rw [← hea, hlastIndex, hel]
      subst el
      exact hnecolor (Option.some.inj (hca.symm.trans hcl))
    have hoddM : Odd M.height := by
      refine ⟨(M.height - 1) / 2, ?_⟩
      omega
    constructor
    · omega
    · simpa [hm] using hoddM

end GoldbergSeymour

end
