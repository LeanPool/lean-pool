/-
Copyright (c) 2026 Tutte formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tutte formalization contributors
-/
module

public import LeanPool.TuttePath.PathTheorem

/-!
# Tutte’s path theorem for matroids

Source: arxiv:2601.02582, url:https://github.com/mbaker386/tutte-homotopy-lean
Authors: Tutte formalization contributors
Status: verified
Main declarations: `TutteFormalization.path_theorem`
Tags: matroids, combinatorics, modular-cuts
MSC: 05B35
-/

/-!
# Attribution and scope

Adapted from https://github.com/mbaker386/tutte-homotopy-lean at commit
ab33c23369865b5fbd30b7a19710a527aa7ebab6, under Apache-2.0.
This project preserves the independent path theorem and its structural dependencies.
The mathematical source is *A modern perspective on Tutte's homotopy theorem*
by Matthew Baker, Tong Jin, and Oliver Lorscheid, with an appendix by Juš Kocutar.
Upstream credits Codex-assisted development coordinated by Matthew Baker and
ChatGPT-assisted mathematical review; its software attribution is collective.
Lean Pool adaptations add module-system integration and update the pinned dependencies.
-/
