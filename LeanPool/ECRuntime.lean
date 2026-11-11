/-
Copyright (c) 2026 Jiri Kovar, Jakub Kudela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiri Kovar, Jakub Kudela
-/
module

public import LeanPool.ECRuntime.ConstantExitRuntime
public import LeanPool.ECRuntime.OneMaxUnaryHarmonic
public import LeanPool.ECRuntime.RLSAllDimensionPaperSharpCentered
public import LeanPool.ECRuntime.RandomStakeCouponArbitraryTargetFiniteHorizon
public import LeanPool.ECRuntime.RandomStakeCouponArbitraryTargetRuntime
public import LeanPool.ECRuntime.RandomStakeCouponSharpPaperCentered
public import LeanPool.ECRuntime.TrajectoryFirstHittingTime

/-!
# Sharp coupon collection and randomized local search

Source: arxiv:1308.6384, url:https://github.com/UAI-VUT-Brno/Runtime-analysis-of-evolutionary-computation-algorithms/tree/a0e34dce6395d48d0fb9c7b8850088973f503d8b
Authors: Jiri Kovar, Jakub Kudela
Status: verified
Main declarations: `ECRuntime.proposed_randomStakeCoupon_allDimensionPaperSharpCentered`,
  `ECRuntime.proposed_strictMonotoneRLS_allDimensionPaperSharpCentered`
Tags: coupon-collector, randomized-local-search, expected-runtime, markov-chains, asymptotics
MSC: 60J10, 60G40, 68Q25, 68W20
-/

/-!
## Imported source and scope

This project preserves the coupon-collector and one-bit randomized local-search
results of `UAI-VUT-Brno/Runtime-analysis-of-evolutionary-computation-algorithms`
at commit `a0e34dce6395d48d0fb9c7b8850088973f503d8b`, under Apache-2.0.
The selected endpoint files were merged in upstream PR 1 on 25 October 2026.
The source authors are Jiri Kovar and Jakub Kudela.

The upstream README describes Claude Code prover agents and human statement and
promotion gates. The card classifies the proof-production workflow as AI;
it does not infer substantial human-written proofs from human approval alone.

The imported scope includes exact finite means, the sharp correction for both
parities, finite Markov and Bellman theory, geometric survival, and the bridge
to the expected first hitting time under an Ionescu–Tulcea trajectory measure.
The coupon kernel is explicitly shown to average the updates setting a uniformly
sampled coordinate to true, including samples of already collected coupons.

Names beginning with `candidate` or `proposed` preserve upstream identifiers;
their bodies are complete proofs. Historical stage comments have been updated
where they described a proved dependency as pending.
-/
