/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.FTAP.MarketFTAP
public import LeanPool.MathFin.Models.Binomial.Market
public import LeanPool.MathFin.Models.ModelFree.RoperConverse
public import LeanPool.MathFin.Models.Rates.VasicekMarket
public import LeanPool.MathFin.Risk.AcceptanceSet
public import LeanPool.MathFin.Risk.WorstCaseRisk

/-!
# Pricing measures, market models and coherent risk

Source: arxiv:2606.01356, url:https://github.com/formal-applied-math/formal-mathfin/tree/55e29a93e75f10b40f61f45c78a6058b2938045f
Authors: Raphael Coelho, Robert Martin, Yang Ye, Alfredo Garcia, Aleksey Salkutsan
Status: verified
Main declarations: `MathFin.Market.noArbitrage_iff_exists_isPricingMeasure_of_finite`,
  `MathFin.Contracts.Binomial.price_pay_eq_binomialPrice_of_isPricingMeasure`,
  `MathFin.exists_market_of_isNormalizedCallPrice`, `MathFin.Rates.price_pay_vasicekMarket`,
  `MathFin.coherentRisk_isLUB`
Tags: mathematical-finance, discrete-time-martingales, asset-pricing, risk-measures
MSC: 91G20, 91G70, 60G44
-/
