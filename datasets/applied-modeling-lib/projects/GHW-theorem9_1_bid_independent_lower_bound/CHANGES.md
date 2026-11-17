# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `fa5379e08df8c13e2bbfb85757bd2675b201d124`](https://github.com/nikhgarg/AppliedModelingLib/blob/fa5379e08df8c13e2bbfb85757bd2675b201d124/papers/GHW01DigitalGoods/PaperInterface.lean).

Roots: `GHW01DigitalGoods.PaperInterface.theorem9_1_bid_independent_lower_bound`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`.

Relocate project-local imports and adapt the historical finite-sum/probability interfaces and proof elaboration. Preserve the selected mechanism, rating-system or fair-division formulation.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Foundations/Math/Asymptotics.lean`, `EconCSLib/Foundations/Math/FiniteSum.lean`, `EconCSLib/Foundations/Probability/FairCoin.lean`, `EconCSLib/Foundations/Probability/MeasureInequalities.lean`, `EconCSLib/Foundations/Probability/OrderStatistics.lean`, `EconCSLib/Foundations/Probability/RealDistribution.lean`, `EconCSLib/MechanismDesign/Auctions/Combinatorial.lean`, `EconCSLib/MechanismDesign/Auctions/DigitalGoods.lean`, `EconCSLib/MechanismDesign/Auctions/Position.lean`, `GHW01DigitalGoods/AuctionMainTheorems.lean`, `GHW01DigitalGoods/BoundedSourceDefinitions.lean`, `GHW01DigitalGoods/FixedSizeSampling.lean`, `GHW01DigitalGoods/PaperInterface.lean`, `GHW01DigitalGoods/RandomSamplingDirectional.lean`, `GHW01DigitalGoods/Section11FixedSizeBridge.lean`.
