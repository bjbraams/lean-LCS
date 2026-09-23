/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn

/-!
# First countability for functions with fixed compact support

The topology of `𝓓^{n}_{K}(E, F)` is induced by its countable family of derivative maps
into spaces of bounded continuous functions. Consequently it is first countable, for every
smoothness order `n : ℕ∞`, without completeness or finite-dimensionality assumptions.
The notation is Mathlib's `Distributions` notation for functions supported in the compact
set `K`.
-/

public section

open TopologicalSpace
open scoped Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} {K : Compacts E}

/-- The topology of functions of fixed differentiability order supported in a fixed compact
set is first countable, as it is induced by countably many derivative sup norms. -/
instance instFirstCountableTopology : FirstCountableTopology 𝓓^{n}_{K}(E, F) :=
  (isUniformEmbedding_pi_structureMapCLM (E := E) (F := F) (n := n) (K := K) ℝ).isEmbedding
    |>.firstCountableTopology

end ContDiffMapSupportedIn
