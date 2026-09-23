/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Convex.Gauge

/-!
# Gauge seminorm balls of convex balanced neighbourhoods

`gaugeSeminorm_ball_mem_nhds` shows that positive-radius gauge seminorm balls are
neighbourhoods of zero. `gaugeSeminorm_ball_one_subset` places the open unit ball inside
the original convex balanced neighbourhood. These results need no locally convex
ambient topology.

## References

* [H. H. Schaefer and M. P. Wolff, *Topological Vector Spaces*][schaefer1999], II §4
-/

public section

open Set Filter

open scoped Topology Pointwise

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
  [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Balls of the gauge seminorm of a convex balanced neighbourhood of zero are neighbourhoods
of zero. -/
theorem gaugeSeminorm_ball_mem_nhds {W : Set E} (hW : W ∈ 𝓝 (0 : E)) (hc : Convex ℝ W)
    (hb : Balanced 𝕜 W) {r : ℝ} (hr : 0 < r) :
    (gaugeSeminorm hb hc (absorbent_nhds_zero hW)).ball 0 r ∈ 𝓝 (0 : E) := by
  have hcont : ContinuousAt (gauge W) 0 := (continuous_gauge hc hW).continuousAt
  have h0 : Iio r ∈ 𝓝 (gauge W (0 : E)) := by
    rw [gauge_zero]
    exact Iio_mem_nhds hr
  refine mem_of_superset (hcont.preimage_mem_nhds h0) fun x hx ↦ ?_
  rw [Seminorm.mem_ball_zero]
  exact hx

omit [IsTopologicalAddGroup E] in
/-- The open unit ball of the gauge seminorm of a convex neighbourhood of zero lies in that
neighbourhood. -/
theorem gaugeSeminorm_ball_one_subset {W : Set E} (hW : W ∈ 𝓝 (0 : E)) (hc : Convex ℝ W)
    (hb : Balanced 𝕜 W) : (gaugeSeminorm hb hc (absorbent_nhds_zero hW)).ball 0 1 ⊆ W :=
  fun x hx ↦ setOfPred_gauge_lt_one_subset_self hc (mem_of_mem_nhds hW)
    (absorbent_nhds_zero hW) (by simpa [Seminorm.mem_ball_zero] using hx)
