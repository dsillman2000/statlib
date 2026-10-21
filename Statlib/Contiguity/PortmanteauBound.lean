/-
Copyright (c) 2026 Statlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Portmanteau-type lower bounds for weak limits

If `μs → L` weakly and `η < L {0}`, then eventually `η < μs a (Iio ε)` for every `ε > 0`.

This is the open-set case of the portmanteau theorem: `Iio ε` is open and contains `{0}`, so
`L {0} ≤ L (Iio ε) ≤ liminfᵢ μsᵢ (Iio ε)`, and a strictly smaller threshold is therefore
eventually exceeded.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- Weak-limit lower bound on `μs a s` for an open set `s`: if `η < L s`, then eventually
`η < μs a s`.  This is the open-set case of the portmanteau theorem. -/
lemma eventually_gt_measure_open_of_tendsto {X α : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X] {h : Filter α}
    (L : ProbabilityMeasure X) (μs : α → ProbabilityMeasure X)
    (hμs : Tendsto μs h (𝓝 L)) (η : ℝ≥0∞) (s : Set X) (hs : IsOpen s)
    (hη : η < L s) :
    ∀ᶠ a in h, η < μs a s := by
  simp only [ennreal_coeFn_eq_coeFn_toMeasure] at hη ⊢
  -- Portmanteau, open sets: `L s ≤ liminf (μs a s)`.
  exact eventually_lt_of_lt_liminf (hη.trans_le (le_liminf_measure_open_of_tendsto hμs hs))

/-- Weak-limit lower bound on `μ (Iio ε)` for any threshold `ε > 0`. -/
lemma eventually_gt_measure_Iio_of_tendsto {α : Type*} {h : Filter α}
    (L : ProbabilityMeasure (ℝ≥0∞)) (μs : α → ProbabilityMeasure (ℝ≥0∞))
    (hμs : Tendsto μs h (𝓝 L)) (η : ℝ≥0∞) (hη : η < L {0})
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∀ᶠ a in h, η < μs a (Iio ε) :=
  -- `{0} ⊆ Iio ε`, hence `L {0} ≤ L (Iio ε)`.
  eventually_gt_measure_open_of_tendsto L μs hμs η (Iio ε) isOpen_Iio <|
    hη.trans_le (ENNReal.coe_le_coe.mpr (L.apply_mono (singleton_subset_iff.2 hε)))

end Statlib.Contiguity
