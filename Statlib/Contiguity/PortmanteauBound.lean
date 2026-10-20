/-
Copyright (c) 2026 Statlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Portmanteau-type lower bounds for weak limits

If `μs → L` weakly and `η < L {0}`, then eventually `η < μs a (Iio ε)` for every `ε > 0`.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- The truncated `1 - x/ε` has `toNNReal` at most `1`. -/
lemma toNNReal_one_sub_div_le_one (x ε : ℝ≥0∞) :
    ENNReal.toNNReal (1 - x / ε) ≤ 1 :=
  ENNReal.toNNReal_mono ENNReal.one_ne_top tsub_le_self

/-- Weak-limit lower bound on `μ (Iio ε)` for a finite threshold `ε ≠ ∞`. -/
lemma eventually_gt_measure_Iio_of_tendsto_ne_top {α : Type*} {h : Filter α}
    (L : ProbabilityMeasure (ℝ≥0∞)) (μs : α → ProbabilityMeasure (ℝ≥0∞))
    (hμs : Tendsto μs h (𝓝 L)) (η : ℝ≥0∞) (hη : η < L {0})
    (ε : ℝ≥0∞) (hε : 0 < ε) (hεfin : ε ≠ ∞) :
    ∀ᶠ a in h, η < μs a (Iio ε) := by
  -- finite ε > 0
    -- Build g_ε : ℝ≥0∞ →ᵇ ℝ≥0, g(x) = (1 - x/ε) (truncated at 0)
    let fenn : ℝ≥0∞ → ℝ≥0∞ := fun x => 1 - x / ε
    have hfenn_cont : Continuous fenn := by
      have hdiv : Continuous (fun x : ℝ≥0∞ => x / ε) :=
        ENNReal.continuous_div_const ε (ne_of_gt hε)
      have hsub : Continuous (fun y : ℝ≥0∞ => (1 : ℝ≥0∞) - y) :=
        @ENNReal.continuous_nnreal_sub (1 : ℝ≥0)
      exact hsub.comp hdiv
    have hfenn_finite : ∀ x, fenn x ≠ ∞ := by
      intro x
      have : fenn x ≤ 1 := tsub_le_self
      exact ne_of_lt (lt_of_le_of_lt this ENNReal.one_lt_top)
    let gfun : ℝ≥0∞ → ℝ≥0 := fun x => ENNReal.toNNReal (fenn x)
    have hg_cont : Continuous gfun := by
      exact ContinuousOn.comp_continuous ENNReal.continuousOn_toNNReal hfenn_cont hfenn_finite
    -- g as a BoundedContinuousFunction; values lie in [0, 1], so the bound is 1
    let cm : C(ℝ≥0∞, ℝ≥0) := ContinuousMap.mk gfun hg_cont
    have hg_bound : ∀ x y : ℝ≥0∞, dist (gfun x) (gfun y) ≤ 1 := by
      intro x y
      have hx := NNReal.coe_le_one.mpr (toNNReal_one_sub_div_le_one x ε)
      have hy := NNReal.coe_le_one.mpr (toNNReal_one_sub_div_le_one y ε)
      rw [NNReal.dist_eq, abs_le]
      constructor <;> linarith [NNReal.coe_nonneg (gfun x), NNReal.coe_nonneg (gfun y)]
    let g : BoundedContinuousFunction (ℝ≥0∞) ℝ≥0 :=
      BoundedContinuousFunction.mkOfBound cm 1 hg_bound
    -- pointwise inequalities
    have hg_ge_ind0 : ∀ x, Set.indicator ({0} : Set ℝ≥0∞) (fun _ => (1 : ℝ≥0)) x ≤ gfun x := by
      intro x
      by_cases hx : x = 0
      · subst hx
        simp [Set.indicator, gfun, fenn, ENNReal.toNNReal_one]
      · have hx' : x ∉ ({0} : Set ℝ≥0∞) := hx
        simp [Set.indicator_of_notMem hx']
    have hg_le_indIio : ∀ x, gfun x ≤ Set.indicator (Iio ε) (fun _ => (1 : ℝ≥0)) x := by
      intro x
      by_cases hx : x < ε
      · have hxmem : x ∈ Iio ε := hx
        have : gfun x ≤ 1 := toNNReal_one_sub_div_le_one x ε
        simpa [Set.indicator_of_mem hxmem] using this
      · have hxe : ¬ (x < ε) := hx
        have : ε ≤ x := le_of_not_gt hx
        have : fenn x = 0 := by
          apply tsub_eq_zero_of_le
          rw [ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hε)) (Or.inl hεfin)]
          simpa [one_mul] using (le_of_not_gt hx)
        simp [Set.indicator_of_notMem (show ¬ x ∈ Iio ε from hx), gfun, this, ENNReal.toNNReal_zero]
    -- lintegral inequalities
    have hL_le : L {0} ≤ ∫⁻ x, (gfun x : ℝ≥0∞) ∂(L : Measure ℝ≥0∞) := by
      have hpoint : ∀ x,
          Set.indicator ({0} : Set ℝ≥0∞) (fun _ => (1 : ℝ≥0∞)) x ≤ (gfun x : ℝ≥0∞) := by
        intro x
        have h := ENNReal.coe_le_coe.mpr (hg_ge_ind0 x)
        rwa [ENNReal.coe_indicator ({0}) (fun _ => (1 : ℝ≥0)) x] at h
      have hmono := lintegral_mono (μ := (L : Measure ℝ≥0∞)) (f := Set.indicator ({0})
        (fun _ => (1 : ℝ≥0∞))) (g := fun x => (gfun x : ℝ≥0∞)) hpoint
      have hind : ∫⁻ x, Set.indicator ({0}) (fun _ => (1 : ℝ≥0∞)) x ∂(L : Measure ℝ≥0∞) =
          L {0} := by
        rw [lintegral_indicator_const (measurableSet_singleton 0) (1 : ℝ≥0∞)]
        simp
      rwa [hind] at hmono
    have hμs_le : ∀ a, ∫⁻ x, (gfun x : ℝ≥0∞) ∂(μs a : Measure ℝ≥0∞) ≤ (μs a) (Iio ε) := by
      intro a
      have hpoint : ∀ x, (gfun x : ℝ≥0∞) ≤ Set.indicator (Iio ε) (fun _ => (1 : ℝ≥0∞)) x := by
        intro x
        have h := ENNReal.coe_le_coe.mpr (hg_le_indIio x)
        rwa [ENNReal.coe_indicator (Iio ε) (fun _ => (1 : ℝ≥0)) x] at h
      have hmono := lintegral_mono (μ := (μs a : Measure ℝ≥0∞))
        (f := fun x => (gfun x : ℝ≥0∞)) (g := Set.indicator (Iio ε) (fun _ => (1 : ℝ≥0∞)))
        hpoint
      have hind : ∫⁻ x, Set.indicator (Iio ε) (fun _ => (1 : ℝ≥0∞)) x ∂(μs a : Measure ℝ≥0∞) =
          (μs a) (Iio ε) := by
        rw [lintegral_indicator_const (measurableSet_Iio (a := ε)) (1 : ℝ≥0∞)]
        simp
      rwa [hind] at hmono
    -- tendsto of integrals
    have htend : Tendsto (fun a => ∫⁻ x, (gfun x : ℝ≥0∞) ∂(μs a : Measure ℝ≥0∞)) h
        (𝓝 (∫⁻ x, (gfun x : ℝ≥0∞) ∂(L : Measure ℝ≥0∞))) := by
      have : Tendsto μs h (𝓝 L) := hμs
      -- use tendsto_iff_forall_lintegral_tendsto with g
      rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto] at hμs
      exact hμs g
    -- combine: η < L{0} ≤ ∫g dL, and integral tends, so eventually η < ∫g dμs a ≤ μs a (Iio ε)
    have hη' : η < ∫⁻ x, (gfun x : ℝ≥0∞) ∂(L : Measure ℝ≥0∞) := lt_of_lt_of_le hη hL_le
    have hev : ∀ᶠ a in h, η < ∫⁻ x, (gfun x : ℝ≥0∞) ∂(μs a : Measure ℝ≥0∞) := by
      exact htend.eventually (Ioi_mem_nhds hη')
    filter_upwards [hev] with a ha
    exact lt_of_lt_of_le ha (hμs_le a)

/-- Weak-limit lower bound on `μ (Iio ε)` for any threshold `ε > 0`. -/
lemma eventually_gt_measure_Iio_of_tendsto {α : Type*} {h : Filter α}
    (L : ProbabilityMeasure (ℝ≥0∞)) (μs : α → ProbabilityMeasure (ℝ≥0∞))
    (hμs : Tendsto μs h (𝓝 L)) (η : ℝ≥0∞) (hη : η < L {0})
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∀ᶠ a in h, η < μs a (Iio ε) := by
  by_cases hεtop : ε = ∞
  · have hfin := eventually_gt_measure_Iio_of_tendsto_ne_top
      L μs hμs η hη 1 zero_lt_one ENNReal.one_ne_top
    filter_upwards [hfin] with a ha
    exact lt_of_lt_of_le ha (ENNReal.coe_le_coe.mpr (ProbabilityMeasure.apply_mono (μs a)
      (show Iio (1 : ℝ≥0∞) ⊆ Iio ε from fun x (hx : x < 1) => hεtop ▸ (lt_of_lt_of_le hx le_top))))
  · exact eventually_gt_measure_Iio_of_tendsto_ne_top L μs hμs η hη ε hε hεtop

end Statlib.Contiguity
