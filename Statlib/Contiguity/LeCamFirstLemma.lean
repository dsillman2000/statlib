/-
Copyright (c) 2026 David Sillman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sillman
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Continuity
public import Statlib.Contiguity.Def
public import Statlib.ForMathlib.ENNReal

/-!
# Le Cam's first lemma: `Contiguous1 → Contiguous2`

Contrapositive proof assembled from the portmanteau, likelihood-ratio and quantile lemmas.

The supporting lemmas below are stated here because they are used only by this proof;
`le_of_le_add_one_div` lives in `Statlib.ForMathlib.ENNReal`.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open ENNReal Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

-- ============================================================
-- Likelihood-ratio facts
-- ============================================================

/-- The pushforward of `Q` under the Radon–Nikodym derivative `f = P.rnDeriv Q`
gives `Q {f < ε}` for the open down-set `Iio ε`. -/
lemma pushforward_rnDeriv_apply_Iio {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ProbabilityMeasure Ω) (ε : ℝ≥0∞) :
    (Q.map (fun x => (P : Measure Ω).rnDeriv (Q : Measure Ω) x)) (Iio ε) =
      Q {x | (P : Measure Ω).rnDeriv (Q : Measure Ω) x < ε} :=
  ProbabilityMeasure.map_apply Q
    ((Measure.measurable_rnDeriv (P : Measure Ω) (Q : Measure Ω)).aemeasurable)
    (measurableSet_Iio (a := ε))

/-- Neyman–Pearson set, sharp form: for any threshold `c` there is a measurable set `s` with
`μ s ≤ c * ν s` which has the same `ν`-mass as the likelihood-ratio level set
`{dμ/dν ≤ c}`. Only the Lebesgue decomposition of `μ` with respect to `ν` is needed. -/
lemma exists_neymanPearson_set_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [μ.HaveLebesgueDecomposition ν] (c : ℝ≥0∞) :
    ∃ s : Set Ω, MeasurableSet s ∧
      μ s ≤ c * ν s ∧
      ν s = ν {x | μ.rnDeriv ν x ≤ c} := by
  have hms := μ.mutuallySingular_singularPart ν
  set t := {x | μ.rnDeriv ν x ≤ c} ∩ hms.nullSet
  have ht : MeasurableSet t :=
    (measurableSet_le (μ.measurable_rnDeriv ν) measurable_const).inter hms.measurableSet_nullSet
  refine ⟨t, ht, ?_, measure_inter_conull hms.measure_compl_nullSet⟩
  -- On `hms.nullSet` the singular part vanishes, so `μ t = ∫⁻ x in t, dμ/dν x ∂ν`.
  calc μ t = μ.singularPart ν t + ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
        conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
        rw [Measure.add_apply, withDensity_apply _ ht]
    _ = ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
        rw [measure_mono_null inter_subset_right hms.measure_nullSet, zero_add]
    _ ≤ ∫⁻ _ in t, c ∂ν := setLIntegral_mono measurable_const fun _ hx => hx.1
    _ = c * ν t := setLIntegral_const _ _

/-- General version for measures: under `[IsProbabilityMeasure ν]` the sharp bound
`μ s ≤ c * ν s` becomes `μ s ≤ c`. -/
lemma exists_neymanPearson_set {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [μ.HaveLebesgueDecomposition ν] [IsProbabilityMeasure ν]
    (c : ℝ≥0∞) :
    ∃ s : Set Ω, MeasurableSet s ∧
      μ s ≤ c ∧
      ν s = ν {x | μ.rnDeriv ν x ≤ c} := by
  obtain ⟨s, hs, hμ, hν⟩ := exists_neymanPearson_set_mul μ ν c
  exact ⟨s, hs, hμ.trans (mul_le_of_le_one_right' prob_le_one), hν⟩

-- ============================================================
-- Portmanteau lower bound
-- ============================================================

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

-- ============================================================
-- Quantile threshold
-- ============================================================

/-- Continuity from above at a quantile threshold.

If `η < ν {f < c + 1/(n+1)}` for every `n`, then `η ≤ ν {f ≤ c}`. -/
lemma le_measure_of_lt_thresholds {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ≥0∞) (η c : ℝ≥0∞)
    (hf : Measurable f)
    (h : ∀ n : ℕ, η < ν {x | f x < c + 1 / (n + 1 : ℝ≥0∞)}) :
    η ≤ ν {x | f x ≤ c} := by
  -- the decreasing sequence of level sets `A n = {f ≤ c + 1/(n+1)}`
  let A : ℕ → Set Ω := fun n => {x | f x ≤ c + 1 / (n + 1 : ℝ≥0∞)}
  have hA_anti : Antitone A := fun m n hmn x (hx : f x ≤ _) => hx.trans (by gcongr)
  -- continuity from above: `ν (⋂ n, A n) = ⨅ n, ν (A n)`
  have hlim : ν (⋂ n, A n) = ⨅ n, ν (A n) :=
    hA_anti.measure_iInter (fun n => (measurableSet_le hf measurable_const).nullMeasurableSet)
      ⟨0, measure_ne_top ν _⟩
  -- `⋂ n, A n ⊆ {f ≤ c}`
  have hsubset : (⋂ n, A n) ⊆ {x | f x ≤ c} := fun x hx =>
    le_of_le_add_one_div (Set.mem_iInter.1 hx)
  calc η ≤ ν (⋂ n, A n) :=
        hlim ▸ le_iInf fun n => (h n).le.trans (measure_mono fun x (hx : f x < _) => hx.le)
    _ ≤ ν {x | f x ≤ c} := measure_mono hsubset

/-- The lower quantile `sInf {ε | η < ν {f < ε}}` is attained:
`η ≤ ν {f ≤ sInf {ε | η < ν {f < ε}}}`, as soon as the defining set is nonempty. -/
lemma le_measure_sInf {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ≥0∞) (η : ℝ≥0∞)
    (hf : Measurable f) (hne : ∃ ε, η < ν {x | f x < ε}) :
    η ≤ ν {x | f x ≤ sInf {ε | η < ν {x | f x < ε}}} := by
  set c := sInf {ε | η < ν {x | f x < ε}}
  obtain ⟨ε₀, hε₀⟩ := hne
  by_cases hc : c = ∞
  · -- the defining set is nonempty, so `η < ν {f < ε₀} ≤ ν {f ≤ ∞}`
    simpa [hc] using hε₀.le.trans (measure_mono (subset_univ _))
  refine le_measure_of_lt_thresholds ν f η c hf fun n => ?_
  obtain ⟨ε, hεη, hεlt⟩ := sInf_lt_iff.1 (ENNReal.lt_add_right hc (by simp) :
    c < c + 1 / (n + 1 : ℝ≥0∞))
  exact hεη.trans_le (measure_mono fun x (hx : f x < ε) => hx.trans hεlt)

-- ============================================================
-- Le Cam's first lemma
-- ============================================================

/-- `Contiguous1 → Contiguous2` (Le Cam's first lemma, contrapositive form). -/
theorem Contiguous1.contiguous2 {α : Type*} {Ω : α → Type*}
    [∀ a, MeasurableSpace (Ω a)] {l : Filter α}
    (P Q : ∀ a, ProbabilityMeasure (Ω a)) (hPQ : Contiguous1 l P Q) :
    Contiguous2 l P Q := by
  intro L h hle hne htend
  by_contra hL0
  -- η : ℝ≥0 with 0 < η < L {0}
  obtain ⟨η, hη0, hηL⟩ := exists_between (pos_iff_ne_zero.mpr hL0)
  -- Write `f a = dP a / dQ a`.
  set f : ∀ a, Ω a → ℝ≥0∞ := fun a => (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a))
  -- Lower bound transported to the `Q`-side: for every `ε > 0`, eventually `η < Q {f < ε}`.
  have hB : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ a in h,
      (η : ℝ≥0∞) < (Q a : Measure (Ω a)) {x | f a x < ε} := by
    intro ε hε
    filter_upwards [eventually_gt_measure_Iio_of_tendsto L _ htend (η : ℝ≥0∞)
      (ENNReal.coe_lt_coe.mpr hηL) ε hε] with a ha
    rwa [pushforward_rnDeriv_apply_Iio, ennreal_coeFn_eq_coeFn_toMeasure] at ha
  -- Quantile `c a` of the likelihood ratio at level `η`
  let c : α → ℝ≥0∞ := fun a => sInf {ε | (η : ℝ≥0∞) < (Q a : Measure (Ω a)) {x | f a x < ε}}
  -- `c a → 0` along `h`
  have hc_tend : Tendsto c h (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [hB ε hε] with a ha
    exact sInf_le ha
  -- Continuity from above: `η ≤ Q a {f a ≤ c a}`, eventually
  have hD : ∀ᶠ a in h, (η : ℝ≥0∞) ≤ (Q a : Measure (Ω a)) {x | f a x ≤ c a} := by
    filter_upwards [hB 1 one_pos] with a ha1
    exact le_measure_sInf (Q a : Measure (Ω a)) (f a) (η : ℝ≥0∞)
      (Measure.measurable_rnDeriv _ _) ⟨1, ha1⟩
  -- Neyman–Pearson sets `s a`: `P a (s a) ≤ c a` and `Q a (s a) = Q a {f a ≤ c a}`
  choose s hs_meas hs_P hs_Q using fun a =>
    exists_neymanPearson_set (P a : Measure (Ω a)) (Q a) (c a)
  -- `c a → 0` ⇒ `P a (s a) → 0` (in `ℝ≥0`)
  have hP_tend : Tendsto (fun a => (P a) (s a)) h (𝓝 0) := by
    rw [← ENNReal.tendsto_coe, ENNReal.coe_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc_tend
      (Eventually.of_forall (fun _ => (bot_le : (0 : ℝ≥0∞) ≤ _))) ?_
    exact Eventually.of_forall fun a => by
      rw [ennreal_coeFn_eq_coeFn_toMeasure]
      exact hs_P a
  -- `Contiguous1` (with the same `h ≤ l`) gives `Q a (s a) → 0` ...
  have hQ_tend := hPQ (s := s) (h := h) hs_meas hle hP_tend
  rw [← ENNReal.tendsto_coe, ENNReal.coe_zero] at hQ_tend
  -- ... but `Q a (s a) ≥ η > 0` eventually, which is incompatible with convergence to `0`.
  obtain ⟨a, ha_lt, ha_le⟩ :=
    ((hQ_tend.eventually (Iio_mem_nhds (ENNReal.coe_pos.mpr hη0))).and hD).exists
  rw [ennreal_coeFn_eq_coeFn_toMeasure, hs_Q] at ha_lt
  exact ha_le.not_gt ha_lt

end Statlib.Contiguity
