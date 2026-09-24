/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib

/-!
# Exercises: CDIS statements Paul already proves on paper

Each statement below compiles with `sorry`. They are the short (S) items that the catalog
assigns to Paul: results he meets in MAT21-2, MAT31-91 or MAT31-3, now to be proved in Lean.
Build with `lake build Exercises`; this target is not part of `CdisLean` and is not audited.
Suggested order: 13, 10, 11, 63, 73, 26, 45, 70, 78, 83. Hints name useful Mathlib lemmas.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace CDIS.Exercises

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- id 13. Hint: `indepSet_iff_measure_inter_eq_mul` turns `IndepSet` into
`P (A ∩ B) = P A * P B`; use `measure_diff` or `prob_compl_eq_one_sub`. -/
theorem indepSet_compl_left {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : IndepSet A B P) : IndepSet Aᶜ B P := by
  sorry

/-- id 10 (total probability, countable partition). Hint: `measure_iUnion` on `A ∩ B i`,
then `cond_mul_eq_inter`. -/
theorem measure_eq_tsum_cond_mul {ι : Type*} [Countable ι] {B : ι → Set Ω}
    (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Function.onFun Disjoint B))
    (hcover : ⋃ i, B i = univ)
    {A : Set Ω} (hA : MeasurableSet A) :
    P A = ∑' i, P[A | B i] * P (B i) := by
  sorry

/-- id 11 (Bayes, countable partition). Hint: `cond_apply`, then id 10 for the denominator. -/
theorem cond_eq_div_tsum {ι : Type*} [Countable ι] {B : ι → Set Ω}
    (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Function.onFun Disjoint B))
    (hcover : ⋃ i, B i = univ)
    {A : Set Ω} (hA : MeasurableSet A) (hPA : P A ≠ 0) (i : ι) :
    P[B i | A] = P[A | B i] * P (B i) / ∑' j, P[A | B j] * P (B j) := by
  sorry

/-- id 63 (Bienaymé-Chebyshev, with the missing hypothesis `a > 0`). Hint:
`meas_ge_le_variance_div_sq`, and `{a < |·|} ⊆ {a ≤ |·|}`. -/
theorem chebyshev {X : Ω → ℝ} (hX : MemLp X 2 P) {a : ℝ} (ha : 0 < a) :
    P.real {ω | a < |X ω - ∫ ω', X ω' ∂P|} ≤ Var[X; P] / a ^ 2 := by
  sorry

/-- id 73 (law of large numbers, L² rate). Hint: the expectation is `Var[M_n] = σ² / n`;
use `IndepFun.variance_sum` and `variance_const_mul`. -/
theorem tendsto_integral_sq_mean_sub {X : ℕ → Ω → ℝ} (h2 : ∀ i, MemLp (X i) 2 P)
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ((∑ i ∈ Finset.range n, X i ω) / n - ∫ ω', X 0 ω' ∂P) ^ 2 ∂P)
      atTop (𝓝 0) := by
  sorry

/-- id 26 (a density defines a probability whose distribution function is `∫_{-∞}^x f`).
Hint: `withDensity_apply` on `univ` and `ofReal_integral_eq_lintegral_ofReal`, then
`cdf_eq_real` and `withDensity_apply` on `Iic x`. -/
theorem density_isProbability_and_cdf {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hint : Integrable f) (h1 : ∫ x, f x = 1) :
    IsProbabilityMeasure (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) ∧
      ∀ x, cdf (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) x = ∫ y in Iic x, f y := by
  sorry

/-- id 45 (method of the dummy function). Hint: take `h = 1_B` for a Borel set `B`, then
`Measure.ext`. -/
theorem map_eq_withDensity_of_forall_integral {X : Ω → ℝ} (hX : Measurable X) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (h : ∀ g : ℝ → ℝ, Measurable g → Integrable (fun x ↦ g x * f x) →
      ∫ ω, g (X ω) ∂P = ∫ x, g x * f x) :
    P.map X = volume.withDensity fun x ↦ ENNReal.ofReal (f x) := by
  sorry

/-- id 70 (bounded case: convergence in probability iff in `L¹`). Hint:
`tendstoInMeasure_of_tendsto_eLpNorm` for one direction, `tendsto_Lp_finite_of_tendstoInMeasure`
with a uniform integrability bound for the other. -/
theorem tendstoInMeasure_iff_tendsto_eLpNorm_of_bdd {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {a : ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) P) (hY : AEStronglyMeasurable Y P)
    (hbdd : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ a) (hYbdd : ∀ᵐ ω ∂P, |Y ω| ≤ a) :
    TendstoInMeasure P X atTop Y ↔ Tendsto (fun n ↦ eLpNorm (X n - Y) 1 P) atTop (𝓝 0) := by
  sorry

/-- id 78 (convergence in law and intervals, when the limit has a density). Hint: the
frontier of `]a, b]` is `{a, b}`, which has measure zero for a law `≪ volume`; use the
portmanteau lemma `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`. -/
theorem tendsto_measure_Ioc_of_tendstoInDistribution {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Y (fun _ ↦ P) P') (hY : P'.map Y ≪ volume) {a b : ℝ} :
    Tendsto (fun n ↦ (P.map (X n)) (Ioc a b)) atTop (𝓝 ((P'.map Y) (Ioc a b))) := by
  sorry

/-- id 83 (characteristic function of an affine image). Hint: `charFun_apply`,
`integral_map`, and `ContinuousLinearMap.adjoint_inner_left`. -/
theorem charFun_map_affine {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (L : E →L[ℝ] F) (c : F) (u : F) :
    charFun (μ.map fun x ↦ c + L x) u =
      Complex.exp (⟪u, c⟫ * Complex.I) * charFun μ (ContinuousLinearMap.adjoint L u) := by
  sorry

end CDIS.Exercises
