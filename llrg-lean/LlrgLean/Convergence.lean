/-
Proposition `convergence_rate`. Under (C1) the accepted correction covers in expectation at least
a fraction `1 − ε₀` of the residual cells, and under (C2) it introduces at most `ε₀ w_t` false
positives; then `E[w_{t+1}] ≤ 2ε₀ E[w_t]`, `E[w_t] ≤ (2ε₀)^t w_0`, `P(w_t ≠ 0) ≤ (2ε₀)^t w_0`
(Markov), and the expected number of iterations with a non-zero residual is at most
`⌈log M / log(1/(2ε₀))⌉ + 1/(1 − 2ε₀)` for `w_0 ≤ M` (`M = m · 2^n`).
-/
import Mathlib

open MeasureTheory Finset

namespace Llrg

/-- One step, in expectation: `w' = w − covered + falsePos`, `E[covered] ≥ (1−ε₀) w`,
`E[falsePos] ≤ ε₀ w` ⇒ `E[w'] ≤ 2ε₀ w`. -/
theorem one_step (w Ecov Efp ε₀ : ℝ) (hC1 : (1 - ε₀) * w ≤ Ecov) (hC2 : Efp ≤ ε₀ * w) :
    w - Ecov + Efp ≤ 2 * ε₀ * w := by nlinarith

/-- Iterating the contraction. -/
theorem iterate_contraction (e : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r) (h : ∀ t, e (t + 1) ≤ r * e t) :
    ∀ t, e t ≤ r ^ t * e 0
  | 0 => by simp
  | t + 1 => by
    have := iterate_contraction e r hr h t
    calc e (t + 1) ≤ r * e t := h t
      _ ≤ r * (r ^ t * e 0) := mul_le_mul_of_nonneg_left this hr
      _ = r ^ (t + 1) * e 0 := by ring

/-- Tail sum: if `p_t ≤ min(1, r^t M)` with `0 ≤ r < 1`, `1 ≤ M`, then every partial sum of `p` is
at most `⌈log M / log(1/r)⌉ + 1/(1 − r)`. -/
theorem tail_sum (p : ℕ → ℝ) (r M : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hM : 1 ≤ M)
    (hp1 : ∀ t, p t ≤ 1) (hpr : ∀ t, p t ≤ r ^ t * M) (N : ℕ) :
    ∑ t ∈ range N, p t ≤ ⌈Real.log M / Real.log (1 / r)⌉₊ + 1 / (1 - r) := by
  set T₀ := ⌈Real.log M / Real.log (1 / r)⌉₊
  have hlog : 0 < Real.log (1 / r) := Real.log_pos (by rw [one_div]; exact one_lt_inv₀ hr0 |>.mpr hr1)
  -- `r^{T₀} M ≤ 1`
  have hT : r ^ T₀ * M ≤ 1 := by
    have h1 : Real.log M ≤ T₀ * Real.log (1 / r) := by
      have := Nat.le_ceil (Real.log M / Real.log (1 / r))
      rwa [div_le_iff₀ hlog] at this
    have h2 : Real.log (r ^ T₀ * M) ≤ 0 := by
      rw [Real.log_mul (by positivity) (by linarith), Real.log_pow, one_div, Real.log_inv] at *
      linarith
    have hpos : 0 < r ^ T₀ * M := by positivity
    have := Real.exp_le_exp.mpr h2
    rwa [Real.exp_log hpos, Real.exp_zero] at this
  have hsplit : ∀ t, p t ≤ (if t < T₀ then 1 else r ^ (t - T₀)) := by
    intro t; split_ifs with ht
    · exact hp1 t
    · calc p t ≤ r ^ t * M := hpr t
        _ = r ^ (t - T₀) * (r ^ T₀ * M) := by rw [← mul_assoc, ← pow_add]; congr 2; omega
        _ ≤ r ^ (t - T₀) * 1 := mul_le_mul_of_nonneg_left hT (by positivity)
        _ = r ^ (t - T₀) := mul_one _
  calc ∑ t ∈ range N, p t ≤ ∑ t ∈ range N, (if t < T₀ then (1 : ℝ) else r ^ (t - T₀)) :=
        sum_le_sum (fun t _ => hsplit t)
    _ ≤ ∑ t ∈ range (N + T₀), (if t < T₀ then (1 : ℝ) else r ^ (t - T₀)) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          (fun t _ _ => by split_ifs <;> positivity)
    _ = T₀ + ∑ t ∈ range N, r ^ t := by
        rw [show N + T₀ = T₀ + N by omega, sum_range_add]
        congr 1
        · rw [sum_congr rfl (fun t ht => if_pos (mem_range.mp ht))]; simp
        · refine sum_congr rfl (fun t _ => ?_); rw [if_neg (by omega)]; congr 1; omega
    _ ≤ T₀ + 1 / (1 - r) := by
        have hg : ∑ t ∈ range N, r ^ t = (1 - r ^ N) / (1 - r) := by
          rw [geom_sum_eq hr1.ne, ← neg_div_neg_eq]; ring_nf
        rw [hg]
        have h1r : 0 < 1 - r := by linarith
        have : (1 - r ^ N) / (1 - r) ≤ 1 / (1 - r) :=
          div_le_div_of_nonneg_right (by have := pow_nonneg hr0.le N; linarith) h1r.le
        linarith


section Prob
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Markov for a natural-valued residual weight: `P(w ≠ 0) ≤ E[w]`. -/
theorem prob_ne_zero_le (w : Ω → ℕ) (hw : Measurable w) (hint : Integrable (fun ω => (w ω : ℝ)) μ) :
    μ.real {ω | w ω ≠ 0} ≤ ∫ ω, (w ω : ℝ) ∂μ := by
  have hmeas : MeasurableSet {ω | w ω ≠ 0} := (measurableSet_singleton 0).compl.preimage hw
  have hind : ∀ ω, ({ω | w ω ≠ 0} : Set Ω).indicator (1 : Ω → ℝ) ω ≤ (w ω : ℝ) := by
    intro ω; by_cases h : w ω = 0
    · rw [Set.indicator_of_notMem (by simpa using h)]; positivity
    · rw [Set.indicator_of_mem (by simpa using h), Pi.one_apply]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
  calc μ.real {ω | w ω ≠ 0} = ∫ ω, ({ω | w ω ≠ 0} : Set Ω).indicator (1 : Ω → ℝ) ω ∂μ := by
        rw [integral_indicator_one hmeas]
    _ ≤ ∫ ω, (w ω : ℝ) ∂μ :=
        integral_mono ((integrable_const (1 : ℝ)).indicator hmeas) hint hind

/-- Proposition `convergence_rate`: if the residual weights `w_t` (natural-valued, integrable,
`w_0 ≤ M = m · 2^n`) satisfy `E[w_{t+1}] ≤ 2ε₀ E[w_t]` with `0 < 2ε₀ < 1` (consequence of (C1)–(C2),
`one_step`), then the expected number of iterations with a non-zero residual, over any horizon `N`,
is at most `⌈log M / log(1/(2ε₀))⌉ + 1/(1 − 2ε₀)`. -/
theorem expected_iterations (w : ℕ → Ω → ℕ) (hw : ∀ t, Measurable (w t))
    (hint : ∀ t, Integrable (fun ω => (w t ω : ℝ)) μ) (ε₀ M : ℝ) (hε0 : 0 < ε₀) (hε1 : 2 * ε₀ < 1)
    (hM : 1 ≤ M) (h0 : ∀ ω, (w 0 ω : ℝ) ≤ M)
    (hstep : ∀ t, ∫ ω, (w (t + 1) ω : ℝ) ∂μ ≤ 2 * ε₀ * ∫ ω, (w t ω : ℝ) ∂μ) (N : ℕ) :
    ∑ t ∈ range N, μ.real {ω | w t ω ≠ 0}
      ≤ ⌈Real.log M / Real.log (1 / (2 * ε₀))⌉₊ + 1 / (1 - 2 * ε₀) := by
  have he := iterate_contraction (fun t => ∫ ω, (w t ω : ℝ) ∂μ) (2 * ε₀) (by linarith) hstep
  have hE0 : ∫ ω, (w 0 ω : ℝ) ∂μ ≤ M := by
    calc ∫ ω, (w 0 ω : ℝ) ∂μ ≤ ∫ _ω, M ∂μ := integral_mono (hint 0) (integrable_const M) h0
      _ = M := by simp
  refine tail_sum _ (2 * ε₀) M (by linarith) hε1 hM (fun t => ?_) (fun t => ?_) N
  · exact measureReal_le_one
  · calc μ.real {ω | w t ω ≠ 0} ≤ ∫ ω, (w t ω : ℝ) ∂μ := prob_ne_zero_le μ (w t) (hw t) (hint t)
      _ ≤ (2 * ε₀) ^ t * ∫ ω, (w 0 ω : ℝ) ∂μ := he t
      _ ≤ (2 * ε₀) ^ t * M := mul_le_mul_of_nonneg_left hE0 (by positivity)

end Prob

end Llrg
