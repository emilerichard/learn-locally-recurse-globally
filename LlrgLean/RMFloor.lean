/-
Remark `rm_floor`, part (iii) (App., proof of Remark `rm_floor`): for a uniform `R₀`, with
probability at least `1 - δ` every pre-completion residual satisfies
`w_T / 2^n ≥ 1/2 - sqrt((K ln 2 + ln(1/δ)) / 2^(n+1))`, `K = Σ_{i ≤ k} C(n, i)`, and the deviation
term tends to `0` as `n → ∞` for fixed `k`. Probabilities over the uniform `R₀` are stated as
counts over all `2^(2^n)` functions `R₀`.
-/
import LlrgLean.JuntaFloor

open Finset Real Filter Topology

namespace Llrg

variable {n : ℕ}

/-- Indicator of a nonzero value. -/
def nz (b : ZMod 2) : ℝ := if b ≠ 0 then 1 else 0

lemma wt_eq_sum (g : (Fin n → Bool) → ZMod 2) : (wt g : ℝ) = ∑ x, nz (g x) := by
  unfold wt nz; rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]

/-- Exponential moment: `Σ_g e^{-λ wt g} = (1 + e^{-λ})^{2^n}`. -/
lemma sum_exp_wt (l : ℝ) :
    ∑ g : (Fin n → Bool) → ZMod 2, exp (-l * wt g) = (1 + exp (-l)) ^ (2 ^ n) := by
  have h1 : ∀ g : (Fin n → Bool) → ZMod 2, exp (-l * wt g) = ∏ x, exp (-l * nz (g x)) := by
    intro g; rw [wt_eq_sum, mul_sum, exp_sum]
  simp_rw [h1]
  have h2 : ∀ x : Fin n → Bool, ∑ b : ZMod 2, exp (-l * nz b) = 1 + exp (-l) := by
    intro x
    have e0 : nz 0 = 0 := by unfold nz; rw [if_neg (by decide)]
    have e1 : nz 1 = 1 := by unfold nz; rw [if_pos (by decide)]
    change ∑ b : Fin 2, exp (-l * nz b) = _
    rw [Fin.sum_univ_two]
    change exp (-l * nz 0) + exp (-l * nz 1) = _
    rw [e0, e1]; simp
  have h3 : ∏ _x : Fin n → Bool, ∑ b : ZMod 2, exp (-l * nz b) = (1 + exp (-l)) ^ (2 ^ n) := by
    rw [prod_congr rfl (fun x _ => h2 x), prod_const, card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  rw [← h3, Fintype.prod_sum]

/-- Hoeffding/Chernoff bound for `Bin(2^n, 1/2)`, as a count: at most `2^(2^n) e^{-2t²/2^n}`
functions `g` have `wt g ≤ 2^(n-1) - t`. -/
theorem tail (t : ℝ) (ht : 0 ≤ t) :
    ((univ.filter (fun g : (Fin n → Bool) → ZMod 2 => (wt g : ℝ) ≤ 2 ^ n / 2 - t)).card : ℝ)
      ≤ 2 ^ (2 ^ n) * exp (-2 * t ^ 2 / 2 ^ n) := by
  set M : ℝ := 2 ^ n with hM
  have hM0 : 0 < M := by positivity
  set l : ℝ := 4 * t / M with hl
  have hl0 : 0 ≤ l := by positivity
  -- each counted `g` contributes at most `exp (l (M/2 - t - wt g))`
  have h1 : ((univ.filter (fun g : (Fin n → Bool) → ZMod 2 => (wt g : ℝ) ≤ M / 2 - t)).card : ℝ)
      ≤ ∑ g : (Fin n → Bool) → ZMod 2, exp (l * (M / 2 - t)) * exp (-l * wt g) := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_le_sum (fun g _ => ?_)
    split_ifs with h
    · rw [← exp_add, Nat.cast_one]; apply one_le_exp; nlinarith
    · positivity
  rw [← mul_sum, sum_exp_wt] at h1
  refine h1.trans ?_
  -- `e^{l(M/2 - t)} (1 + e^{-l})^M = e^{-lt} (2 cosh (l/2))^M ≤ 2^M e^{-lt + M l²/8}`
  have hc : exp (l / 2) * (1 + exp (-l)) = 2 * cosh (l / 2) := by
    rw [cosh_eq, mul_add, mul_one, ← exp_add]; ring_nf
  have hcosh := cosh_le_exp_half_sq (l / 2)
  have hpow : (1 + exp (-l)) ^ (2 ^ n) * exp (l * (M / 2))
      = (2 * cosh (l / 2)) ^ (2 ^ n) := by
    rw [← hc, mul_pow, ← exp_nat_mul]; push_cast; rw [← hM, mul_comm]; congr 2; ring
  calc exp (l * (M / 2 - t)) * (1 + exp (-l)) ^ (2 ^ n)
      = exp (-(l * t)) * (2 * cosh (l / 2)) ^ (2 ^ n) := by
        rw [← hpow, mul_sub, sub_eq_add_neg, exp_add]; ring
    _ ≤ exp (-(l * t)) * (2 * exp ((l / 2) ^ 2 / 2)) ^ (2 ^ n) := by
        gcongr
    _ = 2 ^ (2 ^ n) * exp (-(l * t) + M * ((l / 2) ^ 2 / 2)) := by
        rw [mul_pow, ← exp_nat_mul, exp_add]; push_cast; rw [← hM]; ring
    _ = 2 ^ (2 ^ n) * exp (-2 * t ^ 2 / M) := by
        congr 2; rw [hl]; field_simp; ring

/-! ### Size of `RM(k, n)` -/

/-- `K = Σ_{i ≤ k} C(n, i)`, the dimension of `RM(k, n)`. -/
def K (n k : ℕ) : ℕ := ∑ i ∈ range (k + 1), n.choose i

open Classical in
/-- `RM(k, n)` as a finset. -/
noncomputable def rmSet (k : ℕ) : Finset ((Fin n → Bool) → ZMod 2) := univ.filter (· ∈ RM k)

lemma card_small (k : ℕ) :
    (univ.filter (fun U : Finset (Fin n) => U.card ≤ k)).card = K n k := by
  unfold K
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range (k + 1))]
  · refine sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have : (univ.filter (fun U : Finset (Fin n) => U.card ≤ k)).filter (fun U => U.card = i)
        = powersetCard i univ := by
      ext U; simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]; omega
    rw [this, card_powersetCard, card_univ, Fintype.card_fin]
  · intro U hU; exact mem_range.mpr (by simp at hU; omega)

open Classical in
theorem card_RM (k : ℕ) : (rmSet (n := n) k).card = 2 ^ K n k := by
  let t : Finset (Fin n) → Finset (ZMod 2) := fun U => if U.card ≤ k then univ else {0}
  have hA : (Fintype.piFinset t).card = 2 ^ K n k := by
    rw [Fintype.card_piFinset]
    have : ∀ U : Finset (Fin n), (t U).card = if U.card ≤ k then 2 else 1 := by
      intro U
      change (if U.card ≤ k then (univ : Finset (ZMod 2)) else {0}).card = _
      split_ifs <;> simp [ZMod.card]
    simp_rw [this]
    rw [prod_ite, prod_const_one, mul_one, prod_const, card_small]
  rw [← hA]
  refine card_bij (fun f _ => rmCoef f) (fun f hf => ?_) (fun f _ g _ h => ?_) (fun a ha => ?_)
  · have hf : ∀ U : Finset (Fin n), k < U.card → rmCoef f U = 0 := by
      simp only [rmSet, mem_filter, mem_univ, true_and] at hf; exact hf
    rw [Fintype.mem_piFinset]; intro U
    by_cases hU : U.card ≤ k
    · simp [t, hU]
    · simp [t, hU, hf U (by omega)]
  · have := congrArg rmEval h; rwa [rmEval_rmCoef, rmEval_rmCoef] at this
  · refine ⟨rmEval a, ?_, rmCoef_rmEval a⟩
    simp only [rmSet, mem_filter, mem_univ, true_and]
    show ∀ U : Finset (Fin n), k < U.card → rmCoef (rmEval a) U = 0
    intro U hU; rw [rmCoef_rmEval]
    have := (Fintype.mem_piFinset.mp ha) U
    simp [t, show ¬ U.card ≤ k by omega] at this; exact this

/-! ### Union bound -/

open Classical in
/-- Count of the `R₀` within distance `2^(n-1) - t` of `RM(k, n)`. -/
theorem union_bound (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((univ.filter (fun R₀ : (Fin n → Bool) → ZMod 2 =>
        ∃ c ∈ RM k, (wt (R₀ + c) : ℝ) ≤ 2 ^ n / 2 - t)).card : ℝ)
      ≤ 2 ^ K n k * (2 ^ (2 ^ n) * exp (-2 * t ^ 2 / 2 ^ n)) := by
  set T := univ.filter (fun g : (Fin n → Bool) → ZMod 2 => (wt g : ℝ) ≤ 2 ^ n / 2 - t)
  have hsub : univ.filter (fun R₀ : (Fin n → Bool) → ZMod 2 =>
        ∃ c ∈ RM k, (wt (R₀ + c) : ℝ) ≤ 2 ^ n / 2 - t)
      ⊆ (rmSet k).biUnion (fun c => univ.filter (fun R₀ => (wt (R₀ + c) : ℝ) ≤ 2 ^ n / 2 - t)) := by
    intro R₀ h
    simp only [mem_filter, mem_univ, true_and] at h
    obtain ⟨c, hc, h⟩ := h
    simp only [mem_biUnion, rmSet, mem_filter, mem_univ, true_and]; exact ⟨c, hc, h⟩
  have hc : ∀ c, (univ.filter (fun R₀ : (Fin n → Bool) → ZMod 2 =>
      (wt (R₀ + c) : ℝ) ≤ 2 ^ n / 2 - t)).card ≤ T.card := by
    intro c
    refine card_le_card_of_injOn (fun R₀ => R₀ + c) (fun R₀ h => ?_) (fun a _ b _ h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h
      simp [T, h]
    · exact add_right_cancel h
  calc _ ≤ (((rmSet k).biUnion (fun c => univ.filter (fun R₀ : (Fin n → Bool) → ZMod 2 =>
            (wt (R₀ + c) : ℝ) ≤ 2 ^ n / 2 - t))).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ((rmSet k).card * T.card : ℕ) := by
        exact_mod_cast card_biUnion_le.trans (sum_le_card_nsmul _ _ _ (fun c _ => hc c))
    _ ≤ 2 ^ K n k * (2 ^ (2 ^ n) * exp (-2 * t ^ 2 / 2 ^ n)) := by
        push_cast; rw [card_RM]; push_cast
        exact mul_le_mul_of_nonneg_left (tail t ht) (by positivity)

/-! ### The `1 - δ` floor -/

/-- The deviation term `sqrt((K ln 2 + ln(1/δ)) / 2^(n+1))`. -/
noncomputable def eps (n k : ℕ) (δ : ℝ) : ℝ :=
  Real.sqrt ((K n k * Real.log 2 + Real.log (1 / δ)) / 2 ^ (n + 1))

open Classical in
/-- Remark `rm_floor` (iii): for all but a `δ` fraction of targets `R₀`, every pre-completion
residual `R₀ + Σ cs` of the projection loop (any list of `k`-junta corrections, i.e. any selector
and step budget) has `w_T / 2^n > 1/2 - sqrt((K ln 2 + ln(1/δ)) / 2^(n+1))`. -/
theorem rm_floor_whp (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((univ.filter (fun R₀ : (Fin n → Bool) → ZMod 2 =>
        ∃ cs : List ((Fin n → Bool) → ZMod 2),
          (∀ c ∈ cs, ∃ S : Finset (Fin n), S.card ≤ k ∧ IsJuntaOn S c) ∧
          (wt (R₀ + cs.sum) : ℝ) / 2 ^ n ≤ 1 / 2 - eps n k δ)).card : ℝ)
      ≤ δ * 2 ^ (2 ^ n) := by
  have hA : 0 ≤ (K n k : ℝ) * Real.log 2 + Real.log (1 / δ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 / δ by rw [le_div_iff₀ hδ]; linarith)
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  set t := 2 ^ n * eps n k δ with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hsub : univ.filter (fun R₀ : (Fin n → Bool) → ZMod 2 =>
        ∃ cs : List ((Fin n → Bool) → ZMod 2),
          (∀ c ∈ cs, ∃ S : Finset (Fin n), S.card ≤ k ∧ IsJuntaOn S c) ∧
          (wt (R₀ + cs.sum) : ℝ) / 2 ^ n ≤ 1 / 2 - eps n k δ)
      ⊆ univ.filter (fun R₀ : (Fin n → Bool) → ZMod 2 =>
        ∃ c ∈ RM k, (wt (R₀ + c) : ℝ) ≤ 2 ^ n / 2 - t) := by
    intro R₀ h
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    obtain ⟨cs, hcs, hw⟩ := h
    obtain ⟨⟨c, hc, he⟩, -⟩ := residual_floor k R₀ cs hcs
    refine ⟨c, hc, ?_⟩
    rw [← he]; rw [div_le_iff₀ h2n] at hw; rw [ht]; linarith
  refine (Nat.cast_le.mpr (card_le_card hsub)).trans ((union_bound k t ht0).trans (le_of_eq ?_))
  -- `2 t² / 2^n = K ln 2 + ln(1/δ)`
  have hsq : 2 * t ^ 2 / 2 ^ n = K n k * Real.log 2 + Real.log (1 / δ) := by
    rw [ht, mul_pow, eps, Real.sq_sqrt (by positivity), pow_succ]; field_simp; ring
  have he : exp (-(K n k * Real.log 2 + Real.log (1 / δ))) = δ / 2 ^ K n k := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log two_pos,
      Real.exp_log (by positivity)]
    field_simp
  rw [neg_mul, neg_div, hsq, he]; field_simp

/-! ### Asymptotics and the `(n, k) = (10, 5)` value -/

lemma K_le (n k : ℕ) (hn : 1 ≤ n) : (K n k : ℝ) ≤ (k + 1) * (n : ℝ) ^ k := by
  unfold K; push_cast
  calc ∑ i ∈ range (k + 1), (n.choose i : ℝ) ≤ ∑ _i ∈ range (k + 1), (n : ℝ) ^ k := by
        refine sum_le_sum (fun i hi => ?_)
        have hi : i ≤ k := by simp at hi; omega
        calc (n.choose i : ℝ) ≤ (n : ℝ) ^ i := by exact_mod_cast Nat.choose_le_pow n i
          _ ≤ (n : ℝ) ^ k := pow_le_pow_right₀ (by exact_mod_cast hn) hi
    _ = (k + 1) * (n : ℝ) ^ k := by simp

/-- For fixed `k` and `δ`, the deviation term tends to `0`, so the floor tends to `1/2`. -/
theorem eps_tendsto (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (fun n => eps n k δ) atTop (𝓝 0) := by
  have hc : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu : Tendsto (fun n : ℕ => ((k + 1) * Real.log 2 / 2) * ((n : ℝ) ^ k / 2 ^ n)
      + (Real.log (1 / δ) / 2) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt k (show (1 : ℝ) < 2 by norm_num)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    simpa using (h1.const_mul ((k + 1) * Real.log 2 / 2)).add (h2.const_mul (Real.log (1 / δ) / 2))
  have hsq : Tendsto (fun n => (K n k * Real.log 2 + Real.log (1 / δ)) / 2 ^ (n + 1))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall (fun n => by positivity)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hK := K_le n k hn
    rw [div_le_iff₀ (by positivity), pow_succ]
    have : ((k + 1) * Real.log 2 / 2 * ((n : ℝ) ^ k / 2 ^ n)
        + Real.log (1 / δ) / 2 * (1 / 2) ^ n) * (2 ^ n * 2)
        = (k + 1) * (n : ℝ) ^ k * Real.log 2 + Real.log (1 / δ) := by
      simp only [one_div_pow]; field_simp
    rw [this]; nlinarith
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at this; exact this

lemma K_10_5 : K 10 5 = 638 := by decide

/-- Tightness at `(n, k) = (10, 5)`, `δ = 0.01`: the guaranteed floor `1/2 - eps` lies in
`[0.03, 0.035]`. -/
theorem floor_10_5 : 0.03 ≤ 1 / 2 - eps 10 5 0.01 ∧ 1 / 2 - eps 10 5 0.01 ≤ 0.035 := by
  have hl1 := Real.log_two_lt_d9
  have hl2 := Real.log_two_gt_d9
  have h100 : Real.log (1 / 0.01) = Real.log 100 := by norm_num
  have hup : Real.log 100 < 7 * Real.log 2 := by
    have : Real.log ((2 : ℝ) ^ 7) = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]; exact Real.log_lt_log (by norm_num) (by norm_num)
  have hlo : 6 * Real.log 2 < Real.log 100 := by
    have : Real.log ((2 : ℝ) ^ 6) = 6 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]; exact Real.log_lt_log (by norm_num) (by norm_num)
  unfold eps; rw [K_10_5, h100]
  constructor
  · have : Real.sqrt ((638 * Real.log 2 + Real.log 100) / 2 ^ (10 + 1)) ≤ 0.47 := by
      rw [Real.sqrt_le_left (by norm_num)]; push_cast; norm_num; nlinarith
    push_cast at this ⊢; linarith
  · have : 0.465 ≤ Real.sqrt ((638 * Real.log 2 + Real.log 100) / 2 ^ (10 + 1)) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; push_cast; norm_num; nlinarith
    push_cast at this ⊢; linarith

end Llrg
