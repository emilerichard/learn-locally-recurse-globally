/-
Appendix (Dyck): Theorem `th:dyck_informal`, closed-form Dyck completion by one attention head.

Model. Tokens are `true = (` with embedding `+1` and `false = )` with `−1`. One causal attention
head with uniform attention reads, at prefix length `r`, the average of `E(z_i) + B_i` over
`i < r`; a scalar value `v` gives the logit `X_r = (v / r) Σ_{i<r} (E(z_i) + B_i)`, and the
unembedding `[X, −X]` gives `P(next = '(') = σ(2 X_r)`, `σ(t) = 1/(1 + e^{−t})`.
Positions are 0-indexed here: the paper's `B_1, B_i (2 ≤ i < 2N)` are `B 0, B i (1 ≤ i < 2N − 1)`.
-/
import Mathlib

open Finset Real

namespace Llrg.Dyck

noncomputable section

/-- Token embedding. -/
def E (b : Bool) : ℝ := if b then 1 else -1

/-- Logistic function. -/
def σ (t : ℝ) : ℝ := 1 / (1 + exp (-t))

/-- Running stack size after `r` tokens. -/
def Δ (z : ℕ → Bool) (r : ℕ) : ℝ := ∑ i ∈ range r, E (z i)

/-- The constructed positional embedding (paper: `B_1 = −E_{s_1} + γ E_{s_2}`,
`B_i = −(1+γ) E_{s_i} + γ E_{s_{i+1}}`). -/
def B (s : ℕ → Bool) (γ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then -E (s 0) + γ * E (s 1) else -(1 + γ) * E (s i) + γ * E (s (i + 1))

/-- Attention-weighted sum at prefix length `r`. -/
def S (s z : ℕ → Bool) (γ : ℝ) (r : ℕ) : ℝ := ∑ i ∈ range r, (E (z i) + B s γ i)

/-- Logit at prefix length `r`. -/
def X (s z : ℕ → Bool) (γ v : ℝ) (r : ℕ) : ℝ := v / r * S s z γ r

/-- Probability that the model emits token `b` after the prefix of length `r` of `z`. -/
def P (s z : ℕ → Bool) (γ v : ℝ) (r : ℕ) (b : Bool) : ℝ :=
  if b then σ (2 * X s z γ v r) else 1 - σ (2 * X s z γ v r)

/-- Telescoping (theorem, generalization bullet): for `r ≥ 1`,
`Σ_{i<r} (E(z_i) + B_i) = Δ_r(z) − Δ_r(s) + γ E(s_r)`. -/
theorem S_eq (s z : ℕ → Bool) (γ : ℝ) : ∀ r, 1 ≤ r →
    S s z γ r = Δ z r - Δ s r + γ * E (s r)
  | 0, h => by omega
  | 1, _ => by simp [S, Δ, B]; ring
  | r + 2, _ => by
    have ih := S_eq s z γ (r + 1) (by omega)
    unfold S Δ at ih ⊢
    rw [sum_range_succ, ih,
      show ∑ i ∈ range (r + 2), E (z i) = ∑ i ∈ range (r + 1), E (z i) + E (z (r + 1)) from
        sum_range_succ _ _,
      show ∑ i ∈ range (r + 2), E (s i) = ∑ i ∈ range (r + 1), E (s i) + E (s (r + 1)) from
        sum_range_succ _ _]
    simp only [B, show r + 1 ≠ 0 by omega, if_false]
    ring

/-! ### Logistic facts -/

lemma σ_neg (t : ℝ) : 1 - σ t = σ (-t) := by
  unfold σ
  have h1 : 0 < 1 + exp (-t) := by positivity
  have h2 : 0 < 1 + exp t := by positivity
  field_simp
  have : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
  nlinarith [this]

lemma σ_mono {a b : ℝ} (h : a ≤ b) : σ a ≤ σ b := by
  unfold σ
  apply one_div_le_one_div_of_le (by positivity)
  have : exp (-b) ≤ exp (-a) := exp_le_exp.mpr (by linarith)
  linarith

/-- `σ(t) ≥ 1 − e^{−t}`. -/
lemma σ_ge (t : ℝ) : 1 - exp (-t) ≤ σ t := by
  unfold σ
  have ha : 0 ≤ exp (-t) := (exp_pos _).le
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (exp (-t))]

/-- Probability of emitting `b` when the logit has the sign of `b`'s embedding. -/
lemma P_eq_σ (s z : ℕ → Bool) (γ v : ℝ) (r : ℕ) (b : Bool) :
    P s z γ v r b = σ (2 * E b * X s z γ v r) := by
  cases b <;> simp [P, E, σ_neg]

lemma σ_pos (t : ℝ) : 0 < σ t := by unfold σ; positivity
lemma σ_le_one (t : ℝ) : σ t ≤ 1 := by
  unfold σ; rw [div_le_one (by positivity)]; linarith [exp_pos (-t)]

lemma P_nonneg (s z : ℕ → Bool) (γ v : ℝ) (r : ℕ) (b : Bool) : 0 ≤ P s z γ v r b := by
  rw [P_eq_σ]; exact (σ_pos _).le
lemma P_le_one (s z : ℕ → Bool) (γ v : ℝ) (r : ℕ) (b : Bool) : P s z γ v r b ≤ 1 := by
  rw [P_eq_σ]; exact σ_le_one _

/-- Union bound for a product of probabilities: `Π p_i ≥ 1 − Σ (1 − p_i)`. -/
lemma prod_ge (p : ℕ → ℝ) (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) :
    ∀ (a n : ℕ), 1 - ∑ i ∈ Ico a (a + n), (1 - p i) ≤ ∏ i ∈ Ico a (a + n), p i
  | a, 0 => by simp
  | a, n + 1 => by
    have ih := prod_ge p h0 h1 a n
    rw [show a + (n + 1) = (a + n) + 1 by omega, sum_Ico_succ_top (by omega),
      prod_Ico_succ_top (by omega)]
    have hP : 0 ≤ ∏ i ∈ Ico a (a + n), p i := prod_nonneg (fun i _ => h0 i)
    have hP1 : ∏ i ∈ Ico a (a + n), p i ≤ 1 := prod_le_one₀ (fun i _ => h0 i) (fun i _ => h1 i)
    nlinarith [h0 (a + n), h1 (a + n)]

/-- Probability that the model generates the tokens `w r₀, …, w (2N − 1)` after the prefix
`w 0, …, w (r₀ − 1)` (autoregressive sampling: product of the conditional probabilities). -/
def pathProb (s w : ℕ → Bool) (γ v : ℝ) (r₀ n : ℕ) : ℝ :=
  ∏ r ∈ Ico r₀ n, P s w γ v r (w r)

lemma pathProb_ge (s w : ℕ → Bool) (γ v : ℝ) (N r₀ : ℕ) (hr : r₀ ≤ 2 * N)
    (hstep : ∀ r, r₀ ≤ r → r < 2 * N → 1 - exp (-(N : ℝ)) ≤ P s w γ v r (w r)) :
    1 - 2 * N * exp (-(N : ℝ)) ≤ pathProb s w γ v r₀ (2 * N) := by
  have := prod_ge (fun r => P s w γ v r (w r)) (fun _ => P_nonneg _ _ _ _ _ _)
    (fun _ => P_le_one _ _ _ _ _ _) r₀ (2 * N - r₀)
  rw [show r₀ + (2 * N - r₀) = 2 * N by omega] at this
  unfold pathProb
  refine le_trans ?_ this
  have hsum : ∑ i ∈ Ico r₀ (2 * N), (1 - P s w γ v i (w i)) ≤ ∑ _i ∈ Ico r₀ (2 * N), exp (-(N : ℝ)) :=
    sum_le_sum (fun i hi => by
      have := hstep i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2; linarith)
  have hcard : ∑ _i ∈ Ico r₀ (2 * N), exp (-(N : ℝ)) ≤ 2 * N * exp (-(N : ℝ)) := by
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    have : ((2 * N - r₀ : ℕ) : ℝ) ≤ (2 * N : ℕ) := by exact_mod_cast Nat.sub_le _ _
    simpa using this
  linarith

lemma E_sq (b : Bool) : E b * E b = 1 := by cases b <;> simp [E]

/-- Theorem `th:dyck_informal`, memorization: if `v γ > N²`, then for every prefix of `s` of
length `1 ≤ r ≤ 2N − 1` the next token of `s` has probability at least `1 − e^{−N}`, and the model
completes every non-empty prefix of `s` back into `s` with probability at least `1 − 2N e^{−N}`. -/
theorem memorization_step (s : ℕ → Bool) (γ v : ℝ) (N r : ℕ) (hr1 : 1 ≤ r) (hr : r < 2 * N)
    (hvg : (N : ℝ) ^ 2 < v * γ) : 1 - exp (-(N : ℝ)) ≤ P s s γ v r (s r) := by
  rw [P_eq_σ]
  refine le_trans (σ_ge _) (σ_mono ?_)
  have hX : 2 * E (s r) * X s s γ v r = 2 * (v * γ) / r := by
    unfold X; rw [S_eq s s γ r hr1]
    have := E_sq (s r)
    field_simp; nlinarith [this]
  rw [hX]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hr' : (r : ℝ) ≤ 2 * N := by exact_mod_cast hr.le
  rw [le_div_iff₀ hrpos]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

theorem memorization (s : ℕ → Bool) (γ v : ℝ) (N r₀ : ℕ) (hr1 : 1 ≤ r₀) (hr : r₀ ≤ 2 * N)
    (hvg : (N : ℝ) ^ 2 < v * γ) :
    1 - 2 * N * exp (-(N : ℝ)) ≤ pathProb s s γ v r₀ (2 * N) :=
  pathProb_ge s s γ v N r₀ hr (fun r h1 h2 => memorization_step s γ v N r (by omega) h2 hvg)

/-! ### Generalization by contraction (`γ = −1/2`, `v < −2N²`) -/

/-- Integer stack size. -/
def D (w : ℕ → Bool) (t : ℕ) : ℤ := ∑ i ∈ range t, (if w i then 1 else -1)

lemma Δ_eq (w : ℕ → Bool) (t : ℕ) : Δ w t = (D w t : ℝ) := by
  unfold Δ D; push_cast; refine sum_congr rfl (fun i _ => ?_); unfold E; split_ifs <;> simp

lemma D_succ (w : ℕ → Bool) (t : ℕ) : D w (t + 1) = D w t + (if w t then 1 else -1) := by
  unfold D; rw [sum_range_succ]

lemma D_parity (w : ℕ → Bool) : ∀ t, Even (D w t - t)
  | 0 => by simp [D]
  | t + 1 => by
    rw [D_succ]; have := D_parity w t
    split_ifs
    · push_cast; rw [show D w t + 1 - (↑t + 1) = D w t - t by ring]; exact this
    · push_cast; rw [show D w t + -1 - (↑t + 1) = D w t - t - 2 by ring]
      exact this.sub (by decide)

lemma D_lip (w : ℕ → Bool) (t : ℕ) : ∀ u, D w (t + u) ≥ D w t - u
  | 0 => by simp
  | u + 1 => by
    have := D_lip w t u
    rw [show t + (u + 1) = (t + u) + 1 by omega, D_succ]; split_ifs <;> push_cast <;> omega

/-- A Dyck word of length `n`: non-negative stack, ending at zero. -/
def IsDyck (n : ℕ) (w : ℕ → Bool) : Prop := (∀ t ≤ n, 0 ≤ D w t) ∧ D w n = 0

lemma dyck_upper {n : ℕ} {w : ℕ → Bool} (h : IsDyck n w) (t : ℕ) (ht : t ≤ n) :
    D w t ≤ n - t := by
  have := D_lip w t (n - t); rw [show t + (n - t) = n by omega, h.2] at this; push_cast at this
  omega

/-- The token that follows the sign of the logit when `γ = −1/2` and `v < 0`: open iff
`D_t(z) − D_t(s) − E(s_t)/2 < 0`, i.e. iff `D_t(z) ≤ D_t(s)` (s opens) or `D_t(z) < D_t(s)`
(s closes). -/
def rule (a b : ℤ) (e : Bool) : Bool := if e then decide (a ≤ b) else decide (a < b)

/-- Stack of the completion that follows the sign of the logit from the prefix `z|_{<r₀}`. -/
def stk (s z : ℕ → Bool) (r₀ : ℕ) : ℕ → ℤ
  | 0 => 0
  | t + 1 => stk s z r₀ t +
      (if (if t < r₀ then z t else rule (stk s z r₀ t) (D s t) (s t)) then 1 else -1)

/-- The completion: the prefix `z`, then the sign-following tokens. -/
def comp (s z : ℕ → Bool) (r₀ : ℕ) (t : ℕ) : Bool :=
  if t < r₀ then z t else rule (stk s z r₀ t) (D s t) (s t)

lemma D_comp (s z : ℕ → Bool) (r₀ : ℕ) : ∀ t, D (comp s z r₀) t = stk s z r₀ t
  | 0 => by simp [D, stk]
  | t + 1 => by rw [D_succ, D_comp s z r₀ t]; rfl

lemma D_comp_prefix (s z : ℕ → Bool) (r₀ : ℕ) : ∀ t ≤ r₀, D (comp s z r₀) t = D z t
  | 0, _ => by simp [D]
  | t + 1, h => by
    rw [D_succ, D_succ, D_comp_prefix s z r₀ t (by omega)]; simp [comp, show t < r₀ by omega]

/-- One sign-following step keeps the stack in `[0, 2N − t]`. -/
lemma step_ok (a b b' L : ℤ) (e : Bool) (h0 : 0 ≤ a) (h1 : a ≤ L) (hb1 : b ≤ L) (hb'0 : 0 ≤ b')
    (hb2 : b' ≤ L - 1) (hb' : b' = b + (if e then 1 else -1)) (hpar : Even (a - b)) :
    0 ≤ a + (if rule a b e then 1 else -1) ∧ a + (if rule a b e then 1 else -1) ≤ L - 1 := by
  obtain ⟨m, hm⟩ := hpar
  cases e <;> simp only [rule] at * <;> split_ifs at * with hh <;> simp_all <;> omega

/-- The completion of any valid prefix is a Dyck word (deterministic part of the theorem). -/
theorem comp_isDyck (s z : ℕ → Bool) (N r₀ : ℕ) (hr : r₀ ≤ 2 * N) (hs : IsDyck (2 * N) s)
    (hz : ∀ t ≤ r₀, 0 ≤ D z t ∧ D z t ≤ 2 * N - t) : IsDyck (2 * N) (comp s z r₀) := by
  have inv : ∀ k, r₀ + k ≤ 2 * N →
      0 ≤ D (comp s z r₀) (r₀ + k) ∧ D (comp s z r₀) (r₀ + k) ≤ 2 * N - (r₀ + k) := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.add_zero, D_comp_prefix s z r₀ r₀ le_rfl]; exact hz r₀ le_rfl
    | succ k ih =>
      intro hk
      obtain ⟨h0, h1⟩ := ih (by omega)
      have hpar : Even (D (comp s z r₀) (r₀ + k) - D s (r₀ + k)) := by
        have := (D_parity (comp s z r₀) (r₀ + k)).sub (D_parity s (r₀ + k))
        rwa [show D (comp s z r₀) (r₀ + k) - ↑(r₀ + k) - (D s (r₀ + k) - ↑(r₀ + k))
          = D (comp s z r₀) (r₀ + k) - D s (r₀ + k) by ring] at this
      have hct : comp s z r₀ (r₀ + k) = rule (D (comp s z r₀) (r₀ + k)) (D s (r₀ + k)) (s (r₀ + k)) := by
        simp [comp, D_comp]
      have key := step_ok (D (comp s z r₀) (r₀ + k)) (D s (r₀ + k)) (D s (r₀ + k + 1))
        (2 * N - (r₀ + k)) (s (r₀ + k)) h0 h1 (dyck_upper hs _ (by omega))
        (hs.1 _ (by omega)) (by have := dyck_upper hs (r₀ + k + 1) (by omega); push_cast at this ⊢; omega)
        (D_succ s _) hpar
      rw [show r₀ + (k + 1) = r₀ + k + 1 by omega, D_succ, hct]
      push_cast at key ⊢; constructor <;> [exact key.1; linarith [key.2]]
  refine ⟨fun t ht => ?_, ?_⟩
  · by_cases htr : t ≤ r₀
    · rw [D_comp_prefix s z r₀ t htr]; exact (hz t htr).1
    · have := inv (t - r₀) (by omega); rw [show r₀ + (t - r₀) = t by omega] at this
      exact this.1
  · have := inv (2 * N - r₀) (by omega)
    rw [show r₀ + (2 * N - r₀) = 2 * N by omega] at this
    push_cast at this; omega

/-- The sign-following token has `E(tok) · (a − b − E(e)/2) ≤ −1/2`. -/
lemma rule_margin (a b : ℤ) (e : Bool) :
    E (rule a b e) * ((a : ℝ) - b + (-1/2) * E e) ≤ -1/2 := by
  cases e
  · by_cases h : a < b
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      simp only [rule, h, decide_true, E, if_true, Bool.false_eq_true, if_false]; linarith
    · have : (b : ℝ) ≤ a := by exact_mod_cast (not_lt.mp h)
      simp only [rule, h, decide_false, E, Bool.false_eq_true, if_false]; linarith
  · by_cases h : a ≤ b
    · have : (a : ℝ) ≤ b := by exact_mod_cast h
      simp only [rule, h, decide_true, E, if_true]; linarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast (not_le.mp h)
      simp only [rule, h, decide_false, E, if_true, Bool.false_eq_true, if_false]; linarith

/-- Theorem `th:dyck_informal`, generalization by contraction: with `γ = −1/2` and `v < −2N²`,
for any Dyck word `s` of length `2N` (the single training sequence) and any non-empty prefix of
length `r₀` of a Dyck word of length `2N` (`0 ≤ D_t(z) ≤ 2N − t` for `t ≤ r₀`), the model completes
the prefix into the Dyck word `comp s z r₀`, which agrees with `z` before `r₀`, with probability at
least `1 − 2N e^{−N}`. -/
theorem generalization (s z : ℕ → Bool) (v : ℝ) (N r₀ : ℕ) (hr1 : 1 ≤ r₀) (hr : r₀ ≤ 2 * N)
    (hs : IsDyck (2 * N) s) (hz : ∀ t ≤ r₀, 0 ≤ D z t ∧ D z t ≤ 2 * N - t)
    (hv : v < -2 * (N : ℝ) ^ 2) :
    IsDyck (2 * N) (comp s z r₀) ∧ (∀ t < r₀, comp s z r₀ t = z t) ∧
    1 - 2 * N * exp (-(N : ℝ)) ≤ pathProb s (comp s z r₀) (-1/2) v r₀ (2 * N) := by
  refine ⟨comp_isDyck s z N r₀ hr hs hz, fun t ht => by simp [comp, ht], ?_⟩
  refine pathProb_ge s (comp s z r₀) (-1/2) v N r₀ hr (fun t ht1 ht2 => ?_)
  rw [P_eq_σ]
  refine le_trans (σ_ge _) (σ_mono ?_)
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht' : (t : ℝ) < 2 * N := by exact_mod_cast ht2
  have hct : comp s z r₀ t = rule (D (comp s z r₀) t) (D s t) (s t) := by
    simp [comp, show ¬ t < r₀ by omega, D_comp]
  have hX : X s (comp s z r₀) (-1/2) v t
      = v / t * ((D (comp s z r₀) t : ℝ) - D s t + (-1/2) * E (s t)) := by
    unfold X; rw [S_eq _ _ _ t (by omega), Δ_eq, Δ_eq]
  rw [hX, hct]
  have hm := rule_margin (D (comp s z r₀) t) (D s t) (s t)
  set M := E (rule (D (comp s z r₀) t) (D s t) (s t)) * ((D (comp s z r₀) t : ℝ) - D s t + (-1/2) * E (s t))
  have hrw : 2 * E (rule (D (comp s z r₀) t) (D s t) (s t)) *
      (v / t * ((D (comp s z r₀) t : ℝ) - D s t + (-1/2) * E (s t))) = 2 * (v / t) * M := by
    simp only [M]; ring
  rw [hrw]
  have hvt : v / t < 0 := div_neg_of_neg_of_pos (by nlinarith [sq_nonneg (N : ℝ)]) htpos
  have h1 : -(v / t) ≤ 2 * (v / t) * M := by nlinarith
  have h2 : (N : ℝ) ≤ -(v / t) := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    rw [← neg_div, le_div_iff₀ htpos]; nlinarith
  linarith

/-! ### Failure under positive `γ` (`0 < γ < 2`, `v γ > N²`) -/

/-- Generalized union bound: per-step error `ε` gives path probability `≥ 1 − 2N ε`. -/
lemma pathProb_ge' (s w : ℕ → Bool) (γ v ε : ℝ) (N r₀ : ℕ) (hr : r₀ ≤ 2 * N) (hε : 0 ≤ ε)
    (hstep : ∀ r, r₀ ≤ r → r < 2 * N → 1 - ε ≤ P s w γ v r (w r)) :
    1 - 2 * N * ε ≤ pathProb s w γ v r₀ (2 * N) := by
  have := prod_ge (fun r => P s w γ v r (w r)) (fun _ => P_nonneg _ _ _ _ _ _)
    (fun _ => P_le_one _ _ _ _ _ _) r₀ (2 * N - r₀)
  rw [show r₀ + (2 * N - r₀) = 2 * N by omega] at this
  unfold pathProb
  refine le_trans ?_ this
  have hsum : ∑ i ∈ Ico r₀ (2 * N), (1 - P s w γ v i (w i)) ≤ ∑ _i ∈ Ico r₀ (2 * N), ε :=
    sum_le_sum (fun i hi => by have := hstep i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2; linarith)
  have hcard : ∑ _i ∈ Ico r₀ (2 * N), ε ≤ 2 * N * ε := by
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hε
    have : ((2 * N - r₀ : ℕ) : ℝ) ≤ (2 * N : ℕ) := by exact_mod_cast Nat.sub_le _ _
    simpa using this
  linarith

/-- The token following the sign of the logit when `v > 0`: open iff
`D_t(z) − D_t(s) + γ E(s_t) > 0`. -/
def ruleP (γ : ℝ) (a b : ℤ) (e : Bool) : Bool := decide ((0 : ℝ) < (a : ℝ) - b + γ * E e)

/-- Stack and tokens of the sign-following completion for `γ > 0`. -/
def stkP (γ : ℝ) (s z : ℕ → Bool) (r₀ : ℕ) : ℕ → ℤ
  | 0 => 0
  | t + 1 => stkP γ s z r₀ t +
      (if (if t < r₀ then z t else ruleP γ (stkP γ s z r₀ t) (D s t) (s t)) then 1 else -1)

def compP (γ : ℝ) (s z : ℕ → Bool) (r₀ : ℕ) (t : ℕ) : Bool :=
  if t < r₀ then z t else ruleP γ (stkP γ s z r₀ t) (D s t) (s t)

lemma D_compP (γ : ℝ) (s z : ℕ → Bool) (r₀ : ℕ) : ∀ t, D (compP γ s z r₀) t = stkP γ s z r₀ t
  | 0 => by simp [D, stkP]
  | t + 1 => by rw [D_succ, D_compP γ s z r₀ t]; rfl

lemma D_compP_prefix (γ : ℝ) (s z : ℕ → Bool) (r₀ : ℕ) : ∀ t ≤ r₀, D (compP γ s z r₀) t = D z t
  | 0, _ => by simp [D]
  | t + 1, h => by
    rw [D_succ, D_succ, D_compP_prefix γ s z r₀ t (by omega)]; simp [compP, show t < r₀ by omega]

/-- With `0 < γ < 2`, a gap of at least 2 in absolute value fixes the sign of the logit, and the
sign-following token keeps the gap at least 2 in absolute value. -/
lemma gap_step (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (a b : ℤ) (e : Bool) (hg : 2 ≤ |a - b|) :
    2 ≤ |(a + (if ruleP γ a b e then 1 else -1)) - (b + (if e then 1 else -1))| ∧
    (2 - γ) ≤ E (ruleP γ a b e) * ((a : ℝ) - b + γ * E e) := by
  rcases le_abs'.mp hg with h | h
  · -- `a − b ≤ −2`: the logit is negative, the model closes
    have hr : (a : ℝ) - b ≤ -2 := by exact_mod_cast (by omega : a - b ≤ -2)
    have hneg : ¬ (0 : ℝ) < (a : ℝ) - b + γ * E e := by cases e <;> simp [E] <;> linarith
    simp only [ruleP, hneg, decide_false, Bool.false_eq_true, if_false]
    constructor
    · cases e <;> simp <;> rw [le_abs'] <;> left <;> omega
    · simp only [E, Bool.false_eq_true, if_false]; cases e <;> simp [E] <;> linarith
  · have hr : (2 : ℝ) ≤ (a : ℝ) - b := by exact_mod_cast h
    have hpos : (0 : ℝ) < (a : ℝ) - b + γ * E e := by cases e <;> simp [E] <;> linarith
    simp only [ruleP, hpos, decide_true, if_true]
    constructor
    · cases e <;> simp <;> rw [le_abs'] <;> right <;> omega
    · simp only [E, if_true]; cases e <;> simp [E] <;> linarith

/-- Theorem `th:dyck_informal`, failure under positive `γ`: if `0 < γ < 2` and `v γ > N²`, and the
prefix of length `r₀ ≥ 1` has a different stack size than `s`'s prefix of the same length, then the
sign-following completion is not a Dyck word, and the model generates it with probability at least
`1 − 2N e^{−N(2−γ)/γ}`. -/
theorem failure (s z : ℕ → Bool) (γ v : ℝ) (N r₀ : ℕ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hr1 : 1 ≤ r₀) (hr : r₀ ≤ 2 * N) (hs : D s (2 * N) = 0) (hvg : (N : ℝ) ^ 2 < v * γ)
    (hdiff : D z r₀ ≠ D s r₀) :
    ¬ IsDyck (2 * N) (compP γ s z r₀) ∧ (∀ t < r₀, compP γ s z r₀ t = z t) ∧
    1 - 2 * N * exp (-((N : ℝ) * (2 - γ) / γ)) ≤ pathProb s (compP γ s z r₀) γ v r₀ (2 * N) := by
  -- the gap is even and non-zero at `r₀`, hence at least 2 in absolute value; it stays so
  have hpar0 : Even (D z r₀ - D s r₀) := by
    have := (D_parity z r₀).sub (D_parity s r₀)
    rwa [show D z r₀ - ↑r₀ - (D s r₀ - ↑r₀) = D z r₀ - D s r₀ by ring] at this
  have hgap : ∀ k, 2 ≤ |D (compP γ s z r₀) (r₀ + k) - D s (r₀ + k)| := by
    intro k
    induction k with
    | zero =>
      rw [Nat.add_zero, D_compP_prefix γ s z r₀ r₀ le_rfl]
      obtain ⟨m, hm⟩ := hpar0
      have : D z r₀ - D s r₀ ≠ 0 := sub_ne_zero.mpr hdiff
      rw [le_abs']; omega
    | succ k ih =>
      have hct : compP γ s z r₀ (r₀ + k)
          = ruleP γ (D (compP γ s z r₀) (r₀ + k)) (D s (r₀ + k)) (s (r₀ + k)) := by
        simp [compP, D_compP]
      rw [show r₀ + (k + 1) = r₀ + k + 1 by omega, D_succ, D_succ, hct]
      exact (gap_step γ hγ0 hγ2 _ _ _ ih).1
  have hv : 0 < v := by
    by_contra h; push_neg at h; nlinarith [sq_nonneg (N : ℝ)]
  refine ⟨fun hd => ?_, fun t ht => by simp [compP, ht], ?_⟩
  · have := hgap (2 * N - r₀)
    rw [show r₀ + (2 * N - r₀) = 2 * N by omega, hd.2, hs] at this
    norm_num at this
  · refine pathProb_ge' s _ γ v _ N r₀ hr (exp_pos _).le (fun t ht1 ht2 => ?_)
    rw [P_eq_σ]
    refine le_trans (σ_ge _) (σ_mono ?_)
    have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have ht' : (t : ℝ) < 2 * N := by exact_mod_cast ht2
    have hk := hgap (t - r₀)
    rw [show r₀ + (t - r₀) = t by omega] at hk
    have hct : compP γ s z r₀ t = ruleP γ (D (compP γ s z r₀) t) (D s t) (s t) := by
      simp [compP, show ¬ t < r₀ by omega, D_compP]
    have hX : X s (compP γ s z r₀) γ v t
        = v / t * ((D (compP γ s z r₀) t : ℝ) - D s t + γ * E (s t)) := by
      unfold X; rw [S_eq _ _ _ t (by omega), Δ_eq, Δ_eq]
    rw [hX, hct]
    have hm := (gap_step γ hγ0 hγ2 (D (compP γ s z r₀) t) (D s t) (s t) hk).2
    set M := E (ruleP γ (D (compP γ s z r₀) t) (D s t) (s t)) *
      ((D (compP γ s z r₀) t : ℝ) - D s t + γ * E (s t))
    have hrw : 2 * E (ruleP γ (D (compP γ s z r₀) t) (D s t) (s t)) *
        (v / t * ((D (compP γ s z r₀) t : ℝ) - D s t + γ * E (s t))) = 2 * (v / t) * M := by
      simp only [M]; ring
    rw [hrw]
    have hvt : 0 < v / t := div_pos hv htpos
    have h1 : 2 * (v / t) * (2 - γ) ≤ 2 * (v / t) * M :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    have h2 : (N : ℝ) * (2 - γ) / γ ≤ 2 * (v / t) * (2 - γ) := by
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h2γ : 0 < 2 - γ := by linarith
      have h3 : (N : ℝ) ≤ 2 * (v / t) * γ := by
        rw [show 2 * (v / t) * γ = 2 * (v * γ) / t by ring, le_div_iff₀ htpos]; nlinarith
      rw [div_le_iff₀ hγ0]
      nlinarith [mul_le_mul_of_nonneg_right h3 h2γ.le]
    linarith

/-! ### Cross-entropy of the memorization regime -/

lemma neg_log_σ_le (t : ℝ) : -Real.log (σ t) ≤ exp (-t) := by
  unfold σ
  rw [one_div, Real.log_inv, neg_neg]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + exp (-t) by positivity)
  linarith

/-- Memorization, loss: if `v γ > N²`, the cross-entropy summed over the prefixes `1 ≤ r ≤ 2N − 1`
of `s` is at most `2N e^{−N}` (hence below `8N² e^{−N}` for `N ≥ 1`). -/
theorem memorization_loss (s : ℕ → Bool) (γ v : ℝ) (N : ℕ) (hvg : (N : ℝ) ^ 2 < v * γ) :
    ∑ r ∈ Ico 1 (2 * N), -Real.log (P s s γ v r (s r)) ≤ 2 * N * exp (-(N : ℝ)) := by
  have hstep : ∀ r ∈ Ico 1 (2 * N), -Real.log (P s s γ v r (s r)) ≤ exp (-(N : ℝ)) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := mem_Ico.mp hr
    rw [P_eq_σ]
    refine le_trans (neg_log_σ_le _) (exp_le_exp.mpr ?_)
    have hX : 2 * E (s r) * X s s γ v r = 2 * (v * γ) / r := by
      unfold X; rw [S_eq s s γ r hr1]
      have := E_sq (s r)
      field_simp; nlinarith [this]
    rw [hX, neg_le_neg_iff]
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hr' : (r : ℝ) ≤ 2 * N := by exact_mod_cast hr2.le
    rw [le_div_iff₀ hrpos]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  calc ∑ r ∈ Ico 1 (2 * N), -Real.log (P s s γ v r (s r)) ≤ ∑ _r ∈ Ico 1 (2 * N), exp (-(N : ℝ)) :=
        sum_le_sum hstep
    _ ≤ 2 * N * exp (-(N : ℝ)) := by
        rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        have : ((2 * N - 1 : ℕ) : ℝ) ≤ (2 * N : ℕ) := by exact_mod_cast Nat.sub_le _ _
        simpa using this

end

end Llrg.Dyck
