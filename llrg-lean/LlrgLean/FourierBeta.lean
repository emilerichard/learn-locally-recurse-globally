/-
Appendix D, Fourier form of the fiber imbalance: `β_S = ‖P_S f‖₁ ≤ ‖P_S f‖₂ =
(Σ_{T ⊆ S} f̂(T)²)^{1/2}` for `f = (−1)^R`, and `β_S = 0` for every `|S| = k` iff `f̂(T) = 0` for
every `|T| ≤ k`. Walsh characters on `{0,1}^n`, orthogonality, Fourier expansion, the averaging
operator `P_S` and Parseval are developed here.
-/
import LlrgLean.Marginals

open scoped symmDiff
open Finset

namespace Llrg.Fourier

variable {n : ℕ}

abbrev Pt (n : ℕ) := Fin n → Bool
abbrev RFun (n : ℕ) := Pt n → ℝ

/-- Walsh character `χ_T(x) = (−1)^{Σ_{i ∈ T} x_i}`. -/
def chi (T : Finset (Fin n)) (x : Pt n) : ℝ := (-1) ^ (T.filter (fun i => x i = true)).card

/-- Normalized inner product `E[f g]` under the uniform distribution. -/
noncomputable def ip (f g : RFun n) : ℝ := (∑ x, f x * g x) / 2 ^ n

/-- Fourier coefficient `f̂(T) = E[f χ_T]`. -/
noncomputable def fhat (f : RFun n) (T : Finset (Fin n)) : ℝ := ip f (chi T)

lemma chi_sq (T : Finset (Fin n)) (x : Pt n) : chi T x * chi T x = 1 := by
  unfold chi; rw [← pow_add, ← two_mul, pow_mul]; simp

lemma chi_mul (T U : Finset (Fin n)) (x : Pt n) : chi T x * chi U x = chi (symmDiff T U) x := by
  unfold chi
  rw [← pow_add]
  set A := T.filter (fun i => x i = true)
  set B := U.filter (fun i => x i = true)
  have hf : (symmDiff T U).filter (fun i => x i = true) = symmDiff A B := by
    ext i; simp only [A, B, mem_filter, Finset.mem_symmDiff]; tauto
  have hc := Llrg.card_symmDiff_int A B
  have h : A.card + B.card = (symmDiff A B).card + 2 * (A ∩ B).card := by omega
  rw [hf, h, pow_add, pow_mul]; simp

lemma chi_empty (x : Pt n) : chi ∅ x = 1 := by simp [chi]

/-- `Σ_x χ_V(x) = 0` for `V ≠ ∅` (flipping one input of `V` negates the character). -/
lemma sum_chi_ne (V : Finset (Fin n)) (hV : V.Nonempty) : ∑ x : Pt n, chi V x = 0 := by
  obtain ⟨i, hi⟩ := hV
  let flip : Pt n → Pt n := fun x => Function.update x i (!x i)
  have hinv : ∀ x, flip (flip x) = x := by
    intro x; funext j; by_cases hj : j = i
    · subst hj; simp [flip]
    · simp [flip, Function.update_of_ne hj]
  have hneg : ∀ x, chi V (flip x) = - chi V x := by
    intro x; unfold chi
    have hA : (V.filter fun j => flip x j = true)
        = if x i then (V.filter fun j => x j = true).erase i
          else insert i (V.filter fun j => x j = true) := by
      ext j; by_cases hj : j = i
      · subst hj; cases hx : x j <;> simp [flip, hx, hi]
      · cases hx : x i <;> simp [flip, Function.update_of_ne hj, hj]
    rw [hA]; cases hx : x i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [card_insert_of_notMem (by simp [hx]), pow_succ]; ring
    · simp only [↓reduceIte]
      have h1 : i ∈ V.filter (fun j => x j = true) := by simp [hi, hx]
      rw [← Finset.card_erase_add_one h1, pow_succ]; ring
  have := Fintype.sum_equiv (Function.Involutive.toPerm flip hinv) (fun x => chi V x)
    (fun x => - chi V x) (fun x => by
      show chi V x = -chi V (flip x); have h := hneg x; linarith)
  rw [sum_neg_distrib] at this
  linarith

lemma sum_chi (V : Finset (Fin n)) : ∑ x : Pt n, chi V x = if V = ∅ then 2 ^ n else 0 := by
  split_ifs with h
  · subst h; simp [chi_empty, Fintype.card_fun]
  · exact sum_chi_ne V (nonempty_iff_ne_empty.mpr h)

/-- Orthonormality of the characters. -/
theorem ip_chi (T U : Finset (Fin n)) : ip (chi T) (chi U) = if T = U then 1 else 0 := by
  unfold ip
  simp_rw [chi_mul]
  rw [sum_chi]
  by_cases h : T = U
  · subst h; simp
  · have : symmDiff T U ≠ ∅ := by
      intro h'; exact h (symmDiff_eq_bot.mp h')
    simp [this, h]

lemma sum_mul_chi (c : Finset (Fin n) → ℝ) (U : Finset (Fin n)) :
    ∑ x : Pt n, (∑ T, c T • chi T) x * chi U x = ∑ T, c T * ∑ x : Pt n, chi T x * chi U x := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]; refine sum_congr rfl (fun T _ => sum_congr rfl (fun x _ => by ring))

/-- Coefficients of a character expansion are its Fourier coefficients. -/
lemma fhat_sum (c : Finset (Fin n) → ℝ) (U : Finset (Fin n)) :
    fhat (∑ T, c T • chi T) U = c U := by
  unfold fhat ip
  rw [sum_mul_chi]
  have : ∀ T, c T * ∑ x : Pt n, chi T x * chi U x = c T * (if T = U then (2 : ℝ) ^ n else 0) := by
    intro T; congr 1
    have := ip_chi T U; unfold ip at this
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    split_ifs at this ⊢ with h
    · field_simp at this; linarith
    · field_simp at this; linarith
  simp_rw [this]
  simp [mul_comm]

lemma chi_linIndep : LinearIndependent ℝ (fun T : Finset (Fin n) => chi T) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc U
  have := fhat_sum c U
  rw [hc] at this
  simpa [fhat, ip] using this.symm

/-- Fourier expansion: `f = Σ_T f̂(T) χ_T`. -/
theorem fourier_expansion (f : RFun n) : f = ∑ T, fhat f T • chi T := by
  have hspan := (chi_linIndep (n := n)).span_eq_top_of_card_eq_finrank
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin])
  have hf : f ∈ Submodule.span ℝ (Set.range (fun T : Finset (Fin n) => chi T)) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hf
  have : ∀ T, fhat f T = c T := fun T => by rw [← hc, fhat_sum]
  simp_rw [this]; exact hc.symm

/-! ### Averaging over fibers: the conditional expectation `P_S` -/

/-- Fiber of `x` for bound set `S`: inputs that agree with `x` on `S`. -/
def fib (S : Finset (Fin n)) (x : Pt n) : Finset (Pt n) := univ.filter (fun y => ∀ i ∈ S, y i = x i)

lemma mem_fib_self (S : Finset (Fin n)) (x : Pt n) : x ∈ fib S x := by simp [fib]

lemma fib_card_pos (S : Finset (Fin n)) (x : Pt n) : (0 : ℝ) < (fib S x).card := by
  exact_mod_cast Finset.card_pos.mpr ⟨x, mem_fib_self S x⟩

/-- `P_S f (x)`: the average of `f` over the fiber of `x`. -/
noncomputable def avg (S : Finset (Fin n)) (f : RFun n) (x : Pt n) : ℝ :=
  (∑ y ∈ fib S x, f y) / (fib S x).card

lemma chi_eq_of_agree (T : Finset (Fin n)) {x y : Pt n} (h : ∀ i ∈ T, y i = x i) :
    chi T y = chi T x := by
  unfold chi; congr 2; ext i; simp only [mem_filter]; constructor
  · rintro ⟨hi, hy⟩; exact ⟨hi, (h i hi) ▸ hy⟩
  · rintro ⟨hi, hx⟩; exact ⟨hi, (h i hi).symm ▸ hx⟩

/-- `P_S χ_T = χ_T` if `T ⊆ S` and `0` otherwise. -/
theorem avg_chi (S T : Finset (Fin n)) (x : Pt n) :
    avg S (chi T) x = if T ⊆ S then chi T x else 0 := by
  unfold avg
  split_ifs with hT
  · rw [sum_congr rfl (fun y hy => chi_eq_of_agree T (fun i hi => by
      simp only [fib, mem_filter, mem_univ, true_and] at hy; exact hy i (hT hi)))]
    rw [sum_const, nsmul_eq_mul]; field_simp [(fib_card_pos S x).ne']
  · obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hT
    let flip : Pt n → Pt n := fun y => Function.update y i (!y i)
    have hinv : ∀ y, flip (flip y) = y := by
      intro y; funext j; by_cases hj : j = i
      · subst hj; simp [flip]
      · simp [flip, Function.update_of_ne hj]
    have hmem : ∀ y ∈ fib S x, flip y ∈ fib S x := by
      intro y hy; simp only [fib, mem_filter, mem_univ, true_and] at hy ⊢
      intro j hj
      have hji : j ≠ i := fun h => hiS (h ▸ hj)
      simp [flip, Function.update_of_ne hji, hy j hj]
    have hneg : ∀ y, chi T (flip y) = - chi T y := by
      intro y; unfold chi
      have hA : (T.filter fun j => flip y j = true)
          = if y i then (T.filter fun j => y j = true).erase i
            else insert i (T.filter fun j => y j = true) := by
        ext j; by_cases hj : j = i
        · subst hj; cases hx : y j <;> simp [flip, hx, hiT]
        · cases hx : y i <;> simp [flip, Function.update_of_ne hj, hj]
      rw [hA]; cases hx : y i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [card_insert_of_notMem (by simp [hx]), pow_succ]; ring
      · simp only [↓reduceIte]
        have h1 : i ∈ T.filter (fun j => y j = true) := by simp [hiT, hx]
        rw [← Finset.card_erase_add_one h1, pow_succ]; ring
    have hsum : ∑ y ∈ fib S x, chi T y = ∑ y ∈ fib S x, chi T (flip y) :=
      Finset.sum_nbij' flip flip hmem hmem (fun y _ => hinv y) (fun y _ => hinv y)
        (fun y _ => by rw [hinv])
    have : ∑ y ∈ fib S x, chi T y = 0 := by
      have h2 : ∑ y ∈ fib S x, chi T (flip y) = - ∑ y ∈ fib S x, chi T y := by
        rw [← sum_neg_distrib]; exact sum_congr rfl (fun y _ => hneg y)
      linarith
    rw [this, zero_div]

lemma avg_sum (S : Finset (Fin n)) (c : Finset (Fin n) → ℝ) (x : Pt n) :
    avg S (∑ T, c T • chi T) x = ∑ T, c T * avg S (chi T) x := by
  unfold avg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, Finset.sum_div]
  refine sum_congr rfl (fun T _ => ?_)
  rw [← Finset.mul_sum, mul_div_assoc]

/-- `P_S f = Σ_{T ⊆ S} f̂(T) χ_T`. -/
theorem avg_expansion (S : Finset (Fin n)) (f : RFun n) (x : Pt n) :
    avg S f x = ∑ T, (if T ⊆ S then fhat f T else 0) * chi T x := by
  conv_lhs => rw [fourier_expansion f]
  rw [avg_sum]
  refine sum_congr rfl (fun T _ => ?_)
  rw [avg_chi]; split_ifs <;> simp

/-- Parseval for an expansion: `E[g²] = Σ_T d_T²` for `g = Σ_T d_T χ_T`. -/
lemma ip_self_sum (d : Finset (Fin n) → ℝ) :
    ip (∑ T, d T • chi T) (∑ T, d T • chi T) = ∑ T, d T ^ 2 := by
  have hlin : ∀ (g : RFun n), ip g (∑ T, d T • chi T) = ∑ T, d T * ip g (chi T) := by
    intro g; unfold ip
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_div]
    refine sum_congr rfl (fun T _ => ?_)
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1; exact sum_congr rfl (fun x _ => by ring)
  rw [hlin]
  refine sum_congr rfl (fun T _ => ?_)
  have := fhat_sum d T; unfold fhat at this; rw [this]; ring

/-- Parseval for the projection: `‖P_S f‖₂² = Σ_{T ⊆ S} f̂(T)²`. -/
theorem norm2_avg (S : Finset (Fin n)) (f : RFun n) :
    ip (avg S f) (avg S f) = ∑ T ∈ S.powerset, fhat f T ^ 2 := by
  have h : avg S f = ∑ T, (if T ⊆ S then fhat f T else 0) • chi T := by
    funext x; rw [avg_expansion, Finset.sum_apply]
    refine sum_congr rfl (fun T _ => ?_); split_ifs <;> simp
  rw [h, ip_self_sum]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun T => T ⊆ S)]
  have h0 : ∑ T ∈ univ.filter (fun T => ¬ T ⊆ S), (if T ⊆ S then fhat f T else 0) ^ 2 = 0 :=
    sum_eq_zero (fun T hT => by simp [(mem_filter.mp hT).2])
  rw [h0, add_zero]
  have hpow : univ.filter (fun T : Finset (Fin n) => T ⊆ S) = S.powerset := by ext T; simp
  rw [hpow]; exact sum_congr rfl (fun T hT => by simp [mem_powerset.mp hT])

/-! ### The fiber imbalance `β_S` in Fourier form -/

/-- Restriction to the bound set `S` (the projection `π_S`). -/
def piS (S : Finset (Fin n)) (x : Pt n) : S → Bool := fun i => x i

/-- `f = (−1)^R`. -/
def sgn (R : Finset (Pt n)) : RFun n := fun x => if x ∈ R then -1 else 1

lemma fib_eq (S : Finset (Fin n)) (x : Pt n) :
    fib S x = univ.filter (fun y => piS S y = piS S x) := by
  ext y; simp only [fib, mem_filter, mem_univ, true_and, piS]
  constructor
  · intro h; funext i; exact h i i.2
  · intro h i hi; exact congrFun h ⟨i, hi⟩

lemma card_fib (S : Finset (Fin n)) (x : Pt n) : (fib S x).card = 2 ^ (n - S.card) := by
  let e : {y // y ∈ fib S x} ≃ ({i // i ∉ S} → Bool) :=
    { toFun := fun y i => y.1 i.1
      invFun := fun g => ⟨fun i => if h : i ∈ S then x i else g ⟨i, h⟩, by
        simp only [fib, mem_filter, mem_univ, true_and]; intro i hi; simp [hi]⟩
      left_inv := fun y => by
        apply Subtype.ext; funext i
        by_cases hi : i ∈ S
        · have := (mem_filter.mp y.2).2 i hi; simp [hi, this]
        · simp [hi]
      right_inv := fun g => by funext i; simp [i.2] }
  have := Fintype.card_congr e
  simp only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool] at this
  rw [this]; congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

lemma uniform_piS (S : Finset (Fin n)) : UniformFibers (piS S) (2 ^ (n - S.card)) := by
  intro z
  -- every `z` is hit: extend it by `false` outside `S`
  let x : Pt n := fun i => if h : i ∈ S then z ⟨i, h⟩ else false
  have hx : piS S x = z := by funext i; simp [piS, x, i.2]
  rw [← hx, ← fib_eq]; exact card_fib S x

lemma sum_sgn_fib (S : Finset (Fin n)) (R : Finset (Pt n)) (x : Pt n) :
    ∑ y ∈ fib S x, sgn R y = (2 ^ (n - S.card) : ℝ) - 2 * W (piS S) R (piS S x) := by
  have hW : W (piS S) R (piS S x) = ((fib S x).filter (fun y => y ∈ R)).card := by
    unfold W; rw [fib_eq]; congr 1; ext y; simp [and_comm]
  rw [hW, show (2 : ℝ) ^ (n - S.card) = ((fib S x).card : ℝ) by rw [card_fib]; push_cast; rfl]
  unfold sgn
  rw [Finset.sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have := Finset.card_filter_add_card_filter_not (s := fib S x) (p := fun y => y ∈ R)
  rw [← this]; push_cast; ring

/-- `β_S = ‖P_S f‖₁`: `Σ_z |2 W_z − F| = Σ_x |P_S f(x)|` (dividing by `2^n`). -/
theorem betaSum_eq_L1 (S : Finset (Fin n)) (R : Finset (Pt n)) :
    (betaSum (piS S) (2 ^ (n - S.card)) R : ℝ) = ∑ x, |avg S (sgn R) x| := by
  have hF : (0 : ℝ) < 2 ^ (n - S.card) := by positivity
  have havg : ∀ x, avg S (sgn R) x
      = ((2 ^ (n - S.card) : ℝ) - 2 * W (piS S) R (piS S x)) / 2 ^ (n - S.card) := by
    intro x; unfold avg; rw [sum_sgn_fib, card_fib]; push_cast; ring
  simp_rw [havg]
  rw [← Finset.sum_fiberwise (s := univ) (g := piS S)]
  unfold betaSum; push_cast
  refine sum_congr rfl (fun z _ => ?_)
  rw [sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2])]
  rw [sum_const, nsmul_eq_mul]
  have hc : ((univ.filter (fun x => piS S x = z)).card : ℝ) = 2 ^ (n - S.card) := by
    exact_mod_cast uniform_piS S z
  rw [hc, abs_div, abs_of_pos hF]
  rw [show |(2 : ℝ) ^ (n - S.card) - 2 * W (piS S) R z| = |2 * (W (piS S) R z : ℝ) - 2 ^ (n - S.card)|
    from by rw [abs_sub_comm]]
  field_simp

/-- `β_S ≤ ‖P_S f‖₂ = (Σ_{T ⊆ S} f̂(T)²)^{1/2}` (Cauchy–Schwarz and Parseval). -/
theorem beta_le_L2 (S : Finset (Fin n)) (R : Finset (Pt n)) :
    (betaSum (piS S) (2 ^ (n - S.card)) R : ℝ) / 2 ^ n
      ≤ Real.sqrt (∑ T ∈ S.powerset, fhat (sgn R) T ^ 2) := by
  rw [betaSum_eq_L1, ← norm2_avg]
  apply Real.le_sqrt_of_sq_le
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => |avg S (sgn R) x|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, sq_abs] at hcs
  unfold ip
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_pow, div_le_div_iff₀ (by positivity) h2]
  push_cast at hcs
  calc (∑ x, |avg S (sgn R) x|) ^ 2 * 2 ^ n ≤ (∑ x, avg S (sgn R) x ^ 2) * 2 ^ n * 2 ^ n := by
        nlinarith
    _ = (∑ x, avg S (sgn R) x * avg S (sgn R) x) * (2 ^ n) ^ 2 := by
        rw [sq]; simp_rw [← sq]; ring

/-- Fourier coefficients of `P_S f`: `f̂(T)` for `T ⊆ S`, `0` otherwise. -/
lemma fhat_avg (S T : Finset (Fin n)) (f : RFun n) :
    fhat (avg S f) T = if T ⊆ S then fhat f T else 0 := by
  have h : avg S f = ∑ U, (if U ⊆ S then fhat f U else 0) • chi U := by
    funext x; rw [avg_expansion, Finset.sum_apply]
    refine sum_congr rfl (fun U _ => ?_); split_ifs <;> simp
  rw [h, fhat_sum]

/-- `β_S = 0` for every `|S| = k` iff `f̂(T) = 0` for every `|T| ≤ k` (`k ≤ n`). -/
theorem beta_zero_iff (k : ℕ) (hk : k ≤ n) (R : Finset (Pt n)) :
    (∀ S : Finset (Fin n), S.card = k → betaSum (piS S) (2 ^ (n - S.card)) R = 0) ↔
    (∀ T : Finset (Fin n), T.card ≤ k → fhat (sgn R) T = 0) := by
  constructor
  · intro h T hT
    obtain ⟨S, hTS, hS⟩ := Finset.exists_superset_card_eq hT (by simpa using hk)
    have h0 := h S hS
    have hL1 : ∑ x, |avg S (sgn R) x| = 0 := by rw [← betaSum_eq_L1]; exact_mod_cast h0
    have hz : avg S (sgn R) = 0 := by
      funext x
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => abs_nonneg _)).mp hL1 x (mem_univ x)
      simpa using this
    have := fhat_avg S T (sgn R)
    rw [hz] at this; simp only [hTS, ite_true] at this
    rw [← this]; simp [fhat, ip]
  · intro h S hS
    have hz : ∀ x, avg S (sgn R) x = 0 := by
      intro x; rw [avg_expansion]
      refine sum_eq_zero (fun T _ => ?_)
      split_ifs with hT
      · rw [h T (hS ▸ Finset.card_le_card hT)]; ring
      · ring
    have := betaSum_eq_L1 S R
    simp only [hz, abs_zero, sum_const_zero] at this
    exact_mod_cast this

/-- Parity on the inputs `J`: its sign function is the character `χ_J`. -/
def parityR (J : Finset (Fin n)) : Finset (Pt n) := univ.filter (fun x => Odd (J.filter (fun i => x i = true)).card)

lemma sgn_parity (J : Finset (Fin n)) : sgn (parityR J) = chi J := by
  funext x; unfold sgn parityR chi
  by_cases h : Odd (J.filter (fun i => x i = true)).card
  · simp [h, h.neg_one_pow]
  · rw [Nat.not_odd_iff_even] at h; simp [Nat.not_odd_iff_even.mpr h, h.neg_one_pow]

/-- Parity examples: for parity on `J`, `β_S = 1` if `J ⊆ S` and `β_S = 0` otherwise. In particular,
at `k = 5`, parity on 5 variables has `β = 1` on its own support (and is removed in one majority step,
`card_after_maj_beta`), whereas parity on 6 variables has `β = 0` for every `|S| = 5`. -/
theorem beta_parity (J S : Finset (Fin n)) :
    (betaSum (piS S) (2 ^ (n - S.card)) (parityR J) : ℝ) = if J ⊆ S then 2 ^ n else 0 := by
  rw [betaSum_eq_L1, sgn_parity]
  simp_rw [avg_chi]
  split_ifs with h
  · simp_rw [show ∀ x : Pt n, |chi J x| = 1 from fun x => by
      unfold chi; rw [abs_pow, abs_neg, abs_one, one_pow]]
    simp
  · simp

lemma card_Z_F (S : Finset (Fin n)) :
    (Fintype.card (S → Bool) : ℤ) * ((2 ^ (n - S.card) : ℕ) : ℤ) = 2 ^ n := by
  have hS : S.card ≤ n := by simpa using card_le_univ S
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]; push_cast
  rw [← pow_add, Nat.add_sub_cancel' hS]

/-- The majority step on `S` applied to parity on `J`: if `J ⊆ S` it removes the residual in one
step; otherwise the residual after the step has weight `2^(n-1)`. -/
theorem parity_maj_step (J S : Finset (Fin n)) :
    2 * ((parityR J ∆ overSet (piS S) (majSet (piS S) (2 ^ (n - S.card)) (parityR J))).card : ℤ)
      = if J ⊆ S then 0 else 2 ^ n := by
  rw [card_after_maj_beta _ _ (uniform_piS S), card_Z_F]
  have hb := beta_parity J S
  by_cases h : J ⊆ S
  · rw [if_pos h] at hb ⊢
    have : betaSum (piS S) (2 ^ (n - S.card)) (parityR J) = 2 ^ n := by exact_mod_cast hb
    rw [this]; ring
  · rw [if_neg h] at hb ⊢
    have : betaSum (piS S) (2 ^ (n - S.card)) (parityR J) = 0 := by exact_mod_cast hb
    rw [this]; ring

end Llrg.Fourier
