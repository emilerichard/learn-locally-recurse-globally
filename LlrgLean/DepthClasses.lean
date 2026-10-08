/-
Appendix H: the generator's depth-`q` classes `G_q(N)`.
Depth-1 gates take distinct inputs (bare inputs occur at depth 1 only when `N < 4`, through draws
with replacement); deeper gates take independently drawn operands of depth `q − 1`.
-/
import Mathlib

open Finset

namespace Llrg

abbrev BFun (N : ℕ) := (Fin N → Bool) → Bool

/-- `G N q f`: the generator can produce `f` (one output, `N` inputs) at depth `q`. -/
inductive G (N : ℕ) : ℕ → BFun N → Prop
  | inv1 (i : Fin N) : G N 1 (fun x => !x i)
  | and1 (S : Finset (Fin N)) (h2 : 2 ≤ S.card) (h4 : S.card ≤ 4) :
      G N 1 (fun x => decide (∀ i ∈ S, x i = true))
  | or1 (S : Finset (Fin N)) (h2 : 2 ≤ S.card) (h4 : S.card ≤ 4) :
      G N 1 (fun x => decide (∃ i ∈ S, x i = true))
  | xor1 (i j : Fin N) (hij : i ≠ j) : G N 1 (fun x => xor (x i) (x j))
  | var1 (i : Fin N) (hN : N < 4) : G N 1 (fun x => x i)
  | inv (q : ℕ) (f : BFun N) : G N q f → G N (q + 1) (fun x => !f x)
  | and (q : ℕ) (fs : List (BFun N)) (h1 : 1 ≤ fs.length) (h4 : fs.length ≤ 4)
      (hfs : ∀ f ∈ fs, G N q f) : G N (q + 1) (fun x => fs.all (fun f => f x))
  | or (q : ℕ) (fs : List (BFun N)) (h1 : 1 ≤ fs.length) (h4 : fs.length ≤ 4)
      (hfs : ∀ f ∈ fs, G N q f) : G N (q + 1) (fun x => fs.any (fun f => f x))
  | xor (q : ℕ) (f g : BFun N) : G N q f → G N q g → G N (q + 1) (fun x => xor (f x) (g x))

variable {N : ℕ}

/-- Nesting `G_q ⊆ G_{q+1}`: an AND with a single (repeated) operand. -/
theorem G_mono {q : ℕ} {f : BFun N} (h : G N q f) : G N (q + 1) f := by
  have := G.and q [f] (by simp) (by simp) (by simpa using h)
  simpa using this

theorem G_mono_le {q q' : ℕ} (hq : q ≤ q') {f : BFun N} (h : G N q f) : G N q' f := by
  induction hq with
  | refl => exact h
  | step _ ih => exact G_mono ih

/-- Outputs are drawn independently: the number of `m`-output functions whose outputs all lie in a
finite class `A` is `|A|^m`. -/
theorem card_multi_output {α : Type*} [DecidableEq α] (A : Finset α) (m : ℕ) :
    Fintype.card (Fin m → A) = A.card ^ m := by
  simp [Fintype.card_fun]

/-- The last input `x_N` and its negation are in `G_3` on `N + 1` inputs. -/
theorem last_var_G3 : G (N + 1) 3 (fun x => x (Fin.last N)) ∧
    G (N + 1) 3 (fun x => !x (Fin.last N)) := by
  have h1 := G.inv1 (N := N + 1) (Fin.last N)
  have h2 : G (N + 1) 2 (fun x => x (Fin.last N)) := by
    simpa using G.inv 1 _ h1
  exact ⟨G_mono h2, by simpa using G.inv 2 _ h2⟩

/-- `f` does not depend on the last input. -/
def IgnoresLast (f : BFun (N + 1)) : Prop :=
  ∀ x y, (∀ i : Fin N, x i.castSucc = y i.castSucc) → f x = f y

/-- Shannon expansion on the last input: if every function of `N + 1` inputs that ignores the last
one is in `G_q`, and `x_N`, `¬x_N` are in `G_q`, then every function of `N + 1` inputs is in
`G_{q+2}`: `f = (x_N ∧ f₁) ∨ (¬x_N ∧ f₀)`. -/
theorem shannon_step (q : ℕ)
    (hall : ∀ f : BFun (N + 1), IgnoresLast f → G (N + 1) q f)
    (hx : G (N + 1) q (fun x => x (Fin.last N))) (hnx : G (N + 1) q (fun x => !x (Fin.last N)))
    (f : BFun (N + 1)) : G (N + 1) (q + 2) f := by
  let f1 : BFun (N + 1) := fun x => f (Function.update x (Fin.last N) true)
  let f0 : BFun (N + 1) := fun x => f (Function.update x (Fin.last N) false)
  have hign : ∀ b : Bool, IgnoresLast (fun x => f (Function.update x (Fin.last N) b)) := by
    intro b x y h
    apply congrArg f; funext i
    by_cases hi : i = Fin.last N
    · rw [hi]; simp only [Function.update_self]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      simp [h j]
  have a1 : G (N + 1) (q + 1) (fun x => [fun x => x (Fin.last N), f1].all (fun g => g x)) :=
    G.and q _ (by simp) (by simp) (by
      intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hx
      · exact hall _ (hign true))
  have a0 : G (N + 1) (q + 1) (fun x => [fun x => !x (Fin.last N), f0].all (fun g => g x)) :=
    G.and q _ (by simp) (by simp) (by
      intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hnx
      · exact hall _ (hign false))
  have o := G.or (q + 1) [_, _] (by simp) (by simp) (by
    intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact a1
    · exact a0)
  convert o using 1
  funext x
  simp only [List.all_cons, List.all_nil, Bool.and_true, List.any_cons, List.any_nil,
    Bool.or_false, f1, f0]
  cases hxl : x (Fin.last N)
  · simp [show Function.update x (Fin.last N) false = x by
      funext i; by_cases hi : i = Fin.last N
      · subst hi; simp [hxl]
      · simp [Function.update_of_ne hi]]
  · simp [show Function.update x (Fin.last N) true = x by
      funext i; by_cases hi : i = Fin.last N
      · subst hi; simp [hxl]
      · simp [Function.update_of_ne hi]]

/-- Restriction of an input of `N + 1` variables to the first `N`. -/
def restr (x : Fin (N + 1) → Bool) : Fin N → Bool := fun i => x i.castSucc

/-- A construction on `N ≥ 4` inputs is a construction on `N + 1` inputs that ignores the last
(for `N ≥ 4`, depth-1 gates never reduce to a bare input). -/
theorem G_embed (hN : 4 ≤ N) {q : ℕ} {f : BFun N} (h : G N q f) :
    G (N + 1) q (fun x => f (restr x)) := by
  induction h with
  | inv1 i => exact G.inv1 i.castSucc
  | and1 S h2 h4 =>
    have := G.and1 (S.map Fin.castSuccEmb) (by simpa using h2) (by simpa using h4)
    convert this using 1; funext x; simp only [restr, Finset.mem_map, Fin.coe_castSuccEmb,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact decide_eq_decide.mpr Iff.rfl
  | or1 S h2 h4 =>
    have := G.or1 (S.map Fin.castSuccEmb) (by simpa using h2) (by simpa using h4)
    convert this using 1; funext x; simp only [restr, Finset.mem_map, Fin.coe_castSuccEmb,
      exists_exists_and_eq_and]
    exact decide_eq_decide.mpr Iff.rfl
  | xor1 i j hij =>
    exact G.xor1 i.castSucc j.castSucc (fun h => hij (Fin.castSucc_injective _ h))
  | var1 i hN' => omega
  | inv q f _ ih => exact G.inv q _ ih
  | and q fs h1 h4 _ ih =>
    have := G.and q (fs.map (fun f x => f (restr x))) (by simpa using h1) (by simpa using h4)
      (by intro g hg; obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg; exact ih f hf)
    convert this using 1; funext x; simp [List.all_map, Function.comp_def]
  | or q fs h1 h4 _ ih =>
    have := G.or q (fs.map (fun f x => f (restr x))) (by simpa using h1) (by simpa using h4)
      (by intro g hg; obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg; exact ih f hf)
    convert this using 1; funext x; simp [List.any_map, Function.comp_def]
  | xor q f g _ _ ihf ihg => exact G.xor q _ _ ihf ihg

/-- Appendix H: if every function of `4` inputs has depth at most `3` (computed: `|G_3(4)| = 2^16`),
then every function of `5` inputs has depth at most `5`. -/
theorem all_G5_of_all_G3 (h4 : ∀ f : BFun 4, G 4 3 f) (f : BFun 5) : G 5 5 f := by
  refine shannon_step (N := 4) 3 (fun g hg => ?_) last_var_G3.1 last_var_G3.2 f
  -- `g` ignores the last input, so it is `g₀ ∘ restr` for a function `g₀` of `4` inputs
  let g0 : BFun 4 := fun y => g (Fin.snoc y false)
  have hg' : (fun x => g0 (restr x)) = g := by
    funext x; apply hg; intro i; simp [restr, Fin.snoc_castSucc]
  rw [← hg']
  exact G_embed (by norm_num) (h4 g0)

end Llrg
