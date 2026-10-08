/-
Remark `rm_floor`, parts (i)–(ii): every correction of the projection loop is a `k`-junta; the
`GF(2)`-span of `k`-juntas is the Reed–Muller code `RM(k, n)`; hence, for any selector and step
budget, the pre-completion residual differs from `R_0` by a codeword of `RM(k, n)`, and its weight
is at least `d(R_0, RM(k, n))`.
-/
import LlrgLean.ReedMuller

open Finset

namespace Llrg

variable {n : ℕ}

/-- `f` depends only on the inputs in `S`. -/
def IsJuntaOn (S : Finset (Fin n)) (f : (Fin n → Bool) → ZMod 2) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

/-- `RM(k, n)`: functions whose Reed–Muller coefficients vanish on sets of more than `k` inputs. -/
def RM (k : ℕ) : Set ((Fin n → Bool) → ZMod 2) := {f | ∀ U, k < U.card → rmCoef f U = 0}

lemma pt_symmDiff_single (T : Finset (Fin n)) (i : Fin n) (j : Fin n) (hj : j ≠ i) :
    pt (symmDiff T {i}) j = pt T j := by
  simp [pt, Finset.mem_symmDiff, hj]

/-- A junta on `S` has no Reed–Muller coefficient outside the subsets of `S`. -/
theorem rmCoef_junta (S : Finset (Fin n)) (f : (Fin n → Bool) → ZMod 2) (hf : IsJuntaOn S f)
    (U : Finset (Fin n)) (hU : ¬ U ⊆ S) : rmCoef f U = 0 := by
  obtain ⟨i, hiU, hiS⟩ := Finset.not_subset.mp hU
  unfold rmCoef
  refine Finset.sum_involution (fun T _ => symmDiff T {i}) (fun T hT => ?_) (fun T hT _ => ?_)
    (fun T hT => ?_) (fun T hT => ?_)
  · -- paired terms are equal, so they cancel in GF(2)
    have : f (pt (symmDiff T {i})) = f (pt T) :=
      hf _ _ (fun j hj => pt_symmDiff_single T i j (fun h => hiS (h ▸ hj)))
    rw [this, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  · intro h
    have : i ∈ symmDiff T {i} ↔ i ∈ T := by rw [h]
    simp [Finset.mem_symmDiff] at this
  · rw [mem_powerset] at hT ⊢
    intro j hj
    rcases Finset.mem_symmDiff.mp hj with ⟨hjT, _⟩ | ⟨hji, _⟩
    · exact hT hjT
    · rw [mem_singleton.mp hji]; exact hiU
  · ext j; simp only [Finset.mem_symmDiff, mem_singleton]; tauto

/-- (i) Every junta on at most `k` inputs is in `RM(k, n)`. -/
theorem junta_mem_RM (k : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ k)
    (f : (Fin n → Bool) → ZMod 2) (hf : IsJuntaOn S f) : f ∈ RM k := by
  intro U hU
  exact rmCoef_junta S f hf U (fun hsub => by
    have := Finset.card_le_card hsub; omega)

/-- (i, converse) Every monomial of degree at most `k` is a junta on at most `k` inputs. -/
theorem mono_junta (U : Finset (Fin n)) : IsJuntaOn U (mono U) := by
  intro x y h; unfold mono
  congr 1; exact propext ⟨fun hx i hi => (h i hi) ▸ hx i hi, fun hy i hi => (h i hi).symm ▸ hy i hi⟩

lemma rmCoef_add (f g : (Fin n → Bool) → ZMod 2) : rmCoef (f + g) = rmCoef f + rmCoef g := by
  funext U; simp [rmCoef, Finset.sum_add_distrib]

/-- `RM(k, n)` is closed under XOR. -/
theorem RM_add {k : ℕ} {f g : (Fin n → Bool) → ZMod 2} (hf : f ∈ RM k) (hg : g ∈ RM k) :
    f + g ∈ RM k := by
  intro U hU; rw [rmCoef_add]; simp [hf U hU, hg U hU]

lemma zero_mem_RM (k : ℕ) : (0 : (Fin n → Bool) → ZMod 2) ∈ RM k := by
  intro U _; simp [rmCoef]

/-- Hamming weight of a `GF(2)`-valued table. -/
def wt (f : (Fin n → Bool) → ZMod 2) : ℕ := (univ.filter (fun x => f x ≠ 0)).card

/-- (ii) For any sequence of corrections that are `k`-juntas (any operator, any selector, any
step budget), the final residual differs from `R_0` by an element of `RM(k, n)`; hence its weight
is at least the distance from `R_0` to `RM(k, n)`. -/
theorem residual_floor (k : ℕ) (R₀ : (Fin n → Bool) → ZMod 2)
    (cs : List ((Fin n → Bool) → ZMod 2))
    (hcs : ∀ c ∈ cs, ∃ S : Finset (Fin n), S.card ≤ k ∧ IsJuntaOn S c) :
    (∃ c ∈ RM k, R₀ + cs.sum = R₀ + c) ∧
    ∀ d, (∀ c ∈ RM k, d ≤ wt (R₀ + c)) → d ≤ wt (R₀ + cs.sum) := by
  have hsum : cs.sum ∈ RM (n := n) k := by
    induction cs with
    | nil => exact zero_mem_RM k
    | cons c cs ih =>
      rw [List.sum_cons]
      obtain ⟨S, hS, hj⟩ := hcs c List.mem_cons_self
      exact RM_add (junta_mem_RM k S hS c hj) (ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')))
  exact ⟨⟨cs.sum, hsum, rfl⟩, fun d hd => hd cs.sum hsum⟩

end Llrg
