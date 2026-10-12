/-
§2.2: every Boolean function has a unique Reed–Muller expansion, an XOR of monomials
`x_S = ∧_{i ∈ S} x_i`, and the coefficient of `x_S` is the XOR of `f` over the inputs whose
1-positions lie in `S`.
-/
import Mathlib

open Finset

namespace Llrg

variable {n : ℕ}

/-- The input whose 1-positions are `T`. -/
def pt (T : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ T)

/-- The monomial `x_S`, with values in `GF(2)`. -/
def mono (S : Finset (Fin n)) (x : Fin n → Bool) : ZMod 2 := if ∀ i ∈ S, x i = true then 1 else 0

/-- Value of the expansion with coefficients `a`. -/
def rmEval (a : Finset (Fin n) → ZMod 2) (x : Fin n → Bool) : ZMod 2 := ∑ S, a S * mono S x

/-- The coefficient formula: `a_S = Σ_{T ⊆ S} f(1_T)` in `GF(2)`. -/
def rmCoef (f : (Fin n → Bool) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 := ∑ T ∈ S.powerset, f (pt T)

lemma mono_pt (S T : Finset (Fin n)) : mono S (pt T) = if S ⊆ T then 1 else 0 := by
  unfold mono pt; simp [Finset.subset_iff]

lemma two_pow_zmod (k : ℕ) : ((2 : ZMod 2) ^ k) = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k => simp [pow_succ, show (2 : ZMod 2) = 0 from rfl]

/-- The coefficient formula inverts the expansion. -/
theorem rmCoef_rmEval (a : Finset (Fin n) → ZMod 2) : rmCoef (rmEval a) = a := by
  funext S
  unfold rmCoef rmEval
  simp_rw [mono_pt, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  -- for each `U`, count the `T` with `U ⊆ T ⊆ S`
  have hcount : ∀ U : Finset (Fin n),
      (∑ T ∈ S.powerset, if U ⊆ T then a U else 0) = if U = S then a U else 0 := by
    intro U
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hUS : U ⊆ S
    · have hfilt : S.powerset.filter (fun T => U ⊆ T) = Finset.Icc U S := by
        ext T; simp [Finset.mem_Icc, and_comm]
      rw [hfilt, Finset.card_Icc_finset hUS]
      push_cast
      rw [two_pow_zmod]
      by_cases hEq : U = S
      · subst hEq; simp
      · have : S.card - U.card ≠ 0 := by
          have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hUS, hEq⟩); omega
        simp [this, hEq]
    · have hfilt : S.powerset.filter (fun T => U ⊆ T) = ∅ := by
        ext T; simp only [mem_filter, mem_powerset, Finset.notMem_empty, iff_false, not_and]
        exact fun hTS hUT => hUS (hUT.trans hTS)
      rw [hfilt]; simp [show U ≠ S from fun h => hUS (h ▸ subset_refl _)]
  rw [Finset.sum_congr rfl (fun U _ => hcount U)]
  simp

/-- Uniqueness: two expansions computing the same function have the same coefficients. -/
theorem rmEval_injective : Function.Injective (rmEval (n := n)) := by
  intro a b h
  rw [← rmCoef_rmEval a, ← rmCoef_rmEval b, h]

/-- Existence: every Boolean function is computed by the expansion whose coefficients are given
by the formula, i.e. the `2^n` monomials span the functions. -/
theorem rmEval_rmCoef (f : (Fin n → Bool) → ZMod 2) : rmEval (rmCoef f) = f := by
  have hbij : Function.Bijective (rmEval (n := n)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨rmEval_injective, ?_⟩
    simp [Fintype.card_fun, Fintype.card_finset]
  obtain ⟨a, rfl⟩ := hbij.2 f
  rw [rmCoef_rmEval]

/-- §2.2: existence and uniqueness of the Reed–Muller expansion, with its coefficient formula. -/
theorem reed_muller (f : (Fin n → Bool) → ZMod 2) :
    ∃! a : Finset (Fin n) → ZMod 2, rmEval a = f ∧ ∀ S, a S = ∑ T ∈ S.powerset, f (pt T) :=
  ⟨rmCoef f, ⟨rmEval_rmCoef f, fun _ => rfl⟩,
    fun a ha => by rw [← ha.1, rmCoef_rmEval]⟩

end Llrg
