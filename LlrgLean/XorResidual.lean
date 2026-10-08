/-
Proposition 2.1 (XOR residual decomposition).

Truth tables over a finite set of cells `C` (rows × outputs, so `card C = m * 2^n`) are
identified with the set of cells equal to 1; pointwise XOR is symmetric difference `∆` and the
Hamming weight is the cardinality.
-/
import Mathlib

open scoped symmDiff

namespace Llrg

variable {C : Type*} [DecidableEq C]

/-- `g = h ⊕ r` exactly, where `r = g ⊕ h` is the residual of the approximation `h`. -/
theorem xor_residual (g h : Finset C) : g = h ∆ (g ∆ h) := by
  rw [symmDiff_comm g h, symmDiff_symmDiff_cancel_left]

/-- Accumulated XOR of the corrections `h 1, …, h t`. -/
def acc (h : ℕ → Finset C) : ℕ → Finset C
  | 0 => ∅
  | t + 1 => acc h t ∆ h (t + 1)

/-- Residual after `t` corrections, starting from the target `g`. -/
def resid (g : Finset C) (h : ℕ → Finset C) : ℕ → Finset C
  | 0 => g
  | t + 1 => resid g h t ∆ h (t + 1)

/-- Telescoping: after any number of steps, `g = (h_1 ⊕ ⋯ ⊕ h_t) ⊕ r_t`. -/
theorem target_eq_acc_xor_resid (g : Finset C) (h : ℕ → Finset C) (t : ℕ) :
    g = acc h t ∆ resid g h t := by
  induction t with
  | zero => ext x; simp [acc, resid, Finset.mem_symmDiff]
  | succ t ih =>
    have key : (acc h t ∆ h (t + 1)) ∆ (resid g h t ∆ h (t + 1)) = acc h t ∆ resid g h t := by
      ext x; simp only [Finset.mem_symmDiff]; tauto
    simp only [acc, resid]
    rw [key]
    exact ih

/-- If every step strictly decreases the Hamming weight of the residual, the number of steps is
bounded by the weight of the target. -/
theorem steps_le_weight (g : Finset C) (h : ℕ → Finset C) (T : ℕ)
    (hdec : ∀ t < T, (resid g h (t + 1)).card < (resid g h t).card) :
    (resid g h T).card + T ≤ g.card := by
  induction T with
  | zero => simp [resid]
  | succ T ih =>
    have h1 := ih (fun t ht => hdec t (Nat.lt_succ_of_lt ht))
    have h2 := hdec T (Nat.lt_succ_self T)
    omega

/-- Proposition 2.1, step bound: with cells `C` (`card C = m * 2^n`), at most `card C` steps that
each strictly decrease the residual weight can be taken. -/
theorem steps_le_card [Fintype C] (g : Finset C) (h : ℕ → Finset C) (T : ℕ)
    (hdec : ∀ t < T, (resid g h (t + 1)).card < (resid g h t).card) :
    T ≤ Fintype.card C := by
  have := steps_le_weight g h T hdec
  have hg : g.card ≤ Fintype.card C := Finset.card_le_univ g
  omega

/-- The bound is reached only if the residual is empty: after `card g` decreasing steps the
residual is exactly zero, i.e. synthesis is exact. -/
theorem resid_empty_of_steps (g : Finset C) (h : ℕ → Finset C)
    (hdec : ∀ t < g.card, (resid g h (t + 1)).card < (resid g h t).card) :
    resid g h g.card = ∅ := by
  have := steps_le_weight g h g.card hdec
  exact Finset.card_eq_zero.mp (by omega)

end Llrg
