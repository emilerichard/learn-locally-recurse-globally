/-
§3: strided positional encoding `strd(r, j) = r · m_max + j`.
It is injective on cells `(r, j)` with `j < m_max`, does not depend on `n` or `m`, and a table with
fewer rows or fewer outputs keeps, for each of its cells, the index it has in the full table.
-/
import Mathlib

namespace Llrg

/-- Position of cell (row `r`, output `j`). -/
def strd (mmax r j : ℕ) : ℕ := r * mmax + j

/-- Distinct cells get distinct positions. -/
theorem strd_injective (mmax : ℕ) {r j r' j' : ℕ} (hj : j < mmax) (hj' : j' < mmax)
    (h : strd mmax r j = strd mmax r' j') : r = r' ∧ j = j' := by
  unfold strd at h
  have hpos : 0 < mmax := by omega
  have h1 : (r * mmax + j) / mmax = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, zero_add]
  have h2 : (r' * mmax + j') / mmax = r' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj', zero_add]
  have hr : r = r' := by rw [← h1, ← h2, h]
  subst hr; exact ⟨rfl, by omega⟩

/-- Positions of a table with `n` inputs and `m ≤ m_max` outputs lie below `2^n · m_max`, which is
the encoder budget (`2^5 · 5 = 160` positions for `n, m ≤ 5`). -/
theorem strd_lt (mmax n r j : ℕ) (hr : r < 2 ^ n) (hj : j < mmax) :
    strd mmax r j < 2 ^ n * mmax := by
  unfold strd
  calc r * mmax + j < r * mmax + mmax := by omega
    _ = (r + 1) * mmax := by ring
    _ ≤ 2 ^ n * mmax := Nat.mul_le_mul_right _ hr

/-- A table over fewer inputs occupies the leading rows: its positions are a prefix-closed subset
of those of the full table, and every cell keeps its index (the index does not involve `n`). -/
theorem strd_sub (mmax n n' r j : ℕ) (hn : n' ≤ n) (hr : r < 2 ^ n') (hj : j < mmax) :
    strd mmax r j < 2 ^ n * mmax :=
  strd_lt mmax n r j (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hn)) hj

end Llrg
