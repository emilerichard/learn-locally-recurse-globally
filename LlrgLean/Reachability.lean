/-
Theorem `dichotomy` (reachability under marginal–XOR recursion), majority marginal.
(a) A residual of weight at most F/2 admits no progress for any bound set; in particular a single
    minterm (the residual of a wide conjunction) is a fixed point.
(b) One step on a block: rows are `A × B` (the block `A` and the remaining inputs `B`), the
    target is `g(a) ⊕ h(b)`, and the bound set is the block (projection `Prod.fst`, fibers of
    size `|B|`). The majority step removes the block exactly (up to complement of the remainder).
-/
import LlrgLean.Marginals

set_option linter.unusedSectionVars false

open scoped symmDiff
open Finset

namespace Llrg

section Small
variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

lemma W_le_card (π : X → Z) (R : Finset X) (z : Z) : W π R z ≤ R.card :=
  card_filter_le _ _

/-- Theorem `dichotomy` (a): if `2|R| ≤ F`, no fiber is majority-set, the gain is zero for every
bound set, and the majority step leaves the residual unchanged. -/
theorem no_progress_of_small (π : X → Z) (F : ℕ) (R : Finset X) (h : 2 * R.card ≤ F) :
    majSet π F R = ∅ ∧ gain π F R = 0 ∧ R ∆ overSet π (majSet π F R) = R := by
  have hm : majSet π F R = ∅ := by
    ext z
    simp only [majSet, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
    have := W_le_card π R z; omega
  refine ⟨hm, by simp [gain, hm], ?_⟩
  rw [hm]; ext x; simp [overSet, Finset.mem_symmDiff]

/-- The residual of a wide conjunction is a single minterm; when fibers have at least two cells
(bound set smaller than the support), it is a fixed point of the majority loop. -/
theorem minterm_fixed (π : X → Z) (F : ℕ) (hF2 : 2 ≤ F) (x₀ : X) :
    ({x₀} : Finset X) ∆ overSet π (majSet π F {x₀}) = {x₀} :=
  (no_progress_of_small π F {x₀} (by simpa using hF2)).2.2

end Small

section Block
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Residual of the target `g(a) ⊕ h(b)` on `A × B`. -/
def xorTarget (g : Finset A) (h : Finset B) : Finset (A × B) :=
  univ.filter (fun p => (p.1 ∈ g) ≠ (p.2 ∈ h))

lemma uniform_fst : UniformFibers (Prod.fst : A × B → A) (Fintype.card B) := by
  intro a
  rw [show (univ.filter fun p : A × B => p.1 = a) = ({a} : Finset A) ×ˢ (univ : Finset B) by
    ext p; simp [Prod.ext_iff, eq_comm]]
  simp

lemma W_xorTarget (g : Finset A) (h : Finset B) (a : A) :
    W Prod.fst (xorTarget g h) a = if a ∈ g then Fintype.card B - h.card else h.card := by
  unfold W xorTarget
  rw [filter_filter]
  split_ifs with ha
  · rw [show (univ.filter fun p : A × B => (p.1 ∈ g) ≠ (p.2 ∈ h) ∧ p.1 = a)
        = ({a} : Finset A) ×ˢ (univ \ h) by
        ext p; simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, mem_sdiff]
        constructor
        · rintro ⟨h1, rfl⟩; exact ⟨rfl, by simpa [ha] using h1⟩
        · rintro ⟨rfl, h2⟩; exact ⟨by simp [ha, h2], rfl⟩]
    simp [card_sdiff_of_subset (subset_univ h)]
  · rw [show (univ.filter fun p : A × B => (p.1 ∈ g) ≠ (p.2 ∈ h) ∧ p.1 = a)
        = ({a} : Finset A) ×ˢ h by
        ext p; simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
        constructor
        · rintro ⟨h1, rfl⟩; exact ⟨rfl, by simpa [ha] using h1⟩
        · rintro ⟨rfl, h2⟩; exact ⟨by simp [ha, h2], rfl⟩]
    simp

/-- Theorem `dichotomy` (b), one step, remainder of density below 1/2: the majority marginal on
the block is exactly `g`, the residual becomes `h` on the remaining inputs, and the gain is
`|g| · F · (1 − 2μ)` with `F = |B|`, `μ = |h|/|B|`. -/
theorem block_step_lt (g : Finset A) (h : Finset B) (hμ : 2 * h.card < Fintype.card B) :
    majSet Prod.fst (Fintype.card B) (xorTarget g h) = g ∧
    xorTarget g h ∆ overSet Prod.fst g = (univ : Finset A) ×ˢ h ∧
    gain Prod.fst (Fintype.card B) (xorTarget g h)
      = g.card * ((Fintype.card B : ℤ) - 2 * h.card) := by
  have hm : majSet Prod.fst (Fintype.card B) (xorTarget g h) = g := by
    ext a; simp only [majSet, mem_filter, mem_univ, true_and, W_xorTarget]
    split_ifs with ha <;> simp only [ha, iff_true, iff_false] <;> omega
  refine ⟨hm, ?_, ?_⟩
  · ext p; simp only [xorTarget, overSet, Finset.mem_symmDiff, mem_filter, mem_univ, true_and,
      mem_product]
    by_cases h1 : p.1 ∈ g <;> by_cases h2 : p.2 ∈ h <;> simp [h1, h2]
  · rw [gain, hm, sum_congr rfl (fun a ha => by rw [W_xorTarget, if_pos ha])]
    have hle : h.card ≤ Fintype.card B := card_le_univ h
    simp only [sum_const, nsmul_eq_mul]; push_cast [Nat.cast_sub hle]; ring

/-- Theorem `dichotomy` (b), one step, remainder of density above 1/2: the majority marginal is
the complement of `g`, the residual becomes the complement of `h`, and the gain is
`(|A| − |g|) · F · (2μ − 1)`. The number of flipped fibers is `|A| − |g|`, not `|g|`. -/
theorem block_step_gt (g : Finset A) (h : Finset B) (hμ : Fintype.card B < 2 * h.card) :
    majSet Prod.fst (Fintype.card B) (xorTarget g h) = univ \ g ∧
    xorTarget g h ∆ overSet Prod.fst (univ \ g) = (univ : Finset A) ×ˢ (univ \ h) ∧
    gain Prod.fst (Fintype.card B) (xorTarget g h)
      = ((Fintype.card A : ℤ) - g.card) * (2 * h.card - Fintype.card B) := by
  have hle : h.card ≤ Fintype.card B := card_le_univ h
  have hm : majSet Prod.fst (Fintype.card B) (xorTarget g h) = univ \ g := by
    ext a; simp only [majSet, mem_filter, mem_univ, true_and, W_xorTarget, mem_sdiff]
    have hsub := Nat.sub_add_cancel hle
    split_ifs with ha <;> simp only [ha, not_true, not_false_eq_true, iff_false, iff_true, not_lt]
      <;> omega
  refine ⟨hm, ?_, ?_⟩
  · ext p; simp only [xorTarget, overSet, Finset.mem_symmDiff, mem_filter, mem_univ, true_and,
      mem_product, mem_sdiff]
    by_cases h1 : p.1 ∈ g <;> by_cases h2 : p.2 ∈ h <;> simp [h1, h2]
  · rw [gain, hm, sum_congr rfl (fun a ha => by
      rw [W_xorTarget, ite_eq_right_iff.mpr (fun h' => absurd h' (by simpa using (mem_sdiff.mp ha).2))])]
    have hg : (univ \ g).card = Fintype.card A - g.card := by
      rw [card_sdiff_of_subset (subset_univ g), card_univ]
    simp only [sum_const, nsmul_eq_mul, hg]
    push_cast [Nat.cast_sub (card_le_univ g)]; ring

/-- Exactly balanced remainder: no fiber is majority-set and the loop stalls on this block. -/
theorem block_step_eq (g : Finset A) (h : Finset B) (hμ : 2 * h.card = Fintype.card B) :
    majSet Prod.fst (Fintype.card B) (xorTarget g h) = ∅ := by
  ext a; simp only [majSet, mem_filter, mem_univ, true_and, W_xorTarget, Finset.notMem_empty,
    iff_false]
  split_ifs <;> omega

end Block

end Llrg
