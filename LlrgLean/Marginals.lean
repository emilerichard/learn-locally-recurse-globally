/-
Projection marginals (Appendix B and F): fibers, the effect of flipping fibers, the parity and
majority marginals, and Proposition `gain` (progress criterion for the majority marginal).

Rows are a finite type `X`; the projection onto a bound set is any map `π : X → Z` whose fibers
all have the same size `F` (for `π_S` on `{0,1}^n`: `Z = {0,1}^k`, `F = 2^{n-k}`). A residual is
the set `R : Finset X` of rows equal to 1 (one output column).
-/
import Mathlib

set_option linter.unusedSectionVars false

open scoped symmDiff
open Finset

namespace Llrg

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

lemma card_eq_sum_ind (s : Finset X) : (s.card : ℤ) = ∑ x, if x ∈ s then (1:ℤ) else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]; simp

/-- Cardinality of a symmetric difference. -/
lemma card_symmDiff_int (R T : Finset X) :
    ((R ∆ T).card : ℤ) = R.card + T.card - 2 * (R ∩ T).card := by
  rw [card_eq_sum_ind (R ∆ T), card_eq_sum_ind R, card_eq_sum_ind T, card_eq_sum_ind (R ∩ T),
    mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl (fun x _ => ?_)
  by_cases h1 : x ∈ R <;> by_cases h2 : x ∈ T <;> simp [Finset.mem_symmDiff, h1, h2]

/-- Weight of the residual on the fiber over `z`. -/
def W (π : X → Z) (R : Finset X) (z : Z) : ℕ := (R.filter (fun x => π x = z)).card

/-- The rows lying over a set of fibers (the support of the correction `g ∘ π`). -/
def overSet (π : X → Z) (Z' : Finset Z) : Finset X := univ.filter (fun x => π x ∈ Z')

/-- All fibers have size `F`. -/
def UniformFibers (π : X → Z) (F : ℕ) : Prop := ∀ z, (univ.filter (fun x => π x = z)).card = F

lemma sum_W (π : X → Z) (R : Finset X) : ∑ z, W π R z = R.card :=
  (card_eq_sum_card_fiberwise (f := π) (s := R) (t := univ) (fun x _ => by simp)).symm

lemma card_overSet (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (Z' : Finset Z) :
    (overSet π Z').card = Z'.card * F := by
  unfold overSet
  rw [card_eq_sum_card_fiberwise (f := π) (s := univ.filter (fun x => π x ∈ Z')) (t := Z')
    (fun x hx => by simpa using hx)]
  calc ∑ z ∈ Z', ((univ.filter (fun x => π x ∈ Z')).filter (fun x => π x = z)).card
      = ∑ z ∈ Z', F := sum_congr rfl (fun z hz => by
        rw [filter_filter, Finset.filter_congr (q := fun x => π x = z)
          (fun x _ => ⟨fun h => h.2, fun h => ⟨h ▸ hz, h⟩⟩)]; exact hF z)
    _ = Z'.card * F := by simp

lemma card_inter_overSet (π : X → Z) (R : Finset X) (Z' : Finset Z) :
    (R ∩ overSet π Z').card = ∑ z ∈ Z', W π R z := by
  rw [card_eq_sum_card_fiberwise (f := π) (s := R ∩ overSet π Z') (t := Z')
    (fun x hx => by simp only [coe_inter, Set.mem_inter_iff, mem_coe, overSet, mem_filter,
      mem_univ, true_and] at hx; exact hx.2)]
  refine sum_congr rfl (fun z hz => ?_)
  unfold W; congr 1; ext x
  simp only [mem_filter, mem_inter, overSet, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hz⟩, h2⟩

/-- Flipping every cell of the fibers in `Z'` changes the weight by `∑_{z ∈ Z'} (F − 2 W_z)`. -/
theorem card_flip (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (R : Finset X) (Z' : Finset Z) :
    ((R ∆ overSet π Z').card : ℤ) = R.card + ∑ z ∈ Z', ((F : ℤ) - 2 * W π R z) := by
  rw [card_symmDiff_int, card_inter_overSet, card_overSet π F hF, sum_sub_distrib, sum_const,
    nsmul_eq_mul, ← mul_sum]
  push_cast; ring

/-- Fibers flipped by the parity (GF(2)) marginal: odd fiber weight. -/
def parSet (π : X → Z) (R : Finset X) : Finset Z := univ.filter (fun z => Odd (W π R z))

/-- Fibers flipped by the majority marginal: more than half of the fiber is set. -/
def majSet (π : X → Z) (F : ℕ) (R : Finset X) : Finset Z :=
  univ.filter (fun z => F < 2 * W π R z)

/-- Appendix B, `Δw_par = Σ_{z : W_z odd} (F − 2 W_z)`. -/
theorem delta_par (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (R : Finset X) :
    ((R ∆ overSet π (parSet π R)).card : ℤ) - R.card
      = ∑ z ∈ parSet π R, ((F : ℤ) - 2 * W π R z) := by
  rw [card_flip π F hF]; ring

/-- Proposition `zero_drift` (ii): if every fiber weight is even, the parity marginal is zero and
the step leaves the residual unchanged. -/
theorem par_noop (π : X → Z) (R : Finset X) (heven : ∀ z, Even (W π R z)) :
    parSet π R = ∅ ∧ R ∆ overSet π (parSet π R) = R := by
  have h0 : parSet π R = ∅ := by
    ext z
    simp only [parSet, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact Nat.not_odd_iff_even.mpr (heven z)
  refine ⟨h0, ?_⟩
  rw [h0]; ext x; simp [overSet, Finset.mem_symmDiff]

/-- Appendix B, `Δw_maj = −Σ_z max(2 W_z − F, 0) ≤ 0`: the majority gain. -/
def gain (π : X → Z) (F : ℕ) (R : Finset X) : ℤ := ∑ z ∈ majSet π F R, (2 * (W π R z : ℤ) - F)

/-- `Σ_z |2 W_z − F| = 2^n β_S`. -/
def betaSum (π : X → Z) (F : ℕ) (R : Finset X) : ℤ := ∑ z, |2 * (W π R z : ℤ) - F|

/-- The majority step removes exactly `gain` cells. -/
theorem card_after_maj (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (R : Finset X) :
    ((R ∆ overSet π (majSet π F R)).card : ℤ) = R.card - gain π F R := by
  rw [card_flip π F hF, gain, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1; exact sum_congr rfl (fun z _ => by ring)

lemma gain_eq_sum_max (π : X → Z) (F : ℕ) (R : Finset X) :
    gain π F R = ∑ z, max (2 * (W π R z : ℤ) - F) 0 := by
  unfold gain majSet
  rw [sum_filter]
  refine sum_congr rfl (fun z _ => ?_)
  split_ifs with h
  · exact (max_eq_left (by omega)).symm
  · exact (max_eq_right (by omega)).symm

lemma gain_nonneg (π : X → Z) (F : ℕ) (R : Finset X) : 0 ≤ gain π F R := by
  rw [gain_eq_sum_max]; exact sum_nonneg (fun z _ => le_max_right _ _)

/-- Proposition `gain`, integer form: `2 · gain = (2w − 2^n) + 2^n β_S`, with `2^n = |Z| · F`.
Dividing by two: `gain = w − 2^{n−1}(1 − β_S)`. -/
theorem two_gain (π : X → Z) (F : ℕ) (R : Finset X) :
    2 * gain π F R = (2 * (R.card : ℤ) - Fintype.card Z * F) + betaSum π F R := by
  rw [gain_eq_sum_max, betaSum, mul_sum]
  have hsum : ∑ z : Z, (2 * (W π R z : ℤ) - F) = 2 * R.card - Fintype.card Z * F := by
    rw [sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, ← sum_W π R]
    push_cast; ring
  rw [← hsum, ← sum_add_distrib]
  refine sum_congr rfl (fun z _ => ?_)
  rcases le_total 0 (2 * (W π R z : ℤ) - F) with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

/-- Proposition `gain`, density after the step: `2 w' = 2^n − 2^n β_S`, i.e. `δ' = (1 − β_S)/2`,
independently of the density before the step. -/
theorem card_after_maj_beta (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (R : Finset X) :
    2 * ((R ∆ overSet π (majSet π F R)).card : ℤ) = Fintype.card Z * F - betaSum π F R := by
  rw [card_after_maj π F hF, mul_sub, two_gain π F R]; ring

/-- Proposition `gain`, progress criterion: the step makes progress iff `β_S > 1 − 2δ`,
i.e. `2^n β_S > 2^n − 2w`. -/
theorem progress_iff (π : X → Z) (F : ℕ) (R : Finset X) :
    0 < gain π F R ↔ (Fintype.card Z * F : ℤ) - 2 * R.card < betaSum π F R := by
  have := two_gain π F R; constructor <;> intro h <;> linarith

/-- Proposition `gain`, selection: between two bound sets with fibers of the same size and the
same number of fibers, the gain is larger iff `β` is larger. -/
theorem gain_le_iff {Z₂ : Type*} [Fintype Z₂] [DecidableEq Z₂]
    (π : X → Z) (π₂ : X → Z₂) (F : ℕ) (hZ : Fintype.card Z = Fintype.card Z₂) (R : Finset X) :
    gain π F R ≤ gain π₂ F R ↔ betaSum π F R ≤ betaSum π₂ F R := by
  have h1 := two_gain π F R; have h2 := two_gain π₂ F R
  rw [hZ] at h1; constructor <;> intro h <;> linarith

end Llrg

namespace Llrg

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- The majority marginal is zero on a zero residual column: if some fiber is majority-set, the
residual is non-empty. This is the hypothesis `hprop` of the size-test guarantee
(`project_le_fallback`) for the majority operator. -/
theorem nonempty_of_majSet_nonempty (π : X → Z) (F : ℕ) (R : Finset X)
    (h : (majSet π F R).Nonempty) : R.Nonempty := by
  obtain ⟨z, hz⟩ := h
  simp only [majSet, mem_filter, mem_univ, true_and] at hz
  have hW : 0 < W π R z := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hW
  exact ⟨x, (mem_filter.mp hx).1⟩

end Llrg
