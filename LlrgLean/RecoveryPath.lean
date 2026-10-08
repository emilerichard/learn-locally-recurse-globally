/-
Theorem `dichotomy` (b), full statement: an XOR of blocks on disjoint inputs is recovered by the
majority loop in exactly one step per block, provided no remainder is exactly balanced.

`RecovIn R k`: the residual `R` reaches zero after exactly `k` majority steps, each on some bound
set (a projection with fibers of uniform size).
-/
import LlrgLean.Reachability

set_option linter.unusedSectionVars false

open scoped symmDiff
open Finset

namespace Llrg

/-- One majority step on bound set `π` with fiber size `F`. -/
def majStep {Y Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (π : Y → Z) (F : ℕ) (R : Finset Y) : Finset Y := R ∆ overSet π (majSet π F R)

inductive RecovIn {Y : Type} [Fintype Y] [DecidableEq Y] : Finset Y → ℕ → Prop
  | zero : RecovIn ∅ 0
  | step {Z : Type} [Fintype Z] [DecidableEq Z] (π : Y → Z) (F : ℕ) (hF : UniformFibers π F)
      (R : Finset Y) (k : ℕ) (h : RecovIn (majStep π F R) k) : RecovIn R (k + 1)

section Lift
variable {A Y Z : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

lemma W_lift (π : Y → Z) (R : Finset Y) (z : Z) :
    W (fun p : A × Y => π p.2) ((univ : Finset A) ×ˢ R) z = Fintype.card A * W π R z := by
  unfold W
  rw [show ((univ : Finset A) ×ˢ R).filter (fun p : A × Y => π p.2 = z)
      = (univ : Finset A) ×ˢ (R.filter (fun y => π y = z)) by
    ext p; simp [mem_product, and_assoc]]
  simp [card_product]

lemma uniform_lift (π : Y → Z) (F : ℕ) (hF : UniformFibers π F) :
    UniformFibers (fun p : A × Y => π p.2) (Fintype.card A * F) := by
  intro z
  rw [show (univ : Finset (A × Y)).filter (fun p => π p.2 = z)
      = (univ : Finset A) ×ˢ (univ.filter (fun y => π y = z)) by ext p; simp]
  simp [card_product, hF z]

lemma majSet_lift (hA : 0 < Fintype.card A) (π : Y → Z) (F : ℕ) (R : Finset Y) :
    majSet (fun p : A × Y => π p.2) (Fintype.card A * F) ((univ : Finset A) ×ˢ R)
      = majSet π F R := by
  ext z; simp only [majSet, mem_filter, mem_univ, true_and, W_lift]
  constructor
  · intro h; by_contra h'; push_neg at h'
    have := Nat.mul_le_mul_left (Fintype.card A) h'
    nlinarith
  · intro h; nlinarith

lemma majStep_lift (hA : 0 < Fintype.card A) (π : Y → Z) (F : ℕ) (R : Finset Y) :
    majStep (fun p : A × Y => π p.2) (Fintype.card A * F) ((univ : Finset A) ×ˢ R)
      = (univ : Finset A) ×ˢ majStep π F R := by
  unfold majStep; rw [majSet_lift hA]
  ext p; simp [overSet, Finset.mem_symmDiff, mem_product]

/-- Lifting: a recovery path for `R` on `Y` is a recovery path of the same length for `A × R`. -/
theorem recov_lift (hA : 0 < Fintype.card A) {R : Finset Y} {k : ℕ} (h : RecovIn R k) :
    RecovIn ((univ : Finset A) ×ˢ R) k := by
  induction h with
  | zero => simpa using (RecovIn.zero : RecovIn (∅ : Finset (A × Y)) 0)
  | @step Z' _ _ π F hF R k _ ih =>
    refine RecovIn.step (fun p : A × Y => π p.2) (Fintype.card A * F) (uniform_lift π F hF) _ k ?_
    rw [majStep_lift hA]; exact ih

end Lift

section Blocks
variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]

/-- Of a remainder and its complement, the one of density below 1/2. -/
def sel (h : Finset Y) : Finset Y := if 2 * h.card < Fintype.card Y then h else univ \ h

lemma compl_xorTarget (g : Finset A) (h : Finset Y) :
    univ \ xorTarget g h = xorTarget g (univ \ h) := by
  ext p; simp only [xorTarget, mem_sdiff, mem_univ, mem_filter, true_and]; tauto

lemma card_compl (h : Finset Y) : (univ \ h).card = Fintype.card Y - h.card := by
  rw [card_sdiff_of_subset (subset_univ h), card_univ]

/-- One block: if the remainder is not exactly balanced and its low-density version `sel h` is
recovered in `k` steps, then `g(a) ⊕ h(y)` is recovered in `k + 1` steps, the first on the block. -/
theorem recov_block (hA : 0 < Fintype.card A) (g : Finset A) (h : Finset Y) (k : ℕ)
    (hb : 2 * h.card ≠ Fintype.card Y) (hr : RecovIn (sel h) k) :
    RecovIn (xorTarget g h) (k + 1) := by
  refine RecovIn.step Prod.fst (Fintype.card Y) uniform_fst _ k ?_
  unfold majStep
  rcases lt_or_gt_of_ne hb with hlt | hgt
  · rw [(block_step_lt g h hlt).1, (block_step_lt g h hlt).2.1]
    simpa [sel, hlt] using recov_lift hA hr
  · rw [(block_step_gt g h hgt).1, (block_step_gt g h hgt).2.1]
    simpa [sel, show ¬ 2 * h.card < Fintype.card Y by omega] using recov_lift hA hr

/-- The complement is recovered in the same number of steps (its low-density version is the same). -/
theorem recov_block_compl (hA : 0 < Fintype.card A) (g : Finset A) (h : Finset Y) (k : ℕ)
    (hb : 2 * h.card ≠ Fintype.card Y) (hr : RecovIn (sel h) k) :
    RecovIn (univ \ xorTarget g h) (k + 1) := by
  rw [compl_xorTarget]
  have hle := card_le_univ h
  have hb' : 2 * (univ \ h).card ≠ Fintype.card Y := by rw [card_compl]; omega
  refine recov_block hA g (univ \ h) k hb' ?_
  have hsel : sel (univ \ h) = sel h := by
    unfold sel; rw [card_compl]
    rcases lt_or_gt_of_ne hb with hlt | hgt
    · rw [if_neg (by omega), if_pos hlt]; ext y; simp
    · rw [if_pos (by omega), if_neg (by omega)]
  rw [hsel]; exact hr

end Blocks

/-! ### Iterated blocks: rows `A × (A × (⋯ × Unit))`. -/

/-- Rows of `t` blocks of type `A`. -/
def Rows (A : Type) : ℕ → Type
  | 0 => Unit
  | t + 1 => A × Rows A t

instance instFintypeRows (A : Type) [Fintype A] : (t : ℕ) → Fintype (Rows A t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t + 1 => @instFintypeProd A (Rows A t) _ (instFintypeRows A t)

instance instDecEqRows (A : Type) [DecidableEq A] : (t : ℕ) → DecidableEq (Rows A t)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | t + 1 => @instDecidableEqProd A (Rows A t) _ (instDecEqRows A t)

variable {A : Type} [Fintype A] [DecidableEq A]

/-- `blockXor gs c t = g_{t−1}(a_{t−1}) ⊕ ⋯ ⊕ g_0(a_0) ⊕ c`, blocks on disjoint inputs. -/
def blockXor (gs : ℕ → Finset A) (c : Bool) : (t : ℕ) → Finset (Rows A t)
  | 0 => if c then (univ : Finset (Rows A 0)) else ∅
  | t + 1 => xorTarget (gs t) (blockXor gs c t)

/-- No remainder is exactly balanced (`μ_j ≠ 1/2` for every block). -/
def Unbalanced (gs : ℕ → Finset A) (c : Bool) (t : ℕ) : Prop :=
  ∀ j < t, 2 * (blockXor gs c j).card ≠ Fintype.card (Rows A j)

lemma card_rows_zero : Fintype.card (Rows A 0) = 1 := Fintype.card_unit

lemma sel_blockXor_zero (gs : ℕ → Finset A) (c : Bool) : sel (blockXor gs c 0) = ∅ := by
  unfold sel
  cases c
  · simp [blockXor, card_rows_zero]
  · simp only [blockXor, if_true, card_univ, card_rows_zero]
    rw [if_neg (by norm_num)]
    exact Finset.sdiff_self _

/-- Low-density remainders of a block XOR are recovered in one step per block. -/
theorem recov_sel_blockXor (hA : 0 < Fintype.card A) (gs : ℕ → Finset A) (c : Bool) :
    ∀ t, Unbalanced gs c t → RecovIn (sel (blockXor gs c t)) t := by
  intro t
  induction t with
  | zero => intro _; rw [sel_blockXor_zero]; exact RecovIn.zero
  | succ t ih =>
    intro hu
    have hin : RecovIn (sel (blockXor gs c t)) t := ih (fun j hj => hu j (Nat.lt_succ_of_lt hj))
    have hb : 2 * (blockXor gs c t).card ≠ Fintype.card (Rows A t) := hu t (Nat.lt_succ_self t)
    unfold sel
    split_ifs
    · exact recov_block hA (gs t) (blockXor gs c t) t hb hin
    · exact recov_block_compl hA (gs t) (blockXor gs c t) t hb hin

/-- Theorem `dichotomy` (b): an XOR of `t ≥ 1` blocks on disjoint inputs (`c = false`), with no
exactly balanced remainder, is recovered by exactly `t` majority steps, the `j`-th on block `j`
(counted from the outside). -/
theorem recov_blockXor (hA : 0 < Fintype.card A) (gs : ℕ → Finset A) (c : Bool) (t : ℕ)
    (hu : Unbalanced gs c (t + 1)) : RecovIn (blockXor gs c (t + 1)) (t + 1) :=
  recov_block hA (gs t) (blockXor gs c t) t (hu t (Nat.lt_succ_self t))
    (recov_sel_blockXor hA gs c t (fun j hj => hu j (Nat.lt_succ_of_lt hj)))

end Llrg
