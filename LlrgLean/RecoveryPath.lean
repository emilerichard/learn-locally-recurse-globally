/-
Theorem `dichotomy` (b), full statement: an XOR of blocks on disjoint inputs is recovered by the
majority loop in exactly one step per block, provided no remainder is exactly balanced.

Rows are `t` blocks `A × (A × ⋯ × Unit)` (each block = the `k` inputs of one `B_j`), optionally
times extra inputs `E` that the target ignores (`n > tk`). The run is explicit: step `d` is the
majority step on the projection onto block `d`, whose fibers have size `|A|^{t−1}` (`· |E|`).
-/
import LlrgLean.Reachability

set_option linter.unusedSectionVars false

open scoped symmDiff
open Finset

namespace Llrg

/-- One majority step on bound set `π` with fiber size `F`. -/
def majStep {Y Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (π : Y → Z) (F : ℕ) (R : Finset Y) : Finset Y := R ∆ overSet π (majSet π F R)

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


end Blocks

/-! ### Iterated blocks: rows `A × (A × (⋯ × Unit))`. -/

/-- Rows of `t` blocks of type `A`. -/
@[reducible] def Rows (A : Type) : ℕ → Type
  | 0 => Unit
  | t + 1 => A × Rows A t

instance instFintypeRows (A : Type) [Fintype A] : (t : ℕ) → Fintype (Rows A t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t + 1 => @instFintypeProd A (Rows A t) _ (instFintypeRows A t)

instance instDecEqRows (A : Type) [DecidableEq A] : (t : ℕ) → DecidableEq (Rows A t)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | t + 1 => @instDecidableEqProd A (Rows A t) _ (instDecEqRows A t)

variable {A : Type} [Fintype A] [DecidableEq A]

lemma card_rows (t : ℕ) : Fintype.card (Rows A t) = Fintype.card A ^ t := by
  induction t with
  | zero => exact Fintype.card_unit
  | succ t ih =>
    show Fintype.card (A × Rows A t) = _
    rw [Fintype.card_prod, ih, pow_succ, mul_comm]

/-- Projection onto block `d` (block `0` is the outermost). -/
def coord : (t : ℕ) → Fin t → Rows A t → A
  | t + 1, ⟨0, _⟩ => fun x => x.1
  | t + 1, ⟨d + 1, h⟩ => fun x => coord t ⟨d, by omega⟩ x.2

/-- The run of Theorem `dichotomy` (b): starting at block `d`, apply at most `k` majority steps, the
step on block `d` using the projection `coord t d` with fiber size `|A|^{t−1}`, then block `d+1`, … -/
def runSteps (t : ℕ) : ℕ → ℕ → Finset (Rows A t) → Finset (Rows A t)
  | _, 0, R => R
  | d, k + 1, R =>
    if h : d < t then runSteps t (d + 1) k (majStep (coord t ⟨d, h⟩) (Fintype.card A ^ (t - 1)) R)
    else R

/-- The projection onto a block has fibers of size `|A|^{t−1}`. -/
lemma uniform_coord : ∀ (t : ℕ) (d : Fin t), UniformFibers (coord (A := A) t d) (Fintype.card A ^ (t - 1))
  | t + 1, ⟨0, h⟩ => by
    have := uniform_fst (A := A) (B := Rows A t)
    rw [card_rows] at this; exact this
  | t + 1, ⟨d + 1, h⟩ => by
    have ih := uniform_coord t ⟨d, by omega⟩
    have := uniform_lift (A := A) (coord t ⟨d, by omega⟩) _ ih
    have ht : 1 ≤ t := by omega
    rw [show Fintype.card A * Fintype.card A ^ (t - 1) = Fintype.card A ^ t by
      rw [← pow_succ']; congr 1; omega] at this
    exact this

/-- Steps on inner blocks act on `A × R` as on `R`. -/
lemma runSteps_lift (hA : 0 < Fintype.card A) (t : ℕ) :
    ∀ (k d : ℕ) (R : Finset (Rows A t)),
      runSteps (t + 1) (d + 1) k ((univ : Finset A) ×ˢ R) = (univ : Finset A) ×ˢ runSteps t d k R
  | 0, d, R => rfl
  | k + 1, d, R => by
    by_cases h : d < t
    · have e1 : runSteps (A := A) (t + 1) (d + 1) (k + 1) ((univ : Finset A) ×ˢ R)
          = runSteps (t + 1) (d + 2) k (majStep (coord (t + 1) ⟨d + 1, by omega⟩)
              (Fintype.card A ^ (t + 1 - 1)) ((univ : Finset A) ×ˢ R)) := by
        rw [runSteps, dif_pos (by omega)]
      have e2 : runSteps (A := A) t d (k + 1) R
          = runSteps t (d + 1) k (majStep (coord t ⟨d, h⟩) (Fintype.card A ^ (t - 1)) R) := by
        rw [runSteps, dif_pos h]
      have hc : coord (A := A) (t + 1) ⟨d + 1, by omega⟩ = fun p => coord t ⟨d, h⟩ p.2 := rfl
      have hpow : Fintype.card A ^ (t + 1 - 1) = Fintype.card A * Fintype.card A ^ (t - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e1, e2, hc, hpow, majStep_lift hA]
      exact runSteps_lift hA t k (d + 1) _
    · have e1 : runSteps (A := A) (t + 1) (d + 1) (k + 1) ((univ : Finset A) ×ˢ R)
          = (univ : Finset A) ×ˢ R := by rw [runSteps, dif_neg (by omega)]
      have e2 : runSteps (A := A) t d (k + 1) R = R := by rw [runSteps, dif_neg h]
      rw [e1, e2]

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

/-- First step of the run on an XOR whose remainder `h` is not exactly balanced: the majority step
on the outer block leaves `A × sel h`, for the target and for its complement. -/
lemma first_step (g : Finset A) {t : ℕ} (h : Finset (Rows A t))
    (hb : 2 * h.card ≠ Fintype.card (Rows A t)) :
    majStep (coord (t + 1) ⟨0, by omega⟩) (Fintype.card A ^ t) (xorTarget g h)
      = (univ : Finset A) ×ˢ sel h ∧
    majStep (coord (t + 1) ⟨0, by omega⟩) (Fintype.card A ^ t) (univ \ xorTarget g h)
      = (univ : Finset A) ×ˢ sel h := by
  have hc : coord (A := A) (t + 1) ⟨0, by omega⟩ = Prod.fst := rfl
  rw [hc, ← card_rows]
  have hle := card_le_univ h
  have key : ∀ h' : Finset (Rows A t), 2 * h'.card ≠ Fintype.card (Rows A t) →
      majStep Prod.fst (Fintype.card (Rows A t)) (xorTarget g h') = (univ : Finset A) ×ˢ sel h' := by
    intro h' hb'
    unfold majStep
    rcases lt_or_gt_of_ne hb' with hlt | hgt
    · rw [(block_step_lt g h' hlt).1, (block_step_lt g h' hlt).2.1]; simp [sel, hlt]
    · rw [(block_step_gt g h' hgt).1, (block_step_gt g h' hgt).2.1]
      simp [sel, show ¬ 2 * h'.card < Fintype.card (Rows A t) by omega]
  refine ⟨key h hb, ?_⟩
  rw [compl_xorTarget, key (univ \ h) (by rw [card_compl]; omega)]
  congr 1; unfold sel; rw [card_compl]
  rcases lt_or_gt_of_ne hb with hlt | hgt
  · rw [if_neg (by omega), if_pos hlt]; ext y; simp
  · rw [if_pos (by omega), if_neg (by omega)]

/-- The run clears the low-density version of a block XOR in exactly `t` steps. -/
theorem runSteps_sel (hA : 0 < Fintype.card A) (gs : ℕ → Finset A) (c : Bool) :
    ∀ t, Unbalanced gs c t → runSteps t 0 t (sel (blockXor gs c t)) = ∅
  | 0, _ => by rw [sel_blockXor_zero]; rfl
  | t + 1, hu => by
    have hb := hu t (Nat.lt_succ_self t)
    have ih := runSteps_sel hA gs c t (fun j hj => hu j (Nat.lt_succ_of_lt hj))
    have hs := first_step (gs t) (blockXor gs c t) hb
    unfold runSteps; rw [dif_pos (by omega)]
    show runSteps (t + 1) 1 t (majStep _ _ (sel (xorTarget (gs t) (blockXor gs c t)))) = ∅
    simp only [Nat.add_sub_cancel]
    unfold sel; split_ifs
    · rw [hs.1, runSteps_lift hA, ih]; simp
    · rw [hs.2, runSteps_lift hA, ih]; simp

/-- Theorem `dichotomy` (b): for an XOR of `t ≥ 1` blocks on disjoint inputs (plus a constant),
with no exactly balanced remainder, the majority steps on blocks `0, 1, …, t−1`, in this order,
reach the zero residual in exactly `t` steps. The intermediate residuals are given by
`first_step`: after the step on a block, the residual is the low-density version of the XOR of the
remaining blocks, constant along the processed ones. -/
theorem runSteps_blockXor (hA : 0 < Fintype.card A) (gs : ℕ → Finset A) (c : Bool) (t : ℕ)
    (hu : Unbalanced gs c (t + 1)) : runSteps (t + 1) 0 (t + 1) (blockXor gs c (t + 1)) = ∅ := by
  have hb := hu t (Nat.lt_succ_self t)
  have ih := runSteps_sel hA gs c t (fun j hj => hu j (Nat.lt_succ_of_lt hj))
  unfold runSteps; rw [dif_pos (by omega)]
  show runSteps (t + 1) 1 t (majStep _ _ (xorTarget (gs t) (blockXor gs c t))) = ∅
  simp only [Nat.add_sub_cancel]
  rw [(first_step (gs t) (blockXor gs c t) hb).1, runSteps_lift hA, ih]; simp

/-! ### Extra inputs ignored by the target (`n > t k`). -/

section Extra
variable {E : Type} [Fintype E] [DecidableEq E]

/-- The same run on `E × Rows A t`: step `d` on block `d`, fibers of size `|E| · |A|^{t−1}`. -/
def runStepsE (t : ℕ) : ℕ → ℕ → Finset (E × Rows A t) → Finset (E × Rows A t)
  | _, 0, R => R
  | d, k + 1, R =>
    if h : d < t then runStepsE t (d + 1) k
      (majStep (fun p : E × Rows A t => coord t ⟨d, h⟩ p.2)
        (Fintype.card E * Fintype.card A ^ (t - 1)) R)
    else R

lemma runStepsE_eq (hE : 0 < Fintype.card E) (t : ℕ) :
    ∀ (k d : ℕ) (R : Finset (Rows A t)),
      runStepsE t d k ((univ : Finset E) ×ˢ R) = (univ : Finset E) ×ˢ runSteps t d k R
  | 0, d, R => by simp [runStepsE, runSteps]
  | k + 1, d, R => by
    unfold runStepsE runSteps
    by_cases h : d < t
    · rw [dif_pos h, dif_pos h, majStep_lift hE]; exact runStepsE_eq hE t k (d + 1) _
    · rw [dif_neg h, dif_neg h]

/-- Theorem `dichotomy` (b) with inputs outside the blocks: the target ignores `E`; the same
`t` block steps reach zero. -/
theorem runStepsE_blockXor (hE : 0 < Fintype.card E) (hA : 0 < Fintype.card A)
    (gs : ℕ → Finset A) (c : Bool) (t : ℕ) (hu : Unbalanced gs c (t + 1)) :
    runStepsE (t + 1) 0 (t + 1) ((univ : Finset E) ×ˢ blockXor gs c (t + 1)) = ∅ := by
  rw [runStepsE_eq hE, runSteps_blockXor hA gs c t hu]; simp

end Extra

end Llrg
