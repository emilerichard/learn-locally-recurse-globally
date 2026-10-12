/-
Algorithm 1 (XOR residual refinement) and SOP completion.

The model, the mask retries and their order are abstracted into an arbitrary `propose`, which
lists candidate corrections for the current residual. The loop accepts the first candidate that
strictly decreases the residual weight, stops when none does or when the step budget is spent,
and returns the accepted corrections together with the remaining residual, which SOP completion
writes out exactly.
-/
import LlrgLean.XorResidual

open scoped symmDiff
open Finset

namespace Llrg

/-! ### SOP completion -/

/-- Minterm of row `r`: the AND of `n` literals, true exactly on `r`. -/
def minterm {n : ℕ} (r : Fin n → Bool) (x : Fin n → Bool) : Bool := decide (∀ i, x i = r i)

/-- Sum of products of a set of rows: the OR of their minterms. -/
def sop {n : ℕ} (S : Finset (Fin n → Bool)) (x : Fin n → Bool) : Bool :=
  decide (∃ r ∈ S, minterm r x = true)

/-- SOP completion is exact: the OR of the minterms of `S` is the indicator of `S`. -/
theorem sop_eq_indicator {n : ℕ} (S : Finset (Fin n → Bool)) (x : Fin n → Bool) :
    sop S x = decide (x ∈ S) := by
  unfold sop minterm
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨r, hr, h⟩
    have : x = r := funext (by simpa using h)
    exact this ▸ hr
  · intro hx; exact ⟨x, hx, by simp⟩

/-! ### Algorithm 1 -/

variable {C : Type*} [DecidableEq C]

/-- The first candidate that strictly decreases the residual weight, if any. -/
def firstAccepted (R : Finset C) : List (Finset C) → Option (Finset C)
  | [] => none
  | c :: cs => if (R ∆ c).card < R.card then some c else firstAccepted R cs

lemma firstAccepted_spec (R : Finset C) :
    ∀ (cs : List (Finset C)) (c : Finset C), firstAccepted R cs = some c → (R ∆ c).card < R.card
  | [], c, h => by simp [firstAccepted] at h
  | d :: ds, c, h => by
    unfold firstAccepted at h
    split_ifs at h with hd
    · cases h; exact hd
    · exact firstAccepted_spec R ds c h

/-- Algorithm 1 with step budget `T`: returns the accepted corrections and the final residual. -/
def refine (propose : Finset C → List (Finset C)) : ℕ → Finset C → List (Finset C) × Finset C
  | 0, R => ([], R)
  | T + 1, R =>
    match firstAccepted R (propose R) with
    | none => ([], R)
    | some c => let r := refine propose T (R ∆ c); (c :: r.1, r.2)

/-- XOR of a list of corrections. -/
def xorAll : List (Finset C) → Finset C
  | [] => ∅
  | c :: cs => c ∆ xorAll cs

/-- Correctness for any model: the accepted corrections XOR the completion of the final residual
equal the target. -/
theorem refine_exact (propose : Finset C → List (Finset C)) :
    ∀ (T : ℕ) (Y : Finset C), xorAll (refine propose T Y).1 ∆ (refine propose T Y).2 = Y
  | 0, Y => by simp [refine, xorAll]
  | T + 1, Y => by
    unfold refine
    split
    · simp [xorAll]
    · rename_i c _
      simp only [xorAll]
      rw [symmDiff_assoc, refine_exact propose T (Y ∆ c)]
      ext x; simp only [Finset.mem_symmDiff]; tauto

/-- Termination for any model: the number of accepted steps is at most the weight of the target,
since each accepted step strictly decreases the residual weight. -/
theorem refine_steps_le (propose : Finset C → List (Finset C)) :
    ∀ (T : ℕ) (Y : Finset C), (refine propose T Y).1.length + (refine propose T Y).2.card ≤ Y.card
  | 0, Y => by simp [refine]
  | T + 1, Y => by
    unfold refine
    split
    · simp
    · rename_i c hc
      have h1 := firstAccepted_spec Y (propose Y) c hc
      have h2 := refine_steps_le propose T (Y ∆ c)
      simp only [List.length_cons]
      omega

end Llrg
