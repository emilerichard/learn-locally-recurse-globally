/-
§6: parity on `n ≥ 1` variables needs `2^{n-1}` terms in any sum of products.
A product term (cube) fixes some variables to a value and leaves the others free.
-/
import Mathlib

open Finset

namespace Llrg

variable {n : ℕ}

/-- A cube: `c i = some b` fixes input `i` to `b`, `none` leaves it free. -/
abbrev Cube (n : ℕ) := Fin n → Option Bool

def covers (c : Cube n) (x : Fin n → Bool) : Prop := ∀ i b, c i = some b → x i = b

instance (c : Cube n) (x : Fin n → Bool) : Decidable (covers c x) := by
  unfold covers; infer_instance

/-- Parity of the input. -/
def parity (x : Fin n → Bool) : Prop := Odd (univ.filter (fun i => x i = true)).card

instance (x : Fin n → Bool) : Decidable (parity x) := by unfold parity; infer_instance

/-- A set of cubes computes `f` as a sum of products. -/
def SOPComputes (S : Finset (Cube n)) (f : (Fin n → Bool) → Prop) : Prop :=
  ∀ x, (∃ c ∈ S, covers c x) ↔ f x

/-- Flipping one input flips the parity. -/
lemma parity_flip (x : Fin n → Bool) (i : Fin n) :
    parity (Function.update x i (!x i)) ↔ ¬ parity x := by
  unfold parity
  have key : ((univ.filter (fun j => Function.update x i (!x i) j = true)).card : ℤ)
      = (univ.filter (fun j => x j = true)).card + (if x i then -1 else 1) := by
    have h1 : univ.filter (fun j => Function.update x i (!x i) j = true)
        = if x i then (univ.filter (fun j => x j = true)).erase i
          else insert i (univ.filter (fun j => x j = true)) := by
      ext j; by_cases hj : j = i
      · subst hj; cases hx : x j <;> simp [hx]
      · cases hx : x i <;> simp [Function.update_of_ne hj, hj]
    rw [h1]; cases hx : x i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [card_insert_of_notMem (by simp [hx])]; push_cast; ring
    · simp only [↓reduceIte]
      rw [card_erase_of_mem (by simp [hx])]
      have : 1 ≤ (univ.filter (fun j => x j = true)).card := card_pos.mpr ⟨i, by simp [hx]⟩
      push_cast [Nat.cast_sub this]; ring
  constructor
  · intro h1 h2
    have := key; rcases h1 with ⟨a, ha⟩; rcases h2 with ⟨b, hb⟩
    split_ifs at this <;> omega
  · intro h
    rw [Nat.not_odd_iff_even] at h; rcases h with ⟨a, ha⟩
    have := key
    split_ifs at this with hx
    · exact ⟨a - 1, by omega⟩
    · exact ⟨a, by omega⟩

/-- In any SOP of parity, every cube fixes every input. -/
lemma cube_total {S : Finset (Cube n)} (hS : SOPComputes S parity) (c : Cube n) (hc : c ∈ S)
    (i : Fin n) : c i ≠ none := by
  intro hi
  -- a point covered by `c`: fixed inputs as in `c`, free inputs set to `false`
  let x : Fin n → Bool := fun j => (c j).getD false
  have hx : covers c x := by intro j b hb; simp [x, hb]
  have hx' : covers c (Function.update x i (!x i)) := by
    intro j b hb
    by_cases hj : j = i
    · subst hj; rw [hi] at hb; exact absurd hb (by simp)
    · rw [Function.update_of_ne hj]; exact hx j b hb
  have p1 := (hS x).mp ⟨c, hc, hx⟩
  have p2 := (hS _).mp ⟨c, hc, hx'⟩
  exact (parity_flip x i).mp p2 p1

/-- A cube that fixes every input covers at most one point. -/
lemma covers_unique {c : Cube n} (hc : ∀ i, c i ≠ none) {x y : Fin n → Bool}
    (hx : covers c x) (hy : covers c y) : x = y := by
  funext i
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (hc i)
  rw [hx i b hb, hy i b hb]

/-- Exactly half of the inputs have odd parity. -/
lemma card_parity (hn : 0 < n) :
    (univ.filter (fun x : Fin n → Bool => parity x)).card = 2 ^ (n - 1) := by
  let i : Fin n := ⟨0, hn⟩
  let flip : (Fin n → Bool) → (Fin n → Bool) := fun x => Function.update x i (!x i)
  have hinv : ∀ x, flip (flip x) = x := by
    intro x; funext j; by_cases hj : j = i
    · subst hj; simp [flip]
    · simp [flip, Function.update_of_ne hj]
  have hodd_even : (univ.filter (fun x : Fin n → Bool => parity x)).card
      = (univ.filter (fun x : Fin n → Bool => ¬ parity x)).card := by
    refine card_bij (fun x _ => flip x) (fun x hx => ?_) (fun x _ y _ h => ?_) (fun y hy => ?_)
    · simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact fun h => ((parity_flip x i).mp h) hx
    · simpa [hinv] using congrArg flip h
    · refine ⟨flip y, ?_, hinv y⟩
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      exact (parity_flip y i).mpr hy
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (Fin n → Bool)))
    (p := fun x => parity x)
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htot
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- §6: every sum of products of parity on `n ≥ 1` inputs has at least `2^{n−1}` terms. -/
theorem parity_sop_card (hn : 0 < n) (S : Finset (Cube n)) (hS : SOPComputes S parity) :
    2 ^ (n - 1) ≤ S.card := by
  rw [← card_parity hn]
  -- each point of odd parity is covered by a cube of `S`; a cube of `S` covers at most one point
  classical
  let pick : (Fin n → Bool) → Cube n := fun x =>
    if h : ∃ c ∈ S, covers c x then Classical.choose h else default
  have hpick : ∀ x, parity x → pick x ∈ S ∧ covers (pick x) x := by
    intro x hx
    have h : ∃ c ∈ S, covers c x := (hS x).mpr hx
    simp only [pick, dif_pos h]; exact Classical.choose_spec h
  refine card_le_card_of_injOn pick (fun x hx => ?_) (fun x hx y hy hxy => ?_)
  · exact (hpick x (mem_filter.mp hx).2).1
  · obtain ⟨hxS, hxc⟩ := hpick x (mem_filter.mp hx).2
    obtain ⟨_, hyc⟩ := hpick y (mem_filter.mp hy).2
    rw [hxy] at hxc
    exact covers_unique (cube_total hS _ (hxy ▸ hxS)) hxc hyc

end Llrg
