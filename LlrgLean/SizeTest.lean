/-
Algorithm 2: the size test and its guarantee.

Cells are rows × outputs. A correction is a set of cells together with the size of the circuit
that writes it. The output of the loop is the XOR, per output column, of the accepted corrections
touching that column and of the completion of the final residual. Its size is
  (sizes of the corrections) + 3 · Σ_j (number of terms of column j − 1) + L(final residual),
where `L` is any completion cost (in the paper, the closed-form size of the minterm SOP).
A candidate `(c, κ)` is accepted iff `κ + 3 · |touched c| + L(R ∆ c) < L(R)`.
Guarantee: the output is exact, and its size never exceeds `L(Y)`, the size of the fallback alone,
strictly so if a step was accepted.
-/
import LlrgLean.Refinement
import LlrgLean.Marginals

open scoped symmDiff
open Finset

namespace Llrg

variable {ρ : Type*} [DecidableEq ρ] {m : ℕ}

local notation "Cell" => ρ × Fin m

/-- Column `j` of a set of cells. -/
def col (R : Finset Cell) (j : Fin m) : Finset Cell := R.filter (fun p => p.2 = j)

/-- Output columns a correction touches. -/
def touched (c : Finset Cell) : Finset (Fin m) := univ.filter (fun j => (col c j).Nonempty)

/-- 1 if the completion has a term in column `j`. -/
def colNE (R : Finset Cell) (j : Fin m) : ℕ := if (col R j).Nonempty then 1 else 0

/-- Number of accepted corrections touching column `j`. -/
def nTouch (cs : List (Finset Cell × ℕ)) (j : Fin m) : ℕ :=
  (cs.filter (fun p => decide (j ∈ touched p.1))).length

/-- Exact number of AIG nodes of the XOR network: per column, `terms − 1` XORs of 3 nodes. -/
def xorCost (cs : List (Finset Cell × ℕ)) (R : Finset Cell) : ℕ :=
  3 * ∑ j, (nTouch cs j + colNE R j - 1)

/-- Size of the emitted circuit for accepted corrections `cs` and final residual `R`. -/
def total (L : Finset Cell → ℕ) (cs : List (Finset Cell × ℕ)) (R : Finset Cell) : ℕ :=
  (cs.map Prod.snd).sum + xorCost cs R + L R

lemma col_symmDiff (R c : Finset Cell) (j : Fin m) : col (R ∆ c) j = col R j ∆ col c j := by
  ext p; simp only [col, mem_filter, Finset.mem_symmDiff]; tauto

lemma col_empty_of_not_touched (c : Finset Cell) (j : Fin m) (hj : j ∉ touched c) :
    col c j = ∅ := by
  simp only [touched, mem_filter, mem_univ, true_and, not_nonempty_iff_eq_empty] at hj; exact hj

/-- Conservative XOR accounting: if every column touched by `c` has a non-empty residual, adding
`c` raises the exact XOR cost by at most `3 · |touched c|`. -/
lemma xorCost_step (cs : List (Finset Cell × ℕ)) (R c : Finset Cell) (κ : ℕ)
    (hne : ∀ j ∈ touched c, (col R j).Nonempty) :
    xorCost ((c, κ) :: cs) (R ∆ c) ≤ xorCost cs R + 3 * (touched c).card := by
  unfold xorCost
  rw [← mul_add]
  apply Nat.mul_le_mul_left
  have hcard : (touched c).card = ∑ j, (if j ∈ touched c then 1 else 0) := by
    rw [Finset.sum_ite_mem, univ_inter]; simp
  rw [hcard, ← sum_add_distrib]
  apply sum_le_sum
  intro j _
  have hn : nTouch ((c, κ) :: cs) j = nTouch cs j + (if j ∈ touched c then 1 else 0) := by
    unfold nTouch; by_cases h : j ∈ touched c <;> simp [List.filter_cons, h]
  rw [hn]
  by_cases hj : j ∈ touched c
  · have h1 : colNE R j = 1 := by simp [colNE, hne j hj]
    have h2 : colNE (R ∆ c) j ≤ 1 := by unfold colNE; split_ifs <;> omega
    simp only [hj, if_true]; omega
  · have hc := col_empty_of_not_touched c j hj
    have h3 : colNE (R ∆ c) j = colNE R j := by
      unfold colNE; rw [col_symmDiff, hc, show col R j ∆ (∅ : Finset Cell) = col R j from by
        ext x; simp [Finset.mem_symmDiff]]
    simp only [hj, ite_false, h3]; omega

/-- The first candidate that passes the size test, if any. -/
def firstPassing (L : Finset Cell → ℕ) (R : Finset Cell) :
    List (Finset Cell × ℕ) → Option (Finset Cell × ℕ)
  | [] => none
  | p :: ps => if p.2 + 3 * (touched p.1).card + L (R ∆ p.1) < L R then some p
               else firstPassing L R ps

lemma firstPassing_spec (L : Finset Cell → ℕ) (R : Finset Cell) :
    ∀ (ps : List (Finset Cell × ℕ)) (p : Finset Cell × ℕ), firstPassing L R ps = some p →
      p ∈ ps ∧ p.2 + 3 * (touched p.1).card + L (R ∆ p.1) < L R
  | [], p, h => by simp [firstPassing] at h
  | q :: qs, p, h => by
    unfold firstPassing at h
    split_ifs at h with hq
    · cases h; exact ⟨List.mem_cons_self .., hq⟩
    · have := firstPassing_spec L R qs p h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

/-- Algorithm 2 with budget `T`, from accepted corrections `cs` and residual `R`. -/
def project (L : Finset Cell → ℕ) (propose : Finset Cell → List (Finset Cell × ℕ)) :
    ℕ → List (Finset Cell × ℕ) → Finset Cell → List (Finset Cell × ℕ) × Finset Cell
  | 0, cs, R => (cs, R)
  | T + 1, cs, R =>
    match firstPassing L R (propose R) with
    | none => (cs, R)
    | some p => project L propose T (p :: cs) (R ∆ p.1)

/-- Size never increases along the loop, provided every proposed correction touches only columns
whose residual is non-empty (true of the majority marginal, `majSet_nonempty` below). -/
theorem project_total_le (L : Finset Cell → ℕ) (propose : Finset Cell → List (Finset Cell × ℕ))
    (hprop : ∀ R, ∀ p ∈ propose R, ∀ j ∈ touched p.1, (col R j).Nonempty) :
    ∀ (T : ℕ) (cs : List (Finset Cell × ℕ)) (R : Finset Cell),
      total L (project L propose T cs R).1 (project L propose T cs R).2 ≤ total L cs R
  | 0, cs, R => by simp [project]
  | T + 1, cs, R => by
    unfold project
    split
    · exact le_rfl
    · rename_i p hp
      obtain ⟨hmem, htest⟩ := firstPassing_spec L R (propose R) p hp
      refine le_trans (project_total_le L propose hprop T (p :: cs) (R ∆ p.1)) ?_
      have hx : xorCost (p :: cs) (R ∆ p.1) ≤ xorCost cs R + 3 * (touched p.1).card :=
        xorCost_step cs R p.1 p.2 (hprop R p hmem)
      unfold total; simp only [List.map_cons, List.sum_cons]
      omega

/-- Strict decrease when at least one step is accepted. -/
theorem project_total_lt (L : Finset Cell → ℕ) (propose : Finset Cell → List (Finset Cell × ℕ))
    (hprop : ∀ R, ∀ p ∈ propose R, ∀ j ∈ touched p.1, (col R j).Nonempty)
    (T : ℕ) (cs : List (Finset Cell × ℕ)) (R : Finset Cell)
    (hstep : (project L propose T cs R).1.length > cs.length) :
    total L (project L propose T cs R).1 (project L propose T cs R).2 < total L cs R := by
  cases T with
  | zero => simp [project] at hstep
  | succ T =>
    cases hfp : firstPassing L R (propose R) with
    | none => simp [project, hfp] at hstep
    | some p =>
      simp only [project, hfp] at hstep ⊢
      obtain ⟨hmem, htest⟩ := firstPassing_spec L R (propose R) p hfp
      refine lt_of_le_of_lt (project_total_le L propose hprop T (p :: cs) (R ∆ p.1)) ?_
      have hx : xorCost (p :: cs) (R ∆ p.1) ≤ xorCost cs R + 3 * (touched p.1).card :=
        xorCost_step cs R p.1 p.2 (hprop R p hmem)
      unfold total; simp only [List.map_cons, List.sum_cons]
      omega

/-- With no accepted correction, the size is that of the completion alone (no XOR gates). -/
lemma total_nil [Fintype ρ] (L : Finset Cell → ℕ) (Y : Finset Cell) : total L [] Y = L Y := by
  unfold total xorCost nTouch; simp only [List.map_nil, List.sum_nil, List.filter_nil,
    List.length_nil, zero_add]
  have : ∀ j : Fin m, colNE Y j - 1 = 0 := fun j => by unfold colNE; split_ifs <;> rfl
  simp [this]

/-- The guarantee of Algorithm 2: the emitted circuit is never larger than the completion of the
whole target (the fallback alone), and strictly smaller if a step was accepted. -/
theorem project_le_fallback [Fintype ρ] (L : Finset Cell → ℕ)
    (propose : Finset Cell → List (Finset Cell × ℕ))
    (hprop : ∀ R, ∀ p ∈ propose R, ∀ j ∈ touched p.1, (col R j).Nonempty) (T : ℕ) (Y : Finset Cell) :
    total L (project L propose T [] Y).1 (project L propose T [] Y).2 ≤ L Y ∧
    ((project L propose T [] Y).1 ≠ [] →
      total L (project L propose T [] Y).1 (project L propose T [] Y).2 < L Y) := by
  refine ⟨(total_nil L Y) ▸ project_total_le L propose hprop T [] Y, fun hne => ?_⟩
  rw [← total_nil L Y]
  exact project_total_lt L propose hprop T [] Y (by
    simpa [List.length_pos_iff] using hne)

/-- Exactness of Algorithm 2: the accepted corrections XOR the completion equal the target. -/
theorem project_exact (L : Finset Cell → ℕ) (propose : Finset Cell → List (Finset Cell × ℕ)) :
    ∀ (T : ℕ) (cs : List (Finset Cell × ℕ)) (R : Finset Cell),
      xorAll ((project L propose T cs R).1.map Prod.fst) ∆ (project L propose T cs R).2
        = xorAll (cs.map Prod.fst) ∆ R
  | 0, cs, R => by simp [project]
  | T + 1, cs, R => by
    unfold project
    split
    · rfl
    · rename_i p _
      rw [project_exact L propose T (p :: cs) (R ∆ p.1)]
      simp only [List.map_cons, xorAll]
      ext x; simp only [Finset.mem_symmDiff]; tauto

end Llrg

namespace Llrg

variable {ρ Z : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype Z] [DecidableEq Z] {m : ℕ}

/-- Rows of output column `j` that are set in `R`. -/
def rowsOf (R : Finset (ρ × Fin m)) (j : Fin m) : Finset ρ := univ.filter (fun r => (r, j) ∈ R)

/-- The majority correction of Algorithm 2 on cells: for each selected output column `j ∈ O`, the
rows over the majority-set fibers of that column's residual. -/
def majCorr (π : ρ → Z) (F : ℕ) (O : Finset (Fin m)) (R : Finset (ρ × Fin m)) :
    Finset (ρ × Fin m) :=
  univ.filter (fun p => p.2 ∈ O ∧ π p.1 ∈ majSet π F (rowsOf R p.2))

/-- The majority correction touches only columns whose residual is non-empty: the hypothesis
`hprop` of `project_le_fallback` holds for the majority operator. -/
theorem majCorr_touched (π : ρ → Z) (F : ℕ) (O : Finset (Fin m)) (R : Finset (ρ × Fin m)) :
    ∀ j ∈ touched (majCorr π F O R), (col R j).Nonempty := by
  intro j hj
  simp only [touched, mem_filter, mem_univ, true_and] at hj
  obtain ⟨p, hp⟩ := hj
  simp only [col, majCorr, mem_filter, mem_univ, true_and] at hp
  obtain ⟨⟨_, hmaj⟩, rfl⟩ := hp
  obtain ⟨r, hr⟩ := nonempty_of_majSet_nonempty π F (rowsOf R p.2) ⟨_, hmaj⟩
  exact ⟨(r, p.2), by simp only [col, mem_filter]; exact ⟨(mem_filter.mp hr).2, trivial⟩⟩

/-- `project_le_fallback` for a proposer that only proposes majority corrections (any family of
bound sets `π i`, fiber sizes, column sets, circuit sizes and order). -/
theorem project_le_fallback_maj {ι : Type*} (L : Finset (ρ × Fin m) → ℕ)
    (π : ι → ρ → Z) (F : ι → ℕ) (O : ι → Finset (Fin m))
    (propose : Finset (ρ × Fin m) → List (Finset (ρ × Fin m) × ℕ))
    (hmaj : ∀ R, ∀ p ∈ propose R, ∃ i, p.1 = majCorr (π i) (F i) (O i) R)
    (T : ℕ) (Y : Finset (ρ × Fin m)) :
    total L (project L propose T [] Y).1 (project L propose T [] Y).2 ≤ L Y ∧
    ((project L propose T [] Y).1 ≠ [] →
      total L (project L propose T [] Y).1 (project L propose T [] Y).2 < L Y) := by
  refine project_le_fallback L propose (fun R p hp j hj => ?_) T Y
  obtain ⟨i, hi⟩ := hmaj R p hp
  rw [hi] at hj
  exact majCorr_touched (π i) (F i) (O i) R j hj

end Llrg
