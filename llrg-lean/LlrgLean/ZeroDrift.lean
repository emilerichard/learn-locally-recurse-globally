/-
Proposition `zero_drift` (i): zero expected drift of the parity (GF(2)) marginal.
For a bound set fixed independently of the residual, fibers of even size `F` (`n > k`), and a
distribution of the residual invariant under complementation (in particular the uniform
distribution), the expected change of the residual weight under one parity step is zero.
-/
import LlrgLean.Marginals

set_option linter.unusedSectionVars false

open scoped symmDiff
open Finset

namespace Llrg

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Change of residual weight under one parity step on bound set `π`. -/
def dPar (π : X → Z) (R : Finset X) : ℤ := ((R ∆ overSet π (parSet π R)).card : ℤ) - R.card

lemma W_compl (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (R : Finset X) (z : Z) :
    W π Rᶜ z = F - W π R z := by
  unfold W
  have hsplit := card_filter_add_card_filter_not (s := univ.filter (fun x => π x = z))
    (p := fun x => x ∈ R)
  rw [hF z] at hsplit
  have e1 : (univ.filter (fun x => π x = z)).filter (fun x => x ∈ R) = R.filter (fun x => π x = z) := by
    ext x; simp [and_comm]
  have e2 : (univ.filter (fun x => π x = z)).filter (fun x => x ∉ R) = Rᶜ.filter (fun x => π x = z) := by
    ext x; simp [and_comm]
  rw [e1, e2] at hsplit; omega

/-- Complementing the residual negates the parity drift (fibers of even size). -/
theorem dPar_compl (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (hEven : Even F) (R : Finset X) :
    dPar π Rᶜ = - dPar π R := by
  have hle : ∀ z, W π R z ≤ F := fun z => W_le_F π F hF R z
  have hpar : parSet π Rᶜ = parSet π R := by
    ext z; simp only [parSet, mem_filter, mem_univ, true_and, W_compl π F hF R z]
    have := hle z
    rcases hEven with ⟨a, ha⟩
    constructor
    · intro h; by_contra h'
      rw [Nat.not_odd_iff_even] at h'; rcases h' with ⟨b, hb⟩; rcases h with ⟨c, hc⟩; omega
    · intro h; rcases h with ⟨c, hc⟩; exact ⟨a - c - 1, by omega⟩
  have h1 := delta_par π F hF Rᶜ
  have h2 := delta_par π F hF R
  unfold dPar at *
  rw [show ((Rᶜ ∆ overSet π (parSet π Rᶜ)).card : ℤ) - (Rᶜ).card
      = ∑ z ∈ parSet π Rᶜ, ((F : ℤ) - 2 * W π Rᶜ z) from h1, h2, hpar, ← sum_neg_distrib]
  refine sum_congr rfl (fun z _ => ?_)
  rw [W_compl π F hF R z]; push_cast [Nat.cast_sub (hle z)]; ring

/-- Proposition `zero_drift` (i): for a fixed bound set with fibers of even size, and any
distribution `p` of the residual invariant under complementation, `E[Δw_par] = 0`. -/
theorem zero_drift (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (hEven : Even F)
    (p : Finset X → ℝ) (hp : ∀ R, p Rᶜ = p R) :
    ∑ R : Finset X, p R * (dPar π R : ℝ) = 0 := by
  have hinv : ∑ R : Finset X, p R * (dPar π R : ℝ) = ∑ R : Finset X, p Rᶜ * (dPar π Rᶜ : ℝ) :=
    (Fintype.sum_equiv (Function.Involutive.toPerm _ compl_involutive) _ _
      (fun R => by simp)).symm
  rw [show (∑ R : Finset X, p Rᶜ * (dPar π Rᶜ : ℝ)) = - ∑ R : Finset X, p R * (dPar π R : ℝ) by
    rw [← sum_neg_distrib]; refine sum_congr rfl (fun R _ => ?_)
    rw [hp, dPar_compl π F hF hEven]; push_cast; ring] at hinv
  linarith

/-- The uniform distribution: the drift summed over all residuals is zero. -/
theorem zero_drift_uniform (π : X → Z) (F : ℕ) (hF : UniformFibers π F) (hEven : Even F) :
    ∑ R : Finset X, dPar π R = 0 := by
  have := zero_drift π F hF hEven (fun _ => 1) (fun _ => rfl)
  simp only [one_mul] at this; exact_mod_cast this

end Llrg
