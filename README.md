# llrg-lean

Lean 4 / Mathlib formalization of the mathematical claims of *Learn Locally, Recurse Globally:
Neural Circuit Synthesis Beyond Training Depth*. Toolchain `leanprover/lean4:v4.34.1`, Mathlib
`v4.34.1`. Build: `lake exe cache get && lake build`. No `sorry`, no `native_decide`; every theorem
below depends only on the axioms `propext`, `Classical.choice`, `Quot.sound` (`#print axioms`).

Modelling: truth tables are finite sets of cells (`Finset`) — the cells equal to 1 — over an
arbitrary finite type of cells, rows or rows × outputs; XOR is symmetric difference, Hamming weight
is cardinality. A projection onto a bound set is any map `π : X → Z` with fibers of uniform size
`F`. Results hold for all `n`, `m`, `k`.

| Paper claim | Lean | File |
|---|---|---|
| Prop. 2.1: `g = h ⊕ r`; `g = (h_1 ⊕ … ⊕ h_t) ⊕ r_t`; at most `‖Y‖₁ ≤ m·2^n` weight-decreasing steps; exact when the bound is reached | `xor_residual`, `target_eq_acc_xor_resid`, `steps_le_weight`, `steps_le_card`, `resid_empty_of_steps` | `XorResidual.lean` |
| SOP completion is exact (OR of minterms = indicator) | `sop_eq_indicator` | `Refinement.lean` |
| Alg. 1: exact output and at most `‖Y‖₁` accepted steps, for any model (arbitrary proposer, incl. mask retries) | `refine_exact`, `refine_steps_le` | `Refinement.lean` |
| Alg. 2: exact output; size never exceeds the fallback alone, strictly smaller after an accepted step; conservative XOR accounting | `project_exact`, `project_le_fallback`, `xorCost_step` | `SizeTest.lean` |
| Alg. 2 hypothesis for the majority operator (corrections touch only non-zero residual columns) | `nonempty_of_majSet_nonempty` | `Marginals.lean` |
| App. B: flipping fibers changes the weight by `Σ (F − 2W_z)`; `Δw_par` | `card_flip`, `delta_par` | `Marginals.lean` |
| Prop. `zero_drift` (ii): even fiber weights ⇒ parity marginal is a no-op | `par_noop` | `Marginals.lean` |
| Prop. `gain`: `gain = w − 2^{n−1}(1−β_S)`; `δ' = (1−β_S)/2`; progress iff `β_S > 1−2δ`; max gain ⇔ max `β` | `card_after_maj`, `two_gain`, `card_after_maj_beta`, `progress_iff`, `gain_le_iff` | `Marginals.lean` |
| Thm. `dichotomy` (a): weight ≤ F/2 ⇒ no progress; a minterm is a fixed point | `no_progress_of_small`, `minterm_fixed` | `Reachability.lean` |
| Thm. `dichotomy` (b), one step, both cases and the balanced case (**corrected gain for μ > 1/2**) | `block_step_lt`, `block_step_gt`, `block_step_eq` | `Reachability.lean` |
| Thm. `dichotomy` (b): XOR of `t` blocks on disjoint inputs, no balanced remainder ⇒ recovered in exactly `t` majority steps | `recov_blockXor` (with `recov_lift`, `recov_block`) | `RecoveryPath.lean` |
| §6: any SOP of parity on `n ≥ 1` inputs has ≥ `2^{n−1}` terms | `parity_sop_card` | `ParitySOP.lean` |
| §3: strided positional encoding is injective, within `2^n·m_max`, independent of `n` | `strd_injective`, `strd_lt`, `strd_sub` | `StridedPE.lean` |
| §2.2: Reed–Muller expansion exists, is unique, coefficient `a_S = ⊕_{T⊆S} f(1_T)` | `reed_muller`, `rmCoef_rmEval`, `rmEval_rmCoef` | `ReedMuller.lean` |
| Remark `rm_floor` (i)–(ii): `k`-juntas span `RM(k,n)`; residual weight ≥ `d(R_0, RM(k,n))` for any selector and budget | `junta_mem_RM`, `mono_junta`, `RM_add`, `residual_floor` | `JuntaFloor.lean` |
| App. H: generator classes `G_q`; nesting; `m`-output count `|G_q|^m`; Shannon step; `G_3(4) = all ⇒ G_5(5) = all` | `G`, `G_mono`, `card_multi_output`, `shannon_step`, `G_embed`, `all_G5_of_all_G3` | `DepthClasses.lean` |

Not formalized (computational or out of scope): the class sizes `|G_2(4)| = 1078`, `|G_3(4)| = 2^16`,
`|G_2(5)| = 15025` and the lower bound on `|G_3(5)|` (computed by closure, cross-checked against the
corpora; `all_G5_of_all_G3` takes `G_3(4) = all` as a hypothesis); Prop. `zero_drift` (i) and
Prop. `convergence_rate` (probabilistic); the asymptotic part of Remark `rm_floor`; the Dyck
completion theorem; the Fourier form of App. F.

Findings while formalizing:
1. Thm. `dichotomy` (b): for `μ_j > 1/2` the flipped fibers are those with `g_j = 0`, so the gain is
   `(2^k − |g_j|) · F · (2μ_j − 1)`, not `|g_j| · F · |1 − 2μ_j|`; it is positive iff `g_j` is not
   constant (`|g_j| > 0` for `μ_j < 1/2`, `|g_j| < 2^k` for `μ_j > 1/2`).
2. The recovery path does not need positive gain at every step; it needs only that no remainder is
   exactly balanced.
