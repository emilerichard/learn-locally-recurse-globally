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
| Prop. 2.1: `g = h ⊕ r`; `g = (h_1 ⊕ … ⊕ h_t) ⊕ r_t`; if every step taken while `r ≠ 0` decreases the weight, `r` reaches 0 within `‖g‖₁ ≤ m·2^n` steps | `xor_residual`, `target_eq_acc_xor_resid`, `resid_reaches_zero`, `steps_le_weight`, `steps_le_card` | `XorResidual.lean` |
| SOP completion is exact (OR of minterms = indicator) | `sop_eq_indicator` | `Refinement.lean` |
| Alg. 1: exact output and at most `‖Y‖₁` accepted steps, for any model (arbitrary proposer, incl. mask retries) | `refine_exact`, `refine_steps_le` | `Refinement.lean` |
| Alg. 2: exact output; size never exceeds the fallback alone, strictly smaller after an accepted step; conservative XOR accounting | `project_exact`, `project_le_fallback`, `xorCost_step` | `SizeTest.lean` |
| Alg. 2 with the majority operator: the multi-column majority correction touches only non-zero residual columns, so the guarantee holds for any proposer of majority corrections | `majCorr`, `majCorr_touched`, `project_le_fallback_maj` (single column: `nonempty_of_majSet_nonempty`) | `SizeTest.lean`, `Marginals.lean` |
| App. B: flipping fibers changes the weight by `Σ (F − 2W_z)`; `Δw_par`; `Δw_maj = −Σ max(2W_z − F, 0)`; the majority marginal is the weight-minimizing correction for a fixed bound set | `card_flip`, `delta_par`, `card_after_maj`, `gain_eq_sum_max`, `maj_optimal` | `Marginals.lean` |
| Prop. `zero_drift` (ii): even fiber weights ⇒ parity marginal is a no-op | `par_noop` | `Marginals.lean` |
| Prop. `gain` and its proof: `gain = w − 2^{n−1}(1−β_S)`; `δ' = (1−β_S)/2`; progress iff `β_S > 1−2δ`; max gain ⇔ max `β`; `β_S ∈ [0,1]`; `β_S = 1` iff `R` is an `S`-junta; `|Z|·F = 2^n` | `two_gain`, `card_after_maj_beta`, `progress_iff`, `gain_le_iff`, `betaSum_bounds`, `betaSum_eq_iff`, `card_Z_mul_F` (integer forms: `betaSum = 2^n β_S`) | `Marginals.lean` |
| Thm. `dichotomy` (a): weight ≤ F/2 ⇒ no progress; a minterm is a fixed point | `no_progress_of_small`, `minterm_fixed` | `Reachability.lean` |
| Thm. `dichotomy` (b), one step, both cases and the balanced case (**corrected gain for μ > 1/2**) | `block_step_lt`, `block_step_gt`, `block_step_eq` | `Reachability.lean` |
| Thm. `dichotomy` (b): XOR of `t` blocks on disjoint inputs, no balanced remainder ⇒ the majority steps on blocks `B_1, …, B_t`, in order (explicit run `runSteps`, projection onto block `d`, fibers of size `2^{n−k}`), reach 0 in exactly `t` steps; also with inputs outside the blocks (`n > tk`); intermediate residuals | `runSteps_blockXor`, `runStepsE_blockXor`, `first_step`, `uniform_coord` | `RecoveryPath.lean` |
| §6: any SOP of parity on `n ≥ 1` inputs has ≥ `2^{n−1}` terms | `parity_sop_card` | `ParitySOP.lean` |
| §3: strided positional encoding is injective, within `2^n·m_max`, independent of `n` | `strd_injective`, `strd_lt`, `strd_sub` | `StridedPE.lean` |
| §2.2: Reed–Muller expansion exists, is unique, coefficient `a_S = ⊕_{T⊆S} f(1_T)` | `reed_muller`, `rmCoef_rmEval`, `rmEval_rmCoef` | `ReedMuller.lean` |
| Remark `rm_floor` (i)–(ii): every correction `x ↦ g(x|_S)` is an `|S|`-junta; `RM(k,n)` is exactly the set of XORs of `k`-juntas; residual weight ≥ `d(R_0, RM(k,n))` for any selector and budget | `proj_junta`, `junta_mem_RM`, `RM_add`, `RM_is_sum_of_juntas`, `mono_junta`, `residual_floor` | `JuntaFloor.lean` |
| App. H: generator classes `G_q`; nesting; `m`-output count `|G_q|^m`; Shannon step; `G_3(4) = all ⇒ G_5(5) = all` | `G`, `G_mono`, `card_multi_output_G`, `shannon_step`, `G_embed`, `all_G5_of_all_G3` | `DepthClasses.lean` |

Not formalized (computational or out of scope):
- the class sizes `|G_2(4)| = 1078`, `|G_3(4)| = 2^16`, `|G_2(5)| = 15025` and the lower bound on
  `|G_3(5)|` (computed by closure, cross-checked against the corpora; `all_G5_of_all_G3` takes
  `G_3(4) = all` as a hypothesis);
- Prop. `zero_drift` (i) and Prop. `convergence_rate` (probabilistic); the asymptotic part of
  Remark `rm_floor`; the Fourier form of App. F; the Dyck completion theorem; the remarks on the
  parity marginal after Thm. `dichotomy`;
- the closed-form size `L` of App. B itself: the guarantees hold for any completion cost `L` and any
  circuit sizes, so they apply to it; the correspondence between a circuit and the cells it sets
  (a synthesized circuit reproduces its sub-table exactly) is the modelling assumption of the loops;
- the composition of loop and completion into a single circuit object: outputs are stated on cell
  sets (`refine_exact`, `project_exact`) and the SOP of a set of rows is its indicator
  (`sop_eq_indicator`).

Findings while formalizing:
1. Thm. `dichotomy` (b): for `μ_j > 1/2` the flipped fibers are those with `g_j = 0`, so the gain is
   `(2^k − |g_j|) · F · (2μ_j − 1)`, not `|g_j| · F · |1 − 2μ_j|`; it is positive unless `g_j ≡ 0`
   (`μ_j < 1/2`) or `g_j ≡ 1` (`μ_j > 1/2`).
2. The recovery path does not need positive gain at every step; it needs only that no remainder is
   exactly balanced.
3. Prop. 2.1 is stated in the paper as "reaches zero within `‖g‖₁ ≤ m·2^n` steps" (formerly "at most
   `m·2^n` steps suffice").
4. The strided index uses the maximal number of outputs `m_max` as stride.
