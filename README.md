# llrg-lean

Lean 4 / Mathlib formalization of the mathematical claims of *Learn Locally, Recurse Globally:
Neural Circuit Synthesis Beyond Training Depth*. Toolchain `leanprover/lean4:v4.34.1`, Mathlib
`v4.34.1`. Build: `lake exe cache get && lake build`. No `sorry`, no `native_decide` (finite computations use `decide +kernel`, checked by the kernel); every theorem
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
| Prop. `zero_drift` (i): for a bound set chosen independently of `R` with `k < n` (fibers of even size), and a distribution of `R` invariant under complementation (in particular uniform), `E[Δw_par] = 0` | `zero_drift`, `zero_drift_uniform`, `dPar_compl` | `ZeroDrift.lean` |
| Prop. `convergence_rate`: (C1)–(C2) ⇒ `E[w_{t+1}] ≤ 2ε₀ w_t` (one step, in expectation; the unconditional recursion `E[w_{t+1}] ≤ 2ε₀ E[w_t]` is assumed for the iteration, the tower step from the conditional form is not formalized; `ε₀ > 0`); `E[w_t] ≤ (2ε₀)^t w_0`; Markov `P(w_t ≠ 0) ≤ E[w_t]`; expected number of iterations with non-zero residual ≤ `⌈log(m 2^n)/log(1/(2ε₀))⌉ + 1/(1−2ε₀)` (any horizon) | `one_step`, `iterate_contraction`, `prob_ne_zero_le`, `tail_sum`, `expected_iterations` | `Convergence.lean` |
| Prop. `gain` and its proof: `gain = w − 2^{n−1}(1−β_S)`; `δ' = (1−β_S)/2`; progress iff `β_S > 1−2δ`; max gain ⇔ max `β`; `β_S ∈ [0,1]`; `β_S = 1` iff `R` is an `S`-junta; `|Z|·F = 2^n` | `two_gain`, `card_after_maj_beta`, `progress_iff`, `gain_le_iff`, `betaSum_bounds`, `betaSum_eq_iff`, `card_Z_mul_F` (integer forms: `betaSum = 2^n β_S`) | `Marginals.lean` |
| Thm. `dichotomy` (a): weight ≤ F/2 ⇒ no progress; a minterm is a fixed point | `no_progress_of_small`, `minterm_fixed` | `Reachability.lean` |
| Thm. `dichotomy` (b), one step, both cases and the balanced case (**corrected gain for μ > 1/2**) | `block_step_lt`, `block_step_gt`, `block_step_eq` | `Reachability.lean` |
| Thm. `dichotomy` (b): XOR of `t` blocks on disjoint inputs, no balanced remainder ⇒ the majority steps on blocks `B_1, …, B_t`, in order (explicit run `runSteps`, projection onto block `d`, fibers of size `2^{n−k}`), reach 0 after the `t` block steps; also with inputs outside the blocks (`n > tk`); intermediate residuals | `runSteps_blockXor`, `runStepsE_blockXor`, `first_step`, `uniform_coord` | `RecoveryPath.lean` |
| §6: any SOP of parity on `n ≥ 1` inputs has ≥ `2^{n−1}` terms | `parity_sop_card` | `ParitySOP.lean` |
| §3: strided positional encoding is injective, within `2^n·m_max`, independent of `n` | `strd_injective`, `strd_lt`, `strd_sub` | `StridedPE.lean` |
| §2.2: Reed–Muller expansion exists, is unique, coefficient `a_S = ⊕_{T⊆S} f(1_T)` | `reed_muller`, `rmCoef_rmEval`, `rmEval_rmCoef` | `ReedMuller.lean` |
| Remark `rm_floor` (i)–(ii): every correction `x ↦ g(x|_S)` is an `|S|`-junta; `RM(k,n)` is exactly the set of XORs of `k`-juntas; residual weight ≥ `d(R_0, RM(k,n))` for any selector and budget | `proj_junta`, `junta_mem_RM`, `RM_add`, `RM_is_sum_of_juntas`, `mono_junta`, `residual_floor` | `JuntaFloor.lean` |
| Remark `rm_floor` (iii), App. proof: Hoeffding/Chernoff for `Bin(2^n, 1/2)` (`#{g : wt g ≤ 2^{n−1} − t} ≤ 2^{2^n} e^{−2t²/2^n}`); `|RM(k,n)| = 2^K`, `K = Σ_{i≤k} C(n,i)`; union bound; for uniform `R_0` (stated as a count over all `2^{2^n}` targets), with probability ≥ `1−δ` (`0 < δ ≤ 1`) every pre-completion residual of any run (any list of `k`-junta corrections) has `w_T/2^n > 1/2 − sqrt((K ln 2 + ln(1/δ))/2^{n+1})`; the deviation term → 0 as `n → ∞` for fixed `k`; at `(n,k,δ) = (10,5,0.01)`, `K = 638` and the floor lies in `[0.03, 0.035]` | `tail`, `card_RM`, `union_bound`, `rm_floor_whp`, `eps_tendsto`, `K_10_5`, `floor_10_5` | `RMFloor.lean` |
| App. F, Fourier form (`f = (−1)^R`, `P_S` = average over the fiber, characters `χ_T`, `f̂(T) = 2^{−n} Σ f χ_T`): `β_S = ‖P_S f‖₁`; `β_S ≤ ‖P_S f‖₂ = (Σ_{T⊆S} f̂(T)²)^{1/2}`; `P_S χ_T = χ_T` if `T ⊆ S`, else 0; for `k ≤ n`, `β_S = 0` for every `|S| = k` iff `f̂(T) = 0` for every `|T| ≤ k`; parity on `J`: `β_S = 1` if `J ⊆ S`, else 0, and one majority step on `S` clears it if `J ⊆ S` and otherwise leaves weight `2^{n−1}` (hence the `k = 5`, `n = 10` example) | `betaSum_eq_L1`, `beta_le_L2`, `fourier_expansion`, `norm2_avg`, `avg_chi`, `beta_zero_iff`, `beta_parity`, `parity_maj_step` | `FourierBeta.lean` |
| App. H: generator classes `G_q`; nesting; `m`-output count `|G_q|^m`; Shannon step; `G_3(4) = all ⇒ G_5(5) = all` | `G`, `G_mono`, `card_multi_output_G`, `shannon_step`, `G_embed`, `all_G5_of_all_G3` | `DepthClasses.lean` |
| App. H, computed sizes: `|G_2(3)| = 133`, `|G_2(4)| = 1078`, `G_3(4)` = all `2^16` functions, every function of 5 inputs in `G_5(5)` | `card_G2_3`, `card_G2_4`, `all_G3_4`, `all_G5_5` (bitmaps computed by the kernel, `decide +kernel`, and related to `G` by `G1_iff`, `G2_iff`, `card_of_spec`; `G_3(4)`: a certificate of one depth-3 witness per truth table, produced outside Lean, checked by the kernel in `G3Cert.lean`) | `ClassCount.lean`, `G3Cert.lean`, `G3Sound.lean` |
| App. Dyck, Thm. `th:dyck_informal` (one causal uniform-attention head, tokens `±1`, `P(next = '(') = σ(2X_r)`, `X_r = (v/r) Σ_{i<r}(E(z_i) + B_i)`): telescoping `Σ (E(z_i)+B_i) = Δ_r(z) − Δ_r(s) + γ E(s_{r+1})`; memorization (`vγ > N²`: every non-empty prefix of `s` completed into `s` w.p. ≥ `1 − 2N e^{−N}`; cross-entropy ≤ `2N e^{−N}`); generalization by contraction (`γ = −1/2`, `−v > 2N²`: every non-empty valid prefix completed into a Dyck word w.p. ≥ `1 − 2N e^{−N}`, via a specific completion that agrees with the prefix); failure (stack sizes differ: for every `γ > 0` the sign-following completion is never balanced; for `0 < γ < 2` and `vγ > N²` it is generated w.p. ≥ `1 − 2N e^{−N(2−γ)/γ}`) | `S_eq`, `memorization`, `memorization_loss`, `generalization`, `comp_isDyck`, `failure`, `failure_det` | `Dyck.lean` |

Not formalized (computational or out of scope):
- the size `|G_2(5)| = 15025` and the lower bound on `|G_3(5)|` (computed by closure, cross-checked
  against the corpora); the other entries of Table `tab:class_single` (`|G_1(n)| = 7, 17, 32, 65`,
  `|G_2(2)| = |G_3(2)| = 16`, `|G_3(3)| = 256`) and the corpus statistics of Table `tab:class_multi`
  and of the Validation paragraph (empirical);
- the sentence of App. F identifying the residuals without low-degree Fourier mass with "the orthogonal
  complement of the low-degree space identified in Remark `rm_floor`" (see finding 8); the remarks on
  the parity marginal after Thm. `dichotomy`;
- the closed-form size `L` of App. B itself: the guarantees hold for any completion cost `L` and any
  circuit sizes, so they apply to it; the correspondence between a circuit and the cells it sets
  (a synthesized circuit reproduces its sub-table exactly) is the modelling assumption of the loops;
- the composition of loop and completion into a single circuit object: outputs are stated on cell
  sets (`refine_exact`, `project_exact`) and the SOP of a set of rows is its indicator
  (`sop_eq_indicator`);
- (C1)–(C2) of Prop. `convergence_rate` are hypotheses about the model, taken as assumptions.

Findings while formalizing:
1. Thm. `dichotomy` (b): for `μ_j > 1/2` the flipped fibers are those with `g_j = 0`, so the gain is
   `(2^k − |g_j|) · F · (2μ_j − 1)`, not `|g_j| · F · |1 − 2μ_j|`; it is positive unless `g_j ≡ 0`
   (`μ_j < 1/2`) or `g_j ≡ 1` (`μ_j > 1/2`).
2. The recovery path does not need positive gain at every step; it needs only that no remainder is
   exactly balanced.
3. Prop. 2.1 is stated in the paper as "reaches zero within `‖g‖₁ ≤ m·2^n` steps" (formerly "at most
   `m·2^n` steps suffice").
4. The strided index uses the maximal number of outputs `m_max` as stride.
5. Prop. `zero_drift` (i) holds for a bound set chosen independently of the residual; it fails for
   adaptive selectors (greedy choice among the 6 bound sets at `n = 4`, `k = 2`, uniform `R`:
   `E[Δw_par] ≈ −1.97`). The condition "exactly when `R` is uniform" was too strong; invariance
   under complementation suffices. The paper now states it this way.
6. Prop. `convergence_rate`: the expected number of iterations is at most
   `⌈log(m 2^n)/log(1/(2ε₀))⌉ + 1/(1−2ε₀)`; the paper's `O(·)` hid the second term.
7. Thm. `th:dyck_informal`: memorization and generalization hold with the stated constants
   (`vγ > N²`, `−v > 2N²`) for non-empty prefixes (with an empty prefix the logit is `v/0`). The
   failure holds for every `γ > 0` deterministically (`failure_det`: the sign-following completion
   never reduces the stack gap, so it is never balanced); the probability bound
   `1 − 2N e^{−N(2−γ)/γ}` is proved for `0 < γ < 2` (`failure`), where the per-step margin is `2 − γ`. The probability bounds are for one
   explicit completion (valid, resp. invalid), hence lower bounds for the event.
8. App. F: the residuals with `f̂(T) = 0` for all `|T| ≤ k` form the orthogonal complement (over `ℝ`)
   of the span of the characters `χ_T`, `|T| ≤ k`. Remark `rm_floor` identifies the code `RM(k,n)`
   over `GF(2)`. The two spaces are related (both are spanned by `k`-juntas, over `ℝ` and over
   `GF(2)` respectively), but they are different objects, so "the orthogonal complement of the
   low-degree space identified in Remark `rm_floor`" is loose. Remark `rm_floor` (iii): the
   `≈ 3%` floor at `(10, 5)`, `δ = 0.01`, is `≥ 3%` and `≤ 3.5%`.
