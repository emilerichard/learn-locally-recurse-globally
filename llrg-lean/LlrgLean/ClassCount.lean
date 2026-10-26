/-
Appendix F, computed class sizes, checked by the Lean kernel: `|G_2(3)| = 133`, `|G_2(4)| = 1078`,
`G_3(4)` = all `2^16` functions (hence every 5-input function is in `G_5(5)`).

Truth tables are natural numbers: bit `r` of the code of `f` is `f` on the input whose bit `i`
is input `i`. Gate classes become bitmaps over codes, computed by the kernel (`decide +kernel`),
and are related to the inductive class `G` by the lemmas below.
-/
import LlrgLean.DepthClasses

open Finset

namespace Llrg.Count

/-! ### Bit sets -/

/-- The bitmap of a list of codes. -/
def setOf (l : List ℕ) : ℕ := l.foldl (fun acc c => acc ||| (1 <<< c)) 0

lemma testBit_one_shiftLeft (c k : ℕ) : (1 <<< c).testBit k = decide (c = k) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

lemma testBit_foldl_set (l : List ℕ) (a k : ℕ) :
    (l.foldl (fun acc c => acc ||| (1 <<< c)) a).testBit k = (a.testBit k || decide (k ∈ l)) := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, testBit_one_shiftLeft, List.mem_cons]
    by_cases h : c = k
    · subst h; simp
    · have h' : ¬ k = c := fun e => h e.symm
      simp [h, h']

@[simp] lemma testBit_setOf (l : List ℕ) (k : ℕ) : (setOf l).testBit k = decide (k ∈ l) := by
  unfold setOf; rw [testBit_foldl_set]; simp

/-- Elements of a bitmap below `K`. -/
def bitsOf (K b : ℕ) : List ℕ := (List.range K).filter b.testBit

@[simp] lemma mem_bitsOf (K b c : ℕ) : c ∈ bitsOf K b ↔ c < K ∧ b.testBit c = true := by
  simp [bitsOf]

/-! ### Codes of Boolean functions -/

variable {N : ℕ}

/-- Row index of an input: bit `i` is input `i`. -/
def idx (x : Fin N → Bool) : ℕ := ∑ i : Fin N, if x i then 2 ^ (i : ℕ) else 0

/-- Input of a row index. -/
def rowOf (r : ℕ) : Fin N → Bool := fun i => r.testBit i

/-- Truth-table of a predicate on row indices. -/
def tab (N : ℕ) (p : ℕ → Bool) : ℕ := setOf ((List.range (2 ^ N)).filter p)

/-- Decoding a code into a Boolean function. -/
def decode (c : ℕ) : BFun N := fun x => c.testBit (idx x)

/-- Code of a Boolean function. -/
def code (f : BFun N) : ℕ := tab N (fun r => f (rowOf r))

/-- Number of codes of `N`-input functions. -/
def K (N : ℕ) : ℕ := 2 ^ (2 ^ N)

/-- The two facts about the row index that the development needs, for a given `N`. -/
structure IdxFacts (N : ℕ) : Prop where
  lt : ∀ x : Fin N → Bool, idx x < 2 ^ N
  rowOf_idx : ∀ x : Fin N → Bool, rowOf (idx x) = x

lemma decode_tab (h : IdxFacts N) (p : ℕ → Bool) (x : Fin N → Bool) :
    decode (tab N p) x = p (idx x) := by
  simp [decode, tab, h.lt x]

lemma decode_code (h : IdxFacts N) (f : BFun N) : decode (code f) = f := by
  funext x; rw [code, decode_tab h, h.rowOf_idx]

lemma code_lt (f : BFun N) : code f < K N := by
  unfold code tab K
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp only [testBit_setOf, List.mem_filter, List.mem_range, decide_eq_false_iff_not, not_and]
  intro h; omega

lemma testBit_tab (p : ℕ → Bool) (k : ℕ) :
    (tab N p).testBit k = (decide (k < 2 ^ N) && p k) := by
  simp [tab]

lemma testBit_code (f : BFun N) (k : ℕ) :
    (code f).testBit k = (decide (k < 2 ^ N) && f (rowOf k)) := testBit_tab _ k

/-- The encoding turns gates into bit operations. -/
lemma code_and (f g : BFun N) : code (fun x => f x && g x) = code f &&& code g := by
  apply Nat.eq_of_testBit_eq; intro k; simp only [testBit_code, Nat.testBit_and]
  cases decide (k < 2 ^ N) <;> simp

lemma code_or (f g : BFun N) : code (fun x => f x || g x) = code f ||| code g := by
  apply Nat.eq_of_testBit_eq; intro k; simp only [testBit_code, Nat.testBit_or]
  cases decide (k < 2 ^ N) <;> simp

lemma code_xor (f g : BFun N) : code (fun x => xor (f x) (g x)) = code f ^^^ code g := by
  apply Nat.eq_of_testBit_eq; intro k; simp only [testBit_code, Nat.testBit_xor]
  cases decide (k < 2 ^ N) <;> simp

/-- All-ones table. -/
def full (N : ℕ) : ℕ := K N - 1

lemma code_not (f : BFun N) : code (fun x => !f x) = full N ^^^ code f := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [testBit_code, Nat.testBit_xor, full, K, Nat.testBit_two_pow_sub_one]
  cases decide (k < 2 ^ N) <;> simp

lemma code_true : code (fun _ : Fin N → Bool => true) = full N := by
  apply Nat.eq_of_testBit_eq; intro k
  simp [testBit_code, full, K, Nat.testBit_two_pow_sub_one]

lemma code_injective (h : IdxFacts N) {f g : BFun N} (e : code f = code g) : f = g := by
  rw [← decode_code h f, ← decode_code h g, e]

lemma code_decode (h : IdxFacts N) (hsurj : ∀ r < 2 ^ N, idx (rowOf (N := N) r) = r)
    {c : ℕ} (hc : c < K N) : code (decode (N := N) c) = c := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [testBit_code]
  by_cases hk : k < 2 ^ N
  · simp [hk, decode, hsurj k hk]
  · simp only [hk, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

/-! ### Depth 1 -/

/-- Depth-1 gates as data. -/
inductive D1 (N : ℕ) where
  | inv (i : Fin N)
  | andL (l : List (Fin N))
  | orL (l : List (Fin N))
  | xorP (i j : Fin N)
  | var (i : Fin N)

def D1.eval : D1 N → BFun N
  | .inv i => fun x => !x i
  | .andL l => fun x => l.all x
  | .orL l => fun x => l.any x
  | .xorP i j => fun x => xor (x i) (x j)
  | .var i => fun x => x i

/-- Subsets of `2`–`4` inputs, as sublists of `[0, …, N−1]`. -/
def subs (N : ℕ) : List (List (Fin N)) :=
  (List.finRange N).sublists.filter (fun l => 2 ≤ l.length ∧ l.length ≤ 4)

/-- All depth-1 gates of the generator (bare inputs only when `N < 4`). -/
def descs (N : ℕ) : List (D1 N) :=
  (List.finRange N).map .inv ++ (subs N).map .andL ++ (subs N).map .orL ++
  ((List.finRange N).product (List.finRange N) |>.filter (fun p => p.1 < p.2)).map
    (fun p => .xorP p.1 p.2) ++
  (if N < 4 then (List.finRange N).map .var else [])

lemma G_zero {f : BFun N} : ¬ G N 0 f := by
  intro h; cases h

lemma not_G_zero_list {fs : List (BFun N)} (h1 : 1 ≤ fs.length) (hfs : ∀ f ∈ fs, G N 0 f) : False := by
  obtain ⟨f, hf⟩ := List.exists_mem_of_length_pos h1
  exact G_zero (hfs f hf)

lemma mem_subs_filter (S : Finset (Fin N)) (h2 : 2 ≤ S.card) (h4 : S.card ≤ 4) :
    (List.finRange N).filter (· ∈ S) ∈ subs N := by
  have hlen : ((List.finRange N).filter (· ∈ S)).length = S.card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange N).filter _)]
    congr 1; ext i; simp
  simp only [subs, List.mem_filter, List.mem_sublists, decide_eq_true_eq]
  exact ⟨List.filter_sublist, by omega, by omega⟩

lemma all_filter_mem (S : Finset (Fin N)) (x : Fin N → Bool) :
    ((List.finRange N).filter (· ∈ S)).all x = decide (∀ i ∈ S, x i = true) := by
  rw [Bool.eq_iff_iff]; simp only [List.all_eq_true, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]

lemma any_filter_mem (S : Finset (Fin N)) (x : Fin N → Bool) :
    ((List.finRange N).filter (· ∈ S)).any x = decide (∃ i ∈ S, x i = true) := by
  rw [Bool.eq_iff_iff]; simp [List.any_eq_true]

/-- Depth 1 is exactly the list of gates `descs`. -/
theorem G1_iff (f : BFun N) : G N 1 f ↔ ∃ d ∈ descs N, f = d.eval := by
  constructor
  · intro h
    cases h with
    | inv1 i =>
      exact ⟨.inv i, by unfold descs; simp, rfl⟩
    | and1 S h2 h4 =>
      refine ⟨.andL ((List.finRange N).filter (· ∈ S)), ?_, ?_⟩
      · unfold descs
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_map.mpr ⟨_, mem_subs_filter S h2 h4, rfl⟩))))
      · funext x; simp only [D1.eval, all_filter_mem]
    | or1 S h2 h4 =>
      refine ⟨.orL ((List.finRange N).filter (· ∈ S)), ?_, ?_⟩
      · unfold descs
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_map.mpr ⟨_, mem_subs_filter S h2 h4, rfl⟩)))
      · funext x; simp only [D1.eval, any_filter_mem]
    | xor1 i j hij =>
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · refine ⟨.xorP i j, ?_, rfl⟩
        unfold descs
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
          ⟨(i, j), List.mem_filter.mpr ⟨by simp [List.mem_product], by simpa using hlt⟩, rfl⟩))
      · refine ⟨.xorP j i, ?_, ?_⟩
        · unfold descs
          exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
            ⟨(j, i), List.mem_filter.mpr ⟨by simp [List.mem_product], by simpa using hgt⟩, rfl⟩))
        · funext x; simp [D1.eval, Bool.xor_comm]
    | var1 i hN =>
      refine ⟨.var i, ?_, rfl⟩
      unfold descs
      exact List.mem_append_right _ (by rw [if_pos hN]; simp)
    | inv q f h' => exact absurd h' G_zero
    | and q fs h1 h4 hfs => exact (not_G_zero_list h1 hfs).elim
    | or q fs h1 h4 hfs => exact (not_G_zero_list h1 hfs).elim
    | xor q f g hf hg => exact absurd hf G_zero
  · rintro ⟨d, hd, rfl⟩
    unfold descs at hd
    rcases List.mem_append.mp hd with hd | hvar
    · rcases List.mem_append.mp hd with hd | hx
      · rcases List.mem_append.mp hd with hd | hor
        · rcases List.mem_append.mp hd with hinv | hand
          · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hinv; exact G.inv1 i
          · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hand
            simp only [subs, List.mem_filter, List.mem_sublists, decide_eq_true_eq] at hl
            have hnd : l.Nodup := hl.1.nodup (List.nodup_finRange N)
            have := G.and1 l.toFinset (by rw [List.toFinset_card_of_nodup hnd]; omega)
              (by rw [List.toFinset_card_of_nodup hnd]; omega)
            convert this using 1; funext x
            rw [Bool.eq_iff_iff]; simp [D1.eval, List.all_eq_true]
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hor
          simp only [subs, List.mem_filter, List.mem_sublists, decide_eq_true_eq] at hl
          have hnd : l.Nodup := hl.1.nodup (List.nodup_finRange N)
          have := G.or1 l.toFinset (by rw [List.toFinset_card_of_nodup hnd]; omega)
            (by rw [List.toFinset_card_of_nodup hnd]; omega)
          convert this using 1; funext x
          rw [Bool.eq_iff_iff]; simp [D1.eval, List.any_eq_true]
      · obtain ⟨⟨i, j⟩, hij, rfl⟩ := List.mem_map.mp hx
        have : i < j := by simpa using (List.mem_filter.mp hij).2
        exact G.xor1 i j (ne_of_lt this)
    · by_cases hN : N < 4
      · rw [if_pos hN] at hvar
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hvar; exact G.var1 i hN
      · rw [if_neg hN] at hvar; simp at hvar

/-! ### Closure of a set of codes under a binary operation -/

/-- One closure step: add `op x b` for every `x` in the bitmap and `b ∈ B`. -/
def step (Kb : ℕ) (op : ℕ → ℕ → ℕ) (B : List ℕ) (a : ℕ) : ℕ :=
  a ||| setOf ((bitsOf Kb a).flatMap fun x => B.map (op x))

def iter (Kb : ℕ) (op : ℕ → ℕ → ℕ) (B : List ℕ) : ℕ → ℕ
  | 0 => setOf B
  | j + 1 => step Kb op B (iter Kb op B j)

/-- Codes reachable with at most `j` applications of `op`. -/
def InClose (op : ℕ → ℕ → ℕ) (B : List ℕ) : ℕ → ℕ → Prop
  | 0, c => c ∈ B
  | j + 1, c => InClose op B j c ∨ ∃ x b, InClose op B j x ∧ b ∈ B ∧ c = op x b

lemma InClose_lt {Kb : ℕ} {op : ℕ → ℕ → ℕ} {B : List ℕ} (hB : ∀ b ∈ B, b < Kb)
    (hop : ∀ x b, x < Kb → b < Kb → op x b < Kb) : ∀ j c, InClose op B j c → c < Kb
  | 0, c, h => hB c h
  | j + 1, c, h => by
    rcases h with h | ⟨x, b, hx, hb, rfl⟩
    · exact InClose_lt hB hop j c h
    · exact hop x b (InClose_lt hB hop j x hx) (hB b hb)

theorem testBit_iter {Kb : ℕ} {op : ℕ → ℕ → ℕ} {B : List ℕ} (hB : ∀ b ∈ B, b < Kb)
    (hop : ∀ x b, x < Kb → b < Kb → op x b < Kb) :
    ∀ j c, (iter Kb op B j).testBit c = true ↔ InClose op B j c
  | 0, c => by simp [iter, InClose]
  | j + 1, c => by
    have ih := testBit_iter hB hop j
    simp only [iter, step, Nat.testBit_or, Bool.or_eq_true, testBit_setOf, decide_eq_true_eq,
      List.mem_flatMap, mem_bitsOf, List.mem_map, InClose, ih]
    constructor
    · rintro (h | ⟨x, ⟨_, hx⟩, b, hb, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, b, hx, hb, rfl⟩
    · rintro (h | ⟨x, b, hx, hb, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, ⟨InClose_lt hB hop j x hx, hx⟩, b, hb, rfl⟩

lemma InClose_mono {op : ℕ → ℕ → ℕ} {B : List ℕ} {j c : ℕ} (h : InClose op B j c) :
    ∀ j', j ≤ j' → InClose op B j' c := by
  intro j' hj
  induction hj with
  | refl => exact h
  | step _ ih => exact Or.inl ih

/-! ### Depth 2 -/

def codes1 (N : ℕ) : List ℕ := (descs N).map (fun d => code d.eval)

lemma G1_iff_code (h : IdxFacts N) (f : BFun N) : G N 1 f ↔ code f ∈ codes1 N := by
  rw [G1_iff]
  constructor
  · rintro ⟨d, hd, rfl⟩; exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · intro hc; obtain ⟨d, hd, e⟩ := List.mem_map.mp hc
    exact ⟨d, hd, code_injective h e.symm⟩

def allF (fs : List (BFun N)) : BFun N := fun x => fs.all (fun g => g x)
def anyF (fs : List (BFun N)) : BFun N := fun x => fs.any (fun g => g x)

lemma code_allF_single (g : BFun N) : code (allF [g]) = code g := by
  unfold allF; simp
lemma code_anyF_single (g : BFun N) : code (anyF [g]) = code g := by
  unfold anyF; simp
lemma code_allF_cons (g : BFun N) (fs : List (BFun N)) :
    code (allF (g :: fs)) = code (allF fs) &&& code g := by
  rw [Nat.land_comm, ← code_and]; rfl
lemma code_anyF_cons (g : BFun N) (fs : List (BFun N)) :
    code (anyF (g :: fs)) = code (anyF fs) ||| code g := by
  rw [Nat.lor_comm, ← code_or]; rfl

/-- Lists of depth-`q` functions give AND/OR closures of their codes. -/
lemma InClose_of_list (h : IdxFacts N) (op : ℕ → ℕ → ℕ) (F : List (BFun N) → BFun N)
    (hsingle : ∀ g, code (F [g]) = code g) (hcons : ∀ g fs, code (F (g :: fs)) = op (code (F fs)) (code g)) :
    ∀ fs : List (BFun N), fs ≠ [] → (∀ g ∈ fs, G N 1 g) →
      InClose op (codes1 N) (fs.length - 1) (code (F fs))
  | [], hne, _ => (hne rfl).elim
  | [g], _, hg => by
    simp only [List.length_singleton, Nat.sub_self, InClose, hsingle]
    exact (G1_iff_code h g).mp (hg g (by simp))
  | g :: g' :: fs, _, hg => by
    have ih := InClose_of_list h op F hsingle hcons (g' :: fs) (by simp)
      (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons] at ih ⊢
    rw [hcons]
    exact Or.inr ⟨_, _, ih, (G1_iff_code h g).mp (hg g (by simp)), rfl⟩

lemma list_of_InClose (h : IdxFacts N) (op : ℕ → ℕ → ℕ) (F : List (BFun N) → BFun N)
    (hsingle : ∀ g, code (F [g]) = code g) (hcons : ∀ g fs, code (F (g :: fs)) = op (code (F fs)) (code g)) :
    ∀ j c, InClose op (codes1 N) j c →
      ∃ fs : List (BFun N), 1 ≤ fs.length ∧ fs.length ≤ j + 1 ∧ (∀ g ∈ fs, G N 1 g) ∧ code (F fs) = c
  | 0, c, hc => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact ⟨[d.eval], by simp, by simp, by simpa using (G1_iff d.eval).mpr ⟨d, hd, rfl⟩, hsingle _⟩
  | j + 1, c, hc => by
    rcases hc with hc | ⟨x, b, hx, hb, rfl⟩
    · obtain ⟨fs, h1, h2, h3, h4⟩ := list_of_InClose h op F hsingle hcons j c hc
      exact ⟨fs, h1, by omega, h3, h4⟩
    · obtain ⟨fs, h1, h2, h3, h4⟩ := list_of_InClose h op F hsingle hcons j x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      refine ⟨d.eval :: fs, by simp, by simp; omega, ?_, by rw [hcons, h4]⟩
      intro g hg; rcases List.mem_cons.mp hg with rfl | hg
      · exact (G1_iff _).mpr ⟨d, hd, rfl⟩
      · exact h3 g hg

/-- Inversion of `G` at depth `q + 1 ≥ 2`. -/
lemma G_succ_inv {q : ℕ} (hq : 1 ≤ q) {f : BFun N} (hf : G N (q + 1) f) :
    (∃ g, G N q g ∧ f = fun x => !g x) ∨
    (∃ fs : List (BFun N), 1 ≤ fs.length ∧ fs.length ≤ 4 ∧ (∀ g ∈ fs, G N q g) ∧ f = allF fs) ∨
    (∃ fs : List (BFun N), 1 ≤ fs.length ∧ fs.length ≤ 4 ∧ (∀ g ∈ fs, G N q g) ∧ f = anyF fs) ∨
    (∃ g g', G N q g ∧ G N q g' ∧ f = fun x => xor (g x) (g' x)) := by
  cases hf with
  | inv1 => omega
  | and1 => omega
  | or1 => omega
  | xor1 => omega
  | var1 => omega
  | inv q g hg => exact Or.inl ⟨g, hg, rfl⟩
  | and q fs h1 h4 hfs => exact Or.inr (Or.inl ⟨fs, h1, h4, hfs, rfl⟩)
  | or q fs h1 h4 hfs => exact Or.inr (Or.inr (Or.inl ⟨fs, h1, h4, hfs, rfl⟩))
  | xor q g g' hg hg' => exact Or.inr (Or.inr (Or.inr ⟨g, g', hg, hg', rfl⟩))

/-- The depth-2 bitmap. -/
def g2map (N : ℕ) : ℕ :=
  setOf ((codes1 N).map (full N ^^^ ·)) ||| iter (K N) (· &&& ·) (codes1 N) 3 |||
  iter (K N) (· ||| ·) (codes1 N) 3 ||| setOf ((codes1 N).flatMap fun a => (codes1 N).map (a ^^^ ·))

lemma codes1_lt : ∀ b ∈ codes1 N, b < K N := by
  intro b hb; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hb; exact code_lt _

lemma land_lt : ∀ x b, x < K N → b < K N → x &&& b < K N :=
  fun x b hx _ => lt_of_le_of_lt Nat.and_le_left hx
lemma lor_lt : ∀ x b, x < K N → b < K N → x ||| b < K N := fun x b hx hb => by
  unfold K at *; exact Nat.or_lt_two_pow hx hb

/-- Depth 2 is exactly the set bits of `g2map`. -/
theorem G2_iff (h : IdxFacts N) (f : BFun N) : G N 2 f ↔ (g2map N).testBit (code f) = true := by
  have hand := testBit_iter (Kb := K N) (op := (· &&& ·)) (B := codes1 N) codes1_lt land_lt 3
  have hor := testBit_iter (Kb := K N) (op := (· ||| ·)) (B := codes1 N) codes1_lt lor_lt 3
  simp only [g2map, Nat.testBit_or, Bool.or_eq_true, testBit_setOf, decide_eq_true_eq, hand, hor,
    List.mem_map, List.mem_flatMap]
  constructor
  · intro hf
    rcases G_succ_inv (le_refl 1) hf with ⟨g, hg, rfl⟩ | ⟨fs, h1, h4, hfs, rfl⟩ |
      ⟨fs, h1, h4, hfs, rfl⟩ | ⟨g, g', hg, hg', rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨code g, (G1_iff_code h g).mp hg, (code_not g).symm⟩))
    · refine Or.inl (Or.inl (Or.inr ?_))
      have := InClose_of_list h (· &&& ·) allF code_allF_single code_allF_cons fs
        (by rintro rfl; simp at h1) hfs
      exact InClose_mono this 3 (by omega)
    · refine Or.inl (Or.inr ?_)
      have := InClose_of_list h (· ||| ·) anyF code_anyF_single code_anyF_cons fs
        (by rintro rfl; simp at h1) hfs
      exact InClose_mono this 3 (by omega)
    · exact Or.inr ⟨code g, (G1_iff_code h g).mp hg, code g', (G1_iff_code h g').mp hg',
        (code_xor g g').symm⟩
  · rintro (((⟨c, hc, e⟩ | hc) | hc) | ⟨a, ha, b, hb, e⟩)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      have : f = fun x => !d.eval x := code_injective h (by rw [code_not, e])
      rw [this]; exact G.inv 1 _ ((G1_iff _).mpr ⟨d, hd, rfl⟩)
    · obtain ⟨fs, h1, h4, hfs, e⟩ :=
        list_of_InClose h (· &&& ·) allF code_allF_single code_allF_cons 3 _ hc
      rw [← code_injective h e]; exact G.and 1 fs h1 (by omega) hfs
    · obtain ⟨fs, h1, h4, hfs, e⟩ :=
        list_of_InClose h (· ||| ·) anyF code_anyF_single code_anyF_cons 3 _ hc
      rw [← code_injective h e]; exact G.or 1 fs h1 (by omega) hfs
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hb
      have : f = fun x => xor (d.eval x) (d'.eval x) := code_injective h (by rw [code_xor, e])
      rw [this]
      exact G.xor 1 _ _ ((G1_iff _).mpr ⟨d, hd, rfl⟩) ((G1_iff _).mpr ⟨d', hd', rfl⟩)

/-! ### Counting -/

/-- The size of a class with a bitmap specification is the number of set bits. -/
theorem card_of_spec (h : IdxFacts N) (hs : ∀ r < 2 ^ N, idx (rowOf (N := N) r) = r)
    (P : BFun N → Prop) [DecidablePred P] (bm : ℕ) (hspec : ∀ f, P f ↔ bm.testBit (code f) = true) :
    (univ.filter P).card = (bitsOf (K N) bm).length := by
  have hnd : (bitsOf (K N) bm).Nodup := by unfold bitsOf; exact (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_nbij code (fun f hf => ?_) (fun f _ g _ e => code_injective h e) (fun c hc => ?_)
  · have hf' : P f := (mem_filter.mp hf).2
    exact List.mem_toFinset.mpr ((mem_bitsOf _ _ _).mpr ⟨code_lt f, (hspec f).mp hf'⟩)
  · have hc' := (mem_bitsOf _ _ _).mp (List.mem_toFinset.mp hc)
    refine ⟨decode c, mem_filter.mpr ⟨mem_univ _, ?_⟩, code_decode h hs hc'.1⟩
    exact (hspec _).mpr (by rw [code_decode h hs hc'.1]; exact hc'.2)

set_option maxRecDepth 100000

theorem idxFacts3 : IdxFacts 3 := ⟨by decide +kernel, by decide +kernel⟩
theorem idxFacts4 : IdxFacts 4 := ⟨by decide +kernel, by decide +kernel⟩
theorem idxSurj3 : ∀ r < 2 ^ 3, idx (rowOf (N := 3) r) = r := by decide +kernel
theorem idxSurj4 : ∀ r < 2 ^ 4, idx (rowOf (N := 4) r) = r := by decide +kernel

theorem g2_count3 : (bitsOf (K 3) (g2map 3)).length = 133 := by decide +kernel
theorem g2_count4 : (bitsOf (K 4) (g2map 4)).length = 1078 := by decide +kernel

open Classical in
/-- Appendix F: `|G_2(3)| = 133`. -/
theorem card_G2_3 : (univ.filter (fun f : BFun 3 => G 3 2 f)).card = 133 := by
  rw [card_of_spec idxFacts3 idxSurj3 _ (g2map 3) (G2_iff idxFacts3), g2_count3]

open Classical in
/-- Appendix F: `|G_2(4)| = 1078`. -/
theorem card_G2_4 : (univ.filter (fun f : BFun 4 => G 4 2 f)).card = 1078 := by
  rw [card_of_spec idxFacts4 idxSurj4 _ (g2map 4) (G2_iff idxFacts4), g2_count4]

end Llrg.Count
