/-
Appendix F: `G_3(4)` contains every function of 4 inputs, and every function of 5 inputs is in
`G_5(5)`, from the kernel-checked certificate `cert_ok`.
-/
import LlrgLean.G3Cert

namespace Llrg.Count

lemma decode_xor' {N : ℕ} (a b : ℕ) (x : Fin N → Bool) :
    decode (a ^^^ b) x = xor (decode a x) (decode b x) := by simp [decode, Nat.testBit_xor]
lemma decode_and' {N : ℕ} (a b : ℕ) (x : Fin N → Bool) :
    decode (a &&& b) x = (decode a x && decode b x) := by simp [decode, Nat.testBit_and]
lemma decode_or' {N : ℕ} (a b : ℕ) (x : Fin N → Bool) :
    decode (a ||| b) x = (decode a x || decode b x) := by simp [decode, Nat.testBit_or]

lemma fld_lt (w k : ℕ) : fld w k < 2 ^ 16 := Nat.mod_lt _ (by norm_num)

/-- Elements of the depth-2 bitmap are depth-2 functions. -/
lemma G2_of_B4 {a : ℕ} (ha : a < 2 ^ 16) (hb : B4.testBit a = true) : G 4 2 (decode a) := by
  have hK : a < K 4 := by simpa [K] using ha
  rw [G2_iff idxFacts4, code_decode idxFacts4 idxSurj4 hK, g2map4_eq]; exact hb

/-- A passing certificate entry gives a depth-3 construction. -/
theorem G3_of_chk {c w : ℕ} (hc : c < 2 ^ 16) (h : chk B4 c w = true) : G 4 3 (decode c) := by
  unfold chk at h
  split_ifs at h with h0 h1 h2
  · simp only [Bool.and_eq_true] at h
    have hx : c ^^^ fld w 0 < 2 ^ 16 := Nat.xor_lt_two_pow hc (fld_lt w 0)
    have := G.xor 2 _ _ (G2_of_B4 (fld_lt w 0) h.1) (G2_of_B4 hx h.2)
    convert this using 1; funext x
    rw [decode_xor']; cases decode (N := 4) c x <;> cases decode (N := 4) (fld w 0) x <;> rfl
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩, he⟩ := h
    have := G.and 2 [decode (fld w 0), decode (fld w 1), decode (fld w 2), decode (fld w 3)]
      (by simp) (by simp) (by
        intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact G2_of_B4 (fld_lt w 0) h1'
        · exact G2_of_B4 (fld_lt w 1) h2'
        · exact G2_of_B4 (fld_lt w 2) h3'
        · exact G2_of_B4 (fld_lt w 3) h4')
    convert this using 1; funext x
    rw [← he]; simp [decode_and', Bool.and_assoc]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩, he⟩ := h
    have := G.or 2 [decode (fld w 0), decode (fld w 1), decode (fld w 2), decode (fld w 3)]
      (by simp) (by simp) (by
        intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl
        · exact G2_of_B4 (fld_lt w 0) h1'
        · exact G2_of_B4 (fld_lt w 1) h2'
        · exact G2_of_B4 (fld_lt w 2) h3'
        · exact G2_of_B4 (fld_lt w 3) h4')
    convert this using 1; funext x
    rw [← he]; simp [decode_or', Bool.or_assoc]

/-- Appendix F: every function of 4 inputs has depth at most 3 (`|G_3(4)| = 2^16`). -/
theorem all_G3_4 (f : BFun 4) : G 4 3 f := by
  have hc : code f < 2 ^ 16 := by simpa [K] using code_lt f
  obtain ⟨w, hw⟩ := cert_all (code f) hc
  have := G3_of_chk hc hw
  rwa [decode_code idxFacts4] at this

/-- Appendix F: every function of 5 inputs has depth at most 5. -/
theorem all_G5_5 (f : BFun 5) : G 5 5 f := all_G5_of_all_G3 all_G3_4 f

end Llrg.Count
