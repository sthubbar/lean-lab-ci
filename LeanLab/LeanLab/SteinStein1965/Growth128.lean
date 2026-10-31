/-
AI wrote this Lean code for CODEX task128.
P0073, Section 2, page 428: a new basis element is eventually generated.
Unbounded odd input and one odd current basis element suffice for eventual growth.
No claim excludes failures at individual targets. Goldbach is open.
-/
import LeanLab.SteinStein1965.Soundness

namespace LeanLab.SteinStein1965

/-- Equation 2.3, pages 427 and 428: a step preserves the current basis as a prefix. -/
theorem step_basis_prefix128 (isA : ℕ → Bool) (st : List ℕ × List ℕ) (m : ℕ) :
    st.1 <+: (step isA st m).1 := by
  unfold step
  split
  · exact List.prefix_rfl
  · split
    · exact List.prefix_append _ _
    · exact List.prefix_rfl

/-- Page 428: continuing a scan preserves every current basis element in order. -/
theorem scan_basis_prefix128 (isA : ℕ → Bool) (L : List ℕ) (st : List ℕ × List ℕ) :
    st.1 <+: (L.foldl (step isA) st).1 := by
  induction L generalizing st with
  | nil => exact List.prefix_rfl
  | cons m L ih =>
    exact (step_basis_prefix128 isA st m).trans (ih (step isA st m))

/-- Equation 2.3, page 427: an uncovered target with a candidate forces one new element. -/
theorem step_grows128 (isA : ℕ → Bool) (st : List ℕ × List ℕ) (m : ℕ)
    (hc : covers st.1 m = false) (hn : cands isA st.1 m ≠ []) :
    st.1.length < (step isA st m).1.length := by
  unfold step
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  cases he : (cands isA st.1 m).max? with
  | none => exact False.elim (hn (List.max?_eq_none_iff.mp he))
  | some a => simp

/-- Page 428: a scan containing such a target grows, even if earlier targets add elements. -/
theorem scan_grows128 (isA : ℕ → Bool) (L : List ℕ) (st : List ℕ × List ℕ) (m : ℕ)
    (hm : m ∈ L) (hc : covers st.1 m = false) (hn : cands isA st.1 m ≠ []) :
    st.1.length < (L.foldl (step isA) st).1.length := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hm
  simp only [List.foldl_append, List.foldl_cons]
  let mid := pre.foldl (step isA) st
  have hp : st.1 <+: mid.1 := scan_basis_prefix128 isA pre st
  have hs := step_basis_prefix128 isA mid m
  have ht := scan_basis_prefix128 isA post (step isA mid m)
  by_cases hbefore : st.1.length < mid.1.length
  · exact lt_of_lt_of_le hbefore (hs.trans ht).length_le
  · have heq : mid.1 = st.1 := (hp.eq_of_length_le (by omega)).symm
    have hg := step_grows128 isA mid m (by simpa [heq] using hc) (by simpa [heq] using hn)
    exact lt_of_le_of_lt hp.length_le (lt_of_lt_of_le hg ht.length_le)

/-- Page 428: unbounded odd input supplies a future uncovered even target with a candidate. -/
theorem future_candidate128 (isA : ℕ → Bool) (bs : List ℕ) (b N : ℕ)
    (hb : b ∈ bs) (hbOdd : Odd b)
    (hInput : ∀ T, ∃ a, T < a ∧ isA a = true ∧ Odd a) :
    ∃ m, N < m ∧ Even m ∧ covers bs m = false ∧ cands isA bs m ≠ [] := by
  obtain ⟨a, ha, haA, haOdd⟩ := hInput (2 * bs.sum + N)
  have hc : covers bs (a + b) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨x, hx, y, hy, hxy⟩ := (covers_iff _ _).mp h
    have hxSum := List.le_sum_of_mem hx
    have hySum := List.le_sum_of_mem hy
    omega
  have hmem : a ∈ cands isA bs (a + b) := by
    apply List.mem_map.mpr
    refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, by simp⟩
    simp [haA]
  exact ⟨a + b, by omega, haOdd.add_odd hbOdd, hc,
    fun he => by rw [he] at hmem; contradiction⟩

/-- Page 428: every current finite state with an odd basis member eventually grows. -/
theorem eventual_growth128 (isA : ℕ → Bool) (st : List ℕ × List ℕ) (b N : ℕ)
    (hb : b ∈ st.1) (hbOdd : Odd b)
    (hInput : ∀ T, ∃ a, T < a ∧ isA a = true ∧ Odd a) :
    ∃ M, N < M ∧ st.1.length <
      ((evensIn (N + 1) M).foldl (step isA) st).1.length := by
  obtain ⟨M, hM, hEven, hc, hn⟩ := future_candidate128 isA st.1 b N hb hbOdd hInput
  exact ⟨M, hM, scan_grows128 isA _ st M
    (mem_evensIn.mpr ⟨by omega, le_rfl, Nat.even_iff.mp hEven⟩) hc hn⟩

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.step_basis_prefix128
#print axioms LeanLab.SteinStein1965.scan_basis_prefix128
#print axioms LeanLab.SteinStein1965.step_grows128
#print axioms LeanLab.SteinStein1965.scan_grows128
#print axioms LeanLab.SteinStein1965.future_candidate128
#print axioms LeanLab.SteinStein1965.eventual_growth128
