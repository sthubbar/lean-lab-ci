/-
Stein and Stein 1965, P0073, unit U-0954, run 20261018T1603Z-12862.
Soundness of the S-algorithm of Section 2: every even in the scanned range is either a
recorded failure or a sum of two output elements, and every output element comes from the
input set. Consequences: the output is a basis past the last failure, and a failure-free
prime run with `p0 = 3` gives binary Goldbach on its range.
AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
-/
import LeanLab.SteinStein1965.Statements

namespace LeanLab.SteinStein1965

/-! ### `primeB` is complete as well as sound -/

theorem noDivFrom_complete (n : ℕ) : ∀ fuel d, n < (d + fuel) * (d + fuel) →
    (∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n) → noDivFrom n (fuel + 1) d = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro d h _
    simp only [Nat.add_zero] at h
    simp [noDivFrom, h]
  | succ k ih =>
    intro d h hnd
    simp only [noDivFrom]
    by_cases h1 : n < d * d
    · simp [h1]
    · rw [if_neg h1]
      have h2 : ¬ n % d = 0 := fun h0 =>
        hnd d le_rfl (by omega) (Nat.dvd_of_mod_eq_zero h0)
      rw [if_neg h2]
      apply ih (d + 1)
      · have : d + 1 + k = d + (k + 1) := by omega
        rw [this]; exact h
      · intro m hm hmm; exact hnd m (by omega) hmm

theorem primeB_complete {n : ℕ} (hp : n.Prime) : primeB n = true := by
  have h2 := hp.two_le
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨h2, ?_⟩
  have hn : n = (n - 1) + 1 := by omega
  have key := noDivFrom_complete n (n - 1) 2 (by
      have : 2 + (n - 1) = n + 1 := by omega
      rw [this]; nlinarith)
    (fun m hm hmm hdvd => by
      rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · omega
      · subst h; nlinarith)
  rw [← hn] at key
  exact key

theorem primeB_iff (n : ℕ) : primeB n = true ↔ n.Prime :=
  ⟨primeB_sound, primeB_complete⟩

theorem primeA_iff (p0 n : ℕ) :
    primeA p0 n = true ↔ p0 ≤ n ∧ (n = 1 ∨ (n ≠ 2 ∧ n.Prime)) := by
  simp [primeA, primeB_iff]

/-! ### `covers` means "is a sum of two elements" -/

theorem covers_iff (bs : List ℕ) (m : ℕ) :
    covers bs m = true ↔ ∃ x ∈ bs, ∃ y ∈ bs, x + y = m := by
  simp only [covers, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem]
  constructor
  · rintro ⟨x, hx, hxm, hy⟩
    exact ⟨x, hx, m - x, hy, by omega⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, by omega, by simpa using hy⟩

theorem covers_append {bs : List ℕ} {m : ℕ} (l : List ℕ) (h : covers bs m = true) :
    covers (bs ++ l) m = true := by
  rw [covers_iff] at h ⊢
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨x, List.mem_append_left _ hx, y, List.mem_append_left _ hy, hxy⟩

theorem mem_cands {isA : ℕ → Bool} {bs : List ℕ} {m a : ℕ} (h : a ∈ cands isA bs m) :
    isA a = true ∧ ∃ b ∈ bs, a + b = m := by
  simp only [cands, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨b, ⟨hb, hbm, hA⟩, rfl⟩ := h
  exact ⟨hA, b, hb, by omega⟩

theorem mem_evensIn {lo hi m : ℕ} : m ∈ evensIn lo hi ↔ lo ≤ m ∧ m ≤ hi ∧ m % 2 = 0 := by
  simp only [evensIn, List.mem_filter, List.mem_range'_1, beq_iff_eq]
  omega

/-! ### The invariant -/

/-- `m` is either a recorded failure or covered by the current basis. -/
def Done (st : List ℕ × List ℕ) (m : ℕ) : Prop := m ∈ st.2 ∨ covers st.1 m = true

theorem step_mono (isA : ℕ → Bool) (st : List ℕ × List ℕ) (m m' : ℕ) (h : Done st m') :
    Done (step isA st m) m' := by
  unfold step
  split_ifs
  · exact h
  · split
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (covers_append _ h)
    · rcases h with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr h

theorem step_self (isA : ℕ → Bool) (st : List ℕ × List ℕ) (m : ℕ) :
    Done (step isA st m) m := by
  unfold step
  split_ifs with hc
  · exact Or.inr hc
  · split
    · rename_i a ha
      have hmem := List.max?_mem ha
      obtain ⟨_, b, hb, hab⟩ := mem_cands hmem
      refine Or.inr ((covers_iff _ _).mpr ⟨a, List.mem_append_right _ (List.mem_singleton_self a),
        b, List.mem_append_left _ hb, by omega⟩)
    · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self m))

theorem foldl_done (isA : ℕ → Bool) : ∀ (L : List ℕ) (st : List ℕ × List ℕ) (m : ℕ),
    (Done st m ∨ m ∈ L) → Done (L.foldl (step isA) st) m := by
  intro L
  induction L with
  | nil =>
    intro st m h
    rcases h with h | h
    · exact h
    · simp at h
  | cons x t ih =>
    intro st m h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · exact Or.inl (step_mono isA st x m h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (step_self isA st m)
      · exact Or.inr h

/-- **Soundness of the S-algorithm.** Every even `2 a0 ≤ m ≤ N1` is a recorded failure or a
sum `b_i + b_j` of two output elements. -/
theorem sAlg_cover (isA : ℕ → Bool) (a0 a1 N1 m : ℕ) (hm : m % 2 = 0)
    (hlo : 2 * a0 ≤ m) (hhi : m ≤ N1) :
    m ∈ (sAlg isA a0 a1 N1).2 ∨ ∃ x ∈ (sAlg isA a0 a1 N1).1, ∃ y ∈ (sAlg isA a0 a1 N1).1,
      x + y = m := by
  have := foldl_done isA (evensIn (2 * a0) N1) ([a0, a1], []) m
    (Or.inr (mem_evensIn.mpr ⟨hlo, hhi, hm⟩))
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr ((covers_iff _ _).mp h)

/-- Every recorded failure is an even number in the scanned range. -/
theorem foldl_fail (isA : ℕ → Bool) : ∀ (L : List ℕ) (st : List ℕ × List ℕ) (f : ℕ),
    f ∈ (L.foldl (step isA) st).2 → f ∈ st.2 ∨ f ∈ L := by
  intro L
  induction L with
  | nil => intro st f h; exact Or.inl h
  | cons x t ih =>
    intro st f h
    simp only [List.foldl_cons] at h
    rcases ih _ f h with h | h
    · unfold step at h
      split_ifs at h
      · exact Or.inl h
      · split at h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · simp at h; subst h; exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem sAlg_fail_mem (isA : ℕ → Bool) (a0 a1 N1 f : ℕ) (h : f ∈ (sAlg isA a0 a1 N1).2) :
    2 * a0 ≤ f ∧ f ≤ N1 ∧ f % 2 = 0 := by
  rcases foldl_fail isA _ _ f h with h | h
  · simp at h
  · exact mem_evensIn.mp h

/-- Every output element is a seed `a0`, `a1` or a member of the input set. -/
theorem foldl_elems (isA : ℕ → Bool) (a0 a1 : ℕ) : ∀ (L : List ℕ) (st : List ℕ × List ℕ),
    (∀ b ∈ st.1, b = a0 ∨ b = a1 ∨ isA b = true) →
    ∀ b ∈ (L.foldl (step isA) st).1, b = a0 ∨ b = a1 ∨ isA b = true := by
  intro L
  induction L with
  | nil => intro st h; exact h
  | cons x t ih =>
    intro st h
    simp only [List.foldl_cons]
    apply ih
    unfold step
    split_ifs
    · exact h
    · split
      · rename_i a ha
        intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact h b hb
        · simp at hb; subst hb
          exact Or.inr (Or.inr (mem_cands (List.max?_mem ha)).1)
      · exact h

theorem sAlg_elems (isA : ℕ → Bool) (a0 a1 N1 b : ℕ) (hb : b ∈ (sAlg isA a0 a1 N1).1) :
    b = a0 ∨ b = a1 ∨ isA b = true := by
  refine foldl_elems isA a0 a1 _ _ ?_ b hb
  intro b hb; simp at hb; rcases hb with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- **The output is a basis for the interval it claims**: past the last failure, from any
`N0 ≥ 2 a0`, the S-sequence is a binary additive basis for the evens up to `N1`. -/
theorem sAlg_basis (isA : ℕ → Bool) (a0 a1 N1 N0 : ℕ) (h0 : 2 * a0 ≤ N0)
    (hf : ∀ f ∈ (sAlg isA a0 a1 N1).2, f < N0) : IsBasisFor (sAlg isA a0 a1 N1).1 N0 N1 := by
  intro m hm hlo hhi
  rcases sAlg_cover isA a0 a1 N1 m hm (by omega) hhi with h | h
  · have := hf m h; omega
  · exact h

/-- With no failures, the S-sequence is a basis for all evens `2 a0 ≤ 2n ≤ N1`. -/
theorem sAlg_basis_of_nil (isA : ℕ → Bool) (a0 a1 N1 : ℕ) (h : (sAlg isA a0 a1 N1).2 = []) :
    IsBasisFor (sAlg isA a0 a1 N1).1 (2 * a0) N1 :=
  sAlg_basis isA a0 a1 N1 _ le_rfl (by simp [h])

/-! ### The prime case -/

theorem nextA_three : nextA 3 = 5 := by decide

theorem nextA_gt (p0 : ℕ) (h : (nextA p0).Prime) : p0 < nextA p0 := by
  unfold nextA at *
  cases hf : (List.range' (p0 + 1) (p0 + 3)).find? (fun n => n != 2 && primeB n) with
  | none => rw [hf] at h; exact absurd h Nat.not_prime_zero
  | some a =>
    simp only [Option.getD_some]
    have := List.mem_of_find?_eq_some hf
    rw [List.mem_range'_1] at this
    omega

theorem sPrime_elems_prime (p0 N1 b : ℕ) (hp0 : p0.Prime)
    (ha1 : (nextA p0).Prime) (hb : b ∈ (sPrime p0 N1).1) : b.Prime ∧ p0 ≤ b := by
  rcases sAlg_elems _ _ _ _ b hb with h | h | h
  · subst h; exact ⟨hp0, le_rfl⟩
  · subst h
    exact ⟨ha1, (nextA_gt p0 ha1).le⟩
  · rw [primeA_iff] at h
    rcases h with ⟨hle, h | ⟨_, h⟩⟩
    · subst h; exact absurd hp0.two_le (by omega)
    · exact ⟨h, hle⟩

/-- **A failure-free S-run from `p0 = 3` verifies binary Goldbach on its range.** -/
theorem goldbach_of_sPrime3 (N : ℕ) (h : (sPrime 3 N).2 = []) : EvenGoldbachUpTo N := by
  intro m hev h4 hN
  have hm : m % 2 = 0 := Nat.even_iff.mp hev
  by_cases h6 : m < 6
  · have : m = 4 := by omega
    subst this
    exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  · have hb := sAlg_basis_of_nil (primeA 3) 3 (nextA 3) N h m hm (by omega) hN
    obtain ⟨x, hx, y, hy, hxy⟩ := hb
    have ha1 : (nextA 3).Prime := by rw [nextA_three]; norm_num
    exact ⟨x, y, (sPrime_elems_prime 3 N x Nat.prime_three ha1 hx).1,
      (sPrime_elems_prime 3 N y Nat.prime_three ha1 hy).1, hxy⟩

/-- Goldbach to `10^7` follows from the cited failure-free S-run, Section 3, p. 429. -/
theorem goldbach_1e7_of_sBasis3 (h : SBasisClaim3) : GoldbachClaim :=
  goldbach_of_sPrime3 _ h

end LeanLab.SteinStein1965

#print axioms LeanLab.SteinStein1965.primeB_complete
#print axioms LeanLab.SteinStein1965.primeA_iff
#print axioms LeanLab.SteinStein1965.covers_iff
#print axioms LeanLab.SteinStein1965.sAlg_cover
#print axioms LeanLab.SteinStein1965.sAlg_fail_mem
#print axioms LeanLab.SteinStein1965.sAlg_elems
#print axioms LeanLab.SteinStein1965.sAlg_basis
#print axioms LeanLab.SteinStein1965.sAlg_basis_of_nil
#print axioms LeanLab.SteinStein1965.sPrime_elems_prime
#print axioms LeanLab.SteinStein1965.goldbach_of_sPrime3
#print axioms LeanLab.SteinStein1965.goldbach_1e7_of_sBasis3
