import LeanLab.Zhan1991.SPLIT_major_1122

/-!
P0068 Zhan 1991, page 271, step 4 of SPLIT_major_1122, the truncated singular series
`Σ_{q ≤ Q₁} μ(q) c_q(N)/φ(q)³ = 𝔖(N) + O(L⁻¹)`, split into the full series identity and the tail
bound; `singTruncEval_of_parts` is PROVED from the two. burst-20261122, session S80.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real
open scoped ArithmeticFunction.Moebius

/-- The term `μ(q) c_q(N)/φ(q)³` of the singular series, page 271, `0` at `q = 0`. -/
noncomputable def singTerm (N q : ℕ) : ℝ :=
  if q = 0 then 0 else (μ q : ℝ) / (Nat.totient q : ℝ) ^ 3 * ramanujanC q N

/-- Page 271, the singular series as a series: `Σ_q μ(q) c_q(N)/φ(q)³ = 𝔖(N)` for odd `N`. -/
def SingSeriesIdentity : Prop := ∀ N : ℕ, Odd N → HasSum (singTerm N) (Sing N)

/-- Page 271, the tail beyond `Q₁ = L^d` is `O(L⁻¹)`, with the series absolutely convergent. -/
def SingSeriesTail : Prop :=
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
    Summable (fun q => |singTerm N q|) ∧
    ∑' q : ℕ, (if ⌊Real.log N ^ d⌋₊ < q then |singTerm N q| else 0) ≤ K / Real.log N

/-- `singTrunc` is the partial sum of `singTerm` up to `⌊Q⌋`. PROVED. -/
theorem singTrunc_eq (N : ℕ) (Q : ℝ) :
    singTrunc N Q = ∑ q ∈ Finset.range (⌊Q⌋₊ + 1), singTerm N q := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
  have h0 : singTerm N 0 = 0 := by simp [singTerm]
  rw [h0, zero_add]
  unfold singTrunc
  apply Finset.sum_congr
  · ext q; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  intro q hq
  have : q ≠ 0 := by have := (Finset.mem_Icc.mp hq).1; omega
  simp [singTerm, this]

set_option maxHeartbeats 800000 in
/-- Page 271, step 4 from the series identity and the tail bound. PROVED. -/
theorem singTruncEval_of_parts (hI : SingSeriesIdentity) (hT : SingSeriesTail) :
    SingTruncEval := by
  obtain ⟨d₀, hd₀, hT'⟩ := hT
  refine ⟨d₀, hd₀, fun d hd => ?_⟩
  obtain ⟨K, N₀, h⟩ := hT' d hd
  refine ⟨K, N₀, fun N hN hN0 => ?_⟩
  obtain ⟨hsum, htail⟩ := h N hN hN0
  set Q := ⌊Real.log N ^ d⌋₊
  have hS := hI N hN
  have hsf : Summable (singTerm N) := hS.summable
  -- Sing N = partial + tail
  have hsplit := hsf.sum_add_tsum_nat_add (Q + 1)
  have htrunc : singTrunc N (Real.log N ^ d) = ∑ q ∈ Finset.range (Q + 1), singTerm N q :=
    singTrunc_eq N _
  have heq : singTrunc N (Real.log N ^ d) - Sing N = -∑' q : ℕ, singTerm N (q + (Q + 1)) := by
    rw [htrunc, ← hS.tsum_eq, ← hsplit]; ring
  rw [heq, abs_neg]
  have hsabs : Summable (fun q : ℕ => |singTerm N (q + (Q + 1))|) :=
    (summable_nat_add_iff (Q + 1)).mpr hsum
  calc |∑' q : ℕ, singTerm N (q + (Q + 1))| ≤ ∑' q : ℕ, |singTerm N (q + (Q + 1))| := by
        have hs' : Summable (fun q : ℕ => ‖singTerm N (q + (Q + 1))‖) := by
          simpa [Real.norm_eq_abs] using hsabs
        have := norm_tsum_le_tsum_norm hs'
        simpa [Real.norm_eq_abs] using this
    _ = ∑' q : ℕ, (if Q < q then |singTerm N q| else 0) := by
        have hind : Summable (fun q : ℕ => if Q < q then |singTerm N q| else 0) :=
          hsum.of_nonneg_of_le (fun q => by split_ifs <;> simp [abs_nonneg])
            (fun q => by split_ifs <;> simp [abs_nonneg])
        rw [← hind.sum_add_tsum_nat_add (Q + 1)]
        have : ∑ q ∈ Finset.range (Q + 1), (if Q < q then |singTerm N q| else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro q hq
          have : ¬ Q < q := by have := Finset.mem_range.mp hq; omega
          simp [this]
        rw [this, zero_add]
        apply tsum_congr
        intro q
        have : Q < q + (Q + 1) := by omega
        simp [this]
    _ ≤ K / Real.log N := htail

/-- LEAF: Page 271, the singular series identity: `μ(q) c_q(N)/φ(q)³` is multiplicative with Euler
factor `1 - 1/(p-1)²` for `p ∣ N` and `1 + 1/(p-1)³` otherwise, absolutely summable since
`|c_q(N)| ≤ (q, N)`, so its sum is `Sing N`. MEDIUM. -/
theorem singSeriesIdentity_leaf : SingSeriesIdentity := by
  sorry

/-- LEAF: Page 271, the tail of the singular series beyond `Q₁ = L^d`:
`Σ_{q > Q₁} |μ(q) c_q(N)|/φ(q)³ ≪ Q₁^{-1+ε} (log log N)³ ≪ L⁻¹` for `d ≥ 2`. MEDIUM. -/
theorem singSeriesTail_leaf : SingSeriesTail := by
  sorry

/-- Step 4 of the major arc split through its two LEAFs. -/
theorem singTruncEval_split : SingTruncEval :=
  singTruncEval_of_parts singSeriesIdentity_leaf singSeriesTail_leaf

end LeanLab.Zhan1991
