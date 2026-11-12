/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372.

ROUTE BURST session 8, part 2, 2026-11-12. The Section 5 leaf `Burst4Split.reduction27A_wide`
split along pp. 363 and 364:

* PROVED: `farey_cover`, the Farey dissection of display 22, p. 363: every point of the window
  `(ξ - 1/H, ξ + 1/H) ∩ 𝔪` lies on an arc `|α - a/q| < 1/(qQ)` with `q` in the family
  `Y(2^j)` of p. 363 for a dyadic `2^j ≤ Q`, `1 ≤ a ≤ q`, `(a, q) = 1`.
* PROVED: `window_le_blocks`, the window integral is at most the sum over the dyadic blocks
  of the arc integrals, by `farey_cover` and the union bound.
* PROVED: `minor_block_bound`, displays 23 to 27, p. 364, for one dyadic block, the sum over
  the numerators `a'` whose arc meets the window, as in display 25: by
  `S(a/q + η) = μ/φ T(η) + R(η, q, a)` the block is at most twice its `R` part plus twice its
  `T` part, `block_le_R_T`; the `T` part is `≪ N L^{-A-2}` on the minor arcs, `Tpart_le`, by the
  tail of display 9, Parseval, `|Y(M)|` of display 21 and `φ(q) ≫ q/log q`.
* LEAF, sorry: `rpart_block_bound`, the `R` part: display 13, Gallagher's lemma,
  P. X. Gallagher, Invent. Math. 11, 1970, pp. 329 to 339, and Cauchy and Schwarz bound it by
  the character expression `energyA` of `Decomp1624`.
* PROVED: `reduction27A_wide_of_split`, the leaf `reduction27A_wide` from the two pieces, with
  the dyadic count `J + 1 ≤ L`.

The final theorem `perelliPintz_p2 : MainTheorem` has the type of `perelliPintz` and no sorry
of its own; it is CONDITIONAL ON `siegel_walfisz_uniform`, `shiu_d2`, `rpart_block_bound` and
`Decomp1624.energy_decayA`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst8P2
import LeanLab.PerelliPintz1992.FareyFamily97

namespace LeanLab.PerelliPintz1992.Burst8P2
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst4Split

noncomputable section

/-- `Finset.mem_filter` with the decidability instance found by unification. -/
lemma mem_filter_of {ι : Type*} {p : ι → Prop} {inst : DecidablePred p} {s : Finset ι} {a : ι}
    (h1 : a ∈ s) (h2 : p a) : a ∈ @Finset.filter ι p inst s := Finset.mem_filter.mpr ⟨h1, h2⟩

/-- `Finset.mem_filter` backwards, with the instance found by unification. -/
lemma of_mem_filter {ι : Type*} {p : ι → Prop} {inst : DecidablePred p} {s : Finset ι} {a : ι}
    (h : a ∈ @Finset.filter ι p inst s) : a ∈ s ∧ p a := Finset.mem_filter.mp h

lemma card_filter_le_of {ι : Type*} {p : ι → Prop} {inst : DecidablePred p} (s : Finset ι) :
    (@Finset.filter ι p inst s).card ≤ s.card := Finset.card_filter_le _ _

/-! ### Definitions, p. 363 -/

/-- The number of dyadic blocks: `2^J ≤ ⌊Q⌋ < 2^{J+1}`. -/
def Jn (N : ℕ) : ℕ := Nat.log 2 ⌊Q N⌋₊

/-- The arc `|α - a/q| < 1/(qQ)` of p. 363, intersected with the minor arcs. -/
def arcM (N : ℕ) (A : ℝ) (q a : ℕ) : Set ℝ :=
  Ioo ((a : ℝ) / q - 1 / ((q : ℝ) * Q N)) ((a : ℝ) / q + 1 / ((q : ℝ) * Q N)) ∩ minorArcs N A

open Classical in
/-- The numerators `a'` of display 25, p. 364: the `a ∈ As q` whose arc `|α - a/q| < 1/(qQ)`
meets the window `|α - ξ| < 1/H`. -/
def aWin (N : ℕ) (ε ξ : ℝ) (q : ℕ) : Finset ℕ :=
  (Decomp1519.As q).filter
    (fun a => ∃ α : ℝ, |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q N) ∧ |α - ξ| < 1 / H N ε)

/-- The arc integrals of the dyadic block `M`, display 25, p. 364:
`Σ_{q ∈ Y(M)} Σ_{a'} ∫_{|η| < 1/(qQ), a'/q + η ∈ 𝔪} |S(a'/q + η)|² dη`, the sum over the
numerators `a'` whose arc meets the window, as on p. 364. -/
def blockInt (N : ℕ) (ε ξ A : ℝ) (M : ℕ) : ℝ :=
  ∑ q ∈ Y N ε ξ M, ∑ a ∈ aWin N ε ξ (q : ℕ), ∫ α in arcM N A q a, ‖S N α‖ ^ 2


lemma minorArcs_measurable (N : ℕ) (A : ℝ) : MeasurableSet (minorArcs N A) := by
  unfold minorArcs majorArcs
  refine measurableSet_Ioo.diff ?_
  refine MeasurableSet.biUnion (Set.to_countable _) fun q _ => ?_
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ => measurableSet_Ioo

lemma arcM_measurable (N : ℕ) (A : ℝ) (q a : ℕ) : MeasurableSet (arcM N A q a) :=
  measurableSet_Ioo.inter (minorArcs_measurable N A)

/-! ### The `T` part of the block, PROVED

On the arc `a/q`, `S(a/q + η) = μ(q)/φ(q) T(η) + R(η, q, a)`, p. 360. The `T` part is small on the
minor arcs: for `q ≤ L^{B/2}` the minor arc condition gives `|η| ≥ L^B/(qN)`, display 9 tail,
and for `q > L^{B/2}` the factor `μ²/φ² ≤ 1/φ²` with Parseval suffices, with `|Y(M)|` from
display 21. This is the `N L^{-A-1}` term of display 25. -/

/-! #### Totient lower bound, copied from `Pintz2021.DecompJ834`, proofs unchanged -/

theorem prod_le_card_succ_mul_prod_pred {s : Finset ℕ} (h2 : ∀ p ∈ s, 2 ≤ p) :
    ∏ p ∈ s, p ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  revert h2
  refine Finset.induction_on_max s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h2
    have h2a : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => h2 p (Finset.mem_insert_of_mem hp)
    have han : a ∉ s := fun h => absurd (ha a h) (lt_irrefl a)
    have hP := ih h2s
    have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨h2s x hx, by have := ha x hx; omega⟩
    have hcard : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have ham : s.card + 2 ≤ a := by omega
    obtain ⟨t, ht⟩ : ∃ t, a = s.card + 2 + t := ⟨a - (s.card + 2), by omega⟩
    have ha1 : a - 1 = s.card + 1 + t := by omega
    rw [Finset.prod_insert han, Finset.prod_insert han, Finset.card_insert_of_notMem han, ha1, ht]
    calc (s.card + 2 + t) * ∏ p ∈ s, p
        ≤ (s.card + 2 + t) * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
          Nat.mul_le_mul_left _ hP
      _ = ((s.card + 2 + t) * (s.card + 1)) * ∏ p ∈ s, (p - 1) := by ring
      _ ≤ ((s.card + 1 + 1) * (s.card + 1 + t)) * ∏ p ∈ s, (p - 1) := by
          refine Nat.mul_le_mul_right _ ?_
          nlinarith
      _ = (s.card + 1 + 1) * ((s.card + 1 + t) * ∏ p ∈ s, (p - 1)) := by ring

/-- `n ≤ φ(n) * (number of distinct prime divisors of n + 1)`. -/
theorem totient_mul_card_succ_ge (n : ℕ) :
    n ≤ Nat.totient n * (n.primeFactors.card + 1) := by
  have hid := Nat.totient_mul_prod_primeFactors n
  have hP : ∏ p ∈ n.primeFactors, p ≤
      (n.primeFactors.card + 1) * ∏ p ∈ n.primeFactors, (p - 1) :=
    prod_le_card_succ_mul_prod_pred fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * (n.primeFactors.card + 1)) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * ((n.primeFactors.card + 1) *
            ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ hP
      _ = (Nat.totient n * (n.primeFactors.card + 1)) *
            ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

theorem totient_ge_div_card_succ (n : ℕ) :
    (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) ≤ (Nat.totient n : ℝ) := by
  have h := totient_mul_card_succ_ge n
  have hc : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hc]
  have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * ((n.primeFactors.card : ℝ) + 1) := by
    exact_mod_cast h
  linarith

theorem two_pow_card_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, 2 ≤ p) → 2 ^ s.card ≤ ∏ p ∈ s, p := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert a s ha ih =>
        intro hs
        have h2a : 2 ≤ a := hs a (Finset.mem_insert_self a s)
        have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
        calc 2 ^ s.card * 2 ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul (ih h2s) h2a
          _ = a * ∏ p ∈ s, p := by ring
  have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    key _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : 0 < n := by omega
  exact h1.trans (Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd n))

theorem card_primeFactors_le_log_div {n : ℕ} (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 := two_pow_card_primeFactors_le hn
  have h2' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast h2
  have hbase : (0 : ℝ) < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hlog := Real.log_le_log hbase h2'
  rw [Real.log_pow] at hlog
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  linarith

/-- **`φ(n) ≫ n / log n`**: `log 2 · n / (1 + log n) ≤ φ(n)` for `n ≥ 1`, the shape the coefficient
bound `‖c'‖ ≪ q^{-3/2} (1 + log q)^2` needs. -/
theorem totient_ge_log_two_mul_div {n : ℕ} (hn : 1 ≤ n) :
    Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤ (Nat.totient n : ℝ) := by
  have hφ := totient_ge_div_card_succ n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hlog1 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk := card_primeFactors_le_log_div hn
  -- `k + 1 ≤ (1 + log n) / log 2`
  have hk2 : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [le_div_iff₀ hlog2] at hk
    linarith
  have hk1 : ((n.primeFactors.card : ℝ) + 1) * Real.log 2 ≤ 1 + Real.log n := by
    nlinarith [hk2, hlog2lt]
  have hone : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  -- `log 2 · n / (1 + log n) ≤ n / (k + 1)`
  have hstep : Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤
      (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + Real.log n) hone]
    nlinarith [hk1, hnpos, hlog2]
  exact hstep.trans hφ


/-! #### The pieces -/

lemma card_As_le_totient {q : ℕ} (hq : 1 ≤ q) : (Decomp1519.As q).card ≤ Nat.totient q := by
  rcases Nat.eq_or_lt_of_le hq with h | h
  · subst h; decide
  · rw [Nat.totient_eq_card_coprime]
    apply Finset.card_le_card
    intro a ha
    obtain ⟨ha1, hcop⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hcop.symm⟩
    rcases Nat.eq_or_lt_of_le h2 with h3 | h3
    · subst h3; simp [Nat.coprime_self] at hcop; omega
    · exact h3

/-- Parseval for `T`, from `Decomp1519.T_orth` at `k = 0`: `∫_{-1/2}^{1/2} |T|² = N + 1`. -/
lemma parseval_T' (N : ℕ) : ∫ η in Ioc (-(1 / 2 : ℝ)) (1 / 2), ‖Decomp1519.T N η‖ ^ 2 = N + 1 := by
  have h := Decomp1519.T_orth (N := N) (k := 0) (by omega)
  have he : ∀ η : ℝ, e (-(2 * ((0 : ℕ) : ℝ) * η)) = 1 := by
    intro η; simp [e]
  simp_rw [he, mul_one] at h
  rw [integral_complex_ofReal] at h
  have := Complex.ofReal_injective h
  rw [this]; push_cast; ring

/-- The translated integral of `|T|²` over an arc of the minor arcs: at most `N + 1`, and at most
`1/(2w)` with `w = L^B/(qN)` when `q ≤ L^{B/2}`. PROVED. -/
lemma arc_T_bound {N : ℕ} {A : ℝ} {q a : ℕ} (hq1 : 1 ≤ q) (ha : a ∈ Decomp1519.As q)
    (hr : 1 / ((q : ℝ) * Q N) ≤ 1 / 2) :
    (∫ α in arcM N A q a, ‖Decomp1519.T N (α - (a : ℝ) / q)‖ ^ 2) ≤ N + 1 ∧
    ((q : ℝ) ≤ L N ^ (Bexp A / 2) → 0 < Decomp1519.wq N A q → Decomp1519.wq N A q ≤ 1 / 2 →
      (∫ α in arcM N A q a, ‖Decomp1519.T N (α - (a : ℝ) / q)‖ ^ 2) ≤
        1 / (2 * Decomp1519.wq N A q)) := by
  set c : ℝ := (a : ℝ) / q with hc
  set g : ℝ → ℝ := fun α => ‖Decomp1519.T N (α - c)‖ ^ 2 with hg
  have hT : Continuous fun η => ‖Decomp1519.T N η‖ ^ 2 := (Decomp1519.continuous_T N).norm.pow 2
  have key := (measurePreserving_add_left volume c).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft c).measurableEmbedding g (arcM N A q a)
  have hgc : ∀ x, g (c + x) = ‖Decomp1519.T N x‖ ^ 2 := fun x => by simp [hg]
  simp_rw [hgc] at key
  change (∫ α in arcM N A q a, g α) ≤ _ ∧ _
  rw [← key]
  have hpre : ∀ x ∈ (fun x => c + x) ⁻¹' arcM N A q a,
      x ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro x hx
    obtain ⟨⟨h1, h2⟩, -⟩ := hx
    constructor <;> linarith
  have hint : IntegrableOn (fun η => ‖Decomp1519.T N η‖ ^ 2) (Ioc (-(1 / 2 : ℝ)) (1 / 2)) :=
    hT.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h0 : ∀ x, 0 ≤ ‖Decomp1519.T N x‖ ^ 2 := fun x => sq_nonneg _
  constructor
  · calc (∫ x in (fun x => c + x) ⁻¹' arcM N A q a, ‖Decomp1519.T N x‖ ^ 2)
        ≤ ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2), ‖Decomp1519.T N x‖ ^ 2 :=
          setIntegral_mono_set hint (Eventually.of_forall fun x => h0 x)
            (Eventually.of_forall hpre)
      _ = N + 1 := parseval_T' N
  · intro hqL hw0 hw2
    have hsub : ∀ x ∈ (fun x => c + x) ⁻¹' arcM N A q a,
        x ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2) \ Ioo (-Decomp1519.wq N A q) (Decomp1519.wq N A q) := by
      intro x hx
      refine ⟨hpre x hx, fun hw => ?_⟩
      obtain ⟨-, hm⟩ := hx
      apply hm.2
      obtain ⟨ha1, hcop⟩ := Finset.mem_filter.mp ha
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha1
      unfold majorArcs
      refine Set.mem_iUnion₂.mpr ⟨q, ⟨hq1, hqL⟩, Set.mem_iUnion₂.mpr ⟨a, ⟨h1, h2, hcop⟩, ?_⟩⟩
      have hw' : Decomp1519.wq N A q = L N ^ Bexp A / (q * N) := rfl
      rw [hw'] at hw
      exact ⟨by simp only [hc] at hw ⊢; linarith [hw.1], by simp only [hc] at hw ⊢; linarith [hw.2]⟩
    calc (∫ x in (fun x => c + x) ⁻¹' arcM N A q a, ‖Decomp1519.T N x‖ ^ 2)
        ≤ ∫ x in Ioc (-(1 / 2 : ℝ)) (1 / 2) \ Ioo (-Decomp1519.wq N A q) (Decomp1519.wq N A q),
            ‖Decomp1519.T N x‖ ^ 2 :=
          setIntegral_mono_set (hint.mono_set diff_subset) (Eventually.of_forall fun x => h0 x)
            (Eventually.of_forall hsub)
      _ ≤ _ := Decomp1519.T_tail N hw0 hw2


/-- The `T` part of the block `M`. -/
def Tpart (N : ℕ) (ε ξ A : ℝ) (M : ℕ) : ℝ :=
  ∑ q ∈ Y N ε ξ M, ∑ a ∈ aWin N ε ξ (q : ℕ),
    ∫ α in arcM N A q a, Decomp1519.muφ q ^ 2 * ‖Decomp1519.T N (α - (a : ℝ) / q)‖ ^ 2

/-- The `R` part of the block `M`, `R(η, q, a) = S(a/q + η) - μ(q)/φ(q) T(η)`, p. 360. -/
def Rpart (N : ℕ) (ε ξ A : ℝ) (M : ℕ) : ℝ :=
  ∑ q ∈ Y N ε ξ M, ∑ a ∈ aWin N ε ξ (q : ℕ),
    ∫ α in arcM N A q a, ‖Decomp1519.R N q a (α - (a : ℝ) / q)‖ ^ 2

/-- The block is at most twice its `R` part plus twice its `T` part, from
`S(a/q + η) = μ/φ T(η) + R(η, q, a)`. PROVED. -/
theorem block_le_R_T (N : ℕ) (ε ξ A : ℝ) (M : ℕ) :
    blockInt N ε ξ A M ≤ 2 * Rpart N ε ξ A M + 2 * Tpart N ε ξ A M := by
  unfold blockInt Rpart Tpart
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  set c : ℝ := (a : ℝ) / (q : ℕ)
  have hR : Continuous fun α => ‖Decomp1519.R N q a (α - c)‖ ^ 2 := by
    unfold Decomp1519.R
    exact (((continuous_S N).comp (continuous_const.add (continuous_id.sub continuous_const))).sub
      (continuous_const.mul ((Decomp1519.continuous_T N).comp
        (continuous_id.sub continuous_const)))).norm.pow 2
  have hT : Continuous fun α => Decomp1519.muφ q ^ 2 * ‖Decomp1519.T N (α - c)‖ ^ 2 :=
    continuous_const.mul (((Decomp1519.continuous_T N).comp
      (continuous_id.sub continuous_const)).norm.pow 2)
  have hS : Continuous fun α => ‖S N α‖ ^ 2 := (continuous_S N).norm.pow 2
  have hsub : arcM N A q a ⊆ Icc (c - 1 / ((q : ℕ) * Q N)) (c + 1 / ((q : ℕ) * Q N)) :=
    inter_subset_left.trans Ioo_subset_Icc_self
  have iR := (hR.integrableOn_Icc (μ := volume)).mono_set hsub
  have iT := (hT.integrableOn_Icc (μ := volume)).mono_set hsub
  have iS := (hS.integrableOn_Icc (μ := volume)).mono_set hsub
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iR.const_mul 2) (iT.const_mul 2)]
  refine setIntegral_mono_on iS ((iR.const_mul 2).add (iT.const_mul 2))
    (arcM_measurable N A q a) fun α _ => ?_
  have hdec : S N α = Decomp1519.R N q a (α - c) +
      ((Decomp1519.muφ q : ℝ) : ℂ) * Decomp1519.T N (α - c) := by
    unfold Decomp1519.R
    rw [show c + (α - c) = α by ring]
    ring
  rw [hdec]
  refine (norm_add_sq_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

set_option maxHeartbeats 1000000 in
/-- The `T` part of a block is small, display 25, p. 364:
`Tpart ≤ 36 (1 + L)(N + 1)(Q/H + L^{-B/2})`, for `N ≥ 16`, `L^B ≤ H` and `1 ≤ M ≤ Q`. PROVED. -/
theorem Tpart_le {N : ℕ} {ε ξ A : ℝ} {M : ℕ} (hN : 16 ≤ N) (hA : 0 < A) (hℓ1 : 1 ≤ L N)
    (hw2 : ∀ q ∈ Decomp1519.Qs N A, Decomp1519.wq N A q ≤ 1 / 2)
    (hLH : L N ^ Bexp A ≤ H N ε) (hM1 : 1 ≤ M) (hMQ : (M : ℝ) ≤ Q N) :
    Tpart N ε ξ A M ≤ 36 * (1 + L N) * (N + 1) * (Q N / H N ε + 1 / L N ^ (Bexp A / 2)) := by
  have hB : 0 < Bexp A := by unfold Bexp; linarith
  have hℓ0 : 0 < L N := by linarith
  set ℓ := L N with hℓdef
  set r := ℓ ^ (Bexp A / 4) with hrdef
  have hr1 : 1 ≤ r := Real.one_le_rpow hℓ1 (by linarith)
  have hP : ℓ ^ (Bexp A / 2) = r ^ 2 := rpow_half_eq hℓ0 _
  have hV : ℓ ^ Bexp A = r ^ 4 := rpow_full_eq hℓ0 _
  rw [hP]
  rw [hV] at hLH
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hH0 : 0 < H N ε := Real.rpow_pos_of_pos hNpos _
  have hQ2 : 2 ≤ Q N := by
    unfold Q; rw [← Real.sqrt_eq_rpow]
    have : (4 : ℝ) ≤ √(N : ℝ) := by
      rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hNr
    linarith
  have hQN : Q N ≤ N := by
    unfold Q; rw [← Real.sqrt_eq_rpow]
    have := Real.sqrt_le_sqrt (show (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
    rw [Real.sqrt_sq hNpos.le] at this; linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set K : ℝ := 2 * (1 + ℓ) * (N + 1) with hK
  have hK0 : 0 < K := by positivity
  set b : ℝ := if (M : ℝ) ≤ r ^ 2 then 1 / r ^ 2 else 1 / M with hb
  -- each modulus
  have hterm : ∀ q ∈ Y N ε ξ M, (∑ a ∈ aWin N ε ξ (q : ℕ),
      ∫ α in arcM N A q a, Decomp1519.muφ q ^ 2 * ‖Decomp1519.T N (α - (a : ℝ) / q)‖ ^ 2) ≤
      K * b := by
    intro q hq
    obtain ⟨hqim, hMq, hqM, -⟩ := of_mem_filter hq
    obtain ⟨q0, -, hq0⟩ := Finset.mem_image.mp hqim
    have hqI := (Finset.mem_Icc.mp q0.property)
    have hqval : (q : ℕ) = q0.val := by rw [← hq0]; rfl
    have hq1 : 1 ≤ (q : ℕ) := q.pos
    have hqQf : (q : ℕ) ≤ ⌊Q N⌋₊ := by rw [hqval]; exact hqI.2
    have hqr : (1 : ℝ) ≤ (q : ℕ) := by exact_mod_cast hq1
    have hqQ : ((q : ℕ) : ℝ) ≤ Q N := (Nat.cast_le.mpr hqQf).trans (Nat.floor_le (by linarith))
    have hr2 : 1 / (((q : ℕ) : ℝ) * Q N) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    -- the totient
    have hφ : ((q : ℕ) : ℝ) / (2 * (1 + ℓ)) ≤ (Nat.totient (q : ℕ) : ℝ) := by
      have h1 := totient_ge_log_two_mul_div hq1
      have hlq : Real.log ((q : ℕ) : ℝ) ≤ ℓ := by
        simp only [hℓdef, L]
        exact Real.log_le_log (by linarith) (hqQ.trans hQN)
      have hlq0 : 0 ≤ Real.log ((q : ℕ) : ℝ) := Real.log_nonneg hqr
      refine le_trans ?_ h1
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : 1 + Real.log ((q : ℕ) : ℝ) ≤ 2 * Real.log 2 * (1 + ℓ) := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ ((q : ℕ) : ℝ))
      linarith
    have hφ0 : (0 : ℝ) < Nat.totient (q : ℕ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    -- the arc bound `X`
    set X : ℝ := if ((q : ℕ) : ℝ) ≤ r ^ 2 then ((q : ℕ) : ℝ) * N / (2 * r ^ 4) else N + 1 with hX
    have harc : ∀ a ∈ aWin N ε ξ (q : ℕ),
        (∫ α in arcM N A q a, ‖Decomp1519.T N (α - (a : ℝ) / q)‖ ^ 2) ≤ X := by
      intro a ha
      have haA : a ∈ Decomp1519.As (q : ℕ) := (of_mem_filter ha).1
      obtain ⟨hfull, htail⟩ := arc_T_bound (N := N) (A := A) hq1 haA hr2
      simp only [hX]
      split_ifs with hcase
      · have hqL : ((q : ℕ) : ℝ) ≤ ℓ ^ (Bexp A / 2) := by rw [hP]; exact hcase
        have hqQs : (q : ℕ) ∈ Decomp1519.Qs N A := by
          refine Finset.mem_Icc.mpr ⟨hq1, Nat.le_floor ?_⟩
          exact hqL
        have hw0 := Decomp1519.wq_pos (A := A) (by omega : 2 ≤ N) hq1
        have h := htail hqL hw0 (hw2 _ hqQs)
        have hw : Decomp1519.wq N A (q : ℕ) = r ^ 4 / (((q : ℕ) : ℝ) * N) := by
          unfold Decomp1519.wq; rw [← hℓdef, hV]
        rw [hw] at h
        refine h.trans (le_of_eq ?_)
        field_simp
      · exact hfull
    have hX0 : 0 ≤ X := by simp only [hX]; split_ifs <;> positivity
    have hsum : (∑ a ∈ aWin N ε ξ (q : ℕ),
        ∫ α in arcM N A q a, Decomp1519.muφ q ^ 2 * ‖Decomp1519.T N (α - (a : ℝ) / q)‖ ^ 2) ≤
        X / Nat.totient (q : ℕ) := by
      have hm := Decomp1519.muφ_sq_le (q := (q : ℕ))
      have hcard : ((aWin N ε ξ (q : ℕ)).card : ℝ) ≤ Nat.totient (q : ℕ) := by
        exact_mod_cast (card_filter_le_of _).trans (card_As_le_totient hq1)
      calc _ = ∑ a ∈ aWin N ε ξ (q : ℕ), Decomp1519.muφ q ^ 2 *
            ∫ α in arcM N A q a, ‖Decomp1519.T N (α - (a : ℝ) / q)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [integral_const_mul]
        _ ≤ ∑ a ∈ aWin N ε ξ (q : ℕ), Decomp1519.muφ q ^ 2 * X :=
            Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (harc a ha) (sq_nonneg _)
        _ = ((aWin N ε ξ (q : ℕ)).card : ℝ) * (Decomp1519.muφ q ^ 2 * X) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Nat.totient (q : ℕ) : ℝ) * (1 / (Nat.totient (q : ℕ) : ℝ) ^ 2 * X) :=
            mul_le_mul hcard (mul_le_mul_of_nonneg_right hm hX0) (by positivity) (by positivity)
        _ = X / Nat.totient (q : ℕ) := by field_simp
    refine hsum.trans ?_
    have hinv : 1 / (Nat.totient (q : ℕ) : ℝ) ≤ 2 * (1 + ℓ) / ((q : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ hφ0 (by linarith)]
      rw [div_le_iff₀ (by positivity)] at hφ
      linarith
    have hXφ : X / Nat.totient (q : ℕ) ≤ X * (2 * (1 + ℓ) / ((q : ℕ) : ℝ)) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv hX0
    refine hXφ.trans ?_
    have hMr : (M : ℝ) ≤ (q : ℕ) := by exact_mod_cast hMq
    simp only [hX, hb]
    split_ifs with hc1 hc2 hc2
    · -- q ≤ r², M ≤ r²
      have : ((q : ℕ) : ℝ) * N / (2 * r ^ 4) * (2 * (1 + ℓ) / ((q : ℕ) : ℝ)) =
          (1 + ℓ) * N / r ^ 4 := by field_simp
      rw [this]
      rw [div_le_iff₀ (by positivity)]
      have he : K * (1 / r ^ 2) * r ^ 4 = K * r ^ 2 := by field_simp
      rw [he, hK]
      have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
      have hX0 : 0 ≤ (1 + ℓ) * (N + 1 : ℝ) := by positivity
      have h5 := mul_le_mul_of_nonneg_left hr2 hX0
      nlinarith
    · -- q ≤ r² < M: impossible
      exact absurd (hMr.trans hc1) hc2
    · -- q > r², M ≤ r²
      push_neg at hc1
      have h1 : (N + 1 : ℝ) * (2 * (1 + ℓ) / ((q : ℕ) : ℝ)) = K / ((q : ℕ) : ℝ) := by
        rw [hK]; ring
      rw [h1, mul_one_div]
      exact div_le_div_of_nonneg_left hK0.le (by positivity) hc1.le
    · -- q > r², M > r²
      have h1 : (N + 1 : ℝ) * (2 * (1 + ℓ) / ((q : ℕ) : ℝ)) = K / ((q : ℕ) : ℝ) := by
        rw [hK]; ring
      rw [h1, mul_one_div]
      exact div_le_div_of_nonneg_left hK0.le (by positivity) hMr
  -- sum over the moduli
  unfold Tpart
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hY := Y_card_le N (by omega) ε ξ M hM1 hMQ
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  simp only [hb]
  split_ifs with hc
  · -- `M ≤ r²`: `M² ≤ r⁴ ≤ H`, so `|Y| ≤ 18`
    have hM2 : (M : ℝ) ^ 2 / H N ε ≤ 1 := by
      rw [div_le_one hH0]
      have : (M : ℝ) ^ 2 ≤ (r ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) hc 2
      nlinarith
    have hY18 : ((Y N ε ξ M).card : ℝ) ≤ 18 := by linarith
    have hQH : 0 ≤ Q N / H N ε := by positivity
    calc ((Y N ε ξ M).card : ℝ) * (K * (1 / r ^ 2)) ≤ 18 * (K * (1 / r ^ 2)) :=
          mul_le_mul_of_nonneg_right hY18 (by positivity)
      _ = 36 * (1 + ℓ) * (N + 1) * (1 / r ^ 2) := by rw [hK]; ring
      _ ≤ 36 * (1 + ℓ) * (N + 1) * (Q N / H N ε + 1 / r ^ 2) := by
          have h36 := mul_nonneg (by positivity : (0 : ℝ) ≤ 36 * (1 + ℓ) * (N + 1)) hQH
          rw [mul_add]; linarith
  · -- `M > r²`
    push_neg at hc
    have hYM : ((Y N ε ξ M).card : ℝ) * (1 / M) ≤ 9 * (Q N / H N ε + 1 / r ^ 2) := by
      have h1 : ((Y N ε ξ M).card : ℝ) * (1 / M) ≤ 9 * ((M : ℝ) ^ 2 / H N ε + 1) * (1 / M) :=
        mul_le_mul_of_nonneg_right hY (by positivity)
      have h2 : 9 * ((M : ℝ) ^ 2 / H N ε + 1) * (1 / M) = 9 * ((M : ℝ) / H N ε + 1 / M) := by
        field_simp
      have h3 : (M : ℝ) / H N ε ≤ Q N / H N ε := div_le_div_of_nonneg_right hMQ hH0.le
      have h4 : 1 / (M : ℝ) ≤ 1 / r ^ 2 := one_div_le_one_div_of_le (by positivity) hc.le
      linarith
    calc ((Y N ε ξ M).card : ℝ) * (K * (1 / M)) = K * (((Y N ε ξ M).card : ℝ) * (1 / M)) := by
          ring
      _ ≤ K * (9 * (Q N / H N ε + 1 / r ^ 2)) := mul_le_mul_of_nonneg_left hYM hK0.le
      _ ≤ 36 * (1 + ℓ) * (N + 1) * (Q N / H N ε + 1 / r ^ 2) := by
          rw [hK]
          have : 0 ≤ (1 + ℓ) * (N + 1) * (Q N / H N ε + 1 / r ^ 2) := by positivity
          nlinarith

/-! ### The leaf for one dyadic block, the `R` part -/

/-- LEAF, displays 13 and 23 to 27, pp. 361 and 364, for one dyadic block `M ≤ Q`, with the
numerators `a'` of display 25 whose arc meets the window: display 13 writes
`R(η, q, a) = φ(q)^{-1} Σ_χ χ(a) τ(χ̄) Ψ'(N, χ, η) + O(N^{1/2})`; the `O(N^{1/2})` term gives
display 26; Gallagher's lemma, P. X. Gallagher, Invent. Math. 11, 1970, pp. 329 to 339,
Lemma 1, turns the integral over `|η| < 1/(qQ)` of `Ψ'` into the mean square of `W`, here `WA`
of `Decomp1624` with window `qQ/2`; Cauchy and Schwarz give the character expression of
display 27, here `energyA`, with a loss `L^c`. Not proved here. -/
theorem rpart_block_bound :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, ∀ M : ℕ, 1 ≤ M →
        (M : ℝ) ≤ Q N →
        Rpart N ε ξ A M ≤ C * N * (L N ^ c * energyA N ε ξ M + L N ^ (-(A + 2))) := by
  sorry

lemma logpow_le_eps (P ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, L N ^ P ≤ (N : ℝ) ^ ε := by
  have h := (isLittleO_log_rpow_rpow_atTop P hε).def (by norm_num : (0 : ℝ) < 1)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with N hN hN1
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hl : 0 ≤ Real.log N := Real.log_nonneg hx
  simp only [Real.norm_eq_abs] at hN
  rw [abs_of_nonneg (Real.rpow_nonneg hl _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hN
  exact hN

/-- **One dyadic block, displays 23 to 27, p. 364**: the block is at most
`C N (L^c energyA + L^{-A-2})`, from `block_le_R_T`, the `R` part leaf `rpart_block_bound` and
the `T` part bound `Tpart_le`. CONDITIONAL ON `rpart_block_bound`; no sorry in this proof. -/
theorem minor_block_bound :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, ∀ M : ℕ, 1 ≤ M →
        (M : ℝ) ≤ Q N →
        blockInt N ε ξ A M ≤ C * N * (L N ^ c * energyA N ε ξ M + L N ^ (-(A + 2))) := by
  obtain ⟨ε₁, hε₁, hR⟩ := rpart_block_bound
  refine ⟨ε₁, hε₁, fun ε hε hεε A hA => ?_⟩
  obtain ⟨C, c, N₀, hC, hc, hRb⟩ := hR ε hε hεε A hA
  have hB : 0 < Bexp A := by unfold Bexp; linarith
  have hLtop : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in atTop,
      (2 ≤ N ∧ 2 * L N ^ (3 * Bexp A / 2) < N ∧ (∀ q ∈ Decomp1519.Qs N A,
        Decomp1519.wq N A q ≤ 1 / 2) ∧ 1 ≤ L N ^ (Bexp A / 2)) ∧ 16 ≤ N ∧ 1 ≤ L N ∧
      L N ^ Bexp A ≤ √(N : ℝ) / 4 ∧ L N ^ (A + 3) ≤ (N : ℝ) ^ ε ∧ N₀ ≤ N := by
    filter_upwards [Decomp1519.estimate6_hyps_vacuity hA, eventually_ge_atTop 16,
      hLtop.eventually_ge_atTop 1, Decomp1519.logpow_le_sqrt_div4 (Bexp A),
      logpow_le_eps (A + 3) ε hε, tendsto_natCast_atTop_atTop.eventually_ge_atTop N₀]
      with N h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  refine ⟨2 * C + 576, c, N1, by positivity, hc, fun N hN ξ M hM1 hMQ => ?_⟩
  have hNN1 : N1 ≤ N := by exact_mod_cast hN
  obtain ⟨⟨-, -, hw2, -⟩, hN16, hℓ1, hLB, hLε, hN0⟩ := hN1 N hNN1
  have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN16
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ := L N with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  have hsqrt : √(N : ℝ) ≤ H N ε := by
    unfold H; rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hLH : ℓ ^ Bexp A ≤ H N ε := by
    have : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
    linarith
  have hT := Tpart_le (ε := ε) (ξ := ξ) hN16 hA hℓ1 hw2 hLH hM1 hMQ
  have hRp := hRb N hN0 ξ M hM1 hMQ
  have hblk := block_le_R_T N ε ξ A M
  -- the `T` part in powers of `ℓ`
  have hu : 0 < ℓ ^ (A + 3) := Real.rpow_pos_of_pos hℓ0 _
  have hQH : Q N / H N ε ≤ 1 / ℓ ^ (A + 3) := by
    have he : Q N / H N ε = 1 / (2 * (N : ℝ) ^ ε) := by
      unfold Q H
      rw [Real.rpow_add hNpos]
      have : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
      have : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
      field_simp
    rw [he]
    have hNε : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
    exact one_div_le_one_div_of_le hu (by linarith)
  have hLBu : 1 / ℓ ^ (Bexp A / 2) ≤ 1 / ℓ ^ (A + 3) :=
    one_div_le_one_div_of_le hu
      (Real.rpow_le_rpow_of_exponent_le hℓ1 (by unfold Bexp; linarith))
  have hTu : Tpart N ε ξ A M ≤ 288 * ℓ * N * (1 / ℓ ^ (A + 3)) := by
    refine hT.trans ?_
    have h1 : Q N / H N ε + 1 / ℓ ^ (Bexp A / 2) ≤ 2 * (1 / ℓ ^ (A + 3)) := by linarith
    have h2 : (1 + ℓ) * ((N : ℝ) + 1) ≤ 4 * ℓ * N := by nlinarith
    have h3 : 0 ≤ Q N / H N ε + 1 / ℓ ^ (Bexp A / 2) := by
      have : 0 < Q N := by unfold Q; positivity
      have : 0 < H N ε := Real.rpow_pos_of_pos hNpos _
      positivity
    calc 36 * (1 + ℓ) * (N + 1) * (Q N / H N ε + 1 / ℓ ^ (Bexp A / 2))
        = 36 * ((1 + ℓ) * (N + 1)) * (Q N / H N ε + 1 / ℓ ^ (Bexp A / 2)) := by ring
      _ ≤ 36 * (4 * ℓ * N) * (2 * (1 / ℓ ^ (A + 3))) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h1 h3 (by positivity)
      _ = 288 * ℓ * N * (1 / ℓ ^ (A + 3)) := by ring
  have hpow : ℓ * (1 / ℓ ^ (A + 3)) = ℓ ^ (-(A + 2)) := by
    rw [show A + 3 = (A + 2) + 1 by ring, Real.rpow_add_one hℓ0.ne', Real.rpow_neg hℓ0.le]
    field_simp
  have hTu' : Tpart N ε ξ A M ≤ 288 * N * ℓ ^ (-(A + 2)) := by
    rw [← hpow]; linarith
  have hE0 : 0 ≤ ℓ ^ c * energyA N ε ξ M :=
    mul_nonneg (Real.rpow_nonneg hℓ0.le _) (energyA_nonneg N ε ξ M)
  have hL0 : 0 ≤ ℓ ^ (-(A + 2)) := Real.rpow_nonneg hℓ0.le _
  calc blockInt N ε ξ A M ≤ 2 * Rpart N ε ξ A M + 2 * Tpart N ε ξ A M := hblk
    _ ≤ 2 * (C * N * (ℓ ^ c * energyA N ε ξ M + ℓ ^ (-(A + 2)))) +
        2 * (288 * N * ℓ ^ (-(A + 2))) := by linarith
    _ ≤ (2 * C + 576) * N * (ℓ ^ c * energyA N ε ξ M + ℓ ^ (-(A + 2))) := by
        have : 0 ≤ (N : ℝ) * (ℓ ^ c * energyA N ε ξ M) := mul_nonneg hNpos.le hE0
        nlinarith

/-! ### The Farey dissection, display 22, PROVED -/

open Classical in
attribute [-instance] Finset.decidableExistsAndFinsetCoe Finset.decidableExistsAndFinset in
/-- Membership in the family `Y(M)` of p. 363 from a witness. PROVED. -/
theorem mem_Y_of {N : ℕ} {ε ξ : ℝ} {M q a : ℕ} (hq1 : 1 ≤ q) (hqQ : q ≤ ⌊Q N⌋₊)
    (hM1 : M ≤ q) (hM2 : q ≤ 2 * M) (ha : a ∈ Finset.Icc 1 q) (hcop : Nat.Coprime a q)
    {α : ℝ} (h1 : |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Q N)) (h2 : |α - ξ| < 1 / H N ε) :
    (⟨q, hq1⟩ : ℕ+) ∈ Y N ε ξ M := by
  refine mem_filter_of ?_ ⟨hM1, hM2, a, ha, hcop, α, h1, h2⟩
  exact Finset.mem_image.mpr ⟨⟨q, Finset.mem_Icc.mpr ⟨hq1, hqQ⟩⟩, Finset.mem_attach _ _, rfl⟩

lemma Q_ge_one {N : ℕ} (hN : 4 ≤ N) : 1 ≤ Q N := by
  unfold Q
  rw [← Real.sqrt_eq_rpow]
  have : (2 : ℝ) ≤ √(N : ℝ) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  linarith

/-- The dyadic index of a modulus `1 ≤ q ≤ ⌊Q⌋`: `2^j ≤ q ≤ 2 · 2^j` with `j ≤ J`. PROVED. -/
lemma dyadic_index {N q : ℕ} (hq1 : 1 ≤ q) (hqQ : q ≤ ⌊Q N⌋₊) :
    Nat.log 2 q ∈ Finset.range (Jn N + 1) ∧ 2 ^ Nat.log 2 q ≤ q ∧ q ≤ 2 * 2 ^ Nat.log 2 q := by
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hqQ)),
    Nat.pow_log_le_self 2 (by omega), ?_⟩
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
  rw [pow_succ] at this
  omega

/-- **Display 22, p. 363**, the Farey dissection: every `α` in `(ξ - 1/H, ξ + 1/H) ∩ 𝔪` lies on
an arc `|α - a/q| < 1/(qQ)` with `q ∈ Y(2^j)`, `j ≤ J`, `a ∈ As q`. By Dirichlet's theorem
with denominators up to `⌊Q⌋`, and the arc of `1/1` for `α > 1`. PROVED. -/
theorem farey_cover {N : ℕ} (hN : 4 ≤ N) {ε ξ A α : ℝ}
    (hα : α ∈ Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A) :
    ∃ j ∈ Finset.range (Jn N + 1), ∃ q ∈ Y N ε ξ (2 ^ j),
      ∃ a ∈ aWin N ε ξ (q : ℕ), α ∈ arcM N A q a := by
  have hQ1 := Q_ge_one hN
  have hQ0 : 0 < Q N := by linarith
  set Qf := ⌊Q N⌋₊ with hQf
  have hQf1 : 1 ≤ Qf := Nat.le_floor (by exact_mod_cast hQ1)
  have hQflt : Q N < Qf + 1 := Nat.lt_floor_add_one _
  obtain ⟨hαw, hαm⟩ := hα
  have hξ : |α - ξ| < 1 / H N ε := abs_lt.mpr ⟨by linarith [hαw.1], by linarith [hαw.2]⟩
  have hαI : 1 / Q N < α ∧ α < 1 + 1 / Q N := hαm.1
  -- the general step from a reduced witness
  have key : ∀ q a : ℕ, (hq1 : 1 ≤ q) → q ≤ Qf → a ∈ Finset.Icc 1 q → Nat.Coprime a q →
      |α - (a : ℝ) / q| < 1 / ((q : ℝ) * Q N) →
      ∃ j ∈ Finset.range (Jn N + 1), ∃ q' ∈ Y N ε ξ (2 ^ j),
        ∃ a' ∈ aWin N ε ξ (q' : ℕ), α ∈ arcM N A q' a' := by
    intro q a hq1 hqQ ha hcop hlt
    obtain ⟨hj, hj1, hj2⟩ := dyadic_index hq1 hqQ
    refine ⟨Nat.log 2 q, hj, ⟨q, hq1⟩, mem_Y_of hq1 hqQ hj1 hj2 ha hcop hlt.le hξ, a,
      mem_filter_of (Finset.mem_filter.mpr ⟨ha, hcop⟩) ⟨α, hlt, hξ⟩, ⟨?_, hαm⟩⟩
    have := abs_lt.mp hlt
    exact ⟨by simp only [PNat.mk_coe]; linarith, by simp only [PNat.mk_coe]; linarith⟩
  by_cases h1 : 1 < α
  · refine key 1 1 le_rfl hQf1 (by simp) (Nat.coprime_one_left 1) ?_
    have hp := one_div_pos.mpr hQ0
    rw [abs_lt]
    simp only [Nat.cast_one, div_one, one_mul]
    constructor <;> linarith [hαI.2]
  · push_neg at h1
    obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α (n := Qf) (by omega)
    have hQfr : (0 : ℝ) < (Qf : ℝ) + 1 := by positivity
    have hlt : |(k : ℝ) * α - j| < 1 / Q N :=
      lt_of_le_of_lt hjk (one_div_lt_one_div_of_lt hQ0 hQflt)
    have hk0r : (0 : ℝ) < k := by exact_mod_cast hk0
    have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    obtain ⟨hl1, hl2⟩ := abs_lt.mp hlt
    -- `1 ≤ j ≤ k`
    have hj1 : 1 ≤ j := by
      by_contra hj
      have : (j : ℝ) ≤ 0 := by exact_mod_cast (by omega : j ≤ 0)
      have h3 : (k : ℝ) * (1 / Q N) < k * α := mul_lt_mul_of_pos_left hαI.1 hk0r
      have h4 : 1 / Q N ≤ (k : ℝ) * (1 / Q N) := by
        have := one_div_pos.mpr hQ0; nlinarith
      linarith
    have hjk' : j ≤ k := by
      by_contra hj
      have : (k : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : k + 1 ≤ j)
      have h3 : (k : ℝ) * α ≤ k := by nlinarith
      have h4 : 1 / Q N ≤ 1 := by rw [div_le_one hQ0]; exact hQ1
      linarith
    obtain ⟨jn, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ j)
    obtain ⟨kn, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k)
    have hjn1 : 1 ≤ jn := by omega
    have hkn1 : 1 ≤ kn := by omega
    have hjkn : jn ≤ kn := by omega
    have hknQ : kn ≤ Qf := by exact_mod_cast hkn
    set g := Nat.gcd jn kn with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgj : g ∣ jn := Nat.gcd_dvd_left _ _
    have hgk : g ∣ kn := Nat.gcd_dvd_right _ _
    set a := jn / g
    set q := kn / g
    have hq1 : 1 ≤ q := Nat.div_pos (Nat.le_of_dvd (by omega) hgk) hg0
    have ha1 : 1 ≤ a := Nat.div_pos (Nat.le_of_dvd (by omega) hgj) hg0
    have haq : a ≤ q := Nat.div_le_div_right hjkn
    have hqk : q ≤ kn := Nat.div_le_self _ _
    have hcop : Nat.Coprime a q := Nat.coprime_div_gcd_div_gcd hg0
    have hfrac : (a : ℝ) / q = (jn : ℝ) / kn := by
      have hgr : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
      simp only [a, q]
      rw [Nat.cast_div hgj hgr, Nat.cast_div hgk hgr]
      field_simp
    refine key q a hq1 (hqk.trans hknQ) (Finset.mem_Icc.mpr ⟨ha1, haq⟩) hcop ?_
    rw [hfrac]
    have hkr : (0 : ℝ) < kn := by exact_mod_cast hkn1
    have hqr : (q : ℝ) ≤ kn := by exact_mod_cast hqk
    have hq0r : (0 : ℝ) < q := by exact_mod_cast hq1
    have e1 : α - (jn : ℝ) / kn = ((kn : ℝ) * α - jn) / kn := by field_simp
    rw [e1, abs_div, abs_of_pos hkr, div_lt_iff₀ hkr]
    have hlt' : |(kn : ℝ) * α - jn| < 1 / Q N := by exact_mod_cast hlt
    have h5 : 1 / Q N ≤ 1 / ((q : ℝ) * Q N) * kn := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hQ0]
      nlinarith
    linarith

/-! ### The union bound, PROVED -/

lemma setIntegral_union_le_add {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hfA : IntegrableOn f A)
    (hfB : IntegrableOn f B) :
    ∫ x in A ∪ B, f x ≤ (∫ x in A, f x) + ∫ x in B, f x := by
  rw [← union_diff_self, setIntegral_union disjoint_sdiff_right (hB.diff hA) hfA
    (hfB.mono_set diff_subset)]
  have := setIntegral_mono_set hfB (Eventually.of_forall fun x => hf0 x)
    (Eventually.of_forall (diff_subset (s := B) (t := A)))
  linarith

lemma setIntegral_biUnion_le {ι : Type*} (s : Finset ι) (t : ι → Set ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (ht : ∀ i, MeasurableSet (t i)) (hfi : ∀ i, IntegrableOn f (t i)) :
    ∫ x in ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∫ x in t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    refine (setIntegral_union_le_add hf0 (ht i) (Finset.measurableSet_biUnion s fun j _ => ht j)
      (hfi i) (integrableOn_finset_iUnion.mpr fun j _ => hfi j)).trans ?_
    linarith

lemma integrableOn_arcM (N : ℕ) (A : ℝ) (q a : ℕ) :
    IntegrableOn (fun α => ‖S N α‖ ^ 2) (arcM N A q a) := by
  have hc : Continuous fun α => ‖S N α‖ ^ 2 := (continuous_S N).norm.pow 2
  exact (hc.integrableOn_Icc (a := (a : ℝ) / q - 1 / ((q : ℝ) * Q N))
    (b := (a : ℝ) / q + 1 / ((q : ℝ) * Q N))).mono_set
    (inter_subset_left.trans Ioo_subset_Icc_self)

/-- p. 363 to 364: the window integral of 7 is at most the sum of the dyadic block integrals,
by `farey_cover` and the union bound. PROVED. -/
theorem window_le_blocks {N : ℕ} (hN : 4 ≤ N) (ε ξ A : ℝ) :
    (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A, ‖S N α‖ ^ 2) ≤
      ∑ j ∈ Finset.range (Jn N + 1), blockInt N ε ξ A (2 ^ j) := by
  set f : ℝ → ℝ := fun α => ‖S N α‖ ^ 2 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  set U := ⋃ j ∈ Finset.range (Jn N + 1), ⋃ q ∈ Y N ε ξ (2 ^ j),
    ⋃ a ∈ aWin N ε ξ (q : ℕ), arcM N A q a with hU
  have hsub : Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A ⊆ U := by
    intro α hα
    obtain ⟨j, hj, q, hq, a, ha, hmem⟩ := farey_cover hN hα
    simp only [hU, mem_iUnion]
    exact ⟨j, hj, q, hq, a, ha, hmem⟩
  have hin : ∀ (j : ℕ), MeasurableSet (⋃ q ∈ Y N ε ξ (2 ^ j), ⋃ a ∈ aWin N ε ξ (q : ℕ),
      arcM N A q a) := fun j =>
    Finset.measurableSet_biUnion _ fun q _ =>
      Finset.measurableSet_biUnion _ fun a _ => arcM_measurable N A q a
  have hii : ∀ (j : ℕ), IntegrableOn f (⋃ q ∈ Y N ε ξ (2 ^ j), ⋃ a ∈ aWin N ε ξ (q : ℕ),
      arcM N A q a) := fun j =>
    integrableOn_finset_iUnion.mpr fun q _ =>
      integrableOn_finset_iUnion.mpr fun a _ => integrableOn_arcM N A q a
  have hUi : IntegrableOn f U := integrableOn_finset_iUnion.mpr fun j _ => hii j
  calc (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A, f α)
      ≤ ∫ α in U, f α :=
        setIntegral_mono_set hUi (Eventually.of_forall fun x => hf0 x)
          (Eventually.of_forall hsub)
    _ ≤ ∑ j ∈ Finset.range (Jn N + 1), ∫ α in ⋃ q ∈ Y N ε ξ (2 ^ j),
          ⋃ a ∈ aWin N ε ξ (q : ℕ), arcM N A q a, f α :=
        setIntegral_biUnion_le _ _ hf0 hin hii
    _ ≤ ∑ j ∈ Finset.range (Jn N + 1), blockInt N ε ξ A (2 ^ j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        unfold blockInt
        refine (setIntegral_biUnion_le (Y N ε ξ (2 ^ j))
          (fun q : ℕ+ => ⋃ a ∈ aWin N ε ξ (q : ℕ), arcM N A q a) hf0
          (fun q => Finset.measurableSet_biUnion _ fun a _ => arcM_measurable N A q a)
          (fun q => integrableOn_finset_iUnion.mpr fun a _ => integrableOn_arcM N A q a)).trans ?_
        refine Finset.sum_le_sum fun q _ => ?_
        exact setIntegral_biUnion_le _ _ hf0 (fun a => arcM_measurable N A q a)
          (fun a => integrableOn_arcM N A q a)

/-! ### The dyadic count and the glue, PROVED -/

/-- `J + 1 ≤ L` for `N ≥ 64`: `2^J ≤ Q ≤ √N`, so `J log 2 ≤ L/2`. PROVED. -/
theorem Jn_succ_le {N : ℕ} (hN : 64 ≤ N) : ((Jn N : ℝ) + 1) ≤ L N := by
  have hN4 : 4 ≤ N := by omega
  have hQ1 := Q_ge_one hN4
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hQf1 : 1 ≤ ⌊Q N⌋₊ := Nat.le_floor (by exact_mod_cast hQ1)
  have h2J : ((2 : ℝ) ^ Jn N) ≤ √(N : ℝ) := by
    have h1 : 2 ^ Jn N ≤ ⌊Q N⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 ^ Jn N : ℕ) : ℝ) ≤ Q N :=
      (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith))
    have h3 : Q N ≤ √(N : ℝ) := by
      unfold Q; rw [← Real.sqrt_eq_rpow]; linarith [Real.sqrt_nonneg (N : ℝ)]
    push_cast at h2; linarith
  have hlog : (Jn N : ℝ) * Real.log 2 ≤ L N / 2 := by
    have := Real.log_le_log (by positivity) h2J
    rw [Real.log_pow, Real.log_sqrt hNpos.le] at this
    unfold L; linarith
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hL64 : 4 ≤ L N := by
    unfold L
    have h64 : Real.log 64 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
    linarith
  have hJ0 : (0 : ℝ) ≤ Jn N := Nat.cast_nonneg _
  nlinarith

/-- **The leaf `Burst4Split.reduction27A_wide`**, same type, from `window_le_blocks` and the
block bound `minor_block_bound`, summing `J + 1 ≤ L` dyadic blocks. CONDITIONAL ON
`rpart_block_bound`; no sorry in this proof. -/
theorem reduction27A_wide_of_split :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, ∀ E : ℝ, 0 ≤ E →
        (∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N → energyA N ε ξ M ≤ E) →
        (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
          ‖S N α‖ ^ 2) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 1))) := by
  obtain ⟨ε₁, hε₁, hb⟩ := minor_block_bound
  refine ⟨ε₁, hε₁, fun ε hε hεε A hA => ?_⟩
  obtain ⟨C, c, N₀, hC, hc, hB⟩ := hb ε hε hεε A hA
  refine ⟨C, c + 1, max N₀ 64, hC, by linarith, fun N hN ξ E hE0 hE => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN64 : 64 ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hL := L_pos hN2
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hJ := Jn_succ_le hN64
  have hblock : ∀ j ∈ Finset.range (Jn N + 1),
      blockInt N ε ξ A (2 ^ j) ≤ C * N * (L N ^ c * E + L N ^ (-(A + 2))) := by
    intro j hj
    have hjJ : j ≤ Jn N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hM1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hMQ : ((2 ^ j : ℕ) : ℝ) ≤ Q N := by
      have hQ1 := Q_ge_one (by omega : 4 ≤ N)
      have h1 : 2 ^ j ≤ ⌊Q N⌋₊ :=
        (Nat.pow_le_pow_right (by norm_num) hjJ).trans (Nat.pow_log_le_self 2
          (by have : 1 ≤ ⌊Q N⌋₊ := Nat.le_floor (by exact_mod_cast hQ1); omega))
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith))
    refine (hB N hN0 ξ (2 ^ j) hM1 hMQ).trans ?_
    have h1 : L N ^ c * energyA N ε ξ (2 ^ j) ≤ L N ^ c * E :=
      mul_le_mul_of_nonneg_left (hE _ hM1 hMQ) (Real.rpow_nonneg hL.le _)
    have h2 : 0 ≤ C * N := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h2
  refine (window_le_blocks (by omega) ε ξ A).trans ?_
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  have hX : 0 ≤ C * N * (L N ^ c * E + L N ^ (-(A + 2))) := by positivity
  have h1 : ((Jn N : ℝ) + 1) * (C * N * (L N ^ c * E + L N ^ (-(A + 2)))) ≤
      L N * (C * N * (L N ^ c * E + L N ^ (-(A + 2)))) := mul_le_mul_of_nonneg_right hJ hX
  refine h1.trans (le_of_eq ?_)
  have e1 : L N ^ (c + 1) = L N ^ c * L N := Real.rpow_add_one hL.ne' c
  have e2 : L N ^ (-(A + 1)) = L N ^ (-(A + 2)) * L N := by
    rw [← Real.rpow_add_one hL.ne']; congr 1; ring
  rw [e1, e2]; ring

/-- 7 for every real centre, `Estimate7Wide`, from `reduction27A_wide_of_split` and
`Decomp1624.energy_decayA`; the proof of `Burst4Split.estimate7Wide_of_split` with the split
reduction. CONDITIONAL ON `rpart_block_bound` and `energy_decayA`. -/
theorem estimate7Wide_of_p2 : Estimate7Wide := by
  obtain ⟨ε₁, hε₁, hred⟩ := reduction27A_wide_of_split
  refine ⟨min ε₁ (1 / 12), lt_min hε₁ (by norm_num), ?_⟩
  intro ε hε hεsmall A hA
  have hεred : ε < ε₁ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have hεden : ε < 1 / 12 := lt_of_lt_of_le hεsmall (min_le_right _ _)
  obtain ⟨C, c, N₀, hC, hc, hbound⟩ := hred ε hε hεred A hA
  obtain ⟨K, N₁, hK, hdecay⟩ := energy_decayA ε hε hεden (A + 1 + c) (by linarith)
  refine ⟨C * (K + 1), max (max N₀ N₁) 2, ?_⟩
  intro N hN ξ
  have hN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₂ : 2 ≤ N := by exact_mod_cast (le_trans (le_max_right _ _) hN : (2 : ℝ) ≤ N)
  have hL := L_pos hN₂
  have hξ0 : 0 ≤ clamp01 ξ := le_max_left _ _
  have hξ1 : clamp01 ξ ≤ 1 := max_le zero_le_one (min_le_right _ _)
  have hE : ∀ M : ℕ, 1 ≤ M → (M : ℝ) ≤ Q N →
      energyA N ε ξ M ≤ K * L N ^ (-(A + 1 + c)) := fun M hM1 hM2 =>
    (energyA_le_clamp (by omega) ε ξ M).trans (hdecay N hN₁ (clamp01 ξ) hξ0 hξ1 M hM1 hM2)
  have he := hbound N hN₀ ξ (K * L N ^ (-(A + 1 + c))) (by positivity) hE
  have hprod : L N ^ c * (K * L N ^ (-(A + 1 + c))) = K * L N ^ (-(A + 1)) := by
    calc
      _ = K * (L N ^ c * L N ^ (-(A + 1 + c))) := by ring
      _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring
  change (∫ α in Ioo (ξ - 1 / H N ε) (ξ + 1 / H N ε) ∩ minorArcs N A,
    ‖S N α‖ ^ 2) ≤ _
  calc
    _ ≤ C * N * (L N ^ c * (K * L N ^ (-(A + 1 + c))) + L N ^ (-(A + 1))) := he
    _ = (C * (K + 1)) * N / L N ^ (A + 1) := by
      rw [hprod, Real.rpow_neg hL.le]
      ring

/-! ### The new top level -/

/-- **Perelli and Pintz 1992, the Theorem, p. 356**, same type as `perelliPintz`, from the
burst 8 split: Section 2 by `mainTheorem_of_wide`, Section 4 by `estimate6Wide_of_split`,
Sections 5 and 6 by `estimate7Wide_of_p2`. CONDITIONAL ON the four leaves
`siegel_walfisz_uniform`, `shiu_d2`, `rpart_block_bound`, `Decomp1624.energy_decayA`.
No sorry in this proof. -/
theorem perelliPintz_p2 : MainTheorem :=
  mainTheorem_of_wide estimate6Wide_of_split estimate7Wide_of_p2

example : MainTheorem := perelliPintz
#check (perelliPintz_p2 : MainTheorem)

#print axioms hAP_of_SW
#print axioms rho_alg
#print axioms R_small
#print axioms term_alg
#print axioms E19_le
#print axioms E19_nonneg
#print axioms shiu_block
#print axioms T_orth_high
#print axioms arc_integral_bound_high
#print axioms eq19_high
#print axioms S2k_le_divisors
#print axioms final_alg
#print axioms mem_Y_of
#print axioms dyadic_index
#print axioms farey_cover
#print axioms setIntegral_union_le_add
#print axioms setIntegral_biUnion_le
#print axioms window_le_blocks
#print axioms Jn_succ_le
#print axioms card_As_le_totient
#print axioms parseval_T'
#print axioms arc_T_bound
#print axioms block_le_R_T
#print axioms Tpart_le
#print axioms minor_block_bound
#print axioms overhang_estimate6
#print axioms estimate6Wide_of_split
#print axioms reduction27A_wide_of_split
#print axioms estimate7Wide_of_p2
#print axioms perelliPintz_p2

end
end LeanLab.PerelliPintz1992.Burst8P2
