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
* LEAF: `rpart_block_bound`, the `R` part: display 13, Gallagher's lemma,
  P. X. Gallagher, Invent. Math. 11, 1970, pp. 329 to 339, and Cauchy and Schwarz bound it by
  the character expression `energyA` of `Decomp1624`.
* PROVED: `reduction27A_wide_of_split`, the leaf `reduction27A_wide` from the two pieces, with
  the dyadic count `J + 1 ≤ L`.

The final result `perelliPintz_p2 : MainTheorem` has the type of `perelliPintz` and carries no sorry
of its own; it is CONDITIONAL ON `siegel_walfisz_uniform`, `shiu_d2`, `rpart_block_bound` and
`Decomp1624.energy_decayA`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst8P2
import LeanLab.PerelliPintz1992.FareyFamily97
import LeanLab.PerelliPintz1992.Burst9Display13
import LeanLab.PerelliPintz1992.Burst9Gallagher

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

/-
The Section 5 development of `Burst9Pieces`, `Burst9Parseval`, `Burst9Arc`, `Burst9Clip` to
`Burst9Clip5` and `Burst9Main`, inlined here so that the module cycle
`Burst9Leaves -> Burst8P2b` no longer blocks the leaf: their nine small `def`s
(`Aset`, `Bset`, `Pset`, `Dset`, `Om`, `Fm`, `SR`, `Phi`, `gsum`) are written out at every use
site, and `Burst9Display13` and `Burst9Gallagher` are imported, their closures carrying no
unproved step reachable from here and being free of the cycle. Generated by `results/Burst8P2b-assemble.py`.
-/

namespace P3
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2
open LeanLab.PerelliPintz1992.Burst9

noncomputable section
set_option maxHeartbeats 1000000
section
-- ===== from Burst9Pieces.lean =====

/-! ### Continuity -/

theorem e_eq_character (x : ℝ) : e x = Burst9G.character293 x := by
  unfold e Burst9G.character293
  congr 1
  push_cast
  ring

theorem continuous_Rx (I : Finset ℕ) (q a : ℕ) : Continuous (Rx I q a) := by
  unfold Rx Sx Tx e
  fun_prop

theorem continuous_Psx (I : Finset ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) :
    Continuous (Psx I χ) := by
  unfold Psx e
  fun_prop

theorem continuous_Ex (I : Finset ℕ) (q a : ℕ) : Continuous (Ex I q a) := by
  unfold Ex e
  fun_prop

/-- `Ψ'` is Gallagher's exponential sum with the coefficients `cf χ`. PROVED. -/
theorem Psx_eq_cexpSum (I : Finset ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (η : ℝ) :
    Psx I χ η = Burst9G.cexpSum I (cf χ) η := by
  unfold Psx Burst9G.cexpSum
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [e_eq_character]

/-! ### The arc integral, p. 364 -/

/-- The arc integral of `|R(α - a/q)|²` over `arcM`, a part of `|α - a/q| < 1/(qQ)`, is at most
the integral of `|R(η)|²` over `|η| < 1/(qQ)`, p. 364. PROVED. -/
theorem arc_to_eta (N : ℕ) (A : ℝ) (q a : ℕ) (hq : 0 < (q : ℝ) * Q N) :
    (∫ α in arcM N A q a, ‖Decomp1519.R N q a (α - (a : ℝ) / q)‖ ^ 2) ≤
      ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)),
        ‖Decomp1519.R N q a η‖ ^ 2 := by
  set δ := 1 / ((q : ℝ) * Q N) with hδ
  set c := (a : ℝ) / q with hc
  have hδ0 : 0 < δ := by positivity
  have hcont : Continuous fun η => ‖Decomp1519.R N q a η‖ ^ 2 := by
    rw [show (fun η => ‖Decomp1519.R N q a η‖ ^ 2) =
      fun η => ‖Rx (Finset.Icc N (2 * N)) q a η‖ ^ 2 from rfl]
    exact (continuous_Rx _ q a).norm.pow 2
  have hcont' : Continuous fun α => ‖Decomp1519.R N q a (α - c)‖ ^ 2 :=
    hcont.comp (continuous_id.sub continuous_const)
  have hsub : arcM N A q a ⊆ Ioo (c - δ) (c + δ) := inter_subset_left
  calc (∫ α in arcM N A q a, ‖Decomp1519.R N q a (α - c)‖ ^ 2)
      ≤ ∫ α in Ioo (c - δ) (c + δ), ‖Decomp1519.R N q a (α - c)‖ ^ 2 :=
        setIntegral_mono_set (hcont'.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
          (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hsub)
    _ = ∫ α in (c - δ)..(c + δ), ‖Decomp1519.R N q a (α - c)‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    _ = ∫ η in (-δ)..δ, ‖Decomp1519.R N q a η‖ ^ 2 := by
        rw [intervalIntegral.integral_comp_sub_right (fun η => ‖Decomp1519.R N q a η‖ ^ 2) c]
        congr 1 <;> ring

/-! ### Minkowski's inequality for a finite sum, the Cauchy and Schwarz step of p. 364 -/

/-- Pointwise weighted Cauchy and Schwarz: for `τ_k > 0`,
`(Σ |w_k| |f_k|)² ≤ (Σ |w_k| τ_k)(Σ |w_k| |f_k|²/τ_k)`. PROVED. -/
theorem weighted_cs {κ : Type*} (X : Finset κ) (w f τ : κ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hτ : ∀ k, 0 < τ k) :
    (∑ k ∈ X, w k * f k) ^ 2 ≤ (∑ k ∈ X, w k * τ k) * ∑ k ∈ X, w k / τ k * f k ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq X (fun k => √(w k * τ k)) (fun k => √(w k / τ k) * f k)
  have e1 : ∀ k, √(w k * τ k) * (√(w k / τ k) * f k) = w k * f k := by
    intro k
    rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg (hw k) (hτ k).le)]
    have : w k * τ k * (w k / τ k) = w k ^ 2 := by
      field_simp [(hτ k).ne']
    rw [this, Real.sqrt_sq (hw k)]
  have e2 : ∀ k, √(w k * τ k) ^ 2 = w k * τ k := fun k =>
    Real.sq_sqrt (mul_nonneg (hw k) (hτ k).le)
  have e3 : ∀ k, (√(w k / τ k) * f k) ^ 2 = w k / τ k * f k ^ 2 := fun k => by
    rw [mul_pow, Real.sq_sqrt (div_nonneg (hw k) (hτ k).le)]
  simp only [e1, e2, e3] at h
  exact h

/-- **Minkowski in `L²` for a finite sum**: `Σ_p ∫ |Σ_k w_k f_{k,p}|² ≤
(Σ_k |w_k| (Σ_p ∫ |f_{k,p}|²)^{1/2})²`. PROVED. -/
theorem minkowski_fin {ι κ : Type*} (P : Finset ι) (X : Finset κ) (w : κ → ℂ)
    (f : κ → ι → ℝ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hf : ∀ k p, Continuous (f k p)) :
    (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ k ∈ X, w k * f k p η‖ ^ 2) ≤
      (∑ k ∈ X, ‖w k‖ * √(∑ p ∈ P, ∫ η in (-δ)..δ, ‖f k p η‖ ^ 2)) ^ 2 := by
  set I : κ → ℝ := fun k => ∑ p ∈ P, ∫ η in (-δ)..δ, ‖f k p η‖ ^ 2 with hI
  have hI0 : ∀ k, 0 ≤ I k := fun k => Finset.sum_nonneg fun p _ =>
    intervalIntegral.integral_nonneg (by linarith) fun η _ => sq_nonneg _
  set S := ∑ k ∈ X, ‖w k‖ * √(I k) with hS
  set W := ∑ k ∈ X, ‖w k‖ with hW
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun k _ => norm_nonneg _
  have key : ∀ t : ℝ, 0 < t →
      (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ k ∈ X, w k * f k p η‖ ^ 2) ≤ S ^ 2 + t * W * S := by
    intro t ht
    set τ : κ → ℝ := fun k => √(I k) + t with hτ
    have hτ0 : ∀ k, 0 < τ k := fun k => by
      simp only [hτ]; linarith [Real.sqrt_nonneg (I k)]
    have hpt : ∀ p η, ‖∑ k ∈ X, w k * f k p η‖ ^ 2 ≤
        (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * ‖f k p η‖ ^ 2 := by
      intro p η
      have h1 : ‖∑ k ∈ X, w k * f k p η‖ ≤ ∑ k ∈ X, ‖w k‖ * ‖f k p η‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
      have h2 := weighted_cs X (fun k => ‖w k‖) (fun k => ‖f k p η‖) τ
        (fun k => norm_nonneg _) hτ0
      have h0 : 0 ≤ ‖∑ k ∈ X, w k * f k p η‖ := norm_nonneg _
      calc ‖∑ k ∈ X, w k * f k p η‖ ^ 2 ≤ (∑ k ∈ X, ‖w k‖ * ‖f k p η‖) ^ 2 :=
            pow_le_pow_left₀ h0 h1 2
        _ ≤ _ := h2
    have hint : ∀ k p, IntervalIntegrable (fun η => ‖f k p η‖ ^ 2) volume (-δ) δ :=
      fun k p => ((hf k p).norm.pow 2).intervalIntegrable _ _
    have hsum_int : ∀ p, (∫ η in (-δ)..δ, (∑ k ∈ X, ‖w k‖ * τ k) *
        ∑ k ∈ X, ‖w k‖ / τ k * ‖f k p η‖ ^ 2) =
        (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * ∫ η in (-δ)..δ, ‖f k p η‖ ^ 2 := by
      intro p
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum
        (fun k _ => (hint k p).const_mul _)]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_const_mul]
    have hcont : ∀ p, Continuous fun η => ‖∑ k ∈ X, w k * f k p η‖ ^ 2 := fun p =>
      (continuous_finsetSum _ fun k _ => continuous_const.mul (hf k p)).norm.pow 2
    have hcont2 : ∀ p, Continuous fun η => (∑ k ∈ X, ‖w k‖ * τ k) *
        ∑ k ∈ X, ‖w k‖ / τ k * ‖f k p η‖ ^ 2 := fun p =>
      continuous_const.mul (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((hf k p).norm.pow 2))
    have step : (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ k ∈ X, w k * f k p η‖ ^ 2) ≤
        (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * I k := by
      calc (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ k ∈ X, w k * f k p η‖ ^ 2)
          ≤ ∑ p ∈ P, ∫ η in (-δ)..δ, (∑ k ∈ X, ‖w k‖ * τ k) *
              ∑ k ∈ X, ‖w k‖ / τ k * ‖f k p η‖ ^ 2 := by
            refine Finset.sum_le_sum fun p _ => ?_
            exact intervalIntegral.integral_mono_on (by linarith)
              ((hcont p).intervalIntegrable _ _) ((hcont2 p).intervalIntegrable _ _)
              fun η _ => hpt p η
        _ = ∑ p ∈ P, (∑ k ∈ X, ‖w k‖ * τ k) *
              ∑ k ∈ X, ‖w k‖ / τ k * ∫ η in (-δ)..δ, ‖f k p η‖ ^ 2 :=
            Finset.sum_congr rfl fun p _ => hsum_int p
        _ = (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * I k := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.mul_sum]
    have hb : ∀ k, ‖w k‖ / τ k * I k ≤ ‖w k‖ * √(I k) := by
      intro k
      have h1 : I k ≤ τ k * √(I k) := by
        show I k ≤ (√(I k) + t) * √(I k)
        nlinarith [Real.mul_self_sqrt (hI0 k), Real.sqrt_nonneg (I k)]
      rw [div_mul_eq_mul_div, div_le_iff₀ (hτ0 k)]
      have := mul_le_mul_of_nonneg_left h1 (norm_nonneg (w k))
      nlinarith
    have hb2 : (∑ k ∈ X, ‖w k‖ / τ k * I k) ≤ S := Finset.sum_le_sum fun k _ => hb k
    have hA : (∑ k ∈ X, ‖w k‖ * τ k) = S + t * W := by
      simp only [hτ, hS, hW, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hA0 : 0 ≤ ∑ k ∈ X, ‖w k‖ * τ k := by rw [hA]; positivity
    calc _ ≤ (∑ k ∈ X, ‖w k‖ * τ k) * ∑ k ∈ X, ‖w k‖ / τ k * I k := step
      _ ≤ (∑ k ∈ X, ‖w k‖ * τ k) * S := mul_le_mul_of_nonneg_left hb2 hA0
      _ = S ^ 2 + t * W * S := by rw [hA]; ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have ht : 0 < ε / (W * S + 1) := by positivity
  refine (key _ ht).trans ?_
  have : ε / (W * S + 1) * W * S ≤ ε := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hW0 hS0]
  linarith

/-! ### The terms with `(n, q) > 1`, display 13 -/

/-- The integers `N ≤ n ≤ 2N` with `Λ(n) ≠ 0` and `(n, q) > 1` are prime powers `p^k` with
`p ∣ q` and `k ≤ log₂ 2N`, so there are at most `q (log₂ 2N + 1)` of them, and
`Σ Λ(n) ≤ q (log₂ 2N + 1) log 2N`. PROVED. -/
theorem Ex_sum_le (N : ℕ) (q : ℕ+) :
    (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n) ≤
      (q : ℕ) * ((Nat.log 2 (2 * N) : ℝ) + 1) * Real.log (2 * N) := by
  classical
  set S := (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q) with hS
  set P := S.filter (fun n => IsPrimePow n) with hP
  have h1 : (∑ n ∈ S, Λ n) = ∑ n ∈ P, Λ n := by
    refine (Finset.sum_filter_of_ne fun n _ hn => ?_).symm
    by_contra h
    exact hn (by rw [vonMangoldt_apply, if_neg h])
  have h2 : (∑ n ∈ P, Λ n) ≤ P.card * Real.log (2 * N) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnS := (Finset.mem_filter.mp hn).1
    have hn2 : n ≤ 2 * N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnS).1).2
    refine vonMangoldt_le_log.trans ?_
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by
        have : (1 : ℝ) ≤ 2 * N ∨ N = 0 := by
          rcases Nat.eq_zero_or_pos N with hN | hN
          · right; exact hN
          · left; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
            linarith
        rcases this with h | h
        · exact h
        · exfalso
          have hpp := (Finset.mem_filter.mp hn).2
          exact (not_isPrimePow_zero) hpp)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn2)
  have h3 : P ⊆ (q.val.primeFactors ×ˢ Finset.range (Nat.log 2 (2 * N) + 1)).image
      (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hpp := (Finset.mem_filter.mp hn).2
    have hcop := (Finset.mem_filter.mp hnS).2
    have hn2 : n ≤ 2 * N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hnS).1).2
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p ∣ (q : ℕ) := by
      by_contra hnd
      exact hcop (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
    refine Finset.mem_image.mpr ⟨(p, k), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.mem_primeFactors.mpr ⟨hp, hpq, q.ne_zero⟩
    · refine Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      exact (Nat.pow_le_pow_left hp.two_le k).trans hn2
  have h4 : (P.card : ℝ) ≤ (q : ℕ) * ((Nat.log 2 (2 * N) : ℝ) + 1) := by
    have := (Finset.card_le_card h3).trans Finset.card_image_le
    rw [Finset.card_product, Finset.card_range] at this
    have hpf : q.val.primeFactors.card ≤ (q : ℕ) := by
      refine (Finset.card_le_card (s := q.val.primeFactors) (t := Finset.Icc 1 (q : ℕ)) ?_).trans
        (by simp)
      intro p hp
      have := Nat.mem_primeFactors.mp hp
      exact Finset.mem_Icc.mpr ⟨this.1.one_lt.le, Nat.le_of_dvd q.pos this.2.1⟩
    have h5 : P.card ≤ (q : ℕ) * (Nat.log 2 (2 * N) + 1) :=
      this.trans (Nat.mul_le_mul_right _ hpf)
    exact_mod_cast h5
  have hlog : 0 ≤ Real.log (2 * N) := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · exact Real.log_nonneg (by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                                linarith)
  rw [h1]
  exact h2.trans (mul_le_mul_of_nonneg_right h4 hlog)

/-- `|E(η)| ≤ Σ_{N ≤ n ≤ 2N, (n,q) > 1} Λ(n)` for `I ⊆ [N, 2N]`. PROVED. -/
theorem norm_Ex_le (N : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.Icc N (2 * N)) (q : ℕ+) (a : ℕ)
    (η : ℝ) :
    ‖Ex I q a η‖ ≤ ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n := by
  unfold Ex
  refine (norm_sum_le _ _).trans ?_
  have : ∀ n, ‖(Λ n : ℂ) * e (n * ((a : ℝ) / q + η))‖ = Λ n := by
    intro n
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  simp only [this]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hI)
    (fun n _ _ => vonMangoldt_nonneg)

/-! ### At most two numerators per modulus, display 25 -/

/-- A finite set of naturals within distance `< 1` of a real `t` has at most two elements.
PROVED. -/
theorem card_le_two_of_near (S : Finset ℕ) (t : ℝ) (hS : ∀ r ∈ S, |(r : ℝ) - t| < 1) :
    S.card ≤ 2 := by
  set m : ℤ := ⌊t⌋
  have hsub : S.image (fun r : ℕ => (r : ℤ)) ⊆ {m, m + 1} := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
    have h := abs_lt.mp (hS r hr)
    have hm1 : (m : ℝ) ≤ t := Int.floor_le t
    have hm2 : t < (m : ℝ) + 1 := Int.lt_floor_add_one t
    have hlo : m ≤ (r : ℤ) := by
      have : (m : ℝ) - 1 < (r : ℝ) := by linarith
      have : m - 1 < (r : ℤ) := by exact_mod_cast this
      omega
    have hhi : (r : ℤ) ≤ m + 1 := by
      have : (r : ℝ) < (m : ℝ) + 2 := by linarith
      have : (r : ℤ) < m + 2 := by exact_mod_cast this
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)] at h1
  exact h1.trans (Finset.card_le_two)

/-- **At most two numerators `a'` per modulus**, display 25, p. 364: the arc
`|α - a'/q| < 1/(qQ)` meets the window `|α - ξ| < 1/H` only if `|a' - qξ| < 1/Q + q/H < 1`.
PROVED. -/
theorem card_aWin_le_two {N : ℕ} (hN : 64 ≤ N) {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) {q : ℕ}
    (hq1 : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q N) : (aWin N ε ξ q).card ≤ 2 := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hQ4 : 4 ≤ Q N := by
    unfold Q; rw [← Real.sqrt_eq_rpow]
    have : (8 : ℝ) ≤ √(N : ℝ) := by
      rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hNr
    linarith
  have hQH : Q N / H N ε ≤ 1 / 2 := by
    unfold Q H
    rw [Real.rpow_add hNpos]
    have h1 : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
    have h2 : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hH0 : 0 < H N ε := Real.rpow_pos_of_pos hNpos _
  refine card_le_two_of_near _ (q * ξ) fun r hr => ?_
  obtain ⟨-, α, h1, h2⟩ := of_mem_filter hr
  have hq0 : (0 : ℝ) < q := by linarith
  have e1 : (r : ℝ) - q * ξ = q * ((r : ℝ) / q - α) + q * (α - ξ) := by
    field_simp; ring
  rw [e1]
  have h1' : |(r : ℝ) / q - α| < 1 / (q * Q N) := by rw [abs_sub_comm]; exact h1
  calc |(q : ℝ) * ((r : ℝ) / q - α) + q * (α - ξ)|
      ≤ |(q : ℝ) * ((r : ℝ) / q - α)| + |(q : ℝ) * (α - ξ)| := abs_add_le _ _
    _ = q * |(r : ℝ) / q - α| + q * |α - ξ| := by
        rw [abs_mul, abs_mul, abs_of_pos hq0]
    _ < q * (1 / (q * Q N)) + q * (1 / H N ε) := by
        have := mul_lt_mul_of_pos_left h1' hq0
        have := mul_lt_mul_of_pos_left h2 hq0
        linarith
    _ = 1 / Q N + q / H N ε := by field_simp
    _ ≤ 1 / 4 + 1 / 2 := by
        have a1 : 1 / Q N ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hQ4
        have a2 : (q : ℝ) / H N ε ≤ Q N / H N ε := div_le_div_of_nonneg_right hqQ hH0.le
        linarith
    _ < 1 := by norm_num

/-! ### Gallagher's lemma at the radius `1/(qQ)`, p. 364 -/

/-- Gallagher's lemma for `Ψ'` of display 13 at the radius `1/(qQ)`: the window is
`qQ/2 = gallagherWindow N q`. PROVED from `Burst9G.gallagher_complex`. -/
theorem gallagher_Psx (N : ℕ) (I : Finset ℕ) (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ))
    (hQ : 0 < Q N) :
    (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Psx I χ η‖ ^ 2) ≤
      2 * π ^ 2 * (1 / ((q : ℝ) * Q N)) ^ 2 *
        ∫ x : ℝ, ‖Burst9G.cwinSum I (cf χ) (gallagherWindow N q) x‖ ^ 2 := by
  have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hY : 0 < 1 / ((q : ℝ) * Q N) := by positivity
  have hw : 1 / (2 * (1 / ((q : ℝ) * Q N))) = gallagherWindow N q := by
    unfold gallagherWindow; field_simp
  have h := Burst9G.gallagher_complex I (cf χ) _ hY
  rw [hw] at h
  simp_rw [Psx_eq_cexpSum]
  exact h


end

section
-- ===== from Burst9Parseval.lean =====

/-! ### Parseval for a finite exponential sum -/


theorem e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  unfold e
  convert Complex.exp_nat_mul_two_pi_mul_I n using 1
  push_cast; ring

theorem gsum_periodic (D : Finset ℕ) (c : ℕ → ℂ) : Function.Periodic ((fun α => ∑ n ∈ D, c n * e (n * α))) 1 := by
  intro α
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (n : ℝ) * (α + 1) = n * α + n by ring, e_add, e_natCast, mul_one]

theorem continuous_gsum (D : Finset ℕ) (c : ℕ → ℂ) : Continuous ((fun α => ∑ n ∈ D, c n * e (n * α))) := by
  unfold e
  fun_prop

/-- **Parseval** on `[t, t + 1]`: `∫ |Σ_{n ∈ D} c_n e(nα)|² = Σ |c_n|²`. PROVED. -/
theorem gsum_parseval (D : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ∫ α in t..t + 1, ‖(∑ n ∈ D, c n * e (n * α))‖ ^ 2 = ∑ n ∈ D, ‖c n‖ ^ 2 := by
  have hper : Function.Periodic (fun α => ‖(∑ n ∈ D, c n * e (n * α))‖ ^ 2) 1 := fun α => by
    simp only [gsum_periodic D c α]
  rw [hper.intervalIntegral_add_eq t 0, zero_add]
  set s : Finset ℤ := D.map Nat.castEmbedding with hs
  set a : ℤ → ℂ := fun z => c z.toNat with ha
  have hS : ∀ α, (∑ n ∈ D, c n * e (n * α)) = LeanLab.CircleOrth.S s a α := by
    intro α
    unfold LeanLab.CircleOrth.S
    rw [hs, Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha, Nat.castEmbedding_apply, Int.toNat_natCast, Int.cast_natCast]
    rfl
  simp_rw [hS]
  rw [LeanLab.CircleOrth.parseval_norm, hs, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [ha, Nat.castEmbedding_apply, Int.toNat_natCast]

/-! ### The arcs of one dyadic block overlap at most nine times -/

/-- Distinct reduced fractions with denominators `≤ 2M` are `1/(4M²)` apart, so a point lies on
at most `8M/Q + 1 ≤ 9` arcs of radius `≤ 1/(MQ)`. PROVED. -/
theorem arc_mult_le (F : Finset (Σ _ : ℕ+, ℕ)) {M : ℕ} (hM : 1 ≤ M) {Qr : ℝ}
    (hMQ : (M : ℝ) ≤ Qr)
    (hF : ∀ i ∈ F, M ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) ≤ 2 * M ∧ Nat.Coprime i.2 i.1) (α : ℝ)
    (hα : ∀ i ∈ F, |α - (i.2 : ℝ) / (i.1 : ℕ)| ≤ 1 / (((i.1 : ℕ) : ℝ) * Qr)) :
    (F.card : ℝ) ≤ 9 := by
  classical
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hQ0 : 0 < Qr := by linarith
  set w := 1 / ((M : ℝ) * Qr) with hw
  have hw0 : 0 < w := by positivity
  have hsepδ : (0 : ℝ) < 1 / (4 * (M : ℝ) ^ 2) := by positivity
  have hbounds : ∀ i ∈ F, α - w ≤ (i.2 : ℝ) / (i.1 : ℕ) ∧ (i.2 : ℝ) / (i.1 : ℕ) ≤ α + w := by
    intro i hi
    obtain ⟨hMq, -, -⟩ := hF i hi
    have hq : (M : ℝ) ≤ ((i.1 : ℕ) : ℝ) := by exact_mod_cast hMq
    have h1 := hα i hi
    have h2 : 1 / (((i.1 : ℕ) : ℝ) * Qr) ≤ w :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hq hQ0.le)
    have := abs_le.mp (h1.trans h2)
    constructor <;> linarith [this.1, this.2]
  have hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      1 / (4 * (M : ℝ) ^ 2) ≤ |(i.2 : ℝ) / (i.1 : ℕ) - (j.2 : ℝ) / (j.1 : ℕ)| := by
    intro i hi j hj hne
    obtain ⟨hMi, hiM, hci⟩ := hF i hi
    obtain ⟨hMj, hjM, hcj⟩ := hF j hj
    set q := (i.1 : ℕ)
    set q' := (j.1 : ℕ)
    set r := i.2
    set r' := j.2
    have hq0 : 0 < q := i.1.pos
    have hq0' : 0 < q' := j.1.pos
    have hne' : r * q' ≠ r' * q := by
      intro heq
      have h1 : q ∣ q' := by
        have : q ∣ r * q' := ⟨r', by rw [heq]; ring⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hci) this)
      have h2 : q' ∣ q := by
        have : q' ∣ r' * q := ⟨r, by rw [← heq]; ring⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hcj) this)
      have hqq : q = q' := Nat.dvd_antisymm h1 h2
      have hrr : r = r' := by
        rw [hqq] at heq
        exact Nat.eq_of_mul_eq_mul_right hq0' heq
      apply hne
      have h1' : i.1 = j.1 := PNat.eq hqq
      exact Sigma.ext h1' (heq_of_eq hrr)
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq0'
    have e1 : (r : ℝ) / q - (r' : ℝ) / q' = (((r * q' : ℕ) : ℝ) - ((r' * q : ℕ) : ℝ)) / (q * q') := by
      push_cast; field_simp
    rw [e1, abs_div, abs_of_pos (mul_pos hqr hqr')]
    have hnum : (1 : ℝ) ≤ |((r * q' : ℕ) : ℝ) - ((r' * q : ℕ) : ℝ)| := by
      have : ((r * q' : ℕ) : ℤ) ≠ ((r' * q : ℕ) : ℤ) := by exact_mod_cast hne'
      have h := Int.one_le_abs (sub_ne_zero.mpr this)
      have : ((|((r * q' : ℕ) : ℤ) - ((r' * q : ℕ) : ℤ)| : ℤ) : ℝ) =
          |((r * q' : ℕ) : ℝ) - ((r' * q : ℕ) : ℝ)| := by push_cast; rfl
      rw [← this]; exact_mod_cast h
    have hden : (q : ℝ) * q' ≤ 4 * (M : ℝ) ^ 2 := by
      have a1 : (q : ℝ) ≤ 2 * M := by exact_mod_cast hiM
      have a2 : (q' : ℝ) ≤ 2 * M := by exact_mod_cast hjM
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (mul_pos hqr hqr')]
    have hM4 : (0 : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hnum hM4]
  have hcard := Section6.separated_interval_card_le F (fun i => (i.2 : ℝ) / (i.1 : ℕ))
    (by linarith : α - w ≤ α + w) hsepδ hbounds hsep
  have e2 : (α + w - (α - w)) / (1 / (4 * (M : ℝ) ^ 2)) + 1 = 8 * M / Qr + 1 := by
    rw [hw]; field_simp; ring
  rw [e2] at hcard
  have : 8 * (M : ℝ) / Qr ≤ 8 := by rw [div_le_iff₀ hQ0]; linarith
  linarith

/-- The sum over the arcs of one dyadic block of the integral of a continuous nonnegative
function of period `1` is at most `27` times its integral over a period. PROVED. -/
theorem arc_sum_le (F : Finset (Σ _ : ℕ+, ℕ)) {M : ℕ} (hM : 1 ≤ M) {Qr : ℝ}
    (hMQ : (M : ℝ) ≤ Qr)
    (hF : ∀ i ∈ F, M ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) ≤ 2 * M ∧ Nat.Coprime i.2 i.1 ∧
      1 ≤ i.2 ∧ i.2 ≤ (i.1 : ℕ))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hper : Function.Periodic f 1) :
    ∑ i ∈ F, (∫ η in (-(1 / (((i.1 : ℕ) : ℝ) * Qr)))..(1 / (((i.1 : ℕ) : ℝ) * Qr)),
        f ((i.2 : ℝ) / (i.1 : ℕ) + η)) ≤ 27 * ∫ α in (0 : ℝ)..1, f α := by
  classical
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hQ1 : 1 ≤ Qr := by linarith
  set x : (Σ _ : ℕ+, ℕ) → ℝ := fun i => (i.2 : ℝ) / (i.1 : ℕ) with hx
  set d : (Σ _ : ℕ+, ℕ) → ℝ := fun i => 1 / (((i.1 : ℕ) : ℝ) * Qr) with hd
  set g : (Σ _ : ℕ+, ℕ) → Set ℝ := fun i => Ioc (x i - d i) (x i + d i) with hg
  have hd0 : ∀ i : (Σ _ : ℕ+, ℕ), 0 < d i := fun i => by
    have : (0 : ℝ) < ((i.1 : ℕ) : ℝ) := by exact_mod_cast i.1.pos
    simp only [hd]; positivity
  have hd1 : ∀ i : (Σ _ : ℕ+, ℕ), d i ≤ 1 := fun i => by
    have : (1 : ℝ) ≤ ((i.1 : ℕ) : ℝ) := by exact_mod_cast i.1.pos
    simp only [hd]
    rw [div_le_one (by positivity)]; nlinarith
  have hxI : ∀ i ∈ F, 0 ≤ x i ∧ x i ≤ 1 := fun i hi => by
    obtain ⟨-, -, -, h1, h2⟩ := hF i hi
    have hq : (0 : ℝ) < ((i.1 : ℕ) : ℝ) := by exact_mod_cast i.1.pos
    have h2' : (i.2 : ℝ) ≤ ((i.1 : ℕ) : ℝ) := by exact_mod_cast h2
    simp only [hx]
    exact ⟨by positivity, (div_le_one hq).mpr h2'⟩
  have hgI : ∀ i ∈ F, g i ⊆ Icc (-1) 2 := fun i hi y hy => by
    have := hxI i hi
    have := hd1 i
    simp only [hg, mem_Ioc] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hfi : ∀ s : Set ℝ, s ⊆ Icc (-1) 2 → IntegrableOn f s := fun s hs =>
    (hf.integrableOn_Icc).mono_set hs
  -- each arc integral as a set integral
  have harc : ∀ i ∈ F, (∫ η in (-(d i))..(d i), f (x i + η)) = ∫ y, (g i).indicator f y := by
    intro i hi
    rw [intervalIntegral.integral_comp_add_left f (x i), integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le (by linarith [hd0 i])]
    rfl
  rw [Finset.sum_congr rfl harc]
  rw [← integral_finset_sum _ fun i hi =>
    (hfi _ (hgI i hi)).integrable_indicator measurableSet_Ioc]
  -- the pointwise multiplicity bound
  have hpt : ∀ y, ∑ i ∈ F, (g i).indicator f y ≤ 9 * (Icc (-1 : ℝ) 2).indicator f y := by
    intro y
    have e1 : ∑ i ∈ F, (g i).indicator f y = ((F.filter (fun i => y ∈ g i)).card : ℝ) * f y := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : y ∈ g i
      · rw [indicator_of_mem h, if_pos h]; push_cast; ring
      · rw [indicator_of_notMem h, if_neg h]
    rw [e1]
    by_cases hy : y ∈ Icc (-1 : ℝ) 2
    · rw [indicator_of_mem hy]
      have hc := arc_mult_le (F.filter (fun i => y ∈ g i)) hM hMQ
        (fun i hi => by
          obtain ⟨h1, h2, h3, -, -⟩ := hF i (Finset.mem_filter.mp hi).1
          exact ⟨h1, h2, h3⟩)
        y (fun i hi => by
          have hy' := (Finset.mem_filter.mp hi).2
          simp only [hg, mem_Ioc] at hy'
          rw [abs_le]
          constructor <;> simp only [hx, hd] at hy' ⊢ <;> linarith [hy'.1, hy'.2])
      exact mul_le_mul_of_nonneg_right hc (hf0 y)
    · rw [indicator_of_notMem hy, mul_zero]
      have : (F.filter (fun i => y ∈ g i)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi hyi
        exact hy (hgI i hi hyi)
      rw [this]; simp
  have hint9 : Integrable (fun y => 9 * (Icc (-1 : ℝ) 2).indicator f y) :=
    ((hfi _ subset_rfl).integrable_indicator measurableSet_Icc).const_mul 9
  refine (integral_mono (integrable_finset_sum _ fun i hi =>
    (hfi _ (hgI i hi)).integrable_indicator measurableSet_Ioc) hint9 hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have h1 : ∫ α in (-1 : ℝ)..2, f α =
      (∫ α in (-1 : ℝ)..(-1) + 1, f α) + (∫ α in (0 : ℝ)..0 + 1, f α) +
        ∫ α in (1 : ℝ)..1 + 1, f α := by
    norm_num
    rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  rw [h1, hper.intervalIntegral_add_eq (-1) 0, hper.intervalIntegral_add_eq 1 0, zero_add]
  ring

/-! ### The Parseval cost -/

/-- `1/φ(q)² ≤ 4(1 + ℓ)²/M²` for `M ≤ q`, `log q ≤ ℓ`, from `φ(q) ≫ q/log q`. PROVED. -/
theorem inv_totient_sq_le {q : ℕ} (hq : 0 < q) {ℓ : ℝ} (hlq : Real.log q ≤ ℓ) {M : ℝ}
    (hM0 : 0 < M) (hqM : M ≤ q) :
    1 / (Nat.totient q : ℝ) ^ 2 ≤ 4 * (1 + ℓ) ^ 2 / M ^ 2 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ : (q : ℝ) / (2 * (1 + ℓ)) ≤ (Nat.totient q : ℝ) := by
    have h1 := totient_ge_log_two_mul_div hq
    refine le_trans ?_ h1
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have h3 : 1 + Real.log (q : ℝ) ≤ 2 * Real.log 2 * (1 + ℓ) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ (q : ℝ))
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h5 : (q : ℝ) ≤ 2 * (1 + ℓ) * (Nat.totient q : ℝ) := by
    rw [div_le_iff₀ (by linarith)] at hφ; linarith
  have h6 : M ≤ 2 * (1 + ℓ) * (Nat.totient q : ℝ) := hqM.trans h5
  have h7 := pow_le_pow_left₀ hM0.le h6 2
  nlinarith

/-- `|Y(M)| ≤ 2M`: its moduli are distinct integers in `[M, 2M]`. PROVED. -/
theorem card_Y_le_two_M (N : ℕ) (ε ξ : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ((Y N ε ξ M).card : ℝ) ≤ 2 * M := by
  have h1 : (Y N ε ξ M).card ≤ (Finset.Icc M (2 * M)).card := by
    refine Finset.card_le_card_of_injOn (fun q : ℕ+ => (q : ℕ)) (fun q hq => ?_)
      (fun q _ q' _ h => PNat.eq h)
    obtain ⟨-, hMq, hqM, -⟩ := of_mem_filter hq
    exact Finset.mem_Icc.mpr ⟨hMq, hqM⟩
  rw [Nat.card_Icc] at h1
  have : ((Y N ε ξ M).card : ℝ) ≤ ((2 * M + 1 - M : ℕ) : ℝ) := by exact_mod_cast h1
  have e : ((2 * M + 1 - M : ℕ) : ℝ) = M + 1 := by
    rw [show 2 * M + 1 - M = M + 1 by omega]; push_cast; ring
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  linarith


/-- **The Parseval cost of the end blocks, PROVED**, the route of `Decomp1624.reduction27A`
for display 27, p. 364: for any `D ⊆ [N, 2N]`, the `R` part over `D`, integrated over the arcs
`|η| < 1/(qQ)` of one dyadic block `Y(M)` of p. 363 and the numerators `a'` of display 25, is at
most `344 |D| L²`; by `|R|² ≤ 2|S|² + 2μ²/φ² |T|²`, `arc_sum_le` with Parseval for `S`,
Parseval for `T`, `|a'| ≤ 2`, `|Y(M)| ≤ 2M` and `φ(q) ≫ q/log q`. -/
theorem parseval_cost_proved :
    ∃ C₀ N₁ : ℝ, 0 < C₀ ∧ ∀ N : ℕ, N₁ ≤ N → ∀ ε ξ : ℝ, 0 < ε → ∀ M : ℕ, 1 ≤ M →
      (M : ℝ) ≤ Q N → ∀ D : Finset ℕ, D ⊆ Finset.Icc N (2 * N) →
        ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx D q r η‖ ^ 2) ≤
            C₀ * D.card * L N ^ 2 := by
  refine ⟨344, 64, by norm_num, fun N hN ε ξ hε M hM1 hMQ D hD => ?_⟩
  have hN64 : 64 ≤ N := by exact_mod_cast hN
  have hNr : (64 : ℝ) ≤ N := hN
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ := L N with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    simp only [hℓdef, L]
    have : Real.log 64 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    have h64 : (1 : ℝ) ≤ Real.log 64 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have hQ4 : 4 ≤ Q N := by
    unfold Q; rw [← Real.sqrt_eq_rpow]
    have : (8 : ℝ) ≤ √(N : ℝ) := by
      rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hNr
    linarith
  have hQ0 : 0 < Q N := by linarith
  have hQN : Q N ≤ N := by
    unfold Q; rw [← Real.sqrt_eq_rpow]
    have := Real.sqrt_le_sqrt (show (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
    rw [Real.sqrt_sq hNpos.le] at this; linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  set fS : ℝ → ℝ := fun α => ‖(∑ n ∈ D, (fun n => (Λ n : ℂ)) n * e (n * α))‖ ^ 2 with hfS
  set fT : ℝ → ℝ := fun η => ‖(∑ n ∈ D, (fun _ => (1 : ℂ)) n * e (n * η))‖ ^ 2 with hfT
  have cS : Continuous fS := (continuous_gsum _ _).norm.pow 2
  have cT : Continuous fT := (continuous_gsum _ _).norm.pow 2
  -- the pointwise split
  have hpt : ∀ (q r : ℕ) (η : ℝ), ‖Rx D q r η‖ ^ 2 ≤
      2 * fS ((r : ℝ) / q + η) + 2 * (Decomp1519.muφ q ^ 2 * fT η) := by
    intro q r η
    have e1 : Rx D q r η = (∑ n ∈ D, (fun n => (Λ n : ℂ)) n * e (n * ((r : ℝ) / q + η))) +
        (-((Decomp1519.muφ q : ℂ)) * (∑ n ∈ D, (fun _ => (1 : ℂ)) n * e (n * η))) := by
      unfold Rx Sx Tx
      simp only [one_mul]
      ring
    rw [e1]
    refine (norm_add_sq_le _ _).trans (le_of_eq ?_)
    simp only [hfS, hfT, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  -- the `T` integral
  have hTint : ∀ q : ℕ+, ((q : ℕ) : ℝ) ≤ Q N →
      (∫ η in (-(1 / (((q : ℕ) : ℝ) * Q N)))..(1 / (((q : ℕ) : ℝ) * Q N)), fT η) ≤ D.card := by
    intro q hqQ
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
    have hδ : 1 / (((q : ℕ) : ℝ) * Q N) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hδ0 : 0 < 1 / (((q : ℕ) : ℝ) * Q N) := by positivity
    have hP := gsum_parseval D (fun _ => (1 : ℂ)) (-(1 / 2))
    simp only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hP
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at hP
    rw [← hP]
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) hδ
      (Eventually.of_forall fun x => sq_nonneg _) (cT.intervalIntegrable _ _)
  -- per arc
  have harc : ∀ q ∈ Y N ε ξ M, ∀ r ∈ aWin N ε ξ (q : ℕ),
      (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx D q r η‖ ^ 2) ≤
        2 * (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) +
          2 * (Decomp1519.muφ q ^ 2 * D.card) := by
    intro q hq r hr
    obtain ⟨hqim, -, -, -⟩ := of_mem_filter hq
    obtain ⟨q0, -, hq0⟩ := Finset.mem_image.mp hqim
    have hqI := Finset.mem_Icc.mp q0.property
    have hqval : (q : ℕ) = q0.val := by rw [← hq0]; rfl
    have hqQ : ((q : ℕ) : ℝ) ≤ Q N :=
      (Nat.cast_le.mpr (by rw [hqval]; exact hqI.2)).trans (Nat.floor_le hQ0.le)
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
    have hδ0 : 0 < 1 / (((q : ℕ) : ℝ) * Q N) := by positivity
    have c1 : Continuous fun η => ‖Rx D q r η‖ ^ 2 := (continuous_Rx D q r).norm.pow 2
    have c2 : Continuous fun η => fS ((r : ℝ) / q + η) := cS.comp (continuous_const.add continuous_id)
    have c3 : Continuous fun η => 2 * fS ((r : ℝ) / q + η) + 2 * (Decomp1519.muφ q ^ 2 * fT η) :=
      (continuous_const.mul c2).add (continuous_const.mul (continuous_const.mul cT))
    calc (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx D q r η‖ ^ 2)
        ≤ ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)),
            (2 * fS ((r : ℝ) / q + η) + 2 * (Decomp1519.muφ q ^ 2 * fT η)) :=
          intervalIntegral.integral_mono_on (by linarith) (c1.intervalIntegrable _ _)
            (c3.intervalIntegrable _ _) fun η _ => hpt q r η
      _ = 2 * (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) +
            2 * (Decomp1519.muφ q ^ 2 *
              ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fT η) := by
          have i1 : IntervalIntegrable (fun η => 2 * fS ((r : ℝ) / q + η)) volume
              (-(1 / ((q : ℝ) * Q N))) (1 / ((q : ℝ) * Q N)) :=
            (continuous_const.mul c2).intervalIntegrable _ _
          have i2 : IntervalIntegrable (fun η => 2 * (Decomp1519.muφ q ^ 2 * fT η)) volume
              (-(1 / ((q : ℝ) * Q N))) (1 / ((q : ℝ) * Q N)) :=
            (continuous_const.mul (continuous_const.mul cT)).intervalIntegrable _ _
          rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ _ := by
          have h := hTint q hqQ
          have hm : 0 ≤ Decomp1519.muφ q ^ 2 := sq_nonneg _
          have := mul_le_mul_of_nonneg_left h hm
          linarith
  -- the `S` part by the arc multiplicity
  have hSsum : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
      ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) ≤
      27 * (D.card * (2 * ℓ) ^ 2) := by
    rw [← Finset.sum_sigma (Y N ε ξ M) (fun q => aWin N ε ξ (q : ℕ))
      (fun i : (Σ _ : ℕ+, ℕ) => ∫ η in (-(1 / (((i.1 : ℕ) : ℝ) * Q N)))..(1 / (((i.1 : ℕ) : ℝ) * Q N)),
        fS ((i.2 : ℝ) / (i.1 : ℕ) + η))]
    have hF : ∀ i ∈ (Y N ε ξ M).sigma (fun q => aWin N ε ξ (q : ℕ)),
        M ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) ≤ 2 * M ∧ Nat.Coprime i.2 i.1 ∧ 1 ≤ i.2 ∧ i.2 ≤ (i.1 : ℕ) := by
      intro i hi
      obtain ⟨hq, hr⟩ := Finset.mem_sigma.mp hi
      obtain ⟨-, hMq, hqM, -⟩ := of_mem_filter hq
      have hrA := (of_mem_filter hr).1
      obtain ⟨hrI, hcop⟩ := Finset.mem_filter.mp hrA
      exact ⟨hMq, hqM, hcop, (Finset.mem_Icc.mp hrI).1, (Finset.mem_Icc.mp hrI).2⟩
    have hper : Function.Periodic fS 1 := fun α => by simp only [hfS, gsum_periodic D _ α]
    have h1 := arc_sum_le _ hM1 hMQ hF fS cS (fun x => sq_nonneg _) hper
    refine h1.trans ?_
    have hP := gsum_parseval D (fun n => (Λ n : ℂ)) 0
    rw [zero_add] at hP
    rw [show (∫ α in (0 : ℝ)..1, fS α) = ∑ n ∈ D, ‖(Λ n : ℂ)‖ ^ 2 from hP]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn2 := (Finset.mem_Icc.mp (hD hn)).2
    have hn1 := (Finset.mem_Icc.mp (hD hn)).1
    rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    have hl : Λ n ≤ 2 * ℓ := by
      refine vonMangoldt_le_log.trans ?_
      have hnpos : (0 : ℝ) < n := by
        have : (64 : ℕ) ≤ n := hN64.trans hn1
        exact_mod_cast (by omega : 0 < n)
      have : Real.log n ≤ Real.log (2 * N) :=
        Real.log_le_log hnpos (by exact_mod_cast hn2)
      have h2 : Real.log (2 * N) ≤ 2 * ℓ := by
        simp only [hℓdef, L]
        rw [Real.log_mul (by norm_num) (by linarith)]
        have : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by linarith)
        linarith
      linarith
    exact pow_le_pow_left₀ vonMangoldt_nonneg hl 2
  -- the `T` part
  have hTsum : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
      2 * (Decomp1519.muφ q ^ 2 * D.card)) ≤ 128 * D.card * ℓ ^ 2 := by
    have hq : ∀ q ∈ Y N ε ξ M, (∑ r ∈ aWin N ε ξ (q : ℕ),
        2 * (Decomp1519.muφ q ^ 2 * D.card)) ≤ 4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card := by
      intro q hq
      obtain ⟨hqim, hMq, -, -⟩ := of_mem_filter hq
      obtain ⟨q0, -, hq0⟩ := Finset.mem_image.mp hqim
      have hqI := Finset.mem_Icc.mp q0.property
      have hqval : (q : ℕ) = q0.val := by rw [← hq0]; rfl
      have hqQ : ((q : ℕ) : ℝ) ≤ Q N :=
        (Nat.cast_le.mpr (by rw [hqval]; exact hqI.2)).trans (Nat.floor_le hQ0.le)
      have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
      have hlq : Real.log ((q : ℕ) : ℝ) ≤ ℓ := by
        simp only [hℓdef, L]; exact Real.log_le_log (by linarith) (hqQ.trans hQN)
      have hqM : (M : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hMq
      have hinv := inv_totient_sq_le q.pos hlq hM0 hqM
      have hmu := (Decomp1519.muφ_sq_le (q := (q : ℕ))).trans hinv
      have hc : ((aWin N ε ξ (q : ℕ)).card : ℝ) ≤ 2 := by
        exact_mod_cast card_aWin_le_two hN64 hε ξ q.pos hqQ
      rw [Finset.sum_const, nsmul_eq_mul]
      have hD0 : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
      have h1 : 2 * (Decomp1519.muφ q ^ 2 * D.card) ≤ 2 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2 * D.card) := by
        have := mul_le_mul_of_nonneg_right hmu hD0
        linarith
      have h2 : 0 ≤ 2 * (Decomp1519.muφ q ^ 2 * D.card) := by positivity
      calc ((aWin N ε ξ (q : ℕ)).card : ℝ) * (2 * (Decomp1519.muφ q ^ 2 * D.card))
          ≤ 2 * (2 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2 * D.card)) :=
            mul_le_mul hc h1 h2 (by norm_num)
        _ = 4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card := by ring
    refine (Finset.sum_le_sum hq).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hY := card_Y_le_two_M N ε ξ hM1
    have hD0 : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
    have h0 : 0 ≤ 4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card := by positivity
    calc ((Y N ε ξ M).card : ℝ) * (4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card)
        ≤ (2 * M) * (4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card) :=
          mul_le_mul_of_nonneg_right hY h0
      _ = 32 * (1 + ℓ) ^ 2 / M * D.card := by field_simp; ring
      _ ≤ 32 * (1 + ℓ) ^ 2 * D.card := by
          have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
          have : 32 * (1 + ℓ) ^ 2 / M ≤ 32 * (1 + ℓ) ^ 2 :=
            div_le_self (by positivity) hM1r
          exact mul_le_mul_of_nonneg_right this hD0
      _ ≤ 128 * D.card * ℓ ^ 2 := by
          have h4 : (1 + ℓ) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ 32 * D.card)
          linarith
  -- assemble
  calc (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
        ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx D q r η‖ ^ 2)
      ≤ ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (2 * (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) +
            2 * (Decomp1519.muφ q ^ 2 * D.card)) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r hr => harc q hq r hr
    _ = 2 * (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) +
          ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), 2 * (Decomp1519.muφ q ^ 2 * D.card) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ 2 * (27 * (D.card * (2 * ℓ) ^ 2)) + 128 * D.card * ℓ ^ 2 := by linarith
    _ = 344 * D.card * L N ^ 2 := by rw [hℓdef]; ring


end

section
-- ===== from Burst9Arc.lean =====



theorem card_Pset (N K0 : ℕ) (hK : K0 ≤ 2 * N) : (((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N)))).card = K0 * K0 := by
  rw [Finset.card_product, Nat.card_Ico, Nat.card_Ioc]
  congr 1 <;> omega

theorem Icc_sub_of_mem {N K0 : ℕ} {p : ℕ × ℕ} (hp : p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N)))) :
    Finset.Icc p.1 p.2 ⊆ Finset.Icc N (2 * N) := by
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have ha' := Finset.mem_Ico.mp ha
  have hb' := Finset.mem_Ioc.mp hb
  intro n hn
  have := Finset.mem_Icc.mp hn
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem card_Dset_le {N K0 : ℕ} (hK : 4 * K0 ≤ N) {p : ℕ × ℕ} (hp : p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N)))) :
    ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)).card ≤ 2 * K0 := by
  rw [Finset.card_sdiff_of_subset (Icc_sub_of_mem hp), Nat.card_Icc, Nat.card_Icc]
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have ha' := Finset.mem_Ico.mp ha
  have hb' := Finset.mem_Ioc.mp hb
  omega

theorem Dset_sub (N : ℕ) (p : ℕ × ℕ) : (Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2) ⊆ Finset.Icc N (2 * N) := Finset.sdiff_subset

/-- `R = R_{[a,b]} + R_D`. PROVED. -/
theorem R_split {N K0 : ℕ} {p : ℕ × ℕ} (hp : p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N)))) (q a : ℕ) (η : ℝ) :
    Decomp1519.R N q a η = Rx (Finset.Icc p.1 p.2) q a η + Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q a η := by
  calc Decomp1519.R N q a η = Rx (Finset.Icc N (2 * N)) q a η := rfl
    _ = Rx (Finset.Icc p.1 p.2 ∪ (Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q a η := by
        rw [Finset.union_sdiff_of_subset (Icc_sub_of_mem hp)]
    _ = _ := Rx_union _ _ Finset.disjoint_sdiff q a η

theorem sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  have h : x + y ≤ (√x + √y) ^ 2 := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc √(x + y) ≤ √((√x + √y) ^ 2) := Real.sqrt_le_sqrt h
    _ = √x + √y := Real.sqrt_sq (by positivity)


theorem WA_sq (N : ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) :
    WA N χ ^ 2 = (1 / (((q : ℝ) * Q N) ^ 2 * N)) *
      (windowMean N χ (gallagherWindow N q) +
        (1 / gallagherWindow N q) * ∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u) := by
  unfold WA
  rw [Real.sq_sqrt]
  have h1 : 0 ≤ windowMean N χ (gallagherWindow N q) :=
    setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  have h2 : 0 ≤ ∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u :=
    setIntegral_nonneg measurableSet_Ioc fun u _ =>
      setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  have h3 : 0 ≤ 1 / gallagherWindow N q := by
    unfold gallagherWindow Q; positivity
  have h4 : 0 ≤ 1 / (((q : ℝ) * Q N) ^ 2 * N) := by unfold Q; positivity
  positivity

set_option maxHeartbeats 1000000 in
/-- **One arc of a dyadic block, displays 13 and 23 to 27, p. 364**, from the end averaging,
display 13, Minkowski, Gallagher and the averaged clipped window sums `hclip`, the leaf
`clip_average_proved` at the modulus `q`. PROVED from `hclip`. -/
theorem qr_bound {N K0 : ℕ} (hK1 : 1 ≤ K0) (hK4 : 4 * K0 ≤ N) (q : ℕ+) (hQ : 0 < Q N)
    {r : ℕ} (hr : Nat.Coprime r q) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hclip : ∀ χ : DirichletCharacter ℂ (q : ℕ),
      (1 / (K0 : ℝ) ^ 2) * ∑ a ∈ (Finset.Ico N (N + K0)), ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)),
          (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) (gallagherWindow N q) x‖ ^ 2) ≤
        C₁ * (windowMean N χ (gallagherWindow N q) + (1 / (K0 : ℝ)) *
          (∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u) +
            (Real.log (2 * N) + 1) ^ 2)) :
    (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Decomp1519.R N q r η‖ ^ 2) ≤
      (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N))),
          (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2) +
        16 * π ^ 2 * C₁ * max 1 (gallagherWindow N q / K0) * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 /
          (Nat.totient (q : ℕ) : ℝ) ^ 2 +
        16 * π ^ 2 * C₁ * (Real.log (2 * N) + 1) ^ 2 / Q N ^ 2 +
        8 * (1 / ((q : ℝ) * Q N)) *
          (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n) ^ 2 := by
  -- notation
  set δ : ℝ := 1 / ((q : ℝ) * Q N) with hδ
  set h : ℝ := gallagherWindow N q with hh
  set lam : ℝ := max 1 (h / K0) with hlam
  set E : ℝ := ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n with hE
  set P := ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N))) with hP
  set φq : ℝ := (Nat.totient (q : ℕ) : ℝ) with hφq
  set L2 : ℝ := Real.log (2 * N) + 1 with hL2
  have hq0 : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
  have hδ0 : 0 < δ := by positivity
  have hh0 : 0 < h := by simp only [hh, gallagherWindow]; positivity
  have hK0r : (0 : ℝ) < K0 := by exact_mod_cast hK1
  have hφ0 : 0 < φq := by simp only [hφq]; exact_mod_cast Nat.totient_pos.mpr q.pos
  have hcard : (P.card : ℝ) = (K0 : ℝ) ^ 2 := by
    rw [hP, card_Pset N K0 (by omega)]; push_cast; ring
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  -- continuity
  have cR : Continuous fun η => ‖Decomp1519.R N q r η‖ ^ 2 :=
    (continuous_Rx (Finset.Icc N (2 * N)) q r).norm.pow 2
  have cRx : ∀ I : Finset ℕ, Continuous fun η => ‖Rx I q r η‖ ^ 2 := fun I =>
    (continuous_Rx I q r).norm.pow 2
  have hδδ : -δ ≤ δ := by linarith
  have cRx2 : ∀ I : Finset ℕ, Continuous fun η => 2 * ‖Rx I q r η‖ ^ 2 := fun I =>
    continuous_const.mul (cRx I)
  -- Step 1: the end averaging
  have step1 : (∫ η in (-δ)..δ, ‖Decomp1519.R N q r η‖ ^ 2) ≤
      (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) +
        (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2) := by
    have hp : ∀ p ∈ P, (∫ η in (-δ)..δ, ‖Decomp1519.R N q r η‖ ^ 2) ≤
        2 * (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) +
          2 * ∫ η in (-δ)..δ, ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2 := by
      intro p hpP
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((cRx2 _).intervalIntegrable _ _)
          ((cRx2 _).intervalIntegrable _ _)]
      refine intervalIntegral.integral_mono_on hδδ (cR.intervalIntegrable _ _)
        (((cRx2 _).add (cRx2 _)).intervalIntegrable _ _) ?_
      intro η _
      rw [R_split hpP]
      exact norm_add_sq_le _ _
    have hsum := Finset.sum_le_sum hp
    rw [Finset.sum_const, nsmul_eq_mul, hcard, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum] at hsum
    have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
    rw [show (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) +
        (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2) =
        (2 * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) +
          2 * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2)) / (K0 : ℝ) ^ 2 by ring]
    rw [le_div_iff₀ hK2]
    linarith
  -- Step 2: display 13 and the terms with `(n, q) > 1`
  set w : DirichletCharacter ℂ (q : ℕ) → ℂ := fun χ =>
    χ⁻¹ (r : ZMod (q : ℕ)) * gaussSum χ ZMod.stdAddChar with hw
  set f : DirichletCharacter ℂ (q : ℕ) → ℕ × ℕ → ℝ → ℂ := fun χ p η =>
    Psx (Finset.Icc p.1 p.2) χ⁻¹ η with hf
  have cf' : ∀ χ p, Continuous (f χ p) := fun χ p => continuous_Psx _ _
  have hmain_eq : ∀ p η, Rx (Finset.Icc p.1 p.2) q r η =
      (1 / (φq : ℂ)) * (∑ χ, w χ * f χ p η) + Ex (Finset.Icc p.1 p.2) q r η := by
    intro p η
    rw [display13 _ q hr η, hφq]
    push_cast
    rfl
  have step2 : ∀ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) ≤
      2 * (1 / φq ^ 2) * (∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) + 2 * (2 * δ * E ^ 2) := by
    intro p hpP
    have cM : Continuous fun η => ‖∑ χ, w χ * f χ p η‖ ^ 2 :=
      (continuous_finsetSum _ fun χ _ => continuous_const.mul (cf' χ p)).norm.pow 2
    have cM2 : Continuous fun η => 2 * (1 / φq ^ 2) * ‖∑ χ, w χ * f χ p η‖ ^ 2 :=
      continuous_const.mul cM
    have hpt : ∀ η, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2 ≤
        2 * (1 / φq ^ 2) * ‖∑ χ, w χ * f χ p η‖ ^ 2 + 2 * E ^ 2 := by
      intro η
      rw [hmain_eq]
      refine (norm_add_sq_le _ _).trans ?_
      have h1 : ‖(1 / (φq : ℂ)) * (∑ χ, w χ * f χ p η)‖ ^ 2 =
          (1 / φq ^ 2) * ‖∑ χ, w χ * f χ p η‖ ^ 2 := by
        rw [norm_mul, mul_pow, norm_div, norm_one, Complex.norm_real,
          Real.norm_of_nonneg hφ0.le]
        ring
      have h2 : ‖Ex (Finset.Icc p.1 p.2) q r η‖ ^ 2 ≤ E ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_Ex_le N _ (Icc_sub_of_mem hpP) q r η) 2
      rw [h1]; linarith
    calc (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2)
        ≤ ∫ η in (-δ)..δ, (2 * (1 / φq ^ 2) * ‖∑ χ, w χ * f χ p η‖ ^ 2 + 2 * E ^ 2) :=
          intervalIntegral.integral_mono_on hδδ ((cRx _).intervalIntegrable _ _)
            ((cM2.add continuous_const).intervalIntegrable _ _) fun η _ => hpt η
      _ = 2 * (1 / φq ^ 2) * (∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) + 2 * (2 * δ * E ^ 2) := by
          rw [intervalIntegral.integral_add (cM2.intervalIntegrable _ _)
            intervalIntegrable_const, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const]
          simp only [smul_eq_mul]; ring
  -- Step 3: Minkowski
  set Iχ : DirichletCharacter ℂ (q : ℕ) → ℝ := fun χ =>
    ∑ p ∈ P, ∫ η in (-δ)..δ, ‖f χ p η‖ ^ 2 with hIχ
  have step3 : (∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) ≤
      (∑ χ, ‖w χ‖ * √(Iχ χ)) ^ 2 :=
    minkowski_fin P Finset.univ w f δ hδ0.le cf'
  -- Step 4: Gallagher and the leaf, for each character
  have step4 : ∀ χ : DirichletCharacter ℂ (q : ℕ), Iχ χ ≤
      2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁ * (lam * N * WA N χ⁻¹ ^ 2 + δ ^ 2 * L2 ^ 2) := by
    intro χ
    have hg : ∀ p ∈ P, (∫ η in (-δ)..δ, ‖f χ p η‖ ^ 2) ≤ 2 * π ^ 2 * δ ^ 2 *
        ∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc p.1 p.2) (cf χ⁻¹) h x‖ ^ 2 :=
      fun p _ => gallagher_Psx N _ q χ⁻¹ hQ
    have hs := Finset.sum_le_sum hg
    rw [← Finset.mul_sum] at hs
    have hc := hclip χ⁻¹
    rw [show (∑ a ∈ (Finset.Ico N (N + K0)), ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)),
        ∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ⁻¹) (gallagherWindow N q) x‖ ^ 2) =
        ∑ p ∈ P, ∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc p.1 p.2) (cf χ⁻¹) h x‖ ^ 2 by
      rw [hP, Finset.sum_product]] at hc
    set G := ∑ p ∈ P, ∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc p.1 p.2) (cf χ⁻¹) h x‖ ^ 2
    have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
    have hG : G ≤ (K0 : ℝ) ^ 2 * (C₁ * (windowMean N χ⁻¹ h + (1 / (K0 : ℝ)) *
        (∫ u in Ioc (0 : ℝ) h, windowMean N χ⁻¹ u) + L2 ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hc hK2.le
      rwa [← mul_assoc, mul_one_div_cancel hK2.ne', one_mul] at this
    -- the window terms in `WA`
    have hw1 : 0 ≤ windowMean N χ⁻¹ h :=
      setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
    have hw2 : 0 ≤ ∫ u in Ioc (0 : ℝ) h, windowMean N χ⁻¹ u :=
      setIntegral_nonneg measurableSet_Ioc fun u _ =>
        setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
    have hlamK : 1 / (K0 : ℝ) ≤ lam * (1 / h) := by
      have : h / K0 ≤ lam := le_max_right _ _
      rw [div_le_iff₀ hK0r] at this
      rw [div_le_iff₀ hK0r, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hh0]
      nlinarith
    have hWA : windowMean N χ⁻¹ h + (1 / (K0 : ℝ)) * (∫ u in Ioc (0 : ℝ) h, windowMean N χ⁻¹ u) ≤
        lam * ((((q : ℕ) : ℝ) * Q N) ^ 2 * N * WA N χ⁻¹ ^ 2) := by
      rw [WA_sq]
      have hN0 : (0 : ℝ) < N := by
        have : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
        linarith
      have e1 : (((q : ℕ) : ℝ) * Q N) ^ 2 * N * ((1 / ((((q : ℕ) : ℝ) * Q N) ^ 2 * N)) *
          (windowMean N χ⁻¹ (gallagherWindow N q) + (1 / gallagherWindow N q) *
            ∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ⁻¹ u)) =
          windowMean N χ⁻¹ h + (1 / h) * ∫ u in Ioc (0 : ℝ) h, windowMean N χ⁻¹ u := by
        rw [← hh]; field_simp
      rw [e1]
      have := mul_le_mul_of_nonneg_right hlamK hw2
      nlinarith
    have hδq : δ ^ 2 * ((((q : ℕ) : ℝ) * Q N) ^ 2) = 1 := by
      rw [hδ]; field_simp
    calc Iχ χ = ∑ p ∈ P, ∫ η in (-δ)..δ, ‖f χ p η‖ ^ 2 := rfl
      _ ≤ 2 * π ^ 2 * δ ^ 2 * G := hs
      _ ≤ 2 * π ^ 2 * δ ^ 2 * ((K0 : ℝ) ^ 2 * (C₁ * (lam * ((((q : ℕ) : ℝ) * Q N) ^ 2 * N *
            WA N χ⁻¹ ^ 2) + L2 ^ 2))) := by
          refine mul_le_mul_of_nonneg_left (hG.trans ?_) (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) hC₁.le
      _ = 2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁ * (lam * N * WA N χ⁻¹ ^ 2 *
            (δ ^ 2 * ((((q : ℕ) : ℝ) * Q N) ^ 2)) + δ ^ 2 * L2 ^ 2) := by ring
      _ = _ := by rw [hδq, mul_one]
  -- Step 5: the square roots
  set c0 : ℝ := √(2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁) with hc0
  have hc00 : 0 ≤ c0 := Real.sqrt_nonneg _
  have hWA0 : ∀ χ : DirichletCharacter ℂ (q : ℕ), 0 ≤ WA N χ := fun χ => Real.sqrt_nonneg _
  have hL20 : 0 ≤ L2 := by
    simp only [hL2]
    have : 0 ≤ Real.log (2 * N) := by
      have : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
      have : (1 : ℝ) ≤ K0 := by exact_mod_cast hK1
      exact Real.log_nonneg (by linarith)
    linarith
  have step5 : ∀ χ : DirichletCharacter ℂ (q : ℕ),
      √(Iχ χ) ≤ c0 * (√(lam * N) * WA N χ⁻¹ + δ * L2) := by
    intro χ
    have h1 := Real.sqrt_le_sqrt (step4 χ)
    refine h1.trans ?_
    rw [Real.sqrt_mul (by positivity), hc0]
    refine mul_le_mul_of_nonneg_left ?_ hc00
    refine (sqrt_add_le' (by positivity) (by positivity)).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (hWA0 _), Real.sqrt_mul (sq_nonneg _) _,
      Real.sqrt_sq hδ0.le, Real.sqrt_sq hL20]
  -- Step 6: reindex the characters
  have hnormw : ∀ χ : DirichletCharacter ℂ (q : ℕ), ‖w χ‖ ≤ ‖gaussSum χ ZMod.stdAddChar‖ := by
    intro χ
    simp only [hw, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hreidx : (∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA N χ⁻¹) =
      (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) := by
    refine Fintype.sum_equiv (Equiv.inv _) _ _ fun χ => ?_
    simp only [Equiv.inv_apply]
    rw [← norm_gaussSum_inv χ]
  set T : ℝ := ∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun χ _ => norm_nonneg _
  have hTle : T ≤ φq * (q : ℕ) := by
    calc T ≤ ∑ _χ : DirichletCharacter ℂ (q : ℕ), (((q : ℕ) : ℕ) : ℝ) :=
          Finset.sum_le_sum fun χ _ => norm_gaussSum_le χ
      _ = φq * (q : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_chars]
  have hOm0 : 0 ≤ (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) := Finset.sum_nonneg fun χ _ => mul_nonneg (norm_nonneg _) (hWA0 _)
  have step6 : (∑ χ, ‖w χ‖ * √(Iχ χ)) ≤ c0 * (√(lam * N) * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) + δ * L2 * T) := by
    calc (∑ χ, ‖w χ‖ * √(Iχ χ))
        ≤ ∑ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ *
            (c0 * (√(lam * N) * WA N χ⁻¹ + δ * L2)) :=
          Finset.sum_le_sum fun χ _ => mul_le_mul (hnormw χ) (step5 χ) (Real.sqrt_nonneg _)
            (norm_nonneg _)
      _ = c0 * (√(lam * N) * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) + δ * L2 * T) := by
          have e : ∀ χ : DirichletCharacter ℂ (q : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ *
              (c0 * (√(lam * N) * WA N χ⁻¹ + δ * L2)) =
              c0 * √(lam * N) * (‖gaussSum χ ZMod.stdAddChar‖ * WA N χ⁻¹) +
                c0 * (δ * L2) * ‖gaussSum χ ZMod.stdAddChar‖ := fun χ => by ring
          rw [Finset.sum_congr rfl fun χ _ => e χ, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, hreidx, ← hT]
          ring
  -- Step 7: assemble
  have hsq : (∑ χ, ‖w χ‖ * √(Iχ χ)) ^ 2 ≤
      2 * c0 ^ 2 * (lam * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 + δ ^ 2 * L2 ^ 2 * T ^ 2) := by
    have h0 : 0 ≤ ∑ χ, ‖w χ‖ * √(Iχ χ) :=
      Finset.sum_nonneg fun χ _ => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have h1 := pow_le_pow_left₀ h0 step6 2
    refine h1.trans ?_
    have hs : √(lam * N) ^ 2 = lam * N := Real.sq_sqrt (by positivity)
    set X := √(lam * N) * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) with hX
    set Z := δ * L2 * T with hZ
    have hXY : (X + Z) ^ 2 ≤ 2 * (X ^ 2 + Z ^ 2) := by linarith [sq_nonneg (X - Z)]
    have hX2 : X ^ 2 = lam * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 := by rw [hX, mul_pow, hs]
    have hZ2 : Z ^ 2 = δ ^ 2 * L2 ^ 2 * T ^ 2 := by rw [hZ]; ring
    calc (c0 * (X + Z)) ^ 2 = c0 ^ 2 * (X + Z) ^ 2 := by ring
      _ ≤ c0 ^ 2 * (2 * (X ^ 2 + Z ^ 2)) := mul_le_mul_of_nonneg_left hXY (sq_nonneg _)
      _ = _ := by rw [hX2, hZ2]; ring
  have hc0sq : c0 ^ 2 = 2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁ := Real.sq_sqrt (by positivity)
  have hTq : T ^ 2 / φq ^ 2 ≤ ((q : ℕ) : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := pow_le_pow_left₀ hT0 hTle 2
    nlinarith
  have hδQ : δ ^ 2 * ((q : ℕ) : ℝ) ^ 2 = 1 / Q N ^ 2 := by
    rw [hδ]; field_simp
  -- the main part
  have hmainsum : (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2) ≤
      16 * π ^ 2 * C₁ * lam * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 / φq ^ 2 +
        16 * π ^ 2 * C₁ * L2 ^ 2 / Q N ^ 2 + 8 * δ * E ^ 2 := by
    have hs := Finset.sum_le_sum step2
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.mul_sum] at hs
    have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
    have hA : (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) *
        ∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) ≤
        16 * π ^ 2 * C₁ * lam * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 / φq ^ 2 +
          16 * π ^ 2 * C₁ * L2 ^ 2 / Q N ^ 2 := by
      have h1 := step3.trans hsq
      rw [hc0sq] at h1
      have e1 : (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) * (2 * (2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁) *
          (lam * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 + δ ^ 2 * L2 ^ 2 * T ^ 2))) =
          16 * π ^ 2 * C₁ * lam * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 / φq ^ 2 +
            16 * π ^ 2 * C₁ * L2 ^ 2 * (T ^ 2 / φq ^ 2) * δ ^ 2 := by
        field_simp
        ring
      have h2 : (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) *
          ∑ p ∈ P, ∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) ≤
          (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) * (2 * (2 * π ^ 2 * (K0 : ℝ) ^ 2 * C₁) *
            (lam * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 + δ ^ 2 * L2 ^ 2 * T ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [e1] at h2
      refine h2.trans ?_
      have h3 : 16 * π ^ 2 * C₁ * L2 ^ 2 * (T ^ 2 / φq ^ 2) * δ ^ 2 ≤
          16 * π ^ 2 * C₁ * L2 ^ 2 / Q N ^ 2 := by
        have : 0 ≤ 16 * π ^ 2 * C₁ * L2 ^ 2 * δ ^ 2 := by positivity
        calc 16 * π ^ 2 * C₁ * L2 ^ 2 * (T ^ 2 / φq ^ 2) * δ ^ 2
            = 16 * π ^ 2 * C₁ * L2 ^ 2 * δ ^ 2 * (T ^ 2 / φq ^ 2) := by ring
          _ ≤ 16 * π ^ 2 * C₁ * L2 ^ 2 * δ ^ 2 * ((q : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hTq this
          _ = 16 * π ^ 2 * C₁ * L2 ^ 2 * (δ ^ 2 * ((q : ℕ) : ℝ) ^ 2) := by ring
          _ = _ := by rw [hδQ]; ring
      linarith
    have hB : (2 / (K0 : ℝ) ^ 2) * ((K0 : ℝ) ^ 2 * (2 * (2 * δ * E ^ 2))) = 8 * δ * E ^ 2 := by
      field_simp; ring
    calc (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ P, (∫ η in (-δ)..δ, ‖Rx (Finset.Icc p.1 p.2) q r η‖ ^ 2)
        ≤ (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) *
            ∑ p ∈ P, (∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2) +
              (K0 : ℝ) ^ 2 * (2 * (2 * δ * E ^ 2))) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (2 / (K0 : ℝ) ^ 2) * (2 * (1 / φq ^ 2) *
            ∑ p ∈ P, (∫ η in (-δ)..δ, ‖∑ χ, w χ * f χ p η‖ ^ 2)) +
            (2 / (K0 : ℝ) ^ 2) * ((K0 : ℝ) ^ 2 * (2 * (2 * δ * E ^ 2))) := by ring
      _ ≤ _ := by rw [hB]; linarith
  have := step1.trans (add_le_add hmainsum le_rfl)
  linarith


end

section
-- ===== from Burst9Clip.lean =====
attribute [local instance] Classical.propDecidable

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

theorem movingSum_eq (x u : ℝ) :
    movingSum χ x u = ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + u⌋₊, cf χ n := rfl

/-- The moving sum is jointly measurable in the start and the window. PROVED. -/
theorem movingSum_measurable : Measurable (fun p : ℝ × ℝ => movingSum χ p.1 p.2) := by
  have h1 : Measurable (fun p : ℝ × ℝ => (⌈p.1⌉₊, ⌊p.1 + p.2⌋₊)) :=
    (measurable_fst.nat_ceil).prodMk ((measurable_fst.add measurable_snd).nat_floor)
  have h2 : Measurable (fun mn : ℕ × ℕ => ∑ n ∈ Finset.Icc mn.1 mn.2, cf χ n) :=
    measurable_of_countable _
  exact h2.comp h1

theorem norm_cf_le (n : ℕ) : ‖cf χ n‖ ≤ Λ n + 1 := by
  unfold cf
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(Λ n : ℂ) * χ (n : ZMod (q : ℕ))‖ ≤ Λ n := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one _ _)
  have h2 : ‖(if χ = 1 then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
  exact add_le_add h1 h2

theorem norm_cf_le_log {N n : ℕ} (hN : 1 ≤ N) (hn : n ≤ 2 * N) :
    ‖cf χ n‖ ≤ Real.log (2 * N) + 1 := by
  refine (norm_cf_le χ n).trans ?_
  have : Λ n ≤ Real.log (2 * N) := by
    refine vonMangoldt_le_log.trans ?_
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
                                linarith)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hn)
  linarith

/-- A uniform bound for the moving sums with `x + u ≤ R`. PROVED. -/
theorem norm_movingSum_le (R : ℝ) {x u : ℝ} (h : x + u ≤ R) :
    ‖movingSum χ x u‖ ≤ ∑ n ∈ Finset.range (⌊R⌋₊ + 1), ‖cf χ n‖ := by
  rw [movingSum_eq]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => norm_nonneg _)
  intro n hn
  have := (Finset.mem_Icc.mp hn).2
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (this.trans (Nat.floor_le_floor h)))

/-- The left end: for `x ∈ (a - 1, a]` the moving sum at `x` with window `u' + (a - x)` is the
moving sum at `a` with window `u'`. PROVED. -/
theorem movingSum_shift_left {a : ℕ} (ha : 1 ≤ a) {x : ℝ} (hx1 : (a : ℝ) - 1 < x)
    (hx2 : x ≤ a) (u' : ℝ) : movingSum χ x (u' + (a - x)) = movingSum χ a u' := by
  rw [movingSum_eq, movingSum_eq, Nat.ceil_natCast]
  have hc : ⌈x⌉₊ = a := by
    rw [Nat.ceil_eq_iff (by omega)]
    constructor
    · push_cast [Nat.cast_sub ha]; linarith
    · exact hx2
  rw [hc, show x + (u' + (a - x)) = (a : ℝ) + u' by ring]

/-- The top unit of windows: `S(a, u) = S(a, u - 1) + c(a + ⌊u⌋)` for `u ≥ 1`. PROVED. -/
theorem movingSum_top (a : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    movingSum χ a u = movingSum χ a (u - 1) + cf χ (a + ⌊u⌋₊) := by
  rw [movingSum_eq, movingSum_eq, Nat.ceil_natCast]
  have h0 : (0 : ℝ) ≤ u := by linarith
  have e1 : ⌊(a : ℝ) + u⌋₊ = a + ⌊u⌋₊ := by
    rw [add_comm, Nat.floor_add_natCast h0, add_comm]
  have e2 : ⌊(a : ℝ) + (u - 1)⌋₊ = a + ⌊u⌋₊ - 1 := by
    rw [show (a : ℝ) + (u - 1) = ((a : ℝ) + u) - 1 by ring, Nat.floor_sub_one, e1]
  have hu1 : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by exact_mod_cast hu)
  rw [e1, e2]
  obtain ⟨m, hm⟩ : ∃ m, ⌊u⌋₊ = m + 1 := ⟨⌊u⌋₊ - 1, by omega⟩
  rw [hm, show a + (m + 1) - 1 = a + m by omega, show a + (m + 1) = (a + m) + 1 by ring,
    Finset.sum_Icc_succ_top (by omega)]

/-- The right end: the moving sum at `x` with window `u` only depends on `⌊x + u⌋`. PROVED. -/
theorem movingSum_right_const {b : ℕ} {x u : ℝ} (h1 : (b : ℝ) ≤ x + u) (h2 : x + u < b + 1) :
    movingSum χ x u = movingSum χ x (b - x) := by
  rw [movingSum_eq, movingSum_eq, show x + (b - x) = (b : ℝ) by ring, Nat.floor_natCast]
  have hb : ⌊x + u⌋₊ = b := by
    rw [Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)])]
    exact ⟨h1, h2⟩
  rw [hb]

/-- The right end, one term split off: for `0 ≤ x < b`,
`S(x, b - x) = c(⌈x⌉) + S(x + 1, b - (x + 1))`. PROVED. -/
theorem movingSum_right_split {b : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hxb : x < b) :
    movingSum χ x (b - x) = cf χ ⌈x⌉₊ + movingSum χ (x + 1) (b - (x + 1)) := by
  rw [movingSum_eq, movingSum_eq, show x + (b - x) = (b : ℝ) by ring,
    show x + 1 + (b - (x + 1)) = (b : ℝ) by ring, Nat.floor_natCast, Nat.ceil_add_one hx0]
  have hcb : ⌈x⌉₊ ≤ b := Nat.ceil_le.mpr hxb.le
  have e : insert ⌈x⌉₊ (Finset.Icc (⌈x⌉₊ + 1) b) = Finset.Icc ⌈x⌉₊ b := by
    ext n; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  rw [← e, Finset.sum_insert (by simp)]

/-! ### Gallagher's clipped window sum -/

open Classical in
theorem cwinSum_eq_filter (T : Finset ℕ) (c : ℕ → ℂ) (h x : ℝ) :
    Burst9G.cwinSum T c h x = ∑ n ∈ T.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), c n := by
  unfold Burst9G.cwinSum Burst9G.win
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : x ∈ Ico ((n : ℝ) - h) n
  · rw [indicator_of_mem hx, if_pos ⟨hx.2, by linarith [hx.1]⟩]
  · rw [indicator_of_notMem hx, if_neg]
    rintro ⟨h1, h2⟩
    exact hx ⟨by linarith, h1⟩

/-- Left end: for `a - h ≤ x < a` and `a + h ≤ b` the clipped sum is the moving sum from `a`.
PROVED. -/
theorem clip_eq_left {a b : ℕ} {h x : ℝ} (hab : (a : ℝ) + h ≤ b) (hx1 : (a : ℝ) - h ≤ x)
    (hx2 : x < a) :
    Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x = movingSum χ a (x + h - a) := by
  rw [cwinSum_eq_filter, movingSum_eq, Nat.ceil_natCast,
    show (a : ℝ) + (x + h - a) = x + h by ring]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  have hxh : 0 ≤ x + h := by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_floor_iff hxh]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    have h1' : (a : ℝ) ≤ n := by exact_mod_cast h1
    refine ⟨⟨h1, ?_⟩, by linarith, h3⟩
    have : (n : ℝ) ≤ b := by linarith
    exact_mod_cast this

/-- Middle: for `a ≤ x ≤ b - h`, `x` not an integer, the clipped sum is the moving sum.
PROVED. -/
theorem clip_eq_mid {a b : ℕ} {h x : ℝ} (hh : 0 ≤ h) (hx1 : (a : ℝ) ≤ x) (hx2 : x + h ≤ b)
    (hxn : ∀ n : ℕ, x ≠ n) :
    Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x = movingSum χ x h := by
  rw [cwinSum_eq_filter, movingSum_eq]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg a) hx1
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.le_floor_iff (by linarith : 0 ≤ x + h),
    Nat.ceil_le]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2.le, h3⟩
  · rintro ⟨h2, h3⟩
    have h2' : x < n := lt_of_le_of_ne h2 (hxn n)
    refine ⟨⟨?_, ?_⟩, h2', h3⟩
    · have : (a : ℝ) < n := by linarith
      exact_mod_cast this.le
    · have : (n : ℝ) ≤ b := by linarith
      exact_mod_cast this

/-- Right end: for `b - h < x < b`, `a ≤ x`, `x` not an integer, the clipped sum is the moving
sum ending at `b`. PROVED. -/
theorem clip_eq_right {a b : ℕ} {h x : ℝ} (hx1 : (b : ℝ) - h < x) (hx2 : x < b)
    (hxa : (a : ℝ) ≤ x) (hxn : ∀ n : ℕ, x ≠ n) :
    Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x = movingSum χ x (b - x) := by
  rw [cwinSum_eq_filter, movingSum_eq, show x + (b - x) = (b : ℝ) by ring, Nat.floor_natCast]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le]
  constructor
  · rintro ⟨⟨-, h2⟩, h3, -⟩; exact ⟨h3.le, h2⟩
  · rintro ⟨h3, h2⟩
    have h3' : x < n := lt_of_le_of_ne h3 (hxn n)
    have h2' : (n : ℝ) ≤ b := by exact_mod_cast h2
    refine ⟨⟨?_, h2⟩, h3', by linarith⟩
    have : (a : ℝ) < n := by linarith
    exact_mod_cast this.le

/-- Outside `[a - h, b)` the clipped sum vanishes. PROVED. -/
theorem clip_eq_zero {a b : ℕ} {h x : ℝ} (hx : x < (a : ℝ) - h ∨ (b : ℝ) ≤ x) :
    Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x = 0 := by
  rw [cwinSum_eq_filter]
  refine Finset.sum_eq_zero fun n hn => ?_
  exfalso
  obtain ⟨hn1, hn2, hn3⟩ := of_mem_filter hn
  have h1 : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn1).1
  have h2 : (n : ℝ) ≤ b := by exact_mod_cast (Finset.mem_Icc.mp hn1).2
  rcases hx with hx | hx <;> linarith


end

section
-- ===== from Burst9Clip2.lean =====

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))


theorem Fm_nonneg (x u : ℝ) : 0 ≤ (‖movingSum χ x u‖ ^ 2) := sq_nonneg _

theorem Fm_measurable : Measurable (fun p : ℝ × ℝ => (‖movingSum χ p.1 p.2‖ ^ 2)) :=
  (movingSum_measurable χ).norm.pow_const 2


theorem Fm_le {R x u : ℝ} (h : x + u ≤ R) : (‖movingSum χ x u‖ ^ 2) ≤ (∑ n ∈ Finset.range (⌊(R : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (norm_movingSum_le χ R h) 2

theorem intOn_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) (hfin : μ s ≠ ⊤) (M : ℝ)
    (hb : ∀ x ∈ s, |f x| ≤ M) : IntegrableOn f s μ :=
  Measure.integrableOn_of_bounded hfin hf.aestronglyMeasurable
    ((ae_restrict_iff' hs).mpr (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]; exact hb x hx))

/-- Integrability on a product box with `x + u ≤ R`. PROVED. -/
theorem Fm_int_prod {J I : Set ℝ} (hJ : MeasurableSet J) (hI : MeasurableSet I)
    (hJf : volume J ≠ ⊤) (hIf : volume I ≠ ⊤) {R : ℝ}
    (hR : ∀ x ∈ J, ∀ u ∈ I, x + u ≤ R) :
    Integrable (fun p : ℝ × ℝ => (‖movingSum χ p.1 p.2‖ ^ 2)) ((volume.restrict J).prod (volume.restrict I)) := by
  rw [Measure.prod_restrict]
  refine intOn_bdd (Fm_measurable χ) (hJ.prod hI) ?_ ((∑ n ∈ Finset.range (⌊(R : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2) ?_
  · rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hJf hIf
  · rintro ⟨x, u⟩ ⟨hx, hu⟩
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le χ (hR x hx u hu)

theorem Fm_int_x {J : Set ℝ} (hJ : MeasurableSet J) (hJf : volume J ≠ ⊤) {u R : ℝ}
    (hR : ∀ x ∈ J, x + u ≤ R) : IntegrableOn (fun x => (‖movingSum χ x u‖ ^ 2)) J := by
  refine intOn_bdd ((Fm_measurable χ).comp (measurable_id.prodMk measurable_const)) hJ hJf
    ((∑ n ∈ Finset.range (⌊(R : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2) fun x hx => ?_
  show |(‖movingSum χ x u‖ ^ 2)| ≤ _
  rw [abs_of_nonneg (Fm_nonneg χ _ _)]
  exact Fm_le χ (hR x hx)

theorem Fm_int_u {I : Set ℝ} (hI : MeasurableSet I) (hIf : volume I ≠ ⊤) {x R : ℝ}
    (hR : ∀ u ∈ I, x + u ≤ R) : IntegrableOn (fun u => (‖movingSum χ x u‖ ^ 2)) I := by
  refine intOn_bdd ((Fm_measurable χ).comp (measurable_const.prodMk measurable_id)) hI hIf
    ((∑ n ∈ Finset.range (⌊(R : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2) fun u hu => ?_
  show |(‖movingSum χ x u‖ ^ 2)| ≤ _
  rw [abs_of_nonneg (Fm_nonneg χ _ _)]
  exact Fm_le χ (hR u hu)

theorem windowMean_eq (N : ℕ) (u : ℝ) :
    windowMean N χ u = ∫ x in Ioc ((N : ℝ) / 2) (3 * N), (‖movingSum χ x u‖ ^ 2) := rfl

/-- **The exchange of the integrals**: for `J ⊆ (N/2, 3N]` and `0 ≤ h ≤ N`,
`∫_J ∫_0^h |S(x, u)|² du dx ≤ ∫_0^h W(u) du`, `W = windowMean`. PROVED. -/
theorem swap_le (N : ℕ) {J : Set ℝ} (hJ : MeasurableSet J) (hJU : J ⊆ Ioc ((N : ℝ) / 2) (3 * N))
    {h : ℝ} (hhN : h ≤ N) :
    ∫ x in J, (∫ u in Ioc 0 h, (‖movingSum χ x u‖ ^ 2)) ≤ ∫ u in Ioc 0 h, windowMean N χ u := by
  have hUf : volume (Ioc ((N : ℝ) / 2) (3 * N)) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hJf : volume J ≠ ⊤ := ((measure_mono hJU).trans_lt measure_Ioc_lt_top).ne
  have hIf : volume (Ioc (0 : ℝ) h) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hR : ∀ x ∈ Ioc ((N : ℝ) / 2) (3 * N), ∀ u ∈ Ioc (0 : ℝ) h, x + u ≤ 4 * N :=
    fun x hx u hu => by linarith [hx.2, hu.2]
  have hRJ : ∀ x ∈ J, ∀ u ∈ Ioc (0 : ℝ) h, x + u ≤ 4 * N := fun x hx => hR x (hJU hx)
  have iJ := Fm_int_prod χ hJ measurableSet_Ioc hJf hIf hRJ
  have iU := Fm_int_prod χ measurableSet_Ioc measurableSet_Ioc hUf hIf hR
  rw [integral_integral_swap (f := fun x u => (‖movingSum χ x u‖ ^ 2)) iJ]
  simp_rw [windowMean_eq]
  refine integral_mono_ae iJ.integral_prod_right iU.integral_prod_right ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu => ?_)
  dsimp only
  exact setIntegral_mono_set
    (Fm_int_x χ measurableSet_Ioc hUf (R := 4 * N) fun x hx => by linarith [hx.2, hu.2])
    (Eventually.of_forall fun x => Fm_nonneg χ x u) (Eventually.of_forall hJU)


end

section
-- ===== from Burst9Clip3.lean =====

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

theorem Fm_iInt (x : ℝ) {lo hi R : ℝ} (hlh : lo ≤ hi) (hR : x + hi ≤ R) :
    IntervalIntegrable (fun u => (‖movingSum χ x u‖ ^ 2)) volume lo hi := by
  refine IntegrableOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hlh]
  exact Fm_int_u χ measurableSet_Icc measure_Icc_lt_top.ne (R := R)
    fun u hu => by linarith [hu.2]

theorem Fm_comp_measurable (g : ℝ → ℝ) (hg : Measurable g) :
    Measurable (fun x : ℝ => (‖movingSum χ x (g x)‖ ^ 2)) := by
  have h1 : Measurable (fun x : ℝ => (x, g x)) := measurable_id'.prodMk hg
  have h2 := (Fm_measurable χ).comp h1
  exact h2


theorem Phi_nonneg (h x : ℝ) : 0 ≤ (∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2) :=
  setIntegral_nonneg measurableSet_Ioc fun u _ => Fm_nonneg χ x u

theorem Phi_intOn {J : Set ℝ} (hJ : MeasurableSet J) (hJf : volume J ≠ ⊤) {h R : ℝ}
    (hR : ∀ x ∈ J, x + h ≤ R) : IntegrableOn ((fun x => ∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2)) J :=
  (Fm_int_prod χ hJ measurableSet_Ioc hJf measure_Ioc_lt_top.ne (R := R)
    fun x hx u hu => by linarith [hR x hx, hu.2]).integral_prod_left

/-- **One left end**: `∫_0^h |S(a, u)|² du ≤ 3 ∫_{a-1}^{a} Φ(x) dx + 2 (log 2N + 1)²`. PROVED. -/
theorem left_end_one {N : ℕ} (hN : 1 ≤ N) {a : ℕ} (ha : 1 ≤ a) {h : ℝ} (h2 : 2 ≤ h)
    (hah : (a : ℝ) + h ≤ 2 * N) :
    (∫ u in (0 : ℝ)..h, (‖movingSum χ a u‖ ^ 2)) ≤
      3 * (∫ x in Ioo ((a : ℝ) - 1) a, (∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2)) + 2 * (Real.log (2 * N) + 1) ^ 2 := by
  set β := Real.log (2 * N) + 1 with hβ
  have iA : ∀ lo hi : ℝ, lo ≤ hi → hi ≤ h → IntervalIntegrable (fun u => (‖movingSum χ a u‖ ^ 2)) volume lo hi :=
    fun lo hi hlh hh => Fm_iInt χ a hlh (R := 2 * N) (by linarith)
  -- the top unit of windows
  have hstep : (∫ u in (h - 1)..h, (‖movingSum χ a u‖ ^ 2)) ≤ 2 * (∫ u in (h - 2)..(h - 1), (‖movingSum χ a u‖ ^ 2)) + 2 * β ^ 2 := by
    have hpt : ∀ u ∈ Icc (h - 1) h, (‖movingSum χ a u‖ ^ 2) ≤ 2 * (‖movingSum χ a (u - 1)‖ ^ 2) + 2 * β ^ 2 := by
      intro u hu
      have hu1 : 1 ≤ u := by linarith [hu.1]
      have hc : ‖cf χ (a + ⌊u⌋₊)‖ ≤ β := by
        refine norm_cf_le_log χ hN ?_
        have : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
        have : ((a + ⌊u⌋₊ : ℕ) : ℝ) ≤ 2 * N := by push_cast; linarith [hu.2]
        exact_mod_cast this
      rw [movingSum_top χ a hu1]
      refine (norm_add_sq_le _ _).trans ?_
      have := pow_le_pow_left₀ (norm_nonneg _) hc 2
      linarith
    have i1 : IntervalIntegrable (fun u => 2 * (‖movingSum χ a (u - 1)‖ ^ 2) + 2 * β ^ 2) volume (h - 1) h := by
      refine ((Fm_iInt χ a (lo := h - 2) (hi := h - 1) (by linarith) (R := 2 * N) (by linarith)
        ).comp_sub_right 1).const_mul 2 |>.add intervalIntegrable_const |>.mono_set ?_
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
      intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    calc (∫ u in (h - 1)..h, (‖movingSum χ a u‖ ^ 2))
        ≤ ∫ u in (h - 1)..h, (2 * (‖movingSum χ a (u - 1)‖ ^ 2) + 2 * β ^ 2) :=
          intervalIntegral.integral_mono_on (by linarith) (iA _ _ (by linarith) le_rfl) i1 hpt
      _ = 2 * (∫ u in (h - 2)..(h - 1), (‖movingSum χ a u‖ ^ 2)) + 2 * β ^ 2 := by
          rw [intervalIntegral.integral_add ?_ intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
              (fun u => (‖movingSum χ a u‖ ^ 2)) 1, intervalIntegral.integral_const]
          · simp only [smul_eq_mul]
            rw [show h - 1 - 1 = h - 2 by ring, show h - 1 = h - 1 by ring]; ring
          · exact (((Fm_iInt χ a (lo := h - 2) (hi := h - 1) (by linarith) (R := 2 * N)
              (by linarith)).comp_sub_right 1).const_mul 2).mono_set (by
              rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
              intro u hu; exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hmono : (∫ u in (h - 2)..(h - 1), (‖movingSum χ a u‖ ^ 2)) ≤ ∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ a u‖ ^ 2) :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
      (Eventually.of_forall fun u => Fm_nonneg χ a u) (iA _ _ (by linarith) (by linarith))
  -- the shift to the start points `x ∈ (a - 1, a)`
  have key : ∀ x ∈ Ioo ((a : ℝ) - 1) a,
      (∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ a u‖ ^ 2)) ≤ (∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2) := by
    intro x hx
    have e1 : (∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ a u‖ ^ 2)) =
        ∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ x (u + (a - x))‖ ^ 2) := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      simp only [ movingSum_shift_left χ ha hx.1 hx.2.le]
    rw [e1, intervalIntegral.integral_comp_add_right (fun u => (‖movingSum χ x u‖ ^ 2)) (a - x), 
      ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.integral_mono_interval (by linarith [hx.2]) (by linarith)
      (by linarith [hx.1]) (Eventually.of_forall fun u => Fm_nonneg χ x u)
      (Fm_iInt χ x (by linarith) (R := 2 * N) (by linarith [hx.2]))
  have hvol : volume (Ioo ((a : ℝ) - 1) a) = 1 := by
    rw [Real.volume_Ioo]; norm_num
  have hD : (∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ a u‖ ^ 2)) ≤ ∫ x in Ioo ((a : ℝ) - 1) a, (∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2) := by
    have hc : (∫ x in Ioo ((a : ℝ) - 1) a, (∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ a u‖ ^ 2))) =
        ∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ a u‖ ^ 2) := by
      rw [setIntegral_const, measureReal_def, hvol, ENNReal.toReal_one, one_smul]
    rw [← hc]
    refine setIntegral_mono_on (integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top))
      (Phi_intOn χ measurableSet_Ioo (by rw [hvol]; exact ENNReal.one_ne_top) (R := 2 * N)
        fun x hx => by linarith [hx.2]) measurableSet_Ioo key
  have hsplit : (∫ u in (0 : ℝ)..h, (‖movingSum χ a u‖ ^ 2)) =
      (∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ a u‖ ^ 2)) + ∫ u in (h - 1)..h, (‖movingSum χ a u‖ ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals (iA _ _ (by linarith) (by linarith))
      (iA _ _ (by linarith) le_rfl)).symm
  rw [hsplit]
  set I0 := ∫ u in (0 : ℝ)..(h - 1), (‖movingSum χ a u‖ ^ 2) with hI0
  set I1 := ∫ u in (h - 1)..h, (‖movingSum χ a u‖ ^ 2) with hI1
  set I2 := ∫ u in (h - 2)..(h - 1), (‖movingSum χ a u‖ ^ 2) with hI2
  set P := ∫ x in Ioo ((a : ℝ) - 1) a, (∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2) with hP
  clear_value I0 I1 I2 P β
  linarith


theorem card_Aset (N K0 : ℕ) : ((Finset.Ico N (N + K0))).card = K0 := by
  rw [Nat.card_Ico]; omega

theorem card_Bset (N K0 : ℕ) (hK : K0 ≤ 2 * N) : ((Finset.Ioc (2 * N - K0) (2 * N))).card = K0 := by
  rw [Nat.card_Ioc]; omega

/-- **The left end block**: `Σ_a ∫_0^h |S(a, u)|² du ≤ 3 ∫_0^h W(u) du + 2 K₀ (log 2N + 1)²`.
PROVED. -/
theorem left_end_sum {N K0 : ℕ} (hN : 64 ≤ N) (hK1 : 1 ≤ K0) (hK4 : 4 * K0 ≤ N) {h : ℝ}
    (h2 : 2 ≤ h) (h8 : 8 * h ≤ N) :
    (∑ a ∈ (Finset.Ico N (N + K0)), ∫ u in (0 : ℝ)..h, (‖movingSum χ a u‖ ^ 2)) ≤
      3 * (∫ u in Ioc 0 h, windowMean N χ u) + 2 * K0 * (Real.log (2 * N) + 1) ^ 2 := by
  set β := Real.log (2 * N) + 1 with hβ
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hK4r : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
  have hone : ∀ a ∈ (Finset.Ico N (N + K0)), (∫ u in (0 : ℝ)..h, (‖movingSum χ a u‖ ^ 2)) ≤
      3 * (∫ x in Ioo ((a : ℝ) - 1) a, (∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2)) + 2 * β ^ 2 := by
    intro a ha
    have ha' := Finset.mem_Ico.mp ha
    have hlt : a + 1 ≤ N + K0 := ha'.2
    have har : (a : ℝ) + 1 ≤ N + K0 := by exact_mod_cast hlt
    exact left_end_one χ (by omega) (by omega) h2 (by linarith)
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_Aset, nsmul_eq_mul]
  have hdisj : Set.Pairwise (↑((Finset.Ico N (N + K0))) : Set ℕ)
      (Function.onFun Disjoint fun a : ℕ => Ioo ((a : ℝ) - 1) a) := by
    intro a _ b _ hab
    refine Set.disjoint_left.mpr fun x hxa hxb => hab ?_
    have h1 : (a : ℝ) < b + 1 := by linarith [hxa.1, hxb.2]
    have h2 : (b : ℝ) < a + 1 := by linarith [hxb.1, hxa.2]
    have h1' : a < b + 1 := by exact_mod_cast h1
    have h2' : b < a + 1 := by exact_mod_cast h2
    omega
  have hsub : (⋃ a ∈ (Finset.Ico N (N + K0)), Ioo ((a : ℝ) - 1) a) ⊆ Ioo ((N : ℝ) - 1) (N + K0) := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    have ha' := Finset.mem_Ico.mp ha
    have h1 : (N : ℝ) ≤ a := by exact_mod_cast ha'.1
    have h2 : (a : ℝ) + 1 ≤ N + K0 := by exact_mod_cast ha'.2
    exact ⟨by linarith [hxa.1], by linarith [hxa.2]⟩
  have hJU : Ioo ((N : ℝ) - 1) (N + K0) ⊆ Ioc ((N : ℝ) / 2) (3 * N) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hPhiJ : IntegrableOn ((fun x => ∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2)) (Ioo ((N : ℝ) - 1) (N + K0)) :=
    Phi_intOn χ measurableSet_Ioo measure_Ioo_lt_top.ne (R := 4 * N)
      fun x hx => by linarith [hx.2]
  have hsum : (∑ a ∈ (Finset.Ico N (N + K0)), ∫ x in Ioo ((a : ℝ) - 1) a, (∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2)) ≤
      ∫ u in Ioc 0 h, windowMean N χ u := by
    rw [← integral_biUnion_finset _ (fun a _ => measurableSet_Ioo) hdisj
      (fun a _ => hPhiJ.mono_set (fun x hx => hsub (by
        simp only [mem_iUnion]; exact ⟨a, by assumption, hx⟩)))]
    refine (setIntegral_mono_set hPhiJ (Eventually.of_forall fun x => Phi_nonneg χ h x)
      (Eventually.of_forall hsub)).trans ?_
    exact swap_le χ N measurableSet_Ioo hJU (by linarith)
  have hβ0 : 0 ≤ β ^ 2 := sq_nonneg _
  nlinarith

/-- **One right end**: `∫_{b-h}^{b} |S(x, b - x)|² dx ≤ 3 ∫_{b-h+1}^{b} |S(x, b - x)|² dx +
2 (log 2N + 1)²`. PROVED. -/
theorem right_end_one {N : ℕ} (hN : 1 ≤ N) {b : ℕ} (hb2 : b ≤ 2 * N) {h : ℝ} (h2 : 2 ≤ h)
    (hbh : h ≤ b) :
    (∫ x in ((b : ℝ) - h)..b, (‖movingSum χ x (b - x)‖ ^ 2)) ≤
      3 * (∫ x in ((b : ℝ) - h + 1)..b, (‖movingSum χ x (b - x)‖ ^ 2)) + 2 * (Real.log (2 * N) + 1) ^ 2 := by
  set β := Real.log (2 * N) + 1 with hβ
  have hGm' : Measurable (fun x : ℝ => (‖movingSum χ x ((b : ℝ) - x)‖ ^ 2)) :=
    Fm_comp_measurable χ (fun x : ℝ => (b : ℝ) - x) (by fun_prop)
  set G : ℝ → ℝ := fun x => (‖movingSum χ x (b - x)‖ ^ 2) with hG
  have hGm : Measurable G := hGm'
  have hGi : ∀ lo hi : ℝ, lo ≤ hi → IntervalIntegrable G volume lo hi := by
    intro lo hi hlh
    refine IntegrableOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hlh]
    refine intOn_bdd hGm measurableSet_Icc measure_Icc_lt_top.ne ((∑ n ∈ Finset.range (⌊(b : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2) fun x _ => ?_
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le (R := b) (x := x) (u := (b : ℝ) - x) χ (by linarith)
  have hpt : ∀ x ∈ Icc ((b : ℝ) - h) (b - h + 1), G x ≤ 2 * β ^ 2 + 2 * G (x + 1) := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hxb : x < b := by linarith [hx.2]
    have hc : ‖cf χ ⌈x⌉₊‖ ≤ β := by
      refine norm_cf_le_log χ hN ((Nat.ceil_le.mpr hxb.le).trans hb2)
    simp only [hG,]
    rw [movingSum_right_split χ hx0 hxb]
    refine (norm_add_sq_le _ _).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hc 2
    linarith
  have hshift : (∫ x in ((b : ℝ) - h)..(b - h + 1), G (x + 1)) =
      ∫ x in ((b : ℝ) - h + 1)..(b - h + 2), G x := by
    rw [intervalIntegral.integral_comp_add_right G 1]
    congr 1 <;> ring
  have h1 : (∫ x in ((b : ℝ) - h)..(b - h + 1), G x) ≤
      2 * β ^ 2 + 2 * ∫ x in ((b : ℝ) - h + 1)..(b - h + 2), G x := by
    have i3 : IntervalIntegrable (fun x => 2 * G (x + 1)) volume ((b : ℝ) - h) (b - h + 1) := by
      refine IntervalIntegrable.const_mul ?_ 2
      refine IntegrableOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (by linarith)]
      have hm1 : Measurable (fun x : ℝ => x + 1) := by fun_prop
      refine intOn_bdd (hGm.comp hm1) measurableSet_Icc
        measure_Icc_lt_top.ne ((∑ n ∈ Finset.range (⌊(b : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2) fun x _ => ?_
      show |(‖movingSum χ (x + 1) (b - (x + 1))‖ ^ 2)| ≤ _
      rw [abs_of_nonneg (Fm_nonneg χ _ _)]
      exact Fm_le (R := b) (x := x + 1) (u := (b : ℝ) - (x + 1)) χ (by linarith)
    have i2 : IntervalIntegrable (fun x => 2 * β ^ 2 + 2 * G (x + 1)) volume ((b : ℝ) - h)
        (b - h + 1) := intervalIntegrable_const.add i3
    calc (∫ x in ((b : ℝ) - h)..(b - h + 1), G x)
        ≤ ∫ x in ((b : ℝ) - h)..(b - h + 1), (2 * β ^ 2 + 2 * G (x + 1)) :=
          intervalIntegral.integral_mono_on (by linarith) (hGi _ _ (by linarith)) i2 hpt
      _ = 2 * β ^ 2 + 2 * ∫ x in ((b : ℝ) - h + 1)..(b - h + 2), G x := by
          rw [intervalIntegral.integral_add intervalIntegrable_const i3,
            intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul, hshift]
          simp only [smul_eq_mul]; ring
  have h3 : (∫ x in ((b : ℝ) - h + 1)..(b - h + 2), G x) ≤ ∫ x in ((b : ℝ) - h + 1)..b, G x :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Eventually.of_forall fun x => Fm_nonneg χ _ _) (hGi _ _ (by linarith))
  have hsplit : (∫ x in ((b : ℝ) - h)..b, G x) =
      (∫ x in ((b : ℝ) - h)..(b - h + 1), G x) + ∫ x in ((b : ℝ) - h + 1)..b, G x :=
    (intervalIntegral.integral_add_adjacent_intervals (hGi _ _ (by linarith))
      (hGi _ _ (by linarith))).symm
  show (∫ x in ((b : ℝ) - h)..b, G x) ≤ 3 * (∫ x in ((b : ℝ) - h + 1)..b, G x) + 2 * β ^ 2
  rw [hsplit]
  linarith


end

section
-- ===== from Burst9Clip4.lean =====

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

/-- The window integral over the unit window `b ≤ x + u < b + 1` is `|S(x, b - x)|²`. PROVED. -/
theorem Fm_unit_window (x : ℝ) (b : ℕ) :
    (∫ u in Ico ((b : ℝ) - x) (b - x + 1), (‖movingSum χ x u‖ ^ 2)) = (‖movingSum χ x (b - x)‖ ^ 2) := by
  have hc : ∀ u ∈ Ico ((b : ℝ) - x) (b - x + 1), (‖movingSum χ x u‖ ^ 2) = (‖movingSum χ x (b - x)‖ ^ 2) := by
    intro u hu
    skip
    rw [movingSum_right_const χ (b := b) (by linarith [hu.1]) (by linarith [hu.2])]
  rw [setIntegral_congr_fun measurableSet_Ico hc, setIntegral_const, measureReal_def,
    Real.volume_Ico, show (b : ℝ) - x + 1 - (b - x) = 1 by ring, ENNReal.ofReal_one,
    ENNReal.toReal_one, one_smul]

/-- The pointwise bound behind the right end block. PROVED. -/
theorem right_pointwise {N K0 : ℕ} {h : ℝ} (hJ : ∀ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)),
      Ioo ((b : ℝ) - h + 1) b ⊆ Ioo (N : ℝ) (2 * N)) (hN : (0 : ℝ) ≤ N) (hhN : h ≤ N) (x : ℝ) :
    ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), (Ioo ((b : ℝ) - h + 1) b).indicator (fun x => (‖movingSum χ x (b - x)‖ ^ 2)) x ≤
      (Ioo (N : ℝ) (2 * N)).indicator ((fun x => ∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2)) x := by
  classical
  by_cases hx : x ∈ Ioo (N : ℝ) (2 * N)
  · rw [indicator_of_mem hx]
    set B' := ((Finset.Ioc (2 * N - K0) (2 * N))).filter (fun b : ℕ => x ∈ Ioo ((b : ℝ) - h + 1) b) with hB'
    have e1 : ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), (Ioo ((b : ℝ) - h + 1) b).indicator (fun x => (‖movingSum χ x (b - x)‖ ^ 2)) x =
        ∑ b ∈ B', ∫ u in Ico ((b : ℝ) - x) (b - x + 1), (‖movingSum χ x u‖ ^ 2) := by
      rw [hB', Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : x ∈ Ioo ((b : ℝ) - h + 1) b
      · rw [indicator_of_mem hb, if_pos hb, Fm_unit_window]
      · rw [indicator_of_notMem hb, if_neg hb]
    rw [e1]
    have hdisj : Set.Pairwise (↑B' : Set ℕ)
        (Function.onFun Disjoint fun b : ℕ => Ico ((b : ℝ) - x) (b - x + 1)) := by
      intro b _ b' _ hbb
      refine Set.disjoint_left.mpr fun u hu hu' => hbb ?_
      have h1 : (b : ℝ) < b' + 1 := by linarith [hu.1, hu'.2]
      have h2 : (b' : ℝ) < b + 1 := by linarith [hu'.1, hu.2]
      have h1' : b < b' + 1 := by exact_mod_cast h1
      have h2' : b' < b + 1 := by exact_mod_cast h2
      omega
    have hsub : (⋃ b ∈ B', Ico ((b : ℝ) - x) (b - x + 1)) ⊆ Ioc 0 h := by
      intro u hu
      simp only [mem_iUnion] at hu
      obtain ⟨b, hb, hub⟩ := hu
      have hxb := (Finset.mem_filter.mp hb).2
      exact ⟨by linarith [hub.1, hxb.2], by linarith [hub.2, hxb.1]⟩
    have hint : IntegrableOn (fun u => (‖movingSum χ x u‖ ^ 2)) (Ioc 0 h) :=
      Fm_int_u χ measurableSet_Ioc measure_Ioc_lt_top.ne (R := 4 * N)
        fun u hu => by linarith [hx.2, hu.2]
    rw [← integral_biUnion_finset _ (fun b _ => measurableSet_Ico) hdisj
      (fun b hb => hint.mono_set (fun u hu => hsub (by
        simp only [mem_iUnion]; exact ⟨b, hb, hu⟩)))]
    exact setIntegral_mono_set hint (Eventually.of_forall fun u => Fm_nonneg χ x u)
      (Eventually.of_forall hsub)
  · rw [indicator_of_notMem hx]
    refine le_of_eq (Finset.sum_eq_zero fun b hb => ?_)
    exact indicator_of_notMem (fun h' => hx (hJ b hb h')) _

/-- **The right end block**: `Σ_b ∫_{b-h}^{b} |S(x, b - x)|² dx ≤ 3 ∫_0^h W(u) du +
2 K₀ (log 2N + 1)²`. PROVED. -/
theorem right_end_sum {N K0 : ℕ} (hN : 64 ≤ N) (hK4 : 4 * K0 ≤ N) {h : ℝ}
    (h2 : 2 ≤ h) (h8 : 8 * h ≤ N) :
    (∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), ∫ x in ((b : ℝ) - h)..b, (‖movingSum χ x (b - x)‖ ^ 2)) ≤
      3 * (∫ u in Ioc 0 h, windowMean N χ u) + 2 * K0 * (Real.log (2 * N) + 1) ^ 2 := by
  set β := Real.log (2 * N) + 1 with hβ
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hK4r : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
  have hbB : ∀ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), b ≤ 2 * N ∧ (2 * N : ℝ) - K0 < b := by
    intro b hb
    have hb' := Finset.mem_Ioc.mp hb
    refine ⟨hb'.2, ?_⟩
    have : 2 * N - K0 < b := hb'.1
    have h3 : ((2 * N - K0 : ℕ) : ℝ) < b := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h3
    push_cast at h3
    linarith
  have hone : ∀ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), (∫ x in ((b : ℝ) - h)..b, (‖movingSum χ x (b - x)‖ ^ 2)) ≤
      3 * (∫ x in ((b : ℝ) - h + 1)..b, (‖movingSum χ x (b - x)‖ ^ 2)) + 2 * β ^ 2 := by
    intro b hb
    obtain ⟨hb2, hb1⟩ := hbB b hb
    exact right_end_one χ (by omega) hb2 h2 (by linarith)
  refine (Finset.sum_le_sum hone).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_Bset N K0 (by omega),
    nsmul_eq_mul]
  have hJ : ∀ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), Ioo ((b : ℝ) - h + 1) b ⊆ Ioo (N : ℝ) (2 * N) := by
    intro b hb x hx
    obtain ⟨hb2, hb1⟩ := hbB b hb
    have hb2' : (b : ℝ) ≤ 2 * N := by exact_mod_cast hb2
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hGint : ∀ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), Integrable ((Ioo ((b : ℝ) - h + 1) b).indicator
      (fun x => (‖movingSum χ x (b - x)‖ ^ 2))) := by
    intro b hb
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioo
    refine intOn_bdd (Fm_comp_measurable χ (fun x : ℝ => (b : ℝ) - x) (by fun_prop))
      measurableSet_Ioo measure_Ioo_lt_top.ne ((∑ n ∈ Finset.range (⌊(b : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2) fun x _ => ?_
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le (R := b) (x := x) (u := (b : ℝ) - x) χ (by linarith)
  have hPhiJ : IntegrableOn ((fun x => ∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2)) (Ioo (N : ℝ) (2 * N)) :=
    Phi_intOn χ measurableSet_Ioo measure_Ioo_lt_top.ne (R := 4 * N)
      fun x hx => by linarith [hx.2]
  have hkey : (∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), ∫ x in ((b : ℝ) - h + 1)..b, (‖movingSum χ x (b - x)‖ ^ 2)) ≤
      ∫ u in Ioc 0 h, windowMean N χ u := by
    have e1 : ∀ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), (∫ x in ((b : ℝ) - h + 1)..b, (‖movingSum χ x (b - x)‖ ^ 2)) =
        ∫ x, (Ioo ((b : ℝ) - h + 1) b).indicator (fun x => (‖movingSum χ x (b - x)‖ ^ 2)) x := by
      intro b hb
      obtain ⟨hb2, hb1⟩ := hbB b hb
      rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
        integral_indicator measurableSet_Ioo]
    rw [Finset.sum_congr rfl e1, ← integral_finsetSum _ hGint]
    calc (∫ x, ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), (Ioo ((b : ℝ) - h + 1) b).indicator (fun x => (‖movingSum χ x (b - x)‖ ^ 2)) x)
        ≤ ∫ x, (Ioo (N : ℝ) (2 * N)).indicator ((fun x => ∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2)) x :=
          integral_mono (integrable_finsetSum _ hGint)
            (hPhiJ.integrable_indicator measurableSet_Ioo)
            (fun x => right_pointwise χ hJ (by linarith) (by linarith) x)
      _ = ∫ x in Ioo (N : ℝ) (2 * N), (∫ u in Ioc 0 h, ‖movingSum χ x u‖ ^ 2) := integral_indicator measurableSet_Ioo
      _ ≤ _ := swap_le χ N measurableSet_Ioo (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
          (by linarith)
  have hβ0 : 0 ≤ β ^ 2 := sq_nonneg _
  nlinarith


end

section
-- ===== from Burst9Clip5.lean =====

variable {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))

theorem Fm_const_measurable (c : ℝ) (g : ℝ → ℝ) (hg : Measurable g) :
    Measurable (fun x : ℝ => (‖movingSum χ c (g x)‖ ^ 2)) := by
  have h1 : Measurable (fun x : ℝ => (c, g x)) := measurable_const.prodMk hg
  have h2 := (Fm_measurable χ).comp h1
  exact h2

/-- **One pair of end points**: `∫ |Σ_{x < n ≤ x + h, a ≤ n ≤ b} c_n|² dx ≤ W(h) +
∫_0^h |S(a, u)|² du + ∫_{b-h}^{b} |S(x, b - x)|² dx`. PROVED. -/
theorem pair_bound {N K0 : ℕ} (hN : 64 ≤ N) (hK4 : 4 * K0 ≤ N) {h : ℝ} (h2 : 2 ≤ h)
    (h8 : 8 * h ≤ N) {a b : ℕ} (ha : a ∈ (Finset.Ico N (N + K0))) (hb : b ∈ (Finset.Ioc (2 * N - K0) (2 * N))) :
    (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2) ≤
      windowMean N χ h + (∫ u in (0 : ℝ)..h, (‖movingSum χ a u‖ ^ 2)) +
        (∫ x in ((b : ℝ) - h)..b, (‖movingSum χ x (b - x)‖ ^ 2)) := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hK4r : (4 : ℝ) * K0 ≤ N := by exact_mod_cast hK4
  have ha' := Finset.mem_Ico.mp ha
  have hb' := Finset.mem_Ioc.mp hb
  have haN : (N : ℝ) ≤ a := by exact_mod_cast ha'.1
  have haK : (a : ℝ) + 1 ≤ N + K0 := by exact_mod_cast ha'.2
  have hb2 : (b : ℝ) ≤ 2 * N := by exact_mod_cast hb'.2
  have hbK : (2 * N : ℝ) - K0 < b := by
    have : 2 * N - K0 < b := hb'.1
    have h3 : ((2 * N - K0 : ℕ) : ℝ) < b := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h3
    push_cast at h3
    linarith
  have hab : (a : ℝ) + h ≤ b := by linarith
  set f1 : ℝ → ℝ := fun x => (‖movingSum χ a (x + h - a)‖ ^ 2) with hf1
  set f2 : ℝ → ℝ := fun x => (‖movingSum χ x h‖ ^ 2) with hf2
  set f3 : ℝ → ℝ := fun x => (‖movingSum χ x (b - x)‖ ^ 2) with hf3
  set g : ℝ → ℝ := fun x => (Ico ((a : ℝ) - h) a).indicator f1 x +
    (Icc (a : ℝ) (b - h)).indicator f2 x + (Ioo ((b : ℝ) - h) b).indicator f3 x with hg
  have i1 : IntegrableOn f1 (Ico ((a : ℝ) - h) a) := by
    refine intOn_bdd (Fm_const_measurable χ a (fun x => x + h - a) (by fun_prop))
      measurableSet_Ico measure_Ico_lt_top.ne ((∑ n ∈ Finset.range (⌊((4 * N) : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2) fun x hx => ?_
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le (R := 4 * N) (x := (a : ℝ)) (u := x + h - a) χ (by linarith [hx.2])
  have i2 : IntegrableOn f2 (Ioc ((N : ℝ) / 2) (3 * N)) :=
    Fm_int_x χ measurableSet_Ioc measure_Ioc_lt_top.ne (R := 4 * N)
      fun x hx => by linarith [hx.2]
  have hsub2 : Icc (a : ℝ) (b - h) ⊆ Ioc ((N : ℝ) / 2) (3 * N) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have i3 : IntegrableOn f3 (Ioo ((b : ℝ) - h) b) := by
    refine intOn_bdd (Fm_comp_measurable χ (fun x : ℝ => (b : ℝ) - x) (by fun_prop))
      measurableSet_Ioo measure_Ioo_lt_top.ne ((∑ n ∈ Finset.range (⌊((4 * N) : ℝ)⌋₊ + 1), ‖cf χ n‖) ^ 2) fun x _ => ?_
    rw [abs_of_nonneg (Fm_nonneg χ _ _)]
    exact Fm_le (R := 4 * N) (x := x) (u := (b : ℝ) - x) χ (by linarith)
  have I1 := i1.integrable_indicator measurableSet_Ico
  have I2 := (i2.mono_set hsub2).integrable_indicator measurableSet_Icc
  have I3 := i3.integrable_indicator measurableSet_Ioo
  -- the a.e. pointwise bound off the integers
  have hnull : volume (Set.range (fun n : ℕ => (n : ℝ))) = 0 :=
    (Set.countable_range _).measure_zero volume
  have hae : ∀ᵐ x ∂volume, x ∉ Set.range (fun n : ℕ => (n : ℝ)) :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  have hpt : ∀ᵐ x ∂volume, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2 ≤ g x := by
    filter_upwards [hae] with x hx
    have hxn : ∀ n : ℕ, x ≠ n := fun n h' => hx ⟨n, h'.symm⟩
    have n1 : 0 ≤ (Ico ((a : ℝ) - h) a).indicator f1 x :=
      indicator_nonneg (fun y _ => Fm_nonneg χ _ _) x
    have n2 : 0 ≤ (Icc (a : ℝ) (b - h)).indicator f2 x :=
      indicator_nonneg (fun y _ => Fm_nonneg χ _ _) x
    have n3 : 0 ≤ (Ioo ((b : ℝ) - h) b).indicator f3 x :=
      indicator_nonneg (fun y _ => Fm_nonneg χ _ _) x
    simp only [hg]
    rcases lt_or_ge x ((a : ℝ) - h) with hx1 | hx1
    · rw [clip_eq_zero χ (Or.inl hx1), norm_zero]; nlinarith
    rcases lt_or_ge x a with hx2 | hx2
    · have e : (Ico ((a : ℝ) - h) a).indicator f1 x = ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2 := by
        rw [indicator_of_mem (show x ∈ Ico ((a : ℝ) - h) a from ⟨hx1, hx2⟩), clip_eq_left χ hab hx1 hx2]
      linarith
    rcases le_or_gt (x + h) b with hx3 | hx3
    · have e : (Icc (a : ℝ) (b - h)).indicator f2 x = ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2 := by
        rw [indicator_of_mem (show x ∈ Icc (a : ℝ) (b - h) from ⟨hx2, by linarith⟩), clip_eq_mid χ (by linarith) hx2 hx3 hxn]
      linarith
    rcases lt_or_ge x b with hx4 | hx4
    · have e : (Ioo ((b : ℝ) - h) b).indicator f3 x = ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2 := by
        rw [indicator_of_mem (show x ∈ Ioo ((b : ℝ) - h) b from ⟨by linarith, hx4⟩), clip_eq_right χ (by linarith) hx4 hx2 hxn]
      linarith
    · rw [clip_eq_zero χ (Or.inr hx4), norm_zero]; nlinarith
  have hmono := integral_mono_ae (Burst9G.cwinSum_sq_integrable _ _ h (by linarith))
    ((I1.add I2).add I3) hpt
  refine hmono.trans ?_
  show (∫ x, g x) ≤ windowMean N χ h + (∫ u in (0 : ℝ)..h, (‖movingSum χ a u‖ ^ 2)) +
    intervalIntegral f3 ((b : ℝ) - h) b volume
  have e1 : (∫ x, g x) = (∫ x in Ico ((a : ℝ) - h) a, f1 x) + (∫ x in Icc (a : ℝ) (b - h), f2 x) +
      (∫ x in Ioo ((b : ℝ) - h) b, f3 x) := by
    have J12 : Integrable (fun x => (Ico ((a : ℝ) - h) a).indicator f1 x +
        (Icc (a : ℝ) (b - h)).indicator f2 x) := I1.add I2
    show (∫ x, ((Ico ((a : ℝ) - h) a).indicator f1 x + (Icc (a : ℝ) (b - h)).indicator f2 x) +
      (Ioo ((b : ℝ) - h) b).indicator f3 x) = _
    rw [integral_add J12 I3, integral_add I1 I2, integral_indicator measurableSet_Ico,
      integral_indicator measurableSet_Icc, integral_indicator measurableSet_Ioo]
  have e2 : (∫ x in Ico ((a : ℝ) - h) a, f1 x) = ∫ u in (0 : ℝ)..h, (‖movingSum χ a u‖ ^ 2) := by
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith)]
    have : ∀ x, x + h - (a : ℝ) = x + (h - a) := fun x => by ring
    simp only [hf1, this]
    rw [intervalIntegral.integral_comp_add_right (fun u => (‖movingSum χ a u‖ ^ 2)) (h - (a : ℝ))]
    congr 1 <;> ring
  have e3 : (∫ x in Ioo ((b : ℝ) - h) b, f3 x) = intervalIntegral f3 ((b : ℝ) - h) b volume := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have e4 : (∫ x in Icc (a : ℝ) (b - h), f2 x) ≤ windowMean N χ h :=
    setIntegral_mono_set i2 (Eventually.of_forall fun x => Fm_nonneg χ _ _)
      (Eventually.of_forall hsub2)
  have h1 := e1
  have h2 := e2
  have h3 := e3
  have h4 := e4
  linarith

/-- **The end averaging of the clipped window sum, PROVED**, with `C₁ = 6`: the route of
`Decomp1624.reduction27A` and the second term of `Decomp1624.WA`, for display 27, p. 364. -/
theorem clip_average_proved :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ N K0 : ℕ, 64 ≤ N → 1 ≤ K0 → 4 * K0 ≤ N →
      ∀ (q : ℕ+) (χ : DirichletCharacter ℂ (q : ℕ)) (h : ℝ), 2 ≤ h → 8 * h ≤ N →
        (1 / (K0 : ℝ) ^ 2) * ∑ a ∈ (Finset.Ico N (N + K0)), ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)),
            (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2) ≤
          C₁ * (windowMean N χ h + (1 / (K0 : ℝ)) * (∫ u in Ioc (0 : ℝ) h, windowMean N χ u) +
            (Real.log (2 * N) + 1) ^ 2) := by
  refine ⟨6, by norm_num, fun N K0 hN hK1 hK4 q χ h h2 h8 => ?_⟩
  set W := windowMean N χ h with hW
  set V := ∫ u in Ioc (0 : ℝ) h, windowMean N χ u with hV
  set β := Real.log (2 * N) + 1 with hβ
  set L : ℕ → ℝ := fun a => ∫ u in (0 : ℝ)..h, (‖movingSum χ a u‖ ^ 2) with hL
  set R : ℕ → ℝ := fun b => ∫ x in ((b : ℝ) - h)..b, (‖movingSum χ x (b - x)‖ ^ 2) with hR
  have hK0 : (0 : ℝ) < K0 := by exact_mod_cast hK1
  have hW0 : 0 ≤ W := setIntegral_nonneg measurableSet_Ioc fun x _ => sq_nonneg _
  have hp : ∀ a ∈ (Finset.Ico N (N + K0)), ∀ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)),
      (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) h x‖ ^ 2) ≤ W + L a + R b :=
    fun a ha b hb => pair_bound χ hN hK4 h2 h8 ha hb
  have hsum := Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hp a ha b hb
  have e : (∑ a ∈ (Finset.Ico N (N + K0)), ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), (W + L a + R b)) =
      (K0 : ℝ) * K0 * W + K0 * (∑ a ∈ (Finset.Ico N (N + K0)), L a) + K0 * ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), R b := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_Aset, card_Bset N K0 (by omega),
      nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  rw [e] at hsum
  have hLs : (∑ a ∈ (Finset.Ico N (N + K0)), L a) ≤ 3 * V + 2 * K0 * β ^ 2 := left_end_sum χ hN hK1 hK4 h2 h8
  have hRs : (∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), R b) ≤ 3 * V + 2 * K0 * β ^ 2 := right_end_sum χ hN hK4 h2 h8
  have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hK2]
  have hβ0 : 0 ≤ β ^ 2 := sq_nonneg _
  have key : (K0 : ℝ) * K0 * W + K0 * (∑ a ∈ (Finset.Ico N (N + K0)), L a) + K0 * ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)), R b ≤
      6 * (W + (1 / (K0 : ℝ)) * V + β ^ 2) * (K0 : ℝ) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hLs hK0.le
    have h2 := mul_le_mul_of_nonneg_left hRs hK0.le
    have e2 : 6 * (W + (1 / (K0 : ℝ)) * V + β ^ 2) * (K0 : ℝ) ^ 2 =
        6 * K0 * K0 * W + 6 * K0 * V + 6 * K0 * K0 * β ^ 2 := by
      field_simp
    rw [e2]
    have h3 : 0 ≤ (K0 : ℝ) * K0 * W := by positivity
    have h4 : 0 ≤ (K0 : ℝ) * K0 * β ^ 2 := by positivity
    nlinarith
  linarith


end

section
-- ===== `logpow_le_eps`, from Burst8P2b itself =====
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

end

section
-- ===== from Burst9Main.lean =====

/-! ### Elementary bounds -/

theorem log_two_mul_le {N : ℕ} (hN : 2 ≤ N) : Real.log (2 * N) ≤ 2 * L N := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold L
  rw [Real.log_mul (by norm_num) (by linarith)]
  have : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  linarith

theorem natlog_succ_le {N : ℕ} (hN : 2 ≤ N) (hℓ : 1 ≤ L N) :
    ((Nat.log 2 (2 * N) : ℕ) : ℝ) + 1 ≤ 4 * L N := by
  have h1 : 2 ^ Nat.log 2 (2 * N) ≤ 2 * N := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((Nat.log 2 (2 * N) : ℕ) : ℝ) * Real.log 2 ≤ Real.log (2 * N) := by
    have := Real.log_le_log (by positivity) (show ((2 ^ Nat.log 2 (2 * N) : ℕ) : ℝ) ≤
      ((2 * N : ℕ) : ℝ) by exact_mod_cast h1)
    push_cast at this
    rwa [Real.log_pow] at this
  have h3 := log_two_mul_le hN
  have hl2 : (2 / 3 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h0 : (0 : ℝ) ≤ (Nat.log 2 (2 * N) : ℕ) := Nat.cast_nonneg _
  nlinarith

theorem Q_sq (N : ℕ) : Q N ^ 2 = N / 4 := by
  unfold Q
  rw [div_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_num

theorem Q_le_sqrt (N : ℕ) : Q N ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
  unfold Q
  have : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  linarith

theorem Q_ge_four {N : ℕ} (hN : 64 ≤ N) : 4 ≤ Q N := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  unfold Q; rw [← Real.sqrt_eq_rpow]
  have : (8 : ℝ) ≤ √(N : ℝ) := by
    rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hNr
  linarith

/-- The moduli of `Y(M)`: `M ≤ q ≤ 2M`, `q ≤ Q`. PROVED. -/
theorem mem_Y_facts {N : ℕ} {ε ξ : ℝ} {M : ℕ} {q : ℕ+} (hq : q ∈ Y N ε ξ M) (hQ : 0 ≤ Q N) :
    M ≤ (q : ℕ) ∧ (q : ℕ) ≤ 2 * M ∧ ((q : ℕ) : ℝ) ≤ Q N := by
  obtain ⟨hqim, hMq, hqM, -⟩ := of_mem_filter hq
  obtain ⟨q0, -, hq0⟩ := Finset.mem_image.mp hqim
  have hqI := (Finset.mem_Icc.mp q0.property)
  have hqval : (q : ℕ) = q0.val := by rw [← hq0]; rfl
  have hqQf : (q : ℕ) ≤ ⌊Q N⌋₊ := by rw [hqval]; exact hqI.2
  exact ⟨hMq, hqM, (Nat.cast_le.mpr hqQf).trans (Nat.floor_le hQ)⟩

theorem card_Y_le (N : ℕ) (ε ξ : ℝ) (M : ℕ) (hQ : 0 ≤ Q N) :
    ((Y N ε ξ M).card : ℝ) ≤ Q N := by
  have h1 : (Y N ε ξ M).card ≤ ⌊Q N⌋₊ := by
    unfold Y
    refine (card_filter_le_of _).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_attach, Nat.card_Icc]; omega
  exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hQ)

/-- The end block length `K₀ = ⌈N L^{-K}⌉`. PROVED. -/
theorem K0_facts {N : ℕ} {K : ℝ} (hK : 1 ≤ K) (hN : 64 ≤ N) (hℓ : 8 ≤ L N)
    (hLN : L N ^ K ≤ N) :
    1 ≤ ⌈(N : ℝ) / L N ^ K⌉₊ ∧ 4 * ⌈(N : ℝ) / L N ^ K⌉₊ ≤ N ∧
      (N : ℝ) / L N ^ K ≤ ⌈(N : ℝ) / L N ^ K⌉₊ ∧
      (⌈(N : ℝ) / L N ^ K⌉₊ : ℝ) ≤ 2 * N / L N ^ K := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ0 : 0 < L N := by linarith
  have hLK : 8 ≤ L N ^ K := by
    calc (8 : ℝ) ≤ L N := hℓ
      _ = L N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L N ^ K := Real.rpow_le_rpow_of_exponent_le (by linarith) hK
  have hpos : 0 < (N : ℝ) / L N ^ K := by positivity
  have h1 : (N : ℝ) / L N ^ K ≤ N / 8 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hLK
  have hge1 : 1 ≤ (N : ℝ) / L N ^ K := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hc := Nat.ceil_lt_add_one hpos.le
  refine ⟨Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [Nat.ceil_eq_zero] at h0; linarith), ?_, Nat.le_ceil _, ?_⟩
  · have : ((4 * ⌈(N : ℝ) / L N ^ K⌉₊ : ℕ) : ℝ) ≤ N := by
      push_cast; linarith
    exact_mod_cast this
  · have : 2 * (N : ℝ) / L N ^ K = (N : ℝ) / L N ^ K + (N : ℝ) / L N ^ K := by ring
    linarith

theorem T1_le (C₁ : ℝ) (hC₁ : 0 < C₁) (N : ℕ) (Omv lam LK u φ : ℝ) (hl : lam ≤ LK)
    (hlam : 0 ≤ lam) (hu : 1 / φ ^ 2 ≤ u) :
    16 * π ^ 2 * C₁ * lam * N * Omv ^ 2 / φ ^ 2 ≤ 16 * π ^ 2 * C₁ * LK * N * Omv ^ 2 * u := by
  have hA0 : 0 ≤ 16 * π ^ 2 * C₁ * N * Omv ^ 2 := by positivity
  have hu0 : 0 ≤ 1 / φ ^ 2 := by positivity
  calc 16 * π ^ 2 * C₁ * lam * N * Omv ^ 2 / φ ^ 2
      = (16 * π ^ 2 * C₁ * N * Omv ^ 2) * lam * (1 / φ ^ 2) := by ring
    _ ≤ (16 * π ^ 2 * C₁ * N * Omv ^ 2) * LK * u :=
        mul_le_mul (mul_le_mul_of_nonneg_left hl hA0) hu hu0
          (mul_nonneg hA0 (hlam.trans hl))
    _ = _ := by ring

theorem T2_le {N : ℕ} (hN : 64 ≤ N) (C₁ : ℝ) (hC₁ : 0 < C₁) :
    16 * π ^ 2 * C₁ * (Real.log (2 * N) + 1) ^ 2 / Q N ^ 2 ≤
      144 * π ^ 2 * C₁ * L N ^ 2 / Q N ^ 2 := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 := log_two_mul_le (by omega : 2 ≤ N)
  have hl20 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hℓ : 1 ≤ L N := by
    unfold L
    have : Real.log 64 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    have h64 : (1 : ℝ) ≤ Real.log 64 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have h9 : (Real.log (2 * N) + 1) ^ 2 ≤ 9 * L N ^ 2 := by nlinarith
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have : 0 ≤ 16 * π ^ 2 * C₁ := by positivity
  nlinarith

theorem T3_le {N : ℕ} (hN : 64 ≤ N) (hℓ1 : 1 ≤ L N) (q : ℕ+) (hqQ : ((q : ℕ) : ℝ) ≤ Q N) :
    8 * (1 / (((q : ℕ) : ℝ) * Q N)) *
        (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n) ^ 2 ≤
      8 * (8 * L N ^ 2) ^ 2 := by
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ0 : 0 < Q N := by have := Q_ge_four hN; linarith
  have hq1 : (1 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.pos
  set B := 8 * L N ^ 2 with hB
  set E := ∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => ¬ Nat.Coprime n q), Λ n with hEdef
  have hE := Ex_sum_le N q
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  have hnl := natlog_succ_le (by omega : 2 ≤ N) hℓ1
  have hl2 := log_two_mul_le (by omega : 2 ≤ N)
  have hl20 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hE' : E ≤ ((q : ℕ) : ℝ) * B := by
    refine hE.trans ?_
    rw [hB, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    calc (((Nat.log 2 (2 * N) : ℕ) : ℝ) + 1) * Real.log (2 * N) ≤ (4 * L N) * (2 * L N) :=
          mul_le_mul hnl hl2 hl20 (by linarith)
      _ = 8 * L N ^ 2 := by ring
  have hE2 := pow_le_pow_left₀ hE0 hE' 2
  rw [show 8 * (1 / (((q : ℕ) : ℝ) * Q N)) * E ^ 2 = 8 * E ^ 2 / (((q : ℕ) : ℝ) * Q N) by ring]
  rw [div_le_iff₀ (by positivity)]
  have hB0 : 0 ≤ B := by positivity
  have hqq : ((q : ℕ) : ℝ) ^ 2 ≤ ((q : ℕ) : ℝ) * Q N := by nlinarith
  calc 8 * E ^ 2 ≤ 8 * ((((q : ℕ) : ℝ) * B) ^ 2) := by linarith
    _ = 8 * B ^ 2 * ((q : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ 8 * B ^ 2 * (((q : ℕ) : ℝ) * Q N) :=
        mul_le_mul_of_nonneg_left hqq (by positivity)

/-! ### The `R` part of one dyadic block -/

set_option maxHeartbeats 2000000 in
/-- **The leaf `Burst8P2.rpart_block_bound`, same type**, Section 5, pp. 363 and 364:
display 13, Gallagher's lemma, Cauchy and Schwarz, giving `energyA`, through the end averaging
route of `Decomp1624.reduction27A`, with `K₀ = ⌈N L^{-(A+4)}⌉` and `c = A + 6`.
PROVED, from `parseval_cost_proved` and `clip_average_proved`. -/
theorem rpart_block_bound_p3 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ A : ℝ, 0 < A →
      ∃ C c N₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ξ : ℝ, ∀ M : ℕ, 1 ≤ M →
        (M : ℝ) ≤ Q N →
        Rpart N ε ξ A M ≤ C * N * (L N ^ c * energyA N ε ξ M + L N ^ (-(A + 2))) := by
  obtain ⟨C₀, N₁, hC₀, hpc⟩ := parseval_cost_proved
  obtain ⟨C₁, hC₁, hcl⟩ := clip_average_proved
  refine ⟨1, one_pos, fun ε hε _ A hA => ?_⟩
  set K : ℝ := A + 4 with hKdef
  have hLtop : Tendsto (fun N : ℕ => L N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in atTop, 64 ≤ N ∧ 8 ≤ L N ∧
      L N ^ (A + 6) ≤ (N : ℝ) ^ (1 / 2 : ℝ) ∧ N₁ ≤ N := by
    filter_upwards [eventually_ge_atTop 64, hLtop.eventually_ge_atTop 8,
      logpow_le_eps (A + 6) (1 / 2) (by norm_num),
      tendsto_natCast_atTop_atTop.eventually_ge_atTop N₁] with N h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp hev
  set Cm : ℝ := 512 * π ^ 2 * C₁ with hCm
  set Ce : ℝ := 288 * π ^ 2 * C₁ + 1024 + 8 * C₀ with hCe
  refine ⟨Cm + Ce, A + 6, N2, by positivity, by linarith, fun N hN ξ M hM1 hMQ => ?_⟩
  have hNN2 : N2 ≤ N := by exact_mod_cast hN
  obtain ⟨hN64, hℓ8, hpow, hN1⟩ := hN2 N hNN2
  have hNr : (64 : ℝ) ≤ N := by exact_mod_cast hN64
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ := L N with hℓdef
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hQ4 := Q_ge_four hN64
  have hQ0 : 0 < Q N := by linarith
  have hsqrtN : (N : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
    rw [← Real.sqrt_eq_rpow]
    have := Real.sqrt_le_sqrt (show (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hNpos.le] at this
  have hKA6 : ℓ ^ K ≤ ℓ ^ (A + 6) := Real.rpow_le_rpow_of_exponent_le hℓ1 (by linarith)
  have hLN : ℓ ^ K ≤ N := hKA6.trans (hpow.trans hsqrtN)
  obtain ⟨hK1, hK4, hKlo, hKhi⟩ := K0_facts (K := K) (by linarith) hN64 hℓ8 hLN
  set K0 := ⌈(N : ℝ) / ℓ ^ K⌉₊ with hK0def
  have hK0r : (0 : ℝ) < K0 := by exact_mod_cast hK1
  have hLK0 : 0 < ℓ ^ K := Real.rpow_pos_of_pos hℓ0 _
  have hLK1 : 1 ≤ ℓ ^ K := Real.one_le_rpow hℓ1 (by linarith)
  -- the per modulus facts
  have hlam : ∀ q : ℕ+, ((q : ℕ) : ℝ) ≤ Q N → max 1 (gallagherWindow N q / K0) ≤ ℓ ^ K := by
    intro q hqQ
    refine max_le hLK1 ?_
    have hh : gallagherWindow N q ≤ N / 8 := by
      unfold gallagherWindow
      have := Q_sq N
      have h1 : ((q : ℕ) : ℝ) * Q N ≤ Q N * Q N := mul_le_mul_of_nonneg_right hqQ hQ0.le
      nlinarith
    rw [div_le_iff₀ hK0r]
    have : (N : ℝ) ≤ ℓ ^ K * K0 := by
      rw [div_le_iff₀ hLK0] at hKlo; linarith
    nlinarith
  have hclipq : ∀ q : ℕ+, ((q : ℕ) : ℝ) ≤ Q N → ∀ χ : DirichletCharacter ℂ (q : ℕ),
      (1 / (K0 : ℝ) ^ 2) * ∑ a ∈ (Finset.Ico N (N + K0)), ∑ b ∈ (Finset.Ioc (2 * N - K0) (2 * N)),
          (∫ x : ℝ, ‖Burst9G.cwinSum (Finset.Icc a b) (cf χ) (gallagherWindow N q) x‖ ^ 2) ≤
        C₁ * (windowMean N χ (gallagherWindow N q) + (1 / (K0 : ℝ)) *
          (∫ u in Ioc (0 : ℝ) (gallagherWindow N q), windowMean N χ u) +
            (Real.log (2 * N) + 1) ^ 2) := by
    intro q hqQ χ
    have hq1 : (1 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.pos
    refine hcl N K0 hN64 hK1 hK4 q χ _ ?_ ?_
    · unfold gallagherWindow; nlinarith
    · unfold gallagherWindow
      have := Q_sq N
      have h1 : ((q : ℕ) : ℝ) * Q N ≤ Q N * Q N := mul_le_mul_of_nonneg_right hqQ hQ0.le
      nlinarith
  -- the bound for each arc
  set δ : ℕ+ → ℝ := fun q => 1 / (((q : ℕ) : ℝ) * Q N) with hδ
  set Dt : ℕ+ → ℕ → ℝ := fun q r => (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N))),
    (∫ η in (-δ q)..(δ q), ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2) with hDt
  set B : ℝ := 8 * ℓ ^ 2 with hB
  set X : ℕ+ → ℝ := fun q =>
    16 * π ^ 2 * C₁ * ℓ ^ K * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) +
      144 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 8 * B ^ 2 with hX
  have harc : ∀ q ∈ Y N ε ξ M, ∀ r ∈ aWin N ε ξ (q : ℕ),
      (∫ α in arcM N A q r, ‖Decomp1519.R N q r (α - (r : ℝ) / q)‖ ^ 2) ≤ Dt q r + X q := by
    intro q hq r hr
    obtain ⟨hMq, -, hqQ⟩ := mem_Y_facts hq hQ0.le
    have hq1 : (1 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.pos
    have hqM : (M : ℝ) ≤ (q : ℕ) := by exact_mod_cast hMq
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hcop : Nat.Coprime r q := (Finset.mem_filter.mp (of_mem_filter hr).1).2
    have h1 := arc_to_eta N A q r (by positivity)
    have h2 := qr_bound hK1 hK4 q hQ0 hcop C₁ hC₁ (hclipq q hqQ)
    refine h1.trans (h2.trans ?_)
    have hlq : Real.log ((q : ℕ) : ℝ) ≤ ℓ := by
      simp only [hℓdef, L]
      exact Real.log_le_log (by linarith) (hqQ.trans ((Q_le_sqrt N).trans hsqrtN))
    have hinvφ := inv_totient_sq_le q.pos hlq hM0 hqM
    have hT1 := T1_le C₁ hC₁ N ((∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ)) _ _ _ _ (hlam q hqQ)
      (le_trans zero_le_one (le_max_left _ _)) hinvφ
    have hT2 := T2_le hN64 C₁ hC₁
    have hT3 := T3_le hN64 hℓ1 q hqQ
    show _ ≤ Dt q r + X q
    simp only [hDt, hX, hδ, hB]
    linarith
  -- sum over the arcs
  have hsum1 : Rpart N ε ξ A M ≤ ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), (Dt q r + X q) := by
    unfold Rpart
    exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r hr => harc q hq r hr
  -- the `D` part
  have hDsum : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), Dt q r) ≤ 4 * C₀ * K0 * ℓ ^ 2 := by
    have e1 : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), Dt q r) =
        (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N))), ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (∫ η in (-δ q)..(δ q), ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2) := by
      simp only [hDt]
      simp_rw [← Finset.mul_sum]
      congr 1
      exact (Finset.sum_congr rfl fun q _ => Finset.sum_comm).trans Finset.sum_comm
    rw [e1]
    have e1' : (∑ p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N))), ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (∫ η in (-δ q)..(δ q), ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2)) ≤
        ∑ _p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N))), C₀ * (2 * K0) * ℓ ^ 2 := by
      refine Finset.sum_le_sum fun p hp => ?_
      have := hpc N (by exact_mod_cast hN1) ε ξ hε M hM1 hMQ ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) (Dset_sub N p)
      refine this.trans ?_
      have hc : (((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)).card : ℝ) ≤ 2 * K0 := by exact_mod_cast card_Dset_le hK4 hp
      have := mul_le_mul_of_nonneg_left hc hC₀.le
      exact mul_le_mul_of_nonneg_right this (by positivity)
    rw [Finset.sum_const, card_Pset N K0 (by omega), nsmul_eq_mul] at e1'
    have hK2 : (0 : ℝ) < (K0 : ℝ) ^ 2 := by positivity
    calc (2 / (K0 : ℝ) ^ 2) * ∑ p ∈ ((Finset.Ico N (N + K0)) ×ˢ (Finset.Ioc (2 * N - K0) (2 * N))), ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (∫ η in (-δ q)..(δ q), ‖Rx ((Finset.Icc N (2 * N) \ Finset.Icc p.1 p.2)) q r η‖ ^ 2)
        ≤ (2 / (K0 : ℝ) ^ 2) * (((K0 * K0 : ℕ) : ℝ) * (C₀ * (2 * K0) * ℓ ^ 2)) :=
          mul_le_mul_of_nonneg_left e1' (by positivity)
      _ = 4 * C₀ * K0 * ℓ ^ 2 := by push_cast; field_simp; ring
  -- the `X` part
  have hX0 : ∀ q, 0 ≤ X q := fun q => by simp only [hX]; positivity
  have hXsum : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), X q) ≤
      ∑ q ∈ Y N ε ξ M, 2 * X q := by
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨-, -, hqQ⟩ := mem_Y_facts hq hQ0.le
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : ((aWin N ε ξ (q : ℕ)).card : ℝ) ≤ 2 := by
      exact_mod_cast card_aWin_le_two hN64 hε ξ q.pos hqQ
    exact mul_le_mul_of_nonneg_right hc (hX0 q)
  have hEA : energyA N ε ξ M = (1 / (M : ℝ) ^ 2) * ∑ q ∈ Y N ε ξ M, (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 := rfl
  have hXsum2 : (∑ q ∈ Y N ε ξ M, 2 * X q) ≤
      128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N * energyA N ε ξ M +
        (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2) := by
    have hYc := card_Y_le N ε ξ M hQ0.le
    simp only [hX]
    rw [Finset.sum_congr rfl fun q _ => (show 2 * (16 * π ^ 2 * C₁ * ℓ ^ K * N * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2 *
        (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) + 144 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 8 * B ^ 2) =
        (128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N) * ((1 / (M : ℝ) ^ 2) * (∑ χ : DirichletCharacter ℂ ((q : ℕ+) : ℕ), ‖gaussSum χ ZMod.stdAddChar‖ * WA (q := q) N χ) ^ 2) +
          (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 16 * B ^ 2) by ring),
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hEA, Finset.sum_const,
      nsmul_eq_mul]
    have h1 : ((Y N ε ξ M).card : ℝ) * (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 16 * B ^ 2) ≤
        Q N * (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 16 * B ^ 2) :=
      mul_le_mul_of_nonneg_right hYc (by positivity)
    have h2 : Q N * (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ^ 2 + 16 * B ^ 2) =
        288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2 := by
      field_simp
    linarith
  -- the final comparison
  have hE0 : 0 ≤ energyA N ε ξ M := energyA_nonneg N ε ξ M
  have hmain : 128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N * energyA N ε ξ M ≤
      Cm * N * (ℓ ^ (A + 6) * energyA N ε ξ M) := by
    have h1 : (1 + ℓ) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
    have h2 : ℓ ^ K * ℓ ^ 2 = ℓ ^ (A + 6) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hℓ0]
      congr 1
      rw [hKdef]; push_cast; ring
    have hA0 : 0 ≤ 128 * π ^ 2 * C₁ * ℓ ^ K * N * energyA N ε ξ M := by positivity
    calc 128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N * energyA N ε ξ M
        = (128 * π ^ 2 * C₁ * ℓ ^ K * N * energyA N ε ξ M) * (1 + ℓ) ^ 2 := by ring
      _ ≤ (128 * π ^ 2 * C₁ * ℓ ^ K * N * energyA N ε ξ M) * (4 * ℓ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hA0
      _ = 512 * π ^ 2 * C₁ * N * ((ℓ ^ K * ℓ ^ 2) * energyA N ε ξ M) := by ring
      _ = Cm * N * (ℓ ^ (A + 6) * energyA N ε ξ M) := by rw [h2, hCm]
  -- the small terms
  have hsmall_base : (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 ≤ N * ℓ ^ (-(A + 2)) := by
    have e : (N : ℝ) * ℓ ^ (-(A + 2)) * ℓ ^ (A + 6) = N * ℓ ^ 4 := by
      rw [mul_assoc, ← Real.rpow_add hℓ0, show -(A + 2) + (A + 6) = ((4 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have hp0 : 0 < ℓ ^ (A + 6) := Real.rpow_pos_of_pos hℓ0 _
    have hs0 : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
    have hss : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add hNpos]; norm_num
    rw [← mul_le_mul_iff_left₀ hp0, e]
    have h4 : 0 ≤ ℓ ^ 4 := by positivity
    calc (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 * ℓ ^ (A + 6)
        ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 * (N : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) * ℓ ^ 4 := by ring
      _ = N * ℓ ^ 4 := by rw [hss]
  have hsmall : 288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2 + 4 * C₀ * K0 * ℓ ^ 2 ≤
      Ce * N * ℓ ^ (-(A + 2)) := by
    have hQ1 : 1 ≤ Q N := by linarith
    have hl24 : ℓ ^ 2 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
    have hs1 : 1 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hQs := Q_le_sqrt N
    have t1 : 288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N ≤ 288 * π ^ 2 * C₁ * ((N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4) := by
      rw [div_le_iff₀ hQ0]
      have : ℓ ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 * Q N := by
        have : (1 : ℝ) * ℓ ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4 * Q N := by
          have := mul_le_mul hs1 hl24 (by positivity) (by positivity)
          nlinarith
        linarith
      have hc : 0 ≤ 288 * π ^ 2 * C₁ := by positivity
      nlinarith
    have t2 : 16 * Q N * B ^ 2 ≤ 1024 * ((N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4) := by
      rw [hB]
      have : 16 * Q N * (8 * ℓ ^ 2) ^ 2 = 1024 * (Q N * ℓ ^ 4) := by ring
      rw [this]
      have h4 : 0 ≤ ℓ ^ 4 := by positivity
      have := mul_le_mul_of_nonneg_right hQs h4
      linarith
    have t3 : 4 * C₀ * K0 * ℓ ^ 2 ≤ 8 * C₀ * (N * ℓ ^ (-(A + 2))) := by
      have hsK : ℓ ^ K = ℓ ^ (A + 2) * ℓ ^ 2 := by
        rw [← Real.rpow_natCast ℓ 2, ← Real.rpow_add hℓ0]
        congr 1
        rw [hKdef]; push_cast; ring
      have hA2 : 0 < ℓ ^ (A + 2) := Real.rpow_pos_of_pos hℓ0 _
      have e : (2 * N / ℓ ^ K) * ℓ ^ 2 = 2 * (N * ℓ ^ (-(A + 2))) := by
        rw [hsK, Real.rpow_neg hℓ0.le]
        field_simp
      have := mul_le_mul_of_nonneg_right hKhi (by positivity : 0 ≤ ℓ ^ 2)
      rw [e] at this
      nlinarith
    have hsb := hsmall_base
    have hc1 : 0 ≤ 288 * π ^ 2 * C₁ + 1024 := by positivity
    calc 288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2 + 4 * C₀ * K0 * ℓ ^ 2
        ≤ (288 * π ^ 2 * C₁ + 1024) * ((N : ℝ) ^ (1 / 2 : ℝ) * ℓ ^ 4) +
            8 * C₀ * (N * ℓ ^ (-(A + 2))) := by linarith
      _ ≤ (288 * π ^ 2 * C₁ + 1024) * (N * ℓ ^ (-(A + 2))) + 8 * C₀ * (N * ℓ ^ (-(A + 2))) := by
          have := mul_le_mul_of_nonneg_left hsb hc1
          linarith
      _ = Ce * N * ℓ ^ (-(A + 2)) := by rw [hCe]; ring
  -- assemble
  have hsplit : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), (Dt q r + X q)) =
      (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), Dt q r) +
        ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), X q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_add_distrib
  have hfin := hsum1.trans (le_of_eq hsplit)
  have hL0 : 0 ≤ ℓ ^ (-(A + 2)) := Real.rpow_nonneg hℓ0.le _
  have hE6 : 0 ≤ Ce * N * (ℓ ^ (A + 6) * energyA N ε ξ M) := by
    have : 0 ≤ Ce := by positivity
    positivity
  have hCm6 : 0 ≤ Cm * N * ℓ ^ (-(A + 2)) := by
    have : 0 ≤ Cm := by positivity
    positivity
  calc Rpart N ε ξ A M
      ≤ 128 * π ^ 2 * C₁ * ℓ ^ K * (1 + ℓ) ^ 2 * N * energyA N ε ξ M +
          (288 * π ^ 2 * C₁ * ℓ ^ 2 / Q N + 16 * Q N * B ^ 2 + 4 * C₀ * K0 * ℓ ^ 2) := by
        linarith
    _ ≤ Cm * N * (ℓ ^ (A + 6) * energyA N ε ξ M) + Ce * N * ℓ ^ (-(A + 2)) := by linarith
    _ ≤ (Cm + Ce) * N * (ℓ ^ (A + 6) * energyA N ε ξ M + ℓ ^ (-(A + 2))) := by nlinarith


end

end
end P3
set_option maxHeartbeats 200000

/-- LEAF: displays 13 and 23 to 27, pp. 361 and 364, for one dyadic block `M ≤ Q`, with the
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
  exact P3.rpart_block_bound_p3

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
