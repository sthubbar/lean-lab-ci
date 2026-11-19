import LeanLab.ExceptionalSet.SPLIT_leaf_inner_high_j0

/-!
Split of `leaf_high_j0_large_phase_strip` from the split file of the assigned
upper index block of the half interval.

The target says: for `γ` in `(1, 3 / 2)` there is a width `δ₀` and, for each
smaller positive `δ` and each `κ` below a positive cap, an eventual threshold
`N₀` such that on the truncated minor window every pair of points whose assigned
block phase exceeds `N E ^ (-(5 / 6))` differs by a point that lies in the
finite union of half integer strips of radius `X ^ (δ - 1)` around multiples of
one half.

The step is cut into the two inputs its argument actually needs.

  * `leaf_high_j0_off_lattice_block_small` is the smallness of the block phase
    away from the half integer lattice: off the strips of radius `X ^ (δ - 1)`
    around the half integers with index at most `E ^ (3 / 4)` the restricted
    block sum is at most `N E ^ (-(5 / 6))`. It is one inequality about one sum,
    it has no existential conclusion and no statement about the strips as a set,
    so it is strictly weaker than the target: it is the contrapositive of the
    target on the finitely many half integers that can occur.
  * `leaf_high_j0_strip_index_bounded` is the arithmetic of that finite range:
    two points of the truncated window are at distance at most `2 E ^ (2 / 3)`
    and the strip radius is at most one once the threshold is passed, so an
    integer within `X ^ (δ - 1)` of their difference is bounded by
    `E ^ (3 / 4)`. This carries no phase and no sum.

The assembly is pure logic plus the ready-made finite index range: if `b` is not
in the union of strips, every bounded half integer is off the strips, the first
step bounds the block phase by `N E ^ (-(5 / 6))`, and this contradicts the
largeness hypothesis.

No existing file is edited, and the assembly does not use the target theorem.
-/

namespace LeanLab.ExceptionalSet.Decomp553b

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-! ### Scaffolding for this pass (private helpers; the leaf itself is untouched)

The leaf below is the parity-sifted block sum bound.  The helpers recorded here are
the pieces any route to it needs and that are already available: the size of the
block length `F γ N`, the gap forced on `b - a` by the off-lattice hypothesis (the
`h = 0` half integer), the trivial card bound on a block phase, and the reduction of
the assigned block to the even-filtered interval. -/

/-- The block length is positive. -/
private theorem F_pos (γ : ℝ) (N : ℕ) : 0 < F γ N := Real.exp_pos _

/-- The block length is at least one for `N ≥ 1`. -/
private theorem one_le_F (γ : ℝ) (hγ : 0 < γ) (N : ℕ) (hN : 1 ≤ N) : 1 ≤ F γ N := by
  rw [F]
  refine Real.one_le_exp ?_
  exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _

/-- The block length is monotone. -/
private theorem F_mono (γ : ℝ) (hγ : 0 < γ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    F γ m ≤ F γ n := by
  rw [F, F]
  refine Real.exp_le_exp.mpr ?_
  refine Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast hm)) ?_ hγ.le
  exact Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm))
    (by exact_mod_cast hmn)

/-- The off-lattice hypothesis at the half integer `0` forces the shift past the
strip radius. -/
private theorem gap_gt_of_off (γ κ δ : ℝ) (N : ℕ) (a b : ℝ)
    (hoff : ∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
      F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) :
    F γ N ^ (δ - 1) < |b - a| := by
  have h0 : (|(0 : ℤ)| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) := by
    simp only [Int.cast_zero, abs_zero]
    exact Real.rpow_nonneg (Real.exp_pos _).le _
  simpa only [Int.cast_zero, zero_div, sub_zero] using hoff 0 h0

/-- A block phase is bounded by the cardinality of its block. -/
private theorem blockPhase_le_card (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ) :
    ‖blockPhase s v t‖ ≤ (s.card : ℝ) :=
  blockPhase_le s v s.card le_rfl t

/-- The assigned high block is exactly the even-filtered interval `(3N/4, N]`. -/
private theorem indices_high_j0_eq (γ : ℝ) (N : ℕ) :
    indices_high_j0 γ N
      = (Finset.Ioc (3 * N / 4) N).filter (fun n => Even (nu γ n + (0 : ℤ))) := by
  unfold indices_high_j0
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by omega, h1.2⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨by omega, h1.2⟩, h2⟩, by omega⟩

/-- For `1 ≤ γ` and `0 < a ≤ b`: `γ a ^ (γ-1) (b - a) ≤ b ^ γ - a ^ γ`. -/
private lemma rpow_sub_rpow_ge {γ a b : ℝ} (hγ : 1 ≤ γ) (ha : 0 < a) (hab : a ≤ b) :
    γ * a ^ (γ - 1) * (b - a) ≤ b ^ γ - a ^ γ := by
  rcases lt_or_eq_of_le hab with h | h
  · have hcont : ContinuousOn (fun t : ℝ => t ^ γ) (Set.Icc a b) :=
      ContinuousOn.rpow_const (f := fun t : ℝ => t) (by fun_prop)
        (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le ha hx.1)))
    have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ γ) (Set.Ioo a b) := by
      intro x hx
      exact (Real.hasDerivAt_rpow_const (p := γ) (x := x)
        (Or.inl (ne_of_gt (lt_of_lt_of_le ha (le_of_lt hx.1))))).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcd⟩ :=
      exists_deriv_eq_slope (f := fun t : ℝ => t ^ γ) (hab := h) (hfc := hcont) (hfd := hdiff)
    rw [Real.deriv_rpow_const] at hcd
    have hc0 : a ≤ c := le_of_lt hc.1
    have hba : 0 < b - a := by linarith
    have hmono : a ^ (γ - 1) ≤ c ^ (γ - 1) := Real.rpow_le_rpow ha.le hc0 (by linarith)
    have hγ0 : 0 ≤ γ := by linarith
    have h1 : γ * a ^ (γ - 1) ≤ γ * c ^ (γ - 1) :=
      mul_le_mul_of_nonneg_left hmono hγ0
    have hstep : γ * a ^ (γ - 1) * (b - a) ≤ γ * c ^ (γ - 1) * (b - a) :=
      mul_le_mul_of_nonneg_right h1 hba.le
    have hkey : γ * c ^ (γ - 1) * (b - a) = b ^ γ - a ^ γ := by
      have hne : b - a ≠ 0 := ne_of_gt hba
      rw [hcd, div_mul_cancel₀ _ hne]
    linarith [hstep, hkey.le]
  · simp [h]

/-- For `n ≥ 2`: `1 / (n+1) ≤ log (n+1) - log n`. -/
private lemma log_step_ge {n : ℕ} (hn : 2 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) / (n : ℝ) := by positivity
  have h1 : 1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹ ≤ Real.log (((n : ℝ) + 1) / (n : ℝ)) :=
    Real.one_sub_inv_le_log_of_pos hpos
  have h2 : (((n : ℝ) + 1) / (n : ℝ))⁻¹ = (n : ℝ) / ((n : ℝ) + 1) := by rw [inv_div]
  have h3 : Real.log (((n : ℝ) + 1) / (n : ℝ))
      = Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) :=
    Real.log_div (by positivity) (by linarith)
  rw [h2, h3] at h1
  have h4 : (1 : ℝ) - (n : ℝ) / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) := by
    field_simp
    ring
  linarith [h1, h4.le]

/-- The step of `x ↦ exp ((log x)^γ)` is at least
`exp ((log n)^γ) * (γ * (log n)^(γ-1) / (n+1))`. -/
private lemma step_lb (γ : ℝ) (hγ : 1 < γ) {n : ℕ} (hn : 2 ≤ n) :
    Real.exp (Real.log (n : ℝ) ^ γ) * (γ * Real.log (n : ℝ) ^ (γ - 1) * (1 / ((n : ℝ) + 1)))
      ≤ Real.exp (Real.log ((n : ℝ) + 1) ^ γ) - Real.exp (Real.log (n : ℝ) ^ γ) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have ha : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hab : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  have hgap : γ * Real.log (n : ℝ) ^ (γ - 1) * (1 / ((n : ℝ) + 1))
      ≤ Real.log ((n : ℝ) + 1) ^ γ - Real.log (n : ℝ) ^ γ := by
    have h1 := rpow_sub_rpow_ge (γ := γ) (a := Real.log (n : ℝ))
      (b := Real.log ((n : ℝ) + 1)) (le_of_lt hγ) ha hab
    have h2 := log_step_ge hn
    have h3 : 0 ≤ γ * Real.log (n : ℝ) ^ (γ - 1) :=
      mul_nonneg (by linarith) (Real.rpow_pos_of_pos ha _).le
    have h4 : γ * Real.log (n : ℝ) ^ (γ - 1) * (1 / ((n : ℝ) + 1))
        ≤ γ * Real.log (n : ℝ) ^ (γ - 1)
            * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 h3
    linarith [h1, h4]
  have hsplit : Real.exp (Real.log ((n : ℝ) + 1) ^ γ)
      = Real.exp (Real.log (n : ℝ) ^ γ)
        * Real.exp (Real.log ((n : ℝ) + 1) ^ γ - Real.log (n : ℝ) ^ γ) := by
    rw [← Real.exp_add]
    ring_nf
  have hfac : Real.exp (Real.log (n : ℝ) ^ γ)
        * Real.exp (Real.log ((n : ℝ) + 1) ^ γ - Real.log (n : ℝ) ^ γ)
        - Real.exp (Real.log (n : ℝ) ^ γ)
      = Real.exp (Real.log (n : ℝ) ^ γ)
        * (Real.exp (Real.log ((n : ℝ) + 1) ^ γ - Real.log (n : ℝ) ^ γ) - 1) := by
    ring
  have hone : Real.log ((n : ℝ) + 1) ^ γ - Real.log (n : ℝ) ^ γ
      ≤ Real.exp (Real.log ((n : ℝ) + 1) ^ γ - Real.log (n : ℝ) ^ γ) - 1 := by
    linarith [Real.add_one_le_exp (Real.log ((n : ℝ) + 1) ^ γ - Real.log (n : ℝ) ^ γ)]
  have hF0 : 0 < Real.exp (Real.log (n : ℝ) ^ γ) := Real.exp_pos _
  rw [hsplit, hfac]
  exact mul_le_mul_of_nonneg_left (le_trans hgap hone) hF0.le

/-- LEAF. Step one, the block phase is small off the half integer strips. For
every admissible width `δ` and every admissible cap for `κ` there is an eventual
threshold such that, at every point `a` and every point `b` of the truncated
minor window, if `b - a` is further than `X ^ (δ - 1)` from `h / 2` for every
integer `h` with `|h| ≤ E ^ (3 / 4)`, then the assigned block phase at `b - a` is
at most `N E ^ (-(5 / 6))`. This is one inequality about one block sum, with no
existential conclusion and no set membership: it is the localization content of
the target read in contrapositive form on a bounded range of half integers, hence
strictly weaker. -/
theorem leaf_high_j0_off_lattice_block_small (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  sorry

/-- `calE γ κ N` tends to infinity in `N`: for every positive `κ` and every
`γ < 3 / 2` it eventually exceeds any fixed bound. -/
private theorem calE_eventually_ge (γ κ : ℝ) (hκ : 0 < κ) (h3 : 0 < 3 - 2 * γ)
    (B : ℝ) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → B ≤ calE γ κ N := by
  rcases le_or_gt B 1 with hB | hB
  · refine ⟨0, fun N _ => hB.trans ?_⟩
    rw [calE]
    refine Real.one_le_exp ?_
    have hlog : 0 ≤ Real.log (N : ℝ) := by
      rcases Nat.eq_zero_or_pos N with h | h
      · simp [h]
      · exact Real.log_nonneg (by exact_mod_cast h)
    exact mul_nonneg hκ.le (Real.rpow_nonneg hlog _)
  · have hlog : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have ht : Filter.Tendsto (fun N : ℕ => Real.log N ^ (3 - 2 * γ))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop h3).comp hlog
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
      (ht.eventually (Filter.eventually_ge_atTop (Real.log B / κ)))
    refine ⟨N₀, fun N hN => ?_⟩
    have h1 : Real.log B / κ ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := hN₀ N hN
    have h2 : Real.log B ≤ κ * Real.log (N : ℝ) ^ (3 - 2 * γ) := by
      have h3' := mul_le_mul_of_nonneg_left h1 hκ.le
      have he : κ * (Real.log B / κ) = Real.log B := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ hκ.ne'
      rwa [he] at h3'
    rw [calE, ← Real.exp_log (lt_trans zero_lt_one hB)]
    exact Real.exp_le_exp.mpr h2

/-- Beyond `5 ^ 12` the term `4 t ^ (2/3) + 2` is dominated by `t ^ (3/4)`. The
substitution `s = t ^ (1/12)` turns this into `4 s ^ 8 + 2 ≤ s ^ 9`, which holds
for `s ≥ 5` since `s ^ 8 (s - 4) ≥ 5 ^ 8 ≥ 2`. -/
private theorem four_rpow_two_thirds_add_two_le (t : ℝ) (ht : (5 : ℝ) ^ 12 ≤ t) :
    4 * t ^ (2 / 3 : ℝ) + 2 ≤ t ^ (3 / 4 : ℝ) := by
  have ht0 : 0 < t := by
    have hpos : (0 : ℝ) < (5 : ℝ) ^ 12 := by positivity
    linarith
  have hs : (5 : ℝ) ≤ t ^ (1 / 12 : ℝ) := by
    have h1 : ((5 : ℝ) ^ 12) ^ (1 / 12 : ℝ) ≤ t ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow (by positivity) ht (by norm_num)
    have h2 : ((5 : ℝ) ^ 12) ^ (1 / 12 : ℝ) = 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    linarith
  have hs2 : (4 : ℝ) ≤ t ^ (2 / 3 : ℝ) := by
    have h1 : ((5 : ℝ) ^ 12) ^ (2 / 3 : ℝ) ≤ t ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) ht (by norm_num)
    have h2 : ((5 : ℝ) ^ 12) ^ (2 / 3 : ℝ) = 390625 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    linarith
  have hc : t ^ (3 / 4 : ℝ) = t ^ (2 / 3 : ℝ) * t ^ (1 / 12 : ℝ) := by
    rw [← Real.rpow_add ht0]
    norm_num
  rw [hc]
  have hprod : t ^ (2 / 3 : ℝ) * 5 ≤ t ^ (2 / 3 : ℝ) * t ^ (1 / 12 : ℝ) :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  nlinarith [hprod, hs2]

/-- LEAF. Step two, the strip index is bounded. Two points of the truncated minor
window differ by at most `2 E ^ (2 / 3)`, the strip radius is at most one, and
`4 E ^ (2 / 3) + 2 ≤ E ^ (3 / 4)` eventually; hence any integer `h` with
`|(b - a) - h / 2| ≤ X ^ (δ - 1)` satisfies `|h| ≤ E ^ (3 / 4)`. This is one
inequality between real numbers: it involves neither the block phase nor any
sum, so it is strictly weaker than the target. -/
theorem leaf_high_j0_strip_index_bounded (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              ∀ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) →
                (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) := by
  have hγ3 : 0 < 3 - 2 * γ := by linarith
  refine ⟨1, by norm_num, ?_⟩
  intro δ hδ hδ1
  refine ⟨1, by norm_num, ?_⟩
  intro κ hκ _
  obtain ⟨N₀, hN₀⟩ := calE_eventually_ge γ κ hκ hγ3 ((5 : ℝ) ^ 12)
  refine ⟨max N₀ 1, ?_⟩
  intro N hN a ha b hb h habs
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hE12 : (5 : ℝ) ^ 12 ≤ calE γ κ N := hN₀ N hN0
  have hX1 : (1 : ℝ) ≤ F γ N := by
    rw [F]
    exact Real.one_le_exp (Real.rpow_nonneg hlog γ)
  have hXp : F γ N ^ (δ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
  simp only [oddDomain, Set.mem_inter_iff, Set.mem_Icc] at ha hb
  have hba : |b - a| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
  have htri : |(h : ℝ) / 2| ≤ |b - a| + |(b - a) - (h : ℝ) / 2| := by
    have he : (h : ℝ) / 2 = (b - a) + (-((b - a) - (h : ℝ) / 2)) := by ring
    calc |(h : ℝ) / 2| = |(b - a) + (-((b - a) - (h : ℝ) / 2))| := by
          conv_lhs => rw [he]
      _ ≤ |b - a| + |-((b - a) - (h : ℝ) / 2)| := abs_add_le _ _
      _ = |b - a| + |(b - a) - (h : ℝ) / 2| := by rw [abs_neg]
  have hstep : |(h : ℝ) / 2| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) + 1 := by
    linarith [htri, hba, hXp]
  have hmul : (|h| : ℝ) = 2 * |(h : ℝ) / 2| := by
    rw [abs_div]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    rw [h2]
    ring
  have h4 : 4 * calE γ κ N ^ (2 / 3 : ℝ) + 2 ≤ calE γ κ N ^ (3 / 4 : ℝ) :=
    four_rpow_two_thirds_add_two_le _ hE12
  rw [hmul]
  linarith

/-- Assembly. The two steps above localize the large values of the assigned
block phase into the finite union of strips. Suppose `b` is outside the union.
Then every half integer index of the bounded range carries a point of the union
away from `b`, which by the first step bounds the block phase by
`N E ^ (-(5 / 6))`, contradicting largeness. The index range is the ready-made
finite set of half integers of size at most `E ^ (3 / 4)`, which the second step
supplies. -/
theorem leaf_high_j0_large_phase_strip_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                ‖blockPhase (indices_high_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖ →
              b ∈ strips (calE γ κ N) (F γ N) δ a := by
  obtain ⟨δa, hδa, hoff⟩ := leaf_high_j0_off_lattice_block_small γ h1 h2
  obtain ⟨δb, hδb, hidx⟩ := leaf_high_j0_strip_index_bounded γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, ?_⟩
  intro δ hδ hδs
  have hδa' : δ < δa := hδs.trans_le (min_le_left _ _)
  have hδb' : δ < δb := hδs.trans_le (min_le_right _ _)
  obtain ⟨κa, hκa, hoff⟩ := hoff δ hδ hδa'
  obtain ⟨κb, hκb, hidx⟩ := hidx δ hδ hδb'
  refine ⟨min κa κb, lt_min hκa hκb, ?_⟩
  intro κ hκ hκs
  have hκa' : κ ≤ κa := hκs.trans (min_le_left _ _)
  have hκb' : κ ≤ κb := hκs.trans (min_le_right _ _)
  obtain ⟨Na, hoff⟩ := hoff κ hκ hκa'
  obtain ⟨Nb, hidx⟩ := hidx κ hκ hκb'
  refine ⟨max Na Nb, ?_⟩
  intro N hN
  have hNa : Na ≤ N := (le_max_left _ _).trans hN
  have hNb : Nb ≤ N := (le_max_right _ _).trans hN
  intro a ha b hb hlarge
  by_contra hnot
  have hoffl : ∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
      F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2| := by
    intro h hh
    apply not_le.mp
    intro hle
    apply hnot
    refine Set.mem_iUnion₂.mpr ⟨h, mem_stripIndices (calE γ κ N) h hh, ?_⟩
    rw [Set.mem_Icc]
    have habs := abs_le.mp hle
    constructor <;> linarith [habs.1, habs.2]
  have hsmall := hoff N hNa a ha b hb hoffl
  exact absurd hsmall (not_le.mpr hlarge)

end LeanLab.ExceptionalSet.Decomp553b
