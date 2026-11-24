import LeanLab.ExceptionalSet.SPLIT_leaf_high_j1_large_phase_localizes

/-!
Feed split of `Decomp553d.leaf_high_j1_off_lattice_block_small`, the
smallness of the assigned upper block phase `indices_high_j1` away from the
half integer strips.

Source: J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998), paper P0082, Lemma 9 on page 368, its proof in
section 7 on page 370, displays (40) and (41), and Theorem 2 on page 354.

The proof of Lemma 9 has two analytic inputs, which are the two leaves here.

  * `feed1122_high_j1_theorem2_block` is Theorem 2 of the paper, the
    Karacuba type bound for the plain sum `∑ e(β F(n))` over the block, used
    with `c = 3 δ` and `κ` below a fixed fraction of the constant of Theorem 2.
  * `feed1122_high_j1_parity_removal` is the Fourier removal of the parity
    condition `ν_n + 1 ≡ 0 mod 2`, displays (40) and (41) together with Lemma 4:
    if the plain sums at all shifts `t + h / 2` with `|h| ≤ X ^ δ` are small
    then the parity restricted block phase is small.

The proved assembly checks, by elementary inequalities taken from the already
proved window parameters, that every shift `t + h / 2` with `|h| ≤ X ^ δ` lies
in the range of Theorem 2 whenever `t` is off the strips, and then concludes as
in the last sentences of section 7. The index `j = 1` only multiplies each term
by the unimodular factor `e(-t)`, and the parity condition becomes
`ν_n + 1 ≡ 0 mod 2`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553d

open Real Finset MeasureTheory Set
open LeanLab.ExceptionalSet.U1539 (nu calE majorArcs eC)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a

/-- LEAF: P0082 Theorem 2 on page 354, applied on the upper block
`3 N / 4 < n ≤ N` with `c = 3 δ`: for `X ^ (δ - 1) < |β| ≤ 2 X ^ δ` the plain sum
`∑ e(β F(n))` over the block is at most `N exp(-K (log N) ^ (3 - 2 γ))`, and
taking `κ` at most a fixed fraction of `K` this is at most `N E ^ (-2)`.
The block is a subinterval of the dyadic range of Theorem 2; the Karacuba
estimate Lemma 10 on page 370 that proves Theorem 2 holds uniformly over
subintervals. Class HARD, a cited analytic theorem. -/
theorem feed1122_high_j1_theorem2_block (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
          F γ N ^ (δ - 1) < |β| → |β| ≤ 2 * F γ N ^ δ →
            ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => ¬ n ≤ 3 * N / 4),
                eC (β * F γ n)‖ ≤ (N : ℝ) * calE γ κ N ^ (-2 : ℝ) := by
  sorry

/-- LEAF: P0082 section 7 page 370, displays (40) and (41) with Lemma 4 on
page 359: the Fourier removal of the parity condition `ν_n + 1 ≡ 0 mod 2`. The
indicator of the condition is replaced by a smoothed periodic function with
Fourier coefficients `c_h ≪ min(1, A ^ (-1) h ^ (-2))`, `A = E ^ (-1)`; Lemma 4
counts the `n` where the smoothing differs from the indicator; the terms with
`|h| ≤ X ^ δ` are bounded by the hypothesis and the remaining terms by the
coefficient tail. The truncation is at `X ^ δ` rather than the paper's
`E ^ (2 / 3)`, since the threshold here is `N E ^ (-(5 / 6))`. Class HARD. -/
theorem feed1122_high_j1_parity_removal (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
          (∀ h : ℤ, (|h| : ℝ) ≤ F γ N ^ δ →
            ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => ¬ n ≤ 3 * N / 4),
                eC ((t + (h : ℝ) / 2) * F γ n)‖ ≤ (N : ℝ) * calE γ κ N ^ (-2 : ℝ)) →
          ‖blockPhase (indices_high_j1 γ N) (fun n => F γ n - (1 : ℤ)) t‖ ≤
            (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  sorry

/-- Proved helper, P0082 page 370 proof of Lemma 9: for `t` off the strips every
shift `t + h / 2` with `|h| ≤ X ^ δ` lies in the range of Theorem 2. -/
theorem feed1122_j1_shift_range (E X δ t : ℝ) (h : ℤ)
    (ht : |t| ≤ 2 * E ^ (2 / 3 : ℝ)) (hW1 : 2 * E ^ (2 / 3 : ℝ) ≤ X ^ δ)
    (hW2 : 4 * E ^ (2 / 3 : ℝ) + 2 ≤ E ^ (3 / 4 : ℝ)) (hW3 : X ^ (δ - 1) ≤ 1)
    (hoff : ∀ h : ℤ, (|h| : ℝ) ≤ E ^ (3 / 4 : ℝ) → X ^ (δ - 1) < |t - (h : ℝ) / 2|)
    (hh : (|h| : ℝ) ≤ X ^ δ) :
    X ^ (δ - 1) < |t + (h : ℝ) / 2| ∧ |t + (h : ℝ) / 2| ≤ 2 * X ^ δ := by
  have hh2 : |(h : ℝ) / 2| = (|h| : ℝ) / 2 := by
    rw [abs_div]; norm_num
  constructor
  · by_cases hc : (|h| : ℝ) ≤ E ^ (3 / 4 : ℝ)
    · have := hoff (-h) (by push_cast; rwa [abs_neg])
      have he : t - (((-h : ℤ) : ℝ)) / 2 = t + (h : ℝ) / 2 := by push_cast; ring
      rwa [he] at this
    · push Not at hc
      have htri : |(h : ℝ) / 2| ≤ |t + (h : ℝ) / 2| + |t| := by
        have := abs_sub (t + (h : ℝ) / 2) t
        simpa using this
      linarith
  · calc |t + (h : ℝ) / 2| ≤ |t| + |(h : ℝ) / 2| := abs_add_le _ _
      _ ≤ 2 * X ^ δ := by
        rw [hh2]
        have : 0 ≤ (|h| : ℝ) := abs_nonneg _
        linarith

/-- Assembly, statement copied verbatim from
`Decomp553d.leaf_high_j1_off_lattice_block_small`. P0082 page 370 proof of
Lemma 9: the block phase is small off the half integer strips, from the two
leaves and the proved shift range helper. -/
theorem leaf_high_j1_off_lattice_block_small_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (3 / 4 : ℝ) →
                F γ N ^ (δ - 1) < |(b - a) - (h : ℝ) / 2|) →
              ‖blockPhase (indices_high_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ ≤
                (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨δT, hδT, HT⟩ := feed1122_high_j1_theorem2_block γ h1 h2
  obtain ⟨δP, hδP, HP⟩ := feed1122_high_j1_parity_removal γ h1 h2
  refine ⟨min (min δT δP) 1, lt_min (lt_min hδT hδP) one_pos, ?_⟩
  intro δ hδ hδs
  have hδT' : δ < δT := hδs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδP' : δ < δP := hδs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := (hδs.trans_le (min_le_right _ _)).le
  obtain ⟨κT, hκT, HT⟩ := HT δ hδ hδT'
  obtain ⟨κP, hκP, HP⟩ := HP δ hδ hδP'
  refine ⟨min κT κP, lt_min hκT hκP, ?_⟩
  intro κ hκ hκs
  obtain ⟨NT, HT⟩ := HT κ hκ (hκs.trans (min_le_left _ _))
  obtain ⟨NP, HP⟩ := HP κ hκ (hκs.trans (min_le_right _ _))
  obtain ⟨NW, HW⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδ1 hκ
  refine ⟨max (max NT NP) NW, ?_⟩
  intro N hN a ha b hb hoff
  have hNT : NT ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNP : NP ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNW : NW ≤ N := (le_max_right _ _).trans hN
  obtain ⟨-, -, -, -, -, -, hW1, hW2, hW3⟩ := HW N hNW
  simp only [oddDomain, Set.mem_inter_iff, Set.mem_Icc] at ha hb
  have hba : |b - a| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [ha.2.1, ha.2.2, hb.2.1, hb.2.2]
  refine HP N hNP (b - a) (fun h hh => ?_)
  obtain ⟨hlo, hhi⟩ := feed1122_j1_shift_range (calE γ κ N) (F γ N) δ (b - a) h
    hba hW1 hW2 hW3 hoff hh
  exact HT N hNT _ hlo hhi

end LeanLab.ExceptionalSet.Decomp553d
