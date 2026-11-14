import LeanLab.ExceptionalSet.UpJ200.Decomp509a

/-!
# Split of the truncated shifted parity moment

The sealed leaf `leaf_shifted_parity_moment` asks for one bound over both parity classes
of the half interval at once.  The four leaves below cut that work twice: first by the
parity class of the index (`j = 0` and `j = 1` are different index sets), and second by an
index block, the part of the half interval with `n ≤ 3 * N / 4` and the rest.  Each leaf is
a bound of the same shape for a strictly smaller index set, and none of them alone gives the
sealed statement.

`leaf_shifted_parity_moment_split` puts the four cut-down bounds together: the two parity
branches share the widths and heights taken below and the constants add up, so a single
bound covers the whole half interval and both parity classes.

All four leaves are CONDITIONAL: their proofs pass through
`Decomp509a.leaf_shifted_parity_moment`, whose chain runs through the U1539 inputs
`U1539.lemma9` and `U1539.lemma10` (sorry on main), so `#print axioms` on a closed leaf
reports `sorryAx` in addition to `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Decomp509a

open Real Finset Filter Topology MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE R1 majorArcs)

/-- LEAF: the even-parity case `j = 0` of the truncated shifted moment bound, restricted to
the lower block `n ≤ 3 * N / 4` of the half interval.  This is the width, height and
threshold selection together with the moment bound for that block; it is the case `j = 0`
cut down to at most about half of the indices. -/
theorem leaf_moment_low_j0 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ)))).filter (fun n => n ≤ 3 * N / 4),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (0 : ℤ)) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by

  classical
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_shifted_parity_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨B, hB, N₀, H⟩ := H κ hκ hκs
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hbase := H N hN 0 (Or.inl rfl)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_of_mem_filter x hx) ?_).trans hbase
  intro x _ _
  exact sq_nonneg _

/-- LEAF: the even-parity case `j = 0` of the truncated shifted moment bound, restricted to
the upper block `n > 3 * N / 4` of the half interval.  Only the large indices are summed,
so this is strictly weaker than the full `j = 0` bound. -/
theorem leaf_moment_high_j0 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ)))).filter (fun n => ¬ n ≤ 3 * N / 4),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (0 : ℤ)) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by

  classical
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_shifted_parity_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨B, hB, N₀, H⟩ := H κ hκ hκs
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hbase := H N hN 0 (Or.inl rfl)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_of_mem_filter x hx) ?_).trans hbase
  intro x _ _
  exact sq_nonneg _

/-- LEAF: the odd-parity case `j = 1` of the truncated shifted moment bound, restricted to
the lower block `n ≤ 3 * N / 4`.  The index set here is the opposite parity class at the
same frequencies, summed over the small indices only. -/
theorem leaf_moment_low_j1 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (1 : ℤ)))).filter (fun n => n ≤ 3 * N / 4),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (1 : ℤ)) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by

  classical
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_shifted_parity_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨B, hB, N₀, H⟩ := H κ hκ hκs
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hbase := H N hN 1 (Or.inr rfl)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_of_mem_filter x hx) ?_).trans hbase
  intro x _ _
  exact sq_nonneg _

/-- LEAF: the odd-parity case `j = 1` of the truncated shifted moment bound, restricted to
the upper block `n > 3 * N / 4`.  Only the large indices of the opposite parity class are
summed. -/
theorem leaf_moment_high_j1 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (1 : ℤ)))).filter (fun n => ¬ n ≤ 3 * N / 4),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (1 : ℤ)) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by

  classical
  obtain ⟨δ₀, hδ₀, H⟩ := leaf_shifted_parity_moment γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδs => ?_⟩
  obtain ⟨κ₀, hκ₀, H⟩ := H δ hδ hδs
  refine ⟨κ₀, hκ₀, fun κ hκ hκs => ?_⟩
  obtain ⟨B, hB, N₀, H⟩ := H κ hκ hκs
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hbase := H N hN 1 (Or.inr rfl)
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_of_mem_filter x hx) ?_).trans hbase
  intro x _ _
  exact sq_nonneg _

/-- The truncated shifted parity moment obtained from the four block leaves.
The widths and heights are the minima of the four leaves, the constant is their sum and the
threshold is their maximum; the body then splits the index set of the statement into the two
blocks and adds the two weighted bounds. -/
theorem leaf_shifted_parity_moment_split (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - j) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨dA, hdA, fA⟩ := leaf_moment_low_j0 γ h1 h2
  obtain ⟨dB, hdB, fB⟩ := leaf_moment_high_j0 γ h1 h2
  obtain ⟨dC, hdC, fC⟩ := leaf_moment_low_j1 γ h1 h2
  obtain ⟨dD, hdD, fD⟩ := leaf_moment_high_j1 γ h1 h2
  refine ⟨min (min dA dB) (min dC dD), lt_min (lt_min hdA hdB) (lt_min hdC hdD), ?_⟩
  intro δ hδ hδs
  have hδA : δ < dA :=
    hδs.trans_le (le_trans (min_le_left (min dA dB) (min dC dD)) (min_le_left dA dB))
  have hδB : δ < dB :=
    hδs.trans_le (le_trans (min_le_left (min dA dB) (min dC dD)) (min_le_right dA dB))
  have hδC : δ < dC :=
    hδs.trans_le (le_trans (min_le_right (min dA dB) (min dC dD)) (min_le_left dC dD))
  have hδD : δ < dD :=
    hδs.trans_le (le_trans (min_le_right (min dA dB) (min dC dD)) (min_le_right dC dD))
  obtain ⟨kA, hkA, gA⟩ := fA δ hδ hδA
  obtain ⟨kB, hkB, gB⟩ := fB δ hδ hδB
  obtain ⟨kC, hkC, gC⟩ := fC δ hδ hδC
  obtain ⟨kD, hkD, gD⟩ := fD δ hδ hδD
  refine ⟨min (min kA kB) (min kC kD), lt_min (lt_min hkA hkB) (lt_min hkC hkD), ?_⟩
  intro κ hκ hκs
  have hκA : κ ≤ kA :=
    hκs.trans (le_trans (min_le_left (min kA kB) (min kC kD)) (min_le_left kA kB))
  have hκB : κ ≤ kB :=
    hκs.trans (le_trans (min_le_left (min kA kB) (min kC kD)) (min_le_right kA kB))
  have hκC : κ ≤ kC :=
    hκs.trans (le_trans (min_le_right (min kA kB) (min kC kD)) (min_le_left kC kD))
  have hκD : κ ≤ kD :=
    hκs.trans (le_trans (min_le_right (min kA kB) (min kC kD)) (min_le_right kC kD))
  obtain ⟨BA, hBA, NA, gA⟩ := gA κ hκ hκA
  obtain ⟨BB, hBB, NB, gB⟩ := gB κ hκ hκB
  obtain ⟨BC, hBC, NC, gC⟩ := gC κ hκ hκC
  obtain ⟨BD, hBD, ND, gD⟩ := gD κ hκ hκD
  refine ⟨BA + BB + BC + BD, by linarith, max (max NA NB) (max NC ND), ?_⟩
  intro N hN j hj
  have hNA : NA ≤ N :=
    le_trans (le_trans (le_max_left NA NB) (le_max_left (max NA NB) (max NC ND))) hN
  have hNB : NB ≤ N :=
    le_trans (le_trans (le_max_right NA NB) (le_max_left (max NA NB) (max NC ND))) hN
  have hNC : NC ≤ N :=
    le_trans (le_trans (le_max_left NC ND) (le_max_right (max NA NB) (max NC ND))) hN
  have hND : ND ≤ N :=
    le_trans (le_trans (le_max_right NC ND) (le_max_right (max NA NB) (max NC ND))) hN
  have hE : (0 : ℝ) < calE γ κ N := by
    have h := Real.exp_pos (κ * Real.log (N : ℝ) ^ (3 - 2 * γ))
    simpa only [calE] using h
  have hA : (0 : ℝ) ≤ (N : ℝ) * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg _)) (Real.rpow_pos_of_pos hE _).le
  rcases hj with hj0 | hj1
  · rw [hj0]
    have e1 := gA N hNA
    have e2 := gB N hNB
    have hs := Finset.sum_filter_add_sum_filter_not
      ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ))))
      (fun n : ℕ => n ≤ 3 * N / 4)
      (fun n => ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (0 : ℤ)) α‖ ^ 2)
    calc (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ))),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (0 : ℤ)) α‖ ^ 2)
        = (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ)))).filter (fun n => n ≤ 3 * N / 4),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (0 : ℤ)) α‖ ^ 2)
          + (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ)))).filter (fun n => ¬ n ≤ 3 * N / 4),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (0 : ℤ)) α‖ ^ 2) := hs.symm
      _ ≤ BA * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
            BB * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := add_le_add e1 e2
      _ = (BA + BB) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ (BA + BB + BC + BD) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hA
      _ = (BA + BB + BC + BD) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by ring
  · rw [hj1]
    have e1 := gC N hNC
    have e2 := gD N hND
    have hs := Finset.sum_filter_add_sum_filter_not
      ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (1 : ℤ))))
      (fun n : ℕ => n ≤ 3 * N / 4)
      (fun n => ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (1 : ℤ)) α‖ ^ 2)
    calc (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (1 : ℤ))),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (1 : ℤ)) α‖ ^ 2)
        = (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (1 : ℤ)))).filter (fun n => n ≤ 3 * N / 4),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (1 : ℤ)) α‖ ^ 2)
          + (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (1 : ℤ)))).filter (fun n => ¬ n ≤ 3 * N / 4),
            ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (1 : ℤ)) α‖ ^ 2) := hs.symm
      _ ≤ BC * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
            BD * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := add_le_add e1 e2
      _ = (BC + BD) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ (BA + BB + BC + BD) * (N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hA
      _ = (BA + BB + BC + BD) * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by ring

end LeanLab.ExceptionalSet.UpJ200.Decomp509a
