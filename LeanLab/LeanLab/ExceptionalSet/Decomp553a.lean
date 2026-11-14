import LeanLab.ExceptionalSet.UpJ200.Decomp539a

/-!
P0082 page369 displays37 to39. Block moment decomposition.
The analytic input controls only an inner large phase mass.
It contains no squared coefficient moment.
Source: https://doi.org/10.5802/aif.1621
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Decomp553a
open Real Finset MeasureTheory Set Filter Topology
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a

/-- P0082 page369 display37, the phase on an arbitrary finite block. -/
noncomputable def blockPhase (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, eC (t * v n)

/-- P0082 page369 before display39, each phase has norm one. -/
theorem blockPhase_le (s : Finset ℕ) (v : ℕ → ℝ) (N : ℕ)
    (hs : s.card ≤ N) (t : ℝ) : ‖blockPhase s v t‖ ≤ N := by
  exact (Fejer467.phase_sum_norm_le_card s v t).trans (by exact_mod_cast hs)

/-- P0082 page369 displays37 to39, finite block Gram reduction. -/
theorem block_moment_from_inner (P X Δ : ℝ) (s : Finset ℕ) (v : ℕ → ℝ)
    (N : ℕ) (hs : s.card ≤ N) (A : Set ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (V Q : ℝ) (hV : 0 ≤ V)
    (hinner : ∀ a ∈ A,
      (∫ b in A ∩ {b | V < ‖blockPhase s v (b - a)‖}, mass P X Δ b) ≤ Q) :
    (∑ n ∈ s, ‖∫ a in A, OddTail467.integrand P X Δ (v n) a‖ ^ 2) ≤
      V * (∫ a in A, mass P X Δ a) ^ 2 + N * Q * (∫ a in A, mass P X Δ a) := by
  have hg := Decomp483c.shifted_moment_gram_bound P X Δ hΔ hΔ1 s v A
  have hc : Continuous (fun z : ℝ × ℝ => ‖blockPhase s v (z.2 - z.1)‖) := by
    unfold blockPhase U1539.eC
    fun_prop
  exact hg.2.trans (localized_gram_bound A (mass P X Δ)
    (fun z => ‖blockPhase s v (z.2 - z.1)‖)
    (mass_integrable P X Δ hΔ hΔ1).integrableOn (fun a => norm_nonneg _)
    (fun z => norm_nonneg _) hc V N Q hV (Nat.cast_nonneg _) hg.1
    (fun a ha b hb => blockPhase_le s v N hs (b - a)) hinner)

/-- P0082 page369 displays38 and39, eventual block moment assembly.
CONDITIONAL ON the explicit inner mass hypothesis hinner. -/
theorem eventual_block_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (s : ℕ → Finset ℕ) (v : ℕ → ℝ) (hs : ∀ N, (s N).card ≤ N)
    (hinner : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            (∫ b in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
              {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                ‖blockPhase (s N) v (b - a)‖},
              mass (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(5 / 12 : ℝ))) b) ≤
                6 * C * F γ N * calE γ κ N ^ (-(2 / 3 : ℝ))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ s N,
            ‖∫ a in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                (calE γ κ N ^ (-(5 / 12 : ℝ))) (v n) a‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨d, hd, hi⟩ := hinner
  refine ⟨min d 1, lt_min hd one_pos, fun δ hδ hδsmall => ?_⟩
  obtain ⟨k, hk, hi⟩ := hi δ hδ (hδsmall.trans_le (min_le_left _ _))
  refine ⟨k, hk, fun κ hκ hκsmall => ?_⟩
  obtain ⟨C, hC, Ni, hi⟩ := hi κ hκ hκsmall
  have hδ1 : δ ≤ 1 := hδsmall.le.trans (min_le_right _ _)
  obtain ⟨Np, hp⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδ1 hκ
  refine ⟨49 * Real.log 4 ^ 2 + 42 * C * Real.log 4, by positivity,
    max Ni Np, fun N hN => ?_⟩
  have hNi : Ni ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hX, hE, hL, hl, hsaving, hTX, htw, hheight, hr⟩ := hp N hNp
  let X := F γ N
  let E := calE γ κ N
  let P := X ^ (6 * δ)
  let Δ := E ^ (-(5 / 12 : ℝ))
  let A := oddDomain P X E
  let M := ∫ a in A, mass P X Δ a
  have hX0 : 0 < X := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hE0 _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE (by norm_num)
  have hMi := mass_integrable P X Δ hΔ hΔ1
  have hM0 : 0 ≤ M := integral_nonneg (fun a => norm_nonneg _)
  have hMb : M ≤ 7 * (Real.log 4 * X * Real.log X) / Real.sqrt Δ := by
    apply (setIntegral_le_integral hMi (Filter.Eventually.of_forall (fun a => norm_nonneg _))).trans
    exact Decomp483d.shifted_weighted_mass_sqrt P X Δ hX hΔ hΔ1
  have hm := block_moment_from_inner P X Δ (s N) v N (hs N) A hΔ hΔ1
    ((N : ℝ) * E ^ (-(5 / 6 : ℝ))) (6 * C * X * E ^ (-(2 / 3 : ℝ)))
    (by positivity) (hi N hNi)
  have hsmall := small_phase_budget E (Real.log 4 * X * Real.log X) M N hE.le
    (by positivity) hM0 hMb
  have hsmalllog := small_phase_log_budget E X N hE.le hl
  have hlarge := large_phase_budget E X C M N hE.le hX0.le hC.le hL hl hMb
  calc
    _ ≤ N * E ^ (-(5 / 6 : ℝ)) * M ^ 2 +
        N * (6 * C * X * E ^ (-(2 / 3 : ℝ))) * M := hm
    _ ≤ (49 * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) +
        (42 * C * Real.log 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) :=
      add_le_add (hsmall.trans hsmalllog) hlarge
    _ = _ := by ring

/-- P0082 page369 display37, the assigned low_j0 index block. -/
noncomputable def indices_low_j0 (γ : ℝ) (N : ℕ) : Finset ℕ :=
  ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ)))).filter (fun n => n ≤ 3 * N / 4)

/-- P0082 page369 before display39, the block has at most N terms. -/
theorem indices_low_j0_card (γ : ℝ) (N : ℕ) : (indices_low_j0 γ N).card ≤ N := by
  unfold indices_low_j0
  exact (Finset.card_filter_le _ _).trans ((Finset.card_filter_le _ _).trans
    (by rw [Nat.card_Ioc]; omega))

/-- LEAF. P0082 page369 display39, derived low_j0 inner mass subproblem.
Only the large phase section is bounded. There is no squared moment here.
The finite Gram and small phase steps are proved separately. -/
theorem leaf_inner_low_j0 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            (∫ b in oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N) ∩
              {b | (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                ‖blockPhase (indices_low_j0 γ N) (fun n => F γ n - (0 : ℤ)) (b - a)‖},
              mass (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(5 / 12 : ℝ))) b) ≤
                6 * C * F γ N * calE γ κ N ^ (-(2 / 3 : ℝ)) := by
  sorry

/-- P0082 page369 displays37 to39, exact supply for the assigned block.
CONDITIONAL ON leaf_inner_low_j0. No source leaf is changed. -/
theorem leaf_moment_low_j0_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (∑ n ∈ ((Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + (0 : ℤ)))).filter (fun n => n ≤ 3 * N / 4),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - (0 : ℤ)) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  exact eventual_block_moment γ h1 h2 (indices_low_j0 γ)
    (fun n => F γ n - (0 : ℤ)) (indices_low_j0_card γ) (leaf_inner_low_j0 γ h1 h2)

end LeanLab.ExceptionalSet.Decomp553a
