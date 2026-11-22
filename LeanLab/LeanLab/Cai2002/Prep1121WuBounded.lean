/-
BOUNDED-g preparation for the Wu 1993 input of Cai 2002, Lemma 4 (page 599).

This is the wiring of `WuTheorem2.lean` with the cited input weakened from Wu's general
hypothesis 1.4 to `|g l| ≤ 1` for every l, and with everything else reused verbatim from
`WuTheorem2.lean` (`wuH1`, `wuCount1`, `wuBadDvd1`, `wuH1_switched`, `wuCount1_bounds`,
`card_shift_dvd_le1`, `sum_wuBadDvd1_le`, `swWu_le_wuH1`, `wu2_eventually`).

The weakened input is written out inline as the hypothesis of each theorem below; this file
declares no definition of any kind, since the lab gate rejects a new def, even a private Prop
def. Three theorems are declared:

* `wuTheorem2Bdd_of_wuTheorem2`, which derives the bounded-g input from `WuTheorem2Stmt`
  (this checks that the inline statement really is weaker than Wu's general form, and that
  its exponents and quantifier order are the ones the wire uses);
* `wuUniform_of_wuTheorem2Bdd`, the lab's `hwu` of `MainConditional.lean` from it;
* `cai2002_main_theorem_wu_bdd`, the theorem of pages 597 to 598 from it.

Why the restriction: the wire to `MainTheorem` instantiates g with the indicator of a
finite set E, for which `|g| ≤ 1` is all that is used; hypothesis 1.4 with λ = 1, C = 3 is
derived from it in `wu_hyp14_of_abs_le_one`. Bounded g is what the wire needs, and the
general g case is where Wu´s Lemma 2.8 enters.

Every theorem below is proved from hypotheses stated on the theorem itself. AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Cai2002.WuTheorem2

open Filter Finset Real
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002

/-- Wu 1993, Théorème 2, display 1.7, page 111, restricted to real g with `|g n| ≤ 1` for
every n, follows from `WuTheorem2Stmt`: bounded g satisfies hypothesis 1.4 with λ = 1 and
C = 3 by `wu_hyp14_of_abs_le_one`, and B and K are allowed to depend on C and λ there. -/
theorem wuTheorem2Bdd_of_wuTheorem2 (h : WuTheorem2Stmt) :
    (∀ θ ε A : ℝ, 0 < ε → 3 / 5 + ε ≤ θ → θ ≤ 1 → 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
      ∀ g : ℕ → ℝ, (∀ n, |g n| ≤ 1) →
      ∀ (a : ℕ → ℕ) (h z : ℕ → ℝ), (∀ q, (a q).Coprime q) →
        (∀ q, 0 ≤ h q ∧ h q ≤ x ^ θ) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
        ∑ q ∈ Icc 1 ⌊x ^ (θ - 1 / 2) / log x ^ B⌋₊,
          |∑ l ∈ (Icc 1 ⌊x ^ ((5 * θ - 3) / 2 - ε)⌋₊).filter (fun l => l.Coprime q),
            g l * wuH1 (z q) (h q) q (a q) l| ≤ K * x ^ θ / log x ^ A) := by
  intro θ ε A hε hθ1 hθ2 hA
  obtain ⟨B, hB, K, hK, x0, hx0⟩ :=
    h θ ε 1 3 A hε hθ1 hθ2 (by norm_num) (by norm_num) hA
  exact ⟨B, hB, K, hK, x0, fun x hx g hg =>
    hx0 x hx g (wu_hyp14_of_abs_le_one g hg)⟩

/-- The uniform Wu input of the lab, the hypothesis `hwu` of `MainConditional.lean` spelled out,
follows from Wu 1993 Théorème 2, display 1.7, in the bounded-g form stated inline, with
θ = 0.95, ε = 0.2. The proof is the one of `wuUniform_of_wuTheorem2`: the only g used there
is the indicator function of E, for which `|g| ≤ 1` holds.
PROVED from that hypothesis. -/
theorem wuUniform_of_wuTheorem2Bdd
    (hW :
    (∀ θ ε A : ℝ, 0 < ε → 3 / 5 + ε ≤ θ → θ ≤ 1 → 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
      ∀ g : ℕ → ℝ, (∀ n, |g n| ≤ 1) →
      ∀ (a : ℕ → ℕ) (h z : ℕ → ℝ), (∀ q, (a q).Coprime q) →
        (∀ q, 0 ≤ h q ∧ h q ≤ x ^ θ) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
        ∑ q ∈ Icc 1 ⌊x ^ (θ - 1 / 2) / log x ^ B⌋₊,
          |∑ l ∈ (Icc 1 ⌊x ^ ((5 * θ - 3) / 2 - ε)⌋₊).filter (fun l => l.Coprime q),
            g l * wuH1 (z q) (h q) q (a q) l| ≤ K * x ^ θ / log x ^ A)) :
    (∀ A : ℝ, 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ E : Finset ℕ,
        (∀ e ∈ E, 0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ)) →
        (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), swWu337 N d E) ≤
          K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A) := by
  intro A hA
  obtain ⟨B, hB, K, hK, x0, hx0⟩ :=
    hW 0.95 0.2 A (by norm_num) (by norm_num) (by norm_num) hA
  refine ⟨B, hB, K + 1, by linarith, ?_⟩
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (wu2_eventually A B hB)
  refine ⟨max ⌈x0⌉₊ N1, fun N hN E hE => ?_⟩
  obtain ⟨hN3, hy3, h23, h4, hlog, hD1, hD2⟩ := hN1 N ((le_max_right ..).trans hN)
  have hx0N : x0 ≤ (N : ℝ) :=
    (Nat.le_ceil x0).trans (by exact_mod_cast (le_max_left ..).trans hN)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  set y : ℝ := (N : ℝ) ^ (0.95 : ℝ) with hy
  set M : ℝ := (N : ℝ) - y with hMdef
  set T : ℝ := (N : ℝ) ^ (0.3 : ℝ) with hTdef
  set D : ℝ := sw2Level337 N B with hDdef
  set L : ℝ := log (N : ℝ) with hLdef
  have hy0 : 0 < y := by positivity
  have hyN : y < N := by linarith
  have hT1 : 1 ≤ T := one_le_rpow hN1r (by norm_num)
  have hTN : (N : ℝ) < T ^ 4 := by
    rw [hTdef, ← rpow_natCast, ← rpow_mul hNp.le]
    have h12 : (N : ℝ) ^ (1 : ℝ) < (N : ℝ) ^ ((0.3 : ℝ) * ((4 : ℕ) : ℝ)) :=
      rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
    simpa using h12
  have hM2 : (N : ℝ) / 2 < M := by rw [hMdef]; linarith
  have hlarge : ∀ e ∈ E, ∀ r : ℕ, M ≤ ((e * r : ℕ) : ℝ) → T ≤ r := by
    intro e he r hr
    by_contra hlt
    rw [not_le] at hlt
    have he2 := (hE e he).2
    have hprod : ((e * r : ℕ) : ℝ) < (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) := by
      rw [rpow_add hNp]; push_cast
      exact mul_lt_mul'' he2 hlt (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hN23 : (0 : ℝ) ≤ (N : ℝ) ^ ((2 / 3 : ℝ) + 0.3) := by positivity
    linarith
  have hE2 : ∀ e ∈ E, 2 ≤ M / e := by
    intro e he
    have hepos : (0 : ℝ) < e := by exact_mod_cast (hE e he).1
    rw [le_div_iff₀ hepos]
    have := (hE e he).2
    linarith
  -- Théorème 2 with g the indicator of E, a = N mod d, h = y, z = M.
  have hW' := hx0 N hx0N (fun l => if l ∈ E then 1 else 0)
    (fun n => by split_ifs <;> norm_num)
    (fun d => if N.Coprime d then N % d else 1) (fun _ => y) (fun _ => M)
    (fun d => by
      split_ifs with hc
      · show Nat.gcd (N % d) d = 1
        rw [← Nat.gcd_rec]; exact hc.symm
      · exact Nat.coprime_one_left d)
    (fun _ => ⟨hy0.le, le_rfl⟩) (fun _ => ⟨hM2, by rw [hMdef]; linarith⟩)
  have e1 : ((0.95 : ℝ) - 1 / 2) = 0.45 := by norm_num
  have e2 : ((5 * (0.95 : ℝ) - 3) / 2 - 0.2) = 0.675 := by norm_num
  rw [e1, e2] at hW'
  -- On d coprime to N the Théorème 2 sum is the sum over E.
  have hS : ∀ d, N.Coprime d →
      (∑ l ∈ (Icc 1 ⌊(N : ℝ) ^ (0.675 : ℝ)⌋₊).filter (fun l => l.Coprime d),
        (if l ∈ E then (1 : ℝ) else 0) * wuH1 M y d (if N.Coprime d then N % d else 1) l) =
      ∑ e ∈ E.filter (fun e => e.Coprime d), wuH1 M y d (N % d) e := by
    intro d hd
    simp only [if_pos hd, ite_mul, one_mul, zero_mul]
    rw [← sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext a
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨_, hc⟩, ha⟩; exact ⟨ha, hc⟩
    · rintro ⟨ha, hc⟩
      refine ⟨⟨⟨(hE a ha).1, Nat.le_floor ?_⟩, hc⟩, ha⟩
      exact (hE a ha).2.le.trans (rpow_le_rpow_of_exponent_le hN1r (by norm_num))
  set Dc := (Icc 1 ⌊D⌋₊).filter (fun d => N.Coprime d)
  have hD0 : (0 : ℝ) ≤ D := le_trans (by positivity) hD1
  have hDfl1 : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by
    push_cast; exact le_trans (one_le_rpow hN1r (by norm_num)) hD1)
  have herr : ∀ d ∈ Dc, swWu337 N d E ≤
      |∑ l ∈ (Icc 1 ⌊(N : ℝ) ^ (0.675 : ℝ)⌋₊).filter (fun l => l.Coprime d),
        (if l ∈ E then (1 : ℝ) else 0) * wuH1 M y d (if N.Coprime d then N % d else 1) l| +
        (3 + 3 * ((y / T) / d)) := by
    intro d hdm
    have hd : N.Coprime d := (mem_filter.mp hdm).2
    rw [hS d hd]
    refine (swWu_le_wuH1 N d E hyN hE2).trans ?_
    gcongr
    have h2 := sum_wuBadDvd1_le N d E hd (by omega) T hT1 hTN hlarge
    rw [← hy] at h2
    linarith
  have hharm : ∑ d ∈ Icc 1 ⌊D⌋₊, ((d : ℝ))⁻¹ ≤ 1 + log (⌊D⌋₊ : ℝ) := by
    have := harmonic_le_one_add_log ⌊D⌋₊
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have hlogD : log (⌊D⌋₊ : ℝ) ≤ L := by
    apply log_le_log (by exact_mod_cast hDfl1)
    calc (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le hD0
      _ ≤ (N : ℝ) ^ (0.45 : ℝ) := hD2
      _ ≤ N := by
          calc (N : ℝ) ^ (0.45 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
                rpow_le_rpow_of_exponent_le hN1r (by norm_num)
            _ = N := rpow_one _
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← log_exp 1]
    apply log_le_log (exp_pos 1)
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith [Real.exp_one_lt_d9]
  have hyT : y / T = (N : ℝ) ^ (0.65 : ℝ) := by
    rw [hy, hTdef, ← rpow_sub hNp]; norm_num
  have h45 : (N : ℝ) ^ (0.45 : ℝ) ≤ (N : ℝ) ^ (0.65 : ℝ) :=
    rpow_le_rpow_of_exponent_le hN1r (by norm_num)
  have h65 : 0 ≤ (N : ℝ) ^ (0.65 : ℝ) := by positivity
  have hErr : ∑ d ∈ Dc, (3 + 3 * ((y / T) / d)) ≤ y / L ^ A := by
    calc _ ≤ ∑ d ∈ Icc 1 ⌊D⌋₊, (3 + 3 * ((y / T) / d)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = 3 * (⌊D⌋₊ : ℝ) + 3 * (y / T) * ∑ d ∈ Icc 1 ⌊D⌋₊, ((d : ℝ))⁻¹ := by
          rw [sum_add_distrib, sum_const, Nat.card_Icc, mul_sum]
          simp only [nsmul_eq_mul, Nat.add_sub_cancel]
          congr 1
          · ring
          · apply sum_congr rfl; intro d _; rw [div_eq_mul_inv]; ring
      _ ≤ 3 * (N : ℝ) ^ (0.65 : ℝ) + 3 * (N : ℝ) ^ (0.65 : ℝ) * (1 + L) := by
          rw [hyT]
          gcongr
          · exact (Nat.floor_le hD0).trans (hD2.trans h45)
          · exact hharm.trans (by linarith)
      _ ≤ 9 * (N : ℝ) ^ (0.65 : ℝ) * L := by nlinarith
      _ ≤ y / L ^ A := by
          have hLA : 0 < L ^ A := rpow_pos_of_pos (by linarith) _
          rw [le_div_iff₀ hLA]
          have hsplitL : L ^ (A + 1) = L ^ A * L := rpow_add_one (by linarith) A
          have hsplitN : y = (N : ℝ) ^ (0.65 : ℝ) * (N : ℝ) ^ (0.3 : ℝ) := by
            rw [hy, ← rpow_add hNp]; norm_num
          rw [hsplitN]
          calc 9 * (N : ℝ) ^ (0.65 : ℝ) * L * L ^ A
              = (N : ℝ) ^ (0.65 : ℝ) * (9 * L ^ (A + 1)) := by rw [hsplitL]; ring
            _ ≤ (N : ℝ) ^ (0.65 : ℝ) * (N : ℝ) ^ (0.3 : ℝ) := by gcongr
  have hWc : ∑ d ∈ Dc,
      |∑ l ∈ (Icc 1 ⌊(N : ℝ) ^ (0.675 : ℝ)⌋₊).filter (fun l => l.Coprime d),
        (if l ∈ E then (1 : ℝ) else 0) * wuH1 M y d (if N.Coprime d then N % d else 1) l| ≤
      K * y / L ^ A :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)).trans hW'
  calc (∑ d ∈ Dc, swWu337 N d E)
      ≤ ∑ d ∈ Dc, (|∑ l ∈ (Icc 1 ⌊(N : ℝ) ^ (0.675 : ℝ)⌋₊).filter (fun l => l.Coprime d),
          (if l ∈ E then (1 : ℝ) else 0) * wuH1 M y d (if N.Coprime d then N % d else 1) l| +
          (3 + 3 * ((y / T) / d))) := sum_le_sum herr
    _ = _ + _ := sum_add_distrib
    _ ≤ K * y / L ^ A + y / L ^ A := add_le_add hWc hErr
    _ = (K + 1) * y / L ^ A := by ring

/-- P0044, the Theorem of pages 597 to 598, CONDITIONAL ON BJS Theorem 6 and on Wu 1993
Théorème 2, display 1.7, page 111, in the bounded-g form stated inline. -/
theorem cai2002_main_theorem_wu_bdd
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt)
    (hW :
    (∀ θ ε A : ℝ, 0 < ε → 3 / 5 + ε ≤ θ → θ ≤ 1 → 0 < A →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
      ∀ g : ℕ → ℝ, (∀ n, |g n| ≤ 1) →
      ∀ (a : ℕ → ℕ) (h z : ℕ → ℝ), (∀ q, (a q).Coprime q) →
        (∀ q, 0 ≤ h q ∧ h q ≤ x ^ θ) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
        ∑ q ∈ Icc 1 ⌊x ^ (θ - 1 / 2) / log x ^ B⌋₊,
          |∑ l ∈ (Icc 1 ⌊x ^ ((5 * θ - 3) / 2 - ε)⌋₊).filter (fun l => l.Coprime q),
            g l * wuH1 (z q) (h q) q (a q) l| ≤ K * x ^ θ / log x ^ A)) : MainTheorem :=
  cai2002_main_theorem_conditional h6 (wuUniform_of_wuTheorem2Bdd hW)

/-- The general Wu input still gives the lab theorem through this file: `WuTheorem2Stmt`
implies the bounded-g form by `wuTheorem2Bdd_of_wuTheorem2`, so
`cai2002_main_theorem_wu_bdd` reproduces `cai2002_main_theorem_wu` of `WuTheorem2.lean`
from a strictly weaker cited statement. -/
theorem cai2002_main_theorem_wu_bdd_of_wuTheorem2
    (h6 : LeanLab.ChenExplicit.Theorem6Stmt) (hW : WuTheorem2Stmt) : MainTheorem :=
  cai2002_main_theorem_wu_bdd h6 (wuTheorem2Bdd_of_wuTheorem2 hW)

#print axioms wuTheorem2Bdd_of_wuTheorem2
#print axioms wuUniform_of_wuTheorem2Bdd
#print axioms cai2002_main_theorem_wu_bdd
#print axioms cai2002_main_theorem_wu_bdd_of_wuTheorem2

end LeanLab.Cai2002
