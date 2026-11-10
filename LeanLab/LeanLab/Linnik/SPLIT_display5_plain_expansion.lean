/-
Split of `LeanLab.Linnik.Decomp1532c.display5_plain_expansion`.

The sealed statement `Display5PlainExpansion` is one eventual bound for the averaged major arc
correlation error: the whole difference of the two tuple sums is bounded by a share `δ` of
`2 N L ^ (2k) / log N ^ 2`. The single open proof step is cut here by the size of the tuple
difference `dif x`. The three ranges are disjoint and cover every tuple with `dif x ≠ 0`, and the
budget `δ` is additive, so the three leaf bounds give the sealed statement back.

Leaves, one per range of `dif x` at fixed `N`, `θ`, `k`, `δ`:
* `split_small_shift_bound`: `|dif x| ≤ N ^ θ`, the shifts no larger than the major arc scale
  `P = N ^ θ`;
* `split_intermediate_shift_bound`: `N ^ θ < |dif x| ≤ N`;
* `split_large_shift_bound`: `N < |dif x|`.

Assembly: `display5_plain_expansion_split`, the sealed statement, with no sorry.

AI-written Lean code, DeepSeek V4.1 Flash Low, 2026-11-07. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Linnik.Decomp1532c
import LeanLab.Linnik.Decomp466b

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory Filter
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg primesLe)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- Gallagher 1975 p.134 display 3 and p.138 before display 5.
Elementary support and counting consequence. If each of the two exponent tuples has all zero based coordinates below H, and k times 2 to the H is at most B, then the absolute tuple difference is at most B.
AI wrote the Lean code. Goldbach is open. -/
theorem small_shift_of_coordinate_bound {k L H : ℕ} (x : LeanLab.Linnik.Decomp1532a.pairs k L)
    (hν : ∀ i, (x.1 i : ℕ) < H) (hμ : ∀ i, (x.2 i : ℕ) < H)
    {B : ℝ} (hB : (k : ℝ) * 2 ^ H ≤ B) : |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ B := by
  have hsum (v : Fin k → Fin L) (hv : ∀ i, (v i : ℕ) < H) : LeanLab.Linnik.U1434Lemma21.sv v ≤ k * 2 ^ H := by
    unfold LeanLab.Linnik.U1434Lemma21.sv
    calc
      _ ≤ ∑ i : Fin k, 2 ^ H :=
        sum_le_sum fun i _ => Nat.pow_le_pow_right (by norm_num) (by have := hv i; omega)
      _ = _ := by simp
  have ha := hsum x.1 hν
  have hb := hsum x.2 hμ
  have hai : (LeanLab.Linnik.U1434Lemma21.sv x.1 : ℤ) ≤ (k * 2 ^ H : ℕ) := by exact_mod_cast ha
  have hbi : (LeanLab.Linnik.U1434Lemma21.sv x.2 : ℤ) ≤ (k * 2 ^ H : ℕ) := by exact_mod_cast hb
  have hi : -(k * 2 ^ H : ℤ) ≤ LeanLab.Linnik.Decomp1532a.dif x ∧ LeanLab.Linnik.Decomp1532a.dif x ≤ (k * 2 ^ H : ℤ) := by
    unfold LeanLab.Linnik.Decomp1532a.dif
    push_cast at hai hbi
    omega
  have hr : -((k : ℝ) * 2 ^ H) ≤ (LeanLab.Linnik.Decomp1532a.dif x : ℝ) ∧ (LeanLab.Linnik.Decomp1532a.dif x : ℝ) ≤ (k : ℝ) * 2 ^ H := by
    exact_mod_cast hi
  exact (abs_le.mpr hr).trans hB

/-- Gallagher 1975 p.134 display 3 and p.138 before display 5.
Elementary support and counting consequence. If the absolute tuple difference exceeds N and k times 2 to the H is at most N, at least one coordinate in one of the two tuples is at least H.
AI wrote the Lean code. Goldbach is open. -/
theorem large_shift_has_high_coordinate {k L H N : ℕ} (x : LeanLab.Linnik.Decomp1532a.pairs k L)
    (hscale : (k : ℝ) * 2 ^ H ≤ (N : ℝ))
    (hlarge : (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|) :
    (∃ i, H ≤ (x.1 i : ℕ)) ∨ (∃ i, H ≤ (x.2 i : ℕ)) := by
  by_contra! h
  have hb := small_shift_of_coordinate_bound x
    (fun i => by have := h.1 i; omega) (fun i => by have := h.2 i; omega) hscale
  linarith

/-- Gallagher 1975 p.134 display 3 and p.138 before display 5.
Elementary support and counting consequence. For H at most L, the number of pairs whose coordinates are all below H is exactly H to the 2k.
AI wrote the Lean code. Goldbach is open. -/
theorem low_box_card {k L H : ℕ} (hHL : H ≤ L) :
    Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L //
      (∀ i, (x.1 i : ℕ) < H) ∧ (∀ i, (x.2 i : ℕ) < H)} = H ^ (2 * k) := by
  let e : {x : LeanLab.Linnik.Decomp1532a.pairs k L //
      (∀ i, (x.1 i : ℕ) < H) ∧ (∀ i, (x.2 i : ℕ) < H)} ≃ LeanLab.Linnik.Decomp1532a.pairs k H :=
    { toFun := fun x => (fun i => ⟨(x.1.1 i : ℕ), x.2.1 i⟩,
        fun i => ⟨(x.1.2 i : ℕ), x.2.2 i⟩)
      invFun := fun y => ⟨(fun i => ⟨(y.1 i : ℕ), (y.1 i).isLt.trans_le hHL⟩,
        fun i => ⟨(y.2 i : ℕ), (y.2 i).isLt.trans_le hHL⟩),
        (fun i => (y.1 i).isLt), (fun i => (y.2 i).isLt)⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; rfl }
  have h := Fintype.card_congr e
  simpa only [LeanLab.Linnik.Decomp1532a.pairs, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ← pow_add, ← two_mul] using h

/-- Gallagher 1975 p.134 display 3 and p.138 before display 5.
Elementary support and counting consequence. For H at most L and k times 2 to the H at most N, the number of tuple pairs with absolute difference greater than N is at most L to the 2k minus H to the 2k.
AI wrote the Lean code. Goldbach is open. -/
theorem large_shift_tuple_count_le {k L H N : ℕ} (hHL : H ≤ L)
    (hscale : (k : ℝ) * 2 ^ H ≤ (N : ℝ)) :
    Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L // (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|} ≤
      L ^ (2 * k) - H ^ (2 * k) := by
  classical
  let p : LeanLab.Linnik.Decomp1532a.pairs k L → Prop := fun x =>
    (∀ i, (x.1 i : ℕ) < H) ∧ (∀ i, (x.2 i : ℕ) < H)
  have hmono : Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L // (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|} ≤
      Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L // ¬ p x} := by
    apply Fintype.card_subtype_mono
    intro x hx hp
    have hb := small_shift_of_coordinate_bound x hp.1 hp.2 hscale
    linarith
  calc
    _ ≤ Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L // ¬ p x} := hmono
    _ = Fintype.card (LeanLab.Linnik.Decomp1532a.pairs k L) - Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L // p x} :=
      Fintype.card_subtype_compl p
    _ = _ := by
      rw [show Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L // p x} = H ^ (2 * k) from low_box_card hHL]
      simp only [LeanLab.Linnik.Decomp1532a.pairs, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        ← pow_add, ← two_mul]

/-- Gallagher 1975 p.134 display 3 and p.138 before display 5.
Elementary support and counting consequence. For d at most L and `k * 2^(L-d) ≤ N`, the large shift tuple count is at most `2*k*d*L^(2*k-1)`.
AI wrote the Lean code. Goldbach is open. -/
theorem large_shift_tuple_count_bound {k L d N : ℕ} (hd : d ≤ L)
    (hscale : (k : ℝ) * 2 ^ (L - d) ≤ (N : ℝ)) :
    (Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k L // (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|} : ℝ) ≤
      2 * k * d * (L : ℝ) ^ (2 * k - 1) := by
  have hc := large_shift_tuple_count_le (Nat.sub_le L d) hscale
  have hp : (L - d) ^ (2 * k) ≤ L ^ (2 * k) := Nat.pow_le_pow_left (Nat.sub_le L d) (2 * k)
  have hdR : (d : ℝ) ≤ L := by exact_mod_cast hd
  have hdiff : (0 : ℝ) ≤ (L : ℝ) - d := sub_nonneg.mpr hdR
  calc
    _ ≤ ((L ^ (2 * k) - (L - d) ^ (2 * k) : ℕ) : ℝ) := by exact_mod_cast hc
    _ = (L : ℝ) ^ (2 * k) - ((L - d : ℕ) : ℝ) ^ (2 * k) := by
      rw [Nat.cast_sub hp]; push_cast; rfl
    _ ≤ |(L : ℝ) ^ (2 * k) - ((L - d : ℕ) : ℝ) ^ (2 * k)| := le_abs_self _
    _ ≤ |(L : ℝ) - ((L - d : ℕ) : ℝ)| * (2 * k) *
        max |(L : ℝ)| |((L - d : ℕ) : ℝ)| ^ (2 * k - 1) := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (abs_pow_sub_pow_le (L : ℝ) ((L - d : ℕ) : ℝ) (2 * k))
    _ = _ := by
      rw [Nat.cast_sub hd]
      simp only [sub_sub_cancel, abs_of_nonneg (show (0 : ℝ) ≤ d by positivity),
        abs_of_nonneg (show (0 : ℝ) ≤ L by positivity), abs_of_nonneg hdiff,
        max_eq_left (by linarith : (L : ℝ) - d ≤ L)]
      ring

/-- Gallagher 1975 p.134 display 3 and p.138 before display 5.
Elementary support and counting consequence. For k at most 2 to the d, d at most log base 2 of N and N positive, the large shift tuple count is at most `2*k*d*L^(2*k-1)`.
AI wrote the Lean code. Goldbach is open. -/
theorem large_shift_tuple_count_log {k d N : ℕ} (hk : k ≤ 2 ^ d)
    (hd : d ≤ Nat.log 2 N) (hN : 1 ≤ N) :
    (Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) // (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|} : ℝ) ≤
      2 * k * d * (Nat.log 2 N : ℝ) ^ (2 * k - 1) := by
  apply large_shift_tuple_count_bound hd
  have hb : k * 2 ^ (Nat.log 2 N - d) ≤ N := by
    calc
      _ ≤ 2 ^ d * 2 ^ (Nat.log 2 N - d) := Nat.mul_le_mul_right _ hk
      _ = 2 ^ Nat.log 2 N := by rw [← pow_add]; congr 1; omega
      _ ≤ N := Nat.pow_log_le_self 2 (by omega)
  exact_mod_cast hb

/-- Gallagher 1975 p.134 display 3 and p.138 before display 5.
Elementary support and counting consequence. For each k at least 1 and each positive delta, every sufficiently large N has at most delta times L to the 2k tuple pairs with absolute difference greater than N.
AI wrote the Lean code. Goldbach is open. -/
theorem large_shift_tuple_density_zero {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (Fintype.card {x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) // (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|} : ℝ) ≤
        δ * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * (k : ℝ) * k / δ)
  refine ⟨2 ^ max k m, fun N hN => ?_⟩
  have hL : max k m ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hN
  have hkL : k ≤ Nat.log 2 N := (le_max_left k m).trans hL
  have hmL : (m : ℝ) ≤ (Nat.log 2 N : ℝ) := by
    exact_mod_cast (le_max_right k m).trans hL
  have hN1 : 1 ≤ N := by
    have hp : 0 < 2 ^ max k m := by positivity
    omega
  have hb := large_shift_tuple_count_log (k := k) (Nat.lt_pow_self (by norm_num : 1 < (2 : ℕ))).le hkL hN1
  have hA : 2 * (k : ℝ) * k ≤ δ * (Nat.log 2 N : ℝ) := by
    have h := (div_lt_iff₀ hδ).mp (hm.trans_le hmL)
    nlinarith
  have hp : (Nat.log 2 N : ℝ) ^ (2 * k - 1) * (Nat.log 2 N : ℝ) =
      (Nat.log 2 N : ℝ) ^ (2 * k) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ ≤ 2 * k * k * (Nat.log 2 N : ℝ) ^ (2 * k - 1) := hb
    _ ≤ (δ * (Nat.log 2 N : ℝ)) * (Nat.log 2 N : ℝ) ^ (2 * k - 1) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by rw [mul_assoc, mul_comm (Nat.log 2 N : ℝ), hp]

/-- Gallagher 1975. P0094 p.133 Lemma 4, p.134 display 3, p.136 Lemma 8 and p.138 before display 5. The restricted weight estimate is derived here from the proved totient bound and tuple count.
For each k at least 1 and each positive delta, every sufficiently large N has the sum of `|n|/φ(|n|)` over tuple pairs with `|n| > N` at most `delta * L^(2*k)`.
AI wrote the Lean code. Goldbach is open. -/
theorem large_shift_totient_weight_negligible {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|,
        ((LeanLab.Linnik.Decomp1532a.dif x).natAbs : ℝ) / (LeanLab.Linnik.Decomp1532a.dif x).natAbs.totient) ≤
          δ * (Nat.log 2 N : ℝ) ^ (2 * k) := by
  classical
  obtain ⟨C, hφ⟩ := LeanLab.Linnik.Decomp1532a.div_totient_le_loglog
  have hC : 0 < C := by
    have h3 := hφ 3 (by omega)
    have hl3 := LeanLab.Romanov.Decomp134b.loglog_pos 3 (by omega)
    by_contra! hneg
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg hneg hl3.le
    have htot : Nat.totient 3 = 2 := by decide
    rw [htot] at h3
    norm_num at h3 hnonpos
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun x : ℝ => Real.log (x + Real.log k) / x) atTop (𝓝 0) := by
    have h₁ := (Real.tendsto_log_comp_add_sub_log (Real.log k)).div_atTop tendsto_id
    have h₂ := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    convert h₁.add h₂ using 1
    · ext x
      simp only [id_eq]
      ring
    · norm_num
  have hll : Tendsto (fun N : ℕ => Real.log (Real.log ((k : ℝ) * N)) / Real.log N)
      atTop (𝓝 0) := by
    apply (hshift.comp hlog).congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [Real.log_mul hkR.ne' hn.ne', add_comm]
    rfl
  have ht : Tendsto (fun N : ℕ =>
      (2 * k * k * C * Real.log (Real.log ((k : ℝ) * N))) / Real.log N) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hll.const_mul (2 * k * k * C)
  obtain ⟨Nlim, hlim⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max Nlim (max 8 (2 ^ k)), fun N hN => ?_⟩
  have hN8 : 8 ≤ N := by omega
  have hNk : 2 ^ k ≤ N := by omega
  have hLk : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) hNk
  have hkN : k ≤ N := (Nat.lt_pow_self (by norm_num : 1 < (2 : ℕ))).le.trans hNk
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let T := (univ : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N))).filter
    (fun x => (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)|)
  let B : ℝ := C * Real.log (Real.log ((k : ℝ) * N))
  have hkn3 : 3 ≤ k * N := by nlinarith
  have hB : 0 ≤ B := by
    have hh := (LeanLab.Romanov.Decomp134b.loglog_pos (k * N) hkn3).le
    simp only [Nat.cast_mul] at hh
    exact mul_nonneg hC.le hh
  have hw (x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) (hx : x ∈ T) :
      ((LeanLab.Linnik.Decomp1532a.dif x).natAbs : ℝ) / (LeanLab.Linnik.Decomp1532a.dif x).natAbs.totient ≤ B := by
    have hxR : (N : ℝ) < ((LeanLab.Linnik.Decomp1532a.dif x).natAbs : ℝ) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (mem_filter.mp hx).2
    have hm : N < (LeanLab.Linnik.Decomp1532a.dif x).natAbs := by exact_mod_cast hxR
    have hm3 : 3 ≤ (LeanLab.Linnik.Decomp1532a.dif x).natAbs := by omega
    have hmN := LeanLab.Linnik.Decomp466b.difference_le (by omega : 1 ≤ N) x
    have hlogm : 0 < Real.log ((LeanLab.Linnik.Decomp1532a.dif x).natAbs : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < (LeanLab.Linnik.Decomp1532a.dif x).natAbs by omega))
    have hmR : ((LeanLab.Linnik.Decomp1532a.dif x).natAbs : ℝ) ≤ (k : ℝ) * N := by exact_mod_cast hmN
    have hllm : Real.log (Real.log ((LeanLab.Linnik.Decomp1532a.dif x).natAbs : ℝ)) ≤
        Real.log (Real.log ((k : ℝ) * N)) :=
      Real.log_le_log hlogm (Real.log_le_log (by positivity) hmR)
    exact (hφ _ hm3).trans (mul_le_mul_of_nonneg_left hllm hC.le)
  have hsum : (∑ x ∈ T, ((LeanLab.Linnik.Decomp1532a.dif x).natAbs : ℝ) / (LeanLab.Linnik.Decomp1532a.dif x).natAbs.totient) ≤ (T.card : ℝ) * B := by
    calc
      _ ≤ ∑ x ∈ T, B := sum_le_sum hw
      _ = _ := by simp
  have hcard : (T.card : ℝ) ≤ 2 * k * k * (Nat.log 2 N : ℝ) ^ (2 * k - 1) := by
    simpa only [T, Fintype.card_subtype] using
      large_shift_tuple_count_log (k := k)
        (Nat.lt_pow_self (by norm_num : 1 < (2 : ℕ))).le hLk (by omega : 1 ≤ N)
  have hcoef : 2 * k * k * C * Real.log (Real.log ((k : ℝ) * N)) ≤
      δ * (Nat.log 2 N : ℝ) := by
    have hh := (div_lt_iff₀ hln).mp (hlim N (by omega))
    have hL := LeanLab.Linnik.U7206.log_le_L hN8
    nlinarith
  have hpow : (Nat.log 2 N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 1) =
      (Nat.log 2 N : ℝ) ^ (2 * k) := by
    rw [← pow_succ']
    congr 1
    omega
  calc
    _ ≤ (T.card : ℝ) * B := hsum
    _ ≤ (2 * k * k * (Nat.log 2 N : ℝ) ^ (2 * k - 1)) * B :=
      mul_le_mul_of_nonneg_right hcard hB
    _ = (2 * k * k * C * Real.log (Real.log ((k : ℝ) * N))) *
        (Nat.log 2 N : ℝ) ^ (2 * k - 1) := by dsimp [B]; ring
    _ ≤ (δ * (Nat.log 2 N : ℝ)) * (Nat.log 2 N : ℝ) ^ (2 * k - 1) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by rw [mul_assoc, hpow]

/-- Gallagher 1975. P0094 p.127 definition of J in Theorem 3, p.134 display 3 and p.138 before display 5. This is a support identity, not a major arc error estimate.
The singular main sum in the sealed large shift leaf is zero for every k, N and theta. Each summand has J equal to zero outside its interval support.
AI wrote the Lean code. Goldbach is open. -/
theorem large_shift_main_sum_eq_zero (k N : ℕ) (θ : ℝ) :
    (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
      LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
        ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)),
      LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
        (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re) = 0 := by
  classical
  apply sum_eq_zero
  intro x hx
  have hn : (N : ℝ) < |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| :=
    lt_of_not_ge (mem_filter.mp hx).2.2.2
  rw [Jn_eq_zero_of_large_shift N _ hn, zero_mul]

/-- LEAF, OPEN. First range only. Tuple differences no larger than the major arc scale
`P = N ^ θ`, so `|dif x| ≤ N ^ θ`. The averaged correlation error with both sums restricted to
those tuples is at most a third of the target budget once `N` is large. This is one step of the
target: it is the part of the signed difference carried by the short shifts, with the full tuple
average still in place. -/
theorem split_small_shift_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ,
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  sorry

/-- LEAF, OPEN. Second range only. Tuple differences above the major arc scale but no larger than
`N`: `N ^ θ < |dif x| ≤ N`. The averaged correlation error with both sums restricted to those
tuples is at most a third of the target budget once `N` is large. This is one step of the target:
it is the part of the signed difference carried by the intermediate shifts. -/
theorem split_intermediate_shift_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  sorry

/-- LEAF, OPEN. Third range only. Tuple differences larger than `N` in absolute value. The
averaged correlation error with both sums restricted to those tuples is at most a third of the
target budget once `N` is large. This is one step of the target: it is the part of the signed
difference carried by the long shifts, where the shift exceeds the summation range itself. -/
theorem split_large_shift_bound :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 4 → ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ →
      ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
        |(∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)),
            ∫ α in majorArcs N ((N : ℝ) ^ θ),
              ‖Sg N α‖ ^ 2 *
                (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re) -
          (∑ x : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) with
            LeanLab.Linnik.Decomp1532a.dif x ≠ 0 ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ) ∧
              ¬(|(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)),
              LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
                (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re)| ≤
          (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 3) := by
  sorry

/-- ASSEMBLY. The sealed statement `Display5PlainExpansion`, from the three range leaves: split the
tuple sum by the size of `dif x`, apply each leaf to its range and add the three bounds. The
constant `θ₀ = 1/4` is the witness, and no `sorry` is used. -/
theorem display5_plain_expansion_split : Display5PlainExpansion := by
  classical
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro θ hθ hθ4 k hk δ hδ
  obtain ⟨N₁, h₁⟩ := split_small_shift_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₂, h₂⟩ := split_intermediate_shift_bound θ hθ hθ4 k hk δ hδ
  obtain ⟨N₃, h₃⟩ := split_large_shift_bound θ hθ hθ4 k hk δ hδ
  refine ⟨max (max N₁ N₂) N₃, ?_⟩
  intro N hN
  have hN₁ : N₁ ≤ N :=
    le_trans (le_trans (le_max_left N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₂ : N₂ ≤ N :=
    le_trans (le_trans (le_max_right N₁ N₂) (le_max_left (max N₁ N₂) N₃)) hN
  have hN₃ : N₃ ≤ N := le_trans (le_max_right (max N₁ N₂) N₃) hN
  let T : Finset (LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N)) :=
    Finset.univ.filter (fun x => LeanLab.Linnik.Decomp1532a.dif x ≠ 0)
  let g : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖Sg N α‖ ^ 2 *
        (LeanLab.PNTPort.LargeSieve.e ((LeanLab.Linnik.Decomp1532a.dif x : ℝ) * α)).re
  let w : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ := fun x =>
    LeanLab.Linnik.Decomp1532b.Jn N (LeanLab.Linnik.Decomp1532a.dif x) *
      (LeanLab.Linnik.Decomp1532b.singSeries (LeanLab.Linnik.Decomp1532a.dif x)).re
  let M : ℝ := 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  let p1 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ θ
  let p2 : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → Prop := fun x =>
    |(LeanLab.Linnik.Decomp1532a.dif x : ℝ)| ≤ (N : ℝ)
  have H₁ : |(T.filter p1).sum g - (T.filter p1).sum w| ≤ M * (δ / 3) := by
    simpa only [T, g, w, M, p1, Finset.filter_filter] using h₁ N hN₁
  have H₂ : |((T.filter (fun x => ¬ p1 x)).filter p2).sum g -
      ((T.filter (fun x => ¬ p1 x)).filter p2).sum w| ≤ M * (δ / 3) := by
    simpa only [T, g, w, M, p1, p2, Finset.filter_filter] using h₂ N hN₂
  have H₃ : |((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum g -
      ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum w| ≤ M * (δ / 3) := by
    simpa only [T, g, w, M, p1, p2, Finset.filter_filter] using h₃ N hN₃
  have hsplit : ∀ F : LeanLab.Linnik.Decomp1532a.pairs k (Nat.log 2 N) → ℝ,
      T.sum F = (T.filter p1).sum F
        + ((T.filter (fun x => ¬ p1 x)).filter p2).sum F
        + ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum F := by
    intro F
    have e1 : (T.filter p1).sum F + (T.filter (fun x => ¬ p1 x)).sum F = T.sum F :=
      Finset.sum_filter_add_sum_filter_not T p1 F
    have e2 : ((T.filter (fun x => ¬ p1 x)).filter p2).sum F +
        ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum F =
        (T.filter (fun x => ¬ p1 x)).sum F :=
      Finset.sum_filter_add_sum_filter_not (T.filter (fun x => ¬ p1 x)) p2 F
    linarith
  have hA := hsplit g
  have hB := hsplit w
  have key : |T.sum g - T.sum w| ≤ M * δ := by
    have step : T.sum g - T.sum w =
        ((T.filter p1).sum g - (T.filter p1).sum w)
          + ((((T.filter (fun x => ¬ p1 x)).filter p2).sum g -
              ((T.filter (fun x => ¬ p1 x)).filter p2).sum w)
            + (((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum g -
              ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum w)) := by
      rw [hA, hB]; ring
    rw [step]
    have t1 := abs_add_le ((T.filter p1).sum g - (T.filter p1).sum w)
      ((((T.filter (fun x => ¬ p1 x)).filter p2).sum g -
          ((T.filter (fun x => ¬ p1 x)).filter p2).sum w)
        + (((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum g -
          ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum w))
    have t2 := abs_add_le
      (((T.filter (fun x => ¬ p1 x)).filter p2).sum g -
        ((T.filter (fun x => ¬ p1 x)).filter p2).sum w)
      (((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum g -
        ((T.filter (fun x => ¬ p1 x)).filter (fun x => ¬ p2 x)).sum w)
    have hb₁ := H₁
    have hb₂ := H₂
    have hb₃ := H₃
    linarith
  simpa only [T, g, w, M] using key
