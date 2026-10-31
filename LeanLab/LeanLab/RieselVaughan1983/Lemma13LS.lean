/-
P0032 Riesel-Vaughan 1983, Lemma 13, pages 64 to 66, WITHOUT the Montgomery-Vaughan inputs.
Unit U-6713, CLOUD 20261020T1816Z-cloud48, track T1. AI-written Lean code, Claude. Checked only
by the Lean kernel. Binary Goldbach is OPEN.

The paper derives (8.18) from Montgomery-Vaughan's weighted large sieve (8.17), `Page65.Eq817`,
and their Lemmas 3 and 8, `Page65.MVLemma38`. Here both are replaced by results the lab proves:
* the large sieve at Farey fractions with constant `N + 2Q²`,
  `LeanLab.PNTPort.LargeSieve.farey_large_sieve`, at the level `Q = z/10`, `z = (2N_k/3)^{1/2}`
  of (8.6), so `Q² = N_k/150` and `N_k + 2Q² = (76/75) N_k`;
* `MuPhi.log_sub_log_two_le_mSum`, `log(Q/r) − log 2 ≤ r/φ(r) Σ_{m ≤ Q/r, (m,r)=1} μ²(m)/φ(m) ·
  1/(1 + rm/Q)`, the elementary form of MV Lemmas 3 and 8 with `0.361` replaced by `−log 2`;
* the generic page 65 machinery `Page65.weighted_char_le`, applied with the auxiliary length
  `N' = 3Q²/2`, which turns the unweighted Farey bound into the needed weighted one.
The price is a weaker Lemma 13: the coefficient of `N_k` is `76/75` instead of `1`, and the
constant `2.9024` becomes `10`, since `log 15000 < 10`:
  Φ_k ≥ ½ C (16/15 S_k² − 2 S_k ((76/75) N_k − S_k log 5)/(15(log N_k − 10))).
Section 9 still closes with these constants, see Section9LS.lean, value 6.9 against 6.7 needed;
every numerical step is checked in Lean there, no outside computation is used.

What is here.
PROVED unconditional:
* `addSq_sieve`: for a finite set `P` of naturals inside `(M, M + N]` and `Q ≥ 1`,
  `Σ_{q ≤ Q} Σ_{(a,q)=1} |Σ_{p ∈ P} e(ap/q)|² ≤ (N + 2Q²) #P`, from `farey_large_sieve`.
* `char_sieve`: the last display of page 65 at level `Q = z/10` with the unweighted sieve,
  `Σ_{r ≤ Q} r/φ(r) mSum(r, Q) Σ*_{χ mod r}|S_k(χ)|² ≤ (N_k + 2Q²) S_k`.
* `eq818LS`: the analogue of (8.18) with `Z = z/20`,
  `Σ_{5 ≤ r ≤ w} log(Z/r) Σ*_{χ mod r}|S_k(χ)|² ≤ (N_k + 2Q²) S_k − S_k² log Z`.
* `lemma13_max0`: `f(q)/log(Z/q) ≤ f(5)/log(Z/5)` for natural `5 ≤ q ≤ Z/5`, `log Z ≥ 5`.
* `lemma13LS`: `Lemma13LSP`, Lemma 13 with the constants above, for the partial sums of (8.10).
* `lemma12and13LS_of`, `lemma11to13LS_of`, `lemma14LSP_of`: the existing chain from Lemma 13
  to Lemma 14 copied with the new constants; Lemma 14 becomes `Lemma14LSP`,
  `Ψ_k ≥ (C/15)((8 + log 5/log y) S_k² − (y/log y)(76/75 + 10.5/log y) S_k)`.
* `lemma14LS`: `Lemma14LSP` with no hypothesis at all.
No Montgomery-Vaughan input, no sorry. KNOWN mathematics; the route is the paper's with the
standard Farey large sieve in place of the weighted one.
-/
import LeanLab.RieselVaughan1983.MuPhiSum
import LeanLab.PNTPort.LargeSieve.Farey

open Finset Real
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.RieselVaughan1983.Lemma13LS

open LeanLab.RieselVaughan1983.Page65 LeanLab.RieselVaughan1983.Lemma13Red
  LeanLab.RieselVaughan1983.Delta LeanLab.RieselVaughan1983.Xi
  LeanLab.RieselVaughan1983.Eq816 LeanLab.RieselVaughan1983.Theta

local notation "LSe" => LeanLab.PNTPort.LargeSieve.e

/-! ### The Farey large sieve for a finite set of naturals -/

lemma sum_zmod_eq_sum_range' {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M]
    (f : ZMod q → M) : ∑ x : ZMod q, f x = ∑ c ∈ range q, f (c : ZMod q) := by
  refine sum_nbij' (fun x => x.val) (fun c => (c : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro x _; rw [mem_range]; exact ZMod.val_lt x
  · intro c _; exact mem_coe.2 (mem_univ _)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro c hc; rw [mem_range] at hc; exact ZMod.val_natCast_of_lt hc
  · intro x _; rw [ZMod.natCast_zmod_val]

lemma stdAddChar_eq {q : ℕ} [NeZero q] (c p : ℕ) :
    ZMod.stdAddChar ((c : ZMod q) * (p : ZMod q)) = LSe (((p : ℤ) : ℝ) * ((c : ℝ) / q)) := by
  rw [show (c : ZMod q) * (p : ZMod q) = (((p : ℤ) * c : ℤ) : ZMod q) by push_cast; ring,
    ZMod.stdAddChar_coe]
  unfold LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

lemma addSq_nonneg (P : Finset ℕ) (q : ℕ) : 0 ≤ addSq P q := by
  unfold addSq; split_ifs
  · exact sum_nonneg fun _ _ => sq_nonneg _
  · exact le_rfl

/-- `addSq` as a sum over `0 ≤ c < q`, `(c, q) = 1`. -/
lemma addSq_eq_range (P : Finset ℕ) {q : ℕ} (hq : q ≠ 0) :
    addSq P q = ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q),
      ‖∑ p ∈ P, LSe (((p : ℤ) : ℝ) * ((c : ℝ) / q))‖ ^ 2 := by
  have : NeZero q := ⟨hq⟩
  unfold addSq
  rw [dif_pos hq, sum_filter, sum_zmod_eq_sum_range', sum_filter]
  refine sum_congr rfl fun c _ => ?_
  by_cases h : c.Coprime q
  · rw [if_pos ((ZMod.isUnit_iff_coprime c q).2 h), if_pos h]
    simp only [stdAddChar_eq]
  · rw [if_neg (fun h' => h ((ZMod.isUnit_iff_coprime c q).1 h')), if_neg h]

/-- **The Farey large sieve for a finite set of naturals**: for `P ⊆ (M, M + N]` and `Q ≥ 1`,
`Σ_{q ≤ Q} Σ_{(a, q) = 1} |Σ_{p ∈ P} e(ap/q)|² ≤ (N + 2Q²) #P`. -/
theorem addSq_sieve (P : Finset ℕ) (M : ℤ) (N : ℕ)
    (hP : ∀ p ∈ P, M < (p : ℤ) ∧ (p : ℤ) ≤ M + N) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Icc 1 Q, addSq P q ≤ (N + 2 * (Q : ℝ) ^ 2) * (#P : ℝ) := by
  set I := Ioc M (M + N)
  set Pim : Finset ℤ := P.image (fun p : ℕ => (p : ℤ)) with hPim
  have hsub : Pim ⊆ I := by
    intro n hn
    rw [hPim, mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    rw [mem_Ioc]; exact hP p hp
  set a : ℤ → ℂ := fun n => if n ∈ Pim then 1 else 0 with ha
  have hinj : Set.InjOn (fun p : ℕ => (p : ℤ)) (P : Set ℕ) :=
    fun p _ p' _ h => by simp only at h; exact_mod_cast h
  have hsum : ∀ f : ℤ → ℂ, ∑ n ∈ I, a n * f n = ∑ p ∈ P, f p := by
    intro f
    have : ∑ n ∈ I, a n * f n = ∑ n ∈ I, if n ∈ Pim then f n else 0 := by
      refine sum_congr rfl fun n _ => ?_
      simp only [ha]; split_ifs <;> simp
    rw [this, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hsub, hPim,
      sum_image hinj]
  have hnorm : ∑ n ∈ I, ‖a n‖ ^ 2 = (#P : ℝ) := by
    have : ∑ n ∈ I, ‖a n‖ ^ 2 = ∑ n ∈ I, if n ∈ Pim then (1 : ℝ) else 0 := by
      refine sum_congr rfl fun n _ => ?_
      simp only [ha]; split_ifs <;> simp
    rw [this, sum_boole, filter_mem_eq_inter, inter_eq_right.mpr hsub, hPim,
      card_image_of_injOn hinj]
  set f : ℕ × ℕ → ℝ := fun x =>
    ‖∑ n ∈ I, a n * LSe (n * LeanLab.PNTPort.LargeSieve.fareyPt x)‖ ^ 2 with hf
  have h1 : ∑ q ∈ Icc 1 Q, addSq P q =
      ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), f (q, c) := by
    refine sum_congr rfl fun q hq => ?_
    rw [mem_Icc] at hq
    rw [addSq_eq_range P (by omega)]
    refine sum_congr rfl fun c _ => ?_
    simp only [hf, LeanLab.PNTPort.LargeSieve.fareyPt]
    rw [hsum]
  set T : Finset (ℕ × ℕ) := (Icc 1 Q).biUnion (fun q =>
    ((range q).filter (fun c => Nat.Coprime c q)).map
      ⟨fun c => (q, c), fun c c' h => by simpa using h⟩) with hT
  have h2 : ∑ q ∈ Icc 1 Q, ∑ c ∈ (range q).filter (fun c => Nat.Coprime c q), f (q, c) =
      ∑ x ∈ T, f x := by
    rw [hT, sum_biUnion]
    · refine sum_congr rfl fun q _ => ?_
      rw [sum_map]; rfl
    · intro q _ q' _ hne
      refine disjoint_left.2 ?_
      intro x hx hx'
      simp only [mem_map] at hx hx'
      obtain ⟨c, _, rfl⟩ := hx
      obtain ⟨c', _, h⟩ := hx'
      exact hne (congrArg Prod.fst h).symm
  have hTsub : T ⊆ LeanLab.PNTPort.LargeSieve.farey Q := by
    intro x hx
    rw [hT, mem_biUnion] at hx
    obtain ⟨q, hq, hx⟩ := hx
    rw [mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [mem_filter, mem_range] at hc
    rw [mem_Icc] at hq
    rw [LeanLab.PNTPort.LargeSieve.mem_farey]
    exact ⟨hq.1, hq.2, hc.1, hc.2⟩
  have h3 : ∑ x ∈ T, f x ≤ ∑ x ∈ LeanLab.PNTPort.LargeSieve.farey Q, f x :=
    sum_le_sum_of_subset_of_nonneg hTsub (fun _ _ _ => by positivity)
  have h4 := LeanLab.PNTPort.LargeSieve.farey_large_sieve hQ a M N
  rw [hnorm] at h4
  rw [h1, h2]
  exact h3.trans h4

/-! ### The paper's objects at the level `Q = z/10` -/

/-- The sieve level `Q = z/10`, `z = (2N_k/3)^{1/2}` of (8.6). -/
def Qs (y : ℝ) (k : ℕ) : ℝ := zk y k / 10

/-- The centre of the logarithms, `Z = Q/2 = z/20`. -/
def Zs (y : ℝ) (k : ℕ) : ℝ := zk y k / 20

/-- The primes of `I_k` lie in `(⌊ky/2⌋, ⌊ky/2⌋ + N_k]`. -/
lemma Pset_window (y : ℝ) (k : ℕ) (hy : 0 ≤ y) :
    ∀ p ∈ Xi.Pset y k, ((⌊(k : ℝ) * y / 2⌋₊ : ℕ) : ℤ) < (p : ℤ) ∧
      (p : ℤ) ≤ ((⌊(k : ℝ) * y / 2⌋₊ : ℕ) : ℤ) +
        ((⌊(k : ℝ) * y / 2 + y⌋₊ - ⌊(k : ℝ) * y / 2⌋₊ : ℕ) : ℤ) := by
  intro p hp
  set a := (k : ℝ) * y / 2 with ha_def
  have ha : 0 ≤ a := by positivity
  have hAB : ⌊a⌋₊ ≤ ⌊a + y⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Xi.Pset, mem_filter, mem_range] at hp
  have h1 : ⌊a⌋₊ < p := (Nat.floor_lt ha).mpr hp.2.2.1
  have h2 : p ≤ ⌊a + y⌋₊ := by
    have := hp.1
    show p ≤ ⌊(k : ℝ) * y / 2 + y⌋₊
    omega
  constructor
  · exact_mod_cast h1
  · have : ⌊a⌋₊ + (⌊a + y⌋₊ - ⌊a⌋₊) = ⌊a + y⌋₊ := by omega
    have h3 : p ≤ ⌊a⌋₊ + (⌊a + y⌋₊ - ⌊a⌋₊) := by omega
    exact_mod_cast h3

lemma Nk_eq_cast (y : ℝ) (k : ℕ) (hy : 0 ≤ y) :
    (((⌊(k : ℝ) * y / 2 + y⌋₊ - ⌊(k : ℝ) * y / 2⌋₊ : ℕ) : ℝ)) = Nk y k := by
  have hAB : ⌊(k : ℝ) * y / 2⌋₊ ≤ ⌊(k : ℝ) * y / 2 + y⌋₊ := Nat.floor_le_floor (by linarith)
  rw [Nat.cast_sub hAB]; rfl

/-- **The large sieve for the primes of `I_k`** at an integer level `Q ≥ 1`:
`Σ_{q ≤ Q} Σ_{(a,q)=1} |S(a/q)|² ≤ (N_k + 2Q²) S_k`. -/
theorem pset_sieve (y : ℝ) (k : ℕ) (hy : 0 ≤ y) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Icc 1 Q, addSq (Xi.Pset y k) q ≤ (Nk y k + 2 * (Q : ℝ) ^ 2) * Sk y k := by
  have h := addSq_sieve (Xi.Pset y k) _ _ (Pset_window y k hy) hQ
  rwa [Nk_eq_cast y k hy, card_Pset_eq y k hy] at h

lemma Qs_facts {y : ℝ} {k : ℕ} (hy : 10 ^ 7 ≤ y) :
    50 ≤ Qs y k ∧ Qs y k ^ 2 = Nk y k / 150 ∧ wk y k ≤ Qs y k := by
  obtain ⟨hz, hz2, hz5⟩ := z_facts (k := k) hy
  refine ⟨by unfold Qs; linarith, by unfold Qs; rw [div_pow, hz2]; ring, ?_⟩
  rw [wk_eq]; unfold Qs; linarith

/-- **The last display of page 65 at level `Q = z/10`, unweighted sieve**, PROVED:
`Σ_{r ≤ Q} r/φ(r) mSum(r, Q) Σ*_{χ mod r}|S_k(χ)|² ≤ (N_k + 2Q²) S_k`. The weighted machinery
`weighted_char_le` is applied with the auxiliary length `N' = 3Q²/2`, so that `z = Q` there, and
its hypothesis follows from the Farey sieve since `(N' + 3qQ/2)⁻¹ ≤ N'⁻¹`. -/
theorem char_sieve {y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 10 ^ 7 ≤ y) :
    ∑ r ∈ Icc 1 ⌊Qs y k⌋₊, (r : ℝ) / r.totient * mSum r (Qs y k) * Qr y k r ≤
      (Nk y k + 2 * Qs y k ^ 2) * Sk y k := by
  obtain ⟨hQ50, hQ2, _⟩ := Qs_facts (k := k) hy
  obtain ⟨hz, _, _⟩ := z_facts (k := k) hy
  set Q := Qs y k with hQdef
  have hQ0 : 0 < Q := by linarith
  set N' := 3 / 2 * Q ^ 2 with hN'
  have hN'0 : 0 < N' := by positivity
  have hS0 : 0 ≤ Sk y k := Sk_nonneg y k (by linarith)
  have hN0 : 0 ≤ Nk y k := by obtain ⟨h1, _⟩ := Nk_bounds y k (by linarith); linarith
  set S' := (Nk y k + 2 * Q ^ 2) * Sk y k / N' with hS'
  have hfl1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hflQ : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hP : ∀ p ∈ Xi.Pset y k, ∀ q ∈ Icc 1 ⌊Q⌋₊, p.Coprime q := by
    intro p hp q hq
    apply Pset_coprime hk hy p hp q
    rw [mem_Icc] at hq ⊢
    refine ⟨hq.1, hq.2.trans (Nat.floor_le_floor ?_)⟩
    rw [hQdef, Qs]; linarith
  have h817 : ∑ q ∈ Icc 1 ⌊Q⌋₊, (N' + 3 / 2 * q * Q)⁻¹ * addSq (Xi.Pset y k) q ≤ S' := by
    calc ∑ q ∈ Icc 1 ⌊Q⌋₊, (N' + 3 / 2 * q * Q)⁻¹ * addSq (Xi.Pset y k) q
        ≤ ∑ q ∈ Icc 1 ⌊Q⌋₊, N'⁻¹ * addSq (Xi.Pset y k) q := by
          refine sum_le_sum fun q _ => mul_le_mul_of_nonneg_right ?_ (addSq_nonneg _ _)
          have : (0 : ℝ) ≤ 3 / 2 * q * Q := by positivity
          exact inv_anti₀ hN'0 (by linarith)
      _ = N'⁻¹ * ∑ q ∈ Icc 1 ⌊Q⌋₊, addSq (Xi.Pset y k) q := by rw [mul_sum]
      _ ≤ N'⁻¹ * ((Nk y k + 2 * (⌊Q⌋₊ : ℝ) ^ 2) * Sk y k) :=
          mul_le_mul_of_nonneg_left (pset_sieve y k (by linarith) hfl1) (by positivity)
      _ ≤ N'⁻¹ * ((Nk y k + 2 * Q ^ 2) * Sk y k) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hS0
          have : (⌊Q⌋₊ : ℝ) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hflQ 2
          linarith
      _ = S' := by rw [hS']; ring
  have h := weighted_char_le (Xi.Pset y k) hQ0 (N := N') (by rw [hN']; ring) hP h817
  have e : S' * N' = (Nk y k + 2 * Q ^ 2) * Sk y k := by rw [hS']; field_simp
  rw [e] at h
  exact h

/-- `log(Z/r) = log(Q/r) − log 2`. -/
lemma log_Zs (y : ℝ) (k : ℕ) {r : ℝ} (hr : 0 < r) (hz : 0 < zk y k) :
    Real.log (Zs y k / r) = -Real.log 2 + Real.log (Qs y k / r) := by
  rw [show Zs y k / r = Qs y k / r / 2 by unfold Zs Qs; ring,
    Real.log_div (by unfold Qs; positivity) two_ne_zero]
  ring

/-- **(8.18) at level `Q = z/10`**, PROVED unconditional: with `Z = z/20`, `w` of (8.6),
`Σ_{5 ≤ r ≤ w} log(Z/r) Σ*_{χ mod r}|S_k(χ)|² ≤ (N_k + 2Q²) S_k − S_k² log Z`. -/
theorem eq818LS {y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hy : 10 ^ 7 ≤ y) :
    ∑ r ∈ Icc 5 ⌊wk y k⌋₊, Real.log (Zs y k / r) * Qr y k r ≤
      (Nk y k + 2 * Qs y k ^ 2) * Sk y k - Sk y k ^ 2 * Real.log (Zs y k) := by
  obtain ⟨hQ50, _, hwQ⟩ := Qs_facts (k := k) hy
  obtain ⟨hz, _, _⟩ := z_facts (k := k) hy
  have hmain := char_sieve hk hy
  set Q := Qs y k with hQdef
  have hQ0 : 0 < Q := by linarith
  set c : ℕ → ℝ := fun r => (r : ℝ) / r.totient * mSum r Q with hc
  have hc0 : ∀ r, 0 ≤ c r := fun r =>
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mSum_nonneg r hQ0.le)
  have hlow : ∀ r : ℕ, 1 ≤ r → Real.log (Zs y k / r) ≤ c r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    rw [log_Zs y k hr0 hz]
    have := MuPhi.log_sub_log_two_le_mSum r hr Q hQ0
    simp only [hc]; linarith
  set W := ⌊wk y k⌋₊ with hWdef
  set Z := ⌊Q⌋₊ with hZdef
  have hw0 : 0 ≤ wk y k := by rw [wk_eq]; linarith
  have hWZ : W ≤ Z := Nat.floor_le_floor hwQ
  have h1Z : 1 ≤ Z := Nat.le_floor (by push_cast; linarith)
  have hsub : insert 1 (Icc 5 W) ⊆ Icc 1 Z := by
    intro r hr
    rw [mem_insert, mem_Icc] at hr
    rw [mem_Icc]
    rcases hr with rfl | hr
    · exact ⟨le_rfl, h1Z⟩
    · omega
  have hnot : 1 ∉ Icc 5 W := by simp
  have hle := sum_le_sum_of_subset_of_nonneg hsub (f := fun r => c r * Qr y k r)
    (fun r _ _ => mul_nonneg (hc0 r) (Qr_nonneg y k r))
  rw [sum_insert hnot] at hle
  have h1 : Sk y k ^ 2 * Real.log (Zs y k) ≤ c 1 * Qr y k 1 := by
    rw [Qr_one y k (by linarith)]
    have := hlow 1 le_rfl
    simp only [Nat.cast_one, div_one] at this
    nlinarith [sq_nonneg (Sk y k)]
  have hr : ∑ r ∈ Icc 5 W, Real.log (Zs y k / r) * Qr y k r ≤
      ∑ r ∈ Icc 5 W, c r * Qr y k r := by
    refine sum_le_sum fun r hr => mul_le_mul_of_nonneg_right ?_ (Qr_nonneg y k r)
    rw [mem_Icc] at hr
    exact hlow r (by omega)
  have hmain' : ∑ r ∈ Icc 1 Z, c r * Qr y k r ≤ (Nk y k + 2 * Q ^ 2) * Sk y k := hmain
  linarith

/-! ### The maximisation on page 66 with `a = 0` and `q ≤ Z/5` -/

lemma one_lt_log5 : 1 < Real.log 5 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

/-- `7 log(Z/7) ≤ q log(Z/q)` for `7 ≤ q ≤ Z/5`, since `t log(Z/t)` increases while `Z/t ≥ e`. -/
theorem incr0 {z q : ℝ} (hq : 7 ≤ q) (hqz : q ≤ z / 5) :
    7 * Real.log (z / 7) ≤ q * Real.log (z / q) := by
  have hq0 : 0 < q := by linarith
  have hz0 : 0 < z := by linarith
  have hl : Real.log (q / 7) ≤ q / 7 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hq0.ne' (by norm_num)] at hl
  have h5 : Real.log 5 ≤ Real.log (z / q) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hq0]; linarith
  have hl5 := one_lt_log5
  rw [Real.log_div hz0.ne' hq0.ne'] at h5
  rw [Real.log_div hz0.ne' (by norm_num), Real.log_div hz0.ne' hq0.ne']
  have key : 7 * (Real.log q - Real.log 7) ≤ q - 7 := by linarith
  nlinarith

/-- `(1/3)/(7 log(Z/7)) < (1/15)/log(Z/5)` once `log Z ≥ 5`. -/
theorem seven_lt_five0 {z : ℝ} (hz : 5 ≤ Real.log z) :
    1 / 3 / (7 * Real.log (z / 7)) < 1 / 15 / Real.log (z / 5) := by
  have hz0 : z ≠ 0 := by rintro rfl; rw [Real.log_zero] at hz; linarith
  rw [Real.log_div hz0 (by norm_num), Real.log_div hz0 (by norm_num)]
  have he1 := Real.exp_one_gt_d9
  have hE2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have h7 : Real.log 7 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), hE2]
    have : (2.7182818283 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he1.le 2
    have : (7 : ℝ) < (2.7182818283 : ℝ) ^ 2 := by norm_num
    linarith
  have h5 : 1 < Real.log 5 := one_lt_log5
  have h7' : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h5' : Real.log 5 < Real.log 7 := Real.log_lt_log (by norm_num) (by norm_num)
  have hA : 0 < Real.log z - Real.log 7 := by linarith
  have hB : 0 < Real.log z - Real.log 5 := by linarith
  rw [div_div, div_lt_div_iff₀ (by positivity) hB]
  nlinarith

/-- **Page 66's maximisation with `a = 0`**: for natural `5 ≤ q ≤ Z/5` and `log Z ≥ 5`,
`f(q)/log(Z/q) ≤ f(5)/log(Z/5)`. -/
theorem lemma13_max0 {z : ℝ} (hz : 5 ≤ Real.log z) {q : ℕ} (h5 : 5 ≤ q)
    (hqz : (q : ℝ) ≤ z / 5) :
    Lemma13Max.fq q / Real.log (z / q) ≤ Lemma13Max.fq 5 / Real.log (z / 5) := by
  have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast h5
  have hz0 : 0 < z := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hl5 := one_lt_log5
  have hden : 0 < Real.log (z / q) := by
    have : Real.log 5 ≤ Real.log (z / q) := by
      apply Real.log_le_log (by norm_num); rw [le_div_iff₀ hq0]; linarith
    linarith
  have hz5 : 0 < Real.log (z / 5) := by
    have : Real.log 5 ≤ Real.log (z / 5) := by
      apply Real.log_le_log (by norm_num); rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  rw [Lemma13Max.fq_five]
  rcases Nat.lt_or_ge q 7 with h | h
  · interval_cases q
    · norm_num [Lemma13Max.fq_five]
    · have : Lemma13Max.fq 6 = 0 := by unfold Lemma13Max.fq; rw [if_neg (by decide)]
      rw [this, zero_div]
      positivity
  · by_cases hos : Odd q ∧ Squarefree q
    · have hf := Lemma13Max.fq_mul_le h hos.1 hos.2
      have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast h
      have hinc := incr0 (z := z) (q := q) hq7 hqz
      have hlt := seven_lt_five0 hz
      have h7pos : 0 < 7 * Real.log (z / 7) := by
        have : Real.log 5 ≤ Real.log (z / 7) := by
          apply Real.log_le_log (by norm_num); rw [le_div_iff₀ (by norm_num)]; linarith
        linarith
      have hfq0 := Lemma13Max.fq_nonneg q
      have step : Lemma13Max.fq q / Real.log (z / q) ≤ 1 / 3 / (7 * Real.log (z / 7)) := by
        rw [div_le_div_iff₀ hden h7pos]
        have e : Lemma13Max.fq q * (7 * Real.log (z / 7)) ≤
            Lemma13Max.fq q * (q * Real.log (z / q)) :=
          mul_le_mul_of_nonneg_left hinc hfq0
        have e3 : (q * Lemma13Max.fq q) * Real.log (z / q) ≤ 1 / 3 * Real.log (z / q) :=
          mul_le_mul_of_nonneg_right hf hden.le
        nlinarith
      linarith
    · have : Lemma13Max.fq q = 0 := by unfold Lemma13Max.fq; rw [if_neg hos]
      rw [this, zero_div]
      positivity

/-! ### Lemma 13 with the new constants -/

/-- **Lemma 13 at level `Q = z/10`**, the statement: as `Lemma12Delta.Lemma13P` with
`N_k` replaced by `(76/75) N_k` and `2.9024` by `10`. -/
def Lemma13LSP : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200, ∀ ε : ℝ, 0 < ε →
    ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
      1 / 2 * Ctw * (16 / 15 * Sk (x / 202) k ^ 2 -
        2 * Sk (x / 202) k * (76 / 75 * Nk (x / 202) k - Sk (x / 202) k * Real.log 5) /
          (15 * (-10 + Real.log (Nk (x / 202) k)))) - ε ≤
        (PhiD (x / 202) k (wk (x / 202) k) D).re

lemma log100_lt : Real.log 100 < 4.61 := by
  have h5 := log5_lt
  have h2 := Real.log_two_lt_d9
  have e : Real.log 100 = 2 * Real.log 2 + 2 * Real.log 5 := by
    rw [show (100 : ℝ) = 2 ^ 2 * 5 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]; push_cast; ring
  rw [e]; norm_num at h2 h5 ⊢; linarith

/-- **Lemma 13 with `(76/75) N_k` and `10`**, PROVED unconditional: `Lemma13LSP`. -/
theorem lemma13LS : Lemma13LSP := by
  intro x hx hL k hk ε hε
  set y := x / 202 with hydef
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hy0 : 0 < y := by positivity
  have hy7 : 10 ^ 7 ≤ y := y_big hy0 hL
  obtain ⟨hN1, hN2⟩ := Nk_bounds y k hy0.le
  obtain ⟨hQ50, hQ2, hwQ⟩ := Qs_facts (k := k) hy7
  obtain ⟨hz0, hz2, hz500⟩ := z_facts (k := k) hy7
  set N := Nk y k with hNdef
  set S := Sk y k with hSdef
  have hN0 : 0 < N := by linarith
  have hlogN : 349 ≤ Real.log N := by
    have h1 : y / 2 ≤ N := by linarith
    have h2 : Real.log (y / 2) ≤ Real.log N := Real.log_le_log (by positivity) h1
    rw [Real.log_div hy0.ne' (by norm_num)] at h2
    have h3 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  set z := zk y k with hzdef
  have hlogz : Real.log z = (Real.log (2 / 3) + Real.log N) / 2 := by
    rw [hzdef, zk, Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hN0.ne']
  have hl23 : Real.log (2 / 3) = -Real.log (3 / 2) := by
    rw [show (2 : ℝ) / 3 = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  have hl32 := log32_lt
  have hl32' : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hl5 := log5_lt
  have hl5' : 1 < Real.log 5 := one_lt_log5
  have hl100 := log100_lt
  have hl20 : Real.log 20 = Real.log 100 - Real.log 5 := by
    rw [show (20 : ℝ) = 100 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  set Zz := Zs y k with hZdef
  have hlogZ : Real.log Zz = Real.log z - Real.log 20 := by
    rw [hZdef, Zs, Real.log_div hz0.ne' (by norm_num)]
  have hZ4 : 5 ≤ Real.log Zz := by rw [hlogZ, hl20, hlogz, hl23]; linarith
  have hZ0 : 0 < Zz := by rw [hZdef, Zs]; positivity
  -- W
  set W := ⌊wk y k⌋₊ with hWdef
  have hw0 : 0 ≤ wk y k := by unfold wk; positivity
  have hW : 4 ≤ W := by
    have h : (5 : ℝ) ≤ wk y k := by rw [wk_eq]; linarith
    have := Nat.le_floor (show ((5 : ℕ) : ℝ) ≤ wk y k by exact_mod_cast h)
    omega
  have hlim := eq816 y k hw0
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hval := re_limit_ge y k hy0.le hW
  -- F
  set F := Lemma13Max.fq 5 / Real.log (Zz / 5) with hFdef
  have hlz5 : Real.log (Zz / 5) = Real.log Zz - Real.log 5 := Real.log_div hZ0.ne' (by norm_num)
  have hden5 : 0 < Real.log (Zz / 5) := by rw [hlz5]; linarith
  have hF0 : 0 ≤ F := div_nonneg (Lemma13Max.fq_nonneg 5) hden5.le
  have hfq : ∀ q ∈ Icc 5 W, Lemma13Max.fq q * Qr y k q ≤
      F * (Real.log (Zz / q) * Qr y k q) := by
    intro q hq
    rw [mem_Icc] at hq
    have hqz : (q : ℝ) ≤ Zz / 5 := by
      have h1 : (q : ℝ) ≤ (W : ℝ) := by exact_mod_cast hq.2
      have h2 : (W : ℝ) ≤ wk y k := Nat.floor_le hw0
      rw [wk_eq] at h2
      rw [hZdef, Zs]; linarith
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hden : 0 < Real.log (Zz / q) := by
      have : (5 : ℝ) ≤ Zz / q := by rw [le_div_iff₀ hq0]; linarith
      exact Real.log_pos (by linarith)
    have hm := lemma13_max0 hZ4 hq.1 hqz
    rw [div_le_iff₀ hden] at hm
    have hQ := Qr_nonneg y k q
    calc Lemma13Max.fq q * Qr y k q
        ≤ (F * Real.log (Zz / q)) * Qr y k q := mul_le_mul_of_nonneg_right hm hQ
      _ = F * (Real.log (Zz / q) * Qr y k q) := by ring
  have h818 := eq818LS hk1 hy7
  rw [← hZdef, hQ2] at h818
  set N2 := N + 2 * (N / 150) with hN2def
  have hsum : ∑ q ∈ Icc 5 W, Lemma13Max.fq q * Qr y k q ≤
      F * (S * N2 - S ^ 2 * Real.log Zz) := by
    calc _ ≤ ∑ q ∈ Icc 5 W, F * (Real.log (Zz / q) * Qr y k q) := sum_le_sum hfq
      _ = F * ∑ q ∈ Icc 5 W, Real.log (Zz / q) * Qr y k q := by rw [mul_sum]
      _ ≤ F * (S * N2 - S ^ 2 * Real.log Zz) := by
          apply mul_le_mul_of_nonneg_left _ hF0; linarith
  have hS0 : 0 ≤ S := Sk_nonneg y k hy0.le
  have hSN : S ≤ N / 2 + 1 := by
    rw [hSdef, ← card_Pset_eq y k hy0.le]; exact card_Pset_le_half hk1 (by linarith)
  have hN2v : N2 = 76 / 75 * N := by rw [hN2def]; ring
  have hX : 0 ≤ S * (N2 - S * Real.log 5) := by
    apply mul_nonneg hS0; rw [hN2v]; nlinarith
  set A := Real.log Zz with hAdef
  have hAL : 0 < A - Real.log 5 := by rw [← hlz5]; exact hden5
  have hfq5 : Lemma13Max.fq 5 = 1 / 15 := Lemma13Max.fq_five
  have hFv : F = 1 / (15 * (A - Real.log 5)) := by
    rw [hFdef, hfq5, hlz5]; field_simp
  have hD : 0 < -10 + Real.log N := by linarith
  have hDle : -10 + Real.log N ≤ 2 * (A - Real.log 5) := by
    rw [hlogZ, hl20, hlogz, hl23]; linarith
  have key : S ^ 2 - F * (S * N2 - S ^ 2 * A) =
      16 / 15 * S ^ 2 - S * (N2 - S * Real.log 5) / (15 * (A - Real.log 5)) := by
    rw [hFv]; field_simp; ring
  have hcmp : S * (N2 - S * Real.log 5) / (15 * (A - Real.log 5)) ≤
      2 * S * (N2 - S * Real.log 5) / (15 * (-10 + Real.log N)) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have h := mul_le_mul_of_nonneg_left hDle hX
    calc S * (N2 - S * Real.log 5) * (15 * (-10 + Real.log N)) =
          15 * (S * (N2 - S * Real.log 5) * (-10 + Real.log N)) := by ring
      _ ≤ 15 * (S * (N2 - S * Real.log 5) * (2 * (A - Real.log 5))) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 2 * S * (N2 - S * Real.log 5) * (15 * (A - Real.log 5)) := by ring
  have hB : 1 / 2 * Ctw * (16 / 15 * S ^ 2 -
      2 * S * (76 / 75 * N - S * Real.log 5) / (15 * (-10 + Real.log N))) ≤
      1 / 2 * Ctw * (S ^ 2 -
        ∑ q ∈ Icc 5 W, Lemma13Max.fq q * Qr y k q) := by
    have hC := Ctw_pos
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : S ^ 2 - F * (S * N2 - S ^ 2 * A) ≤
        S ^ 2 - ∑ q ∈ Icc 5 W, Lemma13Max.fq q * Qr y k q := by
      linarith
    rw [← hN2v]
    linarith
  have hfin := (tendsto_order.1 hre).1 _ (show 1 / 2 * Ctw *
      (16 / 15 * S ^ 2 - 2 * S * (76 / 75 * N - S * Real.log 5) /
        (15 * (-10 + Real.log N))) - ε < _ by linarith)
  obtain ⟨D0, hD0⟩ := Filter.eventually_atTop.mp hfin
  exact ⟨D0, fun D hD => (hD0 D hD).le⟩

/-! ### Lemma 14 with the new constants, page 67 -/

/-- The numerical step of page 67 with `10` for `2.9024`:
`(1 + 1/y)/(1 − 10/log y) ≤ 1 + 10.3/log y` for `log y ≥ 350`. -/
theorem lemma14_stepLS (y : ℝ) (hy : 0 < y) (hL : 350 ≤ Real.log y) :
    (1 + 1 / y) / (1 - 10 / Real.log y) ≤ 1 + 103 / 10 / Real.log y := by
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  have hy5 : L ^ 5 / 120 ≤ y := by
    have := Real.pow_div_factorial_le_exp L hL0.le 5
    have hf : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
    rw [hf, Real.exp_log hy] at this
    exact this
  have hε : 1 / y ≤ 120 / L ^ 5 := by
    rw [div_le_div_iff₀ hy (by positivity)]; linarith
  have hden : 0 < 1 - 10 / L := by
    have : 10 / L < 1 := by rw [div_lt_one hL0]; linarith
    linarith
  rw [div_le_iff₀ hden]
  have e : (1 + 103 / 10 / L) * (1 - 10 / L) =
      1 + ((103 / 10 - 10) * L - 103 / 10 * 10) / L ^ 2 := by
    field_simp; ring
  rw [e]
  set c := (103 / 10 - 10) * L - 103 / 10 * 10 with hc
  have hc0 : 1 ≤ c := by rw [hc]; nlinarith
  have hL3 : (350 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  have hb : 120 / L ^ 5 ≤ c / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 120 * L ^ 2 ≤ c * L ^ 3 * L ^ 2 := by
      have h1 : (120 : ℝ) ≤ c * L ^ 3 := by nlinarith
      nlinarith [sq_nonneg L]
    nlinarith
  linarith

/-- Page 67 with `10`: `N/(−10 + log N) ≤ y/log y + 10.3 y/(log y)²` for `y − 1 < N < y + 1`. -/
theorem N_div_leLS {y N : ℝ} (hy : 0 < y) (hL : 350 ≤ Real.log y) (hN1 : y - 1 < N)
    (hN2 : N < y + 1) :
    N / (-10 + Real.log N) ≤ y / Real.log y + 103 / 10 * y / Real.log y ^ 2 := by
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  have hy2 : 2 ≤ y := by
    have : Real.exp 1 ≤ y := by
      rw [← Real.exp_log hy]; exact Real.exp_le_exp.mpr (by linarith)
    have := Real.exp_one_gt_d9; linarith
  have hN0 : 0 < N := by linarith
  have hlogN : L - 1 ≤ Real.log N := by
    have h1 : y / 2 ≤ N := by linarith
    have h2 : Real.log (y / 2) ≤ Real.log N := Real.log_le_log (by positivity) h1
    rw [Real.log_div hy.ne' (by norm_num)] at h2
    have := Real.log_two_lt_d9; linarith
  have hmono := Lemma14.div_log_mono (c := 10) hN0 hN2.le (by linarith)
  have hlogy1 : L ≤ Real.log (y + 1) := Real.log_le_log hy (by linarith)
  have hden : 0 < L - 10 := by linarith
  have h3 : (y + 1) / (Real.log (y + 1) - 10) ≤ (y + 1) / (L - 10) :=
    div_le_div_of_nonneg_left (by linarith) hden (by linarith)
  have h4 : (y + 1) / (L - 10) = y / L * ((1 + 1 / y) / (1 - 10 / L)) := by
    field_simp
  have h5 := lemma14_stepLS y hy hL
  have h6 : y / L * ((1 + 1 / y) / (1 - 10 / L)) ≤ y / L * (1 + 103 / 10 / L) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have h7 : y / L * (1 + 103 / 10 / L) = y / L + 103 / 10 * y / L ^ 2 := by
    field_simp
  have e1 : N / (-10 + Real.log N) = N / (Real.log N - 10) := by ring_nf
  rw [e1]
  linarith [hmono, h3, h4 ▸ h6, h7]

/-- Lemma 13's new bound gives the `Φ_k` display of page 67 with `(76/75)` and `10.3`. -/
theorem phi_lowerLS {y N C S Φ : ℝ} (hy : 0 < y) (hL : 350 ≤ Real.log y) (hN1 : y - 1 < N)
    (hN2 : N < y + 1) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (h13 : 1 / 2 * C * (16 / 15 * S ^ 2 - 2 * S * (76 / 75 * N - S * Real.log 5) /
      (15 * (-10 + Real.log N))) ≤ Φ) :
    C / 15 * ((8 + Real.log 5 / Real.log y) * S ^ 2 -
      76 / 75 * (y / Real.log y + 103 / 10 * y / Real.log y ^ 2) * S) ≤ Φ := by
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  have hy2 : 2 ≤ y := by
    have : Real.exp 1 ≤ y := by
      rw [← Real.exp_log hy]; exact Real.exp_le_exp.mpr (by linarith)
    have := Real.exp_one_gt_d9; linarith
  have hN0 : 0 < N := by linarith
  set D := -10 + Real.log N with hD
  have hlogN : L - 1 ≤ Real.log N := by
    have h1 : y / 2 ≤ N := by linarith
    have h2 : Real.log (y / 2) ≤ Real.log N := Real.log_le_log (by positivity) h1
    rw [Real.log_div hy.ne' (by norm_num)] at h2
    have := Real.log_two_lt_d9; linarith
  have hD0 : 0 < D := by rw [hD]; linarith
  have hDL : D ≤ L := by
    have hq : Real.log (N / y) ≤ N / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hN0.ne' hy.ne'] at hq
    have : N / y - 1 ≤ 1 := by
      rw [div_sub_one hy.ne', div_le_one hy]; linarith
    rw [hD]; linarith
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hND := N_div_leLS hy hL hN1 hN2
  have e : 1 / 2 * C * (16 / 15 * S ^ 2 - 2 * S * (76 / 75 * N - S * Real.log 5) / (15 * D)) =
      C / 15 * (8 * S ^ 2 + S ^ 2 * Real.log 5 / D - 76 / 75 * (N / D) * S) := by
    field_simp; ring
  rw [e] at h13
  have h1 : S ^ 2 * Real.log 5 / L ≤ S ^ 2 * Real.log 5 / D :=
    div_le_div_of_nonneg_left (by positivity) hD0 hDL
  have h2 : 76 / 75 * (N / D) * S ≤ 76 / 75 * (y / L + 103 / 10 * y / L ^ 2) * S := by
    apply mul_le_mul_of_nonneg_right _ hS
    linarith
  have h3 : C / 15 * ((8 + Real.log 5 / L) * S ^ 2 -
      76 / 75 * (y / L + 103 / 10 * y / L ^ 2) * S) ≤
      C / 15 * (8 * S ^ 2 + S ^ 2 * Real.log 5 / D - 76 / 75 * (N / D) * S) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (8 + Real.log 5 / L) * S ^ 2 = 8 * S ^ 2 + S ^ 2 * Real.log 5 / L := by ring
    rw [this]; linarith
  linarith

/-- **Lemma 14 with the new constants**, from (8.9) and the displayed conclusions of Lemmas
10, 11, 12 and the new Lemma 13: `Ψ ≥ (C/15)((8 + log 5/L) S² − (y/L)(76/75 + 10.5/L) S)`. -/
theorem lemma14_ofLS {y N w C S Ψ Φ Δ Θ Ξ : ℝ}
    (hy : 0 < y) (hL : 350 ≤ Real.log y)
    (hN1 : y - 1 < N) (hN2 : N < y + 1)
    (hw1 : Real.sqrt y / 200 ≤ w) (hw2 : w ≤ Real.sqrt y)
    (hC : 1 ≤ C) (hS : 0 ≤ S)
    (h89 : Ψ = Φ - Δ + Θ + Ξ)
    (h10 : |Ξ| ≤ 6.31 * OddSums.A10 * S)
    (h11 : |Θ| ≤ 3 * OddSums.A10 * (y / w) * S)
    (h12 : |Δ| ≤ 8 * OddSums.A11 * w * S)
    (h13 : 1 / 2 * C * (16 / 15 * S ^ 2 - 2 * S * (76 / 75 * N - S * Real.log 5) /
      (15 * (-10 + Real.log N))) ≤ Φ) :
    C / 15 * ((8 + Real.log 5 / Real.log y) * S ^ 2 -
      y / Real.log y * (76 / 75 + 105 / 10 / Real.log y) * S) ≤ Ψ := by
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  have hΦ := phi_lowerLS hy hL hN1 hN2 (by linarith) hS h13
  have herr := Lemma14.errors_le hy hL hw1 hw2 hS h10 h11 h12
  rw [← hLdef] at hΦ herr
  have hΨ : Φ - |Δ| - |Θ| - |Ξ| ≤ Ψ := by
    rw [h89]
    have := neg_abs_le Δ; have := le_abs_self Θ; have := le_abs_self Ξ
    have := neg_abs_le Θ; have := neg_abs_le Ξ; have := le_abs_self Δ
    linarith
  set G := y / (15 * L ^ 2) * S with hG
  have hG0 : 0 ≤ G := by positivity
  have herr' : |Ξ| + |Θ| + |Δ| ≤ C * (3 * (1 / 10 ^ 50) * G) := by
    have : 3 * (1 / 10 ^ 50) * (y / (15 * L ^ 2)) * S = 3 * (1 / 10 ^ 50) * G := by
      rw [hG]; ring
    rw [this] at herr
    have h0 : 0 ≤ 3 * (1 / 10 ^ 50 : ℝ) * G := by positivity
    nlinarith
  have hfin : C / 15 * ((8 + Real.log 5 / L) * S ^ 2 - y / L * (76 / 75 + 105 / 10 / L) * S) ≤
      C / 15 * ((8 + Real.log 5 / L) * S ^ 2 -
        76 / 75 * (y / L + 103 / 10 * y / L ^ 2) * S) - C * (3 * (1 / 10 ^ 50) * G) := by
    have e : y / L * (76 / 75 + 105 / 10 / L) * S =
        76 / 75 * (y / L + 103 / 10 * y / L ^ 2) * S + (47 / 750) * (15 * G) := by
      rw [hG]; field_simp; ring
    rw [e]
    have hC0 : 0 ≤ C := by linarith
    have : C * (3 * (1 / 10 ^ 50) * G) ≤ C / 15 * ((47 / 750) * (15 * G)) := by
      have : 3 * (1 / 10 ^ 50 : ℝ) * G ≤ (47 / 750) * G := by
        apply mul_le_mul_of_nonneg_right _ hG0; norm_num
      nlinarith
    nlinarith
  linarith

/-- The same with `w` defined by (8.6). -/
theorem lemma14_of_NLS {y N C S Ψ Φ Δ Θ Ξ : ℝ}
    (hy : 0 < y) (hL : 350 ≤ Real.log y)
    (hN1 : y - 1 < N) (hN2 : N < y + 1)
    (hC : 1 ≤ C) (hS : 0 ≤ S)
    (h89 : Ψ = Φ - Δ + Θ + Ξ)
    (h10 : |Ξ| ≤ 6.31 * OddSums.A10 * S)
    (h11 : |Θ| ≤ 3 * OddSums.A10 * (y / (Real.sqrt (2 / 3 * N) / 100)) * S)
    (h12 : |Δ| ≤ 8 * OddSums.A11 * (Real.sqrt (2 / 3 * N) / 100) * S)
    (h13 : 1 / 2 * C * (16 / 15 * S ^ 2 - 2 * S * (76 / 75 * N - S * Real.log 5) /
      (15 * (-10 + Real.log N))) ≤ Φ) :
    C / 15 * ((8 + Real.log 5 / Real.log y) * S ^ 2 -
      y / Real.log y * (76 / 75 + 105 / 10 / Real.log y) * S) ≤ Ψ := by
  have hy2 : 2 ≤ y := by
    have : Real.exp 1 ≤ y := by
      rw [← Real.exp_log hy]; exact Real.exp_le_exp.mpr (by linarith)
    have := Real.exp_one_gt_d9; linarith
  obtain ⟨hw1, hw2⟩ := Lemma14.w_bounds hy2 hN1 hN2
  exact lemma14_ofLS hy hL hN1 hN2 hw1 hw2 hC hS h89 h10 h11 h12 h13

/-! ### The chain from Lemma 13 to Lemma 14, copied from Lemma12Delta, Lemma11Theta and
Lemma10Xi with the new constants -/

/-- `Theta.Lemma12and13P` with the new Lemma 13 bound. -/
def Lemma12and13LSP : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200,
    1 / 2 * Ctw * (16 / 15 * Sk (x / 202) k ^ 2 -
        2 * Sk (x / 202) k * (76 / 75 * Nk (x / 202) k - Sk (x / 202) k * Real.log 5) /
          (15 * (-10 + Real.log (Nk (x / 202) k)))) -
      8 * OddSums.A11 * wk (x / 202) k * Sk (x / 202) k ≤
        (DK (x / 202) k (wk (x / 202) k)).re

/-- `Xi.Lemma11to13P` with the new Lemma 13 bound. -/
def Lemma11to13LSP : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200,
    1 / 2 * Ctw * (16 / 15 * Sk (x / 202) k ^ 2 -
        2 * Sk (x / 202) k * (76 / 75 * Nk (x / 202) k - Sk (x / 202) k * Real.log 5) /
          (15 * (-10 + Real.log (Nk (x / 202) k)))) -
      8 * OddSums.A11 * wk (x / 202) k * Sk (x / 202) k -
      3 * OddSums.A10 * (x / 202 / wk (x / 202) k) * Sk (x / 202) k ≤ RestK x (x / 202) k

/-- **Lemma 14 with the new constants**, the statement:
`Ψ_k ≥ (C/15)((8 + log 5/log y) S_k² − (y/log y)(76/75 + 10.5/log y) S_k)`. -/
def Lemma14LSP : Prop :=
  ∀ x : ℝ, 0 < x → 350 < Real.log (x / 202) → ∀ k ∈ Icc 1 200,
    Ctw / 15 * ((8 + Real.log 5 / Real.log (x / 202)) * Sk (x / 202) k ^ 2 -
      x / 202 / Real.log (x / 202) * (76 / 75 + 105 / 10 / Real.log (x / 202)) * Sk (x / 202) k)
      ≤ PsiK x (x / 202) k

/-- Lemma 12 discharged, as `Delta.lemma12and13_of`. -/
theorem lemma12and13LS_of (h : Lemma13LSP) : Lemma12and13LSP := by
  intro x hx hL k hk
  set y := x / 202 with hydef
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hy0 : 0 < y := by positivity
  have hy4 : 4 < y := by
    by_contra hc
    push_neg at hc
    have : Real.log y ≤ Real.log 4 := Real.log_le_log hy0 hc
    have : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  obtain ⟨hN1, hN2⟩ := Nk_bounds y k hy0.le
  have hw0 : 0 ≤ wk y k := by unfold wk; positivity
  have hwy : wk y k ≤ y / 2 := by
    obtain ⟨-, h2⟩ := Lemma14.w_bounds (by linarith : (2 : ℝ) ≤ y) hN1 hN2
    have hs : Real.sqrt y ≤ y / 2 := by
      have h0 := Real.sqrt_nonneg y
      have hsq := Real.sq_sqrt hy0.le
      have h2s : 2 ≤ Real.sqrt y := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      nlinarith
    unfold wk; linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨D0, hD0⟩ := h x hx hL k hk ε hε
  set D := max D0 ⌊y / 2⌋₊
  have hΦ := hD0 D (le_max_left _ _)
  simp only [← hydef] at hΦ
  have hsp := phi_split (w := wk y k) hk1 hy0.le (le_max_right D0 ⌊y / 2⌋₊)
  have hre : (PhiD y k (wk y k) D).re = (DK y k (wk y k)).re + (DeltaD y k (wk y k) D).re := by
    rw [hsp, Complex.add_re]
  have hΔ := lemma12 hk1 hy0 hw0 hwy D
  have hΔre : (DeltaD y k (wk y k) D).re ≤ 8 * OddSums.A11 * wk y k * Sk y k := by
    have := Complex.re_le_norm (DeltaD y k (wk y k) D)
    linarith
  linarith

/-- Lemma 11 discharged, as `Theta.lemma11to13_of`. -/
theorem lemma11to13LS_of (h : Lemma12and13LSP) : Lemma11to13LSP := by
  intro x hx hL k hk
  set y := x / 202 with hydef
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hk2 : k ≤ 200 := (mem_Icc.mp hk).2
  have hy0 : 0 < y := by positivity
  have hy1 : 1 < y := by
    by_contra hc
    push_neg at hc
    have : Real.log y ≤ 0 := Real.log_nonpos hy0.le hc
    linarith
  obtain ⟨hN1, -⟩ := Nk_bounds y k hy0.le
  have hw : 0 < wk y k := by
    unfold wk
    apply div_pos _ (by norm_num)
    apply Real.sqrt_pos.mpr
    linarith
  have hsplit := rest_split (x := x) (y := y) (k := k) hk1 hy0.le
    (Expand87.cut_ok hx.le hk2) (wk y k)
  have hre : RestK x y k = (DK y k (wk y k)).re + (ThetaK y k (wk y k)).re := by
    have := congrArg Complex.re hsplit
    simpa using this
  have hT := lemma11 (w := wk y k) hk1 hy0 hw
  have hTre : -(3 * OddSums.A10 * (y / wk y k) * Sk y k) ≤ (ThetaK y k (wk y k)).re := by
    have := Complex.abs_re_le_norm (ThetaK y k (wk y k))
    have := neg_abs_le (ThetaK y k (wk y k)).re
    linarith
  have hD := h x hx hL k hk
  rw [hre]
  linarith

/-- Lemma 14 from Lemmas 10 to 13, as `Xi.lemma14P_of`. -/
theorem lemma14LSP_of (h : Lemma11to13LSP) : Lemma14LSP := by
  intro x hx hL k hk
  set y := x / 202 with hydef
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hy0 : 0 < y := by positivity
  have hy4 : 4 < y := by
    by_contra hc
    push_neg at hc
    have : Real.log y ≤ Real.log 4 := Real.log_le_log hy0 hc
    have : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    linarith
  have hS := Sk_nonneg y k hy0.le
  obtain ⟨hN1, hN2⟩ := Nk_bounds y k hy0.le
  have hsplit := psi_split (x := x) (y := y) (k := k) hx.le hy4 hk1 (by rw [hydef]; linarith)
  have h10 := lemma10 (x := x) (k := k) hy4 hk1
  have hA10 : 0 ≤ OddSums.A10 := by have := OddSums.A10_ge; linarith
  have hA11 := A11_nonneg
  have hw0 : 0 ≤ wk y k := by unfold wk; positivity
  set S := Sk y k
  set N := Nk y k
  set w := wk y k
  have hH := h x hx hL k hk
  exact lemma14_of_NLS (y := y) (N := N) (C := Ctw) (S := S)
    (Ψ := PsiK x y k) (Ξ := XiK x y k)
    (Δ := 8 * OddSums.A11 * w * S) (Θ := -(3 * OddSums.A10 * (y / w) * S))
    (Φ := RestK x y k + 8 * OddSums.A11 * w * S + 3 * OddSums.A10 * (y / w) * S)
    hy0 hL.le hN1 hN2 (by have := Ctw_ge; linarith) hS
    (by rw [hsplit]; ring) h10
    (by rw [abs_neg, abs_of_nonneg (by positivity)]; unfold w wk; exact le_refl _)
    (by rw [abs_of_nonneg (by positivity)]; unfold w wk; exact le_refl _)
    (by linarith)

/-- **Lemma 14 with the new constants**, PROVED with no hypothesis: `Lemma14LSP`. Sections 7
and 8 of the paper are now formalized without any cited input, at the price of the weaker
constants `76/75` and `10.5` in place of `1` and `2.9267`. -/
theorem lemma14LS : Lemma14LSP :=
  lemma14LSP_of (lemma11to13LS_of (lemma12and13LS_of lemma13LS))

end LeanLab.RieselVaughan1983.Lemma13LS
