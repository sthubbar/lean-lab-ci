/-
Counting obstructions for the three strict constant phase bands.
Gallagher 1975 p.134 display 3 supplies the exponent tuples.
The lab range cuts are auxiliary and are not printed paper estimates.
These results concern tuple counts. They do not lower bound prime errors.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik.Decomp496a

namespace LeanLab.Linnik.Decomp554a

open Filter
open scoped Topology

/-- Gallagher 1975 p.134 display 3 and the auxiliary lab cuts. For each b at
most two, the band between N to `(1+b)/32` and N to `(2+b)/32` contains at least
m to four exponent pairs when N is two to 128m. The lower cut is strict. -/
theorem constant_band_box_density (m b : ℕ) (hm : 1 ≤ m) (hb : b ≤ 2) :
    let L : ℕ := 128 * m
    let N : ℕ := 2 ^ L
    let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
      ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
      ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + b : ℝ) / 32) ∧
      |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 32) ∧
      |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))
    m ^ 4 ≤ T.card ∧ L ^ 4 ≤ 128 ^ 4 * T.card := by
  classical
  let L : ℕ := 128 * m
  let N : ℕ := 2 ^ L
  let t : ℕ := (6 + 4 * b) * m
  let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
    Decomp1532a.dif x ≠ 0 ∧
    ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
    ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + b : ℝ) / 32) ∧
    |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 32) ∧
    |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))
  change m ^ 4 ≤ T.card ∧ L ^ 4 ≤ 128 ^ 4 * T.card
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have hmt : m ≤ t := by rcases hb' with rfl | rfl | rfl <;> dsimp [t] <;> omega
  have htL : t + m ≤ L := by rcases hb' with rfl | rfl | rfl <;> dsimp [t, L] <;> omega
  obtain ⟨f, hf, hbox⟩ := Decomp496a.shifted_box_embedding m t L hmt htL
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (Nat.one_le_pow L 2 (by norm_num))
  have hcut (r : ℝ) : (N : ℝ) ^ r = (2 : ℝ) ^ ((L : ℝ) * r) := by
    simp only [N, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hmaps : Set.MapsTo f (Finset.univ : Finset (Decomp1532a.pairs 2 m)) T := by
    intro x _hx
    have hlo : (2 : ℝ) ^ (t + 1) ≤ (Decomp1532a.dif (f x) : ℝ) := by
      exact_mod_cast (hbox x).1
    have hhi : (Decomp1532a.dif (f x) : ℝ) ≤ (2 : ℝ) ^ (t + m + 1) := by
      exact_mod_cast (hbox x).2
    have hp : (0 : ℝ) < Decomp1532a.dif (f x) :=
      (pow_pos (by norm_num) _).trans_le hlo
    have hlow : (N : ℝ) ^ ((1 + b : ℝ) / 32) < |(Decomp1532a.dif (f x) : ℝ)| := by
      rw [abs_of_pos hp, hcut]
      apply lt_of_lt_of_le _ hlo
      rw [← Real.rpow_natCast]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      rcases hb' with rfl | rfl | rfl <;> dsimp [L, t] <;> push_cast <;> nlinarith
    have hupp : |(Decomp1532a.dif (f x) : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 32) := by
      rw [abs_of_pos hp, hcut]
      apply hhi.trans
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rcases hb' with rfl | rfl | rfl <;> dsimp [L, t] <;> push_cast <;> nlinarith
    have hglobal : |(Decomp1532a.dif (f x) : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
      apply hupp.trans
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have hbr : (b : ℝ) ≤ 2 := by exact_mod_cast hb
      linarith
    have hsmall : (N : ℝ) ^ (1 / 32 : ℝ) < |(Decomp1532a.dif (f x) : ℝ)| := by
      apply lt_of_le_of_lt _ hlow
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have hbr : (0 : ℝ) ≤ b := Nat.cast_nonneg _
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by exact_mod_cast hp.ne',
      not_le.mpr hsmall, not_le.mpr hlow, hupp, hglobal⟩
  have hcard : m ^ 4 ≤ T.card := by
    have h := Finset.card_le_card_of_injOn f hmaps hf.injOn
    simpa [Decomp1532a.pairs, ← pow_add] using h
  refine ⟨hcard, ?_⟩
  calc
    L ^ 4 = 128 ^ 4 * m ^ 4 := mul_pow _ _ _
    _ ≤ 128 ^ 4 * T.card := Nat.mul_le_mul_left _ hcard



/-- Gallagher 1975 p.134 display 3 and the three auxiliary strict constant phase
bands. Each tuple count fails to be little o of the full count. This is a
negative result for a counting proof and does not refute any prime error leaf. -/
theorem constant_band_count_not_littleO (b : ℕ) (hb : b ≤ 2) :
    let R : ℕ → ℝ := fun N =>
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + b : ℝ) / 32) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 32) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))).card : ℝ)
    ¬ Asymptotics.IsLittleO atTop R (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  let R : ℕ → ℝ := fun N =>
    (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + b : ℝ) / 32) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 32) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))).card : ℝ)
  change ¬ Asymptotics.IsLittleO atTop R (fun N => (Nat.log 2 N : ℝ) ^ 4)
  intro h
  let ε : ℝ := 1 / (2 * 128 ^ 4)
  obtain ⟨Nk, hNk⟩ := eventually_atTop.mp (h.bound (by dsimp [ε]; positivity : 0 < ε))
  let m := max Nk 1
  let L := 128 * m
  let N : ℕ := 2 ^ L
  let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
    Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + b : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))
  have hm : 1 ≤ m := le_max_right _ _
  have hmNk : Nk ≤ m := le_max_left _ _
  have hmL : m ≤ L := by dsimp [L]; omega
  have hNL : L < N := L.lt_two_pow_self
  have hNNk : Nk ≤ N := by omega
  have hlog : Nat.log 2 N = L := by
    dsimp [N]
    exact Nat.log_pow (by norm_num) L
  have hR : R N = (T.card : ℝ) := by
    dsimp [R]
    rw [hlog]
  have hdensity : L ^ 4 ≤ 128 ^ 4 * T.card := (constant_band_box_density m b hm hb).2
  have hd : (L : ℝ) ^ 4 ≤ (128 : ℝ) ^ 4 * (T.card : ℝ) := by exact_mod_cast hdensity
  have hb : (T.card : ℝ) ≤ ε * (L : ℝ) ^ 4 := by
    have hh := hNk N hNNk
    rw [hR, hlog, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)] at hh
    exact hh
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpos : (0 : ℝ) < (L : ℝ) ^ 4 := pow_pos hLp _
  have hcoeff : (128 : ℝ) ^ 4 * ε = 1 / 2 := by norm_num [ε]
  have hbd : (128 : ℝ) ^ 4 * (T.card : ℝ) ≤ (1 / 2 : ℝ) * (L : ℝ) ^ 4 := by
    calc
      _ ≤ (128 : ℝ) ^ 4 * (ε * (L : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [← mul_assoc, hcoeff]
  have hf := hd.trans hbd
  linarith only [hf, hpos]

/-- Gallagher 1975 p.127 Theorem 3 and p.138 error sum. The positive arithmetic
weight in the printed exponential allowance cannot give a vanishing weighted
tuple fraction on any of the three strict constant phase bands. -/
theorem constant_band_weight_not_littleO (b : ℕ) (hb : b ≤ 2) :
    let W : ℕ → ℝ := fun N =>
      ∑ x : Decomp1532a.pairs 2 (Nat.log 2 N) with
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + b : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ),
        Decomp466a.totientWeight (Decomp1532a.dif x)
    ¬ Asymptotics.IsLittleO atTop W (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  let T : ∀ N : ℕ, Finset (Decomp1532a.pairs 2 (Nat.log 2 N)) := fun N =>
    Finset.univ.filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
        ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + b : ℝ) / 32) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + b : ℝ) / 32) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))
  let W : ℕ → ℝ := fun N =>
    ∑ x ∈ T N, Decomp466a.totientWeight (Decomp1532a.dif x)
  change ¬ Asymptotics.IsLittleO atTop W (fun N => (Nat.log 2 N : ℝ) ^ 4)
  intro hW
  apply constant_band_count_not_littleO b hb
  change Asymptotics.IsLittleO atTop (fun N => ((T N).card : ℝ))
    (fun N => (Nat.log 2 N : ℝ) ^ 4)
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hW.bound hε] with N hN
  have hcard : ((T N).card : ℝ) ≤ W N := by
    calc
      _ = ∑ _x ∈ T N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx =>
        MajorArcEnergy.one_le_totientWeight (Finset.mem_filter.mp hx).2.1)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hcard.trans ((le_abs_self _).trans hN)

/-- Gallagher 1975 p.134 display 3 and the exact quarter lab filter.
At theta one quarter and k two its tuple count is not little o of all exponent pairs.
Every clause of the original filter is retained. No prime error lower bound is asserted. -/
theorem quarter_count_not_littleO :
    ¬ Asymptotics.IsLittleO atTop (fun N : ℕ =>
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 8) ∧
           |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 4) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ))
      (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  intro h
  apply constant_band_count_not_littleO 0 (by norm_num)
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [h.bound hε, eventually_ge_atTop 1] with N hN hN1
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hglobal : (N : ℝ) ^ (1 / 8 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have hcard :
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + 0 : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + 0 : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))).card : ℝ) ≤
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 8) ∧
           |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 4) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨hz, hfirst, hlower, hupper, hsmall⟩
    norm_num at hlower hupper ⊢
    exact ⟨hz, not_le.mp hfirst, hupper, hsmall, hsmall.trans hglobal⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using
    hcard.trans ((le_abs_self _).trans hN)

/-- Gallagher 1975 p.134 display 3 and the exact three_eighths lab filter.
At theta one quarter and k two its tuple count is not little o of all exponent pairs.
Every clause of the original filter is retained. No prime error lower bound is asserted. -/
theorem three_eighths_count_not_littleO :
    ¬ Asymptotics.IsLittleO atTop (fun N : ℕ =>
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 8) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 4) ∧
           |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * (1 / 4 : ℝ) / 8) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ))
      (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  intro h
  apply constant_band_count_not_littleO 1 (by norm_num)
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [h.bound hε, eventually_ge_atTop 1] with N hN hN1
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hglobal : (N : ℝ) ^ (1 / 8 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have hcard :
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + 1 : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + 1 : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))).card : ℝ) ≤
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 8) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 4) ∧
           |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * (1 / 4 : ℝ) / 8) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨hz, hfirst, hlower, hupper, hsmall⟩
    norm_num at hlower hupper ⊢
    exact ⟨hz, not_le.mp hfirst, hlower, hupper, hsmall, hsmall.trans hglobal⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using
    hcard.trans ((le_abs_self _).trans hN)

/-- Gallagher 1975 p.134 display 3 and the exact half lab filter.
At theta one quarter and k two its tuple count is not little o of all exponent pairs.
Every clause of the original filter is retained. No prime error lower bound is asserted. -/
theorem half_count_not_littleO :
    ¬ Asymptotics.IsLittleO atTop (fun N : ℕ =>
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 8) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 4) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * (1 / 4 : ℝ) / 8) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ))
      (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  intro h
  apply constant_band_count_not_littleO 2 (by norm_num)
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [h.bound hε, eventually_ge_atTop 1] with N hN hN1
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hglobal : (N : ℝ) ^ (1 / 8 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
  have hcard :
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 + 2 : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((2 + 2 : ℝ) / 32) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ))).card : ℝ) ≤
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 8) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 4) ∧
          ¬ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (3 * (1 / 4 : ℝ) / 8) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ ((1 / 4 : ℝ) / 2) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨hz, hfirst, hlower, hupper, hsmall⟩
    norm_num at hlower hupper ⊢
    have hcut : (N : ℝ) ^ (1 / 16 : ℝ) ≤ (N : ℝ) ^ (3 / 32 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
    exact ⟨hz, not_le.mp hfirst, hcut.trans_lt hlower,
      hlower, hupper, hupper.trans hglobal⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  simpa only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using
    hcard.trans ((le_abs_self _).trans hN)

/-- Gallagher 1975 p.127 Theorem 3 and p.138 error sum. The first constant
phase range also has no vanishing totient weighted tuple fraction. This reuses
the existing first range count obstruction and does not reprove its embedding. -/
theorem first_range_weight_not_littleO :
    let W : ℕ → ℝ := fun N =>
      ∑ x : Decomp1532a.pairs 2 (Nat.log 2 N) with
        Decomp1532a.dif x ≠ 0 ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ),
        Decomp466a.totientWeight (Decomp1532a.dif x)
    ¬ Asymptotics.IsLittleO atTop W (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  let T : ∀ N : ℕ, Finset (Decomp1532a.pairs 2 (Nat.log 2 N)) := fun N =>
    Finset.univ.filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))
  let W : ℕ → ℝ := fun N =>
    ∑ x ∈ T N, Decomp466a.totientWeight (Decomp1532a.dif x)
  change ¬ Asymptotics.IsLittleO atTop W (fun N => (Nat.log 2 N : ℝ) ^ 4)
  intro hW
  apply Decomp495a.first_range_count_not_littleO
  change Asymptotics.IsLittleO atTop (fun N => ((T N).card : ℝ))
    (fun N => (Nat.log 2 N : ℝ) ^ 4)
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hW.bound hε] with N hN
  have hcard : ((T N).card : ℝ) ≤ W N := by
    calc
      _ = ∑ _x ∈ T N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx =>
        MajorArcEnergy.one_le_totientWeight (Finset.mem_filter.mp hx).2.1)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hcard.trans ((le_abs_self _).trans hN)

end LeanLab.Linnik.Decomp554a

#print axioms LeanLab.Linnik.Decomp554a.constant_band_box_density

#print axioms LeanLab.Linnik.Decomp554a.constant_band_count_not_littleO

#print axioms LeanLab.Linnik.Decomp554a.constant_band_weight_not_littleO

#print axioms LeanLab.Linnik.Decomp554a.quarter_count_not_littleO

#print axioms LeanLab.Linnik.Decomp554a.three_eighths_count_not_littleO

#print axioms LeanLab.Linnik.Decomp554a.half_count_not_littleO

#print axioms LeanLab.Linnik.Decomp554a.first_range_weight_not_littleO
