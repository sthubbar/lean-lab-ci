/-
P0087 Akeno 2026 pages 32 and 36. Grid 1/80 T5 certificate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveCTables80
import LeanLab.Akeno2026.Thm12Numerics
set_option maxRecDepth 4000
namespace LeanLab.Akeno2026.Thm12Certified80
open Real Set MeasureTheory intervalIntegral LeanLab.Akeno2026 LeanLab.Akeno2026.SieveFns
open LeanLab.Akeno2026.SieveFns.Grid80
/-- Lower table for `K(k/80)`, scaled by `10⁹`. -/
def tKL : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 4663823, 9410221, 14241356, 19159475, 24166914, 29266103, 34459571, 39749952, 45139989, 50632542, 56230595, 61937262, 67755796, 73689596, 79742216, 85917376, 92218971, 98651083, 105217993,
   111924194, 118774406, 125773590, 132926966, 140240031, 147718579, 155368722, 163196916, 171209985, 179415150, 187820061, 196432831, 205262076, 214316954, 223607215, 233143252, 242936157, 252997788, 263340840, 273978924,
   284926659, 296199776, 307815230, 319791333, 332147900, 344906423, 358090261, 371724865, 385838034, 400460216, 415624852, 431368784, 447732732, 464761858, 482506437, 501022656, 520373584]

/-- Upper table for `K(k/80)`, scaled by `10⁹`. -/
def tKU : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 4664715, 9412024, 14244090, 19163161, 24171574, 29271759, 34466247, 39757672, 45148778, 50642427, 56241605, 61949426, 67769144, 73704160, 79758030, 85934476, 92237394, 98670869, 105239183,
   111946832, 118798538, 125799265, 132954235, 140268949, 147749204, 155401116, 163231145, 171246118, 179453262, 187860232, 196475147, 205306628, 214363841, 223656544, 233195137, 242990722, 253055167, 263401178, 274042380,
   284993406, 296270003, 307889144, 319869161, 332229894, 344992860, 358181449, 371821146, 385939792, 400567880, 415738906, 431489776, 447861285, 464898683, 482652350, 501178601, 520540656]

def KL (k : ℕ) : ℕ := tKL.getD k 0
def KU (k : ℕ) : ℕ := tKU.getD k 0

/-- Step checks for `K`, `j = k - 80`, `n = 759 - k`. -/
def chkK (k : ℕ) : Bool :=
  decide (KL (k + 1) * ((2 * (759 - k) + 1) * (k - 80 + 1)) ≤
    KL k * ((2 * (759 - k) + 1) * (k - 80 + 1)) + 2 * Grid80.cL4 k * (k - 80 + 1) + Grid80.cL3 (k - 80)) &&
  decide (KU k * (2 * (759 - k) * (759 - k + 1) * (k - 80)) +
    Grid80.cU4 k * (2 * (759 - k) + 1) * (k - 80) + Grid80.cU3 (k - 80 + 1) * (759 - k + 1) ≤
    KU (k + 1) * (2 * (759 - k) * (759 - k + 1) * (k - 80)))

theorem chk_K : ∀ k < 736, 680 ≤ k → chkK k = true := by decide +kernel

theorem tab_K_base : KL 680 = 0 ∧ KU 680 = 0 := by decide +kernel

theorem K_TB : ∀ k, 680 ≤ k → k ≤ 736 → TB Kfun 80 1000000000 KL KU k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    unfold TB Kfun; rw [tab_K_base.1, tab_K_base.2]; norm_num
  | succ k hk ih =>
    intro hkN
    have hgk := ih (by omega)
    have c := chk_K k (by omega) hk
    simp only [chkK, Bool.and_eq_true, decide_eq_true_eq] at c
    obtain ⟨c1, c2⟩ := c
    obtain ⟨j, hj⟩ : ∃ j, j = k - 80 := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, n = 759 - k := ⟨_, rfl⟩
    rw [← hj, ← hn] at c1 c2
    have hkj : k = j + 80 := by omega
    have hkn : 760 = k + n + 1 := by omega
    have hMr : (0 : ℝ) < (80 : ℕ) := by norm_num
    have hKr : (k : ℝ) = j + (80 : ℕ) := by exact_mod_cast hkj
    have hTr : ((760 : ℕ) : ℝ) = k + n + 1 := by exact_mod_cast hkn
    have hJ0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hk340 : (680 : ℝ) ≤ k := by exact_mod_cast hk
    have hk367 : (k : ℝ) ≤ 735 := by exact_mod_cast (show k ≤ 735 by omega)
    have h4 := Grid80.TB_c4 k (by omega) (by omega)
    have h3 := Grid80.TB_c3 j (by omega) (by omega)
    have h3' := Grid80.TB_c3 (j + 1) (by omega) (by omega)
    unfold TB at h3'; push_cast at h3'
    have key := kgrid_step (G := Kfun) (f := cR 4) (e := cR 3) (M := ((80 : ℕ) : ℝ)) (J := j) (K := k)
      (n := n) (T := ((760 : ℕ) : ℝ)) (D := ((1000000000 : ℕ) : ℝ)) (Gl := KL k) (Gu := KU k)
      (Lf := Grid80.cL4 k) (Uf := Grid80.cU4 k) (Le := Grid80.cL3 j) (Ue := Grid80.cU3 (j + 1)) (Gl' := KL (k + 1))
      (Gu' := KU (k + 1)) hMr hKr hJ0 hTr hn0 (by norm_num) ?_ ?_
      (Grid80.cR_monoOn 4 _ |>.mono (fun x hx => hx.1)) (Grid80.cR_monoOn 3 _ |>.mono (fun x hx => hx.1))
      hgk h4 ⟨h3.1, h3'.2⟩ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast c1) (by exact_mod_cast c2)
    · unfold TB; push_cast; exact key
    · have e380 : ((760 : ℕ) : ℝ) / ((80 : ℕ) : ℝ) = 19 / 2 := by norm_num
      rw [e380]
      apply Kfun_delay
      · push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
      · push_cast; exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
      · push_cast; rw [div_lt_iff₀ (by norm_num)]; linarith
    · intro x hx
      have hp : ((2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) / ((80 : ℕ) : ℝ) := by
        push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
      exact cR_delay 2 hp hx.1

theorem tab_T5_vals : KL 736 = 520373584 ∧ KU 736 = 520540656 ∧ Grid80.cL4 736 = 475067236 ∧
    Grid80.cU4 736 = 475118633 ∧ Grid80.cL3 656 = 1270037853 ∧ Grid80.cU3 658 = 1276421969 ∧ Grid80.cL5 816 = 111391062 ∧
    Grid80.cU5 816 = 111416443 ∧ Grid80.cL5 760 = 78057563 ∧ Grid80.cU5 760 = 78078636 := by decide +kernel

/-- Linear bounds for `c₄` on `[9.2, τ]`, `τ = 1235/134 = 9.5 (1 - 1/33.5)`. -/
theorem c4_slope (x : ℝ) (hx : x ∈ Icc (46 / 5 : ℝ) (1235 / 134)) :
    475067236 / 1000000000 + 1270037853 / 1000000000 / (1235 / 134 - 1) * (x - 46 / 5) ≤ cR 4 x ∧
    cR 4 x ≤ 475118633 / 1000000000 + 1276421969 / 1000000000 / (46 / 5 - 1) * (x - 46 / 5) := by
  obtain ⟨_, _, v3, v4, v5, v6, _⟩ := tab_T5_vals
  have h4 := Grid80.TB_c4 736 (by norm_num) (by norm_num)
  have h3 := Grid80.TB_c3 656 (by norm_num) (by norm_num)
  have h3' := Grid80.TB_c3 658 (by norm_num) (by norm_num)
  unfold TB at h4 h3 h3'
  rw [v3, v4] at h4; rw [v5] at h3; rw [v6] at h3'
  norm_num at h4 h3 h3'
  have hinc := incr (f := cR 4) (e := cR 3) (p := 46 / 5) (q := 1235 / 134) (by norm_num) (by norm_num)
    (fun y hy => cR_delay 2 (by norm_num) hy.1) (Grid80.cR_monoOn 3 _ |>.mono (fun y hy => hy.1))
    ((cR_mono_nonneg 3).2 _) x hx
  have hq : cR 3 (1235 / 134 - 1) ≤ cR 3 (658 / 80) := (cR_mono_nonneg 3).1 (by norm_num)
  have hu0 : 0 ≤ x - 46 / 5 := by linarith [hx.1]
  have e1 : (46 / 5 : ℝ) - 1 = 41 / 5 := by norm_num
  have e2 : (46 / 5 : ℝ) = 46 / 5 := rfl
  rw [show (46 / 5 : ℝ) - 1 = 41 / 5 by norm_num] at hinc
  constructor
  · have hd : 1270037853 / 1000000000 / (1235 / 134 - 1) ≤ cR 3 (41 / 5) / (1235 / 134 - 1) :=
      div_le_div_of_nonneg_right (by linarith [h3.1]) (by norm_num)
    linarith [mul_le_mul_of_nonneg_left hd hu0, hinc.1, h4.1]
  · have hd : cR 3 (1235 / 134 - 1) / (41 / 5) ≤ 1276421969 / 1000000000 / (41 / 5) :=
      div_le_div_of_nonneg_right (by linarith [h3'.2]) (by norm_num)
    have : (1276421969 : ℝ) / 1000000000 / (46 / 5 - 1) = 1276421969 / 1000000000 / (41 / 5) := by
      norm_num
    rw [this]
    linarith [mul_le_mul_of_nonneg_left hd hu0, hinc.2, h4.2]

theorem K_tau_bounds : (0.5471751 : ℝ) ≤ Kfun (1235 / 134) ∧ Kfun (1235 / 134) ≤ 0.5473689 := by
  obtain ⟨v1, v2, _⟩ := tab_T5_vals
  have hK := K_TB 736 (by norm_num) le_rfl
  unfold TB at hK; rw [v1, v2] at hK; norm_num at hK
  have hab : (46 / 5 : ℝ) ≤ 1235 / 134 := by norm_num
  have hdel := Kfun_delay (a := 46 / 5) (b := 1235 / 134) (by norm_num) hab (by norm_num)
  obtain ⟨hW, hV⟩ := weight_refl (t := 19 / 2) hab (by norm_num)
  have hw0 : ∀ u ∈ Icc (46 / 5 : ℝ) (1235 / 134), 0 ≤ (19 / 2 - u)⁻¹ :=
    fun u hu => inv_nonneg.mpr (by linarith [hu.2])
  have hwc : ContinuousOn (fun u : ℝ => (19 / 2 - u)⁻¹) (Icc (46 / 5 : ℝ) (1235 / 134)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro u hu; linarith [hu.2]
  obtain ⟨s1, s2⟩ := wstep hab (c4_refl_integrable hab (by norm_num)) hw0 hwc hW hV
    (fun u hu => (c4_slope u hu).1) (fun u hu => (c4_slope u hu).2)
  rw [← hdel] at s1 s2
  have hy : 1 < ((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) := by norm_num
  have hΛL := two_mul_div_le_log hy
  have hΛU := log_le_half_sub_inv hy.le
  set L := log (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134))
  constructor
  · have : (0.5471751 : ℝ) ≤ 520373584 / 1000000000 + (475067236 / 1000000000 *
        (2 * (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) - 1) /
          (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) + 1)) +
        1270037853 / 1000000000 / (1235 / 134 - 1) * (-(1235 / 134 - 46 / 5) + (19 / 2 - 46 / 5) *
        (2 * (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) - 1) /
          (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) + 1)))) := by norm_num
    have hpos1 : (0 : ℝ) ≤ 475067236 / 1000000000 := by norm_num
    have hpos2 : (0 : ℝ) ≤ 1270037853 / 1000000000 / (1235 / 134 - 1) * (19 / 2 - 46 / 5) := by
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hΛL hpos1, mul_le_mul_of_nonneg_left hΛL hpos2]
  · have : 520540656 / 1000000000 + (475118633 / 1000000000 *
        ((((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) -
          (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134))⁻¹) / 2) +
        1276421969 / 1000000000 / (46 / 5 - 1) * (-(1235 / 134 - 46 / 5) + (19 / 2 - 46 / 5) *
        ((((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) -
          (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134))⁻¹) / 2))) ≤ (0.5473689 : ℝ) := by
      norm_num
    have hpos1 : (0 : ℝ) ≤ 475118633 / 1000000000 := by norm_num
    have hpos2 : (0 : ℝ) ≤ 1276421969 / 1000000000 / (46 / 5 - 1) * (19 / 2 - 46 / 5) := by
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hΛU hpos1, mul_le_mul_of_nonneg_left hΛU hpos2]

theorem c5_tau1_bounds : (0.1122403 : ℝ) ≤ cR 5 (1369 / 134) ∧ cR 5 (1369 / 134) ≤ 0.1122659 := by
  obtain ⟨_, _, _, _, _, _, v7, v8, _⟩ := tab_T5_vals
  have h5 := Grid80.TB_c5 816 (by norm_num) (by norm_num)
  unfold TB at h5; rw [v7, v8] at h5; norm_num at h5
  have ha : (1 : ℝ) < 51 / 5 := by norm_num
  have hab : (51 / 5 : ℝ) ≤ 1369 / 134 := by norm_num
  have hlo : ∀ u ∈ Icc (51 / 5 : ℝ) (1369 / 134), 475067236 / 1000000000 +
      1270037853 / 1000000000 / (1235 / 134 - 1) * (u - 51 / 5) ≤ cR 4 (u - 1) := by
    intro u hu
    have := (c4_slope (u - 1) ⟨by linarith [hu.1], by linarith [hu.2]⟩).1
    have e : u - 1 - 46 / 5 = u - 51 / 5 := by ring
    rw [e] at this; exact this
  have hhi : ∀ u ∈ Icc (51 / 5 : ℝ) (1369 / 134), cR 4 (u - 1) ≤ 475118633 / 1000000000 +
      1276421969 / 1000000000 / (46 / 5 - 1) * (u - 51 / 5) := by
    intro u hu
    have := (c4_slope (u - 1) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
    have e : u - 1 - 46 / 5 = u - 51 / 5 := by ring
    rw [e] at this; exact this
  have hy : 1 < ((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) := by norm_num
  obtain ⟨s1, s2⟩ := dstep (g := cR 5) (f := cR 4) ha hab
    (cR_delay 3 (by norm_num) hab) (Grid80.cR_monoOn 4 _ |>.mono (fun y hy => hy.1)) hlo hhi
    (two_mul_div_le_log hy) (log_le_half_sub_inv hy.le) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  constructor
  · have : (0.1122403 : ℝ) ≤ 111391062 / 1000000000 + 475067236 / 1000000000 *
        (2 * (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) - 1) / (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) + 1)) +
        1270037853 / 1000000000 / (1235 / 134 - 1) * (1369 / 134 - 51 / 5 - (51 / 5 - 1) *
        ((((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) - (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1))⁻¹) / 2)) := by
      norm_num
    linarith [h5.1]
  · have : 111416443 / 1000000000 + 475118633 / 1000000000 *
        ((((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) - (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1))⁻¹) / 2) +
        1276421969 / 1000000000 / (46 / 5 - 1) * (1369 / 134 - 51 / 5 - (51 / 5 - 1) *
        (2 * (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) - 1) / (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) + 1)))
        ≤ (0.1122659 : ℝ) := by
      norm_num
    linarith [h5.2]

/-- Partial fractions: `T₅,₀ + T₅,₁ = (c₅(t) + c₅(τ+1))/2 + K(τ)/2` at `s = 33.5`, `t = 9.5`,
using `∫_{t-1}^{τ} c₄(u)/u du = c₅(τ+1) - c₅(t)` from the `c_r` recursion. -/
theorem T5_split : T5kuhn 33.5 9.5 = (cR 5 (19 / 2) + cR 5 (1369 / 134)) / 2 + Kfun (1235 / 134) / 2 := by
  have eτ : (9.5 : ℝ) * (1 - 1 / 33.5) = 1235 / 134 := by norm_num
  have et : (9.5 : ℝ) = 19 / 2 := by norm_num
  unfold T5kuhn
  rw [eτ, et]
  have hpq : (19 / 2 - 1 : ℝ) ≤ 1235 / 134 := by norm_num
  have hmono : MonotoneOn (cR 4) (uIcc (19 / 2 - 1 : ℝ) (1235 / 134)) :=
    (cR_mono_nonneg 4).1.monotoneOn _
  have hc1 : ContinuousOn (fun u : ℝ => u⁻¹) (uIcc (19 / 2 - 1 : ℝ) (1235 / 134)) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro u hu; rw [uIcc_of_le hpq] at hu; simp only [id]; linarith [hu.1]
  have hi1 : IntervalIntegrable (fun u => cR 4 u * u⁻¹) volume (19 / 2 - 1 : ℝ) (1235 / 134) :=
    (hmono.intervalIntegrable (μ := volume)).mul_continuousOn hc1
  have hi2 := c4_refl_integrable hpq (by norm_num)
  have hsplit : ∫ u in (19 / 2 - 1 : ℝ)..(1235 / 134), cR 4 u / (u * (19 / 2 - u)) =
      (2 / 19) * ((∫ u in (19 / 2 - 1 : ℝ)..(1235 / 134), cR 4 u * u⁻¹) +
        ∫ u in (19 / 2 - 1 : ℝ)..(1235 / 134), cR 4 u * (19 / 2 - u)⁻¹) := by
    rw [← intervalIntegral.integral_add hi1 hi2, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu; rw [uIcc_of_le hpq] at hu
    have h1 : u ≠ 0 := by linarith [hu.1]
    have h2 : 19 / 2 - u ≠ 0 := by linarith [hu.2]
    have h3 : 19 - u * 2 ≠ 0 := by linarith [hu.2]
    simp only
    field_simp
    ring
  have hshift : ∫ u in (19 / 2 - 1 : ℝ)..(1235 / 134), cR 4 u * u⁻¹ =
      cR 5 (1369 / 134) - cR 5 (19 / 2) := by
    rw [cR_delay 3 (by norm_num) (by norm_num : (19 / 2 : ℝ) ≤ 1369 / 134)]
    rw [intervalIntegral.integral_comp_sub_right (fun x => cR 4 x / x)]
    norm_num [div_eq_mul_inv]
  rw [hsplit, hshift]
  unfold Kfun
  ring

/-- **`T₅` certified** for the page 36 formula `T₅ = c₅(t) + (t/2) ∫ c₄(u)/(u(t-u)) du`,
`s = 33.5`, `t = 9.5`: `T₅ ∈ [0.3687, 0.3689]`. Printed: `[0.3687, 0.3689]`, page 32. -/
theorem T5_bounds_printed : (0.3687 : ℝ) ≤ T5kuhn 33.5 9.5 ∧ T5kuhn 33.5 9.5 ≤ 0.3689 := by
  obtain ⟨_, _, _, _, _, _, _, _, v9, v10⟩ := tab_T5_vals
  have h5 := Grid80.TB_c5 760 (by norm_num) (by norm_num)
  unfold TB at h5; rw [v9, v10] at h5; norm_num at h5
  have hK := K_tau_bounds
  have hc := c5_tau1_bounds
  rw [T5_split]
  constructor <;> linarith [h5.1, h5.2, hK.1, hK.2, hc.1, hc.2]


end LeanLab.Akeno2026.Thm12Certified80
