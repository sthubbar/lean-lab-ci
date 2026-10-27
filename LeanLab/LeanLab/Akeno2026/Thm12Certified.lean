/-
P0087 M. Akeno, arXiv 2606.29559 v1, proof of Theorem 1.2 pages 31 to 32 and Appendix 5.1
pages 35 to 36. AI-written Lean code, Claude, session 20261020T2317Z-cloud53, unit U-6767.
Checked only by the Lean kernel. Binary Goldbach is OPEN; nothing here proves it.

Contents.
* `K_TB`, `K_tau_bounds`, `c5_tau1_bounds`: certified enclosures of
  `K = ∫_{t-1}^{t(1-1/s)} c₄(u)/(t-u) du` and `c₅(t(1-1/s)+1)` at `s = 33.5`, `t = 9.5`.
* `T5_split`: `T₅,₀ + T₅,₁ = (c₅(t) + c₅(τ+1))/2 + K/2`, `τ = t(1-1/s)`, by partial fractions
  and the `c_r` recursion.
* `T5_bounds`: `T₅ ∈ [0.3686, 0.369041]` for the page 36 formula; printed `[0.3687, 0.3689]`;
  grid `1/40`, the grid `1/80` run that reaches the printed interval ran out of memory.
* `thm1_2_certified`: Theorem 1.2 CONDITIONAL ON Proposition 4.4, the reduction of `M₄`, the
  page 36 formula for `T₅`, existence of `ω±` as in Lemma 4.1, and the printed enclosures of
  the `F`-integral and `T₆,…,T₁₀`; the printed enclosures of `ω⁻(sθ)` and `T₅` are replaced by
  the PROVED ones of `SieveFns.omega_minus_bounds`, which is the printed `[0.56118, 0.56121]`,
  and `T5_bounds`.
* `thm1_2_omega_certified`: `Thm12Numerics.thm1_2_of_prop44` with only `ω⁻(sθ)` discharged.
-/
import LeanLab.Akeno2026.SieveCTables
import LeanLab.Akeno2026.Thm12Numerics

namespace LeanLab.Akeno2026.Thm12Certified
open Real Set MeasureTheory intervalIntegral LeanLab.Akeno2026 LeanLab.Akeno2026.SieveFns

/-- Lower table for `K(k/40)`, scaled by `10⁹`. -/
def tKL : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   9407744, 19154421, 29258364, 39739410, 50619071, 61920725, 73669843, 85894243, 98624391,
   111893745, 125739165, 140201387, 155325587, 171162054, 187766988, 205203470, 223542629,
   242865074, 263262659, 284840676, 307720612, 332043650, 357975173, 385710627, 415483283,
   447574670, 482328872, 520172550]

/-- Upper table for `K(k/40)`, scaled by `10⁹`. -/
def tKU : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   9414883, 19169017, 29280762, 39769985, 50658231, 61968916, 73727554, 85962013, 98702814,
   111983482, 125840951, 140316045, 155454045, 171305360, 187926335, 205380224, 223738366,
   243081624, 263502165, 285105670, 308014115, 332369304, 358337420, 386114960, 415936590,
   448085735, 482909110, 520837114]

def KL (k : ℕ) : ℕ := tKL.getD k 0
def KU (k : ℕ) : ℕ := tKU.getD k 0

/-- Step checks for `K`, `j = k - 40`, `n = 379 - k`. -/
def chkK (k : ℕ) : Bool :=
  decide (KL (k + 1) * ((2 * (379 - k) + 1) * (k - 40 + 1)) ≤
    KL k * ((2 * (379 - k) + 1) * (k - 40 + 1)) + 2 * cL4 k * (k - 40 + 1) + cL3 (k - 40)) &&
  decide (KU k * (2 * (379 - k) * (379 - k + 1) * (k - 40)) +
    cU4 k * (2 * (379 - k) + 1) * (k - 40) + cU3 (k - 40 + 1) * (379 - k + 1) ≤
    KU (k + 1) * (2 * (379 - k) * (379 - k + 1) * (k - 40)))

theorem chk_K : ∀ k < 368, 340 ≤ k → chkK k = true := by decide +kernel

theorem tab_K_base : KL 340 = 0 ∧ KU 340 = 0 := by decide +kernel

theorem K_TB : ∀ k, 340 ≤ k → k ≤ 368 → TB Kfun 40 1000000000 KL KU k := by
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
    obtain ⟨j, hj⟩ : ∃ j, j = k - 40 := ⟨_, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, n = 379 - k := ⟨_, rfl⟩
    rw [← hj, ← hn] at c1 c2
    have hkj : k = j + 40 := by omega
    have hkn : 380 = k + n + 1 := by omega
    have hMr : (0 : ℝ) < (40 : ℕ) := by norm_num
    have hKr : (k : ℝ) = j + (40 : ℕ) := by exact_mod_cast hkj
    have hTr : ((380 : ℕ) : ℝ) = k + n + 1 := by exact_mod_cast hkn
    have hJ0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hk340 : (340 : ℝ) ≤ k := by exact_mod_cast hk
    have hk367 : (k : ℝ) ≤ 367 := by exact_mod_cast (show k ≤ 367 by omega)
    have h4 := TB_c4 k (by omega) (by omega)
    have h3 := TB_c3 j (by omega) (by omega)
    have h3' := TB_c3 (j + 1) (by omega) (by omega)
    unfold TB at h3'; push_cast at h3'
    have key := kgrid_step (G := Kfun) (f := cR 4) (e := cR 3) (M := ((40 : ℕ) : ℝ)) (J := j) (K := k)
      (n := n) (T := ((380 : ℕ) : ℝ)) (D := ((1000000000 : ℕ) : ℝ)) (Gl := KL k) (Gu := KU k)
      (Lf := cL4 k) (Uf := cU4 k) (Le := cL3 j) (Ue := cU3 (j + 1)) (Gl' := KL (k + 1))
      (Gu' := KU (k + 1)) hMr hKr hJ0 hTr hn0 (by norm_num) ?_ ?_
      (cR_monoOn 4 _ |>.mono (fun x hx => hx.1)) (cR_monoOn 3 _ |>.mono (fun x hx => hx.1))
      hgk h4 ⟨h3.1, h3'.2⟩ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast c1) (by exact_mod_cast c2)
    · unfold TB; push_cast; exact key
    · have e380 : ((380 : ℕ) : ℝ) / ((40 : ℕ) : ℝ) = 19 / 2 := by norm_num
      rw [e380]
      apply Kfun_delay
      · push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
      · push_cast; exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
      · push_cast; rw [div_lt_iff₀ (by norm_num)]; linarith
    · intro x hx
      have hp : ((2 : ℕ) : ℝ) + 2 ≤ (k : ℝ) / ((40 : ℕ) : ℝ) := by
        push_cast; rw [le_div_iff₀ (by norm_num)]; linarith
      exact cR_delay 2 hp hx.1

theorem tab_T5_vals : KL 368 = 520172550 ∧ KU 368 = 520837114 ∧ cL4 368 = 474987741 ∧
    cU4 368 = 475190374 ∧ cL3 328 = 1269956143 ∧ cU3 329 = 1276496293 ∧ cL5 408 = 111354505 ∧
    cU5 408 = 111453376 ∧ cL5 380 = 78027519 ∧ cU5 380 = 78109585 := by decide +kernel

/-- Linear bounds for `c₄` on `[9.2, τ]`, `τ = 1235/134 = 9.5 (1 - 1/33.5)`. -/
theorem c4_slope (x : ℝ) (hx : x ∈ Icc (46 / 5 : ℝ) (1235 / 134)) :
    474987741 / 1000000000 + 1269956143 / 1000000000 / (1235 / 134 - 1) * (x - 46 / 5) ≤ cR 4 x ∧
    cR 4 x ≤ 475190374 / 1000000000 + 1276496293 / 1000000000 / (46 / 5 - 1) * (x - 46 / 5) := by
  obtain ⟨_, _, v3, v4, v5, v6, _⟩ := tab_T5_vals
  have h4 := TB_c4 368 (by norm_num) (by norm_num)
  have h3 := TB_c3 328 (by norm_num) (by norm_num)
  have h3' := TB_c3 329 (by norm_num) (by norm_num)
  unfold TB at h4 h3 h3'
  rw [v3, v4] at h4; rw [v5] at h3; rw [v6] at h3'
  norm_num at h4 h3 h3'
  have hinc := incr (f := cR 4) (e := cR 3) (p := 46 / 5) (q := 1235 / 134) (by norm_num) (by norm_num)
    (fun y hy => cR_delay 2 (by norm_num) hy.1) (cR_monoOn 3 _ |>.mono (fun y hy => hy.1))
    ((cR_mono_nonneg 3).2 _) x hx
  have hq : cR 3 (1235 / 134 - 1) ≤ cR 3 (329 / 40) := (cR_mono_nonneg 3).1 (by norm_num)
  have hu0 : 0 ≤ x - 46 / 5 := by linarith [hx.1]
  have e1 : (46 / 5 : ℝ) - 1 = 41 / 5 := by norm_num
  have e2 : (46 / 5 : ℝ) = 46 / 5 := rfl
  rw [show (46 / 5 : ℝ) - 1 = 41 / 5 by norm_num] at hinc
  constructor
  · have hd : 1269956143 / 1000000000 / (1235 / 134 - 1) ≤ cR 3 (41 / 5) / (1235 / 134 - 1) :=
      div_le_div_of_nonneg_right (by linarith [h3.1]) (by norm_num)
    linarith [mul_le_mul_of_nonneg_left hd hu0, hinc.1, h4.1]
  · have hd : cR 3 (1235 / 134 - 1) / (41 / 5) ≤ 1276496293 / 1000000000 / (41 / 5) :=
      div_le_div_of_nonneg_right (by linarith [h3'.2]) (by norm_num)
    have : (1276496293 : ℝ) / 1000000000 / (46 / 5 - 1) = 1276496293 / 1000000000 / (41 / 5) := by
      norm_num
    rw [this]
    linarith [mul_le_mul_of_nonneg_left hd hu0, hinc.2, h4.2]

theorem K_tau_bounds : (0.5469695 : ℝ) ≤ Kfun (1235 / 134) ∧ Kfun (1235 / 134) ≤ 0.5476694 := by
  obtain ⟨v1, v2, _⟩ := tab_T5_vals
  have hK := K_TB 368 (by norm_num) le_rfl
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
  · have : (0.5469695 : ℝ) ≤ 520172550 / 1000000000 + (474987741 / 1000000000 *
        (2 * (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) - 1) /
          (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) + 1)) +
        1269956143 / 1000000000 / (1235 / 134 - 1) * (-(1235 / 134 - 46 / 5) + (19 / 2 - 46 / 5) *
        (2 * (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) - 1) /
          (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) + 1)))) := by norm_num
    have hpos1 : (0 : ℝ) ≤ 474987741 / 1000000000 := by norm_num
    have hpos2 : (0 : ℝ) ≤ 1269956143 / 1000000000 / (1235 / 134 - 1) * (19 / 2 - 46 / 5) := by
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hΛL hpos1, mul_le_mul_of_nonneg_left hΛL hpos2]
  · have : 520837114 / 1000000000 + (475190374 / 1000000000 *
        ((((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) -
          (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134))⁻¹) / 2) +
        1276496293 / 1000000000 / (46 / 5 - 1) * (-(1235 / 134 - 46 / 5) + (19 / 2 - 46 / 5) *
        ((((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134) -
          (((19 / 2 : ℝ) - 46 / 5) / (19 / 2 - 1235 / 134))⁻¹) / 2))) ≤ (0.5476694 : ℝ) := by
      norm_num
    have hpos1 : (0 : ℝ) ≤ 475190374 / 1000000000 := by norm_num
    have hpos2 : (0 : ℝ) ≤ 1276496293 / 1000000000 / (46 / 5 - 1) * (19 / 2 - 46 / 5) := by
      norm_num
    nlinarith [mul_le_mul_of_nonneg_left hΛU hpos1, mul_le_mul_of_nonneg_left hΛU hpos2]

theorem c5_tau1_bounds : (0.1122036 : ℝ) ≤ cR 5 (1369 / 134) ∧ cR 5 (1369 / 134) ≤ 0.1123030 := by
  obtain ⟨_, _, _, _, _, _, v7, v8, _⟩ := tab_T5_vals
  have h5 := TB_c5 408 (by norm_num) (by norm_num)
  unfold TB at h5; rw [v7, v8] at h5; norm_num at h5
  have ha : (1 : ℝ) < 51 / 5 := by norm_num
  have hab : (51 / 5 : ℝ) ≤ 1369 / 134 := by norm_num
  have hlo : ∀ u ∈ Icc (51 / 5 : ℝ) (1369 / 134), 474987741 / 1000000000 +
      1269956143 / 1000000000 / (1235 / 134 - 1) * (u - 51 / 5) ≤ cR 4 (u - 1) := by
    intro u hu
    have := (c4_slope (u - 1) ⟨by linarith [hu.1], by linarith [hu.2]⟩).1
    have e : u - 1 - 46 / 5 = u - 51 / 5 := by ring
    rw [e] at this; exact this
  have hhi : ∀ u ∈ Icc (51 / 5 : ℝ) (1369 / 134), cR 4 (u - 1) ≤ 475190374 / 1000000000 +
      1276496293 / 1000000000 / (46 / 5 - 1) * (u - 51 / 5) := by
    intro u hu
    have := (c4_slope (u - 1) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
    have e : u - 1 - 46 / 5 = u - 51 / 5 := by ring
    rw [e] at this; exact this
  have hy : 1 < ((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) := by norm_num
  obtain ⟨s1, s2⟩ := dstep (g := cR 5) (f := cR 4) ha hab
    (cR_delay 3 (by norm_num) hab) (cR_monoOn 4 _ |>.mono (fun y hy => hy.1)) hlo hhi
    (two_mul_div_le_log hy) (log_le_half_sub_inv hy.le) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  constructor
  · have : (0.1122036 : ℝ) ≤ 111354505 / 1000000000 + 474987741 / 1000000000 *
        (2 * (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) - 1) / (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) + 1)) +
        1269956143 / 1000000000 / (1235 / 134 - 1) * (1369 / 134 - 51 / 5 - (51 / 5 - 1) *
        ((((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) - (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1))⁻¹) / 2)) := by
      norm_num
    linarith [h5.1]
  · have : 111453376 / 1000000000 + 475190374 / 1000000000 *
        ((((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) - (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1))⁻¹) / 2) +
        1276496293 / 1000000000 / (46 / 5 - 1) * (1369 / 134 - 51 / 5 - (51 / 5 - 1) *
        (2 * (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) - 1) / (((1369 / 134 : ℝ) - 1) / (51 / 5 - 1) + 1)))
        ≤ (0.1123030 : ℝ) := by
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
`s = 33.5`, `t = 9.5`: `T₅ ∈ [0.3686, 0.369041]`. Printed: `[0.3687, 0.3689]`, page 32. -/
theorem T5_bounds : (0.3686 : ℝ) ≤ T5kuhn 33.5 9.5 ∧ T5kuhn 33.5 9.5 ≤ 0.369041 := by
  obtain ⟨_, _, _, _, _, _, _, _, v9, v10⟩ := tab_T5_vals
  have h5 := TB_c5 380 (by norm_num) (by norm_num)
  unfold TB at h5; rw [v9, v10] at h5; norm_num at h5
  have hK := K_tau_bounds
  have hc := c5_tau1_bounds
  rw [T5_split]
  constructor <;> linarith [h5.1, h5.2, hK.1, hK.2, hc.1, hc.2]

open LeanLab.Akeno2026.Thm12Numerics in
/-- Theorem 1.2, CONDITIONAL ON: `prop44`, Proposition 4.4 with `M_k` and the piecewise smooth
class abstract; `hPS`; `hω`, a pair `ω±` as in Lemma 4.1, whose existence is classical but not
proved here; `hdecomp`, the reduction of `M₄` for Kuhn's weight at `θ = 0.1635`, `s = 33.5`,
`t = 9.5` to `s ω⁻(sθ) - s I - (2/θ)(T₅ + ⋯ + T₁₀)` with `T₅` given by the page 36 formula
`T5kuhn`; and the printed enclosures of the `F`-integral `I` and of `T₆,…,T₁₀`.
Compared with `Thm12Numerics.thm1_2_of_prop44`, the printed enclosures of `ω⁻(sθ)` and `T₅` are
no longer hypotheses: they are `omega_minus_bounds` and `T5_bounds`, PROVED. -/
theorem thm1_2_certified
    (Mk : ℕ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (PwSmooth : (ℝ → ℝ) → Prop)
    (prop44 : ∀ k : ℕ, 2 ≤ k → ∀ θ s : ℝ, θ < 1 / 6 → 1 / θ < s → ∀ F : ℝ → ℝ,
      PwSmooth F → (∀ u, 0 ≤ F u) →
      (∃ ε : ℝ, 0 < ε ∧ Function.support F ⊆ Set.Icc 0 (θ - ε)) →
      0 < Mk k F θ s → AlmostAllDyadic Even (DiffForm k))
    (hPS : PwSmooth (kuhnF 9.5))
    (ωp ωm : ℝ → ℝ) (hω : IsOmegaPair ωp ωm)
    (I T6 T7 T8 T9 T10 : ℝ)
    (hdecomp : Mk 4 (kuhnF 9.5) 0.1635 33.5 =
      33.5 * ωm (0.1635 * 33.5) - 33.5 * I -
        2 / 0.1635 * (T5kuhn 33.5 9.5 + T6 + T7 + T8 + T9 + T10))
    (hI : 0.40941 ≤ I ∧ I ≤ 0.40943)
    (h6 : 0.04192 ≤ T6 ∧ T6 ≤ 0.04193)
    (h7 : 0.001818 ≤ T7 ∧ T7 ≤ 0.001819) (h8 : 1.913e-5 ≤ T8 ∧ T8 ≤ 1.914e-5)
    (h9 : 1.327e-8 ≤ T9 ∧ T9 ≤ 1.329e-8) (h10 : 1.017e-16 ≤ T10 ∧ T10 ≤ 1.023e-16) :
    AlmostAllDyadic Even (DiffForm 4) := by
  refine prop44 4 (by norm_num) 0.1635 33.5 (by norm_num) (by norm_num) (kuhnF 9.5) hPS
    (kuhnF_nonneg 9.5) ⟨0.1635 - 1 / 9.5, by norm_num, ?_⟩ ?_
  · refine (kuhnF_support 9.5).trans ?_
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  · rw [hdecomp]
    have hωb := omega_minus_bounds hω
    have hT5 := T5_bounds
    obtain ⟨_, _⟩ := hI; obtain ⟨_, _⟩ := h6; obtain ⟨_, _⟩ := h7; obtain ⟨_, _⟩ := h8
    obtain ⟨_, _⟩ := h9; obtain ⟨_, _⟩ := h10
    norm_num at hωb hT5 ⊢
    nlinarith [hωb.1, hT5.2]

/-- The certified enclosures alone, with the printed ones for `I` and `T₆,…,T₁₀`, give
`M₄ ≥ 0.0336`. -/
theorem m4_certified_margin :
    (0.0336 : ℝ) ≤ 33.5 * 0.561171 - 33.5 * 0.40943 - 2 / 0.1635 *
      (0.369041 + 0.04193 + 0.001819 + 1.914e-5 + 1.329e-8 + 1.023e-16) := by
  norm_num

open LeanLab.Akeno2026.Thm12Numerics in
/-- `Thm12Numerics.thm1_2_of_prop44` with the printed enclosure of `ω⁻(sθ)` discharged by
`omega_minus_bounds`, PROVED, and the simplex `T₅` kept abstract with its printed enclosure.
CONDITIONAL ON the remaining inputs of `thm1_2_of_prop44` and on `hω`. -/
theorem thm1_2_omega_certified
    (Mk : ℕ → (ℝ → ℝ) → ℝ → ℝ → ℝ) (PwSmooth : (ℝ → ℝ) → Prop)
    (prop44 : ∀ k : ℕ, 2 ≤ k → ∀ θ s : ℝ, θ < 1 / 6 → 1 / θ < s → ∀ F : ℝ → ℝ,
      PwSmooth F → (∀ u, 0 ≤ F u) →
      (∃ ε : ℝ, 0 < ε ∧ Function.support F ⊆ Set.Icc 0 (θ - ε)) →
      0 < Mk k F θ s → AlmostAllDyadic Even (DiffForm k))
    (hPS : PwSmooth (kuhnF 9.5))
    (ωp ωm : ℝ → ℝ) (hω : IsOmegaPair ωp ωm)
    (I T5 T6 T7 T8 T9 T10 : ℝ)
    (hdecomp : Mk 4 (kuhnF 9.5) 0.1635 33.5 =
      33.5 * ωm (0.1635 * 33.5) - 33.5 * I - 2 / 0.1635 * (T5 + T6 + T7 + T8 + T9 + T10))
    (hI : 0.40941 ≤ I ∧ I ≤ 0.40943)
    (h5 : 0.3687 ≤ T5 ∧ T5 ≤ 0.3689) (h6 : 0.04192 ≤ T6 ∧ T6 ≤ 0.04193)
    (h7 : 0.001818 ≤ T7 ∧ T7 ≤ 0.001819) (h8 : 1.913e-5 ≤ T8 ∧ T8 ≤ 1.914e-5)
    (h9 : 1.327e-8 ≤ T9 ∧ T9 ≤ 1.329e-8) (h10 : 1.017e-16 ≤ T10 ∧ T10 ≤ 1.023e-16) :
    AlmostAllDyadic Even (DiffForm 4) :=
  thm1_2_of_prop44 Mk PwSmooth prop44 hPS (ωm (0.1635 * 33.5)) I T5 T6 T7 T8 T9 T10 hdecomp
    (omega_minus_bounds hω) hI h5 h6 h7 h8 h9 h10

end LeanLab.Akeno2026.Thm12Certified
