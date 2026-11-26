/-
P0083 Perelli 1996, page 482, equation 6 of the proof of the named Lemma.
ROUTE BURST S79 burst-20261122 split of Diff1122.leaf_weyl_differencing.
The k-1 fold Weyl differencing and the count of difference tuples by τ_k are LEAFs;
grouping the tuples by the frequency m and choosing one interval per m is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.VaughanInput

namespace LeanLab.Perelli1996.Weyl1122
open Finset Real Polynomial
open LeanLab.Perelli1996.Section2
noncomputable section

/-- The difference tuples (h_1, ..., h_(k-1)) with 1 ≤ |h_i| ≤ R. -/
abbrev tuples (k R : ℕ) : Finset (Fin (k - 1) → ℤ) :=
  Fintype.piFinset fun _ => (Icc (-(R : ℤ)) R).filter (· ≠ 0)

/-- The frequency k! a_k |h_1 ⋯ h_(k-1)| of the linear (k-1)-th difference, page 482. -/
abbrev freq (k a : ℕ) (h : Fin (k - 1) → ℤ) : ℕ := k.factorial * a * (∏ i, h i).natAbs

/-! Proof of leaf_iterated_differencing, burst 1123: Vaughan 1981 Lemmas 2.3 and 2.4,
the k-1 th difference of F and the count of tuples with a zero entry. -/
namespace Iter

/-- The forward difference f(n+h) - f(n), Vaughan 1981 Lemma 2.3. -/
def fdiff {G : Type*} [AddCommGroup G] (h : ℤ) (f : ℤ → G) : ℤ → G := fun n => f (n + h) - f n

/-- The j fold difference Δ_{h_j} ⋯ Δ_{h_1} f, Vaughan 1981 Lemma 2.4. -/
def idiff {G : Type*} [AddCommGroup G] : (j : ℕ) → (Fin j → ℤ) → (ℤ → G) → ℤ → G
  | 0, _, f => f
  | j + 1, h, f => fdiff (h (Fin.last j)) (idiff j (Fin.init h) f)

/-- The exponential sum ∑_{a ≤ n < b} e(f(n)) over an interval of integers. -/
def isum (f : ℤ → ℝ) (a b : ℤ) : ℂ := ∑ n ∈ Ico a b, Kernel.e (f n)

/-- The difference commutes with an additive map. -/
theorem idiff_map {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G') :
    ∀ (j : ℕ) (h : Fin j → ℤ) (g : ℤ → G) (n : ℤ), idiff j h (fun m => φ (g m)) n = φ (idiff j h g n)
  | 0, _, _, _ => rfl
  | j + 1, h, g, n => by
    simp only [idiff, fdiff]
    rw [idiff_map φ j, idiff_map φ j, map_sub]

theorem e_add (x y : ℝ) : Kernel.e (x + y) = Kernel.e x * Kernel.e y := by
  unfold Kernel.e; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem norm_e (x : ℝ) : ‖Kernel.e x‖ = 1 := by
  unfold Kernel.e; rw [Complex.norm_exp]; simp

theorem e_neg (x : ℝ) : Kernel.e (-x) = starRingEnd ℂ (Kernel.e x) := by
  unfold Kernel.e; rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, map_ofNat]

theorem norm_T_neg (A L : ℕ) (y : ℝ) : ‖Kernel.T A L (-y)‖ = ‖Kernel.T A L y‖ := by
  have : Kernel.T A L (-y) = starRingEnd ℂ (Kernel.T A L y) := by
    unfold Kernel.T; rw [map_sum]; refine Finset.sum_congr rfl fun n _ => ?_
    rw [← e_neg]; congr 1; ring
  rw [this, Complex.norm_conj]

theorem isum_lin (A B : ℤ) (hA : 0 ≤ A) (y : ℝ) :
    ∑ n ∈ Ico A B, Kernel.e ((n : ℝ) * y) = Kernel.T A.toNat (B - A).toNat y := by
  unfold Kernel.T
  refine Finset.sum_nbij' (fun n => (n - A).toNat) (fun m => A + m) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [mem_Ico, mem_range] at hn ⊢; omega
  · intro m hm; simp only [mem_Ico, mem_range] at hm ⊢; omega
  · intro n hn; simp only [mem_Ico] at hn ⊢; omega
  · intro m hm; simp only [mem_range] at hm ⊢; omega
  · intro n hn
    simp only [mem_Ico] at hn
    have : ((A.toNat + (n - A).toNat : ℕ) : ℤ) = n := by omega
    have h2 : ((A.toNat + (n - A).toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast this
    rw [h2]

theorem norm_isum_le (g : ℤ → ℝ) (a b : ℤ) : ‖isum g a b‖ ≤ ((b - a).toNat : ℝ) := by
  unfold isum
  calc ‖∑ n ∈ Ico a b, Kernel.e (g n)‖ ≤ ∑ n ∈ Ico a b, ‖Kernel.e (g n)‖ := norm_sum_le _ _
    _ = ((b - a).toNat : ℝ) := by simp [norm_e]


/-- Vaughan 1981 Lemma 2.3, one step of Weyl differencing on an interval of at most
M+1 integers. -/
theorem one_step (M : ℕ) (g : ℤ → ℝ) (a b : ℤ) (hab : b - a ≤ M + 1) :
    ‖isum g a b‖ ^ 2 ≤ ∑ h ∈ Icc (-(M : ℤ)) M,
      ‖isum (fdiff h g) (max a (a - h)) (min b (b - h))‖ := by
  have hsq : ((‖isum g a b‖ ^ 2 : ℝ) : ℂ) = ∑ h ∈ Icc (-(M : ℤ)) M,
      isum (fdiff h g) (max a (a - h)) (min b (b - h)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', isum, map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
    unfold isum fdiff
    rw [Finset.sum_sigma']
    refine Finset.sum_nbij' (fun p => ⟨p.1 - p.2, p.2⟩) (fun x => (x.2 + x.1, x.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [mem_product, mem_sigma, mem_Icc, mem_Ico] at hp ⊢
      omega
    · intro x hx
      simp only [mem_product, mem_sigma, mem_Icc, mem_Ico] at hx ⊢
      omega
    · intro p hp; simp
    · intro x hx; simp
    · intro p hp
      rw [← e_neg, ← e_add]
      congr 1
      have : p.2 + (p.1 - p.2) = p.1 := by ring
      show g p.1 + -g p.2 = g (p.2 + (p.1 - p.2)) - g p.2
      rw [this]; ring
  have : ‖isum g a b‖ ^ 2 = ‖∑ h ∈ Icc (-(M : ℤ)) M,
      isum (fdiff h g) (max a (a - h)) (min b (b - h))‖ := by
    rw [← hsq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [this]
  exact norm_sum_le _ _

/-- Splitting a tuple into its first j entries and its last entry. -/
theorem piFinset_succ_sum (j : ℕ) (Q : Finset ℤ) (G : (Fin (j + 1) → ℤ) → ℝ) :
    ∑ h ∈ Fintype.piFinset (fun _ : Fin (j + 1) => Q), G h =
      ∑ h0 ∈ Fintype.piFinset (fun _ : Fin j => Q), ∑ t ∈ Q, G (Fin.snoc h0 t) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun h => (Fin.init h, h (Fin.last j))) (fun p => Fin.snoc p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro h hh
    rw [Fin.mem_piFinset_iff_last_init] at hh
    simp only [mem_product]
    exact ⟨hh.2, hh.1⟩
  · intro p hp
    simp only [mem_product] at hp
    rw [Fin.mem_piFinset_iff_last_init]
    simp only [Fin.snoc_last, Fin.init_snoc]
    exact ⟨hp.2, hp.1⟩
  · intro h _; simp
  · intro p _; simp
  · intro h _; simp

/-- Vaughan 1981 Lemma 2.4, the iteration of Lemma 2.3 with Cauchy's inequality. -/
theorem iterated (M : ℕ) (f : ℤ → ℝ) (a b : ℤ) (hab : b - a ≤ M + 1) : ∀ j : ℕ,
    ∃ a' b' : (Fin j → ℤ) → ℤ, (∀ h, a ≤ a' h ∧ b' h - a' h ≤ M + 1) ∧
      ‖isum f a b‖ ^ (2 ^ j) ≤ (2 * M + 1 : ℝ) ^ (2 ^ j - j - 1) *
        ∑ h ∈ Fintype.piFinset (fun _ : Fin j => Icc (-(M : ℤ)) M),
          ‖isum (idiff j h f) (a' h) (b' h)‖
  | 0 => ⟨fun _ => a, fun _ => b, fun _ => ⟨le_rfl, hab⟩, by simp [idiff]⟩
  | j + 1 => by
    obtain ⟨a', b', hinv, hb⟩ := iterated M f a b hab j
    refine ⟨fun h => max (a' (Fin.init h)) (a' (Fin.init h) - h (Fin.last j)),
      fun h => min (b' (Fin.init h)) (b' (Fin.init h) - h (Fin.last j)), ?_, ?_⟩
    · intro h; have := hinv (Fin.init h); simp only; constructor <;> omega
    rw [piFinset_succ_sum]
    simp only [idiff, Fin.init_snoc, Fin.snoc_last]
    set P := Fintype.piFinset (fun _ : Fin j => Icc (-(M : ℤ)) M) with hP
    have hcard : (P.card : ℝ) = (2 * M + 1 : ℝ) ^ j := by
      rw [hP, Fintype.card_piFinset, prod_const, Int.card_Icc, card_univ, Fintype.card_fin]
      have : (↑M + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
      rw [this]; push_cast; ring
    have hstep : ∀ h0 ∈ P, ‖isum (idiff j h0 f) (a' h0) (b' h0)‖ ^ 2 ≤
        ∑ t ∈ Icc (-(M : ℤ)) M, ‖isum (fdiff t (idiff j h0 f)) (max (a' h0) (a' h0 - t))
          (min (b' h0) (b' h0 - t))‖ := fun h0 _ => one_step M _ _ _ (hinv h0).2
    set E := 2 ^ j - j - 1 with hE
    have hE' : 2 ^ (j + 1) - (j + 1) - 1 = 2 * E + j := by
      have := Nat.lt_two_pow_self (n := j)
      rw [pow_succ]; omega
    rw [hE']
    have hpos : (0 : ℝ) ≤ 2 * M + 1 := by positivity
    calc ‖isum f a b‖ ^ 2 ^ (j + 1) = (‖isum f a b‖ ^ 2 ^ j) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ ((2 * M + 1 : ℝ) ^ E * ∑ h ∈ P, ‖isum (idiff j h f) (a' h) (b' h)‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hb 2
      _ = (2 * M + 1 : ℝ) ^ (2 * E) * (∑ h ∈ P, ‖isum (idiff j h f) (a' h) (b' h)‖) ^ 2 := by
          ring
      _ ≤ (2 * M + 1 : ℝ) ^ (2 * E) *
            (P.card * ∑ h ∈ P, ‖isum (idiff j h f) (a' h) (b' h)‖ ^ 2) := by
          gcongr; exact sq_sum_le_card_mul_sum_sq
      _ ≤ (2 * M + 1 : ℝ) ^ (2 * E) * ((2 * M + 1 : ℝ) ^ j * ∑ h0 ∈ P, ∑ t ∈ Icc (-(M : ℤ)) M,
            ‖isum (fdiff t (idiff j h0 f)) (max (a' h0) (a' h0 - t))
              (min (b' h0) (b' h0 - t))‖) := by
          rw [hcard]; gcongr with h0 hh0; exact hstep h0 hh0
      _ = _ := by rw [pow_add]; ring
/-- Proved: Vaughan 1981 Lemma 2.4, the j fold Weyl differencing obtained by iterating
Lemma 2.3 with Cauchy's inequality, for an interval I of at most M+1 consecutive integers:
|∑_{n ∈ I} e(f(n))|^(2^j) ≤ (2M+1)^(2^j - j - 1) ∑_{|h_i| ≤ M} |∑_{n ∈ I_h} e(Δ_h f(n))|,
I_h a subinterval of I. This is the first half of page 482 equation 6 before the polynomial
is specialised. Class MEDIUM. -/
theorem vaughan_iterated (j M : ℕ) (_hj : 1 ≤ j) (f : ℤ → ℝ) (a b : ℤ)
    (hab : b - a ≤ M + 1) :
    ∃ a' b' : (Fin j → ℤ) → ℤ, (∀ h, a ≤ a' h ∧ b' h - a' h ≤ M + 1) ∧
      ‖isum f a b‖ ^ (2 ^ j) ≤ (2 * M + 1 : ℝ) ^ (2 ^ j - j - 1) *
        ∑ h ∈ Fintype.piFinset (fun _ : Fin j => Icc (-(M : ℤ)) M),
          ‖isum (idiff j h f) (a' h) (b' h)‖ :=
  iterated M f a b hab j

/-- The j fold difference on polynomials, Δ_h P = P(X + h) - P, Vaughan 1981 Lemma 2.4. -/
def pdiff : (j : ℕ) → (Fin j → ℤ) → ℤ[X] → ℤ[X]
  | 0, _, P => P
  | j + 1, h, P => taylor (h (Fin.last j)) (pdiff j (Fin.init h) P) - pdiff j (Fin.init h) P

/-- The polynomial difference evaluates to the difference of the values. -/
theorem eval_pdiff (P : ℤ[X]) : ∀ (j : ℕ) (h : Fin j → ℤ) (n : ℤ),
    (pdiff j h P).eval n = idiff j h (fun n => P.eval n) n
  | 0, _, _ => rfl
  | j + 1, h, n => by
    simp only [pdiff, idiff, fdiff, eval_sub, taylor_eval]
    rw [eval_pdiff P j, eval_pdiff P j]

/-- The top Hasse derivative is the top coefficient. -/
theorem hasse_eval_top (P : ℤ[X]) (N : ℕ) (hN : P.natDegree ≤ N) (h : ℤ) :
    (hasseDeriv N P).eval h = P.coeff N := by
  rw [eq_C_of_natDegree_eq_zero (p := hasseDeriv N P) (by rw [natDegree_hasseDeriv]; omega),
    eval_C, hasseDeriv_coeff]
  simp

/-- One difference lowers the degree by one, the new top coefficient is m h a_m. -/
theorem diff_step (P : ℤ[X]) (m : ℕ) (hm : 1 ≤ m) (hP : P.natDegree ≤ m) (h : ℤ) :
    (taylor h P - P).natDegree ≤ m - 1 ∧
      (taylor h P - P).coeff (m - 1) = m * h * P.coeff m := by
  constructor
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sub, taylor_coeff, hasse_eval_top P N (by omega)]
    simp
  · rw [coeff_sub, taylor_coeff]
    have h1 : (hasseDeriv (m - 1) P).natDegree ≤ 1 := by
      rw [natDegree_hasseDeriv]; omega
    rw [eq_X_add_C_of_natDegree_le_one h1]
    simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff]
    have h2 : 1 + (m - 1) = m := by omega
    rw [h2]
    have h3 : m.choose (m - 1) = m := by
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      simp
    rw [h3]
    simp
    ring

/-- After j differences the top coefficient is m(m-1)⋯(m-j+1) h_1⋯h_j a_m. -/
theorem pdiff_shape (P : ℤ[X]) (m : ℕ) (hP : P.natDegree ≤ m) : ∀ (j : ℕ) (h : Fin j → ℤ), j ≤ m →
    (pdiff j h P).natDegree ≤ m - j ∧
      (pdiff j h P).coeff (m - j) = (m.descFactorial j : ℤ) * (∏ i, h i) * P.coeff m
  | 0, _, _ => by simp [pdiff, hP]
  | j + 1, h, hj => by
    obtain ⟨ih1, ih2⟩ := pdiff_shape P m hP j (Fin.init h) (by omega)
    obtain ⟨s1, s2⟩ := diff_step (pdiff j (Fin.init h) P) (m - j) (by omega) ih1 (h (Fin.last j))
    have e1 : m - j - 1 = m - (j + 1) := by omega
    refine ⟨by simp only [pdiff]; rw [← e1]; exact s1, ?_⟩
    simp only [pdiff]
    rw [← e1, s2, ih2, Nat.descFactorial_succ, Fin.prod_univ_castSucc]
    simp only [Fin.init]
    push_cast [Nat.cast_sub (show j ≤ m by omega)]
    ring

/-- Proved: page 482, the k-1 th difference of F of degree k is linear in n with slope
k! a_k h_1 ⋯ h_(k-1), Vaughan 1981 proof of Lemma 2.4 and Theorem 2.1. Class EASY. -/
theorem poly_difference (F : ℤ[X]) (hk : 1 ≤ F.natDegree) :
    ∃ c : (Fin (F.natDegree - 1) → ℤ) → ℤ, ∀ h n,
      idiff (F.natDegree - 1) h (fun n => F.eval n) n =
        (F.natDegree.factorial : ℤ) * F.leadingCoeff * (∏ i, h i) * n + c h := by
  refine ⟨fun h => (pdiff _ h F).coeff 0, fun h n => ?_⟩
  obtain ⟨s1, s2⟩ := pdiff_shape F F.natDegree le_rfl (F.natDegree - 1) h (by omega)
  have e1 : F.natDegree - (F.natDegree - 1) = 1 := by omega
  rw [e1] at s1 s2
  rw [← eval_pdiff, eq_X_add_C_of_natDegree_le_one s1, s2]
  have hd : (F.natDegree.descFactorial (F.natDegree - 1) : ℤ) = F.natDegree.factorial := by
    have := Nat.factorial_mul_descFactorial (show F.natDegree - 1 ≤ F.natDegree by omega)
    rw [e1] at this
    simp at this
    exact_mod_cast this
  simp only [eval_add, eval_mul, eval_C, eval_X, hd, leadingCoeff]
  ring

/-- Proved: page 482, the tuples with some h_i = 0: at most j (2M+1)^(j-1) of the
(2M+1)^j tuples with |h_i| ≤ M have a zero entry. Class EASY. -/
theorem zero_tuples (j M : ℕ) :
    ((Fintype.piFinset fun _ : Fin j => Icc (-(M : ℤ)) M).filter
      (fun h => ∃ i, h i = 0)).card ≤ j * (2 * M + 1) ^ (j - 1) := by
  classical
  set P := Fintype.piFinset fun _ : Fin j => Icc (-(M : ℤ)) M
  have hsub : P.filter (fun h => ∃ i, h i = 0) ⊆
      Finset.univ.biUnion (fun i : Fin j =>
        Fintype.piFinset (Function.update (fun _ : Fin j => Icc (-(M : ℤ)) M) i {0})) := by
    intro h hh
    simp only [P, mem_filter, Fintype.mem_piFinset] at hh
    obtain ⟨hP, i, hi⟩ := hh
    simp only [mem_biUnion, mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨i, fun a => ?_⟩
    by_cases ha : a = i
    · subst ha; simp [hi]
    · rw [Function.update_of_ne ha]; exact hP a
  have hcard : ∀ i : Fin j, (Fintype.piFinset
      (Function.update (fun _ : Fin j => Icc (-(M : ℤ)) M) i {0})).card = (2 * M + 1) ^ (j - 1) := by
    intro i
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (mem_univ i)]
    rw [Function.update_self, card_singleton, one_mul]
    rw [Finset.prod_congr rfl (fun a ha => by rw [Function.update_of_ne (ne_of_mem_erase ha)])]
    rw [prod_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, Int.card_Icc]
    congr 1
    omega
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ i : Fin j, (Fintype.piFinset
      (Function.update (fun _ : Fin j => Icc (-(M : ℤ)) M) i {0})).card := card_biUnion_le
    _ = j * (2 * M + 1) ^ (j - 1) := by simp [hcard]

/-- The window as an integer interval. -/
theorem kernel_eq_isum (F : ℤ[X]) (N H α : ℝ) :
    polynomialKernel F N H α =
      isum (fun n => ((F.eval n : ℤ) : ℝ) * α) (⌈N ^ (1 / (F.natDegree : ℝ))⌉₊ : ℤ)
        ((⌊N ^ (1 / (F.natDegree : ℝ)) + H⌋₊ : ℤ) + 1) := by
  unfold polynomialKernel isum win Fv
  refine Finset.sum_nbij' (fun n : ℕ => (n : ℤ)) (fun m => m.toNat) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [mem_Icc, mem_Ico] at hn ⊢; omega
  · intro m hm; simp only [mem_Icc, mem_Ico] at hm ⊢; omega
  · intro n hn; simp
  · intro m hm; simp only [mem_Ico] at hm ⊢; omega
  · intro n hn; simp

/-- The window has at most ⌊H⌋ + 1 points. -/
theorem window_length (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) :
    (⌊x + H⌋₊ : ℤ) + 1 - (⌈x⌉₊ : ℤ) ≤ (⌊H⌋₊ : ℤ) + 1 := by
  by_contra hc
  have h1 : ⌈x⌉₊ + ⌊H⌋₊ + 1 ≤ ⌊x + H⌋₊ := by omega
  have h2 : ((⌈x⌉₊ + ⌊H⌋₊ + 1 : ℕ) : ℝ) ≤ x + H := by
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))
  have h3 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h4 : H < (⌊H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one H
  push_cast at h2
  linarith


/-- A linear sum with a constant phase reduces to Kernel.T at the absolute frequency. -/
theorem norm_lin_sum (A B : ℤ) (hA : 0 ≤ A) (z d : ℤ) (α : ℝ) :
    ‖∑ n ∈ Ico A B, Kernel.e (((z * n + d : ℤ) : ℝ) * α)‖ =
      ‖Kernel.T A.toNat (B - A).toNat (α * (z.natAbs : ℕ))‖ := by
  have hs : ∑ n ∈ Ico A B, Kernel.e (((z * n + d : ℤ) : ℝ) * α) =
      (∑ n ∈ Ico A B, Kernel.e ((n : ℝ) * ((z : ℝ) * α))) * Kernel.e ((d : ℝ) * α) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun n _ => ?_
    rw [← e_add]; congr 1; push_cast; ring
  rw [hs, norm_mul, norm_e, mul_one, isum_lin A B hA]
  rcases Int.natAbs_eq z with hz | hz
  · congr 2; rw [hz]; push_cast; simp; ring
  · rw [← norm_T_neg]; congr 2; rw [hz]; push_cast; simp; ring

end Iter
open Iter

/-- LEAF: Page 482 equation 6, first half, as in Vaughan 1981 Lemma 2.4 with j = k-1:
|K(F,α)|^K ≪ H^(K-k) (H^(k-1) + ∑_h |∑_{n ∈ I_h} e(α k! a_k h_1⋯h_(k-1) n)|), the sum over
tuples with 1 ≤ |h_i| ≤ H, the tuples with some h_i = 0 contributing H^(k-1), and I_h an
interval of at most H+1 consecutive integers. The constant term of the linear difference
and the sign of the product do not change the modulus. Class MEDIUM. -/
theorem leaf_iterated_differencing (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H α : ℝ, N₀ ≤ N → 1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∃ start len : (Fin (F.natDegree - 1) → ℤ) → ℕ, (∀ h, (len h : ℝ) ≤ H + 1) ∧
        ‖polynomialKernel F N H α‖ ^ weylExponent F ≤
          C * H ^ (weylExponent F - F.natDegree) *
            (H ^ (F.natDegree - 1) +
              ∑ h ∈ tuples F.natDegree ⌊H⌋₊,
                ‖Kernel.T (start h) (len h) (α * (freq F.natDegree F.leadingCoeff.natAbs h : ℕ))‖) := by
  obtain ⟨hk1, hlc⟩ := hF
  set k := F.natDegree with hkdef
  obtain ⟨c, hc⟩ : ∃ c : (Fin (k - 1) → ℤ) → ℤ, ∀ h n,
      idiff (k - 1) h (fun n => F.eval n) n =
        (k.factorial : ℤ) * F.leadingCoeff * (∏ i, h i) * n + c h :=
    poly_difference F (by omega)
  set E := 2 ^ (k - 1) - (k - 1) - 1 with hE
  refine ⟨3 ^ E * (2 * (k - 1 : ℝ) * 3 ^ (k - 2) + 1), 3, ?_, le_rfl, ?_⟩
  · have : (1 : ℝ) ≤ k - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    positivity
  intro N H α hN hH _
  set x := N ^ (1 / (k : ℝ)) with hxdef
  have hx : 0 ≤ x := rpow_nonneg (by linarith) _
  set M := ⌊H⌋₊ with hMdef
  have hMH : (M : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using hH)
  set f : ℤ → ℝ := fun n => ((F.eval n : ℤ) : ℝ) * α with hf
  obtain ⟨a', b', hab', hbound⟩ := vaughan_iterated (k - 1) M (by omega) f
    (⌈x⌉₊ : ℤ) ((⌊x + H⌋₊ : ℤ) + 1) (window_length x H hx (by linarith))
  refine ⟨fun h => (a' h).toNat, fun h => (b' h - a' h).toNat, ?_, ?_⟩
  · intro h
    have h1 := (hab' h).2
    have : ((b' h - a' h).toNat : ℝ) ≤ M + 1 := by
      exact_mod_cast (show (b' h - a' h).toNat ≤ M + 1 by omega)
    linarith
  have hkE : k ≤ 2 ^ (k - 1) := by
    have := Nat.lt_two_pow_self (n := k - 1)
    omega
  have hK : weylExponent F = ((2 ^ (k - 1) : ℕ) : ℝ) := by simp [weylExponent, k]
  have hEk : ((2 ^ (k - 1) : ℕ) : ℝ) - (k : ℝ) = (E : ℝ) := by
    rw [hE, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hK, Real.rpow_natCast, kernel_eq_isum, hEk, Real.rpow_natCast]
  refine hbound.trans ?_
  set P := Fintype.piFinset (fun _ : Fin (k - 1) => Icc (-(M : ℤ)) M) with hP
  have hdf : ∀ h n, idiff (k - 1) h f n =
      ((idiff (k - 1) h (fun n => F.eval n) n : ℤ) : ℝ) * α := by
    intro h n
    have := idiff_map ((AddMonoidHom.mulRight α).comp (Int.castAddHom ℝ)) (k - 1) h
      (fun n => F.eval n) n
    simpa [hf] using this
  have hterm : ∀ h, ‖isum (idiff (k - 1) h f) (a' h) (b' h)‖ =
      ‖Kernel.T (a' h).toNat (b' h - a' h).toNat (α * (freq k F.leadingCoeff.natAbs h : ℕ))‖ := by
    intro h
    have ha0 : 0 ≤ a' h := le_trans (by positivity) (hab' h).1
    have hfr : freq k F.leadingCoeff.natAbs h = ((k.factorial : ℤ) * F.leadingCoeff * (∏ i, h i)).natAbs := by
      simp [freq, Int.natAbs_mul]
    unfold isum
    simp_rw [hdf, hc]
    rw [hfr, ← norm_lin_sum (a' h) (b' h) ha0 _ (c h) α]
  have hsplit := (Finset.sum_filter_add_sum_filter_not P (fun h => ∃ i, h i = 0)
    (fun h => ‖isum (idiff (k - 1) h f) (a' h) (b' h)‖)).symm
  have hT : P.filter (fun h => ¬ ∃ i, h i = 0) = tuples k M := by
    ext h; simp [hP, tuples, Fintype.mem_piFinset]
    exact ⟨fun ⟨u, v⟩ i => ⟨u i, v i⟩, fun w => ⟨fun i => (w i).1, fun i => (w i).2⟩⟩
  have hR : ∑ h ∈ tuples k M, ‖Kernel.T ((fun h => (a' h).toNat) h)
      ((fun h => (b' h - a' h).toNat) h) (α * (freq k F.leadingCoeff.natAbs h : ℕ))‖ =
      ∑ h ∈ tuples k M, ‖isum (idiff (k - 1) h f) (a' h) (b' h)‖ :=
    Finset.sum_congr rfl fun h _ => (hterm h).symm
  rw [hsplit, hT, hR, ← hE]
  set Tm := ∑ h ∈ tuples k M, ‖isum (idiff (k - 1) h f) (a' h) (b' h)‖ with hTm
  set Z := ∑ h ∈ P with ∃ i, h i = 0, ‖isum (idiff (k - 1) h f) (a' h) (b' h)‖ with hZdef
  have hT0 : 0 ≤ Tm := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hZ1 : Z ≤ ((P.filter fun h => ∃ i, h i = 0).card : ℝ) * (M + 1) := by
    have := Finset.sum_le_card_nsmul (P.filter fun h => ∃ i, h i = 0)
      (fun h => ‖isum (idiff (k - 1) h f) (a' h) (b' h)‖) ((M : ℝ) + 1) (fun h _ => by
        refine (norm_isum_le _ _ _).trans ?_
        exact_mod_cast (show (b' h - a' h).toNat ≤ M + 1 by have := (hab' h).2; omega))
    rw [nsmul_eq_mul] at this; exact this
  have hcard : ((P.filter fun h => ∃ i, h i = 0).card : ℝ) ≤ (k - 1 : ℝ) * (2 * M + 1) ^ (k - 2) := by
    have := zero_tuples (k - 1) M
    have h2 : k - 1 - 1 = k - 2 := by omega
    rw [h2] at this
    have h3 : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1]; simp
    rw [← h3]; exact_mod_cast this
  have hk1r : (1 : ℝ) ≤ k - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hb : (2 * (M : ℝ) + 1) ≤ 3 * H := by linarith
  have hb0 : (0 : ℝ) ≤ 2 * (M : ℝ) + 1 := by positivity
  have hH0 : (0 : ℝ) ≤ H := by linarith
  have hpE : (2 * (M : ℝ) + 1) ^ E ≤ 3 ^ E * H ^ E := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hb0 hb E
  have hpk : (2 * (M : ℝ) + 1) ^ (k - 2) ≤ 3 ^ (k - 2) * H ^ (k - 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hb0 hb _
  have hHk : H ^ (k - 1) = H ^ (k - 2) * H := by
    rw [← pow_succ]; congr 1; omega
  set A : ℝ := 2 * (k - 1 : ℝ) * 3 ^ (k - 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hZ : Z ≤ A * H ^ (k - 1) := by
    refine hZ1.trans ?_
    have hM1' : (M : ℝ) + 1 ≤ 2 * H := by linarith
    calc ((P.filter fun h => ∃ i, h i = 0).card : ℝ) * (M + 1)
        ≤ ((k - 1 : ℝ) * (3 ^ (k - 2) * H ^ (k - 2))) * (2 * H) := by
          apply mul_le_mul _ hM1' (by positivity) (by positivity)
          exact hcard.trans (mul_le_mul_of_nonneg_left hpk (by linarith))
      _ = A * H ^ (k - 1) := by rw [hA, hHk]; ring
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hHk0 : 0 ≤ H ^ (k - 1) := by positivity
  calc (2 * (M : ℝ) + 1) ^ E * (Z + Tm) ≤ 3 ^ E * H ^ E * (A * H ^ (k - 1) + Tm) :=
        mul_le_mul hpE (by linarith) (by positivity) (by positivity)
    _ ≤ 3 ^ E * H ^ E * ((A + 1) * (H ^ (k - 1) + Tm)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
    _ = 3 ^ E * (A + 1) * H ^ E * (H ^ (k - 1) + Tm) := by ring

/-- The number of d-tuples of naturals with product n is at most (ζ^d) n. -/
theorem card_finMulAntidiag_le_zeta_pow (d n : ℕ) :
    (Nat.finMulAntidiag d n).card ≤ (ArithmeticFunction.zeta ^ d) n := by
  induction d generalizing n with
  | zero =>
    by_cases hn : n = 1
    · subst hn; simp [Nat.finMulAntidiag_one]
    · simp [Nat.finMulAntidiag_zero_left hn]
  | succ d ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun f : Fin (d+1) → ℕ => ∏ i, Fin.tail f i)
      (t := n.divisors)]
    · apply Finset.sum_le_sum
      intro e he
      refine le_trans ?_ (ih e)
      apply Finset.card_le_card_of_injOn (fun f => Fin.tail f)
      · intro f hf
        simp only [coe_filter, Set.mem_ofPred_eq] at hf
        obtain ⟨hf1, hf2⟩ := hf
        simp only [mem_coe, Nat.mem_finMulAntidiag]
        exact ⟨hf2, Nat.ne_of_gt (Nat.pos_of_mem_divisors he)⟩
      · intro f hf g hg hfg
        simp only [coe_filter, Set.mem_ofPred_eq] at hf hg
        have h1 := hf.1; have h2 := hg.1
        rw [Nat.mem_finMulAntidiag, Fin.prod_univ_succ] at h1 h2
        have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
        have ht : Fin.tail f = Fin.tail g := hfg
        have hfe : ∏ i : Fin d, f i.succ = e := hf.2
        have hge : ∏ i : Fin d, g i.succ = e := hg.2
        rw [hfe] at h1; rw [hge] at h2
        have h0 : f 0 = g 0 := by
          have := h1.1.trans h2.1.symm
          exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero he0) this
        rw [← Fin.cons_self_tail f, ← Fin.cons_self_tail g, h0, ht]
    · intro f hf
      rw [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ] at hf
      simp only [mem_coe, Nat.mem_divisors]
      exact ⟨⟨f 0, by rw [← hf.1]; simp [Fin.tail, mul_comm]⟩, hn0⟩

/-- LEAF: Page 482 equation 6, second half: the number of tuples with
k! a |h_1⋯h_(k-1)| = m is at most 2^(k-1) τ_(k-1)(m/(k! a)) ≤ 2^(k-1) τ_k(m).
Class EASY. -/
theorem leaf_tuple_count (k a R m : ℕ) (hk : 2 ≤ k) (ha : 1 ≤ a) :
    (((tuples k R).filter (fun h => freq k a h = m)).card : ℝ) ≤
      2 ^ (k - 1) * (divisorCount k m : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  show (((tuples (j+1) R).filter (fun h => freq (j+1) a h = m)).card : ℝ) ≤
      2 ^ j * (divisorCount (j+1) m : ℝ)
  have key : ((tuples (j+1) R).filter (fun h => freq (j+1) a h = m)).card ≤
      ((univ : Finset (Fin j → Bool)) ×ˢ Nat.finMulAntidiag (j+1) m).card := by
    apply Finset.card_le_card_of_injOn
      (fun h : Fin j → ℤ => ((fun i => decide (h i < 0)),
        (Fin.cons ((j+1).factorial * a) (fun i => (h i).natAbs) : Fin (j+1) → ℕ)))
    · intro h hh
      simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_filter] at hh
      obtain ⟨hh1, hh2⟩ := hh
      simp only [mem_coe, mem_product, mem_univ, true_and, Nat.mem_finMulAntidiag,
        Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hne : ∀ i, h i ≠ 0 := fun i => (hh1 i).2
      have hprod : (∏ i, h i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)
      have habs : (∏ i, (h i).natAbs) = (∏ i, h i).natAbs :=
        (map_prod Int.natAbsHom (fun i => h i) univ).symm
      refine ⟨?_, ?_⟩
      · rw [habs]; exact hh2
      · rw [← hh2]
        have : 0 < (∏ i, h i).natAbs := Int.natAbs_pos.mpr hprod
        exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) ha) this)
    · intro h _ g _ hhg
      simp only [Prod.mk.injEq] at hhg
      obtain ⟨hs, hc⟩ := hhg
      funext i
      have h1 := congrFun hs i
      have h2 := congrFun hc i.succ
      simp only [Fin.cons_succ, decide_eq_decide] at h1 h2
      omega
  rw [card_product, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at key
  have h2 := card_finMulAntidiag_le_zeta_pow (j+1) m
  have : (((tuples (j+1) R).filter (fun h => freq (j+1) a h = m)).card : ℝ) ≤
      ((2 ^ j * (Nat.finMulAntidiag (j+1) m).card : ℕ) : ℝ) := by exact_mod_cast key
  refine this.trans ?_
  push_cast
  gcongr
  exact_mod_cast h2

end
end LeanLab.Perelli1996.Weyl1122
