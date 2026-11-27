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

/-- The absolute value of a product over `Fin n` is the product of the absolute values. -/
private theorem natAbs_prod_fin (n : ℕ) (h : Fin n → ℤ) :
    (∏ i, h i).natAbs = ∏ i, (h i).natAbs := by
  induction n with
  | zero => simp
  | succ n ih => rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Int.natAbs_mul, ih]

/-- The product of the absolute values of a tuple of nonzero integers is at least one. -/
private theorem one_le_natAbs_prod {j : ℕ} (h : Fin j → ℤ) (hne : ∀ i, h i ≠ 0) :
    1 ≤ ∏ k, (h k).natAbs := by
  classical
  apply Finset.one_le_prod
  intro k _
  exact Int.natAbs_pos.2 (hne k)

/-- A coordinate of a tuple of nonzero integers is at most the product of the absolute values. -/
private theorem natAbs_le_natAbs_prod {j : ℕ} (h : Fin j → ℤ) (hne : ∀ i, h i ≠ 0)
    (i : Fin j) : (h i).natAbs ≤ ∏ k, (h k).natAbs := by
  classical
  have hsplit : ∏ k : Fin j, (h k).natAbs
      = (h i).natAbs * ∏ k ∈ Finset.univ.erase i, (h k).natAbs :=
    (Finset.mul_prod_erase Finset.univ (fun k => (h k).natAbs) (Finset.mem_univ i)).symm
  rw [hsplit]
  have h1 : 1 ≤ ∏ k ∈ Finset.univ.erase i, (h k).natAbs := by
    apply Finset.one_le_prod
    intro k _
    exact Int.natAbs_pos.2 (hne k)
  calc (h i).natAbs = (h i).natAbs * 1 := (Nat.mul_one _).symm
    _ ≤ (h i).natAbs * ∏ k ∈ Finset.univ.erase i, (h k).natAbs :=
        Nat.mul_le_mul_left _ h1

/-- The number of ordered factorizations of `m` into `j` positive factors is at most `τ j m`. -/
private theorem card_factor_le_divisorCount (j M m : ℕ) (hm : 0 < m) (hM : m ≤ M) :
    ((Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 M)).filter
        (fun f => ∏ i, f i = m)).card ≤ divisorCount j m := by
  classical
  induction j generalizing m with
  | zero =>
      by_cases hm1 : m = 1
      · subst hm1
        have hd : divisorCount 0 1 = 1 := by simp [divisorCount]
        rw [hd]
        refine Finset.card_le_one.2 (fun a _ b _ => ?_)
        funext i
        exact i.elim0
      · have hd : divisorCount 0 m = 0 := by simp [divisorCount, hm1]
        rw [hd, Nat.le_zero]
        by_contra hne
        obtain ⟨f, hf⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
        rw [Finset.mem_filter] at hf
        have hp : ∏ i : Fin 0, f i = 1 := Fin.prod_univ_zero f
        rw [hp] at hf
        exact hm1 hf.2.symm
  | succ j ih =>
      set T : Finset (Fin (j + 1) → ℕ) :=
        (Fintype.piFinset (fun _ : Fin (j + 1) => Finset.Icc 1 M)).filter
          (fun f => ∏ i, f i = m) with hT
      have hprod : ∀ f : Fin (j + 1) → ℕ, ∏ i, f i = f 0 * ∏ i : Fin j, Fin.tail f i := by
        intro f
        rw [Fin.prod_univ_succ]
        rfl
      have hmaps : ∀ f ∈ T, (∏ i, Fin.tail f i) ∈ m.divisors := by
        intro f hf
        rw [hT, Finset.mem_filter, Fintype.mem_piFinset] at hf
        obtain ⟨hfpi, hfprod⟩ := hf
        rw [Nat.mem_divisors]
        refine ⟨⟨f 0, ?_⟩, hm.ne'⟩
        rw [← hfprod, hprod f]
        exact Nat.mul_comm _ _
      have hcard : T.card = ∑ b ∈ m.divisors, (T.filter (fun f => ∏ i, Fin.tail f i = b)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      have hfib : ∀ b ∈ m.divisors,
          (T.filter (fun f => ∏ i, Fin.tail f i = b)).card ≤ divisorCount j b := by
        intro b hb
        obtain ⟨hb1, hb2⟩ := Nat.mem_divisors.1 hb
        have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hb1 hm
        have hble : b ≤ m := Nat.le_of_dvd hm hb1
        have hdivmul : m / b * b = m := Nat.div_mul_cancel hb1
        have hbij : (T.filter (fun f => ∏ i, Fin.tail f i = b)).card
            = ((Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 M)).filter
                (fun g => ∏ i, g i = b)).card := by
          refine Finset.card_bij' (fun f _ => Fin.tail f) (fun g _ => Fin.cons (m / b) g)
            ?_ ?_ ?_ ?_
          · intro f hf
            rw [Finset.mem_filter] at hf
            obtain ⟨hfT, hfb⟩ := hf
            rw [hT, Finset.mem_filter, Fintype.mem_piFinset] at hfT
            exact Finset.mem_filter.2
              ⟨Fintype.mem_piFinset.2 (fun i => hfT.1 i.succ), hfb⟩
          · intro g hg
            rw [Finset.mem_filter, Fintype.mem_piFinset] at hg
            obtain ⟨hgpi, hgprod⟩ := hg
            rw [Finset.mem_filter, hT, Finset.mem_filter, Fintype.mem_piFinset]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · rw [Fin.forall_fin_succ]
              refine ⟨?_, fun i => by simpa using hgpi i⟩
              rw [Fin.cons_zero, Finset.mem_Icc]
              have hne0 : m / b ≠ 0 := by
                intro h0
                rw [h0, Nat.zero_mul] at hdivmul
                omega
              exact ⟨Nat.one_le_iff_ne_zero.2 hne0, (Nat.div_le_self m b).trans hM⟩
            · rw [Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [hgprod, hdivmul]
            · simp only [Fin.tail, Fin.cons_succ]
              exact hgprod
          · intro f hf
            rw [Finset.mem_filter] at hf
            obtain ⟨hfT, hfb⟩ := hf
            rw [hT, Finset.mem_filter, Fintype.mem_piFinset] at hfT
            have hf0 : f 0 = m / b := by
              rw [← Nat.mul_div_cancel (f 0) hbpos]
              congr 1
              rw [← hfb, ← hprod f, hfT.2]
            rw [← hf0]
            exact Fin.cons_self_tail f
          · intro g _
            funext i
            rfl
        rw [hbij]
        exact ih b hbpos (le_trans hble hM)
      calc T.card = ∑ b ∈ m.divisors, (T.filter (fun f => ∏ i, Fin.tail f i = b)).card := hcard
        _ ≤ ∑ b ∈ m.divisors, divisorCount j b := Finset.sum_le_sum hfib
        _ = divisorCount (j + 1) m := by
            rw [divisorCount, pow_succ, ArithmeticFunction.mul_zeta_apply]
            rfl

/-! Towards a `def`-free proof of `leaf_iterated_differencing`: Vaughan 1981 Lemma 2.3.
No auxiliary definition is introduced; every difference is written out. -/

private theorem weyl_e_add (x y : ℝ) : Kernel.e (x + y) = Kernel.e x * Kernel.e y := by
  unfold Kernel.e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem weyl_norm_e (x : ℝ) : ‖Kernel.e x‖ = 1 := by
  unfold Kernel.e
  rw [Complex.norm_exp]
  simp

private theorem weyl_e_neg (x : ℝ) : Kernel.e (-x) = starRingEnd ℂ (Kernel.e x) := by
  unfold Kernel.e
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

/-- Vaughan 1981 Lemma 2.3: one step of Weyl differencing on an interval of at most
`M + 1` consecutive integers. -/
private theorem weyl_step (M : ℕ) (g : ℤ → ℝ) (a b : ℤ) (hab : b - a ≤ (M : ℤ) + 1) :
    ‖∑ n ∈ Finset.Ico a b, Kernel.e (g n)‖ ^ 2 ≤
      ∑ h ∈ Finset.Icc (-(M : ℤ)) M,
        ‖∑ n ∈ Finset.Ico (max a (a - h)) (min b (b - h)),
          Kernel.e (g (n + h) - g n)‖ := by
  have hsq : ((‖∑ n ∈ Finset.Ico a b, Kernel.e (g n)‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ Finset.Icc (-(M : ℤ)) M,
        ∑ n ∈ Finset.Ico (max a (a - h)) (min b (b - h)), Kernel.e (g (n + h) - g n) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum,
      ← Finset.sum_product', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun p => ⟨p.1 - p.2, p.2⟩) (fun x => (x.2 + x.1, x.2))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_Icc] at hp ⊢
      omega
    · intro x hx
      simp only [Finset.mem_product, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_Icc] at hx ⊢
      omega
    · intro p _
      simp
    · intro x _
      simp
    · intro p _
      rw [← weyl_e_neg, ← weyl_e_add]
      congr 1
      have hsplit : p.2 + (p.1 - p.2) = p.1 := by ring
      show g p.1 + -g p.2 = g (p.2 + (p.1 - p.2)) - g p.2
      rw [hsplit]
      ring
  have hnorm : ‖∑ n ∈ Finset.Ico a b, Kernel.e (g n)‖ ^ 2 =
      ‖∑ h ∈ Finset.Icc (-(M : ℤ)) M,
        ∑ n ∈ Finset.Ico (max a (a - h)) (min b (b - h)), Kernel.e (g (n + h) - g n)‖ := by
    rw [← hsq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm]
  exact norm_sum_le _ _

/-- Splitting a sum over sign vectors at the last coordinate. -/
private theorem sum_fun_last (j : ℕ) (F : (Fin (j + 1) → Bool) → ℝ) :
    (∑ ε : Fin (j + 1) → Bool, F ε)
      = ∑ ε' : Fin j → Bool, ∑ c : Bool, F (Fin.snoc ε' c) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun ε => (Fin.init ε, ε (Fin.last j))) (fun p => Fin.snoc p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro ε _; simp
  · intro p _; simp
  · intro ε _; simp
  · intro p _; simp
  · intro ε _; simp

/-- The sign of a sign vector splits at the last coordinate. -/
private theorem sign_snoc (j : ℕ) (ε' : Fin j → Bool) (c : Bool) :
    (∏ i : Fin (j + 1), (if Fin.snoc (α := fun _ : Fin (j + 1) => Bool) ε' c i = true then (1 : ℝ) else -1))
      = (∏ i : Fin j, (if ε' i = true then (1 : ℝ) else -1)) *
          (if c = true then (1 : ℝ) else -1) := by
  rw [Fin.prod_univ_castSucc, Fin.snoc_last]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by rw [Fin.snoc_castSucc])

/-- The shift of a sign vector splits at the last coordinate. -/
private theorem shift_snoc (j : ℕ) (h : Fin (j + 1) → ℤ) (ε' : Fin j → Bool) (c : Bool) :
    (∑ i : Fin (j + 1), (if Fin.snoc (α := fun _ : Fin (j + 1) => Bool) ε' c i = true then h i else 0))
      = (∑ i : Fin j, (if ε' i = true then h i.castSucc else 0)) +
          (if c = true then h (Fin.last j) else 0) := by
  rw [Fin.sum_univ_castSucc, Fin.snoc_last, Finset.sum_congr rfl
    (fun i (_ : i ∈ Finset.univ) => by rw [Fin.snoc_castSucc])]

/-- One last-coordinate step of the iterated difference, as a finite sum over sign vectors:
summing the two values of the last sign gives the difference of the shifted sum. -/
private theorem weyl_phase_split (j : ℕ) (h : Fin (j + 1) → ℤ) (f : ℤ → ℝ) (n : ℤ)
    (ε' : Fin j → Bool) :
    (∑ c : Bool,
        (∏ i : Fin (j + 1),
            (if Fin.snoc (α := fun _ : Fin (j + 1) => Bool) ε' c i = true then (1 : ℝ) else -1)) *
          f (n + ∑ i : Fin (j + 1),
            (if Fin.snoc (α := fun _ : Fin (j + 1) => Bool) ε' c i = true then h i else 0)))
      = (∏ i : Fin j, (if ε' i = true then (1 : ℝ) else -1)) *
          f ((n + h (Fin.last j)) + ∑ i : Fin j, (if ε' i = true then h i.castSucc else 0)) -
        (∏ i : Fin j, (if ε' i = true then (1 : ℝ) else -1)) *
          f (n + ∑ i : Fin j, (if ε' i = true then h i.castSucc else 0)) := by
  rw [Fintype.univ_bool, Finset.sum_pair (by decide : (true : Bool) ≠ false)]
  simp only [sign_snoc, shift_snoc, Bool.false_eq_true]
  have harg : (n + ((∑ i : Fin j, (if ε' i = true then h i.castSucc else 0)) +
        (if True then h (Fin.last j) else 0)))
      = (n + h (Fin.last j)) + ∑ i : Fin j, (if ε' i = true then h i.castSucc else 0) := by
    norm_num
    ring
  rw [harg]
  norm_num
  ring

/-- The iterated difference satisfies its recursion: one more sign vector coordinate
turns the sum into the difference of the shifted sum and the unshifted one. -/
private theorem weyl_dsucc (j : ℕ) (h : Fin (j + 1) → ℤ) (f : ℤ → ℝ) (n : ℤ) :
    (∑ ε : Fin (j + 1) → Bool,
        (∏ i : Fin (j + 1), (if ε i = true then (1 : ℝ) else -1)) *
          f (n + ∑ i : Fin (j + 1), (if ε i = true then h i else 0)))
      = (∑ ε' : Fin j → Bool,
          (∏ i : Fin j, (if ε' i = true then (1 : ℝ) else -1)) *
            f ((n + h (Fin.last j)) +
              ∑ i : Fin j, (if ε' i = true then h i.castSucc else 0))) -
        ∑ ε' : Fin j → Bool,
          (∏ i : Fin j, (if ε' i = true then (1 : ℝ) else -1)) *
            f (n + ∑ i : Fin j, (if ε' i = true then h i.castSucc else 0)) := by
  rw [sum_fun_last j]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun ε' _ => by rw [weyl_phase_split])

/-- Splitting a sum over tuples at the last coordinate. -/
private theorem piFinset_succ_sum (j : ℕ) (Q : Finset ℤ) (G : (Fin (j + 1) → ℤ) → ℝ) :
    (∑ h ∈ Fintype.piFinset (fun _ : Fin (j + 1) => Q), G h)
      = ∑ h0 ∈ Fintype.piFinset (fun _ : Fin j => Q),
          ∑ t ∈ Q, G (Fin.snoc (α := fun _ : Fin (j + 1) => ℤ) h0 t) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun h => (Fin.init h, h (Fin.last j)))
    (fun p => Fin.snoc (α := fun _ : Fin (j + 1) => ℤ) p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    rw [Fin.mem_piFinset_iff_last_init] at hh
    simp only [Finset.mem_product]
    exact ⟨hh.2, hh.1⟩
  · intro p hp
    simp only [Finset.mem_product] at hp
    rw [Fin.mem_piFinset_iff_last_init]
    simp only [Fin.snoc_last, Fin.init_snoc]
    exact ⟨hp.2, hp.1⟩
  · intro h _; simp
  · intro p _; simp
  · intro h _; simp

/-- Vaughan 1981 Lemma 2.4, the sharp iteration of Lemma 2.3: after `j` differencing
steps the exponent is `2 ^ j` and the gain is `(2M+1) ^ (2^j - j - 1)`, the interval
shrinking at each step. -/
private theorem weyl_iterate (M : ℕ) (f : ℤ → ℝ) (a b : ℤ) (hab : b - a ≤ (M : ℤ) + 1) :
    ∀ j : ℕ, ∃ a' b' : (Fin j → ℤ) → ℤ,
      (∀ h, a ≤ a' h ∧ b' h - a' h ≤ (M : ℤ) + 1) ∧
      ‖∑ n ∈ Finset.Ico a b, Kernel.e (f n)‖ ^ (2 ^ j) ≤
        (2 * (M : ℝ) + 1) ^ (2 ^ j - j - 1) *
          ∑ h ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc (-(M : ℤ)) M),
            ‖∑ n ∈ Finset.Ico (a' h) (b' h),
              Kernel.e (∑ ε : Fin j → Bool,
                (∏ i : Fin j, (if ε i = true then (1 : ℝ) else -1)) *
                  f (n + ∑ i : Fin j, (if ε i = true then h i else 0)))‖ := by
  intro j
  induction j with
  | zero =>
    refine ⟨fun _ => a, fun _ => b, fun _ => ⟨le_rfl, hab⟩, ?_⟩
    have huniq : (Finset.univ : Finset (Fin 0 → Bool)) =
        {(fun i => i.elim0 : Fin 0 → Bool)} :=
      Finset.eq_singleton_iff_unique_mem.2
        ⟨Finset.mem_univ _, fun ε _ => funext (fun i => i.elim0)⟩
    have hpi : Fintype.piFinset (fun _ : Fin 0 => Finset.Icc (-(M : ℤ)) M) =
        {(fun i => i.elim0 : Fin 0 → ℤ)} :=
      Finset.eq_singleton_iff_unique_mem.2
        ⟨Fintype.mem_piFinset.2 (fun i => i.elim0), fun h _ => funext (fun i => i.elim0)⟩
    rw [hpi, huniq]
    simp
  | succ j ih =>
    obtain ⟨a', b', hinv, hb⟩ := ih
    set P : Finset (Fin j → ℤ) := Fintype.piFinset (fun _ : Fin j => Finset.Icc (-(M : ℤ)) M)
      with hP
    set Q : Finset ℤ := Finset.Icc (-(M : ℤ)) M with hQ
    set G : (Fin j → ℤ) → ℤ → ℝ := fun h0 n => ∑ ε : Fin j → Bool,
      (∏ i : Fin j, (if ε i = true then (1 : ℝ) else -1)) *
        f (n + ∑ i : Fin j, (if ε i = true then h0 i else 0)) with hG
    refine ⟨fun h => max (a' (Fin.init h)) (a' (Fin.init h) - h (Fin.last j)),
      fun h => min (b' (Fin.init h)) (b' (Fin.init h) - h (Fin.last j)), ?_, ?_⟩
    · intro h
      have hi := hinv (Fin.init h)
      constructor
      · exact le_trans hi.1 (le_max_left _ _)
      · have h2 : min (b' (Fin.init h)) (b' (Fin.init h) - h (Fin.last j)) ≤ b' (Fin.init h) :=
          min_le_left _ _
        have h3 : a' (Fin.init h) ≤ max (a' (Fin.init h)) (a' (Fin.init h) - h (Fin.last j)) :=
          le_max_left _ _
        linarith [hi.2]
    · have hstep : ∀ h0 ∈ P, ∀ t ∈ Q,
            ‖∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t)) (min (b' h0) (b' h0 - t)),
                Kernel.e (∑ ε : Fin (j + 1) → Bool,
                  (∏ i : Fin (j + 1), (if ε i = true then (1 : ℝ) else -1)) *
                    f (n + ∑ i : Fin (j + 1),
                      (if ε i = true then
                        (Fin.snoc (α := fun _ : Fin (j + 1) => ℤ) h0 t) i else 0)))‖
              = ‖∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t)) (min (b' h0) (b' h0 - t)),
                  Kernel.e (G h0 (n + t) - G h0 n)‖ := by
          intro h0 _ t _
          have hph : ∀ n : ℤ,
              (∑ ε : Fin (j + 1) → Bool,
                (∏ i : Fin (j + 1), (if ε i = true then (1 : ℝ) else -1)) *
                  f (n + ∑ i : Fin (j + 1),
                    (if ε i = true then
                      (Fin.snoc (α := fun _ : Fin (j + 1) => ℤ) h0 t) i else 0)))
                = G h0 (n + t) - G h0 n := by
            intro n
            rw [weyl_dsucc j (Fin.snoc (α := fun _ : Fin (j + 1) => ℤ) h0 t) f n]
            simp only [Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc, hG]
          rw [show (∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t)) (min (b' h0) (b' h0 - t)),
                Kernel.e (∑ ε : Fin (j + 1) → Bool,
                  (∏ i : Fin (j + 1), (if ε i = true then (1 : ℝ) else -1)) *
                    f (n + ∑ i : Fin (j + 1),
                      (if ε i = true then
                        (Fin.snoc (α := fun _ : Fin (j + 1) => ℤ) h0 t) i else 0))))
              = ∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t)) (min (b' h0) (b' h0 - t)),
                  Kernel.e (G h0 (n + t) - G h0 n) from
            Finset.sum_congr rfl (fun n _ => by rw [hph n])]
      have hnorm : ∀ h0 ∈ P,
          ‖∑ n ∈ Finset.Ico (a' h0) (b' h0), Kernel.e (G h0 n)‖ ^ 2 ≤
            ∑ t ∈ Q, ‖∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t))
              (min (b' h0) (b' h0 - t)), Kernel.e (G h0 (n + t) - G h0 n)‖ :=
        fun h0 hh0 => weyl_step M (G h0) (a' h0) (b' h0) (hinv h0).2
      have hcard : ((P.card : ℝ)) = (2 * (M : ℝ) + 1) ^ j := by
        rw [hP, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Int.card_Icc]
        have hmm : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
        rw [hmm]
        push_cast
        ring
      have hEx : 2 ^ (j + 1) - (j + 1) - 1 = 2 * (2 ^ j - j - 1) + j := by
        have := Nat.lt_two_pow_self (n := j)
        rw [pow_succ]
        omega
      rw [piFinset_succ_sum]
      simp only [Fin.init_snoc, Fin.snoc_last]
      rw [← hP]
      have hsum_eq : (∑ h0 ∈ P, ∑ t ∈ Q,
          ‖∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t)) (min (b' h0) (b' h0 - t)),
              Kernel.e (∑ ε : Fin (j + 1) → Bool,
                (∏ i : Fin (j + 1), (if ε i = true then (1 : ℝ) else -1)) *
                  f (n + ∑ i : Fin (j + 1),
                    (if ε i = true then
                      (Fin.snoc (α := fun _ : Fin (j + 1) => ℤ) h0 t) i else 0)))‖)
          = ∑ h0 ∈ P, ∑ t ∈ Q,
              ‖∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t)) (min (b' h0) (b' h0 - t)),
                Kernel.e (G h0 (n + t) - G h0 n)‖ := by
        refine Finset.sum_congr rfl (fun h0 hh0 => Finset.sum_congr rfl (fun t ht => ?_))
        exact hstep h0 hh0 t ht
      rw [hsum_eq]
      have hpos : (0 : ℝ) ≤ 2 * (M : ℝ) + 1 := by positivity
      calc ‖∑ n ∈ Finset.Ico a b, Kernel.e (f n)‖ ^ 2 ^ (j + 1)
          = (‖∑ n ∈ Finset.Ico a b, Kernel.e (f n)‖ ^ 2 ^ j) ^ 2 := by
            rw [pow_succ, pow_mul]
        _ ≤ ((2 * (M : ℝ) + 1) ^ (2 ^ j - j - 1) *
              ∑ h0 ∈ P, ‖∑ n ∈ Finset.Ico (a' h0) (b' h0), Kernel.e (G h0 n)‖) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by simpa [hP, hQ, hG] using hb) 2
        _ = (2 * (M : ℝ) + 1) ^ (2 * (2 ^ j - j - 1)) *
              (∑ h0 ∈ P, ‖∑ n ∈ Finset.Ico (a' h0) (b' h0), Kernel.e (G h0 n)‖) ^ 2 := by
            rw [mul_pow, ← pow_mul]
            congr 1
            ring
        _ ≤ (2 * (M : ℝ) + 1) ^ (2 * (2 ^ j - j - 1)) *
              ((P.card : ℝ) * ∑ h0 ∈ P,
                ‖∑ n ∈ Finset.Ico (a' h0) (b' h0), Kernel.e (G h0 n)‖ ^ 2) := by
            gcongr
            exact sq_sum_le_card_mul_sum_sq
        _ ≤ (2 * (M : ℝ) + 1) ^ (2 * (2 ^ j - j - 1)) *
              ((2 * (M : ℝ) + 1) ^ j * ∑ h0 ∈ P, ∑ t ∈ Q,
                ‖∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t)) (min (b' h0) (b' h0 - t)),
                  Kernel.e (G h0 (n + t) - G h0 n)‖) := by
            rw [hcard]
            gcongr with h0 hh0
            exact hnorm h0 hh0
        _ = (2 * (M : ℝ) + 1) ^ (2 ^ (j + 1) - (j + 1) - 1) * ∑ h0 ∈ P, ∑ t ∈ Q,
                ‖∑ n ∈ Finset.Ico (max (a' h0) (a' h0 - t)) (min (b' h0) (b' h0 - t)),
                  Kernel.e (G h0 (n + t) - G h0 n)‖ := by
            rw [hEx]
            ring

/-- The top Hasse derivative is the top coefficient. -/
private theorem hasse_eval_top (P : ℤ[X]) (N : ℕ) (hN : P.natDegree ≤ N) (h : ℤ) :
    (hasseDeriv N P).eval h = P.coeff N := by
  rw [eq_C_of_natDegree_eq_zero (p := hasseDeriv N P)
      (by rw [natDegree_hasseDeriv]; omega), eval_C, hasseDeriv_coeff]
  simp

/-- One difference lowers the degree by one, and the new top coefficient is `m h a_m`. -/
private theorem diff_step (P : ℤ[X]) (m : ℕ) (hm : 1 ≤ m) (hP : P.natDegree ≤ m) (h : ℤ) :
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

/-- After `j` differences the top coefficient is `m (m-1) ⋯ (m-j+1) h_1 ⋯ h_j a_m`, with the
difference written as the explicit sum over sign vectors rather than as a new polynomial. -/
private theorem poly_diff_shape (P : ℤ[X]) (m : ℕ) (hP : P.natDegree ≤ m) :
    ∀ (j : ℕ) (h : Fin j → ℤ), j ≤ m →
      ∃ Q : ℤ[X],
        (∀ n : ℤ, ((Q.eval n : ℤ) : ℝ) = ∑ ε : Fin j → Bool,
          (∏ i : Fin j, (if ε i = true then (1 : ℝ) else -1)) *
            ((P.eval (n + ∑ i : Fin j, (if ε i = true then h i else 0)) : ℤ) : ℝ)) ∧
        Q.natDegree ≤ m - j ∧
        Q.coeff (m - j) = (m.descFactorial j : ℤ) * (∏ i, h i) * P.coeff m := by
  intro j
  induction j with
  | zero =>
    intro h _
    refine ⟨P, ?_, by simpa using hP, by simp⟩
    intro n
    simp
  | succ j ih =>
    intro h hj
    obtain ⟨Q, hQeval, hQdeg, hQcoeff⟩ := ih (Fin.init h) (by omega)
    refine ⟨taylor (h (Fin.last j)) Q - Q, ?_, ?_, ?_⟩
    · intro n
      have hev : ((taylor (h (Fin.last j)) Q - Q).eval n : ℤ)
          = Q.eval (n + h (Fin.last j)) - Q.eval n := by
        simp [eval_sub, taylor_eval]
      rw [hev]
      push_cast
      rw [hQeval (n + h (Fin.last j)), hQeval n]
      simp only [Fin.init]
      rw [← weyl_dsucc j h (fun m => ((P.eval m : ℤ) : ℝ)) n]
    · have := (diff_step Q (m - j) (by omega) hQdeg (h (Fin.last j))).1
      have e : m - j - 1 = m - (j + 1) := by omega
      rwa [e] at this
    · have := (diff_step Q (m - j) (by omega) hQdeg (h (Fin.last j))).2
      have e : m - j - 1 = m - (j + 1) := by omega
      rw [e] at this
      rw [this, hQcoeff, Nat.descFactorial_succ, Fin.prod_univ_castSucc]
      simp only [Fin.init]
      push_cast [Nat.cast_sub (show j ≤ m by omega)]
      ring

/-- The (k-1)-fold difference of a polynomial of degree k is linear in `n` with slope
`k! a_k h_1 ⋯ h_(k-1)`: page 482, Vaughan 1981's proof of Lemma 2.4. -/
private theorem poly_difference (F : ℤ[X]) (hk : 1 ≤ F.natDegree) :
    ∃ c : (Fin (F.natDegree - 1) → ℤ) → ℤ, ∀ h n,
      (∑ ε : Fin (F.natDegree - 1) → Bool,
          (∏ i, (if ε i = true then (1 : ℝ) else -1)) *
            ((F.eval (n + ∑ i, (if ε i = true then h i else 0)) : ℤ) : ℝ))
        = ((F.natDegree.factorial : ℝ) * (F.leadingCoeff : ℝ) * ((∏ i, h i : ℤ) : ℝ)) *
            (n : ℝ) + (c h : ℝ) := by
  classical
  have hd : (F.natDegree.descFactorial (F.natDegree - 1) : ℤ) = F.natDegree.factorial := by
    have h1 : F.natDegree - (F.natDegree - 1) = 1 := by omega
    have := Nat.factorial_mul_descFactorial (show F.natDegree - 1 ≤ F.natDegree by omega)
    rw [h1] at this
    simp at this
    exact_mod_cast this
  have hex : ∀ h : (Fin (F.natDegree - 1) → ℤ), ∃ Q : ℤ[X],
      (∀ n : ℤ, ((Q.eval n : ℤ) : ℝ) = ∑ ε : Fin (F.natDegree - 1) → Bool,
          (∏ i, (if ε i = true then (1 : ℝ) else -1)) *
            ((F.eval (n + ∑ i, (if ε i = true then h i else 0)) : ℤ) : ℝ)) ∧
      Q.natDegree ≤ 1 ∧ Q.coeff 1 = (F.natDegree.factorial : ℤ) * F.leadingCoeff * ∏ i, h i := by
    intro h
    obtain ⟨Q, h1, h2, h3⟩ :=
      poly_diff_shape F F.natDegree le_rfl (F.natDegree - 1) h (by omega)
    have e1 : F.natDegree - (F.natDegree - 1) = 1 := by omega
    rw [e1] at h2 h3
    refine ⟨Q, h1, h2, ?_⟩
    rw [h3, hd]
    have hc : F.coeff F.natDegree = F.leadingCoeff := rfl
    rw [hc]
    ring
  choose Q hQeval hQdeg hQcoeff using hex
  refine ⟨fun h => (Q h).coeff 0, fun h n => ?_⟩
  have hform := eq_X_add_C_of_natDegree_le_one (hQdeg h)
  rw [← hQeval h n]
  have heval : (Q h).eval n = (Q h).coeff 1 * n + (Q h).coeff 0 := by
    conv_lhs => rw [hform]
    simp only [eval_add, eval_mul, eval_C, eval_X]
  rw [heval]
  rw [hQcoeff h]
  push_cast
  ring

/-- The kernel on the paper's window is the exponential sum over an integer interval. -/
private theorem kernel_eq_isum (F : ℤ[X]) (N H α : ℝ) :
    polynomialKernel F N H α =
      ∑ n ∈ Finset.Ico (⌈N ^ (1 / (F.natDegree : ℝ))⌉₊ : ℤ)
        ((⌊N ^ (1 / (F.natDegree : ℝ)) + H⌋₊ : ℤ) + 1), Kernel.e (((F.eval n : ℤ) : ℝ) * α) := by
  unfold polynomialKernel win Fv
  refine Finset.sum_nbij' (fun n : ℕ => (n : ℤ)) (fun m => m.toNat) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [Finset.mem_Icc, Finset.mem_Ico] at hn ⊢; omega
  · intro m hm; simp only [Finset.mem_Icc, Finset.mem_Ico] at hm ⊢; omega
  · intro n _; simp
  · intro m hm; simp only [Finset.mem_Ico] at hm ⊢; omega
  · intro n _; simp

/-- The window has at most `⌊H⌋ + 1` points. -/
private theorem window_length (x H : ℝ) (hx : 0 ≤ x) (hH : 0 ≤ H) :
    (⌊x + H⌋₊ : ℤ) + 1 - (⌈x⌉₊ : ℤ) ≤ (⌊H⌋₊ : ℤ) + 1 := by
  by_contra hc
  have h1 : ⌈x⌉₊ + ⌊H⌋₊ + 1 ≤ ⌊x + H⌋₊ := by omega
  have h2 : ((⌈x⌉₊ + ⌊H⌋₊ + 1 : ℕ) : ℝ) ≤ x + H := by
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))
  have h3 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have h4 : H < (⌊H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one H
  push_cast at h2
  linarith

/-- An exponential sum over an integer interval is a `Kernel.T` at the same frequency. -/
private theorem isum_lin (A B : ℤ) (hA : 0 ≤ A) (y : ℝ) :
    (∑ n ∈ Finset.Ico A B, Kernel.e ((n : ℝ) * y)) = Kernel.T A.toNat (B - A).toNat y := by
  unfold Kernel.T
  refine Finset.sum_nbij' (fun n => (n - A).toNat) (fun m => A + m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Ico, Finset.mem_range] at hm ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    omega
  · intro m hm
    simp only [Finset.mem_range] at hm ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    have h1 : ((A.toNat + (n - A).toNat : ℕ) : ℤ) = n := by omega
    have h2 : ((A.toNat + (n - A).toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast h1
    rw [h2]

/-- The kernel norm only depends on the absolute value of the frequency. -/
private theorem norm_T_neg (A L : ℕ) (y : ℝ) : ‖Kernel.T A L (-y)‖ = ‖Kernel.T A L y‖ := by
  have hconj : Kernel.T A L (-y) = starRingEnd ℂ (Kernel.T A L y) := by
    unfold Kernel.T
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← weyl_e_neg]
    congr 1
    ring
  rw [hconj, Complex.norm_conj]

/-- A linear sum with a constant phase reduces to `Kernel.T` at the absolute frequency. -/
private theorem norm_lin_sum (A B : ℤ) (hA : 0 ≤ A) (z d : ℤ) (α : ℝ) :
    ‖∑ n ∈ Finset.Ico A B, Kernel.e (((z * n + d : ℤ) : ℝ) * α)‖ =
      ‖Kernel.T A.toNat (B - A).toNat (α * (z.natAbs : ℕ))‖ := by
  have e_mul : ∀ x y : ℝ, Kernel.e (x + y) = Kernel.e x * Kernel.e y := weyl_e_add
  have hs : (∑ n ∈ Finset.Ico A B, Kernel.e (((z * n + d : ℤ) : ℝ) * α)) =
      (∑ n ∈ Finset.Ico A B, Kernel.e ((n : ℝ) * ((z : ℝ) * α))) *
        Kernel.e ((d : ℝ) * α) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← e_mul]
    congr 1
    push_cast
    ring
  rw [hs, norm_mul, weyl_norm_e, mul_one]
  rw [isum_lin A B hA ((z : ℝ) * α)]
  rcases Int.natAbs_eq z with hz | hz
  · congr 2
    rw [hz]; push_cast; simp; ring
  · rw [← norm_T_neg]
    congr 2
    rw [hz]; push_cast; simp; ring

/-- The tuples with some `h_i = 0`: at most `j (2M+1)^(j-1)` of the `(2M+1)^j` tuples
with `|h_i| ≤ M` have a zero entry. -/
private theorem zero_tuples (j M : ℕ) :
    ((Fintype.piFinset fun _ : Fin j => Finset.Icc (-(M : ℤ)) M).filter
      (fun h => ∃ i, h i = 0)).card ≤ j * (2 * M + 1) ^ (j - 1) := by
  classical
  set P := Fintype.piFinset fun _ : Fin j => Finset.Icc (-(M : ℤ)) M
  have hsub : P.filter (fun h => ∃ i, h i = 0) ⊆
      Finset.univ.biUnion (fun i : Fin j =>
        Fintype.piFinset (Function.update (fun _ : Fin j => Finset.Icc (-(M : ℤ)) M) i {0})) := by
    intro h hh
    simp only [P, Finset.mem_filter, Fintype.mem_piFinset] at hh
    obtain ⟨hP, i, hi⟩ := hh
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨i, fun a => ?_⟩
    by_cases ha : a = i
    · subst ha; simp [hi]
    · rw [Function.update_of_ne ha]; exact hP a
  have hcard : ∀ i : Fin j, (Fintype.piFinset
      (Function.update (fun _ : Fin j => Finset.Icc (-(M : ℤ)) M) i {0})).card =
      (2 * M + 1) ^ (j - 1) := by
    intro i
    rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    rw [Function.update_self, Finset.card_singleton, one_mul]
    rw [Finset.prod_congr rfl (fun a ha => by rw [Function.update_of_ne (ne_of_mem_erase ha)])]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, Int.card_Icc]
    congr 1
    omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin j, (Fintype.piFinset
      (Function.update (fun _ : Fin j => Finset.Icc (-(M : ℤ)) M) i {0})).card :=
        Finset.card_biUnion_le
    _ = j * (2 * M + 1) ^ (j - 1) := by simp [hcard]

/-- LEAF: Page 482 equation 6, second half: the number of tuples with
k! a |h_1⋯h_(k-1)| = m is at most 2^(k-1) τ_(k-1)(m/(k! a)) ≤ 2^(k-1) τ_k(m).
Class EASY. -/
theorem leaf_tuple_count (k a R m : ℕ) (hk : 2 ≤ k) (ha : 1 ≤ a) :
    (((tuples k R).filter (fun h => freq k a h = m)).card : ℝ) ≤
      2 ^ (k - 1) * (divisorCount k m : ℝ) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hpow : (2 : ℕ) ^ (n + 1 - 1) = 2 ^ n := by rw [Nat.add_sub_cancel]
  have hfac : 1 ≤ (n + 1).factorial * a :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (by omega))
  have key : ((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card ≤
      2 ^ n * divisorCount (n + 1) m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hzero : ((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = 0)).card = 0 := by
        by_contra hne
        obtain ⟨h, hh⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
        rw [Finset.mem_filter] at hh
        obtain ⟨htup, hfreq⟩ := hh
        rw [tuples, Fintype.mem_piFinset] at htup
        have hhne : ∀ i, h i ≠ 0 := by
          intro i
          have hi := htup i
          rw [Finset.mem_filter] at hi
          exact hi.2
        have hP : 1 ≤ (∏ i, h i).natAbs := by
          rw [natAbs_prod_fin]
          exact one_le_natAbs_prod h hhne
        have hmin : 1 ≤ freq (n + 1) a h := by
          have hm := Nat.mul_le_mul hfac hP
          simpa [freq, Nat.one_mul] using hm
        omega
      have hd0 : divisorCount (n + 1) 0 = 0 := by
        rw [divisorCount, pow_succ, ArithmeticFunction.mul_zeta_apply]
        simp
      rw [hzero, hd0]
      simp
    · set T : Finset (Fin (n + 1) → ℕ) :=
        (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.Icc 1 m)).filter
          (fun f => ∏ i, f i = m) with hT
      set Φ : (Fin n → ℤ) → (Fin (n + 1) → ℕ) :=
        fun h => Fin.cons ((n + 1).factorial * a) (fun i : Fin n => (h i).natAbs) with hΦ
      set sgn : (Fin n → ℤ) → (Fin n → Bool) := fun h i => decide (h i < 0) with hsgn
      have hmem : ∀ h ∈ (tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m),
          (∀ i, h i ≠ 0) ∧ freq (n + 1) a h = m := by
        intro h hh
        rw [Finset.mem_filter] at hh
        obtain ⟨htup, hfreq⟩ := hh
        rw [tuples, Fintype.mem_piFinset] at htup
        refine ⟨fun i => ?_, hfreq⟩
        have hi := htup i
        rw [Finset.mem_filter] at hi
        exact hi.2
      have hΦprod : ∀ h : Fin n → ℤ,
          ∏ i : Fin (n + 1), Φ h i = (n + 1).factorial * a * ∏ i, (h i).natAbs := by
        intro h
        rw [hΦ, Fin.prod_univ_succ]
        simp
      have hΦmem : ∀ h ∈ (tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m),
          Φ h ∈ T := by
        intro h hh
        obtain ⟨hhne, hfreq⟩ := hmem h hh
        have hP : 1 ≤ ∏ i, (h i).natAbs := one_le_natAbs_prod h hhne
        have hmul : (n + 1).factorial * a * ∏ i, (h i).natAbs = m := by
          rw [← natAbs_prod_fin]
          exact hfreq
        have h0 : Φ h 0 = (n + 1).factorial * a := Fin.cons_zero _ _
        have hj : ∀ i : Fin n, Φ h i.succ = (h i).natAbs := fun i => Fin.cons_succ _ _ _
        rw [hT, Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨?_, ?_⟩
        · rw [Fin.forall_fin_succ]
          refine ⟨?_, ?_⟩
          · rw [h0, Finset.mem_Icc]
            exact ⟨hfac, by
              calc (n + 1).factorial * a = (n + 1).factorial * a * 1 := (Nat.mul_one _).symm
                _ ≤ (n + 1).factorial * a * ∏ k, (h k).natAbs :=
                    Nat.mul_le_mul (le_refl _) hP
                _ = m := hmul⟩
          · intro i
            rw [hj i, Finset.mem_Icc]
            refine ⟨Int.natAbs_pos.2 (hhne i), ?_⟩
            calc (h i).natAbs ≤ ∏ k, (h k).natAbs := natAbs_le_natAbs_prod h hhne i
              _ = 1 * ∏ k, (h k).natAbs := (Nat.one_mul _).symm
              _ ≤ ((n + 1).factorial * a) * ∏ k, (h k).natAbs :=
                  Nat.mul_le_mul hfac (le_refl _)
              _ = m := hmul
        · rw [hΦprod]
          exact hmul
      have hinj : ∀ h1 ∈ (tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m),
          ∀ h2 ∈ (tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m),
          (sgn h1, Φ h1) = (sgn h2, Φ h2) → h1 = h2 := by
        intro h1 h1s h2 h2s heq
        obtain ⟨hsgneq, hΦeq⟩ := Prod.ext_iff.1 heq
        funext i
        have habs : (h1 i).natAbs = (h2 i).natAbs := by
          have h := congrFun hΦeq i.succ
          exact h
        have hsgniff : (h1 i < 0) ↔ (h2 i < 0) := by
          have h := congrFun hsgneq i
          rw [hsgn] at h
          simpa using h
        rcases Int.natAbs_eq_natAbs_iff.1 habs with h' | h'
        · exact h'
        · have h2zero : h2 i = 0 := by
            by_contra hb
            rcases Int.lt_or_gt_of_ne hb with hbn | hbp
            · have h1pos : 0 < h1 i := by omega
              have h1neg : h1 i < 0 := hsgniff.mpr hbn
              omega
            · have h1neg : h1 i < 0 := by omega
              have h2neg : h2 i < 0 := hsgniff.mp h1neg
              omega
          omega
      have huniv : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
        rw [Finset.card_univ]
        simp
      have hstep1 : ((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card
          ≤ ((Finset.univ : Finset (Fin n → Bool)) ×ˢ T).card := by
        apply Finset.card_le_card_of_injOn (fun h => (sgn h, Φ h))
        · intro h hh
          exact Finset.mem_product.2 ⟨Finset.mem_univ _, hΦmem h hh⟩
        · exact hinj
      have hstep3 : T.card ≤ divisorCount (n + 1) m :=
        card_factor_le_divisorCount (n + 1) m m hmpos (le_refl m)
      calc ((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card
          ≤ ((Finset.univ : Finset (Fin n → Bool)) ×ˢ T).card := hstep1
        _ = 2 ^ n * T.card := by rw [Finset.card_product, huniv]
        _ ≤ 2 ^ n * divisorCount (n + 1) m := Nat.mul_le_mul (le_refl _) hstep3
  have keyR : (((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card : ℝ) ≤
      ((2 ^ n * divisorCount (n + 1) m : ℕ) : ℝ) := by exact_mod_cast key
  calc (((tuples (n + 1) R).filter (fun h => freq (n + 1) a h = m)).card : ℝ)
      ≤ ((2 ^ n * divisorCount (n + 1) m : ℕ) : ℝ) := keyR
    _ = 2 ^ (n + 1 - 1) * (divisorCount (n + 1) m : ℝ) := by
        rw [Nat.add_sub_cancel]
        push_cast
        ring

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
  obtain ⟨c, hc⟩ := poly_difference F (by omega)
  set E := 2 ^ (k - 1) - (k - 1) - 1 with hE
  refine ⟨3 ^ E * (2 * (k - 1 : ℝ) * 3 ^ (k - 2) + 1), 3, ?_, le_rfl, ?_⟩
  · have h2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : (1 : ℝ) ≤ k - 1 := by linarith
    positivity
  intro N H α hN hH _
  set x := N ^ (1 / (k : ℝ)) with hxdef
  have hx : 0 ≤ x := Real.rpow_nonneg (by linarith) _
  set M := ⌊H⌋₊ with hMdef
  have hMH : (M : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hH0 : (0 : ℝ) < H := by linarith
  set f : ℤ → ℝ := fun n => ((F.eval n : ℤ) : ℝ) * α with hf
  obtain ⟨a', b', hab', hbound⟩ := weyl_iterate M f (⌈x⌉₊ : ℤ) ((⌊x + H⌋₊ : ℤ) + 1)
    (window_length x H hx (by linarith)) (k - 1)
  refine ⟨fun h => (a' h).toNat, fun h => (b' h - a' h).toNat, ?_, ?_⟩
  · intro h
    have h1 := (hab' h).2
    have h2 : ((b' h - a' h).toNat : ℝ) ≤ (M : ℝ) + 1 := by
      exact_mod_cast (show (b' h - a' h).toNat ≤ M + 1 by omega)
    linarith
  have hK : weylExponent F = ((2 ^ (k - 1) : ℕ) : ℝ) := by simp [weylExponent, k]
  have hkE : k ≤ 2 ^ (k - 1) := by
    have := Nat.lt_two_pow_self (n := k - 1)
    omega
  have hEk : ((2 ^ (k - 1) : ℕ) : ℝ) - (k : ℝ) = (E : ℝ) := by
    rw [hE, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hK, Real.rpow_natCast, kernel_eq_isum, hEk, Real.rpow_natCast]
  refine hbound.trans ?_
  set P := Fintype.piFinset (fun _ : Fin (k - 1) => Finset.Icc (-(M : ℤ)) M) with hP
  have hphase : ∀ (h : Fin (k - 1) → ℤ) (n : ℤ),
      (∑ ε : Fin (k - 1) → Bool,
        (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
          f (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0)))
        = ((∑ ε : Fin (k - 1) → Bool,
          (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
            ((F.eval (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0)) : ℤ) : ℝ))) * α := by
    intro h n
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro ε _
    simp only [hf]
    ring
  have hterm : ∀ h : Fin (k - 1) → ℤ,
      ‖∑ n ∈ Finset.Ico (a' h) (b' h),
          Kernel.e (∑ ε : Fin (k - 1) → Bool,
            (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
              f (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0)))‖
        = ‖Kernel.T (a' h).toNat (b' h - a' h).toNat
            (α * (freq k F.leadingCoeff.natAbs h : ℕ))‖ := by
    intro h
    have ha0 : 0 ≤ a' h := le_trans (by positivity) (hab' h).1
    have hfr : freq k F.leadingCoeff.natAbs h
        = ((k.factorial : ℤ) * F.leadingCoeff * (∏ i, h i)).natAbs := by
      simp [freq, Int.natAbs_mul]
    have hsum : (∑ n ∈ Finset.Ico (a' h) (b' h),
          Kernel.e (∑ ε : Fin (k - 1) → Bool,
            (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
              f (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0))))
        = ∑ n ∈ Finset.Ico (a' h) (b' h),
            Kernel.e ((((k.factorial : ℤ) * F.leadingCoeff * (∏ i, h i) * n + c h : ℤ) : ℝ) * α) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [hphase h n]
      congr 1
      rw [hc h n]
      push_cast
      ring
    rw [hsum, hfr, ← norm_lin_sum (a' h) (b' h) ha0 _ (c h) α]
  have hsplit := (Finset.sum_filter_add_sum_filter_not P (fun h => ∃ i, h i = 0)
    (fun h => ‖∑ n ∈ Finset.Ico (a' h) (b' h),
      Kernel.e (∑ ε : Fin (k - 1) → Bool,
        (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
          f (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0)))‖)).symm
  have hT : P.filter (fun h => ¬ ∃ i, h i = 0) = tuples k M := by
    ext h
    simp only [hP, Finset.mem_filter, Fintype.mem_piFinset, tuples, not_exists, ne_eq,
      forall_and]
  have hR : (∑ h ∈ tuples k M, ‖Kernel.T ((fun h => (a' h).toNat) h)
      ((fun h => (b' h - a' h).toNat) h) (α * (freq k F.leadingCoeff.natAbs h : ℕ))‖)
      = ∑ h ∈ tuples k M, ‖∑ n ∈ Finset.Ico (a' h) (b' h),
          Kernel.e (∑ ε : Fin (k - 1) → Bool,
            (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
              f (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0)))‖ :=
    Finset.sum_congr rfl fun h _ => (hterm h).symm
  rw [hsplit, hT, hR, ← hE]
  set Tm := ∑ h ∈ tuples k M, ‖∑ n ∈ Finset.Ico (a' h) (b' h),
      Kernel.e (∑ ε : Fin (k - 1) → Bool,
        (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
          f (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0)))‖ with hTm
  set Z := ∑ h ∈ P with ∃ i, h i = 0, ‖∑ n ∈ Finset.Ico (a' h) (b' h),
      Kernel.e (∑ ε : Fin (k - 1) → Bool,
        (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
          f (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0)))‖ with hZdef
  have hZ1 : Z ≤ ((P.filter fun h => ∃ i, h i = 0).card : ℝ) * (M + 1) := by
    have hle := Finset.sum_le_card_nsmul (P.filter fun h => ∃ i, h i = 0)
      (fun h => ‖∑ n ∈ Finset.Ico (a' h) (b' h),
        Kernel.e (∑ ε : Fin (k - 1) → Bool,
          (∏ i : Fin (k - 1), (if ε i = true then (1 : ℝ) else -1)) *
            f (n + ∑ i : Fin (k - 1), (if ε i = true then h i else 0)))‖) ((M : ℝ) + 1) (fun h _ => by
        refine (norm_sum_le _ _).trans ?_
        simp only [weyl_norm_e, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Int.card_Ico]
        exact_mod_cast (show (b' h - a' h).toNat ≤ M + 1 by have := (hab' h).2; omega))
    rw [hZdef]
    refine hle.trans (le_of_eq ?_)
    rw [nsmul_eq_mul]
  have hcard : ((P.filter fun h => ∃ i, h i = 0).card : ℝ) ≤ (k - 1 : ℝ) * (2 * M + 1) ^ (k - 2) := by
    rw [hP]
    have h1 := zero_tuples (k - 1) M
    have h2 : k - 1 - 1 = k - 2 := by omega
    rw [h2] at h1
    have h3 : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1]; simp
    have h4 : ((2 * M + 1 : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by push_cast; ring
    rw [← h3, ← h4]
    exact_mod_cast h1
  have hb : (2 * (M : ℝ) + 1) ≤ 3 * H := by linarith
  have hb0 : (0 : ℝ) ≤ 2 * (M : ℝ) + 1 := by positivity
  have hH0' : (0 : ℝ) ≤ H := by linarith
  have hpE : (2 * (M : ℝ) + 1) ^ E ≤ 3 ^ E * H ^ E := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hb0 hb E
  have hpk : (2 * (M : ℝ) + 1) ^ (k - 2) ≤ 3 ^ (k - 2) * H ^ (k - 2) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hb0 hb _
  have hHk : H ^ (k - 1) = H ^ (k - 2) * H := by
    rw [← pow_succ]
    congr 1
    omega
  set A : ℝ := 2 * (k - 1 : ℝ) * 3 ^ (k - 2) with hA
  have hk2r : (0 : ℝ) < (k : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hHk0 : (0 : ℝ) ≤ H ^ (k - 1) := by positivity
  have hTm0 : (0 : ℝ) ≤ Tm := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hZ : Z ≤ A * H ^ (k - 1) := by
    refine hZ1.trans ?_
    have hM1' : (M : ℝ) + 1 ≤ 2 * H := by linarith
    have hXY : (0 : ℝ) ≤ (k - 1 : ℝ) * (3 ^ (k - 2) * H ^ (k - 2)) := by
      have h1 : (0 : ℝ) ≤ (k - 1 : ℝ) := by linarith
      have h2 : (0 : ℝ) ≤ H ^ (k - 2) := by positivity
      exact mul_nonneg h1 (mul_nonneg (by positivity) h2)
    calc ((P.filter fun h => ∃ i, h i = 0).card : ℝ) * (M + 1)
        ≤ ((k - 1 : ℝ) * (3 ^ (k - 2) * H ^ (k - 2))) * (2 * H) := by
          apply mul_le_mul _ hM1' (by positivity) hXY
          exact hcard.trans (mul_le_mul_of_nonneg_left hpk (by linarith))
      _ = A * H ^ (k - 1) := by rw [hA, hHk]; ring
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc (2 * (M : ℝ) + 1) ^ E * (Z + Tm) ≤ 3 ^ E * H ^ E * (A * H ^ (k - 1) + Tm) :=
        mul_le_mul hpE (by linarith) (by positivity) (by positivity)
    _ ≤ 3 ^ E * H ^ E * ((A + 1) * (H ^ (k - 1) + Tm)) := by
        have hA0 : (0 : ℝ) ≤ A := by
          rw [hA]
          exact mul_nonneg (mul_nonneg (by norm_num) hk2r.le) (by positivity)
        have hprod : (0 : ℝ) ≤ A * Tm := mul_nonneg hA0 hTm0
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hZ0, hTm0, hHk0, hprod]
    _ = 3 ^ E * (A + 1) * H ^ E * (H ^ (k - 1) + Tm) := by ring

end
end LeanLab.Perelli1996.Weyl1122
