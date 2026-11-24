import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4415_17
    (hPairs1 :
      have x1 : List (BitVec 59) := [360930119642124586, 432486920269079116, 293578547141297264, 289365901620316032, 439119665042618368, 297239789478805504, 306275578149863424, 540467122476679168, 576425567931334656];
      have x2 : List (BitVec 59) → Fin 3 × List (Fin 25) → List (BitVec 59) := fun ws g =>
        have ins : List (BitVec 59) := g.2.map fun i => ws.getD i.val 0;
        ws ++ [if g.1 = 0 then ins.foldr (· &&& ·) (~~~0) else if g.1 = 1 then ins.foldr (· ||| ·) 0 else ~~~ins.headD 0];
      ∀ p ∈ ([(1, 3), (1, 5)] : List (Fin 9 × Fin 9)),
        ∀ (x5 : List (Fin 3 × List (Fin 25))) (x6 : Fin 25),
          5 ≤ x5.length → x5.length ≤ 13 →
          11 ≤ x6.val → x6.val < 11 + x5.length →
          (∀ g ∈ x5, g.2.length ≤ 2) →
          (∀ i : Fin 25, i.val < 9 → ∃ g ∈ x5, i ∈ if g.1 = 2 then g.2.take 1 else g.2) →
          have x11 : List (BitVec 59) := x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD p.1.val 0 ||| x1.getD p.2.val 0];
          (List.foldl x2 x11 x5).getD x6.val 0 ≠ 316380210352264264)
    (hPairs2 :
      have x1 : List (BitVec 59) := [360930119642124586, 432486920269079116, 293578547141297264, 289365901620316032, 439119665042618368, 297239789478805504, 306275578149863424, 540467122476679168, 576425567931334656];
      have x2 : List (BitVec 59) → Fin 3 × List (Fin 25) → List (BitVec 59) := fun ws g =>
        have ins : List (BitVec 59) := g.2.map fun i => ws.getD i.val 0;
        ws ++ [if g.1 = 0 then ins.foldr (· &&& ·) (~~~0) else if g.1 = 1 then ins.foldr (· ||| ·) 0 else ~~~ins.headD 0];
      ∀ p ∈ ([(1, 7), (1, 8)] : List (Fin 9 × Fin 9)),
        ∀ (x5 : List (Fin 3 × List (Fin 25))) (x6 : Fin 25),
          5 ≤ x5.length → x5.length ≤ 13 →
          11 ≤ x6.val → x6.val < 11 + x5.length →
          (∀ g ∈ x5, g.2.length ≤ 2) →
          (∀ i : Fin 25, i.val < 9 → ∃ g ∈ x5, i ∈ if g.1 = 2 then g.2.take 1 else g.2) →
          have x11 : List (BitVec 59) := x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD p.1.val 0 ||| x1.getD p.2.val 0];
          (List.foldl x2 x11 x5).getD x6.val 0 ≠ 316380210352264264)
    (hPairs3 :
      have x1 : List (BitVec 59) := [360930119642124586, 432486920269079116, 293578547141297264, 289365901620316032, 439119665042618368, 297239789478805504, 306275578149863424, 540467122476679168, 576425567931334656];
      have x2 : List (BitVec 59) → Fin 3 × List (Fin 25) → List (BitVec 59) := fun ws g =>
        have ins : List (BitVec 59) := g.2.map fun i => ws.getD i.val 0;
        ws ++ [if g.1 = 0 then ins.foldr (· &&& ·) (~~~0) else if g.1 = 1 then ins.foldr (· ||| ·) 0 else ~~~ins.headD 0];
      ∀ p ∈ ([(2, 6), (2, 8)] : List (Fin 9 × Fin 9)),
        ∀ (x5 : List (Fin 3 × List (Fin 25))) (x6 : Fin 25),
          5 ≤ x5.length → x5.length ≤ 13 →
          11 ≤ x6.val → x6.val < 11 + x5.length →
          (∀ g ∈ x5, g.2.length ≤ 2) →
          (∀ i : Fin 25, i.val < 9 → ∃ g ∈ x5, i ∈ if g.1 = 2 then g.2.take 1 else g.2) →
          have x11 : List (BitVec 59) := x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD p.1.val 0 ||| x1.getD p.2.val 0];
          (List.foldl x2 x11 x5).getD x6.val 0 ≠ 316380210352264264)
    (hPairs4 :
      have x1 : List (BitVec 59) := [360930119642124586, 432486920269079116, 293578547141297264, 289365901620316032, 439119665042618368, 297239789478805504, 306275578149863424, 540467122476679168, 576425567931334656];
      have x2 : List (BitVec 59) → Fin 3 × List (Fin 25) → List (BitVec 59) := fun ws g =>
        have ins : List (BitVec 59) := g.2.map fun i => ws.getD i.val 0;
        ws ++ [if g.1 = 0 then ins.foldr (· &&& ·) (~~~0) else if g.1 = 1 then ins.foldr (· ||| ·) 0 else ~~~ins.headD 0];
      ∀ p ∈ ([(3, 6), (6, 7)] : List (Fin 9 × Fin 9)),
        ∀ (x5 : List (Fin 3 × List (Fin 25))) (x6 : Fin 25),
          5 ≤ x5.length → x5.length ≤ 13 →
          11 ≤ x6.val → x6.val < 11 + x5.length →
          (∀ g ∈ x5, g.2.length ≤ 2) →
          (∀ i : Fin 25, i.val < 9 → ∃ g ∈ x5, i ∈ if g.1 = 2 then g.2.take 1 else g.2) →
          have x11 : List (BitVec 59) := x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD p.1.val 0 ||| x1.getD p.2.val 0];
          (List.foldl x2 x11 x5).getD x6.val 0 ≠ 316380210352264264) :
    have x1 : List (BitVec (59 : ℕ)) := [(360930119642124586 : BitVec (59 : ℕ)), (432486920269079116 : BitVec (59 : ℕ)), (293578547141297264 : BitVec (59 : ℕ)), (289365901620316032 : BitVec (59 : ℕ)), (439119665042618368 : BitVec (59 : ℕ)), (297239789478805504 : BitVec (59 : ℕ)), (306275578149863424 : BitVec (59 : ℕ)), (540467122476679168 : BitVec (59 : ℕ)), (576425567931334656 : BitVec (59 : ℕ))]; have x2 : List (BitVec (59 : ℕ)) → Fin (3 : ℕ) × List (Fin (25 : ℕ)) → List (BitVec (59 : ℕ)) := fun (x2 : List (BitVec (59 : ℕ))) (x3 : Fin (3 : ℕ) × List (Fin (25 : ℕ))) =>   have x4 : List (BitVec (59 : ℕ)) := List.map (fun (x4 : Fin (25 : ℕ)) => x2.getD ↑x4 (0 : BitVec (59 : ℕ))) x3.2;   x2 ++ [if x3.1 = (0 : Fin (3 : ℕ)) then List.foldr (fun (x5 x6 : BitVec (59 : ℕ)) => x5 &&& x6) (~~~(0 : BitVec (59 : ℕ))) x4 else if x3.1 = (1 : Fin (3 : ℕ)) then List.foldr (fun (x5 x6 : BitVec (59 : ℕ)) => x5 ||| x6) (0 : BitVec (59 : ℕ)) x4 else ~~~x4.headD (0 : BitVec (59 : ℕ))]; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : List (Fin (3 : ℕ) × List (Fin (25 : ℕ)))) (x6 : Fin (25 : ℕ)),   (10 : ℕ) * Min.min ↑x3 ↑x4 + Max.max ↑x3 ↑x4 ∈ [(13 : ℕ), (15 : ℕ), (17 : ℕ), (18 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (35 : ℕ), (36 : ℕ), (37 : ℕ), (56 : ℕ), (67 : ℕ), (78 : ℕ)] →     x5.length ≤ (13 : ℕ) →       (∀ x9 ∈ x5, x9.2.length ≤ (2 : ℕ)) →         (∀ (x10 : Fin (25 : ℕ)), ↑x10 < (9 : ℕ) → ∃ x12 ∈ x5, x10 ∈ if x12.1 = (2 : Fin (3 : ℕ)) then List.take (1 : ℕ) x12.2 else x12.2) →           have x11 : List (BitVec (59 : ℕ)) := x1 ++ [x1.getD (0 : ℕ) (0 : BitVec (59 : ℕ)) ||| x1.getD (4 : ℕ) (0 : BitVec (59 : ℕ)), x1.getD ↑x3 (0 : BitVec (59 : ℕ)) ||| x1.getD ↑x4 (0 : BitVec (59 : ℕ))];           have x12 : List (BitVec (59 : ℕ)) := List.foldl x2 x11 x5;           x12.getD ↑x6 (0 : BitVec (59 : ℕ)) ≠ (316380210352264264 : BitVec (59 : ℕ)) := by
  intro x1 x2 x3 x4 x5 x6 hpair hlen hfan hcov x11 x12
  let target : BitVec 59 := 316380210352264264
  have getD_snoc_eq (l : List (BitVec 59)) (a : BitVec 59) : (l ++ [a]).getD l.length 0 = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne (l : List (BitVec 59)) (a : BitVec 59) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j 0 = l.getD j 0 := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) 0 (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l 0 (n := j) (by omega)]
  have run_len (gs : List (Fin 3 × List (Fin 25))) (ws : List (BitVec 59)) :
      (List.foldl x2 ws gs).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g rest ih =>
      simp only [List.foldl_cons]
      rw [ih (x2 ws g)]
      simp only [x2, List.length_append, List.length_cons, List.length_nil]
      omega
  have run_keep (gs : List (Fin 3 × List (Fin 25))) (ws : List (BitVec 59)) :
      ∀ i < ws.length, (List.foldl x2 ws gs).getD i 0 = ws.getD i 0 := by
    induction gs generalizing ws with
    | nil => intro i _; rfl
    | cons g rest ih =>
      intro i hi
      simp only [List.foldl_cons]
      have hi' : i < (x2 ws g).length := by
        simp only [x2, List.length_append, List.length_cons, List.length_nil]; omega
      rw [ih (x2 ws g) i hi']
      exact List.getD_append _ _ _ _ hi
  let eff : Fin 3 × List (Fin 25) → List (Fin 25) := fun g => if g.1 = 2 then g.2.take 1 else g.2
  have hlen5 (gs : List (Fin 3 × List (Fin 25))) (hgf : ∀ g ∈ gs, g.2.length ≤ 2)
      (hgc : ∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs, i ∈ eff g) : 5 ≤ gs.length := by
    have hflat_le (l : List (Fin 3 × List (Fin 25))) (hf : ∀ g ∈ l, g.2.length ≤ 2) :
        (l.flatMap eff).length ≤ 2 * l.length := by
      induction l with
      | nil => simp only [List.flatMap_nil, List.length_nil, Nat.mul_zero, Nat.le_refl]
      | cons g rest ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hg2 := hf g List.mem_cons_self
        have heff_le : (eff g).length ≤ 2 := by
          dsimp only [eff]; split_ifs
          · rw [List.length_take]; omega
          · exact hg2
        have hrest := ih (fun g' hg' => hf g' (List.mem_cons_of_mem g hg'))
        omega
    let S9 : List (Fin 25) := [0, 1, 2, 3, 4, 5, 6, 7, 8]
    have hS9_card : S9.toFinset.card = 9 := by dsimp only [S9]; decide
    have hS9_sub : S9.toFinset ⊆ (gs.flatMap eff).toFinset := by
      intro u hu
      rw [List.mem_toFinset] at hu ⊢
      have hult : u.val < 9 := by
        have hcheck : ∀ v : Fin 25, v ∈ S9 → v.val < 9 := by dsimp only [S9]; decide
        exact hcheck u hu
      obtain ⟨g, hg, hug⟩ := hgc u hult
      exact List.mem_flatMap.mpr ⟨g, hg, hug⟩
    have h1 : 9 ≤ (gs.flatMap eff).toFinset.card := by
      rw [← hS9_card]; exact Finset.card_le_card hS9_sub
    have h2 : (gs.flatMap eff).toFinset.card ≤ (gs.flatMap eff).length := List.toFinset_card_le _
    have h3 : (gs.flatMap eff).length ≤ 2 * gs.length := hflat_le gs hgf
    omega
  let reps8 : List (Fin 9 × Fin 9) := [(1, 3), (1, 5), (1, 7), (1, 8), (2, 6), (2, 8), (3, 6), (6, 7)]
  have hbase_ne : ∀ p ∈ reps8, ∀ k : Fin 11,
      (x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD p.1.val 0 ||| x1.getD p.2.val 0]).getD k.val 0 ≠ target := by
    dsimp only [reps8, x1, target]; decide
  have hzero_ne : (0 : BitVec 59) ≠ target := by dsimp only [target]; decide
  have hDispatch (p : Fin 9 × Fin 9) (hp : p ∈ reps8) (gs : List (Fin 3 × List (Fin 25))) (out : Fin 25)
      (hgl : gs.length ≤ 13) (hgf : ∀ g ∈ gs, g.2.length ≤ 2)
      (hgc : ∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs, i ∈ eff g) :
      (List.foldl x2 (x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD p.1.val 0 ||| x1.getD p.2.val 0]) gs).getD out.val 0 ≠ target := by
    let ws0 : List (BitVec 59) := x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD p.1.val 0 ||| x1.getD p.2.val 0]
    have hws0_len : ws0.length = 11 := rfl
    by_cases hlt11 : out.val < 11
    · rw [run_keep gs ws0 out.val (by rw [hws0_len]; exact hlt11)]
      exact hbase_ne p hp ⟨out.val, hlt11⟩
    · by_cases hge : 11 + gs.length ≤ out.val
      · rw [List.getD_eq_default (List.foldl x2 ws0 gs) 0 (n := out.val) (by rw [run_len, hws0_len]; exact hge)]
        exact hzero_ne
      · have h5 := hlen5 gs hgf hgc
        have hlo : 11 ≤ out.val := by omega
        have hhi : out.val < 11 + gs.length := by omega
        simp only [reps8, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hPairs1 (1, 3) (by decide) gs out h5 hgl hlo hhi hgf hgc
        · exact hPairs1 (1, 5) (by decide) gs out h5 hgl hlo hhi hgf hgc
        · exact hPairs2 (1, 7) (by decide) gs out h5 hgl hlo hhi hgf hgc
        · exact hPairs2 (1, 8) (by decide) gs out h5 hgl hlo hhi hgf hgc
        · exact hPairs3 (2, 6) (by decide) gs out h5 hgl hlo hhi hgf hgc
        · exact hPairs3 (2, 8) (by decide) gs out h5 hgl hlo hhi hgf hgc
        · exact hPairs4 (3, 6) (by decide) gs out h5 hgl hlo hhi hgf hgc
        · exact hPairs4 (6, 7) (by decide) gs out h5 hgl hlo hhi hgf hgc
  let pi : List ℕ :=
    [0, 1, 16, 17, 45, 46, 53, 7, 8, 20, 50, 11, 12, 22, 51, 15, 2, 3, 18, 47,
     9, 21, 13, 23, 34, 35, 41, 55, 56, 38, 40, 36, 39, 57, 24, 25, 31, 54, 29, 32,
     30, 26, 42, 43, 44, 4, 5, 19, 48, 49, 10, 14, 52, 6, 37, 27, 28, 33, 58]
  have hpi_lt : ∀ b : Fin 59, pi.getD b.val 0 < 59 := by dsimp only [pi]; decide
  let permBV : BitVec 59 → BitVec 59 := fun v =>
    BitVec.cast (by simp only [List.length_map, List.length_range])
      (BitVec.ofBoolListLE ((List.range 59).map fun b => v.getLsbD (pi.getD b 0)))
  have permBV_get (v : BitVec 59) (i : ℕ) (hi : i < 59) : (permBV v).getLsbD i = v.getLsbD (pi.getD i 0) := by
    dsimp only [permBV]
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
        List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi),
        List.getElem_map, List.getElem_range]
  have permBV_zero : permBV 0 = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [permBV_get 0 i hi]
    change (0#59).getLsbD (pi.getD i 0) = (0#59).getLsbD i
    rw [BitVec.getLsbD_zero, BitVec.getLsbD_zero]
  have permBV_not (v : BitVec 59) : permBV (~~~v) = ~~~permBV v := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hlt := hpi_lt ⟨i, hi⟩
    rw [permBV_get (~~~v) i hi, BitVec.getLsbD_not, BitVec.getLsbD_not, permBV_get v i hi]
    simp only [hi, hlt, decide_true, Bool.true_and]
  have permBV_and (a b : BitVec 59) : permBV (a &&& b) = permBV a &&& permBV b := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [permBV_get (a &&& b) i hi, BitVec.getLsbD_and, BitVec.getLsbD_and, permBV_get a i hi, permBV_get b i hi]
  have permBV_or (a b : BitVec 59) : permBV (a ||| b) = permBV a ||| permBV b := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [permBV_get (a ||| b) i hi, BitVec.getLsbD_or, BitVec.getLsbD_or, permBV_get a i hi, permBV_get b i hi]
  have permBV_foldr_and (l : List (BitVec 59)) :
      permBV (l.foldr (· &&& ·) (~~~0)) = (l.map permBV).foldr (· &&& ·) (~~~0) := by
    induction l with
    | nil => simp only [List.foldr_nil, List.map_nil, permBV_not, permBV_zero]
    | cons a t ih => simp only [List.foldr_cons, List.map_cons, permBV_and, ih]
  have permBV_foldr_or (l : List (BitVec 59)) :
      permBV (l.foldr (· ||| ·) 0) = (l.map permBV).foldr (· ||| ·) 0 := by
    induction l with
    | nil => simp only [List.foldr_nil, List.map_nil, permBV_zero]
    | cons a t ih => simp only [List.foldr_cons, List.map_cons, permBV_or, ih]
  have permBV_headD (l : List (BitVec 59)) : permBV (l.headD 0) = (l.map permBV).headD 0 := by
    cases l with
    | nil => exact permBV_zero
    | cons a t => rfl
  let sigNat : ℕ → ℕ := fun i =>
    if i = 1 then 5 else if i = 5 then 1
    else if i = 2 then 8 else if i = 8 then 2
    else if i = 6 then 7 else if i = 7 then 6
    else i
  have hsig_lt25 : ∀ i : Fin 25, sigNat i.val < 25 := by dsimp only [sigNat]; decide
  have hsig_lt9 : ∀ i : Fin 9, sigNat i.val < 9 := by dsimp only [sigNat]; decide
  let sig25 : Fin 25 → Fin 25 := fun i => ⟨sigNat i.val, hsig_lt25 i⟩
  let sig9 : Fin 9 → Fin 9 := fun i => ⟨sigNat i.val, hsig_lt9 i⟩
  have hsigNat_inv : ∀ i : Fin 25, sigNat (sigNat i.val) = i.val := by dsimp only [sigNat]; decide
  have hsig25_inv (i : Fin 25) : sig25 (sig25 i) = i := Fin.ext (hsigNat_inv i)
  have hsig_ge9 (i : ℕ) (hi : 9 ≤ i) : sigNat i = i := by dsimp only [sigNat]; split_ifs <;> omega
  have hperm_inputs_bits : ∀ i : Fin 9, ∀ k : Fin 59,
      (x1.getD i.val 0).getLsbD (pi.getD k.val 0) = (x1.getD (sigNat i.val) 0).getLsbD k.val := by
    dsimp only [pi, x1, sigNat]; decide
  have hperm_inputs (i : Fin 9) : permBV (x1.getD i.val 0) = x1.getD (sig9 i).val 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [permBV_get _ k hk]
    exact hperm_inputs_bits i ⟨k, hk⟩
  have hperm_target_bits : ∀ k : Fin 59, target.getLsbD (pi.getD k.val 0) = target.getLsbD k.val := by
    dsimp only [pi, target]; decide
  have hperm_target : permBV target = target := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    rw [permBV_get _ k hk]
    exact hperm_target_bits ⟨k, hk⟩
  let mapG : Fin 3 × List (Fin 25) → Fin 3 × List (Fin 25) := fun g => (g.1, g.2.map sig25)
  have hsim (gs : List (Fin 3 × List (Fin 25))) (wA wB : List (BitVec 59))
      (hlen_w : wA.length = wB.length) (h9 : 9 ≤ wA.length)
      (hrel : ∀ i : Fin 25, wB.getD (sig25 i).val 0 = permBV (wA.getD i.val 0)) :
      ∀ i : Fin 25, (List.foldl x2 wB (gs.map mapG)).getD (sig25 i).val 0 =
        permBV ((List.foldl x2 wA gs).getD i.val 0) := by
    induction gs generalizing wA wB with
    | nil => exact hrel
    | cons g rest ih =>
      simp only [List.map_cons, List.foldl_cons] at ih ⊢
      let insA := g.2.map fun u => wA.getD u.val 0
      let insB := (g.2.map sig25).map fun u => wB.getD u.val 0
      have hins : insB = insA.map permBV := by
        dsimp only [insA, insB]; rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro u _; exact hrel u
      let bA := if g.1 = 0 then insA.foldr (· &&& ·) (~~~0) else if g.1 = 1 then insA.foldr (· ||| ·) 0 else ~~~insA.headD 0
      let bB := if g.1 = 0 then insB.foldr (· &&& ·) (~~~0) else if g.1 = 1 then insB.foldr (· ||| ·) 0 else ~~~insB.headD 0
      have hb_eq : bB = permBV bA := by
        dsimp only [bA, bB]; rw [hins]
        split_ifs
        · exact (permBV_foldr_and insA).symm
        · exact (permBV_foldr_or insA).symm
        · rw [permBV_not, permBV_headD]
      have hx2A : x2 wA g = wA ++ [bA] := rfl
      have hx2B : x2 wB (mapG g) = wB ++ [permBV bA] := by
        change wB ++ [bB] = wB ++ [permBV bA]; rw [hb_eq]
      rw [hx2A, hx2B]
      apply ih (wA ++ [bA]) (wB ++ [permBV bA])
      · simp only [List.length_append, hlen_w, List.length_cons, List.length_nil]
      · simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro i
        by_cases heq : i.val = wA.length
        · have hs : (sig25 i).val = wB.length := by
            change sigNat i.val = wB.length
            rw [hsig_ge9 i.val (by omega), heq, hlen_w]
          rw [hs, heq, getD_snoc_eq wB (permBV bA), getD_snoc_eq wA bA]
        · have hsne : (sig25 i).val ≠ wB.length := by
            change sigNat i.val ≠ wB.length
            by_cases hlt : i.val < 9
            · have := hsig_lt9 ⟨i.val, hlt⟩; dsimp only at this; omega
            · rw [hsig_ge9 i.val (by omega)]; omega
          rw [getD_snoc_ne wB (permBV bA) (sig25 i).val hsne, getD_snoc_ne wA bA i.val heq]
          exact hrel i
  have hApplySig (a b : Fin 9) (hp : (sig9 a, sig9 b) ∈ reps8 ∨ (sig9 b, sig9 a) ∈ reps8) :
      (List.foldl x2 (x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD a.val 0 ||| x1.getD b.val 0]) x5).getD x6.val 0 ≠ target := by
    let wA := x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD a.val 0 ||| x1.getD b.val 0]
    let wB := x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD (sig9 a).val 0 ||| x1.getD (sig9 b).val 0]
    have hwA_len : wA.length = 11 := rfl
    have hwB_len : wB.length = 11 := rfl
    have hx1_len : x1.length = 9 := rfl
    have hrel0 : ∀ i : Fin 25, wB.getD (sig25 i).val 0 = permBV (wA.getD i.val 0) := by
      intro i
      by_cases hi9 : i.val < 9
      · have hsi9 : (sig25 i).val < 9 := hsig_lt9 ⟨i.val, hi9⟩
        dsimp only [wA, wB]
        rw [List.getD_append x1 _ 0 (sig25 i).val (by rw [hx1_len]; exact hsi9),
            List.getD_append x1 _ 0 i.val (by rw [hx1_len]; exact hi9)]
        exact (hperm_inputs ⟨i.val, hi9⟩).symm
      · by_cases hi_eq9 : i.val = 9
        · have hsi9 : (sig25 i).val = 9 := by change sigNat i.val = 9; rw [hi_eq9]; rfl
          rw [hsi9, hi_eq9]
          dsimp only [wA, wB]
          rw [List.getD_append_right x1 _ 0 9 (by rw [hx1_len]),
              List.getD_append_right x1 _ 0 9 (by rw [hx1_len])]
          simp only [hx1_len, Nat.sub_self, List.getD_cons_zero]
          change x1.getD (sig9 0).val 0 ||| x1.getD (sig9 4).val 0 = permBV (x1.getD (0 : Fin 9).val 0 ||| x1.getD (4 : Fin 9).val 0)
          rw [permBV_or, hperm_inputs 0, hperm_inputs 4]
        · by_cases hi_eq10 : i.val = 10
          · have hsi10 : (sig25 i).val = 10 := by change sigNat i.val = 10; rw [hi_eq10]; rfl
            rw [hsi10, hi_eq10]
            dsimp only [wA, wB]
            rw [List.getD_append_right x1 _ 0 10 (by rw [hx1_len]; omega),
                List.getD_append_right x1 _ 0 10 (by rw [hx1_len]; omega)]
            simp only [hx1_len, show (10 : ℕ) - 9 = 1 from rfl, List.getD_cons_succ, List.getD_cons_zero]
            rw [permBV_or, hperm_inputs a, hperm_inputs b]
          · have hge11 : 11 ≤ i.val := by omega
            have hsi : (sig25 i).val = i.val := hsig_ge9 i.val (by omega)
            rw [hsi, List.getD_eq_default wB 0 (n := i.val) (by omega),
                List.getD_eq_default wA 0 (n := i.val) (by omega), permBV_zero]
    have hsim_out := hsim x5 wA wB (by omega) (by omega) hrel0 x6
    have hgs'_len : (x5.map mapG).length ≤ 13 := by rw [List.length_map]; exact hlen
    have hgs'_fan : ∀ g ∈ x5.map mapG, g.2.length ≤ 2 := by
      intro g hg; rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp only [mapG, List.length_map]; exact hfan g0 hg0
    have hgs'_cov : ∀ i : Fin 25, i.val < 9 → ∃ g ∈ x5.map mapG, i ∈ eff g := by
      intro i hi
      have hsi : (sig25 i).val < 9 := hsig_lt9 ⟨i.val, hi⟩
      obtain ⟨g0, hg0, hmem⟩ := hcov (sig25 i) hsi
      refine ⟨mapG g0, List.mem_map.mpr ⟨g0, hg0, rfl⟩, ?_⟩
      dsimp only [eff, mapG]
      split_ifs with h2
      · simp only [h2, ↓reduceIte] at hmem
        rw [← List.map_take]
        exact List.mem_map.mpr ⟨sig25 i, hmem, hsig25_inv i⟩
      · simp only [h2, ↓reduceIte] at hmem
        exact List.mem_map.mpr ⟨sig25 i, hmem, hsig25_inv i⟩
    intro heq
    have hB_eq : (List.foldl x2 wB (x5.map mapG)).getD (sig25 x6).val 0 = target := by
      rw [hsim_out, heq, hperm_target]
    rcases hp with h1 | h2
    · exact hDispatch (sig9 a, sig9 b) h1 (x5.map mapG) (sig25 x6) hgs'_len hgs'_fan hgs'_cov hB_eq
    · have hwB_comm : wB = x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD (sig9 b).val 0 ||| x1.getD (sig9 a).val 0] := by
        dsimp only [wB]; rw [BitVec.or_comm (x1.getD (sig9 a).val 0)]
      rw [hwB_comm] at hB_eq
      exact hDispatch (sig9 b, sig9 a) h2 (x5.map mapG) (sig25 x6) hgs'_len hgs'_fan hgs'_cov hB_eq
  let reps8Code : List ℕ := [13, 15, 17, 18, 26, 28, 36, 67]
  have hmem_reps8 (a b : Fin 9) (h : 10 * a.val + b.val ∈ reps8Code) : (a, b) ∈ reps8 := by
    have ha := a.isLt
    have hb := b.isLt
    simp only [reps8Code, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [reps8, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · exact Or.inr (Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext (by omega), Fin.ext (by omega)⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩))))))
  have hClassifyNat : ∀ a b : Fin 9,
      10 * min a.val b.val + max a.val b.val ∈ [13, 15, 17, 18, 25, 26, 28, 35, 36, 37, 56, 67, 78] →
      (10 * a.val + b.val ∈ reps8Code ∨ 10 * b.val + a.val ∈ reps8Code) ∨
      (10 * sigNat a.val + sigNat b.val ∈ reps8Code ∨ 10 * sigNat b.val + sigNat a.val ∈ reps8Code) := by
    dsimp only [reps8Code, sigNat]; decide
  rcases hClassifyNat x3 x4 hpair with (h1 | h2) | (h3 | h4)
  · exact hDispatch (x3, x4) (hmem_reps8 x3 x4 h1) x5 x6 hlen hfan hcov
  · have hx11_comm : x11 = x1 ++ [x1.getD 0 0 ||| x1.getD 4 0, x1.getD x4.val 0 ||| x1.getD x3.val 0] := by
      dsimp only [x11]; rw [BitVec.or_comm (x1.getD x3.val 0)]
    change (List.foldl x2 x11 x5).getD x6.val 0 ≠ target
    rw [hx11_comm]
    exact hDispatch (x4, x3) (hmem_reps8 x4 x3 h2) x5 x6 hlen hfan hcov
  · exact hApplySig x3 x4 (Or.inl (hmem_reps8 (sig9 x3) (sig9 x4) h3))
  · exact hApplySig x3 x4 (Or.inr (hmem_reps8 (sig9 x4) (sig9 x3) h4))
