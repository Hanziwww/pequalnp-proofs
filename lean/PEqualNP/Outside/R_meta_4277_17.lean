import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4277_17
    (hOneLive09 :
      have p9 : (Fin 9 → Bool) → Bool := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun k =>
          x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        D.size = 13 →
        (D.gates.filter (fun g => ([0, 9] : List ℕ).any g.inputs.contains)).length = 1 →
        (∀ g ∈ D.gates, ([0, 9] : List ℕ).any g.inputs.contains = true →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) ∨
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9]))) →
        (D.gates.filter (fun g => !([0, 9] : List ℕ).any g.inputs.contains && g.inputs.contains 4)).length ≤ 1 →
        ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0]) ≠ p9 x)
    (hBothOr :
      have p9 : (Fin 9 → Bool) → Bool := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun k =>
          x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        D.size = 14 →
        (D.gates.filter (fun g => g.inputs.contains 0)).length = 2 →
        (∀ g ∈ D.gates, g.inputs.contains 0 = true →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ w : ℕ, w ≠ 0 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) →
        (D.gates.filter (fun g => !g.inputs.contains 0 && g.inputs.contains 4)).length ≤ 1 →
        ∃ x : Fin 9 → Bool, D.eval (List.ofFn x) ≠ p9 x)
    (hBothAnd :
      have p9 : (Fin 9 → Bool) → Bool := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun k =>
          x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        D.size = 14 →
        (D.gates.filter (fun g => g.inputs.contains 0)).length = 2 →
        (∀ g ∈ D.gates, g.inputs.contains 0 = true →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) →
        (D.gates.filter (fun g => !g.inputs.contains 0 && g.inputs.contains 4)).length ≤ 1 →
        ∃ y : Fin 9 → Bool, D.eval (List.ofFn y) ≠ p9 (Function.update y 0 (!y 0)))
    (hMixedOrAnd :
      have p9 : (Fin 9 → Bool) → Bool := fun x =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun k =>
          x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size = 14 →
        (C.gates.filter (fun g => g.inputs.contains 0)).length = 1 →
        (C.gates.filter (fun g => g.inputs.contains 9)).length = 1 →
        (∀ g ∈ C.gates, g.inputs.contains 0 = true →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) →
        (∀ g ∈ C.gates, g.inputs.contains 9 = true →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9])) →
        (C.gates.filter (fun g => !([0, 9] : List ℕ).any g.inputs.contains && g.inputs.contains 4)).length ≤ 1 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠ p9 x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Set ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any x5.inputs.contains) x1.gates).length = (2 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => ! [(0 : ℕ), (9 : ℕ)].any x6.inputs.contains && x6.inputs.contains (4 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (x1.output ∈ x2 ∧ (0 : ℕ) ∉ x2 ∧ (9 : ℕ) ∉ x2 ∧ ∀ (x7 : List PEqualNP.CircuitLowerBounds.Gate) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x7 ++ x8 :: x9 → if [(0 : ℕ), (9 : ℕ)].any x8.inputs.contains = Bool.true then (10 : ℕ) + x7.length ∈ x2 → ∃ x12 ∈ x2, x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x8.inputs = [(0 : ℕ), x12] ∨ x8.inputs = [x12, (0 : ℕ)]) ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x8.inputs = [(9 : ℕ), x12] ∨ x8.inputs = [x12, (9 : ℕ)]) else (10 : ℕ) + x7.length ∈ x2 ∧ ∀ x11 ∈ x8.inputs, x11 ∈ x2) → ∃ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))]) ≠ (fun (x9 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x10 : ℕ) => x9 (Fin.ofNat (9 : ℕ) (x10 / (10 : ℕ))) && x9 (Fin.ofNat (9 : ℕ) (x10 % (10 : ℕ)))) x8 := by
  intro C S hFan hSz hFlt09 hFlt4 hS
  obtain ⟨houtS, h0nS, h9nS, hSgate⟩ := hS
  let p9 : (Fin 9 → Bool) → Bool := fun x =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun k =>
      x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))
  let is09 : Gate → Bool := fun g => ([0, 9] : List ℕ).any g.inputs.contains
  have his09_iff (g : Gate) : is09 g = true ↔ 0 ∈ g.inputs ∨ 9 ∈ g.inputs := by
    simp only [is09, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, List.contains_iff_mem]
  have his09_false (g : Gate) : is09 g = false ↔ 0 ∉ g.inputs ∧ 9 ∉ g.inputs := by
    constructor
    · intro h
      refine ⟨fun h0 => ?_, fun h9 => ?_⟩
      · have ht := (his09_iff g).mpr (Or.inl h0); rw [h] at ht; cases ht
      · have ht := (his09_iff g).mpr (Or.inr h9); rw [h] at ht; cases ht
    · rintro ⟨h0, h9⟩
      cases hb : is09 g
      · rfl
      · rcases (his09_iff g).mp hb with h | h
        · exact absurd h h0
        · exact absurd h h9
  let step : List Bool → Gate → List Bool := fun ws g =>
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs ws => gs.foldl step ws
  have getD_snoc_eq (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  have getD_snoc_ne (l : List Bool) (a : Bool) (j : ℕ) (hj : j ≠ l.length) :
      (l ++ [a]).getD j false = l.getD j false := by
    by_cases hlt : j < l.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default (l ++ [a]) false (n := j) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
          List.getD_eq_default l false (n := j) (by omega)]
  have run_len (gs : List Gate) (ws : List Bool) : (run gs ws).length = ws.length + gs.length := by
    induction gs generalizing ws with
    | nil => simp only [run, List.foldl_nil, List.length_nil, Nat.add_zero]
    | cons g rest ih =>
      simp only [run, List.foldl_cons] at ih ⊢
      rw [ih (step ws g)]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have run_append (gs1 gs2 : List Gate) (ws : List Bool) :
      run (gs1 ++ gs2) ws = run gs2 (run gs1 ws) := by
    simp only [run, List.foldl_append]
  have hFlt0_all (l : List Gate) (h0 : (l.filter is09).length = 0) : ∀ g ∈ l, is09 g = false := by
    intro g hg
    cases hb : is09 g
    · rfl
    · have hmem : g ∈ l.filter is09 := List.mem_filter.mpr ⟨hg, hb⟩
      have hpos : 0 < (l.filter is09).length := List.length_pos_of_mem hmem
      omega
  have hSplit1 : ∀ l : List Gate, (l.filter is09).length = 1 →
      ∃ (l1 l2 : List Gate) (g1 : Gate),
        l = l1 ++ g1 :: l2 ∧ is09 g1 = true ∧ (∀ g ∈ l1, is09 g = false) ∧ (∀ g ∈ l2, is09 g = false) := by
    intro l
    induction l with
    | nil => intro h; simp only [List.filter_nil, List.length_nil] at h; omega
    | cons a t ih =>
      intro hlen
      cases ha : is09 a
      · simp only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte] at hlen
        obtain ⟨l1, l2, g1, hteq, hg1, hl1, hl2⟩ := ih hlen
        refine ⟨a :: l1, l2, g1, by rw [hteq]; rfl, hg1, ?_, hl2⟩
        intro g hg
        rw [List.mem_cons] at hg
        rcases hg with rfl | hg'
        · exact ha
        · exact hl1 g hg'
      · simp only [List.filter_cons, ha, ↓reduceIte, List.length_cons] at hlen
        refine ⟨[], t, a, rfl, ha, (fun g hg => by cases hg), hFlt0_all t (by omega)⟩
  have hSplit2 : ∀ l : List Gate, (l.filter is09).length = 2 →
      ∃ (l1 l2 l3 : List Gate) (g1 g2 : Gate),
        l = l1 ++ g1 :: (l2 ++ g2 :: l3) ∧
        is09 g1 = true ∧ is09 g2 = true ∧
        (∀ g ∈ l1, is09 g = false) ∧ (∀ g ∈ l2, is09 g = false) ∧ (∀ g ∈ l3, is09 g = false) := by
    intro l
    induction l with
    | nil => intro h; simp only [List.filter_nil, List.length_nil] at h; omega
    | cons a t ih =>
      intro hlen
      cases ha : is09 a
      · simp only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte] at hlen
        obtain ⟨l1, l2, l3, g1, g2, hteq, hg1, hg2, hl1, hl2, hl3⟩ := ih hlen
        refine ⟨a :: l1, l2, l3, g1, g2, by rw [hteq]; rfl, hg1, hg2, ?_, hl2, hl3⟩
        intro g hg
        rw [List.mem_cons] at hg
        rcases hg with rfl | hg'
        · exact ha
        · exact hl1 g hg'
      · simp only [List.filter_cons, ha, ↓reduceIte, List.length_cons] at hlen
        obtain ⟨l2, l3, g2, hteq, hg2, hl2, hl3⟩ := hSplit1 t (by omega)
        exact ⟨[], l2, l3, a, g2, by rw [hteq]; rfl, ha, hg2, (fun g hg => by cases hg), hl2, hl3⟩
  obtain ⟨l1, l2, l3, g1, g2, hCg, hg1_09, hg2_09, hl1_no, hl2_no, hl3_no⟩ := hSplit2 C.gates hFlt09
  let w1 : ℕ := 10 + l1.length
  let w2 : ℕ := 10 + (l1.length + 1 + l2.length)
  have hg1_spec : w1 ∈ S →
      ∃ u ∈ S,
        (g1.op = GateOp.or ∧ (g1.inputs = [0, u] ∨ g1.inputs = [u, 0])) ∨
        (g1.op = GateOp.and ∧ (g1.inputs = [9, u] ∨ g1.inputs = [u, 9])) := by
    have h := hSgate l1 g1 (l2 ++ g2 :: l3) hCg
    simp only [is09] at hg1_09
    simp only [hg1_09, ↓reduceIte] at h
    exact h
  have hg2_spec : w2 ∈ S →
      ∃ u ∈ S,
        (g2.op = GateOp.or ∧ (g2.inputs = [0, u] ∨ g2.inputs = [u, 0])) ∨
        (g2.op = GateOp.and ∧ (g2.inputs = [9, u] ∨ g2.inputs = [u, 9])) := by
    have hCg2 : C.gates = (l1 ++ [g1] ++ l2) ++ g2 :: l3 := by
      rw [hCg]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have h := hSgate (l1 ++ [g1] ++ l2) g2 l3 hCg2
    simp only [is09] at hg2_09
    simp only [hg2_09, ↓reduceIte, List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at h
    exact h
  have hNon09_inputs : ∀ g ∈ C.gates, is09 g = false → ∀ u ∈ g.inputs, u ∈ S := by
    intro g hg hno
    obtain ⟨pre, suf, hsp⟩ := List.append_of_mem hg
    have h := hSgate pre g suf hsp
    simp only [is09] at hno
    simp only [hno, Bool.false_eq_true, ↓reduceIte] at h
    exact h.2
  have hNon09_all_in : ∀ g ∈ l1 ++ l2 ++ l3, ∀ u ∈ g.inputs, u ∈ S := by
    intro g hg
    have hgC : g ∈ C.gates ∧ is09 g = false := by
      simp only [List.mem_append] at hg
      rw [hCg]
      rcases hg with (h | h) | h
      · exact ⟨List.mem_append_left _ h, hl1_no g h⟩
      · exact ⟨List.mem_append_right _ (List.mem_cons_of_mem g1 (List.mem_append_left _ h)), hl2_no g h⟩
      · exact ⟨List.mem_append_right _ (List.mem_cons_of_mem g1 (List.mem_append_right _ (List.mem_cons_of_mem g2 h))), hl3_no g h⟩
    exact hNon09_inputs g hgC.1 hgC.2
  by_cases hw1S : w1 ∈ S
  · by_cases hw2S : w2 ∈ S
    · obtain ⟨u1, hu1S, hg1_form⟩ := hg1_spec hw1S
      obtain ⟨u2, hu2S, hg2_form⟩ := hg2_spec hw2S
      have hu1_ne0 : u1 ≠ 0 := fun h => h0nS (h ▸ hu1S)
      have hu1_ne9 : u1 ≠ 9 := fun h => h9nS (h ▸ hu1S)
      have hu2_ne0 : u2 ≠ 0 := fun h => h0nS (h ▸ hu2S)
      have hu2_ne9 : u2 ≠ 9 := fun h => h9nS (h ▸ hu2S)
      have hC_filter0_all (p : Gate → Bool) :
          (C.gates.filter p).length =
            (l1.filter p).length + (if p g1 then 1 else 0) + (l2.filter p).length + (if p g2 then 1 else 0) + (l3.filter p).length := by
        rw [hCg]
        simp only [List.filter_append, List.filter_cons, List.length_append]
        cases p g1 <;> cases p g2 <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons] <;> omega
      have hFlt_empty (l : List Gate) (p : Gate → Bool) (hp : ∀ g ∈ l, p g = false) : (l.filter p).length = 0 := by
        cases h : l.filter p with
        | nil => rfl
        | cons a t =>
          have ha : a ∈ l.filter p := by rw [h]; exact List.mem_cons_self
          obtain ⟨hal, hpa⟩ := List.mem_filter.mp ha
          rw [hp a hal] at hpa; cases hpa
      have hMap_filter_len (f : Gate → Gate) (p q : Gate → Bool) (gs : List Gate)
          (hpq : ∀ g ∈ gs, p (f g) = q g) : ((gs.map f).filter p).length = (gs.filter q).length := by
        induction gs with
        | nil => rfl
        | cons a t ih =>
          simp only [List.map_cons, List.filter_cons]
          have ha := hpq a List.mem_cons_self
          have ht := ih (fun g hg => hpq g (List.mem_cons_of_mem a hg))
          rw [ha]
          cases q a <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ht]
      rcases hg1_form with ⟨hg1_or, hg1_in⟩ | ⟨hg1_and, hg1_in⟩
      · rcases hg2_form with ⟨hg2_or, hg2_in⟩ | ⟨hg2_and, hg2_in⟩
        · have hno9 : ∀ g ∈ C.gates, 9 ∉ g.inputs := by
            intro g hg
            rw [hCg] at hg
            simp only [List.mem_append, List.mem_cons] at hg
            rcases hg with h | rfl | h | rfl | h
            · exact ((his09_false g).mp (hl1_no g h)).2
            · intro h9
              rcases hg1_in with h | h <;> (rw [h] at h9; simp only [List.mem_cons, List.not_mem_nil, or_false] at h9; rcases h9 with h9 | h9 <;> omega)
            · exact ((his09_false g).mp (hl2_no g h)).2
            · intro h9
              rcases hg2_in with h | h <;> (rw [h] at h9; simp only [List.mem_cons, List.not_mem_nil, or_false] at h9; rcases h9 with h9 | h9 <;> omega)
            · exact ((his09_false g).mp (hl3_no g h)).2
          let drop9 : ℕ → ℕ := fun i => if i < 9 then i else i - 1
          let D : Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map drop9⟩, drop9 C.output⟩
          have hdrop9_0 (i : ℕ) (hi9 : i ≠ 9) : drop9 i = 0 ↔ i = 0 := by
            dsimp only [drop9]; split_ifs <;> omega
          have hdrop9_4 (i : ℕ) (hi9 : i ≠ 9) : drop9 i = 4 ↔ i = 4 := by
            dsimp only [drop9]; split_ifs <;> omega
          have hdrop9_mem (g : Gate) (hg9 : 9 ∉ g.inputs) (k : ℕ) (hk : k = 0 ∨ k = 4) :
              (g.inputs.map drop9).contains k = g.inputs.contains k := by
            rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
            constructor
            · rintro ⟨u, hu, hdu⟩
              have hu9 : u ≠ 9 := fun h => hg9 (h ▸ hu)
              rcases hk with rfl | rfl
              · rw [(hdrop9_0 u hu9).mp hdu] at hu; exact hu
              · rw [(hdrop9_4 u hu9).mp hdu] at hu; exact hu
            · intro hk_mem
              refine ⟨k, hk_mem, ?_⟩
              rcases hk with rfl | rfl <;> rfl
          have hD_fan : FanInTwo D := by
            intro g hg
            simp only [D, List.mem_map] at hg
            obtain ⟨g0, hg0, rfl⟩ := hg
            have hf := hFan g0 hg0
            exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
          have hD_sz : D.size = 14 := by
            change (C.gates.map _).length = 14
            rw [List.length_map]; exact hSz
          have hC_0_eq_09 (g : Gate) (hg9 : 9 ∉ g.inputs) : g.inputs.contains 0 = is09 g := by
            rw [Bool.eq_iff_iff, List.contains_iff_mem, his09_iff]
            exact ⟨Or.inl, fun h => by rcases h with h | h; exact h; exact absurd h hg9⟩
          have hD_flt0 : (D.gates.filter (fun g => g.inputs.contains 0)).length = 2 := by
            change ((C.gates.map fun g : Gate => Gate.mk g.op (g.inputs.map drop9)).filter (fun g => g.inputs.contains 0)).length = 2
            rw [hMap_filter_len _ _ is09 C.gates (fun g hg => (hdrop9_mem g (hno9 g hg) 0 (Or.inl rfl)).trans (hC_0_eq_09 g (hno9 g hg)))]
            exact hFlt09
          have hD_flt4 : (D.gates.filter (fun g => !g.inputs.contains 0 && g.inputs.contains 4)).length ≤ 1 := by
            change ((C.gates.map fun g : Gate => Gate.mk g.op (g.inputs.map drop9)).filter (fun g => !g.inputs.contains 0 && g.inputs.contains 4)).length ≤ 1
            rw [hMap_filter_len _ _ (fun g => !is09 g && g.inputs.contains 4) C.gates (fun g hg => by
              dsimp only
              rw [hdrop9_mem g (hno9 g hg) 0 (Or.inl rfl), hC_0_eq_09 g (hno9 g hg), hdrop9_mem g (hno9 g hg) 4 (Or.inr rfl)])]
            exact hFlt4
          have hD_0spec : ∀ g ∈ D.gates, g.inputs.contains 0 = true →
              g.op = GateOp.or ∧ ∃ w : ℕ, w ≠ 0 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0]) := by
            intro g hg h0
            simp only [D, List.mem_map] at hg
            obtain ⟨g0, hg0, rfl⟩ := hg
            dsimp only at h0 ⊢
            rw [hdrop9_mem g0 (hno9 g0 hg0) 0 (Or.inl rfl), hC_0_eq_09 g0 (hno9 g0 hg0)] at h0
            rw [hCg] at hg0
            simp only [List.mem_append, List.mem_cons] at hg0
            rcases hg0 with h | rfl | h | rfl | h
            · rw [hl1_no g0 h] at h0; cases h0
            · refine ⟨hg1_or, drop9 u1, fun hd => hu1_ne0 ((hdrop9_0 u1 hu1_ne9).mp hd), ?_⟩
              rcases hg1_in with h | h <;> rw [h]
              · exact Or.inl rfl
              · exact Or.inr rfl
            · rw [hl2_no g0 h] at h0; cases h0
            · refine ⟨hg2_or, drop9 u2, fun hd => hu2_ne0 ((hdrop9_0 u2 hu2_ne9).mp hd), ?_⟩
              rcases hg2_in with h | h <;> rw [h]
              · exact Or.inl rfl
              · exact Or.inr rfl
            · rw [hl3_no g0 h] at h0; cases h0
          obtain ⟨x, hx⟩ := hBothOr D hD_fan hD_sz hD_flt0 hD_0spec hD_flt4
          have hdrop9_sim (gs : List Gate) (hgs : ∀ g ∈ gs, 9 ∉ g.inputs)
              (wA wB : List Bool) (hwA : 9 ≤ wA.length) (hwB : wB.length = wA.length + 1)
              (hrel : ∀ i, i ≠ 9 → wA.getD (drop9 i) false = wB.getD i false) :
              ∀ i, i ≠ 9 → (run (gs.map fun g => ⟨g.op, g.inputs.map drop9⟩) wA).getD (drop9 i) false =
                (run gs wB).getD i false := by
            induction gs generalizing wA wB with
            | nil => exact hrel
            | cons g rest ih =>
              simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
              have hg9 : 9 ∉ g.inputs := hgs g List.mem_cons_self
              have hinp : (g.inputs.map drop9).map (fun j => wA.getD j false) = g.inputs.map (fun i => wB.getD i false) := by
                rw [List.map_map]; apply List.map_congr_left
                intro i hi; exact hrel i (fun h => hg9 (h ▸ hi))
              let b := g.op.eval (g.inputs.map fun i => wB.getD i false)
              have hstepA : step wA ⟨g.op, g.inputs.map drop9⟩ = wA ++ [b] := by dsimp only [step, b]; rw [hinp]
              rw [hstepA]
              apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (wA ++ [b]) (step wB g)
              · simp only [List.length_append, List.length_cons, List.length_nil]; omega
              · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
              · intro i hi9
                dsimp only [step]
                by_cases heq : i = wB.length
                · subst heq
                  have hdr : drop9 wB.length = wA.length := by dsimp only [drop9]; split_ifs <;> omega
                  rw [hdr, getD_snoc_eq wA b, getD_snoc_eq wB b]
                · have hdr_ne : drop9 i ≠ wA.length := by dsimp only [drop9]; split_ifs <;> omega
                  rw [getD_snoc_ne wA b (drop9 i) hdr_ne, getD_snoc_ne wB b i heq]
                  exact hrel i hi9
          have hbase : ∀ i, i ≠ 9 → (List.ofFn x).getD (drop9 i) false = (List.ofFn x ++ [!x 0]).getD i false := by
            intro i hi9
            by_cases hi : i < 9
            · have hdr : drop9 i = i := by simp only [drop9, hi, ↓reduceIte]
              rw [hdr]; exact (List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact hi)).symm
            · have hdr : drop9 i = i - 1 := by simp only [drop9, hi, ↓reduceIte]
              rw [hdr, List.getD_eq_default (List.ofFn x) false (n := i - 1) (by simp only [List.length_ofFn]; omega),
                  List.getD_eq_default (List.ofFn x ++ [!x 0]) false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
          have hev := hdrop9_sim C.gates hno9 (List.ofFn x) (List.ofFn x ++ [!x 0])
            (by simp only [List.length_ofFn]; omega)
            (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
            hbase C.output (fun h => h9nS (h ▸ houtS))
          refine ⟨x, ?_⟩
          change (run C.gates (List.ofFn x ++ [!x 0])).getD C.output false ≠ p9 x
          rw [← hev]
          exact hx
        · have hg1_0 : g1.inputs.contains 0 = true := by
            rw [List.contains_iff_mem]; rcases hg1_in with h | h <;> rw [h]
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem u1 List.mem_cons_self
          have hg1_n9 : g1.inputs.contains 9 = false := by
            cases hb : g1.inputs.contains 9
            · rfl
            · rw [List.contains_iff_mem] at hb
              rcases hg1_in with h | h <;> (rw [h] at hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with h9 | h9 <;> omega)
          have hg2_n0 : g2.inputs.contains 0 = false := by
            cases hb : g2.inputs.contains 0
            · rfl
            · rw [List.contains_iff_mem] at hb
              rcases hg2_in with h | h <;> (rw [h] at hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with h0 | h0 <;> omega)
          have hg2_9 : g2.inputs.contains 9 = true := by
            rw [List.contains_iff_mem]; rcases hg2_in with h | h <;> rw [h]
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem u2 List.mem_cons_self
          have hF0 : (C.gates.filter (fun g => g.inputs.contains 0)).length = 1 := by
            rw [hC_filter0_all, hg1_0, hg2_n0,
              hFlt_empty l1 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl1_no g hg)).1 (List.contains_iff_mem.mp h)),
              hFlt_empty l2 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl2_no g hg)).1 (List.contains_iff_mem.mp h)),
              hFlt_empty l3 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl3_no g hg)).1 (List.contains_iff_mem.mp h))]
            rfl
          have hF9 : (C.gates.filter (fun g => g.inputs.contains 9)).length = 1 := by
            rw [hC_filter0_all, hg1_n9, hg2_9,
              hFlt_empty l1 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl1_no g hg)).2 (List.contains_iff_mem.mp h)),
              hFlt_empty l2 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl2_no g hg)).2 (List.contains_iff_mem.mp h)),
              hFlt_empty l3 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl3_no g hg)).2 (List.contains_iff_mem.mp h))]
            rfl
          have hS0 : ∀ g ∈ C.gates, g.inputs.contains 0 = true →
              g.op = GateOp.or ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0]) := by
            intro g hg h0
            rw [hCg] at hg; simp only [List.mem_append, List.mem_cons] at hg
            rcases hg with h | rfl | h | rfl | h
            · exact absurd (List.contains_iff_mem.mp h0) ((his09_false g).mp (hl1_no g h)).1
            · exact ⟨hg1_or, u1, hu1_ne0, hu1_ne9, hg1_in⟩
            · exact absurd (List.contains_iff_mem.mp h0) ((his09_false g).mp (hl2_no g h)).1
            · rw [hg2_n0] at h0; cases h0
            · exact absurd (List.contains_iff_mem.mp h0) ((his09_false g).mp (hl3_no g h)).1
          have hS9 : ∀ g ∈ C.gates, g.inputs.contains 9 = true →
              g.op = GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9]) := by
            intro g hg h9
            rw [hCg] at hg; simp only [List.mem_append, List.mem_cons] at hg
            rcases hg with h | rfl | h | rfl | h
            · exact absurd (List.contains_iff_mem.mp h9) ((his09_false g).mp (hl1_no g h)).2
            · rw [hg1_n9] at h9; cases h9
            · exact absurd (List.contains_iff_mem.mp h9) ((his09_false g).mp (hl2_no g h)).2
            · exact ⟨hg2_and, u2, hu2_ne0, hu2_ne9, hg2_in⟩
            · exact absurd (List.contains_iff_mem.mp h9) ((his09_false g).mp (hl3_no g h)).2
          exact hMixedOrAnd C hFan hSz hF0 hF9 hS0 hS9 hFlt4
      · rcases hg2_form with ⟨hg2_or, hg2_in⟩ | ⟨hg2_and, hg2_in⟩
        · have hg1_n0 : g1.inputs.contains 0 = false := by
            cases hb : g1.inputs.contains 0
            · rfl
            · rw [List.contains_iff_mem] at hb
              rcases hg1_in with h | h <;> (rw [h] at hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with h0 | h0 <;> omega)
          have hg1_9 : g1.inputs.contains 9 = true := by
            rw [List.contains_iff_mem]; rcases hg1_in with h | h <;> rw [h]
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem u1 List.mem_cons_self
          have hg2_0 : g2.inputs.contains 0 = true := by
            rw [List.contains_iff_mem]; rcases hg2_in with h | h <;> rw [h]
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem u2 List.mem_cons_self
          have hg2_n9 : g2.inputs.contains 9 = false := by
            cases hb : g2.inputs.contains 9
            · rfl
            · rw [List.contains_iff_mem] at hb
              rcases hg2_in with h | h <;> (rw [h] at hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with h9 | h9 <;> omega)
          have hF0 : (C.gates.filter (fun g => g.inputs.contains 0)).length = 1 := by
            rw [hC_filter0_all, hg1_n0, hg2_0,
              hFlt_empty l1 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl1_no g hg)).1 (List.contains_iff_mem.mp h)),
              hFlt_empty l2 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl2_no g hg)).1 (List.contains_iff_mem.mp h)),
              hFlt_empty l3 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl3_no g hg)).1 (List.contains_iff_mem.mp h))]
            rfl
          have hF9 : (C.gates.filter (fun g => g.inputs.contains 9)).length = 1 := by
            rw [hC_filter0_all, hg1_9, hg2_n9,
              hFlt_empty l1 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl1_no g hg)).2 (List.contains_iff_mem.mp h)),
              hFlt_empty l2 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl2_no g hg)).2 (List.contains_iff_mem.mp h)),
              hFlt_empty l3 _ (fun g hg => by rw [Bool.eq_false_iff]; intro h; exact ((his09_false g).mp (hl3_no g hg)).2 (List.contains_iff_mem.mp h))]
            rfl
          have hS0 : ∀ g ∈ C.gates, g.inputs.contains 0 = true →
              g.op = GateOp.or ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0]) := by
            intro g hg h0
            rw [hCg] at hg; simp only [List.mem_append, List.mem_cons] at hg
            rcases hg with h | rfl | h | rfl | h
            · exact absurd (List.contains_iff_mem.mp h0) ((his09_false g).mp (hl1_no g h)).1
            · rw [hg1_n0] at h0; cases h0
            · exact absurd (List.contains_iff_mem.mp h0) ((his09_false g).mp (hl2_no g h)).1
            · exact ⟨hg2_or, u2, hu2_ne0, hu2_ne9, hg2_in⟩
            · exact absurd (List.contains_iff_mem.mp h0) ((his09_false g).mp (hl3_no g h)).1
          have hS9 : ∀ g ∈ C.gates, g.inputs.contains 9 = true →
              g.op = GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9]) := by
            intro g hg h9
            rw [hCg] at hg; simp only [List.mem_append, List.mem_cons] at hg
            rcases hg with h | rfl | h | rfl | h
            · exact absurd (List.contains_iff_mem.mp h9) ((his09_false g).mp (hl1_no g h)).2
            · exact ⟨hg1_and, u1, hu1_ne0, hu1_ne9, hg1_in⟩
            · exact absurd (List.contains_iff_mem.mp h9) ((his09_false g).mp (hl2_no g h)).2
            · rw [hg2_n9] at h9; cases h9
            · exact absurd (List.contains_iff_mem.mp h9) ((his09_false g).mp (hl3_no g h)).2
          exact hMixedOrAnd C hFan hSz hF0 hF9 hS0 hS9 hFlt4
        · have hno0 : ∀ g ∈ C.gates, 0 ∉ g.inputs := by
            intro g hg
            rw [hCg] at hg
            simp only [List.mem_append, List.mem_cons] at hg
            rcases hg with h | rfl | h | rfl | h
            · exact ((his09_false g).mp (hl1_no g h)).1
            · intro h0
              rcases hg1_in with h | h <;> (rw [h] at h0; simp only [List.mem_cons, List.not_mem_nil, or_false] at h0; rcases h0 with h0 | h0 <;> omega)
            · exact ((his09_false g).mp (hl2_no g h)).1
            · intro h0
              rcases hg2_in with h | h <;> (rw [h] at h0; simp only [List.mem_cons, List.not_mem_nil, or_false] at h0; rcases h0 with h0 | h0 <;> omega)
            · exact ((his09_false g).mp (hl3_no g h)).1
          let remap0 : ℕ → ℕ := fun i => if i = 9 then 0 else if i < 9 then i else i - 1
          let D : Circuit := ⟨C.gates.map fun g => ⟨g.op, g.inputs.map remap0⟩, remap0 C.output⟩
          have hrem_0 (i : ℕ) (hi0 : i ≠ 0) : remap0 i = 0 ↔ i = 9 := by
            dsimp only [remap0]; split_ifs <;> omega
          have hrem_4 (i : ℕ) : remap0 i = 4 ↔ i = 4 := by
            by_cases h9 : i = 9
            · subst h9; decide
            · by_cases hlt : i < 9
              · simp only [remap0, h9, hlt, ↓reduceIte]
              · simp only [remap0, h9, hlt, ↓reduceIte]
                constructor <;> (intro h; omega)
          have hrem_mem0 (g : Gate) (hg0 : 0 ∉ g.inputs) :
              (g.inputs.map remap0).contains 0 = is09 g := by
            rw [Bool.eq_iff_iff, List.contains_iff_mem, his09_iff, List.mem_map]
            constructor
            · rintro ⟨u, hu, hru⟩
              have hu0 : u ≠ 0 := fun h => hg0 (h ▸ hu)
              rw [(hrem_0 u hu0).mp hru] at hu
              exact Or.inr hu
            · rintro (h0 | h9)
              · exact absurd h0 hg0
              · exact ⟨9, h9, rfl⟩
          have hrem_mem4 (g : Gate) :
              (g.inputs.map remap0).contains 4 = g.inputs.contains 4 := by
            rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
            constructor
            · rintro ⟨u, hu, hru⟩
              rw [(hrem_4 u).mp hru] at hu; exact hu
            · intro h4; exact ⟨4, h4, rfl⟩
          have hD_fan : FanInTwo D := by
            intro g hg
            simp only [D, List.mem_map] at hg
            obtain ⟨g0, hg0, rfl⟩ := hg
            have hf := hFan g0 hg0
            exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
          have hD_sz : D.size = 14 := by
            change (C.gates.map _).length = 14
            rw [List.length_map]; exact hSz
          have hD_flt0 : (D.gates.filter (fun g => g.inputs.contains 0)).length = 2 := by
            change ((C.gates.map fun g : Gate => Gate.mk g.op (g.inputs.map remap0)).filter (fun g => g.inputs.contains 0)).length = 2
            rw [hMap_filter_len _ _ is09 C.gates (fun g hg => hrem_mem0 g (hno0 g hg))]
            exact hFlt09
          have hD_flt4 : (D.gates.filter (fun g => !g.inputs.contains 0 && g.inputs.contains 4)).length ≤ 1 := by
            change ((C.gates.map fun g : Gate => Gate.mk g.op (g.inputs.map remap0)).filter (fun g => !g.inputs.contains 0 && g.inputs.contains 4)).length ≤ 1
            rw [hMap_filter_len _ _ (fun g => !is09 g && g.inputs.contains 4) C.gates (fun g hg => by
              dsimp only; rw [hrem_mem0 g (hno0 g hg), hrem_mem4 g])]
            exact hFlt4
          have hD_0spec : ∀ g ∈ D.gates, g.inputs.contains 0 = true →
              g.op = GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0]) := by
            intro g hg h0
            simp only [D, List.mem_map] at hg
            obtain ⟨g0, hg0, rfl⟩ := hg
            dsimp only at h0 ⊢
            rw [hrem_mem0 g0 (hno0 g0 hg0)] at h0
            rw [hCg] at hg0
            simp only [List.mem_append, List.mem_cons] at hg0
            rcases hg0 with h | rfl | h | rfl | h
            · rw [hl1_no g0 h] at h0; cases h0
            · refine ⟨hg1_and, remap0 u1, fun hr => hu1_ne9 ((hrem_0 u1 hu1_ne0).mp hr), ?_⟩
              rcases hg1_in with h | h <;> rw [h]
              · exact Or.inl rfl
              · exact Or.inr rfl
            · rw [hl2_no g0 h] at h0; cases h0
            · refine ⟨hg2_and, remap0 u2, fun hr => hu2_ne9 ((hrem_0 u2 hu2_ne0).mp hr), ?_⟩
              rcases hg2_in with h | h <;> rw [h]
              · exact Or.inl rfl
              · exact Or.inr rfl
            · rw [hl3_no g0 h] at h0; cases h0
          obtain ⟨y, hy⟩ := hBothAnd D hD_fan hD_sz hD_flt0 hD_0spec hD_flt4
          let x : Fin 9 → Bool := Function.update y 0 (!y 0)
          have hrem_sim (gs : List Gate) (hgs : ∀ g ∈ gs, 0 ∉ g.inputs)
              (wA wB : List Bool) (hwA : 9 ≤ wA.length) (hwB : wB.length = wA.length + 1)
              (hrel : ∀ i, i ≠ 0 → wA.getD (remap0 i) false = wB.getD i false) :
              ∀ i, i ≠ 0 → (run (gs.map fun g => ⟨g.op, g.inputs.map remap0⟩) wA).getD (remap0 i) false =
                (run gs wB).getD i false := by
            induction gs generalizing wA wB with
            | nil => exact hrel
            | cons g rest ih =>
              simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
              have hg0 : 0 ∉ g.inputs := hgs g List.mem_cons_self
              have hinp : (g.inputs.map remap0).map (fun j => wA.getD j false) = g.inputs.map (fun i => wB.getD i false) := by
                rw [List.map_map]; apply List.map_congr_left
                intro i hi; exact hrel i (fun h => hg0 (h ▸ hi))
              let b := g.op.eval (g.inputs.map fun i => wB.getD i false)
              have hstepA : step wA ⟨g.op, g.inputs.map remap0⟩ = wA ++ [b] := by dsimp only [step, b]; rw [hinp]
              rw [hstepA]
              apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (wA ++ [b]) (step wB g)
              · simp only [List.length_append, List.length_cons, List.length_nil]; omega
              · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
              · intro i hi0
                dsimp only [step]
                by_cases heq : i = wB.length
                · subst heq
                  have hrm : remap0 wB.length = wA.length := by dsimp only [remap0]; split_ifs <;> omega
                  rw [hrm, getD_snoc_eq wA b, getD_snoc_eq wB b]
                · have hrm_ne : remap0 i ≠ wA.length := by dsimp only [remap0]; split_ifs <;> omega
                  rw [getD_snoc_ne wA b (remap0 i) hrm_ne, getD_snoc_ne wB b i heq]
                  exact hrel i hi0
          have hbase : ∀ i, i ≠ 0 → (List.ofFn y).getD (remap0 i) false = (List.ofFn x ++ [!x 0]).getD i false := by
            intro i hi0
            by_cases hi9 : i = 9
            · subst hi9
              have hrm : remap0 9 = 0 := rfl
              rw [hrm]
              have hlt0 : 0 < (List.ofFn y).length := by simp only [List.length_ofFn]; omega
              rw [List.getD_eq_getElem _ _ hlt0, List.getElem_ofFn]
              have hsn : (List.ofFn x ++ [!x 0]).getD 9 false = !x 0 := by
                simpa only [List.length_ofFn] using getD_snoc_eq (List.ofFn x) (!x 0)
              rw [hsn]
              have hx0 : x 0 = !y 0 := Function.update_self 0 (!y 0) y
              rw [hx0, Bool.not_not]
              rfl
            · by_cases hi : i < 9
              · have hrm : remap0 i = i := by simp only [remap0, hi9, hi, ↓reduceIte]
                rw [hrm]
                have hlt1 : i < (List.ofFn y).length := by simp only [List.length_ofFn]; exact hi
                have hlt2 : i < (List.ofFn x).length := by simp only [List.length_ofFn]; exact hi
                rw [List.getD_append _ _ _ _ hlt2, List.getD_eq_getElem _ _ hlt1, List.getElem_ofFn,
                    List.getD_eq_getElem _ _ hlt2, List.getElem_ofFn]
                dsimp only [x]
                rw [Function.update_of_ne (fun h => hi0 (congrArg Fin.val h))]
              · have hrm : remap0 i = i - 1 := by simp only [remap0, hi9, hi, ↓reduceIte]
                rw [hrm, List.getD_eq_default (List.ofFn y) false (n := i - 1) (by simp only [List.length_ofFn]; omega),
                    List.getD_eq_default (List.ofFn x ++ [!x 0]) false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
          have hev := hrem_sim C.gates hno0 (List.ofFn y) (List.ofFn x ++ [!x 0])
            (by simp only [List.length_ofFn]; omega)
            (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
            hbase C.output (fun h => h0nS (h ▸ houtS))
          refine ⟨x, ?_⟩
          change (run C.gates (List.ofFn x ++ [!x 0])).getD C.output false ≠ p9 x
          rw [← hev]
          exact hy
    · have hEraseDead (pre suf : List Gate) (gDead : Gate) (hsp : C.gates = pre ++ gDead :: suf)
          (hdead_nS : 10 + pre.length ∉ S) (hdead_09 : is09 gDead = true)
          (hother_nDead : ∀ g ∈ pre ++ suf, 10 + pre.length ∉ g.inputs)
          (hlive_spec : ∀ g ∈ pre ++ suf, is09 g = true →
            ∃ u ∈ S,
              (g.op = GateOp.or ∧ (g.inputs = [0, u] ∨ g.inputs = [u, 0])) ∨
              (g.op = GateOp.and ∧ (g.inputs = [9, u] ∨ g.inputs = [u, 9]))) :
          ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠ p9 x := by
        let wd : ℕ := 10 + pre.length
        let sh : ℕ → ℕ := fun i => if i < wd then i else i - 1
        let D : Circuit := ⟨pre ++ suf.map (fun g => ⟨g.op, g.inputs.map sh⟩), sh C.output⟩
        have hsh_lt (i : ℕ) (hi : i < 10) : sh i = i := by simp only [sh, wd]; split_ifs <;> omega
        have hsh_eq_small (i k : ℕ) (hi : i ≠ wd) (hk : k < 10) : sh i = k ↔ i = k := by
          dsimp only [sh, wd] at hi ⊢; split_ifs <;> omega
        have hsh_mem_small (g : Gate) (hg : wd ∉ g.inputs) (k : ℕ) (hk : k < 10) :
            (g.inputs.map sh).contains k = g.inputs.contains k := by
          rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
          constructor
          · rintro ⟨u, hu, hsu⟩
            rw [(hsh_eq_small u k (fun h => hg (h ▸ hu)) hk).mp hsu] at hu; exact hu
          · intro hk_mem; exact ⟨k, hk_mem, hsh_lt k hk⟩
        have hsh_is09 (g : Gate) (hg : wd ∉ g.inputs) : is09 ⟨g.op, g.inputs.map sh⟩ = is09 g := by
          rw [Bool.eq_iff_iff, his09_iff, his09_iff]
          dsimp only
          rw [← List.contains_iff_mem, ← List.contains_iff_mem, ← List.contains_iff_mem, ← List.contains_iff_mem,
              hsh_mem_small g hg 0 (by omega), hsh_mem_small g hg 9 (by omega)]
        have hD_fan : FanInTwo D := by
          intro g hg
          simp only [D, List.mem_append, List.mem_map] at hg
          rcases hg with hg1 | ⟨g0, hg0, rfl⟩
          · exact hFan g (by rw [hsp]; exact List.mem_append_left _ hg1)
          · have hf := hFan g0 (by rw [hsp]; exact List.mem_append_right _ (List.mem_cons_of_mem gDead hg0))
            exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
        have hD_sz : D.size = 13 := by
          change (pre ++ suf.map _).length = 13
          have hlenC : C.gates.length = 14 := hSz
          rw [hsp, List.length_append, List.length_cons] at hlenC
          simp only [List.length_append, List.length_map]; omega
        have hMap_flen (p q : Gate → Bool) (gs : List Gate) (hpq : ∀ g ∈ gs, p ⟨g.op, g.inputs.map sh⟩ = q g) :
            ((gs.map fun g => ⟨g.op, g.inputs.map sh⟩).filter p).length = (gs.filter q).length := by
          induction gs with
          | nil => rfl
          | cons a t ih =>
            simp only [List.map_cons, List.filter_cons]
            rw [hpq a List.mem_cons_self]
            have ht := ih (fun g hg => hpq g (List.mem_cons_of_mem a hg))
            cases q a <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ht]
        have hD_flt09 : (D.gates.filter is09).length = 1 := by
          have hC2 : (C.gates.filter is09).length = 2 := hFlt09
          rw [hsp, List.filter_append, List.filter_cons, hdead_09] at hC2
          simp only [↓reduceIte, List.length_append, List.length_cons] at hC2
          change ((pre ++ suf.map fun g : Gate => Gate.mk g.op (g.inputs.map sh)).filter is09).length = 1
          rw [List.filter_append, List.length_append,
              hMap_flen is09 is09 suf (fun g hg => hsh_is09 g (hother_nDead g (List.mem_append_right _ hg)))]
          omega
        have hD_flt4 : (D.gates.filter (fun g => !is09 g && g.inputs.contains 4)).length ≤ 1 := by
          have hC4 : (C.gates.filter (fun g => !is09 g && g.inputs.contains 4)).length ≤ 1 := hFlt4
          rw [hsp, List.filter_append, List.filter_cons, hdead_09] at hC4
          simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.length_append] at hC4
          change ((pre ++ suf.map fun g : Gate => Gate.mk g.op (g.inputs.map sh)).filter (fun g => !is09 g && g.inputs.contains 4)).length ≤ 1
          rw [List.filter_append, List.length_append,
              hMap_flen _ (fun g => !is09 g && g.inputs.contains 4) suf (fun g hg => by
                dsimp only
                rw [hsh_is09 g (hother_nDead g (List.mem_append_right _ hg)),
                    hsh_mem_small g (hother_nDead g (List.mem_append_right _ hg)) 4 (by omega)])]
          exact hC4
        have hD_09spec : ∀ g ∈ D.gates, is09 g = true →
            (g.op = GateOp.or ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) ∨
            (g.op = GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9])) := by
          intro g hg h09
          simp only [D, List.mem_append, List.mem_map] at hg
          rcases hg with hg1 | ⟨g0, hg0, rfl⟩
          · obtain ⟨u, huS, hform⟩ := hlive_spec g (List.mem_append_left _ hg1) h09
            have hu0 : u ≠ 0 := fun h => h0nS (h ▸ huS)
            have hu9 : u ≠ 9 := fun h => h9nS (h ▸ huS)
            rcases hform with ⟨hor, hin⟩ | ⟨hand, hin⟩
            · exact Or.inl ⟨hor, u, hu0, hu9, hin⟩
            · exact Or.inr ⟨hand, u, hu0, hu9, hin⟩
          · rw [hsh_is09 g0 (hother_nDead g0 (List.mem_append_right _ hg0))] at h09
            obtain ⟨u, huS, hform⟩ := hlive_spec g0 (List.mem_append_right _ hg0) h09
            have hu0 : u ≠ 0 := fun h => h0nS (h ▸ huS)
            have hu9 : u ≠ 9 := fun h => h9nS (h ▸ huS)
            have huwd : u ≠ wd := fun h => hdead_nS (by dsimp only [wd] at h; rw [← h]; exact huS)
            have hshu0 : sh u ≠ 0 := fun h => hu0 ((hsh_eq_small u 0 huwd (by omega)).mp h)
            have hshu9 : sh u ≠ 9 := fun h => hu9 ((hsh_eq_small u 9 huwd (by omega)).mp h)
            rcases hform with ⟨hor, hin⟩ | ⟨hand, hin⟩
            · refine Or.inl ⟨hor, sh u, hshu0, hshu9, ?_⟩
              dsimp only
              rcases hin with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hsh_lt 0 (by omega)]
              · exact Or.inl rfl
              · exact Or.inr rfl
            · refine Or.inr ⟨hand, sh u, hshu0, hshu9, ?_⟩
              dsimp only
              rcases hin with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hsh_lt 9 (by omega)]
              · exact Or.inl rfl
              · exact Or.inr rfl
        obtain ⟨x, hx⟩ := hOneLive09 D hD_fan hD_sz hD_flt09 hD_09spec hD_flt4
        let inp := List.ofFn x ++ [!x 0]
        let wA1 := run pre inp
        let wB2 := step wA1 gDead
        have hwA1_len : wA1.length = wd := by
          dsimp only [wA1, inp, wd]
          rw [run_len, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
        have hmid_rel : ∀ i, i ≠ wd → wA1.getD (sh i) false = wB2.getD i false := by
          intro i hiwd
          by_cases hlt : i < wd
          · have hshi : sh i = i := by simp only [sh, hlt, ↓reduceIte]
            rw [hshi]; dsimp only [wB2, step]
            exact (getD_snoc_ne wA1 _ i (by omega)).symm
          · have hshi : sh i = i - 1 := by simp only [sh, hlt, ↓reduceIte]
            rw [hshi, List.getD_eq_default wA1 false (n := i - 1) (by omega),
                List.getD_eq_default wB2 false (n := i) (by simp only [wB2, step, List.length_append, List.length_cons, List.length_nil]; omega)]
        have hsh_sim (gs : List Gate) (hgs : ∀ g ∈ gs, wd ∉ g.inputs)
            (wA wB : List Bool) (hwA : wd ≤ wA.length) (hwB : wB.length = wA.length + 1)
            (hrel : ∀ i, i ≠ wd → wA.getD (sh i) false = wB.getD i false) :
            ∀ i, i ≠ wd → (run (gs.map fun g => ⟨g.op, g.inputs.map sh⟩) wA).getD (sh i) false =
              (run gs wB).getD i false := by
          induction gs generalizing wA wB with
          | nil => exact hrel
          | cons g rest ih =>
            simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
            have hgwd : wd ∉ g.inputs := hgs g List.mem_cons_self
            have hinp : (g.inputs.map sh).map (fun j => wA.getD j false) = g.inputs.map (fun i => wB.getD i false) := by
              rw [List.map_map]; apply List.map_congr_left
              intro i hi; exact hrel i (fun h => hgwd (h ▸ hi))
            let b := g.op.eval (g.inputs.map fun i => wB.getD i false)
            have hstepA : step wA ⟨g.op, g.inputs.map sh⟩ = wA ++ [b] := by dsimp only [step, b]; rw [hinp]
            rw [hstepA]
            apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (wA ++ [b]) (step wB g)
            · simp only [List.length_append, List.length_cons, List.length_nil]; omega
            · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
            · intro i hiwd
              dsimp only [step]
              by_cases heq : i = wB.length
              · subst heq
                have hshi : sh wB.length = wA.length := by dsimp only [sh]; split_ifs <;> omega
                rw [hshi, getD_snoc_eq wA b, getD_snoc_eq wB b]
              · have hsh_ne : sh i ≠ wA.length := by dsimp only [sh]; split_ifs <;> omega
                rw [getD_snoc_ne wA b (sh i) hsh_ne, getD_snoc_ne wB b i heq]
                exact hrel i hiwd
        have hfinal := hsh_sim suf (fun g hg => hother_nDead g (List.mem_append_right _ hg)) wA1 wB2
          (by omega) (by simp only [wB2, step, List.length_append, List.length_cons, List.length_nil])
          hmid_rel C.output (fun h => hdead_nS (by dsimp only [wd] at h; rw [← h]; exact houtS))
        refine ⟨x, ?_⟩
        change (run C.gates inp).getD C.output false ≠ p9 x
        have hDeq : (run D.gates inp).getD (sh C.output) false = (run C.gates inp).getD C.output false := by
          change (run (pre ++ suf.map fun g => ⟨g.op, g.inputs.map sh⟩) inp).getD (sh C.output) false = _
          rw [run_append, hfinal]
          conv_rhs => rw [hsp, run_append]
          rfl
        rw [← hDeq]
        exact hx
      have hCg2 : C.gates = (l1 ++ [g1] ++ l2) ++ g2 :: l3 := by
        rw [hCg]; simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hlen2_eq : 10 + (l1 ++ [g1] ++ l2).length = w2 := by
        simp only [w2, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      apply hEraseDead (l1 ++ [g1] ++ l2) l3 g2 hCg2 (by rw [hlen2_eq]; exact hw2S) hg2_09
      · intro g hg
        rw [hlen2_eq]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with ((h | rfl) | h) | h
        · exact fun h2 => hw2S (hNon09_all_in g (List.mem_append_left _ (List.mem_append_left _ h)) w2 h2)
        · obtain ⟨u1, hu1S, hform⟩ := hg1_spec hw1S
          intro h2
          rcases hform with ⟨_, hin⟩ | ⟨_, hin⟩
          · rcases hin with h | h
            · rw [h, List.mem_cons, List.mem_singleton] at h2
              rcases h2 with h2 | h2
              · dsimp only [w2] at h2; omega
              · exact hw2S (by rw [h2]; exact hu1S)
            · rw [h, List.mem_cons, List.mem_singleton] at h2
              rcases h2 with h2 | h2
              · exact hw2S (by rw [h2]; exact hu1S)
              · dsimp only [w2] at h2; omega
          · rcases hin with h | h
            · rw [h, List.mem_cons, List.mem_singleton] at h2
              rcases h2 with h2 | h2
              · dsimp only [w2] at h2; omega
              · exact hw2S (by rw [h2]; exact hu1S)
            · rw [h, List.mem_cons, List.mem_singleton] at h2
              rcases h2 with h2 | h2
              · exact hw2S (by rw [h2]; exact hu1S)
              · dsimp only [w2] at h2; omega
        · exact fun h2 => hw2S (hNon09_all_in g (List.mem_append_left _ (List.mem_append_right _ h)) w2 h2)
        · exact fun h2 => hw2S (hNon09_all_in g (List.mem_append_right _ h) w2 h2)
      · intro g hg h09
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with ((h | rfl) | h) | h
        · rw [hl1_no g h] at h09; cases h09
        · exact hg1_spec hw1S
        · rw [hl2_no g h] at h09; cases h09
        · rw [hl3_no g h] at h09; cases h09
  · by_cases hw2S : w2 ∈ S
    · let wd : ℕ := w1
      let pre : List Gate := l1
      let suf : List Gate := l2 ++ g2 :: l3
      let sh : ℕ → ℕ := fun i => if i < wd then i else i - 1
      let D : Circuit := ⟨pre ++ suf.map (fun g => ⟨g.op, g.inputs.map sh⟩), sh C.output⟩
      have hother_nDead : ∀ g ∈ pre ++ suf, wd ∉ g.inputs := by
        intro g hg
        simp only [pre, suf, List.mem_append, List.mem_cons] at hg
        rcases hg with h | h | rfl | h
        · exact fun h1 => hw1S (hNon09_all_in g (List.mem_append_left _ (List.mem_append_left _ h)) w1 h1)
        · exact fun h1 => hw1S (hNon09_all_in g (List.mem_append_left _ (List.mem_append_right _ h)) w1 h1)
        · obtain ⟨u2, hu2S, hform⟩ := hg2_spec hw2S
          intro h1
          rcases hform with ⟨_, hin⟩ | ⟨_, hin⟩
          · rcases hin with h | h
            · rw [h, List.mem_cons, List.mem_singleton] at h1
              rcases h1 with h1 | h1
              · dsimp only [wd, w1] at h1; omega
              · exact hw1S (by dsimp only [wd] at h1; rw [h1]; exact hu2S)
            · rw [h, List.mem_cons, List.mem_singleton] at h1
              rcases h1 with h1 | h1
              · exact hw1S (by dsimp only [wd] at h1; rw [h1]; exact hu2S)
              · dsimp only [wd, w1] at h1; omega
          · rcases hin with h | h
            · rw [h, List.mem_cons, List.mem_singleton] at h1
              rcases h1 with h1 | h1
              · dsimp only [wd, w1] at h1; omega
              · exact hw1S (by dsimp only [wd] at h1; rw [h1]; exact hu2S)
            · rw [h, List.mem_cons, List.mem_singleton] at h1
              rcases h1 with h1 | h1
              · exact hw1S (by dsimp only [wd] at h1; rw [h1]; exact hu2S)
              · dsimp only [wd, w1] at h1; omega
        · exact fun h1 => hw1S (hNon09_all_in g (List.mem_append_right _ h) w1 h1)
      have hsh_lt (i : ℕ) (hi : i < 10) : sh i = i := by simp only [sh, wd, w1]; split_ifs <;> omega
      have hsh_eq_small (i k : ℕ) (hi : i ≠ wd) (hk : k < 10) : sh i = k ↔ i = k := by
        dsimp only [sh, wd, w1] at hi ⊢; split_ifs <;> omega
      have hsh_mem_small (g : Gate) (hg : wd ∉ g.inputs) (k : ℕ) (hk : k < 10) :
          (g.inputs.map sh).contains k = g.inputs.contains k := by
        rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
        constructor
        · rintro ⟨u, hu, hsu⟩
          rw [(hsh_eq_small u k (fun h => hg (h ▸ hu)) hk).mp hsu] at hu; exact hu
        · intro hk_mem; exact ⟨k, hk_mem, hsh_lt k hk⟩
      have hsh_is09 (g : Gate) (hg : wd ∉ g.inputs) : is09 ⟨g.op, g.inputs.map sh⟩ = is09 g := by
        rw [Bool.eq_iff_iff, his09_iff, his09_iff]; dsimp only
        rw [← List.contains_iff_mem, ← List.contains_iff_mem, ← List.contains_iff_mem, ← List.contains_iff_mem,
            hsh_mem_small g hg 0 (by omega), hsh_mem_small g hg 9 (by omega)]
      have hD_fan : FanInTwo D := by
        intro g hg
        simp only [D, List.mem_append, List.mem_map] at hg
        rcases hg with hg1 | ⟨g0, hg0, rfl⟩
        · exact hFan g (by rw [hCg]; exact List.mem_append_left _ hg1)
        · have hf := hFan g0 (by rw [hCg]; exact List.mem_append_right _ (List.mem_cons_of_mem g1 hg0))
          exact ⟨hf.1, by simp only [List.length_map]; exact hf.2⟩
      have hD_sz : D.size = 13 := by
        change (pre ++ suf.map _).length = 13
        have hlenC : C.gates.length = 14 := hSz
        rw [hCg, List.length_append, List.length_cons] at hlenC
        simp only [pre, suf, List.length_append, List.length_map] at hlenC ⊢; omega
      have hMap_flen (p q : Gate → Bool) (gs : List Gate) (hpq : ∀ g ∈ gs, p ⟨g.op, g.inputs.map sh⟩ = q g) :
          ((gs.map fun g => ⟨g.op, g.inputs.map sh⟩).filter p).length = (gs.filter q).length := by
        induction gs with
        | nil => rfl
        | cons a t ih =>
          simp only [List.map_cons, List.filter_cons]
          rw [hpq a List.mem_cons_self]
          have ht := ih (fun g hg => hpq g (List.mem_cons_of_mem a hg))
          cases q a <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ht]
      have hD_flt09 : (D.gates.filter is09).length = 1 := by
        have hC2 : (C.gates.filter is09).length = 2 := hFlt09
        rw [hCg, List.filter_append, List.filter_cons, hg1_09] at hC2
        simp only [↓reduceIte, List.length_append, List.length_cons] at hC2
        change ((pre ++ suf.map fun g : Gate => Gate.mk g.op (g.inputs.map sh)).filter is09).length = 1
        rw [List.filter_append, List.length_append,
            hMap_flen is09 is09 suf (fun g hg => hsh_is09 g (hother_nDead g (List.mem_append_right _ hg)))]
        dsimp only [pre, suf]
        omega
      have hD_flt4 : (D.gates.filter (fun g => !is09 g && g.inputs.contains 4)).length ≤ 1 := by
        have hC4 : (C.gates.filter (fun g => !is09 g && g.inputs.contains 4)).length ≤ 1 := hFlt4
        rw [hCg, List.filter_append, List.filter_cons, hg1_09] at hC4
        simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.length_append] at hC4
        change ((pre ++ suf.map fun g : Gate => Gate.mk g.op (g.inputs.map sh)).filter (fun g => !is09 g && g.inputs.contains 4)).length ≤ 1
        rw [List.filter_append, List.length_append,
            hMap_flen _ (fun g => !is09 g && g.inputs.contains 4) suf (fun g hg => by
              dsimp only
              rw [hsh_is09 g (hother_nDead g (List.mem_append_right _ hg)),
                  hsh_mem_small g (hother_nDead g (List.mem_append_right _ hg)) 4 (by omega)])]
        exact hC4
      have hD_09spec : ∀ g ∈ D.gates, is09 g = true →
          (g.op = GateOp.or ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) ∨
          (g.op = GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9])) := by
        intro g hg h09
        simp only [D, List.mem_append, List.mem_map] at hg
        rcases hg with hg1 | ⟨g0, hg0, rfl⟩
        · rw [hl1_no g hg1] at h09; cases h09
        · rw [hsh_is09 g0 (hother_nDead g0 (List.mem_append_right pre hg0))] at h09
          simp only [suf, List.mem_append, List.mem_cons] at hg0
          rcases hg0 with h | rfl | h
          · rw [hl2_no g0 h] at h09; cases h09
          · obtain ⟨u2, hu2S, hform⟩ := hg2_spec hw2S
            have hu0 : u2 ≠ 0 := fun h => h0nS (h ▸ hu2S)
            have hu9 : u2 ≠ 9 := fun h => h9nS (h ▸ hu2S)
            have huwd : u2 ≠ wd := fun h => hw1S (by dsimp only [wd] at h; rw [← h]; exact hu2S)
            have hshu0 : sh u2 ≠ 0 := fun h => hu0 ((hsh_eq_small u2 0 huwd (by omega)).mp h)
            have hshu9 : sh u2 ≠ 9 := fun h => hu9 ((hsh_eq_small u2 9 huwd (by omega)).mp h)
            rcases hform with ⟨hor, hin⟩ | ⟨hand, hin⟩
            · refine Or.inl ⟨hor, sh u2, hshu0, hshu9, ?_⟩
              dsimp only
              rcases hin with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hsh_lt 0 (by omega)]
              · exact Or.inl rfl
              · exact Or.inr rfl
            · refine Or.inr ⟨hand, sh u2, hshu0, hshu9, ?_⟩
              dsimp only
              rcases hin with h | h <;> rw [h, List.map_cons, List.map_cons, List.map_nil, hsh_lt 9 (by omega)]
              · exact Or.inl rfl
              · exact Or.inr rfl
          · rw [hl3_no g0 h] at h09; cases h09
      obtain ⟨x, hx⟩ := hOneLive09 D hD_fan hD_sz hD_flt09 hD_09spec hD_flt4
      let inp := List.ofFn x ++ [!x 0]
      let wA1 := run pre inp
      let wB2 := step wA1 g1
      have hwA1_len : wA1.length = wd := by
        dsimp only [wA1, inp, wd, w1, pre]
        rw [run_len, List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      have hmid_rel : ∀ i, i ≠ wd → wA1.getD (sh i) false = wB2.getD i false := by
        intro i hiwd
        by_cases hlt : i < wd
        · have hshi : sh i = i := by simp only [sh, hlt, ↓reduceIte]
          rw [hshi]; dsimp only [wB2, step]
          exact (getD_snoc_ne wA1 _ i (by omega)).symm
        · have hshi : sh i = i - 1 := by simp only [sh, hlt, ↓reduceIte]
          rw [hshi, List.getD_eq_default wA1 false (n := i - 1) (by omega),
              List.getD_eq_default wB2 false (n := i) (by simp only [wB2, step, List.length_append, List.length_cons, List.length_nil]; omega)]
      have hsh_sim (gs : List Gate) (hgs : ∀ g ∈ gs, wd ∉ g.inputs)
          (wA wB : List Bool) (hwA : wd ≤ wA.length) (hwB : wB.length = wA.length + 1)
          (hrel : ∀ i, i ≠ wd → wA.getD (sh i) false = wB.getD i false) :
          ∀ i, i ≠ wd → (run (gs.map fun g => ⟨g.op, g.inputs.map sh⟩) wA).getD (sh i) false =
            (run gs wB).getD i false := by
        induction gs generalizing wA wB with
        | nil => exact hrel
        | cons g rest ih =>
          simp only [List.map_cons, run, List.foldl_cons] at ih ⊢
          have hgwd : wd ∉ g.inputs := hgs g List.mem_cons_self
          have hinp : (g.inputs.map sh).map (fun j => wA.getD j false) = g.inputs.map (fun i => wB.getD i false) := by
            rw [List.map_map]; apply List.map_congr_left
            intro i hi; exact hrel i (fun h => hgwd (h ▸ hi))
          let b := g.op.eval (g.inputs.map fun i => wB.getD i false)
          have hstepA : step wA ⟨g.op, g.inputs.map sh⟩ = wA ++ [b] := by dsimp only [step, b]; rw [hinp]
          rw [hstepA]
          apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (wA ++ [b]) (step wB g)
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega
          · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
          · intro i hiwd
            dsimp only [step]
            by_cases heq : i = wB.length
            · subst heq
              have hshi : sh wB.length = wA.length := by dsimp only [sh]; split_ifs <;> omega
              rw [hshi, getD_snoc_eq wA b, getD_snoc_eq wB b]
            · have hsh_ne : sh i ≠ wA.length := by dsimp only [sh]; split_ifs <;> omega
              rw [getD_snoc_ne wA b (sh i) hsh_ne, getD_snoc_ne wB b i heq]
              exact hrel i hiwd
      have hfinal := hsh_sim suf (fun g hg => hother_nDead g (List.mem_append_right _ hg)) wA1 wB2
        (by omega) (by simp only [wB2, step, List.length_append, List.length_cons, List.length_nil])
        hmid_rel C.output (fun h => hw1S (by dsimp only [wd] at h; rw [← h]; exact houtS))
      refine ⟨x, ?_⟩
      change (run C.gates inp).getD C.output false ≠ p9 x
      have hDeq : (run D.gates inp).getD (sh C.output) false = (run C.gates inp).getD C.output false := by
        change (run (pre ++ suf.map fun g => ⟨g.op, g.inputs.map sh⟩) inp).getD (sh C.output) false = _
        rw [run_append, hfinal]
        conv_rhs => rw [hCg, run_append]
        rfl
      rw [← hDeq]
      exact hx
    · let xA : Fin 9 → Bool := fun i => decide (i = 1)
      let xB : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have hp9A : p9 xA = false := by decide
      have hp9B : p9 xB = true := by decide
      have hS_agree (gs : List Gate) (wA wB : List Bool) (hlen : wA.length = wB.length)
          (hstepS : ∀ (pre : List Gate) (g : Gate) (suf : List Gate), gs = pre ++ g :: suf →
            wA.length + pre.length ∈ S → ∀ u ∈ g.inputs, u ∈ S)
          (hinit : ∀ i ∈ S, wA.getD i false = wB.getD i false) :
          ∀ i ∈ S, (run gs wA).getD i false = (run gs wB).getD i false := by
        induction gs generalizing wA wB with
        | nil => exact hinit
        | cons g rest ih =>
          simp only [run, List.foldl_cons] at ih ⊢
          apply ih (step wA g) (step wB g)
          · simp only [step, List.length_append, List.length_cons, List.length_nil, hlen]
          · intro pre g' suf hsp hmem u hu
            have h1 := hstepS (g :: pre) g' suf (by rw [hsp]; rfl)
            simp only [step, List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hmem h1
            have heq_len : wA.length + (pre.length + 1) = wA.length + 1 + pre.length := by omega
            rw [heq_len] at h1
            exact h1 hmem u hu
          · intro i hiS
            dsimp only [step]
            by_cases heq : i = wA.length
            · subst heq
              have hgin := hstepS [] g rest rfl (by simpa only [List.length_nil, Nat.add_zero] using hiS)
              have hinp : g.inputs.map (fun u => wA.getD u false) = g.inputs.map (fun u => wB.getD u false) := by
                apply List.map_congr_left
                intro u hu
                exact hinit u (hgin u hu)
              rw [getD_snoc_eq wA _, hlen, getD_snoc_eq wB _, hinp]
            · have heq2 : i ≠ wB.length := by rw [← hlen]; exact heq
              rw [getD_snoc_ne wA _ i heq, getD_snoc_ne wB _ i heq2]
              exact hinit i hiS
      have hC_stepS : ∀ (pre : List Gate) (g : Gate) (suf : List Gate), C.gates = pre ++ g :: suf →
          (List.ofFn xA ++ [!xA 0]).length + pre.length ∈ S → ∀ u ∈ g.inputs, u ∈ S := by
        intro pre g suf hsp hmem
        have hlen10 : (List.ofFn xA ++ [!xA 0]).length = 10 := by
          simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
        rw [hlen10] at hmem
        cases hb : is09 g
        · exact hNon09_inputs g (by rw [hsp]; exact List.mem_append_right _ List.mem_cons_self) hb
        · exfalso
          have hget : C.gates[pre.length]? = some g := by
            rw [hsp, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
          have hidx_eq : pre.length = l1.length ∨ pre.length = l1.length + 1 + l2.length := by
            by_cases hlt1 : pre.length < l1.length
            · rw [hCg, List.getElem?_append_left hlt1] at hget
              rw [hl1_no g (List.mem_of_getElem? hget)] at hb; cases hb
            · by_cases heq1 : pre.length = l1.length
              · exact Or.inl heq1
              · by_cases hlt2 : pre.length < l1.length + 1 + l2.length
                · have hCg2 : C.gates = (l1 ++ [g1]) ++ (l2 ++ g2 :: l3) := by
                    rw [hCg]; simp only [List.append_assoc, List.singleton_append]
                  have hge1 : (l1 ++ [g1]).length ≤ pre.length := by
                    simp only [List.length_append, List.length_cons, List.length_nil]; omega
                  have hlt2' : pre.length - (l1 ++ [g1]).length < l2.length := by
                    simp only [List.length_append, List.length_cons, List.length_nil]; omega
                  rw [hCg2, List.getElem?_append_right hge1, List.getElem?_append_left hlt2'] at hget
                  rw [hl2_no g (List.mem_of_getElem? hget)] at hb; cases hb
                · by_cases heq2 : pre.length = l1.length + 1 + l2.length
                  · exact Or.inr heq2
                  · have hCg3 : C.gates = (l1 ++ [g1] ++ l2 ++ [g2]) ++ l3 := by
                      rw [hCg]; simp only [List.append_assoc, List.cons_append, List.nil_append]
                    have hge2 : (l1 ++ [g1] ++ l2 ++ [g2]).length ≤ pre.length := by
                      simp only [List.length_append, List.length_cons, List.length_nil]; omega
                    rw [hCg3, List.getElem?_append_right hge2] at hget
                    rw [hl3_no g (List.mem_of_getElem? hget)] at hb; cases hb
          rcases hidx_eq with h1 | h2
          · rw [h1] at hmem; exact hw1S hmem
          · rw [h2] at hmem; exact hw2S hmem
      have hinit_AB : ∀ i ∈ S, (List.ofFn xA ++ [!xA 0]).getD i false = (List.ofFn xB ++ [!xB 0]).getD i false := by
        intro i hiS
        have hi0 : i ≠ 0 := fun h => h0nS (h ▸ hiS)
        have hi9 : i ≠ 9 := fun h => h9nS (h ▸ hiS)
        by_cases hi : i < 9
        · have hltA : i < (List.ofFn xA).length := by simp only [List.length_ofFn]; exact hi
          have hltB : i < (List.ofFn xB).length := by simp only [List.length_ofFn]; exact hi
          rw [List.getD_append _ _ _ _ hltA, List.getD_append _ _ _ _ hltB,
              List.getD_eq_getElem _ _ hltA, List.getElem_ofFn,
              List.getD_eq_getElem _ _ hltB, List.getElem_ofFn]
          simp only [xA, xB]
          have hne0 : (⟨i, hi⟩ : Fin 9) ≠ 0 := fun h => hi0 (congrArg Fin.val h)
          simp only [hne0, false_or]
        · rw [List.getD_eq_default (List.ofFn xA ++ [!xA 0]) false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega),
              List.getD_eq_default (List.ofFn xB ++ [!xB 0]) false (n := i) (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]; omega)]
      have hev_eq : C.eval (List.ofFn xA ++ [!xA 0]) = C.eval (List.ofFn xB ++ [!xB 0]) :=
        hS_agree C.gates (List.ofFn xA ++ [!xA 0]) (List.ofFn xB ++ [!xB 0])
          (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil])
          hC_stepS hinit_AB C.output houtS
      cases hval : C.eval (List.ofFn xA ++ [!xA 0])
      · refine ⟨xB, ?_⟩
        change C.eval (List.ofFn xB ++ [!xB 0]) ≠ p9 xB
        rw [← hev_eq, hval, hp9B]
        decide
      · refine ⟨xA, ?_⟩
        change C.eval (List.ofFn xA ++ [!xA 0]) ≠ p9 xA
        rw [hval, hp9A]
        decide
