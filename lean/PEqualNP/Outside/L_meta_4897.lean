import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

namespace PEqualNP.Outside.L_meta_4897

def OrPath (N : ℕ) (C : Circuit) (w target : ℕ) : Prop :=
  ∀ P : ℕ → Prop,
    P target →
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.or →
      ∀ a ∈ (gateAt C k).inputs, P a → P (N + k)) →
    P w

lemma orPath_refl (N : ℕ) (C : Circuit) (t : ℕ) : OrPath N C t t :=
  fun _ h _ => h

lemma orPath_step {N : ℕ} {C : Circuit} {k a t : ℕ}
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (ha : a ∈ (gateAt C k).inputs) (hp : OrPath N C a t) :
    OrPath N C (N + k) t :=
  fun P ht hs => hs k hk hor a ha (hp P ht hs)

lemma orPath_trans {N : ℕ} {C : Circuit} {u v w : ℕ}
    (huv : OrPath N C u v) (hvw : OrPath N C v w) : OrPath N C u w :=
  fun P hw hs => huv P (hvw P hw hs) hs

lemma orPath_cases {N : ℕ} {C : Circuit} {w t : ℕ} (h : OrPath N C w t) :
    w = t ∨ ∃ k < C.gates.length, w = N + k ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, OrPath N C a t := by
  apply h (fun x => x = t ∨ ∃ k < C.gates.length, x = N + k ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, OrPath N C a t)
  · exact Or.inl rfl
  · intro k hk hor a ha hPa
    refine Or.inr ⟨k, hk, rfl, hor, a, ha, ?_⟩
    rcases hPa with rfl | ⟨k', hk', rfl, hor', a', ha', hp'⟩
    · exact orPath_refl N C _
    · exact orPath_step hk' hor' ha' hp'

lemma orPath_parent {N : ℕ} {C : Circuit} {w t : ℕ} (h : OrPath N C w t) (hne : w ≠ t) :
    ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
      OrPath N C w (N + y) ∧ t ∈ (gateAt C y).inputs := by
  have hdisj : w = t ∨ ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
      OrPath N C w (N + y) ∧ t ∈ (gateAt C y).inputs := by
    apply h (fun x => x = t ∨ ∃ y < C.gates.length, (gateAt C y).op = GateOp.or ∧
        OrPath N C x (N + y) ∧ t ∈ (gateAt C y).inputs)
    · exact Or.inl rfl
    · intro k hk hor a ha hPa
      rcases hPa with rfl | ⟨y, hy, hory, hpy, hty⟩
      · exact Or.inr ⟨k, hk, hor, orPath_refl N C (N + k), ha⟩
      · exact Or.inr ⟨y, hy, hory, orPath_step hk hor ha hpy, hty⟩
  rcases hdisj with heq | hex
  · exact (hne heq).elim
  · exact hex

lemma orPath_le {N : ℕ} {C : Circuit} (hRB : ReadsBack N C) {w t : ℕ}
    (h : OrPath N C w t) : t ≤ w := by
  apply h (fun x => t ≤ x) (Nat.le_refl t)
  intro k hk _ a ha hta
  have hlt := hRB k hk a ha
  omega

lemma foldl_wires_len (gs : List Gate) :
    ∀ ws : List Bool,
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).length =
        ws.length + gs.length := by
  induction gs with
  | nil => intro ws; simp
  | cons g rest ih =>
    intro ws
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_prefix (gs : List Gate) :
    ∀ (ws : List Bool) (i : ℕ), i < ws.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) ws).getD i false =
        ws.getD i false := by
  induction gs with
  | nil => intro ws i _; rfl
  | cons g rest ih =>
    intro ws i hi
    simp only [List.foldl_cons]
    rw [ih (ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)]) i
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma wireVal_input (N : ℕ) (C : Circuit) (i : Fin N) (x : Fin N → Bool) :
    wireVal N C i.val x = x i := by
  unfold wireVal Circuit.wires
  rw [foldl_wires_prefix C.gates (List.ofFn x) i.val (by simp [i.isLt])]
  rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]

lemma wireVal_gate {N : ℕ} {C : Circuit} (hRB : ReadsBack N C)
    (k : ℕ) (hk : k < C.gates.length) (x : Fin N → Bool) :
    wireVal N C (N + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => wireVal N C i x) := by
  unfold wireVal Circuit.wires
  have hsplit : C.gates = C.gates.take k ++ [gateAt C k] ++ C.gates.drop (k + 1) := by
    have h1 : C.gates = C.gates.take (k + 1) ++ C.gates.drop (k + 1) :=
      (List.take_append_drop (k + 1) C.gates).symm
    conv_lhs => rw [h1, List.take_succ_eq_append_getElem hk, ← List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hk]
    rfl
  let w0 := (C.gates.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)
  have hw0_len : w0.length = N + k := by
    dsimp only [w0]
    rw [foldl_wires_len, List.length_ofFn, List.length_take]
    omega
  have hw_lt : ∀ i < N + k,
      (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) (List.ofFn x)).getD i false =
        w0.getD i false := by
    intro i hi
    conv_lhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
    exact foldl_wires_prefix (C.gates.drop k) w0 i (by omega)
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_append]
  have hstep_len :
      ([gateAt C k].foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length = N + k + 1 := by
    rw [foldl_wires_len]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [foldl_wires_prefix (C.gates.drop (k + 1)) _ (N + k) (by change N + k < ([gateAt C k].foldl _ w0).length; omega)]
  simp only [List.foldl_cons, List.foldl_nil]
  change (w0 ++ [(gateAt C k).op.eval ((gateAt C k).inputs.map fun i => w0.getD i false)]).getD (N + k) false = _
  rw [← hw0_len, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hw_lt i (hRB k hk i hi)).symm

lemma wireVal_or_mem {N : ℕ} {C : Circuit} (hRB : ReadsBack N C)
    {k a : ℕ} (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (ha : a ∈ (gateAt C k).inputs) (x : Fin N → Bool)
    (hva : wireVal N C a x = true) :
    wireVal N C (N + k) x = true := by
  rw [wireVal_gate hRB k hk x, hor]
  change ((gateAt C k).inputs.map fun i => wireVal N C i x).any id = true
  rw [List.any_eq_true]
  exact ⟨true, List.mem_map.mpr ⟨a, ha, hva⟩, rfl⟩

lemma wireVal_and_pair {N : ℕ} {C : Circuit} (hRB : ReadsBack N C)
    {k a b : ℕ} (hk : k < C.gates.length) (hand : (gateAt C k).op = GateOp.and)
    (hin : (gateAt C k).inputs = [a, b]) (x : Fin N → Bool) :
    wireVal N C (N + k) x = (wireVal N C a x && wireVal N C b x) := by
  rw [wireVal_gate hRB k hk x, hand, hin]
  change [wireVal N C a x, wireVal N C b x].all id = (wireVal N C a x && wireVal N C b x)
  simp

lemma orPath_sound {N : ℕ} {C : Circuit} (hRB : ReadsBack N C)
    {w t : ℕ} (hp : OrPath N C w t) (x : Fin N → Bool)
    (ht : wireVal N C t x = true) : wireVal N C w x = true := by
  apply hp (fun u => wireVal N C u x = true) ht
  intro k hk hor a ha hva
  exact wireVal_or_mem hRB hk hor ha x hva

lemma isAO2_gate_inputs {N : ℕ} {C : Circuit} (hAO2 : IsAO2 N C)
    {k : ℕ} (hk : k < C.gates.length) :
    ∃ a b : ℕ, (gateAt C k).inputs = [a, b] ∧ a < N + k ∧ b < N + k := by
  have hmem : gateAt C k ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hlen := hAO2.2.2 (gateAt C k) hmem
  cases hin : (gateAt C k).inputs with
  | nil => rw [hin] at hlen; simp at hlen
  | cons a t1 =>
    cases t1 with
    | nil => rw [hin] at hlen; simp at hlen
    | cons b t2 =>
      cases t2 with
      | nil =>
        have ha := hAO2.2.1 k hk a (by rw [hin]; exact List.mem_cons_self)
        have hb := hAO2.2.1 k hk b (by rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        exact ⟨a, b, rfl, ha, hb⟩
      | cons _ _ => rw [hin] at hlen; simp at hlen

lemma isAO2_gate_op {N : ℕ} {C : Circuit} (hAO2 : IsAO2 N C)
    {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  have hmem : gateAt C k ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  exact hAO2.1 (gateAt C k) hmem

lemma mem_foldl_insertNew (B : List (List ℕ)) :
    ∀ (acc : List (List ℕ)) (v : List ℕ),
      v ∈ B.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ B := by
  induction B with
  | nil => intro acc v; simp
  | cons u rest ih =>
    intro acc v
    simp only [List.foldl_cons, ih, insertNew, List.mem_cons]
    by_cases hu : u ∈ acc
    · simp only [hu, ↓reduceIte]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hu
        · exact Or.inr h
    · simp only [hu, ↓reduceIte, List.mem_append, List.mem_singleton]
      tauto

lemma mem_andStep (k : ℕ) (A B : List (List ℕ)) (w : List ℕ) :
    w ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, w = capAdd k u v := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩

lemma setList_pair {m n : ℕ} (p : Fin m) (l : Fin n) :
    setList ({Fin.castAdd n p, Fin.natAdd m l} : Finset (Fin (m + n))) = [p.val, m + l.val] := by
  unfold setList
  let S : Finset (Fin (m + n)) := {Fin.castAdd n p, Fin.natAdd m l}
  let L : List ℕ := ((List.finRange (m + n)).filter fun i => decide (i ∈ S)).map Fin.val
  have hmem : ∀ k : ℕ, k ∈ L ↔ k = p.val ∨ k = m + l.val := by
    intro k
    simp only [L, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      S, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl | rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨Fin.castAdd n p, Or.inl rfl, rfl⟩
      · exact ⟨Fin.natAdd m l, Or.inr rfl, rfl⟩
  have hpw_fin : (List.finRange (m + n)).Pairwise (fun a b : Fin (m + n) => a.val < b.val) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_finRange]
    exact hij
  have hpw : L.Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.Pairwise.filter _ hpw_fin
  have hlt : p.val < m + l.val := by omega
  cases hL : L with
  | nil =>
    have := (hmem p.val).mpr (Or.inl rfl)
    rw [hL] at this; cases this
  | cons x t1 =>
    cases t1 with
    | nil =>
      have hp := (hmem p.val).mpr (Or.inl rfl)
      have hl := (hmem (m + l.val)).mpr (Or.inr rfl)
      rw [hL] at hp hl
      simp only [List.mem_singleton] at hp hl
      omega
    | cons y t2 =>
      rw [hL] at hpw
      have hxy : x < y := (List.pairwise_cons.mp hpw).1 y List.mem_cons_self
      have hx : x = p.val ∨ x = m + l.val := (hmem x).mp (by rw [hL]; exact List.mem_cons_self)
      have hy : y = p.val ∨ y = m + l.val := (hmem y).mp (by rw [hL]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have hx_eq : x = p.val := by omega
      have hy_eq : y = m + l.val := by omega
      cases t2 with
      | nil => change L = [p.val, m + l.val]; rw [hL, hx_eq, hy_eq]
      | cons z t3 =>
        have hyz : y < z := (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).1 z List.mem_cons_self
        have hz : z = p.val ∨ z = m + l.val := (hmem z).mp (by
          rw [hL]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        omega

lemma readVectors_pair_inv {m n : ℕ} {C : Circuit} (hAO2 : IsAO2 (m + n) C)
    (p : Fin m) (l : Fin n) :
    let R := readVectors C (m + n) [p.val, m + l.val] 1
    R.length = m + n + C.gates.length ∧
    ∀ w < R.length, ∀ v ∈ R.getD w [],
      (∃ c0 c1 : ℕ, v = [c0, c1] ∧ 1 ≤ c0 + c1) ∧
      (v = [1, 0] → OrPath (m + n) C w p.val) ∧
      (v = [0, 1] → OrPath (m + n) C w (m + l.val)) ∧
      (v = [1, 1] → ∃ j : Fin C.gates.length, (gateAt C j.val).op = GateOp.and ∧
        OrPath (m + n) C w (m + n + j.val) ∧
        ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
          ((OrPath (m + n) C a p.val ∧ OrPath (m + n) C b (m + l.val)) ∨
           (OrPath (m + n) C a (m + l.val) ∧ OrPath (m + n) C b p.val))) := by
  let S : List ℕ := [p.val, m + l.val]
  let rvStep : List (List (List ℕ)) → Gate → List (List (List ℕ)) := fun R g =>
    let ins := g.inputs.map fun i => R.getD i []
    R ++ [match g.op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep 1) [S.map fun _ => 0]
      | _ => []]
  let R0 : List (List (List ℕ)) := (List.range (m + n)).map (leafVectors S 1)
  have hplt : p.val < m + l.val := by omega
  have hinv_prefix : ∀ k ≤ C.gates.length,
      let Rk := (C.gates.take k).foldl rvStep R0
      Rk.length = m + n + k ∧
      ∀ w < Rk.length, ∀ v ∈ Rk.getD w [],
        (∃ c0 c1 : ℕ, v = [c0, c1] ∧ 1 ≤ c0 + c1) ∧
        (v = [1, 0] → OrPath (m + n) C w p.val) ∧
        (v = [0, 1] → OrPath (m + n) C w (m + l.val)) ∧
        (v = [1, 1] → ∃ j : Fin C.gates.length, (gateAt C j.val).op = GateOp.and ∧
          OrPath (m + n) C w (m + n + j.val) ∧
          ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
            ((OrPath (m + n) C a p.val ∧ OrPath (m + n) C b (m + l.val)) ∨
             (OrPath (m + n) C a (m + l.val) ∧ OrPath (m + n) C b p.val))) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hlen0 : R0.length = m + n := by simp [R0]
      refine ⟨by simpa [List.take_zero] using hlen0, ?_⟩
      intro w hw v hv
      simp only [List.take_zero, List.foldl_nil] at hw hv
      have hwlt : w < m + n := by omega
      have hget : R0.getD w [] = leafVectors S 1 w := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [R0]
      rw [hget] at hv
      unfold leafVectors at hv
      by_cases hwin : w ∈ S
      · simp only [hwin, ↓reduceIte, List.mem_singleton] at hv
        simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hwin
        rcases hwin with rfl | rfl
        · have hv10 : v = [1, 0] := by
            rw [hv]; simp [S, Nat.ne_of_gt hplt]
          rw [hv10]
          exact ⟨⟨1, 0, rfl, by omega⟩, fun _ => orPath_refl _ _ _,
            fun h => (by cases h), fun h => (by cases h)⟩
        · have hv01 : v = [0, 1] := by
            rw [hv]; simp [S, Nat.ne_of_lt hplt]
          rw [hv01]
          exact ⟨⟨0, 1, rfl, by omega⟩, fun h => (by cases h),
            fun _ => orPath_refl _ _ _, fun h => (by cases h)⟩
      · simp only [hwin, ↓reduceIte, List.not_mem_nil] at hv
    | succ k ih =>
      intro hk_le
      have hk : k < C.gates.length := by omega
      obtain ⟨hlen_k, hinv_k⟩ := ih (by omega)
      let Rk := (C.gates.take k).foldl rvStep R0
      change Rk.length = m + n + k at hlen_k
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [gateAt C k] := by
        rw [List.take_succ_eq_append_getElem hk]
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hk]
      have hRk1 : (C.gates.take (k + 1)).foldl rvStep R0 = rvStep Rk (gateAt C k) := by
        rw [htake, List.foldl_append]; rfl
      have hlen1 : (rvStep Rk (gateAt C k)).length = m + n + (k + 1) := by
        simp only [rvStep, List.length_append, List.length_cons, List.length_nil]
        change Rk.length + 1 = m + n + (k + 1)
        omega
      rw [hRk1]
      refine ⟨hlen1, ?_⟩
      intro w hw v hv
      by_cases hw_old : w < Rk.length
      · have hget : (rvStep Rk (gateAt C k)).getD w [] = Rk.getD w [] :=
          List.getD_append _ _ _ _ hw_old
        rw [hget] at hv
        exact hinv_k w hw_old v hv
      · have hweq : w = m + n + k := by omega
        subst hweq
        have hget : (rvStep Rk (gateAt C k)).getD (m + n + k) [] =
            (match (gateAt C k).op with
              | GateOp.or => ((gateAt C k).inputs.map fun i => Rk.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
              | GateOp.and => ((gateAt C k).inputs.map fun i => Rk.getD i []).foldl (andStep 1) [S.map fun _ => 0]
              | _ => []) := by
          have hl : m + n + k = Rk.length := hlen_k.symm
          dsimp only [rvStep]
          rw [hl, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
          simp
        rw [hget] at hv
        obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := isAO2_gate_inputs hAO2 hk
        have ha_rk : a < Rk.length := by omega
        have hb_rk : b < Rk.length := by omega
        rcases isAO2_gate_op hAO2 hk with hand | hor
        · rw [hand, hab] at hv
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hv
          rw [mem_andStep] at hv
          obtain ⟨u1', hu1', u2, hu2, rfl⟩ := hv
          rw [mem_andStep] at hu1'
          obtain ⟨z0, hz0, u1, hu1, rfl⟩ := hu1'
          simp only [List.mem_singleton] at hz0
          subst hz0
          have hi1 := hinv_k a ha_rk u1 hu1
          have hi2 := hinv_k b hb_rk u2 hu2
          obtain ⟨x1, y1, hu1_eq, hsum1⟩ := hi1.1
          obtain ⟨x2, y2, hu2_eq, hsum2⟩ := hi2.1
          have hcap : capAdd 1 (capAdd 1 (S.map fun _ => 0) u1) u2 =
              [min (min x1 2 + x2) 2, min (min y1 2 + y2) 2] := by
            rw [hu1_eq, hu2_eq]
            simp [S, capAdd]
          rw [hcap]
          refine ⟨⟨min (min x1 2 + x2) 2, min (min y1 2 + y2) 2, rfl, by omega⟩, ?_, ?_, ?_⟩
          · intro h10
            have h0 := congrArg (fun l => l.getD 0 0) h10
            have h1 := congrArg (fun l => l.getD 1 0) h10
            simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
            omega
          · intro h01
            have h0 := congrArg (fun l => l.getD 0 0) h01
            have h1 := congrArg (fun l => l.getD 1 0) h01
            simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
            omega
          · intro h11
            have h0 := congrArg (fun l => l.getD 0 0) h11
            have h1 := congrArg (fun l => l.getD 1 0) h11
            simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
            refine ⟨⟨k, hk⟩, hand, orPath_refl _ _ _, a, b, hab, ?_⟩
            by_cases hx1 : x1 = 0
            · have hy1 : y1 = 1 := by omega
              have hx2 : x2 = 1 := by omega
              have hy2 : y2 = 0 := by omega
              rw [hx1, hy1] at hu1_eq
              rw [hx2, hy2] at hu2_eq
              exact Or.inr ⟨hi1.2.2.1 hu1_eq, hi2.2.1 hu2_eq⟩
            · have hx1' : x1 = 1 := by omega
              have hx2 : x2 = 0 := by omega
              have hy2 : y2 = 1 := by omega
              have hy1 : y1 = 0 := by omega
              rw [hx1', hy1] at hu1_eq
              rw [hx2, hy2] at hu2_eq
              exact Or.inl ⟨hi1.2.1 hu1_eq, hi2.2.2.1 hu2_eq⟩
        · rw [hor, hab] at hv
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at hv
          rw [mem_foldl_insertNew, mem_foldl_insertNew] at hv
          simp only [List.not_mem_nil, false_or] at hv
          have ha_mem : a ∈ (gateAt C k).inputs := by rw [hab]; exact List.mem_cons_self
          have hb_mem : b ∈ (gateAt C k).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
          rcases hv with hva | hvb
          · have hia := hinv_k a ha_rk v hva
            refine ⟨hia.1,
              fun h => orPath_step hk hor ha_mem (hia.2.1 h),
              fun h => orPath_step hk hor ha_mem (hia.2.2.1 h),
              fun h => ?_⟩
            obtain ⟨j, hjand, hjp, a', b', hab', hlr⟩ := hia.2.2.2 h
            exact ⟨j, hjand, orPath_step hk hor ha_mem hjp, a', b', hab', hlr⟩
          · have hib := hinv_k b hb_rk v hvb
            refine ⟨hib.1,
              fun h => orPath_step hk hor hb_mem (hib.2.1 h),
              fun h => orPath_step hk hor hb_mem (hib.2.2.1 h),
              fun h => ?_⟩
            obtain ⟨j, hjand, hjp, a', b', hab', hlr⟩ := hib.2.2.2 h
            exact ⟨j, hjand, orPath_step hk hor hb_mem hjp, a', b', hab', hlr⟩
  have hfull := hinv_prefix C.gates.length (Nat.le_refl _)
  rw [List.take_length] at hfull
  exact hfull

def mergeStep {α : Type*} [DecidableEq α] (P : Finset (Finset α)) (u v : α) : Finset (Finset α) :=
  let hit := P.filter (fun B => u ∈ B ∨ v ∈ B)
  let rest := P.filter (fun B => ¬ (u ∈ B ∨ v ∈ B))
  if hit.Nonempty then insert (hit.biUnion id) rest else P

def IsPartition {α : Type*} [DecidableEq α] (U : Finset α) (P : Finset (Finset α)) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
  (∀ B1 ∈ P, ∀ B2 ∈ P, B1 ≠ B2 → Disjoint B1 B2) ∧
  P.biUnion id = U

lemma partition_unique_block {α : Type*} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPartition U P) {x : α} {B1 B2 : Finset α}
    (h1 : B1 ∈ P) (h2 : B2 ∈ P) (hx1 : x ∈ B1) (hx2 : x ∈ B2) : B1 = B2 := by
  by_contra hne
  exact Finset.disjoint_left.mp (hP.2.1 B1 h1 B2 h2 hne) hx1 hx2

lemma partition_exists_block {α : Type*} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPartition U P) {x : α} (hx : x ∈ U) : ∃ B ∈ P, x ∈ B := by
  rw [← hP.2.2, Finset.mem_biUnion] at hx
  obtain ⟨B, hB, hxB⟩ := hx
  exact ⟨B, hB, hxB⟩

lemma mergeStep_props {α : Type*} [DecidableEq α] {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPartition U P) {u v : α} (hu : u ∈ U) (hv : v ∈ U) :
    IsPartition U (mergeStep P u v) ∧
    P.card ≤ (mergeStep P u v).card + 1 ∧
    (∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ mergeStep P u v, x ∈ B ∧ y ∈ B) ∧
    (∃ B ∈ mergeStep P u v, u ∈ B ∧ v ∈ B) := by
  obtain ⟨Bu, hBuP, huBu⟩ := partition_exists_block hP hu
  obtain ⟨Bv, hBvP, hvBv⟩ := partition_exists_block hP hv
  let hit := P.filter (fun B => u ∈ B ∨ v ∈ B)
  let rest := P.filter (fun B => ¬ (u ∈ B ∨ v ∈ B))
  have hBu_hit : Bu ∈ hit := Finset.mem_filter.mpr ⟨hBuP, Or.inl huBu⟩
  have hBv_hit : Bv ∈ hit := Finset.mem_filter.mpr ⟨hBvP, Or.inr hvBv⟩
  have hhit_ne : hit.Nonempty := ⟨Bu, hBu_hit⟩
  have hhit_sub : hit ⊆ {Bu, Bv} := by
    intro B hB
    obtain ⟨hBP, hor⟩ := Finset.mem_filter.mp hB
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hor with huB | hvB
    · exact Or.inl (partition_unique_block hP hBP hBuP huB huBu)
    · exact Or.inr (partition_unique_block hP hBP hBvP hvB hvBv)
  have hhit_card : hit.card ≤ 2 :=
    (Finset.card_le_card hhit_sub).trans Finset.card_le_two
  have hmerge_eq : mergeStep P u v = insert (hit.biUnion id) rest := by
    unfold mergeStep
    simp only [hit, rest, hhit_ne, ↓reduceIte]
  have hnot_mem_rest : hit.biUnion id ∉ rest := by
    intro hmem
    have hno := (Finset.mem_filter.mp hmem).2
    apply hno
    exact Or.inl (Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩)
  have hdisj_hr : Disjoint hit rest := by
    rw [Finset.disjoint_left]
    intro B h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hunion_hr : hit ∪ rest = P := by
    ext B
    simp only [hit, rest, Finset.mem_union, Finset.mem_filter]
    tauto
  have hpart : IsPartition U (mergeStep P u v) := by
    rw [hmerge_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hBr
      · exact ⟨u, Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩⟩
      · exact hP.1 B (Finset.mem_filter.mp hBr).1
    · intro B1 h1 B2 h2 hne
      rcases Finset.mem_insert.mp h1 with rfl | h1r <;>
        rcases Finset.mem_insert.mp h2 with rfl | h2r
      · exact (hne rfl).elim
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨B', hB'h, hxB'⟩ := Finset.mem_biUnion.mp hx1
        have hB'P := (Finset.mem_filter.mp hB'h).1
        have hB2P := (Finset.mem_filter.mp h2r).1
        have heq := partition_unique_block hP hB'P hB2P hxB' hx2
        subst heq
        exact (Finset.mem_filter.mp h2r).2 (Finset.mem_filter.mp hB'h).2
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨B', hB'h, hxB'⟩ := Finset.mem_biUnion.mp hx2
        have hB'P := (Finset.mem_filter.mp hB'h).1
        have hB1P := (Finset.mem_filter.mp h1r).1
        have heq := partition_unique_block hP hB'P hB1P hxB' hx1
        subst heq
        exact (Finset.mem_filter.mp h1r).2 (Finset.mem_filter.mp hB'h).2
      · exact hP.2.1 B1 (Finset.mem_filter.mp h1r).1 B2 (Finset.mem_filter.mp h2r).1 hne
    · rw [Finset.biUnion_insert]
      change hit.biUnion id ∪ rest.biUnion id = U
      ext x
      rw [← hP.2.2, ← hunion_hr]
      simp only [Finset.mem_union, Finset.mem_biUnion, id]
      constructor
      · rintro (⟨B, hB, hx⟩ | ⟨B, hB, hx⟩)
        · exact ⟨B, Or.inl hB, hx⟩
        · exact ⟨B, Or.inr hB, hx⟩
      · rintro ⟨B, hB | hB, hx⟩
        · exact Or.inl ⟨B, hB, hx⟩
        · exact Or.inr ⟨B, hB, hx⟩
  have hcard : P.card ≤ (mergeStep P u v).card + 1 := by
    rw [hmerge_eq, Finset.card_insert_of_notMem hnot_mem_rest, ← hunion_hr,
      Finset.card_union_of_disjoint hdisj_hr]
    omega
  have hmono : ∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ mergeStep P u v, x ∈ B ∧ y ∈ B := by
    rintro x y ⟨B, hBP, hxB, hyB⟩
    rw [hmerge_eq]
    by_cases hhit : u ∈ B ∨ v ∈ B
    · refine ⟨hit.biUnion id, Finset.mem_insert_self _ _, ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_filter.mpr ⟨hBP, hhit⟩, hxB⟩
      · exact Finset.mem_biUnion.mpr ⟨B, Finset.mem_filter.mpr ⟨hBP, hhit⟩, hyB⟩
    · exact ⟨B, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hBP, hhit⟩), hxB, hyB⟩
  have hpair : ∃ B ∈ mergeStep P u v, u ∈ B ∧ v ∈ B := by
    rw [hmerge_eq]
    exact ⟨hit.biUnion id, Finset.mem_insert_self _ _,
      Finset.mem_biUnion.mpr ⟨Bu, hBu_hit, huBu⟩,
      Finset.mem_biUnion.mpr ⟨Bv, hBv_hit, hvBv⟩⟩
  exact ⟨hpart, hcard, hmono, hpair⟩

lemma mergeFold_props {α : Type*} [DecidableEq α] (U : Finset α) (pairs : List (α × α)) :
    ∀ (P : Finset (Finset α)),
      IsPartition U P →
      (∀ pr ∈ pairs, pr.1 ∈ U ∧ pr.2 ∈ U) →
      let Q := pairs.foldl (fun acc pr => mergeStep acc pr.1 pr.2) P
      IsPartition U Q ∧
      P.card ≤ pairs.length + Q.card ∧
      (∀ x y : α, (∃ B ∈ P, x ∈ B ∧ y ∈ B) → ∃ B ∈ Q, x ∈ B ∧ y ∈ B) ∧
      (∀ pr ∈ pairs, ∃ B ∈ Q, pr.1 ∈ B ∧ pr.2 ∈ B) := by
  induction pairs with
  | nil =>
    intro P hP _
    exact ⟨hP, by simp, fun _ _ h => h, fun _ h => by cases h⟩
  | cons pr rest ih =>
    intro P hP hmem
    have hpr := hmem pr List.mem_cons_self
    have hrest : ∀ pr' ∈ rest, pr'.1 ∈ U ∧ pr'.2 ∈ U :=
      fun pr' h' => hmem pr' (List.mem_cons_of_mem _ h')
    obtain ⟨hP1, hcard1, hmono1, hpair1⟩ := mergeStep_props hP hpr.1 hpr.2
    obtain ⟨hQ, hcard2, hmono2, hpair2⟩ := ih (mergeStep P pr.1 pr.2) hP1 hrest
    refine ⟨hQ, by simp only [List.foldl_cons, List.length_cons]; omega,
      fun x y hxy => hmono2 x y (hmono1 x y hxy), ?_⟩
    intro pr' hpr'
    rcases List.mem_cons.mp hpr' with rfl | hrest'
    · exact hmono2 pr'.1 pr'.2 hpair1
    · exact hpair2 pr' hrest'

open Classical in
lemma side_component_bound {N : ℕ} {C : Circuit} (hAO2 : IsAO2 N C)
    {X : Type*} [Fintype X] [DecidableEq X]
    (wireOf : X → ℕ) (hwire_lt : ∀ x : X, wireOf x < N)
    (hwire_inj : Function.Injective wireOf)
    (S_gates : Finset (Fin C.gates.length))
    (opWire : Fin C.gates.length → ℕ)
    (hnonempty : ∀ j ∈ S_gates, ∃ x : X, OrPath N C (opWire j) (wireOf x)) :
    let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath N C w (wireOf x))
    let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
    let O_S : Finset (Fin C.gates.length) :=
      Finset.univ.filter (fun o =>
        (gateAt C o.val).op = GateOp.or ∧
        2 ≤ (reach (N + o.val)).card ∧
        ∃ j ∈ S_gates, OrPath N C (opWire j) (N + o.val))
    E_S.card ≤ O_S.card + S_gates.card := by
  classical
  let reach (w : ℕ) : Finset X := Finset.univ.filter (fun x => OrPath N C w (wireOf x))
  let E_S : Finset X := S_gates.biUnion (fun j => reach (opWire j))
  let O_S : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun o =>
      (gateAt C o.val).op = GateOp.or ∧
      2 ≤ (reach (N + o.val)).card ∧
      ∃ j ∈ S_gates, OrPath N C (opWire j) (N + o.val))
  let pairOf (o : Fin C.gates.length) : Option (X × X) :=
    let a := (gateAt C o.val).inputs.getD 0 0
    let b := (gateAt C o.val).inputs.getD 1 0
    if h : (reach a).Nonempty ∧ (reach b).Nonempty then some (h.1.choose, h.2.choose) else none
  let pairs : List (X × X) := O_S.toList.filterMap pairOf
  have hpairs_len : pairs.length ≤ O_S.card := by
    have h1 := List.length_filterMap_le pairOf O_S.toList
    rw [Finset.length_toList] at h1
    exact h1
  have hpairs_in : ∀ pr ∈ pairs, pr.1 ∈ E_S ∧ pr.2 ∈ E_S := by
    intro pr hpr
    obtain ⟨o, ho_list, hpair_eq⟩ := List.mem_filterMap.mp hpr
    have ho : o ∈ O_S := Finset.mem_toList.mp ho_list
    obtain ⟨hor, _, j, hjS, hjo⟩ := (Finset.mem_filter.mp ho).2
    obtain ⟨a, b, hab, _, _⟩ := isAO2_gate_inputs hAO2 o.isLt
    have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
    have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
    dsimp only [pairOf] at hpair_eq
    rw [ha_get, hb_get] at hpair_eq
    split_ifs at hpair_eq with hne
    injection hpair_eq with hpr_eq
    rw [← hpr_eq]
    have hu : hne.1.choose ∈ reach a := hne.1.choose_spec
    have hv : hne.2.choose ∈ reach b := hne.2.choose_spec
    have hua : OrPath N C a (wireOf hne.1.choose) := (Finset.mem_filter.mp hu).2
    have hvb : OrPath N C b (wireOf hne.2.choose) := (Finset.mem_filter.mp hv).2
    have ha_mem : a ∈ (gateAt C o.val).inputs := by rw [hab]; exact List.mem_cons_self
    have hb_mem : b ∈ (gateAt C o.val).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
    refine ⟨Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo (orPath_step o.isLt hor ha_mem hua)⟩⟩,
      Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orPath_trans hjo (orPath_step o.isLt hor hb_mem hvb)⟩⟩⟩
  let P0 : Finset (Finset X) := E_S.image (fun x => {x})
  have hP0_part : IsPartition E_S P0 := by
    refine ⟨?_, ?_, ?_⟩
    · intro B hB
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hB
      exact ⟨x, Finset.mem_singleton_self x⟩
    · intro B1 h1 B2 h2 hne
      obtain ⟨x1, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨x2, _, rfl⟩ := Finset.mem_image.mp h2
      rw [Finset.disjoint_singleton]
      intro heq; subst heq; exact hne rfl
    · ext x
      simp only [P0, Finset.mem_biUnion, Finset.mem_image, id]
      constructor
      · rintro ⟨B, ⟨y, hy, rfl⟩, hx⟩
        rw [Finset.mem_singleton.mp hx]; exact hy
      · intro hx
        exact ⟨{x}, ⟨x, hx, rfl⟩, Finset.mem_singleton_self x⟩
  have hP0_card : P0.card = E_S.card := by
    rw [Finset.card_image_of_injective _ (fun a b h => Finset.singleton_injective h)]
  let Q := pairs.foldl (fun acc pr => mergeStep acc pr.1 pr.2) P0
  obtain ⟨hQ_part, hQ_card, _, hQ_pairs⟩ := mergeFold_props E_S pairs P0 hP0_part hpairs_in
  have hsame_wire : ∀ w : ℕ, (∃ j ∈ S_gates, OrPath N C (opWire j) w) →
      ∀ x1 ∈ reach w, ∀ x2 ∈ reach w, ∃ B ∈ Q, x1 ∈ B ∧ x2 ∈ B := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      rintro ⟨j, hjS, hjw⟩ x1 hx1 x2 hx2
      have hp1 : OrPath N C w (wireOf x1) := (Finset.mem_filter.mp hx1).2
      have hp2 : OrPath N C w (wireOf x2) := (Finset.mem_filter.mp hx2).2
      by_cases h12 : x1 = x2
      · subst h12
        have hx1E : x1 ∈ E_S := Finset.mem_biUnion.mpr ⟨j, hjS,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, orPath_trans hjw hp1⟩⟩
        obtain ⟨B, hBQ, hxB⟩ := partition_exists_block hQ_part hx1E
        exact ⟨B, hBQ, hxB, hxB⟩
      · have hne_w : wireOf x1 ≠ wireOf x2 := fun h => h12 (hwire_inj h)
        have hstep_ex : ∃ k < C.gates.length, w = N + k ∧ (gateAt C k).op = GateOp.or := by
          rcases orPath_cases hp1 with rfl | ⟨k, hk, hwk, hor, _⟩
          · rcases orPath_cases hp2 with h2 | ⟨k, hk, hwk, hor, _⟩
            · exact (hne_w h2).elim
            · exact ⟨k, hk, hwk, hor⟩
          · exact ⟨k, hk, hwk, hor⟩
        obtain ⟨k, hk, hwk, hor⟩ := hstep_ex
        let o : Fin C.gates.length := ⟨k, hk⟩
        have h2card : 2 ≤ (reach (N + o.val)).card := by
          rw [← hwk]
          exact Finset.one_lt_card.mpr ⟨x1, hx1, x2, hx2, h12⟩
        have ho_mem : o ∈ O_S :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hor, h2card, j, hjS, hwk ▸ hjw⟩
        obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := isAO2_gate_inputs hAO2 hk
        have ha_mem : a ∈ (gateAt C k).inputs := by rw [hab]; exact List.mem_cons_self
        have hb_mem : b ∈ (gateAt C k).inputs := by rw [hab]; exact List.mem_cons_of_mem _ List.mem_cons_self
        have hja : OrPath N C (opWire j) a :=
          orPath_trans hjw (hwk ▸ orPath_step hk hor ha_mem (orPath_refl N C a))
        have hjb : OrPath N C (opWire j) b :=
          orPath_trans hjw (hwk ▸ orPath_step hk hor hb_mem (orPath_refl N C b))
        have hsplit_x : ∀ x ∈ reach w, x ∈ reach a ∨ x ∈ reach b := by
          intro x hx
          have hpx : OrPath N C w (wireOf x) := (Finset.mem_filter.mp hx).2
          have hlt_x : wireOf x < N := hwire_lt x
          rcases orPath_cases hpx with hxeq | ⟨k', _, hwk', _, c, hc, hpc⟩
          · omega
          · have hkeq : k' = k := by omega
            subst hkeq
            rw [hab] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩)
            · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpc⟩)
        rcases hsplit_x x1 hx1 with h1a | h1b <;> rcases hsplit_x x2 hx2 with h2a | h2b
        · exact ih a (by omega) ⟨j, hjS, hja⟩ x1 h1a x2 h2a
        · have hne_ab : (reach a).Nonempty ∧ (reach b).Nonempty := ⟨⟨x1, h1a⟩, ⟨x2, h2b⟩⟩
          have hpair_in : (hne_ab.1.choose, hne_ab.2.choose) ∈ pairs := by
            apply List.mem_filterMap.mpr
            refine ⟨o, Finset.mem_toList.mpr ho_mem, ?_⟩
            dsimp only [pairOf]
            have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
            have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
            rw [ha_get, hb_get]; split_ifs; rfl
          obtain ⟨B1, hB1Q, hx1B1, huB1⟩ := ih a (by omega) ⟨j, hjS, hja⟩ x1 h1a hne_ab.1.choose hne_ab.1.choose_spec
          obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
          obtain ⟨B3, hB3Q, hvB3, hx2B3⟩ := ih b (by omega) ⟨j, hjS, hjb⟩ hne_ab.2.choose hne_ab.2.choose_spec x2 h2b
          have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
          have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
          subst h12B; subst h23B
          exact ⟨B1, hB1Q, hx1B1, hx2B3⟩
        · have hne_ab : (reach a).Nonempty ∧ (reach b).Nonempty := ⟨⟨x2, h2a⟩, ⟨x1, h1b⟩⟩
          have hpair_in : (hne_ab.1.choose, hne_ab.2.choose) ∈ pairs := by
            apply List.mem_filterMap.mpr
            refine ⟨o, Finset.mem_toList.mpr ho_mem, ?_⟩
            dsimp only [pairOf]
            have ha_get : (gateAt C o.val).inputs.getD 0 0 = a := by rw [hab]; rfl
            have hb_get : (gateAt C o.val).inputs.getD 1 0 = b := by rw [hab]; rfl
            rw [ha_get, hb_get]; split_ifs; rfl
          obtain ⟨B1, hB1Q, hx2B1, huB1⟩ := ih a (by omega) ⟨j, hjS, hja⟩ x2 h2a hne_ab.1.choose hne_ab.1.choose_spec
          obtain ⟨B2, hB2Q, huB2, hvB2⟩ := hQ_pairs _ hpair_in
          obtain ⟨B3, hB3Q, hvB3, hx1B3⟩ := ih b (by omega) ⟨j, hjS, hjb⟩ hne_ab.2.choose hne_ab.2.choose_spec x1 h1b
          have h12B := partition_unique_block hQ_part hB1Q hB2Q huB1 huB2
          have h23B := partition_unique_block hQ_part hB2Q hB3Q hvB2 hvB3
          subst h12B; subst h23B
          exact ⟨B1, hB1Q, hx1B3, hx2B1⟩
        · exact ih b (by omega) ⟨j, hjS, hjb⟩ x1 h1b x2 h2b
  let blk (j : Fin C.gates.length) : Finset X :=
    if hj : j ∈ S_gates then
      have hx : (hnonempty j hj).choose ∈ E_S :=
        Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnonempty j hj).choose_spec⟩⟩
      (partition_exists_block hQ_part hx).choose
    else ∅
  have hQ_sub : Q ⊆ S_gates.image blk := by
    intro B hBQ
    obtain ⟨x, hxB⟩ := hQ_part.1 B hBQ
    have hxE : x ∈ E_S := by
      rw [← hQ_part.2.2]
      exact Finset.mem_biUnion.mpr ⟨B, hBQ, hxB⟩
    obtain ⟨j, hjS, hxj⟩ := Finset.mem_biUnion.mp hxE
    refine Finset.mem_image.mpr ⟨j, hjS, ?_⟩
    let x0 := (hnonempty j hjS).choose
    have hx0j : x0 ∈ reach (opWire j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnonempty j hjS).choose_spec⟩
    obtain ⟨B', hB'Q, hxB', hx0B'⟩ := hsame_wire (opWire j) ⟨j, hjS, orPath_refl N C _⟩ x hxj x0 hx0j
    have hBB' := partition_unique_block hQ_part hBQ hB'Q hxB hxB'
    have hblk_spec : blk j ∈ Q ∧ x0 ∈ blk j := by
      dsimp only [blk]
      simp only [hjS, ↓reduceDIte]
      have hx0E : x0 ∈ E_S := Finset.mem_biUnion.mpr ⟨j, hjS, hx0j⟩
      exact (partition_exists_block hQ_part hx0E).choose_spec
    have hB'blk := partition_unique_block hQ_part hB'Q hblk_spec.1 hx0B' hblk_spec.2
    exact (hBB'.trans hB'blk).symm
  have hQ_le_S : Q.card ≤ S_gates.card :=
    (Finset.card_le_card hQ_sub).trans Finset.card_image_le
  change P0.card ≤ pairs.length + Q.card at hQ_card
  change E_S.card ≤ O_S.card + S_gates.card
  omega

end PEqualNP.Outside.L_meta_4897

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_4897 :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → PEqualNP.ReadK.IsReadK (x1 + x2) x4 (1 : ℕ) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro m n E C hNoC4 hAO2 hComp hRead1
  by_cases hEempty : E = ∅
  · subst hEempty
    exact ⟨∅, ∅, fun _ h => (by cases h), by simp⟩
  let N := m + n
  have hRB : ReadsBack N C := hAO2.2.1
  let pts (w : ℕ) : Finset (Fin m) :=
    Finset.univ.filter (fun p => PEqualNP.Outside.L_meta_4897.OrPath N C w p.val)
  let lns (w : ℕ) : Finset (Fin n) :=
    Finset.univ.filter (fun l => PEqualNP.Outside.L_meta_4897.OrPath N C w (m + l.val))
  have hComp_wire (x : Fin N → Bool) :
      wireVal N C C.output x =
        decide (∃ (p : Fin m) (l : Fin n), (p, l) ∈ E ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd m l) = true) :=
    hComp x
  have hno_pts_only (x : Fin N → Bool) (h0 : ∀ l : Fin n, x (Fin.natAdd m l) = false) :
      wireVal N C C.output x = false := by
    rw [hComp_wire, decide_eq_false_iff_not]
    rintro ⟨p, l, _, _, hl⟩
    rw [h0 l] at hl; cases hl
  have hno_lns_only (x : Fin N → Bool) (h0 : ∀ p : Fin m, x (Fin.castAdd n p) = false) :
      wireVal N C C.output x = false := by
    rw [hComp_wire, decide_eq_false_iff_not]
    rintro ⟨p, l, _, hp, _⟩
    rw [h0 p] at hp; cases hp
  have hedge_covered : ∀ p : Fin m, ∀ l : Fin n, (p, l) ∈ E →
      ∃ j : Fin C.gates.length, (gateAt C j.val).op = GateOp.and ∧
        PEqualNP.Outside.L_meta_4897.OrPath N C C.output (N + j.val) ∧
        ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
          ((PEqualNP.Outside.L_meta_4897.OrPath N C a p.val ∧ PEqualNP.Outside.L_meta_4897.OrPath N C b (m + l.val)) ∨
           (PEqualNP.Outside.L_meta_4897.OrPath N C a (m + l.val) ∧ PEqualNP.Outside.L_meta_4897.OrPath N C b p.val)) := by
    intro p l hpl
    let S : Finset (Fin N) := {Fin.castAdd n p, Fin.natAdd m l}
    have hprime : IsPrimeImplicant N C S := by
      refine ⟨?_, ?_⟩
      · rw [hComp]
        simp only [decide_eq_true_eq, setInput, S, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨p, l, hpl, Or.inl rfl, Or.inr rfl⟩
      · intro T hT
        have hss : T ⊂ S := Finset.mem_ssubsets.mp hT
        rw [hComp, decide_eq_false_iff_not]
        rintro ⟨p', l', _, hp', hl'⟩
        simp only [setInput, decide_eq_true_eq] at hp' hl'
        have hp'S : Fin.castAdd n p' ∈ S := hss.1 hp'
        have hl'S : Fin.natAdd m l' ∈ S := hss.1 hl'
        have hne_pl : ∀ (a : Fin m) (b : Fin n), Fin.castAdd n a ≠ Fin.natAdd m b := by
          intro a b heq
          have := congrArg Fin.val heq
          simp only [Fin.val_castAdd, Fin.val_natAdd] at this
          omega
        have hp_eq : p' = p := by
          rcases Finset.mem_insert.mp hp'S with h1 | h2
          · exact Fin.ext (by simpa using congrArg Fin.val h1)
          · exact (hne_pl p' l (Finset.mem_singleton.mp h2)).elim
        have hl_eq : l' = l := by
          rcases Finset.mem_insert.mp hl'S with h1 | h2
          · exact (hne_pl p l' h1.symm).elim
          · exact Fin.ext (by have := congrArg Fin.val (Finset.mem_singleton.mp h2); simp at this; omega)
        subst hp_eq; subst hl_eq
        have hsub : S ⊆ T := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | h2
          · exact hp'
          · rw [Finset.mem_singleton.mp h2]; exact hl'
        exact hss.2 hsub
    have hrm := hRead1 S hprime
    rw [PEqualNP.Outside.L_meta_4897.setList_pair p l] at hrm
    unfold readsAtMost at hrm
    rw [List.any_eq_true] at hrm
    obtain ⟨v, hv_mem, hv_all⟩ := hrm
    obtain ⟨hRlen, hRinv⟩ := PEqualNP.Outside.L_meta_4897.readVectors_pair_inv hAO2 p l
    have hout_lt : C.output < (readVectors C N [p.val, m + l.val] 1).length := by
      by_contra hge
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hge)] at hv_mem
      cases hv_mem
    have hvi := hRinv C.output hout_lt v hv_mem
    obtain ⟨c0, c1, rfl, hsum⟩ := hvi.1
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hv_all
    have hcases : (c0 = 1 ∧ c1 = 0) ∨ (c0 = 0 ∧ c1 = 1) ∨ (c0 = 1 ∧ c1 = 1) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hop := hvi.2.1 rfl
      let x : Fin N → Bool := fun i => decide (i = Fin.castAdd n p)
      have hx_p : wireVal N C p.val x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.castAdd n p) x
        simpa [x] using this
      have hout_t := PEqualNP.Outside.L_meta_4897.orPath_sound hRB hop x hx_p
      have hout_f := hno_pts_only x (fun l' => by
        simp only [x, decide_eq_false_iff_not]
        intro heq; have := congrArg Fin.val heq; simp at this; omega)
      rw [hout_t] at hout_f; cases hout_f
    · have hop := hvi.2.2.1 rfl
      let x : Fin N → Bool := fun i => decide (i = Fin.natAdd m l)
      have hx_l : wireVal N C (m + l.val) x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.natAdd m l) x
        simpa [x] using this
      have hout_t := PEqualNP.Outside.L_meta_4897.orPath_sound hRB hop x hx_l
      have hout_f := hno_lns_only x (fun p' => by
        simp only [x, decide_eq_false_iff_not]
        intro heq; have := congrArg Fin.val heq; simp at this; omega)
      rw [hout_t] at hout_f; cases hout_f
    · exact hvi.2.2.2 rfl
  let Tstar : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j =>
      (gateAt C j.val).op = GateOp.and ∧
      PEqualNP.Outside.L_meta_4897.OrPath N C C.output (N + j.val) ∧
      ∃ p : Fin m, ∃ l : Fin n, ∃ a b : ℕ, (gateAt C j.val).inputs = [a, b] ∧
        ((PEqualNP.Outside.L_meta_4897.OrPath N C a p.val ∧ PEqualNP.Outside.L_meta_4897.OrPath N C b (m + l.val)) ∨
         (PEqualNP.Outside.L_meta_4897.OrPath N C a (m + l.val) ∧ PEqualNP.Outside.L_meta_4897.OrPath N C b p.val)))
  let pWire (j : Fin C.gates.length) : ℕ :=
    let a := (gateAt C j.val).inputs.getD 0 0
    let b := (gateAt C j.val).inputs.getD 1 0
    if (pts a).Nonempty then a else b
  let lWire (j : Fin C.gates.length) : ℕ :=
    let a := (gateAt C j.val).inputs.getD 0 0
    let b := (gateAt C j.val).inputs.getD 1 0
    if (pts a).Nonempty then b else a
  let pSide (j : Fin C.gates.length) : Finset (Fin m) := pts (pWire j)
  let lSide (j : Fin C.gates.length) : Finset (Fin n) := lns (lWire j)
  have hTstar_props : ∀ j ∈ Tstar,
      (gateAt C j.val).op = GateOp.and ∧
      PEqualNP.Outside.L_meta_4897.OrPath N C C.output (N + j.val) ∧
      (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
      lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
      (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) ∧
      ((pSide j).card = 1 ∨ (lSide j).card = 1) := by
    intro j hj
    obtain ⟨hand, htop, p0, l0, a, b, hab, hlr0⟩ := (Finset.mem_filter.mp hj).2
    have ha_get : (gateAt C j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
    have hb_get : (gateAt C j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
    have hand_sound : ∀ x : Fin N → Bool,
        wireVal N C a x = true → wireVal N C b x = true → wireVal N C C.output x = true := by
      intro x hxa hxb
      apply PEqualNP.Outside.L_meta_4897.orPath_sound hRB htop x
      rw [PEqualNP.Outside.L_meta_4897.wireVal_and_pair hRB j.isLt hand hab x, hxa, hxb]
      rfl
    have hno_both_pts : ¬ ((pts a).Nonempty ∧ (pts b).Nonempty) := by
      rintro ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩⟩
      let x : Fin N → Bool := fun i => decide (i = Fin.castAdd n p1 ∨ i = Fin.castAdd n p2)
      have h1 : wireVal N C p1.val x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.castAdd n p1) x
        simpa [x] using this
      have h2 : wireVal N C p2.val x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.castAdd n p2) x
        simpa [x] using this
      have hxa := PEqualNP.Outside.L_meta_4897.orPath_sound hRB (Finset.mem_filter.mp hp1).2 x h1
      have hxb := PEqualNP.Outside.L_meta_4897.orPath_sound hRB (Finset.mem_filter.mp hp2).2 x h2
      have ht := hand_sound x hxa hxb
      have hf := hno_pts_only x (fun l => by
        simp only [x, decide_eq_false_iff_not]
        rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
      rw [ht] at hf; cases hf
    have hno_both_lns : ¬ ((lns a).Nonempty ∧ (lns b).Nonempty) := by
      rintro ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
      let x : Fin N → Bool := fun i => decide (i = Fin.natAdd m l1 ∨ i = Fin.natAdd m l2)
      have h1 : wireVal N C (m + l1.val) x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.natAdd m l1) x
        simpa [x] using this
      have h2 : wireVal N C (m + l2.val) x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.natAdd m l2) x
        simpa [x] using this
      have hxa := PEqualNP.Outside.L_meta_4897.orPath_sound hRB (Finset.mem_filter.mp hl1).2 x h1
      have hxb := PEqualNP.Outside.L_meta_4897.orPath_sound hRB (Finset.mem_filter.mp hl2).2 x h2
      have ht := hand_sound x hxa hxb
      have hf := hno_lns_only x (fun p => by
        simp only [x, decide_eq_false_iff_not]
        rintro (h | h) <;> (have := congrArg Fin.val h; simp at this; omega))
      rw [ht] at hf; cases hf
    have hbiclique : ∀ (p : Fin m) (l : Fin n),
        ((p ∈ pts a ∧ l ∈ lns b) ∨ (p ∈ pts b ∧ l ∈ lns a)) → (p, l) ∈ E := by
      intro p l hpl
      let x : Fin N → Bool := fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd m l)
      have hxp : wireVal N C p.val x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.castAdd n p) x
        simpa [x] using this
      have hxl : wireVal N C (m + l.val) x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.natAdd m l) x
        simpa [x] using this
      have hout_t : wireVal N C C.output x = true := by
        rcases hpl with ⟨hpa, hlb⟩ | ⟨hpb, hla⟩
        · exact hand_sound x
            (PEqualNP.Outside.L_meta_4897.orPath_sound hRB (Finset.mem_filter.mp hpa).2 x hxp)
            (PEqualNP.Outside.L_meta_4897.orPath_sound hRB (Finset.mem_filter.mp hlb).2 x hxl)
        · exact hand_sound x
            (PEqualNP.Outside.L_meta_4897.orPath_sound hRB (Finset.mem_filter.mp hla).2 x hxl)
            (PEqualNP.Outside.L_meta_4897.orPath_sound hRB (Finset.mem_filter.mp hpb).2 x hxp)
      rw [hComp_wire, decide_eq_true_eq] at hout_t
      obtain ⟨p', l', hp'l', hxp', hxl'⟩ := hout_t
      simp only [x, decide_eq_true_eq] at hxp' hxl'
      have hp_eq : p' = p := by
        rcases hxp' with h1 | h2
        · exact Fin.ext (by simpa using congrArg Fin.val h1)
        · have := congrArg Fin.val h2; simp at this; omega
      have hl_eq : l' = l := by
        rcases hxl' with h1 | h2
        · have := congrArg Fin.val h1; simp at this; omega
        · exact Fin.ext (by have := congrArg Fin.val h2; simp at this; omega)
      rw [← hp_eq, ← hl_eq]; exact hp'l'
    have hsides : (pSide j).Nonempty ∧ (lSide j).Nonempty ∧
        lns (pWire j) = ∅ ∧ pts (lWire j) = ∅ ∧
        (∀ p ∈ pSide j, ∀ l ∈ lSide j, (p, l) ∈ E) := by
      rcases hlr0 with ⟨hpa, hlb⟩ | ⟨hla, hpb⟩
      · have hpa_ne : (pts a).Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩⟩
        have hlb_ne : (lns b).Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlb⟩⟩
        have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
        have hlW : lWire j = b := by dsimp only [lWire]; simp only [ha_get, hb_get, hpa_ne, ↓reduceIte]
        have hla_em : lns a = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_lns ⟨h, hlb_ne⟩)
        have hpb_em : pts b = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_pts ⟨hpa_ne, h⟩)
        refine ⟨by simpa [pSide, hpW] using hpa_ne, by simpa [lSide, hlW] using hlb_ne,
          by rw [hpW]; exact hla_em, by rw [hlW]; exact hpb_em, ?_⟩
        intro p hp l hl
        rw [show pSide j = pts a by simp [pSide, hpW]] at hp
        rw [show lSide j = lns b by simp [lSide, hlW]] at hl
        exact hbiclique p l (Or.inl ⟨hp, hl⟩)
      · have hla_ne : (lns a).Nonempty := ⟨l0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩⟩
        have hpb_ne : (pts b).Nonempty := ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩⟩
        have hpa_not : ¬ (pts a).Nonempty := fun h => hno_both_pts ⟨h, hpb_ne⟩
        have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
        have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
        have hlb_em : lns b = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hno_both_lns ⟨hla_ne, h⟩)
        have hpa_em : pts a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hpa_not
        refine ⟨by simpa [pSide, hpW] using hpb_ne, by simpa [lSide, hlW] using hla_ne,
          by rw [hpW]; exact hlb_em, by rw [hlW]; exact hpa_em, ?_⟩
        intro p hp l hl
        rw [show pSide j = pts b by simp [pSide, hpW]] at hp
        rw [show lSide j = lns a by simp [lSide, hlW]] at hl
        exact hbiclique p l (Or.inr ⟨hp, hl⟩)
    have hstar : (pSide j).card = 1 ∨ (lSide j).card = 1 := by
      have hp1 : 1 ≤ (pSide j).card := Finset.card_pos.mpr hsides.1
      have hl1 : 1 ≤ (lSide j).card := Finset.card_pos.mpr hsides.2.1
      by_contra hneither
      have hp2 : 1 < (pSide j).card := by omega
      have hl2 : 1 < (lSide j).card := by omega
      obtain ⟨p1, hp1m, p2, hp2m, hpne⟩ := Finset.one_lt_card.mp hp2
      obtain ⟨l1, hl1m, l2, hl2m, hlne⟩ := Finset.one_lt_card.mp hl2
      exact hNoC4 p1 p2 l1 l2 hpne hlne
        ⟨hsides.2.2.2.2 p1 hp1m l1 hl1m, hsides.2.2.2.2 p1 hp1m l2 hl2m,
         hsides.2.2.2.2 p2 hp2m l1 hl1m, hsides.2.2.2.2 p2 hp2m l2 hl2m⟩
    exact ⟨hand, htop, hsides.1, hsides.2.1, hsides.2.2.1, hsides.2.2.2.1, hsides.2.2.2.2, hstar⟩
  have hE_in_Tstar : ∀ p : Fin m, ∀ l : Fin n, (p, l) ∈ E →
      ∃ j ∈ Tstar, p ∈ pSide j ∧ l ∈ lSide j := by
    intro p l hpl
    obtain ⟨j, hand, htop, a, b, hab, hlr⟩ := hedge_covered p l hpl
    have hjT : j ∈ Tstar :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hand, htop, p, l, a, b, hab, hlr⟩
    have hprops := hTstar_props j hjT
    have ha_get : (gateAt C j.val).inputs.getD 0 0 = a := by rw [hab]; rfl
    have hb_get : (gateAt C j.val).inputs.getD 1 0 = b := by rw [hab]; rfl
    refine ⟨j, hjT, ?_⟩
    rcases hlr with ⟨hpa, hlb⟩ | ⟨hla, hpb⟩
    · have hpa_m : p ∈ pts a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩
      have hlb_m : l ∈ lns b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlb⟩
      have hpa_ne : (pts a).Nonempty := ⟨p, hpa_m⟩
      have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
      have hlW : lWire j = b := by dsimp only [lWire]; simp only [ha_get, hb_get, hpa_ne, ↓reduceIte]
      exact ⟨by simpa [pSide, hpW] using hpa_m, by simpa [lSide, hlW] using hlb_m⟩
    · have hla_m : l ∈ lns a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hla⟩
      have hpb_m : p ∈ pts b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩
      have hpa_not : ¬ (pts a).Nonempty := by
        intro hpa_ne
        have hpW : pWire j = a := by dsimp only [pWire]; simp only [ha_get, hpa_ne, ↓reduceIte]
        have hlem := hprops.2.2.2.2.1
        rw [hpW] at hlem
        rw [hlem] at hla_m; cases hla_m
      have hpW : pWire j = b := by dsimp only [pWire]; simp only [ha_get, hb_get, hpa_not, ↓reduceIte]
      have hlW : lWire j = a := by dsimp only [lWire]; simp only [ha_get, hpa_not, ↓reduceIte]
      exact ⟨by simpa [pSide, hpW] using hpb_m, by simpa [lSide, hlW] using hla_m⟩
  let Tpt : Finset (Fin C.gates.length) := Tstar.filter (fun j => (pSide j).card = 1)
  let Tln : Finset (Fin C.gates.length) := Tstar.filter (fun j => (pSide j).card ≠ 1)
  have hTpt_Tln_disj : Disjoint Tpt Tln := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hTpt_Tln_union : Tpt ∪ Tln = Tstar := by
    ext j; simp only [Tpt, Tln, Finset.mem_union, Finset.mem_filter]; tauto
  have hTstar_split : Tpt.card + Tln.card = Tstar.card := by
    rw [← Finset.card_union_of_disjoint hTpt_Tln_disj, hTpt_Tln_union]
  let centerP (j : Fin C.gates.length) : Fin m :=
    if h : (pSide j).Nonempty then h.choose else
      have hneE : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEempty
      hneE.choose.1
  let centerL (j : Fin C.gates.length) : Fin n :=
    if h : (lSide j).Nonempty then h.choose else
      have hneE : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEempty
      hneE.choose.2
  have hcenterP_eq : ∀ j ∈ Tpt, ∀ p ∈ pSide j, p = centerP j := by
    intro j hj p hp
    have hjT := (Finset.mem_filter.mp hj).1
    have hcard1 := (Finset.mem_filter.mp hj).2
    have hne := (hTstar_props j hjT).2.2.1
    have hmem_c : centerP j ∈ pSide j := by
      dsimp only [centerP]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
    exact Finset.card_le_one.mp (le_of_eq hcard1) p hp (centerP j) hmem_c
  have hcenterL_eq : ∀ j ∈ Tln, ∀ l ∈ lSide j, l = centerL j := by
    intro j hj l hl
    have hjT := (Finset.mem_filter.mp hj).1
    have hne1 := (Finset.mem_filter.mp hj).2
    have hprops := hTstar_props j hjT
    have hcard1 : (lSide j).card = 1 := by
      rcases hprops.2.2.2.2.2.2.2 with h | h
      · exact (hne1 h).elim
      · exact h
    have hne := hprops.2.2.2.1
    have hmem_c : centerL j ∈ lSide j := by
      dsimp only [centerL]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
    exact Finset.card_le_one.mp (le_of_eq hcard1) l hl (centerL j) hmem_c
  have hcenterP_mem : ∀ j ∈ Tpt, centerP j ∈ pSide j := by
    intro j hj
    have hne := (hTstar_props j (Finset.mem_filter.mp hj).1).2.2.1
    dsimp only [centerP]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
  have hcenterL_mem : ∀ j ∈ Tln, centerL j ∈ lSide j := by
    intro j hj
    have hne := (hTstar_props j (Finset.mem_filter.mp hj).1).2.2.2.1
    dsimp only [centerL]; simp only [hne, ↓reduceDIte]; exact hne.choose_spec
  let A : Finset (Fin m) := Tpt.image centerP
  let B : Finset (Fin n) := Tln.image centerL
  have hAB_card : A.card + B.card ≤ Tstar.card := by
    have hA : A.card ≤ Tpt.card := Finset.card_image_le
    have hB : B.card ≤ Tln.card := Finset.card_image_le
    omega
  have hcover : ∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B := by
    intro e he
    obtain ⟨j, hjT, hpj, hlj⟩ := hE_in_Tstar e.1 e.2 he
    by_cases h1 : (pSide j).card = 1
    · have hjpt : j ∈ Tpt := Finset.mem_filter.mpr ⟨hjT, h1⟩
      exact Or.inl (Finset.mem_image.mpr ⟨j, hjpt, (hcenterP_eq j hjpt e.1 hpj).symm⟩)
    · have hjln : j ∈ Tln := Finset.mem_filter.mpr ⟨hjT, h1⟩
      exact Or.inr (Finset.mem_image.mpr ⟨j, hjln, (hcenterL_eq j hjln e.2 hlj).symm⟩)
  let Otop : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun o =>
      (gateAt C o.val).op = GateOp.or ∧
      PEqualNP.Outside.L_meta_4897.OrPath N C C.output (N + o.val) ∧
      ∃ a ∈ Tstar, PEqualNP.Outside.L_meta_4897.OrPath N C (N + o.val) (N + a.val))
  have hOtop_disj_Tstar : Disjoint Otop Tstar := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have hor := (Finset.mem_filter.mp h1).2.1
    have hand := (hTstar_props j h2).1
    rw [hor] at hand; cases hand
  have hTstar_le_Otop : Tstar.card ≤ Otop.card + 1 := by
    by_cases hle1 : Tstar.card ≤ 1
    · omega
    · have hlt : 1 < Tstar.card := by omega
      obtain ⟨a1, ha1, a2, ha2, hne12⟩ := Finset.one_lt_card.mp hlt
      have hop1 := (hTstar_props a1 ha1).2.1
      have hop2 := (hTstar_props a2 ha2).2.1
      have hroot_ex : ∃ root ∈ Otop, C.output = N + root.val := by
        rcases PEqualNP.Outside.L_meta_4897.orPath_cases hop1 with heq1 | ⟨k, hk, hok, hork, _, _, _⟩
        · rcases PEqualNP.Outside.L_meta_4897.orPath_cases hop2 with heq2 | ⟨k, hk, hok, hork, _, _, _⟩
          · have : a1.val = a2.val := by omega
            exact (hne12 (Fin.ext this)).elim
          · have : k = a1.val := by omega
            subst this
            have hand1 := (hTstar_props a1 ha1).1
            rw [hork] at hand1; cases hand1
        · refine ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hork,
            hok ▸ PEqualNP.Outside.L_meta_4897.orPath_refl N C _,
            a1, ha1, hok ▸ hop1⟩, hok⟩
      obtain ⟨root, hrootO, hroot_eq⟩ := hroot_ex
      let H := Otop ∪ Tstar
      have hrootH : root ∈ H := Finset.mem_union_left _ hrootO
      have hH_card : H.card = Otop.card + Tstar.card :=
        Finset.card_union_of_disjoint hOtop_disj_Tstar
      have hpar_ex : ∀ x ∈ H.erase root,
          ∃ y ∈ Otop, N + x.val ∈ (gateAt C y.val).inputs := by
        intro x hx
        have hxne : x ≠ root := (Finset.mem_erase.mp hx).1
        have hxH : x ∈ H := (Finset.mem_erase.mp hx).2
        have hx_out : PEqualNP.Outside.L_meta_4897.OrPath N C C.output (N + x.val) := by
          rcases Finset.mem_union.mp hxH with hO | hT
          · exact (Finset.mem_filter.mp hO).2.2.1
          · exact (hTstar_props x hT).2.1
        have hx_a : ∃ a ∈ Tstar, PEqualNP.Outside.L_meta_4897.OrPath N C (N + x.val) (N + a.val) := by
          rcases Finset.mem_union.mp hxH with hO | hT
          · exact (Finset.mem_filter.mp hO).2.2.2
          · exact ⟨x, hT, PEqualNP.Outside.L_meta_4897.orPath_refl N C _⟩
        have hne_out : C.output ≠ N + x.val := by
          rw [hroot_eq]; intro h; exact hxne (Fin.ext (by omega))
        obtain ⟨y, hy, hory, hpy, hxin⟩ := PEqualNP.Outside.L_meta_4897.orPath_parent hx_out hne_out
        obtain ⟨a, haT, hxa⟩ := hx_a
        refine ⟨⟨y, hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hory, hpy,
          a, haT, PEqualNP.Outside.L_meta_4897.orPath_step hy hory hxin hxa⟩, hxin⟩
      let par (x : Fin C.gates.length) : Fin C.gates.length :=
        if hx : x ∈ H.erase root then (hpar_ex x hx).choose else root
      have hpar_mem : ∀ x ∈ H.erase root, par x ∈ Otop := by
        intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.1
      have hpar_in : ∀ x ∈ H.erase root, N + x.val ∈ (gateAt C (par x).val).inputs := by
        intro x hx; dsimp only [par]; simp only [hx, ↓reduceDIte]; exact (hpar_ex x hx).choose_spec.2
      have hfiber_le2 : ∀ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ 2 := by
        intro y _
        let F := (H.erase root).filter (fun x => par x = y)
        have hsub : F.image (fun x : Fin C.gates.length => N + x.val) ⊆ (gateAt C y.val).inputs.toFinset := by
          intro w hw
          obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨hxH, hxy⟩ := Finset.mem_filter.mp hxF
          rw [List.mem_toFinset, ← hxy]
          exact hpar_in x hxH
        have hinj : Function.Injective (fun x : Fin C.gates.length => N + x.val) := by
          intro a b h; dsimp only at h; exact Fin.ext (by omega)
        have h1 : F.card = (F.image (fun x : Fin C.gates.length => N + x.val)).card :=
          (Finset.card_image_of_injective F hinj).symm
        have h2 : (F.image (fun x : Fin C.gates.length => N + x.val)).card ≤ ((gateAt C y.val).inputs.toFinset).card :=
          Finset.card_le_card hsub
        have h3 : ((gateAt C y.val).inputs.toFinset).card ≤ (gateAt C y.val).inputs.length :=
          List.toFinset_card_le _
        have h4 : (gateAt C y.val).inputs.length = 2 := by
          obtain ⟨a, b, hab, _, _⟩ := PEqualNP.Outside.L_meta_4897.isAO2_gate_inputs hAO2 y.isLt
          rw [hab]; rfl
        change F.card ≤ 2
        omega
      have hsum_eq : (H.erase root).card = ∑ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card :=
        Finset.card_eq_sum_card_fiberwise (f := par) hpar_mem
      have hsum_le : ∑ y ∈ Otop, ((H.erase root).filter (fun x => par x = y)).card ≤ ∑ _y ∈ Otop, 2 :=
        Finset.sum_le_sum hfiber_le2
      simp only [Finset.sum_const, smul_eq_mul] at hsum_le
      have herase : (H.erase root).card + 1 = H.card := Finset.card_erase_add_one hrootH
      omega
  let Tpt_p (p : Fin m) : Finset (Fin C.gates.length) := Tpt.filter (fun j => centerP j = p)
  let E_p (p : Fin m) : Finset (Fin n) := (Tpt_p p).biUnion lSide
  let Obot_p (p : Fin m) : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun o =>
      (gateAt C o.val).op = GateOp.or ∧
      2 ≤ (lns (N + o.val)).card ∧
      ∃ j ∈ Tpt_p p, PEqualNP.Outside.L_meta_4897.OrPath N C (lWire j) (N + o.val))
  let Tln_l (l : Fin n) : Finset (Fin C.gates.length) := Tln.filter (fun j => centerL j = l)
  let E_l (l : Fin n) : Finset (Fin m) := (Tln_l l).biUnion pSide
  let Obot_l (l : Fin n) : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun o =>
      (gateAt C o.val).op = GateOp.or ∧
      2 ≤ (pts (N + o.val)).card ∧
      ∃ j ∈ Tln_l l, PEqualNP.Outside.L_meta_4897.OrPath N C (pWire j) (N + o.val))
  have hEp_bound : ∀ p ∈ A, (E_p p).card ≤ (Obot_p p).card + (Tpt_p p).card := by
    intro p _
    exact PEqualNP.Outside.L_meta_4897.side_component_bound hAO2
      (fun l : Fin n => m + l.val) (fun l => by omega)
      (fun l1 l2 h => Fin.ext (by dsimp only at h; omega))
      (Tpt_p p) lWire
      (fun j hj => by
        obtain ⟨l, hl⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.2.1
        exact ⟨l, (Finset.mem_filter.mp hl).2⟩)
  have hEl_bound : ∀ l ∈ B, (E_l l).card ≤ (Obot_l l).card + (Tln_l l).card := by
    intro l _
    exact PEqualNP.Outside.L_meta_4897.side_component_bound hAO2
      (fun p : Fin m => p.val) (fun p => by omega)
      (fun p1 p2 h => Fin.ext h)
      (Tln_l l) pWire
      (fun j hj => by
        obtain ⟨p, hp⟩ := (hTstar_props j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1).2.2.1
        exact ⟨p, (Finset.mem_filter.mp hp).2⟩)
  have hObot_p_disj : Set.PairwiseDisjoint (A : Set (Fin m)) Obot_p := by
    intro p1 _ p2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro o h1 h2
    obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
    obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
    obtain ⟨l1, hl1, l2, hl2, hlne⟩ := Finset.one_lt_card.mp (by omega : 1 < (lns (N + o.val)).card)
    have hj1pt := (Finset.mem_filter.mp hj1).1
    have hj1p := (Finset.mem_filter.mp hj1).2
    have hj2pt := (Finset.mem_filter.mp hj2).1
    have hj2p := (Finset.mem_filter.mp hj2).2
    have hp1_in : p1 ∈ pSide j1 := hj1p ▸ hcenterP_mem j1 hj1pt
    have hp2_in : p2 ∈ pSide j2 := hj2p ▸ hcenterP_mem j2 hj2pt
    have hl1_j1 : l1 ∈ lSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo1 (Finset.mem_filter.mp hl1).2⟩
    have hl2_j1 : l2 ∈ lSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo1 (Finset.mem_filter.mp hl2).2⟩
    have hl1_j2 : l1 ∈ lSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo2 (Finset.mem_filter.mp hl1).2⟩
    have hl2_j2 : l2 ∈ lSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo2 (Finset.mem_filter.mp hl2).2⟩
    have hpr1 := (hTstar_props j1 (Finset.mem_filter.mp hj1pt).1).2.2.2.2.2.2.1
    have hpr2 := (hTstar_props j2 (Finset.mem_filter.mp hj2pt).1).2.2.2.2.2.2.1
    exact hNoC4 p1 p2 l1 l2 hne hlne ⟨hpr1 p1 hp1_in l1 hl1_j1, hpr1 p1 hp1_in l2 hl2_j1,
      hpr2 p2 hp2_in l1 hl1_j2, hpr2 p2 hp2_in l2 hl2_j2⟩
  have hObot_l_disj : Set.PairwiseDisjoint (B : Set (Fin n)) Obot_l := by
    intro l1 _ l2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro o h1 h2
    obtain ⟨_, hcard2, j1, hj1, hjo1⟩ := (Finset.mem_filter.mp h1).2
    obtain ⟨_, _, j2, hj2, hjo2⟩ := (Finset.mem_filter.mp h2).2
    obtain ⟨p1, hp1, p2, hp2, hpne⟩ := Finset.one_lt_card.mp (by omega : 1 < (pts (N + o.val)).card)
    have hj1ln := (Finset.mem_filter.mp hj1).1
    have hj1l := (Finset.mem_filter.mp hj1).2
    have hj2ln := (Finset.mem_filter.mp hj2).1
    have hj2l := (Finset.mem_filter.mp hj2).2
    have hl1_in : l1 ∈ lSide j1 := hj1l ▸ hcenterL_mem j1 hj1ln
    have hl2_in : l2 ∈ lSide j2 := hj2l ▸ hcenterL_mem j2 hj2ln
    have hp1_j1 : p1 ∈ pSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo1 (Finset.mem_filter.mp hp1).2⟩
    have hp2_j1 : p2 ∈ pSide j1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo1 (Finset.mem_filter.mp hp2).2⟩
    have hp1_j2 : p1 ∈ pSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo2 (Finset.mem_filter.mp hp1).2⟩
    have hp2_j2 : p2 ∈ pSide j2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo2 (Finset.mem_filter.mp hp2).2⟩
    have hpr1 := (hTstar_props j1 (Finset.mem_filter.mp hj1ln).1).2.2.2.2.2.2.1
    have hpr2 := (hTstar_props j2 (Finset.mem_filter.mp hj2ln).1).2.2.2.2.2.2.1
    exact hNoC4 p1 p2 l1 l2 hpne hne ⟨hpr1 p1 hp1_j1 l1 hl1_in, hpr2 p1 hp1_j2 l2 hl2_in,
      hpr1 p2 hp2_j1 l1 hl1_in, hpr2 p2 hp2_j2 l2 hl2_in⟩
  let ObotA := A.biUnion Obot_p
  let ObotB := B.biUnion Obot_l
  have hObotAB_disj : Disjoint ObotA ObotB := by
    rw [Finset.disjoint_left]
    intro o hA hB
    obtain ⟨p, _, hoA⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨l, _, hoB⟩ := Finset.mem_biUnion.mp hB
    have hcard_l := (Finset.mem_filter.mp hoA).2.2.1
    obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (N + o.val)).card)
    obtain ⟨j, hj, hjo⟩ := (Finset.mem_filter.mp hoB).2.2.2
    have hjT := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
    have hlem := (hTstar_props j hjT).2.2.2.2.1
    have hl0_in : l0 ∈ lns (pWire j) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      PEqualNP.Outside.L_meta_4897.orPath_trans hjo (Finset.mem_filter.mp hl0).2⟩
    rw [hlem] at hl0_in; cases hl0_in
  let Obot := ObotA ∪ ObotB
  have hObot_card : Obot.card = (∑ p ∈ A, (Obot_p p).card) + (∑ l ∈ B, (Obot_l l).card) := by
    rw [Finset.card_union_of_disjoint hObotAB_disj,
      Finset.card_biUnion hObot_p_disj, Finset.card_biUnion hObot_l_disj]
  have hObot_disj_Tstar : Disjoint Obot Tstar := by
    rw [Finset.disjoint_left]
    intro o h1 h2
    have hand := (hTstar_props o h2).1
    rcases Finset.mem_union.mp h1 with hA | hB
    · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
      have hor := (Finset.mem_filter.mp ho).2.1
      rw [hor] at hand; cases hand
    · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
      have hor := (Finset.mem_filter.mp ho).2.1
      rw [hor] at hand; cases hand
  have hObot_disj_Otop : Disjoint Obot Otop := by
    rw [Finset.disjoint_left]
    intro o hbot htop
    have hop_out := (Finset.mem_filter.mp htop).2.2.1
    rcases Finset.mem_union.mp hbot with hA | hB
    · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hA
      have hcard := (Finset.mem_filter.mp ho).2.2.1
      obtain ⟨l0, hl0⟩ := Finset.card_pos.mp (by omega : 0 < (lns (N + o.val)).card)
      have hop := PEqualNP.Outside.L_meta_4897.orPath_trans hop_out (Finset.mem_filter.mp hl0).2
      let x : Fin N → Bool := fun i => decide (i = Fin.natAdd m l0)
      have hx_l : wireVal N C (m + l0.val) x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.natAdd m l0) x
        simpa [x] using this
      have ht := PEqualNP.Outside.L_meta_4897.orPath_sound hRB hop x hx_l
      have hf := hno_lns_only x (fun p' => by
        simp only [x, decide_eq_false_iff_not]
        intro h; have := congrArg Fin.val h; simp at this; omega)
      rw [ht] at hf; cases hf
    · obtain ⟨_, _, ho⟩ := Finset.mem_biUnion.mp hB
      have hcard := (Finset.mem_filter.mp ho).2.2.1
      obtain ⟨p0, hp0⟩ := Finset.card_pos.mp (by omega : 0 < (pts (N + o.val)).card)
      have hop := PEqualNP.Outside.L_meta_4897.orPath_trans hop_out (Finset.mem_filter.mp hp0).2
      let x : Fin N → Bool := fun i => decide (i = Fin.castAdd n p0)
      have hx_p : wireVal N C p0.val x = true := by
        have := PEqualNP.Outside.L_meta_4897.wireVal_input N C (Fin.castAdd n p0) x
        simpa [x] using this
      have ht := PEqualNP.Outside.L_meta_4897.orPath_sound hRB hop x hx_p
      have hf := hno_pts_only x (fun l' => by
        simp only [x, decide_eq_false_iff_not]
        intro h; have := congrArg Fin.val h; simp at this; omega)
      rw [ht] at hf; cases hf
  have hTpt_sum : ∑ p ∈ A, (Tpt_p p).card = Tpt.card :=
    (Finset.card_eq_sum_card_fiberwise (f := centerP) (fun j hj => Finset.mem_image_of_mem centerP hj)).symm
  have hTln_sum : ∑ l ∈ B, (Tln_l l).card = Tln.card :=
    (Finset.card_eq_sum_card_fiberwise (f := centerL) (fun j hj => Finset.mem_image_of_mem centerL hj)).symm
  have hE_sub : E ⊆ A.biUnion (fun p => (E_p p).image (fun l => (p, l))) ∪
      B.biUnion (fun l => (E_l l).image (fun p => (p, l))) := by
    intro e he
    obtain ⟨j, hjT, hpj, hlj⟩ := hE_in_Tstar e.1 e.2 he
    by_cases h1 : (pSide j).card = 1
    · have hjpt : j ∈ Tpt := Finset.mem_filter.mpr ⟨hjT, h1⟩
      have hcp : centerP j = e.1 := (hcenterP_eq j hjpt e.1 hpj).symm
      apply Finset.mem_union_left
      refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_image.mpr ⟨j, hjpt, hcp⟩, ?_⟩
      refine Finset.mem_image.mpr ⟨e.2, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjpt, hcp⟩, hlj⟩, rfl⟩
    · have hjln : j ∈ Tln := Finset.mem_filter.mpr ⟨hjT, h1⟩
      have hcl : centerL j = e.2 := (hcenterL_eq j hjln e.2 hlj).symm
      apply Finset.mem_union_right
      refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_image.mpr ⟨j, hjln, hcl⟩, ?_⟩
      refine Finset.mem_image.mpr ⟨e.1, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjln, hcl⟩, hpj⟩, rfl⟩
  have hE_le_sum : E.card ≤ (∑ p ∈ A, (E_p p).card) + (∑ l ∈ B, (E_l l).card) := by
    calc E.card
        ≤ (A.biUnion (fun p => (E_p p).image (fun l => (p, l))) ∪
            B.biUnion (fun l => (E_l l).image (fun p => (p, l)))).card := Finset.card_le_card hE_sub
      _ ≤ (A.biUnion (fun p => (E_p p).image (fun l => (p, l)))).card +
            (B.biUnion (fun l => (E_l l).image (fun p => (p, l)))).card := Finset.card_union_le _ _
      _ ≤ (∑ p ∈ A, ((E_p p).image (fun l => (p, l))).card) +
            (∑ l ∈ B, ((E_l l).image (fun p => (p, l))).card) :=
          Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ ≤ (∑ p ∈ A, (E_p p).card) + (∑ l ∈ B, (E_l l).card) :=
          Nat.add_le_add
            (Finset.sum_le_sum fun p _ => Finset.card_image_le)
            (Finset.sum_le_sum fun l _ => Finset.card_image_le)
  have hsum_A : ∑ p ∈ A, (E_p p).card ≤ (∑ p ∈ A, (Obot_p p).card) + Tpt.card := by
    calc ∑ p ∈ A, (E_p p).card
        ≤ ∑ p ∈ A, ((Obot_p p).card + (Tpt_p p).card) := Finset.sum_le_sum hEp_bound
      _ = (∑ p ∈ A, (Obot_p p).card) + (∑ p ∈ A, (Tpt_p p).card) := Finset.sum_add_distrib
      _ = (∑ p ∈ A, (Obot_p p).card) + Tpt.card := by rw [hTpt_sum]
  have hsum_B : ∑ l ∈ B, (E_l l).card ≤ (∑ l ∈ B, (Obot_l l).card) + Tln.card := by
    calc ∑ l ∈ B, (E_l l).card
        ≤ ∑ l ∈ B, ((Obot_l l).card + (Tln_l l).card) := Finset.sum_le_sum hEl_bound
      _ = (∑ l ∈ B, (Obot_l l).card) + (∑ l ∈ B, (Tln_l l).card) := Finset.sum_add_distrib
      _ = (∑ l ∈ B, (Obot_l l).card) + Tln.card := by rw [hTln_sum]
  have h3disj : Tstar.card + Obot.card + Otop.card ≤ C.size := by
    have hdisj1 : Disjoint (Tstar ∪ Obot) Otop := by
      rw [Finset.disjoint_union_left]
      exact ⟨hOtop_disj_Tstar.symm, hObot_disj_Otop⟩
    have hcard_u : ((Tstar ∪ Obot) ∪ Otop).card = Tstar.card + Obot.card + Otop.card := by
      rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hObot_disj_Tstar.symm]
    have hle : ((Tstar ∪ Obot) ∪ Otop).card ≤ (Finset.univ : Finset (Fin C.gates.length)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    change Tstar.card + Obot.card + Otop.card ≤ C.gates.length
    omega
  refine ⟨A, B, hcover, ?_⟩
  omega
