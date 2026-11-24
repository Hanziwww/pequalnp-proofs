import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fixing pin six removes its reader. The eight-input minimum then forces
-- exactly thirteen ordinary gates and a live final gate. Three rows exclude
-- five physical pins as companions. The remaining obstruction uses bounded
-- addresses, paired-input gates and output wire twenty-three.
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3338_73
    (compact :
      let input (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,false,x 6,x 3,x 1 || false]
      let read (g : Gate) := (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
        (fun i => decide (i = 6))
      ∀ C : Circuit, FanInTwo C → (∃ x, C.eval (input x) = false) →
        ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP read ≤ C.size ∧
          ∀ x, D.eval (List.ofFn x) = C.eval (input x))
    (lower : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
    (finiteCheck :
      let decode (z : Fin 3 × Fin 25 × Fin 25) : Gate :=
        ⟨if z.1 = 0 then .and else if z.1 = 1 then .or else .not, [z.2.1.val,z.2.2.val]⟩
      ∀ (p s : List (Fin 3 × Fin 25 × Fin 25)) (k : Fin 25),
        p.length + s.length = 13 → s ≠ [] →
        (∀ z ∈ p ++ s, z.2.1 ≠ 6 ∧ z.2.2 ≠ 6) → k.val ∉ ([0,2,6,7,8,9] : List ℕ) → k.val < 10 + p.length →
        let C : Circuit := ⟨p.map decode ++ ⟨.or,[6,k.val]⟩ :: s.map decode,23⟩
        ∃ x : Fin 9 → Bool,
          let v := List.ofFn x
          C.eval (v ++ [x 0 || x 6]) ≠
            ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
              (fun e => v.getD (e/9) false && v.getD (e % 9) false)) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) =>   have x4 : ℕ := PEqualNP.MetaComplexity.tableIndex x3;   ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x4 / (64 : ℕ)) (0 : ℕ)).testBit (x4 % (64 : ℕ)); ∀ (x4 x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x4 ++ x6 :: x5, output := x7 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 →     x4.length + x5.length ≤ (13 : ℕ) →       (∀ x11 ∈ x4 ++ x5, x1 x11 = Bool.false) →         x1 x6 = Bool.true →           x6.op = PEqualNP.CircuitLowerBounds.GateOp.or →             (have x14 : Fin (8 : ℕ) → Bool := fun (x14 : Fin (8 : ℕ)) => Decidable.decide (x14 = (1 : Fin (8 : ℕ)) ∨ x14 = (3 : Fin (8 : ℕ)));               have x15 : Bool → Bool := fun (x15 : Bool) => x6.op.eval (List.map (fun (x16 : ℕ) => ({ gates := x4, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 x15 x14)).getD x16 Bool.false) x6.inputs);               x15 Bool.true ≠ x15 Bool.false) →               (∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.false x15) = x3 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.true x16) ≠ (x3 x16 || x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ))) := by
  have evalAnd (v : List Bool) : GateOp.and.eval v = v.all id := rfl
  have evalOr (v : List Bool) : GateOp.or.eval v = v.any id := rfl
  have evalNot (v : List Bool) : GateOp.not.eval v = !(v.headD false) := rfl
  let sensorRead (g : Gate) : Bool :=
    (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any
      (fun j => decide (j = 6))

  let sensorInput (b : Bool) (x : Fin 8 → Bool) : List Bool :=
    [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]

  let sensorTable (x : Fin 8 → Bool) : Bool :=
    let k := tableIndex x
    (([18369897887404062920,18446740762289764600,18446744073709551560,
      18446744073709551608] : List ℕ).getD (k / 64) 0).testBit (k % 64)

  let sensorValue (g : Gate) (w : List Bool) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  let sensorStep (w : List Bool) (g : Gate) : List Bool := w ++ [sensorValue g w]

  let sensorAgree (u v : List Bool) : Prop :=
    ∀ i, i ≠ 6 → u.getD i false = v.getD i false

  let sensorOK (g : Gate) : Prop :=
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ sensorRead g = false

  have sensor_gate_agree (g : Gate) (ok : sensorOK g) (u v : List Bool)
      (h : sensorAgree u v) : sensorValue g u = sensorValue g v := by
    obtain ⟨op, pins⟩ := g
    obtain ⟨basis, skip⟩ := ok
    rcases basis with a | a | a <;> change op = _ at a <;> subst op
    · apply congrArg GateOp.and.eval
      apply List.map_congr_left
      intro i hi
      apply h
      rintro rfl
      change (pins.any (fun j => decide (j = 6))) = false at skip
      have exclude : ∀ x ∈ pins, x ≠ 6 := by simpa using skip
      exact exclude 6 hi rfl
    · apply congrArg GateOp.or.eval
      apply List.map_congr_left
      intro i hi
      apply h
      rintro rfl
      change (pins.any (fun j => decide (j = 6))) = false at skip
      have exclude : ∀ x ∈ pins, x ≠ 6 := by simpa using skip
      exact exclude 6 hi rfl
    · cases pins with
      | nil => rfl
      | cons i rest =>
        change (decide (i = 6) || false) = false at skip
        have ne : i ≠ 6 := by simpa using skip
        exact congrArg Bool.not (h i ne)

  have sensor_snoc_agree {u v : List Bool} {a b : Bool}
      (len : u.length = v.length) (h : sensorAgree u v) (hab : a = b) :
      sensorAgree (u ++ [a]) (v ++ [b]) := by
    intro i hi
    by_cases lt : i < u.length
    · exact (List.getD_append _ _ _ _ lt).trans
        ((h i hi).trans (List.getD_append _ _ _ _ (len ▸ lt)).symm)
    · simp only [List.getD_append_right _ _ _ _ (by omega : u.length ≤ i),
        List.getD_append_right _ _ _ _ (by omega : v.length ≤ i), len, hab]

  have sensor_run_agree (gs : List Gate) (ok : ∀ g ∈ gs, sensorOK g)
      (u v : List Bool) (len : u.length = v.length) (h : sensorAgree u v) :
      sensorAgree (gs.foldl sensorStep u) (gs.foldl sensorStep v) := by
    induction gs generalizing u v with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun g' h' => ok g' (List.mem_cons_of_mem _ h')) _ _
        (by simp [sensorStep, len])
      exact sensor_snoc_agree len h (sensor_gate_agree _ (ok g (by simp)) _ _ h)

  have sensor_run_length (gs : List Gate) (w : List Bool) :
      (gs.foldl sensorStep w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [sensorStep, List.length_append, List.length_cons, List.length_nil]
      omega

  have sensor_run_preserve (gs : List Gate) (w : List Bool) (j : ℕ) (h : j < w.length) :
      (gs.foldl sensorStep w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (sensorStep w g) (by simp [sensorStep]; omega)]
      exact List.getD_append _ _ _ _ h

  have sensor_forced_zero (pre post : List Gate) (g : Gate) (out : ℕ)
      (fan : FanInTwo (Circuit.mk (pre ++ g :: post) out))
      (rest : ∀ h ∈ pre ++ post, sensorRead h = false)
      (reads : sensorRead g = true) (hop : g.op = .or)
      (low : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (sensorInput false x) = sensorTable x)
      (high : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (sensorInput true x) =
        (sensorTable x || x 0 || x 3))
      (x : Fin 8 → Bool) (h1 : x 1 = true) (hz : sensorTable x = false) (h3 : x 3 = true) :
      ∀ j ∈ g.inputs, ((Circuit.mk pre 0).wires (sensorInput false x)).getD j false = false := by
    have out_ne : out ≠ 6 := by
      rintro rfl
      have hh := high (fun _ => false)
      change ((pre ++ g :: post).foldl sensorStep _).getD 6 false = _ at hh
      rw [sensor_run_preserve _ _ _ (by decide)] at hh
      revert hh
      decide
    have mem6 : 6 ∈ g.inputs := by
      simpa [sensorRead, hop, evalAnd,evalOr,evalNot] using reads
    have okPart (p : List Gate) (sub : ∀ h ∈ p, h ∈ pre ++ post) : ∀ h ∈ p, sensorOK h := by
      intro h hh
      have hp := sub h hh
      have hc : h ∈ pre ++ g :: post := by
        rcases List.mem_append.mp hp with hp | hp <;> simp [hp]
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fan h hc).1, rest h hp⟩
    have sameInput : sensorAgree (sensorInput true x) (sensorInput false x) := by
      intro i hi
      by_cases hb : i < 10
      · interval_cases i <;> first | rfl | contradiction | simp [sensorInput, h1]
      · rw [List.getD_eq_default _ false (by change 10 ≤ i; omega),
          List.getD_eq_default _ false (by change 10 ≤ i; omega)]
    let w (b : Bool) := pre.foldl sensorStep (sensorInput b x)
    have equalLen : (w true).length = (w false).length := by simp [w, sensor_run_length, sensorInput]
    have agree : sensorAgree (w true) (w false) :=
      sensor_run_agree pre (okPart _ (fun _ h => List.mem_append_left _ h)) _ _ rfl sameInput
    have isHigh : sensorValue g (w true) = true := by
      have hp : (w true).getD 6 false = true := by
        exact sensor_run_preserve pre (sensorInput true x) _ (by change 6 < 10; decide)
      simpa [sensorValue, hop, evalAnd,evalOr,evalNot, Function.comp_def] using
        (show ∃ j ∈ g.inputs, (w true).getD j false = true from ⟨6, mem6, hp⟩)
    intro j hj
    change (w false).getD j false = false
    by_contra! hbit
    have isLow : sensorValue g (w false) = true := by
      simpa [sensorValue, hop, evalAnd,evalOr,evalNot, Function.comp_def] using
        (show ∃ j ∈ g.inputs, (w false).getD j false = true from ⟨j, hj, by simpa using hbit⟩)
    have after : sensorAgree (sensorStep (w true) g) (sensorStep (w false) g) :=
      sensor_snoc_agree equalLen agree (isHigh.trans isLow.symm)
    have suffix := sensor_run_agree post (okPart _ (fun _ h => List.mem_append_right _ h))
      _ _ (by simp [sensorStep, equalLen]) after out out_ne
    have eqOut : (Circuit.mk (pre ++ g :: post) out).eval (sensorInput true x) =
        (Circuit.mk (pre ++ g :: post) out).eval (sensorInput false x) := by
      change ((pre ++ g :: post).foldl sensorStep _).getD out false =
        ((pre ++ g :: post).foldl sensorStep _).getD out false
      simpa only [List.foldl_append, List.foldl_cons, w] using suffix
    rw [low, high, hz, h3] at eqOut
    simp at eqOut

  have sensor_forbidden_pins (pre : List Gate) (g : Gate)
      (zero : ∀ x : Fin 8 → Bool, x 1 = true → sensorTable x = false → x 3 = true →
        ∀ j ∈ g.inputs, ((Circuit.mk pre 0).wires (sensorInput false x)).getD j false = false) :
      ∀ j ∈ g.inputs, j ∉ ([0,2,7,8,9] : List ℕ) := by
    intro j hj bad
    have witness : ∃ x : Fin 8 → Bool, x 1 = true ∧ sensorTable x = false ∧ x 3 = true ∧
        (sensorInput false x).getD j false = true ∧ j < (sensorInput false x).length := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at bad
      rcases bad with hb | hb | hb | hb | hb <;> subst j
      all_goals first
        | exact ⟨fun i => decide (i = 1 ∨ i = 3), by decide⟩
        | exact ⟨fun i => decide (i = 1 ∨ i = 3 ∨ i = 4), by decide⟩
        | exact ⟨fun i => decide (i = 1 ∨ i = 3 ∨ i = 6), by decide⟩
    obtain ⟨x, h1, hz, h3, bit, len⟩ := witness
    have hb := zero x h1 hz h3 j hj
    change (pre.foldl sensorStep (sensorInput false x)).getD j false = false at hb
    rw [sensor_run_preserve _ _ _ len, bit] at hb
    contradiction

  have sensor_last (pre post : List Gate) (g : Gate) (out : ℕ)
      (expensive : ∀ (p s : List Gate) (a : Gate) (o : ℕ),
        FanInTwo (Circuit.mk (p ++ a :: s) o) → sensorRead a = true → a.op = .or →
        (∀ x, (Circuit.mk (p ++ a :: s) o).eval (sensorInput false x) = sensorTable x) →
        13 ≤ p.length + s.length)
      (fan : FanInTwo (Circuit.mk (pre ++ g :: post) out))
      (cost : pre.length + post.length ≤ 13)
      (rest : ∀ h ∈ pre ++ post, sensorRead h = false)
      (reads : sensorRead g = true) (hop : g.op = .or)
      (low : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (sensorInput false x) = sensorTable x)
      (high : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (sensorInput true x) =
        (sensorTable x || x 0 || x 3)) :
      post ≠ [] ∧ out = 10 + pre.length + post.length := by
    let probe : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
    have high1 : (Circuit.mk (pre ++ g :: post) out).eval (sensorInput true probe) = true := by
      rw [high]
      decide
    have low1 : (Circuit.mk (pre ++ g :: post) out).eval (sensorInput false probe) = false := by
      rw [low]
      decide
    have high0 : (Circuit.mk (pre ++ g :: post) out).eval (sensorInput true (fun _ => false)) = false := by
      rw [high (fun _ => false)]
      decide
    have upto : out ≤ 10 + pre.length + post.length := by
      by_contra! far
      change ((pre ++ g :: post).foldl sensorStep _).getD out false = true at high1
      rw [List.getD_eq_default _ _ (by
        simp only [sensor_run_length, List.length_append, List.length_cons]
        change 10 + (pre.length + (post.length + 1)) ≤ out
        omega)] at high1
      contradiction
    have hpost : post ≠ [] := by
      rintro rfl
      change out ≤ 10 + pre.length + 0 at upto
      let w (b : Bool) (x : Fin 8 → Bool) := pre.foldl sensorStep (sensorInput b x)
      have wlen (b : Bool) (x : Fin 8 → Bool) : (w b x).length = 10 + pre.length :=
        sensor_run_length pre (sensorInput b x)
      have final (b : Bool) (x : Fin 8 → Bool) :
          (Circuit.mk (pre ++ [g]) out).eval (sensorInput b x) =
            (w b x ++ [sensorValue g (w b x)]).getD out false := by
        change ((pre ++ [g]).foldl sensorStep _).getD _ _ = _
        rw [List.foldl_append]
        rfl
      by_cases last : out = 10 + pre.length
      · have mem6 : 6 ∈ g.inputs := by simpa [sensorRead, hop, evalAnd,evalOr,evalNot] using reads
        have bit : (w true (fun _ => false)).getD 6 false = true :=
          sensor_run_preserve pre _ 6 (by change 6 < 10; decide)
        have gv : sensorValue g (w true (fun _ => false)) = true := by
          simpa [sensorValue, hop, evalAnd,evalOr,evalNot, Function.comp_def] using
            (show ∃ j ∈ g.inputs, (w true (fun _ => false)).getD j false = true from ⟨6, mem6, bit⟩)
        rw [final true (fun _ => false), last, List.getD_append_right _ _ _ _ (by rw [wlen true (fun _ => false)]),
          wlen true (fun _ => false), Nat.sub_self, gv] at high0
        contradiction
      · have before (b : Bool) (x : Fin 8 → Bool) :
            (Circuit.mk (pre ++ [g]) out).eval (sensorInput b x) = (w b x).getD out false := by
          rw [final]
          exact List.getD_append _ _ _ _ (by rw [wlen]; omega)
        have outne : out ≠ 6 := by
          intro e
          rw [before true (fun _ => false), e] at high0
          have bit : (w true (fun _ => false)).getD 6 false = true :=
            sensor_run_preserve pre _ 6 (by change 6 < 10; decide)
          exact Bool.noConfusion (bit.symm.trans high0)
        have ok (h : Gate) (hh : h ∈ pre) : sensorOK h := by
          refine ⟨?_, rest h (List.mem_append_left _ hh)⟩
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
            (fan h (List.mem_append_left _ hh)).1
        have same : sensorAgree (sensorInput true probe) (sensorInput false probe) := by
          intro i hi
          by_cases h : i < 10
          · interval_cases i <;> first | rfl | contradiction
          · rw [List.getD_eq_default _ false (by change 10 ≤ i; omega),
              List.getD_eq_default _ false (by change 10 ≤ i; omega)]
        have agree := sensor_run_agree pre ok (sensorInput true probe) (sensorInput false probe)
          rfl same out outne
        change (w true probe).getD out false = (w false probe).getD out false at agree
        rw [before] at high1 low1
        rw [high1, low1] at agree
        contradiction
    refine ⟨hpost, ?_⟩
    obtain ⟨init, k, rfl⟩ : ∃ (init : List Gate) (k : Gate), post = init ++ [k] :=
      ⟨_, _, (List.dropLast_concat_getLast hpost).symm⟩
    by_contra! hne
    have shorter : out < 10 + pre.length + (init ++ [k]).length := by omega
    have hfan : FanInTwo (Circuit.mk (pre ++ g :: init) out) := by
      intro h hh
      apply fan h
      change h ∈ pre ++ g :: (init ++ [k])
      have mem : h ∈ pre ++ g :: init := hh
      rcases List.mem_append.mp mem with hpre | htail
      · exact List.mem_append_left _ hpre
      · refine List.mem_append_right _ ?_
        rcases List.mem_cons.mp htail with heq | hinit
        · exact List.mem_cons.mpr (Or.inl heq)
        · exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ hinit))
    have hlow (x : Fin 8 → Bool) :
        (Circuit.mk (pre ++ g :: init) out).eval (sensorInput false x) = sensorTable x := by
      have eqn : pre ++ g :: (init ++ [k]) = (pre ++ g :: init) ++ [k] := by simp
      have hh := low x
      change ((pre ++ g :: (init ++ [k])).foldl sensorStep _).getD out false = _ at hh
      rw [eqn, List.foldl_append] at hh
      let wires := (pre ++ g :: init).foldl sensorStep (sensorInput false x)
      change (wires ++ [sensorValue k wires]).getD out false = sensorTable x at hh
      have below : out < wires.length := by
        simp only [wires, sensor_run_length, List.length_append, List.length_cons]
        change out < 10 + (pre.length + (init.length + 1))
        simp only [List.length_append, List.length_singleton] at shorter
        omega
      rw [List.getD_append _ _ _ _ below] at hh
      exact hh
    have size := expensive pre init g out hfan reads hop hlow
    simp only [List.length_append, List.length_singleton] at cost
    omega
  let Instr := Fin 3 × Fin 25 × Fin 25

  let unpack (z : Instr) : Gate :=
    ⟨if z.1 = 0 then .and else if z.1 = 1 then .or else .not, [z.2.1.val,z.2.2.val]⟩

  let clip (i : ℕ) : Fin 25 := ⟨min i 24, by omega⟩

  let value (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

  let readPin (g : Gate) : Bool :=
    (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any fun i => decide (i = 6)

  have clip_ok (w : List Bool) (bw : w.length ≤ 24) (i : ℕ) :
      w.getD (clip i).val false = w.getD i false := by
    by_cases h : i ≤ 24
    · simp [clip,h]
    · have hi : 24 ≤ i := by omega
      simp only [clip, min_eq_right hi]
      rw [List.getD_eq_default _ _ bw, List.getD_eq_default _ _ (by omega)]

  have opt_clip (w : List Bool) (h : w.length ≤ 24) (i : ℕ) :
      w[(clip i).val]?.getD false = w[i]?.getD false := by
    simpa only [List.getD] using clip_ok w h i

  have opt_end (w : List Bool) (h : w.length ≤ 24) : w[24]?.getD false = false := by
    simp [List.getElem?_eq_none h]

  have clip_ne (i : ℕ) (h : i ≠ 6) : clip i ≠ 6 := by
    intro eq
    have hh := congrArg Fin.val eq
    change min i 24 = 6 at hh
    omega

  have ordinary_code (g : Gate) (basis : g.op = .and ∨ g.op = .or ∨ g.op = .not)
      (arity : g.inputs.length ≤ 2) (skip : readPin g = false) :
      ∃ z : Instr, z.2.1 ≠ 6 ∧ z.2.2 ≠ 6 ∧
        ∀ w : List Bool, w.length ≤ 24 → value (unpack z) w = value g w := by
    obtain ⟨op,pins⟩ := g
    change op = _ ∨ op = _ ∨ op = _ at basis
    change pins.length ≤ 2 at arity
    rcases basis with rfl|rfl|rfl
    · have h : ∀ i ∈ pins, i ≠ 6 := by simpa [readPin, evalAnd,evalOr,evalNot] using skip
      rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c,s⟩⟩⟩
      ·
        refine ⟨(2,24,24), by decide, by decide, fun w hw => ?_⟩
        simp [value,unpack,evalAnd,evalOr,evalNot,opt_end w hw]
      ·
        refine ⟨(0,clip a,clip a),clip_ne _ (h a (by simp)),clip_ne _ (h a (by simp)),?_⟩
        intro w hw
        simp [value,unpack,evalAnd,evalOr,evalNot,opt_clip w hw]
      ·
        refine ⟨(0,clip a,clip b),clip_ne _ (h a (by simp)),clip_ne _ (h b (by simp)),?_⟩
        intro w hw
        simp [value,unpack,evalAnd,evalOr,evalNot,opt_clip w hw]
      · simp at arity
    · have h : ∀ i ∈ pins, i ≠ 6 := by simpa [readPin, evalAnd,evalOr,evalNot] using skip
      rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c,s⟩⟩⟩
      ·
        refine ⟨(1,24,24), by decide, by decide, fun w hw => ?_⟩
        simp [value,unpack,evalAnd,evalOr,evalNot,opt_end w hw]
      ·
        refine ⟨(1,clip a,clip a),clip_ne _ (h a (by simp)),clip_ne _ (h a (by simp)),?_⟩
        intro w hw
        simp [value,unpack,evalAnd,evalOr,evalNot,opt_clip w hw]
      ·
        refine ⟨(1,clip a,clip b),clip_ne _ (h a (by simp)),clip_ne _ (h b (by simp)),?_⟩
        intro w hw
        simp [value,unpack,evalAnd,evalOr,evalNot,opt_clip w hw]
      · simp at arity
    · rcases pins with _ | ⟨a,s⟩
      · refine ⟨(2,24,24), by decide, by decide, fun w hw => ?_⟩
        simp [value,unpack,evalAnd,evalOr,evalNot,opt_end w hw]
      ·
        have ha : a ≠ 6 := by simpa [readPin,evalAnd,evalOr,evalNot] using skip
        refine ⟨(2,clip a,clip a),clip_ne _ ha,clip_ne _ ha,?_⟩
        intro w hw
        simp [value,unpack,evalAnd,evalOr,evalNot,opt_clip w hw]

  let run (l : List Gate) (w : List Bool) : List Bool := l.foldl (fun v g => v ++ [value g v]) w

  have list_code (l : List Gate) (ok : ∀ g ∈ l,
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 ∧ readPin g = false) :
      ∃ z : List Instr, z.length = l.length ∧
        (∀ a ∈ z, a.2.1 ≠ 6 ∧ a.2.2 ≠ 6) ∧
        ∀ w : List Bool, w.length + l.length ≤ 24 → run (z.map unpack) w = run l w := by
    induction l with
    | nil => exact ⟨[],rfl,by simp,by simp [run]⟩
    | cons g gs ih =>
      obtain ⟨basis,arity,skip⟩ := ok g (by simp)
      obtain ⟨a,h1,h2,he⟩ := ordinary_code g basis arity skip
      obtain ⟨as,hl,hs,hh⟩ := ih (fun h hm => ok h (List.mem_cons_of_mem _ hm))
      refine ⟨a::as,by simp [hl],by simpa [h1,h2] using hs,?_⟩
      intro w hw
      simp only [List.length_cons] at hw
      simp only [List.map_cons,run,List.foldl_cons]
      rw [he w (by omega)]
      apply hh
      simp
      omega
  let edge8 (x : Fin 8 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  have fromTable : ∀ x, sensorTable x = edge8 x := by
    dsimp only [sensorTable,edge8]
    decide +kernel
  have cheap : ¬ HasCircuitSize 8 sensorTable 12 := by
    rw [show sensorTable = edge8 from funext fromTable]
    exact lower
  -- Wire-alias simulation adapted from L-meta-1498.
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  let shiftDown (wOld u : ℕ) : ℕ :=
    if wOld < u then u - 1 else u

  let wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
    wC.length = wD.length + 1 ∧
    w0.length ≤ wD.length ∧
    wC.getD w0.length false = bOld ∧
    (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
    (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
    (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

  have wiresMatch_init (w0 : List Bool) (bOld : Bool) :
      wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
    refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
    · simp [List.getD_eq_getElem?_getD]
    · intro u hu
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
    · intro u hu
      have h1 : w0.length ≤ u - 1 := by omega
      have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
      rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

  have wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
      (hm : wiresMatch w0 bOld wC wD) :
      wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
    obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
    refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
    · have hlt : w0.length < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      simpa [List.getD_eq_getElem?_getD] using hbold
    · intro u hu
      have h1 : u < wD.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
      simpa [List.getD_eq_getElem?_getD] using hltD u hu
    · intro u hu
      have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hltC u hu
    · intro u hu
      by_cases h1 : u - 1 < wD.length
      · have h2 : u < wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left h1, List.getElem?_append_left h2]
        simpa [List.getD_eq_getElem?_getD] using hgt u hu
      · by_cases heq : u - 1 = wD.length
        · have heqC : u = wC.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
              List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
          simp
        · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
          have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
          rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

  have wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
      (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
      wD.getD (shiftDown w0.length u) false = wC.getD u false := by
    unfold shiftDown
    by_cases hgt : w0.length < u
    · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
    · simp only [hgt, ↓reduceIte]
      have hlt : u < w0.length := by omega
      rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

  have foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
      (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
      (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
        wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
        (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
        (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
      wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
    induction gsC generalizing gsD wC wD with
    | nil =>
      cases gsD with
      | nil => exact hm
      | cons => simp at hlen
    | cons gC restC ih =>
      cases gsD with
      | nil => simp at hlen
      | cons gD restD =>
        simp only [List.foldl_cons]
        have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
        simp only [List.getElem_cons_zero] at heq0
        have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
          unfold stepWire
          rw [heq0]
          exact wiresMatch_step hm
        apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
        intro t htC htD vC vD hmv hvlen
        have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
          (by simp [stepWire] at hvlen ⊢; omega)
        simpa only [List.getElem_cons_succ] using h'

  let aliasWire (wOld wNew u : ℕ) : ℕ :=
    if u = wOld then wNew else shiftDown wOld u

  let aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩


  have thirteen_impossible (D : Circuit) (fan : FanInTwo D) (sz : D.size ≤ 13)
      (low : ∀ x, D.eval (sensorInput false x) = sensorTable x)
      (high : ∀ x, D.eval (sensorInput true x) = (sensorTable x || x 0 || x 3)) : False := by
    let p : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
    have outNe : D.output ≠ 6 := by
      intro eo
      have h := high (fun _ => false)
      change (D.gates.foldl sensorStep _).getD D.output false = _ at h
      rw [eo, sensor_run_preserve _ _ _ (by change 6 < 10; decide)] at h
      revert h
      dsimp only [sensorInput,sensorTable]
      decide +kernel
    have count : 1 ≤ D.gates.countP sensorRead := by
      by_contra! hn
      have hn' : D.gates.countP sensorRead = 0 := by omega
      have ok : ∀ g ∈ D.gates, sensorOK g := by
        intro g hg
        refine ⟨(fan g hg).1, ?_⟩
        change sensorRead g = false
        exact Bool.eq_false_iff.mpr (List.countP_eq_zero.mp hn' g hg)
      have agree : sensorAgree (sensorInput true p) (sensorInput false p) := by
        intro i ne
        by_cases h : i < 10
        · interval_cases i <;> first | rfl | contradiction
        · rw [List.getD_eq_default _ false (by change 10 ≤ i; omega),
              List.getD_eq_default _ false (by change 10 ≤ i; omega)]
      have he := sensor_run_agree D.gates ok (sensorInput true p) (sensorInput false p) rfl agree D.output outNe
      change D.eval (sensorInput true p) = D.eval (sensorInput false p) at he
      rw [high, low] at he
      revert he
      dsimp only [p,sensorTable]
      decide +kernel
    obtain ⟨T, ht, hs, he⟩ := compact D fan
      ⟨fun _ => false, (low (fun _ => false)).trans (show sensorTable (fun _ => false) = false by dsimp only [sensorTable] <;> decide +kernel)⟩
    change T.size + D.gates.countP sensorRead ≤ D.size at hs
    exact cheap ⟨T, ht, by omega, fun x => (he x).trans (low x)⟩

  have collapse_alias6 (pre post : List Gate) (g : Gate) (out : ℕ)
      (fan : FanInTwo (Circuit.mk (pre ++ g :: post) out))
      (alias6 : ∀ (b : Bool) (x : Fin 8 → Bool),
        g.op.eval (g.inputs.map fun i => ((Circuit.mk pre 0).wires (sensorInput b x)).getD i false) = b) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = pre.length + post.length ∧
        ∀ (b : Bool) (x : Fin 8 → Bool), D.eval (sensorInput b x) =
          (Circuit.mk (pre ++ g :: post) out).eval (sensorInput b x) := by
    let k := 10 + pre.length
    let D : Circuit := ⟨pre ++ post.map (aliasGate k 6), aliasWire k 6 out⟩
    refine ⟨D, ?_, by change D.gates.length = _; simp [D], ?_⟩
    · intro g' hg
      change g' ∈ pre ++ post.map (aliasGate k 6) at hg
      rcases List.mem_append.mp hg with hpre | hpost
      · exact fan g' (List.mem_append_left _ hpre)
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hpost
      have h := fan r (List.mem_append_right _ (List.mem_cons_of_mem _ hr))
      exact ⟨h.1, by simpa [aliasGate] using h.2⟩
    · intro b x
      let w := pre.foldl stepWire (sensorInput b x)
      have hlen : w.length = k := sensor_run_length _ _
      have h6 : 6 < w.length := by rw [hlen]; dsimp [k]; omega
      have v6 : w.getD 6 false = b :=
        (sensor_run_preserve _ _ _ (by simp [sensorInput])).trans rfl
      have equal : stepWire w g = w ++ [b] := by
        unfold stepWire
        rw [show g.op.eval (g.inputs.map fun i => w.getD i false) = b from alias6 b x]
      have sim {vC vD : List Bool} (hv : wiresMatch w b vC vD) (u : ℕ) :
          vD.getD (aliasWire k 6 u) false = vC.getD u false := by
        by_cases hu : u = k
        · subst u
          rw [show aliasWire k 6 k = 6 by simp [aliasWire], hv.2.2.2.1 6 h6, v6,
            ← hlen, hv.2.2.1]
        · rw [show aliasWire k 6 u = shiftDown w.length u by simp [aliasWire, hu, hlen]]
          exact wiresMatch_getD_shiftDown hv (by omega)
      have fin := foldl_wiresMatch w b post (post.map (aliasGate k 6)) (w ++ [b]) w
        (wiresMatch_init w b) (by simp) (by
          intro j hj hj' vC vD hv _
          simp only [List.getElem_map, aliasGate, List.map_map]
          congr 1
          exact List.map_congr_left (fun u _ => sim hv u))
      change ((pre ++ post.map (aliasGate k 6)).foldl stepWire (sensorInput b x)).getD
        (aliasWire k 6 out) false =
        ((pre ++ g :: post).foldl stepWire (sensorInput b x)).getD out false
      rw [List.foldl_append, List.foldl_append, List.foldl_cons]
      change ((post.map (aliasGate k 6)).foldl stepWire w).getD (aliasWire k 6 out) false =
        (post.foldl stepWire (stepWire w g)).getD out false
      rw [equal]
      exact sim fin out

  have effective_companion (pre post : List Gate) (g : Gate) (out : ℕ)
      (fan : FanInTwo (Circuit.mk (pre ++ g :: post) out))
      (len : pre.length + post.length ≤ 13) (reads : sensorRead g = true) (op : g.op = .or)
      (low : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (sensorInput false x) = sensorTable x)
      (high : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (sensorInput true x) =
        (sensorTable x || x 0 || x 3)) :
      ∃ i ∈ g.inputs, i ≠ 6 ∧ i < 10 + pre.length ∧
        ∃ x, ((Circuit.mk pre 0).wires (sensorInput false x)).getD i false = true := by
    classical
    have mem6 : 6 ∈ g.inputs := by simpa [sensorRead, op, evalAnd,evalOr,evalNot] using reads
    have aliasOr : (∀ (b : Bool) (x : Fin 8 → Bool),
        g.op.eval (g.inputs.map fun i => ((Circuit.mk pre 0).wires (sensorInput b x)).getD i false) = b) →
        False := by
      intro mask
      obtain ⟨D, hd, hs, he⟩ := collapse_alias6 pre post g out fan mask
      exact thirteen_impossible D hd (by omega)
        (fun x => (he false x).trans (low x)) (fun x => (he true x).trans (high x))
    by_contra hnone
    apply aliasOr
    intro b x
    let w := pre.foldl stepWire (sensorInput b x)
    have hw : w.length = 10 + pre.length := sensor_run_length _ _
    have h6 : w.getD 6 false = b :=
      (sensor_run_preserve _ _ _ (by simp [sensorInput])).trans rfl
    change g.op.eval (g.inputs.map fun i => w.getD i false) = b
    rw [op]
    cases b with
    | true =>
      apply List.any_eq_true.mpr
      exact ⟨true, List.mem_map.mpr ⟨6, mem6, h6⟩, rfl⟩
    | false =>
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨v, hv, hv'⟩ := List.any_eq_true.mp ht
      change v = true at hv'
      subst v
      obtain ⟨i, hi, hit⟩ := List.mem_map.mp hv
      have ne : i ≠ 6 := by rintro rfl; rw [h6] at hit; contradiction
      have lt : i < w.length := by
        by_contra! large
        rw [List.getD_eq_default _ _ large] at hit
        contradiction
      exact hnone ⟨i, hi, ne, by omega, x, hit⟩
  have expensive (p s : List Gate) (a : Gate) (o : ℕ)
      (hf : FanInTwo (Circuit.mk (p ++ a :: s) o))
      (hr : sensorRead a = true) (_ : a.op = .or)
      (hl : ∀ x, (Circuit.mk (p ++ a :: s) o).eval (sensorInput false x) = sensorTable x) :
      13 ≤ p.length + s.length := by
    let C : Circuit := ⟨p ++ a :: s,o⟩
    have hasF : ∃ x, C.eval (sensorInput false x) = false :=
      ⟨fun _ => false,(hl (fun _ => false)).trans (by dsimp only [sensorTable]; decide)⟩
    obtain ⟨D,dfan,sz,eqn⟩ := compact C hf hasF
    change D.size + C.gates.countP sensorRead ≤ C.size at sz
    have count : 1 ≤ C.gates.countP sensorRead := by simp [C,List.countP_append,hr]; omega
    have len : C.size = p.length + s.length + 1 := by change (p ++ a :: s).length = _; simp; omega
    by_contra! small
    apply lower
    refine ⟨D,dfan,by omega,fun x => ?_⟩
    exact (eqn x).trans ((hl x).trans (fromTable x))
  intro read input table pre post g out C fan cost rest reads hop _ low
  change sensorRead g = true at reads
  change ∀ x, C.eval (sensorInput false x) = sensorTable x at low
  change ∃ x, C.eval (sensorInput true x) ≠ (sensorTable x || x 0 || x 3)
  by_contra! high
  change ∀ x, C.eval (sensorInput true x) = (sensorTable x || x 0 || x 3) at high
  have sat : pre.length + post.length = 13 := Nat.le_antisymm cost (expensive pre post g out fan reads hop low)
  obtain ⟨nonempty,last⟩ := sensor_last pre post g out expensive fan cost rest reads hop low high
  have good (a : Gate) (h : a ∈ pre ++ post) :
      (a.op = .and ∨ a.op = .or ∨ a.op = .not) ∧ a.inputs.length ≤ 2 ∧ readPin a = false := by
    have mem : a ∈ C.gates := by
      change a ∈ pre ++ g :: post
      rcases List.mem_append.mp h with hp|hp <;> simp [hp]
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan a mem).1,
      (fan a mem).2, rest a h⟩
  obtain ⟨p,plen,pok,peval⟩ := list_code pre (fun a ha => good a (List.mem_append_left _ ha))
  obtain ⟨s,slen,sok,seval⟩ := list_code post (fun a ha => good a (List.mem_append_right _ ha))
  have prune := sensor_forbidden_pins pre g (sensor_forced_zero pre post g out fan rest reads hop low high)
  have gmem : g ∈ C.gates := by change g ∈ pre ++ g :: post; simp
  obtain ⟨j,jmem,jne,jlt,_⟩ := effective_companion pre post g out fan cost reads hop low high
  let k : Fin 25 := ⟨j,by omega⟩
  have kok : k.val ∉ ([0,2,6,7,8,9] : List ℕ) := by
    have h := prune j jmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    change ¬ (j=0 ∨ j=2 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9)
    intro hit
    apply h
    rcases hit with h0|h2|h6|h7|h8|h9
    · exact Or.inl h0
    · exact Or.inr (Or.inl h2)
    · exact False.elim (jne h6)
    · exact Or.inr (Or.inr (Or.inl h7))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h8)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h9)))
  have twoPins (pins : List ℕ) (len : pins.length ≤ 2) (a : 6 ∈ pins) (b : j ∈ pins) :
      pins = [6,j] ∨ pins = [j,6] := by
    rcases pins with _ | ⟨u, _ | ⟨v, _ | ⟨w,ws⟩⟩⟩
    · simp at a
    · have hu : 6 = u := by simpa using a
      have ju : j = u := by simpa using b
      exact False.elim (jne (ju.trans hu.symm))
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at a b
      rcases a with hu|hv <;> rcases b with ju|jv
      · exact False.elim (jne (ju.trans hu.symm))
      · exact Or.inl (by rw [← hu,← jv])
      · exact Or.inr (by rw [← ju,← hv])
      · exact False.elim (jne (jv.trans hv.symm))
    · simp at len
  have six : 6 ∈ g.inputs := by simpa [sensorRead,hop,evalOr] using reads
  have keval (w : List Bool) : value ⟨.or,[6,k.val]⟩ w = value g w := by
    rcases twoPins g.inputs (fan g gmem).2 six jmem with h|h <;>
      simp [value,hop,h,k,evalOr,Bool.or_comm]
  have blocked : ∀ z ∈ p ++ s, z.2.1 ≠ 6 ∧ z.2.2 ≠ 6 := by
    intro z hz
    exact (List.mem_append.mp hz).elim (pok z) (sok z)
  have sn : s ≠ [] := by
    intro he
    have hl : post.length = 0 := by simpa [he] using slen.symm
    exact nonempty (List.length_eq_zero_iff.mp hl)
  obtain ⟨x,bad⟩ := finiteCheck p s k (by omega) sn blocked kok (by simpa [k,plen] using jlt)
  let row (x : Fin 9 → Bool) : Fin 8 → Bool :=
    fun i => [x 1,x 0,x 5,x 8,x 2,x 4,x 7,x 3].getD i.val false
  have roweq : ∀ z : Fin 9 → Bool, sensorInput (z 6) (row z) = List.ofFn z ++ [z 0 || z 6] := by
    dsimp only [sensorInput,row]
    decide +kernel
  let target (x : Fin 9 → Bool) :=
    ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
      (fun e => (List.ofFn x).getD (e/9) false && (List.ofFn x).getD (e % 9) false)
  have targetRows : ∀ z : Fin 9 → Bool,
      (if z 6 then edge8 (row z) || row z 0 || row z 3 else edge8 (row z)) = target z := by
    dsimp only [row,edge8,target]
    decide +kernel
  let w := List.ofFn x ++ [x 0 || x 6]
  have wl : w.length = 10 := by simp [w]
  have wp : (run pre w).length = 10 + pre.length := by
    change (pre.foldl sensorStep w).length = _
    rw [sensor_run_length,wl]
  have sim :
      (Circuit.mk (p.map unpack ++ ⟨GateOp.or,[6,k.val]⟩ :: s.map unpack) 23).eval w = C.eval w := by
    have lo : out = 23 := by omega
    change (run (p.map unpack ++ ⟨GateOp.or,[6,k.val]⟩ :: s.map unpack) w).getD 23 false =
      (run (pre ++ g :: post) w).getD out false
    rw [lo]
    change ((p.map unpack ++ _ :: s.map unpack).foldl (fun v a => v ++ [value a v]) w).getD _ _ =
      ((pre ++ g :: post).foldl (fun v a => v ++ [value a v]) w).getD _ _
    simp only [List.foldl_append,List.foldl_cons]
    change (run (s.map unpack) (run (p.map unpack) w ++ [value _ (run (p.map unpack) w)])).getD _ _ =
      (run post (run pre w ++ [value g (run pre w)])).getD _ _
    rw [peval w (by omega),keval,seval _ (by simp [wp]; omega)]
  have atrow : C.eval w = target x := by
    change C.eval (List.ofFn x ++ [x 0 || x 6]) = _
    rw [← roweq x, ← targetRows x]
    cases b : x 6 with
    | false => simpa only [Bool.false_eq_true,ite_false,fromTable] using low (row x)
    | true => simpa only [ite_true,fromTable] using high (row x)
  exact bad (sim.trans atrow)
