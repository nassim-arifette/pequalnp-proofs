import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Existing full-graph size and binary-gate bounds leave an exact fourteen-gate
-- suffix, with its output last and at most two negations. The suffix sees the
-- specified disjunction as a tenth input, so its gates need no renumbering.
theorem PEqualNP.Outside.R_meta_2446_317
    (minimum : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) 14)
    (binary : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) →
      13 ≤ C.gates.countP (fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)))
    (residual : ∀ p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9)),
      ∀ D : Circuit, FanInTwo D → D.size = 14 → D.output = 23 →
      12 ≤ D.gates.countP (fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)) →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x p.1 || x p.2]) ≠ (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) x) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 x1.1 || x5 x1.2)) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x3.size := by
  let f := fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
  have runLength (l : List Gate) (w : List Bool) :
      (l.foldl step w).length = w.length + l.length := by
    induction l generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have keep (l : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (l.foldl step w).getD i false = w.getD i false := by
    induction l generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  intro p hp C fan first computes
  have eqf : circuitFun 9 C = f := by
    rw [computes]
    funext x
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  by_contra! small
  have exactSize : C.gates.length = 15 := by
    have lower : ¬ C.size ≤ 14 := fun h => minimum ⟨C,fan,h,congrFun eqf⟩
    change C.gates.length < 16 at small
    change ¬ C.gates.length ≤ 14 at lower
    omega
  have outputLast : C.output = 23 := by
    have valid : C.output < 24 := by
      by_contra! outside
      let x : Fin 9 → Bool := fun _ => true
      have on : (C.gates.foldl step (List.ofFn x)).getD C.output false = true :=
        (congrFun eqf x).trans (by decide)
      rw [List.getD_eq_default _ _ (by rw [runLength, List.length_ofFn, exactSize]; omega)] at on
      contradiction
    by_contra earlier
    let A : Circuit := ⟨C.gates.take 14, C.output⟩
    apply minimum
    refine ⟨A, fun g hg => fan g (List.mem_of_mem_take hg), ?_, ?_⟩
    · change (C.gates.take 14).length ≤ 14
      simp
    · intro x
      have eq := congrFun eqf x
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = f x at eq
      rw [← List.take_append_drop 14 C.gates, List.foldl_append, keep] at eq
      · exact eq
      · rw [runLength, List.length_ofFn, List.length_take, exactSize]
        omega
  cases gates : C.gates with
  | nil => simp [gates] at exactSize
  | cons g gs =>
    let D : Circuit := ⟨gs, C.output⟩
    have fanD : FanInTwo D := fun h hh => fan h (by rw [gates]; exact List.mem_cons_of_mem g hh)
    have sizeD : D.size = 14 := by
      change gs.length = 14
      simp [gates] at exactSize
      omega
    have enough : 12 ≤ D.gates.countP (fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)) := by
      have bound := binary C fan eqf
      let pred := fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)
      change 13 ≤ C.gates.countP pred at bound
      rw [gates] at bound
      change 12 ≤ gs.countP _
      have inc : (g :: gs).countP pred ≤ gs.countP pred + 1 := by
        rw [List.countP_cons]
        split <;> omega
      change 12 ≤ gs.countP pred
      omega
    obtain ⟨x, miss⟩ := residual p hp D fanD sizeD outputLast enough
    apply miss
    let w := List.ofFn x
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    have atNine : (w ++ [v]).getD 9 false = v := by
      simp [w]
    have val := first x
    change (C.gates.foldl step w).getD 9 false = _ at val
    rw [gates, List.foldl_cons, keep] at val
    · change (w ++ [v]).getD 9 false = _ at val
      rw [atNine] at val
      have h := congrFun eqf x
      change (C.gates.foldl step w).getD C.output false = _ at h
      rw [gates, List.foldl_cons] at h
      change (gs.foldl step (w ++ [v])).getD C.output false = _ at h
      rw [val] at h
      exact h
    · simp [step,w]
