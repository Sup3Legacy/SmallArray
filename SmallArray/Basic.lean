import Std
import Mathlib
universe u

abbrev nEmptyArray (α: Type u) := 
  {arr: Array α // 1 < arr.size}

inductive SmallArray (α: Type u) where
  | None: SmallArray α 
  | Some: α → SmallArray α 
  | Array: nEmptyArray α → SmallArray α
deriving Repr

theorem array_two_elems_length (n m: α):
  #[n, m].size > 1:= by
  have h:  #[n, m].size = 2:= by
    rfl
  rw [h]
  simp_arith

theorem array_preserves_condition (arr: nEmptyArray α) (val: α):
  1 < (arr.val.push val).size:= by
  simp only [Array.size_push, lt_add_iff_pos_left]
  apply Nat.le_of_lt
  exact arr.property

theorem non_empty_array_last (arr: Array α) (h: 0 < arr.size):
  arr.size - 1 < arr.size:= by
  have h₁: arr.size ≠ 0:= Nat.ne_of_gt h
  apply Nat.pred_lt h₁ 

theorem non_empty_array_pop (arr: Array α):
  arr.pop.size = arr.size - 1:= by
  simp only [Array.size_pop, ge_iff_le]

namespace SmallArray
  def size {α : Type u} (sa: SmallArray α): Nat:=
    match sa with
    | None => 0
    | Some _ => 1
    | Array arr => arr.val.size
  
  def push {α : Type u} (sa: SmallArray α) (val: α): SmallArray α :=
    match sa with
    | None => Some val
    | Some val' => Array ⟨#[val', val], array_two_elems_length val' val⟩
    | Array arr => Array ⟨arr.val.push val, array_preserves_condition arr val⟩

  @[simp] theorem push_size (sa: SmallArray α) (val: α):
    0 < (sa.push val).size:= by
    simp only [size, push]
    cases sa
    -- TODO: `only` this `simp`
    <;> simp

  def pop {α : Type u} (sa: SmallArray α) (h: 0 < sa.size) :=
    match sa with
    | Some val => (None, val)
    | Array arr =>
      have h: 0 < arr.val.size:=
        Nat.lt_trans (by decide) arr.property
      let val := 
        arr.val.get ⟨arr.val.size - 1, non_empty_array_last arr.val h⟩
      let arr' := arr.val.pop
      have h'': 0 < arr'.size:= by
        have h: arr'.size = arr.val.size - 1:=  non_empty_array_pop arr.val
        rw [h]
        simp only [ge_iff_le, tsub_pos_iff_lt, gt_iff_lt]
        exact arr.property
      if h': 1 < arr'.size then 
        (Array ⟨arr', h'⟩, val)
      else
        (Some (arr'.get ⟨0, h''⟩), val)
    
  def pop? {α : Type u} (sa: SmallArray α) :=
    if h: 0 < sa.size then
      sa.pop h |> fun (sa', val) => (sa', some val)
    else
      (sa, none)
end SmallArray
